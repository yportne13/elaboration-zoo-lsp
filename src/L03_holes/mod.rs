//! L03 — 双向 elaboration + 元变量（holes）与 pattern unification
//! （elaboration zoo 上游 03-holes 层 `Main.hs` 的 Rust 移植）。
//!
//! 本文件是**参考实现**（与 Main.hs 一一对应：`Box<Tm>` 项、`List` Rc 持久
//! 环境、递归 eval/quote/force/unify/rename）；极致性能版见
//! [`bump_spine_iter`]（L01/L02 调研冠军配方的移植），两版输出逐字节一致
//! （互检测试）。
//!
//! 与 L02（tyck）的语义差别：
//! - `Raw::Hole`（`_`）可出现在任意项位置，elaboration 遇之创建 fresh meta
//!   （binder 位置的 `_` 只是匿名 binder 名）；
//! - 核心语法多出 `Meta`/`InsertedMeta`，值多出 `Flex`（未解 meta 的中性
//!   应用链）；meta 是"函数"——hole 处插入的 meta 抽象掉当前作用域的全部
//!   Bound 变量（`InsertedMeta m bds`），因此解可以引用局部变量；
//! - conv 升级为 **unification**：比较带有求解 meta 的副作用（untyped
//!   pattern unification），`force` 让值跟上 metacontext 的演化——模式匹配
//!   前必须先 force；
//! - 解完全展开（不能引用 let 定义，只能引用经 spine 抽象的 Bound 变量），
//!   解通过 `invert`（partial renaming）+ `rename`（occurs/scope check）构造。

pub(crate) mod bump_spine_iter;
pub(crate) mod parser;

use parser::Raw;

use crate::list::List;
use crate::parser_lib::Span;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::fmt;

// metacontext
// --------------------------------------------------------------------------------

/// 元变量编号（metacontext 的下标）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MetaVar(u32);

impl fmt::Display for MetaVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// metacontext 条目：已解（解是空环境下的值）或未解。
#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val),
    Unsolved,
}

/// unification 失败（刚性失配 / occurs check / scope check / 非模式 spine）。
#[derive(Debug)]
struct UnifyError;

// syntax
// --------------------------------------------------------------------------------

/// De Bruijn 索引。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Ix(u32);

/// De Bruijn 层级。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lvl(u32);

impl std::ops::Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

/// binder 名。`SmolStr`：≤23 字节内联存储，`clone` 免堆分配（见 L02 readme
/// 「名字表示换 SmolStr」）。
type Name = Span<SmolStr>;

/// fresh meta 抽象的作用域掩码：`Bound` = 真依赖（解里要 λ 抽象），
/// `Defined` = 可展开的 let 定义（解里跳过该槽位）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BD {
    Bound,
    Defined,
}

/// 表面语法经 elaboration 产出的核心语法。
#[derive(Debug, Clone)]
enum Tm {
    Var(Ix),
    Lam(Name, Box<Tm>),
    App(Box<Tm>, Box<Tm>),
    U,
    Pi(Name, Box<Ty>, Box<Ty>),
    Let(Name, Box<Ty>, Box<Tm>, Box<Tm>),
    /// 显式引用的 meta（`rename` 产出：解里对其它 meta 的引用、以及
    /// `?m := ?m'` 一类解）。
    Meta(MetaVar),
    /// hole 处插入的 meta：抽象掉 elaboration 当时的全部 Bound 变量
    /// （`bds` 与求值环境平行，`Defined` 槽位跳过）。
    InsertedMeta(MetaVar, List<BD>),
}

type Ty = Tm;

// values
// --------------------------------------------------------------------------------

type Env = List<Val>;

/// 中性应用链：`?m a1 … an` / `x a1 … an` 的实参表（snoc：头 = 最后应用的实参）。
type Spine = List<Val>;

#[derive(Debug, Clone)]
struct Closure(Env, Box<Tm>);

/// 中性应用的两个子值用 `Rc` 共享：eval 查变量 clone 环境条目，而 let 绑定的
/// 中性链会被 β-级联反复引用——`Box` 树的 clone 是 O(子树) 深拷贝（church
/// 翻倍负载实测 O(n²)），`Rc` 的 clone 是引用计数（L02 教训 1，同款修复）。
#[derive(Debug, Clone)]
enum Val {
    /// 未解 meta 的中性应用链（已解的 meta 在 force 时展开成解值）。
    Flex(MetaVar, Spine),
    /// 局部变量的中性应用链。
    Rigid(Lvl, Spine),
    Lam(Name, Closure),
    Pi(Name, Box<VTy>, Closure),
    U,
}

type VTy = Val;

impl Val {
    fn vvar(x: Lvl) -> Self {
        Val::Rigid(x, List::new())
    }
}

fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
    Ix(l.0 - x.0 - 1)
}

// Elaboration
// --------------------------------------------------------------------------------

/// metacontext + 求值/引读/unification/elaboration（对应 Main.hs 的全局
/// IORef + 顶层函数束；Rust 版聚合为一个 struct，一次 elaboration 一个实例）。
#[derive(Debug)]
struct Infer {
    metas: Vec<MetaEntry>,
}

impl Infer {
    fn new() -> Self {
        Infer { metas: vec![] }
    }

    /// 挂新洞：metacontext 追加未解条目，产出应用到当前全部 Bound 槽位的
    /// `InsertedMeta`。
    fn fresh_meta(&mut self, cxt: &Cxt) -> Tm {
        self.metas.push(MetaEntry::Unsolved);
        Tm::InsertedMeta(MetaVar(self.metas.len() as u32 - 1), cxt.bds.clone())
    }

    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.metas[m.0 as usize]
    }

    /// `vMeta`：meta 的当前值（已解给解值，未解给 `?m`）。
    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v) => v.clone(),
            MetaEntry::Unsolved => Val::Flex(m, List::new()),
        }
    }

    /// `($$) (Closure env t) ~u = eval (u:env) t`。
    fn closure_apply(&self, clo: &Closure, u: Val) -> Val {
        self.eval(&clo.0.prepend(u), &clo.1)
    }

    fn v_app(&self, t: &Val, u: Val) -> Val {
        match t {
            Val::Lam(_, clo) => self.closure_apply(clo, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend(u)),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend(u)),
            _ => panic!("impossible"), // Π/U 不可应用（良类型项不会到达）
        }
    }

    /// `vAppSp t sp`：把 spine 里全部实参按应用顺序摔回 `t` 上。
    fn v_app_sp(&self, t: &Val, sp: &List<Val>) -> Val {
        match sp.head() {
            None => t.clone(),
            Some(u) => {
                let v = self.v_app_sp(t, &sp.tail());
                self.v_app(&v, u.clone())
            }
        }
    }

    /// `vAppBDs env ~v bds`：把 `v` 应用到环境里与 `Bound` 槽位对齐的值上
    /// （外层绑定先应用；`Defined` 槽位跳过）。
    fn v_app_bds(&self, env: &Env, v: Val, bds: &List<BD>) -> Val {
        match (env.head(), bds.head()) {
            (None, None) => v,
            (Some(_), Some(BD::Bound)) => {
                let v = self.v_app_bds(&env.tail(), v, &bds.tail());
                self.v_app(&v, env.head().unwrap().clone())
            }
            (Some(_), Some(BD::Defined)) => self.v_app_bds(&env.tail(), v, &bds.tail()),
            _ => panic!("impossible"), // env 与 bds 错位（空环境引带 binder 的 hole）
        }
    }

    fn eval(&self, env: &Env, tm: &Tm) -> Val {
        match tm {
            Tm::Var(Ix(x)) => env
                .iter()
                .nth(*x as usize)
                .expect("de Bruijn 越界：闭项不应查越深")
                .clone(),
            Tm::App(t, u) => {
                let v = self.eval(env, t);
                self.v_app(&v, self.eval(env, u))
            }
            Tm::Lam(x, t) => Val::Lam(x.clone(), Closure(env.clone(), t.clone())),
            Tm::Pi(x, a, b) => Val::Pi(
                x.clone(),
                Box::new(self.eval(env, a)),
                Closure(env.clone(), b.clone()),
            ),
            Tm::Let(_, _, t, u) => {
                let vt = self.eval(env, t);
                self.eval(&env.prepend(vt), u)
            }
            Tm::U => Val::U,
            Tm::Meta(m) => self.v_meta(*m),
            Tm::InsertedMeta(m, bds) => {
                let v = self.v_meta(*m);
                self.v_app_bds(env, v, bds)
            }
        }
    }

    /// **force**：把值更新到 metacontext 的当前状态（只展开到下一个不可再
    /// 解阻塞的头构造器，不下钻子值——模式匹配只需要头构造器，深展开会
    /// 重复做功）。unify/quote/rename 一律先 force 再分派。
    fn force(&self, t: &Val) -> Val {
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(*m) {
                MetaEntry::Solved(t_solved) => {
                    let v = self.v_app_sp(t_solved, sp);
                    self.force(&v)
                }
                MetaEntry::Unsolved => Val::Flex(*m, sp.clone()),
            },
            _ => t.clone(),
        }
    }

    fn quote_sp(&self, l: Lvl, t: Tm, sp: &List<Val>) -> Tm {
        match sp.head() {
            None => t,
            Some(u) => {
                let t = self.quote_sp(l, t, &sp.tail());
                Tm::App(Box::new(t), Box::new(self.quote(l, u)))
            }
        }
    }

    fn quote(&self, l: Lvl, v: &Val) -> Tm {
        let v = self.force(v);
        match v {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), &sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), &sp),
            Val::Lam(x, clo) => Tm::Lam(
                x,
                Box::new(self.quote(l + 1, &self.closure_apply(&clo, Val::vvar(l)))),
            ),
            Val::Pi(x, a, b) => Tm::Pi(
                x,
                Box::new(self.quote(l, &a)),
                Box::new(self.quote(l + 1, &self.closure_apply(&b, Val::vvar(l)))),
            ),
            Val::U => Tm::U,
        }
    }

    fn nf(&self, env: &Env, t: &Tm) -> Tm {
        let l = Lvl(env.len() as u32);
        self.quote(l, &self.eval(env, t))
    }

    // Pattern unification
    // --------------------------------------------------------------------------------

    /// `λ x1 x2. … body`：按解域大小包 λ（名字 x1、x2、…，只服务 pretty）。
    fn lams(&self, l: Lvl, t: Tm) -> Tm {
        fn go(x: u32, l: Lvl, t: Tm) -> Tm {
            if x == l.0 {
                t
            } else {
                let var_name = format!("x{}", x + 1);
                Tm::Lam(empty_span(var_name.into()), Box::new(go(x + 1, l, t)))
            }
        }
        go(0, l, t)
    }

    /// 把 spine 反演成 partial renaming（Γ 变量 → 解域位置）。spine 必须
    /// 由**互不相同的** rigid 变量构成，否则非模式问题，报 `UnifyError`。
    fn invert_go(&self, sp: &Spine) -> Result<(Lvl, HashMap<u32, Lvl>), UnifyError> {
        match sp.head() {
            None => Ok((Lvl(0), HashMap::new())),
            Some(t) => {
                let (dom, mut ren) = self.invert_go(&sp.tail())?;
                match self.force(t) {
                    Val::Rigid(x, sp2) if sp2.is_empty() && !ren.contains_key(&x.0) => {
                        ren.insert(x.0, dom);
                        Ok((dom + 1, ren))
                    }
                    _ => Err(UnifyError),
                }
            }
        }
    }

    fn invert(&self, gamma: Lvl, sp: &Spine) -> Result<PartialRenaming, UnifyError> {
        let (dom, ren) = self.invert_go(sp)?;
        Ok(PartialRenaming {
            dom,
            cod: gamma,
            ren,
        })
    }

    /// 对 rhs 执行 partial renaming，同时做 occurs check（`m` 出现在 rhs）
    /// 与 scope check（rhs 的自由变量不在 spine 里）。
    fn rename_go_sp(
        &self,
        m: MetaVar,
        pren: &PartialRenaming,
        t: Tm,
        sp: &List<Val>,
    ) -> Result<Tm, UnifyError> {
        match sp.head() {
            None => Ok(t),
            Some(u) => {
                let t = self.rename_go_sp(m, pren, t, &sp.tail())?;
                let u = self.rename_go(m, pren, u)?;
                Ok(Tm::App(Box::new(t), Box::new(u)))
            }
        }
    }

    fn rename_go(&self, m: MetaVar, pren: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
        let v = self.force(v);
        match v {
            // occurs check
            Val::Flex(m_prime, sp) if m == m_prime => Err(UnifyError),
            Val::Flex(m_prime, sp) => self.rename_go_sp(m, pren, Tm::Meta(m_prime), &sp),
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                // scope error（"escaping variable"）
                None => Err(UnifyError),
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_go_sp(m, pren, t, &sp)
                }
            },
            Val::Lam(x, clo) => {
                let t = self.rename_go(
                    m,
                    &lift(pren),
                    &self.closure_apply(&clo, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, Box::new(t)))
            }
            Val::Pi(x, a, b) => {
                let a = self.rename_go(m, pren, &a)?;
                let b = self.rename_go(
                    m,
                    &lift(pren),
                    &self.closure_apply(&b, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(x, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
        }
    }

    /// `Γ ⊢ ?m spine ≡ rhs` 的求解：`?m := λ spine⁻¹. rhs[spine⁻¹]`。
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: &Spine, rhs: &Val) -> Result<(), UnifyError> {
        let pren = self.invert(gamma, sp)?;
        let rhs = self.rename(m, &pren, rhs)?;
        let solution = self.eval(&List::new(), &self.lams(pren.dom, rhs));
        self.metas[m.0 as usize] = MetaEntry::Solved(solution);
        Ok(())
    }

    fn unify_sp(&mut self, l: Lvl, sp: &List<Val>, sp_prime: &List<Val>) -> Result<(), UnifyError> {
        match (sp.head(), sp_prime.head()) {
            (None, None) => Ok(()),
            (Some(_), Some(_)) => {
                self.unify_sp(l, &sp.tail(), &sp_prime.tail())?;
                self.unify(l, sp.head().unwrap(), sp_prime.head().unwrap())
            }
            _ => Err(UnifyError), // spine 长度不等
        }
    }

    /// unification：结构比较，遇到 `?m spine =? rhs` 形态的方程则求解。
    /// 分派次序与 Main.hs 一致（λ 情形 → U → Π → 同头中性 → 求解）。
    fn unify(&mut self, l: Lvl, t: &Val, u: &Val) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);
        match (&t, &u) {
            (Val::Lam(_, t_clo), Val::Lam(_, u_clo)) => self.unify(
                l + 1,
                &self.closure_apply(t_clo, Val::vvar(l)),
                &self.closure_apply(u_clo, Val::vvar(l)),
            ),
            (_, Val::Lam(_, u_clo)) => {
                let t2 = self.v_app(&t, Val::vvar(l));
                self.unify(l + 1, &t2, &self.closure_apply(u_clo, Val::vvar(l)))
            }
            (Val::Lam(_, t_clo), _) => {
                let u2 = self.v_app(&u, Val::vvar(l));
                self.unify(l + 1, &self.closure_apply(t_clo, Val::vvar(l)), &u2)
            }

            (Val::U, Val::U) => Ok(()),

            (Val::Pi(_, a, b), Val::Pi(_, a_prime, b_prime)) => {
                self.unify(l, a, a_prime)?;
                self.unify(
                    l + 1,
                    &self.closure_apply(b, Val::vvar(l)),
                    &self.closure_apply(b_prime, Val::vvar(l)),
                )
            }

            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, sp, sp_prime)
            }

            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.unify_sp(l, sp, sp_prime)
            }

            (Val::Flex(m, sp), _) => self.solve(l, *m, sp, &u),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(l, *m_prime, sp_prime, &t),

            _ => Err(UnifyError), // rigid 失配
        }
    }

    fn rename(&self, m: MetaVar, pren: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
        self.rename_go(m, pren, v)
    }

    // bidirectional algorithm:
    //   use check when the type is already known
    //   use infer if the type is unknown

    fn check(&mut self, cxt: &Cxt, t: &Raw, a: &VTy) -> Result<Tm, Error> {
        match (t, &self.force(a)) {
            (Raw::SrcPos(pos, t), _) => {
                let mut cxt = cxt.clone();
                cxt.pos = *pos;
                self.check(&cxt, t, a)
            }

            // (\x. t) : ((x : A) -> B)
            (Raw::Lam(x, t), Val::Pi(_, a, b)) => {
                let body = self.check(
                    &cxt.bind(x.clone(), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), Box::new(body)))
            }

            (Raw::Let(x, a, t, u), a_prime) => {
                let a = self.check(cxt, a, &Val::U)?;
                let va = self.eval(&cxt.env, &a);
                let t = self.check(cxt, t, &va)?;
                let vt = self.eval(&cxt.env, &t);
                let u = self.check(&cxt.define(x.clone(), vt, va), u, a_prime)?;
                Ok(Tm::Let(x.clone(), Box::new(a), Box::new(t), Box::new(u)))
            }

            // hole：直接以 fresh meta 填充（期望类型暂不约束它）
            (Raw::Hole, _) => Ok(self.fresh_meta(cxt)),

            (t, expected) => {
                let (t, tty) = self.infer(cxt, t)?;
                self.unify_catch(cxt, expected, &tty)?;
                Ok(t)
            }
        }
    }

    fn infer(&mut self, cxt: &Cxt, t: &Raw) -> Result<(Tm, VTy), Error> {
        match t {
            Raw::SrcPos(pos, t) => {
                let mut cxt = cxt.clone();
                cxt.pos = *pos;
                self.infer(&cxt, t)
            }

            Raw::Var(x) => {
                let mut i = 0u32;
                for (x2, a) in cxt.types.iter() {
                    if x.data == x2.data {
                        return Ok((Tm::Var(Ix(i)), a.clone()));
                    }
                    i += 1;
                }
                Err(report_at(cxt.pos, format!("Name not in scope: {}", x.data)))
            }

            Raw::U => Ok((Tm::U, Val::U)),

            Raw::Lam(x, t) => {
                // 定义域挂洞；余定义域闭包住当前环境（解可引用局部变量）
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, &new_meta);
                let (t, b) = self.infer(&cxt.bind(x.clone(), a.clone()), t)?;
                let b_closure = self.close_val(cxt, &b);
                Ok((Tm::Lam(x.clone(), Box::new(t)), Val::Pi(x.clone(), Box::new(a), b_closure)))
            }

            Raw::App(t, u) => {
                let (t, tty) = self.infer(cxt, t)?;
                // 确保 tty 是 Π：不是则挂一对洞（定义域 + 余定义域），
                // 用合成的 Π 与 tty 做 unification（可能求解出它们的值）
                let (a, b) = match self.force(&tty) {
                    Val::Pi(_, a, b) => (*a, b),
                    tty => {
                        let new_meta = self.fresh_meta(cxt);
                        let a = self.eval(&cxt.env, &new_meta);
                        let cod_meta = self.fresh_meta(&cxt.bind(empty_span("x".into()), a.clone()));
                        let b = Closure(cxt.env.clone(), Box::new(cod_meta));
                        self.unify_catch(cxt, &Val::Pi(empty_span("x".into()), Box::new(a.clone()), b.clone()), &tty)?;
                        (a, b)
                    }
                };
                let u = self.check(cxt, u, &a)?;
                let b_applied = self.closure_apply(&b, self.eval(&cxt.env, &u));
                Ok((Tm::App(Box::new(t), Box::new(u)), b_applied))
            }

            Raw::Pi(x, a, b) => {
                let a = self.check(cxt, a, &Val::U)?;
                let b = self.check(
                    &cxt.bind(x.clone(), self.eval(&cxt.env, &a)),
                    b,
                    &Val::U,
                )?;
                Ok((Tm::Pi(x.clone(), Box::new(a), Box::new(b)), Val::U))
            }

            Raw::Let(x, a, t, u) => {
                let a = self.check(cxt, a, &Val::U)?;
                let va = self.eval(&cxt.env, &a);
                let t = self.check(cxt, t, &va)?;
                let vt = self.eval(&cxt.env, &t);
                let (u, b) = self.infer(&cxt.define(x.clone(), vt, va), u)?;
                Ok((Tm::Let(x.clone(), Box::new(a), Box::new(t), Box::new(u)), b))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, &new_meta);
                let t = self.fresh_meta(cxt);
                Ok((t, a))
            }
        }
    }

    /// `closeVal`：把 Γ 下的值闭进 Closure（quote 在 `lvl + 1`——给即将到来的
    /// binder 留出第 0 槽）。
    fn close_val(&self, cxt: &Cxt, t: &Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Val, t_prime: &Val) -> Result<(), Error> {
        self.unify(cxt.lvl, t, t_prime).map_err(|_| {
            Error {
                msg: format!(
                    "Cannot unify expected type\n\n  {}\n\nwith inferred type\n\n  {}",
                    show_tm(cxt, &self.quote(cxt.lvl, t)),
                    show_tm(cxt, &self.quote(cxt.lvl, t_prime)),
                ),
                pos: cxt.pos,
            }
        })
    }

    /// `displayMetas`：metacontext 逐条打印（未解 `let ?m = ?;`，已解
    /// `let ?m = <nf>;`），末尾空行。`elab` 模式用。
    fn display_metas(&self) -> String {
        let mut out = String::new();
        for (m, e) in self.metas.iter().enumerate() {
            match e {
                MetaEntry::Unsolved => out.push_str(&format!("let ?{m} = ?;\n")),
                MetaEntry::Solved(v) => {
                    let quoted = self.quote(Lvl(0), v);
                    out.push_str(&format!("let ?{m} = {};\n", pretty_tm(0, &[], &quoted)))
                }
            }
        }
        out.push('\n');
        out
    }
}

// context
// --------------------------------------------------------------------------------

/// scope 里每一项的类型（头 = 最内层绑定；服务名字查找与报错 pretty）。
type Types = List<(Name, VTy)>;

/// Elaboration 上下文。`bds` 是 fresh meta 抽象的槽位掩码（与 env 平行）。
#[derive(Debug, Clone)]
struct Cxt {
    env: Env,
    types: Types,
    lvl: Lvl,
    bds: List<BD>,
    pos: Span<()>,
}

impl Cxt {
    fn empty(pos: Span<()>) -> Self {
        Cxt {
            env: List::new(),
            types: List::new(),
            lvl: Lvl(0),
            bds: List::new(),
            pos,
        }
    }

    /// Extend Cxt with a bound variable.
    fn bind(&self, x: Name, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            types: self.types.prepend((x, a)),
            lvl: self.lvl + 1,
            bds: self.bds.prepend(BD::Bound),
            pos: self.pos,
        }
    }

    /// Extend Cxt with a definition.
    fn define(&self, x: Name, t: VTy, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(t),
            types: self.types.prepend((x, a)),
            lvl: self.lvl + 1,
            bds: self.bds.prepend(BD::Defined),
            pos: self.pos,
        }
    }
}

// pattern renaming
// --------------------------------------------------------------------------------

/// partial renaming：`ren` 把 Γ 变量映射到解域位置；`dom`/`cod` 是两侧规模。
#[derive(Debug, Clone)]
struct PartialRenaming {
    dom: Lvl,               // size of Γ（解体所在的域 = spine 长度 + lift）
    cod: Lvl,               // size of Δ（rhs 所在的域）
    ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
}

/// Lifting a partial renaming over an extra bound variable.
fn lift(pren: &PartialRenaming) -> PartialRenaming {
    let mut ren = pren.ren.clone();
    ren.insert(pren.cod.0, pren.dom);
    PartialRenaming {
        dom: pren.dom + 1,
        cod: pren.cod + 1,
        ren,
    }
}

// printing
// --------------------------------------------------------------------------------

fn empty_span(data: SmolStr) -> Span<SmolStr> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

fn fresh(ns: &[String], x: &str) -> String {
    if x == "_" {
        "_".to_string()
    } else if ns.iter().any(|n| n == x) {
        fresh(ns, &format!("{x}'"))
    } else {
        x.to_string()
    }
}

// printing precedences
const ATOMP: usize = 3; // U, var, meta
const APPP: usize = 2; // application
const PIP: usize = 1; // pi
const LETP: usize = 0; // let, lambda

/// ns 按 Main.hs 的约定：**最内层 binder 在头部**（`x:ns` 前插），
/// `Var (Ix x) -> ns !! x`。
pub fn pretty_tm(prec: usize, ns: &[String], t: &Tm) -> String {
    let mut out = String::new();
    go(prec, ns, t, &mut out);
    out
}

fn show_tm(cxt: &Cxt, t: &Tm) -> String {
    let ns: Vec<String> = cxt.types.iter().map(|(x, _)| x.data.to_string()).collect();
    pretty_tm(0, &ns, t)
}

/// Wrap in parens if expression precedence is lower than enclosing precedence.
fn go(p: usize, ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Var(Ix(x)) => out.push_str(&ns[*x as usize]),

        Tm::App(t, u) => {
            let paren = APPP < p;
            if paren {
                out.push('(');
            }
            go(APPP, ns, t, out);
            out.push(' ');
            go(ATOMP, ns, u, out);
            if paren {
                out.push(')');
            }
        }

        Tm::Lam(name, body) => {
            let paren = LETP < p;
            if paren {
                out.push('(');
            }
            out.push_str("λ ");
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            out.push_str(&x);
            ns.insert(0, x);
            go_lam(&ns, body, out);
            if paren {
                out.push(')');
            }
        }

        Tm::U => out.push('U'),

        Tm::Pi(name, a, b) if name.data == "_" => {
            let paren = PIP < p;
            if paren {
                out.push('(');
            }
            go(APPP, ns, a, out);
            out.push_str(" → ");
            let mut ns = ns.to_vec();
            ns.insert(0, "_".to_string());
            go(PIP, &ns, b, out);
            if paren {
                out.push(')');
            }
        }

        Tm::Pi(name, a, b) => {
            let paren = PIP < p;
            if paren {
                out.push('(');
            }
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            pi_bind(&ns, &x, a, out);
            ns.insert(0, x);
            go_pi(&ns, b, out);
            if paren {
                out.push(')');
            }
        }

        Tm::Let(name, a, t, u) => {
            let paren = LETP < p;
            if paren {
                out.push('(');
            }
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            out.push_str("let ");
            out.push_str(&x);
            out.push_str(" : ");
            go(LETP, &ns, a, out);
            out.push_str("\n  = ");
            go(LETP, &ns, t, out);
            out.push_str(";\n\n");
            ns.insert(0, x);
            go(LETP, &ns, u, out);
            if paren {
                out.push(')');
            }
        }

        Tm::Meta(m) => out.push_str(&format!("?{m}")),

        // `?m` 应用到掩码里的 Bound 变量名（外层绑定在前；Defined 槽位跳过）
        Tm::InsertedMeta(m, bds) => go_bds(p, ns, m.0, bds, out),
    }
}

/// `goBDS`：`?m n_外 … n_内`（ns 与 bds 平行推进，`Defined` 跳名）。
fn go_bds(p: usize, ns: &[String], m: u32, bds: &List<BD>, out: &mut String) {
    match (ns.split_first(), bds.head()) {
        (None, None) => out.push_str(&format!("?{m}")),
        (Some((n, ns_tail)), Some(BD::Bound)) => {
            let paren = APPP < p;
            if paren {
                out.push('(');
            }
            go_bds(APPP, ns_tail, m, &bds.tail(), out);
            out.push(' ');
            out.push_str(n);
            if paren {
                out.push(')');
            }
        }
        (Some((_, ns_tail)), Some(BD::Defined)) => go_bds(APPP, ns_tail, m, &bds.tail(), out),
        _ => panic!("impossible"), // ns 与 bds 长度错位
    }
}

fn go_lam(ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Lam(name, body) => {
            out.push(' ');
            let x = fresh(ns, &name.data);
            out.push_str(&x);
            let mut ns = ns.to_vec();
            ns.insert(0, x);
            go_lam(&ns, body, out);
        }
        t => {
            out.push_str(". ");
            go(LETP, ns, t, out);
        }
    }
}

fn go_pi(ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Pi(name, a, b) if name.data == "_" => {
            out.push_str(" → ");
            go(APPP, ns, a, out);
            out.push_str(" → ");
            let mut ns = ns.to_vec();
            ns.insert(0, "_".to_string());
            go(PIP, &ns, b, out);
        }
        Tm::Pi(name, a, b) => {
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            pi_bind(&ns, &x, a, out);
            ns.insert(0, x);
            go_pi(&ns, b, out);
        }
        t => {
            out.push_str(" → ");
            go(PIP, ns, t, out);
        }
    }
}

fn pi_bind(ns: &[String], x: &str, a: &Tm, out: &mut String) {
    out.push('(');
    out.push_str(x);
    out.push_str(" : ");
    go(LETP, ns, a, out);
    out.push(')');
}

// errors & main
// --------------------------------------------------------------------------------

/// 类型检查错误：消息 + 当前源位置。
#[derive(Debug)]
pub struct Error {
    pub msg: String,
    pub pos: Span<()>,
}

fn report_at(pos: Span<()>, msg: String) -> Error {
    Error { msg, pos }
}

fn line_col(file: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (i, b) in file.bytes().enumerate() {
        if i >= offset {
            break;
        }
        if b == b'\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    (line, offset - line_start + 1)
}

/// Main.hs 的 `displayError`（megaparsec 风格的源码摘录 + caret）。
/// 位置来自 elaboration 时记录的最内层 `SrcPos`。
pub fn display_error(file: &str, err: &Error) -> String {
    let (linum, colnum) = line_col(file, err.pos.start_offset as usize);
    let lnum = linum.to_string();
    let lpad = " ".repeat(lnum.len());
    let line = file
        .split('\n')
        .nth(linum - 1)
        .unwrap_or("")
        .trim_end_matches('\r');
    format!(
        "(stdin):{}:{}:\n{} |\n{} | {}\n{} | {}^\n{}\n",
        linum,
        colnum,
        lpad,
        lnum,
        line,
        lpad,
        " ".repeat(colnum - 1),
        err.msg
    )
}

const HELP_MSG: &str = "usage: elabzoo-holes [--help|elab|nf|type]\n\
  \x20 --help : display this message\n\
  \x20 elab   : read & elaborate expression from stdin\n\
  \x20 nf     : read & typecheck expression from stdin, print its normal form and type\n\
  \x20 type   : read & typecheck expression from stdin, print its type\n";

fn initial_pos() -> Span<()> {
    Span {
        data: (),
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

/// Main.hs 的 `mainWith`：`--help` / `elab` / `nf` / `type` 四种模式，返回
/// 本应打印到 stdout 的全部文本（供测试断言）。nf/type 的 quote 用与
/// elaboration 同一个 `Infer`（metacontext 的解要在引读时生效）。
pub fn main_with(mode: &str, file: &str) -> String {
    match mode {
        "--help" => HELP_MSG.to_string(),
        "nf" | "type" | "elab" => match parser::parser(file, 0) {
            None => "parse error\n".to_string(),
            Some(t) => {
                let mut ty = Infer::new();
                match ty.infer(&Cxt::empty(initial_pos()), &t) {
                    Err(err) => display_error(file, &err),
                    Ok((t, a)) => match mode {
                        "nf" => format!(
                            "{}\n  :\n{}\n",
                            pretty_tm(0, &[], &ty.nf(&List::new(), &t)),
                            pretty_tm(0, &[], &ty.quote(Lvl(0), &a))
                        ),
                        "type" => format!("{}\n", pretty_tm(0, &[], &ty.quote(Lvl(0), &a))),
                        _ => {
                            let mut out = ty.display_metas();
                            out.push_str(&pretty_tm(0, &[], &t));
                            out.push('\n');
                            out
                        }
                    },
                }
            }
        },
        _ => HELP_MSG.to_string(),
    }
}

// examples
// --------------------------------------------------------------------------------

/// 上游模块注释的 id/id2 示例：`id _ x` 的洞在第二个实参的检查处被解
/// （`?α := λ x1 x2. x2`，即 `?α A x ≡ x`）。
pub const EX0_SRC: &str = "\
let id : (A : U) -> A -> A = λ A x. x;
let id2 : (A : U) -> A -> A = λ A x. id _ x;
U
";

/// 顶层洞作为实参：`id _ two` 的类型洞被解为 Nat。
pub const EX1_SRC: &str = "\
let id : (A : U) -> A -> A
  = \\A x. x;
let Nat : U = (N : U) -> (N -> N) -> N -> N;
let two : Nat = \\N s z. s (s z);
id _ two
";

/// holes 压力样例：List/Bool/Eq/church 编码全用 `_` 注类型洞。
pub const EX2_SRC: &str = "\
let id : (A : _) -> A -> A
  = \\A x. x;

let List : U -> U
  = \\A. (L : _) -> (A -> L -> L) -> L -> L;

let nil : (A : _) -> List A
  = \\A L cons nil. nil;

let cons : (A : _) -> A -> List A -> List A
  = \\A x xs L cons nil. cons x (xs _ cons nil);

let Bool : U
  = (B : _) -> B -> B -> B;

let true : Bool
  = \\B t f. t;

let false : Bool
  = \\B t f. f;

let not : Bool -> Bool
  = \\b B t f. b B f t;

let list1 : List Bool
  = cons _ (id _ true) (nil _);

let Eq : (A : _) -> A -> A -> U
  = \\A x y. (P : A -> U) -> P x -> P y;

let refl : (A : _)(x : A) -> Eq A x x
  = \\A x P px. px;

let list1 : List Bool
  = cons _ true (cons _ false (nil _));

let Nat  : U = (N : U) -> (N -> N) -> N -> N;
let five : Nat = \\N s z. s (s (s (s (s z))));
let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);
let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;

let ten      : Nat = add five five;
let hundred  : Nat = mul ten ten;
let thousand : Nat = mul ten hundred;

let eqTest : Eq _ hundred hundred = refl _ _;

eqTest
";

#[allow(non_snake_case)]
pub fn ex0() -> String {
    main_with("elab", EX0_SRC)
}

#[allow(non_snake_case)]
pub fn ex1() -> String {
    main_with("nf", EX1_SRC)
}

#[allow(non_snake_case)]
pub fn ex2() -> String {
    main_with("nf", EX2_SRC)
}

// benchmark entries（l03bench 用）
// --------------------------------------------------------------------------------

/// 基准口径：仅 check（conv/求解工作负载的 unification 发生在 check 里）。
pub(crate) fn bench_check(raw: &Raw) {
    let _ = Infer::new().infer(&Cxt::empty(initial_pos()), raw);
}

/// 基准口径：check + nf，产出丢弃。深 Box 树的递归析构会爆栈，基准里
/// mem::forget（进程退出统一回收；L01/L02 readme「已知限制」同款处理）。
pub(crate) fn bench_check_nf(raw: &Raw) {
    if let Ok((t, _)) = Infer::new().infer(&Cxt::empty(initial_pos()), raw) {
        let n = Infer::new().nf(&List::new(), &t);
        std::mem::forget(n);
    }
}

/// church n 的 nf-mode 期望输出（`λ N s z. s (s (… z))`）。
pub(crate) fn church_nf(n: usize) -> String {
    fn f(k: usize) -> String {
        match k {
            0 => "z".to_string(),
            1 => "s z".to_string(),
            k => format!("s ({})", f(k - 1)),
        }
    }
    format!("λ N s z. {}\n", f(n))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 上游注释示例的 elab 输出：`?0`（id2 体里的洞）被解为 `λ x1 x2. x1`
    /// ——`id _ x` 在第二实参 `x` 对 `?0 A x` 的检查处触发求解（解即
    /// 上游注释里的 `?α := λ A x. A`）。
    #[test]
    fn ex0_elab_solves_id2_hole() {
        assert_eq!(
            ex0(),
            "let ?0 = λ x1 x2. x1;\n\n\
             let id : (A : U) → A → A\n  = λ A x. x;\n\n\
             let id2 : (A : U) → A → A\n  = λ A x. id (?0 A x) x;\n\n\
             U\n"
        );
    }

    /// nf 模式：`id _ two` 的类型洞解为 Nat，项归约为 two 本身。
    #[test]
    fn ex1_nf() {
        assert_eq!(
            ex1(),
            "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
        );
    }

/// church 编码全用 `_` 注类型洞的样例：`eqTest` 的 nf 是 `λ P px. px`，
    /// 其类型展开里 `P hundred` 的两处 hundred 是完整的 church 100 展开
    /// （mul ten ten = s^10 迭代 10 次；求解 + 引读走完整条 neutral 链）。
    #[test]
    fn ex2_nf() {
        let out = ex2();
        // church n 展开（与 church_nf 同形，无尾换行）
        fn f(k: usize) -> String {
            match k {
                0 => "z".to_string(),
                1 => "s z".to_string(),
                k => format!("s ({})", f(k - 1)),
            }
        }
        let ch = format!("λ N s z. {}", f(100));
        // Nat 作为 Pi 的 dom 要括号：`(P : (Nat) → U)`，Nat = (N : U) → …
        assert_eq!(
            out,
            format!(
                "λ P px. px\n  :\n(P : ((N : U) → (N → N) → N → N) → U) → P ({ch}) → P ({ch})\n"
            )
        );
    }

    #[test]
    fn help_mode() {
        assert!(main_with("--help", "").starts_with("usage: elabzoo-holes"));
        assert!(main_with("bogus", "").starts_with("usage:"));
    }

    /// `type` 模式 + 顶层洞直接作项：`_ : ?0` 两个洞，均未解。
    #[test]
    fn type_mode_unsolved_hole() {
        let out = main_with("type", "_");
        assert_eq!(out, "?0\n");
        let out = main_with("elab", "_");
        assert_eq!(out, "let ?0 = ?;\nlet ?1 = ?;\n\n?1\n");
    }

    #[test]
    fn name_not_in_scope() {
        let out = main_with("type", "id");
        assert_eq!(
            out,
            r#"(stdin):1:1:
  |
1 | id
  | ^
Name not in scope: id
"#
        );
    }

    /// cannot unify：`id id` 的类型洞检查——期望 U，推断出函数类型。
    #[test]
    fn cannot_unify() {
        let src = "let id : (A : U) -> A -> A\n  = \\A x. x;\nlet bar : U = id id;\nbar\n";
        let out = main_with("nf", src);
        assert!(out.contains("Cannot unify expected type"), "{out}");
        assert!(out.contains("U"), "{out}");
        assert!(out.contains("(A : U) → A → A"), "{out}");
    }

    /// 匿名 binder：`_` 在 binder 位置只是名字，不产生 meta。
    #[test]
    fn underscore_binder_is_not_a_hole() {
        let out = main_with("type", "let f : U -> U -> U = \\x _. x;\nf");
        assert_eq!(out, "U → U → U\n");
    }

    /// 与性能版（bump_spine_iter）互检：所有示例的输出逐字节一致。
    #[test]
    fn fast_impl_matches_basic_on_examples() {
        for (name, src) in [
            ("ex0", EX0_SRC),
            ("ex1", EX1_SRC),
            ("ex2", EX2_SRC),
            ("hole arg", "let id : (A : U) -> A -> A\n  = \\A x. x;\nid _ _"),
            ("solve", "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
                       let zero : Nat = \\N s z. z;\n\
                       let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
                       let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
                       let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
                       let p0 : Nat = \\N s z. s (s z);\n\
                       let p1 : Nat = add p0 p0;\n\
                       let eqTest : Eq _ p1 p1 = refl _ _;\n\
                       eqTest\n"),
            // 同号 flex-flex 回归：`g w` 在 cod 位置被两处独立求值，同一未解
            // meta 以两个 spine 句柄（同实参）在 check fallthrough 的 unify
            // 相遇——必须逐实参比较（参考版 unifySpine）；曾误入 solve，
            // occurs check 必败而误报 Cannot unify ?m w ≡ ?m w。
            ("cod 双求值同号 flex-flex", "let g : (w : U) -> _ = \\w. _;\n\
                                          let f : (w : U) -> U -> g w = \\w x. _;\n\
                                          let test : (w : U) -> U -> g w = \\w x. f w x;\n\
                                          test\n"),
        ] {
            for mode in ["nf", "type", "elab"] {
                let basic = main_with(mode, src);
                let fast = bump_spine_iter::main_with(mode, src);
                assert_eq!(basic, fast, "mismatch on {name} ({mode})");
            }
        }
    }
}
