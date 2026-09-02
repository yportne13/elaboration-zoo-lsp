//! L04 — 隐式参数（elaboration zoo 上游 04-implicit-args 的 Rust 移植）。
//!
//! 本文件是**参考实现**（与上游一一对应：`Box<Tm>` 项、`List` Rc 持久环境、
//! 递归 eval/quote/force/unify/rename）；极致性能版见 [`bump_spine_iter`]
//! （L03 冠军配方的移植 + icit 穿线），两版输出逐字节一致（互检测试）。
//!
//! 与 L03（holes）的语义差别：
//! - `Icit`（Impl/Expl）穿线核心语法与值：`Lam`/`App`/`Pi` 与 spine 实参都
//!   携带 icit；Pi 比较要求 icit 相等，spine 实参比较忽略 icit（类型已定，
//!   上游 Unification.hs 同款）；
//! - **隐式参数插入**：infer 出的项在显式应用/检查前自动补 `?m` 实参
//!   （`insert`/`insert_t`），隐式 lambda 检查到隐式 Pi 时跳过插入；
//! - **命名隐式**：`t {x = u}` 实参与 `\{x = y}` lambda binder 按 Pi binder
//!   名字定位（`insert_until_name` / check 的命名守卫）；
//! - **Inserted binder**：检查非 lambda 项到隐式 Pi 时补的 binder 对源码
//!   名字不可见（`NameOrigin`：insert 处 `new_binder`，源码处 `bind`）；
//! - solve 的解体 λ 包裹的 icit 取自 meta spine（上游 `reverse $ map snd sp`：
//!   反转成应用序，最外层 λ 拿最先应用槽位的 icit——β 应用不看 icit，
//!   仅影响显示）。

pub(crate) mod bump_spine_iter;
pub(crate) mod parser;

use parser::{Either, Icit, Raw};

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

/// binder 名。`SmolStr`：≤23 字节内联存储，`clone` 免堆分配。
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
    Lam(Name, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    U,
    Pi(Name, Icit, Box<Ty>, Box<Ty>),
    Let(Name, Box<Ty>, Box<Tm>, Box<Tm>),
    /// 显式引用的 meta（`rename` 产出：解里对其它 meta 的引用）。
    Meta(MetaVar),
    /// hole 处插入的 meta：抽象掉 elaboration 当时的全部 Bound 变量
    /// （`bds` 与求值环境平行，`Defined` 槽位跳过）。
    InsertedMeta(MetaVar, List<BD>),
}

type Ty = Tm;

// values
// --------------------------------------------------------------------------------

type Env = List<Val>;

/// 中性应用链的实参表（snoc：头 = 最后应用的实参；icit 随实参携带）。
type Spine = List<(Val, Icit)>;

#[derive(Debug, Clone)]
struct Closure(Env, Box<Tm>);

/// 中性应用的两个子值用 `Rc` 共享（L02 教训 1，同 L03）。
#[derive(Debug, Clone)]
enum Val {
    /// 未解 meta 的中性应用链（已解的 meta 在 force 时展开成解值）。
    Flex(MetaVar, Spine),
    /// 局部变量的中性应用链。
    Rigid(Lvl, Spine),
    Lam(Name, Icit, Closure),
    Pi(Name, Icit, Box<VTy>, Closure),
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

/// metacontext + 求值/引读/unification/elaboration（一次 elaboration 一个实例）。
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

    /// `vApp t u i`：β 应用不看 icit，中性链把 `(u, i)` 记进 spine。
    fn v_app(&self, t: &Val, u: Val, i: Icit) -> Val {
        match t {
            Val::Lam(_, _, clo) => self.closure_apply(clo, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))),
            _ => panic!("impossible"), // Π/U 不可应用（良类型项不会到达）
        }
    }

    /// `vAppSp t sp`：把 spine 里全部实参按应用顺序摔回 `t` 上。
    fn v_app_sp(&self, t: &Val, sp: &Spine) -> Val {
        match sp.head() {
            None => t.clone(),
            Some((u, i)) => {
                let v = self.v_app_sp(t, &sp.tail());
                self.v_app(&v, u.clone(), *i)
            }
        }
    }

    /// `vAppBDs env ~v bds`：把 `v` 应用到环境里与 `Bound` 槽位对齐的值上
    /// （外层绑定先应用；`Defined` 槽位跳过；icit 硬编码 Expl——上游同款，
    /// 解体 λ 的 icit 另取自 spine）。
    fn v_app_bds(&self, env: &Env, v: Val, bds: &List<BD>) -> Val {
        match (env.head(), bds.head()) {
            (None, None) => v,
            (Some(_), Some(BD::Bound)) => {
                let v = self.v_app_bds(&env.tail(), v, &bds.tail());
                self.v_app(&v, env.head().unwrap().clone(), Icit::Expl)
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
            Tm::App(t, u, i) => {
                let v = self.eval(env, t);
                self.v_app(&v, self.eval(env, u), *i)
            }
            Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone())),
            Tm::Pi(x, i, a, b) => Val::Pi(
                x.clone(),
                *i,
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
    /// 解阻塞的头构造器）。unify/quote/rename 一律先 force 再分派。
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

    fn quote_sp(&self, l: Lvl, t: Tm, sp: &Spine) -> Tm {
        match sp.head() {
            None => t,
            Some((u, i)) => {
                let t = self.quote_sp(l, t, &sp.tail());
                Tm::App(Box::new(t), Box::new(self.quote(l, u)), *i)
            }
        }
    }

    fn quote(&self, l: Lvl, v: &Val) -> Tm {
        let v = self.force(v);
        match v {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), &sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), &sp),
            Val::Lam(x, i, clo) => Tm::Lam(
                x,
                i,
                Box::new(self.quote(l + 1, &self.closure_apply(&clo, Val::vvar(l)))),
            ),
            Val::Pi(x, i, a, b) => Tm::Pi(
                x,
                i,
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

    /// `λ x1 x2. … body`：icit 取 meta spine **收集序反转**（应用序——
    /// 上游 `lams (reverse $ map snd sp)`：spine 头 = 最后应用的实参，
    /// 反转后最外层 λ 取最先应用槽位的 icit；β 不看 icit，仅影响解的
    /// 显示）。
    fn lams(&self, icits: &[Icit], t: Tm) -> Tm {
        fn go(x: u32, icits: &[Icit], t: Tm) -> Tm {
            match icits.split_first() {
                None => t,
                Some((i, rest)) => Tm::Lam(
                    empty_span(SmolStr::from(format!("x{}", x + 1))),
                    *i,
                    Box::new(go(x + 1, rest, t)),
                ),
            }
        }
        go(0, icits, t)
    }

    /// 把 spine 反演成 partial renaming（Γ 变量 → 解域位置）。spine 必须
    /// 由**互不相同的** rigid 变量构成（icit 不参与——上游 invert 丢弃之）。
    fn invert_go(&self, sp: &Spine) -> Result<(Lvl, HashMap<u32, Lvl>), UnifyError> {
        match sp.head() {
            None => Ok((Lvl(0), HashMap::new())),
            Some((t, _)) => {
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
        Ok(PartialRenaming { dom, cod: gamma, ren })
    }

    /// 对 rhs 执行 partial renaming，同时做 occurs check 与 scope check。
    fn rename_go_sp(
        &self,
        m: MetaVar,
        pren: &PartialRenaming,
        t: Tm,
        sp: &Spine,
    ) -> Result<Tm, UnifyError> {
        match sp.head() {
            None => Ok(t),
            Some((u, i)) => {
                let t = self.rename_go_sp(m, pren, t, &sp.tail())?;
                let u = self.rename_go(m, pren, u)?;
                Ok(Tm::App(Box::new(t), Box::new(u), *i))
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
            Val::Lam(x, i, clo) => {
                let t = self.rename_go(
                    m,
                    &lift(pren),
                    &self.closure_apply(&clo, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(x, i, Box::new(t)))
            }
            Val::Pi(x, i, a, b) => {
                let a = self.rename_go(m, pren, &a)?;
                let b = self.rename_go(
                    m,
                    &lift(pren),
                    &self.closure_apply(&b, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
        }
    }

    /// `Γ ⊢ ?m spine ≡ rhs` 的求解：`?m := λ spine⁻¹. rhs[spine⁻¹]`。
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: &Spine, rhs: &Val) -> Result<(), UnifyError> {
        let pren = self.invert(gamma, sp)?;
        let rhs = self.rename(m, &pren, rhs)?;
        // spine 头 = 最后应用的实参；反转成应用序——最外层 λ 取最先应用
        // 槽位的 icit（上游 `lams (reverse $ map snd sp)` 同款）
        let mut icits: Vec<Icit> = sp.iter().map(|(_, i)| *i).collect();
        icits.reverse();
        let solution = self.eval(&List::new(), &self.lams(&icits, rhs));
        self.metas[m.0 as usize] = MetaEntry::Solved(solution);
        Ok(())
    }

    /// 同头中性的逐实参比较（icit 不比：类型已定，上游同款）。
    fn unify_sp(&mut self, l: Lvl, sp: &Spine, sp_prime: &Spine) -> Result<(), UnifyError> {
        match (sp.head(), sp_prime.head()) {
            (None, None) => Ok(()),
            (Some(_), Some(_)) => {
                self.unify_sp(l, &sp.tail(), &sp_prime.tail())?;
                self.unify(l, &sp.head().unwrap().0, &sp_prime.head().unwrap().0)
            }
            _ => Err(UnifyError), // spine 长度不等
        }
    }

    /// unification：结构比较，遇到 `?m spine =? rhs` 形态的方程则求解。
    /// 分派次序与上游一致（λ 情形 → U → Π（icit 相等）→ 同头中性 → 求解）。
    fn unify(&mut self, l: Lvl, t: &Val, u: &Val) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);
        match (&t, &u) {
            (Val::Lam(_, _, t_clo), Val::Lam(_, _, u_clo)) => self.unify(
                l + 1,
                &self.closure_apply(t_clo, Val::vvar(l)),
                &self.closure_apply(u_clo, Val::vvar(l)),
            ),
            // η：按 λ 一侧的 icit 应用中性一侧
            (_, Val::Lam(_, i, u_clo)) => {
                let t2 = self.v_app(&t, Val::vvar(l), *i);
                self.unify(l + 1, &t2, &self.closure_apply(u_clo, Val::vvar(l)))
            }
            (Val::Lam(_, i, t_clo), _) => {
                let u2 = self.v_app(&u, Val::vvar(l), *i);
                self.unify(l + 1, &self.closure_apply(t_clo, Val::vvar(l)), &u2)
            }

            (Val::U, Val::U) => Ok(()),

            (Val::Pi(_, i, a, b), Val::Pi(_, i_prime, a_prime, b_prime)) if i == i_prime => {
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

            _ => Err(UnifyError), // rigid 失配 / Pi icit 失配
        }
    }

    fn rename(&self, m: MetaVar, pren: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
        self.rename_go(m, pren, v)
    }

    // bidirectional algorithm:
    //   use check when the type is already known
    //   use infer if the type is unknown

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参（上游 `insert'`）。
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: &Val) -> (Tm, VTy) {
        match self.force(va) {
            Val::Pi(_, Icit::Impl, _, b) => {
                let m = self.fresh_meta(cxt);
                let mv = self.eval(&cxt.env, &m);
                let va = self.closure_apply(&b, mv);
                self.insert_go(cxt, Tm::App(Box::new(t), Box::new(m), Icit::Impl), &va)
            }
            va => (t, va),
        }
    }

    /// infer 后无条件插入（上游 `insert'` 的 Result 包装）。
    fn insert_t(&mut self, cxt: &Cxt, t: Tm, va: VTy) -> Result<(Tm, VTy), Error> {
        Ok(self.insert_go(cxt, t, &va))
    }

    /// infer 后插入，但隐式 lambda 本身免插（`\{A} x. …` 已显式拿住隐式
    /// binder，再插就是多余应用）。
    fn insert(&mut self, cxt: &Cxt, t: Tm, va: VTy) -> Result<(Tm, VTy), Error> {
        match &t {
            Tm::Lam(_, Icit::Impl, _) => Ok((t, va)),
            _ => self.insert_t(cxt, t, va),
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止；类型的隐式
    /// 前缀耗尽仍无匹配 → `NoNamedImplicitArg`。
    fn insert_until_go(
        &mut self,
        cxt: &Cxt,
        name: &Span<SmolStr>,
        t: Tm,
        va: &Val,
    ) -> Result<(Tm, VTy), Error> {
        match self.force(va) {
            Val::Pi(x, Icit::Impl, a, b) => {
                if x.data == name.data {
                    Ok((t, Val::Pi(x, Icit::Impl, a, b)))
                } else {
                    let m = self.fresh_meta(cxt);
                    let mv = self.eval(&cxt.env, &m);
                    let va = self.closure_apply(&b, mv);
                    self.insert_until_go(
                        cxt,
                        name,
                        Tm::App(Box::new(t), Box::new(m), Icit::Impl),
                        &va,
                    )
                }
            }
            _ => Err(report_at(
                cxt.pos,
                format!("No named implicit argument with name {}", name.data),
            )),
        }
    }

    fn insert_until_name(
        &mut self,
        cxt: &Cxt,
        name: &Span<SmolStr>,
        t: Tm,
        va: VTy,
    ) -> Result<(Tm, VTy), Error> {
        self.insert_until_go(cxt, name, t, &va)
    }

    fn check(&mut self, cxt: &Cxt, t: &Raw, a: &VTy) -> Result<Tm, Error> {
        match (t, &self.force(a)) {
            (Raw::SrcPos(pos, t), _) => {
                let mut cxt = cxt.clone();
                cxt.pos = *pos;
                self.check(&cxt, t, a)
            }

            // binder 形态与 Π 的 icit 匹配：位置 binder 要求 icit 相等，
            // 命名 binder（\{x = y}）要求**Pi binder 名**相等且 Π 为隐式
            // （上游 `either (\x -> x == x' && i' == Impl) (== i') i`——
            // 匹配的 Either Name 是引用名，Pi 名才是被匹配方）。
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b))
                if match i {
                    Either::Name(n) => n.data == x_t.data && *i_t == Icit::Impl,
                    &Either::Icit(j) => j == *i_t,
                } =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), *i_t, Box::new(body)))
            }

            // 非 lambda 项检查到隐式 Π：插入隐式 binder（对源码名不可见）
            (t, Val::Pi(x, Icit::Impl, a, b)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), Icit::Impl, Box::new(body)))
            }

            (Raw::Let(x, a, t, u), a_prime) => {
                let a = self.check(cxt, a, &Val::U)?;
                let va = self.eval(&cxt.env, &a);
                let t = self.check(cxt, t, &va)?;
                let vt = self.eval(&cxt.env, &t);
                let u = self.check(&cxt.define(x.clone(), vt, va), u, a_prime)?;
                Ok(Tm::Let(x.clone(), Box::new(a), Box::new(t), Box::new(u)))
            }

            // hole：直接以 fresh meta 填充
            (Raw::Hole, _) => Ok(self.fresh_meta(cxt)),

            (t, expected) => {
                let (t, tty) = self.infer(cxt, t)?;
                let (t, tty) = self.insert(cxt, t, tty)?;
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
                for (x2, origin, a) in cxt.types.iter() {
                    // inserted binder 对源码名字不可见
                    if x.data == x2.data && *origin == NameOrigin::Source {
                        return Ok((Tm::Var(Ix(i)), a.clone()));
                    }
                    i += 1;
                }
                Err(report_at(cxt.pos, format!("Name not in scope: {}", x.data)))
            }

            Raw::U => Ok((Tm::U, Val::U)),

            Raw::Lam(x, Either::Icit(i), t) => {
                // 定义域挂洞；余定义域闭包住当前环境（解可引用局部变量）。
                // 体推断后在**扩展后**的上下文里 insert（上游 `insert cxt'`）。
                let new_meta = self.fresh_meta(cxt);
                let a = self.eval(&cxt.env, &new_meta);
                let cxt1 = cxt.bind(x.clone(), a.clone());
                let (t, b) = self.infer(&cxt1, t)?;
                let (t, b) = self.insert(&cxt1, t, b)?;
                let b_closure = self.close_val(cxt, &b);
                Ok((
                    Tm::Lam(x.clone(), *i, Box::new(t)),
                    Val::Pi(x.clone(), *i, Box::new(a), b_closure),
                ))
            }

            Raw::Lam(_, Either::Name(_), _) => Err(report_at(
                cxt.pos,
                "Cannot infer type for lambda with named argument".to_string(),
            )),

            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用（显式给隐式）；位置 Expl → 先 insert_t。
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer(cxt, t)?;
                        let (t, tty) = self.insert_until_name(cxt, name, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    &Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer(cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    &Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer(cxt, t)?;
                        let (t, tty) = self.insert_t(cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let (a, b) = match self.force(&tty) {
                    Val::Pi(_, i_t, a, b) if i_t == i => ((*a).clone(), b.clone()),
                    Val::Pi(_, i_t, _, _) => {
                        return Err(report_at(
                            cxt.pos,
                            format!(
                                "Function icitness mismatch: expected {}, got {}.",
                                show_icit(i),
                                show_icit(i_t)
                            ),
                        ))
                    }
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder 用普通 bind + 名字 "x"（上游同款）。
                    tty => {
                        let new_meta = self.fresh_meta(cxt);
                        let a = self.eval(&cxt.env, &new_meta);
                        let cod_meta = self.fresh_meta(&cxt.bind(empty_span("x".into()), a.clone()));
                        let b = Closure(cxt.env.clone(), Box::new(cod_meta));
                        self.unify_catch(
                            cxt,
                            &tty,
                            &Val::Pi(empty_span("x".into()), i, Box::new(a.clone()), b.clone()),
                        )?;
                        (a, b)
                    }
                };
                let u = self.check(cxt, u, &a)?;
                let b_applied = self.closure_apply(&b, self.eval(&cxt.env, &u));
                Ok((Tm::App(Box::new(t), Box::new(u), i), b_applied))
            }

            Raw::Pi(x, i, a, b) => {
                let a = self.check(cxt, a, &Val::U)?;
                let b = self.check(
                    &cxt.bind(x.clone(), self.eval(&cxt.env, &a)),
                    b,
                    &Val::U,
                )?;
                Ok((Tm::Pi(x.clone(), *i, Box::new(a), Box::new(b)), Val::U))
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

    /// `closeVal`：把 Γ 下的值闭进 Closure（quote 在 `lvl + 1`）。
    fn close_val(&self, cxt: &Cxt, t: &Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Val, t_prime: &Val) -> Result<(), Error> {
        self.unify(cxt.lvl, t, t_prime).map_err(|_| Error {
            msg: format!(
                "Cannot unify expected type\n\n  {}\n\nwith inferred type\n\n  {}",
                show_tm(cxt, &self.quote(cxt.lvl, t)),
                show_tm(cxt, &self.quote(cxt.lvl, t_prime)),
            ),
            pos: cxt.pos,
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

/// binder 的来源：`Source` = 源码写出的（名字可被 `Raw::Var` 引用），
/// `Inserted` = elaboration 补插的隐式 binder（对源码名字不可见）。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NameOrigin {
    Inserted,
    Source,
}

/// scope 里每一项（名字、来源、类型；头 = 最内层绑定）。
type Types = List<(Name, NameOrigin, VTy)>;

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

    /// Extend Cxt with a bound variable（源码 binder）。
    fn bind(&self, x: Name, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            types: self.types.prepend((x, NameOrigin::Source, a)),
            lvl: self.lvl + 1,
            bds: self.bds.prepend(BD::Bound),
            pos: self.pos,
        }
    }

    /// Extend Cxt with an inserted implicit binder（对源码名不可见）。
    fn new_binder(&self, x: Name, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            types: self.types.prepend((x, NameOrigin::Inserted, a)),
            lvl: self.lvl + 1,
            bds: self.bds.prepend(BD::Bound),
            pos: self.pos,
        }
    }

    /// Extend Cxt with a definition.
    fn define(&self, x: Name, t: VTy, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(t),
            types: self.types.prepend((x, NameOrigin::Source, a)),
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

/// `Show Icit`（上游 Common.hs）：`implicit` / `explicit`。
pub(crate) fn show_icit(i: Icit) -> &'static str {
    match i {
        Icit::Impl => "implicit",
        Icit::Expl => "explicit",
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

/// ns 按 Main.hs 的约定：**最内层 binder 在头部**，`Var (Ix x) -> ns !! x`。
pub fn pretty_tm(prec: usize, ns: &[String], t: &Tm) -> String {
    let mut out = String::new();
    go(prec, ns, t, &mut out);
    out
}

fn show_tm(cxt: &Cxt, t: &Tm) -> String {
    let ns: Vec<String> = cxt.types.iter().map(|(x, _, _)| x.data.to_string()).collect();
    pretty_tm(0, &ns, t)
}

/// Wrap in parens if expression precedence is lower than enclosing precedence.
fn go(p: usize, ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Var(Ix(x)) => out.push_str(&ns[*x as usize]),

        // 显式实参按 atom 优先级；隐式实参裹 `{}`（内部 let 优先级，不再加括号）
        Tm::App(t, u, i) => {
            let paren = APPP < p;
            if paren {
                out.push('(');
            }
            go(APPP, ns, t, out);
            out.push(' ');
            match i {
                Icit::Expl => go(ATOMP, ns, u, out),
                Icit::Impl => {
                    out.push('{');
                    go(LETP, ns, u, out);
                    out.push('}');
                }
            }
            if paren {
                out.push(')');
            }
        }

        Tm::Lam(name, i, body) => {
            let paren = LETP < p;
            if paren {
                out.push('(');
            }
            out.push_str("λ ");
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            match i {
                Icit::Expl => out.push_str(&x),
                Icit::Impl => {
                    out.push('{');
                    out.push_str(&x);
                    out.push('}');
                }
            }
            ns.insert(0, x);
            go_lam(&ns, body, out);
            if paren {
                out.push(')');
            }
        }

        Tm::U => out.push('U'),

        // 非依赖显式 Pi 的箭头简写（上游仅对 `"_"` + Expl）
        Tm::Pi(name, Icit::Expl, a, b) if name.data == "_" => {
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

        Tm::Pi(name, i, a, b) => {
            let paren = PIP < p;
            if paren {
                out.push('(');
            }
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            pi_bind(&ns, &x, *i, a, out);
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

        // `?m` 应用到掩码里的 Bound 变量名（外层绑定在前；Defined 槽位跳名）
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
        Tm::Lam(name, i, body) => {
            out.push(' ');
            let x = fresh(ns, &name.data);
            match i {
                Icit::Expl => out.push_str(&x),
                Icit::Impl => {
                    out.push('{');
                    out.push_str(&x);
                    out.push('}');
                }
            }
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

/// Π 链：后续 binder 的 fresh 名 ≠ `"_"` 才续链（上游 goPi 守卫），否则
/// 落回箭头形（`"_"` binder 由 `go` 的 Expl 简写或 `{_ : A}` 处理）。
fn go_pi(ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Pi(name, i, a, b) if name.data != "_" => {
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            pi_bind(&ns, &x, *i, a, out);
            ns.insert(0, x);
            go_pi(&ns, b, out);
        }
        t => {
            out.push_str(" → ");
            go(PIP, ns, t, out);
        }
    }
}

/// Pi binder：显式 `(x : A)`，隐式 `{x : A}`。
fn pi_bind(ns: &[String], x: &str, i: Icit, a: &Tm, out: &mut String) {
    match i {
        Icit::Expl => {
            out.push('(');
            out.push_str(x);
            out.push_str(" : ");
            go(LETP, ns, a, out);
            out.push(')');
        }
        Icit::Impl => {
            out.push('{');
            out.push_str(x);
            out.push_str(" : ");
            go(LETP, ns, a, out);
            out.push('}');
        }
    }
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

const HELP_MSG: &str = "usage: elabzoo-implicit-args [--help|elab|nf|type]\n\
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
/// 本应打印到 stdout 的全部文本（供测试断言）。
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

/// 隐式插入的最小样例：`id` 的隐式 `A` 在应用处自动补 meta 并解出。
pub const EX0_SRC: &str = "\
let id : {A : U} -> A -> A = \\x. x;
let id2 : {A : U} -> A -> A = \\x. id x;
U
";

/// 上游 04 readme 的示例套件（命名隐式实参/命名 lambda、List/map/comp、
/// church 编码的 mul、Eq/refl/sym——隐式插入 + 求解的全谱覆盖）。
pub const EX1_SRC: &str = "\
let id : {A : U} -> A -> A = \\x. x;

let const : {A B} -> A -> B -> A = \\x y. x;

let the : (A : _) -> A -> A = \\_ x. x;

let argTest1 = const {U}{U} U;

let argTest2 = const {B = U} U;

let id2 : {A} -> A -> A = \\{A} x. x;

let namedLam  : {A B C} -> A -> B -> C -> A = \\{B = B} a b c. a;

let insert : {A} -> A -> A = id;

let noinsert = \\{A} x. the A x;

let insert2 = (\\{A} x. the A x) U;

let Bool : U
    = (B : _) -> B -> B -> B;
let true : Bool
    = \\B t f. t;
let false : Bool
    = \\B t f. f;

let List : U -> U
    = \\A. (L : _) -> (A -> L -> L) -> L -> L;
let nil : {A} -> List A
    = \\L cons nil. nil;
let cons : {A} -> A -> List A -> List A
    = \\x xs L cons nil. cons x (xs L cons nil);
let map : {A B} -> (A -> B) -> List A -> List B
    = \\{A}{B} f xs L c n. xs L (\\a. c (f a)) n;

let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
           (f : {a}(b : B a) -> C b)
           (g : (a : A) -> B a)
           (a : A)
           -> C (g a)
    = \\f g a. f (g a);

let compExample = comp (cons true) (cons false) nil;

let Nat : U
    = (N : U) -> (N -> N) -> N -> N;
let mul : Nat -> Nat -> Nat
    = \\a b N s z. a _ (b _ s) z;
let ten : Nat
    = \\N s z. s (s (s (s (s (s (s (s (s (s z)))))))));
let hundred = mul ten ten;

let Eq : {A} -> A -> A -> U
    = \\{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A}{x : A} -> Eq x x
    = \\_ px. px;

the (Eq (mul ten ten) hundred) refl
";

#[allow(non_snake_case)]
pub fn ex0() -> String {
    main_with("elab", EX0_SRC)
}

#[allow(non_snake_case)]
pub fn ex1() -> String {
    main_with("nf", EX1_SRC)
}

// benchmark entries（l04bench 用）
// --------------------------------------------------------------------------------

/// 基准口径：仅 check（插入/求解工作负载的 unification 发生在 check 里）。
pub(crate) fn bench_check(raw: &Raw) {
    let _ = Infer::new().infer(&Cxt::empty(initial_pos()), raw);
}

/// 基准口径：check + nf，产出丢弃（深 Box 树的递归析构会爆栈，基准里
/// mem::forget——L03 同款处理）。
pub(crate) fn bench_check_nf(raw: &Raw) {
    let mut inf = Infer::new();
    if let Ok((t, _)) = inf.infer(&Cxt::empty(initial_pos()), raw) {
        let n = inf.nf(&List::new(), &t);
        std::mem::forget(n);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// help 模式。
    #[test]
    fn help_mode() {
        assert!(main_with("--help", "").starts_with("usage: elabzoo-implicit-args"));
        assert!(main_with("bogus", "").starts_with("usage:"));
    }

    /// 名字越界：inserted binder 对源码不可见（这里直接查未定义名）。
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

    /// icit 失配：`{u}` 隐式实参应用到显式 Pi 头。（反方向不可达：Expl 分支
    /// 先 insert_t 吞掉全部隐式前缀，残存隐式 Pi 不会走到失配判断。）
    #[test]
    fn icit_mismatch() {
        let src = "let g : U -> U -> U = \\x y. x;\ng {U}";
        let out = main_with("type", src);
        assert!(
            out.contains("Function icitness mismatch: expected implicit, got explicit."),
            "{out}"
        );
    }

    /// 混合 icit 的 solve：spine = [(v0, Expl), (v1, Impl)]（v0 最后应用）、
    /// rhs = ((v1 {v0}) v0)（内层 Impl、外层 Expl）。App 重建须位置配对
    /// （内层 App 拿内层槽位的 Impl），λ 标签取应用序（最外层 λ {x1} 配
    /// 最先应用槽位的 Impl）——上游 `renameGoSp` 的 `pure i` 与
    /// `lams (reverse $ map snd sp)` 同款。
    #[test]
    fn solve_mixed_icit_order() {
        let mut inf = Infer::new();
        inf.metas.push(MetaEntry::Unsolved);
        let sp_inner = List::new().prepend((Val::vvar(Lvl(0)), Icit::Impl));
        let app_inner = Val::Rigid(Lvl(1), sp_inner);
        let sp_outer = List::new()
            .prepend((Val::vvar(Lvl(0)), Icit::Impl))
            .prepend((Val::vvar(Lvl(0)), Icit::Expl));
        let rhs = Val::Rigid(Lvl(1), sp_outer);
        let msp = List::new()
            .prepend((Val::vvar(Lvl(1)), Icit::Impl))
            .prepend((Val::vvar(Lvl(0)), Icit::Expl));
        inf.solve(Lvl(2), MetaVar(0), &msp, &rhs).expect("solve 失败");
        let q = inf.quote(Lvl(0), &inf.v_meta(MetaVar(0)));
        assert_eq!(pretty_tm(0, &[], &q), "λ {x1} x2. x1 {x2} x2");
    }

    /// 命名隐式实参找不到同名 Pi binder。
    #[test]
    fn no_named_implicit_arg() {
        let src = "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {C = U} U U\n";
        let out = main_with("type", src);
        assert!(
            out.contains("No named implicit argument with name C"),
            "{out}"
        );
    }

    /// 命名隐式 lambda 不可推断。
    #[test]
    fn infer_named_lambda() {
        let out = main_with("type", "\\{B = x} y. y");
        assert!(
            out.contains("Cannot infer type for lambda with named argument"),
            "{out}"
        );
    }

    /// EX1 全套件类型检查通过（nf = refl 的展开；匿名 binder `_` 保持 `_`）。
    #[test]
    fn ex1_zoo_suite_typechecks() {
        let out = main_with("nf", EX1_SRC);
        assert!(out.starts_with("λ _ px. px\n"), "{out}");
    }

    /// EX0：`id x` 的隐式 A 插入被解为 lambda binder（elab 显示解）。
    /// `?0` 的 spine 是（应用序）`A x`，解 `λ x1 x2. x1`（x1 收 A）；
    /// id2 检查到隐式 Pi 补了 inserted binder `λ {A}`。
    #[test]
    fn ex0_elab() {
        let out = ex0();
        assert!(out.contains("let ?0 = λ x1 x2. x1;\n"), "{out}");
        assert!(
            out.contains("let id : {A : U} → A → A\n  = λ {A} x. x;\n"),
            "{out}"
        );
        assert!(
            out.contains("let id2 : {A : U} → A → A\n  = λ {A} x. id {?0 A x} x;\n"),
            "{out}"
        );
    }

    /// 与性能版（bump_spine_iter）互检：示例与隐式特例的三模式输出
    /// 逐字节一致。
    #[test]
    fn fast_impl_matches_basic_on_examples() {
        for (name, src) in [
            ("ex0", EX0_SRC),
            ("ex1", EX1_SRC),
            ("named arg", "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {B = U} U U\n"),
            ("icit mismatch", "let g : U -> U -> U = \\x y. x;\ng {U}"),
            ("noinsert", "let the : (A : _) -> A -> A = \\_ x. x;\nlet noinsert = \\{A} x. the A x;\nU\n"),
            // comp：`B (?m …)` 形态（中性头应用到中性实参）——L04 移除
            // unify 长度 fail-fast 的回归样例（隐式插入大量制造该形态）
            ("comp neutral-on-neutral", "\
             let comp : {A}{B : A -> U}{C : {a} -> B a -> U}\n\
                        (f : {a}(b : B a) -> C b)\n\
                        (g : (a : A) -> B a)\n\
                        (a : A)\n\
                        -> C (g a)\n\
                 = \\f g a. f (g a);\n\
             U\n"),
            // 同号 flex-flex（cod 双求值形态，L03 e541de0 的隐式版）：
            // `g w` 的两个隐式插入 meta 在 cod 位置被独立求值后相遇
            ("cod 双求值同号 flex-flex", "\
             let g : {w : U} -> _ = \\w. _;\n\
             let f : {w : U} -> U -> g {w} = \\w x. _;\n\
             let test : {w : U} -> U -> g {w} = \\w x. f {w} x;\n\
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
