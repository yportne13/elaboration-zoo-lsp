//! L05 — meta 探测（pruning）：elaboration zoo 上游 `05-pruning` 的 Rust 移植。
//!
//! 本文件是**参考实现**（与上游一一对应：`Box<Tm>` 项、`List` Rc 持久环境、
//! 递归 eval/quote/force/unify/rename/prune）；极致性能版见
//! [`bump_spine_iter`]（L04 冠军配方的移植 + pruning 机制），两版输出
//! **逐字节一致**（互检测试 + `tests/l05_blackbox.rs` 双 oracle）。
//!
//! 与上游 Main.hs 的对应：语义与 `05-pruning` 各模块逐函数对应
//! （Cxt/Evaluation/Unification/Elaboration/Pretty/Errors/Main）；
//! 错误措辞按上游 Errors.hs；`displayMetas` 带类型（`let ?m : A = v;`，
//! 上游 05 的新形态——meta 类型要保留正是 pruning 的前提）。
//!
//! 与 L04 的语义差别（上游 04 → 05 的增量）：
//!
//! 1. **typed metas**：`MetaEntry` 携带类型（已解也保留），fresh meta 的
//!    类型是 `eval [] (close_ty locals (quote lvl a))`——把当前局部 telescope
//!    闭成迭代 Π；`AppPruning` 节点把 meta 应用到 scope 的**掩码**
//!    （`Pruning = List<Option<Icit>>`：bind/newBinder → `Some(Expl)`，
//!    define → `None`），eval 按掩码选择性应用实参。
//! 2. **invert 允许非线性**：spine 里的重复变量记入 `nlvars`，产出
//!    `Option<Pruning>` 掩码（重复变量的全部槽位 → `None`）；
//!    `solve_with_pren` 先 `prune_ty` 验证掩码可从 meta 类型里删掉再解。
//! 3. **rename 的 flex 分支 = pruneVFlex**：spine 是 renaming 且含越界变量时
//!    剪掉越界槽位、造新 meta（`prune_meta`），旧 meta 解为
//!    `λ sp. ?m' pruned-sp`；spine 含非变量实参 → 不再可能是 renaming。
//! 4. **同头 flex-flex = intersect**：两 spine 都是纯变量时取交
//!    （`?m sp =? ?m sp'` → 剪掉差异槽位）；否则回落 `unify_sp`。
//!    （L04 此处是逐实参 unify_sp——本层换成 intersect。）
//! 5. **λ 包裹取自类型**：`lams` 沿 meta 类型的 Π 层剥（名字随 Π，`"_"`
//!    改名 `x{l}`）——不再是 L04 的 spine-icit 版。
//!
//! 与旧移植的两处偏差修正（原码留有 `//TODO:revPruning` /
//! `//TODO:need rev()?`，均已核对上游后修正）：
//! - `pruneTy` 收 `RevPruning`：**外→内**走掩码、配对 Π 层（旧移植是
//!   内→外，掩码与 Π 层错位）；
//! - `pruneVFlex` 的结果折叠对齐上游 `foldr`：**最外层实参先应用**
//!   （旧移植 `iter().fold` 从内层起，应用序倒置）。

pub(crate) mod bump_spine_iter;
pub(crate) mod parser;

use parser::{Either, Icit, Raw};

use crate::list::List;
use crate::parser_lib::Span;
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
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

/// metacontext 条目：**类型一律保留**（pruning 要检查剪后的类型良型），
/// 已解另存解值。
#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
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
pub struct Lvl(u32);

impl std::ops::Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

/// binder 名。`SmolStr`：≤23 字节内联存储，`clone` 免堆分配。
type Name = Span<SmolStr>;

/// 变量掩码：scope 各槽位保留（`Some(icit)`，按该 icit 应用实参）或剪除
/// （`None`）。List 头 = 最内层绑定（与 env/pruning 惯例一致）。
pub type Pruning = List<Option<Icit>>;

/// 局部 telescope：`Bind` 存**引好的类型项**、`Define` 存类型项与定义项，
/// `close_ty` 只需沿链搬运（上游 Syntax.hs 注释同款：不重命名不重引）。
#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Box<Locals>, Name, crate::L05_pruning::Ty, crate::L05_pruning::Tm),
    Bind(Box<Locals>, Name, crate::L05_pruning::Ty),
}

/// 上下文内的类型 → 闭包迭代 Π/Λ-let（上游 `closeTy`：Bind 补显式 Π、
/// Define 补 let；先剥内层，故内层 binder 包得更深）。
pub fn close_ty(mcl: Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => {
            close_ty(*mcl, Tm::Pi(x, Icit::Expl, Box::new(a), Box::new(b)))
        }
        Locals::Define(mcl, x, a, t) => {
            close_ty(*mcl, Tm::Let(x, Box::new(a), Box::new(t), Box::new(b)))
        }
    }
}

/// 表面语法经 elaboration 产出的核心语法（上游 Syntax.hs `Tm`）。
#[derive(Debug, Clone)]
enum Tm {
    Var(Ix),
    Lam(Name, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    /// 把项（实践中即 `Meta`）按掩码应用到当前 scope：`Some(icit)` 槽位
    /// 应用（icit 取掩码里的）、`None` 槽位跳过（上游 `TAppPruning`）。
    AppPruning(Box<Tm>, Pruning),
    U,
    Pi(Name, Icit, Box<Ty>, Box<Ty>),
    Let(Name, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
}

type Ty = Tm;

// values
// --------------------------------------------------------------------------------

type Env = List<Val>;

/// 中性应用链的实参表（头 = 最后应用的实参；icit 随实参携带）。
type Spine = List<(Val, Icit)>;

#[derive(Debug, Clone)]
struct Closure(Env, Box<Tm>);

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

    fn vmeta(m: MetaVar) -> Self {
        Val::Flex(m, List::new())
    }
}

fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
    Ix(l.0 - x.0 - 1)
}

// context
// --------------------------------------------------------------------------------

/// Elaboration 上下文（上游 Cxt.hs）：`src_names` 只收**源码 binder**
/// （bind/define），`new_binder` 补的隐式 binder 不入表——对源码名不可见。
/// `pruning` 与 env 平行（bind/newBinder → Some(Expl)，define → None）。
#[derive(Debug, Clone)]
struct Cxt {
    env: Env,
    lvl: Lvl,
    locals: Locals,
    pruning: Pruning,
    src_names: HashMap<SmolStr, (Lvl, VTy)>,
    pos: Span<()>,
}

impl Cxt {
    fn empty(pos: Span<()>) -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: HashMap::new(),
            pos,
        }
    }

    /// 源码 binder：env/lvl/locals/pruning/src_names 全扩展。
    fn bind(&self, x: Name, a_quote: Tm, a: Val) -> Cxt {
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, a.clone()));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            pos: self.pos,
        }
    }

    /// 补插的隐式 binder：除 `src_names` 外照常扩展（源码名不可见）。
    fn new_binder(&self, x: Name, a_quote: Tm, a: Val) -> Cxt {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
            pos: self.pos,
        }
    }

    /// 定义：env 收**值**、locals 收类型项与定义项、pruning 记 `None`。
    fn define(&self, x: Name, t: Tm, vt: Val, a: Ty, va: VTy) -> Cxt {
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, va));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Box::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
            pos: self.pos,
        }
    }

    /// pretty 用名字表：locals 头 = 最内层（与 `Tm::Var` 的 Ix 同序）。
    fn names(&self) -> Vec<String> {
        let mut ns = Vec::new();
        let mut cur = &self.locals;
        loop {
            match cur {
                Locals::Here => break,
                Locals::Bind(next, x, _) => {
                    ns.push(x.data.to_string());
                    cur = next;
                }
                Locals::Define(next, x, _, _) => {
                    ns.push(x.data.to_string());
                    cur = next;
                }
            }
        }
        ns
    }
}

// pattern renaming
// --------------------------------------------------------------------------------

/// partial renaming：`ren` 把 Γ 变量映射到解域位置；`occ` 是 occurs check
/// 目标（rename rhs 时挂上被解 meta；prune_ty 里是 `None`）。
#[derive(Debug, Clone)]
struct PartialRenaming {
    occ: Option<MetaVar>,
    dom: Lvl,               // size of Γ（解体所在的域 = spine 长度 + lift）
    cod: Lvl,               // size of Δ（rhs 所在的域）
    ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
}

/// Lifting over an extra bound variable（Γ、Δ 各深一层，binder 进映射）。
fn lift(pren: &PartialRenaming) -> PartialRenaming {
    let mut ren = pren.ren.clone();
    ren.insert(pren.cod.0, pren.dom);
    PartialRenaming {
        occ: pren.occ,
        dom: pren.dom + 1,
        cod: pren.cod + 1,
        ren,
    }
}

/// Skipping a bound variable（Δ 深一层但**不进**映射：被剪的槽位越界）。
fn skip(pren: &PartialRenaming) -> PartialRenaming {
    PartialRenaming {
        occ: pren.occ,
        dom: pren.dom,
        cod: pren.cod + 1,
        ren: pren.ren.clone(),
    }
}

/// `pruneVFlex` 的 spine 状态（上游 SpinePruneStatus）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    /// 合法 spine 且是 renaming（全是互不相同的变量）。
    OKRenaming,
    /// 合法 spine 但不是 renaming（含非变量实参）。
    OKNonRenaming,
    /// 是 renaming 但含越界变量槽位——需要剪枝。
    NeedsPruning,
}

// 术语与打印辅助
// --------------------------------------------------------------------------------

#[derive(Debug)]
pub struct Error {
    pub msg: String,
    pub pos: Span<()>,
}

fn report_at(pos: Span<()>, msg: String) -> Error {
    Error { msg, pos }
}

fn empty_span(data: SmolStr) -> Span<SmolStr> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

// evaluator & unifier & elaborator
// --------------------------------------------------------------------------------

/// metacontext + 求值/引读/unification/pruning/elaboration（一次
/// elaboration 一个实例）。
#[derive(Debug)]
struct Infer {
    meta: Vec<MetaEntry>,
}

impl Infer {
    fn new() -> Self {
        Infer { meta: vec![] }
    }

    /// 挂新 meta（带类型），返回编号。
    fn new_meta(&mut self, a: VTy) -> MetaVar {
        self.meta.push(MetaEntry::Unsolved(a));
        MetaVar(self.meta.len() as u32 - 1)
    }

    /// `freshMeta cxt a`：类型闭成迭代 Π 存进 metacontext，项侧是
    /// `AppPruning ?m (cxtPruning)`——把 meta 应用到当前全部绑定槽位。
    fn fresh_meta(&mut self, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.eval(&List::new(), &close_ty(cxt.locals.clone(), self.quote(cxt.lvl, &a)));
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(m)), cxt.pruning.clone())
    }

    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }

    /// **force**：把值更新到 metacontext 的当前状态（只展开到下一个不可再
    /// 解阻塞的头构造器）。unify/quote/rename 一律先 force 再分派。
    fn force(&self, t: &Val) -> Val {
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(*m) {
                MetaEntry::Solved(t_solved, _) => {
                    let v = self.v_app_sp(t_solved, sp);
                    self.force(&v)
                }
                MetaEntry::Unsolved(_) => Val::Flex(*m, sp.clone()),
            },
            _ => t.clone(),
        }
    }

    /// `vMeta`：meta 的当前值（已解给解值，未解给 `?m`）。
    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(m),
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

    /// `vAppPruning env v pr`：把 `v` 应用到 env 里掩码为 `Some(icit)` 的
    /// 槽位（外层先应用，icit 取自掩码；`None` 槽位跳过）。
    fn v_app_pruning(&self, env: &Env, v: Val, pr: &Pruning) -> Val {
        match (env.head(), pr.head()) {
            (None, None) => v,
            (Some(a), Some(Some(i))) => {
                let v = self.v_app_pruning(&env.tail(), v, &pr.tail());
                self.v_app(&v, a.clone(), *i)
            }
            (Some(_), Some(None)) => self.v_app_pruning(&env.tail(), v, &pr.tail()),
            _ => panic!("impossible"), // env 与 pr 错位（空环境引带 binder 的洞）
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
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, t), pr),
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

    /// `closeVal`：把 Γ 下的值闭进 Closure（quote 在 `lvl + 1`）。
    fn close_val(&self, cxt: &Cxt, t: &Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Val, t_prime: &Val) -> Result<(), Error> {
        self.unify(cxt.lvl, t, t_prime)
            .map_err(|_| Error {
                msg: format!(
                    "Cannot unify expected type\n\n  {}\n\nwith inferred type\n\n  {}",
                    show_tm(cxt, &self.quote(cxt.lvl, t)),
                    show_tm(cxt, &self.quote(cxt.lvl, t_prime)),
                ),
                pos: cxt.pos,
            })
    }

    // Pattern unification with pruning
    // --------------------------------------------------------------------------------

    /// `invert` 的核：spine 必须是**纯变量**（icit 不参与）。返回
    /// (dom, ren, nlvars, fsp)：`nlvars` 记非线性（重复）变量，`fsp` 是
    /// 应用序的 (lvl, icit) 收集（头 = 最内层）。
    fn invert_go(
        &self,
        sp: &Spine,
    ) -> Result<(Lvl, HashMap<u32, Lvl>, HashSet<u32>, List<(Lvl, Icit)>), UnifyError> {
        match sp.head() {
            None => Ok((Lvl(0), HashMap::new(), HashSet::new(), List::new())),
            Some((t, i)) => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(&sp.tail())?;
                match self.force(t) {
                    Val::Rigid(x, sp2) if sp2.is_empty() => {
                        if ren.contains_key(&x.0) || nlvars.contains(&x.0) {
                            // 重复出现：移出 renaming、记入非线性集
                            ren.remove(&x.0);
                            nlvars.insert(x.0);
                        } else {
                            ren.insert(x.0, dom);
                        }
                        Ok((
                            dom + 1,
                            ren,
                            nlvars,
                            fsp.prepend((x, *i)),
                        ))
                    }
                    _ => Err(UnifyError), // 非变量实参（含带 spine 的变量）
                }
            }
        }
    }

    /// invert：若 spine 非线性（有重复变量），产出把**重复变量的全部出现**
    /// 记为 `None` 的掩码（solve 前用它检查剪枝可行性）。
    fn invert(
        &self,
        gamma: Lvl,
        sp: &Spine,
    ) -> Result<(PartialRenaming, Option<Pruning>), UnifyError> {
        let (dom, ren, nlvars, fsp) = self.invert_go(sp)?;
        Ok((
            PartialRenaming {
                occ: None,
                dom,
                cod: gamma,
                ren,
            },
            if nlvars.is_empty() {
                None
            } else {
                Some(fsp.map(|(x, i)| {
                    if nlvars.contains(&x.0) {
                        None
                    } else {
                        Some(*i)
                    }
                }))
            },
        ))
    }

    /// 上游 `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层：
    /// `Some` 层保留（定义域过 renaming，进 lift），`None` 层整个删掉
    /// （进 skip）；掩码耗尽后剩余类型过 renaming。
    fn prune_ty(&mut self, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
        // revPruning：头 = 最外层（与 Π 剥层同序）
        let mut rev: Vec<Option<Icit>> = pr.iter().copied().collect();
        rev.reverse();
        self.prune_ty_go(
            &rev,
            &PartialRenaming {
                occ: None,
                dom: Lvl(0),
                cod: Lvl(0),
                ren: HashMap::new(),
            },
            a,
        )
    }

    fn prune_ty_go(
        &mut self,
        rev: &[Option<Icit>],
        pren: &PartialRenaming,
        a: Val,
    ) -> Result<Tm, UnifyError> {
        match (rev.split_first(), self.force(&a)) {
            (None, a) => self.rename(pren, &a),
            (Some((Some(_), rest)), Val::Pi(x, i, a, b)) => {
                let a_tm = self.rename(pren, &a)?;
                let b_v = self.closure_apply(&b, Val::vvar(pren.cod));
                let b_tm = self.prune_ty_go(rest, &lift(pren), b_v)?;
                Ok(Tm::Pi(x, i, Box::new(a_tm), Box::new(b_tm)))
            }
            (Some((None, rest)), Val::Pi(_, _, _, b)) => {
                let b_v = self.closure_apply(&b, Val::vvar(pren.cod));
                self.prune_ty_go(rest, &skip(pren), b_v)
            }
            _ => Err(UnifyError), // impossible：掩码与类型结构不匹配
        }
    }

    /// `pruneMeta`：按掩码剪掉 meta 的实参——检查剪后类型良型、造新 meta、
    /// 旧 meta 解为 `λ telescope. AppPruning ?m' pruned`。
    fn prune_meta(&mut self, pruning: Pruning, m: MetaVar) -> Result<MetaVar, UnifyError> {
        let mty = match &self.lookup_meta(m) {
            MetaEntry::Unsolved(a) => a.clone(),
            _ => unreachable!(), // 只对未解 meta 剪枝
        };
        let pruned_tm = self.prune_ty(&pruning, mty.clone())?;
        let prunedty = self.eval(&List::new(), &pruned_tm);
        let m_prime = self.new_meta(prunedty);
        let solution_tm = self.lams(
            Lvl(pruning.len() as u32),
            &mty.clone(),
            Tm::AppPruning(Box::new(Tm::Meta(m_prime)), pruning),
        );
        let solution = self.eval(&List::new(), &solution_tm);
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(m_prime)
    }

    /// `pruneVFlex` 的核：逐 spine 槽位（外→内的递归，结果头 = 最内层）：
    /// 变量在 ren 里 → 改名保留；不在 → 记 `None` 进 NeedsPruning；
    /// 非变量 → rename 保留并进 OKNonRenaming（与 NeedsPruning 互斥）。
    fn prune_vflex_go(
        &mut self,
        pren: &PartialRenaming,
        sp: &Spine,
    ) -> Result<(List<(Option<Tm>, Icit)>, SpinePruneStatus), UnifyError> {
        match sp.head() {
            None => Ok((List::new(), SpinePruneStatus::OKRenaming)),
            Some((t, i)) => {
                let (sp_rest, status) = self.prune_vflex_go(pren, &sp.tail())?;
                match self.force(t) {
                    Val::Rigid(x, sp2) if sp2.is_empty() => match (pren.ren.get(&x.0), status) {
                        (Some(xp), _) => Ok((
                            sp_rest.prepend((Some(Tm::Var(lvl2ix(pren.dom, *xp))), *i)),
                            status,
                        )),
                        (None, SpinePruneStatus::OKNonRenaming) => Err(UnifyError),
                        (None, _) => Ok((sp_rest.prepend((None, *i)), SpinePruneStatus::NeedsPruning)),
                    },
                    t => match status {
                        SpinePruneStatus::NeedsPruning => Err(UnifyError),
                        _ => {
                            let t = self.rename(pren, &t)?;
                            Ok((
                                sp_rest.prepend((Some(t), *i)),
                                SpinePruneStatus::OKNonRenaming,
                            ))
                        }
                    },
                }
            }
        }
    }

    /// rename 的 flex 分支：可能触发剪枝的 meta+spine 重建。
    fn prune_vflex(
        &mut self,
        pren: &PartialRenaming,
        m: MetaVar,
        sp: &Spine,
    ) -> Result<Tm, UnifyError> {
        let (sp, status) = self.prune_vflex_go(pren, sp)?;

        let m_prime = match status {
            SpinePruneStatus::NeedsPruning => {
                // 掩码 = 保留槽位的 icit（剪除槽位 → None）；只对未解 meta
                self.prune_meta(sp.map(|(mt, i)| mt.as_ref().map(|_| *i)), m)?
            }
            _ => {
                match self.lookup_meta(m) {
                    MetaEntry::Unsolved(_) => m,
                    _ => unreachable!(), // force 已保证未解
                }
            }
        };

        // 上游 `foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp`：
        // foldr 从尾（最外层）起 = 最外层实参先应用（修正旧移植 `iter().fold`
        // 从内层起导致的倒序）。
        let mut slots: Vec<(Option<Tm>, Icit)> = sp.iter().cloned().collect();
        slots.reverse();
        let mut t = Tm::Meta(m_prime);
        for (mu, i) in slots {
            if let Some(u) = mu {
                t = Tm::App(Box::new(t), Box::new(u), i);
            }
        }
        Ok(t)
    }

    fn rename_sp(
        &mut self,
        pren: &PartialRenaming,
        t: Tm,
        sp: &Spine,
    ) -> Result<Tm, UnifyError> {
        match sp.head() {
            None => Ok(t),
            Some((u, i)) => {
                let t = self.rename_sp(pren, t, &sp.tail())?;
                let u = self.rename(pren, u)?;
                Ok(Tm::App(Box::new(t), Box::new(u), *i))
            }
        }
    }

    /// 对 rhs 执行 partial renaming，同时做 occurs check 与 scope check；
    /// flex spine 走 `pruneVFlex`（可能剪枝）。
    fn rename(&mut self, pren: &PartialRenaming, v: &Val) -> Result<Tm, UnifyError> {
        let v = self.force(v);
        match v {
            Val::Flex(m_prime, sp) => match pren.occ {
                Some(m) if m == m_prime => Err(UnifyError), // occurs check
                _ => self.prune_vflex(pren, m_prime, &sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => Err(UnifyError), // scope error（"escaping variable"）
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(pren, t, &sp)
                }
            },
            Val::Lam(x, i, clo) => {
                let t =
                    self.rename(&lift(pren), &self.closure_apply(&clo, Val::vvar(pren.cod)))?;
                Ok(Tm::Lam(x, i, Box::new(t)))
            }
            Val::Pi(x, i, a, clo) => {
                let a = self.rename(pren, &a)?;
                let b =
                    self.rename(&lift(pren), &self.closure_apply(&clo, Val::vvar(pren.cod)))?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
        }
    }

    /// `lams l a t`：沿 meta 类型 `a` 的 Π 层包 `l` 个 λ——binder 名与 icit
    /// 取自 Π（`"_"` 改名 `x{l'}`，0 起）；逐层用新的 `VVar l'` 剥闭包。
    fn lams(&self, l: Lvl, a: &VTy, t: Tm) -> Tm {
        fn go(inf: &Infer, l: Lvl, mut a: VTy, l_prime: Lvl, t: Tm) -> Tm {
            if l_prime == l {
                return t;
            }
            match inf.force(&a) {
                Val::Pi(span, icit, _, clo) => {
                    let name = if span.data == "_" {
                        empty_span(SmolStr::from(format!("x{}", l_prime.0)))
                    } else {
                        span
                    };
                    let next = inf.closure_apply(&clo, Val::vvar(l_prime));
                    Tm::Lam(name, icit, Box::new(go(inf, l, next, l_prime + 1, t)))
                }
                _ => unreachable!(), // 类型 Π 层数不足
            }
        }
        go(self, l, a.clone(), Lvl(0), t)
    }

    /// `Γ ⊢ ?m spine ≡ rhs` 的求解（非线性时先验证剪枝可行性）。
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: &Spine, rhs: &Val) -> Result<(), UnifyError> {
        let (pren, prune_non_linear) = self.invert(gamma, sp)?;
        self.solve_with_pren(m, pren, prune_non_linear, rhs)
    }

    fn solve_with_pren(
        &mut self,
        m: MetaVar,
        pren: PartialRenaming,
        prune_non_linear: Option<Pruning>,
        rhs: &Val,
    ) -> Result<(), UnifyError> {
        let mty = match &self.lookup_meta(m) {
            MetaEntry::Unsolved(a) => a.clone(),
            _ => unreachable!(),
        };

        // 非线性 spine：先检查非线性的变量槽位可以从 meta 类型里剪掉
        // （剪完仍良型才允许求解）。
        if let Some(pr) = prune_non_linear {
            self.prune_ty(&pr, mty.clone())?;
        }

        let rhs = self.rename(
            &PartialRenaming {
                occ: Some(m),
                ..pren
            },
            rhs,
        )?;
        let solution = self.eval(&List::new(), &self.lams(pren.dom, &mty, rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(())
    }

    /// 同头中性的逐实参比较（icit 不比：类型已定，上游 Unification.hs 同款）。
    fn unify_sp(&mut self, l: Lvl, sp: &Spine, sp_prime: &Spine) -> Result<(), UnifyError> {
        match (sp.head(), sp_prime.head()) {
            (None, None) => Ok(()),
            (Some((t, _)), Some((t_prime, _))) => {
                self.unify_sp(l, &sp.tail(), &sp_prime.tail())?;
                self.unify(l, t, t_prime)
            }
            _ => Err(UnifyError), // spine 长度不等
        }
    }

    /// 异头 flex-flex：较长 spine 一侧优先反演（解内层 meta 少剪枝）；
    /// 反演失败则用另一侧求解。
    fn flex_flex(
        &mut self,
        gamma: Lvl,
        m: MetaVar,
        sp: &Spine,
        m_prime: MetaVar,
        sp_prime: &Spine,
    ) -> Result<(), UnifyError> {
        let mut go = |m: MetaVar,
                      sp: &Spine,
                      m_prime: MetaVar,
                      sp_prime: &Spine|
         -> Result<(), UnifyError> {
            match self.invert(gamma, sp) {
                Err(UnifyError) => self.solve(gamma, m_prime, sp_prime, &Val::Flex(m, sp.clone())),
                Ok((pren, p1)) => {
                    self.solve_with_pren(m, pren, p1, &Val::Flex(m_prime, sp_prime.clone()))
                }
            }
        };

        if sp.len() < sp_prime.len() {
            go(m_prime, sp_prime, m, sp)
        } else {
            go(m, sp, m_prime, sp_prime)
        }
    }

    /// `intersect` 的核：两 spine 逐槽都是变量时产出「相等槽位 = 其 icit、
    /// 不等槽位 = None」的掩码；含非变量槽位返回 None（回落 unify_sp）。
    /// 长度不等也返回 None（上游 `impossible` 分支——本层落地为 unify_sp
    /// 的长度失配失败，不炸栈，结论同为不可解）。
    fn intersect_go(&self, sp: &Spine, sp_prime: &Spine) -> Option<Pruning> {
        match (sp.head(), sp_prime.head()) {
            (None, None) => Some(List::new()),
            (Some((t, i)), Some((t_prime, _))) => {
                match (self.force(t), self.force(t_prime)) {
                    (Val::Rigid(x, s1), Val::Rigid(x_prime, s2))
                        if s1.is_empty() && s2.is_empty() =>
                    {
                        self.intersect_go(&sp.tail(), &sp_prime.tail())
                            .map(|l| l.prepend(if x == x_prime { Some(*i) } else { None }))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `?m sp =? ?m sp'`：两 spine 都是变量序列时**取交**——差异槽位从
    /// `?m` 剪掉（`pruneMeta`）；否则回落逐实参比较。
    fn intersect(
        &mut self,
        l: Lvl,
        m: MetaVar,
        sp: &Spine,
        sp_prime: &Spine,
    ) -> Result<(), UnifyError> {
        match self.intersect_go(sp, sp_prime) {
            None => self.unify_sp(l, sp, sp_prime),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }

    /// unification：结构比较 + 模式求解，分派与上游 Unification.hs 逐项
    /// 对应（U → Π（icit 相等）→ 同头 rigid → 同头 flex = intersect →
    /// 异头 flex = flexFlex → λ/η → 求解）。
    fn unify(&mut self, l: Lvl, t: &Val, u: &Val) -> Result<(), UnifyError> {
        let t = self.force(t);
        let u = self.force(u);
        match (&t, &u) {
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
                self.intersect(l, *m, sp, sp_prime)
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(l, *m, sp, *m_prime, sp_prime)
            }
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
            (Val::Flex(m, sp), _) => self.solve(l, *m, sp, &u),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(l, *m_prime, sp_prime, &t),
            _ => Err(UnifyError), // rigid 失配 / Pi icit 失配
        }
    }

    // bidirectional elaboration
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参（上游 `insert'`）。
    fn insert_go(&mut self, cxt: &Cxt, t: Tm, va: &Val) -> (Tm, VTy) {
        match self.force(va) {
            Val::Pi(_, Icit::Impl, a, b) => {
                let m = self.fresh_meta(cxt, (*a).clone());
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

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止；隐式前缀
    /// 耗尽仍无匹配 → `No named implicit argument with name x`。
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
                    let m = self.fresh_meta(cxt, (*a).clone());
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
            // 命名 binder（\{x = y}）要求 Pi binder 名相等且 Π 为隐式。
            (Raw::Lam(x, i, t), Val::Pi(x_t, i_t, a, b))
                if match i {
                    Either::Name(n) => n.data == x_t.data && *i_t == Icit::Impl,
                    &Either::Icit(j) => j == *i_t,
                } =>
            {
                let body = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, a), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), *i_t, Box::new(body)))
            }

            // 非 lambda 项检查到隐式 Π：插入隐式 binder（对源码名不可见）
            (t, Val::Pi(x, Icit::Impl, a, b)) => {
                let body = self.check(
                    &cxt.new_binder(x.clone(), self.quote(cxt.lvl, a), (**a).clone()),
                    t,
                    &self.closure_apply(b, Val::vvar(cxt.lvl)),
                )?;
                Ok(Tm::Lam(x.clone(), Icit::Impl, Box::new(body)))
            }

            (Raw::Let(x, a_ty, t, u), a_prime) => {
                let a_tm = self.check(cxt, a_ty, &Val::U)?;
                let va = self.eval(&cxt.env, &a_tm);
                let t_tm = self.check(cxt, t, &va)?;
                let vt = self.eval(&cxt.env, &t_tm);
                let u_tm = self.check(
                    &cxt.define(x.clone(), t_tm.clone(), vt, a_tm.clone(), va),
                    u,
                    a_prime,
                )?;
                Ok(Tm::Let(
                    x.clone(),
                    Box::new(a_tm),
                    Box::new(t_tm),
                    Box::new(u_tm),
                ))
            }

            // hole：直接以 fresh meta（类型为期望类型）填充
            (Raw::Hole, _) => Ok(self.fresh_meta(cxt, a.clone())),

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

            Raw::Var(x) => match cxt.src_names.get(&x.data) {
                Some((x2, a)) => Ok((Tm::Var(lvl2ix(cxt.lvl, *x2)), a.clone())),
                None => Err(report_at(
                    cxt.pos,
                    format!("Name not in scope: {}", x.data),
                )),
            },

            // 定义域挂洞；余定义域闭包住当前环境；体推断后在**扩展后的**
            // 上下文里 insert（上游 `insert cxt'`——meta 的 pruning 含本 binder）
            Raw::Lam(x, Either::Icit(i), t) => {
                let new_meta = self.fresh_meta(cxt, Val::U);
                let a = self.eval(&cxt.env, &new_meta);
                let cxt1 = cxt.bind(x.clone(), self.quote(cxt.lvl, &a), a.clone());
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
                        let new_meta = self.fresh_meta(cxt, Val::U);
                        let a = self.eval(&cxt.env, &new_meta);
                        let cod_meta = self.fresh_meta(
                            &cxt.bind(
                                empty_span("x".into()),
                                self.quote(cxt.lvl, &a),
                                a.clone(),
                            ),
                            Val::U,
                        );
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

            Raw::U => Ok((Tm::U, Val::U)),

            Raw::Pi(x, i, a, b) => {
                let a_tm = self.check(cxt, a, &Val::U)?;
                let va = self.eval(&cxt.env, &a_tm);
                let b_tm = self.check(
                    &cxt.bind(x.clone(), self.quote(cxt.lvl, &va), va),
                    b,
                    &Val::U,
                )?;
                Ok((Tm::Pi(x.clone(), *i, Box::new(a_tm), Box::new(b_tm)), Val::U))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check(cxt, a_ty, &Val::U)?;
                let va = self.eval(&cxt.env, &a_tm);
                let t_tm = self.check(cxt, t, &va)?;
                let vt = self.eval(&cxt.env, &t_tm);
                let (u_tm, b) = self.infer(
                    &cxt.define(x.clone(), t_tm.clone(), vt, a_tm.clone(), va),
                    u,
                )?;
                Ok((
                    Tm::Let(x.clone(), Box::new(a_tm), Box::new(t_tm), Box::new(u_tm)),
                    b,
                ))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(cxt, Val::U);
                let a = self.eval(&cxt.env, &new_meta);
                let t = self.fresh_meta(cxt, a.clone());
                Ok((t, a))
            }
        }
    }

    /// `displayMetas`：metacontext 逐条打印（上游 05 带类型形态：
    /// 未解 `let ?m : A = ?;`，已解 `let ?m : A = <v>;`），末尾空行。
    fn display_metas(&self) -> String {
        let mut out = String::new();
        for (m, e) in self.meta.iter().enumerate() {
            match e {
                MetaEntry::Unsolved(a) => out.push_str(&format!(
                    "let ?{m} : {} = ?;\n",
                    pretty_tm(0, &[], &self.quote(Lvl(0), a))
                )),
                MetaEntry::Solved(v, a) => out.push_str(&format!(
                    "let ?{m} : {} = {};\n",
                    pretty_tm(0, &[], &self.quote(Lvl(0), a)),
                    pretty_tm(0, &[], &self.quote(Lvl(0), v))
                )),
            }
        }
        out.push('\n');
        out
    }
}

// printing
// --------------------------------------------------------------------------------

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

/// ns 按本仓约定：**最内层 binder 在头部**，`Var (Ix x) -> ns[x]`。
pub fn pretty_tm(prec: usize, ns: &[String], t: &Tm) -> String {
    let mut out = String::new();
    go(prec, ns, t, &mut out);
    out
}

fn show_tm(cxt: &Cxt, t: &Tm) -> String {
    pretty_tm(0, &cxt.names(), t)
}

/// `AppPruning` 的应用串（上游 `goPr`）：ns 与掩码平行推进（头 = 最内层），
/// 先递归外层再贴本层名字（应用序外先）；`Some(Impl)` 裹 `{}`；`None` 跳名。
fn go_pr(p: usize, ns: &[String], t: &Tm, pr: &Pruning, out: &mut String) {
    go_pr_i(p, 0, ns, t, pr, out);
}

/// `i` = 自最内层的位序（上游 goPr 的 `x`，匿名 binder 打印 `@i`）。
fn go_pr_i(p: usize, i: usize, ns: &[String], t: &Tm, pr: &Pruning, out: &mut String) {
    match (ns.split_first(), pr.head()) {
        (None, None) => go(p, ns, t, out),
        // 绑定槽位（Some）：递归外层先行，本层名字在回归尾追加（= 应用序
        // 外先）；`Impl` 裹 `{}`、`Expl` 裸名；匿名 binder `_` 打印 `@i`。
        (Some((n, ns_tail)), Some(Some(icit))) => {
            let paren = APPP < p;
            if paren {
                out.push('(');
            }
            go_pr_i(APPP, i + 1, ns_tail, t, &pr.tail(), out);
            out.push(' ');
            let shown = if n == "_" {
                format!("@{i}")
            } else {
                n.clone()
            };
            match icit {
                Icit::Impl => {
                    out.push('{');
                    out.push_str(&shown);
                    out.push('}');
                }
                Icit::Expl => out.push_str(&shown),
            }
            if paren {
                out.push(')');
            }
        }
        // define 槽位（Nothing）：只推进，不产名字（上游 goPr 的 Nothing 支）。
        (Some((_, ns_tail)), Some(None)) => {
            go_pr_i(APPP, i + 1, ns_tail, t, &pr.tail(), out);
        }
        _ => panic!("impossible"), // ns 与 pr 长度错位
    }
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

        Tm::AppPruning(t, pr) => go_pr(p, ns, t, pr, out),

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

const HELP_MSG: &str = "usage: elabzoo-pruning [--help|elab|nf|type]\n\
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

/// 隐式插入的最小样例（L04 同款基线）。
pub const EX0_SRC: &str = "\
let id : {A : U} -> A -> A = \\x. x;
let id2 : {A : U} -> A -> A = \\x. id x;
U
";

/// 上游 05 的 Main.hs `ex1`（unification with pruning 全套示例：非线性
/// spine 可解、交集剪枝、`pr1/pr2/pr3` 的剪枝推断）。
pub const EX1_SRC: &str = "\
let Eq : {A : U} -> A -> A -> U
    = \\{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x
    = \\ _ px. px;

let the : (A : U) -> A -> A = \\ _ x. x;

let m : (A : U)(B : U) -> U -> U -> U = _;
let test = \\ a b. the (Eq (m a a) (\\ x y. y)) refl;

let m : U -> U -> U -> U = _;
let test = \\ a b c. the (Eq (m a b c) (m c b a)) refl;

let pr1 = \\ f x. f x;
let pr2 = \\ f x y. f x y;
let pr3 = \\ f. f U;

U
";

#[allow(non_snake_case)]
pub fn ex0() -> String {
    main_with("elab", EX0_SRC)
}

#[allow(non_snake_case)]
pub fn ex1() -> String {
    main_with("nf", EX1_SRC)
}

// benchmark entries（l05bench 用）
// --------------------------------------------------------------------------------

/// 基准口径：仅 check。
pub(crate) fn bench_check(raw: &Raw) {
    let _ = Infer::new().infer(&Cxt::empty(initial_pos()), raw);
}

/// 基准口径：check + nf，产出丢弃（深 Box 树的递归析构会爆栈，基准里
/// mem::forget——L03/L04 同款处理）。
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
        assert!(main_with("--help", "").starts_with("usage: elabzoo-pruning"));
        assert!(main_with("bogus", "").starts_with("usage:"));
    }

    /// 名字越界报错（上游措辞 + megaparsec 风格定位）。
    #[test]
    fn name_not_in_scope() {
        assert_eq!(
            main_with("type", "id"),
            r#"(stdin):1:1:
  |
1 | id
  | ^
Name not in scope: id
"#
        );
    }

    /// icit 失配：`{u}` 隐式实参应用到显式 Pi 头。
    #[test]
    fn icit_mismatch() {
        let src = "let g : U -> U -> U = \\x y. x;\ng {U}";
        let out = main_with("type", src);
        assert!(
            out.contains("Function icitness mismatch: expected implicit, got explicit."),
            "{out}"
        );
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

    /// 上游 ex1 全套件通过（顶层 U：type 模式打印 `U`）。
    #[test]
    fn ex1_zoo_suite() {
        let out = main_with("type", EX1_SRC);
        assert_eq!(out, "U\n", "{out}");
    }

    /// 剪枝基线：`\f. f U`——`f` 的类型洞 `?0` 合成 Π 时，`?1/?5` 的
    /// spine 挂着 `f`（越界），`pruneVFlex` 把 `f` 槽剪掉：`?5` 类型成
    /// 为 `(x : U) → U`（不含 f），保持未解。全串金样与上游 README
    /// 的 pr3 讲解逐槽核对过。
    #[test]
    fn pr3_prunes_meta() {
        assert_eq!(
            main_with("elab", "let pr3 = \\f. f U;\nU\n"),
            "let ?0 : U = (f : (x : U) → ?5 x) → ?5 U;\n\
             let ?1 : U = (x : U) → ?5 x;\n\
             let ?2 : (f : (x : U) → ?5 x) → U = λ f. U;\n\
             let ?3 : (f : (x : U) → ?5 x)(x : U) → U = λ f x. ?5 x;\n\
             let ?4 : U = U;\n\
             let ?5 : (x : U) → U = ?;\n\n\
             let pr3 : ?0\n  = λ f. f U;\n\nU\n"
        );
    }
}
