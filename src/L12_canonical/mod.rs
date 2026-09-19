use cxt::Cxt;
use parser::{syntax::{Either, Icit, Raw}, IError};
use pattern_match::Compiler;
use smol_str::SmolStr;
use syntax::{Pruning, close_ty};
use pretty::pretty_tm;

use crate::list::List;
use crate::parser_lib::Span;

pub mod cxt;
mod elaboration;
pub mod parser;
mod pattern_match;
mod syntax;
mod unification;
mod typeclass;
pub mod pretty;
pub(crate) mod bump_spine_iter;
mod canonical;

type Rc<T> = std::sync::Arc<T>;

type Decl = HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>, std::sync::Arc<Cxt>, Rc<VTy>),
}

#[derive(Debug, Clone, Copy)]
pub struct Ix(u32);

#[derive(Debug, Clone)]
enum BD {
    Bound,
    Defined,
}

#[derive(Clone, Debug)]
pub enum DeclTm {
    Def {
        name: Span<SmolStr>,
        typ: Rc<Val>,
        body: Rc<Val>,
        typ_pretty: String,
        body_pretty: String,
    },
    Println(Rc<Tm>, String, Span<()>),
    Enum {
        //TODO:
    },
    Trait {
        //TODO:
    },
    TraitImpl {
        //TODO:
    },
}

#[derive(Clone)]
pub struct PrimFunc(Rc<dyn Fn(&Infer, &Decl, &Env, Rc<Val>) -> Rc<Val> + Send + Sync>);

impl std::fmt::Debug for PrimFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PrimFunc")
    }
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    Decl(Span<SmolStr>),
    Obj(Rc<Tm>, Span<SmolStr>),
    Lam(Span<SmolStr>, Icit, Rc<Tm>),
    App(Rc<Tm>, Rc<Tm>, Icit),
    AppPruning(Rc<Tm>, Pruning),
    U(u32),
    Pi(Span<SmolStr>, Icit, Rc<Ty>, Rc<Ty>),
    Let(Span<SmolStr>, Rc<Ty>, Rc<Tm>, Rc<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim(Rc<Val>, PrimFunc),
    Sum(Span<SmolStr>, Vec<(Span<SmolStr>, Rc<Tm>, Rc<Ty>, Icit)>, Vec<Span<SmolStr>>, bool),
    SumCase {
        typ: Rc<Tm>,
        case_name: Span<SmolStr>,
        datas: Vec<(Span<SmolStr>, Rc<Tm>, Icit)>,
        is_trait: bool,
    },
    Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>),
    /// Call(name, display_args, val_args, body) - body was inlined from function `name`
    Call(SmolStr, Vec<Rc<Tm>>, Vec<Rc<Val>>, Rc<Tm>),
}

impl Tm {
    pub fn no_metas(&self, infer: &Infer, decl: &Decl, l: Lvl) -> Option<(Cxt, Rc<Val>)> {
        match self {
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Prim(_, _) => None,
            Tm::Obj(tm, _) => tm.no_metas(infer, decl, l),
            Tm::Lam(_, _, t) => t.no_metas(infer, decl, l + 1),
            Tm::App(t, u, _) => t.no_metas(infer, decl, l).or_else(|| u.no_metas(infer, decl, l)),
            Tm::AppPruning(t, _) => {
                t.no_metas(infer, decl, l)
            },
            Tm::Pi(_, _, t, u) => t.no_metas(infer, decl, l).or_else(|| u.no_metas(infer, decl, l + 1)),
            Tm::Let(_, a, t, u) => a.no_metas(infer, decl, l).or_else(|| t.no_metas(infer, decl, l)).or_else(|| u.no_metas(infer, decl, l)),
            Tm::Meta(m) => match infer.lookup_meta(*m) {
                MetaEntry::Unsolved(_, cxt, oty) => Some((cxt.as_ref().clone(), oty.clone())),
                MetaEntry::Solved(v, _) => {
                    infer.quote(decl, l, v).no_metas(infer, decl, l)
                }
            },
            Tm::Sum(_, items, _, _) => items.iter().flat_map(|(_, t, ty, _)| t.no_metas(infer, decl, l).or_else(|| ty.no_metas(infer, decl, l))).next(),
            Tm::SumCase { typ, case_name: _, datas, is_trait: _ } => typ.no_metas(infer, decl, l)
                .or_else(|| datas.iter().flat_map(|(_, t, _)| t.no_metas(infer, decl, l)).next()),
            Tm::Match(tm, items) => tm.no_metas(infer, decl, l).or_else(|| items.iter().flat_map(|(_, t)| t.no_metas(infer, decl, l)).next()),
            Tm::Call(_, args, _, body) => args.iter().flat_map(|a| a.no_metas(infer, decl, l)).next().or_else(|| body.no_metas(infer, decl, l)),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<SmolStr>),
    Con(Span<SmolStr>, Vec<PatternDetail>),
}

impl PatternDetail {
    fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, pattern_details) => {
                pattern_details.iter().map(|pattern_detail| pattern_detail.bind_count()).sum::<u32>()
            },
        }
    }
    fn bind_names(&self, ns: &List<SmolStr>) -> List<SmolStr> {
        match self {
            PatternDetail::Any(_) => ns.prepend(SmolStr::new("_")),
            PatternDetail::Bind(name) => ns.prepend(name.data.clone()),
            PatternDetail::Con(_, pattern_details) => {
                pattern_details
                    .iter()
                    .fold(ns.clone(), |ns, pattern_detail| pattern_detail.bind_names(&ns))
            },
        }
    }
    fn bind_cxt(&self, cxt: &Cxt) -> Cxt {
        match self {
            PatternDetail::Any(_) => cxt.clone(),
            PatternDetail::Bind(name) => cxt.bind(name.clone(), Tm::U(0).into(), Val::U(0).into()),
            PatternDetail::Con(_, pattern_details) => {
                pattern_details
                    .iter()
                    .fold(cxt.clone(), |cxt, pattern_detail| pattern_detail.bind_cxt(&cxt))
            },
        }
    }
}

impl std::fmt::Display for PatternDetail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternDetail::Any(_) => write!(f, "_"),
            PatternDetail::Bind(name) => write!(f, "{}", name.data),
            PatternDetail::Con(name, pattern_details) => {
                let p = pattern_details
                    .iter()
                    .map(|pattern_detail| pattern_detail.to_string())
                    .collect::<Vec<_>>();
                if p.is_empty() {
                    write!(f, "{}", name.data)
                } else {
                    write!(f, "{}({})", name.data, p.join(", "))
                }
            }
        }
    }
}

/// 已走查臂在某嵌套位置的覆盖贡献（参考版与孪生版共用，保证嵌套覆盖
/// 检查的判定与文案逐字节一致，L07 mod.rs 同款 2026-09-18 前向传播）：
/// 全覆盖（var/Any，含路径中途变变量）、贡献某构造子（路径末端是 Con）、
/// 不可达该位置（祖先选了别的构造子）。
pub(crate) enum PosCover {
    All,
    Ctor(SmolStr),
    None,
}

/// 沿 (构造子名, 字段下标) 路径下钻一棵已走查的 PatternDetail 树。
/// 字段下标与 `walk_pat` 的 details 布局同源（望远镜中产槽绑定器的序数）。
pub(crate) fn cover_at(detail: &PatternDetail, path: &[(String, usize)]) -> PosCover {
    let mut cur = detail;
    for (ctor, field) in path {
        match cur {
            PatternDetail::Any(_) | PatternDetail::Bind(_) => return PosCover::All,
            PatternDetail::Con(n, subs) if n.data.as_str() == ctor.as_str() => {
                cur = &subs[*field]
            }
            PatternDetail::Con(..) => return PosCover::None,
        }
    }
    match cur {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => PosCover::All,
        PatternDetail::Con(n, _) => PosCover::Ctor(n.data.clone()),
    }
}

/// 人读路径：`cons#2 → nil#1` 表示 cons 第二字段的 nil 第一字段处。
pub(crate) fn fmt_path(path: &[(String, usize)]) -> String {
    path.iter()
        .map(|(c, f)| format!("{c}#{}", f + 1))
        .collect::<Vec<_>>()
        .join(" → ")
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct Lvl(u32);

impl Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

impl Sub<u32> for Lvl {
    type Output = Lvl;
    fn sub(self, rhs: u32) -> Lvl {
        Lvl(self.0 - rhs)
    }
}

type Env = List<Rc<Val>>;
type Spine = List<(Rc<Val>, Icit)>;

#[derive(Clone)]
pub struct Closure(Env, Rc<Tm>);

impl std::fmt::Debug for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure(..{}, {:?})", self.0.len(), self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Decl(Span<SmolStr>, Spine),
    Obj(Rc<Val>, Span<SmolStr>, Spine),
    Lam(Span<SmolStr>, Icit, Closure),
    Pi(Span<SmolStr>, Icit, Rc<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim(Rc<Val>, PrimFunc),
    Sum(
        Span<SmolStr>,
        Vec<(Span<SmolStr>, Rc<Val>, Rc<VTy>, Icit)>,
        Vec<Span<SmolStr>>,
        bool,
    ),
    SumCase {
        is_trait: bool,
        typ: Rc<Val>,
        case_name: Span<SmolStr>,
        datas: Vec<(Span<SmolStr>, Rc<Val>, Icit)>,
    },
    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>, Option<(SmolStr, Vec<Rc<Val>>)>),
    /// Call(name, args, body) - value inlined from function `name`
    Call(SmolStr, Vec<Rc<Tm>>, Rc<Val>),
    /// 显式替换下的值（模式精化，dpm-nbe `VSub`）：特化解不改写既有值，
    /// 只把解包在外面；`force` 在读点把 σ 推进值的结构（`frcs`，对齐
    /// dpm-nbe 的 `frcS`）。不变式：`force` 的返回值顶层不会是 VSub
    /// （fuel 耗尽时为有界降级的例外，各消费点有防御臂）。
    VSub(Rc<Val>, Rc<Subst>),
}

type VTy = Val;

/// 模式特化的解：层级 → 值 的**持久化单链**（dpm-nbe 的 explicit
/// substitution；链头 = 最新的解）。仅由模式编译器经 `Subst::extend` /
/// 特化合一的 `SpecSolve::acc` 构建；`Rc`（本层 = `Arc`）共享让臂边界
/// 回滚 = 指针赋值、`Val::VSub` 包裹 = O(1)。
///
/// σ 表示为持久化单链（链头 = 最新）：`extend` O(1) cons、`lookup` 沿链
/// 首个命中 + **条件包裹**（解值浅结构不引用任何已解层级时原样返回，零
/// 分配零 fuel；引用才包 `VSub(·, σ)`，由 force 读点推开）。
///
/// 与旧 `update_cxt` 的对应：旧机制把解**改写进环境槽**并 `refresh` 全量
/// 重引用（L07 README §6 淘汰的旧架构，值过期/槽位错位 bug 族的载体）；
/// 新机制不动槽位，只把 σ 包在被消费的值外，force 在读点逐层推开。
#[derive(Debug, Clone, Default)]
pub struct Subst {
    head: Option<Rc<SubEntry>>,
}

#[derive(Debug)]
struct SubEntry {
    lvl: Lvl,
    /// 解的原始值。不预先包裹"更新的解"——读取时 `lookup_hit` 把整条 σ
    /// 包在外面（见其文档），由 force 在读点一次性推开。
    val: Rc<Val>,
    next: Option<Rc<SubEntry>>,
}

impl Subst {
    pub(crate) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配零 fuel）；引用时把整条 σ 包在解值外（解值不含
    /// x 自身——occurs 守卫），由 force 在读点推开。未命中 None。
    pub(crate) fn lookup_hit(self: &Rc<Self>, x: Lvl) -> Option<Rc<Val>> {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return Some(if !Self::mentions_level(&e.val, self) {
                    e.val.clone()
                } else {
                    Rc::new(Val::VSub(e.val.clone(), self.clone()))
                });
            }
            cur = e.next.clone();
        }
        None
    }

    /// x 是否已有解。
    pub(crate) fn has(&self, x: Lvl) -> bool {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return true;
            }
            cur = e.next.clone();
        }
        false
    }

    /// 解值的浅结构是否引用 σ 的某个已解层级。含闭包 **env 槽**（它们是
    /// 值，读点会流出）与 Match 的 scrutinee/captured env/origin 实参；
    /// 不含闭包体 / Match 分支体（Tm，求值时才经 env 读到槽值）。VSub
    /// 保守记为引用。误报只多一次包裹，漏报才会丢精化——扫描口径宁宽勿窄。
    fn mentions_level(v: &Val, sub: &Subst) -> bool {
        fn env_slots(env: &Env, sub: &Subst) -> bool {
            env.iter().any(|v| mentions_level(v, sub))
        }
        fn spine(sp: &Spine, sub: &Subst) -> bool {
            sp.iter().any(|(v, _)| mentions_level(v, sub))
        }
        fn origin(
            o: &Option<(SmolStr, Vec<Rc<Val>>)>,
            sub: &Subst,
        ) -> bool {
            match o {
                Some((_, args)) => args.iter().any(|v| mentions_level(v, sub)),
                None => false,
            }
        }
        fn mentions_level(v: &Val, sub: &Subst) -> bool {
            match v {
                Val::Rigid(y, sp) => sub.has(*y) || spine(sp, sub),
                Val::Flex(_, sp) | Val::Decl(_, sp) => spine(sp, sub),
                Val::Obj(o, _, sp) => mentions_level(o, sub) || spine(sp, sub),
                Val::Lam(_, _, cl) => env_slots(&cl.0, sub),
                Val::Pi(_, _, a, cl) => mentions_level(a, sub) || env_slots(&cl.0, sub),
                Val::Sum(_, params, _, _) => params
                    .iter()
                    .any(|(_, v, t, _)| mentions_level(v, sub) || mentions_level(t, sub)),
                Val::SumCase { typ, datas, .. } => {
                    mentions_level(typ, sub) || datas.iter().any(|(_, v, _)| mentions_level(v, sub))
                }
                Val::Match(s, env, _, o) => {
                    mentions_level(s, sub) || env_slots(env, sub) || origin(o, sub)
                }
                Val::Call(_, _, body) => mentions_level(body, sub),
                // 已被包裹的值保守视为引用（内层结构不再探查）
                Val::VSub(..) => true,
                Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Prim(..) => false,
            }
        }
        mentions_level(v, sub)
    }

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新 ≙ 旧 `update_cxt`
    /// 后写覆盖先写；同键旧条目留在链上但永不命中）。
    pub(crate) fn extend(sub: &Rc<Subst>, x: Lvl, v: Rc<Val>) -> Rc<Subst> {
        Rc::new(Subst {
            head: Some(Rc::new(SubEntry {
                lvl: x,
                val: v,
                next: sub.head.clone(),
            })),
        })
    }

    /// 组合：内层 `inner` 先应用、外层 `outer` 后应用。外层条目接到链头
    /// （先被查到 = 覆盖同键）——对齐旧 `update_cxt` 的"后写覆盖"语义。
    pub(crate) fn compose(outer: &Rc<Subst>, inner: &Rc<Subst>) -> Rc<Subst> {
        fn cons_all(entry: &Option<Rc<SubEntry>>, onto: Option<Rc<SubEntry>>) -> Option<Rc<SubEntry>> {
            match entry {
                None => onto,
                Some(e) => Some(Rc::new(SubEntry {
                    lvl: e.lvl,
                    val: e.val.clone(),
                    next: cons_all(&e.next, onto),
                })),
            }
        }
        Rc::new(Subst {
            head: cons_all(&outer.head, inner.head.clone()),
        })
    }
}

/// η 展开与 frcs 读点共用的可应用性守卫（L07/L09/L10 同款）：只有 `v_app`
/// 能吃的**中性形态**允许应用。L12 的 `v_app` 对 Match（卡住 match）/Prim
/// （卡住内建）/字面量 / U / Π / Sum / SumCase 会 panic——不加守卫会命中
/// `impossible apply`。Lam 亦可被 `v_app` β，但按蓝本口径排除（Lam 与实参
/// 相遇由 η 臂/显式展开处理，frcs 读点保守保持卡住）。
pub(crate) fn v_applicable(v: &Val) -> bool {
    matches!(
        v,
        Val::Flex(..)
            | Val::Rigid(..)
            | Val::Decl(..)
            | Val::Obj(..)
            | Val::Call(..)
            | Val::VSub(..)
    )
}

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc，
/// force 在消费点惰性推开）。σ 为空时零开销直通。
pub(crate) fn wrap_sub(sub: &Rc<Subst>, v: Rc<Val>) -> Rc<Val> {
    if sub.is_empty() {
        v
    } else {
        Rc::new(Val::VSub(v, sub.clone()))
    }
}

/// 展开燃料：每个展开步骤消耗 1，耗尽即停止（防环）。
fn burn(cell: &std::cell::Cell<u32>) -> bool {
    let f = cell.get();
    if f == 0 {
        return false;
    }
    cell.set(f - 1);
    true
}

/// 值树里是否出现某层级（浅层结构扫描；闭包体 / Match 分支体跳过——那里
/// 的环由 force 的 fuel 兜底）。特化解的环守卫（`unify_pm` 的 occurs）用。
/// **不扫 Flex 的 spine**（L10 定制同款）：本层元变量以"全 scope 剪枝
/// spine"登记（fresh_meta 的 AppPruning），spine 里合法地含当前方程正在
/// 解的 rigid；扫 spine 会把这类合法解误判成环。元变量内的真环仍由 force
/// 的 fuel 兜底（与旧机制一致）。
fn val_mentions_lvl(v: &Val, x: Lvl) -> bool {
    fn spine(sp: &Spine, x: Lvl) -> bool {
        sp.iter().any(|(v, _)| val_mentions_lvl(v, x))
    }
    fn env_slots(env: &Env, x: Lvl) -> bool {
        env.iter().any(|v| val_mentions_lvl(v, x))
    }
    fn origin(o: &Option<(SmolStr, Vec<Rc<Val>>)>, x: Lvl) -> bool {
        match o {
            Some((_, args)) => args.iter().any(|v| val_mentions_lvl(v, x)),
            None => false,
        }
    }
    match v {
        Val::Rigid(y, sp) => *y == x || spine(sp, x),
        Val::Flex(..) => false,
        Val::Decl(_, sp) => spine(sp, x),
        Val::Obj(o, _, sp) => val_mentions_lvl(o, x) || spine(sp, x),
        Val::Lam(_, _, cl) => env_slots(&cl.0, x),
        Val::Pi(_, _, a, cl) => val_mentions_lvl(a, x) || env_slots(&cl.0, x),
        Val::Sum(_, params, _, _) => params
            .iter()
            .any(|(_, v, t, _)| val_mentions_lvl(v, x) || val_mentions_lvl(t, x)),
        Val::SumCase { typ, datas, .. } => {
            val_mentions_lvl(typ, x) || datas.iter().any(|(_, v, _)| val_mentions_lvl(v, x))
        }
        Val::Match(s, env, _, o) => val_mentions_lvl(s, x) || env_slots(env, x) || origin(o, x),
        Val::Call(_, _, body) => val_mentions_lvl(body, x),
        // 只扫解值自身的结构，**不扫 σ 的映射值**（σ 其它条目合法引用别的
        // 模式变量）。σ 槽位若真引用 x，解包后的 v 结构里自会以 Rigid(x)
        // 出现（对齐旧世界"occurs 只看解的裸值"的语义；更深间接环由 force
        // 的 fuel 兜底）。
        Val::VSub(v, _) => val_mentions_lvl(v, x),
        Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Prim(..) => false,
    }
}

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

fn lookup_function_by_cases(decl: &Decl, cases: &[(PatternDetail, Rc<Tm>)]) -> Option<SmolStr> {
    for (name, (_, body_tm, _, _, _)) in decl {
        if match_has_same_patterns(cases, body_tm) {
            return Some(name.clone());
        }
    }
    None
}

fn match_has_same_patterns(cases: &[(PatternDetail, Rc<Tm>)], tm: &Tm) -> bool {
    match tm {
        Tm::Match(_, inner_cases) => {
            cases.len() == inner_cases.len()
                && cases.iter().zip(inner_cases.iter()).all(|((p1, _), (p2, _))| p1 == p2)
        }
        Tm::Lam(_, _, inner) => match_has_same_patterns(cases, inner),
        _ => false,
    }
}

fn extract_decl_name(tm: &Tm) -> Option<Span<SmolStr>> {
    match tm {
        Tm::Decl(name) => Some(name.clone()),
        Tm::App(t, _, _) => extract_decl_name(t),
        _ => None,
    }
}

fn collect_app_args(tm: &Tm) -> Vec<Rc<Tm>> {
    match tm {
        Tm::App(t, u, _) => {
            let mut args = collect_app_args(t);
            args.push(u.clone());
            args
        }
        _ => vec![],
    }
}

use std::ops::{Add, Sub};
use std::collections::HashMap;

#[derive(Debug)]
pub enum UnifyError {
    Basic,
    Stuck,
    Trait(String),
}

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

pub struct Error(
    pub Span<String>,
    pub Vec<Box<dyn Fn() -> Option<String>>>
);

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // 只渲染第一个字段，输出效果如：Error(Span { ... })
        f.debug_tuple("Error")
            .field(&self.0)
            .finish()
    }
}

impl IError {
    pub fn to_err(self) -> Error {
        Error(self.msg.map(|x| format!("{:?}", x)), vec![])
    }
}

/// unify/force 的共享递归 fuel 池容量（L08 护栏前向传播：L09 重写时
/// 丢失；L12 的 `unify(.., fuel)` 参数只护 Decl 展开重试臂，本池补齐
/// `force` meta 展开与 unify 结构递归的深度防护）。
const UNIFY_FUEL: u32 = 4096;

#[derive(Clone)]
pub struct Infer {
    meta: Vec<MetaEntry>,
    meta_contrains: Vec<(Rc<Val>, Rc<Val>)>,
    trait_solver: typeclass::Synth,
    trait_definition: HashMap<SmolStr, (Vec<(Span<SmolStr>, Raw, Icit)>, Vec<bool>, Vec<(Span<SmolStr>, Vec<(Span<SmolStr>, Raw, Icit)>, Raw)>)>,
    trait_out_param: HashMap<SmolStr, Vec<bool>>,
    pub mutable_map: Rc<std::sync::RwLock<HashMap<String, Rc<Val>>>>,
    pub hover_table: Vec<(Span<()>, Span<()>, Cxt, Rc<Val>)>,
    pub completion_table: Vec<(Span<()>, SmolStr)>,
    /// unify/force 共享 fuel 池（L08 同款）：外层入口（`nf`/`unify_catch`/
    /// canonical 探测点）充值；`unify` 递归与 `force` 的 meta 展开各烧 1，
    /// 耗尽时 unify 按不可合一失败、force 停止展开按未解处理。
    unify_fuel: std::cell::Cell<u32>,
}

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            meta_contrains: vec![],
            trait_solver: Default::default(),
            trait_definition: Default::default(),
            trait_out_param: Default::default(),
            mutable_map: Default::default(),
            hover_table: vec![],
            completion_table: vec![],
            unify_fuel: std::cell::Cell::new(UNIFY_FUEL),
        }
    }
    /// 烧 1 格 fuel；池空返回 `false`（调用方按各自失败语义降级）。
    fn burn_fuel(&self) -> bool {
        let f = self.unify_fuel.get();
        if f == 0 {
            return false;
        }
        self.unify_fuel.set(f - 1);
        true
    }
    /// 外层入口充值（L08 `meta_refuel` 同款纪律）。
    fn refuel(&self) {
        self.unify_fuel.set(UNIFY_FUEL);
    }
    /// fuel 是否已耗尽。消费点：覆盖探测（`probe_accessible`）失败时区分
    /// "预算问题"与"结构冲突"——fuel 耗尽的失败按**可达**处理（保守要求
    /// 覆盖）；反方向（判不可达 → 覆盖检查放过该构造子）会让深负载下的
    /// 非穷尽 match 被静默接受（L07 评审 P1-2 前向传播）。
    pub(crate) fn fuel_exhausted(&self) -> bool {
        self.unify_fuel.get() == 0
    }
    fn new_meta(&mut self, a: Rc<VTy>, cxt: Cxt, origin_typ: Rc<VTy>) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a, std::sync::Arc::new(cxt), origin_typ));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: Rc<VTy>) -> Rc<Tm> {
        // 期望类型可能被精化 σ 包裹：先推开，实例合成 / trait 判形才看得到
        // 真实形态（对齐旧 refresh 后槽值已展开的世界）
        let a = self.force(&cxt.decl, &a);
        if let Ok(Some((a, _))) = self.solve_trait(cxt, &a) {
            a
        } else if let Val::Sum(_, _, _, true) = a.as_ref() {
            let m = self.new_meta(a.clone(), cxt.clone(), a);
            Tm::Meta(MetaVar(m)).into()
        } else {
            //let temp = &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a));
            //println!("{:?}: {}", a, pretty_tm(0, cxt.names(), temp));
            //println!("{:?}: {:?}", a, temp);
            let closed = self.eval(
                &cxt.decl,
                &List::new(),
                &close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a)),
            );
            let m = self.new_meta(closed, cxt.clone(), a);
            Tm::AppPruning(Tm::Meta(MetaVar(m)).into(), cxt.pruning.clone()).into()
        }
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, decl: &Decl, t: &Rc<Val>) -> Rc<Val> {
        //println!("{} {:?}", "force".red(), t);
        match t.as_ref() {
            Val::Flex(m, sp) => match self.lookup_meta(*m) {
                // 展开烧 fuel（L08 前向传播）：solve 无跨 meta occurs check，
                // 解链成环时展开会无限递归；池空停止展开、按未解处理
                MetaEntry::Solved(t_solved, _) if self.burn_fuel() => {
                    self.force(decl, &self.v_app_sp(decl, t_solved.clone(), sp))
                }
                _ => Val::Flex(*m, sp.clone()).into(),
            },
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1），对齐旧 `update_cxt`+`refresh`
            // 时代"读到被解槽才展开"的燃烧剖面；包裹/组合的机械开销免费。
            Val::VSub(v, sub) => self.frcs(decl, sub, v.clone()),
            Val::Obj(x, a, b) => {
                Val::Obj(self.force(decl, x), a.clone(), b.clone()).into()
            }
            Val::Call(name, args, body) => {
                Val::Call(name.clone(), args.clone(), self.force(decl, body)).into()
            }
            _ => t.clone(),
        }
    }

    /// 把替换 `σ` 推进值 `v` 的结构（dpm-nbe `frcS`）。与 `force` 的分工：
    /// σ 是本次精化的局部解，只作用于**被包裹过**的值；推进到中性头为止
    /// ——spine 逐槽推进，闭包 env 逐槽包裹（惰性，不进入闭包体重求值）；
    /// Scrutinee 推进后可重选分支。对应 dpm-nbe `napp (lookupSub sb v)
    /// (frcS sb sp)`。
    fn frcs(&self, decl: &Decl, sub: &Rc<Subst>, v: Rc<Val>) -> Rc<Val> {
        if sub.is_empty() {
            return self.force(decl, &v);
        }
        match v.as_ref() {
            // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
            Val::VSub(v2, sub2) => {
                let composed = Subst::compose(sub, sub2);
                self.frcs(decl, &composed, v2.clone())
            }
            // 被解变量的读点：lookup 命中（真正的精化传播）烧 1 fuel——
            // 对齐旧 refresh 重求值被解槽的燃烧剖面；fuel 耗尽按未解处理
            // （返回裸 rigid，有界降级，防闭环无限推进）。解值带实参但头
            // 不可应用（对非函数解变量做应用的 ill-typed 形态）时保持卡住。
            Val::Rigid(x, sp) => {
                let mut head = match sub.lookup_hit(*x) {
                    Some(hit) => {
                        if !burn(&self.unify_fuel) {
                            return Rc::new(Val::Rigid(*x, sp.clone()));
                        }
                        self.force(decl, &hit)
                    }
                    None => Rc::new(Val::vvar(*x)),
                };
                if !sp.is_empty() && !v_applicable(&head) {
                    return Rc::new(Val::Rigid(*x, sp.clone()));
                }
                let args: Vec<(Rc<Val>, Icit)> = sp.iter().cloned().collect();
                for (u, i) in args.into_iter().rev() {
                    head = self.v_app(decl, &head, wrap_sub(sub, u), i);
                }
                head
            }
            // 中性头的 spine 槽只**包裹**不推进——槽位引用是作用域事实，
            // 物化会破坏后续 solve 的 invert（与 force_arg 的分工同一理由；
            // 旧 force 也从不触碰 spine 槽）。包裹后交回 force 重走既有臂
            // （meta 解 / 投影 / Call 内联）。
            Val::Flex(m, sp) => {
                self.force(decl, &Rc::new(Val::Flex(*m, self.wrap_sp(sub, sp.clone()))))
            }
            Val::Decl(name, sp) => {
                self.force(decl, &Rc::new(Val::Decl(name.clone(), self.wrap_sp(sub, sp.clone()))))
            }
            Val::Obj(o, name, sp) => self.force(decl, &Rc::new(Val::Obj(
                self.frcs(decl, sub, o.clone()),
                name.clone(),
                self.wrap_sp(sub, sp.clone()),
            ))),
            Val::Call(name, args, body) => self.force(decl, &Rc::new(Val::Call(
                name.clone(),
                args.clone(),
                self.frcs(decl, sub, body.clone()),
            ))),
            // 闭包 env 逐槽包裹（dpm-nbe `subst sb cl` 的惰性形态）
            Val::Lam(x, i, cl) => Rc::new(Val::Lam(
                x.clone(),
                *i,
                Closure(self.frcs_env(sub, &cl.0), cl.1.clone()),
            )),
            Val::Pi(x, i, a, cl) => Rc::new(Val::Pi(
                x.clone(),
                *i,
                self.frcs(decl, sub, a.clone()),
                Closure(self.frcs_env(sub, &cl.0), cl.1.clone()),
            )),
            // Sum/SumCase 的槽位同样只包裹（旧 force 不进入这些结构）
            Val::Sum(name, params, cases, is_trait) => Rc::new(Val::Sum(
                name.clone(),
                params
                    .iter()
                    .map(|(n, v, t, i)| {
                        (
                            n.clone(),
                            wrap_sub(sub, v.clone()),
                            wrap_sub(sub, t.clone()),
                            *i,
                        )
                    })
                    .collect(),
                cases.clone(),
                *is_trait,
            )),
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => Rc::new(Val::SumCase {
                is_trait: *is_trait,
                typ: wrap_sub(sub, typ.clone()),
                case_name: case_name.clone(),
                datas: datas
                    .iter()
                    .map(|(n, v, i)| (n.clone(), wrap_sub(sub, v.clone()), *i))
                    .collect(),
            }),
            // scrutinee **推进**：旧 `refresh` 在槽值重求值时，若被解变量
            // 是卡住 match 的 scrutinee，会连带重选分支——这里等价地在
            // 推进后若已是构造子值就按首匹配重选。捕获 env 与 Call origin
            // 实参只包裹。
            Val::Match(s, env, cases, origin) => {
                let s2 = self.frcs(decl, sub, s.clone());
                let env2 = self.frcs_env(sub, env);
                if matches!(s2.as_ref(), Val::SumCase { .. }) && burn(&self.unify_fuel) {
                    if let Some((tm, env3)) = Compiler::eval_aux(self, &s2, decl, &env2, cases) {
                        return self.force(decl, &self.eval(decl, &env3, &tm));
                    }
                }
                Rc::new(Val::Match(
                    s2,
                    env2,
                    cases.clone(),
                    origin
                        .clone()
                        .map(|(n, args)| (n, args.into_iter().map(|a| wrap_sub(sub, a)).collect())),
                ))
            }
            // U / 字面量 / Prim：σ 无从推进（Prim 携带的 typ 是内建登记类型，
            // 与精化解无关）
            Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Prim(..) => v,
        }
    }

    fn wrap_sp(&self, sub: &Rc<Subst>, sp: Spine) -> Spine {
        if sp.is_empty() {
            return sp;
        }
        sp.map(|(v, i)| (wrap_sub(sub, v.clone()), *i))
    }

    fn frcs_env(&self, sub: &Rc<Subst>, env: &Env) -> Env {
        if sub.is_empty() {
            return env.clone();
        }
        env.map(|v| Rc::new(Val::VSub(v.clone(), sub.clone())))
    }

    /// `to_typ` / trait 求解等"结构消费者"的深读点：force 到 WHNF 后，若
    /// 顶层是 Sum/SumCase，把**槽位值也 force 推开**（旧机制下这些槽位已被
    /// update_cxt/refresh 物化；新机制只包裹，故此处按需展开）。只服务
    /// trait 求解边界（非热路径），不进入 spine/闭包体。
    pub(crate) fn force_deep(&self, decl: &Decl, v: &Rc<Val>) -> Rc<Val> {
        let v = self.force(decl, v);
        match v.as_ref() {
            Val::Sum(name, params, cases, is_trait) => Rc::new(Val::Sum(
                name.clone(),
                params
                    .iter()
                    .map(|(n, x, t, i)| {
                        (n.clone(), self.force_deep(decl, x), self.force_deep(decl, t), *i)
                    })
                    .collect(),
                cases.clone(),
                *is_trait,
            )),
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => Rc::new(Val::SumCase {
                is_trait: *is_trait,
                typ: self.force_deep(decl, typ),
                case_name: case_name.clone(),
                datas: datas
                    .iter()
                    .map(|(n, x, i)| (n.clone(), self.force_deep(decl, x), *i))
                    .collect(),
            }),
            _ => v,
        }
    }

    /// 合一器**参数视角**的 WHNF：与 `force` 相同，但不展开精化、不做
    /// Match 重选。`invert` / `prune_vflex` 关心的是"元变量被应用在哪些
    /// **槽位**上"——槽位引用（`Rigid(x)`）本身就是作用域事实，分支内的
    /// 精化等式（x := zero）不改变槽位的存在；在它们身上展开反而会把可逆
    /// spine 变成含构造子值的不可逆 spine。逐层解包 VSub（subst_cxt 可
    /// 叠加——嵌套 match 的上下文被外层臂与内层臂各包一次）。
    pub(crate) fn force_arg(&self, decl: &Decl, t: &Rc<Val>) -> Rc<Val> {
        {
            let mut cur: &Val = t.as_ref();
            while let Val::VSub(v, _) = cur {
                cur = v.as_ref();
            }
            match cur {
                Val::Rigid(x, sp) if sp.is_empty() => {
                    return Rc::new(Val::Rigid(*x, List::new()));
                }
                Val::Rigid(..) | Val::Match(..) => return t.clone(),
                _ => {}
            }
        }
        self.force(decl, t)
    }
    fn v_meta(&self, m: MetaVar) -> Rc<Val> {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_, _, _) => Val::vmeta(m).into(),
        }
    }

    fn closure_apply(&self, decl: &Decl, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(decl, &closure.0.prepend(u), &closure.1)
    }

    fn v_app(&self, decl: &Decl, t: &Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
        //println!("v_app {t:?} {u:?}");
        match t.as_ref() {
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点会把
            // VSub 头送进来——如臂上下文里 Var 引用了被解槽；force 顶层不再
            // 产出 VSub，递归必终止）
            Val::VSub(..) => {
                let t = self.force(decl, t);
                self.v_app(decl, &t, u, i)
            }
            Val::Lam(_, _, closure) => self.closure_apply(decl, closure, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
            Val::Decl(x, sp) => Val::Decl(x.clone(), sp.prepend((u, i))).into(),
            Val::Obj(x, name, sp) => Val::Obj(x.clone(), name.clone(), sp.prepend((u, i))).into(),
            Val::Call(_, _, body) => self.v_app(decl, body, u, i),
            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
        }
    }

    fn v_app_sp(&self, decl: &Decl, t: Rc<Val>, spine: &Spine) -> Rc<Val> {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(decl, &self.v_app_sp(decl, t, &a.tail()), u.clone(), *i)
            }
        }
    }

    fn v_app_pruning(&self, decl: &Decl, env: &Env, v: Rc<Val>, pr: &Pruning) -> Rc<Val> {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                decl,
                &self.v_app_pruning(decl, &a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(decl, &a.tail(), v, &b.tail())
            }
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, decl: &Decl, env: &Env, tm: &Rc<Tm>) -> Rc<Val> {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm.as_ref() {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => panic!("var {:?} not found", x.0),
            },
            Tm::Decl(x) => decl.get(&x.data).map(|x| x.2.clone()).unwrap_or(Val::Decl(x.clone(), List::new()).into()),//TODO:directly unwrap?
            Tm::Obj(tm, name) => {
                let a = self.eval(decl, env, tm);
                let a = self.force(decl, &a);
                match a.as_ref() {
                    Val::Sum(_, params, _, _) => {
                        params.iter()
                            .find(|(f_name, _, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    Val::SumCase { datas, typ, .. } => {
                        (match typ.as_ref() {
                            Val::Sum(_, params, _, _) => params,
                            _ => panic!("impossible {typ:?}"),
                        }).iter()
                            .map(|x| (x.0.clone(), x.1.clone(), x.3))
                            .chain(datas.iter().cloned())
                        //datas.into_iter()
                            .find(|(f_name, _, _)| f_name == name)
                            .unwrap().1.clone()
                    },
                    _ => {
                        Val::Obj(a, name.clone(), List::new()).into()
                    },
                }
            }
            Tm::App(t, u, i) => self.v_app(decl, &self.eval(decl, env, t), self.eval(decl, env, u), *i),
            Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone())).into(),
            Tm::Pi(x, i, a, b) => {
                Val::Pi(x.clone(), *i, self.eval(decl, env, a), Closure(env.clone(), b.clone())).into()
            }
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(decl, env, t);
                self.eval(decl, &env.prepend(t_val), u)
            }
            Tm::U(x) => Val::U(*x).into(),
            Tm::Meta(m) => self.v_meta(*m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(decl, env, self.eval(decl, env, t), pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x.clone()).into(),
            Tm::LiteralType => Val::LiteralType.into(),
            Tm::Prim(typ, func) => func.0(self, decl, env, typ.clone()),
            Tm::Sum(name, params, cases, is_trait) => {
                let new_params = params
                    .iter()
                    .map(|x| (x.0.clone(), self.eval(decl, env, &x.1), self.eval(decl, env, &x.2), x.3))
                    .collect();
                Val::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Tm::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| (p.0.clone(), self.eval(decl, env, &p.1), p.2))
                    .collect();
                let typ = self.eval(decl, env, typ);
                Val::SumCase {
                    is_trait: *is_trait,
                    typ,
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Tm::Call(name, _, val_args, body) => {
                let result = self.eval(decl, env, body);
                if let Val::Match(scrut, env, cases, _) = result.as_ref() {
                    Val::Match(scrut.clone(), env.clone(), cases.clone(), Some((name.clone(), val_args.clone()))).into()
                } else {
                    result
                }
            },
            Tm::Match(tm, cases) => {
                let val = self.eval(decl, env, tm);
                let val = self.force(decl, &val);
                match val.as_ref() {
                    Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, &val, decl, env, cases) {
                            Some((tm, env)) => self.eval(decl, &env, &tm),
                            None => Val::Match(val, env.clone(), cases.clone(), None).into(),
                        }
                    }
                    _ => {
                        Val::Match(val, env.clone(), cases.clone(), None).into()
                    }
                }
            }
        }
    }

    fn quote_sp(&self, decl: &Decl, l: Lvl, t: Rc<Tm>, spine: &Spine) -> Rc<Tm> {
        /*spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })*/
        match spine {
            List { head: None, .. } => t,
            _ => {
                let head = spine.head().unwrap();
                Tm::App(self.quote_sp(decl, l, t, &spine.tail()), self.quote(decl, l, &head.0), head.1).into()
            }
        }
    }

    pub fn quote(&self, decl: &Decl, l: Lvl, t: &Rc<Val>) -> Rc<Tm> {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(decl, t);
        match t.as_ref() {
            Val::Flex(m, sp) => self.quote_sp(decl, l, Tm::Meta(*m).into(), sp),
            Val::Rigid(x, sp) => self.quote_sp(decl, l, Tm::Var(lvl2ix(l, *x)).into(), sp),
            Val::Decl(x, sp) => self.quote_sp(decl, l, Tm::Decl(x.clone()).into(), sp),
            Val::Obj(x, name, sp) => self.quote_sp(decl, l, Tm::Obj(self.quote(decl, l, x), name.clone()).into(), sp),
            Val::Lam(x, i, closure) => Tm::Lam(
                x.clone(),
                *i,
                self.quote(decl, l + 1, &self.closure_apply(decl, closure, Val::vvar(l).into())),
            ).into(),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x.clone(),
                *i,
                self.quote(decl, l, a),
                self.quote(decl, l + 1, &self.closure_apply(decl, closure, Val::vvar(l).into())),
            ).into(),
            Val::U(x) => Tm::U(*x).into(),
            Val::LiteralIntro(x) => Tm::LiteralIntro(x.clone()).into(),
            Val::LiteralType => Tm::LiteralType.into(),
            Val::Prim(typ, func) => Tm::Prim(typ.clone(), func.clone()).into(),
            Val::Sum(name, params, cases, is_trait) => {
                let new_params = params.iter()
                    .map(|x| {
                        (x.0.clone(), self.quote(decl, l, &x.1), self.quote(decl, l, &x.2), x.3)
                    })
                    .collect();
                Tm::Sum(name.clone(), new_params, cases.clone(), *is_trait).into()
            }
            Val::SumCase {
                is_trait,
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| {
                        (p.0.clone(), self.quote(decl, l, &p.1), p.2)
                    })
                    .collect();
                Tm::SumCase {
                    is_trait: *is_trait,
                    typ: self.quote(decl, l, typ),
                    case_name: case_name.clone(),
                    datas,
                }.into()
            }
            Val::Call(name, args, body) => {
                let quoted_body = self.quote(decl, l, body);
                Tm::Call(name.clone(), args.clone(), vec![], quoted_body).into()
            },
            Val::Match(val, env, cases, origin) => {
                /*TODO:let tm_cases = cases
                    .into_iter()
                    .map(|(p, clos)| {
                        let binders_count = p.count_binders();
                        let body_tm = self.quote(l + binders_count, self.closure_apply_pats(&clos, l, &p));
                        (p, body_tm)
                    })
                    .collect();*/
                // 中性 decl 表只依赖 decl，与分支无关——提到分支循环外
                // （对齐 L07/L08 `simpl_decl` 的位置），避免 #分支 × |decls|
                // 次全表重建。
                let declb = decl.iter()
                    .map(|x| (x.0.clone(), (
                        x.1.0,
                        Tm::Decl(x.1.0.map(|_| x.0.clone())).into(),
                        Val::Decl(x.1.0.map(|_| x.0.clone()), List::new()).into(),
                        x.1.3.clone(),
                        x.1.4.clone(),
                    )))
                    .collect();
                let tm_cases = cases
                    .iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, x| env.prepend(Val::vvar(l + x).into()));
                            let tm = self.eval(&declb, &env, &x.1);
                            self.quote(decl, l+x.0.bind_count(), &tm)
                        }
                    ))
                    .collect();
                let quoted_match = Tm::Match(self.quote(decl, l, val), tm_cases).into();
                let effective_origin = match origin {
                    Some((n, a)) => Some((n.clone(), a.clone())),
                    None => lookup_function_by_cases(decl, cases).map(|name| (name, vec![val.clone()])),
                };
                if let Some((name, arg_vals)) = effective_origin {
                    let display_args: Vec<Rc<Tm>> = arg_vals.iter()
                        .map(|v| self.quote(decl, l, v))
                        .collect();
                    Tm::Call(name.clone(), display_args, arg_vals.clone(), quoted_match).into()
                } else {
                    quoted_match
                }
            }
            // 不变式：force 的返回值顶层不会是 VSub；fuel 耗尽的降级返回
            // 裸 rigid 而非 VSub，故此臂仅在极端角落可达（解包内层继续
            // quote，链式 VSub 由递归消化）。
            Val::VSub(v, _) => self.quote(decl, l, v),
        }
    }

    pub fn nf(&self, decl: &Decl, env: &Env, t: &Rc<Tm>) -> Rc<Tm> {
        // quote → eval 会 force；一次 nf 充值 fuel 防循环解（L08 同款）
        self.refuel();
        let l = Lvl(env.iter().count() as u32);
        self.quote(decl, l, &self.eval(decl, env, t))
    }

    fn close_val(&self, cxt: &Cxt, t: &Rc<Val>) -> Closure {
        Closure(cxt.env.clone(), self.quote(&cxt.decl, cxt.lvl + 1, t))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>, span: Span<()>) -> Result<(), Error> {
        self.meta_contrains.clear();
        self.refuel();
        let ret = self.unify(cxt.lvl, cxt, t, t_prime, 100)
            .map_err(|e| {
                /*Error::CantUnify(
                    cxt.clone(),
                    self.quote(cxt.lvl, t),
                    self.quote(cxt.lvl, t_prime),
                )*/
                //println!("{:?} == {:?}", t, t_prime);
                //println!("{:?}", self.eval(&cxt.env, self.quote(cxt.lvl, t_prime.clone())));
                /*panic!(
                    //"can't unify {:?} == {:?}",
                    "can't unify\n      find: {}\n  expected: {}",
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                );*/
                let err = match e {
                    UnifyError::Basic | UnifyError::Stuck => format!(
                        //"can't unify {:?} == {:?}",
                        "can't unify\n  expected: {}\n      find: {}",
                        pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                        pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                    ),
                    UnifyError::Trait(e) => e,
                };
                Error(span.map(|_| err.clone()), vec![])
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            });
        if !self.meta_contrains.is_empty() {
            let err = format!(
                    //"can't unify {:?} == {:?}",
                    "can't unify for unsolved meta\n  expected: {}\n      find: {}",
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(&cxt.decl, cxt.lvl, t_prime)),
                );
            self.meta_contrains.clear();
            Err(Error(span.map(|_| err.clone()), vec![]))?
        }
        self.meta_contrains.clear();
        ret
    }
}

#[allow(unused)]
pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(&preprocess(input), path_id).unwrap();
    let mut cxt = Cxt::new(&infer);
    let mut ret = String::new();
    //TODO: do not print err. return error
    for e in ast.1 {
        println!("{:?}", e)
    }
    for tm in ast.0 {
        match &tm {
            parser::syntax::Decl::Def { name, .. }
            | parser::syntax::Decl::Enum { name, .. }
            | parser::syntax::Decl::TraitDecl { name, .. } => {
                println!("> {}", name.data);
                //cxt.print_env(&infer);
            },
            parser::syntax::Decl::Println(raw) => {},
            parser::syntax::Decl::ImplDecl { .. } => {
                println!("> impl");
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &s;
            ret += "\n";
        }
    }
    /*cxt.env
        .iter()
        .zip(cxt.names().iter())
        .for_each(|(ty, name)| {
            println!("{}: {}", name, pretty::pretty_tm(0, cxt.names(), &infer.quote(cxt.lvl, ty.clone())));
            //println!("{:?}\n", ty);
        });*/
    Ok(ret)
}

#[allow(unused)]
pub fn run_with_prelude(input: &str) -> Result<String, Error> {
    let mut infer = Infer::new();
    let prelude = &[
        include_str!("../prelude/core/op.typort"),
        include_str!("../prelude/core/eq.typort"),
        include_str!("../prelude/core/nat.typort"),
        include_str!("../prelude/core/bool.typort"),
        include_str!("../prelude/data/option.typort"),
        include_str!("../prelude/data/result.typort"),
        include_str!("../prelude/data/order.typort"),
        include_str!("../prelude/core/void.typort"),
        include_str!("../prelude/data/decidable.typort"),
        include_str!("../prelude/data/vec.typort"),
        include_str!("../prelude/data/either.typort"),
        include_str!("../prelude/data/list.typort"),
        include_str!("../prelude/data/string.typort"),
        include_str!("../prelude/data/nonempty.typort"),
        include_str!("../prelude/hdl/hdl-core.typort"),
        include_str!("../prelude/hdl/hdl-types.typort"),
        include_str!("../prelude/hdl/hdl-ops.typort"),
        include_str!("../prelude/hdl/hdl-clock.typort"),
        include_str!("../prelude/hdl/hdl-bus.typort"),
        include_str!("../prelude/hdl/hdl-signals.typort"),
        include_str!("../prelude/hdl/hdl-macros.typort"),
        include_str!("../prelude/hdl/hdl-verilog.typort"),
        include_str!("../prelude/show.typort"),
    ];
    let mut cxt = Cxt::new(&infer);
    let mut ret = String::new();

    // Accumulate exported macros from prelude files
    let mut global_macros: std::collections::HashMap<String, Vec<parser::macros::MacroRule>> = Default::default();
    let mut id = 0;
    for p in prelude {
        if let Some((decls, parse_errs, new_exports, _)) = parser::parser_with_macros(&preprocess(p), id, &global_macros) {
            for ast_err in parse_errs {
                println!("{:?}", ast_err)
            }
            for (name, rules) in new_exports {
                global_macros.insert(name, rules);
            }
            for tm in decls {
                let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
                cxt = new_cxt;
            }
        }
        id += 1;
    }
    // Parse main file with accumulated macros from prelude
    let ast = parser::parser_with_macros(&preprocess(input), prelude.len() as u32, &global_macros)
        .map(|(d, e, _, _)| (d, e))
        .unwrap();
    println!("-----------------");
    //TODO: do not print err. return error
    for e in ast.1 {
        println!("{:?}", e)
    }
    for tm in ast.0 {
        match &tm {
            parser::syntax::Decl::Def { name, .. }
            | parser::syntax::Decl::Enum { name, .. }
            | parser::syntax::Decl::TraitDecl { name, .. } => {
                println!("> {}", name.data);
                //cxt.print_env(&infer);
            },
            parser::syntax::Decl::Println(raw) => {},
            parser::syntax::Decl::ImplDecl { .. } => {
                println!("> impl");
            }
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(_, s, _) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &s;
            ret += "\n";
        }
    }
    /*cxt.env
        .iter()
        .zip(cxt.names().iter())
        .for_each(|(ty, name)| {
            println!("{}: {}", name, pretty::pretty_tm(0, cxt.names(), &infer.quote(cxt.lvl, ty.clone())));
            //println!("{:?}\n", ty);
        });*/
    Ok(ret)
}

// 单遍扫描 + 单输出缓冲（与 L13_namespace::preprocess 同实现，彼处有
// 黄金校验记录：全仓 .typort 逐文件 diff + 差分模糊测试——等字节长不变
// 量保持 parser span 偏移；原两遍 reduce 折叠第 i 步重拷前 i 段全部字节）。
pub fn preprocess(s: &str) -> String {
    // 单遍扫描 + 单输出缓冲：一次左到右扫描同时完成原「块注释 → 行注释」
    // 两遍变换，任何字节只写一次。旧实现逐行/逐块 `reduce(|a, b| a + sep + &b)`
    // 折叠——第 i 步重拷前 i 段全部字节，O(字节数 × 行数)（LSP 每按键跑 2 遍，
    // perf-debt 共享层发现 1）。
    //
    // 与旧实现的逐字节一致性（含全部边界怪癖）：
    // - 旧第一遍按 `/*` 切块：每块内首个 `*/` 之前的文本换等字节空白、`*/`
    //   换两空格，其后原样；无 `*/` 的块整体原样（含 `*/` 先于任何 `/*` 的
    //   块、嵌套 `/*` 重新切块后未闭合的前段）。这里用区间扫描完全复刻：
    //   chunk = 相邻 `/*` 之间的文本，块内首个 `*/`（不得越过块边界——与
    //   `/*` 跨界重叠的匹配不算，如 `a*/*b`）之前空白化。
    // - 旧第二遍按行处理第一遍的输出：行内首个「存活」的 `//` 换两空格、
    //   到行尾换等字节空白。这里以 line_blank 状态融合进同一遍：仅原样区
    //   间里的 `//` 会存活（空白化区间里的 `//` 已被第一遍吃掉），触发后到
    //   `\n` 为止全部空白化，`\n` 复位。
    // - 空白化按 char 语义（is_whitespace 的原 char 保留、其余按 len_utf8
    //   换空格），与旧 replace_non_ws_preserve_bytes 完全一致，保持 parser
    //   span 字节偏移不变量；输出与旧实现逐字节一致（黄金校验：全仓
    //   .typort 逐文件 diff + 差分模糊测试 + lib 测试）。
    // - 不变量：输出与输入等字节长。
    let mut out = String::with_capacity(s.len());
    // 行注释状态：触发后到 `\n` 为止输出全部空白化
    let mut line_blank = false;

    // 块注释内部区间发射：等字节空白，保留换行（并复位行注释状态）
    fn emit_blanked(region: &str, out: &mut String, line_blank: &mut bool) {
        for c in region.chars() {
            if c == '\n' {
                out.push('\n');
                *line_blank = false;
            } else if c.is_whitespace() {
                out.push(c);
            } else {
                for _ in 0..c.len_utf8() {
                    out.push(' ');
                }
            }
        }
    }

    // 原样区间发射 + 行注释融合：首个存活的 `//` 触发行空白化
    fn emit_raw(region: &str, out: &mut String, line_blank: &mut bool) {
        let bytes = region.as_bytes();
        let mut j = 0usize;
        while j < region.len() {
            if *line_blank {
                let c = region[j..].chars().next().unwrap();
                if c == '\n' {
                    out.push('\n');
                    *line_blank = false;
                } else if c.is_whitespace() {
                    out.push(c);
                } else {
                    for _ in 0..c.len_utf8() {
                        out.push(' ');
                    }
                }
                j += c.len_utf8();
            } else if bytes[j] == b'/' && j + 1 < bytes.len() && bytes[j + 1] == b'/' {
                // 行注释头：`//` 换两空格，行尾前全部空白化
                out.push_str("  ");
                *line_blank = true;
                j += 2;
            } else {
                // 批量拷贝到下一个 '/'（ASCII，必在 char 边界）；孤 '/' 原样推入
                match bytes[j..].iter().position(|&b| b == b'/') {
                    Some(k) if k > 0 => {
                        out.push_str(&region[j..j + k]);
                        j += k;
                    }
                    Some(_) => {
                        out.push('/');
                        j += 1;
                    }
                    None => {
                        out.push_str(&region[j..]);
                        j = region.len();
                    }
                }
            }
        }
    }

    // 块注释主扫描：chunk = 相邻 `/*` 之间的文本
    let mut i = 0usize;
    loop {
        let next_open = s[i..].find("/*").map(|p| i + p);
        let chunk_end = next_open.unwrap_or(s.len());
        match s[i..chunk_end].find("*/") {
            Some(qrel) => {
                let q = i + qrel;
                emit_blanked(&s[i..q], &mut out, &mut line_blank);
                // `*/` → 两空格
                out.push_str("  ");
                emit_raw(&s[q + 2..chunk_end], &mut out, &mut line_blank);
            }
            None => emit_raw(&s[i..chunk_end], &mut out, &mut line_blank),
        }
        match next_open {
            Some(p) => {
                // `/*` → 两空格，下一块从标记之后开始
                out.push_str("  ");
                i = p + 2;
            }
            None => break,
        }
    }
    debug_assert_eq!(out.len(), s.len(), "preprocess 必须保持等字节长");
    out
}


#[test]
fn test_trait() {
    let input = r#"
def outParam[A](a: A): A = a

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def two = succ (succ zero)

trait Say {
    def say(x: Nat): String
}

impl[T] Say for T {
    def say(x: Nat): String = "hello"
}

println (zero.say zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

def t[T][s: ToString[T]](x: T): String =
    s.to_string x

println (t true)

trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat =
        nat_add_helper this that
}

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => y + (mul n y)
}

def four = two + two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

impl Add[Point[Nat], Point[Nat]] for Point[Nat] {
    def +(that: Point[Nat]): Point[Nat] =
        new Point(this.x + that.x, this.y + that.y)
}

impl Add[Nat, Point[Nat]] for Point[Nat] {
    def +(that: Nat): Point[Nat] =
        new Point(this.x + that, this.y + that)
}

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (start_point + end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("hello"));
    assert!(result.contains("Bool::false"));
    assert!(result.contains("true"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
}

#[test]
fn test5() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => cons(x, t xs ys)
        }
    }

impl[T, len: Nat] Vec[T](len) {
    def map[U](f: T -> U): Vec[U] len =
        match this {
            case nil => nil
            case cons(x, xs) => cons(f x, xs.map f)
        }
}

def tt = cons(zero, cons(zero, nil)).map[U=Nat](x => match x {
    case succ(z) => succ(zero)
    case zero => zero
})

def z[len: Nat](x: Vec[Nat]len) = match x {
    case nil => 1
    case cons[l=lll](x, xs) => lll
}

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test6() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t[len: Nat](x: Vec[Nat] len, y: Vec[Nat] len): Vec[Nat] (succ len) =
    match x {
        case nil => cons zero nil
        case cons(x, xs) => match y {
            case cons(y, ys) => match t xs ys {
                case cons(z, zs) => cons(zero, cons zero zs)
            }
        }
    }

def ttt =
    let useless1 = create_global "Nat" 2;
    let useless2 = change_mutable("Nat", z => succ(z));
    get_global "Nat"

println ttt

println stringify t123

macro_rules module {
    ($name: ident $body: raw) => {def $name = string_concat(string_concat("module ", stringify $name), $body)};
    ($name: ident) => {def $name = string_concat("module ", stringify $name)};
}

module test1 " {}"

println test1

module test2

println test2

"#;
    println!("{}", run(input, 0).unwrap());
}

#[test]
fn test4() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) =
    match x {
        case zero => zero
        case succ(n) => add(y, mul n y)
    }

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq (add (n, succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq (add (add n m) k) (add(n, add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

def double(n: Nat): Nat = add n n

def double_pow(k: Nat, n: Nat): Nat =
    match k {
        case zero => n
        case succ(k) => double(double_pow k n)
    }

def double_add(a: Nat, b: Nat): Eq(double(add a b), add(double a, double b)) =
    let e1 = add_assoc(a, b, add a b);
    let e2 = cong[f=add a](add_comm (b, add a b));
    let e3 = symm (add_assoc (a, add a b, b));
    let e4 = symm (cong[f=x => add x b] (add_assoc a a b));
    let e5 = add_assoc (add a a) b b;
    trans(e1, trans(e2, trans(e3, trans e4 e5)))

def prove(k: Nat, a: Nat, b: Nat): Eq(double_pow(k, add a b), add (double_pow k a) (double_pow k b)) =
    match k {
        case zero => rfl
        case succ(kk) => let ih = prove kk a b;
            let ih1 = cong[f=double] ih;
            let ih2 = double_add(double_pow(kk, a), double_pow(kk, b));
            trans ih1 ih2
    }
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    println!("success");
}

#[test]
fn test2() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons (true, cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add (y, mul n y)
}

def four = add two two

println four

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

def Eq[A](x: A, y: A) = (P : A -> Type 0) -> P x -> P y

def refl[A, x: A]: Eq[A] x x = _ => px => px

struct Bits {
    name: String
    size: Nat
}

def get_name(x: Bits) = x.name

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = a.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB refl

def cd = assign sigC sigD refl

"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Bool::false"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def test1: Type 2 = Type 1 -> Type 0

struct HighLvl[A] {
    case1: A
    case2: test1
}

def test2_t: Type 1 -> Type 0 = t => Nat

def test2: HighLvl[Nat] = new HighLvl(zero, test2_t)

def test3: Type 2 = HighLvl[Nat]

struct HighLvl2[A: Type 2] {
    case2_1: A
    case2_2: Nat
}

def test1_2: HighLvl2[HighLvl[Nat]] = new HighLvl2(test2, zero)

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

struct HighLvl3[A: Type 2] {
    case3_1: Nat
    case3_2: Nat
}

def test2_2: HighLvl3[HighLvl[Nat]] = new HighLvl3(zero, zero)

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    println!("success");
}

#[test]
fn test0() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons(n, taill) => match rhs {
            case cons(m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons(c, tail) => match full_adder n m c {
                    case product(a, b) => cons (a, cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Vec[Bool]::cons(1, Bool::false, Vec[Bool]::cons(0, Bool::true, Vec[Bool]::nil)"));
}

#[test]
pub fn test_index() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def test: Eq two two = refl

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def t = cons (zero, cons(two, cons(three, cons two nil)))

println t.len

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

println (head (cons zero nil))

def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

    "#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("4"));
    assert!(result.contains("0"));
}

#[test]
fn test7() {
    let input = r#"
enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Product[A, B] {
    product(a: A, b: B)
}

def half_adder(lhs: Bool, rhs: Bool): Product[Bool][Bool] =
    match lhs {
        case false => product false rhs
        case true => match rhs {
            case false => product false true
            case true => product true false
        }
    }

def full_adder(lhs: Bool, rhs: Bool, carrier: Bool): Product[Bool][Bool] =
    match lhs {
        case false => half_adder rhs carrier
        case true => match rhs {
            case false => half_adder true carrier
            case true => product true carrier
        }
    }

def bits_adder_carrier[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len, carrier: Bool): Vec[Bool] (succ len) =
    match lhs {
        case nil => cons carrier nil
        case cons[_](n, taill) => match rhs {
            case cons[_](m, tailr) => match bits_adder_carrier taill tailr carrier {
                case cons[_](c, tail) => match full_adder n m c {
                    case product(a, b) => cons(a, cons b tail)
                }
            }
        }
    }

def bits_adder[len: Nat](lhs: Vec[Bool] len, rhs: Vec[Bool] len): Vec[Bool] (succ len) =
    bits_adder_carrier lhs rhs false

println bits_adder (cons true nil) (cons false nil)"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Vec[Bool]::cons(1, Bool::false, Vec[Bool]::cons(0, Bool::true, Vec[Bool]::nil)"));
}

#[test]
fn test8() {
    let input = r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

enum Eq[T](x: T, y: T) {
    refl(a: T) -> Eq a a
}

def rfl[A][a: A]: Eq a a =
    refl a

def listid(x: List[Bool]): List[Bool] = x

def create0: List[Bool] = nil

def create1: List[Bool] = cons true nil

def create2: List[Bool] = cons(true, cons false nil)

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => add(y, mul n y)
}

def four = add two two

println four

def cong[A, B, f: A -> B, x: A, y: A](e: Eq x y): Eq (f x) (f y) =
    match e {
        case refl(a) => refl (f a)
    }

def cong_succ[x: Nat, y: Nat](e: Eq x y): Eq (succ x) (succ y) =
    cong[Nat][Nat][succ][x][y] e

def add_zero_right(a: Nat): Eq (add a zero) a =
    match a {
        case zero => refl zero
        case succ(t) => cong_succ (add_zero_right t)
    }

def symm[A, x, y: A](e: Eq[A] x y): Eq[A] y x =
    match e {
        case refl(a) => refl[A] a
    }

def trans[A, x, y, z: A](e1: Eq[A] x y, e2: Eq[A] y z): Eq[A] x z =
    match e1 {
        case refl(a) => e2
    }

def add_succ_right (n: Nat, m: Nat): Eq[Nat] (add(n, succ m)) (succ (add n m)) =
    match n {
        case zero => refl[Nat] (succ m)
        case succ(k) => cong_succ (add_succ_right k m)
    }

def add_comm (n: Nat, m: Nat): Eq[Nat] (add n m) (add m n) =
    match n {
        case zero => symm (add_zero_right m)
        case succ(k) => trans (cong_succ (add_comm k m)) (symm (add_succ_right m k))
    }

def add_assoc (n: Nat, m: Nat, k: Nat): Eq[Nat] (add (add n m) k) (add(n, add m k)) =
    match n {
        case zero => rfl
        case succ(l) => cong_succ (add_assoc l m k)
    }

def add_zero_left(m: Nat): Eq[Nat] (add zero m) m =
    rfl

def mul_zero_right(n: Nat): Eq[Nat] (mul n zero) zero =
    match n {
        case zero => rfl
        case succ(k) => trans (refl (add(zero, mul k zero))) (mul_zero_right k)
    }

def add_succ_zero_left(k: Nat): Eq[Nat] (add (succ zero) k) (succ k) =
    cong_succ (add_zero_left k)

def mul_one_right(n: Nat): Eq[Nat] (mul (n, succ zero)) n =
    match n {
        case zero => rfl[Nat][zero]
        case succ(k) =>
            let ih = mul_one_right k;
            let lemma: Eq[Nat] (add (succ zero) k) (succ k) = cong_succ (add_zero_left k);
            trans (cong[Nat][Nat][add (succ zero)][mul (k, succ zero)][k] ih) lemma
    }

struct Exists[A: Type 0, P: A -> Type 0] {
    witness: A
    proof: P witness
}

def exists_two: Exists[Nat][x => Eq x two] = Exists.mk[Nat][x => Eq x two] two rfl

struct Point[T] {
    x: T
    y: T
}

def get_x[T](p: Point[T]): T = p.x

def point_add(p1: Point[Nat], p2: Point[Nat]): Point[Nat] =
    new Point((add p1.x p2.x), (add p1.y p2.y))

def start_point = new Point(zero, four)

def end_point = new Point(four, two)

println (get_x start_point)

println (point_add start_point end_point)

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(x: A)
    case2(x: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

enum HighLvl2[A: Type 2] {
    case2_1(x: A)
    case2_2(x: Nat)
}

def test1_2: HighLvl2[HighLvl[Nat]] = case2_1 test2

def test1_3: Type 2 = HighLvl2[HighLvl[Nat]]

enum HighLvl3[A: Type 2] {
    case3_1
    case3_2(x: Nat)
}

def test2_2: HighLvl3[HighLvl[Nat]] = case3_1

def test2_3: Type 2 = HighLvl3[HighLvl[Nat]]

struct Bits {
    name: String
    size: Nat
}

def assign(a: Bits, b: Bits)(eq: Eq[Nat] a.size b.size): String = string_concat a.name b.name

def sigA = new Bits("A", four)

def sigB = new Bits("B", four)

def sigC = new Bits("C", two)

def sigD = new Bits("D", two)

def ab = assign sigA sigB rfl

def cd = assign sigC sigD rfl

def three = add(two, succ zero)

println 5
"#;
    let result = run(input, 0).unwrap();
    println!("{}", result);
    assert!(result.contains("Bool::false"));
    assert!(result.contains("4"));
    assert!(result.contains("0"));
    assert!(result.contains("Point[Nat]::Point.mk(4, 6)"));
    assert!(result.contains("5"));
}

// --------------------------------------------------------------------------------
// 2026-09-18 评审修复轮回归钉（L07_sum_type 修复轮同款场景向本层移植，
// docs/review-l07l12/REVIEW-4ANGLE-2026-09-18.md §六）：嵌套模式覆盖检查 /
// 构造子良构性 / 覆盖探测的两段式结算。

/// P0（嵌套覆盖缺失）：nil 臂 + cons(h, nil) 臂缺 cons(h, cons(..))——
/// 修复前静默接受、运行期在尾部为 cons 的值上卡死；修复后报模式位置缺失。
#[test]
fn test_nested_coverage_gap() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
    }
"#;
    match run(src, 0) {
        Err(e) => assert!(e.0.data.contains("缺少构造子 cons"), "{}", e.0.data),
        Ok(out) => panic!("非穷尽 match 被静默接受：\n{out}"),
    }
}

/// P0（嵌套覆盖缺失，三层）：深度 2 的嵌套位置缺 cons。
#[test]
fn test_nested_coverage_gap3() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, nil)) => h2
    }
"#;
    match run(src, 0) {
        Err(e) => assert!(e.0.data.contains("缺少构造子 cons"), "{}", e.0.data),
        Ok(out) => panic!("非穷尽 match 被静默接受：\n{out}"),
    }
}

/// 嵌套覆盖的正向对照：同一位置被 cons(h, cons(h2, t)) 完整覆盖 → Ok 且
/// 求值正确（防误报）。运行期验证避开本层既有的
/// 「双重嵌套构造子应用作实参」推导缺口（与本修复无关，见 parity 套件
/// 头注的已知偏差登记）。
#[test]
fn test_nested_coverage_complete_ok() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, t)) => h2
    }

println (f nil)
println (f (cons (succ zero) nil))
"#;
    let out = run(src, 0).unwrap();
    assert!(out.contains("0"), "{out}");
}

/// 索引族的嵌套位置（本层口径，与 L07 精度的刻意差异）：Vec 长度恰 2 上
/// cons(h, nil) 臂是荒谬臂（尾部 nil 要求长度 1 与头部索引冲突）——raw
/// 推断期 `?l := zero` 与特化方程冲突，check_pm_final 失败，臂按 L11 口径
/// **静默跳过**；其嵌套记账随之丢弃（失败臂不产生覆盖义务）。存活的
/// cons(h, cons(h2, t)) 臂的嵌套位置上，尾部索引槽未被 σ 精化（本层的
/// 特化解只落 scrutinee 与内层槽，不落外层隐式索引槽），nil 与 cons 都
/// 按"可达"处理——nil 无臂覆盖 → 报"模式位置缺少构造子 nil"。保守方向
/// （拒绝运行期完备的程序），与 L07 的"分支不可达"拒绝同判。
#[test]
fn test_nested_coverage_gadt_tail_position() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def f(v: Vec[Nat] (succ (succ zero))): Nat =
    match v {
        case cons(h, nil) => h
        case cons(h, cons(h2, t)) => h2
    }
"#;
    match run(src, 0) {
        Err(e) => {
            assert!(
                e.0.data.contains("缺少构造子 nil"),
                "{}",
                e.0.data
            );
        }
        Ok(out) => panic!("索引族嵌套位置漏报：\n{out}"),
    }
}

/// P1（构造子良构性）：ret 不是本 enum——c -> Nat 向构造子名字空间注入
/// phantom 值（对 Nat 的覆盖完备 match 在该值上卡死），修复后注册期拒绝。
#[test]
fn test_ctor_wf_external_ret() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c -> Nat
}
"#;
    match run(src, 0) {
        Err(e) => assert!(e.0.data.contains("不是 Foo"), "{}", e.0.data),
        Ok(out) => panic!("phantom 构造子被静默接受：\n{out}"),
    }
}

/// P1（构造子良构性）：参数位特化——隐式参数位是 Bool 而非参数变量，
/// 修复后拒绝（特化请走显式索引）。
#[test]
fn test_ctor_wf_param_specialized() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Foo[A] {
    c -> Foo[Bool]
}
"#;
    match run(src, 0) {
        Err(e) => assert!(e.0.data.contains("参数变量"), "{}", e.0.data),
        Ok(out) => panic!("参数特化被静默接受：\n{out}"),
    }
}

/// 构造子良构性的正向对照：构造子重绑定参数惯用法（p[A,B](a,b) ->
/// Pack[A][B] a b，使用点经特化方程解回枚举参数）必须保持 Ok——
/// WF 检查只封 phantom/特化两个洞，不误伤该惯用法。
#[test]
fn test_ctor_rebind_params_ok() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Pack[A, B](x: A, y: B) {
    p[A, B](a: A, b: B) -> Pack[A][B] a b
}

def sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true

println sw.y
"#;
    let out = run(src, 0).unwrap();
    assert!(out.contains("Bool::true"), "{out}");
}

/// P1（stale-solvable 臂序污染，评审 2026-09-18）：L12 无 solvable 白名单
/// 且臂 σ 逐臂重建（见 pattern_match.rs 头注），臂序不应影响可达性判定。
/// 注意 L12 的收窄语义是"特化失败 = 臂静默跳过"（同 L10，非 L07 的报
/// "分支不可达"），故本钉断言**两种臂序判定一致**（同为 Ok）；若失败说明
/// 臂间出现了状态泄漏。
#[test]
fn test_stale_solvable_order_independent() {
    let src = |arms: &str| {
        format!(
            r#"
enum Nat {{
    zero
    succ(x: Nat)
}}

enum W(f: Nat -> Nat) {{
    big(a: Nat, b: Nat, c: Nat, d: Nat) -> W (n => succ zero)
    mk -> W (n => succ zero)
    ident -> W (n => n)
}}

def t(w: W (n => succ zero)): Nat =
    match w {{
        {arms}
    }}
"#
        )
    };
    let r_big_first = run(&src("case big(a, b, c, d) => a\n        case ident => zero\n        case mk => succ zero"), 0);
    let r_ident_first = run(&src("case ident => zero\n        case big(a, b, c, d) => a\n        case mk => succ zero"), 0);
    match (&r_big_first, &r_ident_first) {
        (Ok(a), Ok(b)) => assert_eq!(a, b, "臂序影响输出"),
        (Err(a), Err(b)) => assert_eq!(a.0.data, b.0.data, "臂序影响错误判定"),
        _ => panic!("臂序影响判定：big-first={r_big_first:?} ident-first={r_ident_first:?}"),
    }
}

