//! L09_mltt —— MLTT 切片（`Type N` 分层宇宙 + 和类型 / match）。
//!
//! **已知限制（ROUND2 §B3，非缺陷，参考版与快版同崩 + parity 一致）**：
//! 值层不支持"卡住 match 再被应用"——`Val::Match` 经 `v_app` 会
//! `panic!("impossible apply")`。合法源码（如打印引用自递归卡住 match 的
//! 函数值）可触发；L07 起以值层 splice 实现了该特性，L09 是时代缺口。
//! 修复需实现实参吸收并要求参考版+快版同步大改，超出最小改动范围。
//! （unify 的两个 η 臂已加 `v_applicable`/`vapp_ok` 守卫——卡住 match/
//! 字面量一侧与 λ 比较时不再 panic，改判 Err；其余 v_app 路径仍同崩，
//! 限制本身不变。）
use cxt::Cxt;
// `Either` 本文件几乎不用，但子模块 `pattern_match` 以 `super::Either` 引用
// （`pattern_match.rs:192/200`）——勿按"本文件未用"删除。
use parser::syntax::{Either, Icit};
use pattern_match::Compiler;
use syntax::{Pruning, close_ty};
use pretty::pretty_tm;

use crate::list::List;
use crate::parser_lib::Span;

mod cxt;
mod elaboration;
mod parser;
mod pattern_match;
mod syntax;
mod unification;
mod pretty;
pub(crate) mod bump_spine_iter;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
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
        /*name: Span<String>,
        params: Vec<(Span<String>, Tm, Icit)>,
        ret_type: Tm,
        body: Tm,*/
    },
    Println(Tm),
    Enum {
        //TODO:
    },
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    Obj(Box<Tm>, Span<String>),
    Lam(Span<String>, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U(u32),
    Pi(Span<String>, Icit, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>),
    SumCase {
        typ: Box<Tm>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Tm, Icit)>,
    },
    Match(Box<Tm>, Vec<(PatternDetail, Tm)>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
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
}

/// 嵌套覆盖检查（L07 2026-09-18 评审修复 5 的 L09 移植）在某路径上的
/// 覆盖判定：已走查臂的 PatternDetail 沿路径下钻的结构贡献。
pub(crate) enum PosCover {
    /// var/Any：该位置全覆盖。
    All,
    /// 该位置只可能是这个构造子（当前层是 Con 模式）。
    Ctor(String),
    /// 祖先异 ctor：该位置在本臂实例化下不可达，不贡献覆盖。
    None,
}

/// 沿路径（根到被拆字段的 (构造子名, 字段下标) 链）下钻模式的覆盖贡献。
pub(crate) fn cover_at(detail: &PatternDetail, path: &[(String, usize)]) -> PosCover {
    let mut cur = detail;
    for (ctor, field) in path {
        match cur {
            PatternDetail::Any(_) | PatternDetail::Bind(_) => return PosCover::All,
            PatternDetail::Con(n, subs) if n.data == *ctor => cur = &subs[*field],
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

type Env = List<Val>;
type Spine = List<(Val, Icit)>;

#[derive(Clone)]
pub struct Closure(Env, Box<Tm>);

impl std::fmt::Debug for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure(.., {:?})", self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Obj(Box<Val>, Span<String>, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Box<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(Span<String>),
    Prim,
    Sum(
        Span<String>,
        Vec<(Span<String>, Rc<Val>, Rc<VTy>, Icit)>,
        Vec<Span<String>>
    ),
    SumCase {
        typ: Rc<Val>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Rc<Val>, Icit)>,
    },
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>),
    /// 显式替换下的值（模式精化，dpm-nbe `VSub`）：特化解不改写既有值，
    /// 只把解包在外面；`force` 在读点把 σ 推进值的结构（[`Infer::frcs`]，
    /// 对齐 dpm-nbe 的 `frcS`）。不变式：`force` 的返回值顶层不会是
    /// VSub（fuel 耗尽的降级点在 frcs 的 lookup 命中处，返回裸 rigid）。
    VSub(Box<Val>, Rc<Subst>),
}

/// 模式特化的解：层级 → 值 的**持久化单链**（dpm-nbe 的 explicit
/// substitution；链头 = 最新的解）。仅由模式编译器 / 特化合一的
/// `SpecSolve::acc` 经 `Subst::extend` 构建；`Rc` 共享让臂边界回滚 =
/// 指针赋值、`Val::VSub` 包裹 = O(1)。
///
/// 表示选型（对齐 L07 蓝本定稿）：**写入 O(1) cons、读取沿链扫描**；
/// `lookup` 沿链首个命中 + 条件包裹（解值浅结构不引用任何已解层级时
/// 原样返回，零分配）。与旧 `update_cxt` 上下文改写的对应：`extend` 累积
/// 解、`lookup_hit` 是 force 读点的展开——区别在于解只对**被包裹过的值**
/// 可见（读点显式），不再是"改写 env 槽 + refresh 全量重引用"。
#[derive(Debug, Clone, Default)]
pub struct Subst {
    head: Option<Rc<SubEntry>>,
}

#[derive(Debug)]
struct SubEntry {
    lvl: Lvl,
    /// 解的原始值。不预先包裹"更新的解"——读取时 `lookup_hit` 把整条 σ
    /// 包在外面（条件包裹，见其文档），由 force 在读点一次性推开。
    val: Val,
    next: Option<Rc<SubEntry>>,
}

impl Subst {
    pub(crate) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配零 fuel）；引用时把整条 σ 包在解值外（解值不含
    /// x 自身——occurs 守卫；比该条目更新的解恰借此对解值生效），由 force
    /// 在读点推开。未命中 None。
    pub(crate) fn lookup_hit(self: &Rc<Self>, x: Lvl) -> Option<Val> {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return Some(if !Self::mentions_level(&e.val, self) {
                    e.val.clone()
                } else {
                    Val::VSub(Box::new(e.val.clone()), self.clone())
                });
            }
            cur = e.next.clone();
        }
        None
    }

    /// 解值的浅结构是否引用 σ 的某个已解层级。含闭包 **env 槽**（它们是
    /// 值，读点会流出）与 Match 的 scrutinee/captured env；不含闭包体 /
    /// Match 分支体（Tm，求值时才经 env 读到槽值）。VSub 保守记为引用（已
    /// 包过 σ 的值再包一层无害）。误报只多一次包裹，漏报才会丢精化——
    /// 扫描口径宁宽勿窄。
    fn mentions_level(v: &Val, sub: &Subst) -> bool {
        fn env_slots(env: &Env, sub: &Subst) -> bool {
            env.iter().any(|v| mentions_level(v, sub))
        }
        fn mentions_level(v: &Val, sub: &Subst) -> bool {
            match v {
                Val::Rigid(y, sp) => sub.has(*y) || sp.iter().any(|(u, _)| mentions_level(u, sub)),
                Val::Flex(_, sp) => sp.iter().any(|(u, _)| mentions_level(u, sub)),
                Val::Obj(o, _, sp) => {
                    mentions_level(o, sub) || sp.iter().any(|(u, _)| mentions_level(u, sub))
                }
                Val::Lam(_, _, cl) => env_slots(&cl.0, sub),
                Val::Pi(_, _, a, cl) => mentions_level(a, sub) || env_slots(&cl.0, sub),
                Val::Sum(_, params, _) => params.iter().any(|(_, v, t, _)| {
                    mentions_level(v, sub) || mentions_level(t, sub)
                }),
                Val::SumCase { typ, datas, .. } => {
                    mentions_level(typ, sub) || datas.iter().any(|(_, v, _)| mentions_level(v, sub))
                }
                Val::Match(s, env, _) => mentions_level(s, sub) || env_slots(env, sub),
                // 已被包裹的值保守视为引用（内层结构不再探查）
                Val::VSub(..) => true,
                Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) | Val::Prim => false,
            }
        }
        mentions_level(v, sub)
    }

    /// x 是否已有解（旧 `update_cxt` 的"是否已精化"判定的显式化）。
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

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新）。
    pub(crate) fn extend(sub: &Rc<Subst>, x: Lvl, v: Val) -> Rc<Subst> {
        Rc::new(Subst {
            head: Some(Rc::new(SubEntry {
                lvl: x,
                val: v,
                next: sub.head.clone(),
            })),
        })
    }

    /// 组合：内层 `inner` 先应用、外层 `outer` 后应用。外层条目接到链头
    /// （先被查到 = 覆盖同键，"取最新"语义）。
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

/// η 展开与 frcs 读点共用的可应用性守卫：只有 `v_app` 不会 panic 的形态
/// （Flex / Rigid / 卡住投影 Obj / VSub）能吃 η 新变量。字面量 / U / Π /
/// Sum / SumCase / 卡住 match 与实参相遇时无从应用。
pub(crate) fn v_applicable(v: &Val) -> bool {
    matches!(
        v,
        Val::Flex(..) | Val::Rigid(..) | Val::Obj(..) | Val::VSub(..)
    )
}

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc，
/// force 在消费点惰性推开）。σ 为空时零开销直通。
pub(crate) fn wrap_sub(sub: &Rc<Subst>, v: Val) -> Val {
    if sub.is_empty() {
        v
    } else {
        Val::VSub(Box::new(v), sub.clone())
    }
}

/// 展开燃料：每个"精化传播"步骤消耗 1，耗尽即停止（防环）。仅 frcs 的
/// lookup 命中点燃烧（对齐 L07 蓝本：force 入口与包裹/组合的机械开销免费）。
fn burn(cell: &Cell<u32>) -> bool {
    let f = cell.get();
    if f == 0 {
        return false;
    }
    cell.set(f - 1);
    true
}

/// 值树里是否出现某层级（浅层结构扫描；闭包跳过——那里的环由 force 的
/// fuel 兜底）。`VSub` 只扫解值自身结构、**不扫 σ 的映射值**：σ 的其它
/// 条目合法引用别的模式变量，扫进来会把无害的解误判成环。
pub(crate) fn val_mentions_lvl(v: &Val, x: Lvl) -> bool {
    fn spine(sp: &Spine, x: Lvl) -> bool {
        sp.iter().any(|(v, _)| val_mentions_lvl(v, x))
    }
    match v {
        Val::Rigid(y, sp) => *y == x || spine(sp, x),
        // **Flex 头的实参视为不透明**：可达性探测用 `Raw::Hole` 实例化构造子
        // 绑定器，fresh meta 的 pruning 会把整组绑定器（含被解变量本身）
        // 收进 spine——`l := succ (?m … l …)` 是"meta 应用到变量"的合法形，
        // 不是结构性自引用（旧 `update_cxt` 无 occurs，把 spine 算进来会把
        // 可达构造子误判不可达）。结构性自引用（`x := succ x`）仍由
        // Rigid/SumCase 等臂捕获；更深的间接环由 force 的 fuel 兜底。
        Val::Flex(_, _) => false,
        Val::Obj(o, _, sp) => val_mentions_lvl(o, x) || spine(sp, x),
        Val::VSub(v, _) => val_mentions_lvl(v, x),
        Val::Sum(_, params, _) => params
            .iter()
            .any(|(_, v, t, _)| val_mentions_lvl(v, x) || val_mentions_lvl(t, x)),
        Val::SumCase { typ, datas, .. } => {
            val_mentions_lvl(typ, x) || datas.iter().any(|(_, v, _)| val_mentions_lvl(v, x))
        }
        Val::Match(s, env, _) => {
            val_mentions_lvl(s, x) || env.iter().any(|v| val_mentions_lvl(v, x))
        }
        Val::Lam(..) | Val::Pi(..) | Val::U(_) | Val::LiteralType | Val::LiteralIntro(_)
        | Val::Prim => false,
    }
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
    // 全局层级哨兵：global_idx 从 0 起（`global_idx + 1919810`），故 0 号
    // 全局恰好等于 1919810——边界必须是 `>=`（eval 的 `x - 1919810` 与快版
    // `*i >= GLOBAL_BASE` 同口径）。用 `>` 会让首个声明的自引用走
    // `l - x - 1` 下溢（debug panic / release 大索引越界）。
    if x.0 >= 1919810 {
        Ix(x.0)
    } else {
        Ix(l.0 - x.0 - 1)
    }
}

use std::{
    cell::Cell,
    collections::HashMap,
    ops::{Add, Sub},
    rc::Rc,
};

#[derive(Debug)]
struct UnifyError;

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

/// Rc 槽位（Sum 参数 / SumCase typ+datas）的所有权取用：独占时零拷贝，
/// 共享时深拷贝——与迁 Rc 前"按值持有、克隆即深拷贝"的语义一致。
/// match 提取字段 / env 存槽走 Rc 引用计数（O(1)），消费型路径（quote /
/// rename / 投影）经此取值。
pub(crate) fn rc_take(v: Rc<Val>) -> Val {
    Rc::try_unwrap(v).unwrap_or_else(|v| (*v).clone())
}

#[derive(Debug)]
pub struct Error(pub Span<String>);

#[derive(Clone)]
pub struct Infer {
    meta: Vec<MetaEntry>,
    global: HashMap<Lvl, VTy>,
    /// 精化传播的展开燃料池（Cell 随 `&self` 的 force/frcs 递减）。仅
    /// frcs 的 lookup 命中点燃烧；外部入口（unify_catch / nf / 模式编译 /
    /// check_pm）充值。耗尽即停止精化展开（有界降级，防闭环无限推进）。
    unify_fuel: Cell<u32>,
}

/// 燃料池容量（对齐 L07 蓝本）。
const UNIFY_FUEL: u32 = 4096;

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            global: HashMap::new(),
            unify_fuel: Cell::new(UNIFY_FUEL),
        }
    }
    /// 给精化展开的燃料池充值（外部合一 / 求值入口调用）。
    pub(crate) fn meta_refuel(&self) {
        self.unify_fuel.set(UNIFY_FUEL);
    }
    /// 燃料池是否已耗尽（探测失败侧的观察口：fuel 耗尽的失败是预算问题
    /// 而非结构冲突——probe_accessible 尾部据此把失败按"可达"处理，保守
    /// 地要求覆盖。L07 2026-09-18 评审修复 2 的同步移植）。
    pub(crate) fn fuel_exhausted(&self) -> bool {
        self.unify_fuel.get() == 0
    }
    fn new_meta(&mut self, a: VTy) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.eval(
            &List::new(),
            close_ty(cxt.locals.clone(), self.quote(cxt.lvl, a)),
        );
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(MetaVar(m))), cxt.pruning.clone())
    }
    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, t: Val) -> Val {
        //println!("{} {:?}", "force".red(), t);
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved, _) => self.force(self.v_app_sp(t_solved.clone(), sp)),
                MetaEntry::Unsolved(_) => Val::Flex(m, sp),
            },
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1）。fuel 耗尽的降级点也在该处
            // （返回裸 rigid）。
            Val::VSub(v, sub) => self.frcs(&sub, *v),
            _ => t,
        }
    }

    /// 把替换 `σ` 推进值 `v` 的结构（dpm-nbe `frcS`；L07 蓝本 frcs 的
    /// L09 Val/Tm 形态适配）。槽位纪律：σ 对 spine / Sum/SumCase 槽只
    /// **包裹**，绝不推进物化——槽位引用是作用域事实，物化会破坏后续
    /// solve 的 invert。
    fn frcs(&self, sub: &Rc<Subst>, v: Val) -> Val {
        if sub.is_empty() {
            return self.force(v);
        }
        match v {
            // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
            Val::VSub(v2, sub2) => {
                let composed = Subst::compose(sub, &sub2);
                self.frcs(&composed, *v2)
            }
            // 被解变量的读点：lookup 命中（真正的精化传播）烧 1 fuel；fuel
            // 耗尽按未解处理（返回裸 rigid，有界降级）。未命中零成本直通。
            // 解出值按应用序（spine 尾到头）经 v_app 拼接（λ ⇒ β；中性头
            // ⇒ spine）——对应 dpm-nbe `napp (lookupSub sb v) (frcS sb sp)`。
            // 解值带实参但头不可应用时卡回裸 rigid（v_applicable 守卫）。
            Val::Rigid(x, sp) => {
                let mut head = match sub.lookup_hit(x) {
                    Some(hit) => {
                        if !burn(&self.unify_fuel) {
                            return Val::Rigid(x, sp);
                        }
                        self.force(hit)
                    }
                    None => Val::vvar(x),
                };
                if !sp.is_empty() && !v_applicable(&head) {
                    return Val::Rigid(x, sp);
                }
                let args: Vec<(Val, Icit)> = sp.iter().cloned().collect();
                for (u, i) in args.into_iter().rev() {
                    head = self.v_app(head, wrap_sub(sub, u), i);
                }
                head
            }
            // 中性头的 spine 槽只包裹不推进（槽位引用是作用域事实），包裹后
            // 交回 force 重走既有解链臂。
            Val::Flex(m, sp) => self.force(Val::Flex(m, self.wrap_sp(sub, sp))),
            Val::Obj(o, name, sp) => self.force(Val::Obj(
                Box::new(self.frcs(sub, *o)),
                name,
                self.wrap_sp(sub, sp),
            )),
            // 闭包 env 逐槽包裹（惰性，不进入闭包体重求值）；返回同型值。
            Val::Lam(x, i, cl) => Val::Lam(x, i, Closure(self.frcs_env(sub, &cl.0), cl.1)),
            Val::Pi(x, i, a, cl) => Val::Pi(
                x,
                i,
                Box::new(self.frcs(sub, *a)),
                Closure(self.frcs_env(sub, &cl.0), cl.1),
            ),
            // Sum/SumCase 的槽位同样只包裹
            Val::Sum(name, params, cases) => Val::Sum(
                name,
                params
                    .into_iter()
                    .map(|(n, v, t, i)| {
                        (
                            n,
                            Rc::new(wrap_sub(sub, rc_take(v))),
                            Rc::new(wrap_sub(sub, rc_take(t))),
                            i,
                        )
                    })
                    .collect(),
                cases,
            ),
            Val::SumCase {
                typ,
                case_name,
                datas,
            } => Val::SumCase {
                typ: Rc::new(wrap_sub(sub, rc_take(typ))),
                case_name,
                datas: datas
                    .into_iter()
                    .map(|(n, v, i)| (n, Rc::new(wrap_sub(sub, rc_take(v))), i))
                    .collect(),
            },
            // scrutinee **推进**（重选分支需要解出的构造子值——L09 的
            // eval/force 无 Match 重选臂，分支重选发生在 eval 的 Tm::Match
            // 臂：scrutinee 经 force 推开 σ 后若是构造子值即选分支）；捕获
            // env 只包裹。
            Val::Match(s, env, cases) => Val::Match(
                Box::new(self.frcs(sub, *s)),
                self.frcs_env(sub, &env),
                cases,
            ),
            // U / LiteralType / LiteralIntro / Prim：原样
            t => t,
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
        env.map(|v| Val::VSub(Box::new(v.clone()), sub.clone()))
    }

    /// 合一器**参数视角**的 WHNF：与 force 相同，但不推开 VSub 精化包裹、
    /// 不做 Match 重选。`invert` / `prune_vflex` 关心的是"元变量被应用在
    /// 哪些槽位上"——槽位引用（Rigid）本身是作用域事实，分支内的精化等式
    /// 不改变槽位的存在；在它们身上展开反而会把可逆 spine 变成含构造子值
    /// 的不可逆 spine。逐层解包 VSub（嵌套 match 的上下文被外层臂与内层臂
    /// 各 subst_cxt 一次，单层解包会漏）。
    pub(crate) fn force_arg(&self, t: Val) -> Val {
        let mut cur = &t;
        while let Val::VSub(v, _) = cur {
            cur = v;
        }
        match cur {
            Val::Rigid(x, sp) if sp.is_empty() => Val::Rigid(*x, sp.clone()),
            Val::Rigid(..) | Val::Match(..) => t,
            _ => self.force(t),
        }
    }
    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(m),
        }
    }

    fn closure_apply(&self, closure: &Closure, u: Val) -> Val {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(&closure.0.prepend(u), *closure.1.clone())
    }

    fn v_app(&self, t: Val, u: Val, i: Icit) -> Val {
        //println!("v_app {t:?} {u:?}");
        match t {
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点会把
            // VSub 头送进来——如臂上下文里 Var 引用了被解槽；force 顶层不再
            // 产出 VSub，递归必终止）
            Val::VSub(..) => {
                let t = self.force(t);
                self.v_app(t, u, i)
            }
            Val::Lam(_, _, closure) => self.closure_apply(&closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
            Val::Obj(x, name, sp) => Val::Obj(x, name, sp.prepend((u, i))),
            x => panic!("impossible apply\n  {:?}\nto\n  {:?}", x, u),
        }
    }

    fn v_app_sp(&self, t: Val, spine: Spine) -> Val {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(self.v_app_sp(t, a.tail()), u.clone(), *i)
            }
        }
    }

    fn v_app_pruning(&self, env: &Env, v: Val, pr: &Pruning) -> Val {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                self.v_app_pruning(&a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(&a.tail(), v, &b.tail())
            }
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, env: &Env, tm: Tm) -> Val {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => self.global.get(&Lvl(x.0 - 1919810)).unwrap().clone(),
            },
            Tm::Obj(tm, name) => {
                let recv = self.eval(env, *tm);
                // 精化包裹的接收者（subst_cxt 包裹的 env 槽会以 VSub 流出）
                // 先推开 σ 再判形态；force 对非 VSub/Flex 是恒等，旧行为不变。
                let recv = match recv {
                    v @ Val::VSub(..) => self.force(v),
                    v => v,
                };
                match recv {
                    Val::Sum(_, params, _) => {
                        params.into_iter()
                            .find(|(f_name, _, _, _)| f_name == &name)
                            .map(|x| rc_take(x.1))
                            .unwrap()
                    },
                    Val::SumCase { datas, typ, .. } => {
                        // typ 槽可能被 frcs 包成 VSub（只包裹不物化）——判
                        // Sum 前先 force
                        (match self.force(rc_take(typ)) {
                            Val::Sum(_, params, _) => params,
                            t => panic!("impossible {t:?}"),
                        }).into_iter()
                            .map(|x| (x.0, x.1, x.3))
                            .chain(datas)
                        //datas.into_iter()
                            .find(|(f_name, _, _)| f_name == &name)
                            .map(|x| rc_take(x.1))
                            .unwrap()
                    },
                    x @ Val::Rigid(_, _) => {
                        Val::Obj(Box::new(x), name, List::new())
                    }
                    x => panic!("impossible {x:?}"),
                }
            }
            Tm::App(t, u, i) => self.v_app(self.eval(env, *t), self.eval(env, *u), i),
            Tm::Lam(x, i, t) => Val::Lam(x, i, Closure(env.clone(), t)),
            Tm::Pi(x, i, a, b) => {
                Val::Pi(x, i, Box::new(self.eval(env, *a)), Closure(env.clone(), b))
            }
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, *t);
                self.eval(&env.prepend(t_val), *u)
            }
            Tm::U(x) => Val::U(x),
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, *t), &pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x),
            Tm::LiteralType => Val::LiteralType,
            Tm::Prim => {
                // 实参槽可能被 subst_cxt 包成 VSub——先 force 推开再判字面量
                let a0 = self.force(env.iter().nth(1).unwrap().clone());
                let b0 = self.force(env.iter().nth(0).unwrap().clone());
                match (a0, b0) {
                    (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
                        Val::LiteralIntro(a.map(|x| format!("{x}{}", b.data)))
                    }
                    _ => Val::Prim,
                }
            }
            Tm::Sum(name, params, cases) => {
                let new_params = params
                    .into_iter()
                    .map(|x| {
                        (
                            x.0,
                            Rc::new(self.eval(env, x.1)),
                            Rc::new(self.eval(env, x.2)),
                            x.3,
                        )
                    })
                    .collect();
                Val::Sum(name, new_params, cases)
            }
            Tm::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .into_iter()
                    .map(|p| (p.0, Rc::new(self.eval(env, p.1)), p.2))
                    .collect();
                let typ = self.eval(env, *typ);
                Val::SumCase {
                    typ: Rc::new(typ),
                    case_name,
                    datas,
                }
            }
            Tm::Match(tm, cases) => {
                let val = self.eval(env, *tm);
                let val = self.force(val);
                match val {
                    val @ Val::SumCase { .. } => {
                        let (tm, env) = Compiler::eval_aux(self, &val, env, &cases).unwrap();
                        self.eval(&env, tm)
                    }
                    neutral => {
                        Val::Match(Box::new(neutral), env.clone(), cases)
                    }
                }
            }
        }
    }

    fn quote_sp(&self, l: Lvl, t: Tm, spine: Spine) -> Tm {
        /*spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })*/
        match spine {
            List { head: None, .. } => t,
            _ => {
                let head = spine.head().unwrap();
                Tm::App(Box::new(self.quote_sp(l, t, spine.tail())), Box::new(self.quote(l, head.0.clone())), head.1)
            }
        }
    }

    fn quote(&self, l: Lvl, t: Val) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t {
            // 正常路径 force 后顶层不会是 VSub；fuel 耗尽时 force 原样返回
            // VSub——解包打印内层（σ 未推开，保真度同旧版"打印未展开 rigid"）。
            Val::VSub(v, _) => self.quote(l, *v),
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Obj(x, name, sp) => self.quote_sp(l, Tm::Obj(Box::new(self.quote(l, *x)), name), sp),
            Val::Lam(x, i, closure) => Tm::Lam(
                x,
                i,
                Box::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x,
                i,
                Box::new(self.quote(l, *a)),
                Box::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::U(x) => Tm::U(x),
            Val::LiteralIntro(x) => Tm::LiteralIntro(x),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim => Tm::Prim,
            Val::Sum(name, params, cases) => {
                let new_params = params.into_iter()
                    .map(|x| {
                        (x.0, self.quote(l, rc_take(x.1)), self.quote(l, rc_take(x.2)), x.3)
                    })
                    .collect();
                Tm::Sum(name, new_params, cases)
            }
            Val::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .into_iter()
                    .map(|p| {
                        (p.0, self.quote(l, rc_take(p.1)), p.2)
                    })
                    .collect();
                Tm::SumCase {
                    typ: Box::new(self.quote(l, rc_take(typ))),
                    case_name,
                    datas,
                }
            }
            Val::Match(val, env, cases) => {
                /*TODO:let tm_cases = cases
                    .into_iter()
                    .map(|(p, clos)| {
                        let binders_count = p.count_binders();
                        let body_tm = self.quote(l + binders_count, self.closure_apply_pats(&clos, l, &p));
                        (p, body_tm)
                    })
                    .collect();*/
                let tm_cases = cases
                    .into_iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, x| env.prepend(Val::vvar(l + x)));
                            let mut avoid_recursive = self.clone();
                            avoid_recursive.global
                                .iter_mut()
                                .for_each(|x| *x.1 = Val::Rigid(*x.0 + 1919810, List::new()));
                            let tm = avoid_recursive.eval(&env, x.1);
                            self.quote(l+x.0.bind_count(), tm)
                        }
                    ))
                    .collect();
                Tm::Match(Box::new(self.quote(l, *val)), tm_cases)
            }
        }
    }

    pub fn nf(&self, env: &Env, t: Tm) -> Tm {
        // quote → eval 会 force；一次 nf 充值燃料防精化闭环
        self.meta_refuel();
        let l = Lvl(env.iter().count() as u32);
        self.quote(l, self.eval(env, t))
    }

    fn close_val(&self, cxt: &Cxt, t: Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: Val, t_prime: Val, span: Span<()>) -> Result<(), Error> {
        // 常规转换（spec = None）：不得解假设；一次合一入口充值精化燃料池
        self.meta_refuel();
        self.unify(cxt.lvl, cxt, t.clone(), t_prime.clone(), None)
            .map_err(|_| {
                /*Error::CantUnify(
                    cxt.clone(),
                    self.quote(cxt.lvl, t),
                    self.quote(cxt.lvl, t_prime),
                )*/
                //println!("{:?} == {:?}", t, t_prime);
                //println!("{:?}", self.eval(&cxt.env, self.quote(cxt.lvl, t_prime.clone())));
                let err = format!(
                    //"can't unify {:?} == {:?}",
                    "can't unify\n      find: {}\n  expected: {}",
                    pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, t_prime)),
                );
                Error(span.map(|_| err.clone()))
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            })
    }
}

#[allow(unused)]
pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let (ast, parse_errs) = parser::parser(&preprocess(input), path_id).unwrap();
    for e in parse_errs {
        println!("{:?}", e);
    }
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        match &tm {
            parser::syntax::Decl::Def { name, .. }
            | parser::syntax::Decl::Enum { name, .. } => {
                println!("> {}", name.data);
                //cxt.print_env(&infer);
            },
            parser::syntax::Decl::Println(raw) => {},
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &pretty::pretty_tm(0, cxt.names(), &infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    Ok(ret)
}

pub fn preprocess(s: &str) -> String {
    let s = s.split("/*")
        .map(|x| {
            x.split_once("*/")
                .map(|(a, b)| a.replace(|c: char| !c.is_whitespace(), " ") + "  " + b)
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "  " + &b)
        .unwrap_or(s.to_owned());
    s.lines()
        .map(|x| {
            x.split_once("//")
                .map(|(a, b)| a.to_owned() + "  " + &b.replace(|c: char| !c.is_whitespace(), " "))
                .unwrap_or(x.to_owned())
        })
        .reduce(|a, b| a + "\n" + &b)
        .unwrap_or(s.to_owned())
}

/// 参考版项的节点数（与性能版 `tm_size` 同口径）。
fn tm_size_ref(t: &Tm) -> u64 {
    let mut stack: Vec<&Tm> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Prim => {}
            Tm::Obj(h, _) => stack.push(h),
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                n += pr.len() as u64;
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
            Tm::Sum(_, params, _) => {
                for (_, v, ty, _) in params {
                    stack.push(v);
                    stack.push(ty);
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push(typ);
                for (_, v, _) in datas {
                    stack.push(v);
                }
            }
            Tm::Match(s, cases) => {
                stack.push(s);
                for (p, b) in cases {
                    n += p.bind_count() as u64;
                    stack.push(b);
                }
            }
        }
    }
    n
}

/// 参考版基准口径：elaborate 全部 decl，返回是否通过。
pub(crate) fn bench_check(decls: &[parser::syntax::Decl]) -> bool {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new();
    for d in decls {
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return false,
        }
    }
    true
}

/// 参考版基准口径：check + nf——取**最后一个 def** 的登记值（define 链的
/// env 槽顶）空层级引读并数节点（深 Box 树的递归析构会爆栈，`mem::forget`）。
pub(crate) fn bench_check_nf(decls: &[parser::syntax::Decl]) -> u64 {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new();
    let mut last: Option<Val> = None;
    for d in decls {
        let is_def = matches!(d, parser::syntax::Decl::Def { .. });
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return 0,
        }
        if is_def {
            last = cxt.env.head().cloned();
        }
    }
    let Some(v) = last else { return 0 };
    infer.meta_refuel();
    let q = infer.quote(Lvl(0), v);
    let n = tm_size_ref(&q);
    std::mem::forget(q);
    n
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

def create2: List[Bool] = cons true (cons false nil)

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
    case succ(n) => add y (mul n y)
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
    println!("{}", run(input, 0).unwrap());
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
    println!("{}", run(input, 0).unwrap());
    println!("success");
}

pub fn run1(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let (ast, parse_errs) = parser::parser(input, path_id).unwrap();
    for e in parse_errs {
        println!("{:?}", e);
    }
    let mut cxt = Cxt::new();
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    println!("{:?}", cxt);
    Ok(ret)
}

#[test]
fn test1() {
    let input = r#"
def str_id(x: String, y: String): String = "builtin"

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id(x: String, y: String): String = x

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id: String = string_concat "hello " "world"

println str_id

"#;
    println!("{}", run1(input, 0).unwrap());
    println!("success");
}
