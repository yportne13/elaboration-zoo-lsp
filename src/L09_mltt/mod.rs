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
use syntax::{Locals, Pruning, close_ty};
use pretty::pretty_tm;

use crate::list::List;
use crate::parser_lib::Span;
use smol_str::SmolStr;

mod cxt;
mod elaboration;
// pub(crate)（parser/pretty）：tests/backport3_pretty_l0910.rs 以 #[path]
// 把本模块编进测试 crate 后要直接调 pretty/parser 做方括号回归与回读断言
// （L07/L08 的 parser 同款可见性；层模块本身在 lib.rs 里是私有的，不扩大
// 对外 API）。
pub(crate) mod parser;
mod pattern_match;
mod struct_eq;
mod syntax;
mod unification;
pub(crate) mod pretty;
pub(crate) mod bump_spine_iter;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// 顶层声明引用（已定名全局，编码 `global_idx + 1919810`）：`eval` 直查
    /// [`Infer::global`] O(1)（2026-11-12 载体切换）。
    ///
    /// 与 `Var(大下标)` 的分工：`Var(大下标)` 只表示**递归定义检查期间**的
    /// 自身占位引用（旧版 `fake_bind` 哨兵；中性全局视图会把这类引用
    /// 中和成 rigid，避免递归展开）；`Global` 是已登记全局的普通引用，
    /// 与旧版「env 槽引用」同语义——中性视图下照常展开。
    Global(Ix),
    Obj(Box<Tm>, Span<String>),
    /// λ 体用 `Rc<Tm>`（继承 L07/L08 表示：借用版 eval 建 Closure 时只加引用
    /// 计数，不再深拷整棵体项——2026-11-13 从 L08 合入）。
    Lam(Span<String>, Icit, Rc<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U(u32),
    Pi(Span<String>, Icit, Rc<Ty>, Rc<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    /// 内建函数体标记（携带名字：求值时卡成 `Val::Prim(name, [])`，实参
    /// 经 App 进入 spine，归约统一在 force 的 `prim_reduce`）。
    Prim(SmolStr),
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
pub struct Closure(Env, Rc<Tm>);

impl std::fmt::Debug for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure(.., {:?})", self.1)
    }
}

/// Val 里的名字 span 用 `Rc<Span<String>>` 句柄（实验 B）：Val 克隆热路径
/// （Nat 大值递归/match 抽取每步若干次）不再为构造子/绑定器名做 String 堆分配，
/// 只加一次引用计数。Tm 侧仍用 `Span<String>`（项层克隆不在热路径）。
#[derive(Clone)]
pub(crate) struct VSpan(pub Rc<Span<String>>);

impl std::ops::Deref for VSpan {
    type Target = Span<String>;
    fn deref(&self) -> &Span<String> { &self.0 }
}

impl VSpan {
    pub(crate) fn new(s: Span<String>) -> Self { VSpan(Rc::new(s)) }
}

/// Debug 与内层 `Span<String>` 同形：错误正文/Debug 打印（含 parity 归一化口径）
/// 依赖 `"name" @ off` 形态，不能出现包装层名。
impl std::fmt::Debug for VSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

pub(crate) fn vspan(s: Span<String>) -> VSpan { VSpan::new(s) }

/// VSpan → Tm 侧 `Span<String>`（名字/显示/错误用；不在克隆热路径）。
pub(crate) fn tmspan(s: &VSpan) -> Span<String> { (*s.0).clone() }

/// 跨表示名比较（Val 的 VSpan ↔ Tm/ Raw 的 Span<String>）：只看名字，偏移无关。
impl PartialEq for VSpan {
    fn eq(&self, other: &VSpan) -> bool { self.0.data == other.0.data }
}
impl PartialEq<Span<String>> for VSpan {
    fn eq(&self, other: &Span<String>) -> bool { self.0.data == other.data }
}
impl PartialEq<VSpan> for Span<String> {
    fn eq(&self, other: &VSpan) -> bool { self.data == other.0.data }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Obj(Rc<Val>, VSpan, Spine),
    Lam(VSpan, Icit, Closure),
    Pi(VSpan, Icit, Rc<VTy>, Closure),
    U(u32),
    LiteralType,
    LiteralIntro(VSpan),
    /// 卡住的内建应用：名字 + 已收实参 spine（头 = 最后应用的实参）。
    /// 全部实参字面量时在 `force` 归约（本层仅 string_concat），否则保持
    /// 中性参与 unify / quote / rename（丢实参的单元 `Prim` 会把
    /// `x ++ y ≡ x ++ z` 判成相等）。
    Prim(SmolStr, Spine),
    Sum(
        VSpan,
        Rc<Vec<(VSpan, Rc<Val>, Rc<VTy>, Icit)>>,
        Rc<Vec<VSpan>>,
    ),
    SumCase {
        typ: Rc<Val>,
        case_name: VSpan,
        datas: Rc<Vec<(VSpan, Rc<Val>, Icit)>>,
    },
    /// 卡住的 match：scrutinee 不是构造子值，等待 scrutinee 归约后再选分支。
    /// 第 4 字段 `pending` = 卡住期间累积的应用实参（值层保存，分支选中后
    /// 在值层应用——项层 splice 会把实参的自由变量 quote 进错误上下文）；恢复
    /// L07 起就有的 splice 能力（L09 早期曾缺失，v_app 直接 panic）。
    Match(
        Rc<Val>,
        Env,
        Rc<Vec<(PatternDetail, Tm)>>,
        Rc<Vec<(Val, Icit)>>,
    ),
    /// 显式替换下的值（模式精化，dpm-nbe `VSub`）：特化解不改写既有值，
    /// 只把解包在外面；`force` 在读点把 σ 推进值的结构（[`Infer::frcs`]，
    /// 对齐 dpm-nbe 的 `frcS`）。不变式：`force` 的返回值顶层不会是
    /// VSub（fuel 耗尽的降级点在 frcs 的 lookup 命中处，返回裸 rigid）。
    VSub(Rc<Val>, Rc<Subst>),
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
                    Val::VSub(Rc::new(e.val.clone()), self.clone())
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
                Val::Match(s, env, _, pending) => {
                    mentions_level(s, sub)
                        || env_slots(env, sub)
                        || pending.iter().any(|(u, _)| mentions_level(u, sub))
                }
                // 已被包裹的值保守视为引用（内层结构不再探查）
                Val::VSub(..) => true,
                // 卡住内建的 spine 槽是值，读点会流出——必须扫描
                Val::Prim(_, sp) => sp.iter().any(|(v, _)| mentions_level(v, sub)),
                Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) => false,
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
/// （Flex / Rigid / 卡住投影 Obj / VSub / **卡住 match**——后者把实参收进
/// pending，L07 splice 同款）能吃 η 新变量。字面量 / U / Π / Sum / SumCase
/// 与实参相遇时无从应用。
pub(crate) fn v_applicable(v: &Val) -> bool {
    matches!(
        v,
        Val::Flex(..)
            | Val::Rigid(..)
            | Val::Obj(..)
            | Val::Prim(..)
            | Val::Match(..)
            | Val::VSub(..)
    )
}

/// 深链候选探测（零分配、不 force）：沿"第一个子值"链下探至多 8 层。
/// 只有可能深的值才走帧式收集器（quote_deep / rename_deep）——浅结构
/// （绝大多数 Sum / SumCase / Obj 值）保持直接递归臂，省掉每层帧的 Vec
/// 分配（微基准回归修复：match 负载每层一个 Sum 值，帧分配占可见比例）。
pub(crate) fn deep_chain(v: &Val) -> bool {
    let mut cur: &Val = v;
    for _ in 0..8 {
        cur = match cur {
            Val::SumCase { datas, .. } => match datas.first() {
                Some((_, next, _)) => next,
                None => return false,
            },
            Val::Obj(x, _, _) => x,
            Val::Sum(_, params, _) => match params.first() {
                Some((_, next, _, _)) => next,
                None => return false,
            },
            Val::VSub(x, _) => x,
            _ => return false,
        };
    }
    true
}

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc，
/// force 在消费点惰性推开）。σ 为空时零开销直通。
pub(crate) fn wrap_sub(sub: &Rc<Subst>, v: Val) -> Val {
    if sub.is_empty() {
        v
    } else {
        Val::VSub(Rc::new(v), sub.clone())
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

/// 内联容量 N 的小栈（热路径零分配；溢出转 Vec）。`T: Copy` 让内联数组
/// 可用 seed 初始化——深值遍历与结构比较的任务栈在浅结构（绝大多数调用）
/// 下完全不碰堆；溢出（宽 spine / 深链）只多一次 Vec 分配，与无内联版同阶。
/// （移植自 L07 `mod.rs` 同款结构，2026-09-18 深值轮。）
pub(crate) struct InlineStack<T: Copy, const N: usize> {
    buf: [T; N],
    len: usize,
    spill: Vec<T>,
}

impl<T: Copy, const N: usize> InlineStack<T, N> {
    pub(crate) fn with_first(seed: T) -> Self {
        let mut s = InlineStack {
            buf: [seed; N],
            len: 0,
            spill: Vec::new(),
        };
        s.push(seed);
        s
    }
    #[inline]
    pub(crate) fn push(&mut self, v: T) {
        if self.len < N {
            self.buf[self.len] = v;
            self.len += 1;
        } else {
            self.spill.push(v);
        }
    }
    #[inline]
    pub(crate) fn pop(&mut self) -> Option<T> {
        if let Some(v) = self.spill.pop() {
            return Some(v);
        }
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        Some(self.buf[self.len])
    }
    #[inline]
    pub(crate) fn extend<I: IntoIterator<Item = T>>(&mut self, it: I) {
        for v in it {
            self.push(v);
        }
    }
}

/// 值树里是否出现某层级（浅层结构扫描；闭包跳过——那里的环由 force 的
/// fuel 兜底）。`VSub` 只扫解值自身结构、**不扫 σ 的映射值**：σ 的其它
/// 条目合法引用别的模式变量，扫进来会把无害的解误判成环。
///
/// 迭代实现（移植 L07 2026-09-18 深值轮）：`succ^N zero` 型深值可由 eval
/// 不烧 fuel 地构造（def 倍增链），递归版在万级深度爆栈。显式工作栈按与
/// 旧递归完全相同的遍历面展开——存在性判定对访问顺序不敏感，语义不变；
/// 栈内联化使 match 编译热路径（每次头部精化）零堆分配。
pub(crate) fn val_mentions_lvl(v: &Val, x: Lvl) -> bool {
    let mut stack = InlineStack::<&Val, 16>::with_first(v);
    while let Some(v) = stack.pop() {
        match v {
            Val::Rigid(y, sp) => {
                if *y == x {
                    return true;
                }
                stack.extend(sp.iter().map(|(v, _)| v));
            }
            // **Flex 头的实参视为不透明**：可达性探测用 `Raw::Hole` 实例化构造子
            // 绑定器，fresh meta 的 pruning 会把整组绑定器（含被解变量本身）
            // 收进 spine——`l := succ (?m … l …)` 是"meta 应用到变量"的合法形，
            // 不是结构性自引用（旧 `update_cxt` 无 occurs，把 spine 算进来会把
            // 可达构造子误判不可达）。结构性自引用（`x := succ x`）仍由
            // Rigid/SumCase 等臂捕获；更深的间接环由 force 的 fuel 兜底。
            Val::Flex(_, _) => {}
            Val::Obj(o, _, sp) => {
                stack.push(o);
                stack.extend(sp.iter().map(|(v, _)| v));
            }
            Val::VSub(v, _) => stack.push(v),
            Val::Sum(_, params, _) => {
                stack.extend(params.iter().flat_map(|(_, v, t, _)| [v.as_ref(), t.as_ref()]));
            }
            Val::SumCase { typ, datas, .. } => {
                stack.push(typ);
                stack.extend(datas.iter().map(|(_, v, _)| v.as_ref()));
            }
            Val::Match(s, env, _, pending) => {
                stack.push(s);
                stack.extend(env.iter());
                stack.extend(pending.iter().map(|(v, _)| v));
            }
            Val::Lam(..) | Val::Pi(..) | Val::U(_) | Val::LiteralType | Val::LiteralIntro(_) => {}
            // 内建 spine 实参：结构上可能引用层级（保守扫描）
            Val::Prim(_, sp) => stack.extend(sp.iter().map(|(v, _)| v)),
        }
    }
    false
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
    cell::{Cell, RefCell},
    ops::{Add, Sub},
    rc::Rc,
};

use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug)]
struct UnifyError;

/// 合一失败的**原因分档**（移植 L07 P3，对齐 dpm-nbe 的
/// `UnifyRes = USucc | UAbs | UIDK`）。`UnifyError` 本身保持无字段：
/// 分档挂在 [`Infer`] 上——每个顶层合一入口先 [`Infer::reset_unify_kind`]，
/// 失败臂按语义 `note`，调用方取 [`Infer::unify_kind`] 决定诊断与覆盖处理。
///
/// 默认值 = `Absurd`：**未被显式分档的失败沿用旧行为**（分支不可达），
/// 这是渐进策略——把"确定无解"与"判不出来"逐点分清需要逐个臂论证。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnifyKind {
    /// 结构性矛盾：确定无解（`zero ≐ succ _`、不同构造子、不同字面量）。
    Absurd,
    /// 无法判定：既不能证相等、也不是矛盾（卡住 match 的相等性、预算耗尽）。
    Undecided,
    /// 预算耗尽（fuel）：判定不可信，最保守。
    Fuel,
}

impl UnifyKind {
    fn rank(self) -> u8 {
        match self {
            UnifyKind::Absurd => 0,
            UnifyKind::Undecided => 1,
            UnifyKind::Fuel => 2,
        }
    }
}

/// 卡住 match 相等性比较的**总次数**上限（每个顶层合一入口一份；移植 L07 P2
/// / 孪生 `MATCH_CMP_BUDGET = 64` 同口径）。结构快路径先试，只有快路径失效、
/// 真正逐分支重求值的比较才计入并消耗；超出按"无法判定为相等"保守失败。
pub(crate) const MATCH_CMP_BUDGET: u32 = 64;

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
    /// 顶层声明值表（键 = `global_idx`，即登记序）：值都是终值（递归 def 在
    /// 体检查期间先放 `Rigid(global_idx + 1919810)` 占位、检查完覆盖）。引用
    /// 方按哨兵大下标直查本表——等价 L07/L08 的名字键 decl 表（O(1)）。
    global: FxHashMap<Lvl, VTy>,
    /// 顶层名字表（名字 → (层级, 类型值)）：**append-only，随 Infer 存续、
    /// 不随 Cxt 克隆**——顶层 def/enum/构造子的真名与 `fake_bind` 的递归
    /// 占位都记在这里（L10 的 `Cxt::define` 同源迁移，2026-09-20 参考版
    /// O(D²) 修复）。
    ///
    /// 旧设计把顶层名累积进 `Cxt.src_names`（每声明 +1 条），而 `fake_bind`
    /// / `define` 每次克隆整表（表大小 O(D)）⇒ 每声明 2 次全表深拷、总计
    /// O(D²)（L09 strchain k=11 实测 2814ms vs 孪生 3.1ms，见
    /// `docs/perf-debt-2026-09-12.md` P2 的孪生侧同款处置）。查找顺序：
    /// `cxt.src_names`（局部，遮蔽）优先，回落本表。
    global_names: FxHashMap<String, (Lvl, Rc<VTy>)>,
    /// **中性全局视图开关**（孪生 `Machine.neutral` 视图的参考版形态）：
    /// 置位期间 `eval` 的全局回落返回中性 rigid（`Rigid(GLOBAL_BASE + idx)`）
    /// 而非全局值——Match/Match 合一、`rename` 与 `quote` 的分支体重求值要
    /// 的"全局名字不再递归展开"视图（求值函数全为 `&self`，Cell 提供内部
    /// 可变性；可嵌套，存旧值恢复）。
    ///
    /// 旧实现是三处 `self.clone()` 整个 Infer 再就地改写 global 表
    /// （O(D + meta 数) 深拷，孪生侧曾以 `neutral_of(&self.globals)` 整拷
    /// 同病，perf-debt P2 残余平方项）——开关是 O(1)，语义逐值一致：原先
    /// 被改写的每个条目恰好是"已登记的全局 → 中性 rigid"，未登记的仍
    /// panic（本字段只改回落路径的取值，不改可达性）。
    neutral_globals: Cell<bool>,
    /// 精化传播的展开燃料池（Cell 随 `&self` 的 force/frcs 递减）。仅
    /// frcs 的 lookup 命中点燃烧；外部入口（unify_catch / nf / 模式编译 /
    /// check_pm）充值。耗尽即停止精化展开（有界降级，防闭环无限推进）。
    unify_fuel: Cell<u32>,
    /// 卡住 match 相等性比较的总次数预算（P2；每顶层合一入口重置）。
    match_cmp_budget: Cell<u32>,
    /// 最近一次合一失败的原因分档（P3；见 [`UnifyKind`]）。
    unify_kind: Cell<UnifyKind>,
    /// 正在展开的 meta 链（跨 meta 环守卫，P5）：force 展开已解 meta 时压栈，
    /// 同一 meta 再次出现即判定环，返回卡住的 Flex，不再递归烧 fuel。
    meta_expanding: RefCell<Vec<MetaVar>>,
    /// **递归定义检查期间**的全局 id 集合（`fake_bind` 插入、`define_global`
    /// 移除）：这些名字在体内被引用时必须编成 `Tm::Var(哨兵大下标)`（旧版
    /// 哨兵语义——中性视图会中和它，防递归展开）；其余已定名全局编成
    /// `Tm::Global(哨兵大下标)`（中性视图照常展开，与旧版 env 槽引用一致）。
    in_progress_globals: FxHashSet<Lvl>,
}

/// 燃料池容量（对齐 L07 蓝本）。
const UNIFY_FUEL: u32 = 4096;

/// 基准专用燃料覆盖：环境变量 `TYPORT_UNIFY_FUEL`（缺省 = [`UNIFY_FUEL`]）。
/// smalltt 迁移基准（NatConv / TreeConv 等 1e6 级 β 步的转换检查）远超 4096；
/// 显式设置该变量可放大单次合一池。未设置时行为与原来逐位一致。
fn unify_fuel_budget() -> u32 {
    static BUDGET: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *BUDGET.get_or_init(|| {
        std::env::var("TYPORT_UNIFY_FUEL")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(UNIFY_FUEL)
    })
}

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            global: FxHashMap::default(),
            global_names: FxHashMap::default(),
            neutral_globals: Cell::new(false),
            unify_fuel: Cell::new(unify_fuel_budget()),
            match_cmp_budget: Cell::new(MATCH_CMP_BUDGET),
            unify_kind: Cell::new(UnifyKind::Absurd),
            meta_expanding: RefCell::new(Vec::new()),
            in_progress_globals: FxHashSet::default(),
        }
    }
    /// 顶层名的局部影子：`Cxt::new` 的两个内建（`String` /
    /// `string_concat`）留在局部表里，而 `Raw::Var` / 构造子探测一律**局部
    /// 优先**；旧单表语义是"后定义覆盖先定义"，两表分离后顶层 def 若与内建
    /// 撞名，必须同步覆写局部条目，否则新 def 反被内建遮蔽（同名递归 def
    /// 的自身引用也会指错）。无同名时是纯读。
    fn shadow_local(cxt: &mut Cxt, x: &Span<String>, lvl: Lvl, ty: &Rc<VTy>) {
        if cxt.src_names.get(&x.data).is_some() {
            cxt.src_names.insert(x.data.clone(), (lvl, ty.clone()));
        }
    }
    /// `Cxt::fake_bind` 的 Infer 侧形态：递归 def/enum 的占位——名字指到
    /// 全局层级（`global_idx + 1919810`），env/lvl/locals/pruning 一概不动，
    /// 返回父上下文的视图。真名随后由 [`Self::define_global`] 覆盖同一条目
    /// （占位只服务本次检查的体）。
    fn fake_bind(&mut self, cxt: &Cxt, x: Span<String>, a: VTy, global_idx: Lvl) -> Cxt {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), cxt.lvl.0);
        let lvl = global_idx + 1919810;
        self.in_progress_globals.insert(global_idx);
        let a = Rc::new(a);
        self.global_names.insert(x.data.clone(), (lvl, a.clone()));
        let mut out = cxt.clone();
        Self::shadow_local(&mut out, &x, lvl, &a);
        out
    }
    /// 顶层 define（`Decl::Def` / `Decl::Enum` / 构造子登记）：真名进
    /// [`Self::global_names`]（append-only，不随 Cxt 克隆），值进
    /// [`Self::global`]（键 = `global_idx`）。**顶层声明不再压进 Cxt**：
    /// env / lvl / locals / pruning 一概不动（L07/L08 decl 表载体的等价物，
    /// 2026-11-12 载体切换）。
    ///
    /// 动机：旧设计把每个顶层 def/enum/构造子作为上下文条目（env 槽 + lvl+1
    /// + `Locals::Define` + pruning None），于是 ①`eval` 的 de Bruijn 下标
    /// 查 env（Rc 单链 `iter().nth`）随声明数线性增长 → 每次引用老全局
    /// O(D)；②`fresh_meta` 的 `close_ty(&cxt.locals, …)` 链长 = D → 每建一个
    /// 隐式 meta O(D²)。改用哨兵大下标 + 全局表直查后两处都是 O(1)，语义
    /// 逐值不变（局部表不增长，返回的 Cxt 克隆是 O(1)）。
    fn define_global(&mut self, cxt: &Cxt, x: Span<String>, global_idx: Lvl, vt: Val, va: VTy) -> Cxt {
        let lvl = global_idx + 1919810;
        self.in_progress_globals.remove(&global_idx);
        self.global.insert(global_idx, vt);
        let va = Rc::new(va);
        self.global_names.insert(x.data.clone(), (lvl, va.clone()));
        let mut out = cxt.clone();
        Self::shadow_local(&mut out, &x, lvl, &va);
        out
    }
    /// 给精化展开的燃料池充值（外部合一 / 求值入口调用）。
    pub(crate) fn meta_refuel(&self) {
        self.unify_fuel.set(unify_fuel_budget());
    }
    /// 燃料池是否已耗尽（探测失败侧的观察口：fuel 耗尽的失败是预算问题
    /// 而非结构冲突——probe_accessible 尾部据此把失败按"可达"处理，保守
    /// 地要求覆盖。L07 2026-09-18 评审修复 2 的同步移植）。
    pub(crate) fn fuel_exhausted(&self) -> bool {
        self.unify_fuel.get() == 0
    }
    /// 顶层合一入口调用：每份"卡住 match 比较次数"预算重置（P2）。
    pub(crate) fn reset_match_cmp_budget(&self) {
        self.match_cmp_budget.set(MATCH_CMP_BUDGET);
    }
    /// 进入一次"真正的"卡住 match 逐分支比较（结构快路径失效之后）时消耗
    /// 一次预算；`false` = 预算耗尽（调用方按"无法判定为相等"失败）。
    pub(crate) fn burn_match_cmp_budget(&self) -> bool {
        let b = self.match_cmp_budget.get();
        if b == 0 {
            false
        } else {
            self.match_cmp_budget.set(b - 1);
            true
        }
    }
    /// 顶层合一入口调用：把失败原因重置为中性值（`Absurd`，沿用旧口径）。
    pub(crate) fn reset_unify_kind(&self) {
        self.unify_kind.set(UnifyKind::Absurd);
    }
    /// 失败臂调用：按"最不结论化"语义累积（`Absurd < Undecided < Fuel`）。
    pub(crate) fn note_unify_kind(&self, k: UnifyKind) {
        let cur = self.unify_kind.get();
        if k.rank() > cur.rank() {
            self.unify_kind.set(k);
        }
    }
    /// 读取当前失败原因（只在 `unify` 返回 `Err` 后有意义）。
    pub(crate) fn unify_kind(&self) -> UnifyKind {
        self.unify_kind.get()
    }
    fn new_meta(&mut self, a: VTy) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.eval(
            &List::new(),
            close_ty(&cxt.locals, self.quote(cxt.lvl, a)),
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
                MetaEntry::Solved(t_solved, _) => {
                    // P5 跨 meta 环守卫：同一 meta 已在展开栈上 ⇒ 环。返回卡住
                    // 的 Flex（与燃料耗尽的降级同形），把"靠 fuel 兜底"变成
                    // 确定性的有界终止（移植 L07 mod.rs 同款）。
                    if self.meta_expanding.borrow().contains(&m) {
                        return Val::Flex(m, sp);
                    }
                    self.meta_expanding.borrow_mut().push(m);
                    let out = self.force(self.v_app_sp(t_solved.clone(), sp));
                    let mut st = self.meta_expanding.borrow_mut();
                    if let Some(i) = st.iter().rposition(|x| *x == m) {
                        st.remove(i);
                    }
                    drop(st);
                    out
                }
                MetaEntry::Unsolved(_) => Val::Flex(m, sp),
            },
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1）。fuel 耗尽的降级点也在该处
            // （返回裸 rigid）。
            Val::VSub(v, sub) => self.frcs(&sub, (*v).clone()),
            // 卡住的 match：scrutinee 是在 match 创建之后才被特化/解出时，
            // 这里重新尝试选分支。没有这一步，精化无法传播进"卡住 match
            // 里面"（期望类型 `Eq (add a zero) a` 的 `add a zero` 就是它）。
            Val::Match(s, env, cases, pending) => {
                let s2 = self.force((*s).clone());
                if let Val::SumCase { .. } = &s2 {
                    if burn(&self.unify_fuel) {
                        if let Some((tm, env2)) = Compiler::eval_aux(self, &s2, &env, &cases) {
                            // 分支选中：先在值层应用卡住期累积的实参（值无需
                            // quote，作用域天然正确），再 force 展开。
                            let mut v = self.eval_ref(&env2, tm);
                            for (u, i) in pending.iter().cloned() {
                                v = self.v_app(v, u, i);
                            }
                            return self.force(v);
                        }
                    }
                }
                Val::Match(s, env, cases, pending)
            }
            // 卡住的内建：实参先 force（spine 槽可能存未归约的嵌套 prim），
            // 反转自然序后交 `prim_reduce`；元数不足 / 实参不合时保持卡住
            // （None），不 panic。
            Val::Prim(name, sp) => {
                if burn(&self.unify_fuel) {
                    let mut args: Vec<Val> =
                        sp.iter().map(|(v, _)| self.force(v.clone())).collect();
                    args.reverse(); // spine 头 = 最后应用 → 自然序
                    if let Some(v) = self.prim_reduce(&name, &args) {
                        return self.force(v);
                    }
                }
                Val::Prim(name, sp)
            }
            _ => t,
        }
    }

    /// 卡住内建的归约体（L07 `Infer::prim_reduce` 的 L09 裁剪版：本层唯一
    /// builtin 是 string_concat）。`args` 自然序（最先应用在前）；元数 /
    /// 字面量检查不满足即 None 保持卡住——源码可达路径不 panic。
    fn prim_reduce(&self, name: &str, args: &[Val]) -> Option<Val> {
        match name {
            "string_concat" => {
                if args.len() < 2 {
                    return None;
                }
                match (&args[0], &args[1]) {
                    (Val::LiteralIntro(a), Val::LiteralIntro(b)) => Some(Val::LiteralIntro(
                        vspan(tmspan(a).map(|x| format!("{x}{}", b.data))),
                    )),
                    _ => None,
                }
            }
            _ => None,
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
                self.frcs(&composed, (*v2).clone())
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
                Rc::new(self.frcs(sub, (*o).clone())),
                name,
                self.wrap_sp(sub, sp),
            )),
            // 闭包 env 逐槽包裹（惰性，不进入闭包体重求值）；返回同型值。
            Val::Lam(x, i, cl) => Val::Lam(x, i, Closure(self.frcs_env(sub, &cl.0), cl.1)),
            Val::Pi(x, i, a, cl) => Val::Pi(
                x,
                i,
                Rc::new(self.frcs(sub, (*a).clone())),
                Closure(self.frcs_env(sub, &cl.0), cl.1),
            ),
            // Sum/SumCase 的槽位同样只包裹
            Val::Sum(name, params, cases) => Val::Sum(
                name,
                Rc::new(
                    params
                        .iter()
                        .map(|(n, v, t, i)| {
                            (
                                n.clone(),
                                Rc::new(wrap_sub(sub, rc_take(v.clone()))),
                                Rc::new(wrap_sub(sub, rc_take(t.clone()))),
                                *i,
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
                cases,
            ),
            Val::SumCase {
                typ,
                case_name,
                datas,
            } => Val::SumCase {
                typ: Rc::new(wrap_sub(sub, rc_take(typ))),
                case_name,
                datas: Rc::new(
                    datas
                        .iter()
                        .map(|(n, v, i)| (n.clone(), Rc::new(wrap_sub(sub, rc_take(v.clone()))), *i))
                        .collect::<Vec<_>>(),
                ),
            },
            // scrutinee **推进**（重选分支需要解出的构造子值：`force` 的
            // Match 臂在 scratchinee 展开成构造子值后重选分支）；捕获 env
            // 与 pending 只包裹（同 L07 frcs 的 Match 臂纪律）。
            Val::Match(s, env, cases, pending) => self.force(Val::Match(
                Rc::new(self.frcs(sub, (*s).clone())),
                self.frcs_env(sub, &env),
                cases,
                Rc::new(
                    pending
                        .iter()
                        .map(|(u, i)| (wrap_sub(sub, u.clone()), *i))
                        .collect::<Vec<_>>(),
                ),
            )),
            // 卡住内建：spine 槽只包裹不推进（槽位引用是作用域事实），
            // 包裹后交回 force 重走归约臂。
            Val::Prim(name, sp) => self.force(Val::Prim(name, self.wrap_sp(sub, sp))),
            // U / LiteralType / LiteralIntro：原样
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
        env.map(|v| Val::VSub(Rc::new(v.clone()), sub.clone()))
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
        // 借用 eval：直接读 Rc 闭包体，β 不再深拷贝体（L07 P0-1 第 2 步 /
        // L08 fd5a3a95 的 L09 对应物）。
        self.eval_ref(&closure.0.prepend(u), &closure.1)
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
            // 卡住的内建：实参收进 spine（头 = 最后应用），归约由 force 的
            // prim_reduce 在满元数 + 全字面量时触发。
            Val::Prim(name, sp) => Val::Prim(name, sp.prepend((u, i))),
            // 卡住的 match 把实参收进 pending（值层保存）：scrutinee 归约选中
            // 分支后由 force / eval 在**值层**逐个应用——项层 splice 需要把实参
            // quote 成项，实参的自由变量层级可能超出捕获 env，引不到正确上下文
            // （L07 v_app 同款；L09 早期此处 panic，合法程序可触发）。
            Val::Match(val, env, cases, pending) => {
                let mut pending = (*pending).clone();
                pending.push((u, i));
                Val::Match(val, env, cases, Rc::new(pending))
            }
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

    /// 拥有版 eval（入口）：顶层 `Lam`/`Pi` 直接把 `Rc` 体交给 `Closure`
    /// （零克隆）；其余形态委托 [`Self::eval_ref`] 只读遍历。
    fn eval(&self, env: &Env, tm: Tm) -> Val {
        match tm {
            Tm::Lam(x, i, t) => Val::Lam(vspan(x), i, Closure(env.clone(), t)),
            Tm::Pi(x, i, a, b) => Val::Pi(
                vspan(x),
                i,
                Rc::new(self.eval(env, (*a).clone())),
                Closure(env.clone(), b),
            ),
            // 拥有 cases 的入口：选中臂借用求值（不拷分支体），卡住时 cases
            // 直接 move 进 Val::Match（借用路径才需要 clone，见 eval_ref）。
            Tm::Match(tm, cases) => {
                let val = self.force(self.eval(env, *tm));
                match val {
                    val @ Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, &val, env, &cases) {
                            Some((body, env2)) => self.eval_ref(&env2, body),
                            // 无臂命中：按卡住值保留（延迟到 scrutinee/模式可用），
                            // 不再 unwrap 成 panic（L09 struct 模式支持所需）。
                            None => Val::Match(
                                Rc::new(val),
                                env.clone(),
                                Rc::new(cases),
                                Rc::new(Vec::new()),
                            ),
                        }
                    }
                    neutral => Val::Match(
                        Rc::new(neutral),
                        env.clone(),
                        Rc::new(cases),
                        Rc::new(Vec::new()),
                    ),
                }
            }
            tm => self.eval_ref(env, &tm),
        }
    }

    /// 借用版 eval：只读遍历 `&Tm`，闭包体 / match 分支体不再深拷（L07 P0-1
    /// 与 L08 bc929dcc/fd5a3a95 的 L09 对应物）。需要把 λ 体存进
    /// `Closure(Rc<Tm>)` 时只能克隆 Box 内容——只发生在"分支体/闭包体内部
    /// 再出现 λ 字面量"的形态，不是每步 β 的热路径。
    fn eval_ref(&self, env: &Env, tm: &Tm) -> Val {
        match tm {
            // 全局引用（哨兵大下标）：先判哨兵直查全局表 O(1)，**不再先扫
            // env**——顶层声明不进上下文后，env 只含局部 binder/内建，扫它
            // 对全局引用是纯浪费（旧实现 `env.iter().nth(大下标)` 会走完整条
            // env 才落到这里的 None 分支）。
            // `Var(大下标)` = 递归检查期自身占位（中性视图中和成 rigid）；
            // `Global(大下标)` = 已定名全局引用（照常展开，同旧版 env 槽）。
            Tm::Global(x) => self.global.get(&Lvl(x.0 - 1919810)).unwrap().clone(),
            Tm::Var(x) => {
                if x.0 >= 1919810 {
                    let v = self.global.get(&Lvl(x.0 - 1919810)).unwrap();
                    return if self.neutral_globals.get() {
                        Val::vvar(Lvl(x.0))
                    } else {
                        v.clone()
                    };
                }
                match env.iter().nth(x.0 as usize) {
                    Some(v) => v.clone(),
                    None => panic!("unbound de Bruijn index {x:?}"),
                }
            }
            Tm::Obj(tm, name) => {
                let recv = self.eval_ref(env, tm);
                // 精化包裹的接收者（subst_cxt 包裹的 env 槽会以 VSub 流出）
                // 先推开 σ 再判形态；force 对非 VSub/Flex 是恒等，旧行为不变。
                let recv = match recv {
                    v @ Val::VSub(..) => self.force(v),
                    v => v,
                };
                match recv {
                    Val::Sum(_, params, _) => {
                        params.iter()
                            .find(|p| &p.0 == name)
                            .map(|p| rc_take(p.1.clone()))
                            .unwrap()
                    },
                    Val::SumCase { datas, typ, .. } => {
                        // typ 槽可能被 frcs 包成 VSub（只包裹不物化）——判
                        // Sum 前先 force
                        (match self.force(rc_take(typ)) {
                            Val::Sum(_, params, _) => params,
                            t => panic!("impossible {t:?}"),
                        }).iter()
                            .map(|x| (x.0.clone(), x.1.clone(), x.3))
                            .chain(datas.iter().cloned())
                            .find(|(f_name, _, _)| f_name == name)
                            .map(|x| rc_take(x.1))
                            .unwrap()
                    },
                    x @ Val::Rigid(_, _) => {
                        Val::Obj(Rc::new(x), vspan(name.clone()), List::new())
                    }
                    x => panic!("impossible {x:?}"),
                }
            }
            Tm::App(t, u, i) => self.v_app(self.eval_ref(env, t), self.eval_ref(env, u), *i),
            Tm::Lam(x, i, t) => Val::Lam(vspan(x.clone()), *i, Closure(env.clone(), t.clone())),
            Tm::Pi(x, i, a, b) => Val::Pi(
                vspan(x.clone()),
                *i,
                Rc::new(self.eval_ref(env, a)),
                Closure(env.clone(), b.clone()),
            ),
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval_ref(env, t);
                self.eval_ref(&env.prepend(t_val), u)
            }
            Tm::U(x) => Val::U(*x),
            Tm::Meta(m) => self.v_meta(*m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval_ref(env, t), pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(vspan(x.clone())),
            Tm::LiteralType => Val::LiteralType,
            Tm::Prim(name) => {
                // 零元卡住头：实参一律经 App 到达（builtin 值即中性 Prim
                // 头，quote 产物也是 `Prim 实参` 应用形态）。**不读现场
                // env**——旧实现把 env 前两槽当实参，只在 builtin λ 链体的
                // 正典路径下正确；quoted Prim 在其它 env 下重求值会捕获
                // 无关槽 / 越界 panic。归约统一在 force（prim_reduce）。
                Val::Prim(name.clone(), List::new())
            }
            Tm::Sum(name, params, cases) => {
                let new_params = params
                    .iter()
                    .map(|x| {
                        (
                            vspan(x.0.clone()),
                            Rc::new(self.eval_ref(env, &x.1)),
                            Rc::new(self.eval_ref(env, &x.2)),
                            x.3,
                        )
                    })
                    .collect();
                Val::Sum(vspan(name.clone()), Rc::new(new_params), Rc::new(cases.iter().map(|s| vspan(s.clone())).collect()))
            }
            Tm::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| (vspan(p.0.clone()), Rc::new(self.eval_ref(env, &p.1)), p.2))
                    .collect();
                let typ = self.eval_ref(env, typ);
                Val::SumCase {
                    typ: Rc::new(typ),
                    case_name: vspan(case_name.clone()),
                    datas: Rc::new(datas),
                }
            }
            Tm::Match(tm, cases) => {
                let val = self.eval_ref(env, tm);
                let val = self.force(val);
                match val {
                    val @ Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, &val, env, &cases[..]) {
                            Some((body, env2)) => self.eval_ref(&env2, body),
                            None => Val::Match(
                                Rc::new(val),
                                env.clone(),
                                Rc::new(cases.clone()),
                                Rc::new(Vec::new()),
                            ),
                        }
                    }
                    neutral => {
                        // 借用路径下卡住值必须持有 owned cases：深拷只发生在
                        // "match 卡住"这一枝（选中臂热路径不再拷分支体）。
                        Val::Match(
                            Rc::new(neutral),
                            env.clone(),
                            Rc::new(cases.clone()),
                            Rc::new(Vec::new()),
                        )
                    }
                }
            }
        }
    }

    /// 中性全局视图下的求值（[`Self::neutral_globals`] 的作用域包装）：
    /// 置位 → eval → 恢复旧值（可嵌套）。三处 Match 分支体重求值点共用
    /// （match 合一的臂体 / `rename` 的 Match 臂 / `quote` 的 Match 臂），
    /// 取代旧实现"`self.clone()` 整机深拷 + 就地改写 global 表"。
    fn eval_neutral(&self, env: &Env, tm: Tm) -> Val {
        let prev = self.neutral_globals.replace(true);
        let v = self.eval(env, tm);
        self.neutral_globals.set(prev);
        v
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

    /// quote 入口：先 force 到 WHNF，再按形态分派——**可能深**的
    /// Sum/SumCase/Obj 链（如 `succ^N zero`）交给帧式收集器
    /// [`Self::quote_deep`]；其余形态（Lam/Pi/Match/spine 头，结构嵌套浅，
    /// 以及浅的 Sum/SumCase/Obj）回落 [`Self::quote_arm`] 的直接递归臂
    /// （L07 README §7.6 路线；浅值探测避免每层多付帧分配的代价）。
    fn quote(&self, l: Lvl, t: Val) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t {
            Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => self.quote_deep(l, t),
            // 正常路径 force 后顶层不会是 VSub；fuel 耗尽时 force 原样返回
            // VSub——解包打印内层（σ 未推开，保真度同旧版"打印未展开 rigid"）。
            // 必须 **move**（不能 clone）：深 Box 链的 clone 是递归深拷贝。
            Val::VSub(v, _) => self.quote(l, (*v).clone()),
            _ => self.quote_arm(l, t),
        }
    }

    /// quote 的深链收集器：**Sum / SumCase / Obj** 帧式下降/组装（与
    /// [`Self::rename_deep`] 同构）。深值按值深递归会爆栈（L07 README §7.6：
    /// `quote` 曾是仅剩的递归路径之一）；子件回落 [`Self::quote_arm`]。
    fn quote_deep(&self, l: Lvl, root: Val) -> Tm {
        enum FrameKind {
            Sum {
                name: VSpan,
                cases: Vec<VSpan>,
                metas: Vec<(VSpan, Icit)>,
            },
            SumCase {
                case_name: VSpan,
                datas_metas: Vec<(VSpan, Icit)>,
            },
            Obj {
                name: VSpan,
            },
        }
        struct Frame {
            pending: Vec<Val>,
            icits: Vec<Icit>,
            kind: FrameKind,
            done: Vec<Tm>,
            idx: usize,
        }
        fn frame_new(v: Val) -> Frame {
            match v {
                Val::Sum(name, params, cases) => {
                    let mut pending = Vec::with_capacity(params.len() * 2);
                    let mut metas = Vec::with_capacity(params.len());
                    for (n, v, t, i) in params.iter() {
                        pending.push(rc_take(v.clone()));
                        pending.push(rc_take(t.clone()));
                        metas.push((n.clone(), *i));
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits: Vec::new(),
                        kind: FrameKind::Sum {
                            name,
                            cases: (*cases).clone(),
                            metas,
                        },
                        done: Vec::with_capacity(n_all),
                        idx: 0,
                    }
                }
                Val::SumCase {
                    typ,
                    case_name,
                    datas,
                } => {
                    let mut pending = Vec::with_capacity(datas.len() + 1);
                    pending.push(rc_take(typ));
                    let mut datas_metas = Vec::with_capacity(datas.len());
                    for (n, v, i) in datas.iter() {
                        pending.push(rc_take(v.clone()));
                        datas_metas.push((n.clone(), *i));
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits: Vec::new(),
                        kind: FrameKind::SumCase {
                            case_name,
                            datas_metas,
                        },
                        done: Vec::with_capacity(n_all),
                        idx: 0,
                    }
                }
                Val::Obj(x, name, sp) => {
                    // pending = [被投影者, spine 实参…]；实参按 List 头→尾序入列
                    let mut pending = vec![(*x).clone()];
                    let mut icits = Vec::new();
                    for (u, i) in sp.iter() {
                        pending.push(u.clone());
                        icits.push(*i);
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits,
                        kind: FrameKind::Obj { name },
                        done: Vec::with_capacity(n_all),
                        idx: 0,
                    }
                }
                _ => unreachable!("quote_deep 只接受 Sum/SumCase/Obj"),
            }
        }
        fn frame_assemble(frame: Frame) -> Tm {
            match frame.kind {
                FrameKind::Sum {
                    name,
                    cases,
                    metas,
                } => {
                    let mut it = frame.done.into_iter();
                    let params = metas
                        .into_iter()
                        .map(|(n, i)| {
                            let v = it.next().unwrap();
                            let t = it.next().unwrap();
                            (tmspan(&n), v, t, i)
                        })
                        .collect();
                    Tm::Sum(tmspan(&name), params, cases.iter().map(tmspan).collect())
                }
                FrameKind::SumCase {
                    case_name,
                    datas_metas,
                } => {
                    let mut it = frame.done.into_iter();
                    let typ = it.next().unwrap();
                    let datas = datas_metas
                        .into_iter()
                        .map(|(n, i)| (tmspan(&n), it.next().unwrap(), i))
                        .collect();
                    Tm::SumCase {
                        typ: Box::new(typ),
                        case_name: tmspan(&case_name),
                        datas,
                    }
                }
                FrameKind::Obj { name } => {
                    let mut it = frame.done.into_iter();
                    let head = Tm::Obj(Box::new(it.next().unwrap()), tmspan(&name));
                    let args: Vec<Tm> = it.collect();
                    let mut acc = head;
                    // spine 头 = 最后应用 ⇒ 逆序折叠（与 quote_sp 应用序一致）
                    for (u, i) in args.into_iter().zip(frame.icits).rev() {
                        acc = Tm::App(Box::new(acc), Box::new(u), i);
                    }
                    acc
                }
            }
        }
        let mut frames: Vec<Frame> = vec![frame_new(root)];
        let mut result: Option<Tm> = None;
        while let Some(frame) = frames.last_mut() {
            if frame.idx == frame.pending.len() {
                let frame = frames.pop().unwrap();
                let tm = frame_assemble(frame);
                match frames.last_mut() {
                    Some(parent) => {
                        parent.done.push(tm);
                        parent.idx += 1;
                    }
                    None => result = Some(tm),
                }
                continue;
            }
            // **move 出**待处理槽（不能 clone）：深链的原始值若留在 frame 里，
            // 帧弹栈时的 Drop 会沿 Rc 链递归 → 10 万层直接爆栈。replace 成
            // 廉价占位后，值被逐层搬走、无深递归 Drop。
            let w = std::mem::replace(&mut frame.pending[frame.idx], Val::U(0));
            let w = self.force(w);
            match w {
                // fuel 耗尽窗口：force 原样返回 VSub——解包后原地重试
                Val::VSub(v, _) => {
                    let frame = frames.last_mut().unwrap();
                    frame.pending[frame.idx] = (*v).clone();
                }
                Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => {
                    frames.push(frame_new(w));
                }
                _ => {
                    let tm = self.quote_arm(l, w);
                    let frame = frames.last_mut().unwrap();
                    frame.done.push(tm);
                    frame.idx += 1;
                }
            }
        }
        result.expect("quote_deep 至少产出一个 Tm")
    }

    /// quote 的浅结构臂（入口已 force、已分派掉深链形态）。
    fn quote_arm(&self, l: Lvl, t: Val) -> Tm {
        match t {
            Val::VSub(v, _) => self.quote(l, (*v).clone()),
            Val::Obj(x, name, sp) => self
                .quote_sp(l, Tm::Obj(Box::new(self.quote(l, (*x).clone())), tmspan(&name)), sp),
            Val::Sum(name, params, cases) => {
                let new_params = params
                    .iter()
                    .map(|x| {
                        (
                            tmspan(&x.0),
                            self.quote(l, rc_take(x.1.clone())),
                            self.quote(l, rc_take(x.2.clone())),
                            x.3,
                        )
                    })
                    .collect();
                Tm::Sum(tmspan(&name), new_params, cases.iter().map(tmspan).collect())
            }
            Val::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let datas = datas
                    .iter()
                    .map(|p| (tmspan(&p.0), self.quote(l, rc_take(p.1.clone())), p.2))
                    .collect();
                Tm::SumCase {
                    typ: Box::new(self.quote(l, rc_take(typ))),
                    case_name: tmspan(&case_name),
                    datas,
                }
            }
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Lam(x, i, closure) => Tm::Lam(
                tmspan(&x),
                i,
                Rc::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                tmspan(&x),
                i,
                Rc::new(self.quote(l, (*a).clone())),
                Rc::new(self.quote(l + 1, self.closure_apply(&closure, Val::vvar(l)))),
            ),
            Val::U(x) => Tm::U(x),
            Val::LiteralIntro(x) => Tm::LiteralIntro(tmspan(&x)),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim(name, sp) => self.quote_sp(l, Tm::Prim(name.clone()), sp),
            Val::Match(val, env, cases, pending) => {
                /*TODO:let tm_cases = cases
                    .into_iter()
                    .map(|(p, clos)| {
                        let binders_count = p.count_binders();
                        let body_tm = self.quote(l + binders_count, self.closure_apply_pats(&clos, l, &p));
                        (p, body_tm)
                    })
                    .collect();*/
                let tm_cases = cases
                    .iter()
                    .map(|x| (
                        x.0.clone(),
                        {
                            let env = (0..x.0.bind_count())
                                .fold(env.clone(), |env, x| env.prepend(Val::vvar(l + x)));
                            // 分支体在中性全局视图下重求值（全局名字不再展开，
                            // 免递归）——`eval_neutral` 取代旧的整机克隆
                            let tm = self.eval_neutral(&env, x.1.clone());
                            self.quote(l+x.0.bind_count(), tm)
                        }
                    ))
                    .collect();
                // 卡住期累积的实参按应用序包在 Match 外（值层应用在 force 的
                // 分支选中后做；quote → eval 往返由此保持恒等）。实参的自由
                // 层级属当前上下文，quote 在调用方的 l 下正确。
                let m = Tm::Match(Box::new(self.quote(l, (*val).clone())), tm_cases);
                pending.iter().fold(m, |acc, (u, i)| {
                    Tm::App(Box::new(acc), Box::new(self.quote(l, u.clone())), *i)
                })
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
        Closure(cxt.env.clone(), Rc::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: Val, t_prime: Val, span: Span<()>) -> Result<(), Error> {
        // 常规转换（spec = None）：不得解假设；一次合一入口充值精化燃料池
        self.meta_refuel();
        // P2/P3：每个顶层合一入口一份"卡住 match 比较"预算与失败分档
        self.reset_match_cmp_budget();
        self.reset_unify_kind();
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
            Tm::Var(_) | Tm::Global(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType
            | Tm::LiteralIntro(_) | Tm::Prim(_) => {}
            Tm::Obj(h, _) => stack.push(h),
            Tm::Lam(_, _, b) => stack.push(&**b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                n += pr.len() as u64;
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(&**a);
                stack.push(&**b);
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

/// 参考版基准口径：check + nf——取**最后一个 def** 的登记值（全局表末条；
/// 顶层声明不再占 env 槽）空层级引读并数节点（深 Box 树的递归析构会爆栈，
/// `mem::forget`）。
// ── 临时实验探针（l09probe 用；实验结束删除）────────────────────────────
pub fn stats_reset() {}
pub fn stats_print(_label: &str) {}
pub(crate) fn bench_check_nf(decls: &[parser::syntax::Decl]) -> u64 {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new();
    let mut last: Option<Val> = None;
    for d in decls {
        let is_def = matches!(d, parser::syntax::Decl::Def { .. });
        let n_globals = infer.global.len();
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return 0,
        }
        if is_def {
            last = infer.global.get(&Lvl(n_globals as u32)).cloned();
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

// --------------------------------------------------------------------------------
// 2026-09-20 负例补齐（模式匹配「应当失败」）。
//
// 本层此前只有 test1/test2 两个正向用例，三处覆盖义务（顶层缺构造子 / 臂
// 不可达 / 嵌套位置缺构造子）一个负例都没有——`pattern_match.rs` 的
// Unmatched / Unreachable / IncompleteNested 三支全靠 L07 移植时的 parity
// 套件兜底。以下各钉一条，末条是防误报的正向对照。
// 注意本层警告经 `elaboration.rs:347` 的 `format!("{error:?}")` 落到
// `Error.0.data`，故断言按 Debug 变体名（与 L10/L11/L12 同形）。

/// 负例：顶层缺构造子（Bool 少了 false 臂）必须报错，不得静默接受。
#[test]
fn test_pm_missing_branch_rejected() {
    let input = r#"
enum Bool {
    true
    false
}

def bad(x: Bool): Bool =
    match x {
        case true => false
    }
"#;
    match run(input, 0) {
        Err(e) => assert!(
            e.0.data.contains("Unmatched") || e.0.data.contains("缺少构造子"),
            "错误文案不含缺分支信息：{}", e.0.data
        ),
        Ok(out) => panic!("非穷尽 match 被静默接受：\n{out}"),
    }
}

/// 负例：臂不可达（`Vec[Nat] zero` 上 cons 臂的索引方程无解）。
///
/// 本层的语义是**不可达臂静默跳过**（与 L10/L11/L12 同款，非 L07 的
/// "报分支不可达"）：`cons` 臂不产生覆盖义务，于是 `nil` 无臂覆盖 →
/// 报 `Unmatched(<nil>)`。所以钉的是"整个 match 必须被拒"，而不是某个
/// 具体文案——被静默接受才是回归。
#[test]
fn test_pm_unreachable_arm_rejected() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def bad(v: Vec[Nat] zero): Nat =
    match v {
        case cons(x, xs) => x
    }
"#;
    match run(input, 0) {
        Err(e) => assert!(
            e.0.data.contains("Unmatched") || e.0.data.contains("niche")
                || e.0.data.contains("不可达") || e.0.data.contains("缺少构造子"),
            "错误文案不含拒因信息：{}", e.0.data
        ),
        Ok(out) => panic!("只有不可达臂的 match 被静默接受：\n{out}"),
    }
}

/// 负例：嵌套位置覆盖缺失（nil 臂 + cons(h, nil) 臂缺 cons(h, cons(..))）。
/// 这类缺口在修复前静默接受、运行期在尾部为 cons 的值上卡死。
#[test]
fn test_pm_nested_coverage_gap_rejected() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def bad(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
    }
"#;
    match run(input, 0) {
        Err(e) => assert!(e.0.data.contains("缺少构造子 cons"), "{}", e.0.data),
        Ok(out) => panic!("嵌套覆盖缺口被静默接受：\n{out}"),
    }
}

/// 正向对照（防误报）：通配臂覆盖全部 + 嵌套位置完整覆盖，两种形态都必须
/// **不报**覆盖类错误。
#[test]
fn test_pm_coverage_controls_ok() {
    let wild = r#"
enum Bool {
    true
    false
}

def ok(x: Bool): Bool =
    match x {
        case true => false
        case _ => true
    }
"#;
    run(wild, 0).unwrap_or_else(|e| panic!("通配臂被误报：{}", e.0.data));

    let nested = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def ok(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, t)) => h2
    }
"#;
    run(nested, 0).unwrap_or_else(|e| panic!("完整嵌套覆盖被误报：{}", e.0.data));
}

// --------------------------------------------------------------------------------
// 2026-09-20 跨层一致性钉子：通配臂之后的臂。
//
// L07 的 README §4（`src/L07_sum_type/README.md:264`）是这条语义的规格：
// 「通配臂之后的臂跳过（运行时永不可达，保持首匹配语义**不报错**）」，
// 且 L07/L08 各有回归钉 `test_catch_all_mixed` 断言这种程序**通过**。
//
// 本层（及 L10–L13）在 `pattern_match.rs` 的臂循环里对被遮蔽的臂推
// `Warning::Unreachable`，而本层把非空 warnings 直接变成 `Err`
// （`elaboration.rs:347`）——于是同一份源在 L07/L08 通过、在本层被拒。
// 该 `Warning::Unreachable` 是决策树时代的残留（老算法里"树从未到达的臂"
// 是另一回事，见 docs/l09l13-match-compiler-analysis-2026-09-17.md §2；
// 改成逐臂下钻后只剩"被 catch-all 遮蔽"这一种情形，而它恰是规格要求不报的）。
/// 2026-09-20 owner 口径更正：**不可达的臂应当报错**（上一轮曾按 L07
/// README:264 对齐成沉默跳过，本轮已还原为报错）。
#[test]
fn test_pm_shadowed_arm_after_catch_all_rejected() {
    let input = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def const_zero(x: Nat): Nat =
    match x {
        case n => zero
        case zero => zero
        case succ(k) => succ k
    }
"#;
        match run(input, 0) {
            Err(e) => assert!(
                e.0.data.contains("Unreachable") || e.0.data.contains("不可达"),
                "错误文案不含臂不可达信息：{}", e.0.data
            ),
            Ok(out) => panic!("通配臂之后的臂（运行时永不可达）被静默接受：\n{out}"),
        }
    }

// --------------------------------------------------------------------------------
// 2026-11-11 L07 加固移植回归钉（P2/P3/P5/深值轮/splice）。
//
// 对应 L07 `tests.rs` 同名用例的 L09 适配：本层 Error 是 `Span<String>`
// （`err.0.data`），无 decl 表（值级用例直接构造 Val），pretty 对卡住 match
// 的输出是 `(unsolved match …)`（下断言处注明）。

#[cfg(test)]
mod tests {
    use super::*;
    use crate::list::List;

    fn nat_sum() -> Val {
        Val::Sum(
            vspan(empty_span("Nat".to_string())),
            Rc::new(vec![]),
            Rc::new(vec![
                vspan(empty_span("zero".to_string())),
                vspan(empty_span("succ".to_string())),
            ]),
        )
    }

    fn zero_of(typ: &Rc<Val>) -> Val {
        Val::SumCase {
            typ: Rc::clone(typ),
            case_name: vspan(empty_span("zero".to_string())),
            datas: Rc::new(vec![]),
        }
    }

    fn succ_of(typ: &Rc<Val>, prev: Val) -> Val {
        Val::SumCase {
            typ: Rc::clone(typ),
            case_name: vspan(empty_span("succ".to_string())),
            datas: Rc::new(vec![(vspan(empty_span("x".to_string())), Rc::new(prev), Icit::Expl)]),
        }
    }

    fn chain(nat: &Rc<Val>, n: usize) -> Val {
        let mut v = zero_of(nat);
        for _ in 0..n {
            v = succ_of(nat, v);
        }
        v
    }

    /// README §7.6 回归钉（L07 `deep_value_iterative_under_default_stack`
    /// 的 L09 适配）：深值（`succ^N` 链）上的 occurs 守卫、结构相等、quote 与
    /// pretty 全部迭代化/定深——**默认测试栈**（约 2 MB）下不再爆栈。
    /// 深链的 Rc/Drop 自身是深递归（测试基建的坑，非被测代码），故
    /// ManuallyDrop 泄漏给进程。
    #[test]
    fn deep_value_iterative_under_default_stack() {
        const N_OCCURS: usize = 100_000;
        const N_EQ: usize = 4_000;

        let nat = Rc::new(nat_sum());
        // ① occurs 守卫：10 万层深链（无预算，纯遍历）
        let deep = std::mem::ManuallyDrop::new(chain(&nat, N_OCCURS));
        assert!(
            !val_mentions_lvl(&deep, Lvl(1)),
            "深链不含 Lvl(1)（且旧递归版此处爆栈）"
        );
        // 链中段嵌 Rigid(7)：命中为 true、别处为 false
        let mut with_rigid = Val::vvar(Lvl(7));
        for _ in 0..N_OCCURS / 2 {
            with_rigid = succ_of(&nat, with_rigid);
        }
        let with_rigid = std::mem::ManuallyDrop::new(with_rigid);
        assert!(val_mentions_lvl(&with_rigid, Lvl(7)));
        assert!(!val_mentions_lvl(&with_rigid, Lvl(1)));

        // ② 结构相等：预算内同构链判等；超预算有界降级为 false——都不爆栈
        let a = std::mem::ManuallyDrop::new(chain(&nat, N_EQ));
        let b = std::mem::ManuallyDrop::new(chain(&nat, N_EQ));
        assert!(struct_eq::val_eq(&a, &b), "同构深链应判等（预算内）");
        let c = std::mem::ManuallyDrop::new(chain(&nat, N_OCCURS));
        assert!(
            !struct_eq::val_eq(&deep, &c),
            "超预算应有界降级（false），不爆栈"
        );

        // ③ quote（曾是仅剩的递归路径）+ pretty（定深截断）：10 万层深链在
        //    默认测试栈下不爆栈。返回的 Tm 是 Box 链，ManuallyDrop 泄漏。
        let infer = Infer::new();
        let quoted =
            std::mem::ManuallyDrop::new(infer.quote(Lvl(0), chain(&nat, N_OCCURS)));
        let mut depth = 1usize;
        let mut cur: &Tm = &quoted;
        loop {
            match cur {
                Tm::SumCase { datas, .. } if !datas.is_empty() => {
                    depth += 1;
                    cur = &datas[0].1;
                }
                _ => break,
            }
        }
        assert_eq!(depth, N_OCCURS + 1, "quote 应逐层产出 SumCase");
        let shown = pretty::pretty_tm(0, List::new(), &quoted);
        assert!(shown.contains('…'), "深值显示应定深截断");
    }

    /// P5 回归钉（L07 `cross_meta_cycle_force_is_bounded` 的 L09 适配）：
    /// 跨 meta 环（m1 := ?m2、m2 := ?m1）的 force 必须**有界终止**——环守卫
    /// 在展开栈上发现重复 meta 即返回卡住的 Flex，不再靠 fuel 烧尽兜底。
    #[test]
    fn cross_meta_cycle_force_is_bounded() {
        let mut infer = Infer::new();
        let ty = Val::U(0);
        let m1 = infer.new_meta(ty.clone());
        let m2 = infer.new_meta(ty.clone());
        infer.meta[m1 as usize] = MetaEntry::Solved(Val::Flex(MetaVar(m2), List::new()), ty.clone());
        infer.meta[m2 as usize] = MetaEntry::Solved(Val::Flex(MetaVar(m1), List::new()), ty);
        infer.unify_fuel.set(64);
        let out = infer.force(Val::Flex(MetaVar(m1), List::new()));
        assert!(
            matches!(out, Val::Flex(..)),
            "环应降级为卡住的 Flex，got {out:?}"
        );
        assert!(
            infer.unify_fuel.get() > 0,
            "环守卫应避免烧光 fuel（旧行为靠耗尽兜底）：left {}",
            infer.unify_fuel.get()
        );
        assert!(
            infer.meta_expanding.borrow().is_empty(),
            "展开栈应在返回时清空"
        );
    }

    /// P3 分档对照（L07 同名用例的值级适配）：**结构矛盾** = Absurd，
    /// **判不出来**（中性头形态无法对齐）= Undecided。两档不能混。
    #[test]
    fn test_unify_kind_separates_absurd_from_undecided() {
        let mut infer = Infer::new();
        let cxt = Cxt::new();
        let nat = Rc::new(nat_sum());
        let zero = zero_of(&nat);
        let one = succ_of(&nat, zero.clone());

        // 结构矛盾：zero ≐ succ zero 无解
        infer.reset_unify_kind();
        assert!(
            infer.unify(Lvl(0), &cxt, zero, one, None).is_err(),
            "zero ≐ succ zero 必须失败"
        );
        assert_eq!(
            infer.unify_kind(),
            UnifyKind::Absurd,
            "构造子矛盾应记为 Absurd（分支不可达）"
        );

        // 判不出来：同一中性头的 spine 长度失配——既不相等也不是矛盾
        infer.reset_unify_kind();
        let bare = Val::Rigid(Lvl(3), List::new());
        let applied = Val::Rigid(Lvl(3), List::new().prepend((Val::U(0), Icit::Expl)));
        assert!(infer.unify(Lvl(0), &cxt, bare, applied, None).is_err());
        assert_eq!(
            infer.unify_kind(),
            UnifyKind::Undecided,
            "spine 长度失配应记为 Undecided（不是矛盾）"
        );
    }

    /// 回归（L07 `test_stuck_match_splice` 的 L09 适配）：卡住 match 被应用
    /// 时不再 panic——实参进 pending，分支选中后在值层应用。
    #[test]
    fn test_stuck_match_splice() {
        let out = run(
            r#"
enum Nat {
    zero
    succ(x: Nat)
}

def f(n: Nat): Nat -> Nat =
    match n {
        case zero => succ
        case succ(k) => succ
    }

println (f zero)
println ((f zero) zero)
println ((f (succ zero)) zero)
"#,
            0,
        )
        .expect("卡住 match 的应用（splice）不得 panic");
        assert!(
            out.contains("Nat::succ(Nat::zero)"),
            "splice 后应归约出 succ zero：{out}"
        );
    }

    /// 回归（L07 `test_stuck_match_applied_with_outer_binder` 的 L09 适配）：
    /// 实参引用比捕获 env 更外层的 binder 时，实参必须在**值层**累积
    /// （pending）、分支选中后再应用——项层 splice 会越界/错位。
    /// 本层 pretty 对卡住 match 的输出是 `(unsolved match m)`。
    #[test]
    fn test_stuck_match_applied_with_outer_binder() {
        let out = run(
            r#"
enum Nat {
    zero
    succ(x: Nat)
}

def pick(n: Nat): Nat -> Nat =
    match n {
        case zero => k => k
        case succ(k) => k => succ k
    }

def test(m: Nat, j: Nat): Nat = (pick m) j

println test
"#,
            0,
        )
        .expect("外层 binder 实参的 splice 不得 panic");
        assert!(out.contains("unsolved match m"), "{out}");
        assert!(out.contains(") j"), "实参应在分支外层应用：{out}");
        assert!(!out.contains("zero => j"), "实参不得 quote 进分支体：{out}");
    }

    /// S1 回归钉（L07 `test_struct_eq_compares_match_pending_values` 的
    /// L09 适配）：`struct_eq` 的卡住 match 臂必须比较 pending **值**，不能
    /// 只比长度/icit；漏比会让「scrutinee 是另一个 pending 不同的卡住 match」
    /// 的两份 match 被判等，refl 可证明两个闭实例化结果不同的函数相等。
    #[test]
    fn struct_eq_compares_match_pending_values() {
        let err = run(
            r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def pfun(n: Nat): Nat -> Nat =
    match n {
        case zero => k => k
        case succ(j) => k => k
    }

def f(x: Nat): Nat =
    match (pfun x zero) {
        case zero => zero
        case succ(m) => succ m
    }

def g(x: Nat): Nat =
    match (pfun x (succ zero)) {
        case zero => zero
        case succ(m) => succ m
    }

def bad : Eq[Nat -> Nat] f g =
    refl f
"#,
            0,
        )
        .expect_err("pending 不同的两份卡住 match 不得判等（否则可证 False）");
        assert!(err.0.data.contains("can't unify"), "err: {}", err.0.data);
    }

    /// P2 回归钉（L07 `test_stuck_match_equation_bounded` 的 L09 适配）：
    /// 卡住 match 比较的结构快路径失效后，逐分支重求值受 `MATCH_CMP_BUDGET`
    /// 封顶——耗尽按「无法判定为相等」失败（Undecided），不是矛盾；两个递归
    /// def 的卡住索引方程互比必须在有界时间内结束（未加预算时为分钟级）。
    #[test]
    fn test_stuck_match_equation_bounded() {
        // ① 值级：预算为 0 时 Match/Match 慢路径立刻判 Undecided
        let mut infer = Infer::new();
        let cxt = Cxt::new();
        let cases = Rc::new(vec![(
            PatternDetail::Any(empty_span(())),
            Tm::Var(Ix(0)),
        )]);
        let scrut = Val::Rigid(Lvl(5), List::new());
        let m1 = Val::Match(
            Rc::new(scrut.clone()),
            List::new(),
            Rc::clone(&cases),
            Rc::new(vec![]),
        );
        // 捕获 env 不同 ⇒ 结构快路径失效，进入预算计数的慢路径
        let m2 = Val::Match(
            Rc::new(scrut),
            List::new().prepend(Val::U(0)),
            cases,
            Rc::new(vec![]),
        );
        infer.reset_match_cmp_budget();
        infer.match_cmp_budget.set(0);
        assert!(
            infer.unify(Lvl(0), &cxt, m1, m2, None).is_err(),
            "预算耗尽应按失败处理"
        );
        assert_eq!(
            infer.unify_kind(),
            UnifyKind::Undecided,
            "预算耗尽应记为无法判定（不是矛盾）"
        );

        // ② 源级：两个递归 def 的卡住索引方程互比——有界时间
        let t0 = std::time::Instant::now();
        let _ = run(
            r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def f(x: Nat, y: Nat, e: Eq[Nat] (add x zero) (add y zero)): Nat =
    match e {
        case refl(a) => a
    }
"#,
            0,
        );
        let dt = t0.elapsed();
        assert!(
            dt < std::time::Duration::from_secs(30),
            "耗时 {dt:?}：卡住 match 比较的深度预算失效（修复前为分钟级）"
        );
    }
}
