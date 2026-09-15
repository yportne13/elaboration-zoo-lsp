//! L07：和类型（enum，带类型参数与索引）+ 依赖模式匹配。
//!
//! 相对 L06 新增：`enum` 声明（参数 `[A]` / 索引 `(len: Nat)`、构造子字段、
//! `-> ret` 索引返回）、`match`（编译为 (模式, 分支体) 列表 + 运行时首匹配）、
//! 索引精化（特化解入 `Subst` 显式替换 + `Val::VSub` 包裹，`force` 的 frcs
//! 臂在读点把 σ 推进值结构——dpm-nbe 对齐，见 README §1.2 与
//! `docs/l07-dpm-refactor-design.md`）、卡住的 match 作为中性值参与
//! unification / quote / rename / 应用（splice）。
//!
//! 设计说明见本目录 README.md。

use std::{
    cell::RefCell,
    collections::HashMap,
    ops::{Add, Sub},
    rc::Rc,
    sync::{
        atomic::{AtomicBool, Ordering},
        LazyLock,
    },
};

/// `L07_LOOP` 调试开关（进程级，只读一次；热路径零 env 访问）。
pub(crate) static LOOP_DEBUG: LazyLock<AtomicBool> =
    LazyLock::new(|| AtomicBool::new(std::env::var("L07_LOOP").is_ok()));


use cxt::{Cxt, DeclEntry, Decls};
use pretty::pretty_tm;
use syntax::{Pruning, close_ty};

use crate::{list::List, parser_lib::Span};
use smol_str::SmolStr;

mod cxt;
mod struct_eq;
mod elaboration;
pub(crate) mod parser;
mod pattern_match;
mod pretty;
mod syntax;
mod unification;
pub(crate) mod bump_spine_iter;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MetaVar(u32);

#[derive(Debug, Clone)]
pub enum MetaEntry {
    Solved(Val, VTy),
    Unsolved(VTy),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ix(u32);

#[derive(Debug, Clone)]
pub enum DeclTm {
    Def,
    Println(Tm),
    Enum,
}

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Ix),
    /// 全局引用（def / enum / 构造子），求值时查 decl 表。
    Decl(SmolStr),
    /// `x.field` 投影。
    Obj(Box<Tm>, Span<String>),
    Lam(Span<String>, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U,
    Pi(Span<String>, Icit, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    /// 内建函数体标记（携带名字：求值时卡成 `Val::Prim(name, env_spine)`）。
    Prim(SmolStr),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 值的类型, icit)，
    /// 声明处值项即参数自身；实例化（`Vec[Nat] 3`）后值槽携带当前实参。
    Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Val::Sum`，
    /// datas = 构造子自身绑定器的值（隐式在前，声明序）。
    SumCase {
        typ: Box<Tm>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Tm, Icit)>,
    },
    /// 已编译的 match：分支体是检查过的项，运行时按模式首匹配。
    Match(Box<Tm>, Vec<(PatternDetail, Tm)>),
}

/// 编译后的模式。bind_count = 该模式在运行时消耗的 env 槽数：
/// Any / Bind 各占 1 槽（整个 head 值），Con 占 1 槽（head 自身）加各子模式槽数。
#[derive(Clone, Debug, PartialEq)]
pub enum PatternDetail {
    Any(Span<()>),
    Bind(Span<String>),
    Con(Span<String>, Vec<PatternDetail>),
}

impl PatternDetail {
    pub fn bind_count(&self) -> u32 {
        match self {
            PatternDetail::Any(_) => 1,
            PatternDetail::Bind(_) => 1,
            PatternDetail::Con(_, subs) => 1 + subs.iter().map(|s| s.bind_count()).sum::<u32>(),
        }
    }
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct Lvl(pub u32);

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
        write!(f, "Closure(..{}, {:?})", self.0.len(), self.1)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    /// 未展开的全局引用（递归定义的占位 / simplify 后的 decl 表）。
    Decl(SmolStr, Spine),
    /// 卡住的投影（被投影者还不是构造子值 / Sum 类型）。
    Obj(Box<Val>, Span<String>, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Box<VTy>, Closure),
    U,
    LiteralType,
    LiteralIntro(Span<String>),
    /// 卡住的内建应用：名字 + 已收实参 spine（头 = 最后应用的实参）。
    /// 全部实参字面量时在 `force` 归约（目前仅 string_concat），否则保持
    /// 中性参与 unify / quote / rename（名字 + 实参不可丢——丢实参的单元
    /// `Prim` 会把 `x ++ y ≡ x ++ z` 判成相等）。
    Prim(SmolStr, Spine),
    Sum(
        Span<String>,
        Vec<(Span<String>, Rc<Val>, Rc<VTy>, Icit)>, // (参数名, 实参值, 实参的类型, icit)
        Vec<Span<String>>,
    ),
    SumCase {
        typ: Rc<Val>,
        case_name: Span<String>,
        datas: Vec<(Span<String>, Rc<Val>, Icit)>,
    },
    /// 卡住的 match：scrutinee 不是构造子值，等待 scrutinee 归约后再选分支。
    /// `pending` = 卡住期间累积的应用实参（值层保存，分支选中后在值层应用
    /// ——项层 splice 把实参 quote 进分支体时，实参的自由变量会引用到
    /// 错误的上下文，见 `v_app` 的 Match 臂）。
    Match(Box<Val>, Env, Vec<(PatternDetail, Tm)>, Vec<(Val, Icit)>),
    /// 显式替换下的值（模式精化，dpm-nbe `VSub`）：特化解不改写既有值，
    /// 只把解包在外面；`force` 在读点把 σ 推进值的结构（`frcs`，对齐
    /// dpm-nbe 的 `frcS`）。不变式：`force` 的返回值顶层不会是 VSub。
    VSub(Box<Val>, Rc<Subst>),
}

type VTy = Val;

/// 模式特化的解：层级 → 值 的**持久化单链**（dpm-nbe 的 explicit
/// substitution；链头 = 最新的解）。仅由模式编译器经 `Subst::extend` /
/// 特化合一的 `SpecSolve::acc` 构建；`Rc` 共享让臂边界回滚 = 指针赋值、
/// `Val::VSub` 包裹 = O(1)。
///
/// 表示选型（性能评审定稿）：**写入 O(1) cons、读取沿链扫描**，不做
/// "写时整表重建 + 逐条包裹"——那会把 n 条解变成 O(n³/6) 次深拷贝分配
/// （深嵌套模式实测 2.5×@depth40 回归，已废弃的 FxHashMap 写时包裹版）。
/// 与旧 `pm_defs` 事实表的对应：`extend` ≙ `pm_solve` + push（链头即
/// 最新，查询沿链首个命中 ≙ `rev().find` 取最新），`lookup` ≙ force 读点
/// 的查表展开——区别在于解只对**被包裹过的值**可见（读点显式），不再是
/// 全局查找表。
#[derive(Debug, Clone, Default)]
pub struct Subst {
    head: Option<Rc<SubEntry>>,
}

#[derive(Debug)]
struct SubEntry {
    lvl: Lvl,
    /// 解的原始值。不预先包裹"更新的解"——读取时 `lookup` 把整条 σ 包在
    /// 外面（见其文档），由 force 在读点一次性推开。
    val: Val,
    next: Option<Rc<SubEntry>>,
}

impl Subst {
    pub(crate) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配零 fuel）；引用时把整条 σ 包在解值外（解值不含
    /// x 自身——occurs 守卫，也不含更旧解的 bare 引用——solve 存值已
    /// force、头部精化值已 wrap，旧条目对它是恒等；比该条目更新的解恰好
    /// 借此对解值生效），由 force 在读点推开。未命中 None。
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

    /// 未映射即 fresh rigid（dpm-nbe `lookupSub` 的恒等延拓）。
    pub(crate) fn lookup(self: &Rc<Self>, x: Lvl) -> Val {
        self.lookup_hit(x).unwrap_or_else(|| Val::vvar(x))
    }

    /// 解值的浅结构是否引用 σ 的某个已解层级。含闭包 **env 槽**（它们是
    /// 值，读点会流出）与 Match 的 scrutinee/captured env/pending；不含
    /// 闭包体 / Match 分支体（Tm，求值时才经 env 读到槽值）。VSub 保守记
    /// 为引用（已包过 σ 的值再包一层无害）。误报只多一次包裹，漏报才会
    /// 丢精化——扫描口径宁宽勿窄。
    fn mentions_level(v: &Val, sub: &Subst) -> bool {
        fn env_slots(env: &Env, sub: &Subst) -> bool {
            env.iter().any(|v| mentions_level(v, sub))
        }
        fn mentions_level(v: &Val, sub: &Subst) -> bool {
            match v {
                Val::Rigid(y, sp) => sub.has(*y) || sp.iter().any(|(u, _)| mentions_level(u, sub)),
                Val::Flex(_, sp) | Val::Decl(_, sp) | Val::Prim(_, sp) => {
                    sp.iter().any(|(u, _)| mentions_level(u, sub))
                }
                Val::Obj(o, _, sp) => mentions_level(o, sub) || sp.iter().any(|(u, _)| mentions_level(u, sub)),
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
                Val::U | Val::LiteralType | Val::LiteralIntro(_) => false,
            }
        }
        mentions_level(v, sub)
    }

    /// x 是否已有解（旧 `pm_def(x).is_none()` 的否定形式）。
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

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新 ≙ 旧 `pm_def`
    /// 的 `rev().find` 取最新；同键旧条目留在链上但永不命中）。
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
    /// （先被查到 = 覆盖同键）——对齐旧 `pm_def` 的"取最新"语义；dpm-nbe
    /// 的左偏 union 在其无冲突场景下与此等价。
    pub(crate) fn compose(outer: &Rc<Subst>, inner: &Rc<Subst>) -> Rc<Subst> {
        fn cons_all(
            entry: &Option<Rc<SubEntry>>,
            onto: Option<Rc<SubEntry>>,
        ) -> Option<Rc<SubEntry>> {
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

/// η 展开与 frcs 读点共用的可应用性守卫（L06 `unification::v_applicable`
/// 同款）：只有 `v_app` 能吃的形态（中性头 / Decl / 卡住投影 / 卡住内建 /
/// 卡住 match / VSub）允许应用。字面量/U/Π/Sum/SumCase 与实参相遇时无从
/// 应用——不加守卫会命中 `v_app` 的 `impossible apply` panic（L06 曾由
/// `string_to_global_type` 把 def 函数值当"动态类型"送进 unify 而踩中；
/// L07 的 st2g 只返回登记**类型**，该触发路径关闭，本守卫为同型加固）。
pub(crate) fn v_applicable(v: &Val) -> bool {
    matches!(
        v,
        Val::Flex(..)
            | Val::Rigid(..)
            | Val::Decl(..)
            | Val::Obj(..)
            | Val::Prim(..)
            | Val::Match(..)
            | Val::VSub(..)
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

/// 展开燃料：每个展开步骤消耗 1，耗尽即停止（防环）。force 的各展开臂
/// 与 frcs 的 lookup 命中点共用。
fn burn(cell: &std::cell::Cell<u32>) -> bool {
    let f = cell.get();
    if f == 0 {
        return false;
    }
    cell.set(f - 1);
    true
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
    if x.0 >= l.0 {
        // 语义上不可达：值里出现了超出 quote 层级的 rigid。debug 构建下断言
        // 捕捉，release 保守降级到 0（只出现在显示路径上时会可见）。
        debug_assert!(false, "lvl2ix: {x:?} out of range at {l:?}");
        Ix(0)
    } else {
        Ix(l.0 - x.0 - 1)
    }
}

#[derive(Debug)]
pub(crate) struct UnifyError;

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
/// rename / project）经此取值。
pub(crate) fn rc_take(v: Rc<Val>) -> Val {
    Rc::try_unwrap(v).unwrap_or_else(|v| (*v).clone())
}

#[derive(Debug)]
pub struct Error(String);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

pub struct Infer {
    meta: Vec<MetaEntry>,
    /// 可变全局表（create_global / change_mutable / get_global 族读写；
    /// L06 同款：单线程 RefCell。参考版随 `Infer` 每次调用新建）。
    pub(crate) mutable_map: RefCell<HashMap<SmolStr, Val>>,
    /// unify 递归深度防护（L13 同款做法）。每次外部配置（unify_catch /
    /// pattern 编译入口）充值；递归中递减，归零即 Err——防索引槽互相嵌入
    /// 的构造子值比较（SuccCase 的 typ 含索引、索引又是 SuccCase）无限递归。
    unify_fuel: std::cell::Cell<u32>,
}

const UNIFY_FUEL: u32 = 4096;

impl Infer {
    pub fn new() -> Self {
        Self {
            meta: vec![],
            mutable_map: RefCell::new(HashMap::new()),
            unify_fuel: std::cell::Cell::new(UNIFY_FUEL),
        }
    }

    fn new_meta(&mut self, a: VTy) -> MetaVar {
        self.meta.push(MetaEntry::Unsolved(a));
        MetaVar(self.meta.len() as u32 - 1)
    }

    /// 生成一个元变量：类型按当前上下文封口，项形如 `?m <pruning>`（只取可见参数）。
    fn fresh_meta(&mut self, decl: &Decls, cxt: &Cxt, a: VTy) -> Tm {
        let closed = self.eval(
            decl,
            &List::new(),
            close_ty(cxt.locals.clone(), self.quote(decl, cxt.lvl, a)),
        );
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(m)), cxt.pruning.clone())
    }

    fn lookup_meta(&self, m: MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }

    /// 元变量快照 / 回滚：模式编译的可达性探测在"临时状态"里做合一，
    /// 探测期间解出的 meta 全部丢弃。
    pub(crate) fn meta_snapshot(&self) -> Vec<MetaEntry> {
        self.meta.clone()
    }

    pub(crate) fn meta_restore(&mut self, snap: Vec<MetaEntry>) {
        self.meta = snap;
    }

    /// 给 unify/force 的共享 fuel 池充值（外层合一入口调用）。
    pub(crate) fn meta_refuel(&self) {
        self.unify_fuel.set(UNIFY_FUEL);
    }

    /// fuel 是否已耗尽（本编译单元的共享池）。错误诊断用：特化方程失败
    /// 时区分"结构冲突（真 absurd）"与"预算耗尽（假 absurd）"。
    pub(crate) fn fuel_exhausted(&self) -> bool {
        self.unify_fuel.get() == 0
    }

    /// 合一器**参数视角**的 WHNF：与 `force` 相同，但不做 Match 重选。
    /// `invert` / `prune_vflex` 关心的是"元变量被应用在哪些**槽位**上"
    /// ——槽位引用（`Rigid(x)`）本身就是作用域事实，分支内的精化等式
    /// （x := zero）不改变槽位的存在；在它们身上展开反而会把可逆 spine
    /// 变成含构造子值的不可逆 spine。
    pub(crate) fn force_arg(&self, decl: &Decls, t: Val) -> Val {
        // 精化包裹的槽位：逐层解包看裸形态（subst_cxt 可叠加——嵌套 match
        // 的上下文被外层臂与内层臂各包一次）。解到底仍是 bare rigid ⇒ 槽位
        // 保留（对齐旧"pm_defs 不参与 invert"的行为——旧版此处读到的正是
        // 未展开的 Rigid(x)）；其余形态全量 force 推开。
        let mut cur = &t;
        while let Val::VSub(v, _) = cur {
            cur = v;
        }
        match cur {
            Val::Rigid(x, sp) if sp.is_empty() => Val::Rigid(*x, sp.clone()),
            Val::Rigid(..) | Val::Match(..) => t,
            _ => self.force(decl, t),
        }
    }

    /// 把值更新到 metacontext / 模式特化的当前状态：元变量探测 + decl 表
    /// 展开 + 卡住投影的再投影 + 模式精化展开。深度防护：meta 解链可能
    /// 形成间接环（solve 无跨 meta occurs check），展开会无限递归——只在
    /// **展开递归**时消耗 fuel（高频直通路径不消耗），fuel 耗尽时停止
    /// 展开，把值当作未解处理。
    pub fn force(&self, decl: &Decls, t: Val) -> Val {
        match t {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved, _) if burn(&self.unify_fuel) => {
                    if LOOP_DEBUG.load(Ordering::Relaxed) && self.unify_fuel.get() < 2200 {
                        eprintln!("  force-expand meta {} (fuel {})", m.0, self.unify_fuel.get());
                    }
                    self.force(decl, self.v_app_sp(decl, t_solved.clone(), sp))
                }
                _ => Val::Flex(m, sp),
            },
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1），对齐旧 pm_defs 时代
            // "force(Rigid) 查表展开烧 1"的燃烧剖面；包裹/组合的机械开销
            // 免费。fuel 耗尽的降级点也在 lookup 命中处（返回裸 rigid）。
            Val::VSub(v, sub) => self.frcs(decl, &sub, *v),
            // 卡住的 match：scrutinee 是在 match 创建之后才被特化/解出时，
            // 这里重新尝试选分支。没有这一步，精化无法传播进"卡住 match
            // 里面"（期望类型 `Eq (add a zero) a` 的 `add a zero` 就是它）。
            Val::Match(s, env, cases, pending) => {
                let s2 = self.force(decl, (*s).clone());
                if let Val::SumCase { .. } = &s2 {
                    if burn(&self.unify_fuel) {
                        if let Some((tm, env2)) =
                            Compiler::eval_aux(self, decl, &s2, &env, &cases)
                        {
                            // 分支选中：先在值层应用卡住期累积的实参（值无需
                            // quote，作用域天然正确；项层 splice 会把实参的
                            // 自由变量引到错误上下文）。
                            let mut v = self.eval(decl, &env2, tm);
                            for (u, i) in pending.iter().cloned() {
                                v = self.v_app(decl, v, u, i);
                            }
                            return self.force(decl, v);
                        }
                    }
                }
                Val::Match(s, env, cases, pending)
            }
            Val::Decl(name, sp) => match decl.get(&name) {
                // unfold 前先检查自引用占位（递归 def 的占位值与 simpl_decl
                // 的中性条目都是 `Decl(自身名, [])`）：v_app_sp 后仍是原值，
                // unfold 永无进展，只会自旋烧光 fuel 池。直接按中性返回。
                Some(e)
                    if !matches!(&e.val, Val::Decl(n2, s2) if *n2 == *name && s2.is_empty())
                        && burn(&self.unify_fuel) =>
                {
                    self.force(decl, self.v_app_sp(decl, e.val.clone(), sp))
                }
                None => Val::Decl(name, sp),
                _ => Val::Decl(name, sp),
            },
            // 卡住的内建：实参按自然序（应用序）交给对应 builtin 体归约
            // （L06 builtin 注册表的全部函数体）；元数不足 / 实参不合 /
            // 缺名时保持卡住。名字 + 实参 spine 由 eval(Tm::Prim) 构造。
            // 实参先 force 再检查字面量：spine 槽可能存的是**未归约的嵌套
            // prim**（如 change_mutable 存的 `f old`、源码里的嵌套应用），
            // 不 force 则外层永远过不了字面量检查，prim 链失去可组合性
            // （与 Val::Obj 分支先 force 头部的纪律对齐）。
            Val::Prim(name, sp) => {
                if burn(&self.unify_fuel) {
                    let mut args: Vec<Val> =
                        sp.iter().map(|(v, _)| self.force(decl, v.clone())).collect();
                    args.reverse(); // spine 头 = 最后应用 → 自然序
                    if let Some(v) = self.prim_reduce(decl, &name, &args) {
                        return self.force(decl, v);
                    }
                }
                Val::Prim(name, sp)
            }
            Val::Obj(v, name, sp) => {
                let v = self.force(decl, *v);
                match project(&v, &name) {
                    Some(p) if burn(&self.unify_fuel) => {
                        self.force(decl, self.v_app_sp(decl, p, sp))
                    }
                    _ => Val::Obj(Box::new(v), name, sp),
                }
            }
            t => t,
        }
    }

    /// 把替换 `σ` 推进值 `v` 的结构（dpm-nbe `frcS`）。与 `force` 的分工：
    /// σ 是本次精化的局部解，只作用于**被包裹过**的值；头部与 scrutinee
    /// 推进、闭包 env 逐槽包裹（惰性，不进入闭包体重求值）；spine 槽与
    /// Sum/SumCase 槽**只包裹不物化**（见下各行内注释——槽位引用是作用域
    /// 事实，物化会破坏后续 solve 的 invert）。
    fn frcs(&self, decl: &Decls, sub: &Rc<Subst>, v: Val) -> Val {
        if sub.is_empty() {
            return self.force(decl, v);
        }
        match v {
            // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
            Val::VSub(v2, sub2) => {
                let composed = Subst::compose(sub, &sub2);
                self.frcs(decl, &composed, *v2)
            }
            // 被解变量的读点：lookup 命中（真正的精化传播）烧 1 fuel——
            // 对齐旧 pm_defs 的 force(Rigid) 查表展开烧 1 剖面；fuel 耗尽
            // 按未解处理（返回裸 rigid，有界降级，防闭环无限推进，也断了
            // v_app ↔ force 在 fuel=0 角落的互递归）。未命中零成本直通。
            // 解出值按应用序（spine 尾到头）经 v_app 拼接（λ ⇒ β；Match ⇒
            // pending；中性头 ⇒ spine）——对应 dpm-nbe
            // `napp (lookupSub sb v) (frcS sb sp)`。解值带实参但头不可应用
            // （对非函数解变量做应用的 ill-typed 形态）时保持卡住，不进
            // v_app（η 臂的 v_applicable 守卫同款加固）。
            Val::Rigid(x, sp) => {
                let mut head = match sub.lookup_hit(x) {
                    Some(hit) => {
                        if !burn(&self.unify_fuel) {
                            return Val::Rigid(x, sp);
                        }
                        self.force(decl, hit)
                    }
                    None => Val::vvar(x),
                };
                if !sp.is_empty() && !v_applicable(&head) {
                    return Val::Rigid(x, sp);
                }
                let args: Vec<(Val, Icit)> = sp.iter().cloned().collect();
                for (u, i) in args.into_iter().rev() {
                    head = self.v_app(decl, head, wrap_sub(sub, u), i);
                }
                head
            }
            // 中性头的 spine 槽只**包裹**不推进——槽位引用是作用域事实，
            // 物化会破坏后续 solve 的 invert（与 force_arg 的分工同一理由；
            // 旧 force 也从不触碰 spine 槽）。包裹后交回 force 重走既有臂
            // （meta 解 / decl 展开 / prim 归约 / 投影），保持"σ 之下的值
            // force 到同一 WHNF 形态"的旧语义。
            Val::Flex(m, sp) => self.force(decl, Val::Flex(m, self.wrap_sp(sub, sp))),
            Val::Decl(name, sp) => self.force(decl, Val::Decl(name, self.wrap_sp(sub, sp))),
            Val::Prim(name, sp) => self.force(decl, Val::Prim(name, self.wrap_sp(sub, sp))),
            Val::Obj(o, name, sp) => self.force(decl, Val::Obj(
                Box::new(self.frcs(decl, sub, *o)),
                name,
                self.wrap_sp(sub, sp),
            )),
            // 闭包 env 逐槽包裹（dpm-nbe `subst sb cl` 的惰性形态）
            Val::Lam(x, i, cl) => Val::Lam(x, i, Closure(self.frcs_env(sub, &cl.0), cl.1)),
            Val::Pi(x, i, a, cl) => Val::Pi(
                x,
                i,
                Box::new(self.frcs(decl, sub, *a)),
                Closure(self.frcs_env(sub, &cl.0), cl.1),
            ),
            // Sum/SumCase 的槽位同样只包裹（旧 force 不进入这些结构）
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
            // scrutinee **推进**（重选分支需要解出的构造子值）；捕获 env 与
            // pending 只包裹。交回 force：scrutinee 若已是构造子值，force 的
            // Match 臂按同一纪律重选分支
            Val::Match(s, env, cases, pending) => self.force(
                decl,
                Val::Match(
                    Box::new(self.frcs(decl, sub, *s)),
                    self.frcs_env(sub, &env),
                    cases,
                    pending
                        .into_iter()
                        .map(|(u, i)| (wrap_sub(sub, u), i))
                        .collect(),
                ),
            ),
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

    /// 卡住内建的归约体（L06 builtin 注册表的逐句移植，force 时触发）。
    /// `args` 自然序（最先应用在前）；元数 / 字面量检查与 L06 的
    /// `PrimFunc` 逐条对应，不满足即 None 保持卡住。文件族失败 panic
    /// （两版一致）。
    fn prim_reduce(&self, decl: &Decls, name: &str, args: &[Val]) -> Option<Val> {
        let lit = |v: &Val| match v {
            Val::LiteralIntro(s) => Some(s.data.clone()),
            _ => None,
        };
        match name {
            "string_concat" => {
                if args.len() < 2 {
                    return None;
                }
                match (&args[0], &args[1]) {
                    (Val::LiteralIntro(a), Val::LiteralIntro(b)) => Some(Val::LiteralIntro(
                        a.clone().map(|x| format!("{x}{}", b.data)),
                    )),
                    _ => None,
                }
            }
            "str_eq" => {
                if args.len() < 2 {
                    return None;
                }
                match (lit(&args[0]), lit(&args[1])) {
                    (Some(a), Some(b)) => {
                        let s = if a == b { "true" } else { "false" };
                        Some(Val::LiteralIntro(empty_span(s.to_string())))
                    }
                    _ => None,
                }
            }
            "str_indent2" => {
                if args.is_empty() {
                    return None;
                }
                match lit(&args[0]) {
                    Some(s) => Some(Val::LiteralIntro(empty_span(s.replace('\n', "\n  ")))),
                    None => None,
                }
            }
            "report_check_issue" => {
                if args.len() < 4 {
                    return None;
                }
                let get = |i: usize| lit(&args[i]).unwrap_or_default();
                let (code, module, signal, message) = (get(0), get(1), get(2), get(3));
                if code.is_empty() || module.is_empty() {
                    return Some(Val::U);
                }
                let line = format!("{}|{}|{}|{}", code, module, signal, message);
                let mut map = self.mutable_map.borrow_mut();
                let existing = match map.get("CheckIssues") {
                    Some(v) => lit(v).unwrap_or_default(),
                    None => String::new(),
                };
                if !existing.split('\n').any(|l| l == line) {
                    let next = if existing.is_empty() {
                        line
                    } else {
                        format!("{}\n{}", existing, line)
                    };
                    map.insert("CheckIssues".into(), Val::LiteralIntro(empty_span(next)));
                }
                Some(Val::U)
            }
            "string_to_global_type" => {
                if args.is_empty() {
                    return None;
                }
                match lit(&args[0]) {
                    // 登记名给登记**类型**（类型即值）；未登记名返回以其自身
                    // 名字的卡住 Decl——动态类型的逃逸舱口（L06 同款），后续
                    // unify 里按宽松臂处理
                    Some(a) => Some(match decl.get(a.as_str()) {
                        Some(e) => e.ty.clone(),
                        None => Val::Decl(SmolStr::new(a), List::new()),
                    }),
                    None => None,
                }
            }
            "create_global" => {
                if args.len() < 2 {
                    return None;
                }
                match lit(&args[0]) {
                    Some(a) => {
                        self.mutable_map.borrow_mut().insert(SmolStr::new(a), args[1].clone());
                        Some(Val::U)
                    }
                    None => None,
                }
            }
            "change_mutable" => {
                if args.len() < 2 {
                    return None;
                }
                match lit(&args[0]) {
                    Some(a) => {
                        // 先取旧值并结束借用，再求值 f——f 的求值可能再触发
                        // 任何 prim（get_global 等），持有借用会 BorrowError
                        let old = self.mutable_map.borrow().get(a.as_str()).cloned();
                        if let Some(old) = old {
                            let new = self.v_app(decl, args[1].clone(), old, Icit::Expl);
                            self.mutable_map.borrow_mut().insert(SmolStr::new(a), new);
                        }
                        Some(Val::U)
                    }
                    None => None,
                }
            }
            "get_global" => {
                if args.is_empty() {
                    return None;
                }
                // 缺名保持卡住（None），不 panic
                match lit(&args[0]) {
                    Some(a) => self.mutable_map.borrow().get(SmolStr::new(a).as_str()).cloned(),
                    None => None,
                }
            }
            "get_global_default" => {
                if args.len() < 2 {
                    return None;
                }
                match lit(&args[0]) {
                    Some(a) => Some(
                        self.mutable_map
                            .borrow()
                            .get(SmolStr::new(a).as_str())
                            .cloned()
                            .unwrap_or_else(|| args[1].clone()),
                    ),
                    None => None,
                }
            }
            "change_mutable_default" => {
                if args.len() < 3 {
                    return None;
                }
                match lit(&args[0]) {
                    Some(a) => {
                        let existing = self.mutable_map.borrow().get(a.as_str()).cloned();
                        match existing {
                            Some(old) => {
                                let new = self.v_app(decl, args[1].clone(), old, Icit::Expl);
                                self.mutable_map.borrow_mut().insert(SmolStr::new(a), new);
                            }
                            None => {
                                self.mutable_map.borrow_mut().insert(SmolStr::new(a), args[2].clone());
                            }
                        }
                        Some(Val::U)
                    }
                    None => None,
                }
            }
            "file_read_all_text" => {
                if args.is_empty() {
                    return None;
                }
                match lit(&args[0]) {
                    Some(path) => {
                        let content = std::fs::read_to_string(&path).unwrap_or_else(|e| {
                            panic!("file_read_all_text: failed to read '{}': {}", path, e)
                        });
                        Some(Val::LiteralIntro(empty_span(content)))
                    }
                    None => None,
                }
            }
            "file_write_all_text" => {
                if args.len() < 2 {
                    return None;
                }
                match (lit(&args[0]), lit(&args[1])) {
                    (Some(path), Some(content)) => {
                        std::fs::write(&path, &content).unwrap_or_else(|e| {
                            panic!("file_write_all_text: failed to write '{}': {}", path, e)
                        });
                        Some(Val::U)
                    }
                    _ => None,
                }
            }
            "file_append_all_text" => {
                if args.len() < 2 {
                    return None;
                }
                match (lit(&args[0]), lit(&args[1])) {
                    (Some(path), Some(content)) => {
                        use std::io::Write;
                        let mut file = std::fs::OpenOptions::new()
                            .append(true)
                            .create(true)
                            .open(&path)
                            .unwrap_or_else(|e| {
                                panic!("file_append_all_text: failed to open '{}': {}", path, e)
                            });
                        write!(file, "{}", content).unwrap_or_else(|e| {
                            panic!(
                                "file_append_all_text: failed to append to '{}': {}",
                                path, e
                            )
                        });
                        Some(Val::U)
                    }
                    _ => None,
                }
            }
            "file_exists" => {
                if args.is_empty() {
                    return None;
                }
                match lit(&args[0]) {
                    Some(path) => {
                        let exists = std::path::Path::new(&path).exists();
                        Some(Val::LiteralIntro(empty_span(if exists {
                            "true".to_string()
                        } else {
                            "false".to_string()
                        })))
                    }
                    None => None,
                }
            }
            "file_delete" => {
                if args.is_empty() {
                    return None;
                }
                match lit(&args[0]) {
                    Some(path) => {
                        std::fs::remove_file(&path).unwrap_or_else(|e| {
                            panic!("file_delete: failed to delete '{}': {}", path, e)
                        });
                        Some(Val::U)
                    }
                    None => None,
                }
            }
            _ => None,
        }
    }

    fn v_meta(&self, m: MetaVar) -> Val {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(m),
        }
    }

    fn closure_apply(&self, decl: &Decls, closure: &Closure, u: Val) -> Val {
        self.eval(decl, &closure.0.prepend(u), *closure.1.clone())
    }

    /// 把 `u` 应用到 `t`。卡住的 match 把实参收进 `pending`（值层保存）——
    /// scrutinee 归约选中分支后，由 `force` / `eval` 在**值层**逐个应用：
    /// 项层 splice 需要把实参 quote 成项，而实参的自由变量层级可能超出
    /// 捕获 env，无法引到正确上下文。
    fn v_app(&self, decl: &Decls, t: Val, u: Val, i: Icit) -> Val {
        match t {
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点
            // 会把 VSub 头送进来——如臂上下文里 Var 引用了被解槽）
            Val::VSub(..) => {
                let t = self.force(decl, t);
                self.v_app(decl, t, u, i)
            }
            Val::Lam(_, _, closure) => self.closure_apply(decl, &closure, u),
            Val::Flex(m, sp) => Val::Flex(m, sp.prepend((u, i))),
            Val::Rigid(x, sp) => Val::Rigid(x, sp.prepend((u, i))),
            Val::Decl(name, sp) => Val::Decl(name, sp.prepend((u, i))),
            Val::Obj(v, name, sp) => Val::Obj(v, name, sp.prepend((u, i))),
            Val::Prim(name, sp) => Val::Prim(name, sp.prepend((u, i))),
            Val::Match(val, env, cases, mut pending) => {
                pending.push((u, i));
                Val::Match(val, env, cases, pending)
            }
            x => panic!("impossible apply\n  {x:?}\nto\n  {u:?}"),
        }
    }

    fn v_app_sp(&self, decl: &Decls, t: Val, spine: Spine) -> Val {
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(decl, self.v_app_sp(decl, t, a.tail()), u.clone(), *i)
            }
        }
    }

    fn v_app_pruning(&self, decl: &Decls, env: &Env, v: Val, pr: &Pruning) -> Val {
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                decl,
                self.v_app_pruning(decl, &a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(decl, &a.tail(), v, &b.tail())
            }
            _ => panic!("impossible {v:?}"),
        }
    }

    fn eval(&self, decl: &Decls, env: &Env, tm: Tm) -> Val {
        match tm {
            Tm::Var(x) => match env.iter().nth(x.0 as usize) {
                Some(v) => v.clone(),
                None => panic!("unbound de Bruijn index {x:?}"),
            },
            Tm::Decl(name) => match decl.get(&name) {
                Some(e) => e.val.clone(),
                None => panic!("unbound global {name}"),
            },
            Tm::Obj(tm, name) => {
                let v = self.eval(decl, env, *tm);
                match project(&v, &name) {
                    Some(p) => p,
                    None => Val::Obj(Box::new(v), name, List::new()),
                }
            }
            Tm::App(t, u, i) => {
                let u_val = self.eval(decl, env, *u);
                self.v_app(decl, self.eval(decl, env, *t), u_val, i)
            }
            Tm::Lam(x, i, t) => Val::Lam(x, i, Closure(env.clone(), t)),
            Tm::Pi(x, i, a, b) => Val::Pi(x, i, Box::new(self.eval(decl, env, *a)), Closure(env.clone(), b)),
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(decl, env, *t);
                self.eval(decl, &env.prepend(t_val), *u)
            }
            Tm::U => Val::U,
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(decl, env, self.eval(decl, env, *t), &pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x),
            Tm::LiteralType => Val::LiteralType,
            Tm::Prim(name) => {
                // 实参经 Lam 链进 env（最内 = 最后应用）：卡成带名字与实参
                // spine 的 Prim。归约统一在 force（不在求值点按 env 触发——
                // quote → eval 往返时项已改成 `Prim 实参` 的应用形态，按
                // 现场 env 触发会把无关的字面量拼进来）。
                let mut args: Vec<(Val, Icit)> =
                    env.iter().map(|v| (v.clone(), Icit::Expl)).collect();
                args.reverse(); // 应用序 → spine 头 = 最后应用
                Val::Prim(
                    name,
                    args.into_iter().fold(List::new(), |acc, e| acc.prepend(e)),
                )
            }
            Tm::Sum(name, params, cases) => {
                let new_params = params
                    .into_iter()
                    .map(|(n, v, t, i)| {
                        (
                            n,
                            Rc::new(self.eval(decl, env, v)),
                            Rc::new(self.eval(decl, env, t)),
                            i,
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
                let typ = self.eval(decl, env, *typ);
                let datas = datas
                    .into_iter()
                    .map(|(n, v, i)| (n, Rc::new(self.eval(decl, env, v)), i))
                    .collect();
                Val::SumCase {
                    typ: Rc::new(typ),
                    case_name,
                    datas,
                }
            }
            Tm::Match(tm, cases) => {
                let val = self.force(decl, self.eval(decl, env, *tm));
                match val {
                    Val::SumCase { .. } => {
                        match Compiler::eval_aux(self, decl, &val, env, &cases) {
                            Some((body, env)) => self.eval(decl, &env, body),
                            None => Val::Match(Box::new(val), env.clone(), cases, Vec::new()),
                        }
                    }
                    neutral => Val::Match(Box::new(neutral), env.clone(), cases, Vec::new()),
                }
            }
        }
    }

    fn quote_sp(&self, decl: &Decls, l: Lvl, t: Tm, spine: Spine) -> Tm {
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                Tm::App(
                    Box::new(self.quote_sp(decl, l, t, a.tail())),
                    Box::new(self.quote(decl, l, u.clone())),
                    *i,
                )
            }
        }
    }

    fn quote(&self, decl: &Decls, l: Lvl, t: Val) -> Tm {
        let t = self.force(decl, t);
        match t {
            // 正常路径 force 后顶层不会是 VSub；fuel 耗尽时 force 原样返回
            // VSub——解包打印内层（σ 未推开，保真度同旧版"打印未展开 rigid"），
            // 链式 VSub 由递归消化，不会产生 Tm::U 垃圾
            Val::VSub(v, _) => self.quote(decl, l, *v),
            Val::Flex(m, sp) => self.quote_sp(decl, l, Tm::Meta(m), sp),
            Val::Rigid(x, sp) => self.quote_sp(decl, l, Tm::Var(lvl2ix(l, x)), sp),
            Val::Decl(name, sp) => self.quote_sp(decl, l, Tm::Decl(name), sp),
            Val::Obj(v, name, sp) => {
                self.quote_sp(decl, l, Tm::Obj(Box::new(self.quote(decl, l, *v)), name), sp)
            }
            Val::Lam(x, i, closure) => Tm::Lam(
                x,
                i,
                Box::new(self.quote(decl, l + 1, self.closure_apply(decl, &closure, Val::vvar(l)))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x,
                i,
                Box::new(self.quote(decl, l, *a)),
                Box::new(self.quote(decl, l + 1, self.closure_apply(decl, &closure, Val::vvar(l)))),
            ),
            Val::U => Tm::U,
            Val::LiteralIntro(x) => Tm::LiteralIntro(x),
            Val::LiteralType => Tm::LiteralType,
            Val::Prim(name, sp) => self.quote_sp(decl, l, Tm::Prim(name), sp),
            Val::Sum(name, params, cases) => Tm::Sum(
                name,
                params
                    .into_iter()
                    .map(|(n, v, t, i)| {
                        (
                            n,
                            self.quote(decl, l, rc_take(v)),
                            self.quote(decl, l, rc_take(t)),
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
            } => Tm::SumCase {
                typ: Box::new(self.quote(decl, l, rc_take(typ))),
                case_name,
                datas: datas
                    .into_iter()
                    .map(|(n, v, i)| (n, self.quote(decl, l, rc_take(v)), i))
                    .collect(),
            },
            Val::Match(val, env, cases, pending) => {
                // 分支体在"捕获 env + fresh rigid 槽"下重新求值再 quote：
                // 这样 quote → eval 往返是恒等的（旧实现未做往返一致，此处
                // 是现架构补齐的关键点）。求值用简化 decl 表（全局值换成
                // 中性 Decl 引用），避免分支体里的递归调用被重展开（正确性
                // + 性能）。
                let declb = Rc::new(simpl_decl(decl));
                let tm_cases = cases
                    .into_iter()
                    .map(|(p, b)| {
                        let count = p.bind_count();
                        let env = (0..count).fold(env.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                        let tm = self.eval(&declb, &env, b);
                        // 分支体的 quote 也要用简化表：eval 产生的中性
                        // Decl(f, spine)（递归调用占位）若用真实表 quote，
                        // 入口 force 会再展开一层——每层 quote 多展开一层，
                        // 递归函数的卡住 match 直接发散。
                        (p, self.quote(&declb, l + count, tm))
                    })
                    .collect();
                // 卡住期累积的实参按应用序包在 Match 外（值层应用在
                // force/eval 的分支选中后做；quote → eval 往返由此保持）。
                // 实参的自由层级属当前上下文，quote 在调用方的 l 下正确。
                let m = Tm::Match(Box::new(self.quote(decl, l, *val)), tm_cases);
                pending.into_iter().fold(m, |acc, (u, i)| {
                    Tm::App(Box::new(acc), Box::new(self.quote(decl, l, u)), i)
                })
            }
        }
    }

    pub fn nf(&self, decl: &Decls, env: &Env, t: Tm) -> Tm {
        // quote → eval 会 force；一次 nf 充值 fuel 防循环解
        self.unify_fuel.set(UNIFY_FUEL);
        let l = Lvl(env.len() as u32);
        self.quote(decl, l, self.eval(decl, env, t))
    }

    fn close_val(&self, decl: &Decls, cxt: &Cxt, t: Val) -> Closure {
        Closure(cxt.env.clone(), Box::new(self.quote(decl, cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, decl: &Decls, cxt: &Cxt, t: Val, t_prime: Val) -> Result<(), Error> {
        self.unify_fuel.set(UNIFY_FUEL);
        self.unify(decl, cxt.lvl, cxt, t.clone(), t_prime.clone(), None)
            .map_err(|_| {
                let fuel_note = if self.unify_fuel.get() == 0 {
                    " (fuel exhausted)"
                } else {
                    ""
                };
                Error(format!(
                    "can't unify{} {} == {}",
                    fuel_note,
                    pretty_tm(0, cxt.names(), &self.quote(decl, cxt.lvl, t)),
                    pretty_tm(0, cxt.names(), &self.quote(decl, cxt.lvl, t_prime)),
                ))
            })
    }
}

/// 值树里是否出现某层级（浅层结构扫描；闭包跳过——那里的环由 force 的
/// fuel 兜底）。特化解的环守卫（`Subst::extend` 的调用方）用。
fn val_mentions_lvl(v: &Val, x: Lvl) -> bool {
    fn spine(sp: &Spine, x: Lvl) -> bool {
        sp.iter().any(|(v, _)| val_mentions_lvl(v, x))
    }
    match v {
        Val::Rigid(y, sp) => *y == x || spine(sp, x),
        Val::Flex(_, sp) | Val::Decl(_, sp) => spine(sp, x),
        Val::Obj(o, _, sp) => val_mentions_lvl(o, x) || spine(sp, x),
        Val::VSub(v, _) => {
            // 只扫解值自身的结构，**不扫 σ 的映射值**：σ 的其它条目（如头部
            // 精化的构造子值）合法引用别的模式变量，扫进来会把无害的解误判
            // 成环。σ 槽位若真引用 x，解包后的 v 结构里自会以 Rigid(x) 出现
            // （对齐旧世界"occurs 只看解的裸值"的语义；更深的间接环仍由
            // force 的 fuel 兜底）。
            val_mentions_lvl(v, x)
        }
        Val::Sum(_, params, _) => {
            params
                .iter()
                .any(|(_, v, t, _)| val_mentions_lvl(v, x) || val_mentions_lvl(t, x))
        }
        Val::SumCase { typ, datas, .. } => {
            val_mentions_lvl(typ, x) || datas.iter().any(|(_, v, _)| val_mentions_lvl(v, x))
        }
        Val::Match(s, env, _, pending) => {
            val_mentions_lvl(s, x)
                || env.iter().any(|v| val_mentions_lvl(v, x))
                || pending.iter().any(|(v, _)| val_mentions_lvl(v, x))
        }
        Val::Prim(_, sp) => spine(sp, x),
        Val::Lam(..) | Val::Pi(..) | Val::U | Val::LiteralType | Val::LiteralIntro(_) => false,
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）再查构造子字段。
/// 其余（Rigid / Flex / Decl / 卡住的 Obj / 函数……）返回 None → 卡住成 `Val::Obj`。
fn project(v: &Val, name: &Span<String>) -> Option<Val> {
    match v {
        Val::Sum(_, params, _) => params
            .iter()
            .find(|(n, ..)| n == name)
            .map(|(_, v, _, _)| (**v).clone()),
        Val::SumCase { typ, datas, .. } => {
            let params = match typ.as_ref() {
                Val::Sum(_, params, _) => params,
                _ => return None,
            };
            params
                .iter()
                .find(|(n, ..)| n == name)
                .map(|(_, v, _, _)| (**v).clone())
                .or_else(|| {
                    datas
                        .iter()
                        .find(|(n, _, _)| n == name)
                        .map(|(_, v, _)| (**v).clone())
                })
        }
        _ => None,
    }
}

/// quote/rename 卡住 match 的分支体时用的 decl 表：所有全局值换成指向自身的
/// 中性 `Val::Decl`，防止递归定义在求值分支体时被重展开。enum 类型本体的值
/// （`Val::Sum`）保持原样——构造子值的 `typ` 槽需要真实的 Sum 值。
fn simpl_decl(decl: &Decls) -> Decls {
    decl.iter()
        .map(|(k, e)| {
            let val = match &e.val {
                Val::Sum(..) => e.val.clone(),
                _ => Val::Decl(k.clone(), List::new()),
            };
            (k.clone(), DeclEntry { ty: e.ty.clone(), val })
        })
        .collect()
}

/// 文件 IO builtin 的固定文件名串行锁（L06 同款：Windows 并行测试线程
/// 的句柄竞争会让删除报 os error 5）。
pub static FILE_IO_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(&preprocess(input), path_id).map_err(Error)?;
    let mut cxt = Cxt::new(&infer);
    let mut ret = String::new();
    for tm in ast {
        if std::env::var_os("L07_DEBUG").is_some() {
            eprintln!("> {}", parser::syntax::Decl::name(&tm));
        }
        let (x, _, new_cxt) = infer.infer(&cxt, tm)?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &pretty_tm(0, cxt.names(), &infer.nf(cxt.decl(), &cxt.env, x));
            ret += "\n";
        }
    }
    Ok(ret)
}

/// 内嵌 `test` 与性能版互检共用的演示源：enum + 依赖 match + String
/// 字面量 + builtin 注册表（str_eq / str_indent2 / 文件 IO）+ decl 表
/// 按名取值 + 可变全局（L06 DEMO 的 L07 版：补 enum/match 段）。
pub(crate) const DEMO_SRC: &str = r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px
def the(A : U)(x: A): A = x

enum Nat {
    zero
    succ(x: Nat)
}

def two : Nat = succ (succ zero)
def four : Nat = succ (succ two)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def six : Nat = add four two
println six

def pr1 = f => x => f x
println pr1

def mystr = "hello world"
println mystr

def add_tail(x: String): String = string_concat x "!"

def mystr2 = add_tail mystr
println mystr2

def eq1 = str_eq "foo" "foo"
println eq1

def eq2 = str_eq "foo" "bar"
println eq2

def ind = str_indent2 "line1\nline2"
println ind

def demo_path = "l07_builtin_demo.txt"
def demo_write : U = file_write_all_text demo_path "hello file"
def demo_append : U = file_append_all_text demo_path "!"
def read_back : String = file_read_all_text demo_path
println read_back

def exists1 : String = file_exists demo_path
println exists1

def demo_delete : U = file_delete demo_path
def exists2 : String = file_exists demo_path
println exists2

def st : U = string_to_global_type "String"
println st

def st_nat : U = string_to_global_type "Nat"
println st_nat

def store1 : U = create_global "greeting" "hi"
def upd1 : U = change_mutable "greeting" (s => string_concat s "!")
def g1 : String = get_global "greeting"
println g1

def g2 : String = get_global_default "greeting" "fallback"
println g2

def g3 : String = get_global_default "missing_name" "fallback"
println g3

def upd2 : U = change_mutable_default "greeting" (s => string_concat s "?") "x"
def g4 : String = get_global "greeting"
println g4

def rep1 : U = report_check_issue "E1" "demo_mod" "sig" "message"
def issues : String = get_global "CheckIssues"
println issues

"#;

/// 参考版基准口径：全量 elaborate（def/enum 注册），返回是否通过。
pub(crate) fn bench_check(decls: &[parser::syntax::Decl]) -> bool {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&infer);
    for d in decls {
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return false,
        }
    }
    true
}

/// 参考版项的节点数（与性能版 `tm_size` 同口径）。
fn tm_size_ref(t: &Tm) -> u64 {
    let mut stack: Vec<&Tm> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Decl(_) | Tm::Prim(_) => {}
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

/// 参考版基准口径：elaborate 全部 decl 后，取**最后一个 def** 在 decl 表里
/// 登记的值，空层级引读并数节点（深 Box 树的递归析构会爆栈，基准里
/// `mem::forget`——L03/L04/L05/L06 同款处理）。
pub(crate) fn bench_check_nf(decls: &[parser::syntax::Decl]) -> u64 {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&infer);
    let mut last: Option<String> = None;
    for d in decls {
        if let parser::syntax::Decl::Def { name, .. } = d {
            last = Some(name.data.clone());
        }
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return 0,
        }
    }
    let Some(name) = last else { return 0 };
    let Some(entry) = cxt.decl_get(&name) else { return 0 };
    let q = infer.quote(cxt.decl(), Lvl(0), entry.val.clone());
    let n = tm_size_ref(&q);
    std::mem::forget(q);
    n
}

/// 注释剥离(行 `//` 与块 `/* */`),**字符串字面量内不生效**——旧版对
/// `//` / `/*` 做纯文本剥离,会把 `"http://…"` 之类的字面量截成未闭合
/// 字符串导致解析失败。现按词法规则跳过字符串区间(含 `\` 转义);注释
/// 内容只替换为空白(ASCII 下 span 偏移稳定;非 ASCII 注释内容会使后续
/// 偏移前移,仅影响错误消息中的偏移数字)。块注释不嵌套;未闭合的块
/// 注释剥到 EOF(余下 decl 静默消失,历史行为)。
pub fn preprocess(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    let mut in_string = false;
    let mut escaped = false;
    while let Some(c) = chars.next() {
        if in_string {
            out.push(c);
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        match c {
            '"' => {
                in_string = true;
                out.push(c);
            }
            '/' if chars.peek() == Some(&'/') => {
                chars.next();
                out.push_str("  ");
                // 行注释:换行前的内容替换为空白(保留换行符)
                for rc in chars.by_ref() {
                    if rc == '\n' {
                        out.push('\n');
                        break;
                    }
                    out.push(if rc.is_whitespace() { rc } else { ' ' });
                }
            }
            '/' if chars.peek() == Some(&'*') => {
                chars.next();
                out.push_str("  ");
                // 块注释:到 `*/` 为止的内容替换为空白
                while let Some(rc) = chars.next() {
                    if rc == '*' && chars.peek() == Some(&'/') {
                        chars.next();
                        out.push_str("  ");
                        break;
                    }
                    out.push(if rc.is_whitespace() { rc } else { ' ' });
                }
            }
            _ => out.push(c),
        }
    }
    out
}

use pattern_match::Compiler;

use parser::syntax::Icit;
#[cfg(test)]
mod tests;
