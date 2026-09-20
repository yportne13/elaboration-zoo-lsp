//! L09 核心机（eval / quote / unify / rename / solve / prune / check /
//! infer / check_universe / 模式编译）的极致性能版：L08 冠军配方
//! （`bump_spine_iter`）向 MLTT/universe 层的移植。继承 L05-L08 的全部
//! 机制（见 L06/L08 版模块注释与 readme）：bump arena、打包值 [`V`]、
//! 扁平中性 + spine 栈（含链头种类 `Entry.hk` 的 O(1) 头判定）、复合环境、
//! 迭代内核（eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈）、
//! quote 记忆化、O(1) 名字解析、`Tycker` 稳态复用。
//!
//! **L09 自己的增量与差异**（参考版 = `super` 的分文件实现，语义以其为
//! 准）——参考版是 init 时期架构的现代残存层，与 L06-L08 的 decl 表世界
//! 有系统性不同，孪生版逐项对齐：
//!
//! - **宇宙层级**：`U(u32)`（`Type N` 语法；裸 `U` 只是普通变量名）。
//!   打包值 tag 3 从立即数改为携带层级（`V = lvl<<3|3`，61 位余量）。
//!   类型注解一律过 [`Machine::check_universe`]（参考版完整版：可解
//!   meta——pren.dom==0 时 meta 类型 force 后是 U 即解 `U(0)`，否则
//!   rename 出 `U(0)` 的解；两分支都返回层级 0）。
//! - **全局 = env 外的 `global` 表 + 大下标**：没有 decl 表。def/enum 在
//!   `Infer.global: HashMap<Lvl, Val>` 里按 `global_idx` 登记，项层引用是
//!   `Tm::Var(Ix(global_idx + 1919810))`（[`GLOBAL_BASE`] 哨兵）；eval 的
//!   Var 臂对越过哨兵的下标查 global 表，quote/rename 对越过哨兵的 Rigid
//!   原样产出大下标 Var。递归 def = fake_bind（src_names 里以全局层级占
//!   位）+ 检查前 global 表放 `VVar(自身大层级)` 占位 + 检查后覆盖真值。
//! - **builtin 只有 `string_concat`**：名字 lambda 链的体是**无名的**
//!   `Tm::Prim`，求值时读 env 前两槽（全为字面量则拼接，否则卡
//!   `Val::Prim`——**不带 spine**，参考版 v_app 对它 panic，故永无
//!   Prim 头的链）。没有可变全局 / 文件 IO / 其余 builtin。
//! - **卡住 match 无 pending、force 只展开 Flex**：v_app 对 Match panic
//!   （不可能吸收实参）；参考版 force 只有一个 Flex 臂——meta 解开后
//!   不会重选 match、不展开投影/decl。卡住投影 `Val::Obj` 只在 eval 的
//!   Tm::Obj 臂产生（接收者 Rigid 才卡，其余 panic）。
//! - **模式特化不走 pm_defs**：参考版走 `check_pm`/`unify_pm` +
//!   `Cxt::update_cxt`/`refresh`——把精化等式**直接改写进环境**（目标槽
//!   替换 + 全槽在"更新后 env"下重求值重锚定），src_names 按层级取类型
//!   （BiMap 的 map2 持久），快版镜像为 `lvl_types` 表 + 双轨迹撤销。
//!   模式编译器（Compiler）与参考版 pattern_match.rs 同步维护（2026-09-18
//!   自决策树矩阵重写为 L07 逐臂下钻，L10-L12 同款）：walk_pat 绑槽 +
//!   check_pm_final 特化 + subst_cxt 臂上下文；覆盖探测 = 值级结构探测
//!   （`run_pure_probe` 快照回滚）。
//! - **unify 无燃料、无 pm 臂、无 (Obj,Obj)/宽松臂**：臂序 = U/Pi/Rigid/
//!   Flex/Flex/Lam/η/Flex 求解/LiteralType 宽松/Sum/SumCase/Match；
//!   flex_flex 单方向尝试无快照回滚；SumCase/SumCase 比 typ+datas（L07+
//!   只比 datas）；Match/Match 分支体在**中性 global 克隆**下重求值
//!   （参考版 avoid_recursive 同款——快版传中性 globals 视图）。
//! - **重定义静默覆盖**（参考版无 redefine 检查）；构造子只以**裸名**登记
//!   （无 `Enum.case` 别名；struct 的 case 名本身是 `Name.mk`）。
//!
//! 与参考版共用 parser / pretty / preprocess，**Ok 输出逐字节一致**（互检
//! 测试 + `tests/l09_fast_parity.rs`）。已知偏差（仅错误消息内容，不影响
//! 判定与 Ok 输出）：快版错误里内嵌的 Debug-Val/Tm 的名字 Span 全零
//! （参考版携带源码偏移），套件比对前按 `start_offset/end_offset/path_id`
//! 归一化。

use bumpalo::Bump;
use smol_str::SmolStr;
use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

use super::parser::syntax::{Decl, Either, Icit, Pattern, Raw};
use super::pretty::pretty_tm;
use super::{cover_at, empty_span, fmt_path, Error, Ix, MetaVar, PatternDetail, PosCover, Tm as CTm};

/// 全局下标哨兵：`Ix >= GLOBAL_BASE` 的 Var/Rigid 引用 global 表。
const GLOBAL_BASE: u32 = 1919810;

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    /// 把头按掩码应用到求值环境：`Some(icit)` 槽位以该 icit 应用实参，
    /// `None` 槽位跳过。
    AppPruning(&'a Tm<'a>, Option<&'a PrCons<'a>>),
    U(u32),
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    Meta(u32),
    /// String 字面量的类型（`String`）。
    LiteralType,
    /// 字符串字面量（内容即值）。
    LiteralIntro(&'a str),
    /// builtin 体标记（无名；求值时读 env 前两槽拼接或卡住）。
    Prim,
    /// `x.field` 投影（参考版 `Tm::Obj`；字段名只服务 pretty/查表）。
    Obj(&'a Tm<'a>, &'a str),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 类型项,
    /// icit)，声明处值项即参数自身；实例化后值槽携带当前实参。
    Sum(&'a str, &'a [SumParamT<'a>], &'a [&'a str]),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Sum`。
    SumCase {
        typ: &'a Tm<'a>,
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
    },
    /// 已编译的 match：分支体是检查过的项，运行时按模式首匹配。
    Match(&'a Tm<'a>, &'a [(PatternDetail, &'a Tm<'a>)]),
}

/// `Tm::Sum` 的参数槽（bump 内）。
pub(crate) struct SumParamT<'a> {
    pub(crate) name: &'a str,
    pub(crate) val: &'a Tm<'a>,
    pub(crate) ty: &'a Tm<'a>,
    pub(crate) icit: Icit,
}

/// `Tm::SumCase` 的字段槽（bump 内）。
pub(crate) struct SumDataT<'a> {
    pub(crate) name: &'a str,
    pub(crate) val: &'a Tm<'a>,
    pub(crate) icit: Icit,
}

/// `AppPruning` 的掩码链表（bump 持久，头 = 最内层绑定）。
pub(crate) struct PrCons<'a> {
    /// `Some(icit)` = 绑定槽位（应用实参，icit 随槽）；`None` = define 槽
    /// （跳过）。
    slot: Option<Icit>,
    /// 本节点向外（next 方向）连续 `None`（define 槽）的个数；Some 槽为 0。
    none_run: u32,
    /// 本 none-run 之后的第一个槽（Some 槽或链尾）——跳段的落点。
    after_run: Option<&'a PrCons<'a>>,
    next: Option<&'a PrCons<'a>>,
}

impl<'a> PrCons<'a> {
    /// 入链构造（新槽恒为链头，最内层）。run 统计只读既有节点。
    fn new(slot: Option<Icit>, next: Option<&'a PrCons<'a>>) -> Self {
        let (none_run, after_run) = match (slot, next) {
            (Some(_), _) => (0, next),
            (None, Some(n)) if n.slot.is_none() => (n.none_run + 1, n.after_run),
            (None, _) => (1, next),
        };
        PrCons {
            slot,
            none_run,
            after_run,
            next,
        }
    }
}

/// 局部 telescope 节点（`fresh_meta` 闭类型用）：`Bind` 槽存引好的类型项，
/// `Define` 槽再存定义项。
struct LCons<'a> {
    name: &'a str,
    a_t: &'a Tm<'a>,
    /// `Some` = define（闭成 Let），`None` = binder（闭成显式 Π）。
    t_t: Option<&'a Tm<'a>>,
    next: Option<&'a LCons<'a>>,
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Rigid(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U(lvl<<3|3)`（宇宙层级进打包字）、`4=Pi(ptr|4)`、
/// `5=Meta(m<<3|5)`（未解 meta 立即数）、`6=LiteralType`（立即数）、
/// `7=XCell(ptr|7)`（字面量 / Prim / 卡住投影 / Sum / SumCase / Match）。
/// icit 不进打包字——由 Clo/Pi 单元与 spine 槽携带（打包字是 quote/unify
/// 记忆化的键，icit 随值结构唯一确定）。
#[derive(Clone, Copy)]
pub(crate) struct V(pub(crate) u64);

#[inline]
pub(crate) fn v_lvl(level: u32) -> V {
    V(((level as u64) << 3) | 0)
}
#[inline]
pub(crate) fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}
#[inline]
pub(crate) fn v_spine(idx: usize) -> V {
    V(((idx as u64) << 3) | 2)
}
#[inline]
pub(crate) fn v_u(lvl: u32) -> V {
    V(((lvl as u64) << 3) | 3)
}
#[inline]
pub(crate) fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
pub(crate) fn v_meta(m: u32) -> V {
    V(((m as u64) << 3) | 5)
}
/// `LiteralType` 立即数。
#[inline]
pub(crate) fn v_lit_ty() -> V {
    V(6)
}
#[inline]
pub(crate) fn v_xcell<'a>(p: &'a XCell<'a>) -> V {
    V((p as *const _ as u64) | 7)
}
#[inline]
pub(crate) fn v_tag(v: V) -> u64 {
    v.0 & 7
}
#[inline]
pub(crate) fn v_lvl_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
#[inline]
pub(crate) fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    // SAFETY: tag 1 由 `v_clo`（`ptr | 1`）唯一产出；`CloCell` 地址 ≥8 对齐
    // （下面的编译期断言），`& !7` 精确还原指针，且该单元在 bump `'a` 内存活。
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    // SAFETY: tag 4 由 `v_pi`（`ptr | 4`）唯一产出；`PiCell` 地址 ≥8 对齐
    // （编译期断言），`& !7` 精确还原指针，单元在 bump `'a` 内存活。
    unsafe { &*((v.0 & !7) as *const PiCell) }
}
#[inline]
pub(crate) fn v_meta_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
/// tag 3 的宇宙层级。
#[inline]
pub(crate) fn v_u_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
/// tag 7 单元解引用（bump 内分配，本轮内有效）。
///
/// 依赖 `XCell` ≥8 对齐（由 `#[repr(align(8))]` 保证，含 wasm32——
/// `&str` 仅 4 对齐时枚举会跌破 8）；`& !7` 才能精确还原 `ptr | 7`。
#[inline]
pub(crate) fn v_xcell_of<'a>(v: V) -> &'a XCell<'a> {
    // SAFETY: tag 7 由 `v_xcell`（`ptr | 7`）唯一产出；`XCell` 地址 ≥8 对齐
    // （`#[repr(align(8))]` + 编译期断言），`& !7` 精确还原指针，单元在
    // bump `'a` 内存活。
    unsafe { &*((v.0 & !7) as *const XCell) }
}

/// `Val::Sum` 的参数槽（值层，bump 内）。
#[derive(Clone)]
pub(crate) struct SumParamV<'a> {
    name: &'a str,
    val: V,
    ty: V,
    icit: Icit,
}

/// `Val::SumCase` 的字段槽（值层，bump 内）。
pub(crate) struct SumDataV<'a> {
    name: &'a str,
    val: V,
    icit: Icit,
}

/// tag 7 的载体：字面量值、builtin 体标记、卡住投影、和类型本体、构造子
/// 值、卡住 match。判等按单元指针（同内容不同次求值各造单元——与参考版
/// 每次构造新值同构）；**位相等捷径对 tag 7 关闭**（见模块注释）。
///
/// 显式 `align(8)`：packed 字用 `ptr | 7` 编码、`v.0 & !7` 解码，要求单元
/// 地址低 3 位为 0。wasm32 的 `&str` 仅 4 字节对齐，若枚举最大对齐由
/// 指针/长度字段决定会跌破 8，`& !7` 就会清掉 bit2 → 错误指针 UB。
#[repr(align(8))]
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    /// builtin 体标记（无名；v_app 对它 panic，故永无 Prim 头的链）。
    Prim,
    /// 卡住投影：被投影者 + 字段名。带实参的卡住投影 = spine 链（头 =
    /// 本单元），与参考版 `Val::Obj(v, name, sp)` 同构。
    Obj { val: V, name: &'a str },
    /// 和类型本体：名 + 参数槽（名/实参/实参类型/icit）+ 构造子名表。
    Sum {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
    },
    /// 构造子值：typ 求值后是其所属的已实例化 `Sum`。
    SumCase {
        typ: V,
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
    },
    /// 卡住 match：scrutinee（创建时已 force）+ 捕获 env + 编译分支。
    /// **无 pending**——参考版 v_app 对 Match panic，卡住 match 永不吸收
    /// 实参。
    Match {
        scrutinee: V,
        env: Env<'a>,
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
    },
    /// 显式替换下的值（模式精化，参考版 `Val::VSub` / dpm-nbe `VSub`）：
    /// 特化解不改写既有值，只把解包在外面；`force` 在读点把 σ 推进值的
    /// 结构（[`frcs`]，对齐 dpm-nbe 的 `frcS`）。不变式：`force` 的返回值
    /// 顶层不会是 VSub（fuel 耗尽的降级点在 frcs 的 lookup 命中处，返回
    /// 裸 rigid）。
    VSub { val: V, sub: Rc<SubstV> },
}

/// 模式特化的解：层级 → 值 的**持久化单链**（参考版 `Subst` 同构；链头 =
/// 最新的解）。仅由模式编译器经 [`SubstV::extend`] / 特化合一的
/// [`SpecSolve::acc`] 构建；`Rc` 共享让臂边界回滚 = 指针赋值、VSub 包裹
/// = O(1)。取代旧 `update_cxt` 的上下文改写（改写目标槽 + 全槽 refresh）。
#[derive(Clone, Default)]
pub(crate) struct SubstV {
    head: Option<Rc<SubEntryV>>,
}

struct SubEntryV {
    lvl: u32,
    /// 解的原始值。不预先包裹"更新的解"——读取时 `lookup_hit` 把整条 σ
    /// 包在外面（条件包裹，见其文档），由 force 在读点一次性推开。
    val: V,
    next: Option<Rc<SubEntryV>>,
}

/// 存活的 σ 链条目数（`SubEntryV` 各计 1；头壳 `SubstV` 带 `Clone` derive、
/// 值级复制会破坏计数配对，故不计）。仅为跨轮回收的回归测试提供观察口
/// （[SUBSTV_ALIVE]）；一次原子加减发生在 extend / compose 的分配与 Rc
/// 归零的 Drop 时机，均非热路径。观察泄漏同样有效：arena 克隆泄漏 ⇒ 其
/// head 链的条目引用不归还 ⇒ 计数不回落。
pub(crate) static SUBSTV_ALIVE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

impl Drop for SubEntryV {
    fn drop(&mut self) {
        SUBSTV_ALIVE.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// --------------------------------------------------------------------------------
// σ 克隆的跨轮回收（L07 2026-09-18 修复轮的 L09 移植，README §7.7 的落地）
// --------------------------------------------------------------------------------
// bump `reset()` 不跑 Drop：arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆
// 的强引用永不归还，链（及后缀）跨轮慢泄漏。登记表在 [`wrap_sub`] 构造
// 克隆的**同一时刻**记录 `Rc::as_ptr`，轮界（[`Machine::clear_round`]，与
// 三处 `bump.reset()` 严格伴生）逐指针 `Rc::from_raw` + drop。
//
// SAFETY（恰好归还"arena 那一份"强引用，等价于被跳过的 Drop）——按 L09
// 实际代码逐条核对（2026-09-18 移植轮）：
// - **构造点唯一**：`XCell::VSub` 在本层孪生里仅 [`wrap_sub`] 一处构造
//   （subst_cxt / frcs / unify_pm 的包裹全部经 [`wrap_sub`]），登记点与
//   构造点一一对应，不存在绕过登记的 arena 克隆；
// - 指针在登记到归还之间始终有效：Rc 节点在全局堆上（arena 只持有
//   克隆），arena 克隆持强引用 ⇒ 计数 ≥ 1，节点不会在归还前释放；外部
//   持有者（编译器局部 σ、链共享）只会让计数更多，不会提前释放节点；
// - 同一节点被 wrap 多次 = 多个克隆 = 多次登记 = 多次减一，各归还各的；
// - 表外持有者不受影响：归还后节点若仍有引用则继续存活（正常 Rc 语义），
//   归零则连同后缀级联释放（后缀条目有自己的计数与 Drop）；
// - [`vsub_reclaim`] 后表已清空（drain），旧指针不会跨轮重复 drop；
// - **线程模型**：`Rc<SubstV>` 非 Send ⇒ 持有 σ 的 Tycker 不可跨线程移动，
//   wrap_sub 与 clear_round 必在同一线程执行，thread_local 登记表所见即
//   所用；线程退出时表随 thread_local 析构（只丢指针，不 from_raw），
//   未归还份额即普通泄漏，无悬垂解引用。
thread_local! {
    static VSUB_REGS: std::cell::RefCell<Vec<*const SubstV>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// 轮界归还 arena 内的全部 σ 克隆（与 `bump.reset()` 伴生）。
fn vsub_reclaim() {
    VSUB_REGS.with(|r| {
        for p in r.borrow_mut().drain(..) {
            // SAFETY：见上——p 来自 wrap_sub 登记的 Rc 克隆，本调用归还其
            // arena 份额且仅此一次（表已 drain）。
            drop(unsafe { Rc::from_raw(p) });
        }
    });
}

impl SubstV {
    #[inline]
    fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配零 fuel；`mentions_level` 浅扫描）；引用时把
    /// 整条 σ 包在解值外（解值不含 x 自身——occurs 守卫；比该条目更新的
    /// 解恰好借此对解值生效），由 force 在读点推开。未命中 None。
    fn lookup_hit<'a>(
        bump: &'a Bump,
        spine: &Spine,
        defs: &[V],
        sub: &Rc<SubstV>,
        x: u32,
    ) -> Option<V> {
        let mut cur = sub.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return Some(if !mentions_level(spine, defs, e.val, sub) {
                    e.val
                } else {
                    wrap_sub(bump, sub, e.val)
                });
            }
            cur = e.next.clone();
        }
        None
    }

    /// x 是否已有解。
    fn has(&self, x: u32) -> bool {
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
    fn extend(sub: &Rc<SubstV>, x: u32, v: V) -> Rc<SubstV> {
        SUBSTV_ALIVE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Rc::new(SubstV {
            head: Some(Rc::new(SubEntryV {
                lvl: x,
                val: v,
                next: sub.head.clone(),
            })),
        })
    }

    /// 组合：内层 `inner` 先应用、外层 `outer` 后应用。外层条目接到链头
    /// （先被查到 = 覆盖同键，"取最新"语义）。
    fn compose(outer: &Rc<SubstV>, inner: &Rc<SubstV>) -> Rc<SubstV> {
        fn cons_all(
            entry: &Option<Rc<SubEntryV>>,
            onto: Option<Rc<SubEntryV>>,
        ) -> Option<Rc<SubEntryV>> {
            match entry {
                None => onto,
                Some(e) => {
                    SUBSTV_ALIVE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    Some(Rc::new(SubEntryV {
                        lvl: e.lvl,
                        val: e.val,
                        next: cons_all(&e.next, onto),
                    }))
                }
            }
        }
        Rc::new(SubstV {
            head: cons_all(&outer.head, inner.head.clone()),
        })
    }
}

/// 解值的浅结构是否引用 σ 的某个已解层级（参考版 `Subst::mentions_level`
/// 同款遍历面）。含闭包 **env 槽**与 Match 的 scrutinee/captured env；不含
/// 闭包体 / Match 分支体。VSub 保守记为引用。Flex 只扫 spine。误报只多
/// 一次包裹，漏报才会丢精化——宁宽勿窄。
fn mentions_level(spine: &Spine, defs: &[V], v: V, sub: &SubstV) -> bool {
    fn env_slots(spine: &Spine, defs: &[V], env: Env<'_>, sub: &SubstV) -> bool {
        let mut n = env.binds;
        while let Some(e) = n {
            if mentions_level(spine, defs, e.val, sub) {
                return true;
            }
            n = e.next;
        }
        for k in 0..env.flat_len {
            if mentions_level(
                spine,
                defs,
                defs[(env.flat_base + env.flat_len - 1 - k) as usize],
                sub,
            ) {
                return true;
            }
        }
        false
    }
    match v_tag(v) {
        0 => sub.has(v_lvl_of(v)),
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            let head_hit = match v_tag(hd) {
                0 => sub.has(v_lvl_of(hd)),
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, .. } => mentions_level(spine, defs, *val, sub),
                    XCell::VSub { .. } => true,
                    _ => false,
                },
                _ => false,
            };
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args);
            head_hit || args.iter().any(|(a, _)| mentions_level(spine, defs, *a, sub))
        }
        5 | 3 | 6 => false,
        1 => {
            let c = v_clo_of(v);
            env_slots(spine, defs, c.env, sub)
        }
        4 => {
            let p = v_pi_of(v);
            mentions_level(spine, defs, p.dom, sub) || env_slots(spine, defs, p.env, sub)
        }
        7 => match v_xcell_of(v) {
            XCell::VSub { .. } => true,
            XCell::Lit(_) | XCell::Prim => false,
            XCell::Obj { val, .. } => mentions_level(spine, defs, *val, sub),
            XCell::Sum { params, .. } => params.iter().any(|p| {
                mentions_level(spine, defs, p.val, sub)
                    || mentions_level(spine, defs, p.ty, sub)
            }),
            XCell::SumCase { typ, datas, .. } => {
                mentions_level(spine, defs, *typ, sub)
                    || datas.iter().any(|d| mentions_level(spine, defs, d.val, sub))
            }
            XCell::Match {
                scrutinee, env, ..
            } => mentions_level(spine, defs, *scrutinee, sub) || env_slots(spine, defs, *env, sub),
        },
        _ => false,
    }
}

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc
/// clone + 一次 bump 单元，force 在消费点惰性推开）。σ 为空时零开销直通。
/// 包裹克隆进 arena 的同时登记 [`VSUB_REGS`]——轮界 [`vsub_reclaim`] 补上
/// 被 bump reset 跳过的 Drop（见其 SAFETY 注释）。
#[inline]
fn wrap_sub<'a>(bump: &'a Bump, sub: &Rc<SubstV>, v: V) -> V {
    if sub.is_empty() {
        v
    } else {
        let cell = bump.alloc(XCell::VSub {
            val: v,
            sub: sub.clone(),
        });
        // 注册后置：alloc 成功（cell 内 clone 的 +1 已落账）才登记。若注册
        // 在前而 alloc 失败 panic 又被 catch_unwind 捕获，轮界 reclaim 的
        // Rc::from_raw + drop 会按未发生的 +1 过度递减引用计数（L07 评审
        // P2，2026-09-18 修复 7 的同步移植）。
        VSUB_REGS.with(|r| r.borrow_mut().push(Rc::as_ptr(sub)));
        v_xcell(cell)
    }
}

/// 值树里是否出现某层级（特化解的环守卫；参考版 `val_mentions_lvl`
/// 同款遍历面，但 **Flex 头的实参视为不透明**）：可达性探测用 `Raw::Hole`
/// 实例化构造子绑定器，fresh meta 的 pruning 会把整组绑定器（含被解变量
/// 本身）收进 spine——`l := succ (?m … l …)` 是"meta 应用到变量"的合法
/// 形，不是结构性自引用（旧 `update_cxt` 无 occurs，把 spine 算进来会把
/// 可达构造子误判不可达）。结构性自引用（`x := succ x`）仍由 Rigid/
/// SumCase 等臂捕获；更深的间接环由 force 的 fuel 兜底。
fn val_mentions_lvl(spine: &Spine, defs: &[V], v: V, x: u32) -> bool {
    match v_tag(v) {
        0 => v_lvl_of(v) == x,
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            // Flex 头的链 = 参考版 `Val::Flex(m, sp)` 的打包形态：**整条
            // 视为不透明**（实参不扫，见函数注释——探测的 fresh meta 会把
            // 绑定器（含被解变量）收进 spine，不是结构性自引用）
            if v_tag(hd) == 5 {
                return false;
            }
            let head_hit = match v_tag(hd) {
                0 => v_lvl_of(hd) == x,
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
                    _ => false,
                },
                _ => false,
            };
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args);
            head_hit || args.iter().any(|(a, _)| val_mentions_lvl(spine, defs, *a, x))
        }
        // Flex 头（裸 meta 立即数）：实参视为不透明（见函数注释）
        5 => false,
        1 | 4 => false, // Lam/Pi 闭包跳过（参考版同）
        3 | 6 => false,
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Prim => false,
            // VSub：只扫解值自身的结构，**不扫 σ 的映射值**
            XCell::VSub { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Obj { val, .. } => val_mentions_lvl(spine, defs, *val, x),
            XCell::Sum { params, .. } => params.iter().any(|p| {
                val_mentions_lvl(spine, defs, p.val, x)
                    || val_mentions_lvl(spine, defs, p.ty, x)
            }),
            XCell::SumCase { typ, datas, .. } => {
                val_mentions_lvl(spine, defs, *typ, x)
                    || datas.iter().any(|d| val_mentions_lvl(spine, defs, d.val, x))
            }
            XCell::Match {
                scrutinee, env, ..
            } => {
                let mut hit = val_mentions_lvl(spine, defs, *scrutinee, x);
                if !hit {
                    let mut n = env.binds;
                    while let Some(e) = n {
                        if val_mentions_lvl(spine, defs, e.val, x) {
                            hit = true;
                            break;
                        }
                        n = e.next;
                    }
                }
                if !hit {
                    'outer: for k in 0..env.flat_len {
                        if val_mentions_lvl(
                            spine,
                            defs,
                            defs[(env.flat_base + env.flat_len - 1 - k) as usize],
                            x,
                        ) {
                            hit = true;
                            break 'outer;
                        }
                    }
                }
                hit
            }
        },
        _ => false,
    }
}

/// 特化合一的进行时状态（参考版 `SpecSolve` 同构）。`solvable` = 本子句
/// 可解的 rigid 层级；`acc` = 已解出的替换。
pub(crate) struct SpecSolve<'a> {
    pub(crate) solvable: &'a [u32],
    pub(crate) acc: Rc<SubstV>,
}

/// 精化传播的展开燃料（线程局部：每个测试/运行线程独立，与参考版
/// `Infer::unify_fuel` 的"每次运行新建"口径一致）。仅 frcs 的 lookup 命中
/// 点燃烧；外部入口（unify_catch / nf / check_pm / 模式编译）充值。
const UNIFY_FUEL: u32 = 4096;
thread_local! {
    static PM_FUEL: std::cell::Cell<u32> = const { std::cell::Cell::new(UNIFY_FUEL) };
}

fn refuel() {
    PM_FUEL.with(|c| c.set(UNIFY_FUEL));
}

/// 燃料池是否已耗尽（探测失败侧的观察口：fuel 耗尽的失败是预算问题而非
/// 结构冲突——probe_accessible 尾部据此把失败按"可达"处理，保守地要求
/// 覆盖。L07 2026-09-18 评审修复 2 的同步移植）。
fn fuel_exhausted() -> bool {
    PM_FUEL.with(|c| c.get() == 0)
}

#[inline]
fn burn() -> bool {
    PM_FUEL.with(|c| {
        let f = c.get();
        if f == 0 {
            false
        } else {
            c.set(f - 1);
            true
        }
    })
}


/// 复合环境：**平坦 def 区域**（elaborator 的 define 链，指入每轮
/// [`Machine::defs`]；tip 环境原地追加，`nth` O(1)；**非 tip 环境**
/// （λ 体内的 define 先占位后、外层再 define）回落到 binder 链——索引
/// 语义一致，仅查链 O(链深)）+ **持久 binder 链表**。机制与论证同 L03-L06。
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    flat_base: u32,
    flat_len: u32,
    binds: Option<&'a EnvCons<'a>>,
}

const EMPTY_ENV: Env<'static> = Env {
    flat_base: 0,
    flat_len: 0,
    binds: None,
};

/// 环境链表节点（bump 内持久链表，头 = 最内层绑定）。
pub(crate) struct EnvCons<'a> {
    val: V,
    next: Option<&'a EnvCons<'a>>,
}

/// `i < binds 深度` → 走链；否则读平坦 def 区域。
#[inline]
pub(crate) fn env_nth(defs: &[V], env: Env<'_>, i: u32) -> V {
    let mut nb = env.binds;
    let mut j = 0u32;
    while let Some(e) = nb {
        if j == i {
            return e.val;
        }
        j += 1;
        nb = e.next;
    }
    defs[(env.flat_base + env.flat_len - 1 - (i - j)) as usize]
}

/// 环境总槽数（链深 + 平坦区）。
#[inline]
pub(crate) fn env_len(env: Env<'_>) -> u32 {
    let mut n = env.flat_len;
    let mut nb = env.binds;
    while let Some(e) = nb {
        n += 1;
        nb = e.next;
    }
    n
}

/// 环境全部槽按 [`env_nth`] 的下标序单趟拷进 `out`：链段直走 +
/// 平坦区倒序读。`(0..env_len).map(env_nth)` 对链段每次从头重走，是
/// O(d²)；本函数一趟 O(d)（同 L07/L08 的 struct_eq / val_mentions_lvl 口径）。
#[inline]
pub(crate) fn env_collect(defs: &[V], env: Env<'_>, out: &mut Vec<V>) {
    let mut nb = env.binds;
    while let Some(e) = nb {
        out.push(e.val);
        nb = e.next;
    }
    for k in 0..env.flat_len {
        out.push(defs[(env.flat_base + env.flat_len - 1 - k) as usize]);
    }
}

/// 环境扩展（**binder 链**：bind / β / 瞬时求值扩展）——O(1)。
#[inline]
pub(crate) fn env_ext<'a>(bump: &'a Bump, env: Env<'a>, v: V) -> Env<'a> {
    Env {
        flat_base: env.flat_base,
        flat_len: env.flat_len,
        binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
    }
}

/// 环境扩展（**平坦 def 区域**：elaborator 的 define）。tip 环境原地追加
/// （chain 负载的 O(1) 线性保证）；其余回落 binder 链。tip 判定要求 binds
/// 为空：λ 体内 define 比链上 binder 更新，必须落在链头——追加平坦区会被
/// env_nth/AppPrun 的链优先序排到 binder 之后（de Bruijn 次序互换，错位值
/// 流进 solve 即错解/误报）。
#[inline]
pub(crate) fn env_ext_defs<'a>(
    bump: &'a Bump,
    defs: &mut Vec<V>,
    env: Env<'a>,
    v: V,
) -> Env<'a> {
    if env.binds.is_none() && env.flat_base + env.flat_len == defs.len() as u32 {
        defs.push(v);
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len + 1,
            binds: env.binds,
        }
    } else {
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len,
            binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
        }
    }
}

/// 闭包单元：λ 的名字 + icit（quote 产出带 icit 的 `Lam`）+ env + 体。
///
/// 对齐：`v_clo` 以 `ptr | 1` 编码、`v_clo_of` 以 `& !7` 解码，要求 ≥8 对齐。
/// 本单元不含 u64 字段，wasm32 上仅 4 对齐（`&str`/`Env`/`&Tm`），故显式
/// `repr(align(8))`（64 位上本就 8 对齐，零行为变化）。
#[repr(align(8))]
pub(crate) struct CloCell<'a> {
    name: &'a str,
    icit: Icit,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

/// Π 值单元：名字 + icit + 定义域值 + 余定义域闭包（内联，一次分配）。
pub(crate) struct PiCell<'a> {
    name: &'a str,
    icit: Icit,
    dom: V,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

// packed-word 指针编码（`ptr | tag`，tag ∈ {1,4,7}）的解引用走 `v.0 & !7`，
// 要求单元地址低 3 位为 0 ⇒ align_of ≥ 8。wasm32 上 `&str` 仅 4 对齐：
// `XCell`/`CloCell`（均无 u64 字段）靠 `#[repr(align(8))]` 钉住；`PiCell`
// 含 `dom: V`(u64) 天然 ≥8，断言只是把不变式写进编译期（防未来改字段跌破）。
// `EnvCons` 不直接进 packed 字，断言为防御性。
const _: () = assert!(std::mem::align_of::<XCell<'static>>() >= 8);
const _: () = assert!(std::mem::align_of::<CloCell<'static>>() >= 8);
const _: () = assert!(std::mem::align_of::<PiCell<'static>>() >= 8);
const _: () = assert!(std::mem::align_of::<EnvCons<'static>>() >= 8);

// spine 栈（扁平中性）
// --------------------------------------------------------------------------------

/// 链头种类（`Entry.hk`）：push 时随函数侧传播，O(1) 判定链头是 Flex
/// （force 的唯一展开臂）/ 卡住投影 Obj（unify 的位相等捷径对它关闭）还是
/// Rigid（force 直接原样返回）。链头只可能是这三种（其余形态 v_app 即
/// panic，进不了链）。
const HK_OTHER: u8 = 0;
const HK_FLEX: u8 = 1;
const HK_OBJ: u8 = 2;

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`hk` 记录链头种类（push 时随函数侧传播）。
struct Entry {
    f: V,
    a: V,
    icit: Icit,
    len: u32,
    base: u32,
    hk: u8,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`hk` 随函数侧传播：
    /// 裸单元直查种类，既有链延伸保持原种类（顶端槽已记下头种类）。
    #[inline]
    fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let hk = match v_tag(f) {
            5 => HK_FLEX,
            7 => match v_xcell_of(f) {
                XCell::Obj { .. } => HK_OBJ,
                _ => HK_OTHER,
            },
            2 => self.stack[v_spine_of(f)].hk,
            _ => HK_OTHER,
        };
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry { f, a, icit, len, base, hk });
        v_spine(idx)
    }

    /// 沿 `f` 指针走到链的最底层头（f 指针严格指向更早的槽位，必终止）。
    #[inline]
    fn spine_head(&self, h: usize) -> V {
        let mut cur = h;
        loop {
            let f = self.stack[cur].f;
            if v_tag(f) == 2 {
                cur = v_spine_of(f);
            } else {
                return f;
            }
        }
    }

    /// 收集链的**引用语义实参**（逆应用序：先 `h.a` 再沿 `f` 下行）。
    #[inline]
    fn collect_args(&self, h: usize, out: &mut Vec<(V, Icit)>) {
        let mut cur = h;
        loop {
            let e = &self.stack[cur];
            out.push((e.a, e.icit));
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
            } else {
                return;
            }
        }
    }

    /// 链长（元数预检：长度失配 / 元数不足时不收集、零分配）。
    #[inline]
    fn spine_len(&self, h: usize) -> usize {
        let mut cur = h;
        let mut n = 1;
        loop {
            let e = &self.stack[cur];
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
                n += 1;
            } else {
                return n;
            }
        }
    }

    /// force 后的未解 flex 探测：`tag 5`（空 spine）或 spine 头是 `Meta`。
    /// 返回 meta 号并把逆应用序实参（带 icit）收进 `out`。要求调用方先 force。
    fn flex_of(&self, v: V, out: &mut Vec<(V, Icit)>) -> Option<u32> {
        match v_tag(v) {
            5 => Some(v_meta_of(v)),
            2 => {
                let h = v_spine_of(v);
                if self.stack[h].hk != HK_FLEX {
                    return None;
                }
                let hd = self.spine_head(h);
                self.collect_args(h, out);
                Some(v_meta_of(hd))
            }
            _ => None,
        }
    }
}

/// 值是否 Flex（裸未解 meta 立即数或 meta 头的链——链查顶端槽的 `hk`，
/// O(1)，无需沿链走底）。
#[inline]
fn is_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 => true,
        2 => spine.stack[v_spine_of(v)].hk == HK_FLEX,
        _ => false,
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。Clone 供 temp-infer 探测的
/// 快照换入换出。
#[derive(Clone)]
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V),
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(_) => v_meta(m),
    }
}

/// 从实参值取字面量内容（非字面量 → None）。返回值的 `'a` 与入参无
/// link——健全性依赖全局不变式：所有 `V` 的 XCell 都指向**当前轮的
/// bump**或 `'static` 钉串，跨轮 `bump.reset()` 前一切句柄已消亡。
#[inline]
fn lit_of<'a>(v: V) -> Option<&'a str> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）
/// 再查构造子字段。其余返回 None。（参考版 eval 的 Tm::Obj 臂自带
/// unwrap-panic 语义，调用方处理；本函数只在命中时给出值。）
fn project<'a>(v: V, name: &str) -> Option<V> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Sum { params, .. } => {
                params.iter().find(|p| p.name == name).map(|p| p.val)
            }
            XCell::SumCase { typ, datas, .. } => {
                let params = match v_xcell_of(*typ) {
                    XCell::Sum { params, .. } => params,
                    _ => return None,
                };
                params
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.val)
                    .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
            }
            _ => None,
        },
        _ => None,
    }
}

/// 独立应用（eval_iter 之外的 v_app：force 的解值展开等）。λ → β；其余
/// 形态逐项对齐参考版 v_app：Rigid/Flex（裸或链）与卡住投影 Obj → spine
/// 压栈；字面量 / Prim / U / Π / LiteralType / Sum / SumCase / 卡住 match
/// → panic（"impossible apply"，参考版同款——两版同时不可达 / 同时
/// panic，判定一致）。
fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    f: V,
    a: V,
    i: Icit,
) -> V {
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, c.body)
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Obj { .. } => spine.push(f, a, i),
            // 精化包裹的值先推开再分发（eval(App) 等不经 force 的调用点会
            // 把 VSub 头送进来——如臂上下文里 Var 引用了被解槽；force 顶层
            // 不再产出 VSub，递归必终止）
            XCell::VSub { .. } => {
                let ff = force(bump, spine, defs, metas, globals, f);
                return vapp1(
                    bump, spine, work, vals, icits, defs, metas, globals, ff, a, i,
                );
            }
            _ => panic!("impossible apply"),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}

/// η 展开的可应用性守卫（参考版 `unification::v_applicable` 的快版对应，

/// L11 同款）：只有 `vapp1` 不会 panic 的形态能吃 η 新变量。tag 7 仅
/// `Obj` 可（`Sum`/`SumCase`/`Prim` → panic）；tag 3(U)/4(Pi)/6(Lit) 不可；
/// 其余（Rigid 0 / Clo 1 / 链 2 / Flex 5）可。防止 λ 值以类型/值身份流入
/// unify 的 η 臂时触发 `impossible apply`（守卫失败落后续臂判败，与参考
/// 版守卫后落 `_` → Err 同判定）。

#[inline]
fn vapp_ok(v: V) -> bool {
    match v_tag(v) {
        3 | 4 | 6 => false,
        7 => matches!(v_xcell_of(v), XCell::Obj { .. }),
        _ => true,
    }
}

// force（迭代；L09 参考版只有 Flex 臂）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。参考版 `Infer::force`
/// 只有一个 Flex 臂（已解 → 展开应用；未解原样）——无 pm 精化读点展开、
/// 无 decl unfold、无 Match 重选、无投影归约。无燃料（meta 解由 occurs
/// check 保证无环，参考版同款裸递归）。
///
/// 内部的 eval_iter 调用用**本调用私有的草稿栈**：外层 eval/unify 循环的
/// work/vals 不能被清空（force 可能在它们循环体中途被调用，且经 eval_aux
/// 与本函数互递归）。L04-L06 的 force 借用调用方的栈，是因为那几章的
/// eval_iter 不回调 force——这个差异**不是**漏同步，别往那方向改。四个
/// `Vec::new()` 本身不分配，只有真正下钻时才增长，早退路径零成本。
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    v0: V,
) -> V {
    let mut v = v0;
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                _ => return v,
            },
            2 => {
                let h = v_spine_of(v);
                if spine.stack[h].hk != HK_FLEX {
                    // Rigid / Obj 头的链：卡住（参考版 force 无对应臂）。
                    // O(1) 读顶端槽种类，省去非 flex 链的整趟走底
                    return v;
                }
                let hd = spine.spine_head(h);
                // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                // 每步都可能 β（参考版 vAppSp 逐步 vApp 同款）
                match &metas[v_meta_of(hd) as usize] {
                    MetaEntry::Unsolved(_) => return v,
                    MetaEntry::Solved(sol, _) => {
                        args.clear();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &(a, i) in args.iter().rev() {
                            t = vapp1(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                globals, t, a, i,
                            );
                        }
                        v = t;
                    }
                }
            }
            // 显式替换（dpm-nbe `frc`）：把模式精化的解推进值的结构。入口
            // 不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的
            // Rigid 臂 lookup 命中时烧 1）。fuel 耗尽的降级点也在该处。
            7 => {
                if let XCell::VSub { val, sub } = v_xcell_of(v) {
                    return frcs(bump, spine, defs, metas, globals, sub, *val);
                }
                return v;
            }
            _ => return v,
        }
    }
}

/// 把替换 `σ` 推进值 `v` 的结构（dpm-nbe `frcS`；参考版 `Infer::frcs`
/// 的快版对应）。槽位纪律：σ 对 spine / Sum/SumCase 槽只**包裹**，绝不
/// 推进物化——槽位引用是作用域事实，物化会破坏后续 solve 的 invert。
#[allow(clippy::too_many_arguments)]
fn frcs<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    sub: &Rc<SubstV>,
    v0: V,
) -> V {
    if sub.is_empty() {
        return force(bump, spine, defs, metas, globals, v0);
    }
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    match v_tag(v0) {
        // 内层先应用、外层后应用：组合后一次推进（frcS (subst sb sb') v）
        7 => match v_xcell_of(v0) {
            XCell::VSub { val, sub: sub2 } => {
                let composed = SubstV::compose(sub, sub2);
                frcs(bump, spine, defs, metas, globals, &composed, *val)
            }
            // 中性头单元：包裹后交回 force 重走既有臂。Sum/SumCase 槽位只
            // **包裹**不推进。
            XCell::Sum { name, params, cases } => {
                let ps: Vec<SumParamV<'_>> = params
                    .iter()
                    .map(|p| SumParamV {
                        name: p.name,
                        val: wrap_sub(bump, sub, p.val),
                        ty: wrap_sub(bump, sub, p.ty),
                        icit: p.icit,
                    })
                    .collect();
                v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                }))
            }
            XCell::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let ds: Vec<SumDataV<'_>> = datas
                    .iter()
                    .map(|d| SumDataV {
                        name: d.name,
                        val: wrap_sub(bump, sub, d.val),
                        icit: d.icit,
                    })
                    .collect();
                v_xcell(bump.alloc(XCell::SumCase {
                    typ: wrap_sub(bump, sub, *typ),
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                }))
            }
            XCell::Lit(_) => v0,
            XCell::Prim => force(bump, spine, defs, metas, globals, v0),
            XCell::Obj { val, name } => {
                let inner = frcs(bump, spine, defs, metas, globals, sub, *val);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    globals,
                    v_xcell(bump.alloc(XCell::Obj { val: inner, name })),
                )
            }
            // scrutinee **推进**（分支重选需要解出的构造子值——L09 的分支
            // 重选发生在 eval 的 Tm::Match 臂：scrutinee 经 force 推开 σ 后
            // 是构造子值即选分支）；捕获 env 只包裹。
            XCell::Match {
                scrutinee, env, cases,
            } => {
                let s2 = frcs(bump, spine, defs, metas, globals, sub, *scrutinee);
                let env2 = frcs_env(bump, defs, sub, env);
                force(
                    bump,
                    spine,
                    defs,
                    metas,
                    globals,
                    v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env: env2,
                        cases,
                    })),
                )
            }
        },
        // 裸 Rigid 的读点：lookup 命中（真正的精化传播）烧 1 fuel；fuel
        // 耗尽按未解处理（返回裸 rigid）。未命中零成本直通。
        0 => match SubstV::lookup_hit(bump, spine, defs, sub, v_lvl_of(v0)) {
            Some(hit) => {
                if !burn() {
                    return v0;
                }
                force(bump, spine, defs, metas, globals, hit)
            }
            None => v0,
        },
        // spine 链分派：Rigid 头 = 解析应用（对齐 dpm-nbe 的
        // `napp (lookupSub sb v) (frcS sb sp)`）；Flex/Obj 头 = 槽位只包裹，
        // 重建链后交回 force。
        2 => {
            let h = v_spine_of(v0);
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                let x = v_lvl_of(hd);
                let mut head = match SubstV::lookup_hit(bump, spine, defs, sub, x) {
                    Some(hit) => {
                        if !burn() {
                            return v0;
                        }
                        force(bump, spine, defs, metas, globals, hit)
                    }
                    None => v_lvl(x),
                };
                if !vapp_ok(head) {
                    return v0;
                }
                let mut args: Vec<(V, Icit)> = Vec::new();
                spine.collect_args(h, &mut args);
                for &(u, i) in args.iter().rev() {
                    head = vapp1(
                        bump, spine, &mut work, &mut vals, &mut icits, defs, metas, globals, head,
                        wrap_sub(bump, sub, u), i,
                    );
                }
                head
            } else {
                // **先查 tag 再解引用**：hd 可以是裸 rigid/meta 立即数
                let base = if v_tag(hd) == 7 {
                    match v_xcell_of(hd) {
                        XCell::Obj { val, name } => v_xcell(bump.alloc(XCell::Obj {
                            val: frcs(bump, spine, defs, metas, globals, sub, *val),
                            name,
                        })),
                        _ => hd,
                    }
                } else {
                    hd
                };
                let mut args: Vec<(V, Icit)> = Vec::new();
                spine.collect_args(h, &mut args);
                let mut t = base;
                for &(u, i) in args.iter().rev() {
                    t = spine.push(t, wrap_sub(bump, sub, u), i);
                }
                force(bump, spine, defs, metas, globals, t)
            }
        }
        // 闭包 env 逐槽包裹；返回同型值，不再 force
        1 => {
            let c = v_clo_of(v0);
            v_clo(bump.alloc(CloCell {
                name: c.name,
                icit: c.icit,
                env: frcs_env(bump, defs, sub, &c.env),
                body: c.body,
            }))
        }
        4 => {
            let p = v_pi_of(v0);
            v_pi(bump.alloc(PiCell {
                name: p.name,
                icit: p.icit,
                dom: frcs(bump, spine, defs, metas, globals, sub, p.dom),
                // 平坦 defs 环境（定义期 cxt 环境）保持原样：其槽位是
                // `defs` 共享区的借用，转链会改变 de Bruijn 索引可达面
                // （参考版 List 表示无此问题；实测转链后 t 的 Π 体求值错位）。
                // 链式环境（subst_cxt 之后）逐槽包裹以传播精化。
                env: if p.env.binds.is_none() && p.env.flat_len > 0 {
                    p.env
                } else {
                    frcs_env(bump, defs, sub, &p.env)
                },
                body: p.body,
            }))
        }
        // 裸 flex：交回 force 走既有解链；U / LiteralType 原样
        5 => force(bump, spine, defs, metas, globals, v0),
        _ => v0,
    }
}

/// 闭包 env 逐槽包裹。包裹值不进 defs 平坦区，整体退化为 binder 链表示
/// （槽序与 `env_nth` 严格一致）。
fn frcs_env<'a>(bump: &'a Bump, defs: &[V], sub: &Rc<SubstV>, env: &Env<'a>) -> Env<'a> {
    if sub.is_empty() {
        return *env;
    }
    let n = env_len(*env);
    let mut e: Option<&'a EnvCons<'a>> = None;
    for i in (0..n).rev() {
        let v = env_nth(defs, *env, i);
        e = Some(bump.alloc(EnvCons {
            val: wrap_sub(bump, sub, v),
            next: e,
        }));
    }
    Env {
        flat_base: 0,
        flat_len: 0,
        binds: e,
    }
}

/// 合一器**参数视角**的 WHNF（参考版 `Infer::force_arg` 同款）：不推开
/// VSub 精化包裹、不做 Match 重选。逐层解包 VSub 后：裸 rigid 返回裸值；
/// 带实参的 rigid 链 / 卡住 match 返回**原值**（包裹原样保留）；其余形态
/// 全量 force。
fn force_arg<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    v: V,
) -> V {
    let mut cur = v;
    loop {
        match v_tag(cur) {
            7 => match v_xcell_of(cur) {
                XCell::VSub { val, .. } => cur = *val,
                _ => break,
            },
            _ => break,
        }
    }
    match v_tag(cur) {
        0 => cur,
        2 if v_tag(spine.spine_head(v_spine_of(cur))) == 0 => v,
        7 if matches!(v_xcell_of(cur), XCell::Match { .. }) => v,
        _ => force(bump, spine, defs, metas, globals, v),
    }
}

// 运行时分支选择（值层首匹配，无合一；L09 参考版 Compiler::eval_aux 同款）
// --------------------------------------------------------------------------------

/// 按模式首匹配。参考版语义逐句对齐：
/// - 入口 force(head)；force 后非 SumCase → 任何 Con 模式都按"不在类型构造
///   子表里"的变量模式命中（`$unknown$` + 空表）。
/// - force 后是 SumCase：typ 必须 force 成 Sum（**否则 panic**——参考版
///   `panic!("by now only can match a sum type")`）；Con 模式名不在 Sum 的
///   cases 里 → 按变量模式命中（prepend head）；名 == case_name → datas 与
///   子模式 zip（**zip 截断**）逐个递归（每步单臂表，env 累积——**head 本身
///   不 prepend**，参考版 Con 臂从 cxt 起步）；同名异构造子 → 试下一分支。
fn eval_aux<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    head: V,
    env: Env<'a>,
    cases: &'a [(PatternDetail, &'a Tm<'a>)],
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    let head = force(bump, spine, defs, metas, globals, head);
    let (case_name, datas, ctor_names): (&str, &[SumDataV<'a>], &[&str]) = if v_tag(head) == 7 {
        match v_xcell_of(head) {
            XCell::SumCase { typ, case_name, datas } => {
                // typ 槽可能被 frcs 包成 VSub（只包裹不物化）——判 Sum 前先
                // force（参考版 eval_aux 同款）
                let typ_f = force(bump, spine, defs, metas, globals, *typ);
                let cases_list = match v_xcell_of(typ_f) {
                    XCell::Sum { cases, .. } => *cases,
                    // 参考 panic：typ 不是 Sum（中性 global 下的重求值可达）
                    _ => panic!("by now only can match a sum type"),
                };
                (case_name, *datas, cases_list)
            }
            _ => ("$unknown$", &[], &[]),
        }
    } else {
        ("$unknown$", &[], &[])
    };
    for (pat, body) in cases.iter() {
        if let Some(r) = eval_aux_case(
            bump, spine, defs, metas, globals, head, case_name, datas, ctor_names, env, pat, *body,
        ) {
            return Some(r);
        }
    }
    None
}

/// 单 (模式, 分支体) 的匹配（`eval_aux` 的内层；返回 None = 试下一分支）。
/// 子模式的下钻走**完整 eval_aux**（对子值重新派生 case 信息——参考版
/// 递归同款，`[(pat.clone(), body)]` 单臂表也照克隆）。
#[allow(clippy::too_many_arguments)]
fn eval_aux_case<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    head: V,
    case_name: &str,
    datas: &[SumDataV<'a>],
    ctor_names: &[&str],
    env: Env<'a>,
    pat: &PatternDetail,
    body: &'a Tm<'a>,
) -> Option<(&'a Tm<'a>, Env<'a>)> {
    match pat {
        PatternDetail::Any(_) | PatternDetail::Bind(_) => {
            Some((body, env_ext(bump, env, head)))
        }
        PatternDetail::Con(name, subs) => {
            let in_type = ctor_names.iter().any(|c| *c == name.data);
            if !in_type {
                // 不是该类型的构造子名 → 变量模式（保守兼容；参考版首臂）
                Some((body, env_ext(bump, env, head)))
            } else if case_name == name.data {
                // datas 与子模式按序 zip（zip 截断；参考版 try_fold 同款：
                // 每步单臂完整 eval_aux，body 原样传递，env 累积——head 不
                // prepend）
                let mut cur_body = body;
                let mut cur_env = env;
                for (d, sub) in datas.iter().zip(subs.iter()) {
                    let arms1: &'a [(PatternDetail, &'a Tm<'a>)] =
                        bump.alloc([(sub.clone(), cur_body)]);
                    match eval_aux(
                        bump, spine, defs, metas, globals, d.val, cur_env, arms1,
                    ) {
                        Some((b, e)) => {
                            cur_body = b;
                            cur_env = e;
                        }
                        None => return None, // 子模式失配：试下一分支
                    }
                }
                Some((cur_body, cur_env))
            } else {
                None // 同类型不同构造子 → 试下一分支
            }
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用 + L09 变体）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包，直接 β（icit 无关）。
    ApplyKnown(V),
    /// vals 顶上是 base 值，其下 `k` 个是待应用的链头（内层最上；每个链头
    /// 的 icit 在 `icits` 侧栈平行压弹）。
    ChainWrap(u32),
    /// vals 顶是 let 绑定的值：弹出压进环境，继续求值体。
    LetBody(&'a Tm<'a>, Env<'a>),
    /// vals 顶是 Π 定义域值：弹出配余定义域闭包，压 Π 值。
    PiBody(&'a str, Icit, &'a Tm<'a>, Env<'a>),
    /// vals 顶是 `vAppPruning` 的当前值；沿 (env, pr) 平行走完剩余槽位
    /// （外层先应用，icit 取自掩码；`None` 槽跳过）。
    AppPrun(Env<'a>, Option<&'a PrCons<'a>>),
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去。
    AppPrunOne(V, Icit),
    /// vals 顶是投影接收者的值：Sum/SumCase 命中给投影值（**miss panic**，
    /// 参考版 unwrap 同款）；Rigid（裸或链）卡成 Obj；其余 panic。
    ObjSel(&'a str),
    /// vals 顶自底向上是 (v0,t0,...,v_{n-1},t_{n-1})（求值序）：装配 Sum。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamT<'a>],
        cases: &'a [&'a str],
    },
    /// vals 顶自底向上是 (typ, d0..d_{nd-1})：装配 SumCase。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
    },
    /// vals 顶是 scrutinee 的值：force 后是 SumCase → eval_aux 选分支
    /// （**None 即 panic**，参考版 unwrap 同款）；否则卡成 Match（无
    /// pending）。
    MatchSel {
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
        env: Env<'a>,
    },
}

/// 双栈迭代 eval（L06 版 + L09 变体：global 大下标、无名 Prim 的 env 双槽
/// 拼接、投影的 panic 语义、match 的编译期选择与卡住停等）。
#[allow(clippy::too_many_arguments)]
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => {
                // 越过哨兵的下标查 global 表（参考版 eval 的 Var 臂：env 走
                // 完才落 global——env 槽数远小于哨兵，次序无观察面）
                if *i >= GLOBAL_BASE {
                    vals.push(globals[(*i - GLOBAL_BASE) as usize]);
                } else {
                    vals.push(env_nth(defs, env, *i));
                }
            }
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U(l), _) => vals.push(v_u(*l)),
            W::Tm(Tm::LiteralType, _) => vals.push(v_lit_ty()),
            W::Tm(Tm::LiteralIntro(s), _) => vals.push(v_xcell(bump.alloc(XCell::Lit(s)))),
            // builtin 体：env 前两槽全为字面量 → 拼接；否则卡住 `Prim`（无
            // spine——v_app 对它 panic，永无 Prim 头的链）。env 不足两槽时
            // env_nth 越界 panic（参考版 unwrap 同款崩溃）。
            W::Tm(Tm::Prim, env) => {
                let b = env_nth(defs, env, 0);
                let a = env_nth(defs, env, 1);
                match (lit_of(a), lit_of(b)) {
                    (Some(a), Some(b)) => {
                        let len = a.len() + b.len();
                        let ptr = bump
                            .alloc_layout(std::alloc::Layout::from_size_align(len, 1).unwrap())
                            .as_ptr();
                        // SAFETY: a/b 都是 &str（合法 UTF-8）；两段完整序列按
                        // 字节拼接仍是合法 UTF-8，不会引入跨边界截断的码点
                        let s = unsafe {
                            std::ptr::copy_nonoverlapping(a.as_ptr(), ptr, a.len());
                            std::ptr::copy_nonoverlapping(b.as_ptr(), ptr.add(a.len()), b.len());
                            std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len))
                        };
                        vals.push(v_xcell(bump.alloc(XCell::Lit(s))));
                    }
                    _ => vals.push(v_xcell(bump.alloc(XCell::Prim))),
                }
            }
            W::Tm(Tm::Pi(name, icit, dom, cod), env) => {
                work.push(W::PiBody(name, *icit, cod, env));
                work.push(W::Tm(dom, env));
            }
            W::Tm(Tm::Let(_, _, t, u), env) => {
                work.push(W::LetBody(u, env));
                work.push(W::Tm(t, env));
            }
            W::Tm(Tm::Meta(m), _) => vals.push(meta_val_of(metas, *m)),
            W::Tm(Tm::AppPruning(head, pr), env) => {
                work.push(W::AppPrun(env, *pr));
                work.push(W::Tm(head, env));
            }
            // 投影：求值接收者（不 force——参考版同）。Sum/SumCase 命中给
            // 投影值（miss panic，参考版 unwrap 同款）；Rigid（裸或链）卡成
            // Obj；其余形态 panic（参考版 "impossible" 臂同款）。
            W::Tm(Tm::Obj(h, name), env) => {
                work.push(W::ObjSel(name));
                work.push(W::Tm(h, env));
            }
            // enum 本体：逐参数求值（值 + 类型）后装配
            W::Tm(Tm::Sum(name, params, cases), env) => {
                work.push(W::SumAsm { name, params, cases });
                for p in params.iter().rev() {
                    work.push(W::Tm(p.ty, env));
                    work.push(W::Tm(p.val, env));
                }
            }
            W::Tm(
                Tm::SumCase {
                    typ,
                    case_name,
                    datas,
                },
                env,
            ) => {
                work.push(W::SumCaseAsm { case_name, datas });
                for d in datas.iter().rev() {
                    work.push(W::Tm(d.val, env));
                }
                work.push(W::Tm(typ, env));
            }
            // match：求值 scrutinee → force → 选分支 / 卡住（参考版 eval 的
            // Tm::Match 臂：SumCase + eval_aux 命中给分支体（**None 即
            // panic**）；其它 neutral 卡 Match，无 pending）
            W::Tm(Tm::Match(s, cases), env) => {
                work.push(W::MatchSel { cases, env });
                work.push(W::Tm(s, env));
            }
            W::Tm(app @ Tm::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals（icit 进侧栈）
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a, i) = match tm {
                        Tm::App(f, a, i) => (f, a, i),
                        base => {
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    let i = *i;
                    match f {
                        Tm::Var(ix) => {
                            let vf = if *ix >= GLOBAL_BASE {
                                globals[(*ix - GLOBAL_BASE) as usize]
                            } else {
                                env_nth(defs, env, *ix)
                            };
                            if v_tag(vf) == 1 {
                                // β 岔路：函数值已在手上（闭包），ApplyKnown
                                // 直接管 β（icit 无关）；heads>0 时 ChainWrap
                                // 照旧收拢
                                if heads > 0 {
                                    work.push(W::ChainWrap(heads));
                                }
                                work.push(W::ApplyKnown(vf));
                                work.push(W::Tm(a, env));
                                break;
                            }
                            vals.push(vf);
                            icits.push(i);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Apply(i));
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        }
                    }
                }
            }
            W::Apply(i) => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let env = env_ext(bump, c.env, va);
                    work.push(W::Tm(c.body, env));
                } else {
                    let r = vapp1(
                        bump, spine, work, vals, icits, defs, metas, globals, vf, va, i,
                    );
                    vals.push(r);
                }
            }
            W::ApplyKnown(vf) => {
                let va = vals.pop().expect("eval 栈：ApplyKnown 缺实参");
                let c = v_clo_of(vf);
                let env = env_ext(bump, c.env, va);
                work.push(W::Tm(c.body, env));
            }
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    let i = icits.pop().expect("eval 栈：ChainWrap 缺 icit");
                    v = vapp1(
                        bump, spine, work, vals, icits, defs, metas, globals, vf, v, i,
                    );
                }
                vals.push(v);
            }
            W::LetBody(u, env) => {
                let vt = vals.pop().expect("eval 栈：LetBody 缺绑定值");
                work.push(W::Tm(u, env_ext(bump, env, vt)));
            }
            W::PiBody(name, icit, cod, env) => {
                let dom = vals.pop().expect("eval 栈：PiBody 缺定义域");
                let cell = bump.alloc(PiCell {
                    name,
                    icit,
                    dom,
                    env,
                    body: cod,
                });
                vals.push(v_pi(cell));
            }
            W::AppPrun(env, bds) => match bds {
                None => {
                    // 与 reference 的 (None, None) 对齐：掩码先行耗尽
                    debug_assert!(env.binds.is_none() && env.flat_len == 0);
                }
                Some(b) if env.binds.is_none() && b.slot.is_none() => {
                    // O(1) 跳段：binds 耗尽后剩余链只剩 define 槽。
                    assert!(env.flat_len >= b.none_run);
                    work.push(W::AppPrun(
                        Env {
                            flat_len: env.flat_len - b.none_run,
                            ..env
                        },
                        b.after_run,
                    ));
                }
                Some(b) => {
                    // 内层绑定 = 链头；链耗尽后走平坦 def 区域末端。先跑
                    // 余下槽位（外层），再应用本槽（内层最后应用）
                    let (arg, rest) = if let Some(e) = env.binds {
                        (
                            b.slot.map(|_| e.val),
                            Env {
                                binds: e.next,
                                ..env
                            },
                        )
                    } else if env.flat_len > 0 {
                        let v = defs[(env.flat_base + env.flat_len - 1) as usize];
                        (
                            b.slot.map(|_| v),
                            Env {
                                flat_len: env.flat_len - 1,
                                ..env
                            },
                        )
                    } else {
                        panic!("impossible") // env 与 pr 错位
                    };
                    match (arg, b.slot) {
                        (Some(a), Some(i)) => work.push(W::AppPrunOne(a, i)),
                        (None, Some(_)) => panic!("impossible"), // env 短于 pr
                        _ => {}
                    }
                    work.push(W::AppPrun(rest, b.next));
                }
            },
            W::AppPrunOne(arg, i) => {
                let v = vals.pop().expect("eval 栈：AppPrunOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let env = env_ext(bump, c.env, arg);
                    work.push(W::Tm(c.body, env));
                } else {
                    let r = vapp1(
                        bump, spine, work, vals, icits, defs, metas, globals, v, arg, i,
                    );
                    vals.push(r);
                }
            }
            W::ObjSel(name) => {
                let v = vals.pop().expect("eval 栈：ObjSel 缺接收者");
                // 精化包裹的接收者（subst_cxt 包裹的 env 槽会以 VSub 流出）
                // 先推开 σ 再判形态（参考版 eval 的 Obj 臂同款）；force 对
                // 非 VSub 是恒等，旧行为不变。
                let v = if v_tag(v) == 7 && matches!(v_xcell_of(v), XCell::VSub { .. }) {
                    force(bump, spine, defs, metas, globals, v)
                } else {
                    v
                };
                match v_tag(v) {
                    7 => match v_xcell_of(v) {
                        XCell::Sum { params, .. } => {
                            match params.iter().find(|p| p.name == name) {
                                Some(p) => vals.push(p.val),
                                None => panic!("impossible"), // 参考 unwrap：字段必在
                            }
                        }
                        XCell::SumCase { typ, datas, .. } => {
                            // typ 必须是 Sum（参考版 match 同款，否则
                            // panic "impossible"）；索引参数优先，字段在后。
                            // typ 槽可能被 frcs 包成 VSub（只包裹不物化）——
                            // 判 Sum 前先 force（参考版 eval 的 Obj 臂同款）。
                            let typ_f = force(bump, spine, defs, metas, globals, *typ);
                            let sparams = match v_xcell_of(typ_f) {
                                XCell::Sum { params, .. } => *params,
                                _ => panic!("impossible"),
                            };
                            match sparams
                                .iter()
                                .find(|p| p.name == name)
                                .map(|p| p.val)
                                .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
                            {
                                Some(p) => vals.push(p),
                                None => panic!("impossible"),
                            }
                        }
                        _ => panic!("impossible"),
                    },
                    // Rigid（裸或链）：卡住投影（参考版 `x @ Val::Rigid` 臂）
                    0 => vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name }))),
                    2 => {
                        let hd = spine.spine_head(v_spine_of(v));
                        if v_tag(hd) == 0 {
                            vals.push(v_xcell(bump.alloc(XCell::Obj { val: v, name })));
                        } else {
                            panic!("impossible"); // Flex/Obj 头接收者：参考版同 panic
                        }
                    }
                    _ => panic!("impossible"),
                }
            }
            W::SumAsm { name, params, cases } => {
                // vals 槽序 = v0, t0, v1, t1, ...（先压者在底）→ pop 序是
                // t_{n-1}, v_{n-1}, ...：按 params 逆序逐槽收进 ps，再整体
                // 反转回自然序——单缓冲，省掉 items 中转 + 二次下标拷贝
                let mut ps: Vec<SumParamV<'_>> = Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = vals.pop().expect("eval 栈：SumAsm 缺参数");
                    let val = vals.pop().expect("eval 栈：SumAsm 缺参数");
                    ps.push(SumParamV {
                        name: p.name,
                        val,
                        ty,
                        icit: p.icit,
                    });
                }
                ps.reverse();
                vals.push(v_xcell(bump.alloc(XCell::Sum {
                    name,
                    params: bump.alloc_slice_fill_iter(ps),
                    cases,
                })));
            }
            W::SumCaseAsm { case_name, datas } => {
                // datas 字段在 vals 栈顶（typ 先压在底）：逆序 pop 落槽后
                // 反转，typ 最后 pop
                let mut ds: Vec<SumDataV<'_>> = Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = vals.pop().expect("eval 栈：SumCaseAsm 缺字段");
                    ds.push(SumDataV {
                        name: d.name,
                        val,
                        icit: d.icit,
                    });
                }
                ds.reverse();
                let typ = vals.pop().expect("eval 栈：SumCaseAsm 缺 typ");
                vals.push(v_xcell(bump.alloc(XCell::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                })));
            }
            W::MatchSel { cases, env } => {
                let sv = vals.pop().expect("eval 栈：MatchSel 缺 scrutinee");
                let s2 = force(bump, spine, defs, metas, globals, sv);
                if v_tag(s2) == 7 && matches!(v_xcell_of(s2), XCell::SumCase { .. }) {
                    match eval_aux(bump, spine, defs, metas, globals, s2, env, cases) {
                        Some((body_tm, env2)) => {
                            // 分支选中：体在本 eval 循环里尾推
                            work.push(W::Tm(body_tm, env2));
                        }
                        // 参考 unwrap：编译期已保证可穷尽，运行时无臂可命中
                        // 即崩溃（两版同崩，判定一致）
                        None => panic!("match: no branch matched at runtime"),
                    }
                } else {
                    vals.push(v_xcell(bump.alloc(XCell::Match {
                        scrutinee: s2,
                        env,
                        cases,
                    })));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；L09 变体）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01/L04/L05/L06；quote 不产
/// `AppPruning`（项层洞形态，值层不存在）。L09 增量：`Obj1` / `SumAsm` /
/// `SumCaseAsm` 装配任务；`Match` 直接内联处理（分支体在"捕获 env + fresh
/// rigid 槽"下用**中性 global 视图**重求值再以真实表 quote——参考版
/// quote 的 Match 臂：avoid_recursive 克隆只作用于 eval，quote 用 self）。
enum QJob<'a> {
    /// 引一个值（先 force）。
    Q(V, u32),
    /// done 栈顶是体，包一层 Lam（名字与 icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合一个 Pi（icit 在 PiCell 里）。
    Pi1(&'a PiCell<'a>),
    /// 先 eval（引出闭包/余定义域的体）再引。
    EvalQ(&'a Tm<'a>, Env<'a>, u32),
    /// done 栈顶两个（先 f 后 a），合一个 App（icit 随任务携带）。
    App1(Icit),
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(key, level)` 结果，入表后放回。
    MemoStore(u64, u32),
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同一变量 / 同一未解
    /// meta 时用共享节点，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: u32,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Tm<'a>>,
        prev: Option<&'a Tm<'a>>,
    },
    /// done 栈顶是投影接收者的引读：包 `Tm::Obj`。
    Obj1(&'a str),
    /// done 栈顶自底向上是 (v0,t0,...)：装配 Tm::Sum（元数据取值层槽）。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
    },
    /// done 栈顶自底向上是 (typ, d0..)：装配 Tm::SumCase（元数据取值层槽）。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
    },
}

/// (值打包字, quote level) → 已引结果子树。icit 不进键：它随 `V` 指向的
/// 单元/槽位携带，同一打包字在同一 level 的 quote 产出（含 icit）唯一。
/// tag 7 的变体（Match/Sum/…）不进表：它们的引读依赖中性 global 视图与
/// meta 状态（参考版无 quote 记忆化，保守起见对新增值形态保持无记忆化
/// 口径）。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote（L06 版 + LiteralType/LiteralIntro/Prim/Obj/Sum/SumCase/
/// Match 臂；L09：tag 0 的大下标直通、tag 3 带层级）。
#[allow(clippy::too_many_arguments)]
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    neutral: &[V],
    level0: u32,
    v0: V,
    mut memo: Option<&mut QuoteMemo<'a>>,
) -> &'a Tm<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, level0));
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v0, level) => {
                // 先 force（metacontext 在 quote 期间冻结，同键同结果）
                let v = force(bump, spine, defs, metas, globals, v0);
                match v_tag(v) {
                    0 => {
                        let l = v_lvl_of(v);
                        // 全局层级（越过哨兵）原样产出大下标 Var（参考版
                        // lvl2ix 同款）；局部层级 level - l - 1
                        if l >= GLOBAL_BASE {
                            done.push(bump.alloc(Tm::Var(l)));
                        } else {
                            done.push(bump.alloc(Tm::Var(level - l - 1)));
                        }
                    }
                    1 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let c = v_clo_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, c.env, v_lvl(level));
                        tasks.push(QJob::Lam1(c.name, c.icit));
                        tasks.push(QJob::EvalQ(c.body, env, level + 1));
                    }
                    5 => done.push(bump.alloc(Tm::Meta(v_meta_of(v)))),
                    3 => done.push(bump.alloc(Tm::U(v_u_of(v)))),
                    // 字面量类型与字面量值（叶子，无 memo 收益）
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        XCell::Prim => done.push(bump.alloc(Tm::Prim)),
                        // 防御：正常路径 force 后顶层不会是 VSub（frcs 的
                        // 降级点是返回裸 rigid）——解包打印内层
                        XCell::VSub { val, .. } => {
                            tasks.push(QJob::Q(*val, level));
                        }
                        XCell::Obj { val, name } => {
                            tasks.push(QJob::Obj1(name));
                            tasks.push(QJob::Q(*val, level));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                        } => {
                            tasks.push(QJob::SumAsm {
                                name,
                                params,
                                cases,
                            });
                            for p in params.iter().rev() {
                                tasks.push(QJob::Q(p.ty, level));
                                tasks.push(QJob::Q(p.val, level));
                            }
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                        } => {
                            tasks.push(QJob::SumCaseAsm { case_name, datas });
                            for d in datas.iter().rev() {
                                tasks.push(QJob::Q(d.val, level));
                            }
                            tasks.push(QJob::Q(*typ, level));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                        } => {
                            // 分支体在"捕获 env + fresh rigid 槽"下用**中性
                            // global 视图**重新求值（递归引用停在中性
                            // Rigid——eval 产生不了新卡住 match），再以真实
                            // 表 quote（参考版 avoid_recursive 同款分工）。
                            let mut qc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (p, b) in cases.iter() {
                                let count = p.bind_count();
                                let mut env2 = *menv;
                                for i in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(level + i));
                                }
                                let tv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, neutral, env2, b,
                                );
                                let q = quote_iter(
                                    bump,
                                    spine,
                                    &mut Vec::new(),
                                    &mut Vec::new(),
                                    work,
                                    vals,
                                    icits,
                                    defs,
                                    metas,
                                    globals,
                                    neutral,
                                    level + count,
                                    tv,
                                    None,
                                );
                                qc.push(((*p).clone(), q));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(qc);
                            // scrutinee 用真实表（调用方的 level 下正确）
                            let sq = quote_iter(
                                bump,
                                spine,
                                &mut Vec::new(),
                                &mut Vec::new(),
                                work,
                                vals,
                                icits,
                                defs,
                                metas,
                                globals,
                                neutral,
                                level,
                                *scrutinee,
                                None,
                            );
                            done.push(bump.alloc(Tm::Match(sq, cs)));
                        }
                    },
                    4 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let cell = v_pi_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, cell.env, v_lvl(level));
                        tasks.push(QJob::Pi1(cell));
                        tasks.push(QJob::EvalQ(cell.body, env, level + 1));
                        tasks.push(QJob::Q(cell.dom, level));
                    }
                    _ => {
                        // spine 链（Rigid / Flex / Obj 头）
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        // 先拷出标量再继续（后续任务会 push spine，Vec 可能扩容）
                        let h = v_spine_of(v);
                        let (ea, len, base, top_icit) = {
                            let e = &spine.stack[h];
                            (e.a, e.len, e.base, e.icit)
                        };
                        if len > 1 && base as usize + len as usize - 1 == h {
                            // 连续右链：先引 base，再 ChainRun 自底向上扫
                            let f0 = spine.stack[base as usize].f;
                            let idx_node = match v_tag(f0) {
                                0 => {
                                    let l = v_lvl_of(f0);
                                    if l >= GLOBAL_BASE {
                                        Some(&*bump.alloc(Tm::Var(l)) as &Tm<'a>)
                                    } else {
                                        Some(&*bump.alloc(Tm::Var(level - l - 1)) as &Tm<'a>)
                                    }
                                }
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0))) as &Tm<'a>),
                                // Obj 头的链（内层值要按 level 引读）挂起走 Q
                                _ => None,
                            };
                            let base_v = spine.stack[base as usize].a;
                            tasks.push(QJob::ChainRun {
                                level,
                                next: base as usize,
                                end: h,
                                f0,
                                idx_node,
                                prev: None,
                            });
                            tasks.push(QJob::Q(base_v, level));
                        } else {
                            // 函数部分可能是「陈旧应用链」：建链后其头 meta
                            // 被解成 λ（值里的位模式不随后续求解更新）。force
                            // 单独引函数部分会停在部分应用的 λ 上，照搬 App
                            // 拼接就产出 β-redex 项（参考版整值 force 经
                            // vAppSp 一路 β，永不产出）。故函数部分 force 为
                            // 闭包时，先按 β 语义应用本槽实参、再引应用结果。
                            let fval = spine.stack[h].f;
                            let ff = force(bump, spine, defs, metas, globals, fval);
                            if v_tag(ff) == 1 {
                                let c = v_clo_of(ff);
                                let applied = {
                                    let env = env_ext(bump, c.env, ea);
                                    eval_iter(
                                        bump, spine, work, vals, icits, defs, metas, globals,
                                        env, c.body,
                                    )
                                };
                                tasks.push(QJob::Q(applied, level));
                            } else {
                                tasks.push(QJob::App1(top_icit));
                                tasks.push(QJob::Q(ea, level));
                                tasks.push(QJob::Q(fval, level));
                            }
                        }
                    }
                }
            }
            QJob::Lam1(name, icit) => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            QJob::Pi1(cell) => {
                let cod = done.pop().expect("quote 栈：Pi 缺余定义域");
                let dom = done.pop().expect("quote 栈：Pi 缺定义域");
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
            QJob::EvalQ(body, env, level) => {
                let v = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, globals, env, body,
                );
                tasks.push(QJob::Q(v, level));
            }
            QJob::App1(icit) => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Tm::App(f, a, icit)));
            }
            QJob::MemoStore(key, level) => {
                let m = memo
                    .as_deref_mut()
                    .expect("quote 栈：MemoStore 缺 memo 表");
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                m.insert((key, level), t);
                done.push(t);
            }
            QJob::Obj1(name) => {
                let inner = done.pop().expect("quote 栈：Obj 缺接收者");
                done.push(bump.alloc(Tm::Obj(inner, name)));
            }
            QJob::SumAsm {
                name,
                params,
                cases,
            } => {
                // done 槽序 = v0, t0, v1, t1, ...（先压者在底）→ 按 params
                // 逆序逐槽收进 ps 再反转，省掉 items 中转 + 二次下标拷贝
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("quote 栈：Sum 缺参数");
                    let val = done.pop().expect("quote 栈：Sum 缺参数");
                    ps.push(SumParamT {
                        name: p.name,
                        val,
                        ty,
                        icit: p.icit,
                    });
                }
                ps.reverse();
                done.push(bump.alloc(Tm::Sum(name, bump.alloc_slice_fill_iter(ps), cases)));
            }
            QJob::SumCaseAsm { case_name, datas } => {
                // datas 字段在 done 栈顶（typ 先压在底）：逆序 pop 落槽后
                // 反转，typ 最后 pop
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("quote 栈：SumCase 缺字段");
                    ds.push(SumDataT {
                        name: d.name,
                        val,
                        icit: d.icit,
                    });
                }
                ds.reverse();
                let typ = done.pop().expect("quote 栈：SumCase 缺 typ");
                done.push(bump.alloc(Tm::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                }));
            }
            QJob::ChainRun {
                level,
                next,
                end,
                f0,
                idx_node,
                prev,
            } => {
                let mut prev = match prev {
                    Some(p) => {
                        // 恢复点：非平凡 f 刚引完在 done 栈顶，合掉一层
                        // （悬挂槽位 = next-1，其 icit 即本层应用的 icit）
                        let f_node = done.pop().expect("quote 栈：链缺函数头");
                        let icit = spine.stack[next - 1].icit;
                        bump.alloc(Tm::App(f_node, p, icit))
                    }
                    None => done.pop().expect("quote 栈：链缺 base"),
                };
                let mut i = next;
                loop {
                    if i > end {
                        done.push(prev);
                        break;
                    }
                    let fi = spine.stack[i].f;
                    match idx_node {
                        Some(n) if fi.0 == f0.0 => {
                            prev = bump.alloc(Tm::App(n, prev, spine.stack[i].icit));
                            i += 1;
                        }
                        _ => {
                            // 非平凡链头：挂起引 f，ChainRun 续跑。f 可能是
                            // 「陈旧应用链」（建链后头 meta 被解成 λ）：force
                            // 单独引它停在部分应用的 λ 上，恢复点照搬 App 拼
                            // 接就产出 β-redex 项（参考版整值 force 经 vAppSp
                            // 一路 β，永不产出）。故 f force 为闭包时改为引
                            // 「f 应用本槽实参」的整值，恢复点直接取该结果为
                            // 已累计项（prev:None = 弹出为初始累计，不再拼接）。
                            let ff = force(bump, spine, defs, metas, globals, fi);
                            if v_tag(ff) == 1 {
                                let arg_v = spine.stack[i].a;
                                let c = v_clo_of(ff);
                                let applied = {
                                    let env = env_ext(bump, c.env, arg_v);
                                    eval_iter(
                                        bump, spine, work, vals, icits, defs, metas, globals,
                                        env, c.body,
                                    )
                                };
                                tasks.push(QJob::ChainRun {
                                    level,
                                    next: i + 1,
                                    end,
                                    f0,
                                    idx_node,
                                    prev: None,
                                });
                                tasks.push(QJob::Q(applied, level));
                            } else {
                                tasks.push(QJob::ChainRun {
                                    level,
                                    next: i + 1,
                                    end,
                                    f0,
                                    idx_node,
                                    prev: Some(prev),
                                });
                                tasks.push(QJob::Q(fi, level));
                            }
                            break;
                        }
                    }
                }
            }
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}

// unify（工作表迭代；L09 参考版臂序，无燃料、无 pm 臂、无 (Obj,Obj) 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// 整表/整栈清空不归还缓冲：容量到过该量级时在清空点主动归还，否则峰值
/// 容量会一路常驻到进程结束（多轮 bench / 长驻进程里直接算进稳态 RSS）。
/// 阈值与 L13 孪生版同值同口径：小表重建比留着更贵，大表留着就是几 MB 起
/// 的空桶（1<<18 条 × ~24B ≈ 6MB）。
const CACHE_SHRINK_MIN_ENTRIES: usize = 1 << 18;
/// 工作表栈（`Spine::stack` 与 unify 草稿 `scratch1/scratch2`）的同一阈值：
/// 槽位（`Entry` / `(V, Icit)`）比 memo 条目小，阈值低一档（1<<16 槽
/// ≈ 1–2MB）。与 L13 同口径。
const SPINE_SHRINK_MIN_ENTRIES: usize = 1 << 16;

/// `Vec` / `HashMap` / `HashSet` 共用的「清空 + 按阈值归还缓冲」口径
/// （三者没有公共 trait，自备一个最小版本）：`clear()` 只清条目、桶数组照留，
/// 容量到过阈值的表在清空时顺带 `shrink_to_fit()`；阈值以下照旧只 `clear()`
/// （重建比留着更贵），故常态只是「clear 前多读一次 capacity」的固定开销。
/// **只改清空的写法，不动清空时机**——时机是既有语义（地址复用、换代、
/// 轮边界），正确性不依赖容量。形状照 L13 孪生版。
trait ReclaimOnClear {
    /// 清空并（容量到 `min_entries` 时）归还缓冲；返回 `(清空前 len, 清空后
    /// capacity)`，与 L13 同形（该处供 `twin_mem_stats` 影子登记；本版无
    /// 统计消费者，调用点 `let _ =`）。
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize);
}

impl<T> ReclaimOnClear for Vec<T> {
    #[inline]
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize) {
        let len = self.len();
        let big = self.capacity() >= min_entries;
        self.clear();
        if big {
            self.shrink_to_fit();
        }
        (len, self.capacity())
    }
}

// impl 的界照 L13 原样带上（`K: Hash + Eq` / `S: BuildHasher`）；调用点都是
// 具名类型，无感。
impl<K, T, S> ReclaimOnClear for std::collections::HashMap<K, T, S>
where
    K: std::hash::Hash + Eq,
    S: std::hash::BuildHasher,
{
    #[inline]
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize) {
        let len = self.len();
        let big = self.capacity() >= min_entries;
        self.clear();
        if big {
            self.shrink_to_fit();
        }
        (len, self.capacity())
    }
}

impl<T, S> ReclaimOnClear for std::collections::HashSet<T, S>
where
    T: std::hash::Hash + Eq,
    S: std::hash::BuildHasher,
{
    #[inline]
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize) {
        let len = self.len();
        let big = self.capacity() >= min_entries;
        self.clear();
        if big {
            self.shrink_to_fit();
        }
        (len, self.capacity())
    }
}

/// unify 的跨调用草稿。
#[derive(Default)]
struct ConvScratch {
    memo: FxHashSet<(u64, u64)>,
    scratch1: Vec<(V, Icit)>,
    scratch2: Vec<(V, Icit)>,
}

/// unify 工作表条目：待比较子对、Π 余定义域的惰性比较屏障、判等记忆化
/// 屏障、或卡住 match 的惰性展开屏障（中性 global 视图下重求值后压
/// `l+count` 层的体对）。
enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
    /// 卡住 match 的一个分支对：两侧体在"各自捕获 env + fresh rigid 槽"
    /// 下用**中性 global 视图**重求值，再压 `l + count` 层的体对。
    MatchBranch {
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        neutral: Rc<Vec<V>>,
        l: u32,
        count: u32,
    },
    /// Match/Match 的结构展开屏障（scrutinee 对比完后到达）：cases 长度
    /// 检查、分支对展开（参考版 scrutinee unify 之后的余下步骤，副作用
    /// 时序与参考版一致）。
    MatchStruct {
        e1: Env<'a>,
        e2: Env<'a>,
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
        neutral: Rc<Vec<V>>,
        l: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
}

/// 链（或裸单元）是否卡住投影 Obj 头——unify 的位相等捷径对它关闭
/// （同单元 Obj 也走 `(Obj, Obj)` 合同臂比接收者，不做字面自反放行——
/// 与参考版守卫后的语义一致）。
#[inline]
fn is_objheaded(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        7 => matches!(v_xcell_of(v), XCell::Obj { .. }),
        2 => spine.stack[v_spine_of(v)].hk == HK_OBJ,
        _ => false,
    }
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败。任一对含非变量
/// → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    m: u32,
    args1: &[(V, Icit)], // 内先（collect_args 的产出序）
    args2: &[(V, Icit)],
) -> bool {
    let n1 = args1.len();
    let n2 = args2.len();
    if n1 != n2 {
        return false; // 长度失配：直败零比较（连 force/压栈都省）
    }
    let common = n1;
    let mut pr: Vec<Option<Icit>> = Vec::with_capacity(common);
    let mut fallback = false;
    for k in 0..common {
        let f1 = force(bump, spine, defs, metas, globals, args1[k].0);
        let f2 = force(bump, spine, defs, metas, globals, args2[k].0);
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            pr.push(if v_lvl_of(f1) == v_lvl_of(f2) {
                Some(args1[k].1)
            } else {
                None
            });
        } else {
            fallback = true; // 上游 go 的 None：回落 unify_sp
            break;
        }
    }
    if !fallback {
        if pr.iter().any(|x| x.is_none()) {
            return prune_meta_bump(bump, spine, work, vals, icits, defs, metas, globals, &pr, m)
                .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）——位相等的同单元
    // 也须分派（见 unify 的 tag 7 守卫）。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。**L09 参考版无快照回滚、
/// 无第二方向**——单次尝试，失败即 Err（部分 meta 写入保留，参考版同款）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    // 方向选择与参考版一致：`sp.len() < sp_prime.len()` → (m', sp') 先；
    // 相等/更长 → (m, sp) 先。调用点约定（L08 同款）：v1 = u（m1 侧的
    // rhs），v2 = t（m2 侧的 rhs）。
    let (fa, aa, va, fb, ab, vb) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, defs, metas, globals, ren, aa) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, globals, ren, fa, aa.len() as u32, gamma,
            mask, va,
        ),
        None => solve_bump(
            bump, spine, work, vals, icits, defs, metas, globals, ren, gamma, fb, ab, vb,
        ),
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、卡住投影走 `_` → Err）。
fn unify_sp_lockstep<'a>(
    spine: &Spine,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    h1: usize,
    h2: usize,
) -> bool {
    if spine.spine_len(h1) != spine.spine_len(h2) {
        return false;
    }
    let mut i1 = h1;
    let mut i2 = h2;
    loop {
        let (f1, a1) = {
            let e = &spine.stack[i1];
            (e.f, e.a)
        };
        let (f2, a2) = {
            let e = &spine.stack[i2];
            (e.f, e.a)
        };
        // 位相等后缀：实参对免比（tag 7 除外）；函数部分对仍须入栈。
        // Obj 头的链（tag 2 头 = Obj 单元）同样不免——交回完整分派后走
        // `(Obj, Obj)` 合同臂比接收者。
        let skip1 = a1.0 == a2.0 && v_tag(a1) != 7 && !is_objheaded(spine, a1);
        if skip1 {
            if f1.0 != f2.0 {
                stack.push(UItem::Pair(l, f1, f2));
            }
            break;
        }
        if v_tag(a1) == 2 && v_tag(a2) == 2 {
            // 下钻门控：两侧的实参链顶层 f 与本层 f 同字（纯 ChainWrap 同头
            // 延续）；实参若是另一条中性链（Apply 惯例：`f` = partial 句柄
            // ≠ 头字）则停下，把子对交回完整分派。派发序与参考版 unify_sp
            // 同序：停钻时先压实参对、后压函数部分对。
            let cont = spine.stack[v_spine_of(a1)].f.0 == f1.0
                && spine.stack[v_spine_of(a2)].f.0 == f2.0;
            if cont {
                if f1.0 != f2.0 {
                    stack.push(UItem::Pair(l, f1, f2));
                }
                i1 = v_spine_of(a1);
                i2 = v_spine_of(a2);
                continue;
            }
        }
        stack.push(UItem::Pair(l, a1, a2));
        if f1.0 != f2.0 {
            stack.push(UItem::Pair(l, f1, f2));
        }
        break;
    }
    true
}

/// 裸 Rigid（tag 0）或 Rigid 头的链的层级；非此形态返回 None。
#[inline]
fn rigid_lvl(spine: &Spine, v: V) -> Option<u32> {
    match v_tag(v) {
        0 => Some(v_lvl_of(v)),
        2 => {
            let h = v_spine_of(v);
            if spine.stack[h].hk != HK_OTHER {
                return None; // flex / Obj 头：必非 Rigid，免走底
            }
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                Some(v_lvl_of(hd))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// unification：结构比较 + meta 求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。臂序与参考版 `Infer::unify` 逐项对应（顺序敏感）：
/// U → Π（icit 相等）→ Rigid/Rigid 同级 → 同头 flex = intersect → 异头
/// flex-flex（单方向）→ λ/η → flex 求解 → LiteralType/宽松臂 → Sum/Sum →
/// SumCase/SumCase（typ+datas）→ Match/Match（scrutinee + 中性分支体重
/// 求值）→ 失配。**位相等捷径对 tag 7 与 Obj 头链关闭**：参考版对字面量
/// 无自反臂（同字面量也 Err）、卡住投影走 `_` → Err；捷径放行会误 Accept。
/// 无燃料（参考版无 fuel）；无 pm 臂（L09 的模式特化在 elaboration 侧的
/// unify_pm/update_cxt 完成）。
#[allow(clippy::too_many_arguments)]
fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    stack: &mut Vec<UItem<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    neutral: &[V],
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    mut spec: Option<&mut SpecSolve<'_>>,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配；容量到过阈值的表
    // 在清空时归还缓冲（memo 见 `CACHE_SHRINK_MIN_ENTRIES`，工作表见
    // `SPINE_SHRINK_MIN_ENTRIES`），否则峰值容量随常驻 Machine 到进程结束。
    let _ = conv.memo.reclaim(CACHE_SHRINK_MIN_ENTRIES);
    let _ = conv.scratch1.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    let _ = conv.scratch2.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    let memo = &mut conv.memo;
    // UItem 工作栈由调用方常驻复用（入口已 clear）；失败早退会留下非空
    // 栈，靠下次入口 clear 兜住（Rc 随 clear 正确减计，引用无 Drop）
    debug_assert!(stack.is_empty());
    stack.push(UItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::MatchBranch {
                b1,
                e1,
                b2,
                e2,
                neutral,
                l,
                count,
            } => {
                // 分支体：两侧各自"捕获 env + fresh rigid 槽（count =
                // bind_count，lvl 从 l 起）"下用中性 global 视图重求值，再在
                // l+count 层比较（参考版 unify 的 Match/Match 全路径同款）
                let mut env1 = e1;
                let mut env2 = e2;
                for i in 0..count {
                    env1 = env_ext(bump, env1, v_lvl(l + i));
                    env2 = env_ext(bump, env2, v_lvl(l + i));
                }
                let v1 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &neutral, env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &neutral, env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                neutral,
                l,
            } => {
                // scrutinee 已比完（参考版 unify 的 Match/Match 臂 scrutinee
                // 递归之后）：cases 长度检查 → 逐分支（pattern → 分支体）。
                // LIFO 按执行序的逆序压：分支（体 → pattern，反序）
                if c1.len() != c2.len() {
                    return false;
                }
                for (i, ((p1, b1), (_, b2))) in c1.iter().zip(c2.iter()).enumerate().rev() {
                    stack.push(UItem::MatchBranch {
                        b1: *b1,
                        e1,
                        b2: *b2,
                        e2,
                        neutral: neutral.clone(),
                        l,
                        count: p1.bind_count(),
                    });
                    stack.push(UItem::MatchPattern(p1, &c2[i].0));
                }
                continue;
            }
            UItem::MatchPattern(p1, p2) => {
                if p1 != p2 {
                    return false;
                }
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 位相等：同一值。tag 7 与 Obj 头链例外（见函数注释——参考版对
        // 字面量无自反性；卡住投影走 `(Obj, Obj)` 合同臂比接收者）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let mut t = force(bump, spine, defs, metas, globals, t);
        let mut u = force(bump, spine, defs, metas, globals, u);
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue; // force 展开后同值（同一解的两处引用）
        }
        // 特化模式：方程两侧置于**当前已积累的解**之下再解释（参考版
        // `unify` 入口的 wrap_sub(&s.acc, ·)，dpm-nbe `subst ɑ vs` 的惰性
        // 等价物）。每次弹出按当时的 acc 重新包裹——先解出的方程对后到的
        // 子方程自动可见。acc 为空时零开销。
        if let Some(s) = spec.as_deref() {
            if !s.acc.is_empty() {
                let acc = s.acc.clone();
                t = force(bump, spine, defs, metas, globals, wrap_sub(bump, &acc, t));
                u = force(bump, spine, defs, metas, globals, wrap_sub(bump, &acc, u));
            }
        }

        // —— 宇宙（参考臂 1）：层级相等才成立（无累积）——
        if v_tag(t) == 3 && v_tag(u) == 3 {
            if v_u_of(t) == v_u_of(u) {
                continue;
            }
            return false;
        }
        // —— Π：icit 相等才比（参考臂 2）；icit 失配落到后续臂 ——
        if v_tag(t) == 4 && v_tag(u) == 4 {
            let p = v_pi_of(t);
            let q = v_pi_of(u);
            if p.icit == q.icit {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                // 先比定义域，再惰性 eval 两侧余定义域
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
                continue;
            }
        }
        // —— Rigid/Rigid（参考臂 3）：同级比实参 spine（裸×裸自反成立），
        // 异级落到后续臂（λ/η 等仍可命中，最终 `_` 失配）——
        if v_tag(t) == 0 && v_tag(u) == 0 {
            if v_lvl_of(t) == v_lvl_of(u) {
                continue; // 双裸单元：unify_sp([][]) 自反成立
            }
        }
        // —— pm 特化臂（参考臂 4/5，**在 Flex/λ/η/链分派之前**——顺序敏感；
        // dpm-nbe unify1 的 VVar 臂）：可解 rigid（spec 携带的模式槽集）与
        // 非 Flex 值相遇 ⇒ 解入 `spec.acc`（显式替换，force 读点惰性展开）。
        // Flex 除外——交给 Flex 规则（meta := var）。occurs 环守卫失败 =
        // 失败。spec = None（常规转换）时守卫不成立，落空到后续臂——不得
        // 解假设。调用侧"头部一侧在前"。
        if v_tag(t) == 0
            && matches!(spec.as_deref(), Some(s) if s.solvable.contains(&v_lvl_of(t)))
            && !is_flex(spine, u)
        {
            if val_mentions_lvl(spine, defs, u, v_lvl_of(t)) {
                return false;
            }
            let s = spec.as_deref_mut().unwrap();
            s.acc = SubstV::extend(&s.acc, v_lvl_of(t), u);
            continue;
        }
        if v_tag(u) == 0
            && matches!(spec.as_deref(), Some(s) if s.solvable.contains(&v_lvl_of(u)))
            && !is_flex(spine, t)
        {
            if val_mentions_lvl(spine, defs, t, v_lvl_of(u)) {
                return false;
            }
            let s = spec.as_deref_mut().unwrap();
            s.acc = SubstV::extend(&s.acc, v_lvl_of(u), t);
            continue;
        }
        // —— 中性链 vs 中性链（参考臂 3/4/5 的链形态全在此分派）——
        if v_tag(t) == 2 && v_tag(u) == 2 {
            let h1 = v_spine_of(t);
            let h2 = v_spine_of(u);
            let hd1 = spine.spine_head(h1);
            let hd2 = spine.spine_head(h2);
            let f1 = v_tag(hd1) == 5;
            let f2 = v_tag(hd2) == 5;
            if f1 && f2 {
                // 双 flex：同头 intersect、异头 flex_flex（参考臂 4/5）
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                spine.collect_args(h1, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                spine.collect_args(h2, &mut a2);
                let m1 = v_meta_of(hd1);
                let m2 = v_meta_of(hd2);
                let ok = if m1 == m2 {
                    intersect_bump(
                        bump, spine, work, vals, icits, defs, metas, globals, stack, l, m1, &a1,
                        &a2,
                    )
                } else {
                    flex_flex_bump(
                        bump, spine, work, vals, icits, defs, metas, globals, ren, l, m1, &a1, u,
                        m2, &a2, t,
                    )
                };
                conv.scratch1 = a1;
                conv.scratch2 = a2;
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
            // 同头判定：位相等（同变量 / 同 meta / 同卡住投影单元）
            if hd1.0 == hd2.0 {
                if !is_objheaded(spine, hd1) {
                    // 同头刚性：逐实参比较（lockstep，长度失配即败）
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                        return false;
                    }
                    continue;
                }
                // 同头 Obj 链：(Obj,Obj) 合同（参考版新臂，L08 评审修复回移）
                // ——比接收者，再比实参（lockstep）。接收者住在头单元里、
                // lockstep 看不见，单独入栈。
                if let (
                    XCell::Obj { val: o1, name: n1 },
                    XCell::Obj { val: o2, name: n2 },
                ) = (v_xcell_of(hd1), v_xcell_of(hd2))
                {
                    if n1 != n2 {
                        return false; // 防御（同头单元名字必相同）
                    }
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    stack.push(UItem::Pair(l, *o1, *o2));
                    if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                        return false;
                    }
                    continue;
                }
                return false; // 防御（is_objheaded 已保证 Obj 头）
            }
            // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve（参考
            // 臂 9/10 的链形态）；双刚性异级 / Obj 头组合 → 失配。
            let (mv, h, rhs) = if f1 {
                (v_meta_of(hd1), h1, u)
            } else if f2 {
                (v_meta_of(hd2), h2, t)
            } else {
                return false;
            };
            let mut args = std::mem::take(&mut conv.scratch1);
            args.clear();
            spine.collect_args(h, &mut args);
            let solved = solve_bump(
                bump, spine, work, vals, icits, defs, metas, globals, ren, l, mv, &args, rhs,
            );
            conv.scratch1 = args;
            if solved {
                if memo_on {
                    memo.insert((t.0, u.0));
                }
                continue;
            }
            return false;
        }
        // —— 裸 Rigid vs 链（同级）：参考臂 3 的 unify_sp——裸侧空 spine
        // 与链长失配即败；异级落后续臂 ——
        if v_tag(t) == 0 && v_tag(u) == 2 {
            if rigid_lvl(spine, u) == Some(v_lvl_of(t)) {
                return false; // 空 spine vs 非空链：长度失配
            }
        }
        if v_tag(t) == 2 && v_tag(u) == 0 {
            if rigid_lvl(spine, t) == Some(v_lvl_of(u)) {
                return false;
            }
        }
        // —— λ / η（参考臂 6/7/8；在 flex 求解之前：Flex vs λ 走 η）——
        if v_tag(t) == 1 && v_tag(u) == 1 {
            let c1 = v_clo_of(t);
            let c2 = v_clo_of(u);
            let vt = {
                let env = env_ext(bump, c1.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, c1.body)
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, c2.body)
            };
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }

        // η：中性一侧按 λ 一侧的 icit 应用（卡住投影的应用压链）。可应用性
        // 由 `vapp_ok` 把关——卡住 match / 字面量等形态的应用本是 panic
        // （参考版 `v_app` 同款），守卫后改判失败（参考版 η 臂
        // `v_applicable` 同款，两版同判定）。

        if v_tag(u) == 1 && vapp_ok(t) {
            let c = v_clo_of(u);
            let vu = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, c.body)
            };
            let vt = vapp1(
                bump, spine, work, vals, icits, defs, metas, globals, t, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        if v_tag(t) == 1 && vapp_ok(u) {
            let c = v_clo_of(t);
            let vt = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, globals, env, c.body)
            };
            let vu = vapp1(
                bump, spine, work, vals, icits, defs, metas, globals, u, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // —— flex 求解（参考臂 4/5/9/10 的裸形态）——
        {
            let mut a1 = std::mem::take(&mut conv.scratch1);
            a1.clear();
            let ft = spine.flex_of(t, &mut a1);
            let mut a2 = std::mem::take(&mut conv.scratch2);
            a2.clear();
            let fu = spine.flex_of(u, &mut a2);
            match (ft, fu) {
                (Some(m1), Some(m2)) => {
                    let ok = if m1 == m2 {
                        intersect_bump(
                            bump, spine, work, vals, icits, defs, metas, globals, stack, l, m1,
                            &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, globals, ren, l, m1, &a1,
                            u, m2, &a2, t,
                        )
                    };
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (Some(m), None) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, globals, ren, l, m, &a1, u,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (None, Some(m)) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, globals, ren, l, m, &a2, t,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (None, None) => {
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    // 非 flex：落到字面量 / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 11）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— 宽松臂（参考臂 12）：String 与卡住内建的宽松合一（参考版无
        // decl 表把关——恒放行）——
        if (v_tag(t) == 6 && v_tag(u) == 7 && matches!(v_xcell_of(u), XCell::Prim))
            || (v_tag(t) == 7 && matches!(v_xcell_of(t), XCell::Prim) && v_tag(u) == 6)
        {
            continue;
        }
        // —— (Obj, Obj) 合同（参考版新臂，L08 8988f7c 评审修复回移）：
        // 字段名相同 ⇒ 比接收者（裸单元无实参，spine 空 vs 空即完）。
        // 带实参的 Obj 链在下方链分派的同头分支处理（接收者 + lockstep）。
        // 位相等捷径对 Obj 仍关闭（同单元也走本臂比接收者，与参考版一致）。
        // ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            if let (XCell::Obj { val: o1, name: n1 }, XCell::Obj { val: o2, name: n2 }) = (xt, xu) {
                if n1 != n2 {
                    return false;
                }
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l, *o1, *o2));
                continue;
            }
        }
        // —— Sum/Sum（参考臂 13）：同名即逐参数（含索引）值合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            if let (
                XCell::Sum {
                    name: n1,
                    params: p1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: p2,
                    ..
                },
            ) = (xt, xu)
            {
                if n1 == n2 {
                    for (a, b) in p1.iter().zip(p2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    continue;
                }
                return false; // 异名 Sum：参考版无后续可命中臂 → Err
            }
            // —— SumCase/SumCase（参考臂 14）：同构造子才比；**typ 与 datas
            // 都比**（typ 先、datas 后——L09 参考版与 L07+ 的 datas-only 不
            // 同）——
            if let (
                XCell::SumCase {
                    typ: ty1,
                    case_name: c1,
                    datas: d1,
                },
                XCell::SumCase {
                    typ: ty2,
                    case_name: c2,
                    datas: d2,
                },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    // pop 序 = typ, d0, d1, ...（参考版执行序）
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    stack.push(UItem::Pair(l, *ty1, *ty2));
                    continue;
                }
                return false; // 异 case：参考版无后续可命中臂 → Err
            }
            // —— Match/Match（参考臂 15）：scrutinee 最先合一（真实副作用
            // 时序），cases 长度与 pattern 检查及其后分支体的中性重求值由
            // MatchStruct 屏障执行 ——
            if let (
                XCell::Match {
                    scrutinee: s1,
                    env: e1,
                    cases: c1,
                },
                XCell::Match {
                    scrutinee: s2,
                    env: e2,
                    cases: c2,
                },
            ) = (xt, xu)
            {
                stack.push(UItem::MatchStruct {
                    e1: *e1,
                    e2: *e2,
                    c1,
                    c2,
                    neutral: Rc::new(neutral.to_vec()),
                    l,
                });
                stack.push(UItem::Pair(l, *s1, *s2));
                continue;
            }
        }
        return false;
    }
    true
}

// solve（invert + prune 验证 + rename + lams，全迭代）
// --------------------------------------------------------------------------------

/// solve 的偏置换缓冲（generational）：`val[x]` 在第 `epoch` 代里给出
/// level x → 新下标；`stamp[x] == epoch` 表示条目有效。`reset` 只推进
/// epoch（O(1) 换代）。`NONE_MARK` 哨兵标记**非线性（重复）变量**——
/// `get` 视其为缺项。
#[derive(Default)]
struct RenBuf {
    val: Vec<u32>,
    /// 各 level 槽位的生效代数（与 `val` 平行）；`== epoch` 才有效。
    stamp: Vec<u64>,
    epoch: u64,
}

/// 非线性（重复）变量的哨兵值。
const NONE_MARK: u32 = u32::MAX;

impl RenBuf {
    /// 换代即「清空」：旧条目的 gen 不等于新 epoch，全部失效。
    #[inline]
    fn reset(&mut self) {
        self.epoch += 1;
    }
    /// `NONE_MARK` 视同缺项（非线性变量不在 renaming 里）。
    #[inline]
    fn get(&self, x: usize) -> Option<u32> {
        match self.stamp.get(x).copied() {
            Some(g) if g == self.epoch => {
                let v = self.val[x];
                if v == NONE_MARK {
                    None
                } else {
                    Some(v)
                }
            }
            _ => None,
        }
    }
    /// 本代里 `x` 是否已标非线性哨兵。
    #[inline]
    fn has_mark(&self, x: usize) -> bool {
        self.stamp.get(x).copied() == Some(self.epoch) && self.val[x] == NONE_MARK
    }
    #[inline]
    fn set(&mut self, x: usize, v: u32) {
        if x >= self.val.len() {
            self.val.resize(x + 1, 0);
            self.stamp.resize(x + 1, 0); // 0 != epoch（epoch 从 1 起）
        }
        self.val[x] = v;
        self.stamp[x] = self.epoch;
    }
    /// 整表逐代克隆（卡住 match 分支体的嵌套 renaming 用——参考版按分支
    /// clone 整个 HashMap 的对应物；克隆保持同代，lift 只写进克隆）。
    /// 只克隆到本代有效高水位（stamp==epoch 的最高槽）：容量只增不减，
    /// 整表克隆会背上历史最高 level 的死重；水位之上的条目本代无效，
    /// `get` 视同缺项，语义不变。
    fn clone_valid(&self) -> RenBuf {
        // 自尾回看取高水位：本代最后写入的槽通常就在尾部，几步即命中
        let end = self
            .stamp
            .iter()
            .rposition(|&g| g == self.epoch)
            .map_or(0, |i| i + 1);
        RenBuf {
            val: self.val[..end].to_vec(),
            stamp: self.stamp[..end].to_vec(),
            epoch: self.epoch,
        }
    }
}

/// 上游 `invert`：实参（应用序）逐个 force 成**裸刚性变量**。非线性
/// （重复变量）移出 renaming、记 `NONE_MARK`，产出把重复变量的全部出现
/// 记为 `None` 的掩码（**与 args 逆序 = 应用序**：最外层实参的槽在前；
/// 消费端 [`prune_ty_bump`] rev 迭代配对 Π 层）；线性时返回空 vec。非变量
/// 实参（字面量 / 带链变量 / Match）即失败（`None`）。
/// **L09 参考版无 gamma 上界检查**——全局层级（越过哨兵）同样进映射
/// （忠实移植，含其后果）。
#[allow(clippy::too_many_arguments)]
fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    ren: &mut RenBuf,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    let _ = bump;
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）。**参数视角**：用 force_arg——槽位可能被 subst_cxt
        // 包成 VSub，解出的槽位不得物化（否则可逆 spine 变不可逆，solve
        // 误败）；force_arg 逐层解包后裸 rigid 原样返回。
        let f = force_arg(bump, spine, defs, metas, globals, a);
        if v_tag(f) != 0 {
            return None;
        }
        let x = v_lvl_of(f);
        let i = lvs.len() as u32;
        lvs.push(x);
        match ren.get(x as usize) {
            // 已标非线性哨兵：保持 NONE_MARK 不动（第 3+ 次出现不覆盖）
            None if ren.has_mark(x as usize) => {}
            None => ren.set(x as usize, i),
            Some(_) => {
                ren.set(x as usize, NONE_MARK);
                nonlinear = true;
            }
        }
    }
    if !nonlinear {
        return Some(Vec::new());
    }
    // 掩码：内先序（mask[0] ↔ 最内层实参，与 prune_ty_bump 的
    // mask_inner_first 契约一致——后者 .rev() 后外→内配对 Π 层）；重复变量
    // 整级剪除
    let mut mask: Vec<Option<Icit>> = Vec::with_capacity(args.len());
    for k in 0..args.len() {
        // args[k] 内先 ↔ 应用序 n-1-k ↔ lvs[n-1-k]
        let x = lvs[args.len() - 1 - k] as usize;
        mask.push(match ren.get(x) {
            Some(_) => Some(args[k].1),
            None => None, // 非线性或从未映射 → 剪
        });
    }
    Some(mask)
}

/// `Γ ⊢ ?m args ≡ rhs` 的求解（invert 已做）：非线性掩码先验证剪枝可行性，
/// 再 rename（occurs/scope check 在内），λ 包裹取自 **meta 类型**，空环境
/// 求值写表。失败即不改 metacontext。
#[allow(clippy::too_many_arguments)]
fn solve_with_pren_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    ren: &mut RenBuf,
    m: u32,
    dom: u32,
    gamma: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> bool {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        // force 在 fuel 耗尽时会把已解 meta 当未解返回（拒绝展开），随后
        // 走到的求解按合一失败降级，不 panic——与"fuel 耗尽按未解失败"的
        // 既有降级故事一致（窗口：恰在 1→0 递减帧内）。（L07 2026-09-18
        // 修复 3 的同步移植）
        _ => return false,
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(bump, spine, work, vals, icits, defs, metas, globals, &mask, mty)
            .is_none()
    {
        return false;
    }
    let Some(tm) = rename_iter(
        bump, spine, work, vals, icits, defs, ren, metas, globals, Some(m), dom, gamma, rhs,
    ) else {
        return false;
    };
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, globals, dom, mty, tm,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, globals, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    true
}

/// solve = invert + solve_with_pren。
#[allow(clippy::too_many_arguments)]
fn solve_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> bool {
    let _ = gamma;
    match invert_bump(bump, spine, defs, metas, globals, ren, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, globals, ren, m, args.len() as u32,
            gamma, mask, rhs,
        ),
        None => false,
    }
}

/// rename 任务。icit 记账同 L04/L05：**只有刚性 `spine_case` 预装载**
/// `done_icits`（按收集序入栈）；flex 链走 `prune_vflex`（自持 fold，
/// 不碰 icit 栈）。
enum RJob<'a> {
    /// 引一个值到解域（产生一个 Tm 到 done）。
    Ren { dom: u32, cod: u32, v: V },
    /// 实参（逆应用序）已由其上任务引完，头是 head_tm，折叠 App
    /// （每个 App 的 icit 从平行 done_icits 栈取）。
    SpineFold {
        head_tm: &'a Tm<'a>,
        n: u32,
    },
    /// done 栈顶是体，包 Lam（icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合 Pi（icit 随 PiCell 携带）。
    Pi2(&'a PiCell<'a>),
}

/// partial renaming 的迭代版（L06 版 + L09 增量：tag 0 的大下标直通、
/// tag 3 带层级、无 Decl 头、Prim 无名；Match 的分支体在"捕获 env + fresh
/// rigid 槽"下用**中性 global 视图**重求值，再在**独立克隆的 renaming**
/// （lift 过 count 次）下 rename——参考版按分支 clone 整个 HashMap，这里
/// 逐代克隆 RenBuf）。
#[allow(clippy::too_many_arguments)]
fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    occ: Option<u32>,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
    let mut tasks: Vec<RJob<'a>> = vec![RJob::Ren {
        dom: dom0,
        cod: cod0,
        v: v0,
    }];
    let mut done: Vec<&'a Tm<'a>> = Vec::new();
    // SpineFold 的实参 icit 预装载栈
    let mut done_icits: Vec<Icit> = Vec::new();
    // 实参收集 / 折叠草稿：跨任务复用（clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    let mut popped: Vec<&'a Tm<'a>> = Vec::new();
    macro_rules! spine_case {
        ($dom:expr, $cod:expr, $h:expr, $head_tm:expr, $tasks:expr) => {{
            args.clear();
            spine.collect_args($h, &mut args);
            $tasks.push(RJob::SpineFold {
                head_tm: $head_tm,
                n: args.len() as u32,
            });
            for &(_, i) in args.iter() {
                done_icits.push(i);
            }
            for &(a, _) in args.iter() {
                $tasks.push(RJob::Ren {
                    dom: $dom,
                    cod: $cod,
                    v: a,
                });
            }
        }};
    }
    while let Some(job) = tasks.pop() {
        match job {
            RJob::Ren { dom, cod, v } => {
                let v = force(bump, spine, defs, metas, globals, v);
                match v_tag(v) {
                    5 => {
                        let m = v_meta_of(v);
                        if occ == Some(m) {
                            return None; // occurs check
                        }
                        done.push(bump.alloc(Tm::Meta(m)));
                    }
                    0 => {
                        let x = v_lvl_of(v) as usize;
                        // scope check（x 不在 spine 映射里；非线性哨兵也算缺项）。
                        // 越过哨兵的全局层级不进映射——原样产出大下标 Var
                        // （参考版 rename 的 Rigid 臂：ren miss 且 x >
                        // 1919810 → Tm::Var(x) 照走 spine）
                        let Some(xp) = ren.get(x) else {
                            let x32 = x as u32;
                            if x32 >= GLOBAL_BASE {
                                done.push(bump.alloc(Tm::Var(x32)));
                                continue;
                            }
                            return None;
                        };
                        done.push(bump.alloc(Tm::Var(dom - xp - 1)));
                    }
                    2 => {
                        let h = v_spine_of(v);
                        let hd = spine.spine_head(h);
                        match v_tag(hd) {
                            5 => {
                                // flex 链：pruneVFlex（occ 检查在内部先行）
                                let m = v_meta_of(hd);
                                if occ == Some(m) {
                                    return None; // occurs check
                                }
                                let t = prune_vflex_bump(
                                    bump, spine, work, vals, icits, defs, ren, metas, globals,
                                    occ, dom, cod, m, h,
                                )?;
                                done.push(t);
                            }
                            // 卡住投影头的链：rename 内层再以 Tm::Obj 为头节点
                            // 折叠实参（参考版 rename 的 Obj 臂同款）
                            7 => {
                                let head_tm: &'a Tm<'a> = bump.alloc(match v_xcell_of(hd) {
                                    XCell::Obj { val, name } => {
                                        let inner = rename_iter(
                                            bump, spine, work, vals, icits, defs, ren, metas,
                                            globals, occ, dom, cod, *val,
                                        )?;
                                        Tm::Obj(inner, name)
                                    }
                                    XCell::Lit(s) => Tm::LiteralIntro(s),
                                    _ => return None,
                                });
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                            _ => {
                                let x = v_lvl_of(hd) as usize;
                                let Some(xp) = ren.get(x) else {
                                    // 越过哨兵的全局层级：大下标 Var 照走 spine
                                    let x32 = x as u32;
                                    if x32 >= GLOBAL_BASE {
                                        let head_tm = bump.alloc(Tm::Var(x32));
                                        spine_case!(dom, cod, h, head_tm, tasks);
                                        continue;
                                    }
                                    return None; // scope check
                                };
                                let head_tm = bump.alloc(Tm::Var(dom - xp - 1));
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                        }
                    }
                    1 => {
                        let c = v_clo_of(v);
                        let bv = {
                            let env = env_ext(bump, c.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, globals, env, c.body,
                            )
                        };
                        // lift：binder 槽 (cod → dom)
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Lam1(c.name, c.icit));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                    }
                    4 => {
                        let cell = v_pi_of(v);
                        let bv = {
                            let env = env_ext(bump, cell.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, globals, env, cell.body,
                            )
                        };
                        // lift（同 Lam）
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Pi2(cell));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                        tasks.push(RJob::Ren {
                            dom,
                            cod,
                            v: cell.dom,
                        });
                    }
                    3 => done.push(bump.alloc(Tm::U(v_u_of(v)))),
                    // 字面量类型与裸单元（Lit / Prim 空链）直出
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        XCell::Prim => done.push(bump.alloc(Tm::Prim)),
                        // 不变式：force 后顶层不会是 VSub——防御性失败（参考版
                        // rename 的 VSub 臂 Err 同款）
                        XCell::VSub { .. } => return None,
                        XCell::Obj { val, name } => {
                            // 卡住投影：rename 内层 → 包 Tm::Obj（空实参；
                            // 带实参的链在 tag 2 臂处理）
                            let inner = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, globals,
                                occ, dom, cod, *val,
                            )?;
                            done.push(bump.alloc(Tm::Obj(inner, name)));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                        } => {
                            let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                            for p in params.iter() {
                                let pv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, globals,
                                    occ, dom, cod, p.val,
                                )?;
                                let pt = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, globals,
                                    occ, dom, cod, p.ty,
                                )?;
                                ps.push(SumParamT {
                                    name: p.name,
                                    val: pv,
                                    ty: pt,
                                    icit: p.icit,
                                });
                            }
                            done.push(bump.alloc(Tm::Sum(
                                name,
                                bump.alloc_slice_fill_iter(ps),
                                cases,
                            )));
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                        } => {
                            let tt = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, globals,
                                occ, dom, cod, *typ,
                            )?;
                            let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                            for d in datas.iter() {
                                let dv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, globals,
                                    occ, dom, cod, d.val,
                                )?;
                                ds.push(SumDataT {
                                    name: d.name,
                                    val: dv,
                                    icit: d.icit,
                                });
                            }
                            done.push(bump.alloc(Tm::SumCase {
                                typ: tt,
                                case_name,
                                datas: bump.alloc_slice_fill_iter(ds),
                            }));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                        } => {
                            // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"
                            // 下重新求值（**中性 global 视图**防重展开），再在
                            // lift 过的独立 renaming 下 rename（参考版 rename
                            // 的 Match 臂同款；scrutinee 用真实表）
                            let neutral = neutral_of(globals);
                            let val_tm = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, globals,
                                occ, dom, cod, *scrutinee,
                            )?;
                            let mut nc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (pat, tm) in cases.iter() {
                                let count = pat.bind_count();
                                let mut ren2 = ren.clone_valid();
                                let mut env2 = *menv;
                                let (mut d2, mut c2) = (dom, cod);
                                for _ in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(c2));
                                    ren2.set(c2 as usize, d2);
                                    d2 += 1;
                                    c2 += 1;
                                }
                                let bv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, &neutral, env2, tm,
                                );
                                let bt = rename_iter(
                                    bump, spine, work, vals, icits, defs, &mut ren2, metas,
                                    globals, occ, d2, c2, bv,
                                )?;
                                nc.push(((*pat).clone(), bt));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(nc);
                            done.push(bump.alloc(Tm::Match(val_tm, cs)));
                        }
                    },
                    _ => return None, // 病态（Π/U/字面量被应用等）
                }
            }
            RJob::SpineFold { head_tm, n } => {
                popped.clear();
                for _ in 0..n {
                    let t = done.pop()?;
                    popped.push(t);
                }
                let mut t = head_tm;
                for k in 0..n as usize {
                    let i = done_icits.pop()?;
                    let a = popped[n as usize - 1 - k];
                    t = bump.alloc(Tm::App(t, a, i));
                }
                done.push(t);
            }
            RJob::Lam1(name, icit) => {
                let body = done.pop()?; // 栈约定：子任务必已完成
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            RJob::Pi2(cell) => {
                let cod = done.pop()?;
                let dom = done.pop()?;
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
        }
    }
    debug_assert_eq!(done_icits.len(), 0, "icit 预装载必须全部配对弹出");
    done.pop()
}

/// `pruneVFlex` 的 spine 状态（参考版 `SpinePruneStatus` 同构）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

/// `pruneVFlex`：meta + 纯变量 renaming 判定与剪枝（L06 版原样；非变量
/// 实参——含字面量/Obj/构造子值——嵌套 rename，与参考版 prune_vflex_go 的
/// 非 Rigid 臂一致；实参探测用全量 force）。
#[allow(clippy::too_many_arguments)]
fn prune_vflex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    occ: Option<u32>,
    dom: u32,
    cod: u32,
    m: u32,
    h: usize,
) -> Option<&'a Tm<'a>> {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args); // 内先序
    let mut slots: Vec<(Option<&'a Tm<'a>>, Icit)> = Vec::with_capacity(args.len());
    let mut status = SpinePruneStatus::OKRenaming;
    for &(a, i) in args.iter().rev() {
        // 应用序（外先）；参数视角用 force_arg（见 invert_bump 同款注释）
        let f = force_arg(bump, spine, defs, metas, globals, a);
        if v_tag(f) == 0 {
            match ren.get(v_lvl_of(f) as usize) {
                Some(xp) => slots.push((Some(bump.alloc(Tm::Var(dom - xp - 1))), i)),
                None if status == SpinePruneStatus::OKNonRenaming => return None,
                None => {
                    slots.push((None, i));
                    status = SpinePruneStatus::NeedsPruning;
                }
            }
        } else {
            if status == SpinePruneStatus::NeedsPruning {
                return None; // 上游：剪枝后 spine 必须全变量
            }
            let t = rename_iter(
                bump, spine, work, vals, icits, defs, ren, metas, globals, occ, dom, cod, f,
            )?;
            slots.push((Some(t), i));
            status = SpinePruneStatus::OKNonRenaming;
        }
    }
    let m_prime = if status == SpinePruneStatus::NeedsPruning {
        // 掩码内先序 = slots 反序
        let mut mask: Vec<Option<Icit>> = Vec::with_capacity(slots.len());
        for (st, i) in slots.iter().rev() {
            mask.push(if st.is_some() { Some(*i) } else { None });
        }
        prune_meta_bump(bump, spine, work, vals, icits, defs, metas, globals, &mask, m)?
    } else {
        m
    };
    // 折叠：上游 foldr = 最外层实参先应用（外先迭代，内层包在最外）
    let mut t: &'a Tm<'a> = bump.alloc(Tm::Meta(m_prime));
    for (st, i) in slots {
        if let Some(u) = st {
            t = bump.alloc(Tm::App(t, u, i));
        }
    }
    Some(t)
}

/// `pruneMeta`：检查剪后类型良型、造新 meta（类型 = 剪后值），旧 meta 解为
/// `λ telescope. AppPruning ?m' pruned`。掩码内先序（同 cxt 惯例）。
#[allow(clippy::too_many_arguments)]
fn prune_meta_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        // fuel 耗尽窗口（同 solve_with_pren_bump 注）：按失败降级
        // （L07 2026-09-18 修复 3 的同步移植）
        _ => return None,
    };
    let pruned_tm = prune_ty_bump(
        bump, spine, work, vals, icits, defs, metas, globals, mask, mty,
    )?;
    let prunedty = eval_iter(
        bump, spine, work, vals, icits, defs, metas, globals, EMPTY_ENV, pruned_tm,
    );
    let mp = metas.len() as u32;
    metas.push(MetaEntry::Unsolved(prunedty));
    // AppPruning 项：掩码外先入链（新槽恒链头 → 最终头 = 最内层）
    let mut pr: Option<&'a PrCons<'a>> = None;
    for slot in mask.iter().rev() {
        pr = Some(bump.alloc(PrCons::new(*slot, pr)));
    }
    let ap = bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(mp)), pr));
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, globals, mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, globals, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    Some(mp)
}

/// `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层。自带换代缓冲。
#[allow(clippy::too_many_arguments)]
fn prune_ty_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    globals: &[V],
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(bump, spine, defs, metas, globals, mty);
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, globals, None, dom,
                cod, pdom,
            )?;
            // lift：binder 进映射
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
            bump, spine, work, vals, icits, defs, metas, globals,
            env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(bump, spine, defs, metas, globals, next);
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, globals, None, dom, cod, cur,
    )?;
    // 保留层由内向外回包（layers 序 = 外→内，rev = 内→外 ✓）
    for (name, icit, dtm) in layers.iter().rev() {
        t = bump.alloc(Tm::Pi(name, *icit, dtm, t));
    }
    Some(t)
}

/// `x{n}` 的 bump 拷贝：栈上格式化，省每 binder 一次 system-heap
/// `String`（solve/prune 密集负载下 `lams_from_ty` 每 λ 层都要一个）。
/// （a806ff0 的同款补齐——该 commit 只落到 L03-L05。）
fn alloc_xname<'a>(bump: &'a Bump, n: u32) -> &'a str {
    let mut buf = [0u8; 11]; // 'x' + u32 十进制最多 10 位
    let mut i = buf.len();
    let mut v = n;
    loop {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }
    i -= 1;
    buf[i] = b'x';
    bump.alloc_str(std::str::from_utf8(&buf[i..]).unwrap()) // ASCII 恒有效
}

/// `lams l a t`：沿 **meta 类型**的 Π 层包 λ（名字与 icit 随 Π，`"_"` 改名
/// `x{l'}`；逐层用 `VVar l'` 剥闭包）。
#[allow(clippy::too_many_arguments)]
fn lams_from_ty<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    globals: &[V],
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(bump, spine, defs, metas, globals, ty);
    for lp in 0..l {
        if v_tag(cur) != 4 {
            unreachable!(); // 类型 Π 层数不足（上游同款不可能）
        }
        let p = v_pi_of(cur);
        let (name, icit, env, body_tm) = (p.name, p.icit, p.env, p.body);
        let name = if name == "_" {
            alloc_xname(bump, lp)
        } else {
            name
        };
        names.push((name, icit));
        let next = eval_iter(
            bump, spine, work, vals, icits, defs, metas, globals,
            env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(bump, spine, defs, metas, globals, next);
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 名字表快照（参考版 BiMap 的 map1/map2 同构；**随 Cxt 克隆**——
/// bind/define/fake_bind 克隆插入，与参考版 `src_names.clone()` 的
/// 逐上下文隔离语义逐字对应，无需撤销轨迹）。
///
/// 只装**当前 def 的局部条目**（binder + fake 占位；顶层 define 已迁
/// [`Machine::global_names`]，perf-debt P2）——表大小 = 当前 def 的
/// binder 数（个位数），每 binder 克隆 O(1)。
#[derive(Clone, Default)]
struct Names {
    /// 名字 → 层级（map1：只收源码 binder 与 fake_bind；inserted binder
    /// 与参考版 `new_binder` 一样不入）。
    by_name: FxHashMap<SmolStr, u32>,
    /// 层级 → 类型值（map2：按层级持久，refresh 的 get_by_key2_mut 目标；
    /// 名字查类型经此中转，refresh 更新即生效）。
    by_lvl: FxHashMap<u32, V>,
}

/// 稳态复用机（L06/L08 版 + L09 增量：global 表）。L09 没有 decl 表 /
/// 可变全局 / 燃料池 / pm 事实表——全局 def 走 [`Machine::globals`]（下标
/// = global_idx，项层以 `GLOBAL_BASE` 偏移的大下标引用）；名字状态在
/// [`Cxt`] 的 `names` 快照里（参考版 BiMap 同构）。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 全局 def/enum 值表（下标 = global_idx）。递归 def 的占位（自身大
    /// 层级的 Rigid）先压入、检查后覆盖。每轮清空（参考版每次调用新建
    /// Infer 的 global 表）。
    globals: Vec<V>,
    /// 全局名字表（顶层 define 的 名字 → (层级, 类型)）：Machine 独有的
    /// append-only 表，**不随 Cxt 克隆**。与 L11+ 的 decls 表同角色——
    /// 旧设计把顶层 define 累积进 Cxt 的 names 快照（每 def 各 +1 条，
    /// 表大小 O(D)），`bind_name` 每 binder 克隆整表即 O(D²)（perf-debt
    /// P2）。查找顺序：Cxt 的局部 names（当前 def 的 binder + fake 占位，
    /// 覆盖全局）之后回落本表。每轮清空（同 globals）。
    global_names: FxHashMap<SmolStr, (u32, V)>,
    /// globals 的中性视图缓存：neutral[i] == v_lvl(i + GLOBAL_BASE)，
    /// 随 globals 同步 push。quote/eval/unify 包装器每次调用都要这串值
    /// （卡住 match 分支重求值的 avoid_recursive 视图）——旧实现每次
    /// neutral_of(&self.globals) 整拷 O(D)（perf-debt P2 残余平方项），
    /// 现按字段借用 O(1)。每轮清空（同 globals）。
    neutral: Vec<V>,
    /// eval / quote / unify 的可复用工作栈。`'static` 仅是**存放口径**：
    /// 进核前 clear，借出期间写入的当轮条目不跨调用存活——与 `conv` /
    /// `icits` 的「进核前 clear」纪律同款。`W`/`QJob`/`UItem` 均为无 Drop
    /// 的 Copy 枚举，`Vec` 布局与元素生命周期参数无关，出借时按当次
    /// 生命周期重写指针类型（SAFETY 见各包装方法）。
    eval_work: Vec<W<'static>>,
    quote_tasks: Vec<QJob<'static>>,
    quote_done: Vec<&'static Tm<'static>>,
    quote_work: Vec<W<'static>>,
    unify_work: Vec<W<'static>>,
    /// unify 的 UItem 主工作栈（同上口径；`UItem::MatchBranch` 持
    /// `Rc`——失败早退留下的 Rc 随下次入口 clear 正确减计，非 Drop 项
    /// 是引用 Copy，'static 存放无析构风险）。
    unify_stack: Vec<UItem<'static>>,
    /// quote 记忆化表：容量跨调用复用，内容**每次调用 clear**——meta 可
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项。
    quote_memo: QuoteMemo<'static>,
}

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine {
                stack: Vec::with_capacity(4096),
            },
            vals: Vec::with_capacity(4096),
            icits: Vec::new(),
            conv: ConvScratch::default(),
            defs: Vec::with_capacity(4096),
            metas: Vec::new(),
            ren: RenBuf::default(),
            globals: Vec::new(),
            global_names: FxHashMap::default(),
            neutral: Vec::new(),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/类型表/轨迹 + 环境区域 + global 表
    /// 全部清空。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮 bump 值 /
    /// metas / defs / globals 持有，轮边界后无任何旧句柄可达；容量到过
    /// `SPINE_SHRINK_MIN_ENTRIES` 时清空顺带归还缓冲（否则峰值容量随常驻
    /// Machine 到进程结束）。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.defs.clear();
        self.globals.clear();
        self.global_names.clear();
        self.neutral.clear();
        let _ = self.spine.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        // 与三处 bump.reset()（run_decls / bench_check / bench_nf_impl）
        // 严格伴生：归还 arena 内 σ 克隆的强引用（Rc 节点在全局堆上，reset
        // 不动其数据；见 VSUB_REGS 的 SAFETY 注释）
        vsub_reclaim();
    }

    // Extend Cxt（源码 binder / inserted binder / define / fake_bind）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, ty);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            names: Rc::new(names),
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
        }
    }

    /// Extend Cxt with an inserted implicit binder：**不入名字表**、trail
    /// 不动、mark 不变——但 telescope/pruning 照常扩展。
    fn new_binder<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            names: cxt.names.clone(),
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: false,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, ty);
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            names: Rc::new(names),
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: Some(t_t),
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(None, cxt.pruning))),
            binds: cxt.binds, // define 槽不产生 Π 层
            lvl: cxt.lvl + 1,
        }
    }

    /// fake_bind（参考版 `Cxt::fake_bind`）：递归 def 的占位——名字指到
    /// 全局层级（`GLOBAL_BASE + global_idx`），env/lvl/locals/pruning 一概
    /// 不动。
    ///
    /// **就地 COW（2026-09-12）**：`Rc::make_mut` 在 cxt 独占名字快照
    /// （强计数 1，顺序 decl 路径恒成立）时原地插入，替代旧的整表深克隆
    /// ——大 decl 数负载（universe/macro 等 2^(k+1) 个 def）上每 def
    /// O(D) 克隆实测 O(D²)；有别的快照观察者（match 臂捕获、refresh 克隆
    /// 等）时自动回退深拷贝，隔离语义与旧实现逐字一致。随后 define 用真
    /// 名覆盖同名 by_name 条目；占位残留的 `by_lvl[GLOBAL_BASE+idx]` 键
    /// 无查找路径可达（by_lvl 只点查，按名解析已指向真实层级）。调用方
    /// 需在使用完返回的 fake 视图后 `drop(fake)` 再就地 define（否则多出
    /// 的 Rc 引用会触发 make_mut 克隆回退）。
    fn fake_bind<'a>(&mut self, cxt: &mut Cxt<'a>, x: &str, ty: V, global_idx: u32) -> Cxt<'a> {
        let names = Rc::make_mut(&mut cxt.names);
        names.by_name.insert(SmolStr::new(x), global_idx + GLOBAL_BASE);
        names.by_lvl.insert(global_idx + GLOBAL_BASE, ty);
        clone_cxt(cxt)
    }

    /// [`Self::define_name`] 的就地版（调用方独占 cxt 的 decl 臂 /
    /// prime_round 顺序路径专用）：真名进 **Machine 的全局名字表**
    /// （append-only，不随 Cxt 克隆——P2：旧实现插进 Cxt 的 names 快照，
    /// 表随 def 数累积，`bind_name` 每 binder 克隆即 O(D²)），并撤除
    /// fake_bind 留在局部 names 里的同名占位（by_name 旧键即其 by_lvl
    /// 键；prime_round 的 builtin 注册无占位，remove 为 no-op）。调用点
    /// 审计：返回后父视图立即被丢弃/覆盖（infer_decl Def/Enum 臂、
    /// prime_round），无"父视图仍被读取"的形态；check 路径的 Let/Pi
    /// （父视图存活、体局部作用域）继续走克隆版 [`Self::define_name`]。
    fn define_name_in<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        self.global_names
            .insert(SmolStr::new(x), (cxt.lvl, ty));
        let names = Rc::make_mut(&mut cxt.names);
        if let Some(old_lvl) = names.by_name.remove(x) {
            names.by_lvl.remove(&old_lvl);
        }
        cxt.env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        cxt.types = Some(bump.alloc(TCons {
            name: bump.alloc_str(x),
            ty,
            source: true,
            next: cxt.types,
        }));
        cxt.locals = Some(bump.alloc(LCons {
            name: bump.alloc_str(x),
            a_t,
            t_t: Some(t_t),
            next: cxt.locals,
        }));
        cxt.pruning = Some(bump.alloc(PrCons::new(None, cxt.pruning)));
        cxt.lvl += 1;
        clone_cxt(cxt)
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。
    ///
    /// **L05-L08 的 bind-prefix 快路径（`bind_prefix_of_telescope` + define
    /// 槽由 `cxt.env` 快照供给）在本层刻意不移植**：那条路径要求"telescope
    /// 里 define 槽的项 ≡ env 快照里的值"。L05-L08 的模式特化走 pm_defs
    /// （只追加等式，快照恒成立）；本层起改走参考版 `Cxt::update_cxt`——
    /// 精化就地改写 env 槽再 refresh 重锚定，而 `locals` 照参考版保持陈旧
    /// （参考版 cxt.rs 里 `locals: self.locals.clone()` 的 TODO），全 close
    /// 正是靠这份陈旧项与参考版逐值同轨。改读快照会拿到精化后的值：孪生的
    /// 契约是与参考版 Ok 输出逐字节一致，不是比参考版更正确。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, EMPTY_ENV, closed)
            }
        };
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved(mty));
        bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(m)), cxt.pruning))
    }

    /// 沿 telescope 链闭包（Bind → 显式 Π、Define → Let）。
    fn close_tm<'a>(
        &self,
        bump: &'a Bump,
        mut ls: Option<&'a LCons<'a>>,
        q: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        let mut b = q;
        while let Some(n) = ls {
            b = match n.t_t {
                None => bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b)),
                Some(t) => bump.alloc(Tm::Let(n.name, n.a_t, t, b)),
            };
            ls = n.next;
        }
        b
    }

    /// fresh meta 的求值快捷路径：掩码全为 define 槽（或空）时 AppPrun
    /// 走空转，结果恒为裸 meta 立即数——免一次 eval。
    fn eval_fresh(&mut self, bump: &Bump, env: Env, m: &Tm<'_>) -> V {
        if let Tm::AppPruning(head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, env, m)
    }

    // 内核包装（Machine 字段借出）
    // --------------------------------------------------------------------------------

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn eval<'a>(&mut self, bump: &'a Bump, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            eval_work,
            ..
        } = self;
        // SAFETY：'static 仅是存放口径（字段注释）。W 无 Drop、Vec 布局与
        // 生命周期参数无关；借出期 = 本次调用，槽内容下次借出前必 clear，
        // 任何 'a 条目都不会被以 'static 读到。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        work.clear();
        eval_iter(
            bump, spine, work, vals, icits, defs, metas, globals, env, tm,
        )
    }

    /// 中性 global 视图下的 eval（卡住 match 分支体的重求值——参考版
    /// avoid_recursive 克隆：全局值全部换成指向自身大层级的 Rigid）。
    #[allow(clippy::unnecessary_cast)]
    fn eval_neutral<'a>(&mut self, bump: &'a Bump, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            neutral,
            eval_work,
            ..
        } = self;
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        work.clear();
        eval_iter(
            bump, spine, work, vals, icits, defs, metas, neutral, env, tm,
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            quote_tasks,
            quote_done,
            quote_work,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(quote_tasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> = unsafe {
            &mut *(quote_done as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>)
        };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(quote_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        tasks.clear();
        done.clear();
        work.clear();
        quote_iter(
            bump,
            spine,
            tasks,
            done,
            work,
            vals,
            icits,
            defs,
            metas,
            globals,
            &neutral,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（表容量跨调用复用、内容每次调用 clear，绝不跨
    /// reset 持有条目——meta 求解会让旧条目过期）。
    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            quote_tasks,
            quote_done,
            quote_work,
            quote_memo,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(quote_tasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> = unsafe {
            &mut *(quote_done as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>)
        };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(quote_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let memo: &mut QuoteMemo<'a> = unsafe {
            &mut *(quote_memo as *mut QuoteMemo<'static> as *mut QuoteMemo<'a>)
        };
        tasks.clear();
        done.clear();
        work.clear();
        // 清空保容量（表随 Machine 常驻），容量到阈值时顺带归还缓冲。
        let _ = memo.reclaim(CACHE_SHRINK_MIN_ENTRIES);
        quote_iter(
            bump,
            spine,
            tasks,
            done,
            work,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            level,
            v,
            Some(&mut *memo),
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn unify<'a>(&mut self, bump: &'a Bump, l: u32, t: V, u: V) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            ren,
            conv,
            unify_work,
            unify_stack,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear（unify
        // 的失败早退会把非空栈留在槽里，靠入口 clear 兜住）。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let stack: &mut Vec<UItem<'a>> =
            unsafe { &mut *(unify_stack as *mut Vec<UItem<'static>> as *mut Vec<UItem<'a>>) };
        work.clear();
        stack.clear();
        unify_iter(
            bump, spine, work, stack, vals, icits, defs, metas, globals, neutral, ren, conv, None,
            l, t, u,
        )
    }

    /// 特化合一入口（参考版 `unify(…, Some(&mut SpecSolve))` 穿参）：模式
    /// 方程与覆盖探测用——bare rigid 可解，解入 `spec.acc`。
    fn unify_spec(
        &mut self,
        bump: &Bump,
        l: u32,
        t: V,
        u: V,
        spec: &mut SpecSolve<'_>,
    ) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            ren,
            conv,
            unify_work,
            unify_stack,
            ..
        } = self;
        // SAFETY：同 unify。
        #[allow(clippy::unnecessary_cast)]
        let work: &mut Vec<W<'_>> =
            unsafe { &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'_>>) };
        #[allow(clippy::unnecessary_cast)]
        let stack: &mut Vec<UItem<'_>> =
            unsafe { &mut *(unify_stack as *mut Vec<UItem<'static>> as *mut Vec<UItem<'_>>) };
        work.clear();
        stack.clear();
        unify_iter(
            bump,
            spine,
            work,
            stack,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            ren,
            conv,
            Some(spec),
            l,
            t,
            u,
        )
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表；快版导出项
    /// 的 Span 全零，消息内容与参考版同构）。
    fn unify_catch(&mut self, bump: &Bump, cxt: &Cxt<'_>, t: V, t_prime: V) -> Result<(), Error> {
        // 常规转换（spec = None）；一次合一入口充值精化燃料池
        refuel();
        if self.unify(bump, cxt.lvl, t, t_prime) {
            Ok(())
} else {
            let tq = export(self.quote(bump, cxt.lvl, t));
            let uq = export(self.quote(bump, cxt.lvl, t_prime));
            let names = types_names_list(cxt.types);
            Err(Error(empty_span(format!(
                "can't unify\n      find: {}\n  expected: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            ))))
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β——分配一律落本轮 bump）。
    fn force_v(&mut self, bump: &Bump, v: V) -> V {
        let Machine {
            spine,
            defs,
            metas,
            globals,
            ..
        } = self;
        force(bump, spine, defs, metas, globals, v)
    }

    // 隐式插入（上游 Elaboration.hs 的 insert 族）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> (&'a Tm<'a>, V) {
        let va = self.force_v(bump, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, env, p.body)
            };
            let t2 = bump.alloc(Tm::App(t, m, Icit::Impl));
            self.insert_go(bump, cxt, t2, b)
        } else {
            (t, va)
        }
    }

    /// infer 后无条件插入。
    fn insert_t<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        Ok(self.insert_go(bump, cxt, t, va))
    }

    /// infer 后插入，但隐式 lambda 本身免插。
    fn insert<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        if let Tm::Lam(_, Icit::Impl, _) = t {
            Ok((t, va))
        } else {
            self.insert_t(bump, cxt, t, va)
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止。
    fn insert_until_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        name: &str,
        t: &'a Tm<'a>,
        mut va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let mut t = t;
        loop {
            let forced = self.force_v(bump, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(Error(empty_span(format!("no named implicit arg {}", name))));
            }
        }
    }

    // 主 check（与参考版 elaboration.rs `check` 逐臂对应）
    // --------------------------------------------------------------------------------

    fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫：命名隐式对准同名隐式 Π；显式对显式
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命中：按 λ 的 binder 名绑定（源码名，入名字表）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, &cxt2, tbody, body_a)?;
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, &cxt2, t, body_a)?;
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general
                    let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt, a, tty)?;
                    Ok(t2)
                }
            } else {
                let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                self.unify_catch(bump, cxt, a, tty)?;
                Ok(t2)
            }
        } else if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl {
            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            let p = v_pi_of(a);
            let name: &'a str = bump.alloc_str(p.name);
            let body_a = {
                let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                self.eval(bump, env, p.body)
            };
            let a_t = self.quote(bump, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, &cxt2, t, body_a)?;
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t2, u2) = t {
            let (a_tm, _) = self.check_universe(bump, cxt, a_ty)?;
            let va = self.eval(bump, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t2, va)?;
            let vt = self.eval(bump, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, &cxt2, u2, a)?;
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else if let Raw::Match(expr, clauses) = t {
            // match：编译（特化合一在编译期完成）+ 逐分支检查
            let expr_span = expr.to_span();
            let (tm, typ) = self.infer_expr(bump, cxt, expr)?;
            let target = self.eval(bump, cxt.env, tm);
            let mut compiler = Compiler::new(a);
            compiler.compile(self, bump, typ, clauses, cxt, target)?;
            if !compiler.warnings.is_empty() {
                return Err(Error(expr_span.map(|_| format!("{:?}", compiler.warnings))));
            }
            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                bump.alloc_slice_fill_iter(compiler.pats.into_iter());
            Ok(bump.alloc(Tm::Match(tm, cs)))
        } else {
            let (t2, tty) = self.infer_expr(bump, cxt, t)?;
            let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
            self.unify_catch(bump, cxt, a, tty)?;
            Ok(t2)
        }
    }

    // 类型注解的 universe 检查（参考版 elaboration.rs `check_universe` 完整
    // 移植：可解 meta——两分支都把 meta 解成 `U(0)` 形态并返回层级 0）
    // --------------------------------------------------------------------------------

    fn check_universe<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, u32), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        // U：层级直出（参考版 match 的 U 臂，不 force）
        if v_tag(inferred_type) == 3 {
            return Ok((t_inferred, v_u_of(inferred_type)));
        }
        // Flex：反演 spine，可解则把 meta 解成 `U(0)` 形态（参考版不 force
        // 直接 match——已解 flex 会触发参考版的 unreachable!，快版同款）
        let mut args: Vec<(V, Icit)> = Vec::new();
        if let Some(m) = self.spine.flex_of(inferred_type, &mut args) {
            let mty = match &self.metas[m as usize] {
                MetaEntry::Unsolved(a) => *a,
                _ => unreachable!(),
            };
            let inv = {
                let Machine {
                    spine,
                    defs,
                    metas,
                    globals,
                    ren,
                    ..
                } = self;
                invert_bump(bump, spine, defs, metas, globals, ren, &args)
            };
            let Some(mask) = inv else {
                return Err(Error(t_span.map(|_| "invert failed".to_owned())));
            };
            // 非线性：剪枝可行性检查（结果弃置——参考版只用作把关）
            if !mask.is_empty() {
                let ok = {
                    let Machine {
                        spine,
                        vals,
                        icits,
                        defs,
                        metas,
                        globals,
                        eval_work,
                        ..
                    } = self;
                    let work: &mut Vec<W<'a>> = unsafe {
                        &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                    };
                    work.clear();
                    prune_ty_bump(
                        bump, spine, work, vals, icits, defs, metas, globals, &mask, mty,
                    )
                };
                if ok.is_none() {
                    return Err(Error(t_span.map(|_| "prune failed".to_owned())));
                }
            }
            if args.is_empty() {
                // pren.dom == 0：meta 类型 force 后是 U 即解 `U(0)`
                let f = self.force_v(bump, mty);
                if v_tag(f) == 3 {
                    self.metas[m as usize] = MetaEntry::Solved(v_u(0), mty);
                    return Ok((t_inferred, 0));
                }
                let f2 = self.force_v(bump, mty);
                let msg = format!("meta type {} is not a universe", debug_val(&self.spine, &self.defs, f2));
                return Err(Error(t_span.map(|_| msg.clone())));
            }
            // rename 出 `U(0)` 的解（occ = m），λ 包裹后空环境求值写表
            let rhs = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas,
                    globals,
                    ren,
                    unify_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                rename_iter(
                    bump, spine, work, vals, icits, defs, ren, metas, globals, Some(m),
                    args.len() as u32, cxt.lvl, v_u(0),
                )
            };
            let Some(rhs) = rhs else {
                return Err(Error(
                    t_span.map(|_| "when check universe, try to rename failed".to_string()),
                ));
            };
            let lam_tm = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas,
                    globals,
                    eval_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                lams_from_ty(bump, spine, work, vals, icits, defs, metas, globals, args.len() as u32, mty, rhs)
            };
            let solution = self.eval(bump, EMPTY_ENV, lam_tm);
            self.metas[m as usize] = MetaEntry::Solved(solution, mty);
            return Ok((t_inferred, 0));
        }
        Err(Error(t_span.map(|_| {
            format!(
                "expected universe, got {}",
                debug_val(&self.spine, &self.defs, inferred_type)
            )
        })))
    }
}

// Elaboration 上下文
// --------------------------------------------------------------------------------

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

/// Elaboration 上下文（绑定量在 bump 里）。方法一律借用 `&Cxt`（扩展上下
/// 文返回**新的** Cxt 值；名字/类型的可变状态在 [`Machine`] 的
/// name_map/lvl_types，随 `mark` 轨迹撤销）。
struct Cxt<'a> {
    env: Env<'a>,
    /// 名字快照（参考版 `src_names: BiMap` 同构；随扩展克隆——隔离语义
    /// 与参考版逐字对应）。
    names: Rc<Names>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目；println 的 pretty 名
    /// 单也走这里，与参考版 `Cxt::names()` 的 locals 序一致）。
    types: Option<&'a TCons<'a>>,
    /// telescope（上游 `cxtLocals`）：fresh_meta 闭类型用。
    locals: Option<&'a LCons<'a>>,
    /// fresh meta 的 scope 掩码（与 env 平行；头 = 最内层）。
    pruning: Option<&'a PrCons<'a>>,
    /// 绑定层数（bind/new_binder/synth +1，define 不动）。
    binds: u32,
    lvl: u32,
}

impl<'a> Cxt<'a> {
    fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            names: Rc::new(Names::default()),
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
        }
    }
}

/// types 链 → 参考版 pretty 的名字 List（头 = 最内层；List::prepend 从尾
/// 起构回，序不变）。
fn types_names_list(tys: Option<&TCons<'_>>) -> crate::list::List<String> {
    let mut ns: Vec<String> = Vec::new();
    let mut cur = tys;
    while let Some(tc) = cur {
        ns.push(tc.name.to_owned());
        cur = tc.next;
    }
    let mut list = crate::list::List::new();
    for n in ns.into_iter().rev() {
        list = list.prepend(n);
    }
    list
}

/// 项里是否含自由 `Var`（按 binder 深度算）。`fresh_meta` 快捷路径 2 的
/// 判据（保守：自由 ⇒ 走全构造）。
fn has_free_var(t: &Tm<'_>) -> bool {
    let mut stack: Vec<(&Tm<'_>, u32)> = vec![(t, 0)];
    while let Some((x, d)) = stack.pop() {
        match x {
            Tm::Var(i) => {
                if *i >= d {
                    return true;
                }
            }
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Prim => {}
            Tm::Obj(h, _) => stack.push((h, d)),
            Tm::Pi(_, _, a, b) => {
                stack.push((a, d));
                stack.push((b, d + 1));
            }
            Tm::Let(_, a, t, u) => {
                stack.push((a, d));
                stack.push((t, d));
                stack.push((u, d + 1));
            }
            Tm::Sum(_, params, _) => {
                for p in params.iter() {
                    stack.push((p.val, d));
                    stack.push((p.ty, d));
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push((typ, d));
                for dd in datas.iter() {
                    stack.push((dd.val, d));
                }
            }
            Tm::Match(s, cases) => {
                stack.push((s, d));
                for (_, b) in cases.iter() {
                    stack.push((b, d));
                }
            }
        }
    }
    false
}

impl Machine {
    // check_pm / unify_pm / update_cxt / refresh（参考版 elaboration.rs +
    // cxt.rs 的模式特化机制——精化等式直接改写进环境）
    // --------------------------------------------------------------------------------

    /// `unify_pm`：模式特化的合一（参考版 elaboration.rs 同款臂序）：双裸
    /// Rigid 同级自反；单侧裸 Rigid → 解累积进 σ（旧 `update_cxt` 的显式
    /// 替换形态）；同名 SumCase 逐 datas、同名 Sum 逐参数（均**只比值槽**）
    /// 递归；其余落 `unify_spec`（带 spec 的常规合一——途中的 bare rigid
    /// 继续累积进 σ）。失败语义不变。
    fn unify_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
        t_span: &crate::parser_lib::Span<()>,
        spec: &mut SpecSolve<'_>,
    ) -> Result<(), Error> {
        let mut f1 = self.force_v(bump, t);
        let mut f2 = self.force_v(bump, t_prime);
        // 方程两侧置于当前 acc 之下（dpm-nbe `subst ɑ vs` 的惰性等价物）
        if !spec.acc.is_empty() {
            let acc = spec.acc.clone();
            f1 = self.force_v(bump, wrap_sub(bump, &acc, f1));
            f2 = self.force_v(bump, wrap_sub(bump, &acc, f2));
        }
        // (Rigid(x1, []), Rigid(x2, [])) if x1 == x2 → 自反
        if v_tag(f1) == 0 && v_tag(f2) == 0 && v_lvl_of(f1) == v_lvl_of(f2) {
            return Ok(());
        }
        // (Rigid(x, []), v) → 精化 x := v
        if v_tag(f1) == 0 {
            return self.spec_refine(cxt, v_lvl_of(f1), f2, t_span, spec);
        }
        // (v, Rigid(x, [])) → 精化 x := v
        if v_tag(f2) == 0 {
            return self.spec_refine(cxt, v_lvl_of(f2), f1, t_span, spec);
        }
        // 同名 SumCase：先比 typ 的 Sum 头名字（L07/L10 同款，2026-09-18
        // 评审修复 4：跨 enum 重名构造子是两个不同值，同 case_name 不足
        // 以判定身份；**不比 typ 的值**——索引槽互相引用深递归），再逐
        // datas（值槽）
        if v_tag(f1) == 7 && v_tag(f2) == 7 {
            if let (
                XCell::SumCase {
                    typ: t1,
                    case_name: n1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: t2,
                    case_name: n2,
                    datas: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    let t1f = self.force_v(bump, *t1);
                    let t2f = self.force_v(bump, *t2);
                    if v_tag(t1f) == 7 && v_tag(t2f) == 7 {
                        if let (
                            XCell::Sum { name: na, .. },
                            XCell::Sum { name: nb, .. },
                        ) = (v_xcell_of(t1f), v_xcell_of(t2f))
                        {
                            if na != nb {
                                return Err(Error(t_span.map(|_| "".to_string())));
                            }
                        }
                    }
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(bump, cxt, x.val, y.val, t_span, spec)?;
                    }
                    return Ok(());
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
            // 同名 Sum：逐参数（值槽）
            if let (
                XCell::Sum {
                    name: n1,
                    params: d1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(bump, cxt, x.val, y.val, t_span, spec)?;
                    }
                    return Ok(());
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
        }
        // 其余落常规合一（spec 穿参）
        if self.unify_spec(bump, cxt.lvl, f1, f2, spec) {
            Ok(())
        } else {
            let tq = export(self.quote(bump, cxt.lvl, f1));
            let uq = export(self.quote(bump, cxt.lvl, f2));
            let names = types_names_list(cxt.types);
            let msg = format!(
                "can't unify\n      find: {}\n  expected: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            );
            Err(Error(t_span.map(|_| msg.clone())))
        }
    }

    /// 一条特化解 `x := v` 累积进 σ（旧 `Cxt::update_cxt` 的单步）。守卫：
    /// Flex 不精化（旧直通）；越界 / 全局层级无操作；浅 occurs 失败 = Err。
    fn spec_refine(
        &self,
        cxt: &Cxt<'_>,
        x: u32,
        v: V,
        t_span: &crate::parser_lib::Span<()>,
        spec: &mut SpecSolve<'_>,
    ) -> Result<(), Error> {
        if is_flex(&self.spine, v) {
            return Ok(());
        }
        if x >= cxt.lvl {
            return Ok(());
        }
        if val_mentions_lvl(&self.spine, &self.defs, v, x) {
            return Err(Error(t_span.map(|_| "".to_string())));
        }
        spec.acc = SubstV::extend(&spec.acc, x, v);
        Ok(())
    }

    /// 「纯探测」统一执行器：进入前快照 `metas`，跑完闭包后**无条件**换回
    /// （无论闭包返回 Ok/Err），把探测期分配的 fresh meta 与对已有 meta 的求解
    /// 一律回滚，杜绝污染外泄到真实机。可达性探测等投机性 check 都走此入口。
    /// 必须**整表 clone**，不能只按 meta 上界截断——探测期 unify 可能解掉已有
    /// meta，而这些解又引用闭包内新建 meta，截断会让解悬空（后续查找越界 panic）。
    fn run_pure_probe<R>(&mut self, f: impl FnOnce(&mut Machine) -> R) -> R {
        let metas = self.metas.clone();
        let r = f(self);
        self.metas = metas;
        r
    }

    /// `check_pm`：infer + insert + `unify_pm`；返回累积的精化替换 σ（调用方
    /// 做 `subst_cxt`），不再返回改写过的 Cxt。
    fn check_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<(&'a Tm<'a>, Rc<SubstV>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        refuel();
        let solvable = self.bind_slots(cxt);
        let mut spec = SpecSolve {
            solvable: &solvable,
            acc: Rc::new(SubstV::default()),
        };
        self.unify_pm(bump, cxt, a, inferred_type, &t_span, &mut spec)?;
        Ok((t_inferred, spec.acc))
    }

    /// `check_pm_final`：第二条方程把原始值与模式的值再对一次（失败容忍）。
    fn check_pm_final<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
        ori: V,
    ) -> Result<(&'a Tm<'a>, Rc<SubstV>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        refuel();
        let solvable = self.bind_slots(cxt);
        let mut acc = Rc::new(SubstV::default());
        {
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc,
            };
            self.unify_pm(bump, cxt, a, inferred_type, &t_span, &mut spec)?;
            acc = spec.acc;
        }
        // 在**未改写**的原 env 下求值 t_inferred（旧实现是在已改写 env 下
        // 求值——显式替换的等价口径）；失败容忍。
        let ori_v = self.eval(bump, cxt.env, t_inferred);
        {
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc,
            };
            let _ = self.unify_pm(bump, cxt, ori, ori_v, &t_span, &mut spec);
            acc = spec.acc;
        }
        Ok((t_inferred, acc))
    }

    /// 把精化替换 σ 施加到上下文（参考版 `Cxt::subst_cxt` / dpm-nbe
    /// `subst sub ctx`）：env 槽、types 链、names.by_lvl（name_map 影子索引：
    /// by_name 不动，按层级持久）的类型值包 VSub；lvl / locals / pruning /
    /// binds 不动——**槽位布局不变**，读点经 force 展开。σ 为空零开销直通。
    fn subst_cxt<'a>(&mut self, bump: &'a Bump, sub: &Rc<SubstV>, cxt: &Cxt<'a>) -> Cxt<'a> {
        if sub.is_empty() {
            return clone_cxt(cxt);
        }
        // env：全部槽包裹（包裹值不进 defs 平坦区，整体退化为 binder 链）
        let env = {
            let defs = &self.defs;
            let n = env_len(cxt.env);
            let mut e: Option<&'a EnvCons<'a>> = None;
            for i in (0..n).rev() {
                let v = env_nth(defs, cxt.env, i);
                e = Some(bump.alloc(EnvCons {
                    val: wrap_sub(bump, sub, v),
                    next: e,
                }));
            }
            Env {
                flat_base: 0,
                flat_len: 0,
                binds: e,
            }
        };
        // types 链：逐节点包裹类型值（头 = 最内层，序不变）
        let types = {
            let mut nodes: Vec<(&'a str, V, bool)> = Vec::new();
            let mut cur = cxt.types;
            while let Some(tc) = cur {
                nodes.push((tc.name, tc.ty, tc.source));
                cur = tc.next;
            }
            let mut types: Option<&'a TCons<'a>> = None;
            for (name, ty, source) in nodes.into_iter().rev() {
                types = Some(bump.alloc(TCons {
                    name,
                    ty: wrap_sub(bump, sub, ty),
                    source,
                    next: types,
                }));
            }
            types
        };
        // names：by_name 影子索引保持（层级键不变），by_lvl 类型值同步包裹
        let names = {
            let mut names = (*cxt.names).clone();
            let keys: Vec<u32> = names.by_lvl.keys().copied().collect();
            for k in keys {
                let ty = names.by_lvl[&k];
                names.by_lvl.insert(k, wrap_sub(bump, sub, ty));
            }
            Rc::new(names)
        };
        Cxt {
            env,
            names,
            types,
            locals: cxt.locals,
            pruning: cxt.pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
        }
    }

    /// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
    /// 模式特化方程可解的对象。嵌套 match 的入口上下文可能已被外层精化
    /// 包裹（subst_cxt）——解包 VSub 看槽的原始形态。
    fn bind_slots(&self, cxt: &Cxt<'_>) -> Vec<u32> {
        let n = cxt.lvl;
        let mut out = Vec::new();
        for i in 0..env_len(cxt.env) {
            let mut raw = env_nth(&self.defs, cxt.env, i);
            while v_tag(raw) == 7 {
                match v_xcell_of(raw) {
                    XCell::VSub { val, .. } => raw = *val,
                    _ => break,
                }
            }
            if v_tag(raw) == 0 && v_lvl_of(raw) + i + 1 == n {
                out.push(v_lvl_of(raw));
            }
        }
        out
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            // 变量：局部 names（当前 def 的 binder + fake 占位，覆盖全局）
            // 优先，之后回落 Machine 的全局名字表（顶层 define，append-only
            // 不随 Cxt 克隆）。都缺即 not in scope（参考版 Raw::Var 臂同款）。
            Raw::Var(x) => {
                if let Some(&blvl) = cxt.names.by_name.get(x.data.as_str()) {
                    let ty = *cxt.names.by_lvl.get(&blvl).expect("by_lvl 缺层级");
                    let ix = if blvl >= GLOBAL_BASE {
                        blvl
                    } else {
                        cxt.lvl - blvl - 1
                    };
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                if let Some(&(blvl, ty)) = self.global_names.get(x.data.as_str()) {
                    let ix = if blvl >= GLOBAL_BASE {
                        blvl
                    } else {
                        cxt.lvl - blvl - 1
                    };
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                Err(Error(x.clone().map(|x| format!("error name not in scope: {}", x))))
            }

            Raw::Obj(x, t) => {
                // `Point.mk` 限定构造子引用：改写成 Var("Point.mk")（src_names
                // 里 struct 的 case 名）——参考版 Obj 臂的 mk 特例同款
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(
                            bump,
                            cxt,
                            &Raw::Var(sum_name.clone().map(|n| format!("{n}.mk"))),
                        );
                    }
                }
                let (tm, a) = self.infer_expr(bump, cxt, x)?;
                let a_f = self.force_v(bump, a);
                if v_tag(a_f) == 7 {
                    if let XCell::Sum { params, cases, .. } = v_xcell_of(a_f) {
                        // struct：单 case 且名字带 `.mk` → 剥 mk 的构造子
                        // 类型链取字段类型。隐式 binder 用头部 Sum 实参实例化
                        // （只取 Impl——显式索引不占槽）；**显式字段 binder 用
                        // 接收者的卡住投影实例化**（eval(Obj(接收者项, 字段名))，
                        // L08 评审修复回移——旧 U(0) 占位会让依赖在前字段的
                        // 在后字段出现在检查位时假拒，与参考版同步）
                        let mut c: Option<Vec<(&str, V)>> = None;
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let case = cases[0];
                            if let Ok((_, case_typ)) =
                                self.infer_expr(bump, cxt, &Raw::Var(empty_span(case.to_string())))
                            {
                                let mut ret: Vec<(&str, V)> = vec![];
                                let mut typ = case_typ;
                                // struct 隐式参数的实例值（声明序）
                                let mut param: Vec<V> = params
                                    .iter()
                                    .filter(|p| p.icit == Icit::Impl)
                                    .map(|p| p.val)
                                    .collect();
                                param.reverse();
                                loop {
                                    let typ_f = self.force_v(bump, typ);
                                    if v_tag(typ_f) == 4 {
                                        let p = v_pi_of(typ_f);
                                        if p.icit == Icit::Expl {
                                            ret.push((p.name, p.dom));
                                            let val = self.eval(
                                                bump,
                                                cxt.env,
                                                bump.alloc(Tm::Obj(tm, p.name)),
                                            );
                                            typ = {
                                                let env = env_ext(bump, p.env, val);
                                                self.eval(bump, env, p.body)
                                            };
                                        } else {
                                            let val = param
                                                .pop()
                                                .unwrap_or_else(v_u0);
                                            ret.push((p.name, p.dom));
                                            typ = {
                                                let env = env_ext(bump, p.env, val);
                                                self.eval(bump, env, p.body)
                                            };
                                        }
                                    } else {
                                        break;
                                    }
                                }
                                c = Some(ret);
                            }
                        }
                        let field = c
                            .and_then(|params| {
                                params
                                    .into_iter()
                                    .find(|(fields_name, _)| *fields_name == t.data.as_str())
                                    .map(|(_, ty)| ty)
                            })
                            .or_else(|| {
                                params
                                    .iter()
                                    .find(|p| p.name == t.data.as_str())
                                    .map(|p| p.ty)
                            });
                        if let Some(ty) = field {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        return Err(Error(t.clone().map(|t| format!(
                            "`{}`: {} has no object `{}`",
                            pretty_tm(
                                0,
                                types_names_list(cxt.types),
                                &export(tm)
                            ),
                            debug_val(&self.spine, &self.defs, a),
                            t,
                        ))));
                    }
                    if let XCell::SumCase { datas, .. } = v_xcell_of(a_f) {
                        // 接收者类型是构造子值：字段类型在 datas 里
                        let field = datas
                            .iter()
                            .find(|d| d.name == t.data.as_str())
                            .map(|d| d.val);
                        if let Some(ty) = field {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        return Err(Error(t.clone().map(|t| format!(
                            "`{}`: {} has no object `{}`",
                            pretty_tm(0, types_names_list(cxt.types), &export(tm)),
                            debug_val(&self.spine, &self.defs, a),
                            t,
                        ))));
                    }
                }
                Err(Error(t.clone().map(|t| format!(
                    "`{}` has no object `{}`",
                    pretty_tm(0, types_names_list(cxt.types), &export(tm)),
                    t,
                ))))
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let a_t = self.quote(bump, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let infered = self.infer_expr(bump, &cxt2, tbody);
                let (t_inferred0, b0) = infered?;
                let (t_inferred, b) = self.insert(bump, &cxt2, t_inferred0, b0)?;
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell {
                    name,
                    icit: *i,
                    dom: a,
                    env: cxt.env,
                    body,
                });
                Ok((bump.alloc(Tm::Lam(name, *i, t_inferred)), v_pi(cell)))
            }

            Raw::Lam(x, Either::Name(_), _) => {
                Err(Error(x.clone().map(|_| "infer named lambda".to_owned())))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let t_span = t.to_span();
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let infered = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_until_name(bump, cxt, &name.data, infered.0, infered.1)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let infered = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, infered.0, infered.1)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(t_span.map(|_| {
                            format!("icit mismatch {:?} {:?}", i, p.icit)
                        })));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 参考版把合成 Π 放在 unify_catch 的首位——忠实复刻，
                    // 只影响报错文案方向。合成 binder（"x"）按参考版
                    // cxt.bind 走全量 bind（env/telescope/pruning 扩展），
                    // 但名字不入表外泄（临时 cxt 只喂 fresh_meta）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                    let a = self.eval_fresh(bump, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt.lvl, a);
                    let cxt2 = self.bind_name(bump, cxt, "x", a_t, a);
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u(0));
                    let cell = bump.alloc(PiCell {
                        name: "x",
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u_checked = self.check(bump, cxt, u, a)?;
                let arg_v = self.eval(bump, cxt.env, u_checked);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u_checked, i)), ty))
            }

            // Infer universe type
            Raw::U(x) => Ok((bump.alloc(Tm::U(*x)), v_u(x + 1))),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let mut universe = 0u32;
                let (a_checked, lvl) = self.check_universe(bump, cxt, a)?;
                universe = universe.max(lvl);
                let a_eval = self.eval(bump, cxt.env, a_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let a_t = self.quote(bump, cxt.lvl, a_eval);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a_eval);
                let checked = self.check_universe(bump, &cxt2, b);
                let (b_checked, lvl) = checked?;
                universe = universe.max(lvl);
                Ok((
                    bump.alloc(Tm::Pi(name, *i, a_checked, b_checked)),
                    v_u(universe),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a_ty, t2, u2) => {
                let (a_checked, _) = self.check_universe(bump, cxt, a_ty)?;
                let va = self.eval(bump, cxt.env, a_checked);
                let t_checked = self.check(bump, cxt, t2, va)?;
                let vt = self.eval(bump, cxt.env, t_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let cxt2 = self.define_name(bump, cxt, &x.data, a_checked, t_checked, vt, va);
                let inferred = self.infer_expr(bump, &cxt2, u2);
                let (u_inferred, b) = inferred?;
                Ok((
                    bump.alloc(Tm::Let(name, a_checked, t_checked, u_inferred)),
                    b,
                ))
            }

            // Infer holes
            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&literal.data))),
                v_lit_ty(),
            )),

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(_, _) => Err(Error(
                t_span_of(t).map(|_| "try to infer match".to_owned()),
            )),

            // enum 本体（Decl::Enum 注册期构造）：逐参数推断值 + 引读类型
            Raw::Sum(name, params, cases, universe) => {
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for (n, i, raw) in params {
                    let (value_checked, value_ty) = self.infer_expr(bump, cxt, raw)?;
                    let ty = self.quote(bump, cxt.lvl, value_ty);
                    ps.push(SumParamT {
                        name: bump.alloc_str(&n.data),
                        val: value_checked,
                        ty,
                        icit: *i,
                    });
                }
                let cs: Vec<&'a str> = cases.iter().map(|c| &*bump.alloc_str(&c.data)).collect();
                Ok((
                    bump.alloc(Tm::Sum(
                        bump.alloc_str(&name.data),
                        bump.alloc_slice_fill_iter(ps),
                        bump.alloc_slice_fill_iter(cs),
                    )),
                    v_u(*universe),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造）：typ 只推断不检查
            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, cxt.env, typ_checked);
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for (n, raw, i) in datas {
                    let (tm, _) = self.infer_expr(bump, cxt, raw)?;
                    ds.push(SumDataT {
                        name: bump.alloc_str(&n.data),
                        val: tm,
                        icit: *i,
                    });
                }
                Ok((
                    bump.alloc(Tm::SumCase {
                        typ: typ_checked,
                        case_name: bump.alloc_str(&case_name.data),
                        datas: bump.alloc_slice_fill_iter(ds),
                    }),
                    typ_val,
                ))
            }
        }
    }

    // decl 层的推断（参考版 `Infer::infer(Decl)`）：def 折叠参数后
    // check_universe 类型、fake_bind 占位、检查体、global 表覆盖真值；
    // Println 推断体；enum 先扫宇宙层级再注册类型本体 + 逐构造子（裸名）。
    fn infer_decl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
        d: &Decl,
    ) -> Result<(DeclOut<'a>, Cxt<'a>), Error> {
        match d {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                // 参数折叠：typ = Π 参数. 返回类型；bod = λ 参数. 体。
                let mut typ = std::borrow::Cow::Borrowed(ret_type);
                for (n, a, i) in params.iter().rev() {
                    typ = std::borrow::Cow::Owned(Raw::Pi(
                        n.clone(),
                        *i,
                        Box::new(a.clone()),
                        Box::new(typ.into_owned()),
                    ));
                }
                let mut bod = std::borrow::Cow::Borrowed(body);
                for (n, _, i) in params.iter().rev() {
                    bod = std::borrow::Cow::Owned(Raw::Lam(
                        n.clone(),
                        Either::Icit(*i),
                        Box::new(bod.into_owned()),
                    ));
                }
                let global_idx = self.globals.len() as u32;
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, cxt.env, typ_tm);
                // 递归：先把名字登记成指向自身的大层级占位（src_names +
                // global 表），检查体，再用真实值覆盖。
                let fake = self.fake_bind(cxt, &name.data, vtyp, global_idx);
                self.globals.push(v_lvl(global_idx + GLOBAL_BASE));
                self.neutral.push(v_lvl(global_idx + GLOBAL_BASE));
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                let vt = self.eval(bump, fake.env, t_tm);
                self.globals[global_idx as usize] = vt;
                drop(fake); // 释放 Rc 引用，define 的 make_mut 才能原地写
                let out = self.define_name_in(bump, cxt, &name.data, typ_tm, t_tm, vt, vtyp);
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), clone_cxt(cxt)))
            }
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U(0)（与参考版
                // 同步，L07/L08 黑盒三轮修复的 L09 形态）。域洞若保留，第
                // 2+ 个参数的域是 AppPruning 部分应用 meta（`?m A`），使用
                // 点显式供给隐式实参需解该 meta，invert 对非变量 spine 实参
                // 直接 Err——误报 can't unify。宇宙扫描对 U(0) 域贡献 lvl 0
                // = max 恒等；显式标注与显式索引不动。
                let params: Vec<(crate::parser_lib::Span<String>, Raw, Icit)> = params
                    .iter()
                    .map(|(n, a, i)| {
                        let a = if *i == Icit::Impl && matches!(a, Raw::Hole) {
                            Raw::U(0)
                        } else {
                            a.clone()
                        };
                        (n.clone(), a, *i)
                    })
                    .collect();
                // 宇宙层级扫描（副作用照参考版：infer_expr/check_universe
                // 的 meta 分配全保留，结果只取层级）
                let mut universe_lvl = 0u32;
                for p in params.iter() {
                    if let Ok((Tm::U(lvl), _)) = self.infer_expr(bump, cxt, &p.1) {
                        universe_lvl = universe_lvl.max(*lvl);
                    }
                }
                for case in cases.iter() {
                    for c in case.1.iter() {
                        if let Ok((_, lvl)) = self.check_universe(bump, cxt, &c.1) {
                            universe_lvl = universe_lvl.max(lvl);
                        }
                    }
                }
                // enum 类型本体：λ params → Sum(name, [(p, Var p, ?, icit)], cases)
                let new_params: Vec<(crate::parser_lib::Span<String>, Icit, Raw)> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    .fold(Raw::Var(name.clone()), |ret, x| {
                        Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Var(x.0.clone())),
                            Either::Icit(Icit::Impl),
                        )
                    });
                // 构造子类型：Pi(枚举隐式参数 ++ 构造子绑定器) -> (用户 ret || 缺省)
                let new_cases: Vec<(crate::parser_lib::Span<String>, Raw)> = cases
                    .iter()
                    .map(|(case_name, p, bind)| {
                        let ty = params
                            .iter()
                            .filter(|x| x.2 == Icit::Impl)
                            .cloned()
                            .chain(p.clone())
                            .rev()
                            .fold(
                                bind.clone().unwrap_or(default_ret.clone()),
                                |ret, x| {
                                    Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
                                },
                            );
                        (case_name.clone(), ty)
                    })
                    .collect::<Vec<_>>();
                let cases_spanned: Vec<crate::parser_lib::Span<String>> = new_cases
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect();
                let sum = Raw::Sum(name.clone(), new_params, cases_spanned, universe_lvl);
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U(universe_lvl), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let global_idx = self.globals.len() as u32;
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, cxt.env, typ_tm);
                let fake = self.fake_bind(cxt, &name.data, vtyp, global_idx);
                self.globals.push(v_lvl(global_idx + GLOBAL_BASE));
                self.neutral.push(v_lvl(global_idx + GLOBAL_BASE));
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                let vt = self.eval(bump, fake.env, t_tm);
                self.globals[global_idx as usize] = vt;
                drop(fake); // 释放 Rc 引用，define 的 make_mut 才能原地写
                let mut cxt = self.define_name_in(bump, cxt, &name.data, typ_tm, t_tm, vt, vtyp);
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}；
                // **裸名登记**（L09 无 Enum.case 别名）
                for ((case_name, binders, ret), (ctor_name, ctor_ty)) in
                    cases.iter().zip(new_cases.iter())
                {
                    let body_ret = Raw::SumCase {
                        typ: Box::new(ret.clone().unwrap_or(default_ret.clone())),
                        case_name: case_name.clone(),
                        datas: binders
                            .iter()
                            .map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i))
                            .collect(),
                    };
                    let bod = params
                        .iter()
                        .filter(|x| x.2 == Icit::Impl)
                        .cloned()
                        .chain(binders.clone())
                        .rev()
                        .fold(body_ret, |a, b| {
                            Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                        });
                    let (typ_tm, _) = self.check_universe(bump, &cxt, ctor_ty)?;
                    let vtyp = self.eval(bump, cxt.env, typ_tm);
                    // 构造子良构性（参考版同步，L07 2026-09-18 评审修复 6）：
                    // ret 必须是本 enum 的 Sum 且参数位是 telescope 内的
                    // bare rigid
                    self.check_ctor_wf(bump, &cxt, &name.data, &ctor_name.data, vtyp)?;
                    let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                    let vt = self.eval(bump, cxt.env, t_tm);
                    cxt = self.define_name_in(bump, &mut cxt, &ctor_name.data, typ_tm, t_tm, vt, vtyp);
                }
                Ok((DeclOut::Enum, cxt))
            }
        }
    }

    /// 构造子返回类型良构性（参考版 `Infer::check_ctor_wf` 同款，L07
    /// 2026-09-18 评审修复 6 的同步移植）：实例化构造子类型的全部绑定器
    /// 后，ret 的 WHNF 必须是 `enum_name` 的 `Sum`，且其隐式参数位逐一等
    /// 于 telescope 内的 bare rigid。允许构造子重绑定参数
    /// （`p[A,B](a,b) -> Pack[A][B] a b`），拒绝参数位非变量
    /// （`c -> Foo[Bool]`）与非本 enum 的 ret（`c -> Nat`）——后者向构造
    /// 子名字空间注入永不匹配任何模式的 phantom 值，对覆盖检查完备的
    /// match 在封闭输入上卡死。
    fn check_ctor_wf(
        &mut self,
        bump: &Bump,
        cxt: &Cxt<'_>,
        enum_name: &str,
        ctor_name: &str,
        ctor_vtyp: V,
    ) -> Result<(), Error> {
        let base = cxt.lvl;
        let mut ty = ctor_vtyp;
        let mut bound = 0u32;
        let ret = loop {
            let tyf = self.force_v(bump, ty);
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let u = v_lvl(base + bound);
                bound += 1;
                let env = env_ext(bump, p.env, u);
                ty = self.eval(bump, env, p.body);
            } else {
                break tyf;
            }
        };
        let retf = self.force_v(bump, ret);
        if !(v_tag(retf) == 7 && matches!(v_xcell_of(retf), XCell::Sum { .. })) {
            return Err(Error(empty_span(()).map(|_| {
                format!("构造子 {ctor_name} 的返回类型不是和类型")
            })));
        }
        if let XCell::Sum { name: sname, params, .. } = v_xcell_of(retf) {
            if *sname != enum_name {
                return Err(Error(empty_span(()).map(|_| {
                    format!("构造子 {ctor_name} 的返回类型是 {sname}，不是 {enum_name}")
                })));
            }
            for p in params.iter() {
                if p.icit == Icit::Impl {
                    let v = p.val;
                    let bare_rigid = v_tag(v) == 0
                        && v_lvl_of(v) >= base
                        && v_lvl_of(v) < base + bound;
                    if !bare_rigid {
                        return Err(Error(empty_span(()).map(|_| {
                            format!(
                                "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
                            )
                        })));
                    }
                }
            }
        }
        Ok(())
    }
}

/// `Raw::Match` 推断错误用的 span（to_span 的借用版）。
fn t_span_of(t: &Raw) -> crate::parser_lib::Span<()> {
    t.to_span()
}

/// `Val::U(0)` 占位（参考版 struct 字段剥链的 `unwrap_or(Val::U(0))`）。
fn v_u0() -> V {
    v_u(0)
}

/// Cxt 的浅克隆（env/引用 Copy，names 是 Rc 克隆——快照共享）。
fn clone_cxt<'a>(cxt: &Cxt<'a>) -> Cxt<'a> {
    Cxt {
        env: cxt.env,
        names: cxt.names.clone(),
        types: cxt.types,
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
    }
}

/// 中性 global 视图（参考版 avoid_recursive 克隆：全局值全部换成指向
/// 自身大层级的 Rigid）。
pub(crate) fn neutral_of(globals: &[V]) -> Vec<V> {
    globals
        .iter()
        .enumerate()
        .map(|(i, _)| v_lvl(i as u32 + GLOBAL_BASE))
        .collect()
}

/// 槽位向量 → 纯链环境（头 = 最内层）。
fn chain_env<'a>(bump: &'a Bump, slots: &[V]) -> Env<'a> {
    let mut env: Option<&'a EnvCons<'a>> = None;
    for val in slots.iter().rev() {
        env = Some(bump.alloc(EnvCons { val: *val, next: env }));
    }
    Env {
        flat_base: 0,
        flat_len: 0,
        binds: env,
    }
}

/// decl 层推断的产出：Def 带名（bench 的 nf 口径按名定位），Println 带
/// elaborated 体（run 的 nf 输出用）。
enum DeclOut<'a> {
    Def { name: &'a str },
    Println(&'a Tm<'a>),
    Enum,
}

// 模式匹配编译（2026-09-18 自决策树矩阵重写为 L07 逐臂下钻；L10-L12 同款，
// 参考版 pattern_match.rs 同步替换）
// --------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（L07 同文案：`match 不完整：模式位置 {path} 缺少
    /// 构造子 {ctor}`；2026-09-18 评审修复 P0 的 L09 移植——文案与参考版
    /// 逐字一致，parity 按 Debug 形态比对）。
    IncompleteNested(String),
}

pub(crate) struct Compiler<'a> {
    warnings: Vec<Warning>,
    pub(crate) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    ret_type: V,
    /// 嵌套覆盖检查的记账（走查中收集，臂循环结束后统一探测；L07 同款，
    /// 2026-09-18 评审修复 P0 的 L09 移植）。两段式：走查中只记
    /// (路径, 字段 Sum, 本层 ret)；本臂特化方程**解出后**（σ 为终态）才
    /// 提升为完整记账——字段走查时索引精化不在 σ 里，此时探测会把已精
    /// 化下不可达的构造子误判可达。整臂特化失败（荒谬臂，静默跳过）时
    /// 丢弃记账。
    nested_checks: Vec<NestedCheck<'a>>,
    /// 本臂走查中的待提升位置（结算方程成功后提升）。`ret` 是该层 Con 的
    /// 走查返回类型（槽位刚性即本层走查变量）。
    pending_pos: Vec<(Vec<(String, usize)>, V, V)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账（参考版 `NestedCheck` 同构）：路径 = 根到被拆
/// 字段的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂实例化下
/// 的 Sum 值；`cxt` 是臂走查上下文快照（探测的 scratch 层级须落在该臂
/// 全部真槽之外，spec_refine 的 `x >= cxt.lvl` 守卫以臂内层级为准）；
/// `sub` 是臂终态的精化替换（延迟探测要在与臂内方程同构的状态下跑）。
struct NestedCheck<'a> {
    path: Vec<(String, usize)>,
    field_sum: V,
    cxt: Cxt<'a>,
    sub: Rc<SubstV>,
}

impl<'a> Compiler<'a> {
    fn new(ret_type: V) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
        }
    }

    /// 构造子可达性探测（值级，L07 `probe_accessible` 口径；参考版同款）：
    /// Π 链上枚举隐式参数用头部 Sum 的实参实例化，其余绑定器用超出上下文的
    /// scratch 层 fresh rigid（同为刚性，可被方程解出；探测状态全在本地，
    /// 弃掉即回滚），返回类型再与头部类型跑一次索引方程。成功 = 该构造子
    /// 可能出现在头部类型的值里；结构冲突（`Vec[A] zero` 上不可能有
    /// `cons`）= absurd。构造子类型经 `infer_expr(Var(名))` 取（L09 的全局
    /// 表按层级存，无名字键的 decl 表——树同款）。
    ///
    /// `init_sub` 显式穿参（参考版同款，2026-09-18 评审修复 2/5 的 L09
    /// 移植）：顶层探测传空 σ；嵌套位置的延迟探测传记账时的臂内终态 σ，
    /// 并传臂走查上下文（bind_slots / lvl / 名字表均为臂内的）。方程两侧
    /// 由 unify_pm 入口置于 acc 之下解释。
    fn probe_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        head_sum: V,
        ctor: &crate::parser_lib::Span<String>,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let (sum_name, head_params, impl_vals) = {
            let f = mach.force_v(bump, head_sum);
            if v_tag(f) != 7 {
                return false;
            }
            match v_xcell_of(f) {
                XCell::Sum { name, params, .. } => (
                    *name,
                    params.iter().map(|p| p.val).collect::<Vec<_>>(),
                    params
                        .iter()
                        .filter(|p| p.icit == Icit::Impl)
                        .map(|p| p.val)
                        .collect::<Vec<_>>(),
                ),
                _ => return false,
            }
        };
        // 逐构造子可达性探测是**纯探测**：infer_expr 与特化方程都可能分配/
        // 解掉 meta，探测期状态无需存活（本函数只带出布尔）。统一走
        // `run_pure_probe` 的 metas 快照换入换出（参考版 meta 快照同款机制）。
        mach.run_pure_probe(|mach| {
            // 每个探测独立充值：多构造子枚举的逐 ctor 探测不互相挤占共享池
            // （探测本身回滚，只有燃料单向消耗）。
            refuel();
            let (_, mut ty) = match mach.infer_expr(bump, cxt, &Raw::Var(ctor.clone())) {
                Ok(x) => x,
                Err(_) => return false,
            };
            let mut impl_idx = 0;
            let mut scratch = 0u32;
            loop {
                let tyf = mach.force_v(bump, ty);
                if v_tag(tyf) != 4 {
                    // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理
                    // （保守地要求覆盖）。反方向（判不可达 → 覆盖检查放
                    // 过该构造子）会让深负载下的非穷尽 match 被静默接受。
                    // 参考版 probe_accessible 同点。
                    break Self::unify_indices(mach, bump, cxt, sum_name, &head_params, tyf, init_sub)
                        || fuel_exhausted();
                }
                let p = v_pi_of(tyf);
                let u = if impl_idx < impl_vals.len() {
                    let v = impl_vals[impl_idx];
                    impl_idx += 1;
                    v
                } else {
                    let l = cxt.lvl + scratch;
                    scratch += 1;
                    v_lvl(l)
                };
                let env = env_ext(bump, p.env, u);
                ty = mach.eval(bump, env, p.body);
            }
        })
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子），弃掉即回滚。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        sum_name: &str,
        head_params: &[V],
        ret_ty: V,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let ret_sum = mach.force_v(bump, ret_ty);
        if v_tag(ret_sum) != 7 {
            return false;
        }
        let rp = match v_xcell_of(ret_sum) {
            XCell::Sum { name, params, .. } if *name == sum_name => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let span = empty_span(());
        let solvable = mach.bind_slots(cxt);
        let mut spec = SpecSolve {
            solvable: &solvable,
            acc: init_sub.clone(),
        };
        for (a, b) in head_params.iter().zip(rp.iter()) {
            if mach.unify_pm(bump, cxt, *a, b.val, &span, &mut spec).is_err() {
                return false;
            }
        }
        true
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；L10-L12 同款）。
    /// L09 的机器 API 是"env 口径"（`force_v`/`quote`/`eval` 不带 cxt）。
    /// 语义相对决策树的三处收窄（覆盖含嵌套位置 / 遮蔽只认通配臂 / 特化
    /// 失败静默跳过）见 L11 README 与 docs/l09l13-match-compiler-analysis。
    fn compile(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        typ: V,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt<'a>,
        target_val: V,
    ) -> Result<(), Error> {
        self.warnings = Vec::new();
        self.nested_checks = Vec::new();
        self.pending_pos = Vec::new();
        self.cur_path = Vec::new();
        let typ = mach.force_v(bump, typ);
        let (constrs, ctor_names): (Vec<crate::parser_lib::Span<String>>, Vec<String>) =
            if v_tag(typ) == 7 {
                match v_xcell_of(typ) {
                    XCell::Sum { cases, .. } => (
                        cases.iter().map(|c| empty_span(c.to_string())).collect(),
                        cases.iter().map(|c| c.to_string()).collect(),
                    ),
                    _ => (vec![], vec![]),
                }
            } else {
                (vec![], vec![])
            };
        // 覆盖检查：可达且无臂覆盖 → Unmatched（「构造子 + 999 通配」形态，
        // 与参考版逐字一致）。不可达（如 `Vec[A] zero` 上的 `cons`）不报——
        // 索引方程不可解即结构上不可能出现。
        let empty_sub = Rc::new(SubstV::default());
        for ctor in &constrs {
            if Self::probe_accessible(mach, bump, cxt, typ, ctor, &empty_sub)
                && !arms
                    .iter()
                    .any(|(pat, _)| covers(pat, ctor.data.as_str(), &ctor_names))
            {
                self.warnings.push(Warning::Unmatched(Pattern::Con(
                    ctor.clone(),
                    vec![Pattern::Any(empty_span(()), Icit::Expl); 999],
                    Icit::Expl,
                )));
            }
        }
        let mut unreachable: Vec<Warning> = Vec::new();
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                unreachable.push(Warning::Unreachable(body.clone()));
                continue;
            }
            // 本臂走查起点无遗留记账（上一臂已结算/丢弃，防御性清空）。
            self.pending_pos.clear();
            self.cur_path.clear();
            let (detail, cxt_walk, top_ret) = match self.walk_pat(mach, bump, cxt, pat, typ) {
                Ok(x) => x,
                Err(_) => {
                    // 走查失败臂的嵌套记账一并丢弃
                    self.pending_pos.clear();
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma0)) = mach.check_pm_final(bump, &cxt_walk, &raw, typ, target_val)
            else {
                // 荒谬臂（特化失败静默跳过）：其嵌套位置不产生覆盖义务——
                // 臂本身被跳过已承担语义（L07 荒谬臂 clear pending 同款）
                self.pending_pos.clear();
                continue;
            };
            // 走查特化方程的结算（L07 walk_con 内联方程的等价物，2026-09-18
            // P0 修复的链接步骤）：本臂每层 Con 的「头部 ≐ 走查 ret」方程以
            // σ 作种子补解入，把**走查槽位刚性链接进 σ**——嵌套位置的延迟
            // 探测由此看到索引精化（如 `Vec[Nat] (succ zero)` 的尾部上
            // `nil` 不可达）。方程失败 = 该臂在走查实例化下不可匹配（荒谬
            // 臂）：连同嵌套记账一并静默跳过。
            let solvable = mach.bind_slots(&cxt_walk);
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc: sigma0.clone(),
            };
            let span = empty_span(());
            let mut absurd = false;
            if let Some(top_ret) = top_ret {
                if mach
                    .unify_pm(bump, &cxt_walk, typ, top_ret, &span, &mut spec)
                    .is_err()
                {
                    absurd = true;
                }
            }
            if !absurd {
                for (_, field_sum, ret) in self.pending_pos.iter() {
                    if mach
                        .unify_pm(bump, &cxt_walk, *field_sum, *ret, &span, &mut spec)
                        .is_err()
                    {
                        absurd = true;
                        break;
                    }
                }
            }
            if absurd {
                self.pending_pos.clear();
                continue;
            }
            let sigma = spec.acc;
            // 嵌套位置结算：此刻本臂全部特化方程已解出、σ 为终态，字段 Sum
            // 置于 σ 之下再探测才能看到索引精化（两段式，L07 同款）。
            for (path, field_sum, _) in std::mem::take(&mut self.pending_pos) {
                self.nested_checks.push(NestedCheck {
                    path,
                    field_sum,
                    cxt: clone_cxt(&cxt_walk),
                    sub: sigma.clone(),
                });
            }
            // 臂上下文置于精化 σ 之下（env 槽 + types + names.by_lvl 包
            // VSub；lvl/locals/pruning 不动——槽位布局永不漂移，读点 force
            // 推开）。
            let cxt_arm = mach.subst_cxt(bump, &sigma, &cxt_walk);
            // 期望类型重锚到臂上下文：quote → eval（flex 免锚）。σ 经臂上下文
            // 的 wrapped env 在 eval 读点生效，无需预先包裹。
            let ret_type = {
                let t = self.ret_type;
                if is_flex(&mach.spine, t) {
                    t
                } else {
                    let tm = mach.quote(bump, cxt_arm.lvl, t);
                    mach.eval(bump, cxt_arm.env, tm)
                }
            };
            let ret = mach.check(bump, &cxt_arm, body, ret_type)?;
            self.pats.push((detail, ret));
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        // 参考版 `unreachable.into_iter().chain(self.warnings)`——不可达警告在前
        self.warnings = unreachable.into_iter().chain(self.warnings.drain(..)).collect();
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，L07 同款，2026-09-18 评审
        // 修复 P0 的 L09 移植）：每条记账在记录臂的实例化（σ/臂上下文快照）
        // 下探测字段 Sum 的可达构造子；覆盖集 = 已走查臂的 PatternDetail
        // 沿路径的结构贡献（var/Any = 全覆盖；祖先异 ctor = 不可达该位置；
        // 同 ctor 前缀 = 贡献其末端构造子）。可达集取各记账臂探测的并集
        // （保守）。荒谬臂 / 被遮蔽臂不在 pats 里，天然不贡献覆盖——与运
        // 行时首匹配结构语义一致。
        let mut reported: FxHashSet<(Vec<(String, usize)>, String)> = FxHashSet::default();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force：索引精化（如尾部
            // 长度 l := succ n）在 σ 里，推开后的 Sum 才是探测该用的类型
            let field_sum = mach.force_v(bump, wrap_sub(bump, &nc.sub, nc.field_sum));
            if !(v_tag(field_sum) == 7 && matches!(v_xcell_of(field_sum), XCell::Sum { .. })) {
                continue;
            }
            let ctor_cases: Vec<crate::parser_lib::Span<String>> = match v_xcell_of(field_sum) {
                XCell::Sum { cases, .. } => {
                    cases.iter().map(|c| empty_span(c.to_string())).collect()
                }
                _ => continue,
            };
            for ctor in ctor_cases {
                if !Self::probe_accessible(mach, bump, &nc.cxt, field_sum, &ctor, &nc.sub) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    PosCover::All => true,
                    PosCover::Ctor(n) => n == ctor.data,
                    PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.data.clone())) {
                    self.warnings.push(Warning::IncompleteNested(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        fmt_path(&nc.path),
                        ctor.data
                    )));
                }
            }
        }
        Ok(())
    }

    /// 模式走查（L07 `walk_con` 口径；参考版 `walk_pat` 的快版）：绑定模式变量槽
    /// 并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽、构造子隐式
    /// 绑定器补虚通配、变量模式以用户名绑槽、**Con 本身不占槽**。
    /// 构造子类型经 `infer_expr(Var(名))` 取（L09 的全局表按层级存，无名字键的
    /// decl 表——树同款）。
    ///
    /// 返回值第三项 = 该层 Con 的走查返回类型（已 force，槽位刚性 = 本层
    /// 走查变量；compile 结算本层特化方程用；非 Con 模式为 `None`）。
    /// 嵌套 `Con` 字段位置记入 `pending_pos`（两段式记账；结算见 `compile`，
    /// 2026-09-18 评审修复 P0 的 L09 移植）。
    fn walk_pat(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        pat: &Pattern,
        head_ty: V,
    ) -> Result<(PatternDetail, Cxt<'a>, Option<V>), Error> {
        match pat {
            Pattern::Any(span, _) => {
                let a_t = mach.quote(bump, cxt.lvl, head_ty);
                let cxt2 = mach.bind_name(bump, cxt, "_", a_t, head_ty);
                Ok((PatternDetail::Any(span.clone()), cxt2, None))
            }
            Pattern::Con(name, subs, _) => {
                let head_sum = mach.force_v(bump, head_ty);
                let is_sum = v_tag(head_sum) == 7
                    && matches!(v_xcell_of(head_sum), XCell::Sum { .. });
                let (sum_params, cases): (Vec<SumParamV<'a>>, Vec<&'a str>) = if is_sum {
                    match v_xcell_of(head_sum) {
                        XCell::Sum { params, cases, .. } => (params.to_vec(), cases.to_vec()),
                        _ => (vec![], vec![]),
                    }
                } else {
                    (vec![], vec![])
                };
                if !is_sum || !cases.iter().any(|c| *c == name.data.as_str()) {
                    if !subs.is_empty() {
                        return Err(Error(name.clone().map(|n| format!(
                            "`{n}` 不是构造子，不能带子模式解构"
                        ))));
                    }
                    let a_t = mach.quote(bump, cxt.lvl, head_ty);
                    let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
                    return Ok((PatternDetail::Bind(name.clone()), cxt2, None));
                }
                let (_, mut ty) = mach.infer_expr(bump, cxt, &Raw::Var(name.clone()))?;
                let mut impl_vals: Vec<V> = sum_params
                    .iter()
                    .filter(|p| p.icit == Icit::Impl)
                    .map(|p| p.val)
                    .collect();
                impl_vals.reverse();
                let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
                let mut details: Vec<PatternDetail> = Vec::new();
                let mut cxt_arm = clone_cxt(cxt);
                loop {
                    let tyf = mach.force_v(bump, ty);
                    if v_tag(tyf) != 4 {
                        break;
                    }
                    let cell = v_pi_of(tyf);
                    let (bname, bicit, dom, body, env0) =
                        (cell.name, cell.icit, cell.dom, cell.body, cell.env);
                    if let Some(v) = impl_vals.pop() {
                        let env = env_ext(bump, env0, v);
                        ty = mach.eval(bump, env, body);
                        continue;
                    }
                    let sub: Option<&Pattern> = match bicit {
                        Icit::Impl => sub_queue
                            .first()
                            .filter(|p| p.get_icit() == Icit::Impl)
                            .copied(),
                        Icit::Expl => match sub_queue.first() {
                            Some(p) if p.get_icit() == Icit::Expl => Some(*p),
                            _ => None,
                        },
                    };
                    let u = v_lvl(cxt_arm.lvl);
                    let detail = match sub {
                        None => {
                            let b = format!("_{}", bname);
                            let d_t = mach.quote(bump, cxt_arm.lvl, dom);
                            cxt_arm = mach.bind_name(bump, &cxt_arm, &b, d_t, dom);
                            PatternDetail::Any(empty_span(()))
                        }
                        Some(Pattern::Any(span, _)) => {
                            sub_queue.remove(0);
                            let b = format!("_{}", bname);
                            let d_t = mach.quote(bump, cxt_arm.lvl, dom);
                            cxt_arm = mach.bind_name(bump, &cxt_arm, &b, d_t, dom);
                            PatternDetail::Any(span.clone())
                        }
                        Some(p @ Pattern::Con(..)) => {
                            sub_queue.remove(0);
                            // 嵌套 Con：字段 dom 是含该构造子的 Sum 时记一笔
                            // 待提升的嵌套位置（该字段位置沿 ctor 路径的可达
                            // 构造子必须有臂覆盖），臂特化方程解出后以终态 σ
                            // 结算（见 compile）。
                            let Pattern::Con(cn, ..) = p else {
                                unreachable!()
                            };
                            let field_sum = mach.force_v(bump, dom);
                            let is_ctor = v_tag(field_sum) == 7
                                && matches!(v_xcell_of(field_sum), XCell::Sum { cases, .. }
                                    if cases.iter().any(|c| *c == cn.data.as_str()));
                            let (d, c2) = if is_ctor {
                                self.cur_path.push((name.data.clone(), details.len()));
                                let (d, c2, inner_ret) =
                                    self.walk_pat(mach, bump, &cxt_arm, p, dom)?;
                                self.cur_path.pop();
                                if let Some(r) = inner_ret {
                                    let mut pa = self.cur_path.clone();
                                    pa.push((name.data.clone(), details.len()));
                                    self.pending_pos.push((pa, field_sum, r));
                                }
                                (d, c2)
                            } else {
                                let (d, c2, _) = self.walk_pat(mach, bump, &cxt_arm, p, dom)?;
                                (d, c2)
                            };
                            cxt_arm = c2;
                            d
                        }
                    };
                    details.push(detail);
                    let env = env_ext(bump, env0, u);
                    ty = mach.eval(bump, env, body);
                }
                let ret = mach.force_v(bump, ty);
                Ok((PatternDetail::Con(name.clone(), details), cxt_arm, Some(ret)))
            }
        }
    }
}

/// 臂是否（结构上）覆盖构造子 `ctor`（L07 `covers` 同款）。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor
        }
    }
}

/// 通配臂（参考版 `is_catch_all` 同款）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data)
        }
    }
}

// Debug 复刻（错误消息里内嵌的 `{:?}` 输出；名字 Span 全零——套件比对
// 前按 start_offset/end_offset/path_id 归一化）
// --------------------------------------------------------------------------------

fn dbg_span_str(s: &str) -> String {
    format!("{:?} @ {},{}", s, 0, 0)
}

fn dbg_span_unit() -> String {
    "() @ 0,0".to_string()
}

/// `{:?}` 的字符串字面量转义（Debug 的 escape_debug 语义：引号与控制
/// 字符转义，其余原样）。
fn strconv_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// 参考 `Val` 的 Debug 形态（递归；闭包体走 Tm Debug）。
fn debug_val(spine: &Spine, defs: &[V], v: V) -> String {
    let mut out = String::new();
    debug_val_go(spine, defs, v, &mut out);
    out
}

fn debug_spine(spine: &Spine, defs: &[V], h: usize, out: &mut String) {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args);
    // collect_args 产出 = 逆应用序（内层在前）；参考 Spine = List（头 =
    // 最后应用 = 内层）——Debug 序一致
    out.push('[');
    for (k, (a, i)) in args.iter().enumerate() {
        if k > 0 {
            out.push_str(", ");
        }
        out.push('(');
        debug_val_go(spine, defs, *a, out);
        out.push_str(", ");
        out.push_str(debug_icit(*i));
        out.push(')');
    }
    out.push(']');
}

fn debug_val_go(spine: &Spine, defs: &[V], v: V, out: &mut String) {
    match v_tag(v) {
        0 => {
            out.push_str(&format!("Rigid(Lvl({}), ", v_lvl_of(v)));
            out.push_str("[])");
        }
        1 => {
            let c = v_clo_of(v);
            out.push_str(&format!(
                "Lam({}, {}, Closure(.., ",
                dbg_span_str(c.name),
                debug_icit(c.icit)
            ));
            debug_tm_go(c.body, out);
            out.push_str("))");
        }
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            match v_tag(hd) {
                0 => {
                    out.push_str(&format!("Rigid(Lvl({}), ", v_lvl_of(hd)));
                    debug_spine(spine, defs, h, out);
                    out.push(')');
                }
                5 => {
                    out.push_str(&format!("Flex(MetaVar({}), ", v_meta_of(hd)));
                    debug_spine(spine, defs, h, out);
                    out.push(')');
                }
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, name } => {
                        out.push_str("Obj(");
                        debug_val_go(spine, defs, *val, out);
                        out.push_str(&format!(", {}, ", dbg_span_str(name)));
                        debug_spine(spine, defs, h, out);
                        out.push(')');
                    }
                    _ => {
                        // 其余头不可达（v_app panic，进不了链）；防御输出
                        out.push_str("Neutral(...)");
                    }
                },
                _ => out.push_str("Neutral(...)"),
            }
        }
        3 => {
            out.push_str(&format!("U({})", v_u_of(v)));
        }
        4 => {
            let p = v_pi_of(v);
            out.push_str(&format!(
                "Pi({}, {}, {}, Closure(.., ",
                dbg_span_str(p.name),
                debug_icit(p.icit),
                debug_val(spine, defs, p.dom)
            ));
            debug_tm_go(p.body, out);
            out.push_str("))");
        }
        5 => {
            out.push_str(&format!("Flex(MetaVar({}), [])", v_meta_of(v)));
        }
        6 => out.push_str("LiteralType"),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => {
                out.push_str(&format!("LiteralIntro({})", dbg_span_str(s)));
            }
            XCell::Prim => out.push_str("Prim"),
            XCell::VSub { val, .. } => {
                out.push_str(&format!("VSub({}, ..)", debug_val(spine, defs, *val)));
            }
            XCell::Obj { val, name } => {
                out.push_str(&format!(
                    "Obj({}, {}, [])",
                    debug_val(spine, defs, *val),
                    dbg_span_str(name)
                ));
            }
            XCell::Sum { name, params, cases } => {
                out.push_str(&format!("Sum({}, [", dbg_span_str(name)));
                for (k, p) in params.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!(
                        "({}, {}, {}, {})",
                        dbg_span_str(p.name),
                        debug_val(spine, defs, p.val),
                        debug_val(spine, defs, p.ty),
                        debug_icit(p.icit)
                    ));
                }
                out.push_str("], [");
                for (k, c) in cases.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&dbg_span_str(c));
                }
                out.push_str("])");
            }
            XCell::SumCase { typ, case_name, datas } => {
                out.push_str(&format!(
                    "SumCase {{ typ: {}, case_name: {}, datas: [",
                    debug_val(spine, defs, *typ),
                    dbg_span_str(case_name)
                ));
                for (k, d) in datas.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!(
                        "({}, {}, {})",
                        dbg_span_str(d.name),
                        debug_val(spine, defs, d.val),
                        debug_icit(d.icit)
                    ));
                }
                out.push_str("]) }");
            }
            XCell::Match { scrutinee, env, cases } => {
                out.push_str(&format!(
                    "Match({}, ",
                    debug_val(spine, defs, *scrutinee)
                ));
                // 捕获 env（List<Val> 的 debug_list）
                out.push('[');
                let n = env_len(*env);
                for i in 0..n {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let sv = env_nth(defs, *env, i);
                    let mut tmp = String::new();
                    debug_val_go(spine, defs, sv, &mut tmp);
                    out.push_str(&tmp);
                }
                out.push_str("], [");
                for (k, (p, b)) in cases.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push('(');
                    debug_pat_go(p, out);
                    out.push_str(", ");
                    debug_tm_go(b, out);
                    out.push(')');
                }
                out.push_str("])");
            }
        },
        _ => out.push_str("Val(...)"),
    }
}

fn debug_icit(i: Icit) -> &'static str {
    match i {
        Icit::Impl => "Impl",
        Icit::Expl => "Expl",
    }
}

fn debug_pat_go(p: &PatternDetail, out: &mut String) {
    match p {
        PatternDetail::Any(_) => {
            out.push_str(&format!("Any({})", dbg_span_unit()));
        }
        PatternDetail::Bind(name) => {
            out.push_str(&format!("Bind({})", dbg_span_str(&name.data)));
        }
        PatternDetail::Con(name, subs) => {
            out.push_str(&format!("Con({}, [", dbg_span_str(&name.data)));
            for (k, s) in subs.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                debug_pat_go(s, out);
            }
            out.push_str("])");
        }
    }
}

/// 参考 `Tm` 的 Debug 形态（快版 bump 项 → 参考格式；`Var` 印成 `Ix`）。
fn debug_tm(t: &Tm<'_>) -> String {
    let mut out = String::new();
    debug_tm_go(t, &mut out);
    out
}

fn debug_tm_go(t: &Tm<'_>, out: &mut String) {
    match t {
        Tm::Var(i) => out.push_str(&format!("Var(Ix({}))", i)),
        Tm::Lam(x, i, b) => {
            out.push_str(&format!(
                "Lam({}, {}, ",
                dbg_span_str(x),
                debug_icit(*i)
            ));
            debug_tm_go(b, out);
            out.push(')');
        }
        Tm::App(f, a, i) => {
            out.push_str("App(");
            debug_tm_go(f, out);
            out.push_str(", ");
            debug_tm_go(a, out);
            out.push_str(&format!(", {})", debug_icit(*i)));
        }
        Tm::AppPruning(h, pr) => {
            out.push_str("AppPruning(");
            debug_tm_go(h, out);
            out.push_str(", ");
            // Pruning = List<Option<Icit>>（头 = 最内层）
            out.push('[');
            let mut slots: Vec<Option<Icit>> = Vec::new();
            let mut cur = *pr;
            while let Some(b) = cur {
                slots.push(b.slot);
                cur = b.next;
            }
            for (k, s) in slots.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                match s {
                    Some(i) => out.push_str(&format!("Some({})", debug_icit(*i))),
                    None => out.push_str("None"),
                }
            }
            out.push_str("])");
        }
        Tm::U(l) => out.push_str(&format!("U({})", l)),
        Tm::Pi(x, i, a, b) => {
            out.push_str(&format!(
                "Pi({}, {}, ",
                dbg_span_str(x),
                debug_icit(*i)
            ));
            debug_tm_go(a, out);
            out.push_str(", ");
            debug_tm_go(b, out);
            out.push(')');
        }
        Tm::Let(x, a, t, u) => {
            out.push_str(&format!("Let({}, ", dbg_span_str(x)));
            debug_tm_go(a, out);
            out.push_str(", ");
            debug_tm_go(t, out);
            out.push_str(", ");
            debug_tm_go(u, out);
            out.push(')');
        }
        Tm::Meta(m) => out.push_str(&format!("Meta(MetaVar({}))", m)),
        Tm::LiteralType => out.push_str("LiteralType"),
        Tm::LiteralIntro(s) => out.push_str(&format!("LiteralIntro({})", dbg_span_str(s))),
        Tm::Prim => out.push_str("Prim"),
        Tm::Obj(h, name) => {
            out.push_str("Obj(");
            debug_tm_go(h, out);
            out.push_str(&format!(", {})", dbg_span_str(name)));
        }
        Tm::Sum(name, params, cases) => {
            out.push_str(&format!("Sum({}, [", dbg_span_str(name)));
            for (k, p) in params.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!(
                    "({}, ",
                    dbg_span_str(p.name)
                ));
                debug_tm_go(p.val, out);
                out.push_str(", ");
                debug_tm_go(p.ty, out);
                out.push_str(&format!(", {})", debug_icit(p.icit)));
            }
            out.push_str("], [");
            for (k, c) in cases.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&dbg_span_str(c));
            }
            out.push_str("])");
        }
        Tm::SumCase { typ, case_name, datas } => {
            out.push_str(&format!(
                "SumCase {{ typ: {}, case_name: {}, datas: [",
                {
                    let mut tmp = String::new();
                    debug_tm_go(typ, &mut tmp);
                    tmp
                },
                dbg_span_str(case_name)
            ));
            for (k, d) in datas.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!("({}, ", dbg_span_str(d.name)));
                debug_tm_go(d.val, out);
                out.push_str(&format!(", {})", debug_icit(d.icit)));
            }
            out.push_str("]) }");
        }
        Tm::Match(s, cases) => {
            out.push_str("Match(");
            debug_tm_go(s, out);
            out.push_str(", [");
            for (k, (p, b)) in cases.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push('(');
                debug_pat_go(p, out);
                out.push_str(", ");
                debug_tm_go(b, out);
                out.push(')');
            }
            out.push_str("])");
        }
    }
}

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。
fn export(t: &Tm<'_>) -> CTm {
    use crate::list::List as CList;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, Icit),
        Pi2(&'a str, Icit),
        Let2(&'a str),
        App2(Icit),
        AppPrun2(CList<Option<Icit>>),
        Obj2(&'a str),
        Sum2 {
            name: &'a str,
            params: &'a [SumParamT<'a>],
            cases: &'a [&'a str],
        },
        SumCase2 {
            case_name: &'a str,
            datas: &'a [SumDataT<'a>],
        },
    }
    fn name(x: &str) -> crate::parser_lib::Span<String> {
        empty_span(x.to_owned())
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<CTm> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(CTm::Var(Ix(*i))),
            J::Do(Tm::Lam(x, i, b)) => {
                tasks.push(J::Lam2(x, *i));
                tasks.push(J::Do(b));
            }
            J::Do(Tm::App(f, a, i)) => {
                tasks.push(J::App2(*i));
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            }
            J::Do(Tm::AppPruning(h, pr)) => {
                // bds 持久链表（头 = 最内层）→ 参考版 List<Option<Icit>>（同序）
                let mut vec: Vec<Option<Icit>> = Vec::new();
                let mut cur = *pr;
                while let Some(b) = cur {
                    vec.push(b.slot);
                    cur = b.next;
                }
                let mut list: CList<Option<Icit>> = CList::new();
                for s in vec.into_iter().rev() {
                    list = list.prepend(s);
                }
                tasks.push(J::AppPrun2(list));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::U(l)) => done.push(CTm::U(*l)),
            J::Do(Tm::Pi(x, i, a, b)) => {
                tasks.push(J::Pi2(x, *i));
                tasks.push(J::Do(b));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Let(x, a, t, u)) => {
                tasks.push(J::Let2(x));
                tasks.push(J::Do(u));
                tasks.push(J::Do(t));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Meta(m)) => done.push(CTm::Meta(MetaVar(*m))),
            J::Do(Tm::LiteralType) => done.push(CTm::LiteralType),
            J::Do(Tm::LiteralIntro(s)) => done.push(CTm::LiteralIntro(name(s))),
            J::Do(Tm::Prim) => done.push(CTm::Prim),
            J::Do(Tm::Obj(h, n)) => {
                tasks.push(J::Obj2(n));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::Sum(nm, params, cases)) => {
                tasks.push(J::Sum2 { name: nm, params, cases });
                for p in params.iter().rev() {
                    tasks.push(J::Do(p.ty));
                    tasks.push(J::Do(p.val));
                }
            }
            J::Do(Tm::SumCase {
                typ,
                case_name,
                datas,
            }) => {
                tasks.push(J::SumCase2 { case_name, datas });
                for d in datas.iter().rev() {
                    tasks.push(J::Do(d.val));
                }
                tasks.push(J::Do(typ));
            }
            J::Do(Tm::Match(s, cases)) => {
                // 分支体逐个内联导出（递归深度 = match 嵌套深度）；模式直接
                // 克隆（PatternDetail 是参考版类型，两版共用）
                let s2 = export(s);
                let mut cs: Vec<(PatternDetail, CTm)> = Vec::with_capacity(cases.len());
                for (p, b) in cases.iter() {
                    cs.push((p.clone(), export(b)));
                }
                done.push(CTm::Match(Box::new(s2), cs));
            }
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(CTm::Lam(name(x), i, Box::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(CTm::Pi(name(x), i, Box::new(dom), Box::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(CTm::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(CTm::App(Box::new(f), Box::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(CTm::AppPruning(Box::new(h), pr));
            }
            J::Obj2(n) => {
                let h = done.pop().expect("export 栈：Obj 缺接收者");
                done.push(CTm::Obj(Box::new(h), name(n)));
            }
            J::Sum2 { name: nm, params, cases } => {
                let mut ps: Vec<(crate::parser_lib::Span<String>, CTm, CTm, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("export 栈：Sum 缺参数类型");
                    let val = done.pop().expect("export 栈：Sum 缺参数值");
                    ps.push((name(p.name), val, ty, p.icit));
                }
                ps.reverse();
                let cs: Vec<crate::parser_lib::Span<String>> =
                    cases.iter().map(|c| name(c)).collect();
                done.push(CTm::Sum(name(nm), ps, cs));
            }
            J::SumCase2 { case_name, datas } => {
                let mut ds: Vec<(crate::parser_lib::Span<String>, CTm, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("export 栈：SumCase 缺字段");
                    ds.push((name(d.name), val, d.icit));
                }
                ds.reverse();
                let typ = done.pop().expect("export 栈：SumCase 缺 typ");
                done.push(CTm::SumCase {
                    typ: Box::new(typ),
                    case_name: name(case_name),
                    datas: ds,
                });
            }
        }
    }
    done.pop().expect("export 必须恰有一个根")
}

/// 参考版项的节点数（与 mod.rs `tm_size_ref` 同口径）。
fn tm_size(t: &Tm<'_>) -> u64 {
    let mut stack: Vec<&Tm<'_>> = vec![t];
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
                let mut cur = *pr;
                while let Some(b) = cur {
                    n += 1;
                    cur = b.next;
                }
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
                for p in params.iter() {
                    stack.push(p.val);
                    stack.push(p.ty);
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push(typ);
                for d in datas.iter() {
                    stack.push(d.val);
                }
            }
            Tm::Match(s, cases) => {
                stack.push(s);
                for (p, b) in cases.iter() {
                    n += p.bind_count() as u64;
                    stack.push(b);
                }
            }
        }
    }
    n
}

// builtin 注册（每轮 prime；参考版 `Cxt::new` 逐条对应）
// --------------------------------------------------------------------------------

impl Machine {
    /// 每轮注册（参考版 `Cxt::new`）：String 类型 + string_concat。两者的
    /// **值按参考版手工构造**——string_concat 的 λ/Π 闭包 env 里钉着
    /// `LiteralType` 填充槽（使 `Tm::Prim` 读 env 前两槽、Π 类型的
    /// `Var(2)` 指回 String），与 eval 出来的形态逐槽一致。
    fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let lit_ty: &'a Tm<'a> = bump.alloc(Tm::LiteralType);
        let u0_t: &'a Tm<'a> = bump.alloc(Tm::U(0));
        // String : U(0)，值 = LiteralType
        let mut cxt = Cxt::empty();
        self.define_name_in(
            bump,
            &mut cxt,
            "String",
            u0_t,
            lit_ty,
            v_lit_ty(),
            v_u(0),
        );
        // string_concat：λ x y → Prim；类型 Π x:String. Π y:String. String
        // （体 Tm 的 Var 索引与参考版一致：域 Var(0)/Var(1)，返回 Var(2)）
        let sc_lam_tm: &'a Tm<'a> = bump.alloc(Tm::Lam(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim))),
        ));
        let sc_pi_tm: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Var(0)),
            bump.alloc(Tm::Pi(
                "y",
                Icit::Expl,
                bump.alloc(Tm::Var(1)),
                bump.alloc(Tm::Var(2)),
            )),
        ));
        // 值 = Lam("x", Expl, Closure([LiteralType], Lam("y", Expl, Prim)))
        let filled = env_ext(bump, EMPTY_ENV, v_lit_ty());
        let sc_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: filled,
            body: sc_lam_body(bump),
        }));
        // 类型 = Pi("x", Expl, LiteralType, Closure([LiteralType], Pi 体))
        let sc_ty = v_pi(bump.alloc(PiCell {
            name: "x",
            icit: Icit::Expl,
            dom: v_lit_ty(),
            env: filled,
            body: sc_pi_cod(bump),
        }));
        self.define_name_in(bump, &mut cxt, "string_concat", sc_pi_tm, sc_lam_tm, sc_val, sc_ty)
    }

    /// 参考版 `bench_check` 的主循环（无输出变体）：返回 (是否通过，最终
    /// 上下文，最后一个 def 的值)。
    fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Cxt<'a>, Option<V>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            let is_def = matches!(d, Decl::Def { .. });
            match self.infer_decl(bump, &mut cxt, d) {
                Ok((_, nc)) => {
                    cxt = nc;
                    if matches!(d, Decl::Def { .. }) {
                        // define 链的 env 槽顶 = 本 def 的登记值
                        last = Some(env_nth(&self.defs, cxt.env, 0));
                    }
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        (Ok(()), cxt, last)
    }
}

/// `Lam("y", Expl, Prim)`（string_concat 值闭包的体）。
fn sc_lam_body<'a>(bump: &'a Bump) -> &'a Tm<'a> {
    bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim)))
}

/// `Pi("y", Expl, Var(1), Var(2))`（string_concat 类型闭包的体）。
fn sc_pi_cod<'a>(bump: &'a Bump) -> &'a Tm<'a> {
    bump.alloc(Tm::Pi(
        "y",
        Icit::Expl,
        bump.alloc(Tm::Var(1)),
        bump.alloc(Tm::Var(2)),
    ))
}

/// 稳态类型检查器（同 L03-L08：owns 反复 `reset` 的 `Bump` 与跨调用复用
/// 的 [`Machine`]）。
pub(crate) struct Tycker {
    bump: Bump,
    machine: Machine,
}

impl Tycker {
    pub(crate) fn new() -> Self {
        Tycker {
            bump: Bump::with_capacity(1 << 20),
            machine: Machine::new(),
        }
    }

    /// 参考版 `run` 的等价物：preprocess + parse 由调用方完成（与参考版
    /// 共用 parser；参考版对 parse 失败 unwrap panic、对 parse 错误只
    /// 打印后继续——快版同口径：None panic、错误静默），本方法做轮重置 +
    /// builtin 重注册 + 逐 decl 推断，println 的 nf 经 pretty 输出（quote
    /// 走记忆化口径——与无记忆化输出逐字节一致，L03-L06 已证）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.bump.reset();
        self.machine.clear_round();
        // 轮尾/出错出口都归还本轮 arena 克隆（轮首 clear_round 覆盖不到
        // "最后一轮"——Tycker 长存时其 σ 会挂到进程结束；归还后 arena 内
        // XCell::VSub 的 Rc 悬垂，但本轮出口已无人再读 arena）。
        // L08 移植轮发现的 L07→孪生缺口，L09 同款补齐。
        struct ReclaimOnExit;
        impl Drop for ReclaimOnExit {
            fn drop(&mut self) {
                vsub_reclaim();
            }
        }
        let _reclaim = ReclaimOnExit;
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for d in ast {
            let (out, nc) = self.machine.infer_decl(bump, &mut cxt, d)?;
            cxt = nc;
            if let DeclOut::Println(t) = out {
                // nf：eval + quote（层级 = env 槽数，参考版 `Infer::nf` 同款）
                // 一次 nf 充值精化燃料池（参考版 `nf` 同款）
                refuel();
                let v = self.machine.eval(bump, cxt.env, t);
                let lvl = env_len(cxt.env);
                let q = self.machine.quote_memo(bump, lvl, v);
                let names = types_names_list(cxt.types);
                ret += &pretty_tm(0, names, &export(q));
                ret += "\n";
            }
        }
        Ok(ret)
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        let (ast, _parse_errs) = match super::parser::parser(&super::preprocess(input), path_id) {
            Some(x) => x,
            // 参考版 run 对 parse 失败 unwrap panic——同款
            None => panic!("parse failed"),
        };
        self.run_decls(&ast)
    }

    /// 基准口径（bench 用）：仅 elaborate。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 的登记值空层级引读，与参考版
    /// `bench_check_nf` 同口径——quote 无记忆化），返回结果树节点数。
    pub(crate) fn bench_check_nf(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, true)
    }

    fn bench_nf_impl(&mut self, ast: &[Decl], use_memo: bool) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let (r, _cxt, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some(v) = last else {
            return 0;
        };
        refuel();
        let q = if use_memo {
            self.machine.quote_memo(bump, 0, v)
        } else {
            self.machine.quote(bump, 0, v)
        };
        tm_size(q)
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

/// 测试/基准辅助：共用参考版 parser（fast 是 L09_mltt 的子模块，可见
/// 私有 parser；产出的 `Decl` 同时喂参考版与快版的 bench 口径）。
pub(crate) fn parse(input: &str, path_id: u32) -> Result<Vec<Decl>, String> {
    match super::parser::parser(&super::preprocess(input), path_id) {
        Some((ast, _errs)) => Ok(ast),
        None => Err("parse failed".to_owned()),
    }
}

/// 解析产出的 decl AST 类型别名（测试/基准用；Decl 本身的 use 是私有的）。
pub(crate) type SourceDecl = Decl;

// 基准负载生成器（L09 语法子集：`Type N` 宇宙、string_concat、enum/match、
// 递归 def、struct/new）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （nf 节点数与 L06/L08 同为 2n + 4）。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "def Nat : Type 1 = (N : Type 0) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

/// strchain 2^(k+1)：每层 `string_concat s_{i-1} "x"`——每层一次 builtin
/// 触发（eval 的 env 双槽字面量拼接），末值是长度 n 的字面量（nf 节点数
/// = 1）。
pub(crate) fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

/// match 2^(k+1)：每层一个**自递归**的依赖 match def——global 占位/覆盖
/// + check_pm 精化 + 运行时首匹配 + 卡住 match 在 check 期与 quote 期
/// （分支体中性重求值）的协同。
pub(crate) fn match_src(k: u32) -> String {
    let mut s = String::from("enum Nat {\n    zero\n    succ(x: Nat)\n}\n");
    for i in 0..=k {
        s += &format!(
            "def f_{i}(x : Nat) : Nat =\n    match x {{\n        case zero => zero\n        case succ(n) => succ (f_{i} n)\n    }}\n"
        );
    }
    s += &format!(
        "def two : Nat = succ (succ zero)\nprintln (f_{k} two)\n"
    );
    s
}

/// enum 负载：多 enum + 依赖索引（Vec 风格 GADT）+ 投影 + 索引等式（Eq）
/// + 递归 length——覆盖 Sum/SumCase 值的 unify / quote / rename 全链路。
pub(crate) fn enum_src() -> String {
    String::from(
        r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def t = cons zero (cons two nil)

println t.len

def ok : Eq two two = refl

def length[T, l: Nat](x: Vec[T] l): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (length xs)
    }

println (length t)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def rep[n: Nat](x: Vec[Nat] n): Nat =
    match x {
        case nil => zero
        case cons(h, xs) => add h (rep xs)
    }

println (rep (cons two (cons two nil)))
"#,
    )
}

/// struct 负载（L09 语义子集）：两层嵌套 struct（`Line{a, b: P}`）+
/// 规模按 2^(k+1) 的**浅值投影 def 链**（每层一次构造子 β + 类型级投影
/// + 合一）。末值 = `zero`（nf 节点数 = 2：SumCase + typ 的 Sum 两个
/// 节点）。注：L09 参考版的 `.mk` 剥链带 U(0) 占位怪癖，三层嵌套 struct
/// 的构造子应用两版一致地 Err——负载避开该形态（parity 不受影响）。
pub(crate) fn struct_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         struct P {
    x: Nat
    y: Nat
}

         struct Line {
    a: P
    b: P
}

         def get_x(p: P): Nat = p.x

         def q0 : Nat = get_x(new P(zero, zero))
",
    );
    for i in 1..n {
        s += &format!("def q{i} : Nat = get_x(new P(q{}, zero))
", i - 1);
    }
    s += &format!("println q{}
", n - 1);
    s
}
