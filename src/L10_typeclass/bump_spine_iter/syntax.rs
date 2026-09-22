//! syntax：bump 内的项表示（`Tm`/`PrCons`/`LCons`）与打包值（`V`/`XCell`）
//! 及其 v_* 构造/访问器。原 bump_spine_iter.rs 的 "syntax" + "values" 两节，
//! 逐行搬运（2026-09-23 拆分）。

use std::rc::Rc;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{CloCell, Env, PiCell};
use super::subst::SubstV;

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
    /// `is_trait`：trait 脱糖的 enum（fresh_meta 走实例合成）。
    Sum(&'a str, &'a [SumParamT<'a>], &'a [&'a str], bool),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Sum`。
    SumCase {
        typ: &'a Tm<'a>,
        case_name: &'a str,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
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
    pub(super) slot: Option<Icit>,
    /// 本节点向外（next 方向）连续 `None`（define 槽）的个数；Some 槽为 0。
    pub(super) none_run: u32,
    /// 本 none-run 之后的第一个槽（Some 槽或链尾）——跳段的落点。
    pub(super) after_run: Option<&'a PrCons<'a>>,
    pub(super) next: Option<&'a PrCons<'a>>,
}

impl<'a> PrCons<'a> {
    /// 入链构造（新槽恒为链头，最内层）。run 统计只读既有节点。
    pub(super) fn new(slot: Option<Icit>, next: Option<&'a PrCons<'a>>) -> Self {
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
pub(super) struct LCons<'a> {
    pub(super) name: &'a str,
    pub(super) a_t: &'a Tm<'a>,
    /// `Some` = define（闭成 Let），`None` = binder（闭成显式 Π）。
    pub(super) t_t: Option<&'a Tm<'a>>,
    pub(super) next: Option<&'a LCons<'a>>,
    /// define 槽的**已求值登记值**（评审 A-1：fresh_meta close 从「重求值
    /// 全链 def 项」改「值链直评」——登记值已在手（env_ext_defs 用的同一
    /// 个），免每次 close 对 stale 链逐条重求值；k=9 一轮 2.1M 个 Let 节点
    /// 重求值的载体）。binder 槽 None。
    pub(super) val: Option<V>,
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
    // SAFETY: 调用方保证 `v_tag(v) == 1`（Clo 指针立即数）；`& !7` 抹掉低 3
    // 位 tag 还原 bump 内 CloCell 地址，分配存活于本轮 Machine 的 'a。依赖
    // `CloCell` ≥8 对齐（`repr(align(8))` 保证，含 wasm32），否则 `& !7` 会
    // 清掉真实地址位。
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    // SAFETY: 调用方保证 `v_tag(v) == 4`（Π 指针立即数）；`& !7` 抹掉低 3 位
    // tag 还原 bump 内 PiCell 地址，分配存活于本轮 Machine 的 'a。依赖
    // `PiCell` ≥8 对齐（`dom: V` 保证；编译期断言钉住，含 wasm32）。
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
#[inline]
pub(crate) fn v_xcell_of<'a>(v: V) -> &'a XCell<'a> {
    // SAFETY: 调用方保证 `v_tag(v) == 7`（XCell 指针立即数）；`& !7` 抹掉低
    // 3 位 tag 还原 bump 内 XCell 地址，分配存活于本轮 Machine 的 'a。依赖
    // `XCell` ≥8 对齐（由 `repr(align(8))` 保证，含 wasm32——wasm 上 `&str`
    // 仅 4 对齐，若不钉住则 `& !7` 清掉 bit2 = UB）。
    unsafe { &*((v.0 & !7) as *const XCell) }
}

/// `Val::Sum` 的参数槽（值层，bump 内）。
#[derive(Clone)]
pub(crate) struct SumParamV<'a> {
    pub(super) name: &'a str,
    pub(super) val: V,
    pub(super) ty: V,
    pub(super) icit: Icit,
}

/// `Val::SumCase` 的字段槽（值层，bump 内）。
pub(crate) struct SumDataV<'a> {
    pub(super) name: &'a str,
    pub(super) val: V,
    pub(super) icit: Icit,
}

/// tag 7 的载体：字面量值、builtin 体标记、卡住投影、和类型本体、构造子
/// 值、卡住 match。判等按单元指针（同内容不同次求值各造单元——与参考版
/// 每次构造新值同构）；**位相等捷径对 tag 7 关闭**（见模块注释）。
///
/// 对齐：`v_xcell` 以 `ptr | 7` 编码、`v_xcell_of` 以 `& !7` 解码，要求单元
/// 地址低 3 位为 0（≥8 对齐）。64 位目标 `&str` 已 8 对齐；wasm32 上 `&str`
/// 仅 4 对齐，故显式 `repr(align(8))` 钉住（否则解码会清掉 bit2 → UB）。
#[repr(align(8))]
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    /// builtin 体标记（无名；v_app 对它 panic，故永无 Prim 头的链）。
    Prim,
    /// 卡住投影：被投影者 + 字段名。带实参的卡住投影 = spine 链（头 =
    /// 本单元），与参考版 `Val::Obj(v, name, sp)` 同构。
    Obj { val: V, name: &'a str },
    /// 和类型本体：名 + 参数槽（名/实参/实参类型/icit）+ 构造子名表 +
    /// is_trait（trait 脱糖的 enum）。
    Sum {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
        is_trait: bool,
    },
    /// 构造子值：typ 求值后是其所属的已实例化 `Sum`。
    SumCase {
        typ: V,
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
        is_trait: bool,
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
    /// 顶层不会是 VSub（本层无燃料，故不存在"耗尽返回 VSub"的例外）。
    VSub { val: V, sub: Rc<SubstV> },
}
