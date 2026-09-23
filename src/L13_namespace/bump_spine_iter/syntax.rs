//! syntax：bump 内的项表示（`Tm`/`PrCons`/`LCons`）与打包值（`V`/`XCell`/
//! `SumParamV`/`SumDataV`）及其 v_* 构造/访问器。原 bump_spine_iter.rs 的
//! "syntax" 与 "values" 两节（decl 表条目归 prim、环境与闭包单元归 env），
//! 逐行搬运（2026-09-23 拆分）。

use super::parser::syntax::Icit;

use super::env::{CloCell, Env, PiCell};
use super::PatternDetail;


// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
pub(crate) enum Tm<'a> {
    Var(u32),
    /// 全局声明的名字引用（参考版 `Tm::Decl(Span<String>)`；名字是 bump
    /// 内的 str，pretty 直接打印——namespace 限定键原样输出）。
    Decl(&'a str),
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
    /// `x.field` 投影（参考版 `Tm::Obj`；字段名只服务 pretty/查表）。
    Obj(&'a Tm<'a>, &'a str),
    /// enum 类型本体（enum 声明 λ 链的体）。params = (参数名, 值项, 类型项,
    /// icit)，声明处值项即参数自身；实例化后值槽携带当前实参。
    /// `is_trait`：trait 脱糖的 enum（fresh_meta 走实例合成）。
    Sum(&'a str, &'a [SumParamT<'a>], &'a [&'a str], bool),
    /// 构造子值：typ 求值后必须是其所属的（已实例化的）`Sum`。case 以
    /// **index** 标识（所属 Sum 的 cases 表下标，参考版 L13 同款），名字
    /// 反查 `cases[index]`。
    SumCase {
        typ: &'a Tm<'a>,
        index: u32,
        datas: &'a [SumDataT<'a>],
        is_trait: bool,
    },
    /// 已编译的 match：分支体是检查过的项，运行时按模式首匹配。
    Match(&'a Tm<'a>, &'a [(PatternDetail, &'a Tm<'a>)]),
    /// 内联调用（参考版 `Tm::Call` / `Tm::OpCall` 的合一）：`name` 是被内联
    /// 的 def 名，args 是 λ 链参数的 `Var` 引用（带 icit，**List 序**：外层
    /// 参数在前——`wrap_match_in_call` 的构造序），body 是原 match 体。eval
    /// 的 Call 帧"body 求值结果卡 Match 才包 `Val::Call`"。参考版的显示专用
    /// `OpCall`（quote 查 `symbol_table` 产中缀/前缀节点）在快版由
    /// [`export`] 以同一规则决定——本机 Tm 不区分，求值行为本就一致。
    Call(&'a str, &'a [(&'a Tm<'a>, Icit)], &'a Tm<'a>),
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
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Rigid(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U(lvl<<3|3)`（宇宙层级进打包字）、`4=Pi(ptr|4)`、
/// `5=Meta(m<<3|5)`（未解 meta 立即数）、`6=LiteralType`（立即数）、
/// `7=XCell(ptr|7)`（字面量 / Prim / 卡住投影 / Sum / SumCase / Match）。
/// icit 不进打包字——由 Clo/Pi 单元与 spine 槽携带（打包字是 quote/unify
/// 记忆化的键，icit 随值结构唯一确定）。
#[derive(Clone, Copy, PartialEq, Eq)]
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

/// 层级 → de Bruijn 索引：`level - l - 1`（参考版 `mod.rs::lvl2ix` 同口径，
/// 孪生此前是 4 处裸减法——加固漏移植）。
///
/// 加 checked 运算与诊断消息的理由与参考版逐字相同：越界层级意味着一个
/// **精化期变量泄漏进了 quote**（typeclass 实例 Nat 参数 bug —
/// `docs/l13-typeclass-instance-nat-param-bug.md` — 与
/// `docs/l13-known-bugs-2026-08.md` Bug 2）。裸减法在 debug 下 panic 成
/// `attempt to subtract with overflow`、**release 下 wrap 成巨大 u32 让
/// 下游行为随机**；`tests/l13_into_probe.rs` 的 v7 探针（hdl-ops 字段投影
/// 形态）正好落在该路径上，两版因此报出不同形态的失败。
#[inline]
pub(crate) fn lvl2ix(level: u32, l: u32) -> u32 {
    level
        .checked_sub(l)
        .and_then(|v| v.checked_sub(1))
        .unwrap_or_else(|| {
            panic!(
                "lvl2ix: level {} is out of scope for a context of level {} — a dangling \
                 elaboration-time variable leaked into a quote (see \
                 docs/l13-typeclass-instance-nat-param-bug.md)",
                l, level
            )
        })
}
#[inline]
pub(crate) fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    // SAFETY: v 是 `v_clo` 写出的 tag 1 打包字（`ptr|1`）。`CloCell` 由
    // `#[repr(align(8))]` 保证 ≥8 对齐，`& !7` 恰好还原分配地址；生命周期
    // 由调用方按 bump 轮次不变式（reset 前句柄消亡）担保。
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    // SAFETY: v 是 `v_pi` 写出的 tag 4 打包字（`ptr|4`）。`PiCell` 含 `V(u64)`

    // 字段故天然 ≥8 对齐（下方 const 断言钉住），`& !7` 还原分配地址。

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
    // SAFETY: v 是 `v_xcell` 写出的 tag 7 打包字（`ptr|7`）。`XCell` 由
    // `#[repr(align(8))]` 保证 ≥8 对齐（含 wasm32），`& !7` 恰好还原分配地址。
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
#[derive(Clone, Copy)]
pub(crate) struct SumDataV<'a> {
    pub(super) name: &'a str,
    pub(super) val: V,
    pub(super) icit: Icit,
}

/// tag 7 的载体：字面量值、原生 Nat、卡住声明引用、卡住投影、和类型
/// 本体、构造子值、内联调用、卡住 match。判等按单元指针（同内容不同次
/// 求值各造单元——与参考版每次构造新值同构）；**位相等捷径对 tag 7
/// 关闭**（见模块注释）。
///
/// `#[repr(align(8))]`：packed 编码用 `ptr | 7` 写、`v.0 & !7` 读回，要求
/// 单元地址低 3 位为 0。64 位目标 `&str` 已 8 对齐，但 wasm32 上 `&str`
/// 仅 4 字节对齐，故显式钉死 ≥8（下方有编译期断言）。
#[repr(align(8))]
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    /// 原生 Nat（参考版 `Val::Nat(u64)`，Lean/Agda 式压缩）：定义上等于
    /// `succ^n zero` 的值用单个 u64 持有。WHNF 叶（force 原样返回）；
    /// quote 经 `quote_nat` 展开回 SumCase 链。
    Nat(u64),
    /// 卡住的声明引用（参考版 `Val::Decl(name, sp)` 的裸头）：decl 表
    /// 未登记 / 递归自引用的存根 / prim 卡住（`None`）。带实参的卡住
    /// 声明 = spine 链（头 = 本单元），v_app 对 Decl 头压 spine。
    Decl { name: &'a str },
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
    /// 构造子值：typ 求值后是其所属的已实例化 `Sum`；case 以 index 标识。
    SumCase {
        typ: V,
        index: u32,
        datas: &'a [SumDataV<'a>],
        is_trait: bool,
    },
    /// 内联调用值（参考版 `Val::Call`）：name + 实参（带 icit）+ 体（卡
    /// Match）。v_app 对它 args prepend + 对 body 递归 v_app。
    Call {
        name: &'a str,
        args: &'a [(V, Icit)],
        body: V,
    },
    /// 卡住 match：scrutinee（创建时已 force）+ 捕获 env + 编译分支。
    /// 无 pending（参考版 L13 同款）；v_app 对 Match 把应用 splice 进
    /// 每个分支体（参考版 mod.rs 的 Match 臂）。
    Match {
        scrutinee: V,
        env: Env<'a>,
        cases: &'a [(PatternDetail, &'a Tm<'a>)],
    },
}
