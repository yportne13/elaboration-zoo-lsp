//! syntax：bump 内的项表示（`Tm`/`PrCons`/`LCons`）与打包值（`V`/`XCell`）
//! 及其 v_* 构造/访问器。原 bump_spine_iter.rs 的 "syntax（bump 内的项
//! 表示）" + "values（打包值）" 两节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;

use super::parser::syntax::Icit;
use super::env::{CloCell, PiCell};

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
/// `AppPruning` 是洞形态：头（实践中恒为 `Meta`）+ scope 掩码。
/// L06 增量：`LiteralType` / `LiteralIntro` / `Decl`（按名查 decl 表）。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    /// 把头按掩码应用到求值环境：`Some(icit)` 槽位以该 icit 应用实参，
    /// `None` 槽位跳过。
    AppPruning(&'a Tm<'a>, Option<&'a PrCons<'a>>),
    U,
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    Meta(u32),
    /// String 字面量的类型（`String`）。
    LiteralType,
    /// 字符串字面量（内容即值）。
    LiteralIntro(&'a str),
    /// 按名 decl 表查找：求值命中给登记值，miss 保持卡住的 Decl 头。
    Decl(&'a str),
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
    /// 链形态缓存：`Some(k)` = 自本节点起头 k 个全是 bind 槽且其后全
    /// define（`k=0` = 纯 define 链）。构造时 O(1) 维护，
    /// [`bind_prefix_of_telescope`] 读缓存 O(1)——旧实现每次全链走查
    /// O(D)，fresh_meta 每定义 4-6 次 → prune 负载 O(D²)（k=13 实测
    /// 23 s，评审 D-F1 与 L05 同款）。
    pub(super) prefix: Option<u32>,
}

impl<'a> LCons<'a> {
    /// 构造 + 形态缓存维护（bind：1 + 后继缓存；define：后继为空或纯
    /// define 链才 `Some(0)`，交错/未知一律 `None` 走回退）。
    pub(super) fn alloc(
        bump: &'a Bump,
        name: &'a str,
        a_t: &'a Tm<'a>,
        t_t: Option<&'a Tm<'a>>,
        next: Option<&'a LCons<'a>>,
    ) -> &'a LCons<'a> {
        let prefix = match t_t {
            None => match next {
                None => Some(1),
                Some(n) => n.prefix.map(|k| k + 1),
            },
            Some(_) => match next {
                None => Some(0),
                Some(n) if n.prefix == Some(0) => Some(0),
                _ => None,
            },
        };
        bump.alloc(LCons {
            name,
            a_t,
            t_t,
            next,
            prefix,
        })
    }
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Lvl(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U`（立即数）、`4=Pi(ptr|4)`、`5=Meta(m<<3|5)`
/// （未解 meta 立即数）、`6=LiteralType`（立即数，L06）、`7=XCell(ptr|7)`
/// （字面量或 Decl 头，L06）。icit 不进打包字——由 Clo/Pi 单元与 spine 槽
/// 携带（打包字是 quote/unify 记忆化的键，icit 随值结构唯一确定）。
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
pub(crate) fn v_u() -> V {
    V(3)
}
#[inline]
pub(crate) fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
pub(crate) fn v_meta(m: u32) -> V {
    V(((m as u64) << 3) | 5)
}
/// `LiteralType` 立即数（同 `U` 的编码方式：tag 本身即值）。
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
    // SAFETY: 调用方已确认 `v_tag(v) == 1`；`CloCell` 由 bump 分配，
    // 对齐 ≥ 8 由 `#[repr(align(8))]` 保证（含 wasm32，低 3 位恒 0），
    // `& !7` 还原的即原指针；`'a` 由 bump 生命期覆盖。
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    // SAFETY: 调用方已确认 `v_tag(v) == 4`；`PiCell` 由 bump 分配，
    // 对齐 ≥ 8 由 `#[repr(align(8))]` 保证（含 wasm32，低 3 位恒 0），
    // `& !7` 还原的即原指针；`'a` 由 bump 生命期覆盖。
    unsafe { &*((v.0 & !7) as *const PiCell) }
}
#[inline]
pub(crate) fn v_meta_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
/// tag 7 单元解引用（bump 内分配，本轮内有效）。
#[inline]
pub(crate) fn v_xcell_of<'a>(v: V) -> &'a XCell<'a> {
    // SAFETY: 调用方已确认 `v_tag(v) == 7`；`XCell` 由 bump 分配，
    // 对齐 ≥ 8 由 `#[repr(align(8))]` 保证（含 wasm32，低 3 位恒 0），
    // `& !7` 还原的即原指针；`'a` 由 bump 生命期覆盖。
    unsafe { &*((v.0 & !7) as *const XCell) }
}

/// tag 7 的两种载体：字符串字面量（惰性无害值）与卡住的按名 Decl 头。
/// 名字内容只在 pretty / prim 里用；判等按单元指针（同内容不同次求值
/// 各造单元——与参考版每次 `Rc::new` 同构）。
///
/// `repr(align(8))`：本类型被 `v_xcell` 以 `ptr | 7` 打包、`v_xcell_of` 以
/// `& !7` 还原，要求 bump 分配地址低 3 位为 0。64 位目标 `&str` 自然对齐 8，
/// 但 wasm32（`&str` = 8B/align 4）上 `align_of == 4`，`& !7` 会清掉 bit2
/// 还原出错误指针（UB）——显式钉到 8 对齐在所有目标上都成立。64 位下布局
/// 与原先逐字节一致（align 本已为 8），零行为变化。
#[repr(align(8))]
pub(crate) enum XCell<'a> {
    Lit(&'a str),
    Decl(&'a str),
}

// packed tag 解码（`& !7`）依赖 ≥8 对齐；断言在编译期钉住，含 wasm32。
const _: () = assert!(std::mem::align_of::<XCell<'static>>() >= 8);
