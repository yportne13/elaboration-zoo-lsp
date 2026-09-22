//! env：复合环境（平坦 def 区域 + 持久 binder 链）与闭包/Π 单元
//! （`CloCell`/`PiCell`）及 packed-word 对齐断言。原 bump_spine_iter.rs 的
//! env 段（原文件无独立分节线，位于 SpecSolve/DeclEntry 之后、spine 栈
//! 之前，按内容归属），逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;

use super::parser::syntax::Icit;

use super::syntax::{Tm, V, XCell};

/// 复合环境：**平坦 def 区域**（elaborator 的 define 链，指入每轮
/// [`Machine::defs`]；tip 环境原地追加，`nth` O(1)；**非 tip 环境**
/// （λ 体内的 define 先占位后、外层再 define）回落到 binder 链——索引
/// 语义一致，仅查链 O(链深)）+ **持久 binder 链表**。机制与论证同 L03-L06。
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    pub(super) flat_base: u32,
    pub(super) flat_len: u32,
    pub(super) binds: Option<&'a EnvCons<'a>>,
}

pub(super) const EMPTY_ENV: Env<'static> = Env {
    flat_base: 0,
    flat_len: 0,
    binds: None,
};

/// 环境链表节点（bump 内持久链表，头 = 最内层绑定）。
pub(crate) struct EnvCons<'a> {
    pub(super) val: V,
    pub(super) next: Option<&'a EnvCons<'a>>,
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
#[repr(align(8))]
pub(crate) struct CloCell<'a> {
    pub(super) name: &'a str,
    pub(super) icit: Icit,
    pub(super) env: Env<'a>,
    pub(super) body: &'a Tm<'a>,
}

/// Π 值单元：名字 + icit + 定义域值 + 余定义域闭包（内联，一次分配）。
pub(crate) struct PiCell<'a> {
    pub(super) name: &'a str,
    pub(super) icit: Icit,
    pub(super) dom: V,
    pub(super) env: Env<'a>,
    pub(super) body: &'a Tm<'a>,
}

/// 编译期钉住所有经 `ptr|tag` 编码的单元类型 ≥8 对齐：`v_clo`/`v_pi`/
/// `v_xcell` 写 `ptr|tag`，对应 `v_*_of` 用 `& !7` 解引用，地址低 3 位必须
/// 为 0。64 位目标天然满足；wasm32（`&str` 仅 4 对齐）靠上面的
/// `#[repr(align(8))]`。`EnvCons` 不直接经 packed 字编码（env 走直接引用），
/// 但同样断言以钉住 packed 值字段的对齐不变式。
const _: () = {
    assert!(std::mem::align_of::<XCell<'static>>() >= 8);
    assert!(std::mem::align_of::<CloCell<'static>>() >= 8);
    assert!(std::mem::align_of::<PiCell<'static>>() >= 8);
    assert!(std::mem::align_of::<EnvCons<'static>>() >= 8);
};
