//! spine：扁平中性栈（`Spine`/`Entry`/链头种类 `HK_*`）与 metacontext
//! （`MetaEntry`/`meta_val_of`）。原 bump_spine_iter.rs 的 "spine 栈" 与
//! "metacontext" 两节，逐行搬运（2026-09-19 拆分）。

use super::parser::syntax::Icit;

use super::machine::{ReclaimOnClear, SPINE_SHRINK_MIN_ENTRIES};
use super::syntax::{V, XCell, v_meta, v_spine, v_meta_of, v_spine_of, v_tag, v_xcell_of};

// spine 栈（扁平中性）
// --------------------------------------------------------------------------------

/// 链头种类（`Entry.hk`）：push 时随函数侧传播，O(1) 判定链头是 Decl /
/// Prim / Obj（force 的三分派）还是其它（Rigid/Flex/Lit——直接中性）。
const HK_OTHER: u8 = 0;
pub(super) const HK_DECL: u8 = 1;
pub(super) const HK_PRIM: u8 = 2;
pub(super) const HK_OBJ: u8 = 3;

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`hk` 记录链头种类（push 时随函数侧传播）。
pub(super) struct Entry {
    pub(super) f: V,
    pub(super) a: V,
    pub(super) icit: Icit,
    pub(super) len: u32,
    pub(super) base: u32,
    pub(super) hk: u8,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    pub(super) stack: Vec<Entry>,
}

impl Spine {
    /// 轮清空（随 `Machine::clear_round` 调用）：V 句柄的全部载体
    /// （metas/defs/name_map/name_trail/mutable_map 在同一函数里
    /// 清空，decl Rc 随上轮 Cxt 在轮界释放）——陈旧句柄流不进新轮，
    /// 槽位下标从 0 重排与 `Machine::new` 同构。不清则稳态复用下 spine
    /// 随轮数线性增长（慢泄漏 + 偶发大 Vec 扩容拷贝）；容量到过
    /// `SPINE_SHRINK_MIN_ENTRIES` 时清空顺带归还缓冲，否则峰值容量随常驻
    /// Machine 到进程结束（与 L13 孪生版 `spine.stack.reclaim` 同口径）。
    pub(super) fn clear(&mut self) {
        let _ = self.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    }

    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`hk` 随函数侧传播：
    /// 裸 XCell 直查种类，既有链延伸保持原种类。
    #[inline]
    pub(super) fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let hk = match v_tag(f) {
            7 => match v_xcell_of(f) {
                XCell::Decl(_) => HK_DECL,
                XCell::Prim(_) => HK_PRIM,
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
        self.stack.push(Entry {
            f,
            a,
            icit,
            len,
            base,
            hk,
        });
        v_spine(idx)
    }

    /// 沿 `f` 指针走到链的最底层头（f 指针严格指向更早的槽位，必终止）。
    #[inline]
    pub(super) fn spine_head(&self, h: usize) -> V {
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
    pub(super) fn collect_args(&self, h: usize, out: &mut Vec<(V, Icit)>) {
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
    pub(super) fn spine_len(&self, h: usize) -> usize {
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
    pub(super) fn flex_of(&self, v: V, out: &mut Vec<(V, Icit)>) -> Option<u32> {
        match v_tag(v) {
            5 => Some(v_meta_of(v)),
            2 => {
                let h = v_spine_of(v);
                let hd = self.spine_head(h);
                if v_tag(hd) != 5 {
                    return None;
                }
                self.collect_args(h, out);
                Some(v_meta_of(hd))
            }
            _ => None,
        }
    }
}

/// 值侧头种类判定（裸单元直查；链查顶端槽的 `hk` 标志，O(1)）。
#[inline]
pub(super) fn head_kind(spine: &Spine, v: V) -> u8 {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Decl(_) => HK_DECL,
            XCell::Prim(_) => HK_PRIM,
            XCell::Obj { .. } => HK_OBJ,
            _ => HK_OTHER,
        },
        2 => spine.stack[v_spine_of(v)].hk,
        _ => HK_OTHER,
    }
}

/// 链（或裸单元）是否 Obj 头——unify 的位相等捷径对它关闭（参考版无
/// `(Obj, Obj)` 臂，同单元也须走 `_` → Err）。
#[inline]
pub(super) fn is_objheaded(spine: &Spine, v: V) -> bool {
    head_kind(spine, v) == HK_OBJ
}

/// 取链（或裸单元）头的 Decl / Prim 名（调用方已判定头种类）。
#[inline]
pub(super) fn xcell_head_name<'a>(spine: &Spine, v: V) -> &'a str {
    let head = if v_tag(v) == 7 {
        v
    } else {
        spine.spine_head(v_spine_of(v))
    };
    match v_xcell_of(head) {
        XCell::Decl(n) => n,
        XCell::Prim(n) => n,
        _ => unreachable!("头名只对 Decl/Prim 链取"),
    }
}

/// 值是否 Flex（裸未解 meta 立即数或 meta 头的链）。unify 的 pm 特化臂
/// 要求另一侧"非 Flex"（交给 Flex 规则 meta := 值）。
#[inline]
pub(super) fn is_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 => true,
        2 => v_tag(spine.spine_head(v_spine_of(v))) == 5,
        _ => false,
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。Clone 供 flex_flex 的快照回滚。
#[derive(Clone)]
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V),
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
pub(super) fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(_) => v_meta(m),
    }
}
