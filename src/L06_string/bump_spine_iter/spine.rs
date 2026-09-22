//! spine：扁平中性栈（`Spine`/`Entry` 与 Decl 头判定 `is_declheaded`/
//! `decl_name`）与 metacontext（`MetaEntry`/`meta_val_of`）。
//! 原 bump_spine_iter.rs 的 spine 栈与 "metacontext" 两段，逐行搬运
//! （2026-09-23 拆分）。

use super::parser::syntax::Icit;

use super::machine::{ReclaimOnClear, SPINE_SHRINK_MIN_ENTRIES};
use super::syntax::{V, XCell, v_meta, v_meta_of, v_spine, v_spine_of, v_tag, v_xcell_of};

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`decl` 标志函数侧是否 Decl 头（builtin 的增量触发要 O(1) 判定，
/// 不 walks 链——见 [`is_declheaded`]）。
pub(super) struct Entry {
    pub(super) f: V,
    pub(super) a: V,
    pub(super) icit: Icit,
    pub(super) len: u32,
    pub(super) base: u32,
    decl: bool,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    pub(super) stack: Vec<Entry>,
}

impl Spine {
    /// 轮清空（随 [`Machine::clear_round`] 调用）：`Entry` 是无 Drop 的
    /// Copy 结构，清空只把长度归零（O(1)），槽位下标从 0 重排，与
    /// `Machine::new` 同构。不清则稳态复用下 spine 随轮数单调增长（内存
    /// 滞留到历史最大 spine 深度 + 偶发大 Vec 扩容拷贝）；容量到过
    /// `SPINE_SHRINK_MIN_ENTRIES` 时清空顺带归还缓冲，否则峰值容量随常驻
    /// Machine 到进程结束（与 L13 孪生版 `spine.stack.reclaim` 同口径）。
    #[inline]
    pub(super) fn clear(&mut self) {
        let _ = self.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES);
    }

    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`decl` 随函数侧传播：
    /// 裸 Decl 单元或既有 decl 链延伸——后续应用可 O(1) 判定要触发 prim。
    #[inline]
    pub(super) fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let decl = match v_tag(f) {
            7 => matches!(v_xcell_of(f), XCell::Decl(_)),
            2 => self.stack[v_spine_of(f)].decl,
            _ => false,
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
            decl,
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

    /// 链长（decl_apply 的元数预检：元数不足时不收集、零分配）。
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

/// 函数侧是否 Decl 头（builtin 触发判定）：裸单元直查；链查**顶端槽**的
/// `decl` 标志（push 时随函数侧传播，O(1)）。
#[inline]
pub(super) fn is_declheaded(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        7 => matches!(v_xcell_of(v), XCell::Decl(_)),
        2 => spine.stack[v_spine_of(v)].decl,
        _ => false,
    }
}

/// 取 Decl 头的名（调用方已 `is_declheaded`）。
#[inline]
pub(super) fn decl_name<'a>(spine: &Spine, v: V) -> &'a str {
    let head = if v_tag(v) == 7 {
        v
    } else {
        spine.spine_head(v_spine_of(v))
    };
    match v_xcell_of(head) {
        XCell::Decl(n) => n,
        XCell::Lit(_) => unreachable!("Lit 头不可触发"),
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。
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
