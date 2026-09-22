//! spine：扁平中性栈（`Spine`/`Entry`/链头种类 `HK_*`）与 metacontext
//! （`MetaSnap`/`MetaEntry`/`meta_val_of`）及其就地写撤销日志（`journal_meta`
//! 族）。原 bump_spine_iter.rs 的 "spine 栈（扁平中性）" 与 "metacontext"
//! 两节的对应条目，逐行搬运（2026-09-23 拆分）。

use std::rc::Rc;

use super::parser::syntax::Icit;

use super::force::META_JOURNAL;
use super::machine::{Cxt, TCons};
use super::prim::Decls;
use super::syntax::{V, XCell, v_meta, v_meta_of, v_spine, v_spine_of, v_tag, v_xcell_of};


// spine 栈（扁平中性）
// --------------------------------------------------------------------------------

/// 链头种类（`Entry.hk`）：push 时随函数侧传播，O(1) 判定链头是 Flex（force
/// 的 meta 展开臂）/ Decl（force 的 prim 臂）/ 卡住投影 Obj（unify 的位相等
/// 捷径对它关闭）还是其它（Rigid——force 直接原样返回）。
pub(super) const HK_OTHER: u8 = 0;
pub(super) const HK_FLEX: u8 = 1;
pub(super) const HK_DECL: u8 = 2;
pub(super) const HK_OBJ: u8 = 3;

/// spine 栈槽：一次中性应用（icit 随槽携带）。`len`/`base` 支撑流式右链
/// quote；`hk` 记录链头种类（push 时随函数侧传播）。链头只可能是 Rigid /
/// Flex / Decl / 卡住投影 Obj（其余形态 v_app 即 panic，进不了链）。
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
    /// 中性应用 `f a`（icit i）压栈，返回句柄值。`hk` 随函数侧传播：裸单元
    /// 直查种类，既有链延伸保持原种类（顶端槽已记下头种类）。
    #[inline]
    pub(super) fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let hk = match v_tag(f) {
            5 => HK_FLEX,
            7 => match v_xcell_of(f) {
                XCell::Obj { .. } => HK_OBJ,
                XCell::Decl { .. } => HK_DECL,
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

/// 值侧头种类判定（裸单元直查；链查顶端槽的 `hk` 标志，O(1)，无需沿链走底）。
#[inline]
pub(super) fn head_kind(spine: &Spine, v: V) -> u8 {
    match v_tag(v) {
        5 => HK_FLEX,
        7 => match v_xcell_of(v) {
            XCell::Obj { .. } => HK_OBJ,
            XCell::Decl { .. } => HK_DECL,
            _ => HK_OTHER,
        },
        2 => spine.stack[v_spine_of(v)].hk,
        _ => HK_OTHER,
    }
}

/// 值是否 Flex（裸未解 meta 立即数或 meta 头的链）。
#[inline]
pub(super) fn is_flex(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        5 => true,
        2 => spine.stack[v_spine_of(v)].hk == HK_FLEX,
        _ => false,
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// meta 创建时刻的上下文快照（参考版 `Arc<Cxt>` 的孪生：错误路径的
/// pretty/lvl/decls 重建 **+ 求解时用创建处上下文**）。`'static` 存放口径
/// 同工作栈（跨轮 reset 前一切句柄已消亡）。
pub(crate) struct MetaSnap<'a> {
    /// meta 创建时的层级。
    pub(crate) lvl: u32,
    /// 名字 telescope（pretty 的 names 用）。
    pub(crate) types: Option<&'a TCons<'a>>,
    /// decl 表快照（错误路径 quote/eval 用）。
    pub(crate) decls: Rc<Decls<'a>>,
    /// **完整上下文快照**（参考版 `MetaEntry::Unsolved(v, Arc<Cxt>, ..)`
    /// 的第二元）：`solve_multi_trait` 必须用 **meta 创建处**的上下文求解，
    /// 不能用调用方的——goal 里的 Rigid 层级按创建处 de Bruijn 编号，换用
    /// 浅上下文会让 rename/quote 算出越界变量（HDL prelude decl 308 的
    /// `impl Add for UInt[width]`：meta 创建于 lvl=4，被以 lvl=0 求解，
    /// 报 `Into[Nat, UInt[Variable index out of bounds]]`）。
    pub(crate) cxt: Cxt<'static>,
}

/// metacontext 条目（参考版 L13 四元同构）：**类型一律保留**（pruning 检查
/// 与 `lams` 都要读）；第二元 = 创建时刻的上下文快照（no_metas 错误路径）；
/// 第三元 = 创建时的开放类型（错误消息 pretty 与 oty 检查用）；第四元 =
/// 创建处 span（no_metas 报错定位——快版全零 span，字段保留对齐参考版
/// 形状）。解是 bump 内的打包值。Clone 供 temp-infer 探测的快照换入换出。
#[derive(Clone)]
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V, Rc<MetaSnap<'static>>, V, crate::parser_lib::Span<()>),
}

/// 取未解条目的（闭类型, 快照, 原始类型, span）。非未解 → unreachable。
#[inline]
pub(crate) fn meta_unsolved<'a>(m: &MetaEntry) -> (V, &'a MetaSnap<'a>, V, crate::parser_lib::Span<()>) {
    match m {
        MetaEntry::Unsolved(a, snap, o, sp) => {
            let snap: &'a MetaSnap<'a> = unsafe { &*(snap.as_ref() as *const MetaSnap<'static> as *const MetaSnap<'a>) };
            (*a, snap, *o, *sp)
        }
        _ => unreachable!(),
    }
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
pub(super) fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(..) => v_meta(m),
    }
}

/// meta 就地写统一入口：journal 激活时先记旧值再写新值。
pub(super) fn journal_meta(metas: &mut [MetaEntry], m: usize, entry: MetaEntry) {
    META_JOURNAL.with(|j| {
        if let Some(top) = j.borrow_mut().last_mut() {
            top.push((m, metas[m].clone()));
        }
    });
    metas[m] = entry;
}

/// journal 回滚：逆序恢复旧值（跳过探测期新增下标），然后截断 append。
/// 返回值无；`metas` 由调用方在恢复后 truncate 到探测前长度。
pub(super) fn meta_journal_rollback(metas: &mut Vec<MetaEntry>, pre_len: usize) {
    let top = META_JOURNAL.with(|j| j.borrow_mut().pop());
    if let Some(log) = top {
        for (idx, old) in log.iter().rev() {
            if *idx < pre_len {
                metas[*idx] = old.clone();
            }
        }
    }
    metas.truncate(pre_len);
}

/// journal 帧丢弃（探测**成功**路径）：帧内记录的全部保留（就地写与
/// append 都成立），只把帧从栈上拿掉。与 [`meta_journal_rollback`] 成对——
/// 失败回滚、成功丢弃，两路径都必须出帧，否则后续写点记错层。
pub(super) fn meta_journal_discard() {
    META_JOURNAL.with(|j| {
        j.borrow_mut().pop();
    });
}
