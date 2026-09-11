//! 持久化列表的 arena 实现（`bytes_env_arena`/`bytes_env_arena_tm`/
//! `bytes_flat_value` 用它当环境）。
//!
//! 环境是不断 `prepend` 的单链表。arena 版把节点全部放进一个追加式 `Vec`，
//! 用 `NonZeroUsize` 下标代替 `Rc` 指针：节点一旦入表就永不失效，所以多次
//! 求值可以复用同一个 `ListArena`（基准正是这么做的），完全没有分配/释放。
//!
//! 哨兵约定（微妙，别改）：`new()` 预置下标 0，但环境的“空表”用下标 1 表示，
//! 而首次 `prepend` 恰好落在下标 1——于是链尾的“后继”指向自身，形成一个
//! 自环。`nth` 对**合法闭项**（索引深度 < 环境深度）永远走不到自环；一旦
//! 越界查表就会无限读出第一个绑定（静默、不报错），所以此实现只对闭项成立。
//! 用下标 0 当空表哨兵的话 `NonZeroUsize` 就用不上了，得不偿失。

use std::num::NonZeroUsize;

pub struct ListArena<T>(Vec<(T, Option<NonZeroUsize>)>);

impl<T: Default> ListArena<T> {
    pub fn new() -> Self {
        Self(vec![(T::default(), None)])
    }
}

impl<T> ListArena<T> {
    pub fn alloc(&mut self, value: T) -> NonZeroUsize {
        let index = self.0.len();
        self.0.push((value, None));
        // SAFETY: `len()` 从 1 起（`new` 预置下标 0），且 push 只会让长度继续
        // 增长，故 index ≥ 1，永不为 0。
        unsafe { NonZeroUsize::new_unchecked(index) }
    }

    /// 空环境哨兵（下标 1，语义见模块头）。
    ///
    /// 它不是 arena 里预先存在的槽位——首次 `prepend` 才落在下标 1 并把链尾
    /// 后继指回自身形成自环。因此本值只能在**首次 prepend 之前**作为空环境
    /// 传递，且只有闭项（索引深度 < 环境深度）的 `nth` 不会走到哨兵；开项
    /// 误用会在 release 下静默读到首个绑定（见 `nth`）。用这个名字取代各处
    /// 手写的 `NonZeroUsize::new_unchecked(1)`，让哨兵约定只有一个定义点。
    pub fn empty() -> NonZeroUsize {
        // SAFETY: 1 != 0，NonZeroUsize 的构造前提成立。
        unsafe { NonZeroUsize::new_unchecked(1) }
    }

    pub fn prepend(&mut self, list: NonZeroUsize, value: T) -> NonZeroUsize {
        let index = self.0.len();
        self.0.push((value, Some(list)));
        // SAFETY: 同 `alloc`，`len()` ≥ 1。
        unsafe { NonZeroUsize::new_unchecked(index) }
    }

    pub fn nth(&self, list: NonZeroUsize, idx: usize) -> &T {
        let mut list = list;
        for _ in 0..idx {
            // SAFETY: 契约是「闭项」——`idx < 环境深度`，步进次数不足以越过
            // 最后一个真实节点，故 `list.get()` 恒落在已初始化槽位内。
            let node = unsafe { self.0.get_unchecked(list.get()) };
            // 越界防护（debug 构建）：合法闭项的查找步数 < 环境深度，绝不会
            // 从链尾哨兵（自环，下标 1）再步进——这里提前炸出误用；release
            // 零成本。残余缺口：arena 跨轮复用后恰好多一步（idx == 深度）
            // 会落在哨兵槽读到轮 1 的旧值，只此一档静默（结构上不可区分）。
            debug_assert!(
                node.1 != Some(list),
                "ListArena::nth 越界：闭项不应从链尾哨兵（自环）再步进"
            );
            // SAFETY: 同上——契约保证步进后仍有真实节点，`next` 为 Some。
            list = unsafe { node.1.unwrap_unchecked() };
        }
        // SAFETY: 契约保证最终落点（含 idx == 0 的空环境、首次 prepend 后
        // 的下标 1）是已初始化槽位。
        unsafe { &self.0.get_unchecked(list.get()).0 }
    }
}