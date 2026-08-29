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
        unsafe { NonZeroUsize::new_unchecked(index) }
    }

    pub fn prepend(&mut self, list: NonZeroUsize, value: T) -> NonZeroUsize {
        let index = self.0.len();
        self.0.push((value, Some(list)));
        unsafe { NonZeroUsize::new_unchecked(index) }
    }

    pub fn nth(&self, list: NonZeroUsize, idx: usize) -> &T {
        let mut list = list;
        for _ in 0..idx {
            let node = unsafe { self.0.get_unchecked(list.get()) };
            // 越界防护（debug 构建）：合法闭项的查找步数 < 环境深度，绝不会
            // 从链尾哨兵（自环，下标 1）再步进——这里提前炸出误用；release
            // 零成本。残余缺口：arena 跨轮复用后恰好多一步（idx == 深度）
            // 会落在哨兵槽读到轮 1 的旧值，只此一档静默（结构上不可区分）。
            debug_assert!(
                node.1 != Some(list),
                "ListArena::nth 越界：闭项不应从链尾哨兵（自环）再步进"
            );
            list = unsafe { node.1.unwrap_unchecked() };
        }
        unsafe { &self.0.get_unchecked(list.get()).0 }
    }
}