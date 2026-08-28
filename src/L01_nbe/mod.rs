//! L01 — 归一化求值：同一份 NBE 算法在 8 种表示下的实现与基准。
//!
//! 这一层是 elaboration zoo 的第一课：用纯 lambda 演算（`Term`，de Bruijn 索引）
//! 演示正常化（eval + quote），并回答一个工程问题——**项和值的表示方式对求值
//! 性能有多大影响**。`L01a_fast` 时代的实验（字节码、arena 环境、扁平值…）按
//! 表示轴整理为 8 个变体，全部用同一个工作负载（丘奇数加法）验证正确性并计时：
//!
//! | 变体 | 项表示 | 环境 | 值表示 | 旧文件名 |
//! |---|---|---|---|---|
//! | `naive` | `Box<Term>` | `crate::list::List` | enum + `Box` | nbe_closure.rs |
//! | `rc_value` | `Box<Term>` | `crate::list::List` | enum + `Rc` | nbe_closure_rc.rs |
//! | `rc_term` | `Rc<TermRc>` | `crate::list::List` | enum + `Rc` | nbe_closure_rc2.rs |
//! | `bytes_env_list` | 字节码（前缀） | `crate::list::List` | enum + `Rc` | nbe_closure1.rs |
//! | `bytes_env_arena` | 字节码（前缀） | `ListArena` | enum + `Rc` | nbe_closure2.rs |
//! | `bytes_env_arena_tm` | 字节码 + 项体共享 arena | `ListArena` | enum + `Rc` | nbe_closure22.rs |
//! | `bytes_flat_value` | 字节码（前缀） | `ListArena` | 扁平字节 `Vec<u8>` | nbe_closure3.rs |
//! | `rpn_owned` | 字节码（后缀/RPN，自持） | `crate::list::List` | enum + `Rc` | nbe_closure4.rs |
//!
//! 运行基准：`typort bench`（详见 [`bench`] 与模块内 `readme.md` 的实测结果）。
//! 正确性：每种表示都会先断言结果等于 `church(2n)`，再开始计时。

pub mod bench;
pub mod persistent_list;
pub mod term;

pub(crate) mod bytes_env_arena;
pub(crate) mod bytes_env_arena_tm;
pub(crate) mod bytes_env_list;
pub(crate) mod bytes_flat_value;
pub(crate) mod naive;
pub(crate) mod rc_term;
pub(crate) mod rc_value;
pub(crate) mod rpn_owned;

pub use term::{Term, TermRc};