//! L01 — 归一化求值：同一份 NBE 算法在 12 种实现下的对比与基准。
//!
//! 这一层是 elaboration zoo 的第一课：用纯 lambda 演算（`Term`，de Bruijn 索引）
//! 演示正常化（eval + quote），并回答一个工程问题——**项和值的表示方式对求值
//! 性能有多大影响**。`L01a_fast` 时代的实验（字节码、arena 环境、扁平值…）按
//! 表示轴整理为 8 个变体，加 1 个求值策略变体（`cek`，CEK 机），再补 3 个
//! arena 演进（`ast_env_arena`、`bump_arena`），全部用同一个工作负载
//! （丘奇数加法）验证正确性并计时：
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
//! | `cek` | `Box<Term>` AST | `crate::list::List` | enum + `Box` | 新写：CEK 机 |
//! | `ast_env_arena` | `Box<Term>` AST | `ListArena` | enum + `Box` | 新写：naive 的 arena 演进 |
//! | `bump_arena` | bump 内引用式 AST | bump 持久链表 | 引用式 enum | 新写：bumpalo 全 arena |
//! | `bump_tree` | bump 引用式 AST（含结果） | bump 持久链表 | 引用式 enum | 新写：bump_arena + 结果 bump 化 |
//!
//! `cek` 不在表示轴上，而在**求值策略**上：其余变体都是递归 eval（调用栈即
//! 控制栈），`cek` 把控制栈显式搬进堆（continuation 栈），求值深度不再受进程
//! 栈限。`ast_env_arena` 与 `bump_arena` 是 Rc 家族的 arena 演进：前者把环境
//! 换成下标式 `ListArena`，后者连项带值全部 bump 分配、引用式结构（无计数、
//! 无析构）。
//!
//! 运行基准：独立的 `l01bench` 二进制（不依赖 typort/lib 其余各层，详见
//! [`bench`] 与模块内 `readme.md` 的实测结果）。正确性：每种表示都会先
//! 断言结果等于 `church(2n)`，再开始计时。

pub mod bench;
pub mod persistent_list;
pub mod term;

pub(crate) mod ast_env_arena;
pub(crate) mod bytes_env_arena;
pub(crate) mod bytes_env_arena_tm;
pub(crate) mod bytes_env_list;
pub(crate) mod bytes_flat_value;
pub(crate) mod bump_arena;
pub(crate) mod cek;
pub(crate) mod naive;
pub(crate) mod rc_term;
pub(crate) mod rc_value;
pub(crate) mod rpn_owned;

pub use term::{Term, TermRc};