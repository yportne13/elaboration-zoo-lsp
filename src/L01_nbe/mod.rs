//! L01 — 归一化求值（NBE）：同一算法在 21 种实现下的对比与基准。
//!
//! 用纯 lambda 演算（[`Term`]，de Bruijn 索引）演示正常化（eval + quote），
//! 并量化一个工程问题：**项和值的表示方式对求值性能有多大影响**。21 个
//! 变体沿五条轴展开，全部用同一个工作负载（丘奇数加法 `church_pair(n)`）
//! 先断言正确（结果 = `church(2n)`）再计时（`l01bench` 独立二进制）：
//!
//! * **项表示**：Box AST（`naive` 族）→ Rc 共享树（`rc_term`）→ 字节码
//!   （`bytes_*` / `rpn_owned`）→ bump 引用树（`bump_*`）→ 指令数组
//!   （`compiled`）→ 原生闭包树（`native_clo`）
//! * **值表示**：24B 枚举（`Bv`）→ 64 位打包字（`bump_spine` 的 `V`，
//!   tag 塞指针低位）
//! * **环境表示**：Rc 持久链表 → `ListArena` 下标链表 → bump 引用链表 →
//!   bump 数组切片（`env_slice`，nth O(1)）
//! * **求值策略**：递归（调用栈即控制栈）→ CEK 显式 kont 栈（`cek` /
//!   `cek_bump`）→ 双栈推土机（`bump_iter`）；中性项的表示从逐节点二叉
//!   单元 → 扁平 spine 栈 + 流式右链 quote（`bump_spine` 系）
//! * **输出编码**：结果树 `&Bt`（`bump_spine`/`bump_spine_iter`）→
//!   RPN 字节流（`bump_spine_rpn`，实测速度中性、体积 ~2.4× 小）
//! * **分配器**：系统堆 → mimalloc → 自研下标 arena → bumpalo
//!
//! 变体一览（**变体名即文件名**，见 `src/L01_nbe/`；公共设施 `term.rs` /
//! `persistent_list.rs` / `bench.rs` 不是变体）：
//!
//! | 变体 | 项表示 | 环境 | 求值策略 | 备注 |
//! |---|---|---|---|---|
//! | `naive` | `Box<Term>` | Rc 链表 | 递归 | 基线 |
//! | `rc_value` | `Box<Term>` | Rc 链表 | 递归 | 值带 Rc 骨架 |
//! | `rc_term` | `Rc<TermRc>` | Rc 链表 | 递归 | 项也共享 |
//! | `bytes_env_list` | 前缀字节码 | Rc 链表 | 递归 | 项扁平化 |
//! | `bytes_env_arena` | 前缀字节码 | `ListArena` | 递归 | 环境免分配 |
//! | `bytes_env_arena_tm` | 字节码 + 体共享 arena | `ListArena` | 递归 | 闭包体免拷贝 |
//! | `bytes_flat_value` | 前缀字节码 | `ListArena` | 递归 | 值也扁平（O(n²)，别用） |
//! | `rpn_owned` | 后缀字节码（自持） | Rc 链表 | 递归 | RPN 镜像 |
//! | `ast_env_arena` | `Box<Term>` | `ListArena` | 递归 | AST + 免分配环境 |
//! | `bump_arena` | bump 引用树 | bump 引用链表 | 递归 | 结果 Box 输出 |
//! | `bump_tree` | bump 引用树 | bump 引用链表 | 递归 | 结果也 bump，零 malloc |
//! | `env_slice` | bump 引用树 | bump 数组切片 | 递归 | nth O(1)，深索引友好 |
//! | `compiled` | 指令数组 `&[Ins]` | bump 引用链表 | 递归解释 | 项编译为指令 |
//! | `cek` | `Box<Term>` | Rc 链表 | CEK kont 栈 | 最简栈安全 |
//! | `cek_bump` | bump 引用树 | bump 引用链表 | CEK kont 栈 | 栈安全 + bump |
//! | `bump_iter` | bump 引用树 | bump 引用链表 | 双栈迭代 | 速度+深度（迭代基线） |
//! | `bump_spine` | bump 引用树 | bump 引用链表 + spine 栈 | 递归+流式 quote | 值打包、中性扁平化 |
//! | `bump_spine_iter` | bump 引用树 | bump 引用链表 + spine 栈 | 双栈+流式 quote | 速度+深度 |
//! | `bump_spine_slim` | bump 引用树 | bump 引用链表 + spine 栈 | 双栈+流式 quote | 条目 16B，连续性 quote 期推断 |
//! | `bump_spine_rpn` | bump 引用树 | bump 引用链表 + spine 栈 | 递归+流式写字节 | quote 直出 RPN（输出 ~2.4x 小） |
//! | `native_clo` | 原生闭包树（bump boxed） | bump 引用链表 + spine 栈 | 原生调用 + 流式 quote | β=间接调用，封轴实验 |
//!
//! 运行基准与选型结论见 [`bench`] 与模块内 `readme.md`。

pub mod bench;
pub mod persistent_list;
pub mod term;

pub(crate) mod ast_env_arena;
pub(crate) mod bytes_env_arena;
pub(crate) mod bytes_env_arena_tm;
pub(crate) mod bytes_env_list;
pub(crate) mod bytes_flat_value;
pub(crate) mod bump_arena;
pub(crate) mod bump_iter;
pub(crate) mod bump_spine;
pub(crate) mod bump_spine_iter;
pub(crate) mod bump_spine_rpn;
pub(crate) mod bump_spine_slim;
pub(crate) mod bump_tree;
pub(crate) mod cek;
pub(crate) mod cek_bump;
pub(crate) mod compiled;
pub(crate) mod env_slice;
pub(crate) mod naive;
pub(crate) mod native_clo;
pub(crate) mod rc_term;
pub(crate) mod rc_value;
pub(crate) mod rpn_owned;

pub use term::{Term, TermRc};