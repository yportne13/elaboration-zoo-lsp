# L12 孪生加固回灌 · 已撤销记录

> **状态：已撤销（2026-11-24 晚）。** 本轮曾把 L07 孪生的 5 项加固回灌进
> `src/L12_canonical/bump_spine_iter/`，随后**全部回退**，代码树已恢复到封印状态。
> 补丁原文留档：[backport-l12-twin.patch](backport-l12-twin.patch)（48 KB，`git apply` 可复原）。

## 为什么撤销

L12 孪生**已被主动封印**，不属于维护范围：

| 事实 | 证据 |
|---|---|
| 封印于 2026-11-22/23，"不再参与门禁/parity" | `7a68abc7 chore(L07): 封印孪生（bump_spine_iter）—— 不再参与门禁/parity`、`2acc5231 perf(L09-L12): let 洞快路径 + 孪生封印` |
| `l12-twin` 是 **off-by-default** feature | `Cargo.toml` `l12-twin = []`（无 `default` 收录） |
| parity 套件默认编成空 | `tests/l12_fast_parity.rs:1` `#![cfg(feature = "l12-twin")]` |
| **不是产品路径** | `src/lib.rs` 对 `L12_canonical::bump_spine_iter` **零引用**；LSP 默认引擎是 L13 孪生（`src/lib.rs:361`） |
| 仅存的使用方是基准工具 | `src/bin/{l12bench,realbench,l06l13mem}.rs` 用 `run_fast`/`parse`/`Tycker` |

⇒ 它是一条**冻结的基准引擎**，不是待修的生产代码。往里面回灌加固没有产品收益，
而且会制造"这个分支还在维护"的错误预期。

## 分类更正（本次方法论失误）

[FINAL.md](FINAL.md) §4 曾把孪生侧 5 项记为 **E3（缺失或落后）**，§9 建议 1 还把它列为
"推荐、成本最低"的待办。**这个分类是错的。**

对一个已被封印的代码路径，"L07 有、L12 没有"的正确归类是 **E3-冻结（不追）**，
而不是待修缺口。分析流水线按"保留率"排序找差异，缺少一道前置过滤：
**这条代码路径还有人在维护吗？** 本次漏了这道过滤，导致把历史快照差异当成了待办事项。

正确的分类口径（今后一并适用）：

| 分类 | 含义 | 处置 |
|---|---|---|
| **E3-活跃** | 该路径仍在门禁/产品/默认测试里 | 记缺口，排期 |
| **E3-冻结** | 该路径已被封印、仅剩基准用途 | **只记录、不过问**；不排期、不回灌 |

本轮 5 项（`struct_eq` 工作栈、`InlineStack` 深值迭代、`pending` cons 链、
`SIMPL_CACHE`、`vapp1` β 守卫）**全部属于 E3-冻结**。

## 撤销是否留下残留

- `src/L12_canonical/` 工作区 **clean**（`git diff --numstat -- src/L12_canonical/` 为空）。
- 新增的 `deep_value_tests` 回归钉一并撤销（它同样只钉孪生）。
- 未提交任何 commit，封印状态与撤销前逐字节一致。

## 补丁里有什么（若将来真要复活孪生）

`backport-l12-twin.patch`（+610 / −331，4 文件）内容：

1. `force.rs`：`vapp1` 的 VSub→闭包 β 守卫（L07 `force.rs:79-113`）；`val_mentions_lvl` 迭代化。
2. `subst.rs`：补 `InlineStack<T,const N>`；`mentions_level` 迭代化。
3. `struct_eq.rs`：递归 `*_go` 族 → `SEqTask`+`seq_run` 显式任务机（保留 L12 的 `Tm::U(x)` /
   `v_u_of` 层级载荷与切片版 `pending`）。
4. `entry.rs`：补回 `deep_value_tests`（10 万层）。

当时验证：`cargo test --lib --features l12-twin` 1281 passed；`--test l12_fast_parity` 137 passed。
**但这是给冻结分支的验证，不构成任何产品保证。**

## 如果要更彻底

现行"封印"只是**不进门禁**，模块仍然参与编译、仍被 3 个 `src/bin/*` 依赖，所以
以后还会有人（包括我）走进去。两个更硬的选项：

- **A. 硬封印**：把 `mod bump_spine_iter;` 挂到 `#[cfg(feature = "l12-twin")]` 下，
  三个 bench bin 同步加 `required-features`。好处：默认构建不再编译这 1.5k+ 行；
  代价：`realbench` 的 L12 层默认不可用。
- **B. 删除**：连同 `tests/l12_fast_parity.rs` 与 bench 入口一起删。最干净，
  但丢掉 L12 的历史对照基准。

不选 A/B 也完全可以——那就把本文件的分类更正当作全部处置。
