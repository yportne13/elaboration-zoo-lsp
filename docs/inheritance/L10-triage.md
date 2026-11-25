# L10 ← L09 继承对账（2026-11-25）

> 口径见 [计划书](../l08-l13-inheritance-refactor-plan.md) §2（D1–D5）。
> 账本：`docs/inheritance/L09_mltt-to-L10_typeclass.tsv`。
> 方法：`tools/chain_merge.py`（提取旧提交的上一章树作 base，对"新上一章 vs 本章"做三方合并）。

## 0 结论

| 指标 | 重构前 | 重构后 |
|---|---:|---:|
| identical | 762 | **794** |
| **非孪生 missing** | 1 | **1**（章名重命名） |
| 非孪生 changed | 13 | **13** |
| missing 总数 | 37 | **1** |
| line_keep | 0.9985 | **0.9984** |

重构前 L10 有 37 项 missing —— 全部是 `observe.rs` / `prof` / `check_with_surface` 这批
**L09 已经从 L08 继承、L10 却没跟上的观察面**。三方合并后一次性归零（只剩 `L09_DEBUG_ON` 改名）。

## 1 做法

`base = 9cd94b06 的 L09`（旧链快照）、`ours = 新 L09`（重构后）、`theirs = 现 L10`：

- **29/32 文件零冲突**（含 `unification.rs`、`typeclass.rs`、`cxt.rs`、`parser/*`）；
- 3 个冲突文件：
  - `elaboration.rs` 冲突 1：`use` 两侧都要（`surface` + `typeclass::{Assertion, Instance, Typ}`）；
    冲突 2：投影臂取 ours（新 L09 的观察接线），并补回 L10 需要的 `ty_orig` 绑定；
  - `mod.rs` 冲突 1：`Infer` 字段两侧都要（L10 的 4 个 trait 字段 + 新 L09 的观察字段）；
    冲突 2：`run_surface_impl` 取 ours（`println_span` + `drain_check_issues` 管线）；
  - `README.md`：取 theirs（L10 自己的文档）。
- 平移到 L10：`observe.rs`（改 crate 路径与文件头）；`mod.rs` 注册 `mod observe;`；
  `L09_DEBUG_ON`/`L09_LOOP` → `L10_*`；`crate::L09_mltt` → `crate::L10_typeclass`（`unification.rs` 2 处）。

## 2 登记（允许的差异）

### D2 本章新特性：trait / typeclass 求解

| 项 | 说明 |
|---|---|
| `typeclass.rs` + `bump_spine_iter/typeclass.rs`（新文件） | trait 声明/实例脱糖、Prolog 式 `Synth` 求解 |
| `mod.rs:Infer` 4 个字段 | `trait_solver` / `trait_definition` / `trait_out_param` / `trait_error` |
| `elaboration.rs:infer_expr` | 接收者方法 `trait_wrap`、`ty_orig` 快照 |
| `unification.rs:unify` | trait 约束合一臂 |
| `parser/mod.rs`（+114 行） | `trait`/`impl`/`for`/`this` 文法 |
| `tests.rs`（+105 行） | trait 用例 |

### D1 章名重命名

`L09_DEBUG_ON` → `L10_DEBUG_ON`（唯一 1 项 missing）；`L09_LOOP` → `L10_LOOP`。

## 3 冻结（F）

孪生 `bump_spine_iter`：4 项 changed（`infer_expr` / `unify_catch` / `prim_reduce` 的 trait 适配）。只登记。

## 4 门禁

| 套件 | 结果 |
|---|---|
| `cargo check --release --lib` | 0 error |
| `cargo test --release --lib L10_` | **86 passed**, 0 failed |
| `--test l10_blackbox` | **65 passed**, 1 ignored |
| `--test l10_lsp_surface` | **89 passed** |
