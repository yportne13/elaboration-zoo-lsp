# L11 ← L10 继承对账（2026-11-25）

> 口径见 [计划书](../l08-l13-inheritance-refactor-plan.md) §2；方法见 `tools/chain_merge.py`。
> 账本：`docs/inheritance/L10_typeclass-to-L11_macro.tsv`。

## 0 结论

| 指标 | 重构前 | 重构后 |
|---|---:|---:|
| identical | 808 | **839** |
| missing | 1 | **1**（`L10_DEBUG_ON` 章名重命名） |
| non-identical（孪生除外） | 11 | **15** |
| line_keep | 0.9992 | **0.9990** |

重构前缺的 1 项 missing 掩盖了真实的继承缺口：`observe.rs` 在 L10 已补齐后，L11 仍然没有。
三方合并后 **missing 达标（仅章名重命名）**，observe/prof 全部归位。

## 1 做法

`base = 9cd94b06 的 L10`、`ours = 新 L10`、`theirs = 现 L11`：**32/34 文件零冲突**。

- 冲突 `mod.rs` ×2：`prof` 模块取 ours（L11 缺）、`run_surface_impl` 取 ours（L11 是旧单通道版）；
- `README.md` 取 theirs。
- 补做：平移 `observe.rs`；注册 `mod observe;`；**恢复被合并丢掉的 `use cxt::{Cxt, DeclEntry, Decls};`**
  （L11 的旧 mod.rs 没有这行，合并让它凭空消失导致 8 处 `Cxt` 解析失败）；
  `L10_DEBUG_ON`/`L10_LOOP` → `L11_*`；`crate::L10_typeclass` → `crate::L11_macro`。

## 2 登记（允许的差异）

### D2 本章新特性：macro_rules

| 项 | 说明 |
|---|---|
| `parser/macros.rs`（新文件，345 行） | 宏文法（token/元变量/重复）、解析期展开 |
| `parser/mod.rs:parser_with_span`（+8 行） | 展开后进入常规解析 |
| `parser/lex.rs`（+29 行） | `macro_rules!` 相关 token |
| `tests.rs`（+23 行） | 宏用例 |

### D1 章名重命名

`L10_DEBUG_ON` → `L11_DEBUG_ON`（唯一 missing）；`L10_LOOP` → `L11_LOOP`；
`DEMO_SRC` 补宏演示段（1 行）；`observe.rs:span_from_name` 的 crate 路径（1 行）。

## 3 冻结（F）

孪生 `bump_spine_iter`：1 changed。只登记。

## 4 门禁

| 套件 | 结果 |
|---|---|
| `cargo check --release --lib` | 0 error |
| `cargo test --release --lib L11_` | **88 passed**, 0 failed |
| `--test l11_blackbox` | **67 passed**, 1 ignored |
| `--test l11_lsp_surface` | **91 passed** |
