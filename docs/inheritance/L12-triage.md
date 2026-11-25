# L12 ← L11 继承对账（2026-11-25）

> 口径见 [计划书](../l08-l13-inheritance-refactor-plan.md) §2；方法见 `tools/chain_merge.py`。
> 账本：`docs/inheritance/L11_macro-to-L12_canonical.tsv`。

## 0 结论

| 指标 | 重构前 | 重构后 |
|---|---:|---:|
| identical | 835 | **866** |
| missing | 9 | **9** |
| 非孪生 missing | 8 | **8**（全部是本章 Val 级重写的**替换**，见 §2） |
| line_keep | 0.9907 | **0.9908** |

三方合并让 `observe.rs`/`prof`/`run_surface_impl` 等继承面归位（identical +31）；
剩下 8 项 missing 全是 L12 **主动替换**掉的 Typ 桥接设施，按 D1 的 Replaced 登记，不是继承缺口。

## 1 做法

`base = 9cd94b06 的 L11`、`ours = 新 L11`、`theirs = 现 L12`：**32/35 文件零冲突**。

- 冲突 `elaboration.rs` ×1：`use` 取 ours（含 `surface`），但**去掉 `Typ`**（L12 已删除该桥接类型）；
- 冲突 `mod.rs` ×1：`run_surface_impl` 取 ours；
- `README.md` 取 theirs。
- 补做：平移 `observe.rs` 并**补 `Tm::Call` 臂**（L12 新增变体，`tm_has_unsolved_meta` 需覆盖）；
  注册 `mod observe;`；`L11_DEBUG_ON`/`L11_LOOP` → `L12_*`；crate 路径改 `L12_canonical`。

## 2 登记（允许的差异）

### D1-Replaced：本章 Val 级 trait 求解替换掉 Typ 桥接（8 项 missing）

| 项 | 原职责 | 替换为 |
|---|---|---|
| `typeclass::Typ` / `typeclass::Subst` / `typeclass::Val` | 桥接层类型别名 | 直接使用 `Tm`/`Val` 级表示 |
| `typeclass::to_typ` | `Raw`/`Tm` → `Typ` 转换 | `val_match` 单向匹配 + `v_to_val` |
| `typeclass::match_typ` | `Typ` 级模式匹配 | 同上 |
| `typeclass::apply_subst_to_typ` / `apply_subst_to_assertion` | `Typ` 级替换 | Val 级 σ 替换（继承自 L11 的 `Subst`/VSub） |
| `mod.rs:L11_DEBUG_ON` | — | `L12_DEBUG_ON`（章名重命名） |

### D2 本章新特性

- **Val 级 trait 求解**：`typeclass::consume`/`synth`/`try_resolve` 改写（-30/-27/-13 行）；
- **`Tm::Call` / `Val::Call` 内联节点**（值层透明外衣）+ `pretty` 还原调用形态；
- `observe.rs` 相应补 `Call` 臂（1 处，19 行）。

## 3 冻结（F）

孪生 `bump_spine_iter/typeclass.rs:val_to_typ` 1 项 missing（同步删除）。只登记。

## 4 门禁

| 套件 | 结果 |
|---|---|
| `cargo check --release --lib` | 0 error |
| `cargo test --release --lib L12_` | **88 passed**, 0 failed |
| `--test l12_blackbox` | **67 passed**, 1 ignored |
| `--test l12_lsp_surface` | **91 passed** |
