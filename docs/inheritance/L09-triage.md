# L09 ← L08 继承对账（2026-11-25）

> 口径见 [计划书](../l08-l13-inheritance-refactor-plan.md) §2（D1–D5）。
> 账本：`docs/inheritance/L08_product_type-to-L09_mltt.tsv`。

## 0 结论

| 指标 | 重构前 | 重构后 |
|---|---:|---:|
| identical | 686 | **721** |
| **非孪生 missing** | 3 | **2** |
| 非孪生 changed | 86 | **63** |
| line_keep | 0.9851 | **0.9881** |

**关键收获不是数字，是"血缘"**：重构前的 L09 是从**旧的 L08**（未继承 L07 观察面）长出来的，
所以它身上缺 `observe.rs`、`prof`、`check_with_surface` 等 38 项。
本次改成**以"新 L08"（`cbfe2dbb`）为基线**重新叠加 L09 增量，那 38 项缺失一次性消失。

## 1 做法：三方合并（base = 旧 L08，ours = 新 L08，theirs = 现 L09）

`git merge-file` 逐文件三方合并，**29/32 文件零冲突**；3 个冲突文件按语义手工定夺：

| 文件 | 冲突数 | 取舍 |
|---|---:|---|
| `elaboration.rs` | 7 | 观察面接线取 ours（新 L08 的 observe 方法版）；`check_universe` 等宇宙增量取 theirs；`use` 两边都要（`surface` + `unification::PartialRenaming`） |
| `mod.rs` | 6 | 全部取 ours（新 L08 的 Infer 字段/入口/surface API），`L08_DEBUG_ON`→`L09_DEBUG_ON` 重命名 |
| `README.md` | 1 | 取 theirs（L09 自己的文档） |

补做：新增 `observe.rs`（L08 平移到 L09，`Tm::U` → `Tm::U(_)`）；`unification.rs` 的
4 处 `crate::L08_product_type::prof` → `crate::L09_mltt::prof`。

## 2 登记（允许的差异）

### D2 本章新特性：`Type N` 分层宇宙（63 项 changed 的主体）

| 差异 | 覆盖条目 |
|---|---|
| `Tm::U` → `Tm::U(u32)` / `Val::U` → `Val::U(u32)`（机械替换） | `mod.rs` 约 40 项（eval/quote/force/tm_size_ref/shift_tm/mentions_level…每项 1–2 行） |
| `ty_precheck` → `check_universe`（推断注解项、解 meta 为 `U(0)`、非空 spine 走 rename 造 λ 解） | `elaboration.rs:check_universe`（新增）、`check_ty`、`check` |
| enum 的 `universe_lvl` 扫描 + `Raw::U(lvl)` 上界 | `elaboration.rs:infer_owned` |
| 内建函数返回类型 `Val::U(0)` | `mod.rs:prim_reduce`、`cxt.rs:new` |
| DEMO 源改用 `Type 0/Type 1` | `mod.rs:DEMO_SRC` |
| 测试断言 `U` → `U(0)` | `tests.rs` 约 15 项（每项 1–4 行） |
| 渲染适配 | `pretty.rs`、`raw_pretty.rs`、`shape.rs`、`struct_eq.rs`、`surface.rs`、`unification.rs`（各 1–2 行） |

### D1 章名重命名 / 已替换

- `L08_DEBUG_ON` → `L09_DEBUG_ON`（1 项 missing 即此）；`L08_LOOP` → `L09_LOOP`。
- `elaboration.rs:ty_precheck` 标记为 **Replaced**（L09 的 `check_universe` 是它的超集：
  不只是结构预检，还会解 meta 并返回层级）。

### D1-同型：观察面文件平移

`observe.rs` 逐行同 L08（仅 crate 路径 + `Tm::U(_)`）。`mod.rs` 的 `prof` / `check_with_surface` /
`run_with_surface_*` / `bench_check_nf_*` 全部与新 L08 一致。

## 3 冻结（F）

孪生 `bump_spine_iter`：1 missing（`ty_precheck` 被宇宙检查吸收）、23 changed（`check_ty`/`infer_expr`/`prim_reduce` 的 `Val::U(u32)` 机械替换）。**只登记**。

## 4 门禁

| 套件 | 结果 |
|---|---|
| `cargo check --release --lib` | 0 error |
| `cargo test --release --lib L09_` | **83 passed**, 0 failed |
| `--test l09_blackbox` | **60 passed**, 1 ignored |
| `--test l09_lsp_surface` | **86 passed** |

## 5 复跑

```powershell
python tools/inherit_audit.py --prev src/L08_product_type --next src/L09_mltt `
  --out docs/inheritance/L08_product_type-to-L09_mltt.tsv
```
