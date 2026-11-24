# L08 ← L07 继承对账（2026-11-25）

> 口径见 [docs/l08-l13-inheritance-refactor-plan.md](../l08-l13-inheritance-refactor-plan.md) §2（D1–D5）。
> 账本：`docs/inheritance/L07_sum_type-to-L08_product_type.tsv`（复跑见 §6）。
> 分支：`rearch/inherit-l08-l13`；起点快照 `9cd94b06`。

## 0 结论

| 指标 | 重构前 | 重构后 |
|---|---:|---:|
| 条目总数 | 808 | 808 |
| identical | 672 | **713** |
| changed | 77 | 72 |
| missing | 59 | **23** |
| line_keep | 0.9138 | **0.9488** |
| **非孪生 missing** | **37** | **0** |
| **非孪生 changed** | 23 | **18**（全部为本章新特性或章名重命名） |

**参考版（产品路径）已达成 D1/D2**：L07 的每个条目在 L08 里要么逐字节同（510 项），
要么是已登记项（18 项 changed + 1 项章名重命名），**没有未登记缺失**。
剩余 23 missing / 54 changed 全部落在孪生 `bump_spine_iter`（已封印，见 §3）。

## 1 恢复（R）——本次实际补进来的继承面

| # | 项 | 数量 |
|---|---|---:|
| R1 | `observe.rs` 整文件（L07 11-21~23 的观察面：hover/inlay/自检行/失败 decl/形状认回/render_typ_pretty/drain_check_issues…） | 1 文件 17 项 |
| R2 | `mod.rs` 观察面入口：`run_with_surface_at` / `run_with_surface_query` / `run_surface_impl` / `check_with_surface`（继续型驱动） | 4 项 |
| R3 | `bench_check_nf_impl` / `bench_check_nf_observe`（基准口径 + 采集闸） | 2 项 |
| R4 | `pub mod prof`（FORCE/EVAL/QUOTE/VAPP/UNIFY/UNIFY_SP/MATCH_RUN/DECL_FORCE 计数器 + enable/reset/report） | 8 项 |
| R5 | `Infer` 观察字段：completion_table / inlay_hint_table / check_issue_lines / issue_drained / failed_decls / hover_query / inlay_query / ctor_pretty（+ hover_table 改用 `surface::HoverEntry`） | 8 字段 |
| R6 | `prof::bump` 调用点：force / v_app / eval / quote / unify / unify_sp | 6 处 |
| R7 | `elaboration.rs` 观察接线：洞 inlay、def 登记（源码注解渲染 + 形状认回 + 惰性 hover）、enum/构造子 decl_spans、投影补全候选、字面量 hover、构造子 hover | 9 处 |

做法：`elaboration.rs` 以 L07 版为基线，只把 L08 的**积类型字段投影**分支（`Val::Sum` 的
`.mk` 剥链）原样回贴；`observe.rs` 整文件平移（仅 `crate::L07_sum_type` → `crate::L08_product_type`）。

## 2 登记（D）——允许的差异

### D2 本章新特性（L08 积类型，18 项 changed 的主体）

| 文件 | 项 | 差异 |
|---|---|---|
| `parser/lex.rs` | `KEYWORD` | 新增 `struct` / `new` 关键字 |
| `parser/mod.rs` | `p_atom` | 原子后接**左结合多段投影链** `p.x.y`（L07 仅单段） |
| `parser/mod.rs` | `p_pattern` | struct 模式糖 `Wrap { p1, p2 }` → `Wrap.mk(p1, p2)` |
| `parser/mod.rs` | `p_decl` | `new Name(a, b)` 构造糖 |
| `elaboration.rs` | `infer_expr` | 接收者是 `Val::Sum`（无实例值）时按 `.mk` 构造子类型链剥字段类型 |
| `pretty.rs` | `go` | `Point.mk(...)` 不再叠 `::` |
| `unification.rs` | `(Obj, Obj)` 合同臂 | 字段名同 ⇒ 比接收者与 spine 实参（L07 潜伏缺臂） |

### D1 章名/路径重命名（机械差异，非行为）

- `L07_DEBUG_ON` → `L08_DEBUG_ON`（1 项 missing 即此）；`L07_LOOP` → `L08_LOOP`；
- `crate::L07_sum_type` → `crate::L08_product_type`（`observe.rs:span_from_name`、`unification.rs` 的 prof 路径各 1 行）。

### D3 文档措辞

- `mod.rs` 头注释、`Infer` 字段注释、`prof` 模块注释：按 L08 语境改写（非代码）。

## 3 冻结（F）——孪生 `bump_spine_iter`

`l08-twin` feature 默认关、`tests/l08_fast_parity.rs` 编成空、`src/lib.rs` 零引用 ⇒ **只登记、不回填**：

`seq_run` / `seq_step_t`（L08 起改递归 `_go` 族）、`rename_iter`、`unify_iter`、`subst_cxt`、
`mentions_level`、`val_mentions_lvl`、`vapp1`、`frcs`、`Machine` 等 —— 22 missing / 54 changed。
理由见 `docs/compare-l07-l12-shared/FINAL.md` §11（路径活性优先：冻结路径的差异只登记不修）。

## 4 门禁（本次实测）

| 套件 | 结果 |
|---|---|
| `cargo test --release --lib L08_` | **83 passed**, 0 failed |
| `--test l08_blackbox` | **57 passed**, 1 ignored |
| `--test l08_blackbox_v2` | **51 passed**, 2 ignored |
| `--test l08_lsp_surface` | **88 passed** |
| `cargo check --release --lib` | 0 error |

## 5 未做 / 下一步

- `l08_fast_parity` 未跑（孪生封印，编成空跑；保持封印口径）。
- `l08bench` 未跑性能对比（本次为继承面回填，路径未新增热开销；后续并入 P7 收口）。
- 下一步 P2：L09 ← L08（现状 3 missing / 86 changed，主体是宇宙检查改造 + `ty_precheck` 改名）。

## 6 复跑

```powershell
python tools/inherit_audit.py --prev src/L07_sum_type --next src/L08_product_type `
  --out docs/inheritance/L07_sum_type-to-L08_product_type.tsv
```
