# L13 重定基方案评估（2026-11-17）

配套决策记录：`docs/l13-rebase-decision-2026-11-17.md`。本文给出若要把 L13
也纳入“以新 L12 为基线”的 copy-forward 重建时，可执行的分阶段方案、实测
规模、顺序、硬门禁与风险。**结论（供决策）**：L13 的核心机与产品面已深度耦合，
完整重定基是一次 ~2 万行非测试代码的改写项目；若目标只是“链一致性”，建议
维持产品层独立（决策记录选项 1）；若要做，按本文 P0–P5 分阶段、以现有 613 +
630 用例为硬门禁推进。

## 1. 现状盘点（HEAD 5b91c08e，L13 零修改）

- 总规模：`src/L13_namespace` 56.0k 行 / 59 个 `.rs`；其中层内测试约 15k
  行（25 个 `*_tests.rs`/legacy_tests 等）。
- 主要文件（行）：`mod.rs` 8282、`legacy_tests` 5336、孪生 `machine.rs` 4949、
  `parser/mod.rs` 4453、`elaboration.rs` 3779、孪生 `entry.rs` 1643、`cxt.rs` 1415、
  `parser/derive.rs` 1402、`unification.rs` 1224、`bump_spine_iter/unify.rs` 1279、
  `bump_spine_iter/observe.rs` 1262、`module_tests` 1038、孪生 `typeclass.rs` 923、
  孪生 `prim.rs` 909、`pretty.rs` 852、`compiler.rs` 792、`class_tests` 791 等。
- 产品/核心命中密度（grep 计数，ref 不含测试）：

| 关键词面 | total | ref | twin |
|---|---:|---:|---:|
| package/import | 297 | 138 | 159 |
| hdl/derive（wire/reg/always/module…） | 2567 | 633 | 153 |
| prelude | 745 | 353 | 168 |
| class | 228 | 118 | 41 |
| LSP/observe/gui | 570 | 201 | 259 |
| 原生 Nat（u64） | 174 | 98 | 62 |
| update_cxt/refresh | 56 | 23 | 33 |
| σ 路线（VSub/frcs/Subst/SpecSolve） | 1 | 0 | 1 |

结论：L13 的血统是 **update_cxt 精化 + 原生 Nat + package 限定名 + prim 挂
decl 表 + LSP/HDL/prelude 产品面**；与 L12（σ 精化、无原生 Nat、decl 名键）
是两条机制路线，不宜按“逐行 copy-forward”硬贴。

## 2. 与“新 L12”核心文件的实测差异（归一化后 numstat）

把 L13 文件名/模块名归一化为 L12 后与新 L12 同文件对比（`.rearch/l13-diff`
底稿；`add/del` 行数）：

| 文件 | add | del | 备注 |
|---|---:|---:|---|
| `mod.rs` | 2096 | 8085 | 值/项表示、prim、Nat、Call/OpCall、观察面 |
| `elaboration.rs` | 892 | 3651 | update_cxt 精化 + class/HDL 检查 |
| `unification.rs` | 1094 | 888 | 载体/名字/预算差异 |
| `cxt.rs` | 403 | 1334 | namespace/package 键/观察面 |
| `parser/mod.rs` | 572 | 3653 | package/import/HDL/derive/错误恢复/优先级 |
| `parser/derive.rs` | —（L12 无） | — | HDL derive 专属 |
| `bump_spine_iter/machine.rs` | 1803 | 4607 | 孪生核心 + trait/observe/nat |
| `bump_spine_iter/typeclass.rs` | 81 | 1006 | Val 级求解 + class 两阶段 |
| `bump_spine_iter/compiler.rs` | 584 | 821 | HDL/覆盖/预算 |
| `pattern_match.rs` / `pretty.rs` / `typeclass.rs` / `parser/lex.rs` | 合计 ~1.2k | ~2.5k | 显示/名字/词法扩展 |

量级：非测试核心差异约 **1.5–2 万行**（含孪生）；加上产品面移植与回归，
属于“周级”独立项目，而不是一次小重构。

## 3. 分阶段方案（若执行）

**P0 冻结与门禁（1 轮内）**

- 从 `master` 拉 `rebase/l13-on-l12` 分支；保留 `pre-rearch-20261117` 备份；
- 记录 L13 现状门禁：`cargo test --release --lib L13_namespace::`（615+6 ignored）、
  `cargo test --release --test l13_fast_parity`（630+6 ignored）、HDL/prelude 语料
  （`tools/bench_corpus` + `l13bench --file`）基线输出；
- 产出“L13 行为快照”（全量 golden/输出 diff 作为后续每阶段回归 oracle）：
  已落地 `tools/l13_rebase_baseline.ps1` + `tools/l13_baseline_2026-11-17.tsv`
  （32 个 examples；脚本增量、单次默认最多 8 个、可断点续跑，首批 11 个已采；
  门禁基线表见 `docs/l13-baseline-2026-11-17.md`），后续每阶段用同脚本增量重生成并 diff。

**P1 核心机对齐（不含载体与产品面；风险最高的一步，建议先做可行性 spike）**

- 以新 L12 的 `mod.rs`/`cxt.rs`/`elaboration.rs`/`unification.rs`/`pattern_match.rs`/
  `pretty.rs`/`typeclass.rs`/`parser` 为基线，**保留 L13 专有面**：
  `update_cxt` 精化载体（不迁移 σ；审计已记录 σ 五轮移植失败）、原生 `u64` Nat、
  `Val::Call/OpCall`、package 限定 decl 键、prim 挂 decl 表、终止/预算；
- 先做“双载体桥” spike：在新 L12 核心上保留 `check_pm_final` 返回精化 Cxt 的旧
  接口，验证 GADT/依赖匹配语料（`l13_fast_parity` 子集 + HDL 断言）不回归；
- 门禁：L13 lib 615 + l13_fast_parity 630 全绿，且与新 L12 共享的跨层语料
  （audit probe / gadt / prim_identity）不变。

**P2 prelude/宏/class/termination 合并**

- 把新 L11 宏机制（MacroState/展开/深度护栏）与 L13 的 prelude 宏库对齐：
  保留 L13 的 `derive` 与 prelude 语义，宏基础设施改为新链实现；
- class 两阶段/注入与 trait 求解：保留 L13 产品语义，消除与新 L12 `typeclass`
  重复实现（可共享同一 `Synth` 算法，断言用 Val 级）；
- 门禁：prelude_stdlib/data/hdl 测试 + class_tests。

**P3 HDL/derive/verilog-compat 移植**

- `parser/derive.rs`、HDL 宏/端口/模块图检查、`observe` 观察面按 L13 语义
  移植到 P1 后的 parser/elaboration 基线；
- 门禁：`hdl_*` 全部测试 + `verilog_compat_tests` + `l13bench --file` HDL 示例。

**P4 LSP/namespace 产品面**

- hover/completion/goto/quickfix/semantic 观察面、package/import/全限定名、
  prelude 加载、LSP 端到端语料；
- 门禁：LSP 测试套件（`l13_*` 之外的产品层测试）+ 手工/脚本 LSP 冒烟。

**P5 文档与链定位收口**

- 更新 L13 README：声明本章已与新 L12 同构（或列出仅剩的产品层差异）；
- 更新审计报告附录；跨层门禁加“L13 接受 L12 语料”回归；
- 全链 final gates + 推送。

> P1 的桥接口与工作包拆分见 `docs/l13-p1-double-carrier-design-2026-11-17.md`。

## 4. 风险与硬约束

- **载体不可强迁**：σ 路线与 `update_cxt` 是两条机制路线；审计记录 L13 的 σ
  移植五轮失败（prelude 21s、深 meta 解链栈溢出、GADT 覆盖误报）。P1 必须
  保留 `update_cxt`，只对齐“其余实现思路”，否则 613 测试无法收敛。
- **parser 不可整替**：L13 的 package/import/HDL/derive 与错误恢复是产品面，
  新 L12 的 parser 契约（严格 Err）不兼容；P3 需在保留 L13 语法面的前提下
  合并基础设施，而不是直接复制新 L12 parser。
- **产品行为是 oracle**：所有阶段以现有 615/630 用例与 HDL/prelude/LSP 语料为
  硬门禁；任何“与 L12 对齐”但产品回归的改动一律回退。
- **不可并行写同一文件**（若用 Agent Teams）：P1/P2 的文件重叠面大，建议串行。

## 5. 复现（规模数据）

```powershell
# L13 文件规模
git ls-files -- 'src/L13_namespace' | Where-Object { $_ -like '*.rs' } | ForEach-Object { (Get-Content -LiteralPath $_).Count.ToString() + ' ' + $_ } | Sort-Object { [int]($_ -split ' ')[0] } -Descending
# 归一化核心差异（底稿见 .rearch/l13-diff）
# 见本轮分析脚本：L13 文件名/模块名归一化为 L12 后 git diff --no-index --numstat
```
