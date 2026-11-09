# P0 + P1 实现报告（optimal-design 迁移第一批）

> 分支：`p0-p1-baseline-cleanup`（从 master `8443586e` 起）
> 落地日期：2026-11-09
> 目标：按 `FINAL-OPTIMAL-DESIGN.md` §7 落地 **P0（基线/判据/CI）** 与 **P1（零风险清理/度量）**；
> P2+ 未开始。本报告是实现记录与验收证据，方法论见 `FRAMEWORK.md` / `D7-architecture.md`。

## 0. 提交一览（5 commits，均可单独 revert）

| commit | 内容 |
|---|---|
| `163eb5f2` | **P1 清理**：删除 `src/bench_head`（陈旧冻结快照，非 HEAD 副本）、`src/bench_pre` → `tools/bench_snapshots/L07_pre/`、17 个 `.bak` 删除；`docs/review-*` 7 目录 → `docs/archive/`（105 rename + 103 处引用 + 归档 README） |
| `faa08aa8` | P1 收尾：3 个 bin 的 `#[path]`、Cargo.toml 注释、L07_pre README、`.commandcode/` 入 `.gitignore` |
| `0180cdd7` | **P0 发现并修复**：trait 重声明后 `head_index` 残留旧下标 → 两引擎 OOB panic；改为"索引越界 → 回退全量扫"，加 2 条回归钉 |
| `f8aaf596` | **P0 工具**：`tests/engine_parity_report.rs`（34 文件双引擎对拍报告）、`tools/metrics.py --check` + 基线、`tools/gate_p0.sh` / `gate_lean_oracle.sh` / `run_engine_parity.sh`、CI 两个 optional step、P0/P1 分报告 |
| `16197655` | 分析/实验报告入库：`FINAL-OPTIMAL-DESIGN.md`、D1–D7、D2b、82 个 raw 实验输出、上一轮 L07–L13 对比报告；以及此前未跟踪的 L13 σ 补丁证据（`docs/wip/`）与 l13-perf-replace 文档 |

整体 diff：273 文件、+39,046 / −13,781 行（其中 −13.7k 主要是删除/迁移的归档代码；+39k 主要是
新入库的分析报告与实验 raw）。

## 1. P1：零风险清理（已完成）

### 1.1 决策偏差（与计划的差异，已实证）

| 计划原文 | 实际执行 | 原因/证据 |
|---|---|---|
| 删 `bench_head` + `bench_pre` | **删 bench_head；bench_pre 移到 `tools/bench_snapshots/L07_pre/`** | bench_pre 是 `l07pre` A/B 与 `pmabbench` 的唯一可复现快照，删除会破坏实验复现；移动后 `src/` 不再包含归档（D3 目标达成），工具继续可用 |
| `bench_head` = HEAD 快照 | 实测**不是**：与 ea01207 及 86 个 L07 历史提交 blob 均不匹配，与当前 L07 差 27 文件/+13,912/−8,293 | l12/l10 独立验证（`P1-structure-verify.md`、`P1-cleanup-report.md`）；因此删除合理 |
| l07alloc 的 `head` 列保留历史对照 | 改为 `L07_head = 当前 L07_sum_type` 别名，文档标注 **head≡cur** | `#[path]` 二次包含 L07 源码会因 `crate::L07_sum_type` 硬编码 + `pub(super)` 产生 35 个编译错误；P2 决策：删 head 列或按目标 commit 重冻快照 |
| 19 bench bin → 1 个参数化 bin、统一 Error 载体 | **延后 P2** | 属行为/API 重构，不是零风险清理；本轮只删除/移动/归档 |

### 1.2 度量结果（`tools/metrics.py`，基线 `docs/metrics/baseline-2026-11-09.*`）

- `src/` 非空行：`8443586e` **230,242** → 本分支 **204,908（−25,334，−11.0%）**；层内（L01–L13）
  **185,432 不变**（84,946 ref 生产 + 85,411 twin + 17,075 test）⇒ 清掉的全是归档/重复，未动语言代码。
- `bench_head` 12,606 行删除；`bench_pre` 12,728 行移出 `src/`；`.bak` 17 文件 / 12,464 行删除；
  归档目录 `archive_nonempty = 0`、`bak_files = 0`。
- 安全/风险指标不变：unsafe **317**、`panic!` 487、`unwrap` 732、`expect` 739、print 663；
  跨层 Jaccard ≥90% 的副本对数 24（≥95%：10）——P2 的清理目标，本轮不动。
- `python tools/metrics.py --check`：**11/11 PASS**（advisory 模式；`--strict` 可转硬门禁）。

### 1.3 归档与链接

`docs/review-*` 7 目录（105 文件）→ `docs/archive/review-*`，git 识别为 rename（历史保留）；
47 个 `.md` / 103 处引用改指新路径，全仓 `*.md` 旧路径 0 命中（`P1-docs-archive-report.md`）。
新增 `docs/archive/README.md` 说明"归档只读、新评审进 docs/optimal-design/ 或活跃目录"。

## 2. P0：基线与判据（已完成）

### 2.1 对拍报告（34 文件 × 双引擎）

`tests/engine_parity_report.rs`（`#[ignore]`，CI/job 显式跑）+ `P0-parity-report.md`：

| 指标 | 结果 |
|---|---|
| 语料 | **34**（examples 32 = 根 5 + hdl 27；tests/*.typort 2）+ prelude 35 |
| 引擎归属 | twin-owned **32/34**；fallback 2（`18-utils`: `untrusted-error`；`trait_system_tests` 修复后为 `untrusted-error (redefine outParam)`） |
| 判定 parity | **34/34** 相等 |
| 诊断逐字节 parity | **33/34**；唯一差异 `examples/typeclass_complex.typort`（twin span 全零，文本相同——已知偏差，D6/l13-perf-replace 已登记） |
| panic | 修复前 2 → **修复后 0** |
| 耗时 | 单文件 elaboration 合计 ref **42.9s** vs twin **16.0s（2.67×）**；全量 wall ≈74s |
| prelude 首载 | ref-hdl **8.47s** vs twin-hdl **4.34s（~2.0×）**；core 模式 0.13/0.11s |
| 已知结论复现 | examples 31/32 owned、18-utils 唯一回落（29/30 口径一致）；`tests/` 侧发现新崩溃点 |

### 2.2 P0 发现：#1 用户可见 panic（已修，有回归钉）

**问题**：`typort check tests/trait_system_tests.typort` 在参考版与孪生上均 panic（index OOB），
LSP 两引擎同点位；最小 9 行复现 = 重声明 prelude trait `Add` 并实例化/使用 `+`。

**根因**：`Synth::new_trait` 重声明时 `class_instances.insert(name, vec![])` 重置实例表，但
`head_index[(trait, head)]` 旧下标桶未清理；`solve_multi_trait_ref` 信任索引 → `instances[i]` 越界
（ref `unification.rs:754`；twin `typeclass.rs:294`）。

**修复**（两引擎同口径，`0180cdd7`）：索引桶中任一 `i >= instances.len()` ⇒ 回退全量扫
`instances.iter().filter_map(filter)`（与无索引路径候选集完全一致；正常路径保留 O(1) 过滤）。
**回归**：`tests/p0_known_bug_pins.rs`（最小复现 + 原 fixture × 2 引擎，2 passed）；
`typort check` 该 fixture exit 0 并输出 `ALL_TRAIT_TESTS_PASSED`；全量 parity panic 0；
`l13_fast_parity` 629/0/6 不变。
**P2 根治项**：`new_trait` 与 undo journal 对齐地 purge 同名 head_index（或拒绝重声明 prelude trait
并给诊断），并覆盖 remove_file/import 重置路径。

### 2.3 工具与 CI

- `tools/metrics.py`：11 项可复现度量 + JSON/MD 基线 + `--check/--strict/--git-ref/--compare-ref`。
- `tools/run_engine_parity.sh`：全量/`GATE_P0_MAX_FILES` smoke 两级；报告 JSON+MD 落 `$CARGO_TARGET_DIR`。
- `tools/gate_p0.sh`：metrics → parity → Lean oracle 三步，SKIP 不算失败，`--dry-run`。
- `tools/gate_lean_oracle.sh`：探测 Lean 工具链（有则 build+oracle 差分；无则明确 SKIP；
  `GATE_LEAN_ORACLE_REQUIRED=1` 转必需）。
- `.github/workflows/ci.yml`：`test` job 末尾两个 optional step（P0 gate + Lean oracle），
  仅为新增行（+15 行），其他 job 未动；YAML 已用 Python safe_load 校验。

## 3. 验收门禁（本分支实跑，2026-11-09）

| 门禁 | 结果 |
|---|---|
| `cargo check --all-targets` | **0 error**（EXIT=0） |
| `cargo test --release --lib` | **994 passed / 0 failed / 6 ignored**（73.6s） |
| `l13_fast_parity`（P0 report + gate） | **629 passed / 0 failed / 6 ignored** |
| `twin_engine_tests` | **28 passed / 0 failed**（89.5s） |
| `hdl042_engine_tests` | **2 passed / 0 failed**（13.8s） |
| `p0_known_bug_pins` | **2 passed / 0 failed**（0.3s） |
| `engine_parity_report`（全量 34 文件） | **1 passed**（报告型）；panic 0 |
| `bash tools/gate_l13.sh --release` | **PASS**（lib 614/6 ignored、parity 15、twin_lsp 28、hdl042 2；169s） |
| `bash tools/gate_p0.sh` | **PASS**（metrics 11/11、parity 65s、Lean oracle 2 passed；86s） |
| `python tools/metrics.py --check` | **PASS 11/11**（advisory） |

> Windows 本地注意：默认 `bash` 是 WSL，其中无 cargo；用 **MSYS2 bash**
> （`C:\msys64\usr\bin\bash.exe`，PATH 加 `/c/Users/<user>/.cargo/bin`）运行 gate 脚本可复现上表。
> CI（Ubuntu）不受影响。P0-ci 报告已记录此差异。

## 4. 风险、未完成与 P2 交接

**已接受的偏差/风险**
1. `l07alloc`/`l07whoalloc` 的 `head` 列自 P1 起 ≡ `cur`（bench_head 是陈旧快照且与历史 commit 不匹配）；
   已写入源码注释与 P1 报告。P2 决策：删 head 列，或按目标 commit 重新 `git archive` 冻结快照。
2. `bench_pre` 仍在仓库（`tools/bench_snapshots/`，12.7k 行），未"删除净收益"；这是为实验可复现性
   主动保留，P2 可改成按需生成（脚本从 commit 抽取）并从树中删除。
3. 19-bin 合并、Error 载体统一、`src/bench_*` 之外的归档（`src/bench_head` 已删）未做——均属 P2。
4. P0 报告未采集 RSS 峰；cross-file（import/package rebuild_set）语义未覆盖；无 per-file 硬超时。
5. `docs/wip/` 的 L13 σ 补丁与 l13-perf-replace 文档已入库防丢失，但补丁本身仍是未应用状态。

**P2（下一步）候选**
- `refcore`/workspace 抽取（行为不变）与 oracle feature 化；
- `head_index` purge 根治 + 覆盖 remove_file/import 重置路径（P0 报告 §5.4）；
- 19 bench bin → 1 个 `--layer` 参数化（消 118 个 `#[path]` 重编译）；
- Error 载体统一（为 P/R parity 的 Err 正文逐字节铺路）；
- 按 `GATE_P0_MAX_FILES` 把 CI parity 控制在 smoke 规模，全量留在本地/夜间 job。

## 5. 复现命令

```bash
# 全量门禁（CI 口径；Windows 用 MSYS2 bash）
CARGO_TARGET_DIR=C:/ezl-target bash tools/gate_l13.sh --release
CARGO_TARGET_DIR=C:/ezl-target bash tools/gate_p0.sh
# P0 对拍全量
CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test engine_parity_report -- --ignored --nocapture
# 度量
python tools/metrics.py --check
# 回归钉
CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test p0_known_bug_pins
```
