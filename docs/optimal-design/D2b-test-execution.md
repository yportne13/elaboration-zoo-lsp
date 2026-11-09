# D2b · EXP-7 正确性实验执行报告（实测完成）

> 执行者：EXP-7（analyst-l09）。时间：2026-11-09 01:42–02:06（Asia/Shanghai）。
> 工作树 HEAD `8443586e`；构建/执行 target `C:\ezl-target`（F: 仅 0.8 GB，全程未在 F: 构建）。
> 二进制：`cargo build --release --bins`（Lead，01:28–01:30）+ 本轮测试目标 `cargo test --release --no-run`
> （batch1 01:43–01:47，288.7 s；batch2 02:02–02:03，49.8 s）。
> 标注：`[实测]` = 本报告 raw；`[码]` = 源码；`[文档]`；`[推断]`。
> 配套 raw：`docs/optimal-design/experiments/raw/EXP-7-*.txt|.csv`（索引见 §10）。
> 说明：`D2-correctness.md` 于 01:35 落盘，本报告按其 §6 E7.1–E7.6 对齐（差异见 §8）。

## 1. 结论摘要（先结论）

1. **全部现役测试套件在重建 HEAD 上通过：2255 passed / 0 failed / 19 ignored（ignored 均为既有探针）**，共 25 个运行目标、全部 exit=0 [实测]。
2. **可复现性**：Lead 用同一批 exe 独立复跑 11 个目标（1115 passed）与本轮逐项一致（含 L13 629 passed/6 ignored）[实测]。
3. **Lean oracle 真例通过**：`LEAN_ORACLE=1` 下 2/2（4 例 curated 语料），使用 11-08 预构建 `engine-oracle.exe`，**无需 lake/Lean 工具链** [实测]。
4. **无新回归、无 S1 失败**。历史文档"全量 lib 49 个既有失败"在 L07–L12 过滤下**不复现**（0 failed）；口径存疑，见 §6。
5. **D4 数据独立复核通过**：4 个复跑点中 3 个计时点误差 +0.7%/+0.8%/+0.9%（窗口内），1 个确定性分配计数点**逐字节相同**；另做 3 处 raw↔正文对账一致 → D4 数据可信 [实测]。
6. **结构性限制未被本轮测试触发**（单行 enum 假阴性、L09 卡住 match panic、effort cap panic 等），因此"全绿"只说明**按当前判据通过**，不构成健全性证明（同 D2 §6 E7.4-7）。

## 2. 方法与执行

### 2.1 资产与构建

| 项 | 事实 | 结论 |
|---|---|---|
| `C:\ezl-target\release\deps` | 预置 95 rlib + `libelaboration_zoo_lsp-*.rlib`（50.75 MB），无测试 harness | 测试目标需现编 |
| F: `target/release/deps` 旧测试二进制 | 最新 2026-09-26（主体 09-25），比 HEAD 旧 6 周+ | **未使用**（口径：不作 HEAD 证据） |
| Lean oracle | `lean/.lake/build/bin/engine-oracle.exe`（4.16 MB，11-08 21:20）预构建；无参输出 `usage: engine-oracle <case>`（4 cases） | 直接可用，无需工具链 |
| `Cargo.toml` | 无 `[dev-dependencies]` | release 测试复用已编依赖，仅编 harness |

构建命令（全部 `CARGO_TARGET_DIR=C:\ezl-target`）：

```text
# batch1（01:43:44–01:47:48，288.7 s，exit 0；14 test 目标 + lib）
cargo test --release --no-run --lib --test l07_blackbox --test l07_blackbox_v2 --test l07_blackbox_v3
  --test l07_fast_parity --test l08_blackbox --test l08_blackbox_v2 --test l08_fast_parity
  --test l09_fast_parity --test l10_fast_parity --test l11_fast_parity --test l12_fast_parity
  --test l13_fast_parity --test known_bug_pins --test lean_oracle_parity
# batch2（02:02:04–02:02:54，49.8 s，exit 0；LSP 4 目标）
cargo test --release --no-run --test namespace_tests --test hover_tests --test completion_tests --test cross_file_tests
```

### 2.2 执行方式与判据

- 直接调用构建出的测试二进制（`C:\ezl-target\release\deps\<suite>-<hash>.exe`），
  `--test-threads=1` 串行（L13 与 LSP 尤其），cwd = 仓根，`2>&1` 落盘到 `raw/EXP-7-<name>.txt`。
- 每项记录 exit code、wall time、`test result:` 行的 passed/failed/ignored（`raw/EXP-7-summary.csv`、`summary2.csv`）。
- 判据：exit 0 且 failed=0；passed 与静态 `#[test]` 数对账（`#[path]` 会带入 lib 测试，见 §5）。
- 与 D2 E7.4 判读树一致：parity 判定分裂/panic/超时/生产套件失败 → 逐项分级；本轮无触发。

### 2.3 并发与 lock

- 起始检查：`.lock` 由 perf 持有（EXP-5/6，01:41 删除）；确认 `Get-Process` 无 cargo/rustc/bench 后
  写 `owner=EXP-7(analyst-l09)`；测试与 bench 不并发；结束删除 lock（§10 时间线）。
- 唯一重叠：Lead 01:53–01:55 用直接 exe 命令独立跑核心套件（不写 lock、不干扰，结果作为**第二执行者**证据，§3 注）。

### 2.4 首次执行失败与修复（重要教训）

- **失败现象**：首版 runner 与 Lead 首版脚本均 0.28 s 内全部 `NO_RESULT_LINE`。
- **根因**：`Start-Process` 在本环境因环境变量同时存在 `NO_PROXY` 与 `no_proxy` 抛
  `ArgumentException`（"字典中的关键字:'NO_PROXY' 所添加的关键字:'no_proxy'"）→ **进程从未启动**；
  不是测试失败。
- **第二坑**：函数参数命名为 `$args`（PowerShell 自动变量）会静默丢失实参——我的首次 D4 复核复跑
  （`EXP-7-review-*`，已作废删除）就因此让 bench 收到空参（l01bench 退回默认 rounds=5、typort 打印 usage、
  l06l13mem 跑全部章节）。
- **修复**：改为**直接调用** `& $exe @arglist`（参数变量改名 `$arglist`），退出码取 `$LASTEXITCODE`；
  正确参数复跑见 §9（`EXP-7-review2-*`）。

## 3. 结果总表 A：语言套件（17 个运行目标，`EXP-7-summary.csv`）

| # | 套件 | 静态 tests(含带入口径) | exit | passed | failed | ignored | wall(s) |
|---:|---|---:|---:|---:|---:|---:|---:|
| 1 | lib L07_sum_type | 70 | 0 | **70** | 0 | 0 | 8.5 |
| 2 | lib L08_product_type | 60 | 0 | **60** | 0 | 0 | 1.2 |
| 3 | l07_blackbox（+70 lib） | 117 | 0 | 48（另 70 lib 在 v3 计） | 0 | 1 | 0.8 |
| 4 | l07_blackbox_v2 | 53 | 0 | 51 | 0 | 2 | 0.2 |
| 5 | l07_blackbox_v3（+70 lib） | 117 | 0 | **116** | 0 | 1 | 7.1 |
| 6 | l07_fast_parity（27+70 lib） | 97 | 0 | **97** | 0 | 0 | 8.4 |
| 7 | l08_blackbox | 58 | 0 | 57 | 0 | 1 | 0.8 |
| 8 | l08_blackbox_v2 | 53 | 0 | 51 | 0 | 2 | 0.2 |
| 9 | l08_fast_parity（35+60 lib） | 95 | 0 | **95** | 0 | 0 | 2.1 |
| 10 | l09_fast_parity（29+10 lib） | 39 | 0 | **39** | 0 | 0 | 0.1 |
| 11 | l10_fast_parity（21+25 lib） | 46 | 0 | **46** | 0 | 0 | 0.1 |
| 12 | l11_fast_parity（19+33 lib） | 52 | 0 | **52** | 0 | 0 | 0.2 |
| 13 | l12_fast_parity（15+35 lib） | 50 | 0 | **50** | 0 | 0 | 0.1 |
| 14 | l13_fast_parity（15+614 lib） | 635 | 0 | **629** | 0 | 6 | 129.9 |
| 15 | lib L13_namespace | 620 | 0 | **614** | 0 | 6 | 126.0 |
| 16 | known_bug_pins | 8 | 0 | **8** | 0 | 0 | 8.4 |
| 17 | lean_oracle_parity（`LEAN_ORACLE=1`） | 2 | 0 | **2** | 0 | 0 | 1.0 |

**小计：17 目标，passed 2085，failed 0，ignored 19。**
注：`lXX_fast_parity`/`l07_blackbox_v3` 用 `#[path]` 编入本层 lib 源码，故再跑一遍该层 lib 单测
（L07：27+70=97、L08：35+60=95、L09–L12 同；L13：15+614=629）——这与 FACTS §3 的"重复执行"说明一致。

## 4. 结果总表 B：LSP 4 套件 + lib L09–L12（8 个运行目标，`EXP-7-summary2.csv`）

| # | 套件 | 静态 tests | exit | passed | failed | ignored | wall(s) |
|---:|---|---:|---:|---:|---:|---:|---:|
| 18 | namespace_tests | 30 | 0 | **30** | 0 | 0 | 8.6 |
| 19 | hover_tests | 20 | 0 | **20** | 0 | 0 | 0.4 |
| 20 | completion_tests | 14 | 0 | **14** | 0 | 0 | 1.3 |
| 21 | cross_file_tests | 3 | 0 | **3** | 0 | 0 | 0.4 |
| 22 | lib L09_mltt | 10 | 0 | **10** | 0 | 0 | 0.1 |
| 23 | lib L10_typeclass | 25 | 0 | **25** | 0 | 0 | 0.1 |
| 24 | lib L11_macro | 33 | 0 | **33** | 0 | 0 | 0.2 |
| 25 | lib L12_canonical | 35 | 0 | **35** | 0 | 0 | 0.1 |

**小计：8 目标，passed 170，failed 0，ignored 0。合计 25 目标 = 2255 passed / 0 failed / 19 ignored。**

**第二执行者（Lead，`EXP-7-lead-run.txt`，01:53:05–01:55:33，直接 exe）**：11 目标、1115 passed、
0 failed、8 ignored，与本表重叠项**逐项数值一致**（97/95/39/46/52/50/629/6、48/1、57/1、oracle 2）[实测]
⇒ 同一二进制上**结果可复现**，不是单次侥幸。

## 5. 静态预期 vs 实测对账

| 观察 | 结论 |
|---|---|
| L13 lib 静态 grep `#[test]`=612（ignored 6）vs 运行 620 匹配（614 passed + 6 ignored） | 差 8，疑为循环/参数化生成用例（未逐一核对），**不影响 0 failed 结论** [推断] |
| `known_bug_pins` 静态 8 tests、文件内 3 处 `#[ignore]` 文本，但运行 8 passed / 0 ignored | 那 3 处是**注释/文档串**而非属性；实测 ignored=0 |
| L13 parity/lib 各 6 ignored | 同一批 6 个探针（`probe_timing`、`*_probe_formats` 等）被跑两次，unique 探针 =6 |
| 19 ignored 累计 | = L07/L08 blackbox 探针 6（1+2+1+1+2，跨 5 文件去重后 6）+ L13 探针 6 + 重复计数 7；**均为既有探针，不是失败** |

## 6. 失败判读：已知 vs 新回归

- **失败明细：无**（25 个运行目标 failed=0，无 panic、无超时、无崩溃码）。
- **历史基线核对**：`docs/l13-perf-review.md:94/227`、`l13-sumcase-decl-typ-pretty-panic.md:193`、
  `nat-primops-plan.md:47` 等（2026-09）称"全量 lib 有 49 个既有失败，位于 L01–L12 旧课程"。
  本轮 **L07–L12 六个 lib 过滤 0 failed**（70/60/10/25/33/35），与"L07–L12 遗留失败"口径**冲突**：
  最可能那批已在 09–11 月修复（或该口径实指 L01–L06 模块）；本轮未跑 L01–L06 过滤，**不能完全裁决**，登记为文档口径待复核。
- **已知限制未被触发（不是通过）**：L13 单行 enum 两版同错（`l13_fast_parity` 头注；parity 仍绿=假阴性）；
  L09 卡住 match 应用 panic（L09 lib 无端到端例）；L10–L12 effort cap panic；L09/L10 重定义静默覆盖；
  with-K 无检查；L12/L13 原生 Nat 定义相等。这些对应 D2 §3 known bugs #2/#8/#9/#10/#1，**本轮测试面不覆盖**。
- **D2 E7.6 已知 bug 复现语料**（未单列手工复现，但映射到已跑的绿测）：
  c1 两跳环 → `test_occurs_check_transitive_chain` ✅；c2 卡住索引方程 → `test_stuck_match_equation_bounded` ✅；
  空类型零臂 → `test_empty_type_zero_arm_match_accepts_canonical_conflicts` ✅；
  P15 struct_eq pending → `test_struct_eq_compares_match_pending_values` ✅；
  R2 VSub 嵌套限制 → `test_occurs_transitive_vsub_nested_is_documented_limitation` ✅；
  L13 卡住 match → `test_stuck_match_application_does_not_panic` ✅；L13 HDL004 宽度 → `known_bug_pins` 2 条 ✅。
  ⇒ **7/12 语料的期望行为被绿测锁定**；effort cap、L09 panic、重定义静默未直接复现（写 §8 未跑项）。

## 7. Lean oracle（真例，非 skip）

- 命令：`$env:LEAN_ORACLE='1'; <lean_oracle_parity-.exe>`（oracle 路径由 `CARGO_MANIFEST_DIR/lean/.lake/build/bin/` 自动发现）。
- 结果：`lean_oracle_rejects_unknown_case` ✅、`lean_oracle_matches_reference_on_review_corpus` ✅，2 passed / 0 failed，1.0 s [实测]。
- 口径：oracle 为 **2026-11-08 M3 curated 语料**（4 cases：occurs-transitive / stuck-match-bounded /
  empty-type-zero-arm / struct-eq-pending），与 L07 参考引擎差分；**未重新 `lake build`**（用预构建 exe，无 Lean 工具链也可跑）。
- 意义：这是唯一"第三方语义裁判 vs Rust 引擎"的独立证据；4/4 一致，但样本小（D2 §5/§6 已登记局限）。

## 8. 与 D2 §6 EXP-7 计划的对齐

| D2 组 | 计划 | 本轮状态 |
|---|---|---|
| E7.1 lib | 各层 lib（L07–L13） | ✅ 全跑（L07 70/L08 60/L09 10/L10 25/L11 33/L12 35/L13 614+6） |
| E7.2 parity | 7 个 fast_parity | ✅ 全跑（27/35/29/21/19/15/15 本体 + 带入口径见 §3） |
| E7.3 blackbox | l07_blackbox×3、l08_blackbox×2 | ✅ 全跑（48/51/116、57/51；ignored 1/2/1、1/2） |
| E7.4 生产 | L13 LSP 11 套 + twin_engine_tests | **部分**：LSP 4/11（Lead 批准收缩：namespace/hover/completion/cross_file）；`twin_engine_tests` 未构建未跑；其余 LSP 7 套未跑 |
| E7.5 oracle | `LEAN_ORACLE=1` + lake build | ✅ 2/2（用预构建 exe 代替 lake build，见 §7） |
| E7.6 已知 bug 复现 | 手工/临时 example | **部分**：7/12 由绿测覆盖（§6）；手工复现未做 |
| E7.4 并行压力轮 | 默认并行再跑 | 未做（本轮全部 `--test-threads=1`，为可归因基线） |

## 9. D4 实验数据独立复核

### 9.1 方法

- 同一份 `C:\ezl-target\release` 二进制、同命令、同参数，在测试任务完成后（**同窗口尾段、静置**）复跑小段；
  raw：`EXP-7-review2-*.txt`。判据：同量级（计时点 ±15% 内视为窗口噪声一致）、确定性计数须逐值相同。
- 另对 D4 正文做 **raw↔正文静态对账**（不依赖复跑）。

### 9.2 复跑结果

| 数据点 | D4 记录 | 本轮复跑 | 偏差 | 判定 |
|---|---|---|---|---|
| EXP-1 church_pair(4000) naive / `bump_spine_iter_ss` min | 0.761 / 0.029 ms | 0.767 / 0.029 ms | +0.8% / 0% | ✅ 一致 |
| EXP-3 L07 match k=11 basic / fast_ss | 0.150 / 0.050 ms | 0.151 / 0.052 ms | +0.7% / +4% | ✅ 一致 |
| EXP-6 `typort check examples/alu.typort` 墙钟 | 5212 ms | 5260 ms（含进程启动） | +0.9% | ✅ 一致 |
| EXP-5 L10 traitchain k=9 basic 分配 | 122,477,444 allocs / 5,555,549,210 B（5298.18 MB）；ratio 172.99× bytes / 489.20× allocs | **完全相同的数值**（122,477,444 / 5298.18 MB / 172.99× / 489.20×） | 0 | ✅ 确定性口径逐字节一致 |

### 9.3 raw↔正文对账（抽 3 处）

1. `exp3-l10.txt`：traitchain basic 23791.136（rounds=1）、fast_ss 39.382、fast 43.063 → D4 §3 表与正文一致 ✅
2. `exp5-mem-L10-traitchain.txt`：`ratio basic/fast = 172.99× bytes, 489.20× allocs` → D4 写"173×/489×" ✅（取整）
3. `exp1-clean-church-4000.txt`：naive 0.761、`bump_spine_iter_ss` 0.029 → D4 §1 表一致 ✅

### 9.4 结论

D4 数据**可信**：计时点在窗口噪声内可重现（≤4%），确定性分配计数逐值相同；正文与 raw 无对不上之处。
保留 D4 自述的限制：bench 只输出 min/median（无 max）、L10 traitchain basic 单轮、跨窗口绝对值仍不可强比。
**唯一补充**：D4 §3 提到 L07 match k=11"两次干净窗口 0.050 vs 0.064 抖动"；本轮复跑 basic=0.151、fast_ss=0.052
（与主表同档，未见 0.064 的系统性偏移），属窗口抖动，不影响结论。

## 10. 局限与下一轮改进

1. **未跑项**：LSP 其余 7 套（lsp_protocol_robustness/error_recovery_backend/hover_stress/completion_handler/
   format_handler/emit/hdl_check_locations/docgen/parser_error/sim/macro_goto/impl_goto/large_did_open）、
   `twin_engine_tests`、D2 E7.6 手工复现、默认并行压力轮、L01–L06 套件；原因=Lead 批准的 30 分钟窗口与优先级。
2. **口径**：全部 `--test-threads=1`（可归因基线）；并行下的偶发（UAF 类，历史已修）未验证。
3. **release vs debug**：本轮 `cargo test --release`；未验证 debug/`[profile.test]` 口径。
4. **单次执行**：每套件跑 1 次（L13 除外有 Lead 第二次）；偶发失败需二次确认的机制未启用。
5. **runner 教训（下一轮方法论）**：① 不要用 `Start-Process`（本机 NO_PROXY/no_proxy 环境字典重复键会抛异常且静默不启动进程）；
   ② 不要用 `$args`/`$input`/`$error` 等自动变量作函数参数；③ 直接 `& exe @arglist` + `$LASTEXITCODE` + Tee 落盘；
   ④ 每套件独立 raw + CSV（本轮 `EXP-7-summary*.csv` 已可机器对账）。
6. **时间线**：构建 batch1 288.7 s + batch2 49.8 s；语言套件执行 ≈ 5 min（L13 占 4.3 min）；LSP+lib 补充 ≈ 42 s。

## 11. 给 Lead 的一句话结论

**重建 HEAD 上 EXP-7 全绿：25 目标 2255 passed / 0 failed / 19 既有探针 ignored，Lean oracle 2/2，
D4 四项复核一致——"按当前判据通过"，但已知假阴性与未覆盖轴（§6/§10）不得读作正确性已证。**
