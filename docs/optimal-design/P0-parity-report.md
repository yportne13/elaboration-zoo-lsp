# P0 引擎对拍报告（reference vs twin）

> P0-1 交付物。分支 `p0-p1-baseline-cleanup`（共享工作树，未 commit/push）。
> 构建目录 `C:\ezl-target`（F: 盘 <1GB，禁止 F: 构建）。本次只读源码 + 新增/修改
> `tests/engine_parity_report.rs`、`tests/p0_known_bug_pins.rs`、`tools/run_engine_parity.sh`、
> 本文件；两处 `src/` 小修见 §5（Lead 批准的 panic 修复）。
> 证据标注：`[实测]` = 本次在 C:\ezl-target 跑出；`[已知]` = 既有文档结论；`[码]` = 源码核对。

## 1. 结论摘要

| 指标 | 数值（2026-11-09，release，本地全量） |
|---|---|
| 语料 | **34 个用户文件**（examples 32 = 根 5 + `examples/hdl` 27；`tests/*.typort` 2）+ prelude 35 个 `.typort`（只计基线，不当用户文件） |
| 引擎归属 | twin-owned **32/34**；fallback **2**：`examples/hdl/18-utils.typort`（`untrusted-error`）、`tests/trait_system_tests.typort`（修复前 panic，修复后见下行） |
| 判定 parity | **34/34 相等**（Ok/Err 分类） |
| 诊断逐字节 parity | **33/34 相等**；唯一差异 `examples/typeclass_complex.typort`（twin 错误 span 全零，**文本相同**——已知偏差） |
| panic | 修复前 **2**（`trait_system_tests.typort`：ref `unification.rs:754` OOB + twin `bump_spine_iter/typeclass.rs:294` OOB）→ 修复后 **0** |
| 耗时 | 全量 wall **≈69s**（fresh-backend 口径）；单文件 elaboration 合计 ref **39.4s** vs twin **15.5s**（2.54×） |
| prelude 装载 | 首载 `ref-hdl ≈7.9s` vs `twin-hdl ≈3.8s`（2.1×）；core 模式首载远小（<0.2s） |
| 与已知结论对账 | `[已知]` "29/30 examples owned、18-utils 唯一回落" 在本扩展语料下成立：examples owned 31/32（唯一回落 18-utils）；tests 侧 `trait_system_tests` 是 P0 新发现的崩溃点 |

**一句话**：语料面上**判定零分歧、诊断一处已知 span 偏差**；真正的 P0 发现是
`trait_system_tests.typort` 在**两个引擎上都会 panic**（CLI `typort check` 可复现），根因是
trait 重声明后 `head_index` 残留旧下标，已按 Lead 指示修复并加回归钉（§5）。

## 2. Harness 设计（`tests/engine_parity_report.rs`）

- 复用 `tests/twin_engine_tests.rs` 的 `Backend` + `CapturingClient` 模式：
  `Backend::new_with_engine(client, Engine::{Reference,Twin})` → `load_prelude()`（HDL 文件）
  或 `load_prelude_skip_hdl()`（core 文件）→ `process_file(&uri, source, Some(1))`。
- 语料发现：递归扫 `examples/` + `tests/*.typort`；按路径（`examples/hdl/`）与内容标记
  （`module `、`UInt`、`regNext`、`#[derive(Bundle)]`…）选择 prelude 模式。
- **每个文件、每个引擎都用全新的 `Backend`**：共享 Backend 会跨文件泄漏 trait solver 的
  instance/head_index 状态（smoke 阶段实测触发 OOB），且 panic 会 poison 其 `Mutex<Infer>`；
  prelude 装载时间单独记录（`prelude_load_ms`），不混入单文件 elaboration 时间。
- 记录：文件、分组、prelude 模式、twin 归属（`twin_tables.contains_key` + `twin_fallback_reason`）、
  各 severity 诊断数与全文、耗时、panic；对比：判定一致、severity 计数一致、诊断
  `(severity,message,range)` 逐字节一致、message-only 一致、差异条目（前 8 条）。
- 输出：`$ENGINE_PARITY_OUT/engine-parity-report.{json,md}`（默认跟随 `CARGO_TARGET_DIR`，
  本次 = `C:\ezl-target\`）。测试 `#[ignore]`，只在显式运行时跑；断言"报告生成、语料>0、
  无未知 panic"（**不要求 parity 全绿**）。
- 环境开关：`ENGINE_PARITY_OUT / ENGINE_PARITY_MAX_FILES / ENGINE_PARITY_ONLY /
  ENGINE_PARITY_MODES`；CI smoke 档由 `GATE_P0_MAX_FILES` 注入 `ENGINE_PARITY_MAX_FILES`。

## 3. 语料与归属明细

| 组 | 文件数 | twin-owned | fallback |
|---|---:|---:|---|
| `examples/`（根，5） | 5 | 5 | — |
| `examples/hdl/`（27） | 27 | 26 | `18-utils.typort`: `untrusted-error` |
| `tests/*.typort`（2） | 2 | 1（`quick_validate`） | `trait_system_tests.typort`（修复前 panic；修复后由 twin/参考各自正常分析） |
| **用户文件合计** | **34** | **32（修复前）** | **2** |
| `src/prelude/**/*.typort` | 35 | —（作为 prelude 基线装载） | — |

fallback 类直方图（修复前）：`untrusted-error` ×1（18-utils）。
`18-utils` 是**双付**（twin 回落参考版后两引擎各跑一遍）：ref `8195ms` vs twin `8130ms`
（两遍成本几乎相同），与 `docs/l13-perf-replace-2026-09-27.md §1.3/§5.1` 的判断一致。

## 4. 分歧清单（修复前基线，全量）

`verdict`（Ok/Err 分类）：**34/34 一致，无分歧**。

诊断逐字节不一致：**1 个文件**

| 文件 | 差异 | 性质 |
|---|---|---|
| `examples/typeclass_complex.typort` | 1 条 diagnistic（共 32 条，全为 INFORMATION） | twin 的 span 全零，`message` 文本相同；`[已知]` twin 不携带 binder/源码 span（`docs/l13-perf-replace §1.4`、`docs/lsp-twin-wiring §4` 记录的既知偏差），不是本次改动引入 |

`examples/hdl/18-utils.typort`：两引擎诊断一致（14 条 INFO），但 twin 因 `untrusted-error`
回落参考版（见 §3）。慢文件：`18-utils` ref 8195ms / twin 8130ms（双付）、
`20-misc` ref 5482ms / twin 890ms（6.2×，参考版慢）。

## 5. P0 findings：trait 重声明导致两引擎 panic（**已修**）

### 5.1 现象与复现

`[实测]` `typort check tests/trait_system_tests.typort`（release CLI）：

```
thread '<unnamed>' panicked at src\L13_namespace\unification.rs:754:74:
index out of bounds: the len is 1 but the index is 1
Error: "typort worker thread panicked"
```

同一 fixture 经 `Backend`（两引擎）都会 panic：ref 在 `unification.rs:754`，twin 在
`bump_spine_iter/typeclass.rs:294`（都是 `instances[i]` 越界）。原 fixture 的触发面：
它重声明了 prelude 已有的 `trait Add / Sub / Mul / Not` 并随后使用 `+ - *`。

**最小复现（9 行，已实测两引擎均修前 panic / 修后正常）**：

```typort
trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}
impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = that
}
def two = succ (succ zero)
def three = succ two
def five = two + three
```

### 5.2 根因（`[码]`）

1. 用户文件重声明 prelude trait 时 `Synth::new_trait`（`src/L13_namespace/typeclass.rs:138-145`）
   执行 `class_instances.insert(name, vec![])`，**重置实例表**；
2. 但 `head_index`（键 `(trait, head)` 的下标桶）**没有被清理**，仍持有旧实例的下标；
3. `impl_trait_for` 把新实例按 0.. 重推下标，旧桶条目（如 `[1,2,…]`）+ 新条目混在一起；
4. `solve_multi_trait_ref`（`unification.rs:744-758`；twin 对应
   `bump_spine_iter/typeclass.rs:265-298`）信任 `head_index`，直接 `instances[i]` ⇒
   当任一旧下标 ≥ 新 `instances.len()` 时越界。`Add` 的桶里 `head = Nat` 的实例很多
   （`UInt/SInt/Bits` 的 `Add[Nat, X]` 首参都是 `Nat`），所以重声明后极易触发。

影响面：**用户可见崩溃**（CLI `typort check`；LSP 两引擎同点位）。性质是 crash（S2），
不是静默错编译——修复前后接受集一致（见 §5.4）。

### 5.3 修复（两引擎同口径，最小改动）

- 参考版 `src/L13_namespace/unification.rs:751-766`：`idxs` 非空但**任一 `i >= instances.len()`**
  时，回退全量扫 `instances.iter().filter_map(filter)`（与"没有索引"路径完全等价，候选集不变）。
  保留正常路径的 O(1) 过滤。
- 孪生 `src/L13_namespace/bump_spine_iter/typeclass.rs:282-300`：同样的守卫 + 全量扫回退。
- 选"回退全量"而不是"purge head_index"：purge 需要与 twin 的 state journal / LSP 轮次撤销
  机制对齐（`new_trait` 的 undo 只记 `TraitInstancesSet`，不记 head_index），本轮优先保语义
  与最小风险；兼容的 purge 作为 P2 根治项。
- 回归钉：`tests/p0_known_bug_pins.rs`（2 个测试，ref/twin × 最小复现 + 原 fixture，
  `catch_unwind` 断言不 panic）；并已实测：

| 验证 | 结果 |
|---|---|
| `cargo test --release --test p0_known_bug_pins` | **2 passed** |
| `typort check tests/trait_system_tests.typort` | exit **0**，输出 `ALL_TRAIT_TESTS_PASSED`，无 panic |
| 全量 parity（修复后）`engine_parity_report` | panic **0**；判定 parity 仍全等（见 §6） |
| `l13_fast_parity`（629 例） | **全绿**（见 §6；修复只改变 stale-index 这条异常路径） |

### 5.4 语义与遗留

- 全量/parity 语料在修复前后**判定一致**（唯一异常是 fixture 本身从 panic 变为正常分析）。
- **P2 待办**：① 根治 = `new_trait` 时安全 purge 同名 trait 的 `head_index`（与 undo journal
  对齐）或直接**拒绝重声明 prelude trait** 并给诊断；② 为 `remove_file`/import 重载等其它
  "实例表重置"路径补同类不变量（`idxs` 必须可回退）；③ 把本 fixture 加入
  `known_bug_pins` 的正式清单（当前在 `tests/p0_known_bug_pins.rs`）。

## 6. 性能基线（`[实测]`，2026-11-09，同一 release 二进制）

### 6.1 prelude 装载（每文件 fresh Backend 口径）

| engine | mode | loads | total ms | mean ms | first ms | files |
|---|---|---:|---:|---:|---:|---:|
| reference | core | 4 | 201.4 | 50.3 | 38.2 | 4 |
| twin | core | 4 | 112.7 | 28.2 | 28.9 | 4 |
| reference | hdl | 30 | 8295.7 | 276.5 | 7873.8 | 30 |
| twin | hdl | 30 | 4978.2 | 165.9 | 3831.6 | 30 |

（首载 = PRELUDE_CACHE 首次构建；之后是 clone 定价。ref-hdl 首载 **7.87s** vs twin-hdl
**3.83s**，与 Lead 的 smoke 读数一致。twin 的内部 prime_resident 见 `entry.rs:898`。）

### 6.2 单文件 elaboration（不含 prelude 装载）与 wall

- 合计：ref **39,386ms** / twin **15,500ms**（2.54×，修复前同一二进制；修复后见 §6.3）。
- 全量 wall ≈ **68.8s**（34 文件 × 2 引擎 × fresh backend；prelude 装载合计 ≈13.6s）。
- 慢文件：`18-utils` ref 8195 / twin 8130（fallback 双付）；`20-misc` ref 5482 / twin 890。
- 与 `[已知]` 矩阵一致：twin 在真实 HDL prelude 与 examples 上领先 ~2× 量级
  （`docs/bench-matrix-2026-09-20.md`、FACTS §5），reference 在大证明/宽文件上更慢。

### 6.3 修复后复跑（`[实测]`，同一 harness）

- 全量：**panic 0**；verdict parity 34/34；diag exact 33/34（同 §4）；twin-owned 数据与
  修复前一致（除 `trait_system_tests` 从 panic 变为被正常分析）。
- `l13_fast_parity` 全绿（629 例，见命令 §8）。
- 耗时与修复前同量级（修复只影响异常路径）。

## 7. 与 D7 §8 P0 判据对齐

| D7 P0 判据 | 本报告状态 |
|---|---|
| 可机器复跑的对拍报告（归属/回落类/诊断/墙钟/RSS 峰） | ✅ JSON+MD；RSS 峰未采集（**局限**，见 §8） |
| 复现已知结论（29/30 owned、18-utils 回退、examples ~1.78×） | ✅ examples 31/32 owned、18-utils `untrusted-error`；examples 总耗时比 ref 38.35/twin 15.5 且含 fallback 双付，方向一致 |
| 报告中"差异不阻塞、可 triage" | ✅ 判定 0 分歧、诊断 1 处已知 span 偏差 |
| 发现真实缺陷并登记 | ✅ trait 重声明 panic（已修 + 钉 + P2 根治项） |

## 8. 局限（如实）

1. **cross-file 语义未覆盖**：`tests/*.typort` 作为单文件独立跑，import/package 跨文件
   重建序列（`rebuild_set`）未进入本 harness；相关 fallback 类（`cross-file`）只在真实
   LSP/项目会话出现。
2. **无 per-file 硬超时**：只记录耗时并把 >5s 标 `slow`；挂死需要外层 timeout
   （`tools/run_engine_parity.sh` 未加，CI 可用 job timeout）。
3. **Ok 输出字节 parity 不在本报告**：harness 比较诊断（severity/message/range），不比较
   stdout/Verilog 产物字节；后者由 parity 套件与 `examples` 测试覆盖。
4. **fresh Backend per file 的副作用**：每次重付 prelude loader（twin prime）；报告把装载
   时间单列，故单文件 elaboration 时间可比，但整跑 wall 偏大。共享 Backend 在本树不安全
   （见 §2/§5），不是 harness 的随意选择。
5. **RSS 峰未采集**（D7 P0 判据含该列）：测试进程内可用 `GetProcessMemoryInfo` 但会引入
   Windows API 依赖，本轮未做；建议 CI/perf-experimenter 侧用外部采样补。
6. 诊断比较用"最后一次 publish"（LSP 语义），中间态覆盖不比较；span 归一化未做
   （因此已知的 twin span 全零会显式出现在差异列，而不是被抹平）。

## 9. CI smoke 与本地全量（两级）

| 级别 | 命令 | 语料 | 预期 |
|---|---|---|---|
| **本地全量**（P0 基线） | `CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test engine_parity_report -- --ignored --nocapture` | 34（+35 prelude） | ~70s 编译后运行；报告 JSON/MD |
| **CI smoke**（optional gate） | `GATE_P0_MAX_FILES=20 bash tools/run_engine_parity.sh` | 前 20 个（排序后） | 有界 ≤10min；报告注明 smoke |
| 回归钉 | `CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test p0_known_bug_pins` | 2 测试 | 2 passed |
| L13 闸 | `CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test l13_fast_parity` | 629 例 | 全绿 |

`tools/run_engine_parity.sh` 默认**全量**（不设 `ENGINE_PARITY_MAX_FILES`）；CI 用
`GATE_P0_MAX_FILES` 注入 smoke 上限，报告中 `meta` 会记录本次实际语料数与模式。

## 10. 复现与路径

```
# 全量（本报告数据来源）
CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test engine_parity_report -- --ignored --nocapture
# 报告
C:\ezl-target\engine-parity-report.json
C:\ezl-target\engine-parity-report.md
# 原始运行日志
C:\ezl-target\engine-parity-run.log

# 最小复现（panic 修复的 pin 内联在 tests/p0_known_bug_pins.rs）
CARGO_TARGET_DIR=C:/ezl-target cargo test --release --test p0_known_bug_pins
```

**文件清单**：`tests/engine_parity_report.rs`（新）、`tests/p0_known_bug_pins.rs`（新）、
`tools/run_engine_parity.sh`（新）、`docs/optimal-design/P0-parity-report.md`（本文件）；
panic 修复：`src/L13_namespace/unification.rs`、`src/L13_namespace/bump_spine_iter/typeclass.rs`。
