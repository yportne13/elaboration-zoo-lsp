# 03 · L13 参考版能否接管 LSP（封印 L13 孪生的前置条件）

> 角度：L13 参考版（`mod.rs` + 分文件）与 L13 孪生（`bump_spine_iter/`）在 **LSP 产品面**上的职责差，
> 回答「参考版接管 LSP 还缺什么、封印孪生要满足什么」。
> 基线：HEAD `8f4287ae` + 2026-11-24 21:3x 工作区（Lead 正在实施 L06–L12 硬封印，行号可能随之漂移）。
> 只读 `src/`；**未** `cargo build/check/test`；实测用的是 16:25 构建的 `target/release/*.exe`（拷贝到 `tmp/lsptest/` 运行，不占 `target/` 锁）。

## 0 结论速览

| 问题 | 答案 | 依据 |
|---|---|---|
| `TYPORT_LSP_ENGINE=reference` 现在能跑通吗 | **能，而且不是残桩**：诊断 / hover / inlayHint / definition 四项在本轮 stdio 实测中与孪生**逐字节相同** | 见 §1.2；`src/lib.rs:2584-2799` |
| 参考版缺什么 | 只缺 3 类：`twin_mem_stats` 读数、每 kick 的 `force_memo_clear`、以及**编译期**对孪生模块的 2 处耦合 | 见 §2 |
| 迁移最小集多大 | 核心是 **1 个函数**（`lsp_default`），外加 6~9 处 `#[cfg]` 与 2 处解耦 | 见 §3 |
| 封印 L13 孪生的拦路虎 | **不是 LSP 能力，是编译依赖**：`typeclass.rs` 调孪生的 `state_journal_record`，`probe_count`/`twin_mem_stats` 从孪生 re-export | `src/L13_namespace/typeclass.rs:144-181`、`mod.rs:27-37` |
| 性能/内存代价 | CPU **3.5×**（359→102 ms/kick 的反向）、内存**省 2.2×**（429MB 稳态 / 730MB 峰 → ~200MB） | `src/lib.rs:266-284` |

> **口径纠正**：任务书里「ref 730MB / twin 200MB」的顺序与源码注释相反。`src/lib.rs:274-284` 原文是
> 「resident twin ~429MB steady / ~730MB peak vs ~200MB for the reference's Rc cache（a ~2.2x memory-for-CPU trade）」。
> ⇒ 封印孪生是**省内存、费 CPU**；这一点会改变迁移的取舍（§3 风险列）。

## 1 (a) `TYPORT_LSP_ENGINE=reference` 这条回落路径的现状

### 1.1 开关与构造点（只有一个）

| 事实 | 锚点 |
|---|---|
| LSP 唯一构造点：`Backend::new_with_engine(Client{..}, Engine::lsp_default())` | `src/lib.rs:4201` |
| `lsp_default()`：仅当变量**恰为** `reference`（忽略大小写）→ Reference，否则 Twin | `src/lib.rs:297-302` |
| 启动时打印实际引擎，是唯一的运行期自证 | `src/lib.rs:4202` |
| 另一个反向默认的构造器 `from_env()`（仅 `twin` 才选 Twin），CLI/tests 走它 | `src/lib.rs:322-327` |
| 参考分支入口：`twin_can_own()` 首位条件是 `self.engine == Engine::Twin` ⇒ Reference 时**必然** false | `src/lib.rs:1506-1510` |
| 于是 `elaborate_with` 第 2500 行直接 `return self.elaborate_reference(..)` | `src/lib.rs:2500-2525` |

### 1.2 实跑证据（本轮新增，不是读码推断）

用 8 条消息（initialize / initialized / didOpen / hover / inlayHint / completion / definition / shutdown）直灌
`elaboration-zoo-lsp.exe`，语料 `examples/alu.typort`（无 import/package ⇒ 孪生**可**拥有的那一类）。坐标均为 LSP 原生 0-based：

| 请求 | reference 结果 | twin 结果 | 判读 |
|---|---|---|---|
| hover @6:11 | `struct simpleALU(_prev: ModuleTree, a: UInt [8], …)`（240B） | 同 | **逐字节相同** |
| inlayHint（全档） | 2 条：`: simpleALU`@13:8、`: adderNat`@26:8 | 同 | **逐字节相同** |
| definition @13:13 | span 7..16 → 模块名 | 同 | **逐字节相同** |
| publishDiagnostics | 两阶段 0 → 4 条（全 INFORMATION=println） | 同 | **逐字节相同** |
| 消息序列 | 14 条，多一条 `println nf <t>` logMessage（`lib.rs:2764`，ref 独有第二阶段） | 13 条 | 仅日志差 |
| 每 kick 墙钟（同进程实测） | `change 0.132 s` | `change 0.0117 s` | 719B 小文件上 ref 固定开销占主导（大语料 3.5×，`lib.rs:268-270`） |

⇒ **观察面三张表在参考版上是活的**：`Infer::new()` 把总闸 `lsp_collect` 默认设 **true**（`src/L13_namespace/mod.rs:2309`，
与 L06/L07 相反），`clone_prelude_state` 收尾再置一次 true（`mod.rs:4542`）；两张查询闸 `hover_query/inlay_query` 默认 `None` = 全量采集
（`surface.rs:109-121`）。这是「参考版能接管」的地基，不需要新写采集器。

### 1.3 两个分支的职责差（逐项）

| 职责 | Twin 分支 | Reference 分支 | 判读 |
|---|---|---|---|
| 诊断四类（类型错 / 解析错 / HDL WARNING / println INFO） | 自产，`1837-1876` | 自产，`2638-2694` + `2804-2839` | **等价**（实测同） |
| 两阶段发布（先 tyck，后 println） | 仿真：`1882`/`1895` | 原生：`2756`/`2766` | 等价；println 在 ref 是 **defer + 第二阶段 nf**（`2626`/`2760-2767`，`2844-2879`） |
| quick-fix thunk | **清空** `quickfix_map`：`1833` | 生成：`2824-2835` | **ref 更强**（twin 无 code action 可用） |
| 观察面三张表 | `Tycker::hover_table()/completion_table()/inlay_hint_table()` → `ObserveSnapshot`：`1580-1585` | `Infer` 三表 → `hover_table` 快照（move 不 clone）：`2772` | **等价**（实测同）；读侧 6 个访问器对两引擎统一回落（`635-731`） |
| decl 导出 / type_map | `user_decl_exports()` → 全局 `cxt.decl`：`1801-1807` | `local_cxt` 差集 → 全局：`2707-2716`；`type_map` `2749` | 等价 |
| 跨文件数据面（import/package） | **不能**（`1506-1510` 排除） | 能（local_cxt = 全局减去本文件旧符号，`2596-2621`） | ref 独有，且是产品主路径 |
| 预算/看门狗 | `scope(TWIN_OBSERVE_BUDGET_MS=10s)` `1597`；超时 → **丢弃 resident、静默回落 ref** `1602-1611` | `scope_default(LSP_INFER_BUDGET_MS=20s)` `2637`；超时 → **一条锚定到 decl 的 ERROR** `2650-2660` | **E2 机制漂移，用户可见**（§2 #5） |
| 预编译 prelude | 共享 `clone_prelude_state`（`1350`）**加**孪生专属 `prime_resident`（`1437-1469`，~3.3s） | 只有 `clone_prelude_state`（进程级，`mod.rs:4555-4595`） | ref 启动更便宜 |
| `twin_mem_stats` 读数 | `force.rs:414`，经 `mod.rs:37` re-export | **无对位**；只有 `Infer::memory_stats_with_cxt`（`mod.rs:2396`） | **缺**（仅 `typort stats` 用，`src/bin/cli.rs:846`） |
| 常驻内存 | ~429MB 稳态 / 730MB 峰 | ~200MB | ref 省 2.2× |

## 2 (b) 参考版缺什么才能「等价接管」

| # | 项 | 档 | 说明与锚点 |
|---|---|---|---|
| 1 | 诊断全套（4 类 + 两阶段 + 导入合并） | **不缺** | `lib.rs:2754-2767`、`2707-2750` |
| 2 | 三张观察表 + 6 个引擎路由访问器 | **不缺，已接线** | `lib.rs:674-731`；`mod.rs:1506-1517` |
| 3 | 采集总闸 `lsp_collect` | **不缺，默认开** | `mod.rs:2309`、`4542`；`surface.rs:109-121` |
| 4 | quick-fix（twin 侧缺失的反向项） | **ref 更强** | `lib.rs:2804-2839` vs `1833` |
| 5 | 求值预算的**语义** | **有实现但语义不同** | twin 10s 超时=静默回落（`1597-1611`）；ref 20s 超时=落诊断（`2637-2660`）。接管后 IDE 只会看到后者 ⇒ 需要产品决策 |
| 6 | 每 kick 的 force-memo 清空 | **缺** | `on_change`（CLI 路径）在 `lib.rs:1956` 清；LSP 走的 `elaborate_reference`（`2584-2799`）**没有**；下一次清空只发生在新建 Backend 的 `clone_prelude_state`（`mod.rs:4595`）。`FORCE_MEMO_CAP=1<<20`（`mod.rs:197`）兜底，故是「钉住 Rc + 命中陈旧地址」的内存/正确性隐患而非无界增长 **[推断]** |
| 7 | `twin_mem_stats` | **缺实现** | `mod.rs:32-37` re-export；`bump_spine_iter/force.rs:414` 是孪生专属 |
| 8 | `probe_count()` | **有但耦合** | `mod.rs:28-30` 把 ref `pattern_match::probe_count()` 与孪生 `PROBE_COUNT` 相加 |
| 9 | `state_journal_record` 记账 | **有但耦合（编译期硬依赖）** | ref 的 `Synth::new_trait/impl_trait_for/…` 直接调 `super::bump_spine_iter::…`：`typeclass.rs:144/152/165/180`。孪生侧帧空即 no-op（`bump_spine_iter/machine.rs:172-189`），**运行时零成本、编译期必需** |
| 10 | `twin_fallback_reason`/`twin_gate_distrusted`/`ObserveSnapshot` | **不需要**（产品面） | `lib.rs:443-456`；仅孪生诊断/测试用 |

## 3 (c) 迁移最小集（按工作量升序）

| 序 | 改动 | 工作量 | 风险 |
|---|---|---|---|
| 1 | `Engine::lsp_default()` 返回 `Reference`（保留 `TYPORT_LSP_ENGINE=twin` 作回退） | **1 个函数**，`lib.rs:297-302` | 低。可先灰度：ref 359ms/kick vs twin 102ms/kick（`lib.rs:268-270`）是唯一体感差；内存反向改善 |
| 2 | `elaborate_reference` 每 kick 补 `L13_namespace::force_memo_clear()` | 1 行，`lib.rs:2584-2586` | 低-中：属行为改动（memo 版本号 +1），建议独立提交、单独跑 66 个 `tests.rs` 用例 |
| 3 | L13 侧解耦：`probe_count` 拆 `ref`/`twin` 两半；`twin_mem_stats` 的 re-export 挂 `#[cfg(feature="l13-twin")]` | 2 处，`mod.rs:27-37` | 低。调用方只有 `src/bin/l13lspsample.rs:60/70` 与 `src/bin/cli.rs:846` |
| 4 | `typeclass.rs` 的 4 个 journal 调用：抽成本模块的空实现（或整段 `#[cfg(feature="l13-twin")]`） | 4 处，`typeclass.rs:144-181` | 低-中。语义是 no-op，但落在 trait 求解写路径上，改动需覆盖 `r5_typeclass_regression` |
| 5 | `lib.rs` 孪生面挂 `#[cfg(feature="l13-twin")]`：`TwinResident`/`TWIN_RESIDENT`（`359-367`）、prelude prime 块（`1437-1469`）、`twin_elaborate`+`note_twin_fallback`+`twin_can_own`+`twin_fallback_reason`（`1472-1901`）、6 个读路 `Engine::Twin` 分支（`641/679/689/703/715/725/759`）、`Engine::Twin` 变体 | **6~9 处**，最大一块 | **中**：`Engine` 是公开枚举，12 个 `tests/*.rs` 引用 `Engine::Twin`（`twin_engine_tests` 35 处、`engine_parity_report` 4、`hdl042_engine_tests` 2、`r3/r4/r5/r7` 各 2~3 等），需同步 cfg |
| 6 | `src/bin/{l13bench,l06l13mem}` 加 `required-features = ["twins"]`（或新增 `l13-twin` 项）；3 个 L13 测试模块（`mod.rs:410/425/428`：`eval_budget_tests`/`cong_projection_tests`/`termination_check_tests`，均 `Tycker::new()`）同步 cfg | 6 处 | 中：默认门禁覆盖**净减**，须在 `tools/gate_l13.ps1` 保留 `--features l13-twin` 阶段（`:220` 已有） |

**不必做**：重写观察面、给 ref 补一套 `ObserveSnapshot`、把 `hover_table` 挪到新结构——§1.2 已实测证明这些路由在 ref 上可用。

## 4 (d) 封印 L13 孪生的充分条件（可执行验收）

把「能封印」定义成下面 7 条全绿；其中 1–4 是**能力**，5–7 是**可逆性与登记**。

| # | 验收项 | 判据（可执行） |
|---|---|---|
| 1 | 默认引擎已换 | 不带 `TYPORT_LSP_ENGINE` 启动，stderr 出现 `typort: lsp engine = Reference`（`lib.rs:4202`） |
| 2 | 默认构建不再编孪生 | `#![cfg(feature="l13-twin")]` 加到 `mod.rs:25`；`cargo build`（无 feature）通过；`grep -rn "bump_spine_iter" src/lib.rs` = **0**（今天 3 处：`361/1457/1568`） |
| 3 | 产品四件套等价 | 同一语料 ref↔twin 的 hover / inlayHint / definition / diagnostics 逐字节相同。本轮已建立口径：`examples/alu.typort` 实测 **4/4 相同**（§1.2）。建议固化成 `tests/l13_lsp_ref_surface.rs`——**今天 L13 没有 lsp_surface 测试**（只有 `tests/l06_lsp_surface.rs` … `l12_lsp_surface.rs`） |
| 4 | 预算语义已定 | 明确接管后超时=**诊断**（`2650-2660`）而非回落（`1602-1611`）；若不可接受，需先给 ref 补「超时后仍出观察面」的能力 |
| 5 | 门禁可逆 | 默认 `cargo test --test l13_fast_parity` = **0 测试且不红**（`tests/l13_fast_parity.rs:1` 已是 `#![cfg(feature="l13-twin")]`）；`--features l13-twin` 时仍全绿（`tools/gate_l13.ps1:220` 已带该 feature） |
| 6 | 读数不悬空 | `typort stats` 的 `twin_mem_stats` 字段在无 feature 时要么省略、要么置 null（`src/bin/cli.rs:846`）；`l13lspsample` 的 `probe_count` 不因缺孪生而链接失败（`mod.rs:28-30`） |
| 7 | 性能/内存重新登记 | 文档写死「单引擎口径」：ref 359ms/kick、~200MB；旧的 102ms/429MB 双引擎口径作废（`lib.rs:266-284` 需同步改写，否则下一位维护者会以为封印是纯损失） |

**判定**：今天的阻塞项只有 #2 与 #6 的**编译依赖**（`typeclass.rs:144-181`、`mod.rs:27-37`）；
`lib.rs` 的孪生面是「挂 cfg」的机械活。**#1 今天就能做**（`lsp_default` 一行），它会让产品立即落在 ref 上，
从而把 #3/#4 从「读码推断」变成「可回归」——**建议顺序：本节 #1 → #3（建测试）→ #2/#6 解耦 → §3-5 挂 cfg → #7 改文档**。
> 复现口径：`tmp/lsptest/`（`in.bin` 为 8 条消息的 framed 流；`out_reference.bin`/`out_twin.bin` 为原始 stdout；`err_*.txt` 含引擎自证行）。

## 5 章节有意增量 vs 顺手漂移（本轮核心判据）

判据不是代码量，而是**还有谁在读**：读侧只剩一个调用点 ⇒ 随手漂移；读侧是产品契约 ⇒ 有意增量。

| 项 | 分类 | 读侧（今天） | 处置 |
|---|---|---|---|
| 引擎路由的 6 个观察面访问器 + `ObserveSnapshot` 契约（`lib.rs:635-731`） | **L13 有意增量（E4）** | `hover_at/inlay_hint_at/completion_at/goto/references` | 保留。它正是把 ref 接进产品面的地基，删了要重写 |
| `Infer::lsp_collect` 默认 true（`mod.rs:2309`） | **L13 有意增量（与 L06/L07 相反）** | `surface.rs:109-121` | 保留；这是 ref 观察面开箱可用的原因 |
| `println` defer 两阶段（`2626`/`2760`） | **L13 有意增量（E2 vs twin）** | `tests/println_two_phase_tests.rs` | 保留；twin 是仿的 |
| `state_journal_record` 借孪生（`typeclass.rs:144-181`） | **顺手漂移（E2）** | 只有 ref `typeclass.rs` 与孪生自己 | 解耦为 ref 侧空实现（§3 #4） |
| `probe_count` 混孪生计数（`mod.rs:28-30`） | **顺手漂移（E2）** | `src/bin/l13lspsample.rs:60/70` | 拆两半（§3 #3） |
| `twin_mem_stats` 当 L13 公共出口（`mod.rs:32-37`） | **顺手漂移（E4→应删）** | `src/bin/cli.rs:846` | 挂 feature（§3 #3） |

> 匹配语义侧不需要复核：`pattern_match.rs` 与顶层 `syntax.rs` **自 L07 起六层逐字节相同**（[MAP](../compare-l07-l12-shared/MAP.md) §10 A.3），
> 本条全队只引一次，本册不重复论证。

## 结论摘要

参考版**已经能接管 LSP**：`TYPORT_LSP_ENGINE=reference` 不是残桩，本轮 stdio 实测 hover/inlayHint/definition/诊断四项与孪生逐字节相同，
且 ref 侧观察面总闸 `lsp_collect` 默认开、三张表读侧路由早已统一。缺口只有 3 类：`twin_mem_stats` 读数（仅 CLI 用）、
每 kick 缺失的 `force_memo_clear`（有 CAP 兜底）、以及**编译期**对孪生模块的两处耦合。
真正的拦路虎不是 LSP 能力而是**编译依赖**：`typeclass.rs` 调孪生 journal、`probe_count/twin_mem_stats` 从孪生 re-export。
迁移成本 ≈ 1 个函数 + 6~9 处 `#[cfg]`；代价是 CPU 3.5×，收益是内存省 2.2×。

## 要改的东西 Top-3

1. **`Engine::lsp_default()` 改指 Reference**（`src/lib.rs:297-302`，保留 `TYPORT_LSP_ENGINE=twin` 回退）——一行改动让产品立即跑在 ref 上，是 #3/#4 验收项可回归的前提；风险=每 kick 359ms（`lib.rs:268-270`）。
2. **解耦两处编译依赖**：`src/L13_namespace/typeclass.rs:144-181` 的 4 处 `super::bump_spine_iter::state_journal_record/StateUndo` 换成本模块空实现；`src/L13_namespace/mod.rs:27-37` 的 `probe_count`/`twin_mem_stats` 拆半并挂 `#[cfg(feature="l13-twin")]`——这是 `mod.rs:25` 挂 cfg 的**唯一硬阻塞**。
3. **建 `tests/l13_lsp_ref_surface.rs` + 给 `elaborate_reference` 补每 kick `force_memo_clear()`**（`src/lib.rs:2584` 入口；对齐 `on_change` 的 `lib.rs:1956`）——把 §1.2 的四项等价钉成断言，并堵住 ref 接管后唯一的内存卫生缺口。
