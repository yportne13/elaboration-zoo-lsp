# L07–L13 真实场景性能基准（2026-11-11）

> 目标：把 L07–L13 现有「k 翻倍的合成生成器负载」升级为**真实场景**性能基准，并在同一 HEAD 二进制上实测参考版（`run` / `bench_check_nf`）与孪生版（`bump_spine_iter`）的差距。
>
> - 工作分支：`bench/realistic-l07-l13`（基于 master `d0bd1bff`，**未改任何 L07–L13 引擎语义**）
> - 环境：Windows / release（opt-level 3）/ mimalloc；realbench 栈 512 MB，L13 bench 栈 1 GB
> - 口径：每配置 min-of-rounds（默认 5 轮），进程隔离；小负载由驱动自动放大 `repeat`
> - 原始日志：`target/bench_real/`（不入库）；语料来源：`tools/bench_corpus/L*/MANIFEST.md`
> - 复现：§6；产物清单：§7

## 0. TL;DR

1. **建成 6 层真实语料 + 1 个统一驱动**：L07–L12 共 **164 个程序 / 19,461 行 / 8,416 decls**（131 个从仓库测试/README 抽取 + 22 个手写项目级 + 18 个规模阶梯；全部通过语义闸门，0 SKIP），另有 L13 的仓库真实语料（prelude 35 文件、examples 32 文件）。
2. **真实语料上孪生全面领先**：L07–L12 整目录 `fast_ss/basic` = **0.002×–0.50×**；去掉 800-decl 阶梯（常规项目规模）后 = **0.082×–0.383×**（即孪生快 2.6–12×）。
3. **L09 参考版在「顶层 def 多」的真实文件上呈 O(D²)**：`ladder_large`（801 decls）参考版 **1,723 ms** vs 孪生 **0.83 ms**（≈2000×）。真实项目规模下参考版不可用，孪生是唯一可扩展路径。
4. **L12 的真实语料收益最小**（no-ladder：`fast_run/basic` 0.471×、`fast_ss/basic` 0.240×）——实例解析路径仍有优化空间。
5. **L13 真实负载**：`prelude-core` 0.45×、`prelude-hdl` 0.36×、`examples-hdl` 0.42–0.52×；**LSP 32 文件 sweep** twin/ref = **0.40×（快 2.50×）**；clean kick **6.9×**、error-state kick **无收益（0.98×）**；`typort check` 墙钟 **~5.0–5.1 s**（几乎全是 prelude 装载）。
6. **合成负载会误判收益**：同层同指标下，合成负载的 `fast_ss/basic` 与真实语料相差 2–4×（如 L10 struct 合成 0.06× vs 真实 0.27×；L09 universe 合成 0.33× vs 真实 0.082×）——验收必须用真实语料。

## 1. 背景与目标

L07–L13 的既有 bench（`src/bin/l07bench.rs` … `l13bench.rs` + 各层 `bump_spine_iter/bench_src.rs`）几乎全是合成生成器负载：church / strchain / global / match / enum / natadd / struct / universe / traitchain / macro / moduletree / gadt，按 k 翻倍放大。它们只覆盖单一语言特性、形态与真实代码差距大：

- 只有 L13 有真实负载（`prelude-core` / `prelude-hdl` / `examples-hdl`、`--file`）；L07–L12 的「真实用例」只存在于 blackbox 测试里，且单例太小、没有接成性能基准（`docs/optimal-design/L07-upgrade-bench-2026-11-09.md` §1 已明确记录，并建议抽 corpus + `--workload real`）。
- 前几轮性能优化（`docs/optimal-design/PERF-FINAL-2026-11-10.md`）的验收矩阵也以合成负载为主，真实负载只覆盖 L13。

本轮目标：为 L07–L13 构造更实用、更贴近真实场景的性能用例，并实测这几章的性能（参考版 vs 孪生版），产出可复现的套件与报告。

## 2. 方法

### 2.1 语料构成（L07–L12）

| 层 | PASS/SKIP | 文件构成 | 行数 | decls |
|---|---|---:|---:|
| L07 sum/依赖模式匹配 | 27 / 0 | 20 抽取 + 4 手写项目级 + 3 阶梯 | 2,462 | 1,384 |
| L08 product/struct | 26 / 0 | 20 抽取 + 3 手写项目级 + 3 阶梯 | 4,974 | 1,512 |
| L09 MLTT 宇宙 | 34 / 0 | 28 抽取 + 3 手写项目级 + 3 阶梯 | 2,508 | 1,444 |
| L10 typeclass | 22 / 0 | 14 抽取 + 3 抽取修补 + 2 手写项目级 + 3 阶梯 | 4,838 | 1,262 |
| L11 macro | 25 / 0 | 19 抽取 + 3 手写项目级 + 3 阶梯 | 2,629 | 1,476 |
| L12 canonical | 30 / 0 | 20 抽取 + 4 探针沉淀 + 3 手写项目级 + 3 阶梯 | 2,050 | 1,338 |
| **合计** | **164 / 0** | 131 抽取 + 22 手写 + 18 阶梯（按层去重后 164） | **19,461** | **8,416** |

三类语料：

1. **抽取**（`ex_*` / `extract_*`）：从 `tests/l0X_fast_parity.rs`、`tests/l0X_blackbox*.rs`、`src/L0X/tests.rs`、各层 README 代码块抽取 Typort 程序（原始候选池 662 个），经 §2.2 语义闸门过滤后保留。覆盖各层真实特性组合（GADT 索引、Eq 证明、struct 投影、trait 字典、宏展开、实例解析……）。
2. **手写项目级**（`proj_*` / `hw_*`，80–266 行）：真实领域程序而非合成微基准——表达式解释器、列表/向量库 + 归纳引理、等式推理库、栈式 VM、几何/传感器记录代数、跨宇宙容器库、AST 流水线、trait 家族/数值注册表、宏驱动代码生成、实例解析库等。
3. **规模阶梯**（`ladder_*`，同形态 50/200/800 decls 三档）：用于观察真实形态下的规模曲线（顶层 def 链、记录投影链、宏生成链、实例解析链）。

L13 直接使用仓库真实语料：`src/prelude/**`（35 个 `.typort`：core 6 + data 9 + hdl 19 + `show`）与 `examples/**`（32 个 `.typort`）。

### 2.2 语义闸门（计时前强制）

- **L07–L10**：参考版全流程 `run` 必须 Ok；参考版与孪生版 `bench_check_nf` 的 nf 节点数一致且非 0（互检防测到错误路径）。
- **L11/L12**：参考版 `run` 与孪生 `run_fast` 均 Ok 且输出逐字节一致；孪生 `bench_check_nf` 非 0。
- **L13**：`l13bench` 内置 nf parity（节点数 + pretty 内容逐字符，预算 20 万节点）。

所有进入计时的文件均通过闸门；`SKIP` 的文件不进入计时（最终 0 SKIP）。

### 2.3 计时口径

| 层 | `basic` | `fast_run` | `fast` | `fast_ss` |
|---|---|---|---|---|
| L07–L10 | 参考版 `bench_check_nf`（parse 在计时外） | — | 孪生 `bench_check_nf`（每轮新建 `Tycker`） | 孪生稳态（复用 `Tycker`） |
| L11/L12 | 参考版全流程 `run`（含 parse + pretty + `println` 输出） | 孪生全流程 `run_fast`（与 basic 同轴） | 孪生 `bench_check_nf`（parse 外，每轮新建） | 孪生稳态 |

- 每轮内各口径**交错执行**，奇偶轮交换执行顺序以抵消窗口漂移；每配置取 **min**（同时记录 median）。
- 进程隔离：L07–L12 每层一个 `realbench` 进程跑完整个目录（整目录时间 = 该层所有文件之和的 min-of-rounds）；L13 每个 workload/文件一个进程。
- 短语料稳定化：整目录 `basic` 合计 < 5 ms 时驱动自动放大 `repeat` 重跑（本轮 L07–L12 均 ≥ 10 ms，未触发）。

### 2.4 环境

- Windows；`master d0bd1bff` + 分支 `bench/realistic-l07-l13`；`cargo build --release`；mimalloc 全局分配器。
- `realbench` 工作线程栈 512 MB；`l13bench` 默认 1 GB（与 CLI worker 同步）。
- 测量窗口：2026-11-11 12:15–12:25（L13 真实负载/逐文件/LSP 除外）与 18:20–18:25（L07–L12 重跑、L13 CLI、LSP kick），同机安静窗口、串行执行。

## 3. 结果

### 3.1 L07–L12 真实语料整目录（min-of-5，单位 ms）

| 层 | PASS | 用例数 | basic | fast_run | fast | fast_ss | fast/basic | fast_ss/basic |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| L07 | 27/0 | 27 | 76.551 | — | 19.444 | 18.863 | 0.25× | 0.25× |
| L08 | 26/0 | 26 | 28.973 | — | 7.061 | 6.843 | 0.24× | 0.24× |
| L09 | 34/0 | 34 | 1792.452 | — | 3.908 | 3.444 | 0.002× | 0.002× |
| L10 | 22/0 | 22 | 16.987 | — | 3.473 | 3.180 | 0.20× | 0.19× |
| L11 | 25/0 | 25 | 19.144 | 9.626 | 4.390 | 4.251 | 0.23× | 0.22× |
| L12 | 30/0 | 30 | 39.771 | 21.139 | 19.301 | 19.737 | 0.49× | 0.50× |

注：L09 整目录被 `ladder_large` 单文件主导（1,723 ms / 1,792 ms ≈ 96%），见 §3.3；L11/L12 的 `basic` 含 parse+pretty+stdout，`fast_run` 才是同轴对照（比值分别为 0.503× / 0.532×）。

### 3.2 去掉 800-decl 阶梯（常规项目规模）

按每文件 min 求和（阶梯三档全部剔除）：

| 层 | basic (µs) | fast_run (µs) | fast (µs) | fast_ss (µs) | fast_ss/basic | fast_run/basic |
|---|---:|---:|---:|---:|---:|---:|
| L07 | 7,773 | — | 2,913 | 2,852 | 0.367× | — |
| L08 | 4,409 | — | 1,766 | 1,690 | 0.383× | — |
| L09 | 26,794 | — | 2,329 | 2,209 | 0.082× | — |
| L10 | 3,622 | — | 1,025 | 974 | 0.269× | — |
| L11 | 10,069 | 4,657 | 3,287 | 3,125 | 0.310× | 0.463× |
| L12 | 3,171 | 1,495 | 868 | 761 | 0.240× | 0.471× |

### 3.3 规模阶梯单文件（为什么 L09 被主导）

| 层 | 阶梯 large | decls | basic (ms) | fast (ms) | fast_ss (ms) | fast_ss/basic |
|---|---|---:|---:|---:|---:|---:|
| L07 | `ladder_l07_large` | 798 | 62.862 | 14.477 | 14.641 | 0.230× |
| L08 | `ladder_l08_large` | 805 | 22.547 | 4.566 | 4.501 | 0.203× |
| L09 | `ladder_large` | 801 | **1723.033** | 0.883 | 0.832 | **0.0005×** |
| L10 | `ladder_large` | 802 | 11.505 | 1.728 | 1.610 | 0.150× |
| L11 | `ladder_800` | 801 | 6.738 | 0.792 | 0.805 | 0.118× |
| L12 | `ladder_800` | 806 | 32.642 | 16.653 | 14.198 | 0.435× |

**解读**：L09 参考版每登记一个顶层 def 都要深拷 decl 表/上下文（O(D²)），在 800 decl 的真实项目规模上放大到 1.7 s；孪生为线性（0.83 ms）。L07/L08/L10 的阶梯也在 10–63 ms 量级，说明「顶层 def 数量」是真实项目里不可忽视的形态轴。

### 3.4 合成负载 vs 真实语料（同 HEAD 二进制）

合成锚点（取该文件最大 k 的一行，min）：

| 层 | 合成负载（k） | basic (ms) | fast_run (ms) | fast (ms) | fast_ss (ms) | fast_ss/basic |
|---|---|---:|---:|---:|---:|---:|
| L07 | match k=11 | 0.096 | — | 0.048 | 0.054 | 0.56× |
| L07 | enum k=9 | 0.172 | — | 0.071 | 0.072 | 0.42× |
| L08 | match k=11 | 0.095 | — | 0.051 | 0.053 | 0.56× |
| L08 | struct k=10 | 5.547 | — | 2.662 | 2.189 | 0.39× |
| L09 | match k=11 | 0.116 | — | 0.054 | 0.054 | 0.47× |
| L09 | universe k=10 | 2.456 | — | 0.827 | 0.804 | 0.33× |
| L10 | match k=11 | 0.095 | — | 0.056 | 0.054 | 0.57× |
| L10 | struct k=10 | 42.561 | — | 2.678 | 2.727 | 0.06× |
| L11 | macro k=10 | 40.472 | 6.000 | 2.504 | 3.014 | 0.07× |
| L11 | match k=11 | 0.180 | 0.097 | 0.046 | 0.049 | 0.27× |
| L12 | macro k=10 | 35.513 | 5.521 | 2.266 | 2.287 | 0.06× |
| L12 | match k=11 | 0.183 | 0.094 | 0.047 | 0.047 | 0.26× |

对照真实语料（§3.2 的 no-ladder 比值）：

| 层 | 合成 `fast_ss/basic`（代表负载） | 真实语料 `fast_ss/basic` | 差异 |
|---|---:|---:|---|
| L07 | 0.42–0.56×（enum/match） | 0.367× | 合成低估孪生收益 |
| L08 | 0.39×（struct） | 0.383× | 接近 |
| L09 | 0.33×（universe） | 0.082× | 合成低估 4× |
| L10 | 0.06×（struct） | 0.269× | 合成高估 4.5× |
| L11 | 0.07×（macro） | 0.310× | 合成高估 4.4× |
| L12 | 0.06×（macro） | 0.240× | 合成高估 4× |

**结论：合成负载与真实语料的倍率并不同向，同层可差 2–4×。** 只用合成负载会误判优化收益与回归风险；真实语料必须纳入验收。

### 3.5 L13 真实负载（min-of-rounds）

| 负载 | decls | basic (ms) | fast (ms) | fast_ss (ms) | fast/basic | fast_ss/basic |
|---|---:|---:|---:|---:|---:|---:|
| `prelude-core` | 208 | 45.772 | 24.509 | 20.408 | 0.54× | 0.45× |
| `prelude-hdl` | 1,439 | 4796.355 | 1775.241 | 1703.774 | 0.37× | 0.36× |
| `examples-hdl[0..5]` | 214–226 | 42.568–45.299 | 18.874–23.550 | 18.697–21.007 | 0.42–0.52× | 0.42–0.47× |

### 3.6 L13 逐文件 sweep（每文件独立进程，含 prelude）

**core 组**（`--with-prelude core`，rounds 2）：

| 文件 | decls | 判定 | basic (ms) | fast (ms) | fast_ss (ms) | fast/basic |
|---|---:|---|---:|---:|---:|---:|
| `examples/adder_proof.typort` | 233 | nf=26307 | 342.843 | 146.744 | 149.842 | 0.43× |
| `examples/theorem_proving.typort` | 248 | nf=42 | 54.858 | 24.651 | 25.199 | 0.45× |
| `examples/typeclass_complex.typort` | 279 | nf=48 | 49.864 | 22.992 | 22.726 | 0.46× |

**HDL 组**（`--with-prelude hdl`，rounds 1；本轮完成 4/8 文件，会话中断导致后 4 个未测——全量 32 文件见 §3.7 的 LSP sweep）：

| 文件 | decls | 判定 | basic (ms) | fast (ms) | fast_ss (ms) | fast/basic |
|---|---:|---|---:|---:|---:|---:|
| `examples/alu.typort` | 1373 | nf=1 | 4770.260 | 1784.556 | 1694.634 | 0.37× |
| `examples/hdl_ops.typort` | 1390 | nf=219 | 4999.720 | 1815.060 | 1729.029 | 0.36× |
| `examples/hdl/01-basics.typort` | 1374 | nf=219 | 4955.449 | 1838.328 | 1807.139 | 0.37× |
| `examples/hdl/09-hierarchy.typort` | 1375 | nf=1 | 4756.621 | 1739.252 | 1721.173 | 0.37× |

### 3.7 L13 LSP per-kick（`tests/twin_engine_bench.rs`，真实 HDL 文件）

| 场景 | 引擎 | min (ms/kick) | avg (ms/kick) |
|---|---|---:|---:|
| clean kick（`examples/hdl/09-hierarchy.typort`） | Reference | 625 | 666 |
| clean kick | Twin | **91** | **100** |
| error-state kick（同文件注入 `can't unify` 错误） | Reference | 654 | 680 |
| error-state kick | Twin | 641 | 708 |

- **clean kick：孪生 6.9×（min）**；**error-state kick：无收益（0.98×）**——错误态仍走参考版回退路径（与 `tests/twin_engine_bench.rs` 的既有记录一致）。
- 32 个真实文件（`examples/**`，逐文件 LSP per-kick，min-of-5）：**ref 合计 34,848 ms vs twin 13,957 ms，twin/ref = 0.40×（快 2.50×）**；单文件加速比 0.86×–12.54×（中位 ~5.3×）。
- **唯一孪生更慢的文件**：`examples/hdl/18-utils.typort`（ref 6,446.5 ms / twin 7,463.8 ms，0.86×）——值得后续单独归因（疑似宏/观察面形态）。
- 全表见附录 A。

### 3.8 L13 `typort check` CLI 墙钟（生产入口，含 prelude 装载）

| 文件 | 墙钟 (ms) | exit |
|---|---:|---:|
| `examples/alu.typort` | 5137.7 | 0 |
| `examples/adder_proof.typort` | 5119.9 | 0 |
| `examples/typeclass_complex.typort` | 4964.1 | 0 |

三个文件墙钟几乎相同（~5.0–5.1 s），与 `docs/optimal-design/D4-experiments.md` §5 的 EXP-6 记录一致：**时间几乎全是 prelude 装载**，源文件 elaborate 占比很小。这是生产路径的首要优化目标。

## 4. 结论

1. **孪生在真实语料上全面领先，且优势随「真实形态」放大或收窄**：常规规模（no-ladder）L07–L12 的 `fast_ss/basic` 为 0.082×–0.383×；`fast_run/basic`（全流程同轴）L11/L12 为 0.46–0.47×。
2. **L09 参考版的 O(D²) 顶层 def 行为在真实项目规模下不可接受**（801 decls → 1.72 s vs 0.83 ms）。任何「真实项目 = 几百个顶层声明」的场景都必须走孪生路径。
3. **L12 是真实语料收益最小的层**（no-ladder `fast_run/basic` 0.471×、`fast_ss/basic` 0.240×；ladder 0.435×）——实例解析/trait 合成路径的孪生优势远小于其它层，仍有优化空间。
4. **L13 生产路径**：真实 prelude/示例负载孪生快 2.2–2.8×；LSP 逐文件快 2.50×；clean kick 6.9×；但 error-state kick 无收益、`18-utils` 单文件孪生反而慢 0.86×、CLI 墙钟 ~5 s 全在 prelude 装载——这三处是下一轮最值得投入的方向。
5. **验收口径必须双轨**：合成负载的 `fast_ss/basic` 与真实语料可差 2–4×（L10 struct 0.06× vs 真实 0.27×；L09 universe 0.33× vs 真实 0.082×）。建议把本报告的 no-ladder 真实语料指标纳入每轮性能验收。
6. **真实语料暴露的新形态轴**：顶层 def 数量（ladder）、prelude/HDL 宏展开与实例化（prelude-hdl）、LSP 观察面（kick/sweep）、错误恢复回退（error-state kick）、CLI 冷启动（prelude 装载）。

## 5. 局限

1. **阶梯主导**：L09 整目录 96% 时间来自 `ladder_large`；正文同时给出 no-ladder 口径，避免单文件主导掩盖其它形态。
2. **L11/L12 的 `basic` 含 stdout**：`run` 会执行 `println` 声明并写 stdout，绝对耗时对 harness 敏感（同一语料在 Windows PowerShell 5.1 的 `Tee-Object` 管道下 L11 basic 曾测得 64.9 ms，pwsh 下为 19.1 ms）——**只使用同轴比值**（`fast_run/basic`），不跨 harness 比绝对值。
3. **L13 HDL 逐文件 sweep 只有 4/8**（会话中断，后 4 个文件未测）；全量 32 文件由 §3.7 的 LSP 逐文件 sweep 覆盖，两者口径不同（LSP 路径含观察面）。
4. **L12 语料是「可 PASS 子集」**：孪生存在已知分叉族（blanket impl `impl[T] X for T`、具体值点号分发、List/Vec fold-to-Nat、struct 接收者实例等），这些形态在 realbench 会 SKIP，语料已收敛；因此 L12 的 trait 覆盖有缺口（多实例/泛型约束/默认方法/多约束都在，但不含上述分叉形态）。
5. **L10 语言面限制**：无 supertrait、无 trait 默认方法体、无实例依赖；「superclass/默认方法」用显式字典参数的库函数模拟。
6. **单机单窗口**：小负载 ±5–10% 噪声；L09 阶梯参考版方差较大（1.72–1.73 s）；L13 prelude-hdl 与 LSP sweep 的绝对值受机器负载影响，比较时优先看比值。
7. **合成锚点仅取代表负载**（match/struct/universe/macro 等，k=10/11），不是全矩阵重跑；与 `docs/bench-matrix-2026-09-20.md` 的历史数据不可直接逐格对齐。

## 6. 复现

```powershell
# 0) 构建（HEAD 源码）
cargo build --release --bin realbench --bin l13bench --bin typort

# 1) 语料语义闸门（应输出 pass=164 / skip=0）
pwsh -File tools/run_realistic_bench.ps1 -ValidateOnly

# 2) L07–L12 真实语料（整目录，rounds=5，自动 repeat）
pwsh -File tools/run_realistic_bench.ps1 -Rounds 5

# 3) 合成锚点（同 HEAD 二进制对照）
pwsh -File tools/run_synthetic_anchor.ps1 -Rounds 2

# 4) L13 真实负载 + 逐文件 + CLI 墙钟
pwsh -File tools/run_l13_real.ps1

# 5) L13 LSP per-kick / 32 文件 sweep（约 5.5 分钟）
cargo test --release --test twin_engine_bench --no-run
# 产物在 target\release\deps\twin_engine_bench-*.exe，跑：
#   <exe> --ignored --nocapture > target\bench_real\lsp_kick.txt

# 6) 汇总为 Markdown 表
python tools\bench_real_report.py --out-dir target\bench_real   # -> target\bench_real\summary.md
```

日志统一为 UTF-8（脚本显式写 UTF-8；`bench_real_report.py` 同时兼容旧日志的 UTF-16 BOM）。

## 7. 产物

| 文件 | 说明 |
|---|---|
| `src/bin/realbench.rs` + `Cargo.toml`（`[[bin]] realbench`） | 统一真实语料驱动：L07–L12、`--layer/--corpus/--rounds/--repeat/--only/--validate`，语义闸门 + 轮级交错计时 + CSV 输出 |
| `tools/bench_corpus/L07…L12/` | 164 个 `.typort`（每层 22–34 个）+ `MANIFEST.md`（来源/特性/行数/decls/档位） |
| `tools/bench_corpus/extract_tests.py` | 从仓库测试/README 抽取候选池（`tools/bench_corpus/raw/`，可再生成，不入库） |
| `tools/run_realistic_bench.ps1` | L07–L12 一键测量/验证（自动 repeat、UTF-8 日志） |
| `tools/run_l13_real.ps1` | L13 真实负载/逐文件/CLI 一键测量 |
| `tools/run_synthetic_anchor.ps1` | 合成锚点（同 HEAD 二进制） |
| `tools/bench_real_report.py` | 日志 → Markdown 汇总表 |
| `docs/bench-realistic-l07l13-2026-11-11.md` | 本报告 |

原始日志：`target/bench_real/`（`realbench_L*.txt`、`synthetic_*.txt`、`l13_*.txt`、`lsp_kick.txt`、`summary.md`），按仓库惯例不入库。

## 附录 A：L13 LSP 逐文件 sweep 全表（32 个真实文件，稳态 min，按加速比升序）

| 文件 | ref min (ms) | twin min (ms) | 加速比 |
|---|---:|---:|---:|
| `examples/hdl/18-utils.typort` | 6446.5 | 7463.8 | 0.86× |
| `examples/theorem_proving.typort` | 55.9 | 21.8 | 2.57× |
| `examples/hdl/24-verilog-practice.typort` | 3493.6 | 1211.1 | 2.88× |
| `examples/hdl/11-bundle-deep.typort` | 1820.9 | 581.8 | 3.13× |
| `examples/adder_proof.typort` | 782.9 | 237.1 | 3.30× |
| `examples/hdl/10-bundle.typort` | 1542.4 | 462.7 | 3.33× |
| `examples/hdl/25-verilog-reset.typort` | 1122.6 | 320.7 | 3.50× |
| `examples/hdl/23-verilog-compat.typort` | 772.6 | 213.5 | 3.62× |
| `examples/hdl/08-control-flow.typort` | 724.3 | 165.5 | 4.38× |
| `examples/hdl/21-crossclock.typort` | 1242.1 | 283.6 | 4.38× |
| `examples/hdl/07-registers.typort` | 581.8 | 125.9 | 4.62× |
| `examples/hdl/26-assert.typort` | 166.7 | 35.3 | 4.72× |
| `examples/hdl/20-misc.typort` | 4938.7 | 1015.0 | 4.87× |
| `examples/hdl/15-inout.typort` | 215.5 | 43.4 | 4.96× |
| `examples/hdl/09-hierarchy.typort` | 519.2 | 101.0 | 5.14× |
| `examples/hdl/17-output-reg.typort` | 262.9 | 50.1 | 5.24× |
| `examples/hdl/22-widthadapter.typort` | 496.5 | 93.8 | 5.30× |
| `examples/hdl/27-blackbox.typort` | 621.5 | 117.3 | 5.30× |
| `examples/alu.typort` | 96.0 | 17.9 | 5.38× |
| `examples/hdl/16-counter.typort` | 221.4 | 40.2 | 5.50× |
| `examples/hdl/02-arithmetic.typort` | 456.0 | 82.6 | 5.52× |
| `examples/hdl_ops.typort` | 952.9 | 171.6 | 5.55× |
| `examples/hdl/04-compare.typort` | 379.6 | 67.7 | 5.60× |
| `examples/hdl/01-basics.typort` | 488.5 | 85.3 | 5.72× |
| `examples/hdl/13-adder-tree.typort` | 425.7 | 72.5 | 5.87× |
| `examples/hdl/06-select-cat.typort` | 427.0 | 72.0 | 5.93× |
| `examples/hdl/19-stream.typort` | 2821.4 | 465.2 | 6.06× |
| `examples/hdl/14-arithmetic-extra.typort` | 680.6 | 107.9 | 6.31× |
| `examples/hdl/05-bool.typort` | 326.6 | 51.7 | 6.32× |
| `examples/hdl/03-bitwise.typort` | 507.3 | 72.0 | 7.05× |
| `examples/typeclass_complex.typort` | 101.2 | 14.2 | 7.12× |
| `examples/hdl/12-memory.typort` | 1157.3 | 92.3 | 12.54× |
| **TOTAL** | **34,848** | **13,957** | **2.50×** |
