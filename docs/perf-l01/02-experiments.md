# 02 · L01 定向优化实验（task-4 / exp-ab）

**结论先行**（已按 §9 复核勘误）：在影子副本上回移 L02 的两条热路径机制
（`W::ApplyKnown` + `ChainWrap(0)` 消除）**机制本身有效**（在岔路密集的合成
负载上 −29%…−38%），但在 L01 现有负载上**没有可复现的收益**：
`church_pair`/`dup`/`church_mul` 的机制触发次数太少、可证明收益 <0.05%；
`parigot_add n=10` 批 1 曾测得 −6.59%，但被 task-5 独立复核否定（−0.58%，
该批地板 17.90%）→ **未复现（未判定）**；`exponential` 则**根本不走 β 岔路**
（`fork_h0 = 0`）。
一次性口径分配轴上，`spine` 预保留 4096→16384 在 `church_pair(8000)` 上
拿到 −10.3%（批 1，同批空对照 p95 = 0.61%，`_ss` 对照 0.00%），
**已由 task-5 独立复现（−10.37%）**。
`ChainRun` 判据外提无效果。**主仓库 `src/**` 零改动。**

本文件所有数字的原始 stdout 在 `docs/perf-l01/raw/exp-*/`；补丁、影子树构建
脚本与 A/B 驱动在 `/tmp/l01-exp/`（工作区外，见 §8）。

---

## 1. 方法与判定阈值

### 1.1 计时协议

| 项 | 取值 |
|---|---|
| 保频 | keepalive = `chrt -i 0 taskset -c 7 sh -c 'while :; do :; done'`（与 `tools/perf-l01/run_bench.sh` 同款），整批不撤 |
| 绑核 | `taskset -c 7`（cpu7 = 2995200 kHz 最大核） |
| 指标 | **`med_of_min`**：每 rep 进程内 min（`--rounds` 轮）→ 每侧 N 个 rep 的**中位数** |
| reps/侧 | **N = 25**（≥21，见 §1.2） |
| 交错 | 同一锁窗内 A B A B …（`ab.py`；`run_bench.sh` 无法表达同批交错，故驱动自写，但**锁 / stale 自愈 / 保频 / taskset / L01_STACK_MB 全部照抄**） |
| 独占 | `docs/perf-l01/.benchlock`（mkdir 取、删 pid + rmdir 放、死 pid 接管），编译影子副本也在锁内 |
| 空对照 | 同批 A 侧 25 个 rep 随机半分组（4000 次重采样）→ \|中位数比 − 1\| 的 **p95** |
| 判定 | 只有 \|ratio−1\| > max(5%, 同批空对照 p95) 才判 WIN/LOSS，否则 UNDECIDED |

`ab.py` 的判定行同时给出 `med_A/med_B/ratio/min_A/min_B/空对照p95/paired p10..p90`。

### 1.2 判定阈值（引用 `00-baseline.md` §3.3）

- `< 5%`：本机不可判定（即使 21 reps/侧）。
- `5–20%`：需 ≥21 reps/侧 **且** 同批内插对照；本报告用同批空对照 p95 作为该批地板。
- `≥ 20%`：单次 7v7 可判定；`≥ 25%` 无条件可信。
- **重负载例外**：单计时段 ≳1 ms 的变体单 rep CV 可 <1%——但这只说明
  "单 rep 离散可能小"，**不保证空对照地板小**（见下）。

**空对照地板必须每批实测，不能由负载特征先验推断**：同一个
`parigot_add n=10`（单 rep min ≈ 146 ms，远超上面的 1 ms 线），三个独立批次的
空对照 p95 分别是 **0.23%（本报告批 1）/ 22.17%（批 2）/ 17.90%（task-5 复核批）**
——**2/3 批 ≥18%**。task-5 那批 25 个循环耗时 646 s，cpu7 `scaling_cur_freq`
中途掉到 1.40 GHz、4 个档位混合，说明档位漂移 / 共机负载会整批抬高地板。
所以批 1 的 0.23% 是**批次运气**，不是该负载的属性；"某负载噪声天然很小"的
先验推断被这三批数据否定。**判定只能引用该批自己的空对照 p95**（§9-A）。

### 1.3 正确性门

每个改动先 `cargo test --release --bin l01bench`：**79 passed / 0 failed**
（exp1、exp2a、exp2b、exp3a、诊断变体各自都过）。A/B 的每个 rep 都要求
`rc=0`——它同时覆盖 bench 内部的结果断言（`assert_eq!` 与基线期望）。
**任何 fail 会立刻中断该批**（`ab.py` 遇非零 rc 即 raise），本报告无此情况。

---

## 2. 对照实验：跨树/跨次构建的混杂（A vs A′）

- **A** = 主树 `target/release/l01bench`（sha256 `503ff7c9…`，2026-10-06 07:25 构建，
  与提交 `071d90c` 同源）。
- **A′** = 影子副本 `/tmp/l01-exp` 里**同源未改动**重建（独立
  `CARGO_TARGET_DIR=/tmp/l01-exp/target`，同一 toolchain 1.98.1，release = LTO +
  codegen-units=1 + mimalloc），sha256 `0cd33fc2…`。
- **A vs A 自身拷贝**（字节相同）作为纯 harness 地板。

| 批次 | 配置 | church 1000/2000/4000/8000 的 min 比 A′/A |
|---|---|---|
| `exp-ctrl2-church` | N=15, rounds=50 | 1.0000 / 1.0000 / 1.0000 / 1.0000 |
| `exp-ctrl3-church` | N=21, rounds=50 | 1.0000 / 1.0000 / 1.0000 / 1.0077 |
| `exp-ctrl-self-church` | N=21, rounds=50（同字节拷贝） | 1.0000 / 1.0000 / 1.0000 / 0.9924 |
| `exp-ctrl4-church` | N=21, rounds=200 | 1.0000 / 1.0000 / 1.0000 / 1.0000 |
| `exp-ctrl3-dup` | N=21, rounds=50 | dup_pair 1.0000/1.0000/1.0000/1.0226；dup_deep 1.0000/0.9921/0.9962/1.0296 |

**结论**：rounds=200 时跨树重建的 min 比恒为 1.0000；rounds=50 时最坏
2.96–3.23%，且方向两侧都出现（无系统性偏差）。**影子副本重建与主树二进制
无可测差异，"跨树构建差异"这一混杂被排除**——后续 A′ vs B 是干净对照。
（该组对照跑在加保频之前的驱动上，用 min 口径；正式判定一律用各批自带的
保频 + 中位数 + 空对照 p95。）

---

## 3. 实验 1：回移 `W::ApplyKnown` + `ChainWrap(0)` 消除

### 3.1 补丁摘要（影子树内文件:行）

`patches/exp1_applyknown_chainwrap0.patch`，改 1 文件 +24/−6：

| 位置（`/tmp/l01-exp/src/L01_nbe/bump_spine_iter.rs`） | 改动 |
|---|---|
| :41 | `W::ApplyKnown(V)` 新变体（对齐 L02 :211） |
| :83-85 | `base` 到达且 `heads == 0` → 不再压 `ChainWrap(0)`（对齐 L02 :260-262） |
| :94-100 | β 岔路：`heads == 0` 不压 `ChainWrap`；改压 `ApplyKnown(vf)` + `Tm(a)`（对齐 L02 :273-276） |
| :109-111 | 复合函数头：`heads == 0` 不压 `ChainWrap(0)`（对齐 L02 :286-288） |
| :123-128 | `ApplyKnown` 执行臂：弹实参、直接 `v_clo_of` + 建 `EnvCons`（对齐 L02 :309-314） |

语义：右链下钻遇到闭包头时函数值已在手上，省掉
`push(ChainWrap(0)) + push(Apply) + push(Tm(f))` 及其 3 次 pop / 1 次
`nth` 环境查找 / 1 次 `v_tag` 分发。`W` 枚举大小不变（`Tm` 载荷 16B，
`ApplyKnown(V)` 载荷 8B，仍是 24B）。

### 3.2 证据 A：机制级动态计数（确定性，非计时）

诊断变体 `D2_diag`（baseline + `diag_counters.patch` + `diag_hooks.patch`）在各
热路径挂 `AtomicU64`，`dump(tag)` 打印后清零，故 `--rounds 2` 减 `--rounds 1`
= **恰好一次 normalize 的计数**。表 = `raw/exp-diag/percase.tsv`（每 normalize）：

| 负载 case | fork_h0 | fork_hn | composite_h0 | base_hn | apply | steps | removed_steps | removed%steps |
|---|---|---|---|---|---|---|---|---|
| church_pair(1000…8000) | **2** | 0 | 4 | 2 | 6 | **37** | 8 | 21.6% |
| dup_pair(1000…8000) | 4 | 0 | 10 | 5 | 14 | 85 | 18 | 21.2% |
| dup_deep(1000…8000) | 8 | 0 | 19 | 11 | 27 | 166 | 35 | 21.1% |
| church_mul 50/100/200 | 52/102/202 | 0 | 3 | ≈n | ≈n+5 | 300/700/1428 | 107/207/407 | 28.3/28.4/28.5% |
| parigot_add 4/6/8/10 | 264/4108/65552/**1048596** | 0 | 533/8223/131113/2097203 | ≈fork | 797/12331/196665/3145799 | 4753/73943/1.18e6/1.89e7 | 1061/16439/262217/4194395 | 22.3/22.2/22.2/22.2% |
| exponential 10/14/18/20 | **0** | 0 | 10/14/18/20 | 同左 | 同左 | 72/100/128/142 | 10/14/18/20 | 13.9/14.0/14.1/14.1% |
| synth clo_chain k=1e3/1e4/1e5 | k | 0 | 1 | 0 | ≈k+1 | ≈5k+7 | 2k+1 | 40.0% |

`removed_steps = 2·fork_h0 + fork_hn + base_h0 + composite_h0` 是回移能删掉的
eval 主循环迭代数（逐事件核对：fork_h0 省 2、fork_hn/composite_h0/base_h0 各省 1）。

**关键读数**
1. `church_pair`：**`fork_h0 = 2`、`steps = 37`，两者都与 n 无关**——β 岔路是
   常数条，而工作量（`wrap_heads = 2n` 次 spine push、quote 建 2n 节点）随 n 线性。
2. `exponential`：**`fork_h0 = 0`，ApplyKnown 一次都不执行**；只有
   10–20 次 `ChainWrap(0)` 消除。这是"机制不适用"，与"测不出来"性质不同。
3. `parigot_add`：岔路随 n 指数增长（n=10 时 1.05e6 次/normalize），是唯一
   岔路能占显著时间份额的现成负载。
4. `synth clo_chain(k)`：`fork_h0 = k`、删掉 40% 的主循环迭代，是收益上限轴
   （hotpath-audit 设计的形状，本报告新增 `--workload synth` 于影子树）。

### 3.3 证据 B：墙钟 A/B（A′ vs B=exp1）

A′ = `A_syn`（同源 + 仅 synth 开关），B = `B_syn`（exp1 + synth），
N=25/侧，A B A B 交错，保频。原始 `raw/exp-exp1-*/summary.tsv`。

| 负载 case | med_A (ms) | med_B (ms) | ratio | 同批空对照 p95 | 判定 |
|---|---|---|---|---|---|
| synth k=1000 | 0.0170 | 0.0120 | **−29.4%** | 0.00% | **WIN** |
| synth k=10000 | 0.1910 | 0.1250 | **−34.6%** | 0.52% | **WIN** |
| synth k=100000 | 2.0470 | 1.2730 | **−37.8%** | 1.07% | **WIN** |
| church_pair 1000 | 0.0180 | 0.0180 | 0.00% | 0.00% | UNDECIDED |
| church_pair 2000 | 0.0360 | 0.0370 | +2.78% | 2.78% | UNDECIDED |
| church_pair 4000 | 0.0770 | 0.0770 | 0.00% | 0.00% | UNDECIDED |
| church_pair 8000 | 0.1640 | 0.1650 | +0.61% | 0.61% | UNDECIDED |
| dup_pair 1000/2000/4000/8000 | 0.036/0.077/0.161/0.334 | 同 | 0.00/0.00/0.00/−0.30% | ≤0.60% | 全 UNDECIDED |
| dup_deep 1000/2000/4000/8000 | 0.075/0.152/0.329/0.675 | 同 | 0.00/+0.66/0.00/+0.15% | ≤0.91% | 全 UNDECIDED |
| church_mul 50/100/200 | 0.022/0.095/0.386 | 0.022/0.096/0.388 | 0.00/+1.05/+0.52% | ≤0.52% | 全 UNDECIDED |
| exponential 10 | 0.0140 | 0.0130 | −7.14% | 3.70% | UNDECIDED（1 µs = 量化一格，不认） |
| exponential 14/18/20 | 0.202/3.528/14.276 | 0.202/3.534/14.310 | 0.00/+0.17/+0.24% | ≤0.55% | 全 UNDECIDED |
| parigot_add 4 | 0.0350 | 0.0300 | −14.29% | 9.38% | UNDECIDED（绝对量 5 µs） |
| parigot_add 6 | 0.5550 | 0.4630 | −16.58% | 10.76% | UNDECIDED（批空对照太宽） |
| parigot_add 8 | 9.1480 | 8.4960 | −7.13% | 10.23% | UNDECIDED |
| parigot_add 10 | 146.670 | 137.003 | −6.59% | 0.23% | 批 1 曾判 WIN，**复核后改判"未复现（未判定）"**（§9-A） |

批 2（`raw/exp-exp1-guest-confirm/summary.tsv`，机器变吵，空对照 p95 15–30%）：
parigot_add 10 点估计 **−7.27%**（同向，但该批判 UNDECIDED）；
parigot_add 8 −3.62%；church_mul 全 +1.35…+5.00%（UNDECIDED）；
exponential 全 UNDECIDED。
**`parigot_add n=10` 最终判"未复现（未判定）"**：批 1 −6.59%（地板 0.23%）与
批 2 −7.27%（地板 22.17%）点估计同向，但 task-5 独立复核批测得 **−0.58%**
（地板 **17.90%**），三批地板 0.23/22.17/17.90% ⇒ 预注册指标 `med_of_min`
在 2/3 批次里分辨不出 7% 的效应，按规则**不判收益**（§9-A）。
n=8 两批只到 −7.1%/−3.6% 且都未判定，同样不判收益。

### 3.4 判定与机制解释

**（1）机制有效，但只在岔路密集时有量级**：synth 把 40% 的主循环迭代变成
可删除，实测 −29%…−38%。用 synth 标定"每个被删迭代 ≈ 2.5–3.9 ns"
（k=1e3/1e4/1e5 分别 `(med_A−med_B)/(2k+1)`）：
- church_pair(8000)：8 × ~3.5 ns ≈ **28 ns** / med 164 µs → **<0.02%**；
- dup_deep(8000)：35 × 3.5 ns ≈ 0.12 µs / 675 µs → **<0.02%**；
- church_mul(200)：407 × 3.5 ns ≈ 1.4 µs / 388 µs → **≈0.4%**；
- exponential(18)：18 × 3.5 ns ≈ 0.06 µs / 3534 µs → **≈0.002%**（且 fork_h0=0）；
- parigot_add(10)：4.19e6 × 3.5 ns ≈ 14.7 ms / 146.7 ms → **机制算术上界 ≈10%**；
  批 1 点估计 6.6% 未被复现（§9-A），故只作"机制量级"证据。

**因此 `church_pair` 上"可证明无收益"，不是"测不出来"**：`fork_h0 = 2`、
`steps = 37` 与 n 无关，机制级上界 <0.05%，任何 <5% 的墙钟判读都只会是噪声。
`dup`/`church_mul` 同理（上界 <0.4%）。这与墙钟"全部 UNDECIDED"完全自洽。

**（2）`exponential` 是"机制从不执行"**：`fork_h0 = 0`（n=10/14/18/20 全为 0），
`ApplyKnown` 在该负载上一次都不落；只有 `ChainWrap(0)` 消除能命中
10–20 次/normalize，量级 <0.01%。**不是"没有测出收益"，而是"该机制在此形状上
不适用"**。

**（3）`parigot_add` 是唯一机制量级足够大的现成负载，但收益未复现**：n=10 每
normalize 有 1.05e6 次 fork_h0（占 22.2% 主循环迭代），机制算术给出 ~10% 上界；
批 1 点估计 −6.6%（地板 0.23%）、批 2 −7.3%（地板 22.17%），但 task-5 独立复核批
仅 **−0.58%（地板 17.90%）** ⇒ 预注册指标下**未复现，判未判定**（§9-A）。
task-5 另有一个**明确标注"不作数、不升级判定"的线索**：按 governor 档位对齐后，
同一档内 B/A 两档都 ≈0.93（171/159 ms、146.7/137 ms），A_copy/A 同档内 ≈1.000
——效应可能存在，但 `med_of_min` 这个预注册指标在该批抓不到；要验证需改用
"档位对齐"的预注册协议，本报告不据此改判。

**（4）语义**：79 测试全过；A/B 全程 bench 断言通过；patch 与 L02 同构
（L02 `src/L02_tyck/bump_spine_iter.rs` :211/:260-262/:273-276/:286-288/:309-314）。

---

## 4. 实验 2：一次性口径的分配轴

一次性口径 `normalize_imported` 每轮新建 `Spine { Vec::with_capacity(4096) }`
（`Entry` 24B → 96 KB）+ 两个 `Vec::new()` 的 vals（eval 一个、quote 一个）；
n=8000 时 spine ~16000 条 → 增长 4096→8192→16384（两次 realloc + 两次
memcpy）。稳态 `_ss` 走 `Machine::normalize`，不受影响，用作**同批对照**。

### 4.1 2a：vals 预保留 + eval/quote 复用同一个 vals
`patches/exp2a_vals_preserve.patch`（影子树 `bump_spine_iter.rs:357-365`）：
`let mut vals: Vec<V> = Vec::with_capacity(4096)` 并同时传给 `eval_iter`/`quote_iter`
（两者入口都 `clear`），省掉第二次分配与两处增长。

| case | med_A | med_B | ratio | 空对照 p95 | 判定 |
|---|---|---|---|---|---|
| church_pair 1000/2000 | 0.018/0.036 | 0.018/0.035 | 0.00/−2.78% | ≤11.1% | UNDECIDED |
| church_pair 4000 | 0.0800 | 0.0760 | −5.00%（刚好压阈值 5.00%） | 4.35% | **未判定（边缘）** |
| church_pair 8000 | 0.1640 | 0.1610 | −1.83% | 0.92% | UNDECIDED |
| `bump_spine_iter_ss`（对照） | 0.017/0.034/0.070/0.138 | 同 | 0.00/0.00/0.00/**+0.72%** | ≤5.9% | 未判定（=无变化；8000 的 +0.72% 见 §9-B） |

**判定：无可靠收益（边缘）**。`_ss` 对照 1000/2000/4000 为 0.00%、8000 为
+0.72%（远小于该批地板），确认它只影响一次性口径；4000 的 −5.00% 正好等于
阈值（raw 的浮点判定显示 WIN，本报告保守读作"未判定（边缘）"）、8000 只有
−1.83%，按标准不判 WIN。

### 4.2 2b：spine 预保留 4096 → 16384
`patches/exp2b_spine_16384.patch`（影子树 `bump_spine_iter.rs:354`）。

**批 1 `raw/exp-exp2b-church/summary.tsv`**（空对照 p95 ≤3.09%）：

| case | med_A | med_B | ratio | 空对照 p95 | 判定 |
|---|---|---|---|---|---|
| church_pair 1000 | 0.0180 | 0.0180 | 0.00% | 5.88% | UNDECIDED |
| church_pair 2000 | 0.0360 | 0.0360 | 0.00% | 2.78% | UNDECIDED |
| church_pair 4000 | 0.0810 | 0.0750 | **−7.41%** | 3.09% | **WIN** |
| church_pair 8000 | 0.1650 | 0.1480 | **−10.30%** | 0.61% | **WIN** |
| `bump_spine_iter_ss` 1000/2000/4000/8000 | 0.018/0.035/0.070/0.139 | 同 | 0.00/−2.86/0.00/−0.72% | ≤2.94% | 未判定（=无变化） |

**批 2 `raw/exp-exp2b-church-confirm/summary.tsv`**（机器变吵，空对照 p95
15.6–21.0%）：4000 −5.19% / 8000 +2.80%，全部 UNDECIDED —— 该批地板太宽，
不构成反证。

**判定：收益 ~7–10%（中高置信度）**。批 1 两个大 n 规模同向、随 n 增大
（n=4000 一次 realloc，n=8000 两次），同批 `_ss` 对照 0.00%/−0.72% 证明
变化只落在一次性口径；批 2 因该批噪声未判定。绝对量与基线矩阵自洽：
`00-baseline.md` §4.1 给出 n=8000 稳态 `_ss` 0.140 vs 一次性 `bump_spine_iter`
0.159（差 ~14%），2b 把一次性侧压到 ~0.148，收掉了其中约 7 个百分点。
未见 mimalloc 大对象（384 KB）反噬——若有，方向会是 LOSS。

**已由 task-5 独立复现（verify 自写 3 臂轮转 A/B/A_copy，N=25/臂，锁内 cpu7 保频）**：
church_pair 4000 = **−7.50%**、8000 = **−10.37%**，该批空对照 p95 = 1.25%/0.61%，
A vs A_copy 同字节臂 0.00%，`_ss` 对照全 0.00% —— 与本报告批 1 的
−7.41%/−10.30% 几乎重合。**这条因此从"单批干净 WIN"升级为"跨批、跨实现独立复现"。**

---

## 5. 实验 3：`ChainRun` 判据外提

`patches/exp3a_chainrun_hoist.patch`（影子树 `bump_spine_iter.rs:256` 起）：
把 `match idx_node { Some(n) if fi.0 == f0.0 => …, _ => … }` 拆成
`if let Some(n) = idx_node { loop { if fi.0 == f0.0 … } } else { loop { … } }`
两个循环变体，使同构链头路径不再每轮判 `idx_node`。

| case | med_A | med_B | ratio | 空对照 p95 | 判定 |
|---|---|---|---|---|---|
| church_pair 1000/2000/4000/8000 | 0.018/0.036/0.077/0.165 | 完全相同 | 0.00% | 4.43–5.88% | 全 UNDECIDED |

**判定：零效果**（79 测试通过）。机制解释：`idx_node` 是循环不变量，LLVM 在
O3 下本就会 unswitch/hoist；且 `ChainRun` 内层循环耗时主要在
`bump.alloc(Bt::App(..))`，一个已被正确预测的分支无关紧要。按 Lead 指示，
本轴不再深入。

---

## 6. 汇总表

| # | 假设 | 补丁（影子树文件:行） | 最干净结果 | 判定 | 置信度 |
|---|---|---|---|---|---|
| 1 | L02 `ApplyKnown`+`ChainWrap(0)` 回移能提速 | `bump_spine_iter.rs:41,83,94,109,123` | synth −29…−38%（WIN）；parigot_add10 −6.59%（p95 0.23%）/ −7.27%（批2）/ **task-5 −0.58%（p95 17.90%）** | **机制有效**；**现成负载无可复现收益**：church/dup/church_mul 可证明 <0.05%，parigot_add10 **未复现（未判定）**，exponential 机制不适用 | 高（synth 上限）/ 证明级（church 上界）/ parigot 未复现 |
| 2a | 一次性 vals 预保留+复用 | `bump_spine_iter.rs:357-365` | 4000 −5.00%（压线）、8000 −1.83%，`_ss` 0.00/0.00/0.00/+0.72% | **未判定（边缘）** | 低 |
| 2b | 一次性 spine 预保留 16384 | `bump_spine_iter.rs:354` | 4000 −7.41%、8000 −10.30%（批1，空对照 ≤3.09%）；**task-5 独立复现 −7.50%/−10.37%** | **WIN ~7–10%** | 高（跨批 + 跨实现独立复现） |
| 3 | `ChainRun` 判据外提 | `bump_spine_iter.rs:256` | 全 0.00% | **零效果** | 中（4 规模一致） |
| 对照 | 跨树重建无偏 | — | min 比 1.0000（rounds=200）；最坏 3.23%（rounds=50，双向） | 混杂已排除 | 高 |

---

## 7. 未试轴及原因

| 未试轴 | 原因 |
|---|---|
| spine 分段栈（不扩容不 memcpy） | 需重写 `Spine` 的 push/索引语义，改动面 ≥ 本任务其余全部补丁；2b 已用更低成本拿到同向收益 |
| eval 主循环 `.expect()` 去边界检查（`unwrap_unchecked`） | 预期 <1%（每步一条已预测分支），且引入 UB 风险；在本机噪声界内不可判定，不值得 |
| `Entry` 布局/`nth`/环境表示/Quote 侧记账 | 属 task-2 hotpath 清单的其他轴，不在本任务范围 |
| L02 其余机制（`LetBody`/`PiBody`/memo） | L01 无 let/Π，记忆化已由本地变体 `bump_spine_memo*` 覆盖 |
| `cek`/`bump_iter`/`bump_spine_slim` 等其他变体 | 本任务只针对 `bump_spine_iter`（L01 冠军线） |
| `parigot_add n=12` | 正态形 2^12 节点，export/assert 时间与内存超预算 |
| retired-instruction / PMU 口径 | 本机 `perf_event_open` 实测 EACCES（Lead 探针），无确定性计数器 |
| 64k 深段（`bench_cek_deep`） | 与本次两条轴无关，属深度轴 |

---

## 8. 产物与复现

- 影子树（工作区外）：`/tmp/l01-exp`（`git clone` 主仓库同提交 `071d90c`，不含 `target/`）。
- 补丁：`/tmp/l01-exp/patches/{exp1_applyknown_chainwrap0,exp2a_vals_preserve,exp2b_spine_16384,exp3a_chainrun_hoist,synth_workload,diag_counters,diag_hooks}.patch`
  （`mkpatches.py` 可从 pristine 源重新生成后 6 个）。
- 构建：`build_locked.sh <名字> --patch … --test`（锁内编译，独立
  `CARGO_TARGET_DIR=/tmp/l01-exp/target`；`--test` = `cargo test --release --bin l01bench`）。
  二进制：`bin/{A_main,A_prime,A_syn,B_syn,E2a,E2b,E3a,D2_diag}`（`sha256sum bin/*` 见各批 `env.txt`）。
- A/B 驱动：`/tmp/l01-exp/ab.py`（§1.1；`--analyze-only` 可只重算已有 raw）。
- 机制计数：`/tmp/l01-exp/diag_analyze.py` → `docs/perf-l01/raw/exp-diag/percase.tsv`。
- 原始数据（本报告全部数字）：`docs/perf-l01/raw/exp-{exp1-synth,exp1-church,exp1-dup,exp1-guest,exp1-guest-confirm,exp2a-church,exp2b-church,exp2b-church-confirm,exp3a-church,ctrl*,diag}/`
  （每目录含 `env.txt`、`A_*_repN.txt`/`B_*_repN.txt`、`summary.tsv`）。
- **`D2_diag` 与 `percase.tsv` 只作机制发生次数证据，其变体不是交付二进制、
  其数字不是性能数字**（计数器本身改变热路径成本）。

**主树纪律**：`git -C /home/dev/elaboration-zoo-lsp status --short` 只有
`docs/perf-l01/`、`tools/perf-l01/`、`.commandcode/` 三个未跟踪目录，
`src/**` 与 `Cargo.toml` 零改动。

---

## 9. 复核后修订（task-5 独立复核，2026-10-06）

本节保留全部原始数字与旧判定痕迹，只记录修订与理由；**凡与上文冲突处，
以本节为准**。task-4 因此曾 reopen 一次。

### 9-A `parigot_add n=10`：WIN → **未复现（未判定）**（最重要）

- verify 自写 3 臂轮转驱动（A / B / A_copy，N=25/臂，锁内、cpu7、保频）的批次：
  `med_A = 147.182`、`med_B = 146.321` → **−0.58%**；该批 A 侧半分组
  p95 = **17.90%**（A vs A_copy 跨臂点估计 −0.17%）→ 按规则**未判定**。
  该批跑飞：25 个循环耗时 **646 s**，cpu7 `scaling_cur_freq` 中途掉到
  **1.40 GHz**，4 个档位混合。
- 同一 case 三个独立批次的空对照 p95：**0.23%（本报告批 1）/ 22.17%（批 2）/
  17.90%（task-5）**，**2/3 批 ≥18%** ⇒ §1.2 原来"重负载例外 ⇒ 该 case 地板
  自然只有 0.23%"的解释**不成立**；批 1 的 0.23% 是批次运气，不是负载属性。
  §1.2 已改写为"空对照地板必须每批实测、不可由负载特征先验推断"。
- 已统一修订：**§0 结论先行、§1.2、§3.3 表与结论段、§3.4(3)、§6 汇总表**
  的 parigot_add n=10 判定为 **未复现（未判定）**。
- §3.4(1) 的机制算术（~10% 上界）保留为"机制量级"证据，**不作为收益结论**。
- **待验证线索（原样引用 verify，明确不作数、不升级判定）**：按 governor 档位
  对齐后，同一档内 B/A 两档都约 0.93（171/159 ms、146.7/137 ms），
  A_copy/A 同档内 ~1.000 —— 效应可能存在，但预注册指标 `med_of_min` 在该批
  抓不到；要验证需改用"档位对齐"的预注册协议，本报告不据此改判。

### 9-B 数字勘误：exp2a 的 `_ss` 对照

- §4.1 原写"`_ss` 全 4 个规模 0.00%"，与 raw 不符。raw
  `docs/perf-l01/raw/exp-exp2a-church/summary.tsv` 实际为
  1000/2000/4000 = 0.00%、**8000 = +0.72%**（0.1380 → 0.1390 ms）。
  已按 raw 修正 §4.1 表格与其结论句。
- 该 +0.72% 仍远小于该批地板，"只影响一次性口径"的结论不变。

### 9-C 加固：exp2b 由 task-5 独立复现

- verify 批次（3 臂 A/B/A_copy）：church_pair 4000 = **−7.50%**、
  8000 = **−10.37%**，空对照 p95 = **1.25% / 0.61%**，A vs A_copy 同字节臂
  0.00%，`_ss` 对照全 0.00%。
- 与本报告批 1 的 −7.41% / −10.30% 几乎重合 ⇒ §4.2 结论由"单批干净 WIN"
  升级为"**跨批、跨实现独立复现**"，§0/§6 同步升级。

### 9-D 复核未推翻的结论

- 机制有效性（synth −29…−38%，WIN）；`church_pair`/`dup`/`church_mul` 的
  可证明 <0.05% 上界（机制计数 `fork_h0=2`、`steps=37` 与 n 无关）；
  `exponential` `fork_h0=0`（机制不适用，非未判定）；exp3a 零效果；
  A vs A′ 跨树重建无系统偏差。
- 补充（本文自查）：§4.1 的 4000 行 raw 因浮点刚好落在阈值上显示 WIN
  （−5.00% vs bound 5.00%），本报告一律保守读作"未判定（边缘）"。
