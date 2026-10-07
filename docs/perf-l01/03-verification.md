# 03 · L01 结论的独立对抗性复核（task-5 / verify）

**结论先行**：`02-experiments.md` 的两条核心声称里，**exp2b（spine 4096→16384）独立复现成立**（我批 −7.50% / −10.37%，空对照 p95 1.25% / 0.61%，同二进制跨臂空对照 0.00%）；**`parigot_add n=10` 的"−6.59% 可判定 WIN"未能复现**（我两批 `med_of_min` = −0.58% / −6.50%，批空对照 p95 = 17.90% / 16.06%，按规则均 UNDECIDED）。`church_pair` 的**计数与算术是证明级、但"<0.05%"是外推估计**，"可证明/证明级"措辞必须降级。另发现 1 处数字与 raw 不符（02 §4.1 `_ss` 行）与若干措辞过强项。

本文件只做"能不能站住"的判定，不新增优化观点；不改任何他人交付文档。

---

## 0. 复核独立性

| 项 | 说明 |
|---|---|
| 计时驱动 | 自己写的 `/tmp/l01-verify/ab3.py`（批 1）、`ab4.py`（批 2，加 `freq.log`），**未 import/复用** `/tmp/l01-exp/ab.py`；只复用 `tools/perf-l01/parse_bench.py` 解析 stdout（题目要求） |
| 空对照 | **(1)** 同 ab.py 口径：参考臂 A 侧 25 rep 随机半分组 4000 次重采样 → \|中位数比−1\| 的 p95；**(2)** 新增**同批跨臂空对照**：`A_syn_copy` 是与 `A_syn` 字节相同的独立文件，同一锁窗内轮转 `A / A_copy / B`，其比值是该仪器+批次的真实假阳地板 |
| 轮转 | 每个 cycle 依次跑 A、A_copy、B，全部 `taskset -c 7` + `L01_STACK_MB=128` + `SCHED_IDLE` 保频；锁：`docs/perf-l01/.benchlock`（mkdir/pid/stale 接管/rm+rmdir） |
| 编译 | 独立副本 `/tmp/l01-verify/tree`（拷自 `/tmp/l01-exp`，含其 target 缓存），`CARGO_TARGET_DIR` 指向自己的目录；**未写 `/tmp/l01-exp/target` 或 `bin/`** |
| 主树 | `/home/dev/elaboration-zoo-lsp` 全复核过程只读 |

我的 raw（本次交付，均在 `docs/perf-l01/raw/`）：
`verify-exp2b-church-verify/`、`verify-exp1-guest-verify/`、`verify-exp1-guest-verify2/`（含 `freq.log`）、`verify-tests/*.log`。

三批环境：`A_syn` sha `2512730883…`、`E2b` sha `cc4dc8c2…`、`B_exp1_syn` sha `888d545e…`（与 02/env.txt 一致）；起点 `loadavg 0.12 0.07 0.02`，锁全程独占。

---

## 1. 结论表

| # | 原声称（出处） | 我的复核 | 判定 |
|---|---|---|---|
| 1 | exp2b `Spine 4096→16384`：church_pair 4000 −7.41%、8000 −10.30%（空对照 p95 3.09%/0.61%）**WIN**（02 §4.2 批 1） | 我批 4000 **−7.50%**（p95 1.25%）、8000 **−10.37%**（p95 0.61%）；同二进制 A_copy 臂 0.00%；`_ss` 对照全 0.00%；paired 中位数 0.9250/0.8963（原文 0.9259/0.8970） | **成立（独立复现）** |
| 2 | `parigot_add n=10`：−6.59%（空对照 p95 **0.23%**）WIN，"唯一可判定收益"（02 §1.2/§3.3/§6） | 我批 A：`med_of_min` **−0.58%**，批空对照 p95 **17.90%**；我批 B：**−6.50%**，p95 **16.06%**；两批的 A_copy 跨臂空对照 −0.17%/+0.16%。均 UNDECIDED | **未复现（未判定）**；"0.23% 地板是重负载属性"被推翻 |
| 3 | `church_pair` "**可证明**收益 <0.05%"，置信度标"**证明级**"（02 §3.4/§6） | 计数方法、钩子位置、`removed_steps` 逐事件算术**全部核实成立**；但 ns/迭代→% 的外推是**估计**（对 <0.05% 只有 ~2.6–4× 余量） | **降级：证明 → 估计**；实用结论（机制拿不到 ≥5%）保留 |
| 4 | exp1 机制在 synth 上 −29.4/−34.6/−37.8%（02 §3.3） | 用 parse_bench 从 raw 重算 = −29.41/−34.55/−37.81% | 成立（数字层面；未重跑墙钟） |
| 5 | exp2a "`_ss` 全 4 个规模 0.00%"（02 §4.1） | raw `exp-exp2a-church/summary.tsv` 8000 = **+0.72%** | **数字有误（1 处）**；不影响其"无可靠收益"判定 |
| 6 | `ChainRun` 判据外提零效果（02 §5） | raw 4 规模全 0.00% | 成立 |
| 7 | 每个改动 79 passed / 0 failed；主树 `src/**` 零改动（02 §1.3/§8） | 独立编译 6 个状态全 79/0；`git status` 只有 docs/.commandcode 未跟踪 | 成立 |

---

## 2. 第 1 条：exp2b（spine 预保留 16384）——**复现成立**

`docs/perf-l01/raw/verify-exp2b-church-verify/summary.tsv`，A=`A_syn`，A_copy=同字节副本，B=`E2b`，N=25/臂，rounds=200，`--only bump_spine_iter,bump_spine_iter_ss`，一次锁窗 82 s。

| size | 变体 | med_A | med_A_copy | med_E2b | copy/A | **E2b/A** | 批空对照 p95 | A_copy 两样本 null p95 | 判定 |
|---|---|---|---|---|---|---|---|---|---|
| 1000 | iter | 0.0180 | 0.0180 | 0.0180 | 0.00% | 0.00% | 9.09% | 5.88% | UNDECIDED |
| 2000 | iter | 0.0370 | 0.0360 | 0.0360 | −2.70% | −2.70% | 2.78% | 2.78% | UNDECIDED |
| 4000 | iter | 0.0800 | 0.0810 | **0.0740** | +1.25% | **−7.50%** | **1.25%** | 1.25% | **WIN** |
| 8000 | iter | 0.1640 | 0.1640 | **0.1470** | 0.00% | **−10.37%** | **0.61%** | 0.61% | **WIN** |
| 4000 | `_ss` | 0.0700 | 0.0700 | 0.0700 | 0.00% | 0.00% | 1.45% | 1.45% | UNDECIDED（=无变化） |
| 8000 | `_ss` | 0.1380 | 0.1380 | 0.1380 | 0.00% | 0.00% | 0.00% | 0.00% | UNDECIDED（=无变化） |

与原文批 1 的对照（两批完全独立、相隔约 1 小时）：

| | 4000 med_of_min | 4000 paired | 8000 med_of_min | 8000 paired |
|---|---|---|---|---|
| 02 批 1 | −7.41% | 0.9259 | −10.30% | 0.8970 |
| **我批** | **−7.50%** | 0.9250 | **−10.37%** | 0.8963 |

判定依据：
1. 两个关键规模的差异都**超过同批 A 侧空对照 p95**（7.50 > 1.25；10.37 > 0.61），也超过**同字节 A_copy 跨臂空对照**（点估计 0.00%，两样本 null p95 1.25%/0.61%）；
2. `_ss` 对照在所有规模 0.00%，证明变化只落在一次性口径（`normalize_imported` 的 `Spine::with_capacity`），符合机制；
3. **绝对增量与机制自洽**：n=4000 省 6.0 µs（一次 realloc，memcpy 96 KB），n=8000 省 17.0 µs（两次 realloc，memcpy 96+192=288 KB）；时间比 17.0/6.0 = 2.83，与 memcpy 字节比 288/96 = 3.0 吻合；
4. 原文批 2 的 UNDECIDED 确实只是**该批空对照 15.6–21.0% 太宽**，不是反证——这一点我复算 `exp-exp2b-church-confirm/summary.tsv` 确认（4000 −5.19% / 8000 +2.80%，p95 15.58/21.03%）。

**判定：成立。** 唯一保留：证据来自 2 个静批（原文批 1 + 我批），本质仍是"同一台机器两个时段的同向复现"，不是跨机复现。

---

## 3. 第 2 条：`parigot_add n=10` —— **未复现（未判定）**

### 3.1 我的两批数字

配方与原文一致：`--workload guest --only bump_spine_iter`，n=10 写死，rounds=10，N=25/臂，A=`A_syn`、B=`B_exp1_syn`，另加同字节 `A_syn_copy` 臂。

| 批 | tag | 锁窗时长 | med_A | med_A_copy | med_B | copy/A | **B/A** | A 半分组 p95 | 判定 |
|---|---|---|---|---|---|---|---|---|---|
| 批 A | `verify-exp1-guest-verify` | 640 s | 147.182 | 146.937 | 146.321 | −0.17% | **−0.58%** | **17.90%** | **UNDECIDED** |
| 批 B | `verify-exp1-guest-verify2` | 890 s | 147.222 | 147.462 | 137.651 | +0.16% | **−6.50%** | **16.06%** | **UNDECIDED** |

（同批其余 case 全部 UNDECIDED，例如批 B：parigot 8 −7.06%/p95 13.42%，parigot 6 −7.53%/13.71%，exponential 18 +0.62%/14.48%，exponential 20 +0.08%/14.72%。）

按预注册规则 `|ratio−1| ≤ max(5%, 同批空对照 p95) → 未判定`，**两批都不成立**；按 Lead 指示"批次变吵就必须如实写未复现、不得用同向当成立"，本条的判定是 **未复现（未判定）**。

### 3.2 "空对照为什么能只有 0.23%"——该解释不成立

02 §1.2 的解释是："n=10 单 rep ≈146 ms，远大于 1 ms 重负载线，25 个 rep 的进程内 min 几乎无离散，所以半分组空对照只有 0.23%"。核对 raw（`exp-exp1-guest/A_syn_rep*.txt`）：

- A 侧 25 个值**并非"几乎无离散"**：min 111.26、max 159.72，CV = **10.3%**；其中 6/25 落在 111–130 的"快簇"，18/25 落在 146.2–147.3，另有 1 个 159.7。
- 0.23% 的真正原因不是离散小，而是**中位数对 <50% 的少数簇不敏感**：只有当一个半分组里 ≥13/25 落到快簇，中位数才会跳档。4000 次重采样的 **max 却达 20.8%（seed=1 时 30.0%）**——分布极重尾，p95 只是把这个尾巴切掉了。
- **地板不是负载属性，是批次属性**：同一 case 四个批次的地板 = 0.23%（原文批 1）、22.17%（原文批 2）、17.90%（我批 A）、16.06%（我批 B）→ **3/4 批 ≥16%**。我批 B 的 `freq.log`（每 rep 前后各采样一次，共 150 个样本）记录到 cpu7 `scaling_cur_freq` 在 **1881600 / 1996800 / 2131200 / 2246400 kHz** 四档间跳动（计数 71/4/6/69，最大最小比 1.194）；同一批各臂的 per-rep 时间也呈明显多簇（我批 A：A 侧 ≈113–132 / 143–147 / 163–181）——**宽地板就是 walt 档位漂移**。
- 关于"25 样本、半分组 12/13 是否低估 p95"：作为**该样本内**中位数的抽样波动估计，半分组 bootstrap 不低估；它低估的是另外两件事——(i) A、B 两臂档位混合不同（跨臂差异），(ii) 批内非平稳漂移。这两件事在本 case 上真实发生，所以 0.23% 远不能当作 A/B 的假阳地板。我的 `A_syn_copy` 跨臂同字节臂正是为量化它们而设。

**结论：02 §1.2 的"重负载例外 ⇒ 空对照自然 0.23%"必须删除或改写为"该 case 地板随批次在 0.2%–22% 间剧烈变化，单批 0.23% 属批次运气"。**

### 3.3 补充证据（**不升级判定**）：配对统计显示效应很可能真实

`ab.py` 本来就输出 `paired_ratio_med`（每 cycle 相邻 A/B 的比值中位数，天然对齐档位）。四个独立批次：

| 批次 | paired_ratio_med | bootstrap 95% CI | 同批同字节空对照 paired_med |
|---|---|---|---|
| 原文批 1 | 0.9344 | [0.9324, 0.9360] | — |
| 原文批 2 | 0.9272 | [0.9130, 0.9303] | — |
| 我批 A | 0.9334 | [0.9310, 0.9566] | 0.9999 [0.9974, 1.0033] |
| 我批 B | 0.9334 | [0.9309, 0.9363] | 1.0002 [0.9984, 1.0060] |

即：**`med_of_min` 口径在四批里给出 0.934 / 0.927 / 0.994 / 0.935（不稳定），而配对口径四批全落在 0.927–0.934，同二进制空对照两批都是 1.000**。这强烈支持"exp1 在 parigot n=10 上确有约 −6.5% 的真实效应"。

为什么会这样——把**我批 A** 的 25 个 rep 按时间簇分组（诊断，非判定）：

| 臂 | 快簇 | 中簇 | 慢簇 |
|---|---|---|---|
| A_syn | ≈113–132（7 个，中位 127.6） | ≈143–147（6 个，中位 146.7） | ≈163–181（12 个，中位 171.2） |
| B_exp1 | ≈107–131（6 个，中位 121.5） | ≈136.9–146.6（8 个，中位 137.1） | ≈159.3–169.2（11 个，中位 159.6） |
| **B/A（同簇）** | **0.9518** | **0.9345** | **0.9323** |
| A_copy/A（同 rep） | ≈1.000 | ≈1.000 | ≈1.000 |

`med_of_min` 在批 A 里失败，是因为 A 的中位数（147.18）落在中簇上沿、B 的中位数（146.32）落在中簇下沿的稀有值上，**跨簇比较**；而按簇对齐后三簇都给出 −4.8%…−6.8%，且同字节臂恒为 1.000。

但它**不能**把本条判定升级为"成立"，原因：(1) 预注册指标是 `med_of_min`，配对中位数不是判定指标；(2) 我批 A 里 A 的中位数落在与 B 不同的档位，说明该统计量对档位混合敏感；(3) 臂序固定为 A→A_copy→B，同字节臂只覆盖了"位置 1 vs 3"，不能完全排除"位置 1 vs 2"的混杂（虽然 A/A_copy = 1.000 表明批内无单调漂移）；(4) 4 批中仍有 1 批 `med_of_min` 给 −0.58%。

**因此最终判定：未复现（未判定）**。可写进报告的最强表述是"疑似 ~−6.5%（配对口径 4 批一致，同二进制对照 1.000），但 `med_of_min` 预注册口径在本机无法稳定判定，不能写成 WIN/可判定收益"。

---

## 4. 第 3 条：`church_pair` 机制计数结论审核

审的对象是 02 §3.2/§3.4：`fork_h0 = 2`、`steps = 37` 与 n 无关 → `removed_steps = 8` → "可证明收益 <0.05%"。

### (a) `--rounds 2 − --rounds 1` = 恰好一次 normalize —— **成立**

- `src/L01_nbe/bench.rs`：church 的 `bump_spine_iter` 每轮 = `assert` 1 次 normalize + `预热` 1 次 + `rounds` 次计时 normalize；guest `guest_time_one` = 预热 1 + `rounds` 次。计数是确定性的、与 rounds 线性。
- raw 验证：`exp-diag/church_r1.stderr` steps=111、`church_r2.stderr` steps=148 → Δ=37；比值 148/111 = **4/3**，正是"3 次 normalize vs 4 次"。guest 的比值精确 **3/2**（2 vs 3 次）。Δ 就是**一次 normalize** 的计数，与报告一致。
- 我用 raw DIAG 独立重算 `percase.tsv` 全部 26 行：**0 处不一致**。

### (b) 钩子位置 —— **成立**

`patches/diag_counters.patch` 的 `FORK_H0/FORK_HN/COMPOSITE_*/BASE_*` 计点就挂在 baseline `eval_iter` 的 `if v_tag(vf)==1` 岔路、`_ =>` 复合头、`base` 分支处；`exp1` patch 改的正是同一批分支。钩子只做 `fetch_add`，不改变控制流/工作栈，不改变被计数事件的发生次数。

### (c) `removed_steps` 算术与"每次省 2/省 1" —— **逐事件核实成立**

对照 baseline 与 `exp1_applyknown_chainwrap0.patch` 的压栈序列：

| 事件 | baseline 压栈（未来迭代数） | exp1 压栈 | 省 |
|---|---|---|---|
| `fork_h0`（β 岔路、heads=0） | `ChainWrap(0)`+`Apply`+`Tm(a)`+`Tm(f)` = 4 | `ApplyKnown(vf)`+`Tm(a)` = 2 | **2** |
| `fork_hn`（heads>0） | `ChainWrap(h)`+`Apply`+`Tm(a)`+`Tm(f)` = 4 | `ChainWrap(h)`+`ApplyKnown(vf)`+`Tm(a)` = 3 | **1** |
| `composite_h0`（复合头、heads=0） | 4（同 fork_h0 形状） | `Apply`+`Tm(a)`+`Tm(f)` = 3 | **1** |
| `base_h0` | `ChainWrap(0)`+`Tm(base)` = 2 | `Tm(base)` = 1 | **1** |
| `base_hn` / `composite_hn` | 不变 | 不变 | **0** |

⇒ `removed = 2·fork_h0 + fork_hn + composite_h0 + base_h0` 与代码逐事件吻合。进一步用**计数之间的结构恒等式**做独立交叉验证：`cw0 ≡ fork_h0+fork_hn+composite_h0+base_h0`、`apply ≡ fork_h0+fork_hn+composite_h0+composite_hn`，在 `percase.tsv` 全部 26 行**逐行成立**（如 church_pair 6≡2+0+4+0、parigot10 3145799≡1048596+0+2097203+0）——这同时确认了钩子挂点没有漏记/重复记。

### (d) "每个被删迭代 ≈3.5 ns" 的外推 —— **是估计，不是证明**

- synth 标定本身可复算：(med_A−med_B)/(2k+1) = 5.0 µs/2001 = **2.50 ns**、66 µs/20001 = **3.30 ns**、774 µs/200001 = **3.87 ns** → 2.5–3.9 ns。
- 外推到 church_pair(8000)：8 个被删迭代 × 3.9 ns = 31 ns / 164 µs = **0.019%**（报告的"<0.02%"对）。
- **余量分析**（关键）：要突破 <0.05% 需单迭代 **10.25 ns**（约 synth 测量值的 2.6–4.1×）；要突破 5% 判定门限需 **1.02 µs/迭代**（约 290×）。而 church_pair 的"平均单迭代 4.4 µs"是被**单个 `ChainWrap(16000)` 巨迭代**拉高的，被删的 8 个都是小迭代。小迭代的单次成本与 synth 的同类迭代（`Tm(Idx)`/`Apply`/`ChainWrap(0)`）同构，但 `Tm(f)` 里的 `nth(env, i)` 成本随 de Bruijn 深度变化，synth 的链形状与 church_pair 并不相同——所以 **10 ns 与 3.9 ns 的 2.6 倍关系只能靠假设，不能算"证明"**。

**判定：计数与算术（a)(b)(c) = 证明级，成立；(d) 及"收益 <0.05%" = 估计。** 02 §3.4 的"因此 church_pair 上'可证明无收益'"与汇总表的"证明级"应改为"机制计数确凿 + 单迭代成本外推的**估计**上界 <0.05%"。实用结论——"该机制在 church_pair 上不可能达到 5% 判定门限（差 ~290×）"——稳健，可以保留。

---

## 5. 第 4 条：数字抽查

抽查方法：`raw` 原始 rep stdout 用 `tools/perf-l01/parse_bench.py` 的 `parse_file` 逐 rep 取进程内 min，再取 25/21/7/5 个 rep 的中位数（= `med_ms`/`med_of_min`）；证据文件路径见下。共抽 **00-baseline 7 项、02-experiments 9 项**。

### 5.1 `00-baseline.md`

| # | 声称（§） | 复核值 | 证据 |
|---|---|---|---|
| 1 | KA 下 median-of-7 跨批离散 中位 0.9% / max 2.9%（§3.1） | 一致 | `raw/20261006-085357_noise_min_vs_median.txt` 末行 |
| 2 | KA null A/B：中位 1.12% / p90 10.8% / max 17.6%（§3.2） | 1.12 / 10.78 / 17.58 | `raw/20261006-085425_nullab_keepalive.txt` 末行 |
| 3 | k=21/side 的 null p95：中位 2.6% / max 14.8%（§3.2） | 一致 | `raw/20261006-085509_nullab_reps_needed.txt` |
| 4 | church 8000：`_ss` 0.140、iter 0.159、memo 0.161、slim 0.203、spine 0.232、tree 0.391、cek_bump 0.482、iter 0.475（§4.1） | 全部一致 | `raw/20261006-085413_baseline_tables.txt` |
| 5 | dup_pair4000 0.156 vs memo 0.081 = 1.9×；dup_deep4000 0.328 vs 0.088 = 3.7×（§4.2） | 1.926× / 3.727× | 同上 |
| 6 | parigot10：spine 103.0 / iter 146.2 / ss 143.3 / memo 0.305，memo 快 337×；exponential20 spine 12.57 / iter 14.28 / memo 0.006 ≈2095×；church_mul200 0.566/0.387/0.334/0.388（§4.3） | 103.016/146.232/143.301/0.305 → 337.8×；12.567/14.284/0.006 → 2094×；0.566/0.387/0.334/0.388 | `raw/20261006-085413_baseline_tables.txt`（guest 段） |
| 7 | deep 64000：cek 30.76 / cek_bump 4.610 / iter 5.425 / spine_iter 1.402 / slim 1.628 / ss 0.966，ss 相对 cek 31.8×、相对 iter 5.6×（§4.4） | 30.759/4.610/5.425/1.402/1.628/0.966 → 31.84× / 5.62× | `raw/20261006-085413_baseline_tables.txt` + `raw/20261006-085327_ka_deep64000_r3_N7_agg.tsv` |

**00-baseline：抽 7 项全部复现，未发现对不上或无 raw 支撑的数字。**

### 5.2 `02-experiments.md`

| # | 声称（§） | 复核值 | 证据 |
|---|---|---|---|
| 1 | church_pair `fork_h0=2`、`steps=37`、`removed=8`、wrap_heads=2n（§3.2） | 一致（Δr1→r2） | `raw/exp-diag/church_r{1,2}.stderr` |
| 2 | parigot10 `fork_h0=1048596`、`steps=18874723`、`removed=4194395`（§3.2） | 一致 | `raw/exp-diag/guest_r{1,2}.stderr` |
| 3 | parigot10 med_A 146.670 / med_B 137.003 / −6.59% / 空对照 p95 0.23%（§3.3） | 一致 | `raw/exp-exp1-guest/summary.tsv` + rep 文件重算 |
| 4 | synth 1000/10000/100000 = −29.41/−34.55/−37.81%（§3.3） | 一致 | `raw/exp-exp1-synth/` |
| 5 | exp2b 4000 −7.41%、8000 −10.30%，`_ss` ≤0.72%（§4.2） | 一致 | `raw/exp-exp2b-church/summary.tsv` |
| 6 | exp2b-confirm 4000 −5.19% / 8000 +2.80%，p95 15.6–21.0%（§4.2） | 一致 | `raw/exp-exp2b-church-confirm/summary.tsv` |
| 7 | 跨树对照 ctrl2/3/self/4 = 1.0000；ctrl3-dup 最坏 2.96%/3.23% 双向（§2） | 一致（按 `min` 比口径） | `raw/exp-ctrl*/summary.tsv` |
| 8 | exp2a 4000 −5.00%、8000 −1.83%（§4.1） | 一致 | `raw/exp-exp2a-church/summary.tsv` |
| 9 | **exp2a "`_ss` 0.00%（全 4 个规模）"（§4.1）** | **✗ 8000 = +0.72%**（1.38→1.39）；1000/2000/4000 确为 0.00% | 同上 |

**对不上/无 raw 支撑清单：**
- ✗ **02 §4.1 表格"`bump_spine_iter_ss` … 0.00%（全 4 个规模）"**：raw 的 8000 行是 `0.1380 → 0.1390 = +0.72%`。结论（无收益）不受影响，但字面数字错误。
- ⚠ **raw `summary.tsv` 的 `verdict` 列与正文结论不一致 3 处**：`exp-exp1-guest` 里 exponential 10 与 parigot_add 4/6 的自动判定是 `WIN`，而正文改判 UNDECIDED（正文更保守、正确）。若有人直接引用 tsv 的 verdict 列就会过度声称；建议在 02 里显式说明"tsv verdict 列未做绝对量门限"。
- ⚠ **跨批绝对值引用**：02 §4.2 用 `00-baseline.md` 的 0.140/0.159（另一 campaign）来"自洽"；该批自带 A_syn 0.165 / `_ss` 0.139 已足够，跨批引用只应作 plausibility。
- 其余抽查项都有 raw 支撑。

---

## 6. 第 5 条：正确性与卫生

### 6.1 测试（独立副本 `/tmp/l01-verify/tree`，自己的 target）

| 状态 | 补丁 | 结果 |
|---|---|---|
| baseline | 无 | **79 passed / 0 failed** |
| exp1 | `exp1_applyknown_chainwrap0` | **79 / 0** |
| exp2a | `exp2a_vals_preserve` | **79 / 0** |
| exp2b | `exp2b_spine_16384` | **79 / 0** |
| exp3a | `exp3a_chainrun_hoist` | **79 / 0** |
| diag | `synth_workload` + `diag_counters` + `diag_hooks` | **79 / 0** |

日志：`docs/perf-l01/raw/verify-tests/*.log`。题目点名的用例都在并通过：`bump_spine_iter::tests::{chain_beta_fork, chain_mixed_heads, interleaved_chains_fallback, guest_shapes_ok, machine_steady_state_two_rounds}`。
**发现（文档缺陷）**：`diag_hooks.patch` 单独**不能** apply 到 pristine `bench.rs`（`error: patch does not apply` at `bench.rs:277`），必须先打 `synth_workload.patch`；02 §8 只列了补丁名，没有给出 D2_diag 的补丁栈，建议补上。

### 6.2 A/B 结果断言一致

- 每个 rep `rc=0`（ab3.py 遇非零即 raise，三批 225 个 rep 全部 0）——bench 内部对每个 (case, variant) 执行 `assert_eq!(got, expect)`，`expect` 是**数学构造的正态形**（`term::church(n*n)`/`term::parigot(2n)`/`term::exponential_expect(n)`），因此 A、B 的结果都等于同一期望项，二者断言一致。
- 把 stdout 的**非数字结构**逐行比较：`exp-exp1-guest`、`exp-exp1-synth`、`exp-exp1-dup`、`exp-exp2b-church` 的 A vs B 完全一致（本机 bench 不打印结果项，只打印时间表；数字以外的表头/变体名/规模全同）。这与"79 测试 + 每 rep 断言"共同构成正确性门。

### 6.3 主树未被污染

```
$ git -C /home/dev/elaboration-zoo-lsp status --short
?? .commandcode/
?? docs/perf-l01-optimization-2026-10-06.md
?? docs/perf-l01/
?? tools/perf-l01/
$ git diff --stat -- src/ Cargo.toml      # 空
```
`src/**`、`Cargo.toml` **零改动**；`target/release/l01bench` sha256 `503ff7c966de…501d37` 与 00-baseline 声称一致，且等于 `/tmp/l01-exp/bin/A_main`。主树干净。
（小注：02 §8 说未跟踪目录只有三个，实际还有一个未跟踪文件 `docs/perf-l01-optimization-2026-10-06.md`。）

---

## 7. 第 6 条：过度声称审计

| # | 位置 | 问题 | 严重度 |
|---|---|---|---|
| P1 | 02 §1.2 | "重负载例外 ⇒ n=10 空对照自然 0.23%"；raw 显示 A 侧 CV 10.3%、111–160 ms 多簇，0.23% 来自中位数对少数簇不敏感 + 该批恰好静；同 case 另 3 批地板 22.17/17.90/16.06%。**必须删/改写** | 高（方法论错误） |
| P2 | 02 §3.3/§6 | "两批独立、点估计一致 → 中高置信度"：批 2 是 UNDECIDED（p95 22.17%），且我两批均 UNDECIDED。用同向点估计提置信度属于"把噪声/未判定当支持" | 高 |
| P3 | 02 摘要/§6 | "只有 `parigot_add` 有约 7% 的**可判定**收益"：我复核未复现可判定性 | 高（需降级） |
| P4 | 02 §3.4/§6 | `church_pair`"**可证明**无收益"、置信度"**证明级**"：计数确凿但 <0.05% 是外推估计，对 0.05% 只有 ~2.6–4× 余量 | 中（措辞过强） |
| P5 | 02 §4.1 | exp2a `_ss` "0.00%（全 4 个规模）"与 raw 8000=+0.72% 不符 | 低（数字错） |
| P6 | 02 §3.2 表 | `removed%steps` 列（church_pair 21.6%、parigot 22.2%）易被读成"工作量/时间占比"；实际是 **eval 迭代数**占比，church_pair 的真实时间上界是 0.02%。建议列名改成"占 eval 迭代数%，非时间" | 低（易误读） |
| P7 | 02 §3.3 raw verdict 列 | tsv 自动判 WIN（exponential 10、parigot 4/6），正文 UNDECIDED；应注明 tsv 列不设绝对量门限 | 低 |
| P8 | 02 §4.2 | 用另一 campaign 的绝对时间做"自洽"；应标注为 plausibility 而非证据 | 低 |
| P9 | 02 §2 | 跨树 null 用 `min` 口径（00 §3.3 已说 min 跨批噪声 ≥20%）；结论靠 rounds=200 时 1.0000 支撑，可用但应说明这是"min 在重 rounds 下才稳定"，且未覆盖 exp1/exp2b 实际用的 A_syn↔E2b/B_syn 二进制对（我补的同字节臂覆盖了） | 低 |
| P10 | 02 §8 | D2_diag 补丁栈未记录（`diag_hooks` 需先 apply `synth_workload`） | 低 |
| P11 | 02 §3.4 | "synth 标定 2.5–3.9 ns"被同时用于预测 parigot（≈10% vs 实测 6.6%）和支持 church 上界；作为量级交叉检查可以，但不应称"标定/证明" | 低 |
| P12 | 00 §4.3 | memo/exponential "~2095×"建立在 0.006 ms（计时分辨率）上；原文已注明"末位不可信"，OK，保持 | 无 |

没有发现"拿环境轴（target-cpu/panic=abort/PGO）冒充算法改进"的问题（02 未涉这些轴）；没有发现"跨批比绝对值当结论"（除 P8 的辅助性引用）；没有发现"用单一 min"（正式判定都用 med_of_min，min 只作辅助）。

---

## 8. 最终报告可写 / 必须降级

**可以直接写进最终报告（本次复核支持）：**
1. `Spine::with_capacity(4096) → 16384`（`normalize_imported`，一次性口径）：church_pair 4000 **−7.5%**、8000 **−10.4%**，两次独立静批复现（原文批 1 + 本复核批），同批空对照 1.25%/0.61%、同字节空对照 0.00%、`_ss` 对照 0.00%；机制（省 1–2 次 realloc + 288 KB memcpy）与实测比例自洽。这是本轮**唯一可复现的现成负载收益**。
2. 机制计数事实：`church_pair` 的 `fork_h0=2`/`steps=37` 与 n 无关；`exponential` 的 `fork_h0=0`（ApplyKnown 从不命中）；`parigot_add n=10` 每 normalize `fork_h0=1.05e6`；`removed_steps` 公式逐事件正确。可写为"机制事实"，不可写为性能数字。
3. exp1 机制在 synth 形状上的 −29…−38%（机制有效性上界轴）。
4. `ChainRun` 判据外提零效果。
5. 正确性/纪律：6 个状态 79 passed/0 failed；`src/**`、`Cargo.toml` 零改动；A/B 结果断言一致。

**必须降级：**
1. "`parigot_add n=10` ~7% 可判定收益" → **未复现/未判定**。最弱可接受表述："疑似 ~−6.5%（配对口径 4 批一致、同二进制对照 1.000），但 `med_of_min` 预注册口径在本机无法稳定判定（本复核两批空对照 p95 16–18%）；不能标 WIN。"
2. "`church_pair` 可证明收益 <0.05%，证明级" → **估计**（计数确凿 + 单迭代成本外推；对 0.05% 仅 ~3× 余量）。实用句保留："远低于 5% 判定门限，本机不可判定，不应作为优化目标。"
3. "`parigot_add n=10` 空对照天然 0.23%、重负载例外" → **删除**；改为"该 case 地板随批次 0.2%–22%，受 walt 档位漂移支配"。
4. "两批同向 → 中高置信度" → **低–中**，并说明批 2 与本复核两批均 UNDECIDED。
5. exp2a `_ss` "全 4 规模 0.00%" → 8000 为 **+0.72%**（结论不变）。

**给 Lead 的最终答案口径建议**：L01 上"还有没有性能优化空间"——按本轮证据，(a) 一次性口径的 spine 预保留是**可复现但一次性、约 −7…−10%（仅 n≥4000 的一次性 normalize 路径）**；(b) β 岔路回移在现有负载上**没有可稳定判定的收益**（parigot n=10 疑似 −6.5% 但判定不了；church/dup/church_mul/exponential 上限 <0.05%–0.4%）；(c) 稳态 `_ss` 路径不受这些改动影响。任何"再来 ~7% 稳定提速"的结论都不应写进最终报告。

---

## 9. 复现命令

```bash
# 我的计时（锁内自动获取/释放）
python3 /tmp/l01-verify/ab3.py --tag exp2b-church-verify \
  --arm A_syn=/tmp/l01-verify/bin/A_syn --arm A_syn_copy=/tmp/l01-verify/bin/A_syn_copy \
  --arm E2b=/tmp/l01-verify/bin/E2b \
  --n 25 --rounds 200 --workload church --max-church 8000 \
  --only bump_spine_iter,bump_spine_iter_ss
python3 /tmp/l01-verify/ab4.py --tag exp1-guest-verify2 \
  --arm A_syn=/tmp/l01-verify/bin/A_syn --arm A_syn_copy=/tmp/l01-verify/bin/A_syn_copy \
  --arm B_exp1_syn=/tmp/l01-verify/bin/B_exp1_syn \
  --n 25 --rounds 10 --workload guest --max-church 8000 --only bump_spine_iter

# 正确性（自己的副本与 target）
/tmp/l01-verify/run_tests.sh          # baseline/exp1/exp2a/exp2b/exp3a
/tmp/l01-verify/run_diag_test.sh      # synth + counters + hooks
```
