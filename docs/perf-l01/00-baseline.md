# L01 本机性能基线（aarch64 / Android Termux, walt governor）

本文件是 task-1 的交付：`src/L01_nbe` 在**本机**的计时基线、方法学与噪声界。
所有数字均来自 `tools/perf-l01/run_bench.sh`，raw stdout 在 `raw/`（文件名
带时间戳），每个数字都能在对应 `_env.txt` / `_rep*.txt` / `_agg.tsv` 里溯源。
复现步骤见 [README.md](README.md)。

**一句话结论**：本机绝对时间没有可比性——`walt` 的离散档位 + 短基准让单次
`min` 的跨批波动高达 **20–25%**；只有「keep-alive 保频 + 每 rep min 取中位数
+ 同批交错」这套口径能把复现性压到 **≤3%**。判定阈值：**单次 7v7 比较不足
20% 的差异不可判定；<5% 即使 21 reps/侧也不可靠；≥25% 无条件可信。**

- 二进制：`target/release/l01bench`，sha256 `503ff7c966de2ef9…501d37`
- 本轮所有计时：`taskset -c 7`，keep-alive 开，`L01_STACK_MB=128`，
  release (`lto=true, codegen-units=1`) + mimalloc
- 源码冻结：`src/L01_nbe/**`、`src/bin/l01bench.rs` 未改动

---

## 1. 机器与实测条件

| 项 | 值 | 证据 |
|---|---|---|
| kernel | `Linux localhost 6.17.0-PRoot-Distro #1 SMP PREEMPT_DYNAMIC aarch64` | `raw/*_env.txt` |
| 核 | 8 核 big.LITTLE：cpu0–3 max 1.8048 GHz（A510）；cpu4–6 max 2.496 GHz（A710）；**cpu7 max 2.9952 GHz** | `cpuinfo_max_freq` |
| governor | `walt`（全部核），`scaling_min_freq` 与 governor **不可写**（非 root） | 见 §3 |
| 实测频率 | 空闲 0.7872 GHz；负载下常见 2.2464 GHz；偶发快档（约相当于 2.7 GHz 档，+20%） | `scaling_cur_freq` 采样 |
| cgroup | 无 CPU 配额（`cpu.max` 不存在），`Cpus_allowed=0-7` | `raw/*_env.txt` |
| 工具 | **无** perf / valgrind / hyperfine；有 `taskset` / `chrt` / `nice` / `python3` | — |
| rustc | 1.98.1 (48a229cea 2026-09-01) | `raw/*_env.txt` |
| profile | `[profile.release] lto = true, codegen-units = 1` | `Cargo.toml` |
| 分配器 | mimalloc（`src/bin/l01bench.rs` `#[global_allocator]`） | 源码 |
| 栈 | `L01_STACK_MB=128`（大栈线程） | `src/bin/l01bench.rs:68-77` |

`sched_cur_freq` 在负载下从 797→2246 MHz 大幅摆动，且 `walt` 会在不同档位
之间跳变——这是本文件所有噪声现象的根因。

## 2. 方法学

### 2.1 命令口径（来自 `src/L01_nbe/bench.rs`）

- 只计 `normalize`；入参 import/编码、结果 export、正确性断言都在计时窗口外。
- 预热 1 次 + `--rounds` 轮；单进程报告该变体该规模的 min/中位（毫秒）。
- arena 变体跨轮复用（`ListArena`）；spine 系的 `_ss` 行（`bump_spine_iter_ss`
  /`bump_spine_slim_ss`）用 `Machine` + `Bump::reset()` 稳态口径。
- n > 8000 只有迭代变体出赛（`cek`/`cek_bump`/`bump_iter`/`bump_spine_iter`/
  `bump_spine_slim`/`bump_spine_iter_ss`），其余递归变体会栈溢出。
- guest 规模写死：`church_mul` [50,100,200]、`parigot_add` [4,6,8,10]、
  `exponential` [10,14,18,20]。

### 2.2 团队计时协议

1. **绑核**：`taskset -c 7`（最大核）。全队统一 cpu7。
2. **整轮重复（rep）**：同一条命令完整跑 N 次进程；每个 (workload,size,variant)
   得到 N 个「进程内 min」，本文件的中位数基线 = 这 N 个的**中位数**
   （`med_of_min`，即 agg tsv 的 `med_ms`）。
3. **keep-alive 保频**（`run_bench.sh` 默认开）：计时窗口内另起一个
   `SCHED_IDLE`（无 `chrt` 时 `nice 19`）空转进程钉在 cpu7，让 `walt` 停在
   稳定档（2.2464 GHz）而不是空闲 0.7872 GHz。`--no-keepalive` 关闭。
4. **独占锁**：计时前 `mkdir docs/perf-l01/.benchlock`，结束时
   `rm -f .benchlock/pid; rmdir .benchlock`；拿不到就 `sleep 10` 重试，
   持有者已死则自动接管。**禁止并行计时**（另一 agent 的计算/计时都会污染
   频率状态）。`run_bench.sh` 已内建（含 `trap`）。
5. 环境指纹写入每批 `<ts>_<tag>_env.txt`。

### 2.3 为什么用「中位数」而不是「min」

`min` 是极值统计量：只要一次 rep 撞上快档，min 就跳 20%。`walt` 下快档是
**随机出现**的瞬态，所以 min-of-N 不可复现。中位数对少数快档不敏感，测量的是
「稳定档下的典型速度」——这才是可比的量。原始 per-rep 序列（`bump_spine_iter`
n=8000，ms）直接展示了这一点：

```
无 keepalive b1: 0.144 0.163 0.159 0.135 0.131 0.134 0.136   ← 后段撞上快档
无 keepalive b2: 0.162 0.158 0.159 0.160 0.159 0.159 0.159   ← 整批卡慢档
keepalive  b1  : 0.162 0.161 0.158 0.166 0.158 0.159 0.159   ← 稳定档
keepalive  b3  : 0.158 0.161 0.159 0.160 0.163 0.159 0.166   ← 稳定档
```

## 3. 噪声界（量化结论）

### 3.1 同一配置重复整轮

church，8 变体，n=4000/8000，每批 7 reps，3 个**完全相同**的批次。
证据：`raw/20261006-084414_noise_church_r3_3batches.txt`（无 keepalive）、
`raw/20261006-085340_noise_keepalive_church.txt`（keepalive）、
`raw/20261006-085357_noise_min_vs_median.txt`（对照表）。

| 口径 | 统计量 | 跨批离散度（中位 / 最大） |
|---|---|---|
| 单次进程（1 rep） | 进程内 min | 单 rep CV **~7%**；7 reps 内 max/min **18–43%** |
| 无 keepalive | min-of-7 | **20.0% / 22.1%** |
| 无 keepalive | median-of-7 | 3.5% / 19.8% |
| **keepalive** | min-of-7 | 17.7% / 24.7% |
| **keepalive** | **median-of-7** | **0.9% / 2.9%** ✅ |

结论：**keepalive + 中位数**是唯一把跨批复现性压到 ≤3% 的组合。keepalive 单独
不够（min 仍会偶发抓快档）——两者必须同时用。

### 3.2 Null A/B（同一二进制，真值比 = 1.000）

这是给 task-4 的**假阳性地板**。把同一二进制的一批 reps 按奇数/偶数分成 A/B
两组，用中位数比较；两组真值完全相同，测出的差就是纯噪声。

- **无 keepalive**（3 批 × 14 reps，7/侧）：|差| 中位 2.5%，p90 17.5%，**max 20.5%**
  → `raw/20261006-085047_nullab_paired.txt`
- **keepalive**（3 批 × 14 reps，7/侧）：|差| 中位 1.12%，p90 10.8%，**max 17.6%**
  → `raw/20261006-085425_nullab_keepalive.txt`
- **keepalive，重采样估计需要多少 reps/侧**（pooled 42 reps，两两不重叠分组，
  3000 次抽样，p95）→ `raw/20261006-085509_nullab_reps_needed.txt`：

| reps/侧 | null \|中位数差\| 的 p95（16 个 n×variant 案例） |
|---|---|
| 7 | 中位 14.6%，最大 18.2% |
| 14 | 中位 10.2%，最大 15.3% |
| 21 | 中位 2.6%，**最大 14.8%**（n=8000 的轻量变体） |

### 3.3 判定阈值（可直接引用）

> 在本机上，用 `run_bench.sh`（keep-alive 默认开）、比较 **`med_ms`（每 rep
> min 的中位数）**、A/B 在同批内按 rep 交错：
> - **< 5%**：本机不可判定（即使 21 reps/侧，n=8000 轻量变体 p95 仍 ~15%）。
> - **5–20%**：单次 7v7 不可判定（keepalive 下 null 最大假阳 **17.6%**）；要把
>   结论做到这一量级，需 ≥21 reps/侧 **并且** 同批内插一个对照变体做归一化。
> - **≥ 20%**：单次 7v7（keepalive + 中位数）可判定。
> - **≥ 25%**：无条件可信（覆盖所有观察到的噪声极值）。
> - **绝对 min-of-N 的跨批/跨 campaign 比较**：噪声 ≥20%，不可用于任何判定。
> - **重负载例外**：每个计时段 ≳1 ms 的变体（如 `cek_bump` ~0.48 ms）单 rep
>   CV 可低到 <1%；轻量变体（~0.08 ms）噪声最大。

## 4. 基线矩阵

**口径**：keepalive 开，`taskset -c 7`，`med_ms`（跨 rep 的中位数）。
church 为 3 批 × 7 reps = **21 reps** 汇总；dup/deep 为 7 reps；guest 为 5 reps。
完整表：`raw/20261006-085413_baseline_tables.txt`；分批 agg：
`raw/*_ka_church_r3_N7_b{1,2,3}_agg.tsv`、`*_ka_dup_r3_N7_agg.tsv`、
`*_ka_guest_r3_N5_agg.tsv`、`*_ka_deep64000_r3_N7_agg.tsv`。

### 4.1 church_pair 推荐路径矩阵（n = 4000 / 8000）

| 变体 | 4000 med ms | 4000 相对 | 8000 med ms | 8000 相对 | 跨批中位离散 |
|---|---|---|---|---|---|
| `bump_spine_iter_ss` | **0.069** | 1.00× | **0.140** | 1.00× | 1.47% / 1.45% |
| `bump_spine_iter` | 0.078 | 1.13× | 0.159 | 1.14× | 0.00% / 0.63% |
| `bump_spine_memo` | 0.079 | 1.14× | 0.161 | 1.15× | 1.28% / 2.52% |
| `bump_spine_slim` | 0.104 | 1.51× | 0.203 | 1.45× | 2.94% / 0.49% |
| `bump_spine` | 0.113 | 1.64× | 0.232 | 1.66× | 0.88% / 0.43% |
| `bump_tree` | 0.194 | 2.81× | 0.391 | 2.79× | 0.52% / 2.31% |
| `cek_bump` | 0.237 | 3.43× | 0.482 | 3.44× | 0.85% / 2.10% |
| `bump_iter` | 0.237 | 3.43× | 0.475 | 3.39× | 0.85% / 0.42% |

（相对列 = 与同规模 `bump_spine_iter_ss` 之比；两批之间的排名稳定，除
`cek_bump`/`bump_iter` 在 4000 打成平手。）

### 4.2 复制强制（dup）

| 负载 | `bump_spine_iter` | `bump_spine_memo` | 分离度 |
|---|---|---|---|
| dup_pair 4000（×2） | 0.156 | **0.081** | 1.9× |
| dup_deep 4000（×4） | 0.328 | **0.088** | 3.7× |
| dup_pair 8000（×2） | 0.337 | **0.171** | 2.0× |
| dup_deep 8000（×4） | 0.675 | **0.182** | 3.7× |

memo 在**线性** church 上的税：4000 `0.079 vs 0.078`（+1.3%）、8000
`0.161 vs 0.159`（+1.3%）——在本机噪声内，读不出 readme 说的 +8%。

### 4.3 guest 形状（`--workload guest`）

| 负载 | 规模 | `bump_spine` | `bump_spine_iter` | `bump_spine_iter_ss` | `bump_spine_memo` |
|---|---|---|---|---|---|
| church_mul | 200 | 0.566 | 0.387 | **0.334** | 0.388 |
| parigot_add | 10 | **103.0** | 146.2 | 143.3 | **0.305** |
| exponential | 20 | **12.57** | 14.28 | 14.46 | **0.006** |

- **共享轴上 memo 碾压**：parigot n=10 比最快的非 memo（`bump_spine` 103.0）
  快 **337×**；exponential n=20 快 **~2095×**（0.006 ms 已接近计时分辨率，
  数量级可信、末位不可信）。
- **非右链形状下递归版反超迭代版**：`bump_spine` 在 parigot 上比
  `bump_spine_iter` 快 **1.42×**、exponential 上 1.14×（方向与 readme 一致，
  幅度比 readme 的 ~1.9×/2.0× 小）。

### 4.4 深 n（迭代系，med ms；递归变体在此规模栈溢出）

| n | `cek` | `cek_bump` | `bump_iter` | `bump_spine_iter` | `bump_spine_slim` | `bump_spine_iter_ss` |
|---|---|---|---|---|---|---|
| 32000 | 16.52 | 2.436 | 2.248 | 0.866 | 1.200 | **0.562** |
| 64000 | 30.76 | 4.610 | 5.425 | 1.402 | 1.628 | **0.966** |

- `_ss` 稳态复用在大 n 收益最大：64000 时 `0.966` vs 一次性 `1.402`（1.45×）。
- 64000 时 `bump_spine_iter_ss` 相对 `cek` 快 31.8×、相对 `bump_iter` 快 5.6×，
  是全场最快。

## 5. 与 readme（Windows x64）的定性对照

readme 实测运行于 Windows x64（`src/L01_nbe/readme.md:75`），**不是本机事实**。
且 readme 报的是 `min`、本文基线报的是 `med_ms`，两者不同口径，绝对值不可
逐项对齐：本机 spine 族（含 `_ss`）比 readme 慢约 **1.8–2.3×**，而
`bump_tree`/`cek_bump`/`bump_iter` 本机 min（0.166/0.198/0.195）与 readme
（0.214/0.183/0.183）互有胜负。因为口径 + 档位不同，**只对照排序与交叉点**，
绝对倍率仅作量级参考。

**本机成立（与 readme 同向）**

- 第一梯队排序 `_ss < iter ≲ memo < slim < spine`：4000/8000 两个规模都成立。
- memo 对复制负载的倍率 1.9×/3.7×（readme 1.8×/3.6×）——成立。
- memo 在共享负载上数量级收益（readme 286×/517×，本机 337×/~2095×）——成立。
- 非右链负载递归 `bump_spine` 反超迭代 `bump_spine_iter`——方向成立。
- `cek` 约慢 30–50×（readme ~50×）——量级成立。
- `bump_spine_rpn`/`native_clo`/`bump_spine_memo_inline` 等被否决轴本轮未复测，
  不作为本机结论。

**本机不成立 / 反转（重要）**

1. **`bump_tree` 与 `cek_bump`/`bump_iter` 的排序反转**。readme n=4000：
   `cek_bump`/`bump_iter` 0.183 快于 `bump_tree` 0.214；本机：`bump_tree`
   0.194 **快于** `cek_bump`/`bump_iter` 0.237（8000 同样 0.391 vs 0.475/0.482）。
   本机 `bump_tree` 不再是「慢 7×」那一档。
2. **`bump_spine` 相对迭代版只慢 1.64×（readme 2.5–3.5×）**：本机递归版与
   迭代版差距比 readme 小得多。
3. **`bump_spine_slim` 在大 n 没有反超 `bump_spine_iter`**。readme 称 64k 起
   slim 反超（0.78 vs 1.04）；本机 64k：slim 1.628 **仍慢于** iter 1.402
   （32k：1.200 vs 0.866）。readme 的交叉点在本机 **64k 未见**；更的大规模
   （256k）本轮超预算未测，不能外推。
4. **memo 的线性税本机 ~1%（readme +8%）**：本机分辨不出该税。
5. **`_ss` 相对一次性口径的收益比 readme 小**：64000 本机 1.45×（readme 512k
   才拉到 3.3×；本机 64k 仅 1.45×，趋势同向但幅度更小）。

## 6. 已知限制

- **本轮规模上限 64000**（深 n 段）。readme 的 128k/256k/512k 交叉点未复测。
- guest 的 parigot/exponential 规模写死在 `bench.rs`；本机 `parigot_add n=10`
  已达 103–146 ms、`exponential n=20` 达 12–14 ms，**不要**擅自放大。
- 计时单位毫秒、打印 3 位小数：`exponential n=20` 的 memo（0.006 ms）与
  小 n guest 已接近分辨率，只可用于数量级结论。
- 所有数字是**同一 campaign（2026-10-06 08:5x UTC）**内的；跨天/跨 session
  的绝对值不可直接比较，须重测。
- 未复测的 readme 变体（`rpn_owned`/`native_clo`/`compiled`/字节码族等）在
  本机没有本文件级别的基线数字；如需判定请用 `--only` 补测。

## 7. 证据索引

| 内容 | 文件 |
|---|---|
| 噪声（church，3 批 × 7 reps，无 keepalive） | `raw/20261006-084414_noise_church_r3_3batches.txt` |
| 噪声（church，3 批 × 7 reps，keepalive） | `raw/20261006-085340_noise_keepalive_church.txt` |
| min vs median 对照 | `raw/20261006-085357_noise_min_vs_median.txt` |
| Null A/B（无 keepalive；keepalive） | `raw/20261006-085047_nullab_paired.txt`、`raw/20261006-085425_nullab_keepalive.txt` |
| reps/侧 → 假阳性（重采样） | `raw/20261006-085509_nullab_reps_needed.txt` |
| 基线汇总表（本文所有数字） | `raw/20261006-085413_baseline_tables.txt` |
| 分批 agg（church/dup/guest/deep） | `raw/*_ka_*_agg.tsv` |
| 环境指纹 | `raw/*_ka_*_env.txt` |
