# L02 本机性能基线（aarch64 / Android Termux, `walt` governor）

本文件是 **task-6** 的交付：`src/L02_tyck`（`l02bench`）在**本机**的墙钟计时口径、
噪声界与基线矩阵，外加 `l02l05mem --chapter L02` 的**确定性分配基线**。所有数字
都能在 `raw/`（文件名带时间戳）里溯源，索引见 §9。复现步骤见 [README.md](README.md)。

**一句话结论**：本机 `walt` governor 有两个相差 **~20%** 的时钟档，且档位在时间上
**成块自相关**（一次转换持续几十个 rep）。同批交错（ABBA）比较的假阳地板 ~0.5%；
**「先跑完 A 再跑完 B」的跨 invocation 对比天然带 ~19% 假阳**，即使 21 reps/侧也
救不回来。`l02l05mem` 的分配计数是确定性的（两次运行逐字节相同），为零噪声证据。

- 二进制：`target/release/l02bench` sha256 `28d9884383ef0440…f0f5e87a`；
  `target/release/l02l05mem` sha256 `8aeadb1577caf455…100df606`
- 本轮所有墙钟计时：`taskset -c 7`，keep-alive 开（SCHED_IDLE 保频），
  `L02_STACK_MB=128`，release（`lto=true, codegen-units=1`）+ mimalloc
- 源码冻结：`src/L02_tyck/**`、`src/bin/l02bench.rs`、`src/bin/l02l05mem.rs` 未改动
- 计时口径：`--only` **单实现隔离**（见 §2.4），聚合量 = **`med_of_min`**
  （每 rep 进程内 min 再取 N 个 rep 的中位数）

---

## 1. 机器与实测条件

| 项 | 值 | 证据 |
|---|---|---|
| kernel | `Linux 6.17.0-PRoot-Distro #1 SMP PREEMPT_DYNAMIC aarch64` | `raw/*_env.txt` |
| 核 | 8 核 big.LITTLE：cpu0–3 max 1.8048 GHz（A510）；cpu4–6 max 2.496 GHz（A710）；**cpu7 max 2.9952 GHz**（Cortex-X2，本轮唯一绑核） | `cpuinfo_max_freq` |
| governor | `walt`（全部核）；有离散档位；非 root 不可写 | `raw/*_env.txt` |
| 实测频率 | 空闲 787.2 MHz；keep-alive 下稳定档 **2246.4 MHz**；偶发快档（观测到约 +20%，相当于 2.7 GHz 档 / X2 boost） | `scaling_cur_freq` 采样 + §3.1 |
| cgroup | 无 CPU 配额（`cpu.max` 不存在）；`Cpus_allowed=0-5,7` | `raw/*_env.txt` |
| 工具 | **无** perf / valgrind / hyperfine；有 `taskset` / `chrt` / `nice` / `python3`；`perf_event_open` 实测 EACCES（无硬件计数器） | — |
| rustc | 1.98.1 (48a229cea 2026-09-01) | `raw/*_env.txt` |
| profile | `[profile.release] lto = true, codegen-units = 1` | `Cargo.toml` |
| 分配器 | mimalloc（`src/bin/l02bench.rs` / `l02l05mem.rs`） | 源码 |
| 栈 | `L02_STACK_MB=128`（`l02bench`）、1 GB（`l02l05mem` 自带） | 源码 |
| `--only` 隔离 | harness 强制，单实现单进程 | §2.4 |

## 2. 方法学

### 2.1 命令口径（来自 `src/bin/l02bench.rs`）

- 每个负载家族按 `k = 9..max_k` 逐点跑，`n = 2^(k+1)`（每步 +1，n 翻倍）。
- 计时窗口外：解析 + 正确性断言（`bench_check` / `bench_check_nf` 的节点数断言）。
- `--rounds R` 内轮：`fast_ss` 预热 1 次后 R 轮复用同一 `Tycker`；`fast` / `fast_memo`
  每轮**新建** `Tycker`；`basic` 预热 1 次后 R 轮。进程报告 R 轮的 min 与中位。
- `--only a,b,...` 只跑列出的实现；conv 族只走 `check`，无 quote，故 `fast_memo` 不出赛。
- `L02_NO_BITEQ` / `L02_NO_CONV_MEMO` 是 `LazyLock<AtomicBool>`（环境变量只读一次），
  本轮**未设置**任何消融开关，基线 = 全部快速路径/记忆化**开启**。

### 2.2 团队计时协议（`tools/perf-l02/run_bench.sh` 内建）

1. **绑核**：`taskset -c 7`（全场唯一，最大核）。
2. **整轮重复（rep）**：同一条命令完整跑 N 次**进程**；每个
   (workload, k, impl) 得到 N 个「进程内 min」。
3. **聚合**：`med_of_min` = 这 N 个 min 的**中位数**（`*_agg.tsv` 的 `med_of_min`）。
4. **keep-alive 保频**：计时窗口内另起 `SCHED_IDLE`（无 `chrt` 时 `nice 19`）空转
   进程钉在 cpu7，让 `walt` 停在 2246.4 MHz 而不是 787 MHz 空闲档；`--no-keepalive` 关闭。
5. **独占锁**：`mkdir docs/perf-l02/.benchlock` 成功才可跑；释放先 `rm -f pid` 再
   `rmdir`；拿不到 `sleep 10` 重试，持有者已死自动接管；`trap` 保证异常退出不泄漏。
   **禁止并行计时**。
6. 环境指纹（kernel / 核频 / governor / loadavg / 二进制 sha256 / profile）写入每批
   `*_env.txt`。

### 2.3 单位

`l02bench` 内部是 `Instant::elapsed().as_micros()`，但打印 `min/1000` + `min%1000`
并带字面 `ms` 后缀（`src/bin/l02bench.rs:260`）——**打印值是毫秒、精度到 µs**
（`4.493` = 4493 µs）。`parse_bench.py` 按后缀识别，若将来改为 `µs` 也会自动换算。

### 2.4 为什么强制 `--only` 单口径隔离

`src/L02_tyck/readme.md`「测量方法论」自记：不加 `--only` 时同进程按
`fast_ss → fast → fast_memo → basic` 顺序计时，`fast_ss` 跨轮持有的大 bump 池
（数 MB–数十 MB）在足迹压力下页被淘汰，**大 k 段 min 被高估**（conv_dup k=15
全量 21 ms vs `--only fast_ss` 隔离 12 ms）。本 harness 因此拒绝一次跑多个实现，
唯一例外是 `--interleave`（§4.4）：仍然一进程一实现，但两个实现**在同一个锁窗口内
逐进程 ABBA 交替**——这是本机唯一能抵消 ~20% 时钟档漂移的对比形态。

## 3. 噪声界（量化结论）

### 3.1 时钟档是双模态的，且成块自相关

同一配置（church / `fast` / 7 reps / 同批）的 per-rep min 不是连续分布，而是两个
间隔 ~20% 的簇。church k=13 的原始 per-rep min（ms，`raw/*noise_church_fast_b3_*`）：

```text
1.027 1.026 1.025 1.022 1.029 0.852 0.855      ← 慢档 ~1.025 / 快档 ~0.853（+20.2%）
```

档位**按进程抽取**（一个 rep 内所有 k 同时快或同时慢），并且在时间上**成块**：
null A/B 的 `fast` 42-rep 序列里 rep 1–11 全部慢档、rep 12–42 大多快档
（`raw/*nullab_church_fast_rep*.txt`）：

```text
rep 1-11 : 1.019-1.031 (慢档)
rep 12-21: 0.851 0.854 0.858 1.024 0.851 ... (快档为主)
rep 22-42: 0.850-1.035（25/42 快档）
```

整个批次可以落在不同档：矩阵批 `church fast_ss k=9` 的 `med_of_min = 0.059`
（快档），而三个噪声批同一格是 `0.072`（慢档）——**整批档位翻转会造成 +22% 的
假差异**。这是本机一切噪声现象的根因。

### 3.2 同一配置重复 3 个批次（church / `fast`，每批 7 reps）

证据：`raw/*noise_church_fast_b{1,2,3}_*`；分析：`noise_report.py`。

| k | min-of-7 跨批离散 | **median-of-7（`med_of_min`）跨批离散** | 单 rep CV | 批内半分组（min-of-half / med-of-half，max） |
|---|---|---|---|---|
| 9 | 0.00% | 0.00% | 7.61% | 22.03% / 22.03% |
| 10 | 0.00% | 0.75% | 7.25% | 20.72% / 18.75% |
| 11 | 0.46% | 0.77% | 7.40% | 20.74% / 19.95% |
| 12 | 0.47% | 0.19% | 6.99% | 21.08% / 20.63% |
| 13 | **20.07%** | **0.10%** | 5.08% | 20.31% / 20.06% |
| 14 | 0.93% | 0.05% | 1.38% | 1.17% / 1.09% |
| 15 | 5.42% | 1.46% | 3.51% | 4.51% / 6.72% |

结论：在这个「三批都主要落在慢档」的会话里，**`med_of_min` 跨批 ≤1.46%**，而
`min-of-N` 在 k=13 因单批撞上快档而跳 20%。但这不是普适保证——§3.1 的整批翻转
（+22%）说明中位数只在**同批同会话**内可靠。批内 3v4 半分组仍可达 20%（奇数个
rep 切成 3/4 时快档恰好全落一侧）。

### 3.3 整批单调漂移（dup_deep / `fast_ss`，3 个连续批次）

证据：`raw/*noise_dupdeep_fastss_b{1,2,3}_*`（三个批 10 秒内跑完）。

| k | b1 `med_of_min` | b2 | b3 | median-of-7 跨批离散 |
|---|---|---|---|---|
| 13 | 4.127 | 4.384 | 4.922 | **19.26%** |
| 15 | 18.347 | 19.152 | 21.217 | **15.64%** |

三个批次**单调变慢**（重负载下的持续降频/热漂移），中位数救不了整批漂移。
**结论：跨批（更不用说跨 invocation）比较重负载格子，噪声界就是 ~15–20%。**

### 3.4 Null A/B（同一二进制，奇偶半分组，21 reps/侧）

证据：`raw/*nullab_church_fast_rep*.txt`、`raw/*nullab_church_fastss_rep*.txt`；
分析：`null_ab.py`。两组真值完全相同，测出的差就是纯噪声。

| 配置 | k | 奇偶交错 \|Δ中位数\| | **blocked 前21 vs 后21** | 随机半分组 bootstrap p95 |
|---|---|---|---|---|
| church `fast` | 9 | 0.00% | 0.00% | 1.69% |
| church `fast` | 10 | 0.00% | 0.90% | 0.91% |
| church `fast` | 11 | 0.46% | **19.27%** | 4.17% |
| church `fast` | 12 | 0.46% | **19.26%** | 19.44% |
| church `fast` | 13 | 0.58% | **18.84%** | 19.29% |
| church `fast_ss` | 9–13 | ≤0.40% | ≤0.39% | ≤0.48% |

- **交错（奇偶）分割**：两侧都拿到两个档，|Δ| ≤0.6% → 这是同批交错 A/B 的假阳地板。
- **blocked（先 A 后 B）**：k≥11 时 **~19%** —— 因为 42 个 rep 里档位切换发生在
  第 12 个 rep 附近，前半慢、后半快。**任何「跑完 A 再跑 B」的实验都会被它污染。**
- `fast_ss` 那一轮恰好几乎全程慢档（1/42 快档），所以两种分割都 ≤0.4%；这不能外推。

### 3.5 判定阈值（本机可直接引用）

> 用 `run_bench.sh`（keep-alive 默认开）、比较 **`med_of_min`**：
> - **< 5%**：不可判定（本机分辨不了）。
> - **5–20%**：**必须同批交错（ABBA）+ ≥21 reps/侧 + 同批空对照**；跨 invocation 的
>   blocked 对比在这个区间**不可判定**（假阳地板 ~19%）。
> - **≥ 20%**：同批交错下可判定；blocked 对比需 ≥25% 才有把握。
> - **≥ 25%**：无条件可信（覆盖所有观察到的噪声极值）。
> - **绝对 `min-of-N` 的跨批比较**：噪声 ≥20%，不可用于任何判定；只可作为「最好档位
>   下的下界」参考。
> - **轻量格子（k≤12，单 rep < ~0.5 ms）整批档位翻转风险最高**：同批交错仍可，
>   blocked/跨批绝对不可。

## 4. 墙钟基线矩阵

**口径**：keep-alive 开、`taskset -c 7`、`--only` 隔离、`--rounds 5`、每批 7 reps，
表中为 **`med_of_min`（ms）**，括号是批内 per-rep min 的相对离散
（`(max-min)/min`，来自 `*_agg.tsv` 的 `spread_pct`）。

### 4.1 五负载 × `fast` / `fast_ss`（证据：`raw/*_m_<wl>_<impl>_agg.tsv`）

| k | church fast | church ss | conv fast | conv ss | conv_dup fast | conv_dup ss | dup fast | dup ss | dup_deep fast | dup_deep ss |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | 0.071 (18%) | 0.059 (2%) | 0.103 (2%) | 0.102 (2%) | 0.196 (2%) | 0.193 (6%) | 0.113 (2%) | 0.112 (2%) | 0.222 (1%) | 0.218 (16%) |
| 10 | 0.133 (22%) | 0.111 (2%) | 0.196 (2%) | 0.193 (2%) | 0.384 (2%) | 0.374 (6%) | 0.219 (1%) | 0.215 (1%) | 0.434 (0%) | 0.424 (16%) |
| 11 | 0.261 (21%) | 0.213 (1%) | 0.383 (1%) | 0.374 (2%) | 0.757 (1%) | 0.734 (6%) | 0.437 (1%) | 0.420 (1%) | 0.874 (22%) | 0.837 (16%) |
| 12 | 0.515 (21%) | 0.419 (1%) | 0.755 (1%) | 0.733 (2%) | 1.509 (1%) | 1.524 (10%) | 0.950 (6%) | 0.833 (3%) | 1.740 (29%) | 1.667 (14%) |
| 13 | **1.028** (1%) | **0.830** (1%) | **1.508** (4%) | **1.463** (1%) | **3.060** (6%) | **3.314** (20%) | **1.841** (5%) | **1.663** (2%) | **3.678** (18%) | **3.620** (31%) |
| 14 | 2.077 (1%) | 1.664 (2%) | 3.067 (5%) | 2.917 (10%) | 6.359 (13%) | 7.013 (20%) | 3.821 (17%) | 3.490 (12%) | 7.894 (28%) | 7.754 (29%) |
| 15 | **4.493** (8%) | **3.592** (20%) | **6.307** (10%) | **5.834** (1%) | **13.416** (10%) | **14.021** (16%) | **7.632** (12%) | **7.239** (19%) | **15.985** (28%) | **14.366** (29%) |

**读表警告**：k≤12 的格子单 rep <1 ms，且矩阵各航班在不同档位批次里跑，行与行之间
（尤其 `fast` vs `fast_ss`）**不可直接相减**（整批档位翻转 ±20%，见 §3.1）。k=13–15
的格子重一些，但仍是单批 7 reps；列间的 10–20% 差异在 §4.4 用交错 A/B 复核。

- 所有负载族在 `fast` 下**严格线性**：每 +1（n 翻倍）时间 ×2（k=11→15 的
  church 0.261→4.493 ≈ ×17.2，2^4=16，含档位差；conv 0.383→6.307 ≈ ×16.5）。
- `conv_dup ≈ 2×conv`（k=13：3.060 vs 1.508）——重复子对确实被比较 3 次（部分被记忆化吸收）；
- `dup_deep ≈ 2×dup`（k=15：15.985 vs 7.632）——复制层数翻倍。

### 4.2 参考版 `basic`（证据：`raw/*_basic_<wl>_agg.tsv`）

| 负载 | k | `basic` `med_of_min` | 批内离散 | `basic/fast`（同 k） |
|---|---|---|---|---|
| church | 11 | 3.786 | 9% | 14.5× |
| church | 13 | 15.780 | 29% | 15.4× |
| church | 15 | 66.950 | 29% | 14.9× |
| conv | 11 | 14.513 | 24% | 37.9× |
| conv | 13 | 60.160 | 18% | 39.9× |
| conv | 15 | 246.808 | 16% | 39.1× |
| dup | 11 | 7.816 | 15% | 17.9× |
| dup | 13 | 33.093 | 17% | 18.0× |
| dup | 15 | 137.870 | 16% | 18.1× |
| dup_deep | 11 | 18.486 | 37% | 21.2× |
| dup_deep | 13 | 74.670 | 17% | 20.3× |
| dup_deep | 15 | 314.646 | 16% | 19.7× |

倍率在 k=11/13/15 三点一致（church ~15×、conv ~39×、dup ~18×、dup_deep ~20×），远超
25% 判定线，**无条件可判**；`basic` 的批内离散偏大（16–31%）正是因为它单 rep
就要几十到几百 ms，容易横跨档位切换。

### 4.3 `fast_memo` vs `fast`（复制强制轴；证据：`raw/*_memo_<wl>_agg.tsv`）

| 负载 | k | `fast` | `fast_memo` | `fast/fast_memo` | `fast_memo` 批内离散 |
|---|---|---|---|---|---|
| dup | 11 | 0.437 | 0.344 | 1.27× | 27% |
| dup | 13 | 1.841 | 1.565 | 1.18× | 48%（档位污染，不可用） |
| dup | 15 | 7.632 | 6.094 | **1.25×** | 28% |
| dup_deep | 11 | 0.874 | 0.380 | 2.30× | 17% |
| dup_deep | 13 | 3.678 | 1.594 | 2.31× | 8% |
| dup_deep | 15 | 15.985 | 6.658 | **2.40×** | 11% |

`dup_deep` 三点一致（2.30/2.31/2.40×）→ 可判；`dup` 的 ~1.25× 在 25% 边界，但三点
同向且 §5 的**确定性分配证据**独立支持（dup k=11 足迹 4.05 MB → 1.48 MB，
dup_deep 4.62 MB → 1.49 MB）。

### 4.4 同批交错 A/B：`fast` vs `fast_ss`（ABBA，21 reps/侧）

`--interleave` 把两个实现逐进程交替（奇数 rep A→B，偶数 rep B→A），使档位漂移对
两臂对称。见 §3.4：这是本机唯一可信的 5–20% 区间对比形态。

（A = `fast`，B = `fast_ss`；`ratio = medA/medB > 1` 表示 `fast` 更慢。
两臂是**同一个 `l02bench` 二进制**，只差 `--only` 口径。）证据：
`raw/*_ab_church_fast_vs_fastss_*`、`raw/*_ab_dupdeep_fast_vs_fastss_*`。

| 负载 | k | `fast` | `fast_ss` | ratio | \|Δ\| | 每 rep 配对中位比 | 配对 IQR | fast 胜 / fast_ss 胜 |
|---|---|---|---|---|---|---|---|---|
| church | 11 | 0.2620 | 0.2580 | 1.016 | 1.6% | 1.016 | 1.5% | 4 / 17 |
| church | 13 | 1.0280 | 1.0030 | 1.025 | 2.5% | 1.025 | 1.0% | 4 / 17 |
| church | 15 | 4.4960 | 4.2400 | 1.060 | 6.0% | 1.059 | 5.1% | 5 / 16 |
| dup_deep | 11 | 1.0420 | 1.0030 | 1.039 | 3.9% | 1.039 | 0.9% | 1 / 20 |
| dup_deep | 13 | 4.4540 | 4.1130 | 1.083 | 8.3% | 1.078 | 2.7% | 2 / 19 |
| dup_deep | 15 | 19.4210 | 18.2860 | 1.062 | 6.2% | 1.064 | 1.1% | 4 / 17 |

**结论（重要）**：`fast_ss` 稳态复用**确实略快，但只有 ~2–8%，不是 §4.1 区块差显示的
20–24%**。§4.1 里 `church k=13` 的 `fast 1.028 vs fast_ss 0.830` 完全由**批次档位翻转**
解释——交错后同一 k 变成 `1.028 vs 1.003`（+2.5%）。配对（ABBA）把档位方差消掉后，
21 reps/侧已经足以让 2.5–8% 的效应在符号检验上显著（`fast_ss` 胜 16–20/21）；这正是
README 判定规则「5–20% 需同批交错 + ≥21 reps/侧」的实证，也证实 readme 的
「`fast_ss` 与 `fast` 两口径相当」。**任何没有交错的 `fast` vs `fast_ss` 结论都是错的。**

## 5. 确定性内存基线（`l02l05mem --chapter L02`）

`l02l05mem` 用计数全局分配器测**分配次数 / 字节 / 大小直方图**，与墙钟无关。
**确定性验证**：同命令连跑两次，输出（含直方图、chunk 序列）**逐字节相同**
（`raw/20261006-112748_L02_mem_k11_wchurch-conv-conv_dup-dup-dup_deep.txt` 的
run 1 与 run 2 `diff` 为空）。

### 5.1 k=11（n=4096）五负载（证据同上文件）

| 负载 | parse | `basic`（Box/Rc） | `fast` 一次性 | arena chunk | `fast_ss` growth | `fast_ss` churn（每轮） | `fast_memo` | `basic/fast` 字节 | `basic/fast` 次数 |
|---|---|---|---|---|---|---|---|---|---|
| church | 296 / 46,824 B | 155,384 / 10.65 MB | 203 / 1.54 MB | 1×1.00 MB | 203 / 1.54 MB（保留 1.00 MB） | 199 / 162,848 B | 206 / 1.54 MB | 6.90× | 765× |
| conv | 458 / 61,416 B | 577,254 / 37.88 MB | 280 / 1.74 MB | 1×1.00 MB | 280 / 1.74 MB | 275 / 46,328 B | — | 21.83× | 2,062× |
| conv_dup | 477 / 83,688 B | 864,315 / 56.72 MB | 297 / 4.50 MB | 2×3.01 MB | 297 / 4.50 MB | 290 / 49,600 B | — | 12.61× | 2,910× |
| dup | 342 / 51,304 B | 307,263 / 20.09 MB | 233 / 3.86 MB | 2×3.01 MB | 233 / 3.86 MB | 227 / 167,936 B | 233 / 1.48 MB | 5.21× | 1,319× |
| dup_deep | 449 / 62,952 B | 611,317 / 39.97 MB | 299 / 4.62 MB | 2×3.01 MB | 299 / 4.62 MB | 292 / 1.51 MB（含 1×4.02 MB chunk） | 300 / 1.49 MB | 8.65× | 2,045× |

### 5.2 k=13（n=16384）标度（证据：`raw/*L02_mem_k13_wchurch-dup.txt`）

| 负载 | `basic` | `fast` 一次性 | arena chunk | `fast_ss` churn（每轮） | `fast_memo` | `basic/fast` 字节 |
|---|---|---|---|---|---|---|
| church | 610,696 / 39.92 MB | 228 / 4.98 MB | 2×3.01 MB | 221 / 1.87 MB | 231 / 4.98 MB | 8.01× |
| dup | 1,217,231 / 79.57 MB | 258 / 10.50 MB | 4×8.53 MB | 249 / 3.22 MB | 258 / 4.99 MB | 7.58× |

### 5.3 三轮口径的语义与能力边界

- **`fast` 一次性**：每轮新建 `Tycker`，计数 = 该轮**完整足迹**（arena chunk 链 +
  Machine 常驻缓冲 + 逐调用草稿）。
- **`fast_ss` 第 1 轮（growth）**：`Tycker::new` + 首轮 = **稳态常驻内存下界**
  （`reset` 不还 chunk、`Vec clear` 保容量）。k=11 与 `fast` 的字节数相同，说明
  一次性口径里常驻部分就是全部；k=13 dup 时 growth 10.50 MB、`reset` 后保留
  4.02 MB（最大 chunk）。
- **`fast_ss` 后续轮（churn）**：每轮**真正的新分配**（arena 内 bump 不经过全局
  分配器）。k=11 全部负载 churn ≤0.16 MB/轮（conv 仅 46 KB）——稳态复用几乎不产生
  新分配；dup_deep k=11 例外（1.51 MB/轮，含一个 4.02 MB arena chunk），说明该负载
  下 bump 池在 reset 后仍需增长。
- **`basic`**：Box/Rc 逐节点计数（`mem::forget` 语义，与 bench 一致）。
- **能力**：分配次数/字节是**确定性**的，可直接证明「某改动减少了 N 次分配 / 多少
  字节」，且逐字复现（零噪声），不受 governor/档位影响。
- **边界**：**不能**直接换算成时间——分配少了也可能被别处掩盖（哈希税、缓存局部性、
  分支预测）。墙钟仍是必需证据，两者互为对照：例如 `fast_memo` 在 dup 族把足迹
  4.05→1.48 MB（2.7×）、dup_deep 4.62→1.49 MB（3.1×），与墙钟 1.25×/2.40× 同向但
  幅度不可直接对应。

## 6. 与 `src/L02_tyck/readme.md` 的定性对照

**readme 数字的来源机与口径（先核对，再对照）**：readme `## 实测结果` 明确写
「机器：Windows x64，release（LTO + codegen-units=1 + mimalloc）」；
「口径：预热 1 次 + N 轮取 min」——即**单进程内的 min-of-rounds**，没有跨进程重复，
正是本机 §3 证明**不可复现**的那个统计量。所以 readme 的绝对值只能作量级参考，
**不能**与本文件的 `med_of_min` 逐项对齐。

**本机成立（与 readme 同向）**

- 两版实现在 church/conv 上**严格线性**（每翻倍 ×2）——成立。
- 排序 `basic ≫ fast ≈ fast_ss`——成立（倍率见 §4.2）。
- `conv_dup ≈ 2×conv`、`dup_deep ≈ 2×dup` 的负载形状——成立。
- **隔离后 `conv_dup k=15 fast_ss` 的 `min = 12.15 ms`**，与 readme 自记的
  「`--only fast_ss` 隔离 12 ms」吻合（`raw/*_m_conv_dup_fast_ss_agg.tsv` 的
  `min_ms`）。readme 的「全量 21 ms」是足迹污染口径，本 harness 强制隔离后无法复现
  该口径，但污染方向与机制一致。
- `conv k=13 fast = 1.508 ms`（readme 1.5）、`dup k=15 fast = 7.632`（readme 7.42）、
  `dup_deep k=15 fast = 15.985`（readme 14.47）——绝对值同量级。
- quote 记忆化对复制负载有效、对线性负载近乎中性：方向成立（幅度见 §4.3）。
- `basic` 相对 memo 的倍率：dup k=15 `basic/fast_memo = 22.6×`（readme 22×）、
  dup_deep `47.3×`（readme 41×）——成立。

**本机不成立 / 需要修正（重要）**

1. **`basic` 在本机相对更慢**：conv 的 `basic/fast` 本机 **39–40×**（readme ~25–27×），
   church **~15×**（readme ~13×）。`fast` 绝对值与 readme 接近（conv k=13 = 1.508 vs 1.5），
   是 `basic` 本身在本机慢 ~1.5×（conv k=13：本机 60.2 vs readme 40.1；church k=15：
   66.95 vs 44.4）。递归 `basic` 在 aarch64 上的常数明显更差。
2. **`fast_ss` 稳态复用只有 ~2–8% 的小幅收益**（§4.4 同批交错 21 reps/侧：church
   k=11/13/15 = +1.6%/+2.5%/+6.0%，dup_deep = +3.9%/+8.3%/+6.2%，符号检验显著）。
   区块中位数一度显示 20–24%，那**纯粹是档位翻转的假象**。与 readme「两口径速度
   相当」方向一致，量级上 readme 说得更保守——本机能验证到 2–8% 的真实小收益。
3. **quote 记忆化幅度比 readme 小**：dup k=15 本机 1.25×（readme 1.9×）、
   dup_deep 2.40×（readme 3.4×）。本机 `fast_memo` 绝对值（6.09/6.66 ms）比 readme
   （3.91/4.24 ms）慢 ~1.6×，而 `fast` 接近，所以比值被压缩。
4. **readme 的 `L02_NO_BITEQ` 消融幅度（conv ~2×）本轮未复测**（本轮基线全部开关开启）；
   消融 A/B 属 task-8。
5. **readme 的探针画像（church ~93% 在 quote、conv ~99.5% 在 conv）本轮未复测**——
   本机无 perf/硬件计数器，只能靠消融/分配计数间接印证。

## 7. 哪些倍率在本机可判定

| 对比 | 本机观测 | 判定性 |
|---|---|---|
| `basic` vs `fast`（church / conv / dup / dup_deep） | 14.9× / 39.1× / 18.1× / 19.7×（k=15） | **可判**（≫25%，且三点一致） |
| `fast_memo` vs `fast`（dup_deep） | 2.30–2.40×（k=11/13/15） | **可判**（无条件） |
| `fast_memo` vs `fast`（dup） | 1.18–1.27× | **可判但处于边界**（三点同向 + §5 确定性分配证据） |
| `conv_dup` vs `conv`（`fast`，k=13） | 2.03× | **可判**（≫25%） |
| `dup_deep` vs `dup`（`fast`，k=15） | 2.09× | **可判**（≫25%） |
| `fast_ss` vs `fast`（church / dup_deep，同批交错 21/侧） | +1.6%/+2.5%/+6.0% 与 +3.9%/+8.3%/+6.2% | **可判**（配对符号检验显著；这是唯一合法的判定形态） |
| `fast_ss` vs `fast`（conv / conv_dup / dup，k≤15） | 区块差 ≤11%，未做交错 | **不可判 / 未测**（需同批交错 ≥21/侧，见 §4.4 方法） |
| any 5–20% 的消融效应（如 `L02_NO_BITEQ`、`L02_NO_CONV_MEMO`） | — | 仅同批交错 + ≥21 reps/侧 + 同批空对照可判 |
| any <5% 的效应 | — | **不可判**（换机器/换硬件计数器才行） |

## 8. 已知限制

- **本轮 k 上限 15**（readme 表到 k=17/21）。`basic` 在 k≥15 单 rep 已达 67 ms（church）
  / 315 ms（dup_deep），再放大收益递减；`--max-k 21 --only fast` 可跑（readme 报
  k=21 ~247 ms），但本轮未做。
- 无 perf / valgrind / 硬件计数器；噪声只能用重复测量刻画，不能做指令级归因。
- `l02l05mem` 的 CLI 与 doc 注释不一致：注释提到 `--hist`，实际只有 `--sizes` /
  `--no-basic`（本轮**未改源码**，仅记录）。L02 的负载表（五负载）与口径
  （fast / fast_ss growth+churn / basic / fast_memo）**齐全，无缺口**。
- 所有数字限于**同一 campaign（2026-10-06 11:22–11:4x UTC）**；跨天/跨 session
  的绝对值不可直接比较，须重测。
- 计时窗口内的 `min` 只反映**最好档位**；§3 已说明为什么基线用 `med_of_min`。

## 9. 证据索引

| 内容 | 文件（`docs/perf-l02/raw/`，`*` = 时间戳前缀） |
|---|---|
| 矩阵 `fast`/`fast_ss`（五负载 × k=9..15） | `*_m_<wl>_<impl>_rep{1..7}.txt`、`*_m_<wl>_<impl>_agg.tsv`、`*_env.txt` |
| `basic` 行 | `*_basic_<wl>_rep{1..7}.txt`、`*_basic_<wl>_agg.tsv` |
| `fast_memo` 行 | `*_memo_<wl>_rep{1..7}.txt`、`*_memo_<wl>_agg.tsv` |
| 噪声：church `fast` 3 批 × 7 reps | `*_noise_church_fast_b{1,2,3}_rep*.txt` + `_agg.tsv` |
| 噪声：dup_deep `fast_ss` 3 批 × 7 reps | `*_noise_dupdeep_fastss_b{1,2,3}_rep*.txt` + `_agg.tsv` |
| Null A/B（church `fast`，42 reps） | `*_nullab_church_fast_rep{1..42}.txt` |
| Null A/B（church `fast_ss`，42 reps） | `*_nullab_church_fastss_rep{1..42}.txt` |
| 交错 A/B（church / dup_deep，21 reps/侧） | `*_ab_<wl>_fast_vs_fastss_*` |
| 分配基线 k=11（五负载，repeat=2） | `20261006-112748_L02_mem_k11_wchurch-conv-conv_dup-dup-dup_deep.txt` |
| 分配基线 k=13（church/dup） | `20261006-112758_L02_mem_k13_wchurch-dup.txt` |
| 环境指纹（每批） | `*_env.txt` |
| 分析脚本 | `tools/perf-l02/{run_bench.sh,parse_bench.py,noise_report.py,null_ab.py,ab_report.py,run_mem.sh}` |
