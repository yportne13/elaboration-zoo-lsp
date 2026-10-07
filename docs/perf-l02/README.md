# L02 性能基线：复现方法（`tools/perf-l02/`）

本目录是 task-6 的交付：`src/L02_tyck`（`l02bench`）在**本机**
（aarch64 / Android Termux，8 核 big.LITTLE，`walt` governor）上的可信计时口径、
基线矩阵与噪声界。结果见 [00-baseline.md](00-baseline.md)，原始数据在 `raw/`
（文件名带时间戳，每个数字都能溯源）。

计时协议与 `tools/perf-l01/` 同源（L01 轮已验证：keep-alive 保频 + 中位数聚合
把跨批复现性从 20–25% 压到 ≤3%）。L02 的两点差异：**强制 `--only` 单口径隔离**
（readme 自记的足迹污染）与**打印单位是毫秒/微秒精度**（不是 µs 整数）。

## 1. 先决条件

```text
cargo build --release --bin l02bench     # 墙钟基线（tools/perf-l02/run_bench.sh 用）
cargo build --release --bin l02l05mem    # 确定性分配基线（run_mem.sh / 手工）
```

- 工具链：rustup 固定 1.98.1（`rust-toolchain.toml`）。
- `l02bench` 用 mimalloc（`#[global_allocator]`）+ 128 MB 栈线程
  （`L02_STACK_MB` 可调，默认 128，见 `src/bin/l02bench.rs:111`）。
- 需要 `taskset`（绑核）与 `chrt`（keep-alive 用 SCHED_IDLE；无 `chrt` 时降级
  `nice -n 19`）。本机无 perf / valgrind / hyperfine，无硬件计数器
  （`perf_event_open` 实测 EACCES），所以噪声只能用重复测量刻画。

## 2. 墙钟基线：`tools/perf-l02/run_bench.sh`

```text
tools/perf-l02/run_bench.sh --only fast --workload church --max-k 15 --reps 7 --rounds 5
tools/perf-l02/run_bench.sh --only fast_ss -w conv_dup -k 15 -N 7 -r 5 --ks 11,13,15
tools/perf-l02/run_bench.sh --only basic -w church -k 15 --tag basic_church
tools/perf-l02/run_bench.sh --only fast -w church -k 13 -N 42 --tag nullab   # null A/B 用
```

参数：

| 参数 | 默认 | 含义 |
|---|---|---|
| `--only IMPL` | **必填** | `basic` / `fast` / `fast_ss` / `fast_memo`，**必须恰好一个** |
| `--workload/-w` | `church` | `church`/`conv`/`conv_dup`/`dup`/`dup_deep` |
| `--max-k/-k` | 15 | `l02bench` 从 k=9 跑到 `--max-k`（每次 +1，n=2^(k+1) 翻倍） |
| `--rounds/-r` | 5 | 进程内计时轮数（`l02bench` 报告其 min/中位） |
| `--reps/-N` | 7 | **整进程重复次数**（每个 rep 一个新进程） |
| `--ks` | 全部 | 只对 tsv 汇总做 k 过滤（显示用） |
| `--bin` | `target/release/l02bench` | 可指向实验二进制（A/B 用） |
| `--interleave` | 关 | 配合 `--only a,b`：两实现**逐进程 ABBA 交替**（§2.6） |
| `--tag` | `<w>_<impl>_k<K>` | raw 文件名标签 |
| `--cpu` | 7 | 绑核（cpu7 = Cortex-X2 2.995 GHz） |
| `--stack-mb` | 128 | `L02_STACK_MB` |
| `--no-keepalive` | 关 | 关闭保频（复现旧的机会主义 min） |

流程：写环境指纹 `*_env.txt` → 取独占锁 → 起 keep-alive → 跑 N 个 rep（raw
`*_repN.txt`）→ `parse_bench.py` 聚合出 `*_agg.tsv`。

### 2.1 为什么 `--only` 是强制的

`src/L02_tyck/readme.md`「测量方法论」自记：不加 `--only` 时同一进程按
`fast_ss → fast → fast_memo → basic` 顺序计时，`fast_ss` 跨轮持有的大 bump 池
（数 MB–数十 MB）在足迹压力下页被淘汰，**大 k 段 min 被高估**——conv_dup k=15
全量跑 21 ms vs `--only fast_ss` 隔离 12 ms。本 harness 因此**拒绝**一次跑多个
实现：一次进程只跑一个实现。唯一的例外是 `--interleave`（§2.6）——它仍然
**一进程一实现**，只是把两个实现在同一个锁窗口内逐进程交替，用于跨实现的 A/B。

### 2.2 聚合量：`med_of_min`

每个 rep 是一个新进程，`l02bench` 在其中报告「`--rounds` 轮内 min / 中位」。
本基线取的量是 **N 个 rep 的 rep 内 min 的中位数**（`agg.tsv` 的
`med_of_min` 列）。`min` 是极值统计量：`walt` 偶发快档时它会跳 ~20%，所以
跨批的 `min-of-N` 不可复现；中位数测的是「稳定档下的典型速度」。

### 2.3 单位

`l02bench` 内部用 `Instant::elapsed().as_micros()`（µs），但打印时
`min/1000` 且带字面 `ms` 后缀（`src/bin/l02bench.rs:260`）——即**打印值是
毫秒、精度到 µs**（如 `4.493` = 4493 µs）。`parse_bench.py` 按后缀识别，
若将来改成 `µs` 后缀会自动换算成 ms。

### 2.4 独占锁协议（跨 agent 约定，非 OS 锁）

计时窗口内**禁止任何并行计时/大编译**（都会改 `walt` 的档位状态）：

- 获取：`mkdir docs/perf-l02/.benchlock` 成功才算拿到；然后写
  `.benchlock/pid`。
- 拿不到：`sleep 10` 重试；若 `pid` 已死（或 `/proc/<pid>` 不是 bench/harness
  进程）则自动接管（清 `pid` 再 `rmdir`）。
- 释放：**先 `rm -f .benchlock/pid` 再 `rmdir`**（pid 文件会让裸 `rmdir`
  失败，否则异常退出会永久泄漏锁）。`run_bench.sh` 用 `trap` 保证。
- 上界：默认等 1800 s（`l02-exp` 可能持锁做 shadow release 编译 + A/B）。
- 分批释放：`--only` 隔离让批次变多，每次 `run_bench.sh` 调用结束即释放锁，
  其他队友可在批次之间插队。

### 2.5 keep-alive 保频

默认在 cpu7 上起一个 `SCHED_IDLE`（无 `chrt` 则 `nice 19`）空转进程：
没有它 `walt` 停在 787 MHz 空闲档，短基准会抓到任意档位；有它 cpu7 稳定在
2.2464 GHz。`--no-keepalive` 关闭（复现 L01 记录的「机会主义 min」现象）。
**注意保频不能消除档位漂移**：`walt` 仍会偶发进入 ~+20% 的快档并持续成块
（见 §2.6），所以 A/B 必须交错。

### 2.6 同批交错 A/B（本机唯一合法的 5–20% 对比形态）

本机 `walt` 有两个相差 ~20% 的时钟档，且档位**成块自相关**（一次转换持续几十个
rep）。null A/B（同二进制）实测：奇偶交错分割的 |中位数差| ≤0.6%，但
**「先跑完 21 个 A 再跑完 21 个 B」的 blocked 对比假阳 ~19%**（k≥11，见
[00-baseline.md §3](00-baseline.md)）。因此：

```text
tools/perf-l02/run_bench.sh --only fast,fast_ss --interleave -w church -N 21 --ks 13,15
tools/perf-l02/run_bench.sh --only fast,fast_memo --interleave -w dup -N 21
```

- 一个锁窗口内交错跑，奇数 rep 按 A→B、偶数 rep 按 B→A，每臂 `-N` 个 rep；
- 每臂仍是**单实现单进程**（隔离仍成立）；
- 结束时 `ab_report.py` 给：两臂 `med_of_min`、比值、**每 rep 配对中位比**、配对
  IQR、每臂胜出 rep 数、前后半比值（查漂移是否漏过配对）；
- 判定用**配对**统计量（每 rep A_i/B_i），不要用两臂区块中位数相减。
- 该方法能把 2.5–8% 的真实效应判出来（`fast_ss` vs `fast` 实测，见 00-baseline §4.4），
  而未交错的区块差会把同一对比虚报成 20–24%。

## 3. 噪声界：`noise_report.py` / `null_ab.py` / `ab_report.py`

```text
tools/perf-l02/noise_report.py 'docs/perf-l02/raw/*noise_church_fast_b*_rep*.txt' --reps 7
tools/perf-l02/null_ab.py 'docs/perf-l02/raw/*nullab_church_fast_rep*.txt'
tools/perf-l02/ab_report.py --a <a_rep*.txt...> --b <b_rep*.txt...> --impl-a fast_ss --impl-b fast
```

- `noise_report.py`：每个 (workload,k,impl) 给 **min-of-N 与 median-of-N 的跨批
  离散度**、单 rep CV、批内前后半分组配对差、min-of-k/median-of-k 的 i.i.d.
  bootstrap CV。
- `null_ab.py`：把同一配置的 rep 序列按 rep 奇偶分成两侧（42 reps → 21/21），
  两侧真值相同，测出的 |中位数差| 就是**假阳性地板**；同时给 **blocked（前 21 vs
  后 21）** 的差与随机均衡分组的 bootstrap p50/p95/max。
- `ab_report.py`：`--interleave` 产出的配对报告（每 rep 比值、配对 IQR、胜出 rep 数、
  前后半比值），由 `run_bench.sh --interleave` 自动调用。

判定规则（L01 轮量化、L02 复验见 [00-baseline.md §3](00-baseline.md)）：

- **< 5%**：本机不可判定；
- **5–20%**：需要**同批交错（ABBA）+ ≥21 reps/侧**；blocked/跨 invocation 对比在这个
  区间不可判（实测假阳 ~19%）；
- **≥ 20%**：同批交错可判；blocked 对比需 ≥25%；
- **≥ 25%**：无条件可信。

## 4. 确定性内存基线：`tools/perf-l02/run_mem.sh`

```text
tools/perf-l02/run_mem.sh                                    # L02 五负载 @ k=11
WORKLOADS=church,conv K=13 ROUNDS=3 tools/perf-l02/run_mem.sh
REPEAT=2 tools/perf-l02/run_mem.sh                           # 两次跑证明确定性
```

`l02l05mem`（`src/bin/l02l05mem.rs`）用计数全局分配器测**分配次数 / 字节 /
大小直方图**，与墙钟完全无关，因此**不需要独占锁**（只要求别在别人计时时开
大编译）；但它是单线程 CPU 负载，仍应避免与计时并行——`run_mem.sh` 不做绑核，
必要时自己 `taskset -c 2` 挪到小核。

三种口径语义（见 `src/bin/l02l05mem.rs` 头注释）：

| 口径 | 含义 |
|---|---|
| `fast(one-shot)` | 每轮新建 `Tycker`，计数 = 该轮完整足迹（arena chunk + Machine 常驻缓冲 + 逐调用草稿） |
| `fast_ss growth` | 一个 `Tycker` 跨轮复用、第 1 轮：**稳态常驻内存下界**（`reset` 不还 chunk、`Vec clear` 保容量） |
| `fast_ss churn` | 后续轮的每轮均值：`Bump::reset` 后真正的新分配（arena 内 bump 不经过全局分配器） |
| `basic` | Box/Rc 参考版逐节点分配计数 |

边界：分配计数是确定性的（同二进制逐字复现），可以证明「某改动减少了 N 次分配 /
多少字节」；但**不能**直接换算成时间——分配少了也可能被别处掩盖。墙钟仍是
必需的证据，两者互为对照。

## 5. 本轮未覆盖 / 已知限制

- 交错 A/B 本轮只做了 `fast` vs `fast_ss` 的 **church 与 dup_deep**（00-baseline §4.4）；
  conv / conv_dup / dup 的同轴对比尚未交错测过，其区块差（≤11%）**不可判**。
  方法即 §2.6，任何队友可复跑。
- 墙钟矩阵 k 上限 15；readme 的 k=17/21 未复测。
- `l02l05mem` 的 L02 负载表与 `l02bench` 一致（church/conv/conv_dup/dup/dup_deep），
  口径齐全（fast / fast_ss growth+churn / basic / fast_memo）；**无缺口**。
  注意它的 doc 注释里提到 `--hist` 但 CLI 实际只有 `--sizes` / `--no-basic`
  （注释陈旧，本轮未改源码）。
- 无硬件计数器，不能做指令级/缓存级归因；分配计数只能归因到分配器层面。
- 深度上限：`basic` 的递归 eval/quote/conv 受栈限（本基线统一
  `L02_STACK_MB=128`）；`fast` 的 `main_with` pretty/`Drop` 路径同样受栈限，
  但本基准只跑 check/nf，不经过该路径。
- 所有数字限于**同一 campaign（2026-10-06 11:22–11:4x UTC）**；跨天/跨 session
  的绝对值须重测。
