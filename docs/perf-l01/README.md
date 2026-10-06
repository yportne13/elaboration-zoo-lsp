# L01 本机性能基线（aarch64 / Android Termux）

本目录是 L01（`src/L01_nbe`，NBE 22 变体研究层）在**本机**
（aarch64, big.LITTLE, governor=`walt`）上的可信计时基线，作为后续优化实验
的对照。所有数字均由 `tools/perf-l01/run_bench.sh` 产出，raw stdout 存在
`raw/`（文件名带时间戳），结论写在 `00-baseline.md`。

`src/L01_nbe/**` 与 `src/bin/l01bench.rs` 在本轮**只读冻结**：变体形态一旦
改动，本目录的基准叙事即作废，必须重跑。

## 为什么需要这套口径

本机没有 `perf` / `valgrind` / `hyperfine`，`walt` governor 下实测
`scaling_cur_freq` 在约 0.8–2.2 GHz 间摆动（`scaling_cur_freq` 仅为
`cpuinfo_max_freq` 的 59–67%），cgroup 无 CPU 配额（`Cpus_allowed=0-7`）。
单次 `l01bench` 的 min-of-rounds 会把这些频率漂移当成"算法差异"。
因此本目录的数字遵守统一协议：

1. **绑核**：所有计时经 `taskset -c 7`（cpu7 = 最大核，`cpuinfo_max_freq`
   2995200 kHz）。全队统一用 cpu7。
2. **min-of-N 整轮重复**：同一命令完整跑 N 次（默认 N=7），每个
   (workload, size, variant) 取 N 次进程内 min 的**最小值**；同时报告
   这 N 个 min 的中位与相对离散度 `(max-min)/min`。任务内 `--rounds`
   只是单进程内轮数，不替代整轮重复。
3. **keep-alive 保频**（默认开）：计时窗口内另起一个 `SCHED_IDLE`
   （无 `chrt` 时退化为 `nice 19`）空转进程钉在同一核上，让 `walt` 停在
   稳定档位（实测 2246 MHz），而不是空闲 787 MHz。没有它时同配置跨批
   min-of-7 会漂 ~20%；有它时降到 ~1–8%。代价是绝对时间慢约 18%
   （量的是稳定档而不是偶发最高档）。`--no-keepalive` 可关掉，用于复现
   旧的机会主义 min。
4. **独占计时**：任何计时命令前先原子取锁
   ```bash
   mkdir docs/perf-l01/.benchlock 2>/dev/null   # 成功才可计时
   ...                                          # 计时
   rm -f docs/perf-l01/.benchlock/pid; rmdir docs/perf-l01/.benchlock
   ```
   拿不到锁就 `sleep 10` 重试，**禁止并行计时**（另一 agent 的计时会污染
   频率/温度状态）。`run_bench.sh` 已内建该协议：`trap` 释放（先删 `pid`
   再 `rmdir`，否则 `rmdir` 非空目录必然失败）、写入 `$LOCK/pid` 持有者，
   并在持有者 pid 已死时**自动接管 stale 锁**。锁目录是 task-1 的保留
   约定，请勿删除。
5. 环境指纹（kernel / CPU / governor / cur_freq / 二进制 sha256 / rustc /
   release profile / stack / keepalive 模式）在每个 batch 前写入
   `<ts>_<tag>_env.txt`。

**噪声界**：同配置整轮重复得到的 min 相对离散度决定"低于多少百分比不可
判定"。具体数字与判定阈值见 `00-baseline.md` 的"噪声界"一节——**报告任何
小于该阈值的差异都必须先看离散度，否则不可判定**。

## 构建与运行

```bash
cargo build --release --bin l01bench        # 不要改 Cargo.toml
tools/perf-l01/run_bench.sh --max-church 8000 --only bump_spine_iter,bump_spine --workload church
tools/perf-l01/run_bench.sh -w dup --only bump_spine_iter,bump_spine_memo --max-church 8000
tools/perf-l01/run_bench.sh -w guest --max-church 8000 --only bump_spine_memo,bump_spine_iter --reps 3 --rounds 5
tools/perf-l01/run_bench.sh --max-church 64000 --only cek,cek_bump,bump_iter,bump_spine_iter,bump_spine_slim,bump_spine_iter_ss --reps 7 --rounds 3
```

`run_bench.sh` 参数：`--max-church/-n`（规模从 1000 翻倍到该值）、
`--rounds/-r`（单进程内轮数，默认 3）、`--reps/-N`（整轮重复次数，默认 7）、
`--only`（逗号分隔透传）、`--workload/-w`（`church|dup|guest|all`）、
`--cpu`（默认 7）、`--stack-mb`（默认 128，即 `L01_STACK_MB`）、
`--sizes`（仅显示过滤，如 `4000,8000`）、`--tag`（raw 文件名标签）、
`--no-keepalive`（关闭保频空转，见上）。
输出：每个 (workload,size) 一张表，列为
`min_ms`（N 次整轮 min 的最小值）、`med_of_min`、`max_min`、`spread%`；
`_agg.tsv` 里对应 `min_ms` / `med_ms` / `max_ms` / `spread_pct`。

**比较时必须用 `med_ms`（`med_of_min`），不要用 `min_ms`。** `min` 会随机
抓到 walt 的瞬态快档，跨批复现性只有 ~20%；中位数把跨批压到 ≤3%。判定阈值
见 `00-baseline.md` §3.3：**单次 7v7 比较 <20% 不可判定，<5% 即使 21 reps/侧
也不可靠，≥25% 无条件可信**。A/B 应在同一批内按 rep 交错，并在同批插一个
对照变体做归一化。

## 口径细节（来自 `src/L01_nbe/bench.rs`，勿凭记忆改）

- **只计 `normalize`**：入参编码（`to_vec`/`into_rc`/`import`）与结果
  `export`、正确性断言都在计时窗口外。
- **预热 1 次 + `--rounds` 轮**，报告 min/中位。
- **arena 变体跨轮复用**（`ListArena` 追加式、下标不过期）= 稳态口径；
  spine 系的 `_ss` 行（`bump_spine_iter_ss`/`bump_spine_slim_ss`）是
  `Machine` + `Bump::reset()` 的稳态测量口径，算法与同名变体一致。
- **大 n（> 8000）只有迭代变体出赛**（`cek`/`cek_bump`/`bump_iter`/
  `bump_spine_iter`/`bump_spine_slim`/`bump_spine_iter_ss`）；其余变体
  构造/求值/比较是递归链，此规模栈溢出。大 n 段用迭代构造 + 迭代比较
  （`bench_cek_deep`）。
- **`L01_STACK_MB`**：`l01bench` 在 `stack_size = L01_STACK_MB << 20` 的
  线程里跑 bench，默认 `128`（MB）。`=0`/非法值视为未设置。实测 bump 系
  迭代变体 4MB 即可跑到 51 万；只有 `cek`（`Value` 派生 Clone/Drop 对深
  Box 树递归）需要大栈。**不同 stack 大小不改变被计时代码路径**，但在
  内存紧张机器上会改变缺页行为——本目录全部数字统一 128MB。
- **分配器 = mimalloc**（`src/bin/l01bench.rs` 的 `#[global_allocator]`），
  与生产 `typort` 一致；Windows 默认堆在这类小分配密集负载上慢约 4 倍，
  本机对照时必须保持 mimalloc。
- **release profile**：`lto = true`, `codegen-units = 1`（`Cargo.toml`
  `[profile.release]`）。基准二进制不链 `elaboration_zoo_lsp` 库，只
  `#[path]` 直编 `src/list.rs` 与 `src/L01_nbe/`。

## 负载

- `church`（默认）：`church_pair(n) = add (church n) (church n)`，正态形
  `church(2n)`，线性，规模 `1000,2000,...,max-church`。
- `dup`：`dup_pair(n)`（同一教堂数被 quote 强制 2×）/`dup_deep(n)`（4×），
  测 quote 记忆化轴。
- `guest`：`church_mul`（n=50/100/200，输出 ~n²）、`parigot_add`
  （n=4/6/8/10，正态形 ~2^n）、`exponential`（n=10/14/18/20，2^n 且高度
  共享）——规模上限由 `bench.rs` 写死，**不要**擅自放大 parigot/
  exponential，会指数爆炸。

## 复现注意

- 干净 shell 直接可跑；脚本自带 `cd` 到仓库根。
- 若 `target/release/l01bench` 不存在，脚本报错并提示先
  `cargo build --release --bin l01bench`（脚本不触发编译，避免与 cargo
  锁/他人构建互相阻塞）。
- 单次进程退出即释放资源；`run_bench.sh` 的锁在 `trap` 中释放（先删
  `.benchlock/pid` 再 `rmdir`），异常退出也不会留下锁；即便残留，下一个
  计时者发现 pid 已死会**自动接管**。手动清理：确认无进程在跑后
  `rm -f docs/perf-l01/.benchlock/pid` 再 `rmdir docs/perf-l01/.benchlock`。
- 频率与环境指纹会随时间变化：**跨天/跨批次的数字不可直接比较**，同批
  内的相对排序才是结论；每个 batch 的 `_env.txt` 是追溯依据。
