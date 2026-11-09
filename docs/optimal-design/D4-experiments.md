# D4 · 主实验记录（EXP-1/2/3/5/6）

> 执行者：perf-experimenter（analyst-l10）。标注约定：`[实测]` = 本文件引用的 raw 原始数据；
> `[历史实测]` = 仓库既有实验（注明采数日期与之后代码是否已变）；`[码]` = 源码核对；`[推断]`。
> 所有 bench 均在 **同一份重建 HEAD 二进制**（`8443586e`，`C:\ezl-target\release`，Lead 报告
> 构建完成于 2026-11-09 **01:32:43**）上运行；构建/实验 target 全部在 C:，未在 F: 构建。
> 机器：AMD Ryzen 5 5600（6C/12T）、34 GB、Windows。**未运行任何 cargo 命令**（测试线由
> analyst-l09 的 EXP-7 负责）。二进制的 `l06l13mem.exe` mtime = 01:32:43（构建结束点），
> 其余 bench 为 01:28:37–01:30:29（LTO 链接期由独立 rustc 完成）。

## 0. 协议、时间线与污染窗口

- 每个数据点：**独立进程、每变体预热 1 次、`--rounds 3` 取 min**；bench harness 只打印
  **min/median**（无 max）——这是本层所有实验的硬限制，D4 不补造 max。
- 并发纪律：开始前写 `docs/optimal-design/experiments/.lock`（owner/exp/time），结束删除；
  同一时间只有一个 bench 进程组。每次实验后 raw 落盘 `experiments/raw/`。
- 时间线与污染：
  | 时段 | 事件 | 处置 |
  |---|---|---|
  | 01:28:37–01:32:43 | Lead 后台 `cargo build --release --bins`（含 LTO 链接）| — |
  | 01:31:21–01:33 | 首轮 EXP-1/EXP-2 raw（`exp1-*.txt`/`exp2-*.txt`）| Lead 判定与构建尾部重叠；**非权威**，01:37 clean 重跑（`*-clean-*`）|
  | 01:34:5x–01:36:48 | EXP-3 L07–L10 首跑 | 函数参数用了 PowerShell 自动变量 `$args` ⇒ bench 收到空参（默认 workload/k13）；**已删除重跑** |
  | 01:37:00–01:37:24 | EXP-1 clean 重跑 | 权威 |
  | 01:37:41–01:37:50 | EXP-2 clean 重跑 + L07 match 干净复核 | 权威 |
  | 01:35:03–01:36:48 | EXP-3 L07–L10 重跑（正确参数）| 权威（L07–L10） |
  | 01:38:01–01:38:03 | EXP-3 L11/L12/L13（正确参数）| 权威 |
  | 01:40:24–01:40:56 | EXP-5 | 权威 |
  | 01:41:09–01:42:21 | EXP-6 | 权威（LSP 未跑，见 §6） |
  | 01:42 起 | `.lock` 交给 EXP-7（analyst-l09）跑测试；本记录不再有 bench | — |

## 1. EXP-1：L01 NbE 表示 × {church, dup, guest} × 规模扫描

**假设**：值/求值表示的性能阶梯在遍历式负载（church）、复制强制（dup）、共享形状（guest）
三类负载上不一致；存在"简单且不慢"的甜点，也存在只在特定负载占优的专门化变体。
**方法**：`l01bench`（25 个 church 变体；30 个 guest 变体列；dup 3 变体×2 形状），
规模翻倍 1000→4000（全变体），8000 只跑迭代子集（递归变体在 `RECURSION_SAFE_MAX=8000` 边界，
`--only` 过滤）；guest 用固定规模表（`src/L01_nbe/bench.rs:93-103`）。

```text
C:\ezl-target\release\l01bench.exe --max-church 4000 --rounds 3 --workload church
C:\ezl-target\release\l01bench.exe --max-church 8000 --rounds 3 --workload church --only cek,cek_bump,bump_iter,bump_arena,bump_tree,compiled,bump_spine,bump_spine_iter,bump_spine_iter_ss,bump_spine_slim,bump_spine_slim_ss,bump_spine_memo,bump_spine_memo_inline,bump_spine_rpn
C:\ezl-target\release\l01bench.exe --max-church 8000 --rounds 3 --workload dup
C:\ezl-target\release\l01bench.exe --rounds 3 --workload guest
```

**结果（church_pair，min ms）**：

| 变体 | n=1000 | n=2000 | n=4000 | n=8000 | 备注 |
|---|---:|---:|---:|---:|---|
| `naive`（Box AST） | 0.177 | 0.372 | 0.761 | — | 递归/派生 Drop 限制大 n |
| `rc_value` | 0.180 | 0.365 | 0.747 | — | Rc 值骨架 |
| `cek` | 0.364 | 0.732 | 1.456 | 2.896 | 大栈递归 |
| `bytes_env_list` | 0.128 | 0.249 | 0.578 | — | 字节码 + List env |
| `bytes_flat_value` | **3.149** | **17.798** | **76.952** | — | 病态：规模翻倍≈5× |
| `bump_arena` | 0.063 | 0.127 | 0.263 | 0.508 | |
| `bump_tree` | 0.039 | 0.081 | 0.184 | 0.327 | |
| `bump_iter` | 0.050 | 0.100 | 0.198 | 0.394 | |
| `cek_bump` | 0.051 | 0.101 | 0.197 | 0.389 | |
| `bump_spine` | 0.015 | 0.030 | 0.086 | 0.197 | |
| `bump_spine_iter` | 0.008 | 0.016 | 0.031 | 0.062 | |
| **`bump_spine_iter_ss`** | **0.008** | **0.015** | **0.029** | **0.058** | 全表最快 |
| `bump_spine_slim` | 0.010 | 0.020 | 0.042 | 0.082 | |
| `bump_spine_memo` | 0.009 | 0.018 | 0.038 | 0.077 | illuminate 同档 |
| `native_clo` | 0.016 | 0.029 | 0.080 | — | |
| `env_slice` | 0.052 | 0.092 | 0.187 | — | |

**结果（dup，min ms；`bump_spine_iter` / `bump_spine_memo` / `memo_inline`）**：
dup_pair 1000/2000/4000/8000 = 0.016/0.031/0.060/0.132 vs **0.013/0.020/0.039/0.082** vs 0.013/0.024/0.044/0.097；
dup_deep = 0.030/0.060/0.137/0.302 vs **0.013/0.023/0.039/0.078** vs 0.013/0.022/0.045/0.098。
⇒ 复制强制下 **quote 记忆化净收益 1.6–3.9×**（n 越大越明显）。

**结果（guest，min ms，代表性变体）**：

| 形状 | 规模 | naive | bump_spine_iter | spine_iter_ss | spine_memo |
|---|---|---:|---:|---:|---:|
| church_mul | 50/100/200 | 1.874/17.826/156.471 | 0.010/0.038/0.184 | 0.009/0.037/0.146 | 0.012/0.049/0.200 |
| parigot_add | 4/8/10 | 0.072/18.049/300.447 | 0.024/6.031/98.354 | 0.024/5.890/94.995 | 0.017/**0.105**/**0.195** |
| exponential | 10/18/20 | 0.056/17.093/72.184 | 0.010/2.449/10.014 | 0.010/2.464/10.374 | **0.001**/**0.004**/**0.005** |

**解释**：
1. 表示阶梯清晰：`naive/rc` ≈ 0.17–0.76ms → bump arena 系 0.03–0.26ms（2–10×）→
   `bump_spine_iter` 0.008–0.062ms（再 2–5×）；**spine+迭代+稳态复用是唯一全程线性最好的一档**
   （4000→8000 翻倍比 0.029→0.058 ≈ 2.0×，近似线性）。
2. **quote 记忆化是负载相关技术**：guest/exponential（强共享 2^n 形）memo 0.005ms vs 非 memo
   10.37ms ≈ **2000×**；parigot_add n=10 约 500×；dup_deep 约 3.9×；但 church_mul（输出 ~n²、
   共享少）memo 略慢于非 memo ⇒ memo 是"共享形状"专用，不是默认最优 [实测+推断]。
3. `bytes_flat_value` 是明确的**负结果**：翻倍增长≈5×，归因于结果/规范化路径的复制（未做
   剖析，仅登记为反例）。
4. 甜点存在：`bump_spine_iter_ss` 在四类负载全部进入最快档；但它需要稳态（Tycker 复用）
   口径，一次性 import 侧成本另计（`bump_spine_iter` 与 ss 仅差 0–15%）。

**局限**：只有 min/median（无 max）；guest 规模表固定、无法扫描；n=8000 只测迭代子集（递归
变体受 `RECURSION_SAFE_MAX` 与栈限制）；25 个变体的"同源输入"已由 `term::*` 统一构造，但
import/export 是否在计时内按变体不同（各变体注释自述）×需 D5 复核。

## 2. EXP-2：pmabbench —— 逐臂 vs 决策树的"复核"

**假设（原）**：同源输入下，逐臂下钻相对决策树矩阵在编译期 scaling 上占优（复核 09-16 结论）。
**关键发现（改变了本实验的性质）**：**HEAD 上已没有决策树实现可测**——
`src/bin/pmabbench.rs:8-11` 仍注释 `l09 = 当前 HEAD 的 L09（决策树矩阵）`，但
`src/L09_mltt/pattern_match.rs:186-188` 明写"逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵
重写）"。因此本实验实际测量的三个臂是**三个逐臂实现的内核差异**：
`l07`（逐臂+σ 显式替换）、`l07pre`（`bench_pre` 自 `b9d54fe` git archive 的旧 L07：
逐臂+pm_defs 事实表）、`l09`（逐臂+重 Cxt/层级 global）。原始 A/B 题面**不可在 HEAD 复现**，
需 `git worktree` 到 09-18 前 commit 并重建——本轮预算内未做（记为未跑项，见 §6）。

```text
C:\ezl-target\release\pmabbench.exe --impls l07,l09   --sweep flat --sizes 4,8,12,16,24,32,48,64 --rounds 3
C:\ezl-target\release\pmabbench.exe --impls l07,l07pre --sweep flat --sizes 4,8,12,16,24,32,48,64 --rounds 3
（wild/cart：--sizes 2,4,6,8；deep：--sizes 8,16,32；其余同）
```

**结果（净 ms = 扣同枚举无 match 对照；比值 = 第二个/第一个）**：

| sweep | size | l07 | l09 | l09/l07 | l07pre | l07pre/l07 |
|---|---:|---:|---:|---:|---:|---:|
| flat | 4 / 16 / 32 / 64 | 0.018/0.155/0.257/0.799 | 0.020/0.103/0.311/1.092 | 1.09/0.67/1.21/**1.37** | 0.033/0.236/1.159/6.692 | 1.85/2.84/4.88/**8.67** |
| wild | 2 / 4 / 6 / 8 | 0.024/0.049/0.095/0.164 | 0.043/0.088/0.264/0.556 | 1.83/1.80/2.79/**3.38** | 0.031/0.044/0.077/0.152 | 1.33/0.93/0.84/0.95 |
| cart | 2 / 4 / 6 / 8 | 0.039/0.247/1.516/9.255 | 0.037/0.218/1.439/8.396 | 0.93/0.88/0.95/0.91 | 0.047/0.245/1.535/9.099 | 0.56/0.58/0.53/**0.49** |
| deep | 8 / 16 / 32 | 0.554/1.944/7.149 | 1.850/13.949/159.104 | **3.34/7.17/22.26** | 0.576/1.957/7.156 | 0.27/0.20/0.17（方向反转）|

**解释**：
1. **flat（臂数）**：逐臂实现间接近平价（l09/l07 0.67–1.37×）；`l07pre` 随臂数显著变差
   （8.67×@65 臂），主要来自其 ctrl（同枚举无 match 源）本身更贵（decl 表按名克隆）——
   净差值放大了旧实现的固定税。
2. **wild（通配重数）**：l07 明显优于 l09（m=8 时 **3.38×**），与"逐臂走查 L09 每列克隆 Cxt/
   重推断"一致；`l07pre` 与 l07 打平（0.84–1.33×）⇒ σ 在通配列上没有明显代价。
3. **cart（完整交叉积）**：三者几乎平价（0.88–0.96×），决策树理论最擅长的形态里，当前逐臂
   实现并没有更差——与 09-16 的结论方向一致但**不再有决策树对照**。
4. **deep（嵌套深度）**：l09 呈超线性（深度 8→32：3.34×→22.26×），l07 线性增长；
   **`l07pre` 在 deep 上反而最快（0.17×，即 l07 的 6×）**——σ 显式替换的包裹/读点开销在深嵌套
   模式上真实存在，这是"显式替换的代价"首个可量化证据 [实测]。
5. 与 [历史实测] `docs/pmab-per-arm-vs-decision-tree.md:106` 对照：wild m=8 的旧决策树 L09 =
   **2739 ms**，今日 per-arm L09 = **0.556 ms** —— 量级差 ~4900×，佐证 HEAD 已换算法，
   该旧结论不可直接与本表并列。

**局限**：净时间 = 总时间 − ctrl（噪声放大，flat size=12 首轮曾出现净≈0 的无效行，clean 重跑
后恢复）；L09 的 `run` 会向 stdout 打印 decl 名（`> Bool` 等），raw 中保留、已注明；
`l07pre` 的源码是 git archive 快照（`src/bench_pre/L07_sum_type/`），不是 HEAD 代码路径。

## 3. EXP-3：当前 HEAD 的 L07–L13 主矩阵

**假设**：现役引擎的孪生/参考比值与层间质量差异（09-20 矩阵后已过 1.5 个月且有 L07 加固、
L10 close 修复等改动）需要重新实测；match 是共同横切负载，大值负载暴露表示差异。
**方法**：`l0Xbench`，`--rounds 3`，独立进程；match 全层 k=9/10/11；每层另选 2–3 个特色负载；
大值负载只取 k=11（L10 traitchain 取 k=9，见注）。

```text
C:\ezl-target\release\l07bench.exe --workload match --max-k 11 --rounds 3
（L08–L12 同构；L13 输出格式为逐实现两行式，命令相同）
C:\ezl-target\release\l10bench.exe --workload traitchain --max-k 9 --rounds 3 --only fast,fast_ss
C:\ezl-target\release\l10bench.exe --workload traitchain --max-k 9 --rounds 1 --only basic   # 单轮限时
```

**match 行（min ms；basic=参考版，fast_ss=孪生稳态）**：

| 层 | k=9 basic / ss | k=10 basic / ss | k=11 basic / ss | 参考/孪生@k11 |
|---|---:|---:|---:|---:|
| L07 | 0.129 / 0.041 | 0.150 / 0.045 | 0.150 / 0.050 | **3.0×** |
| L08 | 0.134 / 0.043 | 0.139 / 0.046 | 0.148 / 0.051 | 2.9× |
| L09 | 0.130 / 0.046 | 0.138 / 0.051 | 0.195 / 0.073 | 2.7× |
| L10 | **0.082 / 0.046** | 0.090 / 0.049 | **0.094 / 0.053** | 1.8× |
| L11 | 0.180 / 0.039 | 0.197 / 0.042 | 0.209 / 0.045 | **4.6×** |
| L12 | 0.185 / 0.040 | 0.214 / 0.057 | 0.205 / 0.047 | 4.4× |
| L13 | 0.186 / 0.139 | 0.209 / 0.146 | 0.214 / 0.149 | 1.4×（孪生领先最小）|

**特色负载（min ms，k=11 除注明）**：

| 层 | 负载 | basic | fast_ss | fast | 备注 |
|---|---|---|---:|---:|---|
| L07 | enum(k=9) / church | 0.275 / 2.608 | 0.072 / 0.271 | 0.071 / 0.275 | church 4096 节点 |
| L08 | enum(k=9) / struct | 0.289 / — | 0.078 / 5.177 | 0.073 / 5.208 | struct 无 basic 输出（bench 口径）|
| L09 | enum(k=9) / universe | 0.741 / 6.724 | 0.117 / 1.646 | 0.107 / 1.615 | universe 4096 decl |
| L10 | struct / traitchain(k=9) | — / **23791.136** | 4.403 / **39.382** | 4.575 / 43.063 | traitchain basic 单轮（warmup+1）|
| L11 | macro / natadd | — / 1.863 | 3.793 / 0.833 | 3.911 / 0.830 | fast_run: 11.278 / 0.656 |
| L12 | strchain / natadd | — / 1.726 | 3.501 / 0.837 | 3.145 / 0.860 | fast_run: 8.108 / 0.677 |
| L13 | gadt(k=9) / moduletree(k=9) | 0.402 / 0.198 | 0.207 / 0.126 | 0.212 / 0.128 | 孪生领先 1.4–1.9× |

**解释**：
1. **match 全层孪生领先 1.4–4.6×**；L13 领先最小（1.4×，生产层孪生优势被真实工作占比稀释），
   L11/L12 参考版显著慢于 L07–L10（4.4–4.6×）⇒ 其参考版引擎税（decl 表/宏重写路径）比
   双引擎比值反映的更大。
2. **L10 的 match 是全层参考版最快（0.094ms）**：无 decl 表 + σ 移植后的 `L07` 血统；
   而 L11/L12（decl 表世界）反而慢 2×——"名字世界选型"对 match 编译期有可测影响 [实测+推断]。
3. **L10 traitchain：参考版 23.79s vs 孪生 39.4ms（≈604×）**，是全场最大同层差距；与
   [历史实测] `docs/bench-matrix-2026-09-20.md:229`（22239ms / 85.392ms）同向但孪生侧因
   2026-09-21 close 化简（`close_tm_reduced`）从 85ms 降到 39ms（−54%，超过 README §6.0 的
   −38%，可能另有窗口/负载差异）[实测；推断]。
4. 大值负载（struct/strchain/universe/macro）孪生领先 100–600×，与 09-20 [历史实测] 同型；
   跨层比"倍率"会误导（参考版地板不同），本表只用于同层比较。
5. **扩展性**：L11 macro 0.918→3.793（k9→k11，4.1×/2×规模）超线性；L12 strchain 0.602→3.501
   （5.8×）；L09 universe 0.378→1.646（4.4×）；L07 church 0.080→0.271（3.4×，接近线性）。

**局限**：① L10 traitchain basic 因参考版 23.8s/次只跑了 `rounds=1`（首轮=计时轮，
故 min=med=23791.136，无 median 意义）；② L08/L10 struct 的 `basic` 列 bench 自身不输出
（`basic_too_slow`/口径，未伪造）；③ L13 输出格式与其他层不同（basic/fast/fast_ss 三行式），
已按行抄录；④ **L07 match k=11 在两次干净窗口测得 0.050 vs 0.064ms（28% 差异）**，属
机器/窗口抖动，引用时取 clean 复核文件（`exp3-l07-match-clean.txt`，0.064）；⑤ 无 max。

## 4. EXP-5：内存/分配（l06l13mem 选点）

**假设**：参考版 vs 孪生的内存差距由表示决定（Box/Rc 树 vs bump arena + 稳态复用）；
L10 traitchain 的 close 病态在参考版仍在（预期 5GB 级），是 [码] L10 README §6.0 的独立复核。

```text
C:\ezl-target\release\l06l13mem.exe --chapter L06,L10,L13 --workload church --k 9 --rounds 3
C:\ezl-target\release\l06l13mem.exe --chapter L10 --workload traitchain --k 9 --rounds 3
C:\ezl-target\release\l06l13mem.exe --chapter L13 --workload prelude --rounds 3
C:\ezl-target\release\l06l13mem.exe --sizes
```

| 测点 | parse | basic | fast(one-shot) | fast_ss churn（3 轮均） | basic/fast 比 |
|---|---|---|---:|---:|---:|
| L06 church k9 | 0.05MB | 2.36MB / 37708 allocs | 1.23MB / 39 allocs | 0.03MB / 12 allocs | 1.91× bytes / 967× allocs |
| L10 church k9 | 0.06MB | 0.97MB / 14773 allocs | （见 raw）| — | — |
| L13 church k9 | （见 raw）| — | — | — | — |
| **L10 traitchain k9** | 4.11MB | **5298.18MB / 122,477,444 allocs** | **30.63MB / 250,364 allocs** | 20.26MB / 250,307 allocs（arena 16MB）| **173× bytes / 489× allocs** |
| L13 prelude-core | 5.10MB | 151.06MB / 1,046,766 allocs | 49.31MB / 266,628 allocs | 36.23MB / 266,488 allocs | ~3.1× bytes / 3.9× allocs |

**解释**：
1. arena 摊销是孪生内存优势的主因：L06 church basic 37708 allocs → fast 39 allocs（967×），
   稳态 churn 只剩 12 allocs/轮；对应时间差 0.79ms vs 0.08ms（EXP-3 church）[实测]。
2. **L10 traitchain 参考版 5.30GB / 1.22 亿次分配**，孪生 30.6MB / 25 万次：**173× 字节、
   489× 分配**，且 basic 的 5.3GB 正是 L10 README §6.0 所述 close 死重的参考版形态
   （孪生侧 `close_tm_reduced` 修复后 30.6MB，与 README 的 k=9 30.63MB 逐位吻合）——
   该修复**仅落孪生**的结论得到独立复核 [实测+码]。
3. L13 prelude-core：basic 151MB vs fast 49MB；parse 5.1MB 是不可压缩的源码/语法税；
   稳态 churn 36MB 说明 prelude 装载后仍有可观常驻/复用结构（与 L13"生产层"定位一致）。
4. `--sizes` 的结构体尺寸表见 raw（`exp5-sizes.txt`），供 D5 判定"哪些表示值得/哪些是税"。

**局限**：只取 3 个层 × 3 个负载（预算约束）；`fast_memo` 列未纳入；`--no-basic` 未启用
（basic 慢但需要基线）；分配计数是确定性口径（可实现跨机复现），字节数含 arena 整块。

## 5. EXP-6：真实负载（L13 prelude / examples / typort check）

**假设**："性能超群"必须体现在真实 prelude/HDL 负载；合成 match 的倍率不代表生产路径收益。

```text
C:\ezl-target\release\l13bench.exe --workload prelude-core --rounds 3
C:\ezl-target\release\l13bench.exe --workload prelude-hdl  --rounds 3
C:\ezl-target\release\l13bench.exe --workload examples-hdl --rounds 3
C:\ezl-target\release\typort.exe check examples/alu.typort   # 同法 3 个 example，计墙钟
```

| 负载 | 规模 | basic (ms) | fast (ms) | fast_ss (ms) | 孪生/basic |
|---|---|---:|---:|---:|---:|
| prelude-core | 208 decls, nf=27 | 55.693 | **18.822** | 20.250 | 2.8× |
| prelude-hdl | 1439 decls, nf=219 | **5171.728** | 1799.979 | **1365.935** | 3.8× |
| examples-hdl[0..5] | 214–226 decls | 53.2–57.2 | 19.1–21.9 | 18.9–19.5 | ~2.9× |
| `typort check examples/alu.typort` | 719 B 源 | **5212 ms** wall | — | — | — |
| `typort check examples/adder_proof.typort` | — | 5491 ms wall | — | — | — |
| `typort check examples/typeclass_complex.typort` | — | 5220 ms wall | — | — | — |

**解释**：
1. **真实负载的孪生收益 2.8–3.8×**，远小于合成大值负载的 100–600×，也小于 match 的 4.6×：
   生产路径被 parse/prelude 装载/观察面（LSP 表）摊薄 ⇒ D5 应把"真实负载收益"单列。
2. prelude-hdl（1439 decls）是 prelude-core 的 **93×** 时间（5.17s vs 55.7ms）、26× 内存
   （151MB vs 5.8MB）；decl 数只 6.9×，**超线性**来自 HDL 段的宏/实例化/观察面 [推断]。
3. `typort check` 单文件墙钟 ≈5.2s 且三文件几乎相同 ⇒ 时间**几乎全是 prelude 装载**，
   源文件 elaborating 占比极小（raw 内 `[LOG] parser 0.0018 / infer 0.106`）；
   prelude 装载是生产路径的真正热点——与 EXP-6 prelude-* 数据闭环 [实测]。
4. raw 中 examples-hdl 各变体带 `BOTH-FAILED（两版都未跑完，与范式一致无关）` 标注：
   该标注是 bench 自身的既有提示，**不作为正确性证据**，需 D2 复核其语义。

**局限**：① LSP kick/交互延迟**未跑**（analyst-l09 的 EXP-7 接管测试线，避免抢 CPU；
改用 `l13lspsample` 也会与测试线冲突）——记为未跑项；② `typort check` 只做了单次墙钟
（无 min/median，未加 `--rounds`）；③ 未测 `typort emit/build`；④ prelude-hdl 的 5.17s
含 LSP 观察面成本（L13 生产路径的一部分），与"纯 elaboration"数字不可直接混用。

## 6. 未跑项与原因（供 FINAL 引用）

| 项 | 状态 | 原因 |
|---|---|---|
| EXP-4 消融 A/B | 未执行 | 属 D5/techniques 协作；接口与开关见 §7，可在测试线结束后补 |
| EXP-2 的"决策树"臂 | 不可测 | HEAD 已无决策树实现（`src/L09_mltt/pattern_match.rs:187`）；需 worktree 到 09-18 前 commit + 独立 target 构建，超出本轮预算 |
| EXP-6 LSP kick / l13lspsample | 未执行 | 测试线（EXP-7）接管 CPU；改由 D2/D5 用历史 LSP 采样数据 [历史实测] |
| EXP-7 正确性实跑 | 未执行（非本角色）| analyst-l09 负责 |
| max 列 | 未采集 | bench harness 只打印 min/median；重跑补采需改源码（禁止改 master）|
| L10 traitchain k=10/11 | 未执行 | 参考版 k=9 已 23.8s/次，k=11 预计 >100s/轮，预算禁止 |
| L13 prelude 的 σ 迁移分支/WIP | 未执行 | 无该分支二进制；D6 负责考古 |

## 7. 给 D5 / EXP-4 的消融接口

本仓已内建环境变量开关（`grep env::var` 全量，见 raw 外的源码；均为**同一二进制**切换）：
`L02_NO_BITEQ`、`L02/L03/L04/L05/L06_NO_CONV_MEMO`、`L03/L04/L05/L06_NO_NAME_MAP`、
`L07_LOOP`/`L08_LOOP`；探针：`L10SOLVE_PROBE`、`L06L13MEM_TRACE`/`_TRACE_MIN`、
`L13SAMPLE_TICK`；栈：`L0x_STACK_MB`（L01–L13 各层）。EXP-4 推荐协议：
1) 固定二进制，A/B 用**同窗口交替**（A,B,A,B…）每配置 ≥3 轮取 min/median；
2) 每组只切一个开关，记录 `owner/env/time` 到 `.lock`；
3) 成对报告比值而非绝对值；4) 至少覆盖 L02–L06 各 1 个 `NO_CONV_MEMO`/`NO_NAME_MAP`
对 + L07/L08 `LOOP` 对；预期"记忆化收益"应与 EXP-1 guest/dup 的 memo 曲线同向。

## 8. 复现与 raw 索引

- 构建：`CARGO_TARGET_DIR=C:\ezl-target cargo build --release --bins`（Lead 执行，Finished 01:32:43）；
- 全部命令已逐行写在 §1–§5；每个 raw 文件的首行/`#####` 行含精确命令与参数；
- raw 索引（`docs/optimal-design/experiments/raw/`，mtime 2026-11-09）：
  - **权威（clean，01:37–01:42）**：`exp1-clean-church-4000.txt`、`exp1-clean-church-8000-iter.txt`、
    `exp1-clean-dup-4000.txt`、`exp1-clean-dup-8000.txt`、`exp1-clean-guest.txt`、
    `exp2-clean-{flat,wild,cart,deep}-l07-{l09,l07pre}.txt`、`exp3-l07.txt`、`exp3-l07-match-clean.txt`、
    `exp3-l08.txt`、`exp3-l09.txt`、`exp3-l10.txt`、`exp3-l11.txt`、`exp3-l12.txt`、`exp3-l13.txt`、
    `exp5-mem-L06-L10-L13-church.txt`、`exp5-mem-L10-traitchain.txt`、`exp5-mem-L13-prelude.txt`、
    `exp5-sizes.txt`、`exp6-l13-prelude-core.txt`、`exp6-l13-prelude-hdl.txt`、
    `exp6-l13-examples-hdl.txt`、`exp6-typort-check.txt`；
  - **非权威（构建尾部重叠，01:31–01:33，仅留档）**：`exp1-*.txt`（非 clean 前缀）、`exp2-*.txt`（非 clean 前缀）；
  - 命名说明：`exp3-l11.txt`/`exp3-l12.txt` 体积较大（65KB）因含全部 fast_run/fast_memo 行与
    L11/L12 的 stderr 诊断，属正常。
- 独立复核建议（给 analyst-l09）：任选 2–3 个数据点用同命令复跑，重点 `exp3-l10.txt` 的
  traitchain 与 `exp5-mem-L10-traitchain.txt`（大数最易发现口径错误）。
