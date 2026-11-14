# smalltt → L07–L10 性能差距详细分析（2026-11-14）

> 数据基础：同机（AMD Ryzen 5 5600 / 32 GB / Windows 10；rustc 1.98.1 release + mimalloc；
> smalltt 用本机 GHC 9.4.8 构建，RTS 默认 -A64M -s -N8）。计时为 min-of-rounds
> （smalltt 3–5 轮 :r，我们 1–5 轮），全部串行、安静窗口（agent 已停止）。
>
> 相关文档：迁移与可行性 docs/smalltt-bench-2026-11-14.md（§11 为同机对照）、
> 上游事实 docs/smalltt-source-notes.md、三族移植笔记 docs/smalltt-port-notes-*.md。
> 原始数据：target/smalltt_bench/final|same_machine/（我们的 CSV）、
> F:\projects\hermes\_ref\smalltt-bench*/（smalltt 日志）、F:\projects\hermes\_ref\alloc-bench/（分配计数）。

## 0. TL;DR（差距排序）

| # | 差距 | 量级（同机） | 主要原因（证据强度） |
|---|---|---|---|
| 1 | **pairTest 形态**（dup 嵌套类型） | twin ≥1800× 分配 / ~2500× 时间；smalltt 31 层 <1 ms，我们 20 层 2.2 s | 无 glued evaluation / meta solution sharing：类型每层被 quote 全展开，节点 2^k（**强**：分配字节 4.31 GB vs 2.36 MB） |
| 2 | **stlc 吞吐**（大文件 + 大量隐式 meta） | twin **5.3–6.8×**、ref 26.8–28.9× | 每 def 分配 **3.0 MB vs 0.46 MB（6.4×）**；每个隐式元变量/类型注解的 quote+close_ty 反复分配（**强**：分配量与时延同向；**中**：具体热点待 per-def 采样确认） |
| 3 | **TreeConv 转换** | twin 1.5–2.9×、ref 6.8–8.6× | 无有界近似转换（同 head spine 先试、失败再展开）：深度 15→23 我们 per-leaf 0.42→0.81 µs、smalltt 0.27→0.35 µs，差距随规模放大（**中强**） |
| 4 | **NatConv 转换** | twin 1.36×/1.83×/**0.84×**（1M/5M/10M）、ref 23.8–46.6× | 孪生版分配量已≈smalltt（0.85×），慢在每步常数与分配吞吐；ref 则是 16M 次小分配/1M 步（**强**） |
| 5 | **nf 族** | twin **0.33–0.71×（更快，forceTree）**；nftree 1.29–1.67× | nf 路径已是唯一全面持平/反超的族；nftree 慢在完整 term 构建的分配吞吐（3.3 vs 6.9 GB/s）（**中强**） |
| 6 | **vecTest** | twin 3.33×、ref 15.7× | 双方都是二次型（meta occurs checking），我们常数大约 3×；分配 346 MB vs ~45 MB（**中**） |
| 7 | **参考版引擎本身** | ref/twin = 2.4–28.4× | 树形 Val/Tm 每步堆分配（natconv 1M：**1600 万次分配** vs 孪生 483 次）；大档栈溢出（ref 5M/10M）（**强**） |

一句话：**优化内核（twin）在「求值/归一化」类已与 smalltt 同量级，差的是「elaboration 的每-def 常数」（stlc）和「meta/展开控制」（pairTest/TreeConvM），以及参考版引擎的每步分配。**

## 1. 口径与数据

### 1.1 同机计时（ms；每格 = 我们最好层 / smalltt 本机）

| 用例 | 我们 ref 最好 | ref/smalltt | 我们 twin 最好 | twin/smalltt |
|---|---:|---:|---:|---:|
| natconv 1M / 5M / 10M | 1724.6 / 8110.6 / 14204.9 | 38.3× / 46.6× / 23.8× | 61.1 / 319.2 / 499.8 | 1.36× / 1.83× / **0.84×** |
| treeconv 15 / 18 / 19 / 20 / 23 | 60.9 / 543.6 / 1197.0 / 2373.3 / — | 6.8× / 7.2× / 8.2× / 7.1× / — | 13.7 / 119.5 / 347.5 / 720.3 / 6828.4 | 1.52× / 1.58× / 2.38× / 2.14× / 2.33× |
| treeconvm 15 / 18 / 19 / 20 | 69.5 / 663.2 / 1277.0 / 2791.4 | 7.7× / 8.6× / 8.5× / 7.8× | 20.0 / 175.1 / 431.4 / 844.0 | 2.22× / 2.28× / 2.87× / 2.37× |
| forcetree 15 / 18 / 19 / 20（nf-only） | 8.3 / 106.0 / 231.4 / 407.6 | 0.92× / 1.26× / 1.47× / 1.03× | 3.0 / 39.8 / 111.7 / 172.6 | **0.33× / 0.47× / 0.71× / 0.44×** |
| nftree 15 / 18 / 19 / 20（nf-only） | 16.8 / 156.2 / 361.5 / 746.7 | 4.19× / 3.69× / 4.37× / 3.92× | 6.4 / 64.1 / 138.2 / 245.6 | 1.59× / 1.52× / 1.67× / 1.29× |
| vecTest 960 | 353.6 | 15.7× | 75.0 | 3.33× |
| stlc 40 / 80 份 | 3676.5 / 7412.7 | 26.8× / 26.9× | 727.8 / 1677.4 | 5.30× / 6.10× |
| stlcl 40 / 80 份 | 3422.9 / 6891.4 | 28.9× / 28.2× | 801.9 / 1325.5 | 6.77× / 5.42× |
| stlcs 96 / 192 份 | 747.9 / 1459.1 | 12.7× / 28.8× | 142.5 / 340.0 | 2.41× / 6.70× |
| pairTest 20（同尺寸 smalltt <1 ms；31 层也 <1 ms） | 5400.5 | — | 2163.3 | **≥2500×** |

> stlc 家族 smalltt 一侧在两次窗口（3 轮/5 轮）可差 15–100%（小文件尤甚）；本表 stlc 采用
> 5 轮 pass 的 min（stlc10k 316.7 / stlc5k 157.8 / lessimpl10k 281.7 / lessimpl5k 133.2 /
> small5k 28.6 / small10k 62.9 ms）；报告 §11.4 用的是 3 轮 pass，比值方向一致。

### 1.2 家族级汇总（min–median–max）

| 家族 | twin/smalltt | ref/smalltt |
|---|---:|---:|
| natconv | 0.84–1.36–1.83× | 23.8–38.3–46.6× |
| treeconv | 1.52–2.14–2.57× | 6.76–7.12–8.20× |
| treeconvm | 2.22–2.33–2.87× | 7.71–8.18–8.64× |
| forcetree（nf） | 0.33–0.45–0.71× | 0.92–1.15–1.47× |
| nftree（nf） | 1.29–1.56–1.67× | 3.69–4.05–4.37× |
| vecTest | 3.33× | 15.69× |
| stlc（full/lessimpl） | 5.30–5.76–6.77× | 26.78–27.56–28.89× |
| stlcSmall | 2.41–4.55–6.70× | 12.66–20.70–28.75× |

### 1.3 逐单位成本（把规模消掉）

| 用例 | 单位 | smalltt 本机 | 我们 twin 最好 | 我们 ref 最好 |
|---|---|---:|---:|---:|
| natconv 1M | ns/β-step | 45.0 | 61.1 | 1724.6 |
| natconv 10M | ns/β-step | 59.7 | 50.0 | 1420.5 |
| treeconv 15 | ns/leaf | 275 | 418 | 1859 |
| treeconv 20 | ns/leaf | 321 | 687 | 2263 |
| treeconv 23 | ns/leaf | 349 | 814 | — |
| treeconvm 20 | ns/leaf | 340 | 805 | 2662 |
| forcetree 20 | ns/leaf(evals) | 377 | 165 | 389 |
| nftree 20 | ns/leaf(term) | 182 | 234 | 712 |
| vecTest 960 | ns/cons | 23438 | 78097 | 368384 |
| stlc 80 份 | µs/def（3120） | 101.5 | 537.6 | 2375.9 |
| stlcSmall 192 份 | µs/def（3648） | 17.2 | 93.2 | 400.0 |

读法：
- **转换（treeconv/treeconvm）**：smalltt 每叶 ~0.28–0.35 µs 且随深度几乎不涨；我们 twin 0.42→0.81 µs，
  **gap 随规模从 1.5× 涨到 2.3×**。这是「近似转换 + 缓存局部性」的双重差距，不是常数差。
- **stlc**：我们每 def 的 elaboration 成本是 smalltt 的 5.3×（twin）/ 23.4×（ref）；stlcSmall 是 5.4×（twin）。
- **nf**：forcetree 我们每叶更便宜（0.44×），nftree 每叶 1.29×——差别在「折叠到小值」 vs「构造完整 term」。

## 2. 归因一：参考版 vs 孪生版（同层内的 2.4–28.4×）

这是最容易定位的部分：两个引擎跑**同一算法**，差异在表示与执行机制。

### 2.1 分配计数（SMALLTTBENCH_ALLOC=1，单轮）

| 用例 | 我们 ref 分配次数 | 分配字节 | 我们 twin 分配次数 | 分配字节 | ref/twin 字节 |
|---|---:|---:|---:|---:|---:|
| natconv 1M | **15 975 741** | 1.02 GB | **483** | 268 MB | 3.8× |
| treeconv 18 | 15 216 141 | 981 MB | 649 | 438 MB | 2.2× |
| treeconv 20 | 75 512 783 | 4.25 GB | 657 | 1.76 GB | 2.4× |
| forcetree 20 | 35 663 212 | 1.89 GB | 329 | 1.08 GB | 1.8× |
| nftree 20 | 20 983 078 | 1.36 GB | 1 003 | 806 MB | 1.7× |
| stlc 80 | **268 513 690** | 16.0 GB | 958 540 | 9.26 GB | 1.7× |
| stlcs 192 | 51 202 581 | 3.14 GB | 474 741 | 3.54 GB | 0.9× |
| pairTest 20 | 117 444 376 | 7.15 GB | 687 | 4.31 GB | 1.7× |
| vecTest 960 | 12 087 697 | 834 MB | 38 371 | 346 MB | 2.4× |

**关键观察**：孪生版把分配次数压到数百～百万级（bump arena：一次拿大 chunk，值用 arena 内
指针 V 表示；Tycker::bench_check 只 bump.reset() + clear_round()），而参考版按「每个中间值一次
堆分配」走（1M 步 NatConv = 1600 万次分配，约 16 次/步；stlc80 = 2.7 亿次）。参考版时间/字节
≈ 0.6–2.2 GB/s（受分配与指针追逐限制），孪生版虽然字节数仍大但**分配事件**几乎为零。

> 这也解释了为什么 ref 在大档会栈溢出：树形 Val/Tm 的递归栈帧 + 每步物化值；
> L07/L08 ref natconv **5M 即 8 GB 栈溢出**，L09 ref 10M 溢出，L10 ref 10M 可跑（14.2 s）。
> 孪生版到 10M（twin 500 ms）无栈问题。

### 2.2 ref/twin 比值的形态

| 用例 | ref/twin |
|---|---:|
| natconv 1M / 10M | 28.2× / 28.4× |
| treeconv 15 / 18 / 20 | 4.4× / 4.5× / 3.3× |
| treeconvm 20 | 3.3× |
| forcetree 20 / nftree 20 | 2.4× / 3.0× |
| vecTest 960 | 4.7× |
| stlc 80 / stlcl 80 / stlcs 192 | 4.4× / 5.2× / 4.3× |
| pairTest 20 | 2.5× |

natconv 的 28× 是离群点：单次转换有 100 万步、每步都新建/匹配 Val，ref 的每步常数被放大到极致；
nf 族只 2.4–3.0×，因为 nf 路径本来就要构造大 term，ref 与 twin 的表示差异被摊薄。
结论：**参考版是语义 oracle，不应作为性能基线**；对外性能数字应以孪生版为准。

## 3. 归因二：孪生版 vs smalltt（真正的性能差距）

### 3.1 转换族（natconv / treeconv / treeconvm）

| 证据 | natconv | treeconv(20) | treeconvm(20) |
|---|---|---|---|
| 时间 gap（twin） | 1.36–1.83×（10M 0.84×） | 2.14× | 2.37× |
| 分配字节 vs smalltt | 0.85×（1M） | 0.70× | — |
| 分配吞吐（GB/s） | 4.4 vs 7.0 | 2.4 vs 7.5 | — |
| per-leaf 成本 | — | 687 vs 321 ns | 805 vs 340 ns |

- **分配量不背锅**：twin 的分配字节甚至更少（0.70–0.85×），但时间更慢 ⇒ 差在**每字节/每步的执行成本**：
  Rust 逐个对象分配 + Drop，vs GHC bump allocation + 并行 GC（smalltt 分配吞吐 4.6–8.2 GB/s，我们 2.4–5.5 GB/s）。
- **treeconv 的 gap 随规模放大**（1.52×@15 → 2.33×@23；per-leaf 418→814 ns，smalltt 275→349 ns）：
  我们做**完整**转换（每叶都展开比较），smalltt 有 rigid/flex 两态**有界近似转换**（同 head spine 先试、
  失败再展开），且值表示更紧凑、缓存局部性更好。TreeConvM（含 meta）同样受益，故 gap 2.2–2.9×。
- **natconv 的 10M 反超（0.84×）**：步数足够大时 twin 的每步常数（~50 ns）已低于 smalltt（~60 ns）；
  1M/5M 时我们慢 1.4–1.8×，说明小规模下固定/缓存效应占比更高。对规模敏感，报告需同时给三档。

### 3.2 nf 族（ForceTree / NfTree）

| 指标 | forcetree 20 | nftree 20 |
|---|---|---|
| 时间（twin/smalltt） | **0.44×** | 1.29× |
| 分配字节（twin/smalltt） | 1.08 GB / 3.31 GB = **0.33×** | 0.81 GB / 1.30 GB = 0.62× |
| 分配吞吐 | 6.3 vs 8.4 GB/s | 3.3 vs 6.9 GB/s |

- **ForceTree**：我们的 eval 直接把树折叠成 Bool，不做 glued-eval 的双分支；smalltt 的 glued evaluation
  反而要多分配（3.3 GB vs 我们 1.1 GB），所以 twin 反超（0.33–0.71×）。
- **NfTree**：要构造完整 term（4.19M 节点），我们的 quote 分配吞吐只有 smalltt 的 ~48%（3.3 vs 6.9 GB/s），
  导致 1.29–1.67× 的差距。这是**表示/分配器**层面的差距，不是算法。
- 参考版在 nftree 是 3.7–4.4×：ref 的 quote 每节点物化更多结构（21M 次分配）。

### 3.3 stlc 吞吐（5.3–6.8×）——差距最大且最值得优化

| 证据 | smalltt stlc10k | 我们 stlc80（L08 twin） | 比值 |
|---|---:|---:|---:|
| 时间 | 316.7 ms | 1677.4 ms | 5.30× |
| defs | 3120 | 3121 | ≈1 |
| 分配字节 | 1.45 GB | 9.26 GB | **6.4×** |
| 分配/def | 0.46 MB | **2.97 MB** | **6.4×** |
| metas（smalltt 打印） | 68 000（21.8/def） | —（未暴露） | — |

- 时间与分配量**严格同向**（5.3× vs 6.4×），且 stlcs（19 defs/份的简版）分配/def 也是 12.6×（twin）——
  说明差距集中在**每个 def 的 elaboration 路径的分配量**，而非某个特定模板特性。
- 按当前实现，每个 def 的高分配来源（代码阅读，待 per-def 采样确认）：
  1. fresh_meta：每个隐式实参插入一次 meta，都会 quote 该 meta 的期望类型（Church 编码的类型项可达
     几十～几百节点）并 close_ty(cxt.locals.clone(), …) 后再 eval；stlc 模板每 def 有大量隐式参数
     （smalltt 同规模 21.8 metas/def）；
  2. check 的注解检查 / check_universe、insert 对 Pi 链逐层 force + closure_apply；
  3. unify_catch 每层 Val 的物化/克隆与 force 展开（twin 的 V 指针缓解了部分，但类型项仍反复构造）；
  4. 每个 def 新建/更新上下文（L07/L08 的 decl 表与 locals）带来的常数。
- 对照 smalltt：contextual metas 直接以 lambda 抽象（不做 per-meta quote+eval 的物化）、eta-short
  meta solutions、有界近似转换、glued evaluation 控制展开——这些正是 stlc/隐式密集负载的关键。
- **方向性验证**：full stlc 与 lessimpl 的相对差距在两边一致（我们 twin 1677/1326 = 1.27×；
  smalltt 316.7/281.7 = 1.12×），说明用例翻译保真；差距来自内核每 def 常数，而非用例形状。

### 3.4 pairTest（≥2500×）——结构性缺口，不是常数差

| 指标 | smalltt（20/31 层） | 我们 twin 20 层 | 我们 ref 20 层 |
|---|---:|---:|---:|
| 时间 | <1 ms（打印 0 s） | 2163 ms | 5400 ms |
| 分配字节 | 2.2–2.4 MB | **4.31 GB** | 7.15 GB |
| 增长 | 平坦（31 层仍 <1 ms） | ≈2.05×/层（10→15→20：2.85→133→5400 ms） | 同左 |

- 机理：pairTest 的每个 let x_{i+1} = dup x_i 让 x_i 的**类型**长度翻倍（Pair 嵌套）。smalltt 的
  meta solution 保持「最小展开」形态（如 ?0 := Pair ?1 ?1 这样的小项）且近似 occurs 检查不展开顶层
  def，所以 30 层仍是小常数；我们的 fresh_meta/quote 把类型全展开后物化，节点数 2^k → 分配 4.3 GB、
  时间 2.2 s（twin）且按 2.05×/层指数增长。
- 这是**唯一一个「换更快的分配器/更紧的代码」解决不了**的差距：需要语义层机制（glued evaluation /
  non-unfolding quote / meta solution sharing / occurs 缓存）。

### 3.5 vecTest（3.3×）与 idTest

- vecTest 960：twin 75 ms / 346 MB vs smalltt 22.5 ms / ~45 MB（7.7× 分配）。双方都是**二次型**
  （每个 cons 的隐式 meta 要做 occurs 检查，线性增长的 meta 链 ⇒ O(n²)）；我们常数大约 3×（时间）/
  7.7×（分配）。属于 meta occurs 检查没有缓存/近似同一族问题，但 960 规模可接受（P2 级优化）。
- idTest 40：我们 0.078–0.093 ms / 238 KB；smalltt 打印 0 s（<1 ms）。处于噪声底，无可比性。

## 4. 层间差距（L07/L08 vs L09/L10）

| 用例 | L07/L08 twin | L09/L10 twin | 差异 |
|---|---:|---:|---:|
| natconv 1M | 131.1 / 136.7 ms | **83.7 / 61.1 ms** | L09/L10 快 1.6–2.2× |
| natconv 1M ref | 3848.5 / 3770.1 ms | **1872.4 / 1724.6 ms** | 快 2.0–2.2× |
| treeconv 20 twin | L07 964 / L08 1050 ms | **L09 720 / L10 747 ms** | 快 1.3–1.5× |
| treeconv 20 ref | — | L09 2373 / L10 2685 ms | 同量级 |
| nftree 18 twin | L07 73.8 / L08 65.1 ms | L09 64.2 / L10 65.0 ms | 基本持平 |
| stlc | 可跑 | 不可直译 | — |

- **NatConv 的层间差异**来自 L09/L10 的 Rc 表示 + 「顶层声明移出 Cxt」载体切换（568c65c5、7a2ebc41）：
  大值转换里全局引用 O(1)、Rc 共享减少物化；L07/L08 参考版 1M 要 1600 万次分配。
- **nf 族层间基本持平**：eval/quote 路径各层同源。
- **L10 的默认燃料上限（natconv ≤2k / tree ≤9）**：L10 参考版 unify 每次递归入口烧 1 fuel
  （src/L10_typeclass/unification.rs:605-609），4096 预算 ≈ 单次转换 4096 次 unify 调用；
  这是实现细节，不是类型论约束，属**可修的性能缺陷**（L09 同编码无此限制）。
- **栈安全**：L07/L08 ref natconv 5M 即 8 GB 栈溢出；L09 ref 10M 溢出；L10 ref 10M 可跑。
  孪生版 10M/tree 23 均无栈问题（迭代内核 + arena）。

## 5. 优化建议（按 expect gain / 成本 排序）

1. **P0 — stlc 每-def 分配（目标 2–3×）**：
   - 先加 per-def 分配/耗时采样（现有 SMALLTTBENCH_ALLOC=1 可给出 case 总量；再加按 def 分桶）
     定位 fresh_meta vs checkType vs unify 占比；
   - 减少 meta 物化：meta 类型/解用 Rc 共享、惰性 quote；对已解 meta 的 type 不重复 quote；
   - 引入 eta-short solutions 与近似转换（先 spine 比较再展开），减少 stlc 隐式解链上的 quote/force；
     评估 L09/L10 的 Rc 表示回灌到 L07/L08。
2. **P0 — pairTest 形态（目标：从指数到近线性）**：glued evaluation / non-unfolding quote
   （meta solution 只保留最小展开），occurs 检查对 active solved meta 做缓存（smalltt 的做法），
   这是单个差距最大（≥2500×）的一项。
3. **P1 — TreeConv 近似转换**：实现 rigid/flex 有界推测（同 head 符号先 unify spine，失败再展开）；
   预期把 2.2–2.9× 压到 1–1.5×，并改善 per-leaf 随深度的劣化。
4. **P1 — 分配吞吐/表示**：twin 已用 arena，但类型项仍物化大量 Rc/Box；对 elaboration 临时值引入
   统一的 arena/对象池（或把 Val 也改为 arena 指针），目标把 nf/conv 的每字节成本从 2.4–5.5 GB/s
   提到接近 GHC 的 5–8 GB/s。
5. **P2 — vecTest occurs 缓存**、**P2 — L10 参考版 fuel 烧点修复**、**P2 — 参考版大档栈安全**
   （若 ref 仍要作为可选性能路径）。
6. **不做**：不要用参考版跑大负载（语义 oracle 用途）；不要再为 smalltt 用例改默认 fuel
   （用基准开关）。

## 6. 复现与工具

```powershell
# 1) 分配计数（我们侧；分析模式，不影响默认计时）
$env:SMALLTTBENCH_ALLOC='1'
target\release\smallttbench.exe --layer L07 --case stlc --sizes 80 --rounds 1 --only ref
# 输出：ALLOC,<layer>,<case>,<size>,<allocs>,<bytes>

# 2) 峰值 WS（我们侧）
powershell -File F:\projects\hermes\_ref\peak_our2.ps1

# 3) smalltt 单用例分配/峰值（RTS -s + 采样）
powershell -File F:\projects\hermes\_ref\run_mem_smalltt.ps1

# 4) 同机对照表
python tools\smalltt_ref\same_machine_compare.py --parsed F:\projects\hermes\_ref\smalltt-bench\parsed.json
    --our-dir target\smalltt_bench\final --our-dir target\smalltt_bench\same_machine
```

数据来源清单：
- 计时：target/smalltt_bench/final/、target/smalltt_bench/same_machine/、F:\projects\hermes\_ref\smalltt-bench*/；
- 分配/内存：F:\projects\hermes\_ref\alloc-bench/（我们的 ALLOC 行）、F:\projects\hermes\_ref\mem-bench/（smalltt RTS 统计 + peak WS）；
- 峰值 WS：F:\projects\hermes\_ref\mem-bench/ 中我们的 *.out.log 采样结果（peak_our2.ps1）。
- 注意：峰值 WS 对 smalltt 含 RTS -A64M -N8 的 arena 预留（约 0.5 GB 基线），
  因此**比较内存时以分配字节为主**；peak WS 只作量级参考。

## 7. 结论

- **孪生版已具备与 smalltt 同量级的转换/归一化性能**：nf 族反超（0.33–0.71×），natconv 10M 反超
  （0.84×），其余转换族慢 1.4–2.9×，且差距主要在「每步常数/分配吞吐」与「无有界近似转换」。
- **两者仍有代差的只有两处**：stlc 式「每 def 大量隐式 meta 的 elaboration」（5.3–6.8×，分配 6.4×）
  和 pairTest 式「指数类型展开」（≥2500×，分配 1800×）。这两处都与 smalltt README 强调的
  meta 管理/展开控制技术一一对应。
- **参考版与孪生版的 2.4–28.4× 是表示层（树形 Val/Tm vs arena 指针 + 迭代内核）差异**，
  参考版大档还有栈上限；对外性能结论应基于孪生版。
- 上述所有 gap 都有可复现的分配/计时证据；接下来应按 §5 的 P0（stlc 每-def 分配、pairTest
  meta 共享）做原型，再用同一套 SMALLTTBENCH_ALLOC + 同机 smalltt 表验收。