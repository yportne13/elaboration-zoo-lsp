# smalltt 性能用例迁移到 L07–L10：可行性调研与性能对比（2026-11-14）

> 目标：调研 András Kovács 的 [smalltt](https://github.com/AndrasKovacs/smalltt)（下称 smalltt）
> 的性能用例，判断能否迁移到本仓库 L07–L10，并在同机同口径下做性能对比。
>
> - 工作分支：`perf/l09-carrier-switch`，HEAD `6ba7ce0e`（未 commit）
> - smalltt 参考仓库：`F:\projects\hermes\_ref\smalltt`（git clone，只读）；**本机已用 GHC 9.4.8 + cabal 构建成功并跑通官方基准**（见 §11）
> - 环境：AMD Ryzen 5 5600（6C/12T）/ 32 GB / Windows 10 / rustc 1.98.1 / release / mimalloc
> - **同机 smalltt**：本机构建（GHC 9.4.8，RTS 默认 `-A64M -s -N8`）；`[elabtime]/[nftime]` 用 `:r` 热重载 min-of-rounds。数据见 §11
> - 历史参照：smalltt README 公布值来自 Intel i5-1165G7（4C/8T，28 W）/ 16 GB（2021）；本机实测与公布值差异不小，见 §11.5
> - 最终干净数据：`target/smalltt_bench/final/`（26 个 CSV）、`target/smalltt_bench/same_machine/`（同机补充档），
>   汇总 `target/smalltt_bench/final/summary.md`（由 `tools/smalltt_bench_report.py` 生成）
> - 三个分工笔记：`docs/smalltt-port-notes-l07l08.md`、`docs/smalltt-port-notes-l09l10.md`、
>   `docs/smalltt-port-notes-stlc.md`；上游事实：`docs/smalltt-source-notes.md`

## 0. TL;DR（六条结论）

1. **能迁移，但要分三档**：conv_eval 族（NatConv/TreeConv/TreeConvM/ForceTree/NfTree）
   **四层全部可行**（L09/L10 需要显式抬宇宙的分层重编码）；asymptotics 族（idTest/pairTest/vecTest）
   与 stlc 族（stlc/stlcLessImpl/stlcSmall）**只能直译到 L07/L08**（type-in-type），
   L09/L10 因分层宇宙**不可直译**（已给出最小反例）。
2. **默认口径天花板不在性能而在燃料**：L07–L10 参考版单次合一有 `UNIFY_FUEL = 4096`。
   L07/L08 的 NatConv 只能到 **n=4k**（smalltt 用例是 1M/5M/10M，差 250–2500×），
   TreeConv 只能到 **depth 10**（smalltt 是 15/18..23）；L10 更紧（natconv ≤2k、tree ≤depth 9），
   L09 因编码不触发 VSub 燃料路径，默认口径能跑到 natconv 10k、tree 18。
3. **迁移后放大燃料（基准专用开关 `TYPORT_UNIFY_FUEL`，默认行为不变）即可对齐 smalltt 规模**：
   NatConv 1M 参考版 1.7–3.8 s、孪生版 **61–137 ms**；TreeConv 18 参考版 0.54–0.61 s、
   孪生版 **135–211 ms**；ForceTree/NfTree 到 depth 20 不需燃料（参考版 **0.75–1.5 s**，
   孪生 **0.25–0.30 s**）。
4. **同机对照（2026-11-14 补测，§11）：参考版落后 1–47×，形态依赖强**——nf 族（ForceTree/NfTree）
   0.92–1.47×（接近），TreeConv 6.8–8.6×，NatConv 24–47×，vecTest 15.7×，stlc 吞吐 **27–29×**。
   （smalltt 本机实测比其 README 公布值快不少，例如 TreeConv15 9 ms vs 55 ms；跨机器对比会失真，以 §11 为准。）
5. **孪生版（bump_spine_iter）才是和 smalltt 同场竞技的引擎**：twin/ref = 0.03×（NatConv1M）–0.47×；
   **同机对比**：NatConv 1M/5M/10M = 1.36×/1.83×/**0.84×**，TreeConv 1.5–2.4×，TreeConvM 2.2–2.9×，
   nf 族 **0.33–0.71×（更快）**，vecTest 3.3×，stlc 吞吐 5.3–6.8×。结论：优化内核在转换/归一化族已与 smalltt 同量级，
   仅 stlc 吞吐与 pairTest 形态仍有大缺口。
6. **差距可归因到 smalltt 明确宣传的几项设计**：glued evaluation / meta solution sharing /
   occurs-cause caching / 有界近似转换。对应到用例上就是：pairTest 指数爆炸（我们无 meta 共享，
   x30 外推 ~2 h vs smalltt 0.000 s）、TreeConv 18 起小 size 之后我们线性于节点数而
   smalltt 公布曲线亚线性（近似转换 shortcut）、stlc 每一份模板都要解大量隐式 meta（差 5×）。

## 1. 背景

### 1.1 smalltt 是什么

smalltt 是 high-performance elaboration demo（type-in-type 的极简依赖类型论：依赖函数、
Agda 风格命名隐式参数、basic pattern unification、顶层 def、无归纳族/无 universe 分层）。
README 用四个基准族（conv_eval / asymptotics / stlc / raw eval）与 Agda/Coq/Lean/Idris 对比，
并且是「第一个稳超所有现有系统 elaboration 速度」的实现之一。其性能设计要点：
glued evaluation（顶层展开控制）、contextual metavariables、近似转换检查（rigid/flex/full 三态）、
eta-short meta solutions、meta freezing + 近似 occurs checking、GHC RTS 调优。详见
`docs/smalltt-source-notes.md`。

### 1.2 L07–L10 是什么

本仓库是「elaboration zoo」式分层实现，每层有**参考版**（树形 Val/Tm，语义基准）与
**孪生版** `bump_spine_iter`（bump arena + 迭代内核，性能版）：

| 层 | 语言面 | 与本任务相关的点 |
|---|---|---|
| L07 | 和类型 enum + 依赖模式匹配 | 单一 `U`（type-in-type），可直译 smalltt |
| L08 | 积类型 struct（+L07 全部） | 同上 |
| L09 | MLTT 分层宇宙 `Type 0/1/…` | **非累积**、无 universe polymorphism；Church 编码必须抬级 |
| L10 | typeclass（+L09 底座） | 同上；参考版 unify 每递归入口烧 1 fuel |

故「迁移到 L07~L10」的真实含义是：**L07/L08 直译；L09/L10 需要按分层宇宙重写 Church 编码**。

## 2. 方法

### 2.1 用例分组与参数（对齐 smalltt 上游）

| smalltt 用例族 | 具体用例 | 我们迁移后的 case/size |
|---|---|---|
| conv_eval（[elabtime]/[nftime]） | NatConv1M/5M/10M、TreeConv{15,18..23}、TreeConvM{15,18..23}、ForceTree{15,18..23}、NfTree{15,18..23} | `natconv` 1k..5M；`treeconv`/`treeconvm` 10/11/12/15/18；`forcetree`/`nftree` 10/12/14/15/18/20 |
| asymptotics | idTest（40 个 id）、pairTest（x0..x30 共 31 let）、vecTest（960 个 `cons U`） | `idtest` 40、`pairtest` 10/15/20（30 不可行）、`vectest` 240/960 |
| stlc 吞吐 | stlc（165 行模板）、stlcLessImpl（164 行）、stlcSmall（71 行），按 `%` → 序号的规则复制 | `stlc` 1/8/40/80 份、`stlcl` 1/40/80、`stlcs` 1/8/96/192 |

> 注：smalltt 公布深度集合是 **{15,18,19,20,21,22,23}**（无 16/17）；我们取 15/18 两个代表档，
> 其余受本仓库时间/燃料预算限制未列。smalltt 的 stlc「5k/10k」是非空行数，对应 40/80 份；
> 我们 stlc80 = 3121 decls ≈ smalltt stlc10k 的 3200 decls。

### 2.2 迁移方式

- **L07/L08（type-in-type）**：逐字直译。语法映射：`λ x. t → x => t`，`{A} → [A]`，
  `f : T = t → def f : T = t`，`→ → ->`，`case` 是关键字故模板里的 `case` 改名 `scase`。
  Church 类型/值/数字链、`Eq = (P:A→U)→P x→P y` 与 `refl` 全部同构。
- **L09/L10（分层宇宙）**：Church 宿主类型显式抬级 + 按层级复制 Eq：
  `BoolC : Type 1`、`TreeC : Type 2`（`T : Type 1` 才能把 `T` 实例化成 `BoolC`）、
  `NatC : Type 3`（`N : Type 2` 才能迭代 `TreeC`）；
  `enum EqN[A : Type 3]`、`enum EqT[A : Type 2]` 作为归纳族复制，
  `conv : EqN[NatC] n n' = reflN[NatC] n`（索引合一 = 真转换检查）。
- 所有生成器保证「**最后一个 def 是基准对象**」；非 nf 用例追加极小尾 def `nf_dummy : U = U`，
  使 ref_nf 口径只多一次平凡 quote，而不污染 check 计时。

### 2.3 度量口径（新驱动 `src/bin/smallttbench.rs`）

- 解析在计时外；每轮内 ref/twin × check/nf 交错执行，奇偶轮换序；每格 **min-of-rounds**（默认 3–5 轮）。
- 四轴：`ref` = 参考版 `bench_check`（只 elaborate）；`ref_nf` = `bench_check_nf`
  （elaborate 后 quote 最后一个 def 的 nf，对应 smalltt `[nftime]`）；`twin`/`twin_nf` = 孪生版同口径。
- 语义闸门：ref `bench_check` 必须为 true，否则 SKIP 并打印原因（不渲染巨型错误项）。
- 关键开关：`TYPORT_UNIFY_FUEL`（**本次为基准新增的 env 覆盖，缺省 4096，正常路径逐位不变**）
  可放大单次合一燃料池；`SMALLTTBENCH_STACK_MB`（缺省 1024）放大测量线程栈。
  两者只被基准进程消费，四层参考版与孪生版都接了这个开关（改动 142 行，见 `git diff --stat`）。

### 2.4 默认 vs 放大燃料

- **默认 profile（主结论/as-is）**：不设 `TYPORT_UNIFY_FUEL`，展示「开箱能不能跑 smalltt 用例」。
- **fuel profile（对标 smalltt 规模）**：`TYPORT_UNIFY_FUEL=20000000`、栈 8192 MB，
  只用于回答「假设允许更大燃料，性能是多少」——**这是基准专用假设，不是产品默认行为**。

## 3. 可行性矩阵（用例 × 层）

| smalltt 用例 | L07 | L08 | L09 | L10 | 备注 |
|---|---|---|---|---|---|
| NatConv（Church 数转换） | ✅ 直译 | ✅ 直译 | ✅ 重编码（Type 3） | ✅ 重编码 | 默认燃料下 4k/4k/10k/2k 上限 |
| TreeConv / TreeConvM | ✅ 直译 | ✅ 直译 | ✅ 重编码（Type 2） | ✅ 重编码 | TreeConvM 含 meta 的近似转换路径也走通 |
| ForceTree / NfTree（nf） | ✅ 直译 | ✅ 直译 | ✅ 重编码 | ✅ 重编码 | nf 不烧合一燃料，默认到 depth 20 |
| idTest | ✅ 直译 | ✅ 直译 | ❌ 不可直译 | ❌ 不可直译 | 需要 `id : {A:U}→A→A` 自应用（type-in-type） |
| pairTest | ✅ 直译（但 20 层已 5.4 s） | ✅ 直译 | ❌ 不可直译 | ❌ 不可直译 | 同上层；30 层外推 ~2 h |
| vecTest | ✅ 直译（960 可跑） | ✅ 直译 | ❌ 不可直译 | ❌ 不可直译 | 需要 `cons U` 把 `U` 当元素 |
| stlc / stlcLessImpl / stlcSmall | ✅ 直译 | ✅ 直译 | ❌ 不可直译 | ❌ 不可直译 | Church 编码的 Ty/Tm 依赖 `U : U` |

L09/L10 不可直译的最小反例（实测 `ref_check` FAIL，详见
`docs/smalltt-port-notes-l09l10.md` §6 与 `target/smalltt_probe/l09l10/ce_*.typort`）：

```text
def t0_bad : Type 0 = Type 0                 -- can't unify: find Type 0 expected Type 1
def selfapp : Type 1 = id1[Type 1] id1       -- can't unify: find Type 1 expected Type 2（任何 v 都不行）
def x0 = dup1[Type 0] Type 0                 -- U 不是自己的元素；30 层需 30 份分层 Pair/dup
```

**结论**：smalltt 的性能用例**不是同一类**：conv_eval 族是「内核转换/求值速度」，
可以迁到全部四层（L09/L10 换编码）；asymptotics 与 stlc 族是「type-in-type 的元编程形态」，
只能迁到 L07/L08。这一划分本身就是迁移调研的核心结果。

## 4. 默认燃料下的天花板（as-is；干净数据，ms）

| 用例档 | L07 | L08 | L09 | L10 |
|---|---|---|---|---|
| NatConv 4k（上限） | 2.689 / 0.433 | 2.741 / 0.376 | 2.063 / 0.281 | —（2k 上限） |
| NatConv 10k | ❌ SKIP fuel | ❌ SKIP | 4.851 / 0.615 | ❌ SKIP |
| TreeConv 10（上限） | 1.999 / 0.581 | 2.008 / 0.544 | 2.103 / 0.494 | ❌ SKIP（9 上限） |
| TreeConv 18 | ❌ SKIP | ❌ SKIP | 592.779 / 119.513 | ❌ SKIP |
| TreeConvM 18 | ❌ | ❌ | 663.159 / 175.070 | ❌ |
| NfTree 20 | 747.084 / 245.695 | 832.713 / 256.495 | —（本次未跑 20） | — |
| ForceTree 20 | 1082.364 / 304.011 | 1514.953 / 300.115 | — | — |
| pairTest 20 | 5400.517 / 2163.318 | 5577.031 / 2086.737 | ❌ | ❌ |
| vecTest 960 | 382.248 / 80.009 | 353.649 / 74.973 | ❌ | ❌ |
| stlc 80 份（≈10k 行） | 7412.728 / 1870.055 | 7432.880 / 1677.353 | ❌ | ❌ |

（每格 = 参考版 / 孪生版；单位 ms。❌ = 该档在默认燃料/该层语言面下不可跑。）

**天花板数值（默认 4096 fuel）**：L07/L08 NatConv ≤ **4k**（5k 起 fuel exhausted）；
TreeConv/TreeConvM ≤ **depth 10**；L10 NatConv ≤ **2k**、Tree ≤ **depth 9**（每次 unify 递归入口烧 1 fuel，
4096 预算 ≈ 4096 次 unify 调用）；L09 对本编码无燃料瓶颈（只烧 VSub lookup 命中，本编码无 VSub），
默认能到 NatConv 10k / Tree 18。

## 5. 放大燃料后与 smalltt 规模对齐（干净数据，ms）

### 5.1 conv_eval 族（参考版 / 孪生版；conv 行需 Fuel=20M + 栈 8 GB，nf 行不需要）

| 用例 | L07 | L08 | L09 | L10 | smalltt 公布 |
|---|---|---|---|---|---|
| NatConv 100k | 165.140 / 11.065 | 177.091 / 9.611 | 93.689 / 5.482 | 95.444 / 5.603 | —（无此档） |
| NatConv 1M | 3848.518 / 131.093 | 3770.144 / 136.716 | 1872.416 / 83.674 | 1724.607 / 61.070 | **45** |
| TreeConv 15 | 62.670 / 21.640 | 60.916 / 21.986 | 64.919 / 20.222 | 66.438 / 20.632 | **55** |
| TreeConv 18 | 543.555 / 210.569 | 609.692 / 205.043 | 595.266 / 144.140 | 571.113 / 135.259 | **88** |
| TreeConvM 15 | 69.451 / 27.964 | 71.834 / 26.185 | 74.864 / 20.125 | 95.864 / 21.355 | **10** |
| TreeConvM 18 | — | — | 705.713 / 180.567 | 708.850 / 201.681 | **92** |
| ForceTree 15 | 28.155 / 7.231 | 28.008 / 7.360 | 35.240 / 8.959 | 23.368 / 8.182 | **11** |
| ForceTree 18 | 265.727 / 76.131 | 268.759 / 73.086 | 282.202 / 76.223 | 233.035 / 79.484 | **100** |
| ForceTree 20 | 1082.364 / 304.011 | 1514.953 / 300.115 | — | — | **487** |
| NfTree 15 | 17.749 / 6.495 | 17.134 / 6.794 | 18.862 / 6.881 | 19.483 / 7.002 | **5** |
| NfTree 18 | 156.494 / 73.791 | 167.259 / 65.149 | 181.988 / 64.235 | 202.983 / 64.984 | **64** |
| NfTree 20 | 747.084 / 245.695 | 832.713 / 256.495 | — | — | **259** |

### 5.2 asymptotics / stlc（L07/L08 专属）

| 用例 | L07 | L08 | smalltt 公布 |
|---|---|---|---|
| idTest 40 | 0.093 / 0.043 | 0.078 / 0.031 | **0.000** |
| pairTest 20（上游 30 层不可行；20 层已 5.4 s） | 5400.517 / 2163.318 | 5577.031 / 2086.737 | **0.000**（30 层） |
| vecTest 960 | 382.248 / 80.009 | 353.649 / 74.973 | **78** |
| stlc 80 份（3121 decls ≈ 10k 行） | 7412.728 / 1870.055 | 7432.880 / 1677.353 | **306**（stlc10k） |
| stlcLessImpl 80 份 | 6891.377 / 1339.054 | 6988.940 / 1325.496 | **275**（stlcLessImpl10k） |
| stlcSmall 192 份（3649 decls） | 1459.090 / 370.258 | 1477.712 / 340.020 | **72**（stlcSmall10k） |

### 5.3 与 smalltt README 公布值的倍数（跨机器历史数据；**同机对照见 §11**）

| 用例 | 我们最好（参考版） | 参考版 / smalltt | 我们最好（孪生版） | 孪生版 / smalltt |
|---|---|---|---|---|
| NatConv 1M | L10 1724.6 ms | **38.3×** | L10 61.1 ms | **1.36×** |
| TreeConv 15 | L08 60.9 ms | 1.11× | L09 20.2 ms | **0.37×** |
| TreeConv 18 | L07 543.6 ms | 6.18× | L10 135.3 ms | 1.54× |
| TreeConvM 15 | L07 69.5 ms | 6.95× | L09 20.1 ms | 2.01× |
| ForceTree 15 | L10 23.4 ms | 2.12× | L07 7.2 ms | **0.66×** |
| ForceTree 18 | L10 233.0 ms | 2.33× | L08 73.1 ms | **0.73×** |
| ForceTree 20 | L07 1082.4 ms | 2.22× | L08 300.1 ms | **0.62×** |
| NfTree 15 | L08 17.1 ms | 3.43× | L07 6.5 ms | 1.30× |
| NfTree 18 | L07 156.5 ms | 2.45× | L09 64.2 ms | 1.00× |
| NfTree 20 | L07 747.1 ms | 2.88× | L07 245.7 ms | **0.95×** |
| vecTest 960 | L08 353.6 ms | 4.53× | L08 75.0 ms | **0.96×** |
| stlc 10k（80 份） | L07 7412.7 ms | 24.2× | L08 1677.4 ms | 5.48× |
| stlcSmall10k（192 份） | L07 1459.1 ms | 20.3× | L08 340.0 ms | 4.72× |
| stlcLessImpl10k（80 份） | L07 6891.4 ms | 25.1× | L08 1325.5 ms | 4.82× |

> **跨机器警告**：我们的 Ryzen 5 5600（2023，桌面 65 W）单核明显快于 smalltt 的
> i5-1165G7（2021，28 W 笔记本）。按经验粗估 1.3–1.8× 单核优势，所以上表「孪生版 ≤1×」
> 的更保守读法是「与 smalltt 同量级或慢 1.5–3×」；参考版的 20–38× 差距则不可能用硬件解释。
> 严格同机对比不可得（本机无 GHC/stack 工具链，不安装系统级 toolchain）。

## 6. 结果解读与归因

1. **燃料是迁移的第一 blocker，不是性能**：smalltt NatConv1M 是**单次合一**里约 1M 步 β 归约；
   本仓库 `UNIFY_FUEL = 4096` 的初衷是防递归构造子值比较/索引槽互相嵌入的无限递归
   （L07 `unify_fuel` 注释；L10 每次 unify 递归入口烧 1），合法的大转换会撞上限。
   **建议**：保留默认 4096（防环），但给基准/批处理入口加显式开关（本次已加 `TYPORT_UNIFY_FUEL`，
   默认不变），或改成「按展开种类/递归层级 refuel」而非单一池。
2. **L09/L10 的编码差异值得单列**：同一 Church 编码在分层宇宙里必须抬到 Type 3/2/1（非累积），
   但抬级后 **L09/L10 的 NatConv 1M 反而比 L07/L08 快 2.0–2.2×**（参考版 1.72–1.87 s vs 3.77–3.85 s；
   孪生版 61–84 ms vs 131–137 ms）。这与 L09/L10 的「顶层声明移出 Cxt」载体切换
   （`docs/l09-carrier-switch-2026-11-12.md`、`docs/l10-carrier-switch-2026-11-14.md`）一致：
   大值转换里全局 def 引用 O(1) 而非 O(D)。**L10 的默认燃料上限（2k/9）来自其 unify 递归燃 1 fuel
   的实现细节，不是类型论约束**，属于可修的性能缺陷。
3. **nf 族（ForceTree/NfTree）是四层最健康的一族**：默认燃料即可到 depth 20；参考版比 smalltt 慢
   2.1–3.4×，孪生版 0.62–1.30×（跨机器）。说明本仓库的 eval/quote 路径（迭代化 quote、结构相等）
   与 smalltt 的「求值+归一化」口径在同一量级。
4. **pairTest 暴露的不是速度而是设计缺口**：smalltt pairTest（30 层 dup U）≈0.000 s，我们 20 层已
   5.4 s、每加一层 ×2.05（外推 25≈4 min、30≈2 h）。根因：smalltt 的 meta solution 是**小项**
   （`?n := Pair ?(n-1) ?(n-1)`）且 occurs 检查不展开顶层 def；本仓库没有 glued evaluation /
   meta solution sharing，无注解 `let` 的类型每层被 quote 全展开，节点数 2^k。
   这是最值得借鉴 smalltt 的一条：**保留 meta 解的「最小展开」形态**（glued eval / non-unfolding quote）。
5. **TreeConvM（含 meta）**：我们能跑通且 meta 解被正确解出，但 constant 比 smalltt 高
   （2.0–7.0×），因为 smalltt 的 rigid/flex 有界近似转换在「同 head 符号的 spine 比较」上短路；
   我们的 unify 是全展开。TreeConv 15→18 的缩放也印证：我们 ~线性于节点数（61→543 ms，8×），
   smalltt 公布值 55→88 ms（仅 1.6×）——**这不是常数差，是近似转换策略差**，直接按常数比会误导。
6. **stlc 吞吐是最大短板**：smalltt 每 10k 行 306 ms，我们参考版 7.4 s（24×）、孪生版 1.68 s（5.5×）。
   有趣的正向校验：full stlc 只比 lessimpl 慢 ~10%（我们 7.41 vs 6.89 s；smalltt 0.306 vs 0.275 s = +11%），
   说明**翻译保真度很高**，慢的是内核每次 solve/quote 的开销，而非用例语义。
   stlc 也是「大文件 + 大量隐式 meta + Church 编码解构」形态，指向与 pairTest 相同的优化方向。

## 7. 局限

1. **跨机器对比（§5.3）只作历史参照；同机对照见 §11**：smalltt 公布值来自 2021 28 W 笔记本，
   而本机 2026-11-14 已构建 smalltt 实测（同一 Ryzen 5 5600），两者差异可达数倍（如 TreeConv15
   公布 55 ms vs 本机 9 ms）。凡是要写「我们 vs smalltt」的结论，一律以 §11 同机数据为准。
2. **放大燃料是基准专用假设**：`TYPORT_UNIFY_FUEL` 改变了内核默认安全阀（虽然默认路径不变），
   所以 §5 的数字回答「如果允许这么大的单次转换」，不等于「今天开箱即用」。
3. **采样**：每格 min-of-rounds（3–5 轮），小档（<0.2 ms）噪声可达几十 %；大档 1–2 轮。
   所有数据在同一安静窗口串行采（4 个 agent 已停止）。
4. **L09/L10 用例是重编码而非逐字直译**：层级标注改变了类型论表示；性能可比性限于「同算法
   （Church 数/树）同等量工作」层面；TreeConvM 的 meta 求解语义也有差异。
5. **上游深度集合 {15,18..23}：§11 同机已补测 treeconv 15–23 / treeconvm 15–20（twin 全部、ref 到 20）**；
   ref 的 21–23 单档需 5–40 s，未测（§11 标注为 —）。
6. **pairTest 30 层未跑**（外推 ~2 h）；vecTest 只到 960（上游原例）。
7. smalltt 公布数字为手抄 3 位小数，且是 `:r` 热重载口径；我们的口径是进程内 parse-out。

## 8. 结论与建议

**迁移可行性结论**：
- ✅ 推荐迁移：conv_eval 族全部 → L07–L10（L09/L10 用分层编码）；作为「大转换/大 nf」基准纳入
  realbench 式套件。
- ✅ 推荐迁移：stlc 家族 → L07/L08（吞吐基准，可直接对照 smalltt）。
- ⚠️ 有条件：asymptotics 的 idTest/vecTest 可迁 L07/L08；pairTest 因指数不建议进套件（可作为
  「meta 共享」优化的目标用例，小 size 10/15）。
- ❌ 不迁移到 L09/L10：asymptotics 与 stlc（type-in-type 前提与分层宇宙冲突，已有反例）。

**对实现的建议（按收益排序）**：
1. 给大转换加可配置燃料/refuel 策略（基准开关已有；若产品需要可考虑「每 N 次递归 refuel」）。
2. 为 L10 参考版修「每次 unify 递归入口烧 1 fuel」的实现（否则大转换默认口径比 L09 差 2× 以上）。
3. 借鉴 smalltt：meta solution 保留最小展开（glued eval / non-unfolding quote）→ pairTest 形态；
   有界近似转换 → TreeConv/TreeConvM 形态；这两条也是 stlc 吞吐的瓶颈来源。
4. 孪生版继续作为性能基线；参考版与孪生版的差距（2–40×）在写性能报告时不应混用。

## 9. 复现

```powershell
# 1) 构建（含基准驱动 + 四层模块）
cargo build --release --bin smallttbench

# 2) 干净窗口跑三组口径（default / fuel / stlc；约 8 分钟）
powershell -NoProfile -ExecutionPolicy Bypass -File tools\smalltt_bench.ps1 -OutDir target\smalltt_bench\final

# 3) 生成 Markdown 汇总
python tools\smalltt_bench_report.py --dir target\smalltt_bench\final --out target\smalltt_bench\final\summary.md

# 单点复现示例
target\release\smallttbench.exe --layer L07 --case natconv --sizes 1k,4k --rounds 5 --only ref,twin
$env:TYPORT_UNIFY_FUEL='20000000'; $env:SMALLTTBENCH_STACK_MB='8192'
target\release\smallttbench.exe --layer L10 --case natconv --sizes 1M --rounds 1 --only ref,twin
```

## 10. 产物

| 文件 | 说明 |
|---|---|
| `src/bin/smallttbench.rs` | 迁移基准驱动（四层 × 四轴 × 用例生成器） |
| `src/bin/smalltt_cases/{mod,l07_l08,l09_l10,stlc}.rs` | 各层族用例生成器（L07/L08、分层 L09/L10、stlc 吞吐） |
| `tools/smalltt_bench.ps1` / `tools/smalltt_bench_report.py` | 一键测量 / CSV→Markdown 汇总 |
| `docs/smalltt-source-notes.md` | smalltt 上游事实（用例语义、测量方式、公布数字） |
| `docs/smalltt-port-notes-l07l08.md` / `-l09l10.md` / `-stlc.md` | 三个迁移/初测笔记（含 SKIP 分类、反例、语法映射） |
| 四层 `src/L0X/mod.rs`（+ L07/L08 `bump_spine_iter/{prim,machine,compiler,entry}.rs`、L09/L10 `bump_spine_iter/force.rs`） | 仅新增 `TYPORT_UNIFY_FUEL` 基准覆盖（默认行为不变，共 142 行改动） |
| `target/smalltt_bench/final/` | 26 个原始 CSV + summary.md（未跟踪，不入库） |
| `target/smalltt_bench/same_machine/` | 同机 smalltt 档位的补充测量 CSV（tree 19–23、nf 19/20、natconv 5M/10M） |
| `F:\projects\hermes\_ref\smalltt`（含 `cabal.project`、`dist-newstyle`） | smalltt 本机构建（GHC 9.4.8；未入本仓库） |
| `F:\projects\hermes\_ref\run-smalltt-bench.ps1` / `parse-smalltt-bench.py` / `same_machine_tables.py` / `compare_same_machine.py` | 同机 smalltt 测量、解析与对比脚本 |
| `F:\projects\hermes\_ref\smalltt-bench\` | smalltt 同机原始日志 + parsed.json（含 pairTest20/31 对照） |
| `C:\ghcup` / `C:\cabal` | GHCup 工具链（GHC 9.4.8 + cabal 3.12.1.0 + msys2；安装细节见 §11.1） |
| 本文件 | 调研与对比报告 |

> 说明：本次没有 git commit；四个新 agent 的写域互相隔离（每层族一个文件 + 一份笔记），
> 最终数据由 Lead 在安静窗口统一重跑，与各笔记里的「载荷下初测」数值可能有 10–25% 差异。

## 11. 同机 smalltt 实测对照（2026-11-14 补测）

> 本节回答「smalltt 在我们这台机器上到底多快」。§5.3 的跨机器/公布值对照只作历史参照；
> 凡是对外写「L07–L10 vs smalltt」的性能结论，以本节为准。

### 11.1 本机 Haskell 工具链与 smalltt 构建

- 安装：GHCup（Windows 官方 bootstrap，`-Minimal`）→ `C:\ghcup`（含 msys2）；GHC **9.4.8**
  （对应 smalltt `stack.yaml` 的 `lts-21.17`）+ cabal-install **3.12.1.0**。
- 本机 cabal 的 hackage index（140 MB）下载卡住，故改用「全本地依赖」构建：
  - 三个 git pin（与 smalltt `stack.yaml` 的 extra-deps 一致）：`dynamic-array`、`primdata`、
    `ghc-strict-implicit-params`（cabal `source-repository-package`）；
  - 仅有的两个 Hackage 依赖 `flatparse-0.5.0.1` / `utf8-string-1.0.2` 下载 tarball 后 vendor 成本地包；
  - `C:\cabal\config` 里注释掉 hackage 仓库 stanza 并置 `active-repositories: :none`，
    smalltt 目录加 `cabal.project`（内容见 `F:\projects\hermes\_ref\smalltt\cabal.project`）。
- 构建：`cabal build -w ghc-9.4.8 exe:smalltt --jobs=6` → 成功（19 模块 + 可执行文件）。
  产物：`F:\projects\hermes\_ref\smalltt\dist-newstyle\...\smalltt.exe`。
- 运行：REPL 交互，`:l <file>` 首载、`:r` 热重载；RTS 默认 `-A64M -s -N8`（cabal 里
  `-with-rtsopts` 已内置）。每文件跑 3 轮（1 次 `:l` + 2 次 `:r`），按 name 取 min。
- 测量脚本：`F:\projects\hermes\_ref\run-smalltt-bench.ps1`（10 个 .stt 用例）、
  `parse-smalltt-bench.py`（解析 `<name> elaborated in 0.xxx s` / `normalized in`）、
  `compare_same_machine.py` / `same_machine_tables.py`（与我们 CSV 合并出表）。
  原始日志：`F:\projects\hermes\_ref\smalltt-bench\*.log` + `parsed.json`。
- 我们侧补充档数据：`target/smalltt_bench/same_machine/*.csv`（treeconv/treeconvm 19–23、
  nf 19/20、nf check-only、natconv 5M/10M）。大档仍用 `TYPORT_UNIFY_FUEL=40M` + 8 GB 栈。

### 11.2 conv_eval：elaborate 族（smalltt `[elabtime]` vs 我们 `bench_check`，min-of-rounds）

| 用例 | smalltt 本机 | 我们 ref 最好层 | ref/smalltt | 我们 twin 最好层 | twin/smalltt |
|---|---:|---|---:|---|---:|
| natconv 1M | 45.0 ms | 1.72 s (L10) | 38.29× | 61.1 ms (L10) | 1.36× |
| natconv 5M | 174.0 ms | 8.11 s (L10) | 46.58× | 319.2 ms (L09) | 1.83× |
| natconv 10M | 597.3 ms | 14.20 s (L10) | 23.78× | 499.8 ms (L10) | **0.84×** |
| treeconv 15 | 9.0 ms | 60.9 ms (L08) | 6.76× | 13.7 ms (L09) | 1.52× |
| treeconv 18 | 75.9 ms | 543.6 ms (L07) | 7.17× | 119.5 ms (L09) | 1.58× |
| treeconv 19 | 145.9 ms | 1.20 s (L10) | 8.20× | 347.5 ms (L10) | 2.38× |
| treeconv 20 | 336.4 ms | 2.37 s (L09) | 7.06× | 720.3 ms (L09) | 2.14× |
| treeconv 21 | 724.8 ms | —（ref 未测） | — | 1.86 s (L09) | 2.57× |
| treeconv 22 | 1.47 s | — | — | 3.12 s (L09) | 2.12× |
| treeconv 23 | 2.93 s | — | — | 6.83 s (L09) | 2.33× |
| treeconvm 15 | 9.0 ms | 69.5 ms (L07) | 7.71× | 20.0 ms (L09) | 2.22× |
| treeconvm 18 | 76.7 ms | 663.2 ms (L09) | 8.64× | 175.1 ms (L09) | 2.28× |
| treeconvm 19 | 150.1 ms | 1.28 s (L08) | 8.51× | 431.4 ms (L10) | 2.87× |
| treeconvm 20 | 356.3 ms | 2.79 s (L09) | 7.84× | 844.0 ms (L10) | 2.37× |

- smalltt 的 `[elabtime]` 只包 RHS 的 infer/check（类型注解检查不计）；我们的 `bench_check` 含注解检查，
  但本族注解都很小，差异可忽略。
- 参考版在大档上的真实限制是**栈**而不只是燃料：L07/L08 ref 跑 natconv **5M 直接栈溢出**（8 GB 栈仍溢出），
  L09 ref 5M 可跑（9.19 s）但 10M 栈溢出；L10 ref 10M 可跑（14.20 s）。twin 在 10M 无栈问题。
- twin 10M（499.8 ms）**快于** smalltt 本机（597.3 ms），是本次唯一 twin 明显反超的档；但 1M/5M 仍 1.4–1.8× 慢。

### 11.3 conv_eval：nf 族（smalltt `[nftime]` vs 我们 nf-only = `ref_nf − ref_check`）

| 用例 | smalltt 本机 | 我们 ref 最好层 | ref/smalltt | 我们 twin 最好层 | twin/smalltt |
|---|---:|---|---:|---|---:|
| forcetree 15 | 9.0 ms | 8.3 ms (L10) | 0.92× | 3.0 ms (L08) | **0.33×** |
| forcetree 18 | 84.4 ms | 106.0 ms (L10) | 1.26× | 39.8 ms (L08) | **0.47×** |
| forcetree 19 | 157.1 ms | 231.4 ms (L08) | 1.47× | 111.7 ms (L10) | **0.71×** |
| forcetree 20 | 395.0 ms | 407.6 ms (L08) | 1.03× | 172.6 ms (L08) | **0.44×** |
| nftree 15 | 4.0 ms | 16.8 ms (L08) | 4.19× | 6.4 ms (L07) | 1.59× |
| nftree 18 | 42.3 ms | 156.2 ms (L07) | 3.69× | 64.1 ms (L09) | 1.52× |
| nftree 19 | 82.6 ms | 361.5 ms (L09) | 4.37× | 138.2 ms (L10) | 1.67× |
| nftree 20 | 190.3 ms | 746.7 ms (L07) | 3.92× | 245.6 ms (L07) | 1.29× |

- 这里把我们的 `ref_nf` 减去同档 `ref_check` 以对齐 smalltt 的「只 nf」口径（check 部分单独测过；
  forcetree 的 check 占比较高、减法误差略大，nftree 几乎为 0）。
- 结论：**nf 族孪生版在本机反超 smalltt（0.33–0.71×）**，参考版除 forcetree 外仍慢 3.7–4.4×。

### 11.4 asymptotics 与 stlc（smalltt 本机 vs 我们）

| 用例 | smalltt 本机 | 我们 ref 最好 | ref/smalltt | 我们 twin 最好 | twin/smalltt |
|---|---:|---|---:|---|---:|
| vecTest 960 | 22.5 ms | 353.6 ms (L08) | 15.69× | 75.0 ms (L08) | 3.33× |
| stlc 40 份（≈5k 行） | 137.3 ms | 3.68 s (L07) | 26.78× | 727.8 ms (L08) | 5.30× |
| stlc 80 份（≈10k 行） | 275.0 ms | 7.41 s (L07) | 26.95× | 1.68 s (L08) | 6.10× |
| stlcLessImpl 40 份 | 118.5 ms | 3.42 s (L07) | 28.89× | 801.9 ms (L08) | 6.77× |
| stlcLessImpl 80 份 | 244.7 ms | 6.89 s (L07) | 28.17× | 1.33 s (L08) | 5.42× |
| stlcSmall 96 份 | 59.1 ms | 747.9 ms (L07) | 12.66× | 142.5 ms (L08) | 2.41× |
| stlcSmall 192 份 | 50.8 ms | 1.46 s (L07) | 28.75× | 340.0 ms (L08) | 6.70× |

**pairTest 特例（直接生成同尺寸文件对照）**：为了排除「上游是 31 层、我们只能 20 层」的口径差，
从 `bench/asymptotics.stt` 截出 `pairTest20` / `pairTest31` 两个文件跑本机 smalltt：
两者都打印 `elaborated in 0s`（<1 ms）。而我们 L07/L08 的 pairTest 20 层：ref **5.40 s**、twin **2.16 s**。
即同一台机器、同一尺寸，**smalltt 比我们快 ≥2500×**，且我们 25/30 层外推 ~4 min/~2 h。
这不是常数差，而是 smalltt 的 meta solution sharing / 近似 occurs-check 设计缺口（§6.4）。

### 11.5 smalltt 本机实测 vs README 公布值（为什么必须同机重测）

| 用例 | README 公布 | 本机实测 | 本机/公布 |
|---|---:|---:|---:|
| NatConv 1M | 45 ms | 45.0 | 1.00× |
| NatConv 10M | 712 ms | 597.3 | 0.84× |
| TreeConv 15 | 55 ms | **9.0** | 0.16× |
| TreeConv 18 | 88 ms | 75.9 | 0.86× |
| TreeConvM 15 | 10 ms | 9.0 | 0.90× |
| ForceTree 20 | 487 ms | 395.0 | 0.81× |
| NfTree 20 | 259 ms | 190.3 | 0.73× |
| vecTest 960 | 78 ms | **22.5** | 0.29× |
| stlc10k | 306 ms | 275.0 | 0.90× |
| stlcSmall10k | 72 ms | 50.8 | 0.71× |

- 最离谱的是 TreeConv15（6×）与 vecTest（3.5×）：本机 warm `:r` 口径远快于 README 数字；
  说明 README 的表是历史机器/旧 GHC/不同热身的混合口径。**跨机器引用公布值会系统性扭曲「我们 vs smalltt」的倍数**
  （例如 TreeConv15 twin 对公布值 0.37×，对同机 smalltt 是 1.52×；vecTest twin 对公布值 0.96×，对同机是 3.33×）。
- 本机 smalltt 与我们的测量条件对齐：同机、同一安静窗口、都取多轮 min（smalltt 3 轮 reload，我们 3–5 轮）。

### 11.6 同机结论（对 §6/§8 的修订）

1. **twin 与 smalltt 已同量级**：nf 族 0.33–0.71×（更快）、NatConv 10M 0.84×、NatConv 1M/5M 1.36×/1.83×、
   TreeConv 1.5–2.4×、TreeConvM 2.2–2.9×、vecTest 3.3×。
2. **twin 仍明显落后的两块**：stlc 吞吐 5.3–6.8×；pairTest 形态（≥2500×，设计缺口）。
3. **参考版不是可比的性能引擎**：除 nf 族（0.92–1.47×）外，其它族慢 6.8–47×；natconv 5M/10M 的 ref
   还有栈溢出上限（L07/L08 5M、L09 10M）。
4. 之前基于「公布值」判断的 TreeConv15/vecTest 「twin 略快/接近」结论**不成立**，以本节为准；
   NatConv1M 「twin 1.36×」等结论方向不变。

### 11.7 复现（同机 smalltt 部分）

```powershell
# 一次性构建（本机已装 C:\ghcup 的 GHC 9.4.8 / cabal 3.12）
cd F:\projects\hermes\_ref\smalltt
cabal build -w ghc-9.4.8 exe:smalltt --jobs=6

# 跑官方基准（每文件 3 轮 :l+:r）
powershell -File F:\projects\hermes\_ref\run-smalltt-bench.ps1 -Rounds 3

# 解析 + 与我们 CSV 合成同机表
python F:\projects\hermes\_ref\parse-smalltt-bench.py --dir F:\projects\hermes\_ref\smalltt-bench --out F:\projects\hermes\_ref\smalltt-bench\parsed.json
python F:\projects\hermes\_ref\same_machine_tables.py
```

原始数据：`F:\projects\hermes\_ref\smalltt-bench\`（10 个 log + pairTest20/31 + parsed.json）；
我们侧：`target/smalltt_bench/same_machine/`（补充档 CSV）。

