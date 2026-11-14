# L09/L10 上的 smalltt 用例迁移（conv_eval 族）

> 写域：porter-l09l10（task-2）。代码：`src/bin/smalltt_cases/l09_l10.rs`。
> （Lead 追加：最终构建里 L09/L10 孪生版也接了 `TYPORT_UNIFY_FUEL` 覆盖；最终干净数据见
> `docs/smalltt-bench-2026-11-14.md`。）
> 复现命令尾部见 §7。所有时间都取自**四 agent 并行、机器有负载**时的 `--rounds 1`
> 初测，只用于可行性判断；干净数据由 Lead 重跑。

## 0. 结论速览

| 用例 | L09 | L10 | 结论 |
|---|---|---|---|
| natconv | ✅ 默认 fuel 全 PASS（1k/2k/3k/4k/10k/100k） | ⚠️ 默认 fuel 只到 **2k**；3k+ 需 `TYPORT_UNIFY_FUEL` | 可行，Church 数 + 分层 Eq |
| treeconv | ✅ 默认 fuel 全 PASS（8/9/10/11/12/15/18） | ⚠️ 默认 fuel 只到 **depth 9**；10+ 需放大 fuel | 可行 |
| treeconvm（含 meta） | ✅ 同上（8..18） | ⚠️ 默认 fuel 只到 depth 9 | 可行，转换会解掉叶子 meta |
| forcetree（nf） | ✅ 全 PASS（8..18） | ✅ 全 PASS（nf 口径不烧合一燃料） | 可行 |
| nftree（nf） | ✅ 全 PASS（8..18） | ✅ 全 PASS | 可行 |
| idtest / pairtest / vectest | ❌ 不可直译 | ❌ 不可直译 | type-in-type 缺失，最小反例见 §6 |

- **L09 与 L10 都通过**（同上表）；差异只在参考版的合一燃料口径：
  L09 参考版只在 `frcs` 命中替换时烧 fuel（本编码无 `VSub` ⇒ 不烧），
  L10 参考版 `unify` **每次递归入口烧 1 fuel**（`src/L10_typeclass/unification.rs:605-609`
  "递归深度防护"），所以 L10 的默认 4096 燃料 ≈ 单次转换最多 4096 次 unify 调用。
- **默认 fuel 上限（实测）**：L09 = 无燃料瓶颈（测到 natconv **1M**、treeconv **depth 20** 仍 PASS）；
  L10 = natconv ≤ **2k**、treeconv/treeconvm ≤ **depth 9**（再大需 `TYPORT_UNIFY_FUEL=20000000`）。
- **放大 fuel 后**（`TYPORT_UNIFY_FUEL=20000000`，twin 与 L09 不受影响）：
  L10 声明的全部 size 都 PASS（含 treeconv/treeconvm 18、natconv 100k）；
  外推：L10 natconv 1M 需 ~4M 次 unify（<20M ✓），treeconv depth 23 需 ~3.4e7 次 unify
  （>20M，需再放大；未实测）。
- 与 smalltt 公布值对照（同数量级，跨机器/跨实现，仅参考）：NatConv1M 上游 45ms vs
  L09 ref 1.59s / twin 98ms；TreeConv15 上游 55ms vs L09 ref 76ms / twin 18ms；
  TreeConv18 上游 88ms vs L09 ref 634ms / twin 163ms；ForceTree15 上游 11ms vs
  L09 ref_nf 31ms / twin_nf 10ms；NfTree15 上游 5ms vs L09 ref_nf 21ms / twin_nf 7.6ms。

## 1. 编码设计（分层宇宙适配）

smalltt 是 type-in-type（`typeInType : U = U`），L09/L10 是**分层、非累积**宇宙：
`Type n : Type (n+1)`、`Type n` 与 `Type m`（n≠m）不可合一、裸 `U` 只是变量名。
Pi 层级 = `max(check_universe(域), check_universe(余域))`，而
`check_universe(Type n) = n+1`（`infer_expr(Type n) = U(n+1)`，见
`src/L09_mltt/elaboration.rs:877` 与 `:880-894`）。**没有 impredicativity**：
Church 编码的宿主类型必须严格高于被迭代的类型，所以每个 Church 类型都要显式抬级。

### 1.1 核心定义（最终可用写法）

```
def BoolC : Type 1 = (B : Type 0) -> B -> B -> B
def trueC  : BoolC = B => t => f => t
def andC   : BoolC -> BoolC -> BoolC = a => b => B => t => f => a B (b B t f) f

def NatC  : Type 3 = (N : Type 2) -> (N -> N) -> N -> N
def addC  : NatC -> NatC -> NatC = a => b => N => s => z => a N s (b N s z)
def mulC  : NatC -> NatC -> NatC = a => b => N => s => z => a N (b N s) z
def sucC  : NatC -> NatC -> NatC = a => N => s => z => s (a N s z)

def TreeC : Type 2 = (T : Type 1) -> (T -> T -> T) -> T -> T
def leaf  : TreeC = T => n => l => l
def node  : TreeC -> TreeC -> TreeC = t1 => t2 => T => n => l => n (t1 T n l) (t2 T n l)
def fullTree : NatC -> TreeC = n => n TreeC (t => node t t) leaf
def fullTreeWithLeaf : TreeC -> NatC -> TreeC = bottom => n => n TreeC (t => node t t) bottom
def forceTree : TreeC -> BoolC = t => t BoolC andC trueC

enum EqN[A : Type 3](x: A, y: A) { reflN(a: A) -> EqN a a }
enum EqT[A : Type 2](x: A, y: A) { reflT(a: A) -> EqT a a }

def conv  : EqN[NatC]  n1k n1kb = reflN[NatC] n1k
def convm : EqT[TreeC] t10b (fullTreeWithLeaf _ n10) = reflT[TreeC] t10b
```

### 1.2 层级推导（为什么是 Type 3 / Type 2 / Type 1）

- `BoolC = (B : Type 0) -> …`：`check_universe(Type 0)=1`，余域 `B->B->B` 在
  `B : Type 0` 下是 0 ⇒ **BoolC : Type 1**。
- `TreeC = (T : Type 1) -> …`：`check_universe(Type 1)=2`，余域 1 ⇒ **TreeC : Type 2**。
  `T` 不能是 `Type 0`：`forceTree` 要把 `T` 实例化成 `BoolC`（`BoolC : Type 1`，
  非累积宇宙里 `Type 1` 的值不能当 `Type 0` 的值用）。
- `NatC = (N : Type 2) -> …`：`check_universe(Type 2)=3`，余域 2 ⇒ **NatC : Type 3**。
  `N : Type 2` 是必需的：`fullTree` 要把 `N` 实例化成 `TreeC`（`TreeC : Type 2`）。
  若把 NatC 压在 Type 1/2（`N : Type 0/1`），tree 家族的第一步 `n TreeC …` 就过不了。
- `EqN`（`enum` 宇宙扫描取参数域 `Type 3` 的层级）：`EqN A x y : Type 3`；
  `EqT : Type 2`。**分层宇宙没有 universe polymorphism**：`Eq` 必须按 `A` 的层级各复制
  一份（`tools/bench_corpus/L09/proj_universe_stack.typort` 的 stratified id 同款做法）。
- 构造子使用点的 icity：`A` 是隐式参数（`[...]`），`x/y` 与构造子字段 `a` 都是显式
  ⇒ 正确写法是 `reflN[NatC] n1k`，写成 `reflN[NatC, n1k]` 会报 `icit mismatch Impl Expl`。

### 1.3 转换检查为什么真的发生

`conv : EqN[NatC] n1k n1kb = reflN[NatC] n1k` 的检查过程：
注解求值成 `Sum(EqN,[NatC,n1k,n1kb])`；体 `reflN[NatC] n1k` 推断出类型
`Sum(EqN,[NatC,n1k,n1k])`；合一走 `(Sum,Sum)` 臂**逐参数值比较**
（`unification.rs:665-677`：只比 `params[i].1`），于是
① `n1k ≈ n1k`、② `n1k ≈ n1kb` 两次 Church 数转换——在 unify 里 λ 逐层展开，
最终比较 `s (s (… z))` 的刚性 spine，**耗时随 n 线性增长**（见 §4 表）。
treeconv 是同一机制，只是 spine 变成二叉树（耗时随 2^depth 增长，nftree 的
`nodes=2^depth` 是直接证据）。treeconvm 的期望类型里带洞 `_`（类型 `TreeC` 的 meta），
转换比较到叶子时由合一解出 `?leaf := leaf`——说明 meta 参与转换的路径也走通了。

负向对照（证明不是语法短路）：`def t0_bad : Type 0 = Type 0`、
`def selfapp : Type 1 = id1[Type 1] id1` 都会 can't unify（`Type 1 vs Type 2`）。

## 2. 可行 size / 上限（实测）

- **L09（默认 `TYPORT_UNIFY_FUEL=4096`）**：本编码不产生 `VSub`，参考版不烧合一燃料 ⇒
  没有燃料上限。实测：natconv **1M**（ref 1.59s / twin 98ms）、treeconv **depth 20**
  （ref 5.0s / twin 0.91s）仍 PASS；再大只是更慢/更深栈。
- **L10（默认 4096）**：`unify` 每递归入口烧 1 ⇒ 上限 = 单次转换 ~4096 次 unify 调用。
  实测分界：natconv **2k PASS / 3k SKIP**；treeconv/treeconvm **depth 9 PASS / 10 SKIP**。
  forcetree/nftree 的 nf 口径不做大转换，**任意声明的 depth 都 PASS**（含 18）。
- **L10（`TYPORT_UNIFY_FUEL=20000000`）**：声明的全部 size PASS（natconv 100k、
  treeconv/treeconvm 18 等）。外推：natconv 1M 约需 4M 次 unify、treeconv depth 23
  约需 3.4e7 次（超过 20M，需再放大）。**twin 与 L09 不受该环境变量影响**。
- 栈：大 size 建议 `SMALLTTBENCH_STACK_MB=4096`（本笔记大档都这样跑）；声明内的
  最大档（tree 18 / natconv 100k）在 1024 默认栈下未观察到问题，1M 档建议 4096。
- `--sizes` 只认 SPECS 里声明的标签；SPECS 之外的可跑标签（调试/扩展用）：
  natconv `2/3/4/5/10/20/100/5k/1M/5M/10M`，tree depth `2/4/5/6/7/9/19/20/21/22/23`
  （`source()` 都支持，只是没进 SPECS）。

## 3. 初测表（`--rounds 1`，机器有负载；单位 µs，列序同 CASE 行）

初测原始文件（可直接对照/复跑）：
`target/smalltt_probe/l09l10/case_l09_defaultfuel.txt`、
`case_l10_defaultfuel.txt`、`case_l10_fuel20m.txt`。

L09（默认 fuel，全部 ref_ok=1 / twin_ok=1）：

| case | size | ref_check | ref_nf | twin_check | twin_nf | nodes |
|---|---|---|---|---|---|---|
| natconv | 1k | 1954 | 966 | 377 | 137 | 1 |
| natconv | 10k | 9222 | 5266 | 1311 | 607 | 1 |
| natconv | 100k | 152140 | 104018 | 11577 | 5608 | 1 |
| treeconv | 8 | 899 | 810 | 232 | 208 | 1 |
| treeconv | 12 | 7409 | 7636 | 1837 | 1785 | 1 |
| treeconv | 15 | 76322 | 70781 | 17970 | 20139 | 1 |
| treeconv | 18 | 634453 | 599678 | 163037 | 138638 | 1 |
| treeconvm | 12 | 7905 | 7969 | 2539 | 2327 | 1 |
| treeconvm | 18 | 681918 | 744064 | 219068 | 206647 | 1 |
| forcetree | 12 | 2652 | 3723 | 629 | 1151 | 4 |
| forcetree | 18 | 164656 | 287655 | 37626 | 93117 | 4 |
| nftree | 12 | 363 | 2382 | 98 | 915 | 16384 |
| nftree | 18 | 519 | 220750 | 322 | 123500 | 1048576 |

L10 默认 fuel：natconv 1k/2k PASS（ref 1821/2396），3k/4k/10k/100k **SKIP reason=ref_check_fail**；
tree 8/9 PASS（treeconv 8 ref 878、9 ref 1807），10+ SKIP；forcetree/nftree 全 PASS。
L10 放大 fuel（20M）后全 PASS，量级与 L09 相当（例：treeconv 18 ref_check 690ms /
twin_check 205ms；nftree 18 ref_nf 277ms / nodes=1048576；natconv 100k ref 171ms / twin 9.0ms）。

## 4. 与 smalltt / L07-L08 的差异

- **smalltt**：type-in-type，Church 编码原样可用；`Eq` 是 Leibniz（`(P:A→U)→P x→P y`）。
  本层用「同层归纳 `Eq` enum」代替（构造子返回 `Eq a a`，与期望 `Eq x y` 的
  索引合一即转换检查）——因为 Leibniz `Eq` 在分层宇宙里对 `A : Type 1` 需要
  `Eq1 : Type 2`（`P : A -> Type 1` 把 Pi 抬到 2），会再抬一级且带 impredicativity 味道；
  enum 版把 `Eq` 钉在 `A` 同层，更贴近「索引合一」口径。
- **宇宙复制代价**：每个层级各一份 `Eq`（`EqN`/`EqT`）；Nat/Tree/Bool 都按「被迭代类型
  的层级 + 1」抬级（NatC 到 Type 3 才能迭代 TreeC）。
- **L07/L08 对照**（porter-l07l08/stlc 的写域）：L07/L08 的 Church 编码可以直接
  type-in-type 风格表达（它们没有宇宙分层），所以 natconv/tree 迁移是「换语法」；
  L09/L10 是「换类型论」——同样的源程序在 L09 需要 `Type N` 标注 + 分层 Eq，
  并且**所有 size 都还要额外验证语义闸门**。
- L09 vs L10 参考版：L10 多一层 typeclass 机制，本编码不触发 trait 求解；
  唯一可观测差异是 `unify` 递归燃料口径（L10 每次 unify 烧 1），所以 L10 大 size
  需要 `TYPORT_UNIFY_FUEL`。

## 5. tree 家族的实现细节

- `fullTree : NatC -> TreeC = n => n TreeC (t => node t t) leaf` —— 依赖
  `NatC` 的 `N : Type 2` 才能把 `N := TreeC`（TreeC : Type 2）。
- `forceTree : TreeC -> BoolC = t => t BoolC andC trueC` —— `TreeC` 的 `T : Type 1`
  才能把 `T := BoolC`（BoolC : Type 1）。这是把 TreeC/BoolC 分别抬到 Type 2/Type 1 的原因。
- `forcetree` 的累加结果 **nf 节点数=4**（=`λB t f. t` 的项大小）：smalltt 的
  forcet15 也是「结果小、展开整棵树」的工作量——nf 是 `quote(eval(…))`，展开
  2^depth 个 `andC` 节点后才归约到 `trueC`；耗时随 2^depth 增长（18 档 ref_nf 288ms）。
- `nftree` 的 nf 直接就是整棵树的项：nodes=2^depth（10→4096, 15→131072, 18→1048576）。
- 数字阶梯完全照 `conv_eval.stt`：`n10=mulC n2 n5`、`n10b=mulC n5 n2`、
  `n15=addC n10 n5`、`n18=addC n15 n3`、`n19=addC n15 n4`、`n20=mulC n2 n10`、
  `n21..n23=sucC 链`（b 侧同式，用 b 版本构造）。深度 **16/17 上游不存在**，
  所以 SPECS 里没有；8/9/10/11/12 是「默认 fuel 可跑」与「小档探测点」的补充标签。

## 6. idtest / pairtest / vectest：不可直译 + 最小反例

三个用例都依赖 smalltt 的 type-in-type（`U : U`）。L09/L10 的非累积分层宇宙里
**没有任何宇宙是自己的元素**：`Type n : Type (n+1)`，`Type n` 不能当 `Type n` 的值。

反例文件（已实测 **L09 与 L10 都 ref_check FAIL**，证据见
`target/smalltt_probe/l09l10/ce_*.typort` 与 `counterexamples_l09.txt` / `_l10.txt`）：

1. `ce_type_in_type.typort`：`def t0_bad : Type 0 = Type 0` ⇒
   `can't unify find: Type 0 expected: Type 1`（`Type 0 : Type 1`）。
   这就是 smalltt `typeInType : U = U` 的最小缺口。
2. `ce_idtest.typort`：`def id1[A : Type 1](x: A): A = x` +
   `def selfapp : Type 1 = id1[Type 1] id1` ⇒ `can't unify find: Type 1 expected: Type 2`。
   idTest 的 40 次 `id id …` 是**同一层上的自应用**：把 A 标成 Type v 后
   id 自身活在 Type (v+1)，永远不能作为 Type v 的实参传给自己（任何 v 都不行）。
3. `ce_pairtest.typort`：`x0 = dup U` 的直接翻译
   `def x0 : Type 1 = dup1[Type 0] Type 0` ⇒ `can't unify find: Type 0 expected: Type 1`。
   `dup U` 要求 `U` 是 U 的元素；分层版每嵌套一层宇宙就要抬一级（30 层需要
   30 份 `Pair_v/dup_v`），不是同一个程序。
4. `ce_vectest.typort`：`cons U` 同理（`Vec : U -> Nat -> U` 的 A := U），
   分层版可写作 `A := Type 1`、元素 `Type 0` 的「抬一级 Church Vec」替代，
   但 960 层 cons 的成本来自 smalltt 的 meta occurs checking（`README.md:741-744`），
   分层版没有同一机制 ⇒ 语义/成本都不同，**不硬造**。

结论：这三个用例在 L09/L10 **不可直译**（属报告结论，不是待办）。上游耗时
（idTest/pairTest < 0.5ms、vecTest 78ms）也说明前两个即使可表达也不构成 benchmark。

## 7. 复现

```powershell
# 构建（与其它 agent 共享 target；改动只在 l09_l10.rs）
cargo build --release --bin smallttbench

# L09（默认 fuel，全部声明 size 走语义闸门）
$env:SMALLTTBENCH_STACK_MB='4096'
.\target\release\smallttbench.exe --layer L09 --case all --rounds 5
# → CASE 行存 target/smalltt_probe/l09l10/case_l09_defaultfuel.txt（本笔记为 rounds=1）

# L10 默认 fuel：只到 natconv<=2k / tree<=9，其余 SKIP reason=ref_check_fail（=燃料上限证据）
.\target\release\smallttbench.exe --layer L10 --case all --rounds 1

# L10 放大 fuel：全部 size PASS
$env:TYPORT_UNIFY_FUEL='20000000'
.\target\release\smallttbench.exe --layer L10 --case all --rounds 1

# 单用例 / 单 size
.\target\release\smallttbench.exe --layer L09 --case treeconv --sizes 15,18
```

快速探针（绕过 cargo / 共享锁，`#[path]` 直编层源码 + 本生成器）：
`target/smalltt_probe/l09l10/`（`probe.rs` + `probecrate/`，支持 `@file:` 读任意
`.typort` 做反例验证；`target/smalltt_probe/l09l10/ctarget/release/l09l10probe.exe`）。
