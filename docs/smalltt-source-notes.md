# smalltt 上游基准事实（源码调研）

> **定位**：报告用「上游事实」底稿。只记录 smalltt 仓库自身的用例语义、公布数字、测量方式与语言/语义约束；typort 侧移植结论见 `docs/smalltt-port-notes-*.md`（其他 agent 维护），本文件不写移植结论。
>
> **材料**：本地 clone `F:\projects\hermes\_ref\smalltt`，remote = `https://github.com/AndrasKovacs/smalltt.git`，HEAD = `ea99b0f`。该 clone 是**浅克隆**（`.git/shallow` 存在，`git rev-list --count HEAD` = 1 个提交），因此无法用 git 历史追溯 2021 年公布数字时的代码版本；四张表的数字已用 GitHub `master` 分支的 README 原文核对一致（抓取时间 2026-11-14）。
>
> **版本**：`smalltt.cabal` version 0.2.0.2（`smalltt.cabal:8`；程序启动打印 `smalltt 0.2.0.2`，`smalltt/Main.hs:31`）；构建解析器 `stack.yaml:2` = `lts-21.17`（GHC 9.4.7，仅供当前 checkout 复现参考；README 数字来自 2021 年机器，未记录当时 GHC 版本）。仓库是作者 2018-2019 旧版的完全重写（`README.md:7-9`）。

---

## 1. smalltt 是什么

**一句话**：András Kovács 的高性能依赖类型 elaboration 演示实现（Haskell），用一套 NbE 语义 elaboration 设计把「原始语法 → 核心语法」的检查/推断做到比 Agda/Coq/Lean/Idris 2 的常规（慢速）求值器快 1-2 个数量级；不含任何工业级特性（无归纳类型、无模块、无宇宙分层、无 termination checking），语言本身只为演示设计与基准存在。

**设计要点**（每条附 README 锚点；行号为本地 clone 的 `README.md`）：

| # | 设计点 | 一句话说明 | 锚点 |
|---|--------|-----------|------|
| 1 | 语义 elaboration / NbE | 基于 Coquand 算法：核心语法是不可变程序，按需 eval 成语义值（含闭包、neutral 值），需要时 quote 回核心语法；**全程不用 substitution**。 | `README.md:101-178`（尤其 123-152、165-174） |
| 2 | Contextual metavariables | 每个 meta 是「对其作用域内绑定变量做抽象」的函数（实现上复用普通 lambda）；输出里 metas 被放进顶层互相递归的 block；解用基本 pattern unification。 | `README.md:180-212` |
| 3 | Glued evaluation | 求值时对顶层定义「展开/不展开」同时惰性计算两个值；quotation 可选择只走一支或同时走两支，从而 quote 出**相对顶层展开最小**的项（元解/错误信息/交互显示都受益）。只对顶层定义做展开控制（本地 let/beta 始终计算）。 | `README.md:223-268`（局限见 259-268、392-397） |
| 4 | 不用 hash consing | 依赖类型里有 beta 归约造成的大小爆炸，hash consing 只能合并重复对象、抓不住 beta；因此不做。 | `README.md:270-294` |
| 5 | 严格/惰性策略 | 顶层与本地定义、Pi 实例化、顶层变量应用惰性；其余函数应用 call-by-value。理由：elaboration 不会被 conversion checking 全量 force，被 force 时用 CBV 更快。 | `README.md:296-325` |
| 6 | 近似 conversion checking（有界投机） | unification 三态：`rigid`（可解 meta，可发起一次投机）/ `flex`（不可解、不可展开，只递归 spine）/ `full`（可解且立即展开）；同头符号先试 spine（flex），失败再展开走 full——每条路径**最多回退一次**。**不允许近似 meta 解**（Agda 也不允许；Coq/Lean 允许）。 | `README.md:327-398`；`src/Unification.hs` 的 `unify` |
| 7 | Paired values（`G`） | infer/check 与 unify 用一对始终可转换的值 `data G = G {g1, g2 :: Val}`：g1 = 最少归约版本（小，利于打印/元解），g2 = 已 force 的版本（避免重复 force）。 | `README.md:400-417`；`src/CoreTypes.hs:69` |
| 8 | Eta-short meta 解 | 一侧是 meta、另一侧非 meta 时**先**尝试解（eta-short）；失败才做完整 eta 展开重试；pattern unification 里还做 meta spine 的 eta 收缩（`?0 x y z = ?1 x y z` → `?0 = ?1`）。目的是保住顶层展开、避免 eta-long 解膨胀。 | `README.md:419-452` |
| 9 | 元解检查与 quotation | 三种 quotation 模式 `rigid`/`flex`/`full`：元解里**从不展开顶层定义/已解 meta**，但合法性仍按完整 beta 归约检查；flex 用 `Irrelevant` 占位 + bool 标记「可能非法」。 | `README.md:454-504` |
| 10 | Meta freezing + 近似 occurs checking | 像 Agda 一样按「每个顶层定义（+可选类型注解）为一个 elaboration 单元」冻结 metas（active/frozen）；active 未解 meta 只能出现在 active 解里 ⇒ rigid/flex quote 中的 occurs 检查只需走进 active 已解 meta 的 term 解，且每个已解 active meta 最多访问一次。这使嵌套 pair 基准（normal form 指数增长）在 smalltt 里可行。 | `README.md:506-568`（pairTest 解释 544-564） |
| 11 | GHC 特定优化 | 自定义异常（省 fingerprint 开销）、RTS `-A64M -N8`、自定义 span-keyed 可变哈希表、`primdata`/`dynamic-array`/`flatparse`（解析 2-3 MLOC/s）。 | `README.md:570-649`（RTS 584-601、异常 603-617、库 619-649）；`src/Exceptions.hs`、`src/SymTable.hs` |

**语言特性**（`README.md:84-96`，例子见 `Basics.stt`）：
- **type-in-type**（`Basics.stt:11-12`：`typeInType : U = U`）——这是所有 Church 编码基准的前提；
- 依赖函数类型；Agda 风格**命名隐式参数**：`{A : U} → ...`，类型可省作 `{A}`，也可命名传参 `{B = U}`、命名隐式 lambda `λ {B = foo} x ...`；
- 基本 pattern unification；顶层作用域 + 任意表达式内的 local `let`；
- 无 data/inductive、无模块、无 termination checking，GADT 也靠 type-in-type + Church 编码表达（`Basics.stt:69`）；
- 单文件、交互式 REPL（`:l`/`:r`/`:n`/`:out` …，`smalltt/Main.hs:144-208`）。

---

## 2. 全部性能用例与公布数字

数字全部取自 `README.md` 的 Benchmarks 节（单位：**秒**，`README.md:677`）：

### 2.1 Elaboration speed（stlc 家族，整文件 elaboration）

源文件是 Church 编码的 STLC + 解释器/例子，靠 `src/GenTestFiles.hs` 把模板**复制并给每个顶层名字加数字后缀**（`%` → 序号）放大；"5k/10k"标签≈**非空行数**（如 stlc5k = 40 份 × 125 非空行 = 5000 非空行）。（对应 README 表 `README.md:711-722`。）

| 用例（README 行名） | 源文件 | 生成规则（`src/GenTestFiles.hs`） | 副本数 | 总行数 / 非空行 | 公布秒数 |
|---|---|---|---|---|---|
| stlc | `bench/stlc.stt`（1 份模板，含文件头注释） | 模板本身 | 1 | 165 / 126 | **0.014** |
| stlc5k | `bench/stlc5k.stt` | `:21` `times 40 smallttStlc` | 40 | 6440 / 5000 | **0.179** |
| stlc10k | `bench/stlc10k.stt` | `:20` `times 80 smallttStlc` | 80 | 12880 / 10000 | **0.306** |
| stlcLessImpl | `bench/stlc_lessimpl.stt`（1 份模板） | 模板本身 | 1 | 164 / 127 | **0.008** |
| stlcLessImpl5k | `bench/stlc_lessimpl5k.stt` | `:23` `times 40 smallttStlcLessImpl` | 40 | 6560 / 5080 | **0.140** |
| stlcLessImpl10k | `bench/stlc_lessimpl10k.stt` | `:22` `times 80 smallttStlcLessImpl` | 80 | 13120 / 10160 | **0.275** |
| stlcSmall | `bench/stlc_small.stt`（1 份模板） | 模板本身 | 1 | 71 / 53 | **0.003** |
| stlcSmall5k | `bench/stlc_small5k.stt` | `:50` `times 96 smallttStlcSmall` | 96 | 6624 / 4992 | **0.037** |
| stlcSmall10k | `bench/stlc_small10k.stt` | `:49` `times 192 smallttStlcSmall` | 192 | 13248 / 9984 | **0.072** |
| stlcSmall1M | **不随仓库分发**（约 50MB，`README.md:697-700`） | `:66` `times 19200 smallttStlcSmall` | 19200 | ≈1.32M / ≈1.0M | **8.725** |

- 每份副本的固定行数：stlc = 161 行 / 125 非空行，stlcLessImpl = 164 / 127，stlcSmall = 69 / 52（已用生成文件行距核对：stlc5k 中 `Ty` 定义每 161 行一次；`stlc_small5k` 每 69 行一次）。
- 仓库里已提交的生成文件：`stlc5k.stt`、`stlc10k.stt`、`stlc100k.stt`（=800 份，`:24`；README 未公布 100k 行）、`stlc_lessimpl5k/10k.stt`、`stlc_small5k/10k.stt`；`stlc_small1M.stt` 不提交。另有仅供其他系统的 `stlc1k`（8 份，`GenTestFiles.hs:26,35,40`）与 idris 的 `stlc_small1k`（19 份）/ `stlc_small2k`（38 份）（`:60-61`）。
- 三个模板的语义：`stlc.stt`/模板 `GenTestFiles.hs:238` 是 Church 编码 STLC（Ty 6 构造子：nat/top/bot/arr/prod/sum；Con/Var；Tm 13 构造子：var/lam/app/tt/pair/fst/snd/left/right/case/zero/suc/rec），再加 tbool/true/tfalse/ifthenelse/times4/add/mul/fact 例子；`stlc_lessimpl.stt`/模板 `:737` 是同一程序但**algebra 内部全用显式绑定**（`(Γ : _)` 代替隐式参数，"no implicit arguments inside stlc algebras"，彼此不依赖高阶隐式参数）；`stlc_small.stt`/模板 `:1495` 只有变量/lambda/应用（Ty = ι|arr，Con，Var，Tm = var|lam|app，v0..v4，test：6 层嵌套 app）。
- README 说明与注意事项（`README.md:687-708`）：stlc 版本"type 尺寸大、meta 数量多"；stlcLessImpl 专为 Coq 准备（**Coq 不支持高阶隐式参数**——implicit function types 不是一等的，所以重版本在 Coq 上是 N/A）；stlcSmall 最轻。另注明 Agda 2.6.2 在大文件上有 parsing blowup（agda/agda#5670），所以只有 stlc/stlcLessImpl/stlcSmall 真正反映 elaboration 性能。

### 2.2 Elaboration asymptotics（`bench/asymptotics.stt`，都是 `[elabtime]`）

（对应 README 表 `README.md:735-739`；用例描述 `README.md:725-730`。）

| 用例 | def（文件:行） | 构造方式 | 测什么 | 公布秒数 |
|---|---|---|---|---|
| idTest | `bench/asymptotics.stt:31-33` | `idTest [elabtime] : {A} → A → A`，`= id id id … id`，**恰好 40 个 `id`**（两行各 20 个；`id : {A:U} → A → A` 在 `:2-3`）。README:728 "40 times iterated"。 | `[elabtime]` | **0.000** |
| pairTest | `bench/asymptotics.stt:35-67` | 31 个局部 let：`x0 = dup U`，`x1 = dup x0` … `x30 = dup x29`，返回 `x30`；`Pair = λ A B. (P:U)→(A→B→P)→P`、`dup = λ a P p. p a a`（`:5-9`）。README:729 "30 times nested pairs"（初始 `dup U` 之后嵌套 30 次）。 | `[elabtime]` | **0.000** |
| vecTest | `bench/asymptotics.stt:72-268` | Church 长度索引向量 `Vec A n`（`:20-27`），**恰好 960 个 `cons U`** 套 `nil`（`:74-233` 每行 6 个 × 160 行）；README:730 "960 elements"。文件 `:69-70` 还有一个 5 元素版本被注释掉。 | `[elabtime]` | **0.078** |

- 与 stlc 家族不同，asymptotics 没有生成器（`src/GenTestFiles.hs` 里没有 asymptotics 相关代码），这三个 def 是手写固定规模。
- 表里 0.000 不等于"不花时间"：`[elabtime]` 打印的 `NominalDiffTime` 被手抄成 3 位小数（`README.md:677-680`），0.000 表示 < 0.5ms。
- README 自己的解读：smalltt 在 vecTest 上**也是二次的**（occurs checking 对每个 cons 访问线性数量的 active metas，`README.md:741-744`），只是足够快；idTest/pairTest 只有 smalltt 完成（其它系统全 TL）；Lean 的 pairTest **elaboration 是线性的**，任务跑不完是后续"compilation"阶段指数（`README.md:745-746`）。

### 2.3 Raw conversion checking（`bench/conv_eval.stt`，都是 `[elabtime]`）

（对应 README 表 `README.md:756-774`；用例描述 `README.md:749-754`：NatConv = Church Peano numerals，TreeConv = 完全 Church 二叉树，TreeConvM = 同上但两边含未解 metas。）

| 用例（README 行名） | def（`bench/conv_eval.stt` 行） | 构造方式 | 公布秒数 |
|---|---|---|---|
| NatConv1M | `:99` `convn1M [elabtime]: Eq n1M n1Mb = refl` | Church 自然数大小 1,000,000：`n1M = mul n10k n100`（`:55`），`n1Mb = mul n10kb n100b`（`:56`，另一条构造链，同一值）。`Nat = (n:U)→(n→n)→n→n`（`:11-12`）；`Eq = λ {A} x y. (P : A → U) → P x → P y`（Leibniz，`:23-27`）。 | **0.045** |
| NatConv5M | `:100` | `n5M = mul n1M n5`（`:57-58`） | **0.188** |
| NatConv10M | `:101` | `n10M = mul n5M n2`（`:59-60`） | **0.712** |
| TreeConv15 | `:106` | `convt15 [elabtime] : Eq t15 t15b = refl`；`t15 = fullTree n15`、`t15b = fullTree n15b`（`:76-77`），`n15 = add n10 n5`、`n15b = add n10b n5`（`:35-36`）。`Tree = (T:U)→(T→T→T)→T→T`、`fullTree = λ n. n Tree (λ t. node t t) leaf`（`:62-71`）⇒ 深度 k 的完全二叉树，叶数 **2^k**。 | **0.055** |
| TreeConv18/19/20/21/22/23 | `:107-112` | 同上，k = 18/19/20/21/22/23（`n_k` 由 `n15`+`add`/`suc` 链构造，`:33-48`） | **0.088 / 0.161 / 0.408 / 0.834 / 1.722 / 3.325** |
| TreeConvM15 | `:117` | `convmt15 [elabtime] : Eq t15b (fullTreeWithLeaf _ n15) = refl`；`fullTreeWithLeaf = λ bottom n. n Tree (λ t. node t t) bottom`（`:69-71`），`_` 是洞 ⇒ **未解 meta** 作底层树。 | **0.010** |
| TreeConvM18/19/20/21/22/23 | `:118-123` | 同上，k = 18..23 | **0.092 / 0.169 / 0.361 / 0.835 / 1.694 / 3.453** |

- ⚠️ **深度 16、17 不存在**：`conv_eval.stt` 只定义 `t15`、`t18..t23`（7 个 `t` 定义），README 表也只公布 15、18..23。任务/报告若写 `TreeConv{15..23}`，需注明上游实际是 `{15,18,19,20,21,22,23}`；16/17 属"上游未公布"，要复现需自己补 `t16/t16b`。
- 文件开头有 `warmup : Eq n10M n10Mb = refl`（`:91-94`，无注解）在计时 def 之前做热机（跑 10M 自然数的一次完整转换，制造 GC/分配预热）；文件末尾还有被注释掉的近似转换实验 `-- approxConvt22 [elabtime] : Eq t23 t23 = refl`（`:147`）。
- README 解读（`README.md:776-782`）：smalltt **不允许近似 meta 解**；Agda、Coq、Lean 的近似 conversion 都更激进——**Lean 能 shortcut 全部 tree conversion**（所以 Lean TreeConv 全是 0.001），而 TreeConvM 的 shortcut 需要 *approximate meta solutions*（Agda 没有，Agda 在 TreeConvM 上从 0.77 掉到 50.8 再到 TL）；TreeConv/ForceTree 的低深度列里 Agda/Coq 反而比 smalltt 快（因为 smalltt 老老实实展开计算，见 2.4）。

### 2.4 Raw evaluation and normalization（`bench/conv_eval.stt`，都是 `[nftime]`）

（对应 README 表 `README.md:790-805`；用例描述 `README.md:784-788`：ForceTree = 用布尔合取折叠二叉树；NfTree = 归一化一棵树。）

| 用例 | def（行） | 构造方式 | 测什么 | 公布秒数 |
|---|---|---|---|---|
| ForceTree15 | `:128` | `forcet15 [nftime] = forceTree t15`；`forceTree = λ t. t Bool and true`（`:73-74`），`Bool = (B:U)→B→B→B`（`:2-3`），`and = λ a b B t f. a B (b B t f) f`（`:8-9`）⇒ 折叠整棵树（2^k 叶）。 | `[nftime]` | **0.011** |
| ForceTree18/19/20/21/22/23 | `:129-134` | 同上 k=18..23 | `[nftime]` | **0.100 / 0.240 / 0.487 / 1.070 / 2.122 / 4.372** |
| NfTree15 | `:136` | `nft15 [nftime] = t15`：把整棵 Church 树求值并 quote 成正规形。 | `[nftime]` | **0.005** |
| NfTree18/19/20/21/22/23 | `:137-142` | 同上 k=18..23 | `[nftime]` | **0.064 / 0.111 / 0.259 / 0.552 / 1.286 / 3.023** |

README 解读（`README.md:807-814`）：Agda/Lean/Idris 2 的 NfTree 是 N/A——它们没有"只 force 正规形、不做打印也不做转换检查"的口径；Coq `vm_compute` 在 ForceTree（轻分配负载）上极强；smalltt **关掉 glued evaluation 会快 2 倍**，但仍只有 Coq VM 的 1/3；反过来在 NfTree（重分配负载）上 smalltt 最快，作者归因于 GHC RTS 性能。

### 2.5 用例生成方式：`src/GenTestFiles.hs`

生成器是**手写模板列表 + 复制/改名**，没有基准驱动脚本（`-- todo: genEverything function`，`:18`）：

```haskell
-- src/GenTestFiles.hs:8-16
replace :: String -> String -> String
replace x =
  foldr (\c s -> case c of '%' -> x ++ s; _ -> c:s) []

render :: [String] -> Int -> String
render ls n = replace (if n == 0 then "" else show n) $ unlines ls

times :: Int -> (Int -> String) -> String
times n f = concatMap f [0..n-1]
```

- 模板里每个 `%` 被替换成副本序号；**第 0 份替换为空串**（名字不带后缀），第 1..n-1 份变成 `Ty1`、`Ty2` …；`times n f` 对 `[0..n-1]` 逐份 `render` 后拼接。
- 生成动作本身就是顶层 `IO`（例如 `smallttStlc5k = writeFile "bench/stlc5k.stt" $ times 40 smallttStlc`，`:20-67`），需要进 ghci/REPL 手动调用；生成结果直接写进 `bench/`。已提交的 `.stt` 只是其中一部分尺寸（见 2.1）。
- 模板函数与行号：`smallttStlc` `:238`、`smallttStlcLessImpl` `:737`、`smallttStlcSmall` `:1495`（另有 lean/agda/coq/idris 版本，`:404` 起）；`:69-236` 的 `test1` 是一个"大杂烩"测试模板（idTest/Nat/Vec/Pair/Top/Bot/STLC 片段），**不用于公布的四张表**。
- 题目里 `[elabtime]`/`[nftime]` 不会出现在生成文件里：stlc 家族测的是**整文件**时间；只有手写的 `conv_eval.stt`、`asymptotics.stt` 带注解，测单 def 时间（见 §3）。

### 2.6 与其它系统对照时 README 的原话要点（供报告引用）

- 所有系统版本与命令：Agda 2.6.2（`-vprofile:7 +RTS -M10G`）、Coq 8.13.2（`coqtop -l FILE -batch -type-in-type -time`，测 elaboration 时去掉 `-time`）、**Lean 4.0.0 nightly 2021-11-20，commit `babcd3563d28`**（`time lean FILE --profile`）、Idris 2 用修了 quadratic parsing bug 的 PR（idris-lang/Idris2#2203，`time idris2 -c FILE`）——`README.md:656-668`，更细的命令在 `bench/README.md:1-11`。
- **口径不同**：smalltt / coqtop 只做 elaboration；Agda、Idris 还做模块序列化；Lean 看起来还做了一些编译。README 认为数字仍能反映"等整个输入可用于交互"的等待时间（`README.md:701-705`）。
- 机器/编译：Intel 1165G7、16GB 3200 MT/s、CPU 限 28W（`README.md:670`）；SO = stack overflow、TL = too long（没耐心等）、OOM = out of memory、所有时间单位秒（`README.md:672-677`）；表格是手工粘贴的 markdown（`README.md:679-680`）。

---

## 3. 测量方式细节（报告的关键方法学）

### 3.1 `[elabtime]` / `[nftime]` 注解如何被解析

注解写在**顶层定义名字之后、类型注解之前**，两种写法：`name [elabtime] : T = t`、`name [nftime] = t`（也可只有 `[elabtime]` 不带类型，例如 `pairTest [elabtime] =`）。解析实现：

```haskell
-- src/Parser.hs:274-281
topDef1 :: Span -> Parser TopLevel
topDef1 x = local (const 1) do
  branch $(symbol "[")
    (do elabt <- branch $(symbol "elabtime") (pure True) (pure False)
        nft   <- branch $(symbol "nftime"  ) (pure True) (pure False)
        $(symbol' "]")
        topDef2 (TopInfo x elabt nft))
    (topDef2 (TopInfo x False False))
```

- 顶层定义入口 `top = exactLvl 0 >> idented topDef1`（`src/Parser.hs:283-285`），即默认两个 flag 都是 False。
- 两个 bool 与定义名 span 一起被**压进一个 Int**（低 2 位是 flag，高位是 span 起点），构造/解构见 `src/Presyntax.hs:77-93`（`data TopInfo = TopInfo# Int Int` + `pattern TopInfo`）；`TopLevel` 类型见 `src/Presyntax.hs:96-109`。

### 3.2 每条定义的时间是怎么打的

```haskell
-- src/Elaboration.hs:254-270
printingElabTime :: Top.WithCxt (Span -> Bool -> IO a -> IO a)
printingElabTime x timing act
  | timing = do
    (a, time) <- timed act
    putStrLn (showTopSpan x ++ " elaborated in " ++ show time)
    pure a
  | otherwise = act

printingNfTime :: Top.WithCxt (Span -> Bool -> Tm -> IO ())
printingNfTime x timing t
  | timing = do
    let cxt = empty Top.cxt
    time <- timedPure_ (quote cxt UnfoldAll (eval cxt t))
    putStrLn (showTopSpan x ++ " normalized in " ++ show time)
  | otherwise = pure ()
```

```haskell
-- src/Elaboration.hs:282-300（elabTopLevel 节选）
P.Definition (P.TopInfo x elabt nft) ma t u -> do
  let cxt = empty $! Top.cxt
  (t, a, va) <- case ma of
    UNothing -> do
      Infer t va <- printingElabTime x elabt (insertApps cxt $ infer cxt t)
      let a = quote cxt UnfoldNone (g1 va)
      printingNfTime x nft t
      pure (t, a, va)
    UJust a -> do
      a <- checkType cxt a
      let va = gjoin $! eval cxt a
      t <- printingElabTime x elabt (check cxt t va)
      printingNfTime x nft t
      pure (t, a, va)
  Top.define x a va t $ elabTopLevel u
```

要点：
- **`[elabtime]` = 该 def 的 RHS 的 elaborate 时间**：无类型注解时包住 `infer`，有注解时包住 `check`。注意**类型注解本身（`checkType cxt a`）不被计时**，`a` 的 quote 也不计时；所以 `convn1M : Eq n1M n1Mb = refl` 的 0.045s 只含"检查 `refl` 对 `Eq n1M n1Mb`"（转换检查发生在这一步）的时间。
- **`[nftime]` = 该 def 的已 elaborate 核心项的"求值 + 归一化"时间**：把核心项 `t` 在空 context 用 `eval` 全展开（`UnfoldAll`）后 `quote` 成正规形；只计这段纯计算，不含打印。这就是 "Raw evaluation and normalization" 表的口径。
- 计时函数本身（`src/Common.hs:415-446`）：

```haskell
-- src/Common.hs:415-446
timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1  <- getCurrentTime
  res <- a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  P.pure (res, diff)

-- | Time a lazy pure value. Result is forced to whnf.
timedPure ~a = do
  t1  <- getCurrentTime
  let res = a
  t2  <- getCurrentTime
  ...
-- | Time a lazy pure value. Result is forced to whnf.
timedPure_ ~a = do
  t1  <- getCurrentTime
  let res = a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  P.pure diff
```

  - 用 **wall clock**（`getCurrentTime`/`diffUTCTime`，`NominalDiffTime`），不是 CPU time；单次测量、无重复/中位数。
  - "forced to whnf" 靠全局 `Strict` 扩展实现：`smalltt.cabal` 的 default-extensions 里有 `Strict`（library `:83`、executable `:143`），因此 `let res = a` 是严格绑定、`timedPure_` 会把结果 force 到 WHNF。GHC 文档中 `Strict` **implies `StrictData`**，加上 `src/CoreTypes.hs:2` 的 `{-# options_ghc -funbox-strict-fields #-}`，`Tm` 的字段是严格的 ⇒ quote 出的正规形会被整体求值，`[nftime]` 的数字才有意义。
  - 打印格式就是 benchmark 数字的原始来源：`<span> elaborated in <NominalDiffTime>` / `<span> normalized in <NominalDiffTime>`（`show NominalDiffTime` 形如 `0.045123s`），作者手工抄到 3 位小数。

### 3.3 两种口径：整文件 vs 单 def

- **整文件口径**：`load` 里 `timed (elab src top)` 打一行 `<path> elaborated in <time>`（`smalltt/Main.hs:59-64`；`load` 还把 parse 单独计时并打印 `parsed in`、最后 `total load time`，`:43-69`）。**Elaboration speed 表（stlc 家族）用的是这一行**（stlc 模板里没有 `[elabtime]` 注解）。
- **单 def 口径**：conv_eval/asymptotics 里带注解的 def 各打印一行，**Raw conversion / Raw evaluation / asymptotics 三张表用的是这些行**。
- 交互命令：`:l <file>` 装载、`:r` 重载（重新 `load (path st)`，`smalltt/Main.hs:144-149`）；`:n <name>` 打印单定义正规形但同样用 `timedPure`（`:158-168`，benchmark 不用它）。

### 3.4 RTS / 编译选项 / 机器

- 可执行文件 RTS 默认参数来自 cabal：`ghc-options: ... -rtsopts -threaded -with-rtsopts= "-A64M -s -N8"`（`smalltt.cabal:152`）。即：**-A64M**（每个 capability 64MB allocation area）、**-N8**（8 个 capability）、`-s`（退出时打印 GC 统计）。
- README 的解释（`README.md:584-601`）：GHC 默认 arena 只有 1MB（9.2 起 4MB），相对典型内存太小；`-A64M -N8` 的有效 arena 是 8×64MB=512MB，"用内存换性能"；**正确设置 RTS 参数可轻松带来 30-50% 提升**。
- 编译：库和可执行都是 `-O2`，另有 `-fexpose-all-unfoldings`、`-fworker-wrapper-cbv`、`-fmax-worker-args=20`（`smalltt.cabal:92,152`）；可选 `-fllvm`（`README.md:67-69`、cabal flag llvm）。GHC 专用优化见 `README.md:570-649`。
- 机器：**Intel 1165G7、16GB 3200 MT/s RAM、CPU 限 28W**（`README.md:670`）。
- 系统/命令/日期：见 §2.6（Lean nightly 日期 2021-11-20 等）。

### 3.5 为什么用 `:r` 重载计时；数字怎么读

README 原文（`README.md:662-665`）："in elaboration benchmarks I use timings for `:r` instead of `:l`; **reloading tends to be 20-30% faster, presumably because the RTS is 'warmed up' by previous heap allocations**. I find this to be more representative of typical usage where we mostly reload files we're actively working on."

读表注意：
1. **所有数字都是"第二次装载"（warm）的 wall-clock 秒**，不是 cold start；跨系统/跨实现比较时这是 intentionally favorable 的口径，但作者认为更贴近交互使用。
2. 数字是**单次测量手抄、保留 3 位小数**（`README.md:677-680`），0.000 表示 < 0.5ms；`N/A` = 没法在该系统复现同一基准；`TL` = 等太久放弃；`SO` = 栈溢出；`OOM` = 内存耗尽。
3. 只有 smalltt 这一列是本文档关心的"上游公布数字"；其它系统列在附录里原样抄录，供报告做对照。
4. conv_eval 文件里 `warmup` def（`conv_eval.stt:91-94`）在计时项之前额外热身；由于 `:r` 已经热过 RTS，两者叠加只影响首次 `:l`。

---

## 4. smalltt 语言/语法速览（移植翻译时对照用）

全部来自 `Basics.stt` 与 benchmark 文件，行号为文件内行：
- 注释/缩进：`--` 行注释；顶层定义必须缩进（Haskell 风格，`Basics.stt:14-15`）；允许任意 name shadowing（`Basics.stt:7-9,19-21`）。
- 顶层定义：`name : type` 换行缩进 ` = rhs`；类型注解可省（`const = λ ...`，`Basics.stt:38-40`）；注解与 `=` 之间可插入 `[elabtime]`/`[nftime]`。
- 依赖函数：`(x : A) → B`，unicode `→`/`λ` 与 ascii `->`/`\` 均可（`Basics.stt:34-36`）；binder 可分组 `(A B : U)`（`Basics.stt:27-29`）。
- 隐式：`{A : U} → ...`，类型可省 `{A}`；隐式 lambda `λ {A} x y. ...`（`bench/conv_eval.stt:24`）与命名隐式 lambda `λ {B = foo} x (y : foo). ...`（`Basics.stt:55-57`）；显式传隐式参数 `f {U} t`、命名传参 `f {B = U}`（`Basics.stt:48-53`）；`_` 可出现在任何需要推断项的位置（`Basics.stt:59-61`），benchmark 里 `fullTreeWithLeaf _ n15` 的 `_` 就是 TreeConvM 的未解 meta 来源。
- local let：`let x : A = t; u` 或 `let x = t; u`（`Basics.stt:7-9,42-46`），pairTest 用 30 层 let 链。
- 无 data 声明；`U : U`；无宇宙/无 termination check；Church 编码即"数据类型"。

---

## 5. 迁移到 typort 时需注意的语义差异清单（点到为止）

> 详细移植结论由各移植笔记（`docs/smalltt-port-notes-l07l08.md` 等）给出；这里只列"上游事实决定的、必须提前在报告里声明"的差异点。

1. **type-in-type（`U : U`）是全部 Church 编码的前提**（`README.md:88`，`Basics.stt:11-12`）：`Bool/Nat/Tree/Pair/Vec` 都定义在 `U` 上，且 `Var : Con → Ty → U`、`Tm : Con → Ty → U` 这类"类型编码"直接量化 `U`。→ 迁移到分层宇宙（L09/L10）不能直译，具体可表达性结论见 L09/L10 移植笔记；L07/L08（若为 type-in-type）可直译。
2. **高阶隐式参数是一等公民**：stlc 模板的 algebra 通过 `{Γ A} → ...` 依赖隐式参数传递（`bench/stlc.stt:40-69`），Coq 因此跑不了重版本（`README.md:693-695` 明说 implicit function types 不是一等的）。typort 的隐式语法/推断策略若不同（如 `{A}`/显式 binder 的差异），需按移植笔记改写并注明会改变 meta 生成顺序。
3. **Holes `_` → implicit metas**：TreeConvM 整个基准就是"转换问题里含未解 meta"（`conv_eval.stt:117-123`），且 smalltt **不允许近似 meta 解**（`README.md:349-352`）——若 typort 的合一/近似策略不同，TreeConvM 的数字不可直接对标。
4. **let 链**：pairTest 的 30 层 `let x_i = dup x_{i-1}`（`asymptotics.stt:35-67`）是 meta freezing + occurs checking 优化（`README.md:506-568`）的专门测试；若移植把 let 展开成嵌套应用，测的语义就变了。
5. **无 `[elabtime]`/`[nftime]` 注解**：typort 没有这两个指令，时间只能由 driver 在 def 粒度记录；smalltt 公布数字里 stlc 家族是**整文件**时间、其它三张表是**单 def** 时间（§3.3），对比时必须对齐口径。
6. **测得的"elab 时间"不含打印/序列化/编译**（smalltt 只 elaborate，`README.md:701-705`）；跨系统数字不能 apples-to-apples，typort 若在 driver 里包含解析/输出，需要单列。
7. **精度与热机**：公布数字是 3 位小数、`:r` warm wall-clock 秒、单次测量；typort 用 µs/ms 多次重复的 driver 不可能逐位对上，报告里只能做量级/趋势对照（README 自己也在 679-680 承认表格是手抄的）。
8. **用例规模标签**：stlc 家族的 "5k/10k" = 非空行数 ≈ 5000/10000，对应 40/80 份副本；`TreeConv` 的 k = 二叉树深度（叶数 2^k，k=15→32768、k=23→8,388,608）；`NatConv` 的 1M/5M/10M = Church numeral 大小；`stlcSmall1M` = 19200 份（≈1M 非空行，~50MB，不在仓库）。
9. **深度 16/17 不存在**（见 §2.3 注）；`TreeConvM` 的深度集合与 TreeConv 相同，均为 `{15,18,19,20,21,22,23}`。
10. `%` 只是生成器占位符（`GenTestFiles.hs:8-13`），不是 smalltt 语言语法；移植生成器应保持同样的副本数/改名方式，否则文件规模对不上 "5k/10k"。

---

## 6. 复现步骤（本次调研未实际运行，仅记录上游方式）

- 安装：`stack install` 或 `cabal v2-install`（有 LLVM 可加 `--flag smalltt:llvm` / `-fllvm`），详见 `README.md:61-82`。
- 测 conv/asymptotics：启动 `smalltt` REPL → `:l bench/conv_eval.stt`（首次装载，热身）→ **`:r`**（重载，读第二次打印的每条 `[elabtime]` "`… elaborated in …`" / `[nftime]` "`… normalized in …`"）；asymptotics 同理。stlc 家族读 `:r` 后的整文件 `<path> elaborated in <time>` 行。
- 生成 stlc 大文件：进 `stack ghci`（加载库模块 `GenTestFiles`），调用对应 IO 动作（如 `smallttStlc5k`、`smallttStlc10k`、`smallttStlcSmall1M`），文件写到 `bench/`（`GenTestFiles.hs:20-67`）。conv_eval/asymptotics **没有**生成器，是静态文件。
- 注意：本次调研按要求**不跑任何程序、不安装工具链**；以上仅作为报告"复现方法"的说明。

---

## 7. 引用清单

**README（本地 clone，行号为当前文件行号；与 GitHub master 核对一致）**
- `README.md:7-9,31` 项目/版本；`:39-59` Overview（非工业级、不追求极致调优）；`:84-96` 语言特性（type-in-type、隐式、pattern unification、顶层+let）。
- 设计：`:101-178`（NbE 基础、无 substitution）；`:180-221`（contextual metas、pattern unification）；`:223-268`（glued evaluation）、`:270-294`（hash consing 取舍）、`:296-325`（严格/惰性）、`:327-398`（近似 conversion、三态 unify）、`:400-417`（paired values `G`）、`:419-452`（eta-short）、`:454-504`（元解检查/quotation 三模式）、`:506-568`（meta freezing + occurs checking，pairTest 解释）。
- GHC 优化：`:570-582`、`:584-601`（RTS `-A64M -N8`、512MB arena、30-50%）、`:603-617`（自定义异常）、`:619-649`（哈希表/库/flatparse）。
- 基准设置：`:652-685`（bench/ 目录、系统版本/命令 656-668、机器 670、缩写 672-677、单位秒 677、手抄表格 679-680）。
- 四张表：`:687-722`（Elaboration speed，表 711-722）、`:725-746`（asymptotics，表 735-739）、`:749-782`（Raw conversion，表 756-774）、`:784-814`（Raw eval/nf，表 790-805，结论 807-814）。
- 代码/源码/安装：`:61-82`、`:84-96`。

**源码（行号为本地 clone）**
- `bench/conv_eval.stt`：`:2-9` Bool/true/and；`:11-21` Nat/add/mul/suc；`:23-27` Eq/refl；`:29-60` 数字构造链（n2..n10M/b）；`:62-74` Tree/leaf/node/fullTree/fullTreeWithLeaf/forceTree；`:76-89` t15..t23；`:91-94` warmup；`:99-101` NatConv；`:106-112` TreeConv；`:117-123` TreeConvM；`:128-134` ForceTree；`:136-142` NfTree；`:147` 被注释的 approx 实验。
- `bench/asymptotics.stt`：`:2-3` id；`:5-9` Pair/dup；`:11-18` Nat/zero/suc；`:20-27` Vec/nil/cons；`:31-33` idTest；`:35-67` pairTest；`:69-70` 注释掉的 5 元素 vecTest；`:72-268` vecTest（960 个 cons U）。
- `bench/stlc.stt`（1 份，`:1-165`）、`bench/stlc_lessimpl.stt`（`:1-164`）、`bench/stlc_small.stt`（`:1-71`）；生成的 `bench/stlc5k.stt`/`stlc10k.stt`/`stlc100k.stt`/`stlc_lessimpl5k.stt`/`stlc_lessimpl10k.stt`/`stlc_small5k.stt`/`stlc_small10k.stt`。
- `src/GenTestFiles.hs`：`:8-16` replace/render/times；`:18` todo；`:20-67` 各生成动作（stlc 20-24、lessimpl 22-23、small 49-50、1M 63-67、其它系统 26-61）；`:69-236` `test1` 大杂烩模板；`:238` `smallttStlc` 模板；`:737` `smallttStlcLessImpl` 模板；`:1495` `smallttStlcSmall` 模板。
- `src/Parser.hs:267-285`：`topDef2`/`topDef1`（`[elabtime]`/`[nftime]` 解析）、`top`。
- `src/Presyntax.hs:77-93`：`TopInfo`（span+两 flag 压进 Int）；`:96-109` `TopLevel`/`Tm` 语法树。
- `src/Elaboration.hs:254-270`：`printingElabTime`/`printingNfTime`；`:276-300`：`elabTopLevel` 的计时调用点。
- `src/Common.hs:415-446`：`timed`/`timedPure`/`timedPure_`（wall clock + WHNF）。
- `src/CoreTypes.hs:2`（`-funbox-strict-fields`）、`:56-70`（`Tm`/`G`）；`src/Unification.hs`（`unify` 三态，`README.md:354-368` 引用）。
- `smalltt/Main.hs:28-70`（REPL/load/整文件计时/统计行）、`:93-97`（`nf0`/`zonk`）、`:144-208`（`:l`/`:r`/`:n` 与帮助）。
- `smalltt.cabal:8`（版本）、`:56-92`（库 default-extensions 含 `Strict` `:83`、ghc-options `:92`）、`:116-152`（exe `Strict` `:143`、RTS `:152`）；`stack.yaml:2`；`bench/README.md:1-11`（各系统命令）；`CITATION.cff:4-8`。

**外部核对**：`https://raw.githubusercontent.com/AndrasKovacs/smalltt/master/README.md`（2026-11-14 抓取，四张表数字与本文件一致）；上游仓库 `https://github.com/AndrasKovacs/smalltt`。

---

## 附录：README 四张表原样抄录（含其它系统列，供报告引用）

单位秒；SO=stack overflow，TL=too long，OOM=out of memory，N/A=未复现。（`README.md:711-722`）

**Elaboration speed**

|                 | smalltt | Agda   | Coq   | Lean   | Idris 2 |
|-----------------|---------|--------|-------|--------|---------|
| stlc            | 0.014   | 0.573  | N/A   | 0.194  | 1.18    |
| stlc5k          | 0.179   | 4.127  | N/A   | 6.049  | 43.698  |
| stlc10k         | 0.306   | 16.160 | N/A   | 12.982 | 129.635 |
| stlcLessImpl    | 0.008   | 0.358  | 0.145 | 0.166  | 0.907   |
| stlcLessImpl5k  | 0.140   | 4.169  | 0.905 | 4.508  | 20.386  |
| stlcLessImpl10k | 0.275   | 17.426 | 1.685 | 8.861  | 52.026  |
| stlcSmall       | 0.003   | 0.106  | 0.128 | 0.073  | 0.542   |
| stlcSmall5k     | 0.037   | 4.445  | 0.762 | 2.649  | 6.397   |
| stlcSmall10k    | 0.072   | 22.8   | 1.388 | 5.244  | 13.496  |
| stlcSmall1M     | 8.725   | TL     | 149   | 615    | OOM     |

**Elaboration asymptotics**（`README.md:735-739`）

|               | smalltt | Agda elab | Agda total | Coq elab | Coq total | Lean elab | Lean total | Idris elab | Idris total |
|---------------|---------|-----------|--------|---------|-------|---------|-------|-------|-------|
| idTest        | 0.000   | TL        | TL     | TL      | TL    | TL      | TL    | TL    | TL    |
| pairTest      | 0.000   | TL        | TL     | TL      | TL    | TL      | TL    | TL    | TL    |
| vecTest       | 0.078   | 1.128     | 4.098  | 0.769   | 0.935 | 0.244   | 3.65  | 4.465 | 6.277 |

**Raw conversion checking**（`README.md:756-774`）

|               | smalltt | Agda    | Coq    | Lean    | Idris 2  |
|---------------|---------|---------|--------|---------|----------|
|NatConv1M      |0.045    | 1.8     | SO     | 16.4    | 3.22     |
|NatConv5M      |0.188    | 9.6     | SO     | 34.6    | 29.65    |
|NatConv10M     |0.712    | 19.7    | SO     | 61.1    | 173.88   |
|TreeConv15     |0.055    | 0.016   | 0.005  | 0.001   | 0.105    |
|TreeConv18     |0.088    | 0.02    | 0.007  | 0.001   | 3.75     |
|TreeConv19     |0.161    | 0.03    | 0.009  | 0.001   | 4        |
|TreeConv20     |0.408    | 1.7     | 0.618  | 0.001   | 16.65    |
|TreeConv21     |0.834    | 3.4     | 1.161  | 0.001   | 5.8      |
|TreeConv22     |1.722    | 6.4     | 2.315  | 0.001   | 12.1     |
|TreeConv23     |3.325    | 13.7    | 4.699  | 0.001   | 25.38    |
|TreeConvM15    |0.010    | 0.770   | 0.003  | 0.001   | 0.1      |
|TreeConvM18    |0.092    | 6.35    | 0.003  | 0.001   | 2        |
|TreeConvM19    |0.169    | 12.8    | 0.004  | 0.001   | 2.67     |
|TreeConvM20    |0.361    | 26.6    | 0.605  | 0.001   | 8.9      |
|TreeConvM21    |0.835    | 50.8    | 1.273  | 0.001   | 10.83    |
|TreeConvM22    |1.694    | TL      | 2.703  | 0.001   | 22.23    |
|TreeConvM23    |3.453    | TL      | 5.472  | 0.001   | 45.9     |

**Raw evaluation and normalization**（`README.md:790-805`）

|               | smalltt | Agda    | Coq vm_compute | Coq compute | Coq lazy    |Lean reduce | Lean eval | Idris 2 |
|---------------|---------|---------|----------------|-------------|-------------|------------|-----------|---------|
|ForceTree15    |0.011    | 0.070   | 0.002          | 0.022       | 0.053       | 0.213      | 0.022     | 0.3     |
|ForceTree18    |0.100    | 0.47    | 0.019          | 0.169       | 0.299       | 1.80       | 0.170     | 3.3     |
|ForceTree19    |0.240    | 0.92    | 0.041          | 0.299       | 0.725       | 3.5        | 0.345     | 7.5     |
|ForceTree20    |0.487    | 1.8     | 0.076          | 0.805       | 1.164       | 6.8        | 0.695     | 17.8    |
|ForceTree21    |1.070    | 3.58    | 0.151          | 1.23        | 2.2662      | 14.6       | 1.38      | 49.4    |
|ForceTree22    |2.122    | 7.37    | 0.299          | 2.492       | 4.55        | 29.4       | 2.75      | OOM     |
|ForceTree23    |4.372    | 15.93   | 0.731          | 5.407       | 9.664       | 62.7       | 5.52      | OOM     |
|NfTree15       |0.005    | N/A     | 0.018          | 0.013       | 0.01        | N/A        | N/A       | N/A     |
|NfTree18       |0.064    | N/A     | 0.192          | 0.127       | 0.213       | N/A        | N/A       | N/A     |
|NfTree19       |0.111    | N/A     | 0.523          | 0.289       | 0.402       | N/A        | N/A       | N/A     |
|NfTree20       |0.259    | N/A     | 0.716          | 0.632       | 0.88        | N/A        | N/A       | N/A     |
|NfTree21       |0.552    | N/A     | 1.559          | 1.195       | 1.572       | N/A        | N/A       | N/A     |
|NfTree22       |1.286    | N/A     | 2.971          | 2.94        | 3.143       | N/A        | N/A       | N/A     |
|NfTree23       |3.023    | N/A     | 5.996          | 4.99        | 7.187       | N/A        | N/A       | N/A     |
