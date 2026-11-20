# smalltt 的优化技术逐项分析（面向 L07 参考版改造）

> 2026-11-20。先更正：上一轮把仓库里已废弃的 L07 arena 实验分支翻出来移植并合入，是错误做法；
> 已全部回退（删除 `perf/l07-ref-smalltt` 分支，master 未动、工作树干净，仓库里原有的
> `exp/l07-*` 实验分支保持原样未动）。本文只基于 **smalltt 上游源码（F:\projects\hermes\_ref\smalltt）**
> 与 L07 参考版源码，做逐项技术分析；文末给出改造顺序与预估。

## 0. 结论先行

1. smalltt 的性能来自**一整套相互依赖的机制**，不是若干可单独搬运的 micro-opt：
   `VUnfold` glued evaluation（值保留折叠头 + 按需展开）、`G` 成对值（g1 少归约 / g2 多归约）、
   `ConvState = Rigid | Flex | Full` 有界近似转换、meta solution 的 `rigidQuote/flexQuote/fullCheck`
   三态报价、eta-short solution、contextual metas 的 scope mask、meta freezing + 近似 occurs cache。
2. L07 参考版与这些机制**逐项都不同**：`force` 入口就展开 Decl；`quote` 只有全展开一种口径；
   求 meta 解时 `rename` 先 force 再内联已解 meta；unify 入口先 force 两侧；没有 ConvState / G /
   quote option / eta-short / occurs cache / meta freezing。
3. 本轮做了最小实验验证“差距能不能靠局部改 quote/rename 消掉”：**不能**。
   - pairTest 20 层 5.56 s；把无注解 let 的推断类型改用 smalltt 式 UnfoldNone quote → 2.80 s（仅 2×）；
   - 再加 closed-solution 快路径、rename 的 rigid meta 引用快路径、binder/fresh_meta 的 UnfoldNone →
     无进一步收益（rename 仍 1677 万次/20 层，指数没破）；
   - stlc/treeconv/natconv/vectest 基本不变（stlc80 仍 7.39 s、tree18 543 ms、nat1M 2.2 s）。
   根因：unify 入口的 `force` 已把 `Pair` 之类的 Decl 展开成 Pi/Lam，之后 solve 的 rename
   在展开后的值上再内联已解 meta，每层复制成 2^k；不改掉 “值保留折叠头 + 解报价不内联” 这一层，
   局部 quote 改动无法触达。
4. 因此正确做法是**按 smalltt 的架构分阶段移植**，而不是继续找单点：
   Phase A 值表示（VUnfold + G + force/quote 模式）→ Phase B 近似转换（ConvState）→
   Phase C meta solution 报价/eta-short/occurs 缓存。预估工作量与收益见 §5。

## 1. 证据来源

- smalltt 源码：`README.md`（Design 各节）、`src/CoreTypes.hs`、`src/Evaluation.hs`、
  `src/Unification.hs`、`src/Elaboration.hs`、`src/Common.hs`；下文所有 smalltt 锚点均为
  `文件:行号`（本机 clone，未改动）。
- L07 参考版：`src/L07_sum_type/mod.rs`、`unification.rs`、`elaboration.rs`、`cxt.rs`、
  `syntax.rs`；孪生版 `bump_spine_iter/` 仅作对照，未改。
- 同机性能基线（用于量化差距）：`docs/smalltt-bench-2026-11-14.md` §11、
  `docs/smalltt-gap-analysis-2026-11-14.md`（L07 参考版 vs 同机 smalltt：stlc 26–29×、
  NatConv1M 47×、TreeConv 7–8×、vecTest 17×、pairTest ≥2500×；nf 族 1.0–1.5×）。

## 2. smalltt 的优化技术逐项拆解（源码锚点）

### 2.1 Glued evaluation：值保留“折叠头 + 展开体”

- `Val`（`CoreTypes.hs:39-47`）：除 Lam/Pi/U 外，`VUnfold UnfoldHead Spine ~Val` 表示
  “一个未展开的头部（TopVar 或已解 meta）+ 实参 spine + 惰性展开体”。`UnfoldHead` 打包成
  unboxed Int + 值（`CoreTypes.hs:78-101`）。
- `force` 只展开 **已解 meta**（`Evaluation.hs:100-111`）；`forceAll` 展开所有 TopVar
  （`Evaluation.hs:114-124`）；`forceMetas` 只展开 meta（`Evaluation.hs:127-145`）。
  `eval` 的 `TopVar` 直接造 `VUnfold` 而不求值（`Evaluation.hs:82`），`app` 对
  `VUnfold` 是 “保留头、追加 spine、惰性推进展开体”（`Evaluation.hs:37/46`）。
- `quote` 有三档（`Evaluation.hs:157-193`）：
  `UnfoldAll`（全展开，nf/打印）、`UnfoldMetas`（只展开 meta）、`UnfoldNone`（都不展开，
  `VUnfold` 只输出 `TopVar/Meta` 头 + spine 实参：`Evaluation.hs:170-171`）。
- README 专节：Glued evaluation（`README.md:223-269`）、On hash consing（`270-295`）。

为什么快：转换/求值期间大量值保持 `Pair`、`Tm` 这类顶层头不展开；只有真正需要结构比较时
才按需展开；quote 存储类型时用 UnfoldNone，term 大小不被展开放大。

### 2.2 Paired values（`G`）：少归约值 + 多归约值并存

- `data G = G {g1, g2 :: ~Val}`（`CoreTypes.hs:69`）；`Infer = Infer Tm GTy`
  （`Elaboration.hs:33`），infer/check 一路返回 `G`。
- unify 对 `G` 用 g2 做快速结构匹配，失败/需要全展开时回退到 **g1**（少归约侧）重新全展开
  （`Unification.hs:331-383` 的 `unify`/`unifyCold`；`forceCS` 见 2.3）。

为什么快：只用一次求值的代价同时拿到“可近似比较的形态”和“可完全展开的原始形态”，避免把值先
彻底求值再比较（L07 正是先 force 再比）。

### 2.3 严格 vs 惰性：按头部选择求值策略

- README：顶层 def、局部 def、Pi 实例化、顶层头应用惰性；其它应用 call-by-value
  （`README.md:296-326`）。
- `appCl`/`appCl'` 的实参是惰性（`Evaluation.hs:26-32`）；`Env` 是惰性链；
  `VUnfold` 展开体字段 `~Val` 惰性（`CoreTypes.hs:42`）。

为什么快：避免为每个中间应用分配/求值 thunk 式值；同时保持顶层链的惰性以支持 glued evaluation。

### 2.4 有界近似转换：`Rigid | Flex | Full`

- `data ConvState = Rigid | Flex | Full`（`Unification.hs:19` 附近）；`forceCS` 对
  `Full` 用 `forceAll`，其余用 `force`（`Unification.hs:19-23`）。
- 关键臂（`Unification.hs:341-402`）：两侧同 `VUnfold` 头且 `cs == Rigid` 时，先在
  `Flex` 下只比 spine；成功即返回；失败则 catch 后回到 `Full` 用 g1 全展开重试。
- `Flex` 模式**禁止展开 TopVar、禁止解 meta**（`guardCS`` 在 solve 前抛
  `FlexSolution`），所以近似步骤不会改变解的形状；失败回退保证判定完备。
- README：Approximate conversion checking（`README.md:327-399`）。

为什么快：同头部的大量比较（尤其类型级 Church 编码）第一步只看 spine，不展开定义体。

### 2.5 Meta solution 的三态报价：rigidQuote / flexQuote / fullCheck

- `rigidQuote`（`Unification.hs:82-127`）：不展开 TopVar/meta，只重命名 spine；
  对 `VUnfold` 头输出 `TopVar` 或 `Meta`；对需要“规范形”的局部才下钻。
  若遇到无法保持折叠的局部（例如需要展开、scope 不合法），设 validity 标志并最终回退。
- `flexQuote`（`Unification.hs:129-181`）：更激进地不展开（含不 force meta 解），
  返回 `(Tm, UBool)` 有效性；`fullCheckRhs`（`Unification.hs:183-211`）用 `forceAll`
  校验报价是否正确。
- `approxOccursInSolution`（`Unification.hs:52-80`）：每个已解 meta 带一个 `cache`
  （`CoreTypes.hs:18` `Solved (Ref MetaVar) ...`），记录最近一次检查的 occurring meta；
  同一 meta 再问直接命中，避免指数重复遍历。
- README：Meta solution checking and quotation（`README.md:454-505`）。

为什么快：meta 解保持“小项”（`?0 := Pair ?1 ?1`），而不是内联成展开后的大项；
这是 pairTest 在 smalltt 里 31 层仍 <1 ms 的直接原因（配合 2.6）。

### 2.6 Eta-short meta solutions + 退化重试

- `solve` 先 `etaContract`：把待解 spine 与 rhs 的公共尾部 eta 变量剥掉再解，
  得到 `?0 := f` 而不是 `?0 := λ x. f x`（`Unification.hs:259-298`）。
- 若 rigid 报价失败，再 `solveLong` 全 eta-展开重试（`Unification.hs:299-307`）；README：
  Eta-short meta solutions（`README.md:419-453`）。

为什么快：解更短，减少后续 quote/rename 的项规模；同时保留顶层折叠（2.5）。

### 2.7 Contextual metavariables（scope mask）+ 不存 meta 类型

- `MetaEntry = Unsolved LvlSet | Solved cache LvlSet Tm ~Val`（`CoreTypes.hs:18`）：
  只存“可见变量集合 mask”，不存 meta 类型。
- `freshMeta` 用 mask 构造 `VFlex` 的 spine（`Elaboration.hs:36-57`）；
  `insertedMeta` 用 maskEnv 从环境取可见实参（`Evaluation.hs:60-77`）。
- README：Contextual metavariables（`README.md:180-222`）。

为什么快：创建 meta O(mask)，不需要为每个 meta quote 并封闭整条上下文的类型
（L07 的 `fresh_meta` 正是 `quote` + `close_ty` + `eval`，stlc 隐式 meta 密集时是主要分配源）。

### 2.8 Meta freezing + 近似 occurs checking

- 顶层定义边界冻结 metas（`Elaboration.hs` 的 `frz` 贯穿；`README.md:506-569`）；
  已冻结的 meta 不再被后续求解/occurs 穿透。
- `approxOccursInSolution` 只对未冻结（`x >= frz`）的 meta 递归，且用 `cache` 记忆
  （`Unification.hs:52-80`）。

为什么快：occurs 检查不再指数遍历共享解链（pairTest / vecTest 的二次型来源之一）。

### 2.9 其它：GHC 专用与数据表示

- `UnfoldHead` 用 unboxed Int 打包（`CoreTypes.hs:78-101`）；`Strict`/`DataKinds`/
  `-fworker-wrapper-cbv`/`-fexpose-all-unfoldings`/`-fmax-worker-args=20`
  （`smalltt.cabal`）；RTS `-A64M -N8`（`README.md:584-602`）；
  自定义异常（`Exceptions.hs`）、自定义 SymTable（`SymTable.hs`）、`primdata`/`dynamic-array`。
- 明确**不用 hash-consing**（`README.md:270-295`）：对高阶项语言收益不足、开销大；
  这提醒我们：优化方向是“少构造/少展开”，不是加通用 memo。

## 3. L07 参考版现状对照（逐项差异）

| smalltt 机制 | L07 参考版现状 | 源码锚点 |
|---|---|---|
| VUnfold 保留折叠头 + 按需展开 | 无；`Val` 没有“折叠头 + 展开体”成对表示 | `mod.rs:239` 起 Val 定义 |
| force / forceAll / forceMetas 三档 | 只有一个 `force`，且**入口就展开 Decl**（非自引用占位） | `mod.rs:858`、Decl 展开臂 `924-947` |
| quote UnfoldAll/UnfoldMetas/UnfoldNone | 只有全展开一种 `quote`（nf/打印同口径） | `mod.rs:1539` |
| G 成对值（g1/g2） | 无；unify 入口直接 force 两侧 | `unification.rs:924-925` |
| ConvState Rigid/Flex/Full + 有界近似 | 无；只有全展开后的结构匹配 | `unification.rs:932-1230` |
| 同头先比 spine、失败回退 | 有 `(Decl a sp, Decl b sp') if a == b` 臂，但 force 已把 Decl 展开，普通情况到不了 | `unification.rs:1020-1022` vs 入口 force |
| meta solution rigidQuote/flexQuote/fullCheck | 只有 `rename`：先 force，再把已解 meta **内联/展开**，无 validity/回退三态 | `unification.rs:344-359`、`solve` 调用 `rename` `731` |
| eta-short solution + 重试 | 无；`solve` 直接按完整 spine 造 lams | `unification.rs:697-736`、`lams_go` |
| contextual metas 的 scope mask | 用 `Pruning` 近似（解/引用处），但 meta 类型是 quote+close_ty 的闭合 Tm | `mod.rs:747-750`、`cxt.rs` bind/define |
| meta freezing + occurs cache | 无冻结；occurs 是精确深度遍历，无 per-meta cache | `unification.rs:52-80` 在 smalltt，L07 无对应；L07 `val_mentions_lvl/occurs_transitive` |
| 严格/惰性混合 | L07 eval/force 是统一 force 语义；无按头部选择 | `mod.rs` eval/force |

## 4. 本轮实验：为什么“局部小改”到不了 smalltt 的量级

在被回退的实验分支上（未合并、已删除）做了最小验证，记录如下（只作分析证据，代码不入库）：

| 尝试 | 结果 |
|---|---|
| 无注解 let 的推断类型改用 UnfoldNone quote（smalltt `Elaboration.hs:289` 的做法） | pairTest 20 层 5.56 s → **2.80 s（2.0×）**；分配 117M→58.7M；仍指数 |
| + solve 的 closed-solution 快路径（闭合 rhs 直接存 Val） | 无变化（`solve_fast` 命中 0；rhs 到 solve 时已被 force 成 Pi） |
| + rename 对已解 dom=0 meta 输出 `Tm::Meta` 引用（rigidQuote 退化） | 无变化：`rename` 入口 `force` 先把 meta/Decl 展开，arm 看不到折叠头 |
| + binder / fresh_meta 的类型 quote 改 UnfoldNone | stlc80 7.39 s、tree18 543 ms、nat1M 2.2 s 均无变化 |

探针（L07_PROBE，已随分支删除）：pairTest 20 层 `unify=43`、`solve=21`、
**`rename=16 777 060`**、`eval=16 779 576`、`closure=8 389 156` —— 指数完全在
`solve` 内部的 `rename`：`dup x_{i-1}` 的隐式 meta 与 x 的类型合一 → `force` 把
`Pair` 展开成 Pi → `rename` 逐个内联被解 meta（每层复制 2 份）→ 2^k。

映射到 smalltt 的根因：smalltt 在 unify 时看到的是 `VUnfold` 的 `Pair` 头，同头先比 spine
（Rigid→Flex），解 quotation 用 `rigidQuote` 保留 `TopVar/Meta` 头（`Unification.hs:82-127`）——
这两步正好阻断本实验里的 force→Pi→rename 展开链。要吃到这部分收益，必须先把 2.1/2.2 的值表示做出来。

## 5. 建议的改造顺序、工作量与预期

> 说明：L07 参考版与孪生版是两份实现；语义 parity 门禁（`l07_fast_parity` 逐字节、blackbox 218 条）
> 要求改参考版时孪生侧同步或至少保持输出一致。以下按“只改参考版、孪生不动、门禁保持绿”的约束估计。

| 阶段 | 内容 | 触及面 | 工作量 | 预期收益（L07 参考版） | 风险 |
|---|---|---|---|---|---|
| A | 值表示：`Val` 增加折叠头/展开体成对表示（VUnfold 等价）、force/forceAll/forceMetas、quote 三档、G 成对值 | mod.rs（Val/force/quote/eval）+ elaboration/cxt 的 G 穿参 | 2–3 天 | 解 quotation 保持小项；pairTest 类指数被结构性阻断；stlc 每-def quote 下降（估 1.3–2×） | 高：Val 全链路表示改；parity 需逐条过 |
| B | 近似转换：`ConvState` Rigid/Flex/Full；unify 用 g1/g2；同头 spine 先试、失败回退 | unification.rs 核心 + forceCS | 2–4 天 | TreeConv/TreeConvM 估 1.2–2×（full 展开→只比 spine）；stlc 类型比较亦受益 | 中高：需保证 Flex 不解 meta、失败回退完备 |
| C | meta solution 报价：rigidQuote/flexQuote/fullCheck、eta-short + solveLong 重试、occurs per-meta cache、meta freezing | unification.rs + MetaEntry + solve/rename | 3–5 天 | stlc 估 1.5–3×；vecTest 二次型常数下降；pairTest 从秒级到毫秒级的必要条件 | 中：validity 标志/回退要严；解形状变化会动 parity 输出 |
| D | 表示层/分配（arena/对象池） | 与 A–C 正交 | 已被你们此前实验覆盖，本文不重复建议 | 另议 | — |

注：A–C 全部是 **smalltt 源码里真实存在的机制**，不是仓库里 11-18 的 `exp/l07-*` 实验路线；
后者（arena 值布局）与本文无交集，本次未使用、也未引用其实现。

更保守的替代路线：若不想动参考版内核，可保持参考版为语义 oracle，只把 A–C 的机制实现到一个
新的 fast reference 上；但这样“L07 参考版自身变快”就不是目标了——需要先明确目标。

## 6. 小结

- 上一轮错误在于：把仓库里废弃的 arena 实验分支当成“借鉴 smalltt”，并把收益归到 smalltt 技术上；
  已回退。
- 真正的 smalltt 优化是 **glued evaluation 值表示 + 成对值 + 有界近似转换 + meta solution 三态报价 +
  eta-short + contextual metas/freezing/occurs cache**；L07 参考版逐项缺失，差距（stlc 26×、NatConv 47×、
  TreeConv 7–8×、pairTest ≥2500×）与这些机制一一对应。
- 局部改 quote/rename 最多带来 ~2×（pairTest），无法破指数——因为 `force` 在 unify 入口已展开 Decl，
  折叠信息在进入 solve 前就丢了。下一步应先做 Phase A（VUnfold + G），这是所有后续收益的前提。

## 7. 参考

- smalltt：`README.md` Design 各节（行号见 §2）；`src/CoreTypes.hs:18,39-47,69,78-101`；
  `src/Evaluation.hs:23-46,82,99-145,157-193,215`；`src/Unification.hs:19-23,52-80,82-211,259-307,331-402`；
  `src/Elaboration.hs:33,36-57,74-94,195-196,288-289`。
- 本项目：同机对比与差距量化见 `docs/smalltt-bench-2026-11-14.md` §11、
  `docs/smalltt-gap-analysis-2026-11-14.md`；L07 参考版锚点见 §3。
