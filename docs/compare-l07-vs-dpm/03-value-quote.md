# 维度 3：值语言、quote/rename/conv 与卡住项（stuck）的规范化与打印

> 对比对象：L07 = `F:\projects\hermes\elaboration-zoo-lsp\src\L07_sum_type\`；dpm = `F:\projects\Rust\dpm-nbe-rs\src\`。
> 文中 `文件:行号` 均以各自项目根为基准。标注：【事实】= 读过代码；【推断】= 由代码推出的语义后果；【存疑】= 证据不足。

## 一句话结论

L07 与 dpm 的价值表示骨架同源（NbE + 闭包 + 显式替换的延迟值），但**卡住项（stuck eliminator）的表示方式完全不同**：L07 把 `match` 当作一等值 `Val::Match`（自带捕获 env + pending 实参，force 时重选分支），dpm 把卡住的模式匹配折进中性 λ（`Ne::Lam(ps, n, cl, sp)`）并靠 `napp` 重跑 `match_`。这一条差异向后传导到 quote、转换判定、发散防护与打印四件事上：dpm 需要"饱和欠应用 λ"（NOTES 偏离 3），L07 需要"在简化 decl 表下重求值分支体再 quote"（mod.rs:1275-1302）。

## 代码地图

| 概念 | L07 | dpm | 是否等价 |
|---|---|---|---|
| 值域 | `Val`（mod.rs:184-220），无独立 Ne 层，中性 = Rigid/Flex/Decl/Obj/Prim/Match + Spine | `Val`（syntax.rs:294-310）+ `Ne`（syntax.rs:348-358）两层 | 机制同族，分层不同 |
| 延迟替换 | `Val::VSub(Val, Rc<Subst>)`（mod.rs:219） | `Val::Sub(Rc<Val>, Rc<Sub>)`（syntax.rs:298） | 等价（都靠 force 消去） |
| 卡住 match | `Val::Match(scrutinee, Env, [(PatternDetail, Tm)], pending)`（mod.rs:215） | 无独立构造；`Ne::Lam(ps, arity, Closure, spine)`（syntax.rs:355） | **不等价**（见 D2） |
| force | `Infer::force`（mod.rs:589-671）+ `frcs`（mod.rs:678-787） | `frc`（eval.rs:90-96）+ `frc_s`（109-130）+ `frc_ne`（134-151） | 同构 |
| quote | `Infer::quote`（mod.rs:1220-1304） | `quote_val`（eval.rs:403-424）+ `quote_ne`（446-501） | 同构，Match 臂差异显著 |
| 转换判定 | `unify` 本体 + `struct_eq::val_eq` 快路径 | `conv`/`conv_sp`/`conv_ne`（eval.rs:315-362） | **不等价**（D5/D6） |
| 预算 | `UNIFY_FUEL=4096` + `burn`（mod.rs:479, 395-402） | `Res{val,progressed}` + `frc_res`（eval.rs:100-106） | 防的目标不同（D7） |
| 深值安全 | struct_eq/occurs/rename 已迭代化（README §7.6） | 无迭代化，靠 MAX_DEPTH=512 + 64 MiB 栈（NOTES 偏离 10） | 不等价 |

## 逐点对照

### D1 值域分层：单层 `Val`+Spine vs `Val`/`Ne` 双层

【事实】dpm 分两层：`Val` 只含构造子/型构造子/延迟替换/中性（`Val::Ne(Rc<Ne>)`），`Ne` 只含"卡住的计算"——变量应用 `Ne::Var(Lvl, Spine)`、卡住的 λ `Ne::Lam(...)`、卡住的 plus `Ne::Plus`（syntax.rs:294-358）。L07 不设 Ne 层：`Rigid(Lvl, Spine)`、`Flex(MetaVar, Spine)`、`Decl(SmolStr, Spine)`、`Obj`、`Prim`、`Match` 都是 `Val` 的变体（mod.rs:184-220）。

【推断】后果有三：
1. dpm 的 `frc` 只需消 `Val::Sub` 与"中性里的 Sub"（`Ne::Sub`），其余值直接返回；L07 的 `force` 必须覆盖 Sum/SumCase/Match/Prim/Obj 的归约与重选，是更"厚"的一个函数（mod.rs:589-671 共 6 个显式臂 + 兜底）。
2. dpm 的 quote 天然按层分派，`quote_val` 遇到 `Val::Ne` 才进 `quote_ne`；L07 的 quote 是单层大 match，且 Match 臂要自己重建上下文。
3. dpm 的 `Ne::Sub` 允许"对中性再叠加替换"而不 force，L07 用 `Val::VSub` 对**任何**值包裹（含 Sum/SumCase），配合 frcs 的"槽位只包裹不物化"纪律（mod.rs:721-784）。

### D2 卡住 eliminator：`Val::Match` 一等值 vs `Ne::Lam` + 重跑 match_

【事实】L07：
- 建值：`eval(Tm::Match)` 在 scrutinee 不是构造子值时构造 `Val::Match(scrutinee, 捕获env, cases, pending)`；
- 重选：`force` 的 Match 臂先 `force(scrutinee)`，一旦变成 `SumCase` 就在 `eval_aux` 选分支、在**值层**依次应用 pending 实参再继续 force（mod.rs:609-628）。pending 之所以存值而非项，注释说明"项层 splice 会把实参的自由变量引到错误上下文"（mod.rs:211-215, 615-619）。
- 变体：`eval_aux`/`eval_aux_arm`（pattern_match.rs:680-750）负责首匹配。

dpm：
- `match_` 从**原始** patterns/spine 逐参数推进（eval.rs:233-263），全部匹配完则 `capp` 后应用剩余实参；参数不够或 refl 模式不匹配则 `stuck_lam(ps, n, cl, sp)` = `Ne::Lam`（eval.rs:267-269）；
- 之后 `frc_ne` 的 `Ne::Lam` 臂：空 spine 直接是值（NOTES 偏离 1 修掉原版发散），非空则 `napp(lam, frc_sp(sp))` 重新走 `match_`（eval.rs:138-148）。

【推断】两条路线的能力差异：
1. **多 scrutinee / 嵌套 match**：L07 用 `Tm::Match` 的嵌套表达式表达，每个 Match 值独立携带自己的捕获 env，force 只重选最外层；dpm 只有 λ 上一串模式，多参数匹配必须靠 λ 的 arity 一次吃满，一旦卡住就整体重跑（重跑会重算已匹配的 binder——NOTES 偏离 2 明确说这是**有意**的）。
2. **重选成本**：L07 的重选是 O(1) 判断 + 一次 eval_aux；dpm 的重跑是 O(已消费参数) 的重新 match + 重新求值 binder 值。对深链递归 match，dpm 的形态更容易在卡住值上做重复工作【推断】。
3. **可扩展性**：L07 的 `Match` 有 `pending` 槽与 splice 语义（quote 时包成 App），dpm 的 stuck λ 直接把 spine 存在 Ne 里，语义更简洁但不能表达"match 结果再被应用"之后的 pending 分层。

### D3 quote 的饱和策略：L07 无需饱和 / dpm 显式饱和欠应用 λ

【事实】dpm `quote_ne` 的 `Ne::Lam` 臂（eval.rs:456-500）：
- 若已供给实参 `sp` 与 patterns 的前缀匹配（`prefix_matches`，429-443），把剩余模式用**规范实参**补满（变量模式补 fresh var，refl 模式补 `Val::Refl`），跑一次 `match_`；有进展就打印 `Tm::Lam(剩余模式, quote(结果))`；
- 否则按原样打印 λ，用 `new_vars` 开体（保留源模式名）。

L07 `quote` 的 `Val::Lam` 臂（mod.rs:1233-1237）只做 `closure_apply(closure, vvar(l))`——因为 L07 的 λ 值**不带 spine**（应用在 `v_app` 里直接 β 或卡住为别的形态），不存在"欠应用 λ"这个值。`Val::Match` 的 quote 则是另一种饱和：分支体在"捕获 env + fresh rigid 槽"下用**简化 decl 表**重求值再 quote，pending 按应用序包成外层 `Tm::App`（mod.rs:1275-1302）。

【推断】dpm 的"饱和"是它单层 λ-模式表示的必要补丁：若不做，`λ x y . plus x y` 应用到 `zero` 后 quote 会把实参丢掉（NOTES 偏离 3 的表格正是这三个例子）。L07 不需要该补丁，但需要另一个补丁：quote(Match) 必须往返一致（quote→eval 恒等），否则 `nf` 输出会被重新求值成不同的卡住形态——注释说这是"现架构补齐的关键点"（mod.rs:1276-1279）。

### D4 quote 的上下文纪律与 decl 表

【事实】L07 在 quote(Match) 与 rename(Match) 两处都用 `simpl_decl_cached`（mod.rs:1281）把全局值换成中性 `Decl` 引用，再在分支体上 eval——注释给出两条理由：递归调用不被重展开（正确性）、以及性能旁表缓存（mod.rs:1277-1294）。dpm 没有 match 值需要 quote，`quote_val` 直接对闭包用 `free_closure`（eval.rs:375-383, 411）。

【推断】这是"把 eliminator 放进值域"的必然代价：值里存了 Tm（分支体）和 Env（捕获环境），quote 就必须重建一个能安全求值 Tm 的环境。dpm 把这项开销放在 `match_` 里（每次重跑），L07 放在 quote 与 rename 里（每次读点）。两者都是 O(分支体) 的重复工作，只是触发时机不同。

### D5 等价判定：结构快路径 + 预算 vs 递归 conv

【事实】L07 `struct_eq.rs`：**不 force、不展开、不求值**，忽略 span，纯结构比较；入口同址短路（`std::ptr::eq`，struct_eq.rs:46-53），`VSub` 只有同一 `Rc<Subst>` 实例才继续（struct_eq.rs:82-88），预算 `EQ_BUDGET=20000` 用完按"不相等"处理（struct_eq.rs:36, 76-78），迭代化实现（struct_eq.rs:10-18 注释）。用途是 unify 对卡住 `Match` 自比较的短路（struct_eq.rs:3-8）。

dpm `conv`/`conv_sp`/`conv_ne`（eval.rs:315-362）：递归、对两侧 force，`Ne::Plus` 结构比较（NOTES 偏离 13 修掉原版"plus n m 不自反"的缺陷），无 η（NOTES "Inherited limitations"），无预算。

【推断】
1. L07 的快路径是"性能 + 收敛"双目的：卡住 match 的两份拷贝逐分支重求值会因 fresh rigid 层级递增而不收敛，结构比较先短路。dpm 没有这个问题——它的 stuck 值不含 Tm。
2. dpm 的 conv 无预算，深值上递归深度 = 值深度；L07 的 `struct_eq` 有预算且迭代化（深值安全轮），但 `quote`/`pretty` 仍是递归（README §7.6b 诚实清单）。两侧的"深值安全"都不完整，只是 L07 记录得更明确。

### D6 η：L07 有，dpm 没有

【事实】L07 `unify` 有两条 η 臂：`(t, Val::Lam(..)) if v_applicable(t)` 与反向（unification.rs:947-962），配合 `v_applicable` 守卫（mod.rs:370-381）；而 `frcs` 的 Rigid 读点比 η 臂**多放行 `Val::Lam`**（mod.rs:707-714 注释：解值是 λ 且读点带实参是良型形态）。dpm NOTES 明确"No eta: `λ x . g x` is not convertible to a neutral `g`"。

【推断】这是**转换能力的实质差异**：L07 能证明一部分函数外延等式，dpm 不能。对依赖模式匹配本身影响不大（索引方程通常是构造子/变量），但会影响 `Eq (f x) (g x)` 形态的期望类型能否通过。L07 为此付出了 η 臂的复杂守卫（v_applicable 的两次语义分裂正是 2026-09-17 评审轮的修复点之二）。

### D7 发散防护：共享 fuel 池 vs "有进展才继续"

【事实】L07 用单一 `Cell<u32>`（`unify_fuel`，`UNIFY_FUEL=4096`，mod.rs:479）在 force 展开臂、`frcs` 的 lookup 命中、`unify` 每次递归各烧 1（mod.rs:589-671, 700-702, unification.rs:835-846）；耗尽时有界降级（force 返回裸 rigid、unify 返回 Err 并带 `(fuel exhausted)` 尾注，mod.rs:1321-1325），可达性探测把 fuel 耗尽**按可达**处理（pattern_match.rs:336-342）。dpm 用 `Res.progressed`：只有归约真的前进才继续 force，否则把值当卡住返回（eval.rs:100-106；syntax.rs:360-368 注释），没有全局预算。

【推断】
1. 两者防的东西不同：dpm 防"对同一个卡住值反复重试"的自旋；L07 防"展开递归 + 合一递归"的总深度（包括 meta 解链成环——solve 无跨 meta occurs check）。
2. 失败语义不同：L07 的耗尽会**改变判定**（假 absurd / 假不可达，README §7.2 明说），dpm 的机制不会改变判定，只会在真正发散的程序上耗尽栈（NOTES 偏离 10 用 64 MiB 线程 + MAX_DEPTH 兜底）。
3. 可移植性：L07 的 fuel 是全局状态，移植到 dpm 那套无 meta 的架构里没有必要；dpm 的 progressed 也不足以替代 L07 的预算（否则深嵌套模式会无限展开）。

### D8 打印与可观测输出

【事实】L07 `pretty`（pretty.rs）渲染 Sum/SumCase/Match/Obj，构造子打印为 `Enum::case`，但**读取**用点号 `Enum.case`（README §2："打印才渲染 `Vec::cons`——读写格式不对称"）。dpm `pretty` 打印 `succ`（解析器接受 `suc` 同义词），freshen 名字加 `'`；卡住的 match 打印成 λ 本身并保留源模式名（eval.rs:489-497）；`⊥` 只显示不能读回（NOTES "Inherited limitations"）。

【推断】两侧都接受"打印产物不一定是合法输入"，但处理方式相反：dpm 扩语法使打印产物可读回（偏离 12，代价是 `succ` 变保留字），L07 保持读写不对称（点号 vs 双冒号），依赖 LSP 层做展示。若要拿两侧 nf 输出做逐字节比对，这条会先炸。

## 可观测的语义差异

| 程序/情形 | L07 | dpm | 依据 |
|---|---|---|---|
| `Eq (add a zero) a` 型期望类型，a 后来被特化为构造子 | 卡住 match 在 force 时重选 → 可归约 | 无 match 值；靠 `frc_ne` 对 stuck λ 重新 napp → 也可归约 | mod.rs:609-628; eval.rs:145-148 |
| `λ x y . plus x y` 应用到 `zero` 后求 nf | 应用即 β，值里无 spine，quote 直接得 `λ y . plus zero y`（再归约） | 欠应用 λ 需饱和：NOTES 表格给出 `λ y . y` | mod.rs:1233-1237; eval.rs:456-488 |
| `Id Nat (plus n m) (plus n m)` | 可证（unify 有 Prim/结构比较 + 宽松臂） | 可证，但依赖 NOTES 偏离 13 的 `Ne::Plus` 结构比较；原版 Haskell 拒绝 | unification.rs:978-981; eval.rs:347-362 |
| `λ x . g x` 与中性 `g` 互转 | 可（η 臂） | 不可（无 η） | unification.rs:947-962; NOTES |
| 深值（10 万层 succ）结构比较 | 迭代 + 预算，2 MiB 栈可跑 | 递归，深值会爆栈（未迭代化） | struct_eq.rs:10-18; NOTES 偏离 10 |
| fuel 耗尽 | 判定可能翻转（假 absurd，带尾注） | 不适用（无预算），改为栈溢出/超时 | README §7.2; NOTES 偏离 10 |

## 机制有无矩阵

| 机制 | L07 | dpm |
|---|---|---|
| 独立 Ne 层 | 无 | 有 |
| 值层 `Sub/VSub` | 有（对任意值包裹） | 有（Val::Sub + Ne::Sub） |
| match 作为值（带捕获 env / pending） | 有 | 无（折进 Ne::Lam） |
| quote 时重求值分支体（simpl_decl） | 有 | 无（无对应物） |
| quote 饱和欠应用 λ | 不需要 | 必须（偏离 3） |
| η 展开 | 有（带 v_applicable 守卫） | 无 |
| 结构快路径 + 预算 | 有（struct_eq） | 无 |
| 深值迭代化 | 部分（occurs/struct_eq/rename；quote/pretty 仍递归） | 无 |
| 全局 fuel 池 | 有（4096，含可达性探测充值） | 无（progressed 单调性） |

## 存疑与待核实

1. 【存疑】L07 `rename`（unification.rs:321, 354 `rename_deep`, 525 `rename_arm`）对 Match 分支体的处理与 quote 的 `simpl_decl` 是否**完全同构**——我只读了文档注释（unification.rs:15-17, 1281-1294），未逐行核对 `rename_arm` 与 `quote` 的分支体环境构造。
2. 【存疑】dpm 的 `conv` 在 `Ne::Lam` 上是否比较 spine（eval.rs:347-362 只看到入口，未读全臂）——若只比 patterns/closure 而不比 spine，两个不同饱和度的卡住 λ 会被判等，这会影响 quote 的饱和触发。
3. 【推断】L07 quote 的 `VSub` 兜底臂（mod.rs:1226）只在 fuel 耗尽时可达；若不变式真成立，该臂是死代码。是否真的有路径让 force 返回顶层 VSub？需要 `frcs` 的空 σ 分支（mod.rs:679-681 走 force）之外的情况做反例搜索。
4. 【存疑】两侧 pretty 对 `Match`/`stuck λ` 的括号与优先级处理是否会导致同一值不同打印，从而影响"逐字节一致"类验收（L07 的黑盒测试断言文案，dpm 的 golden 也是）。

## 给 Lead 的三条要点

1. **最本质的一条**：dpm 把模式匹配放在**语法层**（λ 的模式 + 卡住的 Ne::Lam），L07 把它放在**值层**（Val::Match）；这决定了 quote/conv/打印的全部差异，也是 dpm 需要"饱和"、L07 需要"分支体重求值"的根因。
2. L07 的能力面严格更宽（η、meta、Sum/GADT、深值迭代化），但代价是**判定不再是纯语义的**：fuel 耗尽会让合法程序报假 absurd（README §7.2），而 dpm 的失败模式是资源耗尽而非判定翻转。
3. 可移植性方向是单向的：把 dpm 的 explicit substitution + force 思想搬进 L07 已完成（本次重构）；反过来把 L07 的 Match-当值搬进 dpm 不划算——dpm 的核心资产正是"值域尽可能小、模式只存在于语法"。
