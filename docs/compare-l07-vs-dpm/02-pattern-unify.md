# L07 vs dpm-nbe-rs：依赖模式匹配的编译流程与特化合一

> 维度：模式编译 / specialization by unification。
> 路径约定：`src/L07_sum_type/…` = 本仓库 L07；`dpm: src/…` = `F:\projects\Rust\dpm-nbe-rs\src\…`。
> 标注：【事实】= 读码确认或跑过；【推断】= 由代码路径推出、未执行；【存疑】= 证据不足。
> ⚠ **实测提示（2026-10-30）**：本文件标【推断】的两处行为已实测并被修正（自指索引：L07 实际**接受**；卡住索引方程：L07 实际 **256 s 后假不可达**），以 [`EXPERIMENTS.md`](EXPERIMENTS.md) 为准。
>
> L07 侧未编译执行（禁止改源码/加测试），结论全部来自代码路径 + 现有回归钉；dpm 侧用 `target/release/dpm-nbe.exe`（2026-10-30 构建）实测过第 4 节标"实测"的用例。

## 一句话结论

两侧的**机制骨架同源**（显式替换 + 解随身携带 + 读点 force 展开 + 上下文不缩 lvl），差异不在"特化合一"本身，而在三处判定分档：dpm 是三值结果（Succ/Abs/Idk）、无 occurs check、无覆盖检查；L07 是二值结果 + 浅 occurs + 独立覆盖探测。L07 真正比 dpm 强的不是模式匹配算法，而是类型层（通用 enum/索引族 + Sum/SumCase 注入 + 头部精化），dpm 只有内建 Id，所以它的"构造子注入"退化成 Refl/Zero/Succ 三条硬编码。

## 代码地图

| 概念 | L07 位置 | dpm 位置 | 是否等价 |
|---|---|---|---|
| 模式编译驱动入口 | `src/L07_sum_type/pattern_match.rs:111`（`Compiler::compile`） | `dpm: src/elab.rs:196`（`check_pm`） | 形似，语义域不同（match 分支 vs λ 模式串） |
| 编译期状态 | `pattern_match.rs:46-71`（`Compiler{sub, solvable, nested_checks, cur_path}`） | 无状态（纯递归 + `Ctx` 参数） | 否 |
| 单方程合一 | `unification.rs:825`（`unify(..., Option<&mut SpecSolve>)`） | `dpm: src/elab.rs:70`（`unify1`） | 部分等价（结果二值 vs 三值） |
| 多方程循环 | `pattern_match.rs:356-396`（`unify_indices` 逐参数循环） | `dpm: src/elab.rs:42-65`（`unify_s`） | 否（L07 是活路径，dpm 在 checker 里只送 1 条方程） |
| 解的累积 | `unification.rs:42-45`（`SpecSolve{solvable, acc}`）+ `901-928`（`acc = Subst::extend`） | `dpm: src/elab.rs:53-61`（返回 `sub`，`gamma2 = subst_sub(&a, gamma)`） | 否（可变就地累积 vs 返回值组合） |
| 可解集 | `pattern_match.rs:57,136` + `cxt.rs:360-376`（`bind_slots`）+ `unification.rs:901-928` | `dpm: src/elab.rs:116-124`（`as_var`：任意 bare `Ne::Var`） | 否（显式登记 vs 形态判定） |
| 特化方程来源 | `pattern_match.rs:356-396`（头部 Sum 参数 zip 构造子返回参数） | `dpm: src/elab.rs:221,247`（只有 `Id` 的两个索引） | 否 |
| 构造子注入 | `unification.rs:983-995`（Sum 同名逐参数）、`1003-1031`（SumCase 同 case 逐 datas） | `dpm: src/elab.rs:96-106`（Refl/Refl、Zero/Zero、Succ/Succ） | 否（通用 vs 三条硬编码） |
| 头部精化 | `pattern_match.rs:650-667`（`x := SumCase{…}`） | 无对应物（`refl` 是常量，解即精化） | 否 |
| 上下文施加 σ | `cxt.rs:333-352`（`subst_cxt`） | `dpm: src/context.rs:174-186`（`subst_ctx`） | 是（都保留 `lvl`） |
| 替换表示 | `mod.rs:237-362`（`Subst` 单链 + `Val::VSub` 包裹） | `dpm: src/syntax.rs:235-270` + `src/subst.rs:26-49`（`Sub` 层叠 + `Val::Sub`） | 语义等价、类型标注不同（dpm 有 dom/cod） |
| 覆盖性检查 | `pattern_match.rs:140-149, 228-261, 276-348`（`probe_accessible` + `PosCover`） | 无 | 否 |
| 不可达判定 | `pattern_match.rs:203-209`（`Walk::Unreachable`） | `dpm: src/elab.rs:228-234`（`UnifyRes::Abs`） | 判定同源、处置不同 |
| 卡住的匹配 | `mod.rs:1181-1202`（`Val::Match`）+ `609-628`（force 重选） | `dpm: src/eval.rs:267-269`（`stuck_lam`）+ `134-151`（`frc_ne` 重 napp） | 形似、触发条件不同 |
| 模式语法 | `parser/syntax.rs:16-19`（`Any`/`Con` 嵌套树） | `dpm: src/syntax.rs:76-80`（`Var`/`Refl`/`Abs` 扁平） | 否 |

## 逐点对照

### D1 驱动方与合一器的接口：就地累积 vs 返回值

**L07 做法**【事实】`Compiler` 持 `sub: Rc<Subst>`（`pattern_match.rs:53`）；`unify` 的第六参 `spec: Option<&mut SpecSolve>`（`unification.rs:832`）非空时，bare rigid 与任意非 Flex 值相遇即 `s.acc = Subst::extend(&s.acc, x, v)`（`901-928`）。调用侧 `walk_con` 用当前 σ 作种子 `SpecSolve { solvable: &self.solvable, acc: self.sub.clone() }`（`641-644`），方程后 `self.sub = spec.acc`（`646`）。"剩余方程置于解之下"由 `unify` 每个递归入口实现：`t = force(wrap_sub(&s.acc, t))`（`860-865`）。

**dpm 做法**【事实】`unify1` 返回 `UnifyRes::Succ { lvl, sub }`（`dpm: elab.rs:70-113`），`unify_s` 把最新解 `a` 应用到剩余方程（`vs2 = rest.map(subst_val(&a, …))`）并与累积 γ 组合（`gamma2 = subst_sub(&a, gamma)`），然后以 `lvl = s` 递归（`dpm: elab.rs:53-61`）。

**差异实质**：L07 是"可变状态 + 显式回滚"，dpm 是"纯返回值 + 无需回滚"。回滚账本：L07 需要臂边界快照（`162-163, 217-218`）、探测的局部 σ + meta 快照（`304, 346`）、flex-flex 的 meta 回滚（`unification.rs:743-757`）三套；dpm 一个都没有。

**后果**：
- 风险：L07 漏一处回滚就是跨臂污染，这正是 `test_stale_solvable_order_independent`（`tests.rs:1670-1698`）钉住的 bug 类；dpm 结构上无此风险。
- 语义：L07 在"同一构造子的多个参数槽方程"中途失败时，部分解已写进 `spec.acc` 并被 `walk_con` 取回（`646`），靠臂边界兜底；dpm 失败即整体丢弃。
- 性能：L07 `extend` 是 O(1) cons（`mod.rs:331-339`），dpm 组合是层列表拼接 O(1)（`dpm: eval.rs:30-56`）；但 dpm 每解一条方程就对**剩余整张方程表**做一次 `subst_val`（`elab.rs:56-59`，产物是延迟 `Val::Sub`，不立即推开），L07 只包当前一对。实际影响被"D2"抵消：`check_pm` 每次只送一条方程（`dpm: elab.rs:221,247`），多方程路径在 checker 里是死代码，只有单测跑（`elab.rs:481-496`）。

### D2 谁是"可解"的：solvable 集合 vs 任意 bare var

**L07**【事实】`solvable: Vec<Lvl>`（`pattern_match.rs:57`），基线 = `cxt.bind_slots()`（`136`；`cxt.rs:360-376`：遍历 env，剥掉 `VSub` 后仍是"指向自身 vvar 的裸槽"才收，故 `let` 定义槽天然排除）；走查中每个模式绑定器 push 自己的层级（`414,494,552,563,609`）。判定条件四合一（`unification.rs:901-914`）：`sp.is_empty() && solvable.contains(x) && 对侧不是 Flex && !val_mentions_lvl(v,x)`。

**dpm**【事实】`as_var`：任何 `Val::Ne(Ne::Var(x, sp))` 且 `sp` 为空即 `Some(x)`（`dpm: elab.rs:116-124`）；`unify1` 在**所有**结构规则之前先试 `u`、再试 `v`（`74-93`）。没有任何"可解集"。

**差异实质**：在两者共有的片段（λ/def 参数 + 变量模式）上，两边可解集**几乎重合**——L07 的基线就是"全部 bind 槽"，dpm 的 `Ne::Var` 也恰好只能是 bind 槽（`define` 存的是值不是 vvar，见 `context.rs:136-157`）。真正的差别只有三点：
1. L07 显式登记，可把"瞬时层级"排除在外：η 下钻 `l+1`（`unification.rs:939-962`）与探测的 scratch 层级（`pattern_match.rs:319-323`，scratch 只加进**探测局部**的 solvable 副本）；
2. L07 在对侧是 Flex 时让位给 meta 规则（`905`、`919`），dpm 无 meta；
3. dpm 无 occurs 前置（见 D6）。

**结论**：不存在"dpm 过度求解、L07 更保守"的笼统结论。L07 的保守只针对**非槽位层级**（瞬态 rigid），这是 stale-solvable 修复的直接产物（`pattern_match.rs:213-216` 的注释把机制说透）；dpm 的激进只有 occurs 一处。

### D3 构造子注入性与索引方程

**L07**【事实】特化方程 = 头部 `Val::Sum` 的参数表与构造子返回类型 `Val::Sum` 的参数表逐槽 `zip` 合一（`pattern_match.rs:365-394`），含类型参数与全部索引；Sum 的注入在合一器里是"同名即逐参数"（`unification.rs:983-995`），构造子值的注入是"同 `case_name` 且头 enum 同名则逐 datas"（`1003-1031`，且显式不比 `typ` 的值，理由见 `996-1002` 注释）；此外有无条件的头部精化 `x := SumCase{typ, case_name, datas}`（`650-667`）。

**dpm**【事实】方程只来自 `Id` 的两个索引（`dpm: elab.rs:221,247`）；注入性只有三条硬编码：`Refl/Refl`、`Zero/Zero`、`Succ/Succ`（`96-106`），其余走 `conv` 兜底（`107-110`），都不成立则 `Idk`（`111`）。

**差异实质**：L07 的注入是"每个 enum 的构造子 × 每个参数槽"的通用模式；dpm 是"内建 Nat/Id 的固定规则集"。L07 还多一条 dpm 没有的通道：当 scrutinee 类型是函数应用（`W (n => succ zero)`、`V n`）而不是 `D p̄ ī` 时，索引方程对可能根本不存在，此时**只有**头部精化能给出 `x := ctor`。

**后果**：通用性差一个量级——dpm 无法表达 `Vec` 这类索引族（语言里没有 enum 声明，`dpm: src/syntax.rs:156-170, 84-112` 只有 `U/Nat/Id/Π/λ`），L07 可以（`tests.rs:191-213`）。反过来在 dpm 的表达力内，`Succ` 的注入是"去构造子"式的（结构注入），L07 的注入是"同位置参数相等"（参数本身是构造子值时再由 SumCase 继续分解）——在共同片段上等价。

### D4 上下文/槽位处理（含对任务简报一处口径的更正）

**L07**【事实】`subst_cxt`（`cxt.rs:333-352`）：`env` 逐槽包 `Val::VSub`、`src_names` 的类型逐条包，`lvl / locals / pruning / decl` 一概不动；σ 为空直通。**lvl 不缩小**。

**dpm**【事实】`subst_ctx`（`dpm: context.rs:174-186`）：`types` 全量 `subst_val`、`env` 全量 `subst_env`、`names/pos` 克隆；`lvl` **同样不动**（`176` 注释明写 "the `lvl` is *not* changed: substitutions restrict the values, not the number of binders"）。

**更正**【事实】：任务简报"dpm `subst_ctx` … unify 成功时 lvl = g-1 缩小"只对两处成立——(i) `insert_sub` 造出的 `Sub` 的域：`Sub::new(g.pred(), g, …)`（`dpm: subst.rs:45-49`）；(ii) `unify_s` 穿给**剩余方程**的 `lvl = s`（`dpm: elab.rs:54-60`）。而 `check_pm` 丢弃了返回值里的 `lvl`（`dpm: elab.rs:222` 只取 `sub`，`..` 忽略 lvl），`ctx.lvl` 全程不变。

**语义后果**：
- 两侧都不会出现 de Bruijn 索引错位或运行时 env 布局漂移：被解变量仍占原槽，值的读点由 force 展开（L07 `mod.rs:697-719` 的 `frcs` Rigid 臂；dpm `eval.rs:154-161` 的 `frc_ne_s` + `lookup_sub`）。这正是旧 L07"改写 env 槽 + quote→eval 刷新上下文"那一族 bug（README §6 首行）在新架构下被"按构造排除"的原因，dpm 从原版继承的也是这个设计。
- 差异在"施加 σ 的方式"：L07 只包裹、不动结构（`pruning` 尤其不动——它是 invert 的槽位事实）；dpm 重建 `types/env` 两个 Vec，但值是延迟 `Val::Sub`，所以复杂度仍是 O(n) 轻量重建。
- 【存疑】dpm 的 `Sub` 带 dom/cod 元数据，而 `ctx.lvl` 从不跟着缩；`subst_sub` 有 `if s1.dom > s2.cod panic`（`dpm: eval.rs:31-33`）。当前调用面（`subst_ctx`/`subst_cl`）不触发，但库用户把该 Sub 与 `id_sub(ctx.lvl)` 组合会 panic。详见第 6 节。

### D5 覆盖性 / 不可达

**L07**【事实】三层：
1. 顶层：对 scrutinee 类型的每个构造子，在"meta 快照 + σ + 局部可解集"下跑一遍特化方程判断可达（`140-149` → `276-348`）；**fuel 耗尽的失败按可达处理**（`336-341`，保守方向：宁可要求覆盖）；
2. 嵌套：走查中把 (路径, 字段 Sum) 记进 `pending_pos`，整臂成功后以终态 σ/solvable/lvl 提升为 `nested_checks`（`169-177`），臂循环结束后统一探测（`228-261`）；覆盖集用 `PosCover` 沿路径判定（`mod.rs:118-139`）；
3. 臂级：通配臂之后的臂报"分支不可达"（`152-160`）；`Walk::Unreachable` 报"分支不可达"且**不产生覆盖义务**（`203-209`）。

**dpm**【事实】没有任何覆盖检查。`refl` 的合法性**就是**覆盖判定：`unify` 返回 `Succ` → 合法（`dpm: elab.rs:221-227`）；`Abs` → 报错并建议改写成 `(!)`（`228-234`）；`Idk` → 报 "not sure"（`235-238`）。`(!)` 的合法条件是同一方程判 `Abs`（`247-255`），且右端必须为空（`255-266`）。

**后果**：双方都**拒绝**"写出来的不可达臂"，但形态完全不同——L07 允许"某构造子不写"（不可达 → 无覆盖义务），dpm 必须显式写 `(!)` 并且该方程必须已被判为矛盾；dpm 没有分支矩阵，所以不存在"漏臂"这种诊断，λ 的每个参数恰好一个模式。

### D6 occurs check

**L07**【事实】浅层 occurs `val_mentions_lvl`（`mod.rs:1393-1434`，工作栈实现；`VSub` 只扫解值不扫 σ 映射值，`1410-1416`）。两处用：特化解处失败 → `Err` → 分支不可达（`unification.rs:908-910` → `pattern_match.rs:645-649` → `203-209`）；头部精化处失败 → 跳过精化但不阻断臂（`663-665`）。

**dpm**【事实】无 occurs check（`dpm: NOTES.md:283-285` 明列为"Inherited limitations"），`unify1` 直接 `insert_sub(g, x, v)`（`82-93`），不检查 `v` 是否提到 `x`（而 `insert_sub` 的类型标注 `[x↦v] : Sub (G/{x}) G` 正要求这一点，`dpm: subst.rs:44-49`）。

**后果**：这是两侧**接受集**最大的单点差异。具体程序见 §4-A：dpm 实测接受自指解 `m := plus m zero` 并打印出该类型（函数永远无法应用，与 NOTES 描述一致）；L07 走 rigid 解臂 → occurs 命中 → 分支不可达。

### D7 结果分档：二值 vs 三值

**L07**【事实】`Result<(), UnifyError>`（`unification.rs:825-833`）；fuel 耗尽也折叠为 `Err`，只在文案上加 `(fuel exhausted)` 尾注（`pattern_match.rs:382-392`、`mod.rs:1317-1333`）。

**dpm**【事实】`UnifyRes::{Succ, Abs, Idk}`（`dpm: elab.rs:26-33`），三个消费者各给三种诊断（`228-270`）。

**后果**：dpm 能区分"矛盾（可写 `(!)`）"与"不可判定（该模式不合法）"，诊断三档、用户可据此修；L07 只有一档"不相容"，且 fuel 耗尽与真矛盾在**判定**上被混同（README §7.2 自认是有界降级：极深负载下可能把合法分支误判不可达）。反向看，L07 的探测侧对 fuel 做了保守偏置（`336-341`），而臂内方程侧没有——同一原因在两侧可能给出不同判定，这是 L07 已知的不对称。

### D8 卡住的值与"精化后复归约"

**L07**【事实】`Tm::Match` 是核心语法（`mod.rs:92-93`），`eval` 产出 `Val::Match(scrut, env, cases, pending)`（`1181-1202`），应用卡住 match 时把实参压进 `pending`（`1060-1063`）；`force` 的 Match 臂重新 force scrutinee，一旦是构造子值就重选分支并把 pending 在**值层**逐个应用（`609-628`）；`frcs` 推 σ 时对 Match **推进 scrutinee**、包裹 env/pending（`773-784`）。

**dpm**【事实】没有 Match 值。模式 λ 求值即 `Ne::Lam`（`dpm: eval.rs:281-286`），匹配卡住 → `stuck_lam`（`267-269`），再次 force 带非空 spine → `frc_ne` 重新 `napp`（`145-148`），在 σ 之下 → `frc_ne_s` 用替换后的 env/spine 重跑 `match_`（`158`）；`match_` 每次都从第一个模式重跑（`233-263`，NOTES 偏离 2，`NOTES.md:86-93`）。

**差异实质**：两者都能在精化后复归约，但**触发条件**不同——L07 由"scrutinee 变成构造子值"驱动（不需要新实参），dpm 由"来更多实参"或"值落在替换之下"驱动（不存在"scrutinee 被精化"这回事）。

**后果**：L07 能把卡住形态原样打印并回读（`Tm::Match` + pending 以应用形式呈现，`tests.rs:646-671` 断言输出含 `match m` 与 `) j`）；dpm 的核心语言没有 case 树，卡住的模式匹配只能打印成 λ 本身（`dpm: NOTES.md:288-290`，`quote_ne` 的 stuck 分支 `dpm: eval.rs:489-498`），信息量更低但仍是合法回读。

### D9 模式组形态与"首匹配"

**L07**【事实】`match` 表达式 + 每臂一棵嵌套 `Pattern` 树（`parser/syntax.rs:16-19`）；逐臂独立下钻、用户书写顺序 = 运行时首匹配（`pattern_match.rs:152-220`；运行时 `eval_aux` `680-694`）。

**dpm**【事实】λ 上一串扁平模式（`dpm: src/syntax.rs:76-80`），`check_pm` 逐个消费并递归精化后续上下文（`196-274`），`wrap_lam` 把整串塞回一个 `Tm::Lam`（`277-293`）。

**后果**：
- 用户可见：dpm 没有"对一个值做多分支"的能力（无 case），消去只发生在 `Id` 上；L07 的"每臂独立方程集"允许同一类型多次分裂。
- 嵌套精化顺序：L07 每臂由外到内、臂间靠 σ 快照隔离；dpm 由左到右，且前一模式的解对后续模式的**域类型**可见（`dpm: elab.rs:224` `subst_cl(&sub, b)` 应用在余域上）。在 L07 里等价的写法是把 match 嵌套（`tests.rs:204-210` 的 `match x { … match y { … } }`）。
- 通配臂语义只有 L07 有（`is_catch_all`，`pattern_match.rs:758-763`；`covers` `750-755` 还把"名字不是本类型构造子"的 `Con` 当变量绑定兼全覆盖，见 `466-481`——dpm 的 `Var` 模式在语法层就没有这种歧义）。

### D10 期望类型与臂上下文（L07 独有的一层）

**L07**【事实】每臂在 `check` 之前做两件事：`cxt_arm.subst_cxt(&self.sub)`（`183`）与期望类型**重锚**——`force(cxt_arm.decl(), wrap_sub(&self.sub, expected))` 后若不是 Flex 则 `quote` → `eval` 到臂上下文（`190-196`）。理由（README §1.4）：让期望里的卡住 match 与 meta 解物化副本有同样的 env 布局，`struct_eq::val_eq` 结构快路径才能命中，否则逐层展开永不收敛。

**dpm**【事实】每模式 `subst_ctx(&sub, ctx)` + `subst_cl(&sub, b).apply(Val::Refl)` 得到剩余余域（`dpm: elab.rs:222-225`）。

**差异实质**：语义上两者等价（都在解之下重新解释期望类型）；L07 多出的 quote→eval 完全是为**元变量求解器**服务的布局规整，dpm 无 meta 故不需要。这条差异在"模式匹配正确性"上不产生分歧，只在出现 meta 的边界场景（L07 已知限制 #1，README §7.1）才可见。

### D11 编译期成本

**L07**【事实】顶层覆盖 = 每构造子一次探测，每次独立充值 fuel + meta 快照（`300-346`）；嵌套记账在臂循环后统一探测（`228-261`），量级 O(位置数 × 构造子数 × 臂数)。dpm：零探测，`check_pm` 对每个模式一次 `unify`（单方程）。

**后果**：L07 用编译期成本换覆盖性保证；dpm 零成本，但它**不需要**覆盖性概念（唯一可消去的类型只有一个构造子，且模式串长度 = 参数个数，"漏臂"无从表达）。这是成本差异而非能力差异。

### D12 表达力边界（承接 D3）

**L07**【事实】`match` 要求 scrutinee 类型 force 后是 `Val::Sum`（`125-128`），否则直接报"match 的对象必须是和类型"——**类型层卡住的计算会挡住 match**。dpm 的 `refl` 要求域 force 后是 `Val::Id`（`dpm: elab.rs:216-220`），类型层卡住同样挡住。两者是同构的限制（都在入口 force 一次类型）。

**L07 多出来的**：索引位置可以是函数值（`enum W(f: Nat -> Nat)`，`tests.rs:1676-1697`），此时合一靠 `Val::Lam/Lam` 的 η 比较（`unification.rs:939-946`）+ `v_applicable` 守卫（`947-962`）；dpm 的索引只到 U/Nat 层，没有这一层。

## 可观测的语义差异

### A. 自指索引（occurs）：dpm 接受，L07 拒绝

dpm（**实测**，`dpm-nbe.exe nf`，exit 0）：

```text
let bad : (m : Nat) -> Id Nat m (plus m zero) -> Nat = \ m refl . zero; bad
```

输出 `λ m refl . zero : (m : Nat) → Id Nat m (plus m zero) → Nat`。`m := plus m zero` 被接受，函数永远无法应用。

L07 的对应写法：

```text
enum Nat { zero  succ(x: Nat) }
enum Eq[A](x: A, y: A) { refl(a: A) -> Eq a a }
def add(x: Nat, y: Nat): Nat = match x { case zero => y  case succ(n) => succ (add n y) }
def bad(m: Nat, e: Eq Nat m (add m zero)): Nat = match e { case refl(a) => zero }
```

【推断】报"分支不可达：模式 … 与被匹配类型不相容"。代码链：`unify_indices`（`pattern_match.rs:356-396`）→ `unify(Rigid m, Match(add m zero))` → rigid 解臂（`unification.rs:901-914`）→ `val_mentions_lvl` 命中 `m` → `Err` → `walk_con` 转 `Walk::Unreachable`（`645-649`）→ `compile` 报错（`203-209`）。标"推断"仅因未实际执行 L07。

### B. 荒谬消去：两侧都做，形式互斥

dpm（**实测**，exit 0）：`let C : (A : U) -> Id Nat (suc zero) zero -> A = \ A (!); C` → `λ A (!) . ⊥ : (A : U) → Id Nat (suc zero) zero → A`。

L07：`def C[A](e: Eq Nat (succ zero) zero): A = match e { }` —— 零臂 match，接受（同型回归钉 `tests/l07_blackbox_v3.rs:337-347`；同族 `307-317` 证明"缺构造子只列可达者"）。反过来，L07 若真写 `case refl(a) => zero`，等价于 dpm 写 `refl`：dpm **实测**报 `It should not be 'refl' for equation between zero and zero, in fact you should try pattern '(!)'`（`dpm: elab.rs:228-234`），L07 报"分支不可达"（`tests/l07_blackbox_v3.rs:321-333`）。差别在产物：dpm 有 `Tm::Bot`/`Val::Bot` 作为分支体（NOTES 偏离 7），L07 是零臂 `Vec<case>` 的 `Val::Match`。

### C. 卡住索引方程：dpm 报"not sure"，L07 可能解掉

dpm（**实测**，exit 1）：

```text
let bad : (x y : Nat) -> Id Nat (plus x zero) (plus y zero) -> Nat = \ x y refl . zero; bad
```

→ `I am not sure if there should be a pattern 'refl' for equation between plus x zero and plus y zero.`（`Idk`，`dpm: elab.rs:111,235-238`）。

L07 对应：`def f(x: Nat, y: Nat, e: Eq Nat (add x zero) (add y zero)): Nat = match e { case refl(a) => zero }`。【推断】**可能接受**——两侧都是 `Val::Match`，合一器的 `Match vs Match` 臂先合一 scrutinee（`unification.rs:1034-1085`），`x` 在 `bind_slots` 基线里（`pattern_match.rs:136`）故解得 `x := y`，两值随即相等。若成立，这是 L07 的"卡住项结构比较"带来的**更宽接受集**（也意味着 arm 内可能顺带解掉外层变量）。未实测，列第 6 节第 2 条。

### D. GADT 索引族：L07 能写，dpm 无法书写

L07（`tests.rs:199-213` 的 `t`）：

```text
enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}
def head[T, L: Nat](x: Vec[T] (succ L)): T = match x { case cons(x, _) => x }
```

dpm 里没有 enum 声明（`dpm: src/syntax.rs:84-112` 的 `Raw` 只有 `U/Nat/Id/Π/λ/let`），`Vec` 连类型都写不出来；唯一可用的索引族是内建 `Id`。所以"谁的模式匹配更通用"这个问题在类型层就已经分出胜负，与模式编译算法无关。

### E. 不可达臂的写法

L07：`def only_nil(v: Vec[Nat] zero): Nat = match v { case nil => zero }` 接受（`tests.rs:451-470`）；补一个 `case cons(x, xs) => x` 则整条 def 报"分支不可达"（`tests.rs:474-493`）。
dpm：同一意图只能写成 `λ … (!)`，且 `(!)` 必须是最后一个模式（`dpm: parse.rs:379-382`），写成 `refl` 是硬错误。**两侧都拒绝写出来的不可达臂，但 dpm 连"写一个不可达分支"这种语法都不存在。**

## 机制有无矩阵

| 机制 | L07 | dpm | 备注 |
|---|---|---|---|
| 显式替换（延迟替换值） | 有 `Val::VSub`（`mod.rs:385-391`） | 有 `Val::Sub`（`dpm: eval.rs:59-64`） | 同源 |
| 解的可变累积 | 有 `SpecSolve.acc`（`unification.rs:42-45`） | 无（返回值 `Succ{sub}`） | D1 |
| 剩余方程置于解之下 | 惰性包裹（`860-865`） | 急切 `subst_val` 剩余表（`elab.rs:56-59`） | 效果等价 |
| 臂/探测回滚 | 有（Rc 快照、meta 快照、局部状态） | 不需要 | D1 |
| 显式可解集 | 有 `Vec<Lvl>` + `bind_slots` | 无（形态判定 `as_var`） | D2 |
| 元变量参与特化 | 有（Flex 优先规则 `905,919`） | 无 | D2 |
| 通用构造子注入 | 有（Sum/SumCase 规则） | 无（Refl/Zero/Succ 三条） | D3 |
| 索引族 / GADT | 有（enum + 返回类型） | 无（只有内建 Id） | D3 |
| 头部精化（`x := ctor`） | 有 | 无对应物 | D3 |
| occurs check | 有（浅层工作栈） | 无（NOTES 明示） | D6 |
| 三值判定 Succ/Abs/Idk | 无（二值 + fuel 尾注） | 有 | D7 |
| 覆盖性检查 | 有（顶层 + 嵌套 + PosCover） | 无 | D5 |
| 不可达臂诊断 | 有（报错、不产生覆盖义务） | 无语法（`(!)` 之外仍是错误） | D5 |
| 荒谬消去 | 零臂 match | `(!)` + `Tm::Bot` | 第 4 节 B |
| 首匹配 / 分支顺序 | 有（用户顺序 + 通配遮蔽报错） | 无（无 case 树） | D9 |
| 嵌套构造子模式 | 有（`Pattern::Con` 递归树） | 无（扁平模式串） | D9 |
| 卡住匹配的复归约 | 有（force 重选 scrutinee） | 有（frc 重 napp / σ 下重跑 match） | D8 |
| 卡住匹配可作为核心项 | 有 `Tm::Match` | 无（打印成 λ） | D8 |
| 期望类型重锚 | 有（quote→eval，为 meta 布局） | 无（直接 `subst_cl`） | D10 |
| 类型层卡住即挡住消去 | 有（`match` 需 Sum） | 有（`refl` 需 Id） | D12 |
| 函数值索引 / η 比较 | 有 | 无（索引只到 U/Nat） | D12 |

## 存疑与待核实

1. **【存疑·高】§4-A 的 L07 侧未实测**。结论建立在"rigid 解臂先于结构比较命中、occurs 守卫返回 Err"这条代码链上；`unify_indices` 的参数顺序（头部在前，`pattern_match.rs:372-393`）已按 `m` 在头部确认，但若 `add m zero` 在实参初始化时已被 force 成别的形态（例如 `add` 的返回类型 meta 尚未解），走查路径可能不同。建议 Lead 用 L07 黑盒跑一次确认。
2. **【存疑·中】§4-C 的 L07 是否真接受卡住索引方程**。`Match vs Match` 臂（`unification.rs:1034-1085`）在解完 scrutinee 后还要逐分支比较体；`add` 的两条体在不同 env 下求值，比较过程可能反过来解掉外层 `y`（`901-928` 对分支体内出现的 bare rigid 同样生效），从而给出比"x := y"更意外但（按充分性）仍成立的解。是否触发取决于 `val_eq` 快路径是否命中（`1041-1055`）。未实测，不下结论。
3. **【存疑·中】dpm 的 `Sub` dom/cod 与不缩小的 `ctx.lvl` 只靠调用约定对齐**。`insert_sub` 给出 dom=`g-1`（`dpm: subst.rs:45-49`），`check_pm` 丢弃 `Succ.lvl`（`elab.rs:222`）并继续以 `ctx.lvl = g` 绑定后续变量；若库用户把该 Sub 与 `id_sub(ctx.lvl)` 组合，`subst_sub` 的守卫（`dpm: eval.rs:31-33`）会 panic。当前源码路径不可达，属于 API 层的脆弱面，不是 checker 的 bug。
4. **【存疑·低】dpm 的 `as_var` 不检查 `x < g`**（`dpm: elab.rs:116-124`）。良型输入下 `Ne::Var` 的层级必在上下文内，但库 API 可以构造越界值并得到 `insert_sub(g, x≥g, …)` 这种 dom/cod 倒挂的替换。不可由源码触达。
5. **【存疑·低】L07 的参数表 `zip` 不查长度**：`unify_indices` 有显式长度检查（`pattern_match.rs:369-371`），但 `Sum` vs `Sum`（`unification.rs:983-995`）与 `SumCase` vs `SumCase`（`1020-1029`）只有 `zip`。靠"同名 enum 参数个数由声明固定"这条不变式兜底，未见断言。
6. **【存疑·低】L07 探测与臂内方程可能不同步**：README §7.4 自认（探测用 scratch 层级、臂内用真槽，"方程解依赖层级数值本身"时判定可能不一致），现有测试未触发。
7. **【事实·影响解读】dpm 的多方程 `unify_s` 在 checker 里是死路径**：`check_pm` 只送一条方程（`dpm: elab.rs:221,247`），多方程只被单测覆盖（`481-496`）。因此"剩余方程置于解之下"在 dpm 里**不影响任何源程序**，真正的跨模式精化靠 `subst_ctx` 推进上下文；L07 的 `unify_indices` 则是每个构造子臂的活路径（`Vec` 每臂 2 条方程）。两边的"多方程"不在同一层级上，比较时不要直接对位。

## 给 Lead 的三条要点

1. **骨架同源，分野在"判定分档"而不是"特化合一"**：两侧都用显式替换 + 解随身带 + 读点 force + 上下文不缩 lvl，连"剩余方程置于解之下"都是同一思想。凡出现"接受集"差异，先查这三条：dpm 三值（Succ/Abs/Idk）、dpm 无 occurs check、L07 有独立覆盖探测。反过来，报告里不宜写成"L07 的合一算法比 dpm 强"——在共同片段上它们的可解集几乎重合（D2）。
2. **表达力差距来自类型层，不来自模式匹配**：dpm 只有内建 Id，所以它的"构造子注入"退化成 Refl/Zero/Succ 三条硬编码、也没有头部精化与索引族；L07 的 Sum/SumCase 通用注入 + `x := SumCase` 才让 `Vec`/函数值索引成立。若要把两者放在同一把尺子上比，必须先归一类型层，否则"谁的模式匹配更通用"这个问法会误导整体结论（D3/D12/第 4 节 D）。
3. **两处最值得复核的实测点**：§4-A（dpm 接受自指索引、L07 预期拒绝）与 §4-C（dpm 报 not-sure、L07 可能解掉卡住方程）。前者已验证 dpm 侧、L07 侧是代码链推断；后者两侧都未实测。这两点决定了"L07 更严格 / 更宽松"的方向：A 指向 L07 更严格，C 指向 L07 更宽松——**同一维度上两侧不是简单的强弱关系**，最终结论必须按"接受集 / 诊断分档 / 表达力"三个坐标分开陈述。
