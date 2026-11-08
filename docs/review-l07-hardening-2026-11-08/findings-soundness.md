# L07 健全性核心改动 review（reviewer-soundness）

> 范围：`2e598594`(P2 预算) / `a474bf98`(P1 传递 occurs) / `2d73b66e`+`691623f8`(P3 两刀) /
> `0c73b65d`(P15 struct_eq pending) / `30547abf`(P5 跨 meta 环守卫) / `999d617f`(P8 宽松合一收窄)。
> 基线 `641c52fe`，HEAD `008f42ed`。行号均为 HEAD 工作区（`src/L07_sum_type/…`）。
> 方法：逐 commit diff + HEAD 源码通读 + `git show <old>:<file>` 作"修复前"oracle（不改 src，未跑 cargo）。

## 结论

**方向正确、无新增"接受非法程序"型健全性缺陷**：P15 是**真修**（旧递归 oracle 证明丢失的正是
pending 值比较）；P1/P2/P3/P8 都只会让接受集**收缩**，不会把旧拒绝的程序变成接受（分析见 Q3）；
P5 环守卫实现确定、状态平衡。全套测试绿（Lead 实测）。

**最严重问题（S1，接受集回归）**：P3 第二刀把若干**确定的**规范值冲突降级为 `Undecided`
（`unify_no_arm` 的 definite 集合不完整），而覆盖探测把 `Undecided` 当**可达**处理 ⇒
一类**合法的空类型零臂 match 被拒绝**（基线 641c52fe 接受）。且判定随冲突值的"形态"不一致：
`Bool ≐ Nat`（Sum×Sum）判 `Absurd`→接受；`String ≐ Nat`（LiteralType×Sum）判 `Undecided`→拒绝，
两个类型在语义上同样为空。**次严重（S2）**：P1 的 `occurs_transitive` 在 `VSub` 臂丢弃外层 σ
（Lead 已单元级证实 `VSub(VSub(Rigid,∅), σ)` 与 `force` 语义不一致；`VSub` 全形态一致性缺口），
另不跟随 `Flex`/meta 解值、2048 预算耗尽按"未出现" ⇒ P1 是部分闭包而非全闭包。

## 逐项结论

### Q1a. struct_eq 比较 stuck-match pending 值（0c73b65d）—— ✅ 真修

- **根因与修复都已证实**：`struct_eq.rs:187-215` 的 `Val::Match` 臂现在逐项比
  scrutinee / env / 分支体 / **pending（icit+值）**；pending 值先压栈（`:204-209`），LIFO 最后弹出，
  访问序与旧递归 `scrutinee → env → 分支体 → pending` 一致；比较对称、无方向性。
  用 `git show 2309e2a4^:src/L07_sum_type/struct_eq.rs` 作 oracle 确认旧递归版确有
  `xi == yi && val_eq_go(xv,yv)`，`2309e2a4` 迭代化时漏掉 —— 与 commit 说明一致。
- **覆盖所有 Val 形态**：`Val` 只有 `Match` 带 pending（`mod.rs:184-219`）；其余惰性形态
  `VSub` 异实例一律 `false`（保守回落慢路径，`struct_eq.rs:82-88`），`Obj/Sum/SumCase/Lam/Pi` 全字段比较；
  `Sum` 的构造子名表未比，但同名 enum 必同表（重定义禁止），不可达。**false→慢路径** 方向安全，
  未发现新的"假相等"通道。
- **终止性**：`EQ_BUDGET=20_000`（`struct_eq.rs:36`）耗尽按不等（保守）；非循环结构上不会自旋。
- 唯一残余影响：修复会使"pending 仅可转换而非结构相同"的合法比较回落到慢路径，可能因预算/stuck
  变为 `Undecided` 而拒绝（方向保守，非健全性缺陷）。

### Q1b. 传递 occurs（a474bf98）—— ⚠️ 修了主类，但语义不等价、存在漏检

- 已覆盖：两个 rigid 解臂（`unification.rs:962-1009`）在写 σ 前跑
  `val_mentions_lvl`（浅）+ `acc.mentions_any_solved` 前置筛选 + `acc.occurs_transitive`
  （`mod.rs:321-385`）。调用点齐全（`Subst::extend` 的另一点 `pattern_match.rs:710-727` 头精化
  目标是"被匹配变量本身"，其 datas 是 fresh 槽、解不出该变量，浅守卫足够——已逐点论证）。
  >2 跳环由 `Rigid` 解值递归跟随覆盖；`test_occurs_check_transitive_chain` 反事实有效（修复前接受）。
- **漏洞 A（机制已证实，Lead 单元探针）**：`Val::VSub(inner, s2) => go(inner, s2, …)`
  （`mod.rs:378-379`）**丢弃外层 σ**；而 `force/frcs` 对 `VSub` 的语义是
  `frcs(outer, VSub(v,s2)) = frcs(compose(outer,s2), v)`（`mod.rs:884-888`）。
  Lead 构造 `VSub(VSub(Rigid(0), ∅), σ)`、σ={0↦7,7↦9}：force 语义应看到 9，occurs_transitive
  返回 false。⇒ **嵌套 VSub 槽里的环可能漏掉**，P1 修复不完整。程序级可达性未构造（见"未能验证"）。
- **漏洞 B（推断）**：`Flex/Decl/Prim` 臂只扫 spine、不跟随 meta 解值（`mod.rs:354-356`）；
  σ 链环若经"meta 解值提到已解 rigid"中转仍可漏（meta 侧 P5 只做 force 有界化，见 Q4）。
- **漏洞 C（设计取舍）掉预算**：`BUDGET=2048`（`mod.rs:336-341`）耗尽按"未出现"（宁漏不误杀），
  >2048 节点的解值/长链仍会漏环。**反向不精确**：`Rigid(y, sp)` 已解时同时扫"解值"和"spine 实参"
  （`mod.rs:343-353`），若解值是丢弃实参的 λ（如 `n => zero`）会**假报环 → 误拒合法分支**；
  与"宁漏不误杀"的取向不一致。
- 注释与实现不符：`unification.rs:972-975` 仍写"先置于 acc 之下 **force 一次**再查"，实际没有
  force（commit message 明说 force 不行）——S4。

### Q2. MATCH_CMP_BUDGET（2e598594）—— ⚠️ 机制可用，语义/注释有边界缺陷

- **计数语义 = 递归深度**，非总步数：`Infer.match_cmp_depth: Cell<u32>`（`mod.rs:613`）
  在 `(Match, Match)` 臂**入口**先查 `>= MATCH_CMP_DEPTH(40)`（`unification.rs:1125-1131`），
  再 `+1`，闭包体结束（含全部 `?`/`return`）后恢复 `saved_depth`（`:1184`）。
  ⇒ 兄弟分支/跨臂**不累加**，只有嵌套路径累加；因此**不依赖臂顺序**（但共享 fuel 仍顺序相关）。
  无顶层 reset，靠"平衡恢复"维持；正常路径不泄漏（panic 会泄漏，见 Q4 同类）。
- 超限行为：`note_unify_kind(Undecided)` + `Err`（`unification.rs:1128-1129`；2e59594 原为默认
  Absurd，2d73b66e 补 note）。**不会放过真矛盾**（任何 `Err` 在所有消费点都是失败/不可达/无法判定），
  但**会把可判定问题误判为不可判定**：`walk` 拒绝且文案变"无法判定"，`probe_accessible` 当可达
  → 可能凭空多出"缺少构造子"（方向保守，接受集只收缩）。
- **缺陷（S3）**：预算检查在**结构快路径之前**（`:1126-1131` 先查限，`:1133-1153` 才是
  `struct_eq` 快路径）。故嵌套深度恰为 40 时，**字面相同的一对也会被直接拒绝**；而 `mod.rs:627`
  注释宣称"结构快路径命中时根本不进这个预算"、commit/PR 宣称"同一 def 的两份值在有限层内就能比完"
  ——与代码不符。无回归钉覆盖 depth 39/40 + 快路径边界。
- 与 U/循环结构：`U` 无 Match，无影响；值图是 DAG（无手工 Rc 环），`struct_eq` 有 20k 预算兜底，
  未见自旋。**总工作量无上界**：深度限制只限路径，分支多的递归 def 在 40 层内仍可能组合爆炸
  （2^40 理论上界）——未实测，列入"未能验证"。

### Q3. UnifyKind 两刀（2d73b66e + 691623f8）—— ⚠️ 方向安全，但有接受集回归与分档不完整

- **产生点**：`Absurd` = 默认（53 处 `Err(UnifyError)` 未 note 者，含 occurs 环、跨 enum 构造子头、
  `Match/Match` 分支结构不符、pending 长度不符）；`Undecided` = 17 处显式 note（solve/rename/invert/
  prune 族、spine 长度不齐、异名 Prim、`Match vs 非 eta`、预算超限、`unify_no_arm` 非 definite）；
  `Fuel` = `unify` 入口 fuel==0（`unification.rs:895-905`）。`note` 取 rank 最大单调累积
  （`mod.rs:719-736`），`unify_indices` **每个方程前 reset**（`pattern_match.rs:433`）后读
  （`:445`）。
- **消费点**：① `probe_accessible`：只有 `Absurd` 判"不可达"，`Undecided/Fuel/Msg` 一律按**可达**
  （`pattern_match.rs:387-397`）⇒ 多要求覆盖；② `walk_con`：`Absurd→Walk::Unreachable`，
  其余→`Walk::Undecided`（`pattern_match.rs:701-709`），后者**不查分支体但仍 push 错误**
  （`:244-259`）⇒ 仍拒绝；③ `unify_catch` 不消费 kind（仅 fuel 尾注，`mod.rs:1705-1726`）。
- **接受集方向：只缩不涨（已逐点确认）**。任何 kind 都是 `Err`；`Walk::Undecided` 也进
  `errors`；探测侧把非 Absurd 当可达/`Msg` 当可达只会**增加**覆盖义务。⇒ **不存在"之前拒绝、
  现在接受"的路径**。规范值冲突（`zero ≐ succ zero`、不同字面量、Sum 头异名）仍在
  `unify_no_arm` 的 definite 列表（`unification.rs:1232-1247`）→ 仍判 `Absurd`，**未放松**；
  `test_unify_kind_separates_absurd_from_undecided` 钉住。
- **但 definite 列表不完整 ⇒ 合法空类型 match 被拒（S1，见发现 F1）**：列表只有
  `SumCase×SumCase / Sum×Sum / LiteralIntro×LiteralIntro / SumCase↔LiteralIntro / U↔LiteralType`；
  `Sum×LiteralType`、`U×Sum`、`Sum×Pi` 等**同为规范值且形态不同**的确定冲突仍是 `Undecided`
  ⇒ 探测判"可达"→ 要求覆盖 → 拒绝。具体：`enum T(A: U) { c -> T Nat }` 上
  `T Bool` 的零臂 match（`Bool≐Nat`→Absurd→接受），`T String` 的零臂 match（`String≐Nat`→
  Undecided→"缺少构造子 c"→拒绝）；两类型语义上都空，基线两者都接受。
- `unify_no_arm` **不会**把 solve/rename/invert 的"真冲突"归 Undecided：这些点是"解不出来"
  （作用域越界/不可逆 spine/预算窗口），本就不是矛盾；而真矛盾走的是默认 Absurd / definite 列表。
  残余风险：`Match/Match` 的 `cases1.len()!=cases2.len()`、`p1!=p2`（`:1155-1163`）默认 Absurd，
  但"分支结构不同、外延相同"的两个卡住 match 可相等 → 仍是旧的"假 absurd"面（预存在，本两刀未扩大）。

### Q4. 跨 meta 环守卫（30547abf）—— ✅ 实现正确，⚠️ 只做"有界化"不是"消除环"

- **插入/移除**：force 展开已解 meta 时先查 `meta_expanding.contains(m)`（`mod.rs:776-781`，
  Vec 顺序 ⇒ **确定性**，不依赖 HashMap 序），未命中才 `burn`、push（`:788`）、递归，返回后
  `rposition` 移除（`:790-794`）。**所有正常返回（含环早退）都会 pop**；提前返回发生在 push **之前**
  （无泄漏）。panic 路径无 RAII/Drop guard → 栈条目泄漏；但 `Infer` 每 `run` 新建（`mod.rs:1908`），
  当前只污染同一次运行，无跨 run 影响（LSP 若复用 Infer 需注意）。
- **不会误伤合法链**：只有"同一 meta 在一次展开路径上重复"才命中，这是真环（同一 meta 的有限解
  展开不可能重复自身）；兄弟/DAG 共享不误报。**环检测失败回退** = 返回卡住 `Flex(m, sp)`，与旧
  fuel 耗尽的降级同形（旧行为在 fuel=0 时同样返回 Flex），故**判定语义不变、只剩确定性收益**，
  且保留剩余 fuel（`test` 断言 fuel>0，反事实有效：旧代码 64 步烧到 0）。
- **但 P5 只"有界化"**：`solve_with_pren` 仍无跨 meta occurs（`unification.rs:698-733`；rename 只查
  目标 meta 自身 `occ`，`:562-568`），m1:=?m2、m2:=?m1 这类循环解仍可**被创建**，只是 force 现在
  确定性停下。`L07-RISKS.md:37` 标"P5 ✅ 已修（环守卫）"偏乐观，应写"环展开有界化"。

### Q5. 宽松合一收窄（999d617f）—— ✅ 有效，残余仅"判据是名字而非 provenance"

- `loose_string`（`unification.rs:862-882`）：已登记名→按登记类型 `unify(LiteralType, e.ty)`
  （保留旧行为）；未登记名**仅 `sp_is_empty`** 放行，否则 `Undecided`+Err。两臂传
  `sp.is_empty()`（`:1051-1056`）。修复前 `.is_err()` 断言反事实有效（旧 `None => Ok(())` 全员放行）。
- **逃逸舱口复核**：未登记名的裸 `Decl(name, [])` 当前唯一生产者是 `string_to_global_type`
  （`mod.rs:1071-1085`），`Val::Decl` 其它构造点都是已知名/占位（已 grep 全量构造点）；
  未登记名+非空 spine 现在必拒；"字符串在 spine 上/嵌套 Decl/非裸头"都被 `sp.is_empty()` 卡住。
  `Prim` 均为已登记 builtin（`cxt.rs:125-200`），未知名在 elaboration 期报 "name not in scope"
  （`elaboration.rs:448-456`）⇒ 当前**无程序级逃生舱**。
- 残余（S4）：判据仍是"名字是否登记"而非"值是否 st2g 产物"（P8 自己建议的 `Dynamic` 标记未做）；
  **已登记名分支完全忽略 spine**（用 `e.ty` 而非"spine 应用后的结果类型"）——当前不可达成
  假接受（已登记名的值不可能既是类型又被应用），但属未来风险。既有 DEMO/黑盒均只用裸
  st2g 产物，**未见回归**（Lead 全套绿）。

### Q6. 回归测试质量 —— ⚠️ 多数反事实有效，两处偏弱

| 测试 | 修复前反事实 | 评价 |
|---|---|---|
| `test_occurs_check_transitive_chain`（`tests.rs:42-65`） | ✅ 修复前接受→`check_err` panic | 有效；文案断言由 P9 加强 |
| `test_occurs_check_keeps_legit_refinement`（`:68-90`） | ❌ 修复前也绿 | **不触发 `occurs_transitive`**：首方程 acc 空、次方程两侧都是未解 bare rigid → 前置筛选为 false。只钉"普通精度不被破坏"，**无法抓假阳性回归**（S4） |
| `test_struct_eq_compares_match_pending_values`（`:98-134`） | ✅ 修复前 Ok | 有效（断言仅 `can't unify`，语义由 Err 本身承担） |
| `test_nested_match_pending_cannot_prove_false`（`:138-188`） | ✅ 修复前 Ok | 有效（完整 False 推导链） |
| `parity_struct_eq_match_pending`（`tests/l07_fast_parity.rs:503-539`） | ✅ 修复前 run=Ok/fast=Err 分裂 | 但 `assert_parity`（`:49-65`）只断言"两版判定一致"，**双版同时回归成 Ok 也会通过**；"两侧都拒绝"无断言（S4） |
| `test_stuck_match_equation_bounded`（`:196-229`） | ✅ 修复前 >30s（release 256s） | 有效；30s 宽但足够；文案已收紧为含"无法判定"、不含"不相容" |
| `test_stuck_match_nonrecursive_still_equal`（`:289-317`） | ❌ 修复前也绿 | 正向对照，非反事实；深度=1，不触预算边界 |
| `test_unify_kind_separates_absurd_from_undecided`（`:234-285`） | ✅ 后半修复前"分支不可达"→红 | 有效；分类语义即文案，只能测文案 |
| `test_stale_solvable_order_independent`（`:1982-2011`，691623f8 改断言） | ✅ 改动前"无法判定"不出现→红 | **未被削弱**（`check_err` 保证拒绝，另加 `!contains("分支不可达")`）；但把"universal η-rigid ≐ 构造子"钉成 Undecided，正是 F1 接受集回归的语义基础；注释称"既不能证相等也不能证矛盾"对 universal 层级并不成立（η 引入的 fresh rigid 与构造子**不可转换**） |
| `cross_meta_cycle_force_is_bounded`（`:2158-2176`） | ✅ fuel>0 断言旧代码 64→0 → 红 | 有效；直接改内部字段，非程序级 |
| `loose_string_requires_empty_spine`（`:2182-2212`） | ✅ 第二例旧版 Ok→红 | 有效；内部 API 层 |

## 发现表

| ID | severity | 标题 | 证据 | 推理/影响 | 建议 | 置信度 |
|---|---|---|---|---|---|---|
| F1 | **S1** | P3 分档 + 探测"Undecided 当可达" ⇒ **合法空类型零臂 match 被拒**（基线接受），且判定随冲突值形态不一致 | `unification.rs:1232-1247`（definite 列表缺 Sum×LiteralType/U×Sum/…）；`pattern_match.rs:387-397`（`Kind(k)=>k!=Absurd` 即可达）；`:168-177`（缺构造子）；`:244-259`（Undecided 也 push error）；2d73b66e diff（旧探测 `is_ok()||fuel_exhausted`） | 修复前：任意 Err→不可达→无覆盖义务→零臂合法。修复后：非 definite 的确定冲突→Undecided→可达→"match 不完整：缺少构造子 c"→拒绝。例：`enum T(A: U){ c -> T Nat }`，`def f(e: T Bool): Nat = match e {}` 两者都接受（Absurd）；`def g(e: T String): Nat = match e {}` 新版拒绝（String≐Nat→Undecided），但两类型同为**空类型**，零臂 match 合法。**无"旧拒绝变接受"方向**（Q3），只缩不涨 | ①`unify_no_arm` 的 definite 集合补全"两侧均为规范类型值且不同形态"（Sum×LiteralType、U×Sum、Sum/Pi 交叉等），或②明确"保守分档"策略并在 README/测试里登记该接受集回归；③补"合法空类型零臂 match"回归钉（Sum 与 LiteralType 两种形态各一） | 高（代码路径确定；修复前行为由旧分支逻辑确定，需 Lead 跑两条 repro 终验） |
| F2 | S2（程序级可达未证；若可达升 S1） | P1 `occurs_transitive` 的 `VSub` 臂**丢弃外层 σ** ⇒ 嵌套 VSub 漏环；另不跟随 meta 解、2048 预算按"未出现"；反向对"已解 rigid+非空 spine"同时扫解值与实参，可假报警 | `mod.rs:378-379`（`go(inner, s2)`）；frcs 语义 `mod.rs:884-888`（compose）；`mod.rs:354-356`（Flex 不解）；`:336-341`（预算 false）；`:343-353`（同时扫 sol+spine）；`unification.rs:976-1003`（前置筛选调用） | Lead 单元探针已证：`VSub(VSub(Rigid(0),∅), σ)`、σ={0↦7,7↦9}，force 应看到 9 而 occurs 返回 false ⇒ σ 链环可经嵌套 VSub 漏检（P1 未闭全）。L08 参考版同码同缺陷 | VSub 臂改为携带外层 σ（`compose(self, s2)` 或显式传 `(outer, inner)` 双 σ）后再扫；或至少文档化"VSub 槽内环不可检出"；补单元钉（Lead 探针可转正式 test） | 机制高（Lead 已证）；程序级中 |
| F3 | S3 | `MATCH_CMP_DEPTH` 检查在**结构快路径之前**，深度 40 时字面相同的一对也被拒；且 `mod.rs:625-632` 注释"快路径根本不进预算"与实现相反；无边界钉 | `unification.rs:1125-1131`（先查限后快路径 `:1133-1153`）；`mod.rs:625-632`；`README` 未记该预算 | 边界上"本可判等"变"无法判定"→ 拒绝。可达性未构造（需 40 层"结构不同但最终字面相同"的嵌套卡住 match），故记 S3 而非 S1 | 把限检查移到快路径之后（先试 `val_eq`，失败再计数），或至少修注释；补 depth 边界钉 | 代码事实高；触发中 |
| F4 | S3 | `UnifyKind` 的 note 不随 meta 快照回滚（`flex_flex` 双向重试等），旧 `Undecided/Fuel` 可污染后续真 `Absurd` 的终判 | `mod.rs:719-731`（rank 单调累积）；`unification.rs:774-806`（flex_flex 失败→`meta_restore`→反向重试，kind 未恢复）；`pattern_match.rs:433`（仅每方程 reset） | 真矛盾被报成"无法判定"→ 覆盖探测多要求覆盖（放大 F1 的拒绝）/ 文案失真；方向保守（不会放过矛盾） | `meta_restore` 一并恢复 `unify_kind` 水位（或 flex_flex 重试前 `reset`），补混合恢复路径单元钉 | 代码事实高；触发中 |
| F5 | S4 | 回归钉反事实质量：occurs 正向对照不触新路径；parity 钉只比"一致"不比"拒绝"；`test_stuck_match_equation_bounded` 注释与断言矛盾 | `tests.rs:68-90`；`tests/l07_fast_parity.rs:49-65,503-539`；`tests.rs:190-196` vs `:222-224` | 假阳性/双版同回归不会被现有套件抓到；注释误导后续维护者 | occurs 正向钉改用"second equation 的解值真引用已解槽"的构造；parity 加"两侧均 Err"断言；修注释 | 高 |
| F6 | S4 | 文档/注释漂移 + 死代码：README §4.1"失败=分支不可达"、§7.2"(fuel exhausted) 尾注"已过时；`L07-RISKS` §0.1 P2 行"判定与文案不变"与 P3 行矛盾；README 未记 `MATCH_CMP_DEPTH`；PR §5 计数 987 实际 990；`unification.rs:972-975` 的 "force 一次" 无实现；`fuel_exhausted`（`mod.rs:715`）与 `Walk::matched`（`pattern_match.rs:109`）已成死代码；P5 标"已修"实为"有界化" | 见证据列；`git show` 各 commit；Lead 实测计数 | 误导下一轮评审/移植（本仓库已有 P14 先例）；死代码产生 build warning | 统一改口径（Absurd/Undecided/Fuel 的消费语义、预算深度、P5 定位）；删/标注死代码；`L07-RISKS` P2 行同步 P3 行 | 高 |
| F7 | S4 | P8 收窄后判据仍是"名字是否登记"而非 provenance；已登记名分支忽略 spine（当前不可达） | `unification.rs:862-882`；st2g 唯一裸 Decl 生产点 `mod.rs:1071-1085`；未知名拒绝 `elaboration.rs:448-456` | 当前无程序级逃生舱（已验证构造点全量）；未来若新增裸卡住 Decl 生产点会静默判等 | 给 st2g 产物打 `Dynamic` 标记（P8 原建议），裸 Decl 仅该来源放行 | 当前安全：高；未来风险：中 |

## 未能验证 / 建议 Lead 实测

1. **F1 程序级终验**（两条，同文件）：
   ```typort
   enum Nat { zero  succ(x: Nat) }
   enum Bool { true  false }
   enum T(A: U) { c -> T Nat }

   def ok1(e: T Bool): Nat = match e { }      -- 期望（旧/新）：OK（Bool≐Nat→Absurd）
   def bad1(e: T String): Nat = match e { }    -- 旧：OK；新：ERR "match 不完整：缺少构造子 c"
   ```
   若 `bad1` 新版确实拒绝，F1 成立（S1 接受集回归）。
2. **F2 程序级可达性**：需要"σ 的嵌套 VSub 槽值经外层 σ 才提到 target"的源程序。可行方向：
   `enum W(f: Nat -> Nat)` 类高阶索引 + 嵌套 match（外层 σ 先解 `x`，内层解值被 `wrap_sub`
   包成双层 VSub 后再解另一变量）；未构造成功，建议按 Lead 的单元探针把 `VSub(VSub(·))` 直接
   喂给 `occurs_transitive` 做成正式 lib 单元钉（不必程序级）。
3. **F3 深度边界**：构造 40 层"结构不同、末层字面相同"的嵌套卡住 match（递归 def 两条不同
   展开序）验证是否误拒；未构造。
4. **MATCH_CMP_DEPTH 总工作量**：分支多的递归 def（如 `plus (f n) (g n)` 型）在深度 40 内是否
   仍组合爆炸（理论 2^40）——需要计时实测。
5. **孪生版口径差异**：参考版 `MATCH_CMP_DEPTH=40`（路径深度）vs 孪生 `MATCH_CMP_BUDGET=64`
   （总预算，见 `L07-RISKS` P2′）——同一深负载可能在两侧判定分裂且 parity 负载未覆盖（P12 类）。
6. **F4 触发路径**：需 flex-flex 第一方向失败（note Undecided/Fuel）后第二方向真 Absurd 的
   源程序；未构造。
7. **L08 同码**：`src/L08_product_type` 的 `unify_no_arm`/`occurs_transitive`/`struct_eq` 是同源
   拷贝（Lead 已认可 VSub 缺陷同款）；本报告结论按模板同样适用，未逐条复读 L08。
8. Lead 已实测（我直接引用，未复跑）：全套测试绿；merge 卫生；`VSub` 单元不一致；`struct_eq`
   /`UnifyKind`/`unify_no_arm` 方向安全——与本报告一致，无异议。
