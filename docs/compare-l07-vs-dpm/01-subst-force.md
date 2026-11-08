# 维度 1：显式替换（Subst/Sub）与 force / frc / frcS 的推进机制

> 对比对象：L07 = `F:\projects\hermes\elaboration-zoo-lsp\src\L07_sum_type\`（HEAD `641c52fe`）；dpm = `F:\projects\Rust\dpm-nbe-rs\src\`（HEAD `db226de`）。
> 文中 `文件:行号` 以各自项目根为基准。标注：【事实】= 我读过该处代码（或跑过探针）；【推断】= 由代码推出的语义后果；【存疑】= 证据不足。
> ⚠ **实测提示（2026-10-30）**：本文件标【推断】的两处行为已实测并被修正（自指索引：L07 实际**接受**；卡住索引方程：L07 实际 **256 s 后假不可达**），以 [`EXPERIMENTS.md`](EXPERIMENTS.md) 为准。
>
> 验证手段：dpm 侧除读码外，用 `cargo build --release --offline` 重编译后对 `dpm-nbe.exe nf` 喂了若干探针（见「可观测的语义差异」）；L07 侧只读代码与既有单测（未在本轮执行测试）。

## 一句话结论

两侧是**同一套显式替换 + NbE 的两种纪律版本**：L07 的 σ 是"无域/余域的类型无关解链 + 读点条件包裹"，替换只对**被包裹过的值**可见，`force` 遇到 `VSub` 不烧 fuel、由 `frcs` 逐臂把 σ 推进结构，且 spine/Sum 槽**只包裹不物化**；dpm 的替换是"带 dom/cod 的层序列 + 入口全量推进"，`frc`/`frcS` 结构性地把替换压进值的每一层（含 spine 实参），没有 occurs、没有 fuel，靠 `Res.progressed` 与"lookup 不重包同层"保证终止。L07 多出来的每一条约束（槽位不物化、fuel、条件包裹、occurs）都可由"它还有元变量求解器，`invert`/`prune` 需要可逆 spine"解释；dpm 没有 meta，所以这些约束在它那里既不需要也不存在。

## 代码地图

| 概念 | L07 位置 | dpm 位置 | 是否等价 |
|---|---|---|---|
| 替换类型 | `Subst { head: Option<Rc<SubEntry>> }`（mod.rs:236-239），**无 dom/cod** | `Sub { dom, cod, layers: Vec<Rc<Layer>> }`（syntax.rs:241-258） | 不等价：类型化态射 vs 无类型解集合 |
| 条目/层 | `SubEntry { lvl, val, next }`（mod.rs:241-248） | `Layer { dom, cod, subs: BTreeMap<usize, Val> }`（syntax.rs:233-239） | 结构不同（单条目 vs 一层小 map） |
| 写入 | `Subst::extend` O(1) cons 到链头（mod.rs:329-339） | `insert_sub` 造单层 `Sub::new`（subst.rs:44-49） | 都是"新解在最前"，但 L07 可叠同一 Rc 链 |
| 组合 | `Subst::compose(outer, inner)`：外层条目逐条 cons 到内层链前（mod.rs:341-361） | `subst_sub(s2, s1)`：层列表直接拼接 `s2.layers ++ s1.layers`（eval.rs:30-56） | 方向都是"内层先、外层后"，但成本与同键语义不同（D2/D3） |
| 查找未命中 | `lookup_hit → None`；`lookup` 回 `Val::vvar(x)`（mod.rs:255-278） | `lookup_sub` 回 `Val::vvar(i)`（subst.rs:26-37） | **等价**（恒等延拓） |
| 查找命中 | 解值浅结构引用已解层级 ⇒ 包 `VSub(·, 整条 σ)`；否则原样返回（mod.rs:260-273, 285-315） | 命中层较新的层逐个 `subst_val` 应用到值上（subst.rs:28-34） | 目的同（把后解的解压到先解的值上），手法不同（包装 vs 应用） |
| 替换值 | `Val::VSub(Box<Val>, Rc<Subst>)`（mod.rs:216-219） | `Val::Sub(Rc<Val>, Rc<Sub>)`（syntax.rs:296-298）、`Ne::Sub`（syntax.rs:349-350） | 等价（force 消去） |
| force 入口 | `Infer::force`：`VSub => frcs`，入口不烧 fuel（mod.rs:584-605） | `frc`：`Sub => frc_s`，无预算（eval.rs:88-96） | 形状同，纪律不同（D5） |
| 推进函数 | `Infer::frcs`（mod.rs:673-787），逐臂包裹/推进 | `frc_s`（eval.rs:108-130）+ `frc_ne_s`（153-161） | 同构但不完全同语义（D5/D6） |
| 应用 | `v_app`（mod.rs:1042-1066），有 `v_applicable` 守卫（mod.rs:364-381） | `napp`（eval.rs:190-217），非中性/裸 Sub ⇒ panic（212-215） | 顺序同，卡住/panic 边界不同（D8） |
| 发散防护 | `UNIFY_FUEL=4096` + `burn`（mod.rs:479, 393-402），force/frcs/unify 共享（:552-555） | `Res { val, progressed }` + `frc_res`（syntax.rs:360-384, eval.rs:98-106）；**无 fuel**（dpm `src/` 内 grep `fuel` 为 0 命中） | **不等价**（D7） |
| occurs | 两处浅扫描 `val_mentions_lvl`：方程失败 ⇒ Err；头精化失败 ⇒ 跳过（unification.rs:901-928；pattern_match.rs:662-665） | **无**（elab.rs:82-93 直接 `insert_sub`） | 不等价（D9） |
| 替换消费时机 | unify 递归入口 `force(wrap_sub(acc, ·))`（unification.rs:856-865） | `unify_s` 每步把剩余方程 `subst_val` 掉（elab.rs:54-60） | 惰性 vs 急切（D10） |
| 上下文 | 不被改写：层级/env 槽/meta spine 一概不动（README:38-46） | `subst_ctx` 逐条重写 types/env（context.rs:172-186；elab.rs:221-227） | **不等价**（D10） |
| 可逆性视角 | `force_arg`（mod.rs:563-582）只看裸槽位 | 无对应物（无 meta invert） | dpm 无 |

## 逐点对照

### D1 替换的类型：无域/余域的解链 vs 带 dom/cod 的态射

【事实】L07 的 `Subst` 只有一个 `head` 指针（mod.rs:236-239），条目是 `(lvl, val, next)`（mod.rs:241-248）；**没有 dom/cod**，也没有"解掉一个变量后上下文缩小"的概念——README §1.2 纪律二明确："变量的层级、env 槽、元变量 spine 一概不动"（README:42-44）。

【事实】dpm 的 `Sub` 携带 `dom/cod`（syntax.rs:241-258），语义是"把 cod 规模上下文的变量映射到 dom 规模上下文的值"；`insert_sub(g, x, v)` 令 `dom = g.pred()`、`cod = g`（subst.rs:44-49），即每解一个变量上下文规模减一。`subst_sub` 还保留一个 `s1.dom > s2.cod` 的 panic 守卫（eval.rs:30-33），并修正了原版把 `dom` 取错的问题（NOTES 偏离 4 末段，NOTES.md:135-140）。

【推断】后果：
1. **正确性责任不同**。dpm 的类型化态射要求"值活在 dom 上下文里"；这个不变量正是 occurs 检查要维护的东西，而 dpm 恰恰没有（D9）——所以它的 `Sub` 类型是**没有强制执行的文档**（只在 `subst_sub` 里对比 dom/cod 数字）。
2. L07 不需要上下文缩小，因为 σ 只在**读点**生效，槽位层级不变；代价是"解只对包裹过的值可见"这条可见性边界（README:92-95）。
3. 可移植性：把 dpm 的 `Sub` 照抄进 L07 会与"层级不动"的纪律冲突（`dom=g-1` 无意义），把 L07 的 `Subst` 照抄进 dpm 会丢掉 `unifyS` 的 `lvl` 递减（dpm 的 `unify_s` 真的用返回的 `s` 当下一步的 `g`，elab.rs:54-60）。

### D2 写入：O(1) cons vs 单层 map；同一 Rc 链的持久共享

【事实】L07 `extend` 是纯 cons：`Rc::new(Subst { head: Some(Rc::new(SubEntry { lvl, val, next: sub.head.clone() })) })`（mod.rs:331-339）。旧链不受影响，臂边界回滚 = `self.sub` 的 Rc 指针赋值（README:45；tests.rs:1359-1374 的 `subst_chain_semantics` 钉死"旧链不受 extend 影响"）。

【事实】dpm 的 `insert_sub` 每次新建一个单层 `Sub`，层内用 `BTreeMap`（subst.rs:44-49）；插入不是"往已有链上 cons"，而是"造一个新替换"。dpm 里替换不共享、不回滚：`unify_s` 每步得到新 `gamma2` 后丢掉旧的（elab.rs:54-60），`check_pm` 每遇一个 `refl` 就用 `subst_ctx` 生成新上下文（elab.rs:221-227）。

【推断】后果：
1. L07 的写成本 O(1) 且天然支持回溯；dpm 的写成本 O(1) 但**不能回溯**（也不需要，它没有探测/多臂回滚）。
2. L07 的链共享让"同一 σ 被大量值包裹"退化为引用计数自增（mod.rs:224-227；perf 文档 size_of::<Subst>()=8，docs/perf-l07-2026-09-17.md:169-170）；dpm 的 `Sub` 是 `Vec<Rc<Layer>>`，克隆也是 O(#layers) 指针复制。
3. dpm 的层内是 map，单层多键（一次 `unify` 多方程？实际上 `insert_sub` 只放一个键，见 subst.rs:46-48）；L07 的一条条目也只放一个键。两者"一次一解"的粒度相同。

### D3 组合与同键覆盖：外层（新）覆盖 vs "参数侧条目优先"

【事实】L07 `Subst::compose(outer, inner)` 把 `outer` 的条目逐条 cons 到 `inner` 链前（mod.rs:341-361），文档写明"外层条目接到链头（先被查到 = 覆盖同键）"（:341-343）。`lookup_hit` 沿链首个命中即返回（:260-273），所以**同键时外层/更新者胜**。测试 `subst_chain_semantics` 的 compose 段断言 `outer` 覆盖 `inner`（tests.rs:1376-1379）。

【事实】dpm `subst_sub(s2, s1)` 把 `s2.layers` 与 `s1.layers` 直接拼接（eval.rs:48-55），`lookup_sub` **从最旧层往新层找**，第一个命中的（最旧）层提供值，然后把它**更新的层**逐个 `subst_val` 到该值上（subst.rs:26-37）。因此同键时**旧层条目的值保留**，新层只作为"作用在它上面的替换"；新层自己的同键条目被遮蔽。测试名即 `the_arguments_entry_shadows_the_newer_one`（subst.rs:61-70），并注释"left-biased `IM.union`"（:20-25）。

【推断】方向表面相反，实际语义一致：dpm 的组合替换在键 x 上的值是 `s2(s1[x])`——先把旧解 transport 过新替换，这等价于"新替换的事实优先，旧解被重新解释"。L07 的 cons 版是"新条目直接胜出、旧条目永不命中"。二者在**真实代码路径上都是构造性不可达**：L07 侧 `has()` 检查 + "已解变量不再以 bare rigid 出现"（unification.rs:895-900 注释、pattern_match.rs:656 `!self.sub.has(*x)`）；dpm 侧解掉 x 后 x 从上下文中消失（`insert_sub` dom 收缩，后续方程不再引用 x）。所以测试都是合成用例，**但** L07 的嵌套 match 会真的把两个 σ 组合起来（外层臂与内层臂都精化同一变量），此时"外层新解覆盖内层旧解"是语义上正确的方向【推断】。

【推断】成本差异是本条真正的后果：L07 每次 `compose` 要为 `outer` 的**每一条目**新建 `Rc<SubEntry>`（`cons_all`，mod.rs:345-357），perf 文档实测深嵌套负载 81% 的分配来自 `Subst::compose::cons_all`（docs/perf-l07-2026-09-17.md:195-202）；dpm 的拼接只分配一个 `Vec<Rc<Layer>>`（eval.rs:48-55），无逐条目分配——这是 NOTES 偏离 4 的核心收益（NOTES.md:116-133）。

### D4 查找：条件包裹 + 未命中恒等 vs 按需应用较新层 + 恒等

【事实】L07 `lookup_hit`（mod.rs:255-273）：
- 未命中 `None`，调用点用 `Val::vvar(x)` 补恒等（mod.rs:277, 405-407）；
- 命中时先做浅扫描 `mentions_level`（mod.rs:280-315），解值不引用任何已解层级 ⇒ **原样返回**（热路径零分配零 fuel）；引用 ⇒ 包 `VSub(e.val, 整条 σ)`，由 force 在读点推开。
- 扫描口径"宁宽勿窄"：闭包 **env 槽**算引用，闭包体（Tm）不算（mod.rs:280-284, 296）；`Val::VSub` 一律视为引用（:309-310）。

【事实】dpm `lookup_sub`（subst.rs:26-37）没有任何"是否需要"判断：命中层 idx 之后（更新的层）逐个 `subst_val(&leaf(newer), r)`，最后返回；未命中回 `Val::vvar(i)`（subst.rs:36）。

【推断】后果：
1. **语义等价**：两侧未命中都退化为恒等（dpm 测试 `lookup_sub_is_the_identity_outside_its_domain`，subst.rs:72-77；L07 tests.rs:1367-1368）。
2. **成本侧重不同**：L07 在命中点做一次浅结构扫描（O(解值浅层结构)），干净解零分配；dpm 在命中点做 O(#较新层) 次 `subst_val`，每次结构化包一层 `Val::Sub`。dpm 无"干净则直通"的快路径。
3. L07 的条件包裹是**为性能引入的**（design doc §9.4：初版 FxHashMap 写时整表重建 + 逐条深包裹是 O(n³/6)，深嵌套 2.5×@depth40 回归，docs/l07-dpm-refactor-design.md:174-179；status 文档同记载，docs/explicit-subst-refactor-status.md:76-80）。
4. 【存疑】"零分配"只在解值是 `Rc`/`List` 结构时严格成立（`Val::Rigid`、`Val::Lam`：`Env = List<Val>` 是 Rc 链，src/list.rs:5-8, 39-46，克隆 O(1)）；`Val::Pi`/`Val::Sum`/`Val::SumCase` 含 `Box`/`Vec`，`e.val.clone()` 仍会分配（mod.rs:184-220）。文档表述（mod.rs:256）对热路径成立，不是对全部形态成立。

### D5 force 入口：**"入口不烧 fuel、逐臂包裹" vs "入口即全量 subst_val"**（本维度最大结构差异）

【事实】L07：
- `force(Val::VSub(v, sub)) => self.frcs(decl, &sub, *v)`，注释明说"入口不烧 fuel——真正的精化传播只发生在被解变量的读点（frcs 的 Rigid 臂 lookup 命中时烧 1）"（mod.rs:600-605）。
- `frcs`（mod.rs:673-787）是**按值形态分派的推进器**：`VSub` 先 `compose` 再递归（:683-687）；`Rigid` 命中则 `force(hit)` 并按应用序拼 spine（:688-720）；`Flex/Decl/Prim` 只把 spine 槽 `wrap_sp` 后**交回 force**（:726-728）；`Obj` 推被投影者（:729-733）；`Lam/Pi` 只包裹闭包 env（:735-741）；`Sum/SumCase` 槽只包裹（:743-769）；`Match` 推 scrutinee、包裹 env/pending（:770-784）；其余原样（:785）。
- force 返回值的顶层不会是 `VSub`（注释 mod.rs:218），但 fuel 耗尽时可能破例，quote 里有防御臂（mod.rs:1223-1226）。

【事实】dpm：
- `frc(Val::Sub(v, s)) => frc_s(s, v)`（eval.rs:90-96）。
- `frc_s` 对 `Val::U/Refl/Nat/Zero/Bot` 原样返回，对 `Pi/Id/Succ` **重建结构并把每个子项 `subst_val` 掉**（eval.rs:108-130），对 `Val::Ne` 转 `frc_ne_s`（:131-161）。
- 【关键】`frc_s` 不"只包裹"：`Ne::Var(v, sp)` 臂是 `napp(lookup_sub(s, v), frc_sp_s(s, sp))`（eval.rs:157），而 `frc_sp_s` 对**每个 spine 实参**调 `frc_s`（:168-171）——spine 槽被**物化**。`frc_ne` 对裸中性同理（:134-151）。

【事实】替代口径说明：`subst_val` 本身不是深拷贝，它是"O(1) 包一层 `Val::Sub`，若内层已是 Sub 就先 `subst_sub` 组合"（eval.rs:58-64）。所以准确表述是：**dpm 的 frc/frcS 在值结构上做一层重建 + 子项延迟替换，并把 spine 实参强制推进**；L07 的 frcs 在值结构上同样重建，但 **spine/Sum 槽一律只包裹、不推进**。

【推断】这条差异的根源是 L07 的**槽位纪律**（design doc §4 末节，docs/l07-dpm-refactor-design.md:79-88）：`invert`/`prune_vflex` 需要 meta 的 spine 槽保持 bare rigid 才可逆（`?m x y := Bool` 才能倒推出 `?m` 的参数），一旦把 σ 推进槽位，槽位就物化成构造子值，invert 失败。复现案例见 design doc：嵌套 `match` 的内层臂 `?2` spine 槽被物化后误报 can't unify。dpm 没有元变量、没有 invert，所以"把替换压进 spine"对它完全合法，而且更简单。

【推断】后果：
1. **完备性**：L07 的不物化意味着"σ 之下的值 force 到与旧语义同一 WHNF 形态"，但槽位里藏的 σ 只对之后的读点可见；dpm 的物化会把精化"提前"烧进值里，因此 dpm 的值更接近 NF，而 L07 的值保留更多惰性结构。
2. **性能**：dpm 的 frc 单次调用可能递归推进整条 spine（无预算），L07 把这项工作摊到后续读点（有 fuel）。
3. **可移植性**：L07 的"槽位只包裹"**不能**当作通用优化搬到 dpm；反过来，把 dpm 的 `frc_s` 逐行搬进 L07 会直接破坏 invert（这是 design doc 明确警告的"评审与孪生版移植必读"）。也就是说：**dpm 不能作为 L07 force 的逐行参考实现**。

### D6 槽位纪律的覆盖面：哪些结构"只包裹"

【事实】L07 的 `frcs` 对以下位置只调 `wrap_sub`（不 force）：`Flex/Decl/Prim/Obj` 的 spine（mod.rs:726-733, 789-794）、`Sum` 的 params 的 val/ty（:743-757）、`SumCase` 的 typ/datas（:758-769）、`Match` 的捕获 env 与 pending（:770-784）、`Lam/Pi` 的闭包 env（:735-741）。真正"推进"的只有：`Rigid` 头（含命中解值与 spine 的应用）、`Obj` 的被投影者、`Match` 的 scrutinee。`wrap_sp` 在空 spine 上直接返回（:789-792），`frcs_env` 在空 σ 上返回 `env.clone()`（:796-801）。

【事实】dpm 没有"槽位"这一层保护：`subst_sp`/`subst_env` 对每个元素 `subst_val`（eval.rs:66-74），`frc_sp_s` 对每个实参 `frc_s`（:168-171），`subst_cl` 替换闭包 env（:76-82）。dpm 的"只延迟不推进"仅体现在 `subst_val` 那一层（子项包 Sub），一旦 force 走到该子项就全量推进。

【推断】后果：L07 的值里可以长期存在 `VSub` 嵌套（perf 文档记录的"包裹叠包裹"，docs/perf-l07-2026-09-17.md:178-180）；dpm 的嵌套延迟也只发生在 `Sub` 包装里，但它的 spine 实参在 force 时会被清干净。两者"值的规范程度"不同：同一程序在 dpm 侧 force 后 spine 更规范，L07 侧更惰性——这解释了 D5 的成本归属差异（L07 成本在构造/包裹，perf 文档:204-208 明确"读路径零命中"）。

### D7 防发散：共享 fuel + 有界降级 vs `Res.progressed` + 无预算

【事实】L07：
- 单一 `UNIFY_FUEL = 4096`（mod.rs:479），存在 `Infer` 上（:476），每个外层入口充值（`meta_refuel`，:552-555；unify 入口的 `unify_catch` 等）。
- `burn` 消耗 1，耗尽返回 false（mod.rs:393-402）；燃烧点：meta 展开（:592）、frcs 的 Rigid 命中（:700）、Match 重选（:612）、Decl 展开（:635）、Prim 归约（:650）、Obj 投影（:663）。**VSub 入口与包裹动作不烧**（:600-605）。
- 耗尽时是**有界降级**：frcs 返回裸 rigid（:700-702）、force 原样返回未展开值、`unify` 直接 `Err(UnifyError)`（unification.rs:834-846）。`fuel_exhausted` 专门用于把"预算耗尽"与"真结构冲突"区分开（mod.rs:557-561）。

【事实】dpm 完全没有 fuel（`src/` 内无 `fuel` 符号）。终止依赖两件事：
1. `frc_res`：只有 `progressed` 才继续 force（eval.rs:98-106），避免"把刚判定为卡住的中性再 force 一遍"的死循环；`frc_ne`/`frc_ne_s` 的 λ/plus 臂都走它（:147, 149, 157-159），`match_` 也用它（:241）。
2. `lookup_sub` 不把**同一层**再次应用到该层的值上（只应用"更新的层"，subst.rs:28-34）——所以 `x := suc x` 这种自引用解返回的是裸 `suc x`，不会立刻再展开。

【推断】两者不等价：
1. **防的对象不同**。dpm 的 `progressed` 是**局部**的"最坏情况下退一步"，它只保证单次 force 不会原地打转；L07 的 fuel 是**全局预算**，防的是"跨调用、跨 meta 展开的链式发散（含 meta 间接环，注释 mod.rs:584-588：solve 无跨 meta occurs check）"。
2. **失效模式不同**。dpm 若存在更长的循环（A→B→A），`progressed` 无法阻止；L07 在预算耗尽时**静默降级**，会把"算力不够"伪装成"类型/结构不对"——status 文档记录过真实 P1：初版"每次 VSub 推开计 1 fuel"把深嵌套模式的安全边界从 d>2000 压到 d≈380，被误报"分支不可达"（假 absurd），修复为燃烧点移到 lookup 命中并加 d=400 回归（docs/explicit-subst-refactor-status.md:86-88；tests.rs:1493-1532 `test_deep_pattern_fuel_budget_regression`）。
3. **风险归属**：L07 的 fuel 与 unify 递归深度共用池（unification.rs:835-846 先查 fuel），所以"深模式"与"深展开"会互相抢预算；dpm 无预算，理论上界由数据决定——【存疑】是否有可构造的 dpm 发散程序，本轮探针未找到（见「可观测的语义差异」）。

### D8 应用序、β 与卡住：`v_app` + `v_applicable` 守卫 vs `napp` + panic

【事实】L07 `frcs` 的 Rigid 臂（mod.rs:688-720）：先 `lookup_hit` 命中判定（fuel 耗尽早退），`head = force(hit)`；再判"头不可应用且 spine 非空"（除 `Lam` 外要求 `v_applicable(head)`，:707-714），不满足就卡回 `Rigid(x, sp)`；否则 `for (u,i) in args.rev()` 逐条 `v_app(head, wrap_sub(sub,u), i)`（:715-718）。即"按应用序 β/拼接，实参只包裹不预先 force"。

【事实】dpm `frc_ne_s` 的 `Ne::Var` 臂（eval.rs:157）：`napp(lookup_sub(s, v), frc_sp_s(s, sp))`。`frc_sp_s` 先 force 每个实参；`napp` 先 `frc(v)`，空 spine 直接 `progress`，否则按中性种类分派：`Var` 追加 spine 并 `block`（:198-201），`Lam` 参数够则 `match_`、不够则重建卡住 λ（:203-210），`Plus`/未 force 的 `Sub` 直接 `panic`（:212-213），非中性直接 `panic`（:215）。

【推断】后果：
1. **约定式 vs 防御式**：L07 用 `v_applicable` 守卫把"对非函数值做应用"卡住（design doc §4 记录这是为堵 `v_app` 的 `impossible apply` panic 而加的，mod.rs:364-369）；dpm 直接 panic，把这类形态当程序错误。对良型输入等价，对研究/扩展场景 L07 更耐操。
2. **β 的惰性不同**：L07 把 `VSub` 实参塞进闭包 env（`v_app` → `closure_apply` → `eval`，mod.rs:1054），读该槽时才 force；dpm 在 `napp` 前已 `frc_sp_s` 把实参推到 WHNF 再交给 `match_`（其中 Var 模式还再 `frc` 一次，eval.rs:248）。同一程序在 dpm 侧 β 之后立刻多做功。
3. **match 分支顺序**：L07 的卡住 match 是独立值 `Val::Match`，force 时先 force scrutinee、是构造子值才重选、分支选中后在**值层**补 pending 实参（mod.rs:606-628）；dpm 没有 match 值，卡住的模式匹配折进 `Ne::Lam` + spine，重选靠 `napp` 重跑 `match_`（eval.rs:233-263，NOTES 偏离 2 明说重跑会重算已匹配 binder，NOTES.md:86-93）。这一条与替换的交互是：L07 的 `pending` 实参在 frcs 里只包裹（:778-782），dpm 的 spine 实参在 frcS 里被推进（:157）——正是 D5/D6 的两个纪律在"卡住项"上的投影。

### D9 occurs 守卫：两处浅 occurs vs 完全没有

【事实】L07 有两处 occurs，语义**不同**：
1. **方程侧**（unification.rs:901-928）：`(Rigid x, v)` / `(v, Rigid x)` 且 x 在 `spec.solvable` 集中、v 非 Flex 时，先 `if val_mentions_lvl(v, *x) { return Err(UnifyError) }`（:908-910, 922-924），才 `Subst::extend` 写入 `spec.acc`（:911-913, 925-927）。失败 = 该臂被判不可达（与旧 `pm_solve` false ⇒ Err 对齐，注释 :898-900）。
2. **头精化侧**（pattern_match.rs:650-667）：被匹配变量本身写入 σ 前，`if !val_mentions_lvl(&ctor_val, *x)` 才写（:662-665）；occurs 失败 **不阻断分支检查**，只是不做这次精化。

【事实】`val_mentions_lvl` 是**浅**扫描（mod.rs:1384-1434）：闭包体（Tm）不进入（:1430 的 `Val::Lam(..) | Val::Pi(..) => {}`），注释说明"闭包内的解环（`x := λ…x…`）在 closure_apply 后的读点闭环——由 force 的 fuel 兜底"（design doc:95-96）。

【事实】dpm **没有 occurs**：`unify1` 见到一侧是 var 就直接 `insert_sub(g, x, v)`（elab.rs:82-93），不检查 v 是否引用 x。

【推断】后果：
1. dpm 可以产生违反 `Sub` 类型不变量的自引用解。**探针证实**（见「可观测的语义差异」S1）：`let bad : (x : Nat) -> Id Nat (suc x) x -> Nat = \ x refl . zero; bad` 被接受，`nf` 输出 `λ x refl . zero`。
2. 自引用解**没有**立刻导致发散：因为 `lookup_sub` 只应用更新的层（D7-2），`x := suc x` 展开一次就停在裸 `suc x`。所以 dpm 的这个缺口当前的可见后果是**残余自引用值 + 误导性诊断**（S2），不是死循环【事实：探针无超时/无 panic】。
3. L07 把 occurs 失败分成"硬（方程）/软（头精化）"两种，是在**完备性**（不要因为环守卫把可达臂误判不可达）与**安全性**（不要写出 x 引用 x 的 σ）之间取平衡；dpm 全不要，代价由"无 meta、无 invert"承担。
4. 【推断】L07 的浅 occurs 会漏"闭包体内的环"，这类环靠 fuel 兜底（D7-2），所以 L07 的 occurs 是**第一道**防线而不是完整防线。

### D10 替换的消费时机：入口 wrap（惰性）vs 剩余方程 subst（急切）+ 上下文改写

【事实】L07 的 `unify` 递归入口（unification.rs:825-865）：先烧 1 fuel、`force` 两侧，然后**若 `spec.acc` 非空**，把两侧 `force(wrap_sub(&s.acc, t/u))` 再 force 一次（:856-865）。注释："每次递归入口按当时的 acc 重新包裹——先解出的方程对后到的子方程自动可见"（:856-859）。

【事实】dpm 的 `unify_s`（elab.rs:40-65）：每解一个方程拿到 `a` 后，`gamma2 = subst_sub(&a, gamma)`，并把**剩余所有方程**左右两侧都 `subst_val(&a, ·)`（:54-60），再递归。

【事实】dpm 的 `check_pm` 每个 `refl` 之后用 `subst_ctx(&sub, ctx)` 重写上下文的 types 与 env（elab.rs:221-227；context.rs:172-186），并把 `b` 用 `subst_cl` 替换后再 `apply(Refl)`（:224）。L07 的对应位置只记 σ（`self.sub = spec.acc`，pattern_match.rs:646）并继续用 `wrap_sub` 读点包裹（:632, 655 等约 20 处调用点）。

【推断】后果：
1. **复杂度归属**：dpm 每步替换所有剩余方程（O(#eq × 值)），L07 每步 O(1) 包裹 + 读点 force。方程数大时 dpm 的急切替换是额外常数（NOTES 偏离 4 的 2^n 正是这条链在"替换套替换"上的极端形态，NOTES.md:116-133）。
2. **语义可见性**：dpm 的上下文被真的改写，所以"后解的解"对上下文里所有旧类型可见（这是它 check 顺序敏感但实现简单的原因）；L07 的可见性只到**被包裹过的值**，meta 解值与 decl 表条目不在扫描/包裹范围（README:92-95）——这是 L07 明示的**语义边界**，dpm 没有这个问题（因为它没有 meta/decl）。
3. **可移植性**：dpm 的 `subst_ctx` 是需要上下文可变的前提；L07 若照搬会破坏"层级/env 槽不动"（README:42-44），并让 `wrap_sub` 的读点纪律失去意义。

### D11 复杂度与实测数据

【事实】L07（文档数据，非本轮实测）：
- σ 的**读**路径（`lookup_hit` / `mentions_level` / `frcs` 的 spine 实参包裹）在四族负载上一次都没进热点（docs/perf-l07-2026-09-17.md:204-208）；成本在**构造**（`extend`）、**包裹**（`frcs`/`frcs_env`，每个 `VSub` 88B）与**组合**（`compose`，每个条目 120B）（:200-202, 169-176）。
- 显式替换重构后 match 密集负载回归 1.18–1.35×，但**比值不随规模漂移**（deep d=16…128 稳在 1.14–1.20，cart 1024 臂 1.30–1.35），判定为常数因子而非复杂度变化（:111-125）。
- 无 match 源上分配次数与重构前**逐位相同**（1.000×），"σ 空则直通"纪律零开销（:139-144, 174-176）。
- 深嵌套下唯一超线性项是 `compose` 的逐条目 cons（deep n=64 时 81% 分配，:195-202）。

【事实】dpm（NOTES 文档数据）：Haskell 原版急切组合在严格语言下 `subst_sub` 被调用 2^n 次（n 步传递性证明）；修复前 trans15 670 ms、trans18 超时；改成层序列后 trans60 16 ms，整族二次（NOTES.md:116-133）。

【推断】两边都不是算法级差异而是"常数 × 触发点"的差异：
- L07 把成本放在**写/包裹/组合**（每个被包裹的值 O(1) 头 + 组合时 O(|outer|) 条目分配），读路径几乎免费；
- dpm 把成本放在**读**（lookup 时按需 `subst_val` 应用较新层）与 force 的 spine 推进，组合是 O(1) 值操作。
- 深嵌套形态对 L07 不友好（compose 逐条 cons），对 dpm 友好（层拼接）；`trans` 型负载对 L07 的刺激点在 `wrap_sub` 调用次数而非 compose。

### D12 变体对照：`bump_spine_iter` 孪生版

【事实】孪生版与参考版**同构**：`SubstV { head: Option<Rc<SubEntryV>> }`（bump_spine_iter/subst.rs:20-38），`lookup_hit` 同样条件包裹（:90-107），`extend`/`compose`/`has` 同款；`frcs` 的注释逐条复述纪律（bump_spine_iter/force.rs:505-513），Rigid 读点烧 fuel（:637-648），spine 分派 `vapp1`（:649-705）。

【事实】差异全在内存管理：arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆在 `bump.reset()` 时不会 Drop，孪生版加 `VSUB_REGS` 登记 + `vsub_reclaim` 轮界归还（subst.rs:53-82；README:301, 343-347）；参考版用普通 `Rc`，靠作用域 Drop，无需该机制。

【推断】对本维度结论无影响：两版在**替换语义/推进纪律**上逐点一致，孪生版只是把"Rc 生命周期"换成"arena + 手工归还"。若比较 L07 与 dpm 时用孪生版作证据，需注意 §7.7 的回收属于实现补丁，不是语义。

## 可观测的语义差异

> 说明：dpm 侧输出为【事实】（本轮 `cargo build --release --offline` 后实跑，源码 HEAD `db226de`，dpm 源码 mtime 2026-10-28 17:47 晚于仓库里预编译的 16:44 二进制——**旧二进制把 `Nat` 当未绑定变量**，故探针一律用新构建）。L07 侧无 `refl` 模式，只能给等价形态的【推断】。

### S1 自引用解：dpm 接受，L07 由 occurs 拒绝（【事实】dpm /【推断】L07）

dpm（实跑接受）：

```
let bad : (x : Nat) -> Id Nat (suc x) x -> Nat = \ x refl . zero; bad
```

输出：

```
λ x refl . zero
  :
(x : Nat) → Id Nat (succ x) x → Nat
```

即 `unify1`（elab.rs:82-93）把 `x` 解成 `suc x`（自引用），`check_pm`（:212-240）照常继续，分支体 `zero` 与精化无关所以通过。改用与 `x` 相关的体仍接受、且 NF 不展开环：

```
let bad : (x : Nat) -> Id Nat (suc x) x -> Nat = \ x refl . x; bad
```

输出 `λ x refl . x`（自引用解只影响类型检查阶段的上下文，不进 core term）。

L07 的等价形态（**未运行**，按代码推断）：

```
enum Nat { zero  succ(x: Nat) }
enum Eq[A](x: A, y: A) { refl(a: A) -> Eq[A] a a }

def bad(x: Nat, e: Eq[Nat] x (succ x)): Nat =
    match e { case refl(a) => zero }
```

特化方程依次解出 `x := a`、`a := succ a`；第二式在 unification.rs:908-910（或 922-924）被 `val_mentions_lvl` 判为环 ⇒ `Err` ⇒ 该臂不可达 ⇒ 唯一构造子不可达 ⇒ 覆盖检查报错。**哪一侧"更对"取决于口径**：dpm 接受的是"从空类型出发的函数"（vacuous，可辩称为合理），L07 报"分支不可达"（把矛盾前置成覆盖错误）。两侧诊断可读性差异明显。

### S2 自引用解的后续代价：dpm 的误导性拒绝（【事实】）

在同一个精化上下文里再要求一条等式：

```
let bad : (x : Nat) -> Id Nat (suc x) x -> Id Nat x zero = \ x refl . refl; bad
```

dpm 输出（exit=1）：

```
<stdin>:1:71:
1 | ... = \ x refl . refl; bad
  |                       ^
expecting succ x equals to zero, but it is not
```

可读性上像"用户在 `refl` 处写错"，实际上是前面 `x := suc x` 留下的自引用解被展开了一次（`lookup_sub` 返回 `suc x`）。L07 在 S1 的位置就会把该臂判死，不会走到这条诊断。

### S3 同键覆盖方向：两侧机制相反、真实路径都不可达（机制级，【事实】）

- L07：`Subst::compose(outer, inner)` 外层胜（tests.rs:1376-1379）。
- dpm：`subst_sub(&s2, &s1)` 同键时**参数侧（较旧）条目**的值保留，较新的替换作为变换（subst.rs:61-70 的 `the_arguments_entry_shadows_the_newer_one`）。

程序层面无法观测（L07 用 `has`/`solvable` 排除重复解，unification.rs:895-900、pattern_match.rs:656；dpm 解掉变量后上下文收缩，后续方程不再引用它）。【推断】L07 的嵌套 `match`（外层臂 + 内层臂都精化同一变量）会把两个 σ 组合，那时"外层覆盖"是正确方向；dpm 无嵌套精化的等价场景。

### S4 恒等替换的代价：L07 零开销直通 vs dpm 仍走 frc_s（文档+代码，【事实】）

- L07 `wrap_sub` 在 σ 空时直接返回 v（mod.rs:383-391），`frcs` 入口 σ 空直接 `force`（:679-681）；perf 文档实测无 match 源分配 1.000×（docs/perf-l07-2026-09-17.md:139-144）。
- dpm `subst_val(s, v)` 对任何 s 都包一层 `Val::Sub`（eval.rs:58-64），恒等替换也要经 `frc_s` 走一遍结构（eval.rs:534-549 的测试注释自述"Substitution is applied lazily: frcS on Succ only delays the substitution on the child, so equality is up to conversion"）。程序输出相同，差在每次精化后的常数成本。

### S5 应用在非函数值上：L07 卡住 vs dpm panic（代码级，【推断】）

dpm `napp` 对非中性值 `panic!("napp: impossible (applying a non-neutral value)")`（eval.rs:215），对未 force 的 `Ne::Sub` 也 panic（:213）。L07 在 `frcs` 读点先用 `v_applicable` 把不可应用头卡回 `Rigid(x, sp)`（mod.rs:707-714），`v_app` 只在真正非法时 panic（mod.rs:1064）。良型输入上不可观测；对"用 unify 做类型级计算"的探索性程序，L07 会把形态留成卡住值，dpm 直接崩。

## 机制有无矩阵

| 机制 | L07 | dpm | 备注 |
|---|---|---|---|
| 持久化替换链 / 层序列 | 有（单链） | 有（层 Vec） | 都可 O(1) 加新解；L07 可回溯 |
| dom/cod 与上下文收缩 | **无** | 有（`Sub{dom,cod}`、`unifyS` 的 lvl 递减） | L07 层级不动（README:42-44） |
| 条件包裹（浅扫描决定包不包） | 有（`mentions_level`，mod.rs:280-315） | 无 | dpm 命中即按需 `subst_val` |
| 解值的"干净则零分配直通" | 有（mod.rs:255-273） | 无 | — |
| 替换入口烧 fuel | 无（mod.rs:600-605） | 无（无 fuel） | 关注点不同 |
| lookup 命中烧 fuel | 有（mod.rs:700） | 无 | L07 的燃烧剖面 |
| 全局共享预算（unify+force） | 有（mod.rs:479, 552-555） | 无 | dpm 无预算 |
| `Res.progressed` 式局部进度标记 | 无（靠"无进展就返回原值"+fuel） | 有（syntax.rs:360-384, eval.rs:98-106） | 失效模式见 D7 |
| occurs（方程） | 有（硬 Err） | **无** | elab.rs:82-93 |
| occurs（头/精化） | 有（软跳过） | 无 | pattern_match.rs:662-665 |
| 槽位只包裹不物化 | 有（spine/Sum/SumCase/Match-env） | **无**（spine 实参被 `frc_sp_s` 推进） | 本维度核心 |
| 上下文改写（subst_ctx） | 无 | 有（context.rs:172-186） | dpm 每 `refl` 一次 |
| 可逆视角 `force_arg` | 有（mod.rs:563-582） | 无 | 无 meta invert |
| VSub 顶层不变式 + quote 防御 | 有，且 fuel 可破例（mod.rs:1223-1226） | 有，`quote_val` 先 force，否则 panic（eval.rs:403-406） | 都靠约定 |
| 同键覆盖策略 | 外层/新者胜 | 参数侧/旧者值保留 + 新者变换 | 真实路径均不可达 |
| 孪生 arena 回收（`VSUB_REGS`） | 参考版无；孪生版有（README:343-347） | 无 | 工程补丁 |

## 存疑与待核实

1. **L07 侧未实跑**。本轮只读代码 + 引用既有单测；`cargo test` 未执行（工作区大、非本维度必要）。S1/S5 的 L07 行为是【推断】。仓库里有 2026-10-11 预编译测试二进制（`target/debug/deps/elaboration_zoo_lsp-*.exe`），但用旧二进制证明当前源码不严谨，未采用。
2. **dpm 探针的构建基线**。仓库自带 `target/release/dpm-nbe.exe`（2026-10-28 16:44）与源码（17:47）不一致：旧二进制把 `Nat`、`plus` 报成 unbound variable，全部探针改用 `cargo build --release --offline` 的新构建。若 Lead 要复现，请先重编译。
3. **dpm 自引用解是否可能造成发散/越界**。探针（S1、S2 变体）均正常终止。理论上 `lookup_sub` 只应用更新层，故单层自引用不会自旋；多层交错（两次 refines 相互引用）未穷举。这一条决定"无 occurs"是"仅诊断问题"还是"真风险"。【存疑，倾向仅诊断问题】
4. **L07 同键覆盖在嵌套 match 的可达性**。D3 断言外层覆盖是正确方向，依据是嵌套臂会组合 σ（frcs 的 VSub 臂，mod.rs:683-687）与 design doc:92；未构造运行用例验证。
5. **"零分配直通"的边界**。只在解值为 `Rc`/`List` 结构时严格；`Val::Pi`/`Sum`/`SumCase` 的 `clone` 有 `Box`/`Vec` 分配（D4-4）。文档表述（mod.rs:256）未区分，属措辞宽松而非错误。
6. **设计稿与实现的偏差需以代码为准**：design doc §10.1 仍写"force 热路径的 rigid 解查找 O(n) → O(1)（HashMap）"（docs/l07-dpm-refactor-design.md:188），但实现是持久化单链 + 沿链扫描（mod.rs:224-248），§9.4 才记录"σ 表示定稿（性能评审后）"（:174-179）。引用该文档时必须回代码核实。
7. **fuel 数值 4096 与 d=400 回归的关系**：单测注释说"修复后剖面与旧 pm_defs 对齐（旧版 d=2000 仍在预算内）"（tests.rs:1493-1497），但当前 4096 预算在更深（>数千）模式上的实际边界未验证。
8. **`Subst::lookup`（非 hit 版）在产物代码里没有调用点**（仅 tests.rs:1366-1368 等），生产路径只用 `lookup_hit`；不要误以为存在"未命中即恒等"的独立展开路径。

## 给 Lead 的三条要点

1. **不要把 dpm 的 `frc/frcS` 当 L07 的参考实现**。两者形状同源，但 L07 的 `frcs` 承载 dpm 没有的**槽位纪律**（spine/Sum/SumCase 只包裹不物化，mod.rs:721-784），其存在理由是 L07 的 meta `invert/prune` 需要可逆 spine（design doc:79-88）。照搬 dpm（spine 实参 `frc_sp_s` 物化，eval.rs:157, 168-171）会重新引入 L07 历史上误报 can't unify 的缺陷；反过来 dpm 也不需要 L07 的条件包裹/occurs。
2. **本维度真正的语义缺口是 occurs，而且两侧缺口方向相反**。dpm 完全没有（elab.rs:82-93），可接受 `x := suc x`（S1 实证）；L07 有两处**不同强度**的浅 occurs：方程侧硬 Err ⇒ 臂不可达（unification.rs:908-910），头精化侧软跳过（pattern_match.rs:662-665），且闭包体内的环靠 fuel 兜底（mod.rs:1430）。评审时不要用"有/无 occurs"一刀切，要说清"哪一处、硬还是软"。
3. **复杂度不构成结论级差异，但成本位置不同**：L07 的成本在写/包裹/组合（perf 文档：读路径零命中，深嵌套 81% 分配在 `compose::cons_all`，docs/perf-l07-2026-09-17.md:195-208），dpm 的成本在 lookup 的按需 `subst_val` 与 force 的 spine 推进；NOTES 偏离 4 的 2^n/trans60 数据是**替换组合算法**的收益（层拼接 vs 渴望 map），不是两侧能力差异。若 Lead 要下"谁更完备/更快"的整体判断，这一维只能支持"常数与触发点不同，均非算法级退化"。
