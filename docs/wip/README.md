# L13 显式替换移植：未落地尝试的证据存档

L13（生产层）的显式替换移植**代码完成、裸语言语义面基本正确**，但
prelude/calc 路径存在规模放大与**若干 parity 语义回归**，未通过验收，
**已回退到 HEAD**。本目录保存历次尝试的补丁与结论，供后续接续。

## 产物

- `l13-explicit-subst-round1.patch`：第一轮移植（参考版 + 孪生版，8 文件
  / +1599−452）——裸语言语料 65 例逐字节 diff = 0，但 prelude 挂起。
- `l13-explicit-subst-attempt.patch`：第二轮修复（= round1 + frcs 入口
  `mentions_level` 快路径、`wrap_sub` 展平、`compose` 去重、`quote_sp`
  迭代化 + 顶层 quote 记忆化、`subst_cxt` 条件包裹）。对干净 HEAD 可独立
  应用（round1 的累积超集）。
- `l13-explicit-subst-round3-perf-probes.patch`：第三轮（= attempt + 三项
  性能修复 + 诊断探针）。
- `l13-explicit-subst-round4-patches.patch`：第四轮（2026-09-16）= round3
  + **prelude 期 LSP 表总闸（重大，见下）+ unify_pm 重锚门槛 + FRCS_MEMO
  内存口径修复 + 深链诊断探针**。对干净 HEAD 可独立应用（`git apply
  --check` 已验证）。
- `l13-explicit-subst-round5-gadt.patch`：**最终累积补丁**（第五轮与评审轮
  修复，含 GADT 覆盖修复参考版实现 + 各项性能/正确性修复 + 诊断探针；
  round1/attempt/round3/round4 的累积超集）。对干净 HEAD 可独立应用
  （`git apply --check` 与 `--check --reverse` 双向验证）。**注意**：master
  有意不含它——补丁是否应用在工作树随评审轮次变动（应用态可用
  `git diff src/` 查看；未应用态用 `git apply --check` 验证，两种均正常）。

## 第四轮结论（2026-09-16）

### 一、prelude 期不再收集 LSP 表 —— 21s → 9.3s（已落地，零行为变更）

**发现**：`load_prelude_state_impl` 末尾本就 `hover_table.clear()`（连同
completion/inlay），prelude 内部产生的 hover 条目**从不被任何消费者读到**；
而显式替换下每个变量引用的类型都带 VSub 包裹，渲染要 quote+frcs 重建+
打印，实测占 prelude 加载 21s 中的 **~10-12s（quote 1.6s + pretty 8.6s）**。

**修复**：`Infer.lsp_collect: bool`（prelude 加载期置 false，克隆给用户
文件的状态恒为 true）。实测 `typort check`（含 HDL prelude 全量）：
**21.1s → 9.3s**。孪生版**早已**有同样的总闸（`bump_spine_iter` 的
`if !self.observe { return; }`，注释即"本轮末表即清，渲染是纯死工作"）
——本修复只是让参考版对齐孪生版，parity 表不会分叉。

`l13bench --workload prelude-core` 的拆分（basic 列）：带 LSP 表 1242ms /
不带 637ms / 基线（移植前）22.4ms ⇒ **LSP 表渲染 ~600ms，纯 elaboration
仍 ~28×**（fast 孪生列 802ms，基线 12.8ms）。

### 二、12k 深 quote 的真身：**meta 解链**（诊断完成，未修）

- 最深 quote 路径 12,287 层，形状 `Flex=1, VSub=12,286`，扇出树 77,811
  节点（第三次修正该画像的定性）：**不是**"巨型卡住应用"，也不是字面
  VSub 塔（σ 链实测 ≤4 层、`wrap_sub` 展平有效、nested-创建计数≈0、
  force 顶层从不返回 VSub）。
- 帧值转储（新增 `QSTACK_VAL` + force 后 DFS）显示：链上每层是
  `SumCase{ typ: VSub(Sum), data: VSub(Flex(m, [Rigid,Rigid,Rigid])) }`，
  即 **`succ(?m₁)`，而 `?m₁ := succ(?m₂)`，`?m₂ := …`——一条 meta 解链**，
  逐层 `force` 展开。深度只受 fuel 池约束（~12k ≈ 3 次充值的量级），
  因此**默认测试栈（无 RUST_MIN_STACK）必栈溢出**——这就是
  `l13_fast_parity` 默认运行崩溃的直接原因（`calc_two_step` 等）。
- 触发位置：`nat.typort` 的 `nat_div`（file[2]）首次出现，之后随
  elaboration 趟数翻倍增长（65→131→…→8447）。
- 与第二轮的"meta 间接环由 fuel 兜底（语料不触发）"注记相符：**L13 的
  prelude 触发了它**。

### 三、深链之外的 elaboration 放大（画像）

prelude 加载（LSP 表已关）逐函数画像：quote 3.7s / 2.93M 次（基线
0.2s / 1.12M）、eval 3.5s（基线 3.0s）、check 2.2s（基线 0.15s）；另有
unify_pm 计时 2.3s——DIAG8 是跨调用方的全局桶（check 之外还有
insert/compiler 等发起），并非全部落在 check 内。`infer_expr` 调用数与基线**完全一致（118,304）**而单次
成本曾 30×——定位到其独占时间里 hover 渲染占绝大部分（已由总闸消除），
其余是模式编译器分支循环内的 quote/探测。

quote 最外层调用归属（新增 `DIAG10`）：**compiler 63,953 / other 14,524
/ unify 1,948 / insert 287**——编译器分支是 quote 的主要发起者。

### 四、parity 状态：**移植版有 4 个既有失败**（第三轮未跑全量 suite）

第四轮首次跑全量 `l13_fast_parity`（大栈）后发现，下列失败**在 round-3
状态同样失败**（已用 stash 对照验证，非第四轮引入）：

1. `legacy_tests::test_pm_vec_bool_exhaustive`
   —— `match (l, x)` 的 GADT 约束本应使 `Tuple2.mk(zero, cons)` /
   `Tuple2.mk(succ, nil)` 不可达，移植版**误报 non-exhaustive**；
2. `legacy_tests::test_pm_tuple_vec_gadt`
3. `legacy_tests::test_pm_tuple_vec_gadt_no_prelude`
4. `bump_spine_iter::observation_tests::resident_compaction_matches_fresh_replay_across_kicks`
   （孪生常驻内存/压缩一致性，26.8s 失败）

⇒ 移植版**同时**有性能问题与 GADT 覆盖检查的语义回归；后者的优先级高于
性能（性能再好也不能落一个会误报非穷尽的类型检查器）。

### 五、第四轮已落地/已回退的改动清单（patch 内）

已落地（保留在补丁里）：
- `Infer.lsp_collect` 总闸（prelude 期不收集 hover/completion/inlay），
  并在 `bench_check_nf_bounded` 提供 `L13BENCH_NO_LSPTABLES` 开关；
- `FRCS_MEMO` 内存口径：1<<20 强持结果会把长链重建图钉到 **8 GB**
  （`resident_compaction_*` 直接 6-8 GB）；改为 **1<<18 + 溢出先按输入存活
  清扫**，命中率与最快配置持平（9.2-9.8s）且内存有界（CLI 峰值 430 MB）。
  选型数据：Weak/Weak 结果 14.4s（下游 memo 反复重算）、1<<14 强持 +
  溢出即清 **103s**（抖动）；
- `unify_pm` 方程重锚的 `mentions_level` 门槛（σ 对该侧无作用则跳过包裹+
  force；语义恒等，实测该路径的值大多仍引用 σ，收益主要在非热点路径）；
- 诊断探针：`DIAG8`（subst_cxt/mentions/check_pm/infer_pm/unify_pm/
  insert/compiler/hover 计时）、`DIAG9/9b`（hover 键/命中/quote-vs-pretty）、
  `DIAG10`（quote 调用方归属）、`DIAG11`（force 返回 VSub 不变式）、
  `DEEPPATH`/`DEEPTREE`/`QSTACK_VAL`（最深路径与帧值转储）、
  `DEEPCALLER`（深 quote 的调用栈）、`QLEAK`（深度配对性）。

已回退（试过但**改变了行为**，勿再重复）：
- `force_chain` / `quote` 的 SumCase 链"VSub 透明解包"：会让链首包裹层不再
  被物化、`force` 可能返回仍带 VSub 槽的链，破坏"顶层非 VSub"不变式 ⇒
  GADT 覆盖检查误报 non-exhaustive。深链不在此路径，修它无用。

## 第五轮结论（2026-09-16 续）：GADT 覆盖回归已修复（参考版）

### 修复了什么

**症状**（见第四轮第 4 节）：`match (l, x)` 中 GADT 约束本应使
`Tuple2.mk(zero, cons)` / `Tuple2.mk(succ, nil)` 不可达，移植版却把它们
报成未覆盖（3 个 legacy 测试红）。

**根因**：模式编译器的构造子可达性探测（`filter_accessible_constrs`）
用的是**精化前构建的头部类型值**（如 `Vec[Boolean] l`），而上下文已被
`subst_cxt` 精化（`l` 的槽已解为 `zero`）。σ 机制下 `force(Rigid(l))`
**不再查全局解表**（旧机制靠它天然让精化对一切读点可见），于是探测把
`cons : Vec[Boolean] (succ n)` 与 `Vec[Boolean] l` 合一成功、把已解为
`zero` 的 l 重新解成 `succ n` ⇒ 误判可达。这正是 L07 设计 §6 的槽位
纪律："解前构建、解后消费"的值**必须在消费点用当前 σ 包裹**。

**修复**（`l13-explicit-subst-round5-gadt.patch`）：
- `ArmEntry` / `FilterResult` 新增 `refine: Rc<Subst>`，把逐列累积的
  GADT 精化 σ 随臂传到探测点（构造子分支处 `refine_acc = compose(新 acc,
  旧 acc)`，其余分支原样透传）；
- 探测前把头部类型置于该 σ 之下：
  `wrap_sub(&entry.refine, typ)` 再交给 `filter_accessible_constrs`。

**验收**：`test_pm_vec_bool_exhaustive` / `test_pm_tuple_vec_gadt` /
`..._no_prelude` **全部转绿**。全量 `l13_fast_parity` 因 `FRCS_MEMO` 长跑
内存残留（见"已知残留"）未能在单次进程内完整跑完（中断于 401/406），
分段实测对账：GADT 3 例 + hover 15 例 + calc 19 例全绿；整跑可见的失败
仅 3 个既有项（test14 / test_prove_term_pure /
test_stuck_match_application_does_not_panic）；第 4 个既有失败
`resident_compaction_matches_fresh_replay_across_kicks` 单独复跑确认仍
失败（与 round-3/4 基线一致，非本轮引入）。examples `typort check` 冒烟
正常。（提交 0ad32cd 信息里"跳过 3 个、397 通过"的口径以此段为准修正。）

### 途中试错（勿重复）

1. **把 σ 施加到递交给递归下降的全部头部类型**（`remaining_new_heads`）：
   过度精化——prelude 的 `list.typort` 立刻报
   `unreachable pattern: (let rest = list_init xs; match rest {...})`，
   prelude 加载失败。原因：头部类型同时被 quote/bind 进上下文，包裹会改
   变**绑定进去的**类型（旧机制只让 force 看到精化，quote 打的是原始
   变量名）。⇒ σ 只能**局部施加在探测点**。
2. 早先（第四轮）试过的 `force_chain`/`quote` 链式 VSub 透明解包同样
   改变行为（破坏"顶层非 VSub"不变式），已回退。

### 孪生版：同病，**未修**（记录分歧）

孪生版编译器**只在臂体叶子做精化**（`check_pm_final` 返回的 σ → 
`subst_cxt`，见 `bump_spine_iter.rs:12073-12081`），下降期**不退带
σ**：`Arm` 结构（`bump_spine_iter.rs:11760`）没有 σ 字段，逐列下降的
**6 个构造点**（11963 初始 / 12222 / 12408 / 12441 / 12511 / 12540）都不
携带精化（cxt 分别为 clone/bind_name/未精化上下文），探测点（12301）用的
仍是原始 `*typ` + 未精化 `arm.cxt`。

实测（临时探针，已从树中移除）：孪生版对同一输入报**与修复前参考版
逐字节相同**的错误 `non-exhaustive pattern: Tuple2.mk(zero, cons) not
covered; ...`。⇒ **镜像修复 = 把参考版的逐列精化搬进孪生编译器**
（结构性改动，非机械对齐）。当前参考版已修、孪生版未修，**任何覆盖
索引类型 match 的 REF/TWIN parity 都会分叉**——列入 round 6 首项。

### 剩余失败（第四轮已对照确认，均**非**本轮引入）

- `legacy_tests::test14`（期望 `find unsolved meta`，实得 `can't unify`）
- `legacy_tests::test_prove_term_pure`
- `legacy_tests::test_stuck_match_application_does_not_panic`
- `bump_spine_iter::observation_tests::resident_compaction_matches_fresh_replay_across_kicks`

前三条在 round-4 状态（即无本轮 GADT 修复）下同样失败，已用 stash 对照
验证；第四条在 round-3 状态同样失败。⇒ 它们属于移植的**另一些**语义差异，
round 6 需逐条定位（`test14` 的报错走向、`test_prove_term_pure` 的证明
搜索、`test_stuck_match...` 的卡住 match 应用）。

### 孪生镜像的实现前置分析（round 6 第 1 项的实施要点）

镜像不只是加 σ 字段，参考版的逐列精化依赖**头部值穿线**，孪生两者皆缺：

1. 参考版的 heads 是四元组 `(typ, name, icit, head_val: Option<Rc<Val>>)`：
   `compile()` 入口放 scrutinee 值（`Some(target_val)`），构造子分支把
   `head_val` 的 SumCase datas 按字段序传给子列
   （`head_val_datas.get(consumed_implicit_count + i)`）。
2. 孪生的 heads 是 `(Var, V, Span, Icit)`（`Var = i32`，仅编号），**heads
   里没有值**；scrutinee 值经 `compile()` 的 `target_val: V` 参数进入
   `Arm.ori`（bump_spine_iter.rs:11956/11976），但只在叶子 `check_pm_final`
   用——镜像时把既有参数接进 heads 第五元即可，无需改签名。
3. 需要搬的三块（对照参考版 pattern_match.rs 行号）：
   a. heads 加第五元 head_val + 入口/构造子分支的值穿线；
   b. 索引精化块：`unify_pm(head_typ, constr_ret)`（constr_ret = Pi 剥完
      隐参后的构造子返回类型，孪生的剥链循环在 12330-12375，循环结束的
      `cty` 即 constr_ret，需存出）；
   c. Rigid 头值传播块：head_val 为裸 Rigid 时
      `unify_pm(vvar(l), SumCase{datas: 新鲜字段 vvar})` → σ。
   然后 `refine_acc = compose(传播σ, compose(索引σ, 入臂σ))` 挂 `Arm.refine`
   （新字段，6 个构造点），探测点（12301）`wrap_sub(&arm.refine, *typ)`。

### test14 初步画像（round 6 第 2 项的入口）

`test14` 期望 `find unsolved meta`，实得 `can't unify`，两侧 spine：
`P {?32381 c b a (t+1)} → P {?32381 a b c (t+1)}` vs
`P {?32381 (t+1) a b c} → P {?32381 (t+1) a b c}`。注意 spine 里混入了
**`def t` 绑定器作用域的 `t`（`succ t` 打成 `t + 1`）**——顶层 `let test`
的方程里出现了前一个 def 作用域的变量：外层 meta 越界泄漏（已知限制 #1
地带）在 σ 机制下走向不同（怀疑与 `invert`/`prune` 的 `force_arg` 解包
VSub 后把越界 rigid 当可逆元的口径有关）。诊断入口：对失败方程打
pretty（unify 入口已有 `println!` 注释块），对照旧机制同输入的方程序。

## 接续建议（round 6 工作清单，按优先级）

1. **孪生版镜像 GADT 精化**（第 5 节）：把参考版的"逐列精化 σ 随臂下传 +
   探测点包裹"搬进孪生编译器（`Arm` 加 σ 字段、下降期构造 Arm 时带上、
   探测点 `wrap_sub`）。在此之前任何覆盖索引类型 match 的 REF/TWIN parity
   都会分叉——这是当前**唯一已知的 REF/TWIN 语义分歧**。
2. **剩余 4 个既有失败**（第 5 节末）：`test14`（报错走向：期望
   `find unsolved meta`）、`test_prove_term_pure`、`test_stuck_match_
   application_does_not_panic`、`resident_compaction_matches_fresh_replay_
   across_kicks`。逐条与旧机制对照定位。
3. **meta 解链**（第四轮第 2 节）：深链来自某处把 meta 解成"含下一个已解
   meta 的构造子"，需定位构造点（建议在 `MetaEntry::Solved` 写入处加环
   检测/深度上限，或扩展 `solve` 的 occurs 面）。修好后默认测试栈不再溢出，
   parity 才能进 CI 口径。
4. **纯 elaboration 的 28×**：以 `DIAG10`（compiler 占 quote 绝大多数）为
   入口做编译器分支级缓存（探测结果按 (构造子, 目标类型) 缓存、ret_type
   重锚按 canonical σ 缓存）；配合 σ 内容寻址内化才能真正把指针键缓存救活。
5. **孪生版 FRCS_MEMO 等价物**：孪生 frcs/XCell 无对应记忆化（round 4/5
   未动孪生性能）。
6. **评审轮补充的工程项**（按性价比）：
   - meta 快照改 undo journal（`filter_accessible_constrs` 每轮探测
     `infer.meta.clone()` 整表拷贝 → journal 记 (下标, 旧值) 逆放；
     `solve` 写入全是下标赋值，语义零变化）——compiler 是 quote 最大
     发起方（DIAG10: 63,953 次），这是其最大常开非缓存开销；
   - `constr_pi` 的 `infer_expr(构造子名)` 按名缓存（每列每构造子重推）；
   - 探测缓存键不要用裸指针（`probe_typ` 每列都是 `wrap_sub` 新建 Rc，
     指针必 miss）——对 forced probe 类型 quote 一次取规范 Tm 哈希做键；
   - `unify_nat_chain` 硬编码 `None` spec 且回填（深路径 Nat 链方程丢
     特化）；QUOTE_MEMO 补 taint/fuel 守卫（与 FRCS_MEMO 口径一致）；
     `accessible_set` 每列只按 `arms.first()` 的 refine 计算——修种子化后
     应评估 per-arm 探测；`typeclass.rs` 的 `val_match`/`vals_eq_ground`
     无 VSub 臂——补"精化臂内 trait 解析"钉子测试；
   - 孪生 `check_pm_final` 在未精化 env 求值 `ori_v`、叶子 ret_type 不
     wrap、**frcs Pi 臂对平坦 defs env 跳过 `frcs_env` 包裹**（其自身
     mentions_level 扫平坦槽，"判真后拒绝包裹"致精化在该闭包读点静默
     丢失）——三项并入 round-6 #1 的孪生镜像范围；
   - 参考版 `spec_refine`（elaboration.rs:557-569）无"已解"守卫：fuel 耗尽
     时 frcs 静默返回裸 rigid，可 cons 出遮蔽旧解的冲突解（仅 fuel 有界
     降级域可达）——防御性加 `spec.acc.has(*x)` 检查可闭合（评审轮 A-P2）；
   - FORCE_MEMO（HEAD 既有）补 `fuel0 > 0` 下限已随本轮落地（fuel=0 降级
     结果入缓存的正确性洞），内存口径仍待 Weak 输入改造。
7. 验收口径不变（`l13_fast_parity` 全绿 / 全量 `cargo test` / 65 例裸语言
   diff / examples `typort check` / l13bench ≤1.5×：基线 prelude-core
   basic 22.4ms、fast 12.8ms，prelude-hdl 3080ms / 1321ms）。

### 已知残留（记录，未修）

- `FRCS_MEMO` 内存口径：1<<18 上限 + 溢出按输入存活清扫，在**长跑大负载**
  （legacy_tests 全量、parity 套件整跑）下仍会累积到 GB 级（实测单进程
  13 GB 仍在涨）——强持结果钉住重建图的量级随活跃值集增长。round 6 需要
  更激进的回收——性能复验报告的改进建议排序：1) 双代清空（young/old，
  命中晋升，young 满只清 young）；2) "σ 内锚 map"变体（memo 搬进
  `Rc<Subst>` 内部，产物生命周期 = σ 生命周期）；3) 按权重预算只作双代
  之上的补充。
- `FORCE_MEMO`（HEAD 既有，非本补丁引入）：1<<20 输入+结果**双双强持**、
  溢出仅整体清空，是长跑内存的另一共同被告。其 fuel=0 正确性洞已随评审轮
  修复闭合（插入守卫现含 `fuel0 > 0`）；**剩余仅内存口径**：建议改 Weak
  输入 + retain 存活（照 FRCS_MEMO 已验证的模式）。
- 常开小浪费（评审轮 P2 打包）：`DECL_PROBE` 的 env::var 每 Class decl
  查一次（应 OnceLock）；completion_table push 未过 lsp_collect 闸；
  mentions_level 原生递归无 visited；compose 的 cons_all O(|inner|·|outer|)
  递归。均已列入 round-6。

### 评审轮（2026-09-17，5 子 agent 多角度评审）结论与处置

| 视角 | 结论 | 已处置 |
|---|---|---|
| 正确性 | σ-ABA（P0）→ **已修**（σ 半边 upgrade+ptr_eq）；fuel=0 缓存洞（P1）→ **已修**（FRCS_MEMO/HOVER_RENDER/FORCE_MEMO 插入守卫 `fuel0>0`）；hover 键缺 decl 身份、叶子 Flex 臂不包 σ → 记录（P2，显示层/对齐旧版）；复验新发现：refine_acc 失败路径丢种子（P1）→ **已修**、spec_refine has 守卫 → round-6 | ✅ |
| 性能资源 | FRCS_MEMO σ-ABA 同上已修；inlay 总闸 → **已修**；FORCE_MEMO 残留 → 本节记录（其 fuel0>0 已随轮落地）；meta 快照 undo journal、双代清空、σ 内锚 → round-6 清单；复验新发现：第二 inlay 生产点未过闸（P2）→ **已修**、归因计数未挂 DIAG（P2）→ 记录 | ✅/📋 |
| 测试完整性 | 补丁声明全部实测成立；**蓝图 §9.5 钉子缺失（P1）→ 已补**，实测暴露 fn 型索引槽解析应用在 HEAD 基线即未实现（既有限制），钉子测试标 `#[ignore]` 留档 | ✅ |
| 文档交付 | round-5 数字对账（P1）→ 本节修正；6 项 P2 表述/一致性 → **已修**；复验新发现：HOVER_RENDER fuel0>0 声称与代码不符（P1）→ **已修**（补守卫）、评审表可追溯性 → 已补 | ✅ |
| 架构机制 | 内层精化块未种子化（P1）→ **已修**（种子 + extend，失败路径种子保持由 `refine_acc = entry.refine` 初始化闭合——复验 E-P1）；孪生 Pi 平坦 env 跳包裹（P1）→ round-6 清单；未记录偏差（Flex occurs 不透明、v_applicable 含 Lam/Call）→ 本节偏差清单补录；typeclass 表面、QUOTE_MEMO 守卫、unify_nat_chain 丢 spec → round-6 清单 | ✅/📋 |

补录的**有意偏差**（此前未记录）：
1. `val_mentions_lvl` 对 Flex 实参不透明（L07 扫 Flex spine）——probe 的
   fresh-meta pruning 合法形所需，后果是 meta 介导的间接环不被 occurs 拒绝、
   由 force fuel 兜底（与 meta 解链同地带）。
2. `v_applicable` 含 Lam/Call（L07 不含 Lam）——方向更完备（对齐 dpm-nbe
   napp），λ 解 + 非空 spine 在 L13 会 β、L07 卡回裸 rigid。

## 历史根因记录（早前轮回的定性，已按第三/四轮实测修正）

1. ~~"一个 meta/中性头被累积应用到约 7.8 万个 VSub 包裹的实参上"~~
   → 第四轮修正：是**meta 解链**逐层 force 展开（第 2 节）。
2. 参考版 quote 无记忆化且 `quote_sp` 递归 ⇒ 8MB 测试栈爆栈——**部分
   成立**：`quote_sp` 已迭代化，但**深链仍以原生递归展开 12k 层**（第四轮
   画像）。
3. ~~calc_err_* 报错文案回归~~ → 第三轮实测不复现。
4. "frcs 重建 + memo 失效"是次因——成立；第四轮的 `FRCS_MEMO` 即针对它，
   但强结果的内存口径必须收紧（第 5 节数据）。

## 附带发现（对文档的订正）

`docs/pattern-match-refinement-analysis.md` 的复现程序经移植前后对照：
**显式替换未使任何"失败→成功"发生**，且其中 weak01/02/04 与文档的
`vtail` 控制例本身即类型错误（文档基线也自认"正确拒绝"），weak03 现状
已通过。该文档的"一般性缺陷"论断过度概括，已在
`docs/explicit-subst-refactor-status.md` 记录订正。
