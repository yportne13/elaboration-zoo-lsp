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
0.2s / 1.12M）、eval 3.5s（基线 3.0s）、check 2.2s（基线 0.15s，其中
unify_pm 2.3s）。`infer_expr` 调用数与基线**完全一致（118,304）**而单次
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

## 接续建议（round 5 工作清单，按优先级）

1. **先修 GADT 覆盖回归**（第 4 节 3 例）：定位移植后"可达性/覆盖"判定与
   旧 `update_cxt` 口径的差异（`accessible_constructors` 的探测 σ 与
   `bind_slots` 基线、`is_refined` 语义）。这是**能否落地的前置条件**。
2. **再修 meta 解链**（第 2 节）：深链来自某处把 meta 解成"含下一个已解
   meta 的构造子"，需要定位构造点（建议在 `MetaEntry::Solved` 写入处加
   环检测/深度上限，或对 `solve` 的 occurs 面扩展）。修好后默认栈不再溢出，
   parity 才能进 CI 口径。
3. **纯 elaboration 的 28×**：以 `DIAG10`（compiler 占 quote 绝大多数）为
   入口，做编译器分支级缓存（探测结果按 (构造子, 目标类型) 缓存；ret_type
   重锚按 canonical σ 缓存）；配合 σ 内容寻址内化（见 round-3 记录第 3 项）
   才能真正把指针键缓存救活。
4. **孪生版同批**：孪生 frcs/XCell 无 `FRCS_MEMO` 等价物（round 4 未动
   孪生）；参考版与孪生版的 hover 总闸口径已一致。
5. 验收口径不变（`l13_fast_parity` 全绿 / 全量 `cargo test` / 65 例裸语言
   diff / examples `typort check` / l13bench ≤1.5×：基线 prelude-core
   basic 22.4ms、fast 12.8ms，prelude-hdl 3080ms / 1321ms）。

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
