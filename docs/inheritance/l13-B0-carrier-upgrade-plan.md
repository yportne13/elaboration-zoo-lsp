# L13 载体升级（B 路线）P0：冻结基线 + 重启侦察（2026-11-25）

> 用户决策：L13 走 **B（载体升级）**。本文件记录开工前的冻结基线、历史证据复核、
> 与第一阶段的实施计划。**当前尚未改动任何 L13 源码。**

## 0 为什么必须先冻结

B 路线动的是 L13 **生产内核**（LSP / HDL / prelude 全依赖）。历史上这条路线走过五轮
（2026-09-15…09-17），**全部回退**。所以本路线的前置条件不是"写代码"，而是：

1. 有一份**逐字节可比的 oracle**（否则改坏了也不知道）；
2. 明确**哪些历史失败是真的语义问题、哪些只是当时的工程欠债**（前者才是真拦路虎）。

## 1 冻结基线（已落盘，`target/b-l13/baseline/`）

| 文件 | 内容 |
|---|---|
| `l13_lib_tests.txt` | 635 个 lib 测试名（`cargo test --lib L13_namespace:: -- --list`） |
| `l13_inherited_tests.txt` | 22 个继承用例名 |
| `examples.txt` | 5 个 example 的 exit + 输出字节数 |
| `out_*.txt` | 5 个 example 的**完整输出**（逐字节比对用） |

当前基线（HEAD `c42a9f91`+）：lib **622 passed / 13 ignored**、examples **5/5 exit=0**。

## 2 历史证据复核（决定路线可行性的关键）

### 2.1 五轮失败的真实原因（`docs/wip/README.md` + `docs/l07-l13-implementation-audit-2026-11-16.md` §3.4 N2）

| 轮次 | 失败现象 | 性质 |
|---|---|---|
| round1–round3 | 裸语言 65 例 `diff=0`（语义对），但 **prelude 21s → 挂起** | **工程欠债**：不是 σ 错了，是 prelude 加载期做了 10–12s 的 hover 渲染 |
| round4 | prelude 21s → **9.3s**（已落地，零行为变更）；但 2k 深 quote 栈溢出 | 一半工程（LSP 表总闸）、一半真实（深 meta 解链） |
| round5 | GADT 覆盖误报 non-exhaustive（`test_pm_vec_bool_exhaustive` 等 3 例）+ 孪生常驻压缩一致性 26.8s 失败 | **真实语义回归** |

⇒ **关键判断**：五轮里只有 round5 那批是"σ 与 L13 GADT 覆盖检查的语义冲突"，
其余两轮是**当时的工程欠债**（hover 渲染总闸、深链栈安全）。而这两项欠债在
2026-09 之后**已被各自独立修复**：

- `lsp_collect` 总闸已进 L13（`load_prelude_state_impl` 末尾清表，见 round4 结论；
  当前 L13 也有 `clear_observation_tables`）；
- 深链栈安全：L12 已有 `rename_deep`/`quote_deep` 的帧式收集器（**纯栈安全化，非语义**），
  可直接移植。

⇒ 所以 B 路线**真正要面对的只剩 round5 那一类 GADT 覆盖冲突**，不是五轮全部。

### 2.2 已有可复用资产

| 资产 | 位置 | 状态 |
|---|---|---|
| 孪生 σ 移植（**成功**，match/prelude-core/examples-hdl 快 2.5–5.5%） | 分支 `perf/l13-twin-sigma`（3 commits，+1308/−307） | 未合入 master；含 L13 特有坑的解（`force_arg` 必选、`vapp1` VSub 臂、σ 归还顺序防 UAF） |
| 参考版 σ 五轮累积补丁 | `docs/wip/l13-explicit-subst-round5-gadt.patch` | 对当前 HEAD **CONFLICTS**（文件谱系已变），但可作为逐行参考 |
| L12 的 σ 实现（权威） | `src/L12_canonical/{mod,cxt,unification}.rs` | 活的，门禁全绿 |

**孪生分支的价值**：它是**同一套语义在 L13 上跑通了**的证明，且记录了三处
L13 特有坑的具体解法。参考版可以直接照它的形状做，不用再摸索。

## 3 缺口分类（125 项 ARCH-DIVERGED）

| 类别 | 项数 | 行数 | 说明 |
|---|---:|---:|---|
| **σ 载体相关** | 24 | 1225 | `Subst`/`SubEntry`/`frcs`/`subst_cxt`/`NameState`/`mentions_level`/`SpecSolve`/`lookup_hit`/`extend`/`compose`/`force_arg` + 深链 `rename_deep`/`frame_*` |
| 其它（形态/产品面） | 101 | 2420 | `prim_reduce`/`quote_arm`/`infer_owned`/`walk_con`/`parser` 族——实现形态差异，不属载体 |

⇒ B 路线的**代码对象是那 24 项 / 1225 行**，不是全部 125 项。

## 4 实施计划（B0 → B3，每步独立门禁）

| 步 | 内容 | 门禁 | 预估 |
|---|---|---|---|
| **B0**（本文件） | 冻结 oracle + 历史复核 + 缺口分类 | 基线落盘、5/5 examples | 已完成 |
| **B1** | **栈安全先做**：移植 L12 的 `rename_deep`/`quote_deep` 帧式收集器到 L13（**纯栈安全化，语义零变化**）。这一步能独立验证"round4 的栈溢出"是否已被解决 | lib 622 + examples 5/5 + 逐字节输出 | 1 轮 |
| **B2** | **σ 载体本体**：`Subst`/`SubEntry`/`lookup_hit`/`extend`/`compose`/`mentions_level`/`frcs`/`frcs_env`/`subst_cxt` + `Val::VSub` 变体 + `force` 的 frcs 臂。**照 `perf/l13-twin-sigma` 的形状做**（含三处 L13 特有坑） | lib 622 + examples 5/5 逐字节 + `l13_inherited_from_l12` 22 | 2–3 轮 |
| **B3** | **精化调用点切换**：`unify_pm` 累加 σ（不再 `update_cxt`）、`check_pm_final` 返回 σ、`NestedCheck` 存 σ 快照；删除 `update_cxt`/`refresh` | 同上 + GADT 覆盖用例（round5 的那 3 例） | 2–3 轮 |

**先做 B1 的理由**：它零语义风险，却能把"round4 的栈溢出"从待办里划掉——
这样 B2 面对的失败面就只剩 round5 一类。

## 5 退出条件（不硬扛）

任一阶段出现下列情况即回退并记录，不继续硬推：

- lib 622 里出现 >5 例不可收敛的失败；
- examples 输出**逐字节不等**且无法解释；
- prelude 加载墙钟回退 >50%（对比 `target/b-l13/baseline`）。

## 6 与 L12 的关键差异（B2/B3 必须处理的）

| 项 | L12 | L13 | 影响 |
|---|---|---|---|
| 值表示 | owned `Val` | `Rc<Val>` 全机 | σ 条目存 `Rc<Val>`，`VSub` 是 `Rc<Val>` 包裹 |
| `Val::Sum` | 3 元组 | 4 元组（+is_trait） | `frcs` 的 Sum 臂要带 `is_trait` |
| `Val::SumCase` | 3 字段 | 5 字段（+is_trait/index） | 同上 |
| Nat | 无 | `Val::Nat(u64)` | `frcs`/`rename`/`quote` 遇 Nat 直接返回（无变量可代换） |
| 名字 | `VSpan` | `Span<SmolStr>` | `SubEntry` 无关；但 `NameState` 的键是 `SmolStr` |
| 预算 | `Cell<u32>` fuel | `burn_fuel` 结构化 | PM_FUEL 可直接接现有 `burn_fuel` |

## 7 B1 实施细节：栈安全化（先做，零语义风险）

### 7.1 L13 现状：部分已做，部分仍是递归

| 深链路径 | L13 当前状态 | 依据 |
|---|---|---|
| `eval`（Sum/SumCase 链） | **已是帧式**（`Frame::EvalArg` 栈） | 源码注释明写 "one native stack frame per node 会溢出" |
| `quote` 的 **SumCase 单构造子链** | **已是迭代**（`nodes` 链） | 注释明写 fast path |
| `quote` 的 **Sum 参数** / **SumCase 多字段** | **仍递归** | 逐层 `quote_inner` |
| `rename` 的 **Sum/SumCase/Obj** | **仍递归** | 无帧式收集器 |
| `force` 的 frcs/meta 解链 | 有 `burn_fuel` 预算兜底 | 不是栈问题 |

⇒ B1 的代码对象精确到**三处**：
(a) `rename` 的 Sum/SumCase/Obj 帧式收集器（照 L12 `rename_deep`，324 行）；
(b) `quote` 的 Sum 参数帧式化；
(c) `quote` 的 SumCase 多字段帧式化。

### 7.2 为什么先做它

round4 的失败现象"2k 深 quote 栈溢出"**不是 σ 引起的**——σ 只是让值变深（`VSub` 包裹），
而栈溢出发生在 `quote_inner` 的递归臂上。把这三处改成帧式后：

- 深链不再消耗 native 栈（与 σ 无关的独立修复）；
- B2 引入 `VSub` 后，`force` 的 frcs 臂会**再增加一层**包裹深度——如果那时才做栈安全化，
  "栈溢出"与"σ 语义错"会混在一起，难以归因。

### 7.3 验收

| 项 | 判据 |
|---|---|
| lib | 622 passed / 13 ignored（与基线逐条同名） |
| 继承用例 | `l13_inherited_from_l12` 22 passed |
| examples | 5/5 exit=0 且输出**逐字节**等于 `target/b-l13/baseline/out_*.txt` |
| 新增 | 一个"深链不爆栈"的回归测试（default stack 2MB 下跑 2k 深 Sum/SumCase） |

基线已冻结在 `target/b-l13/baseline/`（635 个测试名 + 5 份完整输出）。