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

## 8 B1 完成记录（2026-11-25）

### 8.1 改了什么

L13 `unification.rs` 的 `rename` 拆成两段：`rename`（入口，按值形态分流）+ `rename_deep`（Sum/SumCase/Obj 帧式收集器）+ `rename_arm`（浅结构递归臂，原 `rename` 的 match 体原样搬入，只把 `t` 的引用/所有权形态改成 `&Rc<Val>`）。

新增 `src/L13_namespace/deep_chain_tests.rs`：两个栈安全回归测试。

### 8.2 语义等价的证据（三层）

| 判据 | 结果 |
|---|---|
| L13 lib | **624 passed / 13 ignored**（622 + 新增 2），零失败 |
| examples 5/5 | 输出与 B0 基线**逐字节相同**（剥掉计时行后） |
| 测试有牙 | 把 `rename` 回退成旧的逐点递归实现，`deep_sumcase_rename` **在 2 MB 默认栈上爆栈**（`thread ... has overflowed its stack`，exit `0xC0000409`）；换回帧式实现即通过 |

第三条是关键：没有它，"栈安全化"就只是个说法。现在它是**可复现的红/绿对比**。

### 8.3 与 L12 的差异（移植时纠正的两处）

| 项 | L12 `rename_deep` | L13 实现 | 原因 |
|---|---|---|---|
| `Sum` 参数 pending | `[实参值, 类型]` 交替，都 `rc_take` 成 owned | 同样交替，但保留 `Rc<Val>` | L13 全机 `Rc<Val>`，不做 owned 降级 |
| `SumCase` 组装 | 需 `case_name` 字段（L12 的 `Val::SumCase` 带 `case_name`） | **不需要**——L13 的 `SumCase` 只有 `is_trait/typ/index/datas`，构造子名在 `datas[0].0` | 载体形态不同，照抄会多一个语义上不存在的字段 |

### 8.4 遗留

- `quote` 的 **Sum 参数** 与 **SumCase 多字段** 仍递归——但实测这两条路径在 5 万深链下**没有爆栈**（`deep_sumcase_quote` 通过）。真正需要帧式化的是 rename，不是 quote。
- 因此 B1 的代码量比预想小：**只动了 `rename` 一条路径**（+213/−120 行），不是计划里写的三条。

## 9 B3 前置探测（2026-11-25，route 2）

### 9.1 上一轮结论的更正

上一轮我判断 "`already_refined` 分支在 624 个 lib 测试里是死路径" —— **这是错的**。
实际是探针实现有 bug（两个独立 `static` 计数器，report 读的是从未累加的那个），
加上打印条件 `total % 1000 == 0` 让它在 total=8137 时也只打在中间不明显的时刻。本轮修正探针实现后得到真值：

| 计数器 | 含义 | 实测 |
|---|---|---:|
| `total` | `already_refined` 判定总调用 | **8137** |
| `env_only` | env 槽已精化但 σ 不知道 | **0** |
| `sub_only` | σ 已有解但 env 槽仍是 self-reference | **12** |

### 9.2 这 12 次分歧的含义

全部是 **σ 先知道、env 槽还没改**。这正是路线 2（双载体并行）的偏差窗口：

- `update_cxt` 里 `refresh` 会把 env 整段重锚定，耗时但同步；
- σ 是 O(1) 叠链，**立刻**生效；
- 所以在 `refresh` 还没跑完（或某些臂干脆不跑 refresh，比如 `update_prune=false`）的窗口里，σ 和 env 会短暂不一致。

`env_only = 0` 是更强的信息：**从来没有出现过 "env 知道而 σ 不知道"**。这说明 σ 是 env 的严格超集——
凡是 env 槽被改写过的地方，σ 都有对应条目。反过来不成立（12 次）。

### 9.3 对 B3 第二段的意义

⇒ 把 `already_refined` 判定从 env 槽换成 `cxt.sub.has(x)`，**不会漏掉任何一次已经发生过的精化**
（因为 env_only=0），只会**多认出 12 次** σ 已记录但 env 未同步的精化。

那 12 次多认出的效果是：本来会走 `update_cxt` 覆盖写，现在会走「取旧精化值再 unify」的递归臂。
这与 L12 的 σ 语义一致（σ 链天然"取最新"，不需要 already_refined 那套三档判定）。

**所以 B3 第二段的第一步（判定换源）风险可控**：它是"多认 12 次"而不是"改变已有判定"。

## 10 B3 第二段第一次尝试：失败并回退（2026-11-25）

### 10.1 做了什么

按 §9 的探测结论，把 `unify_pm` 两处 `already_refined` 判定从「查 env 槽」换成「查 σ」
（`cxt.sub.has(*x)`），并把旧值提取优先从 `cxt.sub.lookup(*x)` 取。

### 10.2 结果：栈溢出

```
lib: exit 0xC00000FD (STATUS_STACK_OVERFLOW)
test 'L13_namespace::bare_ctor_member_tests::applied_and_concrete_receivers_still_show' has overflowed its stack
```

### 10.3 根因（已定位）

`cxt.update_cxt` 往 σ 里存的是 `infer.wrap_sub(&self.sub, &v_for_sub)` —— 但 `update_cxt` 的 `v`
在 `(Rigid, _)` 臂里来自 `t_prime`，而 `t_prime` 可能是**未解/卡住的形态**。更关键的是：

- 旧载体：`env.change_n` 之后由 `refresh` 遍历重锚定，`Rigid(x)` 的槽会被真正替换成解值；
- 新判定：`sub.has(x)` 立刻为真，下一轮同 `x` 的调用进 `already_refined` 臂，
- 取 `cxt.sub.lookup(x)` 拿到的是**包裹了 `VSub` 的解值**，再 `unify_pm(cur, t_prime)`，
- 该值经 `frcs` 展开时又触发 `Rigid(x)` 的 lookup 命中……递归没有终止点。

`env_only = 0` 只证明 σ 覆盖了 env 的**已知条目**，不证明 σ 里的值形态与 env 槽等价——
env 槽是 `refresh` 之后的**重锚定值**，σ 里是**原始解值**。两者不同构。

### 10.4 结论与下一步

判定换源不能单独做，必须与「`refresh` 的重锚定」一起换（也就是真正删掉 `update_cxt` 的
env 改写），否则 σ 存的是未重锚定的值，拿来当精化值会递归。

⇒ 这印证了 §8.4 的判断：B3 第二段真正的工作量在 `refresh`，不在判定。下一步要先把
「σ 里的值需要什么形态」定清楚（是重锚定后的值，还是原始解值 + 读点 frcs 展开）。

## 11 根因的更深一层：σ 里的值形态（对照 L12 SpecSolve）

读 L12 的 unify 后，σ 存值的口径很清楚（unification.rs:1069-1116）：

```rust
(Val::Rigid(x, sp), v) if sp.is_empty() && spec.solvable.contains(x) => {
    if val_mentions_lvl(v, *x) { return Err(...) }        // 单步 occurs
    if acc.mentions_any_solved(v) && acc.occurs_transitive(v, *x) {
        return Err(...)                                    // 传递 occurs
    }
    s.acc = Subst::extend(&s.acc, *x, v.clone());          // 存原始值
}
```

关键三点：

1. 存的是原始值 v（已 force，但未包裹 σ），不是重锚定后的值；
2. 存之前做两级 occurs 检查（单步 val_mentions_lvl + 传递 occurs_transitive）；
3. 每步递归入口把 acc 包在两侧再解释（`if !s.acc.is_empty() { t = force(wrap_sub(acc, t)) ... }`）。

### 11.1 L13 的 update_cxt 缺了什么

上一轮的做法是「update_cxt 里 Subst::extend(&self.sub, x, wrap_sub(...))」——三个全错：

| 项 | L12 | 我的做法 | 后果 |
|---|---|---|---|
| 存什么值 | 原始值 v | wrap_sub(sub, v) 包裹过的值 | 值里嵌着 σ，lookup 取出后 frcs 又展开，递归 |
| occurs 检查 | 单步 + 传递两级 | 完全没有 | x := ... x ... 直接进 σ，读点无限展开 |
| 何时应用 | 每步递归入口包两侧 | 只在 already_refined 取旧值时用 | 后续子方程看不见前面的解 |

第 1 条是栈溢出的直接原因：wrap_sub 把 VSub(v, sub) 存进 σ，下次 lookup(*x) 返回的还是带 VSub 的值，frcs 展开时又命中同一个 x。

### 11.2 正确的做法

σ 必须存原始值，且 update_cxt 里要补两级 occurs 检查。但这只是「存」的正确性；「读」的正确性要求 unify_pm 每步递归入口都按 acc 包两侧——这正是 L13 的 unify_pm 没有的形状（它靠 env 槽被 refresh 改写来实现「后续子方程看见前面的解」）。

⇒ 结论：路线 2 的「双载体并行」在本轮被证伪。σ 与 env 槽不是可以并行的两套信息，而是两种根本不同的传播机制：env 槽靠 refresh 一次性改写全局，σ 靠每步包裹 + 读点展开。折中方案两头不讨好。

### 11.3 下一步的选择

| 路线 | 内容 | 代价 |
|---|---|---|
| B3' | 按 L12 原样改 unify_pm：签名穿 SpecSolve，每步入口包两侧，check_pm_final 返回 σ | 3 文件 + 14 调用点，但形状正确 |
| B4 | 放弃 σ，B 路线缩回到 B1（栈安全化）+ B2 骨架（保留但不启用） | 已完成的 B1 有价值，B2 变成死代码 |

我倾向 B3'：既然已经知道正确形状是什么，就按正确形状做。之前选路线 2 是想避开 14 个调用点，但现在证明那条路走不通。

## 12 B3 第二段第二次尝试：仍然失败（2026-11-25，已回退）

### 12.1 改了什么

按 §11.2 的正确口径修 `update_cxt` 的 σ 存值：

- 存**原始解值**（不 `wrap_sub`）；
- 补两级 occurs 守卫（单步用只含 `x` 的临时 σ 判 `mentions_level`；传递用现有 σ 判）；
- 新增 `Cxt::subst_cxt`（L12 同构：env 槽包 `VSub`、槽位布局不变、σ 空零开销）。

### 12.2 结果：lib 绿但 examples 栈溢出

| 判据 | 结果 |
|---|---|
| `cargo check --release --lib` | 0 error |
| L13 lib（624 用例） | **624 passed** |
| `typort check examples/*.typort` | **两个 example 栈溢出**（`thread has overflowed its stack`） |

adder_proof 与 alu 在真实负载下爆栈，而 lib 的 624 个用例全过——说明**单元测试覆盖不到这条路径**，
正是 §11 分析里说的「σ 与 env 槽的传播机制差异」。

### 12.3 结论

两次尝试（判定换源、存值修正）都失败，且失败形态不同：

| 尝试 | lib | examples | 失败形态 |
|---|---|---|---|
| 判定换源 | 栈溢出 | — | `already_refined` 取 σ 原始值递归 |
| 存值修正 | **绿** | 栈溢出 | 真实负载下 VSub 链过深 |

第二次数值上更接近成功（lib 全绿），但 examples 是**硬门槛**（B0 冻结的 oracle 之一）。

### 12.4 判断

**路线 2 彻底证伪。** σ 要在 L13 上工作，必须同时满足：

1. `unify_pm` 每步入口按 acc 包两侧（L13 没有）；
2. 深链 VSub 的展开有栈安全保证（`frcs` 是递归的，B2 里我没做帧式化）。

第 2 条是我在 B2 里就预见到的问题（当时说「孪生版 frcs 是递归的，参考版直接递归会重新引入栈问题」），
现在实证了。

### 12.5 退出条件触发

按 §5 的退出条件：「examples 输出逐字节不等且无法解释」→ 已触发（且是崩溃而非输出差异）。
**B 路线到此为止需要用户决策**：继续做 B3'（完整换载体 + 帧式 frcs）还是缩回 B4（只保留 B1）。

## 13 第 11 轮：σ 链迭代 Drop（已落地）+ 二进制新鲜度纪律

### 13.1 修复：`impl Drop for Subst` 迭代排空

σ 链每次精化 `Subst::extend` 叠一条，真实负载下可达数万深。派生 Drop 逐层递归释放
`SubEntry.next`，默认 2 MB 栈上 `STATUS_STACK_OVERFLOW`。

改为逐节点摘 `next` 移入待处理表再释放（与 `Val`/`Tm` 的排空式 Drop 同款）。链头仍被别处持有时放回，
由最后持有者走排空路径。

提交 `f6ced3d1`。新增 `deep_subst_chain_drop_does_not_overflow_default_stack`（10 万深链 + 默认栈），
**红绿对照已验证**：把 `impl Drop for Subst` 剥掉，同一测试立刻 `STATUS_STACK_OVERFLOW`（exit 0xC00000FD）。

### 13.2 纪律：二进制新鲜度

第 10 轮发现 `typort.exe` 被挂起进程锁住，导致 `cargo build` 静默失败、examples 一直跑的是 17:42 的旧二进制。
`baseline` 那次"examples 栈溢出"因此**证据不可靠**。

本轮采用三条纪律：

1. 跑 examples 前先 `taskkill` 所有 `typort` / `elaboration_zoo` 残留进程；
2. 记录 `typort.exe` 的 `LastWriteTime`，确认**晚于**最新源码时间；
3. 构建失败必须肉眼确认 `build=0`，不能只看"命令返回了"。

### 13.3 本轮实测（全部在干净二进制上）

| 判据 | 结果 |
|---|---|
| `cargo build --release --bin typort` | build=0，binary 19:48:14（晚于源码 19:39:58） |
| examples 5/5 | **逐字节等于 B0 基线** |
| L13 lib | **625 passed** / 13 ignored（624 + 新增的 drop 测试） |
| 链继承门禁 | 2 passed |

### 13.4 对 B3 的意义

σ 链 Drop 爆栈是**独立于传播机制**的缺陷，与"σ 还是 env 槽做载体"无关——它属于 B2 引入的
数据结构本身。修掉它之后，第 9/10 轮观察到的 examples 溢出**很可能是这个 Drop 缺陷**而非
`already_refined` 判定问题。

⇒ **B3 第二段需要重做**：在干净的 Drop 实现上重新验证 σ 存值策略，才可能分清"Drop 爆栈"与"语义递归"。

## 14 第 12 轮：B3 第二段重做（干净 Drop + 新鲜二进制）

### 14.1 实验平台问题（先说清楚）

本轮发现真正的构建阻塞：栈溢出后残留的 `typort` 僵尸进程（**0 线程、Access denied**）
会锁住 `target/release/typort.exe`，让 `cargo build` 静默失败（`拒绝访问 os error 5`）。
这些僵尸的父进程是 `cmd.exe`，`taskkill /F /T` 也杀不掉。

**对策**：改用独立 target 目录 `target_b13` 构建验证。本轮所有 examples 结果都来自
`target_b13/release/typort.exe`（时间戳已验证晚于源码）。

### 14.2 三次实验结论

| 实验 | lib | examples | 坍缩点 |
|---|---|---|---|
| 阶段1：只换判定（`cxt.sub.has`） | — | **栈溢出** | σ 说已精化，但 env 槽仍是 self-reference，取到 `Rigid(x)` 自身 → 无限递归 |
| 阶段2：判定 + 取值换源 + 存原始值 | — | **栈溢出** | 同上（取值虽优先 σ，但 σ 里存的就是原始解值，仍可能是 `Rigid(x)`） |
| 阶段2+自引用守卫 | — | **不溢出，但 prelude 语义错** | `prelude elaboration failed: can't unify Fin(t+1) vs Fin(_n1)` |

### 14.3 决定性的第三行

加自引用守卫（`if cur 仍是 Rigid(x) 本身 { return Ok(cxt.clone()) }`）后**栈溢出消失了**，
但 examples 输出变成 prelude 检查失败 + 大片 `name not in scope`（因为 prelude 没加载成功）。

两条硬事实：

1. 栈溢出的直接机制**确认**是「`already_refined` 为真但取到自引用值 → 递归」；
2. 加守卫能挡住递归，但**σ 的生效时机与 env 槽不同**——σ 一旦叠上就立刻对所有读点可见，
   而 env 槽要等 `refresh` 才生效。这个时序差导致 prelude 的 GADT 精化提前发生，类型检查就错了。

### 14.4 结论（这次证据是干净的）

**路线 2 确实不可行，但理由与第 9/10 轮说的不同**：

- 第 9/10 轮的「栈溢出」有两种成因混在一起（Drop 缺陷 + 自引用递归），归因不清；
- 本轮分离后：Drop 缺陷已由 `f6ced3d1` 修掉；剩下的真问题是**载体时序**——σ 即时生效、
  env 槽延迟生效，两者不能并存。

⇒ 要在 L13 上用 σ，必须**整体替换** env 槽载体（不是并行），即路线 B3'（`unify_pm` 穿 `SpecSolve`，
`refresh` 删除）。这是 L12 的形状，也是唯一自洽的形状。

## 15 第 13 轮：B 路线收口（B4）

### 15.1 决策依据

B3 连续三轮失败，且每轮的失败点已被独立确认：

| 轮 | 现象 | 真因 |
|---|---|---|
| 9 | 判定换源 → 栈溢出 | σ 说已精化但 env 槽仍是 self-reference，取到 `Rigid(x)` 自身 |
| 10 | 存值换源 → examples 栈溢出 | 二进制被僵尸进程锁住，证据无效 |
| 12 | 判定+取值+守卫 → 不溢出但 prelude 语义错 | σ 即时生效 vs env 槽等 `refresh`，时序不可并存 |

第 12 轮的第三条是决定性的：它证明**路线 2（双载体并行）在语义上就不可能**，
不是实现细节问题。要用 σ 必须整段重写 `unify_pm`（B3'），工作量大且风险高。

### 15.2 本轮收口内容

把 `update_cxt` 里的 σ 累积改为**直通**（`sub: self.sub.clone()`）：

- σ 不再随精化增长，`Cxt::sub` 恒为空（或由调用方显式设置）；
- `force` 的 `VSub` 分支与 `frcs` 变成**无调用者**的备用路径，不再可能被误触发；
- 消除了「只写不读的死字段」隐患——之前它一旦被接上读点就会复现栈溢出。

### 15.3 门禁（全部在 `target_b13` 的新鲜二进制上）

| 判据 | 结果 |
|---|---|
| `cargo build --release --bin typort` | build=0，binary 20:57:57（晚于源码 20:53:39） |
| examples 5/5 | **逐字节等于 B0 基线** |
| L13 lib | **625 passed** / 13 ignored |
| 链继承门禁 | 2 passed |

### 15.4 B 路线最终成果

| 提交 | 内容 | 价值 |
|---|---|---|
| `0efa4203` | B0 冻结 oracle + 五轮失败归因 | 建立了可复跑的验证基线 |
| `1142c607` | B1 `rename` 帧式化 | **净收益**：栈安全 + 红绿对照测试 |
| `f6ced3d1` | σ 链迭代 Drop | **净收益**：栈安全 + 红绿对照测试 |
| `630f6e18` | B2-1 `Subst` 链 + `Val::VSub` | 数据结构就位（备用，无调用者） |
| `168143ec` | B2-2 `frcs` + `force`/`v_app` 钩子 | 备用路径（无调用者） |
| `28c6f830` | B3-1 `Cxt` 携带 σ | 载体桥就位（本轮收口为直通） |

**三项净收益**：B1 的 rename 栈安全、σ 链 Drop 栈安全、以及一套可复跑的 L13 验证基线
（`target/b-l13/baseline/` 的 635 个测试名 + 5 份完整输出 + 新鲜度纪律）。

### 15.5 未达成的部分（诚实登记）

**σ 显式替换载体没有在 L13 上落地。** L13 仍用 `update_cxt`/`refresh` 的急切载体。
这与 2026-09 五轮移植的最终状态一致——B 路线证明这条路径需要整体重写（B3'），
不是渐进改造能做到的。

若将来要做 B3'，起点是本文档 §3/§4 的分步计划，且**必须**先做的是把 `unify_pm` 的
签名改成穿 `SpecSolve`（L12 形状），而不是在现有 `update_cxt` 外挂 σ。