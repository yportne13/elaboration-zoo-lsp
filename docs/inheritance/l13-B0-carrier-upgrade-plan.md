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

## 16 B 路线收口总结（2026-11-25）

### 16.1 目标达成情况

用户指令「L13 的话先做 B 吧」= 载体升级（把 L12 的 σ 显式替换移植进 L13）。

**达成部分（可验证的净收益）**：

| 项 | 提交 | 证据 |
|---|---|---|
| B1：`rename` 的 Sum/SumCase/Obj 改帧式收集器 | `1142c607` | `deep_chain_tests` 3 例；剥掉帧式实现即栈溢出 |
| σ 链迭代 Drop | `f6ced3d1` | `deep_subst_chain_drop` 10 万深链默认栈通过；剥掉 impl 即溢出 |
| L13 行为 oracle（examples + 测试名） | `8cbf0cc0` | `l13_oracle_check.ps1` PASS |
| σ 数据结构与 `frcs`（备用，无调用者） | `630f6e18` `168143ec` | `cargo check` 0 error，未被触发 |

**未达成部分**：σ 未成为 L13 的精化载体，L13 仍用 `update_cxt`/`refresh`。

### 16.2 为什么未达成（三轮实验的收敛结论）

| 实验 | 结果 | 说明 |
|---|---|---|
| 判定换源（`already_refined` 查 σ） | 栈溢出 | σ 说已精化但 env 槽是 self-reference，取到 `Rigid(x)` 自身 |
| 判定+取值换源+原始值存储 | 栈溢出 | 同上 |
| 上述 + 自引用守卫 | 不溢出，但 prelude 语义错 | `can't unify Fin(t+1) vs Fin(_n1)` |

第三条是决定性的：**σ 即时生效、env 槽等 `refresh` 才生效**，两种载体的传播时序不可并存。
这不是实现细节，是语义冲突——路线 2（双载体并行）不可行。

### 16.3 与历史的对照

2026-09 的五轮 σ 移植失败（`docs/wip/`）与本轮的三次失败**根因相同**，但本轮把两件事分离清楚了：

- 当年归因为「prelude 21s / 深链栈溢出 / GADT 覆盖误报」三件事混在一起；
- 本轮证明：prelude 21s 是工程欠债（LSP 表总闸，已修）；深链栈溢出有两个独立成因（`rename` 递归 + σ 链 Drop 递归，均已修）；**只剩 GADT 精化时序**是 σ 本身的语义障碍。

### 16.4 现状

| 判据 | 结果 |
|---|---|
| `l13_oracle_check.ps1` | PASS（binary 新鲜、examples 5/5、638 测试名一致） |
| L13 lib | **625 passed** / 13 ignored |
| `chain_inheritance` | 2 passed |
| `l13_inherited_from_l12` | 22 passed |
| 跨层（gadt 265 / prim 258 / known_diff 3） | 全绿 |

### 16.5 若要做 B3'（需新授权）

起点：本文件 §4/§15 的计划。必须的第一步是**改 `unify_pm` 签名穿 `SpecSolve`**（L12 形状），
而不是在 `update_cxt` 外挂 σ。涉及 10 个调用点 + 删除 `refresh` 143 行，属生产内核级改动。

## 17 B3' 实验记录（2026-11-26）

### 17.1 五次尝试的收敛过程

| 步 | 动作 | 结果 |
|---|---|---|
| 1-5 | 就位 SpecSolve / occurs 守卫 / subst_cxt / unify_pm 穿 spec / bind_slots | 全部零行为变更，门禁绿 |
| 6a | check_pm 传真 SpecSolve（solvable 空） | **prelude 崩：occurs check** |
| 6b | 补 L12 门禁（solvable.contains + 非 Flex）后重试 | **prelude 崩：can't unify for unsolved meta** |

6a 的失败是**我的实现缺陷**（漏了门禁），已修。6b 的失败是**语义差异**。

### 17.2 6b 的失败信息

```
prelude elaboration failed: Error("can't unify for unsolved meta
  expected: Vec[U]\u{200b}(0)
      find: Vec[?1139 T U 0 f]\u{200b}(0)" @ 469,472)
```

右侧带 `?1139` 未解 meta 且带 pruning（`T U 0 f`）。也就是说：σ 把某个解提前推进后，
另一个位置的 meta 失去了本应被它约束的信息——两者不再能合一。

这正是 §16.2 描述的「时序差」的具体形态：env 槽的 `refresh` 会**同时**重锚定所有槽，
而 σ 只让**被解层级**的读点看到新值，其余位置的 meta/pruning 状态没有同步更新。

### 17.3 结论

**两件事都已确认**：

1. 我的实现缺陷（门禁缺失）—— 已修，且修复本身有价值（σ 分支现在只在正确条件下触发）；
2. 载体时序冲突 —— 真实存在，且不是补一个门禁能解决的。

6b 的报错位置（pruning 状态失配）指向 B3' 的真正难点：σ 路线要求**所有**读点都经 `frcs` 展开，
而 L13 里还有大量直接读 `cxt.env` 的路径（`refresh` 的后代、`update_by_cxt`、`locals` 轨迹）。
只换 `unify_pm` 的解累积方式、不换读点，就会出现这种「一半看到新值、一半没看到」的失配。

### 17.4 下一步

B3' 要做完整，必须同时换**读点**：把所有 `cxt.env.iter().nth(...)` 的直接读取改成经 σ 展开。
这是比 `unify_pm` 签名改造大得多的工程量（`env` 在 `cxt.rs`/`elaboration.rs` 里被读了几十处）。

## 18 B3' 突破：σ 通道首次在 L13 上全绿（2026-11-26）

### 18.1 根因：update_cxt 有两个职责，σ 只替代了一个

连续两轮失败（occurs check / unsolved meta）的最终根因是**职责遗漏**，不是语义冲突：

| `update_cxt` 的职责 | σ 分支是否覆盖 |
|---|---|
| 改写 env 槽 `env.change_n(x_prime, v)` | ✅ 由 `Subst::extend` 替代 |
| 清 pruning 在该槽的标记 `pruning.change_n(x_prime, |_| None)` | ❌ **漏了** |

遗漏的后果链条：

1. `fresh_meta`（mod.rs:3133）给每个新 meta 挂 `cxt.pruning`；
2. 槽位若仍带 pruning，该位置的实参在应用时被剪掉；
3. 于是「本该被解约束的位置」变成未解 meta —— 报 `Vec[U]0 vs Vec[?m T U 0 f]0`。

### 18.2 修法与验证

σ 分支在 `Subst::extend` 之后补一行清 pruning（`cxt.pruning.change_n(lvl2ix(cxt.lvl, *x).0, |_| None)`），
然后 check_pm 重新启用 σ（`solvable` 取自 `Cxt::bind_slots()`）。

**全部通过（历史上第一次）**：

| 套件 | 结果 |
|---|---|
| oracle（examples 逐字节 + 638 测试名） | **PASS**（binary 01:41:28 > src 01:37:58） |
| L13 lib | **625 passed** / 13 ignored |
| chain_inheritance | 2 passed |
| l13_inherited_from_l12 | 22 passed |
| gadt_refine_cross_layer | 265 passed |

### 18.3 这改变了什么

§16.3 曾说「σ 与 env 槽时序不可并存」。这句话**需要修正**：

- 不是「时序不可并存」，而是「**换载体时必须把所有职责一起换**」；
- 前几轮失败都是职责遗漏（门禁漏、pruning 漏），不是机制冲突；
- 修齐职责后，σ 与现有 env 槽载体在 check_pm 这一入口上**可以共存**（σ 累积、env 槽由 update_cxt 保留）。

### 18.4 下一步（B3' 剩余部分）

当前状态：check_pm 走 σ（solvable = bind_slots），但 `check_pm_final` 仍传 None、仍返回 Cxt。
要把 B3' 的既定目标做完，还需：

1. `check_pm_final` 也启用 σ；
2. `unify_pm` 返回类型改为 `Result<(), Error>`（不再产生新 Cxt）；
3. `check_pm`/`check_pm_final` 返回 `(Tm, Rc<Subst>)`；
4. `pattern_match.rs:584` 改为 `cxt_walk.subst_cxt(&σ)`；
5. 最后删 `update_cxt`/`refresh` 的 env 槽改写。

## 19 `check_pm_final` 启用 σ 第一次尝试失败（2026-11-26）

### 19.1 改了什么

按 §18.4 第 1 步，把 `check_pm_final` 也切到 σ 通道（内部用 `subst_cxt` 桥接回 Cxt，保持调用方契约）：

```rust
let solvable = cxt.bind_slots();
let mut spec = SpecSolve { solvable: &solvable, acc: Rc::new(Subst::default()) };
let ok = self.unify_pm(&cxt, &ori, &tmv, Some(&mut spec), t_span).is_ok();
let new_cxt = if ok { cxt.clone().subst_cxt(&spec.acc) } else { cxt };
```

### 19.2 结果：prelude 崩

```
prelude elaboration failed: Error("can't unify for unsolved meta
  expected: Eq[Nat]\u{200b}(?260 t + 1 t, ?261 t + 1 t)
      find: Eq[Nat]\u{200b}(0 + t, t)" @ 2422,2437)
```

注意这与 §18.2 的修复**不是同一类问题**：

- 第 7 步（check_pm）失败时是 `Vec[U]0 vs Vec[?m T U 0 f]0` —— 修 pruning 后就好了；
- 本步是 `Eq[Nat](?260 t+1 t, ...) vs Eq[Nat](0 + t, t)` —— 两侧**都带未解 meta**，且形态是「应用了 t 的表达式 vs 未应用的 `0 + t`」。

### 19.3 为什么 check_pm 能过、check_pm_final 不能

两者的输入差异：

| | `check_pm` | `check_pm_final` |
|---|---|---|
| 方程 | `a`（期望类型） ≐ `inferred_type`（推断出的类型） | `ori`（构造子的返回类型） ≐ `tmv`（`eval(t_inferred)`） |
| 一侧的来源 | 都是类型层面的值 | **一侧是 eval 出来的项值** |
| 触发时机 | 臂体检查时 | 臂特化时（`pattern_match.rs:584`） |

`check_pm_final` 的 `tmv = eval(t_inferred)` 会把项里的变量**应用状态**带出来（`t + 1` 带 spine）。
σ 的 `acc` 在 solve 时会把解值原样存进去、`frcs` 在读点按 spine 展开。但 `ori` 这一侧是「未被 σ 包裹的」
构造子返回类型——两侧的 spine 状态在同一方程里不同步，就出现「一侧已应用 t、一侧还没应用」。

### 19.4 结论

§18.3 说「σ 与 env 槽可以共存」在 **check_pm 这一入口上成立**，在 `check_pm_final` 上**不成立**——
因为后者的方程一侧是 eval 出的项值，spine 状态与另一侧不匹配。

⇒ `check_pm_final` 的正确做法不是「也走 σ」，而是**保持 update_cxt**（它是急切载体，会 refresh 全槽、
把 spine 状态重锚定到一致）；或者按 L12 的完整做法：`pattern_match` 侧维护 `self.sub`（σ 链）、
`check_pm_final` 接收并以它为种子（L12 `pattern_match.rs:712-718` 就是这么做的）。

后者才是 B3' 的正解，但需要 `pattern_match` 的 `Compiler` 持有 σ 状态（L12 有 `sub: Rc<Subst>` 字段），
这是比改 `check_pm_final` 大一圈的改造。

## 20 第 6 轮：Compiler 加 `sub` 字段（B3' 第八步）

### 20.1 本轮做了什么

按 §19.4 的正解方向，给 `pattern_match::Compiler` 加 `sub: Rc<Subst>` 字段（L12 的 `Compiler` 就是这样持有 σ 的）。
纯增量：字段 + 默认值就位，**无写入者**，当前精化仍走 `Cxt` 的 env 槽。

验证：oracle PASS（binary 02:14:23 > src 02:10:54、examples 5/5、638 测试名一致）。

### 20.2 为什么这一步要单独做

§19.4 说 `check_pm_final` 的正解是「`pattern_match` 侧维护 σ、`check_pm_final` 接收并以它为种子」。
但直接做那一步需要同时改 4 处（`Compiler` 字段、走查累积、`check_pm_final` 签名、臂上下文桥接），
任何一处不对都会以同一种症状（spine 不同步）失败，无法归因。

先把字段就位、单独验证零回归，是把这个改造拆成可定位的小步——这是本轮系列里一贯的方法（B1/B2/B3' 前七步都是）。

### 20.3 剩余工作（B3' 目标 vs 现状）

| 目标项 | 现状 |
|---|---|
| `unify_pm` 穿 `SpecSolve` | ✅ 已就位（`f117cd7b` `8879324d`） |
| 每步递归入口按 acc 包两侧 | ✅ 已就位（`bb03431c`） |
| 解入 acc 前两级 occurs 守卫 | ✅ 已就位 + 门禁修正（`0129496a`） |
| pruning 清位（`update_cxt` 的第二职责） | ✅ 已修（`ef77fc97`） |
| `check_pm` 走 σ | ✅ 已启用且全绿 |
| **`check_pm_final` 走 σ** | ❌ 失败（spine 不同步），需 `Compiler::sub` 作种子 |
| **`unify_pm` 返回 `Result<(), Error>`** | ❌ 仍是 `Result<Cxt, Error>` |
| **两个入口返回 `Rc<Subst>`** | ❌ 仍返回 `Cxt` |
| **删除 `update_cxt`/`refresh` 的 env 槽改写** | ❌ 未动 |
| `Compiler::sub` 字段 | ✅ 刚就位（`b78cf996`，无写入者） |

### 20.4 关键认知（写给继续做的人）

`check_pm` 与 `check_pm_final` 的失败模式**不同构**，这是 B3' 最大的坑：

- `check_pm` 的方程两侧都是**类型层面的值**，σ 可以直接替代 env 槽；
- `check_pm_final` 的一侧（`tmv = eval(t_inferred)`）是**项值 eval 出来的**，带 spine（`t + 1`），
  而另一侧 `ori` 是未包裹的构造子返回类型——spine 状态不同源。

所以「统一改用 σ」这个方向本身对 `check_pm_final` 不成立，必须让 σ **在 `pattern_match` 里累积**
（L12 的 `self.sub`），使 `ori` 与 `tmv` 都处于同一 σ 之下再比较。

## 21 第 7 轮：`unify_indices` 穿 spec（B3' 第九步）

### 21.1 本轮做了什么

把 `check_pm` 那条 σ 通道往上游接一步：`unify_indices`（构造子可达性探测里的索引方程）
改成接收 `&mut SpecSolve<'a>`，调用点用 `probe_cxt.bind_slots()` 建可解集。

**零行为变更**：`acc` 仍是空链。原因见 §21.2。

### 21.2 一个必须记录的结构约束

`probe_accessible` 是**关联函数**（`fn probe_accessible(...)`，没有 `self`），
因此拿不到 `Compiler` 的 `sub`。而 L12 的对应函数是显式接收 `&sub` 的
（`pattern_match.rs:181`：`probe_accessible(infer, cxt, cxt.lvl, &head_sum, &ctor, &self.sub, &self.solvable)`）。

所以本轮只能把 `spec` 参数就位、`acc` 留空。要让探测期也看到 σ，需要把 `probe_accessible` 改成
方法（或显式传 `sub`）——这是后续步骤。

### 21.3 验证

| 项 | 结果 |
|---|---|
| oracle | PASS（binary 02:38:31 > src 02:34:52、examples 5/5、638 测试名） |
| L13 lib | **625 passed** / 13 ignored |
| chain_inheritance | 2 passed |
| l13_inherited_from_l12 | 22 passed |

### 21.4 B3' 剩余工作（更新）

| 项 | 现状 |
|---|---|
| `check_pm` 走 σ | ✅ 全绿 |
| `unify_indices` 穿 spec | ✅ 参数就位（acc 空） |
| `probe_accessible` 拿得到 σ | ❌ 关联函数，无 `self` |
| `check_pm_final` 走 σ | ❌ 需 `Compiler::sub` 作种子 |
| `Compiler::sub` 被写入 | ❌ 字段就位、无写入者 |
| `unify_pm` 返回 `()` | ❌ 仍是 `Cxt` |
| 两入口返回 `Rc<Subst>` | ❌ 仍是 `Cxt` |
| 删 `update_cxt`/`refresh` | ❌ 未动 |

## 22 第 8 轮：σ 穿进探测期（B3' 第十步）

### 22.1 解决 §21.2 的结构约束

`probe_accessible` / `ctor_accessible` 都是关联函数（无 `self`），拿不到 `Compiler::sub`。
本轮按 L12 的做法**显式传 `sub` 参数**（不改方法化，改动面最小）：

```rust
fn probe_accessible(infer, cxt, head_sum, ctor, sub: &Rc<Subst>) -> Walk
fn ctor_accessible(infer, cxt, typ, constrs, memo, i, sub: &Rc<Subst>) -> Walk
```

内部构造 `SpecSolve` 时 `acc` 从 `sub.clone()` 取（此前是空链）。两个 `ctor_accessible` 调用点补 `&self.sub`。

### 22.2 `Compiler::sub` 第一次被读

此前加字段时它是「只写不读的死字段」。现在它第一次被读取——但因为还没有写入者，
恒为空链，`Subst::lookup` 全不命中、`unify_pm` 的 σ 分支也不触发，**行为零变化**。

这一步的价值是**把「探测期的 σ 来源」接通**：下一轮给 `Compiler::sub` 装写入者时，
探测期立刻就能看到累积的 σ，无需再改签名。

### 22.3 验证

| 项 | 结果 |
|---|---|
| oracle | PASS（binary 02:53:59 > src 02:50:21、examples 5/5、638 测试名） |
| L13 lib | **625 passed** / 13 ignored |
| chain_inheritance | 2 passed |
| l13_inherited_from_l12 | 22 passed |

### 22.4 B3' 剩余工作（9 项 → 4 项）

| 项 | 现状 |
|---|---|
| `check_pm` 走 σ | ✅ 全绿 |
| `unify_pm` 穿 `SpecSolve` + acc 包裹 + 两级 occurs + pruning 清位 | ✅ 全部就位 |
| `unify_indices` 穿 spec | ✅ 就位 |
| `probe_accessible` / `ctor_accessible` 拿得到 σ | ✅ 显式传参（`145dc5a1`） |
| `Compiler::sub` 被写入 | ❌ 仍无写入者 |
| `check_pm_final` 走 σ | ❌ 需 `Compiler::sub` 作种子 |
| `unify_pm` 返回 `()` | ❌ 仍是 `Cxt` |
| 两入口返回 `Rc<Subst>` | ❌ 仍是 `Cxt` |
| 删 `update_cxt`/`refresh` | ❌ 未动 |

## 23 第 9 轮：`Compiler.sub` 写入路径的两次尝试与回退（2026-11-26）

### 23.1 尝试一：`probe_accessible` 返回 σ

目标：让探测期解出的 σ 回到 `Compiler`（`self.sub = spec.acc`），为 `check_pm_final` 提供种子。

改法：`probe_accessible` 返回 `(Walk, Rc<Subst>)`，调用方写回。

**放弃原因**：函数体内有 5 个返回点——1 个 early `return Walk::Matched`（无参数 Sum 短路）+
`break match res` 的 4 个臂。其中 4 个臂里的 `spec` 在 `break` 之后**不可见**（`break match` 表达式
的作用域不含臂外的局部变量），所以不能简单地给每个臂加 `spec.acc.clone()`；需要把 `spec` 提到
`break` 之前并改写成 `break (walk, spec.acc.clone())` 的形态。机械化改写的风险明显高于收益，已回退。

### 23.2 尝试二：RefCell 旁路

考虑用 `RefCell<Rc<Subst>>` 作为 out-parameter，避开返回类型改造。
**放弃原因**：`probe_accessible` 是关联函数、可能被多处并发语义调用（探测有 memo），
旁路会引入生命周期与借用面的不确定性；且它把「函数纯性」破坏了。未落地。

### 23.3 本轮实际落地

只有 `check_pm_final` 的**方程组约束注释**：

- 说明为什么这里必须保持 `update_cxt`（§19 的 spine 不同源），
- 说明 `solvable` 的域（`cxt.bind_slots()`）已经就位，等 σ 接入时不需要再造。

### 23.4 结论：`Compiler.sub` 的写入需要一个更结构化的改法

两次尝试都撞在同一个地方：**`probe_accessible` 是关联函数 + `break match` 的作用域**。
要走通，正确的做法是 L12 那样：`Compiler` 有 `walk_pat` 方法（`&mut self`），
σ 的读写都在方法内完成，不靠返回值搬运。L13 的 `walk_pat` 已经是方法（`&mut self`），
但它调用的 `probe_accessible`/`ctor_accessible` 还是关联函数——这是需要一并解决的。

⇒ 下一轮的正确方向是把 `probe_accessible` / `ctor_accessible` **也改成方法**（`&mut self`），
这样 σ 的读写都落在 `self.sub` 上，不需要返回值搬运、也不需要旁路。
这比本轮尝试的两种改法都更接近 L12 的形状。

## 24 第 10 轮：`probe_accessible` / `ctor_accessible` 方法化（B3' 第十一/十二步）

### 24.1 解决了 §23.4 的结构障碍

两个函数从关联函数改成 `&mut self` 方法，去掉显式 `sub` 参数——**σ 的读写直接落在 `self.sub` 上**。
这消除了上一轮两次尝试都撞上的两个障碍：

| 障碍 | 方法化之后 |
|---|---|
| 关联函数没有 `self` | 有 `self`，直接读 `self.sub` |
| `break match` 作用域不含臂外局部（无法把 `spec` 带出） | 不需要带出——写入走 `self.sub` |

改动：`fn probe_accessible(&mut self, ...)` / `fn ctor_accessible(&mut self, ...)`，
4 处调用点从 `Self::xxx(..., &self.sub)` 改成 `self.xxx(...)`。

### 24.2 探测仍是只读（L12 口径）

方法化之后 `probe_accessible` **可以**写回，但它**不应该**写回：

- L12 的 `probe_accessible` 是只读 `&sub`（探测边界丢弃 σ）；
- 探测的目的是判可达性，解出的精化是「假设」不是「事实」，写回会污染臂上下文；
- 所以本步只把它从「拿不到 σ」改成「能读 σ」，仍**不写回**。注释已订正，避免后人误以为它该写。

### 24.3 验证

| 项 | 结果 |
|---|---|
| oracle | PASS（binary 03:39:19 > src 03:35:40、examples 5/5、638 测试名） |
| L13 lib | **625 passed** / 13 ignored |
| chain_inheritance | 2 passed |
| l13_inherited_from_l12 | 22 passed |

### 24.4 B3' 剩余工作（4 项 → 3 项）

| 项 | 现状 |
|---|---|
| `probe_accessible` / `ctor_accessible` 拿得到 σ | ✅ **方法化后可直接读 `self.sub`** |
| `Compiler::sub` 被写入 | ❌ 仍无写入者（且按 §24.2，探测期不该写） |
| `check_pm_final` 走 σ | ❌ 需 `Compiler::sub` 作种子 |
| `unify_pm` 返回 `()` | ❌ 仍是 `Cxt` |
| 两入口返回 `Rc<Subst>` | ❌ 仍是 `Cxt` |
| 删 `update_cxt`/`refresh` | ❌ 未动 |

### 24.5 下一个真正的写入点

探测期不该写（§24.2），那 `Compiler::sub` 的**唯一合法写入点**是**臂特化成功之后**——
即 `pattern_match.rs:590` 的 `check_pm_final` 返回处。那正是 L12 的做法（`self.sub = spec.acc` 在
`unify_indices` 之后、臂体检查之前）。

所以要推进，必须先让 `check_pm_final` 能返回 σ——这又回到 §19 的 spine 不同源问题。
两者互相依赖：`check_pm_final` 需要 `Compiler.sub` 作种子，`Compiler.sub` 需要 `check_pm_final` 返回 σ。

**打破这个循环的办法**：先让 `check_pm_final` 返回 `(Tm, Cxt, Rc<Subst>)`（σ 从内部 `unify_pm` 的 `spec.acc` 取），
调用方写回 `self.sub`，但**暂不使用**这个 σ（臂上下文仍用 `Cxt`）。这样 σ 开始累积、口径可验证，
再观察它是否让探测期/后续方程的行为改变。

## 25 第 11 轮：`check_pm_final` 返回 σ 的尝试失败（2026-11-26）

### 25.1 做了什么（按 §24.5 的破法）

让 `check_pm_final` 返回 `(Rc<Tm>, Cxt, Rc<Subst>)`：内部用 `SpecSolve`（`solvable = cxt.bind_slots()`）
跑 `unify_pm`，把 `spec.acc` 作为 σ 返回。调用方（`pattern_match.rs:605`）收下 σ 并写回 `self.sub`。

设计意图：σ 开始累积但**不被消费**（臂上下文仍用返回的 `Cxt`），这样能验证 σ 链路是否健康而不触碰精化语义。

### 25.2 结果：prelude 崩

```
prelude elaboration failed: Error("can't unify
  expected: Eq[Nat](0 + a, a)
      find: Eq[Nat](0, 0)" @ 2380,2386)
```

### 25.3 为什么「不消费」也会改变行为

这是本轮最重要的观察：**写回 `self.sub` 本身就是一次消费**。

`probe_accessible` 现在能读 `self.sub`（第 10 轮方法化的结果）。一旦 `self.sub` 非空：

1. 可达性探测的 `unify_indices` 会带着这个 σ 去解方程；
2. 解方向、解出的值都受 σ 影响；
3. 探测结论（Matched / Unreachable）随之改变；
4. 覆盖检查与臂过滤都跟着变。

所以「只写不读」在 `self.sub` 上**做不到**——`probe_accessible` 已经在读它了。

### 25.4 结论

σ 的引入必须**一次性完成**：`Compiler::sub` 一旦开始累积，探测期、臂上下文、
`check_pm_final` 的方程比较就都处于同一个 σ 之下，不能再分段启用。

这与 §24.5 的计划相反——我原本想「先让 σ 累积、暂不消费」，但消费点（探测期）已经在第 10 轮接好了。

⇒ 正确的路径只有一条：把 σ 全面接管（探测期 + 臂上下文 + check_pm_final），
也就是 B3' 剩下的三项一起做，不能再分步。

## 26 B3' 规模实测（2026-11-26，第 12 轮）

上一轮说「先统计规模再做决定」。数据如下。

### 26.1 env / pruning / locals 的依赖点：105 处，但绝大多数无关载体

| 文件 | 依赖点数 |
|---|---:|
| `elaboration.rs` | 64 |
| `cxt.rs` | 30 |
| `mod.rs` | 11 |

按**角色**分类（以 `elaboration.rs` 的 64 处为例）：

| 角色 | 数量 | 换载体后是否需要改 |
|---|---:|---|
| 把 `&cxt.env` 当求值环境传给 `eval` / `nf` | **57** | **否**——这些只是「在哪套环境里求值」，σ 不改变环境结构 |
| 按槽取值（`env.iter().nth(...)`） | 6 | **是**——正是需要改成经 σ 展开的点 |
| pruning 语义 | 1 | 是 |
| locals 语义 | 0 | — |

**结论**：真正需要改的是 **7 处**（在 `elaboration.rs` 内），不是 64 处。
其余 57 处传 `&cxt.env` 的地方，σ 路线下照样传 env——`subst_cxt` 产出的 `Cxt` 里 env 已经包了 `VSub`，
`eval` 读到 `VSub` 会经 `force` 展开，与 L12 的语义一致。

### 26.2 其余三个数字

| 项 | 数量 | 说明 |
|---|---:|---|
| `update_cxt` 调用点 | **7** | 全部在 `elaboration.rs` 的 `unify_pm` 与 `update_by_cxt` 内部 |
| `refresh` / `fresh_val` 调用 | 6 | 全在 `cxt.rs` 内（`update_cxt` + `refresh` 自身递归） |
| 相关函数体量 | `update_cxt` 约 45 行、`refresh` 约 25 行、`update_by_cxt` 约 36 行 | 合计约 106 行 |

### 26.3 与 L12 的对照

L12 的同名职责：

- `Subst` 链 + `lookup_hit` + `frcs` —— 已在 L13 就位（B2 的两个提交）；
- `SpecSolve { solvable, acc }` —— 已就位；
- `Cxt::subst_cxt` —— 已就位；
- `Cxt::bind_slots` —— 已就位；
- `probe_accessible` / `ctor_accessible` 能读写 σ —— 已就位（第 10 轮方法化）。

**缺的只有**：

1. `Compiler::sub` 的写入（`pattern_match.rs:605` 的 `check_pm_final` 返回处）；
2. `check_pm_final` 的方程两侧处于同一 σ 之下（§19 的 spine 不同源问题）；
3. 删 `update_cxt` / `refresh` / `update_by_cxt`（约 106 行）；
4. 改那 7 处按槽取值的读取点。

### 26.4 修正上一轮的判断

上一轮我写「这不是按 L12 形状改签名，而是把 `cxt.rs` 和 `elaboration.rs` 的精化面整体重写」。
**数据不支持这个说法**：真正要改的是 7 处读取点 + 106 行旧载体删除 + 两个入口的返回值，
其余 57 处 `&cxt.env` 的用法在 σ 路线下原样保留。

⇒ B3' 的剩余工作量是**中等规模**（不是重写级），难点集中在 §19 的 spine 不同源问题——
那是唯一一处需要新的语义设计（让 `ori` 与 `tmv` 处于同一 σ 下比较）的地方。

## 27 第 13 轮：方法论问题——当前 oracle 无法判定 σ 的对错

### 27.1 两次尝试与结果

按 §26.4 的计划，在 `check_pm_final` 里用**局部 σ**（不写回 `Compiler::sub`）让 `ori` 与 `tmv` 处于同一替换下比较：

| 尝试 | 结果 |
|---|---|
| 局部 σ，`unify_pm(Some(&mut spec))` | prelude 崩：`Eq[Nat](0 + a, a)` vs `Eq[Nat](0, 0)` |
| 加上 `c.subst_cxt(&spec.acc)` 桥接 | prelude 仍崩，但换了个位置：`Vec[Nat](?30054 ...)` vs `Vec[Nat](w)` |

两次都回退。第二次的报错变化说明 `subst_cxt` 桥接起了作用（臂上下文拿到了被 σ 包裹的 env），但仍有别处不匹配。

### 27.2 发现的方法论问题（本轮最重要的结论）

**当前的 oracle 冻结的是「L13 现在的行为」。如果 σ 是正确的但确实改变了行为，oracle 永远会红。**

也就是说，用 `l13_oracle_check.ps1` 这个工具，**无法区分**这两种情况：

1. σ 实现错了（该红）；
2. σ 实现对了，但 L13 的既有行为确实应当改变（不该按红处理）。

前 12 轮我一直用同一个 oracle 判定，所以在「L13 的既有行为是否就是正确基准」这个问题上从未被检验。

### 27.3 现有的可用对照物

| 资产 | 数量/内容 | 能否判定 σ 的正确性 |
|---|---|---|
| `docs/wip/*.patch`（σ 五轮补丁） | 5 个，对当前 HEAD 全部 CONFLICTS | 否（无法应用），但可作语义参考 |
| `tools/bench_corpus/common` | 6 个 L07 风格文件 | **部分**——这些是 L07–L12 共有语料，判定应当一致 |
| `tools/bench_corpus/L07..L12` | 27/26/34/22/25/30 个 | **可以**——用 L12 的 σ 实现跑同一批语料，比对判定 |
| `tests/l07_l13_known_diff.rs::core_programs_keep_the_same_verdict` | 8 个纯共有 CORE 程序 | **可以**——已登记「判定必须一致」 |

### 27.4 结论与下一步

要继续做 B3'，必须先建立**独立于 L13 当前行为的判据**。可行做法：

1. 用 L12 的实现（σ 路线，已全绿）跑 `tools/bench_corpus/L07..L12` 的语料，记录判定（PASS/FAIL）；
2. 用 L13 的 σ 版本跑同一批，比对**判定**（不是输出文本——L07↔L13 的渲染本就故意不同）；
3. 判定一致的部分是硬 oracle，不一致的部分逐个分析。

这比当前的「examples 输出逐字节」宽松，但**能区分对错**——因为基准是 L12 的 σ 而非 L13 的 env 槽。

在这条判据建立之前，任何 σ 相关的改动都无法被可靠评价。

## 28 第 14 轮：建立独立判据（L12 vs L13 判定对照）

### 28.1 问题

§27.2 记录的：`l13_oracle_check.ps1` 冻结「L13 现在的行为」，无法区分「σ 错了」与「σ 对了但行为该变」。

### 28.2 解法：用 L12（σ 路线）作基准，比对**判定**而非文本

新增 `tests/l12_l13_verdict_parity.rs`：

- 语料 170 个（`tools/bench_corpus/{common,L07..L12}`）；
- 每个语料分别喂 `L12_canonical::run` 与 `L13_namespace::run`，只比 `is_ok()`；
- 深链语料在 64 MB 栈线程上跑（默认 2 MB 会 `STATUS_STACK_OVERFLOW`，已实测）；
- 容差：差异 ≤ 15%。

### 28.3 实测结果

```
corpus verdict agreement: 147/170 (23 differences)
```

差异 13.5%，落在容差内。分布有结构：

| 层 | 方向 | 例数 |
|---|---|---:|
| L07 / L08 / L09 / L10 | L12=true, L13=false（L13 更严） | 2 / 1 / 1 / 1 |
| L11 | L12=false, L13=true（L13 更宽松） | 15 |
| L12 | 混合 | 3 |

### 28.4 这个判据的价值与局限

**价值**：σ 相关改动现在有了不被「L13 当前行为」束缚的评价面——若某改动让 L13 向 L12 靠拢（差异数下降），
即使 `examples` 输出变了，也能判断它是改进而非退步。

**局限**：

1. 只比判定、不比类型精度——判 Ok 不代表类型相同；
2. L11 那 15 例的差异方向是「L13 更宽松」，若 B3' 让它们变成一致（L13 变严），差异数会下降，
   但这未必是「更正确」——需要逐个分析这些语料在 L12 上为何失败；
3. 容差不等于正确性证明，只是「差异有界」的回归护栏。

### 28.5 下一步

B3' 的改动现在可以这样评价：

1. `l12_l13_verdict_parity` 差异数（目标：下降或持平）；
2. `l13_oracle_check.ps1`（目标：examples 输出——若 σ 正确但改变了行为，这里会红，需人工确认是有意的）；
3. L13 lib 全绿（不能退）。

三者一致时才可接受。第 1 项是新增的、也是唯一能判定「σ 方向是否正确」的那一项。

## 29 第 15 轮：用独立判据评价 σ 实验（第一次有条件可判的实验）

### 29.1 实验与读数

把 `check_pm_final` 的方程改到局部 σ + `subst_cxt` 桥接，然后用新判据评价：

| 判据 | 基线 | 实验 |
|---|---|---|
| `l12_l13_verdict_parity` 差异数 | **23 / 170** | **24 / 170** |
| 移除的差异 | — | **0** |
| 新增的差异 | — | **1**（`L07 ex_let_match_forms.typort`） |
| `l13_oracle_check.ps1` | PASS | FAIL（5/5 examples 漂移） |

### 29.2 读数说明什么

**方向错了**，而且是双重的：

1. 判定层面：没有任何一个与 L12 的差异被消除（0 removed），反而多了 1 个；
2. 输出层面：5 个 examples 全部漂移。

这与前 13 轮的区别在于——**这次是有判据支撑的结论**，不是「oracle 红了所以回退」。
若 σ 的方向正确，即使 examples 输出变化，也应该看到与 L12 的判定差异减少；实测是增加。

### 29.3 为什么 σ 在这个位置必然失败（新的技术理解）

`check_pm_final` 的方程是 `ori ≐ tmv`，其中 `tmv = eval(&cxt.decl, &cxt.env, t_inferred)`。

关键点：`tmv` 是用**臂上下文的 env** 求值出来的。那个 env 已经是「走查 + check_pm」精化的结果。
若再套一层 σ（`subst_cxt`），等于把精化施加两次：

- 第一次：`check_pm` 内部 `update_cxt` 把解写进 env 槽（env 已精化）；
- 第二次：`subst_cxt(&spec.acc)` 再包一层 `VSub`。

两层的交互产生 `Vec[Nat](?30054 ...)` 那样带未解 meta 的形态——不是 σ 本身错，而是**同一次精化被施加了两遍**。

### 29.4 结论

`check_pm_final` 必须**只用一个载体**：要么 env 槽（现状），要么 σ（需要先让 `check_pm` 也改用 σ、
从臂上下文起就只有一个载体）。**混用（env 精化 + σ 包裹）在语义上不成立**——这与 §18.3 的成果并不矛盾：
§18.3 说的是「σ 与 env 槽可以共存」，但共存的前提是**同一方程内只有一种载体生效**；
§29.3 的发现是「同一方程内两种载体都被施加」时必然错。

⇒ B3' 的正确顺序不是「先改 check_pm_final」，而是**先把 check_pm 的 env 槽精化也换成 σ**
（即 `check_pm` 不再返回被 `update_cxt` 修改过的 Cxt，而是返回 σ，由调用方 `subst_cxt` 生成臂上下文）。
这样 `check_pm_final` 面对的就是「已被 σ 精化过的 env」，再套 σ 是幂等的。

## 30 第 16 轮：核实一个决定性事实——L12 没有 `update_cxt`

### 30.1 核实结果

```
L12_canonical/cxt.rs 里 fn update_cxt 的数量：0
L13_namespace 里 check_pm 的调用点：3（elaboration.rs:685 / 778 / 789）
```

**L12 根本没有 `update_cxt`。** 它的臂上下文全部由 `subst_cxt(&self.sub)` 生成，
`sub` 在 `pattern_match` 里累积（`self.sub = spec.acc`）。L13 的 `update_cxt` 是 L13 独立演进中
新增的急切载体（L09–L13 的 `refresh` 血统），在 L12 里不存在对应物。

### 30.2 这意味着什么

§29.3 的结论「先把 check_pm 的 env 槽精化换成 σ」在 L13 里不是一个「局部替换」：

`check_pm` 返回的 `Cxt` 被三处消费：

| 调用点 | 消费方式 |
|---|---|
| `elaboration.rs:685` | `check_pm_final` 的臂特化 |
| `elaboration.rs:778` | `infer_expr_pm` 的 App 递归（取 `cxt` 继续推断） |
| `elaboration.rs:789` | `check_pm` 自身定义 |

第 2 处是**递归链**：`check_pm → infer_expr_pm → (App) → check_pm → …`。要让 `check_pm` 只返回 σ，
这条链上的每一环都得改成传 σ——也就是把 `infer_expr_pm` 的整条签名改掉。

### 30.3 与目标定义的差距（诚实登记）

B3' 的目标（本次 goal 的 objective）写的是：

> `unify_pm` 穿 `SpecSolve`、每步递归入口按 acc 包两侧、解入 acc 前两级 occurs、
> `check_pm/check_pm_final` 返回 `Rc<Subst>`、删除 `update_cxt/refresh` 的 env 槽改写

已完成的部分：

| 项 | 状态 |
|---|---|
| `unify_pm` 穿 `SpecSolve` | ✅ |
| 递归入口按 acc 包两侧 | ✅ |
| 两级 occurs 守卫 | ✅ |
| `Subst` / `frcs` / `subst_cxt` / `bind_slots` | ✅ |
| `probe_accessible` / `ctor_accessible` 读 σ | ✅ |
| **`check_pm`/`check_pm_final` 返回 `Rc<Subst>`** | ❌ 三轮尝试失败 |
| **删除 `update_cxt`/`refresh`** | ❌ 未动 |

后两项互相锁死：要删 `update_cxt` 必须先让所有消费者接受 σ；要返回 σ 又必须先让所有消费者不再需要 `Cxt`。
这是一个**同时生效**的改动，不能分步——而它的影响面是 `infer_expr_pm` 的整条递归链加 `pattern_match` 的臂循环。

### 30.4 本轮的技术结论

前 15 轮我一直在「分步启用 σ」，而 §30.2 说明这个方向在 L13 里**结构性不可分步**：
`check_pm` 的返回类型是递归链的公共接口，改它等于改整条链。

这不是「再试一次就能成」的问题，是「要么一次改完整条链、要么不动」的问题。
一次改完整条链意味着：`infer_expr_pm` / `check_pm` / `check_pm_final` / `pattern_match::compile` 四处签名同时变，
期间无法用「小步验证」降低风险——正是我在前 15 轮极力避免的那种改动。

## 31 第 17 轮：`check_pm` 返回 σ 的两种消费方式都失败（2026-11-26）

### 31.1 本轮的两个实验

让 `check_pm` 返回 `(Tm, Cxt, Rc<Subst>)`（内部 `subst_cxt` 精化后，σ 一并返回），
`check_pm_final` 用这个 σ 让 `ori` 与 `tmv` 同帧。消费方式试了两种：

| 方式 | 做法 | verdict 差异 | examples |
|---|---|---:|---|
| A. 预先包 `ori` | `ori_w = force(wrap_sub(&sigma_in, ori))`，`spec.acc = sigma_in` | 24（+1，-0） | 5/5 漂移 |
| B. 只作 acc 种子 | `spec.acc = sigma_in`，不预包 `ori` | **24（+1，-0）** | 5/5 漂移 |

两种方式的差异集**完全相同**（都多出 `L07 ex_let_match_forms.typort`，都没消除任何既有差异），
说明 `wrap_sub` 在 `unify_pm` 入口的重复包裹是幂等的——它们实质是同一个实验。

### 31.2 关键读数

**0 消除、+1 新增。** 这是第二次用同一判据得到「方向错」的结论（第一次见 §29）。

两次实验的共同点：都是让 `check_pm_final` 的方程**带上 σ 精化**后比较。
两次的失败形态也相同（`Vec[Nat](?30054 ... )` vs `Vec[Nat](w)`）。

### 31.3 新认识：`tmv` 的 spine 不是问题，`?30054` 的来源才是

报错里的 `?30054` 是一个**未解 meta**。它出现在 `Vec[Nat]` 的索引位置——
说明某个本应被索引方程解掉的 meta 没有被解。

`check_pm_final` 的职责正是「构造子返回类型 ≐ 臂体推断类型」的**最终对齐**。
若它提前把 σ 加进来，会让索引位置的 meta 在**这里**就被解掉（而不是等到臂上下文里），
后续 `Vec[Nat] (w)` 那一侧就失去对应关系——`w` 是臂上下文里的变量，它的索引约束来自
臂上下文而不是这个方程。

⇒ σ 在这个方程上生效**过早**。这与 §18.2 的「pruning 清位」不是同一类问题，也不能靠补一行解决：
`check_pm_final` 的方程按其语义**就是**在臂上下文已经定型之后做最终确认，
它不该引入新的解。

### 31.4 结论

`check_pm_final` 保持 `update_cxt`（现状）**不是技术欠债，而是它的语义位置决定的**：
它是「确认」而非「求解」。σ 属于求解阶段（`check_pm`），不属于确认阶段。

这与 §29.4 的方向修正一致：不该动 `check_pm_final`，该动的是**`check_pm` 之后臂上下文如何生成**
——即 `pattern_match::compile` 里 `cxt_arm` 的构造方式。L12 在 `cxt_arm = cxt_arm.subst_cxt(&self.sub)`
之后直接用，而 L13 目前用 `check_pm_final` 返回的 Cxt。

## 32 第 18 轮：探针实测——`check_pm_final` 的方程**大部分**在无 σ 下进行

### 32.1 探针与结果

在 `check_pm_final` 里对 `cxt.sub` 计数（原子计数，因为每个语料跑在独立线程上——
首版用 `thread_local` 读出恒为 0，是探针本身的 bug，不是被测对象的行为）。

跑全部 170 个语料：

```
sigma probe over 170 files: empty=679 nonempty=70
```

**`check_pm_final` 的方程 90.7%（679/749）在 σ 为空时进行，只有 9.3% 带 σ。**

### 32.2 这个数字意味着什么

第 17 轮的结论是「σ 在 `check_pm_final` 上生效过早」。探针给出了**机制解释**：

- `check_pm_final` 的 `cxt` 来自 `check_pm`，而 `check_pm` 内部的 `unify_pm` 用的是
  `Rc::new(Subst::default())`（**每次新建空 σ**，见 `elaboration.rs:795`）；
- 所以 `cxt.sub` 几乎总是空——只有极少数路径（9.3%）走到带 σ 的情形；
- **`check_pm` 的 σ 根本没有流到 `check_pm_final`**：它在 `check_pm` 内部就被 `subst_cxt` 消费掉了，
  没返回给调用方。

这解释了第 17 轮两个实验为何都失败：我在 `check_pm_final` 里新建的 σ（或从别处取的 σ）
与 `check_pm` 内部实际用的 σ 不是同一个——`check_pm` 的解已经通过 `subst_cxt` 写进 `cxt` 的 env，
但那个 σ 本身已经丢了。

### 32.3 结论

要让 σ 在 `check_pm_final` 可用，**必须让 `check_pm` 把它的 σ 返回出来**（第 17 轮已做过这一步，
但那轮同时改了 `check_pm_final` 的方程，两个改动叠在一起无法归因）。

正确的做法是**分两步**：

1. 先让 `check_pm` 返回 σ，但 `check_pm_final` **完全不用它**（只看基线是否保持）；
2. 确认基线不变后，再单独实验「用 σ 包裹 `ori`」。

第 17 轮把这两步合并成一步，所以两个实验的差异无法区分——本轮探针提供了分开做的依据。

### 32.4 探针的清理

探针已移除（`git checkout` 恢复三个文件）。首版用 `thread_local` 是错的（worker 线程各自持有计数器，
主线程读出恒 0）；改原子后得到真实数字。这个坑值得记录：**跨线程的探针计数不能用 `thread_local`**，
而 `tests/` 里为了跑深链语料必然是每文件一个 worker 线程。

## 33 第 19 轮：分两步走的第一步成功——σ 可安全流出（2026-11-26）

### 33.1 本轮做法

按 §32.3 的方法，**只做第一步**：

```rust
pub fn check_pm(&mut self, cxt: &Cxt, t: Raw, a: Rc<Val>)
    -> Result<(Rc<Tm>, Cxt, Rc<Subst>), Error>
```

σ 取自内部 `SpecSolve` 的 `acc`（即 `check_pm` 自己解出的那个 σ）。两个调用点绑成 `_sigma`
但**完全不使用**。

### 33.2 结果：三项判据全部与基线一致

| 判据 | 基线 | 本步 |
|---|---|---|
| `verdict_parity` 差异数 | 23 / 170 | **23 / 170** |
| oracle examples | PASS | **PASS** |
| L13 lib | 625 passed | **625 passed** |
| chain_inheritance / inherited | 2 / 22 | **2 / 22** |

**这建立了「σ 可以安全从 `check_pm` 流出」这一事实**——第 17 轮把「返回 σ」与「消费 σ」合并，
所以无法判断失败是来自哪一半；本轮把两半分开，前半已证明无害。

### 33.3 与 §32.2 的关系

探针测出 90.7% 的 `check_pm_final` 方程在空 σ 下进行，因为 `check_pm` 用 `Rc::new(Subst::default())`
新建 σ 且不返回。现在 σ 已经流出了——但探针若再跑，**空/非空比例不会变**，
因为 `check_pm_final` 仍未消费它（`_sigma` 被丢弃）。

### 33.4 第二步的关键差异（下一轮）

第 17 轮在 `check_pm_final` 里**新建**一个 σ（`Rc::new(Subst::default())` 或从 `cxt.sub` 取），
而 `cxt.sub` 由 `check_pm` 的 `subst_cxt` 设置、几乎恒空。现在可以直接用 **`_sigma`（`check_pm` 真实解出的那个）**。

这是本质区别：

- 第 17 轮：`spec.acc` = 空 σ，与 `cxt` 里已施加的 σ 不同 → 两侧仍不同帧；
- 下一步：`spec.acc` = `check_pm` 真实 σ，与 `cxt` 里已施加的是**同一个** → 理论上幂等。

若下一步仍失败，则可确定结论是「σ 不该在这个方程上生效」（§31.4），而非实现问题。