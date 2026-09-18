# L09–L13 的 match 为什么慢：算法级诊断与重写代价（2026-09-17）

> 起因：`docs/bench-matrix-2026-09-17.md` 的 `match` 行显示 L10/L11/L12/L13 的
> 孪生**慢于**自己的参考版（0.3–0.8×），而 L07/L08 是 2–3× 快。本文把差距
> 定位到根因，并给出"照着 L07 改成逐臂下钻"的实际代价。

## 0.0 落地状态（2026-09-18 更新）

- **L11：已完成**（`6ae12a6`）——参考版 + 孪生同步重写；实测参考版 match 2.3×、
  孪生 8.5×（0.180 ms @k=11），孪生/参考从 0.3× 变为 ~3×。
- **L12：已完成**（`45330e6`）——参考版 4.8×、孪生 8.9×（0.172 ms @k=11）。
- **L10：已完成**（`4e97743`）——参考版 3.0×、孪生 5.1×（0.186 ms @k=11）。
- **L10：已完成**（`4e97743`）——参考版 3.0×（0.750→0.252 ms @k=11）、孪生
  5.1×（0.946→0.186 ms）；孪生/参考 0.8× → 1.35×。其余负载 0.80–1.03×。
- **L13 / L09：未做**。配方同 L11/L12（参考版 `pattern_match.rs` 与孪生
  `bump_spine_iter.rs` 同步替换 `compile`/`compile_aux*` 为逐臂 `compile` +
  `walk_pat`，以 `lXX_fast_parity` + lib 测试为闸门，再跑 bench 交错 A/B）。

### L13 特有的适配点（已勘明，可直接照做）

1. **构造子键是限定名**：`elaboration.rs:1345` 明确写 `EnumName.caseName`、
   **不设裸名别名**（L10–L12 是裸名）。因此 `walk_pat` 里取构造子类型**不要**
   手工拼 `{sum}.{ctor}`，改用树同款的 `infer_expr(Raw::Var(名))`——名字解析
   交给命名空间机制；
2. **参考版 `check_pm_final` 返回精化后的 `Cxt`**（`Result<(Rc<Tm>, Cxt)>`，
   内部 `check_pm` → `infer_expr_pm` + `insert` + `unify_pm`，`unify_pm` 走
   `cxt.update_cxt(...)` 改写），**不是 σ**——所以参考版逐臂实现里**不要**
   调 `subst_cxt`，直接把返回的 Cxt 用作臂上下文；孪生侧仍是 σ（`SubstV`）
   + `subst_cxt`（与 L10–L12 相同）；
3. 参考版 `check<const CANONICAL: bool>`、`Error(span, vec![])`、
   `Span<SmolStr>` + `Either::Icit`（同 L12）；`closure_apply(&self, decl, closure, u)`
   带 `decl` 参（L11 也是）、`Cxt::bind(Span<SmolStr>, Rc<Tm>, Rc<Val>)`；
4. 规模的量级：参考版 `compile_aux` 985 行、孪生 `compile_aux_inner` 608 行
   （L11/L12 是 400–450），另有 `make_implicit_name`/`FilterResult`/`ArmEntry`/
   `is_impl`/`moduletree` 等 L13 专有件——移植时只需覆盖 `compile`/`walk` 这条
   路径，那些都是决策树内部件，可随 `compile_aux*` 一并删除。
5. **L09**：其孪生本就比参考版快 2.3×（`match`），优先级最低；适配点预计介于
   L10（env 口径机器、层级化全局表）与 L11（String 键）之间。

## 0. 结论

1. **根因是算法选择，不是实现细节**：L09–L13 的参考版与孪生都用**决策树矩阵**
   编译 match，L07/L08 用**逐臂下钻**。两者对同一份源（各层 `match_src` 逐字节
   相同，已核）差 10–2363×，本仓 `docs/pmab-per-arm-vs-decision-tree.md` 早有
   受控实验。
2. **差距在本负载上约 20×**，且**全部在编译期**（L11 孪生实测，`match` k=9）：
   `elab` 2.35 ms / `quote` 0.00 ms；def 内 `check` 占 100%；`check` 内
   `compile` 占 100%；`compile` 内 **360 次决策树节点访问**（每 def ≈30 次，
   而 L07 逐臂只走 2 条臂），其中 `filter_accessible_constrs` 占 34%
   （60 次调用/单次 run），其余是逐节点开销（quote / bind_name / clone_cxt /
   叶上体检查）。meta 表在探测期是空的（`probe_entries=0`），**不是** meta
   克隆的问题。
3. **不能只改孪生**：`lXX_fast_parity` 比对的是**Err 判定与错误文案**，而
   L09–L13 的 match 诊断由决策树产出（见 §2），只换孪生会立刻红。要动就得
   **参考版 + 孪生同步**，5 层共 10 份实现。
4. **规模**：每层要重写的量约 **1000–1800 行**（参考版 `compile_aux` 403–985 行
   + 孪生 `compile_aux_inner` 361–608 行），替换为 L07 那套约 440 行的逐臂实现
   **外加**诊断重建。5 层合计 ≈5000–8000 行，且要逐层重建诊断语义。
5. **只做常数优化拿不到多少**：把 `filter_accessible_constrs` 记忆化最多省下
   那 34% 的一部分（整层 ~1.25×），与换算法的 20× 不是一个量级。

## 1. 测量链（L11 孪生，`match`，k=9，`--only fast_ss`）

| 层 | 占比 | 手段 |
|---|---|---|
| `bench_check_nf` 全程 | `elab` 2.35 ms / `quote` 0.000 ms | `Instant` 包 `elab_all` 与 `quote` |
| `elab_all` 逐 decl | 每个 `def f_i` ≈0.13 ms，`two`/`println` 各 ≈0.001 ms | 逐 decl 计时 |
| `def` 内部 | `fake_bind`/`trait`/`nometas`/`eval`/`reg` 各 0.000；**`check` 0.128 ms** | 逐阶段计时 |
| `check` 的 Match 臂 | `infer` 0.000 / `evalscrut` 0.000 / **`compile` 0.126 ms** | 逐阶段计时 |
| `compile` 内部 | `compile_aux_inner` **360 次/run**（30 次/def）；`filter_accessible_constrs` 60 次/run、**0.80 ms（占 elab 34%）** | 计数器 + 计时 |

对照：L07 的孪生对同一份源同一负载是 **0.072 ms**（k=11）——同源、同语义、
不同算法。L07 逐臂实现对每个 def 只走 2 条臂：绑臂槽 → 解索引方程 → 检查体。

## 2. 为什么这不是"换个函数"：诊断由决策树产出

L09–L13 的 match 诊断有两类，都由决策树的遍历记账给出：

- `Warning::Unmatched(Pattern)`：不可达构造子的**路径感知**填充模式——由
  `fill_context` 把构造子名填回它在外层模式里的位置，再用
  `Pattern::Con(constr, vec![Pattern::Any(empty_span(()), Expl); 999], icit)`
  补通配。**嵌套**不完整（如 `Vec` 上只覆盖了部分内层形态）也能报出路径。
- `Warning::Unreachable(Raw)`：决策树**从未到达**的臂（含被前面臂遮蔽/重叠的
  臂，不只是 catch-all 之后的）。

L07 的逐臂实现只有更弱的一套：顶层覆盖检查（`probe_accessible` + `covers`）
与"catch-all 之后跳过"。也就是说，**照着 L07 重构 = 拿掉/弱化这些层的
match 诊断**，除非另行重建一套等价分析——而"某臂是否被前面臂覆盖"正是决策树
本来就免费给出的东西（usefulness 检查）。

## 3. 代价与路线（建议）

| 层 | 参考版待替换 | 孪生待替换 | 备注 |
|---|---|---|---|
| L09 | `compile_aux` 403 行 | `compile_aux_inner` 361 行 | 宇宙/`U` 层 |
| L10 | 423 行 | 435 行 | trait 包装、`check_pm_final` |
| L11 | 431 行 | 448 行 | 宏展开交互 |
| L12 | 423 行 | 438 行 | canonical/宏 |
| L13 | **985 行** | **608 行** | 命名空间、`moduletree`、额外守卫 |

替换目标是 L07 的 ~440 行逐臂实现（`compile` 106 + `walk_con` 292 + `walk` 33 +
`probe_accessible` 71 + `unify_indices` 41），按各层机器 API 适配
（L09+ 的 `Machine` 是 Cxt 形参、`SpecSolve` 无 `solvable` 字段、名字表是
持久化 `Rc<Names>` 而非轨迹）。**另需**：为 `Unmatched`/`Unreachable` 重建
路径感知覆盖分析，或者改语义并同步 10 份实现的测试口径。

建议顺序（每层一个 commit，参考版+孪生同 commit，以 `lXX_fast_parity` +
`lXX_blackbox*` 为闸门）：

1. **L11**（差距最大、1.5 ms，且孪生里已带 `L09_TRACE` 调试口便于对照）；
2. L12、L10（同族，改一份基本可复制）；
3. L13（985 行的 `compile_aux`，命名空间语义最复杂）；
4. L09（孪生目前仍比参考版快 2.3×，优先级最低）。

预计收益（`match` 一族）：孪生 1.2–1.5 ms → 0.06–0.08 ms（~20×），相对参考版从
0.3× 变成 ~8×；对**通配/多列**的真实源收益更大（pmab 文档：最高 14807×）。

## 4. 本轮做过但已撤回的改动

为定位热点，本轮在 `src/L11_macro/bump_spine_iter.rs` 里临时加过
`L11_PHASE` 门控的逐阶段计时/计数器（`elab`/`quote`/`def` 六段/`match` 三段/
`filter_accessible`/节点数/`run_pure_probe`）。**全部已撤回**，该文件与
HEAD 逐字节一致（`git status` 干净、`cargo build` 通过），本文的数字即来自
那轮探针。
