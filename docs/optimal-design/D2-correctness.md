# D2 正确性与健壮性证据评估

> 范围：L01–L13 七层实现 + 孪生引擎 + Lean 形式化（M1/M3）。方法：**静态核对**（源码/测试/文档），
> 未运行任何 cargo/bench/Lean 命令（EXP-7 待 Lead 批准后执行，见 §6）。工作树 HEAD `8443586e`
> （2026-11-08），`src/ tests/ lean/` 无未提交改动。证据标注：`[码]` 源码核对 /`[文档]` 文档陈述
> （抽样回码）/`[历史实测]` 仓库既有实验数据 /`[推断]` 未执行 /`[未核实]` 需 EXP-7。
> 轴定位：FRAMEWORK §1 的 **A 正确性（权重 30%）**；结论同时服务 D1 设计轴与 D7 架构提案。

## 0. TL;DR

1. **当前实现是"教学检查器"级正确性，不是"证明助手/生产编译器"级**：with-K 无检查（L07 README §7.3）、
   浅 occurs 不传递且 VSub 嵌套仍有盲区（L07-RISKS R2 未修）、fuel/次数预算会翻转判定
   （L07 README §7.2）——三者是**接受集层面**的语义缺口，不是工程瑕疵。
2. **最强的证据不是"测试全绿"，而是三类机制各自的"构造性保证"**：σ 显式替换按构造消除
   `update_cxt` 的槽位错位 bug 族；三档 `UnifyKind` 把"算不完"从"矛盾"里分出（仅 L07）；
   构造子 WF 检查（`check_ctor_wf`）封死 phantom 构造子注入。但每条保证都只覆盖一个 bug 族。
3. **最严重的 3 个风险**：①**原生 Nat 的定义相等**（L12/L13 `Val::Nat`+primop+`vals_eq_ground` 宽放，
   是唯一"定义相等可被改宽"的面且未被形式化覆盖）；②**trait 求解的单向一阶匹配/多解非确定**
   （无 coherence/overlap 检查，L10–L12 effort 超限仍 panic）；③**层间加固不对称**
   （P1–P11 几乎只在 L07，L08 只镜像 P1/P2/P9，L09–L13 零回灌 ⇒ 同源码跨层判定分裂）。
4. **最值得推广的 2 个护栏**：①**三值判定 + "预算耗尽永不判 Absurd"**（L07 已落，Lean T3 机检）；
   ②**双 oracle+限定语料 oracle 的差分矩阵**（ref/twin parity + Lean M3 + 反例钉），并扩展到
   "同一语义的跨载体/跨表示影子比对"（§5 G2）。
5. **证据最大空白**：Lean 只形式化了**声明层类型论**（T1/T2/T3/T5 有定理），**算法健全性**
   （eval/unify/refine 与声明式关系一致）、精化精化（`trans`/`subst` 字面写法在标准规则下不可判型
   而实现接受）**均未证**（lean/README.md:158-207 诚实边界）；M3 oracle 仅 4 条 curated 语料。
   **"没测出 bug"不能当健全性证据**，本报告按此口径打分。

## 1. 我们实际拥有什么证据（分级清点）

| 证据层 | 内容 | 强度/覆盖 | 缺口 |
|---|---|---|---|
| 静态测试 | 各层 lib：L07 70 / L08 60 / L09 10 / L10 25 / L11 33 / L12 35 / L13 **612（6 ignored）**；parity 套件：27/35/29/21/19/15/15；黑盒：L07 49/53/47、L08 58/53；L13 LSP 11 套 | 正向 + 部分负向；L07 最厚（三轮黑盒 + 双 oracle + 限制钉） | **L09–L13 负向半区普遍薄**（test-catalog §3 P0-1）；L07/L08 parity 的 Err 只比判定不比正文（P0-2）；无外部 golden 快照 |
| 双引擎 parity | 判据 = Ok 逐字节 / Err 判定（L09–L13 正文经 span/`?N` 归一化）；`#[path]` 会把 lib 测试再跑一遍 | 抓"两实现分叉"最强；L13 修复过 1 个真 UAF | 不保证"两版同错"（L13 单行 enum 即两版同错假阴性）；不校文案（L07/L08） |
| Lean 形式化 M1 | 声明层：`HasType`/`Conv`/`Covers`；Engine 模块 T1（occurs 等级证书/精确刻画）、T2/T3（三档分类器健全性）、T5/P15（struct_eq pending）——全部 `lake build` 无 `sorry` | **规格级**证据，能证伪"某算法按该判据健全" | 不含 NBE/元变量/合一/fuel/精化/名字层；精化健全性（refinement）未证；无 subject reduction |
| Lean oracle M3 | `engine-oracle` 4 条 curated 语料（c1 occurs、c2 预算、空类型零臂、P15）与 L07 参考引擎判定比对；默认跳过（`LEAN_ORACLE=1`） | 第三方语义裁判 + 漂移探针，实测 4/4（lean/README.md:100-102） | 不解析 Typort、不做完整 unify；无生成式语料 |
| 历史实验 | pmab（逐臂 vs 决策树 10×→2363×/14807×）、bench 矩阵、perf-*、mem-* | 性能/定位证据，**不是正确性证据** | 多数采于 09-12/17/18/20，之后 L07 加固已改判定路径 |
| known-bug 文档 | L07-RISKS P1–P15、`docs/l13-*.md` 系列、`pattern-match-refinement-analysis.md`、`trait-system-analysis.md`、`test-catalog.md` | 作者诚实清单，信息量最大 | **部分已过期**（如 trait-system-analysis 的 4 条 bug 未标注修复状态；L13 lib 计数 341 vs 静态 612） |

> 结论：正确性证据呈"**金字塔尖薄、塔基厚而不齐**"——L07 有最厚的测试 + 4 条 Lean 机检判据，
> 但 `trans`/`subst` 这类真实 prelude 证明依赖的精化行为**在形式化里恰好不可判型**（lean/README.md:163-176），
> 即最关键的机制位于证据空白的正中央。

## 2. 设计轴对决：哪类写法在构造上消除 bug 族，哪类引入新风险

### A. 精化载体：`update_cxt`（L13 现役）vs `pm_defs`（旧 L07/L08）vs σ 显式替换（L07–L12）

| 候选 | 构造性保证 | 遗留/新增风险 | 证据 |
|---|---|---|---|
| `update_cxt` + `refresh` | 无 | 已捕获旧上下文的值（卡住 match 的 env、meta 解、闭包）过期；被精化变量从 pruning 剔除 → 解的 λ 深度与使用现场错位 → `add_assoc` 族失败 | [文档] L07 README §6 首行；L13 README §6.8（refresh 全槽重求值） |
| σ 显式替换 | **不改写上下文**：层级/env 槽/pruning/decl 一概不动，"解前构建、解后消费"的值在读点 `wrap_sub` + `frcs` 惰性展开；臂边界回滚 = Rc 指针 | ①**"每消费点必须显式包裹"的纪律**是新的 bug 源：L13 移植期出现过可达性探测用精化前头部类型 → GADT 覆盖回归（`ArmEntry` 携 σ + `acc` 起种子才修好，explicit-subst §4）②**σ 可见性边界**：decl 表缓存值与 meta 解不扫 σ（README §1.3，钉 `visibility_boundary_decl_value_is_not_refined`）→ 判定可能随求解顺序变化（P6）③σ-ABA / fuel=0 缓存洞在评审中出现过 | [码] `mod.rs:224-273,900-1022`；[文档] `docs/l08-l13-refactor-plan.md` §0-2、`explicit-subst-refactor-status.md` §4 |
| `pm_defs` 事实表（过渡态） | 惰性精化 + 回滚靠长度截断 | 读点 O(n) 反序扫；可解性经 Infer 全局旁路耦合；前身即旧 L07 的 bug 族 | [文档] L07 README §6 末三行 |

**判断**：σ 是三者中**最可论证**的载体（L08–L12 五层实测迁移、全仓 4013 用例 0 失败），但它是
"**把全局陈旧性 bug 换成局部遗漏包裹 bug**"，不是免费的正确性提升；L13 的 GADT 覆盖回归证明
"漏包一处"就是 S1 级。**最优不是纯 σ**：需在测试/调试态加"消费点不变量"检查（§5 G3），
或把 `wrap_sub` 变成类型上不可绕过的接口（D7 可设计）。

### B. 匹配编译：逐臂下钻（L07/L08）vs 决策树矩阵（L09–L13 旧、2026-09-18 后全仓统一逐臂）

- **接受集**：两者都能做特化方程判定；逐臂由"同一套方程"同时给出可达/覆盖/精化，且两段式嵌套覆盖
  已由评审钉恢复（nested coverage 两段式 commit 链，CONVENTIONS §2）[文档]。
- **诊断能力是真实回归**：决策树天然产出**路径感知**的 `Unmatched(Pattern)` filling 与
  `Unreachable`（含被前臂重叠遮蔽的臂）；逐臂只有顶层探测 + catch-all 后跳过。2026-09-18 的统一
  代价被三处文档诚实登记：L11 README §5「匹配编译器诊断弱于决策树」、L13 README §6.1
  「诊断三收窄」（**`Bool×Bool` 缺 `(true,false)` 组合仍被接受**，parity 钉 `(11)` 锁现状）。
- **反向 bug**：旧 L07 的矩阵实现曾"丢分支"（README §6 表），说明决策树在当前代码基的实现风险不低。
- **性能**（作为选型代价的参照，[历史实测]）：pmab 受控实验逐臂在臂数扫描 10×→2363×、列数
  9×→14807× 胜出，根因是通配造成的分支重数积 `2^m`。

**判断**：接受集等价（经两段式恢复），但**诊断完备性退步**是正确性"可观测面"的净损失；若重选，
应"逐臂执行 + 决策树仅用于诊断/usefulness 检查"的混合（D7 候选），而不是二选一。

### C. trait/typeclass：单向一阶匹配 + 表驱动 Prolog DFS

- 机制：`Synth` = `generator_stack` 逐实例 DFS × `consumer_stack` × `assertion_table`（顺带答案缓存）；
  head-indexed 实例查找 O(1)（L10 README §1.4；L13 `typeclass.rs:622` "First matching answer: depth-first"）[码/文档]。
- **正确性风险**：①**无 coherence/孤儿/重叠检查**（trait-system-analysis §总结：Coherence 0 实现、1 部分）；
  实例重叠时按 DFS 首个答案定生死 ⇒ **多解非确定**（换实例顺序可能换判定）；②outParam 与单向匹配
  交互；③`vals_eq_ground` **把 Flex 视为等于一切**、`val_match` 同策略（L12 README §6 明确"刻意语义"）
  ⇒ 转换关系在 trait 探针里被放宽，这是"为了求解而加的不健全近似"。
- **崩溃面**：L10/L11/L12 的 `effort > 1000` **直接 panic `"Too much effort :("`**
  （L10/typeclass.rs:223、L11:205、L12:315），L10 README §6.2 自认"是崩溃不是错误"；
  L13 已改为降级 `None`（`class_tests.rs:691 synth_effort_cap_returns_none_not_panic`）——
  **L13 更优但 L10–L12 未回灌**。
- **已证 bug 族**：trait 实例 Nat 参数未实例化（复现 A 已修、B 参数化模块仍存但显式 HDL004 警告、
  C `lvl2ix` 改 checked 后 panic 可诊断，`l13-typeclass-instance-nat-param-bug.md`）；
  悬空 meta → `lvl2ix` 下溢（`l13-known-bugs-2026-08.md` Bug 2，checker panic 缓解）。
- **判断**：这是继元变量之后**最大的未证正确性面**；"没有重叠检查"意味着语言层语义未定义，
  实验必须用实例顺序置换语料（§6）。

### D. 构造子良构性（WF）：`check_ctor_wf`

- 2026-09-18 起 L07–L13 全部有检查（[码] `L07/elaboration.rs:383-442`，孪生 `machine.rs:1554`；
  grep 各层 6–7 处/层；回归钉 `test_ctor_wf_external_ret` / `_param_specialized`、L11/L12 的
  `test_ctor_wf_*`）[码]。
- 保证的不变量：构造子类型实例化全部 Π 后，ret 的 WHNF 必须是**本 enum** 的 `Sum`；
  隐式参数位必须是 telescope 内 bare rigid（拒绝 `c -> Foo[Bool]` 特化）；拒绝 `c -> Nat`
  这类 phantom 注入（否则覆盖检查对封闭输入卡死）。
- 残余：未形式化进 Lean 的 `HasType`（Lean 只在声明层保留 ctorType 形状）；实现只查 ret 形状，
  不查"构造子 tele 是否完全 WF 于 enum 参数"以外的语义（由通用 check 保证）[推断]。
- **判断**：小而高价值的护栏，所有层一致；应保留并加"phantom 注入"属性测试（§5 G4）。

### E. with-K 定位（无 K 检查）

- L07 README §7.3/L10 §6.2/L11:293 都声明 with-K、无 without-K 条件检查；全仓 grep 无 K 检查实现。
- Lean 形式化的 `matchE` 是**标准规则**（显式 motive + λ telescope 臂），而实现的精化接受
  `trans`/`subst` 的字面写法；lean/README.md:163-176 明说"本形式化**不覆盖** trans/subst 的字面写法"
  ——即**实现比已形式化的理论严格更强**，这个"更强"没有 soundness 证明。
- **判断**：定位必须写成"教学检查器，不是证明助手"（README 已做）；若要当证明助手，需按
  "Pattern Matching Without K" 的"精化不触碰其它假设"条件补检查——这是理论级工作，不是补丁。

### F. fuel / 次数预算 / 静默降级（判定可信度）

| 机制 | 现状 | 失效语义 |
|---|---|---|
| `UNIFY_FUEL=4096` | L07 `mod.rs:627`、L08:542、L09:476、L10:450、L11:486、L12:605、L13:1419；孪生各 `prim/force` 同值 | force 展开耗尽返回**裸 rigid**（按未解处理）；unify 耗尽 `Err`——**判定可翻转**；L09 README §6.3 论证多数路径在本层不可触发（其余为死代码） |
| `MATCH_CMP_BUDGET=64` | 仅 L07（`mod.rs:641`；孪生 `unify.rs:40`），结构快路径**后**计数，耗尽记 `Undecided` | 合法但需 >64 次逐分支比较的负载被报"无法判定"；L08 未迁三档仍报"分支不可达"（L07 README §7.2） |
| `EQ_BUDGET=20000` | `struct_eq.rs:36`（L07–L13 同值） | 超预算 `val_eq` 返回 false → 快路径失效，回落慢路径（安全方向）[推断] |
| `probe_accessible` fuel | 每 ctor 独立充值（L07 `pattern_match.rs:354`） | 耗尽按**可达**处理（保守，不误拒）——方向正确 |
| L13 primop 溢出 | `checked_*` 溢出 ⇒ `None` 回落卡住 Decl（`nat-primops-plan.md` §6） | 静默降级为不可归约，不 panic 不回绕（可接受） |

**关键不变量**（应固化为 CI 断言，§5 G1）：**"预算耗尽"永不得映射为 `Absurd`/"分支不可达"**。
L07 的三档（`mod.rs:511-518`、`unification.rs:1233-1239`；Lean T3 `fuel_exhaustion_not_absurd`）
是唯一正确形态；L08–L13 尚未迁移（L08 判定分裂窗口，L07-RISKS §0.1）。

### G. panic 面（"合法源码可崩"清单）

| 位置 | 触发 | 状态 |
|---|---|---|
| L09（及 L10–L13 旧口径）`v_app(Val::Match, …)` | 打印"引用自递归卡住 match 的函数值"这类**合法源码** | 时代缺口，两版同崩 + parity 一致（L09 README §6.1"刻意不修"） |
| L10/L11/L12 `effort>1000` | trait 搜索失控（如 1200 个互异实例全不匹配） | `panic!("Too much effort :(")`；L13 已改降级，L10–L12 未回灌（L10 README §1.4、§6.2） |
| L13 `file_*` 五个 prim | IO 错误直接 panic，且无 `FILE_IO_LOCK` 串行化（L06–L08 有） | L13 README §6.6；测试靠文件名隔离 |
| L13 `lvl2ix` | 悬空 elaboration 变量泄漏进 quote | 已改 checked（指名根因），仍 panic 但可诊断（known-bugs Bug 2） |
| L06–L08 文件 IO | 评审轮已改"卡住降级"（不 panic，v2 三个 `v2_file_*_stuck_not_panic`） | 已修（L07 README §6 评审轮行） |

粗口径计数（[码·粗] 各层 `src/` 中 `panic!/unreachable!/todo!/unwrap()/expect(` 命中，排除文件名含
test 的文件）：L07 118、L10 129、L12 211、L13 **435**；L13 占比最高且为生产层——panic 面随
语言面扩张（parser/IO/命名空间）而增长，没有对应的"panic→Result"治理。

### H. UB / unsafe / 内存安全

- unsafe 计数（[码] 原始出现次数，含注释/测试）：L02 4、L03–L05 15、L06 16、L07/L08 16、
  L09 23、L10 22、L11 24、L12 27、**L13 94**，另有 `bench_head/bench_pre` 各 15–94。
- **已发生过的真 UB**：L13 孪生 `solve_multi_trait_ref` 用 `transmute` 洗掉 `MetaSnap.cxt` 生命周期，
  随后 `&mut self` 求解替换 meta 槽释放快照 → 悬垂 `cxt.decls` → 并发测试 `0xC0000005`；
  修复 = 同时克隆 `Rc<MetaSnap>` 保命（`docs/l13-parallel-test-uaf-2026-09.md` §4/§8）。
  该文 §4 明说孪生还有"大量刻意 `transmute` 与 `mach_ptr: *mut Machine` 别名写"，**同类生产点未逐一排查**。
- L07 孪生 `VSUB_REGS` 的"轮界 `Rc::from_raw` 归还"是另一类高风险 unsafe（有 SAFETY 论证 +
  `fast_substv_reclaimed_across_rounds` 回归钉），但目前只有"计数回落"证据，无 UB 检测器覆盖 [码/文档]。
- **证据缺口**：ASan 在本机不可用（缺 `clang_rt.asan`，UAF 文档 §5）；无 Miri/TSan CI；
  并发 UAF 只在 `--test-threads=12` 压力下才显形——**绿色默认 CI 不能证明无 UB**。

### I. 原生 Nat 的定义相等（L12/L13 特有，最高风险）

- L12/L13 引入 `Val::Nat(k)` + `nat_add/mul/sub/div/rem` primop（[码] `Val::Nat` 命中 L12 10/L13 99；
  `docs/nat-primops-plan.md`）。设计原则是"**prim 必须精确复刻旧递归定义的可归约性**，否则
  definitional equality 变化会打碎 prelude 里以 `rfl` 写成的证明"（nat-primops-plan §3 首段）[文档]。
- **风险点 1（表示双轨）**：原生 `Nat(k)` 与 unary `succ^k zero` 并存；`vals_eq_ground` 负责
  两者互判相等（`class_tests.rs:677-681`：native 7 ≡ chain 7 双向为真），这是**定义相等被显式拓宽**
  的位置——一旦桥接判据与转换/规范化不一致，就会产生"按 unary 语义不成立但被接受"的证明。
- **风险点 2（Flex 宽放）**：`vals_eq_ground` 把 Flex 视为等于一切（L12 README §6 登记为刻意语义）
  ⇒ trait 实例匹配的"相等"比转换关系更宽。
- **风险点 3（fuelless 归约语义差）**：部分展开规则（`x*succ d`、`sub` 单步）是为忠实旧 unfold
  而补的；任何一条漏/错都会让某条 `rfl` 证明从 Ok 变 Err 或反之。Lean 形式化**没有 δ/primop 层**，
  `add_zero_right` 这类 rfl 证明无法重演（lean/README.md 边界第 4 条）。
- **判断**：这是**最需要差分 oracle 的面**：建议保留 unary 语义的"影子引擎"或生成式对拍（§5 G2b）。

### J. 卡住 match（一等中性值）与 η/转换

- L07 的 `Val::Match(scrutinee, env, cases, pending)` + `force` 重选 + 值层 pending 应用、
  `Match vs Match` 结构快路径 + 严格 η（`unification.rs:1125-1218`）是七层中最完整的卡住项处理；
  但 P15 证明这条路径**曾漏比 pending 值**（可证 False，已修 + Lean T5 机检）。
- L09–L13 时代缺口：**卡住 match 不可再应用**（`v_app` panic）、**force 无 Match 重选**、
  `unify(Match,Match)` 用 `avoid_recursive` 中性 global 克隆（与 `struct_eq` 不同构，L09 README §6.2）
  ⇒ 精化传播更弱、部分合法源码崩溃/判定更保守。
- **判断**：L07 设计在正确性上严格优于下游；若 D7 统一架构，应把 `Val::Match`+pending+重选
  作为规范（并附带 L07 的 P15/R1/R3 全部钉子）。

## 3. known bugs/limits 清点（按严重度，均带锚点）

| # | 层 | 问题 | 级别 | 状态 |
|---|---|---|---|---|
| 1 | L12/L13 | 原生 Nat 定义相等双轨 + `vals_eq_ground` Flex 宽放 | S1[推断] | 文档登记，无对拍护栏 |
| 2 | L07/L10/L11 | with-K 无检查，接受集宽于 Agda | S1 | 文档化（README §7.3 / L10 §6.2 / L11:293） |
| 3 | L07 | 浅 occurs 不传递；`occurs_transitive` 的 VSub 嵌套只跟内层 σ（R2，测试钉 false） | S1/S2 | 主类已修，VSub 盲区**未修**（`L07-RISKS` §0.1 R2；`mod.rs:378-381`） |
| 4 | L07 | `Match` vs `Match` 逐分支重求值无结构指纹 → P2 曾 256 s + 假不可达；现 64 次预算 + 三档 | S1/S2 | 已修（`mod.rs:641`；Lean T3） |
| 5 | L07 | σ 可见性边界（decl/meta 不扫 σ，P6） | S1/S2 | 已知取舍 + 限制钉 |
| 6 | L07 | 探测（scratch 层级）与臂内（真槽）可能不同步（P7） | S1 | 文档化、**未设钉**（拒绝假钉） |
| 7 | L07 | 深值：quote Lam/Pi/Match 深链 + 端到端递归 Drop 未解（P11） | S3 | Sum/SumCase/Obj 已迭代化；Drop 未解 |
| 8 | L09–L13 | 卡住 match 不可应用/无重选（合法源码 panic，时代缺口） | S1 | 文档化、刻意不修（L09 §6.1） |
| 9 | L10–L12 | effort 超限 panic 而非类型错误 | S2 | L13 已改，L10–L12 **未回灌** |
| 10 | L10/L11 | 重定义静默覆盖（无 `redefine` 检查） | S2 | L10 §1.5；L11 无（L07/L08/L12/L13 有） |
| 11 | L13 | 诊断三收窄：`Bool×Bool` 缺组合仍接受 | S2 | 已知保守边界，parity 钉锁现状（L13 §6.1） |
| 12 | L13 | 单行 enum 两版同错（假阴性）；早期 parity 全绿即此因 | S2 | 已换 multiline 真覆盖 + 行为钉（L13 §6.2） |
| 13 | L13 | 快版分叉家族：GADT 索引宇宙×trait、struct 接收者、单臂 ctor 匹配、Prim 求值时机 | S2 | 剔除/结构化用例保证，缺陷另案（L13 §6.3） |
| 14 | L13 | trait 实例 Nat 参数：B 参数化模块静默错误→HDL004 警告；C 原 lvl2ix panic→可诊断 | S1/S2 | A 已修；B 根治需 meta 解支持消费点参数化 |
| 15 | L13 | `file_*` IO panic + 无锁；并发测试互踩 | S3 | 文档化（L13 §6.6） |
| 16 | L13 | 并行测试 UAF（transmute 生命周期洗白 + 悬垂快照） | S1 | 已修；同类生产点未排查（UAF 文档 §4） |
| 17 | 全层 | 加固不对称：P1–P11 只全落 L07；L08 只 P1/P2/P9；L09–L13 零回灌 | S1/S2 | `L07-RISKS` §0.1、CONVENTIONS §2 |
| 18 | 文档 | 多处计数/行号/结论过期（L13 lib 341 vs 静态 612；trait-analysis 4 bug 未标修复态） | S4 | 引用前回码 |

## 4. 正确性评分（A 轴）与敏感性

| 子维度 | 分 | 依据 |
|---|---:|---|
| 接受集健全性（soundness） | 3 | 构造性消除 2 个 bug 族（update_cxt 槽位族、phantom ctor），但 with-K/浅 occurs/Nat 双轨三处未证 |
| 拒绝集完备性（completeness） | 3 | 预算启发式可能误报"无法判定"；L13 `Bool×Bool` 覆盖保守缺口 |
| 崩溃安全 | 2 | L09 合法源码 panic、L10–L12 effort panic、L13 IO panic；L13 是生产层 |
| 内存/UB 安全 | 2.5 | L13 94 unsafe + 已发生 UAF；ASan 不可用、无 Miri/TSan CI |
| 诊断可信度 | 3 | L07 三档 + span；L08–L12 文案分层、span 归一化后比；L13 生产 LSP 诊断较全 |
| 形式化/oracle 证据 | 2.5 | Lean 有 T1/T2/T3/T5 真定理，但引擎/精化/nat 全在边界外；M3 仅 4 例 |
| **A 轴综合** | **2.8/5** | 教学场景加权可到 3.5–4；证明助手/生产场景压到 2 |

敏感性：若"最优"的目标是**教学/研究原型**，正确性权重可下调、L07 的构造性论证足够拿 4；
若目标是**HDL/LSP 生产编译器**（FRAMEWORK 用户原话"确保正确"+生产层），则 A 轴短板（panic、UB、
Nat 定义相等）会直接决定架构选型——**不能把 L13 当"生产就绪"的正确性基线**。

## 5. 正确性护栏设计建议（按性价比排序）

**G1 三值判定纪律全局化（P0，成本低）**：把 L07 的 `UnifyKind{Absurd,Undecided,Fuel}` + "预算耗尽
永不判 Absurd/不可达"移植到 L08–L13（L08 已明确未迁）；CI 增加断言：任何含 `(fuel exhausted)`/
预算耗尽的路径不得产出 coverage-unreachable。参照 Lean `fuel_exhaustion_not_absurd`/`classify_absurd_sound`。
**G2 差分矩阵（P0，本报告核心建议）**：四路对拍——
(a) **ref↔twin parity**（已有，扩到 Err 正文 + 全部层）；
(b) **unary↔native Nat 影子对拍**：同一语料分别用 `Nat(k)` 与 `succ^k zero` 语义求解，判定必须一致
（专治 §2-I；可在测试里构造两种 prelude/开关）；
(c) **σ↔update_cxt 跨载体对拍**：L07/L12（σ）与 L13（update_cxt）跑同一 curated 语料，差异归类为
"σ 边界/P6"或"update_cxt 陈旧"，作为 D7 选型的硬证据（注意 L13 σ 移植已回退，需 worktree 实验，归 EXP-8/D4）；
(d) **Lean oracle 扩容**：把 M3 从 4 条 curated 扩成"生成器 + 第三方裁判"，优先覆盖 occurs 两跳/VSub、
三档边界、struct_eq pending、空类型零臂、η、覆盖判定。
**G3 调试态不变量断言（P1，成本中）**：`debug_assert!` 级：`force` 顶层不返回 `VSub`；`SpecSolve.acc`
单调扩展且解值不含新 x；`subst_cxt` 不改 `lvl/locals/pruning`；`bind_count` 三方同序（编译期/运行时/prepend）；
σ 消费点清单化（grep 可审计）。把"私有纪律"变成可执行检查，专治 §2-A 的"漏包一处"。
**G4 对抗/属性测试（P1）**：用 `pmab_gen.rs` 的生成器扩成"覆盖矩阵生成器"（构造子×臂×通配×嵌套列），
期望由独立 oracle（决策树 usefulness 或 Lean 声明层）给出；trait 侧做**实例顺序置换**与重叠检测语料；
occurs 侧做"链式环/多跳/VSub 嵌套"最小反例自动生成。
**G5 known-bug 钉子标准化（P1，成本低）**：每份 `docs/*bug*` 文档 ↔ 同名测试（`<doc-id>_pin`），
panic 契约用 `catch_unwind` 而非 `should_panic`（L13 当前 0 个 `should_panic`，L09 `v_app` panic 无钉）；
计数口径统一（静态 vs 实跑、参考侧 vs 双子）。
**G6 panic→诊断迁移（P1/P2）**：L10–L12 effort 降级（照 L13 `None`）；L09 `v_app` 卡住 match 改
`Undecided` 或显式错误；L13 `file_*` io 错误 → `Err`/卡住；`lvl2ix` 保持 checked 并补"悬空 meta"
的普通错误路径。目标：**用户可达路径零 panic**（`typo`/IO/搜索失控三类）。
**G7 CI 门禁清单（P1）**：
1. `cargo test --lib`（各层）+ 全部 `lXX_fast_parity` + `l07/l08_blackbox*` + L13 LSP 11 套；
2. `LEAN_ORACLE=1 cargo test --test lean_oracle_parity`（独立 nightly job，需 `lake build engine-oracle`）；
3. 并行压力 job：`--test-threads=12` 重复 N 轮（UB 显形面）；
4. 反 panic 门禁：对已知 panic 点跑 `catch_unwind` 断言"应为 Err 而非 panic"（G6 落地后）；
5. `grep` 门禁：生产路径新增 `panic!/todo!/eprintln` 白名单化；
6. 计数对账 job：静态 `#[test]` 数 vs 实跑数 vs README 数，偏差 >10% 报警（治文档腐化）。
**G8 形式化优先级（P2，长期）**：①**refinement 健全性**（match 方程求解 + `subst_cxt` 上下文替换，
Cockx/Abel 式）——这是唯一能把"最强接受行为"纳入证据的路径；②NBE/元变量/合一规格（`docs/tt-spec-*` 已有）；
③subject reduction / 替换引理（lean/README.md:201-206 已列路线）。**不建议**先形式化决策树诊断或 HDL。

## 6. EXP-7 实验计划（**待 Lead 批准，暂不执行**）

**归属**：correctness-auditor（本报告）设计 + 判读；执行由 analyst-l09 承担（依 Lead 通知）；
**必须经 Lead 批准、与 perf 实验互斥**（FRAMEWORK §2 并发纪律：实验前写
`docs/optimal-design/experiments/.lock`，owner/exp-id/time，结束后删除）。构建前置：Lead 已完成
`CARGO_TARGET_DIR=C:\ezl-target cargo build --release --bins`（F: 盘仅 0.8 GB，禁止在 F: 构建）。

**EXP-7 目标**：在重建后的 HEAD 上，用统一口径回答三问——
Q1 现役测试体系是否全绿、与 README/静态计数是否对得上（漂移检测）；
Q2 18 条 known bug/limit 中哪些是"已修且钉住"、哪些是"文档化限制"、哪些是"实跑才暴露的新增失败"；
Q3 Lean oracle（M3）与 L07 参考引擎是否仍判定一致（4/4），并记录耗时/边界。

**E7.1 套件矩阵与命令**（全部 `CARGO_TARGET_DIR=C:\ezl-target`；先串行 `--test-threads=1` 取得
可归因基线，再单独跑默认并行压力轮；每层单独命令以便归因）：

| 组 | 套件 | 命令（示意） | 判据 |
|---|---|---|---|
| E7.1 lib | 各层 lib | `cargo test --lib L07_sum_type -- --test-threads=1` … `L13_namespace` | 0 failed；记录 passed/ignored 与 README/FACTS 静态数对账 |
| E7.2 parity | 7 个 `lXX_fast_parity` | `cargo test --test l07_fast_parity` … | 0 failed（L07/L08 只看判定；L09–L13 归一化正文） |
| E7.3 黑盒 | `l07_blackbox{,_v2,_v3}`、`l08_blackbox{,_v2}` | 同上 | 0 failed；`#[ignore]` 记数（L07 4 个） |
| E7.4 生产 | L13 LSP 11 套 + `twin_engine_tests` | `cargo test --test namespace_tests` … | 0 failed；记录 prelude 加载时间 |
| E7.5 oracle | `LEAN_ORACLE=1 cargo test --test lean_oracle_parity` | 先 `cd lean; lake build engine-oracle`（Lean 4.34.1 PATH） | `lean_oracle_rejects_unknown_case` + `lean_oracle_matches_reference_on_review_corpus` 全过；每例 <30 s |
| E7.6 已知 bug 复现 | 见 E7.2 表 | 手工/临时 example 按文档复现，不入库 | 与文档期望逐条比对（见下） |

**E7.2 已知 bug 复现语料与期望判定**（写进实验 raw，作为 D2 台账）：

| 语料 | 来源 | 期望（HEAD） | 失败判读 |
|---|---|---|---|
| c1 两跳环 occurs（README §8） | L07-RISKS P1 | **Err**（主类已修） | Ok ⇒ P1 回归（S1） |
| c1b 索引对调 | EXPERIMENTS F1 | Err | 与 c1 不一致 ⇒ occurs 仍不对称 |
| c2 卡住索引方程（`add` 递归 + 刚性 scrutinee） | L07-RISKS P2 | Err；参考版文案「无法判定」、孪生「分支不可达」 | >1 s 或超 30 s ⇒ 预算失效；Ok ⇒ 假接受；文案分层属已知（P3 未镜像） |
| 空类型零臂 `T Bool`/`T String` 零臂 match | review R1 | **Ok** | Err ⇒ R1 回归（Lean M3 同时会红） |
| P15 struct_eq pending（`pfun x zero` vs `pfun x (succ zero)` 上 `refl f`） | L07-RISKS P15 | **Err** | Ok ⇒ 可证 False（S1，最高优先） |
| R2 VSub 嵌套限制钉 | L07 tests | 测试断言"返回 false"（限制存在） | 若转为 true ⇒ R2 被修（预期外，更新台账） |
| L13 单行 enum | L13 README §6.2 | **两版同错**（parity 仍绿）：预期解析吞构造子/无构造子可用 | 若变 Ok ⇒ 现状变化，需重写钉子 |
| L13 GADT `/ struct` 精化弱例（`pattern-match-refinement-analysis` weak01–05/edge01） | 该文档 | 按文档：**weak03 已过、weak05/edge01 仍失败**（其他"失败"多为本身类型错误） | 逐例记录 Ok/Err + 错误文案，判"文档过期"或"真回归" |
| L13 trait Nat 参数复现 A/B/C | `l13-typeclass-instance-nat-param-bug.md` | A：Ok（已修）；B：**Ok + HDL004 警告**；C：**可诊断 panic 消息**（非裸溢出） | A Err ⇒ 回归；B 静默无警告 ⇒ S1 生产风险；C 裸 overflow ⇒ 回归 |
| L10–L12 effort cap | L10 README §1.4 | `panic!("Too much effort")`（**预期崩溃**，记录为已知） | 若已变 Err ⇒ 已回灌（更新台账）；其余形态 ⇒ 新问题 |
| L09 卡住 match 应用 | L09 README §6.1 | 按文档 panic / 或 parity 同错 | 若已不 panic ⇒ 时代缺口被修，更新 |
| L09/L10 重定义静默覆盖 | L09 §6.4、L10 §1.5 | 无 `redefine` 报错（静默覆盖） | 与 L07/L13 行为比对，记录跨层分裂 |

**E7.3 记录与原始数据**：每命令记录 `command / env(rustc) / start-end / passed-failed-ignored / wall time`；
原始输出存 `docs/optimal-design/experiments/raw/EXP-7-<组>-<层>.txt`；汇总成 D4 的矩阵（层×套件×判据）。
失败必须保留完整 stderr/归一化前后对比（尤其 parity 判定分裂）。

**E7.4 失败判读树（triage）**：
1. **parity 判定分裂（ref Ok / twin Err）** → 引擎不一致，S1；先看是否 P1/P2/P3 类（对比 `L07-RISKS`
   台账），记录首个差异源码与两侧文案；不修代码，仅记录 + 归因。
2. **lib 失败但源码=文档限制钉** → 期望行为变化，检查是否 HEAD 有未记录改动；归入"文档过期"。
3. **超时（>30 s 单例）** → 疑似预算/守卫失效（P2 类）；记录套件/语料，判 S2 回归。
4. **panic** → 查 §2-G 已知清单：命中 = 已知（记录）；未命中 = **S1 blocker**（合法源码可崩）。
5. **Lean oracle 判定分裂** → 最高优先（第三方裁判 vs Rust）；按 `lean/Typort/Engine/Oracle.lean`
   的机检依据逐条对照，若 Lean 侧期望本身因文档裁定改变，则记录"oracle 需升级"。
6. **L13 LSP/生产套件失败** → 生产回归，S1（优先级高于教学层）。
7. **全绿** → 只写"按当前判据通过"；必须同时列出**已知假阴性**（单行 enum、`Bool×Bool` 缺口、
   `#[ignore]` 探针、parity 不校文案、oracle 4 例）与**未覆盖轴**（with-K、Nat 双轨、UB/并发、深值 Drop），
   禁止把绿写成"正确性已证"。

**E7.5 产出**：`D4` 收录原始数据与汇总；`D2` 追加"EXP-7 结果"小节（判定/失败/已知限制核对表）；
给 Lead 的交接：若发现 S1 级新失败，立即 `send_message` 并暂停后续组（防止污染 baseline）。

## 7. 给 Lead 的一句话结论

**当前正确性 = "有构造性论证的教学检查器"（A 轴 2.8/5）：σ/三档/ctor-WF 是应保留的护栏，
with-K、Nat 定义相等、trait 多解、panic/UB 是 D7 必须显式兜底的四条红线；EXP-7 按本报告
E7.2/E7.4 执行，全绿也只算"按当前判据通过"，不算健全性证明。**
