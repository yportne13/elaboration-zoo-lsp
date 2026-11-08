# L07 潜在问题清单（代码审读 + 三侧实测）

> 对象：`F:\projects\hermes\elaboration-zoo-lsp\src\L07_sum_type`（参考版；孪生版在同目录 `bump_spine_iter/`）。
> 依据：本轮对 L07 / dpm-nbe-rs / Haskell 原版的三侧实测（[`EXPERIMENTS.md`](EXPERIMENTS.md)）、L07 源码通读、以及 L07 自己的 README §7「已知限制」诚实清单。
> 标注：【实测】= 跑过程序；【读码】= 代码路径确认；【已知】= 作者已在 README/注释中记录；【推断】= 由代码推出未验证。
> 级别：**S1** 健全性/语义（会给出错误判定）、**S2** 可用性/性能（判对但代价不可接受、或判断翻转）、**S3** 工程/诊断（不影响正确性但阻碍产品化）、**S4** 文档一致性。

## 0. 总表

| # | 问题 | 级别 | 证据 | 复现成本 | 修复成本 |
|---|---|---|---|---|---|
| P1 | 浅 occurs 不传递：接受循环解（同一程序换个索引顺序就被拒） | S1 | 实测 | 4 行 | 中 |
| P2 | 卡住索引方程：**256 s 后报假不可达** | S1+S2 | 实测 | 4 个 def | 中（需改 Match 合一策略） |
| P3 | fuel 语义污染：耗尽 = 判定翻转，且探测侧与臂侧方向相反 | S1+S2 | 读码+已知 | 构造深负载 | 低（改成三值结果） |
| P4 | no-K 无保护（with-K 假设） | S1 | 已知 | 理论构造 | 高（要设计） |
| P5 | meta 求解无跨 meta occurs，间接环只靠 fuel 兜底 | S1 | 读码 | 构造 meta 环 | 中 |
| P6 | σ 可见性边界：decl 表/meta 解不扫 σ | S1/S2 | 读码+已知 | 需缓存 def 值 | 高 |
| P7 | 覆盖探测与臂内方程可能不同步（scratch 层级 vs 真槽） | S1 | 已知 §7.4 | 依赖层级值 | 中 |
| P8 | 宽松 String/未登记 Decl 的合一逃逸舱口 | S1 | 读码 | 构造字符串程序 | 低-中 |
| P9 | 错误文案泄漏内部 Debug 表示（LSP 用户可见） | S3 | 实测 | 1 行 | 低 |
| P10 | `Error(String)` 无位置、解析错误折叠成 `parse error` | S3 | 实测+读码 | — | 中 |
| P11 | 深值：quote/pretty 仍递归，Drop 递归 | S3 | 已知 §7.6 | 深值 | 中 |
| P12 | 双实现（孪生 7611 行）的同步负担；parity 不覆盖错误文案 | S3 | 读码 | — | 结构性问题 |
| P13 | bench 覆盖缺口：c2 这类输入不在 7 个 workload 里 | S3 | 实测 | — | 低 |
| P14 | 文档漂移（design doc §10 仍写 HashMap；README 测试数过期） | S4 | 实测 | — | 低 |
| P15 | **struct_eq 漏比卡住 match 的 pending 值**：可证 False（S1 健全性） | S1 | 实测 | 4 个 def | 低（1 处，已修） |

## 0.1 修复进展（2026-11-08 收口）

> 历史：2026-10-31 分支 `fix/l07-match-unify` 的修复记录保留在下方；
> 2026-11-08 独立 review（[`docs/review-l07-hardening-2026-11-08/FINAL.md`](../review-l07-hardening-2026-11-08/FINAL.md)）
> 确认 **1 个 S1 接受集回归（R1）+ P1 未闭全（R2）+ 预算不同构（R3）与
> 工程/诊断/文档项（R4–R16）**，随后进入修复轮；本表与下方
> 「review 修复轮」小节已按修复轮后的状态重写。

| # | 状态 | commit / 轮次 | 验证 |
|---|---|---|---|
| P2 / P2′ | ✅ 已修（参考 + 孪生，**口径已统一**） | `2e598594` / `a70b5aaa` + 2026-11-08 修复轮 | c2 由 256 197 ms → **368 ms**（参考）/ 26.3 s → 95 ms（孪生）；两侧预算统一为 **64 次总次数 / 顶层合一入口、结构快路径后计数**（review R3/R8；旧的"参考深度 40 vs 孪生次数 64"两套代理不再存在） |
| P1 / P1′ | ✅ **主类**已修（参考 + 孪生）；**VSub 嵌套是已知限制** | `a474bf98` / `0f8acc52` + 2026-11-08 修复轮 | 两跳环两侧一致拒绝；`occurs_transitive` 的 VSub 臂只跟随内层 σ，嵌套时外层 σ 不可见（review R2，**未修**），限制钉 `test_occurs_transitive_vsub_nested_is_documented_limitation` 钉 false |
| P3 | ✅ 已修（参考版；孪生未迁三档） | `2d73b66e` + `691623f8` + 2026-11-08 修复轮（R1） | c2 由「分支不可达」→「**无法判定**」（278 ms），与 dpm/Agda 的 `not sure` 对齐；真矛盾仍报「分支不可达」。2026-11-08 补全 `unify_no_arm` 的 definite 集合，修复**合法空类型零臂 match 被拒**（review R1），钉 `test_empty_type_zero_arm_match_accepts_canonical_conflicts` |
| P9 | ✅ 已修（参考 + 孪生） | `503c3187` | 文案由 `Con("refl" @ 166,170, …)` → `refl(a)` / `cons(_, _)` |
| P8 | ✅ 已收窄 | `999d617f` | 宽松合一只对**裸**未知名 `Decl/Prim` 放行；带实参的未知头 → Undecided（不再静默判等）。判据仍是"名字是否登记"而非 provenance（review R12：当前无程序级逃生舱，属未来风险） |
| P4 | ✅ 文档化 | `86f431a4` | README §7.3 + 设计稿：with-K 定位、教学检查器≠证明助手、产品化路径 |
| P5 | ✅ **有界化**（非"已修"） | `30547abf` | `meta_expanding` 展开栈：跨 meta 环保留为卡住的 `Flex`（深度 2 即停），不再烧光 fuel；钉 `cross_meta_cycle_force_is_bounded`。`solve_with_pren` 仍无跨 meta occurs（m1:=?m2、m2:=?m1 仍可被创建），只是展开有界（review R12） |
| P6 | ✅ 已知边界已钉 | `551ad1f2` | `visibility_boundary_decl_value_is_not_refined`：直接包裹的 rigid 按 σ 展开，decl 缓存值原样返回 |
| P7 | ⏳ 未设钉（拒绝假钉） | — | 未能构造「方程解依赖层级数值」的触发用例；保留文档化描述 |
| P10 | 🟢 载体 + 解析/模式 span 已做（LSP 消费待接入） | `3221433e` + `26108306` + 2026-11-08 修复轮（R6/R7） | `Error(String, Option<Span<()>>)`；模式臂错误、解析错误（语法/残余 token）均填位置；语法错误 span 已修到**失败 token**（`many1_sep` 保留底层错误 + `p_decl` 用 `or_far` 保留最远失败分支，review R6）、偏移已改为**原文本坐标**（`preprocess` 保持字节长度，review R7）；文案/Debug 零漂移。余：LSP 出 Diagnostic（待本层接入） |
| P11 | ✅ 已做（quote 部分迭代 + pretty 定深截断） | `75cad763` + 2026-11-08 review R10/R11/R15 复核 | Sum/SumCase/Obj 深链迭代化（`quote_deep`）、`quote()` 顶层 VSub 臂改回 move、pretty 截断只作用于 `pretty_tm`；**Lam/Pi/Match 深链仍递归**（难以由源程序构造合法线性深值）、**端到端递归 Drop 未解**（测试用 `ManuallyDrop` 绕开） |
| P14 | ✅ 已修（本轮再同步） | `551ad1f2` + 2026-11-08 | README §8 计数对齐本 PR 合并时点实测（lib 66 / v3 113 / parity 92）；修复轮新增 4 lib 钉 + 1 parity 守卫后**静态核对 lib 70 / v3 117 / parity 97**（以 Lead 实跑为准）；design doc §10 改掉 HashMap 旧口径 |
| P15 | ✅ 已修（S1） | `0c73b65d` | `refl` 曾可证明两个闭实例化不同的函数相等并证 False；修复后两例均 `can't unify`；lib+parity 双回归钉 |
| P13 | ✅ 已做 | `1e1562e4` | 病理输入入 parity（两侧判定一致，单用例 0.29 s debug）；bench workload 未加。**PR 表旧描述"修复前 run=Ok/fast=Err"是错的**——修复前两侧都 Err、只是慢（review R13，PR 表已改） |

**孪生版现状（2026-11-08 更新）**：**P2 与 P1 均已跟修，且预算口径已与参考版
统一**（`a70b5aaa` + 2026-11-08：`MATCH_CMP_BUDGET = 64` 次总次数 / 每次
`unify_iter` 一份、结构快路径后计数；`occurs_transitive` 与参考版逐臂同构，
**含同一 VSub 嵌套盲区 R2**）。**仅 P3（三档判定）未跟修**——需要把
`unify_iter` 的 `bool` 结果改成三档，留作后续；因此同一程序在孪生侧仍报
「分支不可达」、参考版报「无法判定」（parity 只比判定/耗时、不比文案；本轮已
补空类型零臂 parity 钉，但 P3 未镜像的判定分裂窗口仍存在）。P5/P8/P10/P11
同样未镜像。

**重要保留（2026-11-08 修订）**：P1/P2 的最初修复在参考版 + 孪生侧各自实现，
但当时两处预算口径**不同构**（参考版递归深度 40 vs 孪生总次数 64）；本轮之后
L07 **双引擎**在 P1 主类 / P2 预算口径上已同构。孪生版
`bump_spine_iter/` 的 unify 是迭代工作栈，预算以 `unify_iter` 调用内的局部
计数实现（与参考版每顶层入口一份同口径），因此 c2 类用例**现在可以**放进
`l07_fast_parity`（孪生已有界）；本轮已补 `parity_empty_type_zero_arm_match`
与 `parity_stuck_match_equation_bounded` 的逐侧耗时断言。

### 2026-11-08 review 修复轮（R1–R9 处置）

来源：`docs/review-l07-hardening-2026-11-08/`（三份分报告 + `FINAL.md` 终报）。
本轮沿用既有设计方向，只补语义缺口、工程细节与文档口径；逐项处置：

| review 项 | 级别 | 处置 | 落点 / 回归钉 |
|---|---|---|---|
| R1 P3 分档不完整：合法空类型零臂 match 被拒（S1，接受集回归） | S1 | ✅ 已修 | `unify_no_arm` 的 definite 判据改为「两侧都是规范值/类型头（`Sum` / `SumCase` / `LiteralType` / `LiteralIntro` / `U` / `Pi` / `Lam`）即 `Absurd`，否则 `Undecided`」；`test_empty_type_zero_arm_match_accepts_canonical_conflicts`、`parity_empty_type_zero_arm_match` |
| R2 `occurs_transitive` 的 VSub 臂丢弃外层 σ（P1 只是部分闭包） | S2（程序级可达则 S1） | ⚠️ **未修（已知限制，文档化）** | 修复需要"非物化 compose 的多 σ 扫描"：`frcs` 的语义是 `frcs(outer, VSub(v, s2)) = frcs(compose(outer, s2), v)`，照做要把外层 σ 与内层 σ 组合——`Subst::compose` 会物化整条替换链（深/长链 O(n²)、可栈爆），与"槽位只包裹不物化"的纪律冲突，留作独立轮。现状：VSub 臂只跟随内层 σ，被多次包裹的槽值上仍有漏环；限制钉 `test_occurs_transitive_vsub_nested_is_documented_limitation` 钉 false（单层对照钉 true） |
| R3 两处"卡住 match 预算"不同构（参考递归深度 40 vs 孪生总次数 64） | S2 | ✅ 已修 | 两侧统一为 `MATCH_CMP_BUDGET = 64` 次总次数 / 每顶层合一入口、**结构快路径后**计数（参考版 `unify_catch` + `unify_indices` 每方程 reset，孪生版每次 `unify_iter` 一份）；常量注释同步；不再作为差异列入 |
| R4 L08 迁移只落参考版（L08 ref/twin 判定分裂：c1 ref Err / twin Ok） | S2 | ✅ 已修 | L08 孪生镜像 P1/P2（`bump_spine_iter/subst.rs` 的 `occurs_transitive` + `unify.rs` 的 `MATCH_CMP_BUDGET = 64`）；`l08_fast_parity` 增 c1/c2 verdict + 计时守卫（`parity_l08_occurs_transitive_chain` / `parity_l08_stuck_match_equation_bounded`） |
| R5 L08 的 `no named implicit arg {:?}` Span Debug 泄漏 | S3 | ✅ 已修 | L08 参考版 `elaboration.rs` / 孪生版 `machine.rs` 均改为 `{}` 直出名字 |
| R6 语法错误 span 指向"失败 decl 的首 token" | S3 | ✅ 已修 | `many1_sep` 保留首个 item 的底层 `IError`（失败 token 的真实 span）+ `p_decl` 改用 `or_far` 保留最远失败分支；`test_parse_error_span_points_at_failing_token`；既有 `parse_error_carries_span` 增强为切片断言 |
| R7 span 偏移是预处理后文本坐标（非 ASCII 注释使后续偏移前移） | S3 | ✅ 已修 | `preprocess` 注释替换保持字节长度（非 ASCII 按 `len_utf8` 个空格替换）；`test_parse_error_span_matches_raw_source_with_unicode_comment` |
| R8 预算检查在结构快路径**之前**（注释与实现相反） | S3 | ✅ 已修 | 结构快路径先试、失效才计数/查预算；"深度 40 边界钉"缺口随总次数口径消除（不再有深度边界） |
| R9 `UnifyKind` 的 note 不随 meta 快照回滚（旧 `Undecided`/`Fuel` 污染终判） | S3 | ✅ 已修 | `flex_flex` 反向重试前恢复 kind 水位（`meta_restore` 后 `unify_kind.set(kind_before)`），真 `Absurd` 不再被前一次尝试的分档污染 |
| R10–R16 | S3/S4 | 文档/数字类随本轮同步（R10/R11/R15 的精确表述落在 L07 README §7.6b；R12 见 P5/P8 行；R13 的计数与 PR 表修正见 PR §5/§9 与本表 P13/P14；R14 见 parity 耗时断言；R16 = 其它 API nit，未改代码） | — |

> **未修清单**：**R2**（VSub 多 σ 盲区，需非物化 compose 的多 σ 查找，
> 避免物化整链导致 O(n²)/栈爆，留独立轮）；**R16 的 API 扩面 nit**
> （`Error` 两字段 `pub`、`Span` 的 `PartialEq` 只比 `data`、`quote_arm`
> 不可达臂与死代码）——不影响可观测行为，未在本轮动。


---

## P1（S1）浅 occurs 不传递：接受循环替换

> **2026-11-08 状态**：两跳环**主类**已在参考版 + 孪生版修复（§0.1 P1 行）；
> `VSub` 嵌套时外层 σ 不可见仍是**已知限制**（review R2，未修，见 §0.1
> 「review 修复轮」R2 行与限制钉
> `test_occurs_transitive_vsub_nested_is_documented_limitation`）。

**现象**【实测】：

```typort
enum Nat { zero  succ(x: Nat) }
enum Eq[A](x: A, y: A) { refl(a: A) -> Eq a a }

def bad(x: Nat, e: Eq[Nat] x (succ x)): Nat =
    match e { case refl(a) => zero }
```

L07 **接受**（81 ms）。把索引对调成 `Eq[Nat] (succ x) x` 则 **拒绝**（"分支不可达"，8 ms）。同题 dpm 与 Haskell 原版也都接受（它们无 occurs）——但 L07 是**有** occurs 检查却漏掉。

**机制**【读码】：
1. 特化方程是逐参数 zip（`pattern_match.rs:356-396`）：`x = a` 与 `succ x = a`（`a` 是构造子字段的 fresh 模式槽）。
2. 第一条走 `(Rigid x, v)` 臂：x 在 `solvable` 里 → `x := a`，`val_mentions_lvl(a, x)` 为假（`unification.rs:901-914`）。
3. 第二条在当前 `acc` 下解释（`wrap_sub` + force，`:860-865`），得到 `succ a` vs `a`；**先命中** `(v, Rigid a)` 臂 → `a := succ x`；此时 `val_mentions_lvl(succ x, a)` 为假 → 通过。
4. 两步都"无环"，但组合出的 σ 是循环的：`x ↦ a`、`a ↦ succ x`。
5. `val_mentions_lvl`（`mod.rs:1393-1434`）只看**值的浅结构**：不进闭包体（`Lam/Pi` 处直接 `{}`），也不扫 σ 的映射值，因此无法发现"v 里提到的 y 的解最终又回到 x"。

**影响**：检查器在一个无解方程上"解出了"循环替换。本层没有运行时求值这一步（def 只做检查），所以不会直接产生错误程序；但 σ 会被后续臂/嵌套 match 读到，`force` 在该读点用 fuel 有界展开（`frcs` 的 lookup 命中烧 1），**循环度越深，后续判定越依赖 fuel 余量**——与 P3 叠加。教学口径上这与 Agda 的行为相反（Agda 直接拒绝该子句）。

**建议**：在写 `acc` 前做一次"传递 occurs"——把 v 在 `acc` 下 force 一次再查 x（贵但只在解点）；或维护 `Subst` 的解依赖图做环检测（union-find，O(α)）；退一步也可把"同一子句解出 >1 条涉及同一 rigid 族的方程"记为可疑并报 can't unify。

**置信度**：机制【推断，与实测判定一致】；c1b 的反向对照（拒绝）是本条最强的证据。

---

## P2（S1+S2）卡住索引方程：256 秒后报"假不可达"

> **2026-11-08 状态**：参考版 + 孪生版均已修，预算口径统一为 **64 次总次数 /
> 每顶层合一入口、结构快路径后计数**（review R3/R8，见 §0.1 P2 行）。
> 超预算按"无法判定为相等"保守失败——L07 记 `Undecided`（臂报「无法判定」），
> L08 未迁三档仍报「分支不可达」；已知取舍：合法但需 >64 次逐分支比较的
> 深/宽嵌套会报「无法判定」（启发式上限，已文档化）。

**现象**【实测，release】：

```typort
def add(x: Nat, y: Nat): Nat =
    match x { case zero => y  case succ(n) => succ (add n y) }

def f(x: Nat, y: Nat, e: Eq[Nat] (add x zero) (add y zero)): Nat =
    match e { case refl(a) => a }
```

- L07：**256 197 ms** 后返回 `分支不可达：模式 Con("refl" …) 与被匹配类型不相容`；
- Haskell 原版：11 ms 报 `I am not sure if there should be a pattern 'refl' for equation between plus x zero and plus y zero.`
- dpm：5 ms，同一句 `not sure`。

**隔离实验**【实测】：

| 变体 | 改动 | 结果 |
|---|---|---|
| c2b | 把 `add` 换成非递归的 `g`（`g x` 仍卡住） | **接受**，13 ms |
| c2c | 索引改成 `add zero x`/`add zero y`（scrutinee 可归约） | **接受**，8 ms |
| c2 | 递归 `add` + 刚性 scrutinee `x`/`y` | **256 s 假不可达** |

**机制**【推断，与 03 文档 D5 / README §1.4 一致】：
1. 合一走 `(Val::Match, Val::Match)` 臂：先比 scrutinee（`x` vs `y`，`x`/`y` 都在 `bind_slots` 里，其实**解得出来** `x := y`）；
2. 但槽位纪律"只包裹不物化"（`mod.rs:721-784`）让两份卡住 match 的捕获 env 各带**不同的 `VSub` 实例**；
3. `struct_eq` 的 VSub 分支只对**同一 `Rc`** 短路（`struct_eq.rs:82-88`），快路径不命中 → 回落到"逐分支在 fresh rigid 下重求值"；
4. 递归 def 的分支体（`succ (add n y)`）又产生新的卡住 match，层级每层递增 → 永不结构收敛 → 直到 fuel 池耗尽（`pattern_match.rs:303` 每次探测都 `meta_refuel`，臂内方程共享池）；
5. 每层 re-eval/quote 的常数很大，4096 次调用 × 数百 μs ≈ 数百秒。

**为什么 bench 没抓到**：`l07bench` 的 7 个 workload（church/strchain/global/match/enum/natadd…）里没有"两个递归 def 的卡住 match 互相比较"。这条是**工作负载盲区**。

**影响**：
- 编译时间悬崖（4 个 def 就 4 分钟；LSP 场景完全不可用）；
- 判定错误：把"解不出来"报成"矛盾"（假 absurd）。更糟的是 P3 的不对称——覆盖探测把 fuel 耗尽**按可达**处理（`pattern_match.rs:336-342`），臂内方程把 fuel 耗尽当 **Err → 不可达**（`:203-209`）。同一原因两侧结论相反，可能出现"报缺构造子"但用户写全了 / 或臂被判不可达后覆盖集缺该构造子而报错，用户无从修复。

**建议**（按性价比）：
1. **在 Match/Match 入口做规范化**：把两侧 `wrap_sub` 到同一 σ 后再比（等价于 README §1.4 的 rebase，但用在方程入口而不是期望类型），让 `struct_eq` 的 VSub 同实例短路有机会命中；
2. **给 `Val::Match` 加结构指纹**：`(def 名, scrutinee 的规范化 spine, cases 长度)`，指纹相同直接判等（同一 def 的两份卡住 match 不需要逐分支重求值）；
3. **让 `PatternDetail`/`cases` 共享 `Rc`**，使同源 match 的 cases 同址，扩大 `ptr::eq` 短路；
4. **判定分级**：fuel 耗尽时返回第三种结果（`Idk`），而不是 `Err`——文案改为"无法判定"而非"不相容"（对齐 dpm 的 `UnifyRes::Idk`）；
5. 短期缓解：给 `probe_accessible` 与臂内方程分别设预算并对"预算耗尽"打标记，别让它伪装成结构冲突。

**置信度**：现象与隔离【实测】；机制【推断】（未插桩验证 `struct_eq` 未命中次数）。

---

## P3（S1+S2）fuel 语义污染与两侧不对称

> **2026-11-08 状态**：参考版已修（`UnifyKind` 三档，`UnifyKind` 拆分
> 真矛盾 `Absurd` / 判不出 `Undecided` / 预算耗尽 `Fuel`）；2026-11-08
> review R1 补全 `unify_no_arm` 的 definite 集合，**合法空类型零臂 match
> 已恢复接受**。**孪生版未迁三档**，仍报旧口径（§0.1 P3 行）。

**现象/机制**【读码 + 已知 §7.2】：`UNIFY_FUEL = 4096`（`mod.rs:479`）是 `Cell<u32>`，被 force 的展开臂、`frcs` 的 lookup 命中、`unify` 每次递归共享（`mod.rs:592/700/612/635/650/663`，`unification.rs:835-846`）；耗尽时有界降级：force 返回裸 rigid（"按未解处理"）、`unify` 返回 `Err`。

**影响**：
1. **把"算力不够"伪装成"结构冲突"**——P2 的 256 s 就是实例；README §7.2 自认"极深嵌套模式负载下可能把合法分支误判为不可达（假 absurd）"。
2. **不对称**：覆盖探测侧 `probe_accessible` 把 `fuel_exhausted` 当**可达**（保守，`:336-342`），臂内方程侧把 `Err` 当**不可达**（`:390-393` 只加尾注）。两侧对同一预算问题给出相反判定。
3. 引导用户"加大 `UNIFY_FUEL`"不是修复：它同时放大了 P2 的时延。

**建议**：`unify` 返回 `Result<(), UnifyErr>`，其中 `UnifyErr = { Absurd, Stuck(Idk), Fuel }`；只有 `Absurd` 允许判不可达，`Fuel` 必须以"无法判定"报错；探测侧也按同一分档处理。

**置信度**：机制【读码】；后果部分【实测】（P2）。

---

## P4（S1）no-K 没有保护

**已知**（README §7.3）：本层和 L07a 一样是 with-K 实现，精化一个"出现在其它假设里"的变量在完整依赖理论里需要 without-K 级论证。
**影响**：教学场景可接受；若被当作产品/证明助手，会接受在 without-K 下不可证的等式（例如与 K 一致的公理下证明 `Id` 上的 UIP 类结论）。**建议**：至少加一个编译期开关/文档警示，或在 API 层提供"禁止 K 依赖"的模式（短期只能文档化）。

---

## P5（S1）元变量求解无跨 meta occurs

> **2026-11-08 状态**：已**有界化**（跨 meta 环确定性停下、不再烧光 fuel），
> **不是"已修"**——`solve_with_pren` 仍无跨 meta occurs（间接环仍可被创建；
> review R12，见 §0.1 P5 行）。

**读码**：`solve`（`unification.rs:653-689`）把解写回 meta 表，但 force 的注释明说 "solve 无跨 meta occurs check"（`mod.rs:584-588`）——meta 解链可能形成间接环，靠 fuel 兜底。
**影响**：与 P3 同源；间接环会让 force 深度爆炸（再叠加 P2 的常数）。
**建议**：solve 前对 `rhs` 做一次 meta 可达性检查（沿 Flex 的 spine 递归，浅层即可），至少把直接环变成报错而不是"烧 fuel"。

---

## P6（S1/S2）σ 的可见性边界：decl 表与 meta 解不扫 σ

**读码**：`force` 的 `Val::Decl` 臂直接取 decl 表缓存的 WHNF 并 `v_app_sp`（`mod.rs:629-641`），**不接触 σ**；`frcs` 对 `Decl` 只包裹 spine（`:727`）。同理 `Val::Flex` 的已解展开只 `v_app_sp(t_solved, sp)`（`:591-599`）。
**后果**（README §1.3 明示的取舍）：若一个 def 的缓存值里含稍后被模式特化的槽位，精化在该读点**不可见**——可能出现"该归约的不归约 / 该相等的比较不等"，判定随求解顺序变化。
**建议**：成本高（def 缓存要按 σ 失效，或把 σ 也推进 decl 条目）；至少要有一个回归用例把这条边界钉成"已知行为"，避免未来被误当 bug 修成不一致。

---

## P7（S1）覆盖探测与臂内方程不同步

**已知**（README §7.4）：探测用 scratch 层级（`pattern_match.rs:319-323`），臂内用真槽；"方程解依赖层级数值本身"时判定可能不一致。现有测试未触发。
**建议**：探测改用与臂内一致的槽位分配（代价：探测不再可丢弃）；或至少在探测与臂内判定不一致时降级为"无法判定"。

---

## P8（S1）宽松合一的逃逸舱口

**读码**：`unify` 有两条 `(LiteralType, Prim/Decl)` 臂走 `loose_string`（`unification.rs:970-975`）：decl 表**未登记名**放行、已登记名按登记类型把关。这是为 `string_to_global_type` 的"动态类型"设计的。
**影响**：未登记名的卡住 `Decl` 可以与 String 字面量层**互相判等**；如果将来有路径让"本应登记却没登记"的名字进来（例如 builtin 注册表或简化 decl 表），会静默接受错误的合一。当前源码路径不可由用户程序触达【推断】。
**建议**：把"未登记名"的放行收窄到 `string_to_global_type` 的产物（例如给该值打一个 `Dynamic` 标记），而不是按"名字是否登记"判断。

---

## P9（S3）错误文案泄漏内部 Debug 表示【实测】

> **2026-11-08 状态**：已修（参考 + 孪生；L08 两引擎的
> `no named implicit arg {:?}` 泄漏也已修，review R5，见 §0.1 P9 行）。

```
== ERR ==
分支不可达：模式 Con("refl" @ 166,170, [Con("a" @ 171,172, [], Expl)], Expl) 与被匹配类型不相容
```

来自 `pattern_match.rs:208` 的 `format!("{:?}", pat)`（`Pattern` 的 derive Debug）。同一句在 IDE 里会直接展示给用户。
**建议**：写一个 `pretty_pattern`（复用 `pretty.rs` 的构造子渲染），文案改为"模式 `refl(_)` 与类型 `Eq Nat (succ x) x` 不相容"。

---

## P10（S3）诊断工程面

> **2026-11-08 状态**：`Error` 已携带可选 `Span`（模式臂错误 / 解析错误
> 均填位置）；语法错误 span 已修到**失败 token**、偏移已改为**原文本坐标**
> （review R6/R7）；余项 = LSP 消费 `Error::span()` 出 Diagnostic（§0.1
> P10 行）。`Error` 两字段 `pub` 属 API 扩面（review R16，未动）。

- `Error(String)` 无位置（`mod.rs:445-455`），`run(input, path_id)` 也不带文件路径（`:1514`）；
- 解析失败统一折叠为 `"parse error"`（`parser/mod.rs:125-128`），只有"残余 token"带字节偏移；
- 工程里虽有 `parser_lib_resilient.rs`，但 L07 的 parser **没有用它做恢复**。
**影响**：LSP 只能定位到"整个文件的某次 run 失败"，无法画 caret；这是 L07 接入项目 LSP 之前的硬前置（README §6 也把"深值栈安全轮"称为 LSP 接入前置，但漏了这一条）。

---

## P11（S3）深值

> **2026-11-08 状态**：quote 的 Sum/SumCase/Obj 深链 + pretty 已处理；
> 2026-11-08 review R10/R11/R15 复核后明确：**Lam/Pi/Match 深链仍递归**、
> `quote()` 顶层 `VSub` 臂已改回 move、pretty 定深截断只作用于 `pretty_tm`、
> **端到端递归 Drop 未解**（深值测试用 `ManuallyDrop` 绕开；见 §0.1 P11 行
> 与 L07 README §7.6b）。

**已知**（README §7.6）：`val_mentions_lvl` / `struct_eq` 全家 / `rename` 已迭代化；但
- `quote` / `pretty` 仍是递归（触发面 = nf 输出与错误显示）；
- 深值的 **释放** 是 Rc/Box 链递归 Drop（参考版）。
**影响**：10^5 层值在默认 2 MB 栈下，nf 输出/错误显示会爆栈；LSP 里一个恶意深值即可打挂进程（除非外层线程栈足够大）。
**建议**：接入 LSP 前把 quote/pretty 迭代化或定深拒绝（与 README §7.6b 的待办一致）。

---

## P12（S3）双实现同步负担

- 参考版 + 孪生版 `bump_spine_iter/`（7611 行）**并存**，语义要求逐点同构；本轮 L07 的所有机制（`Subst`/`VSub`/`frcs`/`SpecSolve`）在孪生侧都有第二份实现；
- `tests/l07_fast_parity.rs` 只断言 "Ok 输出逐字节一致 / Err 判定一致"，**不比较错误文案**——所以文案漂移不会被 parity 抓到，只能靠黑盒套件；
- 已知偏差清单（README §10 末）已经有一串（span 全零、错误文案常数、求值序、binder 改名）。
**影响**：P1/P2 的任何修复都要写两遍（且孪生侧有 arena/迭代内核的额外约束）；给 L08–L13 的推广会把这个成本乘 4。
**建议**：先修参考版并加 parity 用例（把 c2 这类输入加入 fast_parity 的负载集），孪生侧按"机制同构"跟。

---

## P13（S3）bench 覆盖缺口

`l07bench` 的 7 个 workload 全部是"程序规模递增"型（church/strchain/global/match/enum/natadd），没有一个在测**同一程序内的合一搜索**。P2 完全在盲区里。
**建议**：把 `c2`（4 个 def、256 s）与 `c2b`（13 ms）作为一对"病理/健康"基准加进 bench；这会立刻把 P2 变成可见的性能回归。

---

## P14（S4）文档漂移

> **2026-11-08 状态**：README §8 计数已按本 PR 合并时点实测对齐（lib 66 /
> v3 113 / parity 92），design doc §10 已改掉 HashMap 旧口径；2026-11-08
> 修复轮之后**静态核对 lib 70 / v3 117 / parity 97**，终值以 Lead 实跑为准
> （§0.1 P14 行）。

- `docs/l07-dpm-refactor-design.md` §10 仍写"force 热路径的 rigid 解查找 O(n) → O(1)（HashMap）"，实现是单链扫描（§9.4 已改口径，§10 没跟着改）；
- `README.md` §8 写"l07_blackbox_v3 95 个、l07_fast_parity 70 个"，实测 `#[test]` 是 47 与 23（v3 通过 `#[path]` 引入 lib 测试，95 可能按"47+48"计；parity 的 70 与 23+48=71 差 1）；
- 设计稿 §5 的 `UnifyRes` 形状与实现（`Option<&mut SpecSolve>`）不同，§9 已注明，但正文未改。
**影响**：新人/移植者按文档走会得到错误实现（§9.4 的 warning 已经出现过一次）。

---

## P15′ 审计结论（2026-11-01）

同一轮"递归→迭代"改写涉及的三个遍历器已逐 case 对照旧版（`git show 2309e2a4^:`）：
`struct_eq`（1 处漏项 = P15，已修）、`val_mentions_lvl`（无漏项）、
`rename/rename_deep/rename_arm`（无漏项，6 处等价性已逐点核对）。
详见 [`AUDIT-iterative-rewrite.md`](AUDIT-iterative-rewrite.md)。孪生版同类遍历未审计。

---

## P15（S1，已修）struct_eq 漏比卡住 match 的 pending 值

**现象**【实测，2026-10-31】：`f 1 = zero`、`g 1 = succ zero`，但 `def bad : Eq[Nat -> Nat] f g = refl f` 被**接受**；在其上可经 `ap` 得到 `Eq Nat zero (succ zero)`，零臂 match 消去即得 `False = (A : U) -> A`（修复前输出 `UNSOUND-FALSE-PROVED`）。孪生版一直正确 ⇒ 修复前是判据分裂。

**根因**【读码】：`struct_eq.rs` 的卡住 match 臂只比较 pending 的**长度与 icit**，漏了 pending 的**值**。`unify` 的 Match/Match 快路径用 `val_eq` 比较两侧 scrutinee；当 scrutinee 本身是「pending 不同」的卡住 match 时（本例 `pfun x zero` vs `pfun x (succ zero)`），两份值被判等。引入点是 commit `2309e2a4`（2026-09-19 迭代化重写）：递归版原本有 `val_eq_go(xv,yv)`，改成任务栈后只压了分支体，**注释仍写「访问序含 pending」**。

**修复**：pending 的 icit 照旧检查，并压 `EqTask::V(xv, yv)` 比较值（按注释访问序先压 → LIFO 最后弹出）。

**回归钉**：lib `test_struct_eq_compares_match_pending_values`、`test_nested_match_pending_cannot_prove_false`；parity `parity_struct_eq_match_pending`（修复前 run=Ok / run_fast=Err）。

**其它层**：L09–L13 的 `Val::Match` 没有 pending 槽；L08 / `bench_head` 的 `struct_eq` 仍保留 pending 值比较（对照正确形态）。故本缺陷仅 L07 参考版一份。

---

## 15. 建议修复顺序

> 2026-10-31 原始建议排序（历史）；实际完成/现状以 §0.1 为准：
> 1（P2/P3/P13）、2（P1 主类）、3（P9/P10 载体）、4（P11）均已落地或有界化；
> P6/P7 为文档化已知行为；R2（VSub 多 σ）与 L09–L13 推广未做。

1. **P2 + P3 + P13**（同一根因族：Match 合一无规范化 + fuel 语义污染）：先加"匹配前 `wrap_sub` 规范化 + Match 结构指纹"，再把 fuel 耗尽改成 `Idk`；配合把 c2/c2b 加进 bench 与 parity。收益最大（4 分钟 → 毫秒级 + 判定不再翻转）。
2. **P1**（occurs 传递闭包）：4 行程序就能暴露，修复局部。
3. **P9 + P10**（诊断）：接 LSP 前必做，成本低。
4. **P11**（quote/pretty 迭代化）：与 LSP 前置绑定。
5. **P6/P7**（可见性边界、探测同步）：先加"已知行为"回归钉，再评估是否改架构。
6. **P4/P5**（no-K、跨 meta occurs）：理论与健壮性层面，写文档 + 保守判定即可。

> 说明：P1/P2 的实测程序、耗时、隔离变体都在 [`EXPERIMENTS.md`](EXPERIMENTS.md)；P2 的机制与 dpm/Haskell 的对照见 [`02-pattern-unify.md`](02-pattern-unify.md) D3/D8 与 [`03-value-quote.md`](03-value-quote.md) D5。
