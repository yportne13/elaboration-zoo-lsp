# PR：L07 稳定性与健全性加固 + L08 迁移（20 commits，分支 `fix/l07-match-unify`）

> 目标仓库：`F:\projects\hermes\elaboration-zoo-lsp` · 基线 `master` @ `641c52fe`
> 变更范围：**`src/L07_sum_type/`（全部）+ `src/L08_product_type/`（P9/P2/P1 三项迁移）+ 对应文档/测试**（L09–L13、LSP、引擎未动；2026-11-08 review 修复轮为 PR 合并后追加，见 §9）
> 结论：L07 参考版单机范围内，「正确性 / 健壮性 / 诊断语义」三类已知问题在**本 PR 范围**内收口；2026-11-08 独立 review 另发现 1 个 S1 接受集回归与若干工程/文档项，修复轮处置见 §9。L07 双引擎 P1/P2 已同构；P3 / quote / span 等差异仍在孪生侧记录在案。

## 1. 这个分支解决什么

起点是与 `dpm-nbe-rs` 的三侧（L07 / dpm-nbe-rs / Haskell 原版）实现比对 + 本轮新增的
「迭代化重写审计」与探针实测。共确认 **1 个 S1 健全性缺陷 + 1 个 4 分钟级性能悬崖 +
2 个语义判定错误 + 若干健壮性/诊断问题**，逐个修复并全部配回归钉。

## 2. commit 地图（按依赖/阅读顺序）

> 以下 20 个 commit 为 **PR 合并时点**（`008f42ed`）；2026-11-08 修复轮的
> 改动不在本表，见 §9。

| # | commit | 类型 | 解决什么 | 回归钉 |
|---|---|---|---|---|
| 1 | `2e598594` | fix | 卡住 match 比较无界下钻：c2 由 **256 s → 368 ms**（假不可达） | `test_stuck_match_equation_bounded` / `..._nonrecursive_still_equal` |
| 2 | `a474bf98` | fix | occurs 不传递：`Eq Nat x (succ x)` 上 match refl 曾**接受**循环解 | `test_occurs_check_transitive_chain` / `..._keeps_legit_refinement` |
| 3 | `503c3187` | fix | 诊断泄漏内部 Debug（`Con("refl" @ 166,170, …)`）→ `refl(a)` / `cons(_, _)` | 文案断言加强（含 `!contains("Con(")`） |
| 4 | `2d73b66e` | fix | 判定二值化：卡住 match/fuel 失败与「结构矛盾」混同 → 引入 `UnifyKind` | `test_unify_kind_separates_absurd_from_undecided` |
| 5 | `a70b5aaa` | fix | 孪生版镜像 #1：`MATCH_CMP_BUDGET`（c2 26.3 s → 95 ms） | — |
| 6 | `1e1562e4` | test | parity 守卫：病理输入纳入双 oracle（修复前**两侧都 Err**、只是慢——256 s / 26.3 s；不是判定差分。"run=Ok/fast=Err" 那类描述属于 #9 的 pending 值用例） | `parity_stuck_match_equation_bounded`（2026-11-08 补逐侧耗时断言） |
| 7 | `0f8acc52` | fix | 孪生版镜像 #2：`occurs_transitive`（V/SubstV 形态） | — |
| 8 | `a1f1bf36` | test | parity 守卫：两跳环两侧一致拒绝 | `parity_occurs_transitive_chain` |
| 9 | `0c73b65d` | **fix（S1）** | `struct_eq` 漏比卡住 match 的 pending 值：可证 `False` | `test_struct_eq_compares_match_pending_values` / `..._cannot_prove_false` / `parity_struct_eq_match_pending` |
| 10 | `691623f8` | fix | `rename/invert/solve` 失败仍报「矛盾」→ 归 `Undecided`；兜底分类器 `unify_no_arm` | `test_stale_solvable_order_independent`（改断言） |
| 11 | `75cad763` | fix | `quote` 深链迭代化 + `pretty` 定深截断（10 万层默认 2 MB 栈） | `deep_value_iterative_under_default_stack` ③ |
| 12 | `3221433e` | feat | `Error` 携带可选 `Span`（模式臂错误填位置；文案/Debug 零漂移） | `error_carries_pattern_span` |
| 13 | `26108306` | feat | 解析错误也带位置（契约不变） | `parse_error_carries_span` |
| 14 | `551ad1f2` | test+docs | σ 可见性边界钉 + README 计数 / 设计稿 §10 漂移 | `visibility_boundary_decl_value_is_not_refined` |
| 15 | `30547abf` | fix | 跨 meta 环守卫（不再靠 fuel 耗尽兜底） | `cross_meta_cycle_force_is_bounded` |
| 16 | `999d617f` | fix | 宽松合一只对裸未知名 `Decl/Prim` 放行 | `loose_string_requires_empty_spine` |
| 17 | `86f431a4` | docs | with-K 定位写成警示（README §7.3 + 设计稿） | — |

## 2.5 L08 迁移（3 commits，模板化落地）

L08 与 L07 共用同一套架构（`Val`/`Subst`/unify 形状一致），把 L07 的三项修复按同一模板落了一遍：

| commit | 迁移项 | 说明 / 实测 |
|---|---|---|
| `efbc9fa9` | P9 诊断渲染 | `Pattern::pretty`；黑盒断言收紧为含 `cons(_, _)` 且不含 `Con(` |
| `3c6b656b` | P2 比较预算 | 时点为递归深度 `MATCH_CMP_DEPTH = 40`：同一 c2 程序 **无预算 475–554 s → 639 ms**（debug）；2026-11-08 起与 L07 参考版/孪生统一为 **64 次总次数 / 快路径后计数**（§9） |
| `d06d4c56` | P1 传递 occurs | `occurs_transitive` + 前置筛选；两跳环由「接受」变「分支不可达」 |

**PR 时点** L08 尚未迁移：P3 三档判定、quote/pretty 深值、Error span（L08 的
`Error` 仍是单字段；以及 L08 孪生版镜像）。2026-11-08 修复轮已补 **L08 孪生
P1/P2 镜像**（`occurs_transitive` + `MATCH_CMP_BUDGET = 64`，`l08_fast_parity`
加 c1/c2 verdict + 计时守卫）与 **L08 两引擎的 `no named implicit arg`
Span Debug 泄漏**；**仍未迁移**：P3 三档、P11 quote/pretty 深值、P10 Error span、
P5/P8（与 L07 的剩余项同构，可按同样模板继续，见 §9 与 L08 README §6）。

### L09–L13 评估（2026-11-01，结论：**不适用模板移植**）

| 层 | 架构 | 结论 |
|---|---|---|
| L08 | L07 代码 + product types（`Val::Decl`、`Match` 带 pending、`Pattern` 同形） | ✅ P9/P2/P1 已迁参考版（3 commits）；2026-11-08 孪生 P1/P2 已镜像（§9） |
| L09 | 早期 MLTT 层：`Val::U(u32)`、`Prim` 无 spine、**无 `Decl`**、`Match` 无 pending | ⏸ 暂缓：模板不适用（见下） |
| L10–L13 | 后世代引擎（L13 是生产版，自带 `Val::Decl(Span<String>, Spine)` 与独立架构） | ⏸ 未评估；先前的“同一批缺陷”假设**未证实**，需逐层单独分析 |

L09 的实测证据（本轮）：
- 同一个 c2 程序（两个递归 def 的卡住索引方程）：L07/L08 会「假不可达」（无预算时 256 s / 8 分钟），**L09 直接接受**（合一半径不同：无结构快路径，分支体比较直接通过）；
- 同一个 c1 程序（两跳环）：L09 在 **2 MB 测试栈上栈溢出**（`STATUS_STACK_OVERFLOW`）；
- 给 L09 加 L07 的传递 occurs 守卫后，c1 **仍然栈溢出**——说明溢出点不在 occurs 路径，而在 L09 自己的归约/模式编译链（无界递归，无 cycle/fuel 守卫）；
- 因 L09 架构已分叉，硬搬模板会引入未经验证的语义变化（先期 P2 补丁实测把 c2 从「接受」变「拒绝」，属语义变更而非修复）。已全部回滚，L09 无任何改动。

> 结论：**跨层推广到 L08 为止**。L09 需要一次独立的架构分析（先定位栈溢出点，再决定是按 L09 自己的设计修，还是整体对齐 L07）；L10–L13 需先做同类评估，不能预设。
## 3. 可观测行为变化（review 重点）

| 场景 | 修复前 | 修复后 |
|---|---|---|
| 两个递归 def 的卡住索引方程（`Eq (add x zero) (add y zero)`） | 256 s 后「分支不可达（不相容）」 | 278 ms 后「**无法判定**」 |
| `Eq Nat x (succ x)` 上 match refl（两跳环） | **接受**（循环解） | 「分支不可达」 |
| `refl : Eq (Nat→Nat) f g`（f/g 闭实例不同） | **接受**（S1，可证 False） | 「can't unify」 |
| 臂级错误文案 | `模式 Con("refl" @ 166,170, …)` | `模式 refl(a)` / `cons(_, _)` |
| 刚性变量 ≐ 构造子（非规范对） | 「分支不可达」 | 「无法判定」 |
| 规范值冲突（`zero ≐ succ zero`） | 「分支不可达」 | 不变 |
| 10 万层深值 nf / 错误显示 | 爆栈（0xC00000FD） | 显示遍历正常（quote 部分迭代 + pretty 截断）；**深值释放仍递归 Drop，未解**（review R15） |
| `Error` 载体 | 仅文案 | 文案 + 可选 `Span`（Display/Debug 不变） |

## 4. 兼容性与风险

- **pub API 变化（唯一破坏性点）**：`pub struct Error(String)` → `pub struct Error(String, Option<Span<()>>)`。
  字段 0 仍是文案（`e.0` 老用法可用）、`Display`/`Debug` 输出逐字节不变；但**外部**若直接 `Error(s)` 构造会编译失败
  ——本仓库内 **60 处 `Error::new(...)` + 1 处带 span 的二元构造**已改
  （参考版 29 / 孪生版 31 处 `Error::new`；另 1 处在参考版 `pattern_match.rs`
  的模式错误拼接点 `Error(self.errors.join("\n"), self.first_span)`）。
  L07 目前未接入 LSP，无外部消费者。
- `UnifyKind` / `MATCH_CMP_BUDGET` / `meta_expanding` 均为 `pub(crate)`，不扩面。
- 判定收紧（occurs、宽松合一、undecidable 分类）只影响**报错语义与接受集**，不影响运行时求值语义；
  测试面：lib + 4 套黑盒 + parity 全绿。
- 孪生版 `bump_spine_iter` **PR 时点**镜像了 P2/P1/P9。此后 2026-11-08 review
  确认该表述过宽：**P3 未镜像不止文案**——判定分档不同会让同一程序在
  ref/twin 上分别报 Err/Ok（review R1 实测 `T Bool` vs `T String` 空类型用例
  ref Err / twin Ok），P5/P8 也未镜像且属语义面；L08 parity 还比较 Err 正文。
  修复轮已补 parity 空类型钉（`parity_empty_type_zero_arm_match`）并统一预算
  口径（§9）；文案差异记录在 `L07-RISKS.md` §0.1。

## 5. 验证

本 PR HEAD（`008f42ed`）实测（2026-11-08 复核；各计数静态核对一致）：

```
cargo test --lib L07_sum_type        # 66 passed
cargo test --test l07_blackbox       # 48 passed（+1 ignored）
cargo test --test l07_blackbox_v2    # 51 passed（+2 ignored）
cargo test --test l07_blackbox_v3    # 112 passed（+1 ignored；含 66 个引入的 lib 测试）
cargo test --test l07_fast_parity    # 92 passed（26 自有 + 66 引入）

# L08（迁移后）
cargo test --lib L08_product_type       # 60 passed
cargo test --test l08_blackbox          # 57 passed（+1 ignored）
cargo test --test l08_blackbox_v2       # 51 passed（+2 ignored）
cargo test --test l08_fast_parity       # 93 passed（33 自有 parity + 60 引入）
```

另：**全库 `cargo test --lib` 990 passed / 0 failed / 6 ignored（81.85 s，实测）**
——跨层无回归（本 PR 合并时记录为 987；2026-11-08 review R13 复测更正为 990）；
`cargo build --release` 通过；L07 文档（README §7.3/§8、设计稿 §10）与实际对齐。

> 2026-11-08 修复轮新增测试后的**终值以 Lead 实跑为准**（见 §9）：L07 侧新增
> 4 个 lib 回归钉（R1/R2/R6/R7）与 1 个 parity 守卫（空类型零臂）
> + 既有预算用例的逐侧耗时断言；L08 侧 parity 增加 c1/c2 两个守卫。
> 静态核对：L07 lib **70** / v3 **117** / parity **97**；L08 parity **95**；
> 全库 lib **994**（990+4）。

## 6. review 指南

1. **先看 3 个 S1/S2 修复**：`2e598594`（预算）、`a474bf98`（传递 occurs）、`0c73b65d`（pending 值）——各自的回归钉在 `src/L07_sum_type/tests.rs` 尾部。
2. 再看语义分档：`2d73b66e` + `691623f8`（`UnifyKind` 的引入与第二刀），重点确认「规范值冲突仍判 Absurd」没有被放松。
3. 最后看工程项：`75cad763`（quote/pretty 深值）、`3221433e`/`26108306`（Error span 载体）、`999d617f`（宽松合一收窄）。
4. 孪生版的两个镜像 commit（`a70b5aaa`、`0f8acc52`）都配了 parity 钉，可独立验证。
5. **2026-11-08 review 修复轮**是合并后追加的：先看 §9 的 R1（S1 接受集回归）与
   预算口径统一（R3/R8），再看 R2（已知限制）与文档/数字修正（R13）。

## 7. 后续（不在本 PR）

1. **LSP 接入 + P10 第三步**：消费 `Error::span()` 出 `Diagnostic.range`（L07 本层尚未接入项目 LSP）。
2. **深值递归 Drop**（README §7.6a）：参考版真树在深值析构时按深度吃栈；需要自定义 Drop/堆栈析构。
3. **孪生版镜像**：**P1/P2 已在 2026-11-08 镜像**（总次数 64 预算口径同构）；
   余 **P3 三档、quote/pretty 深值、Error span**（按当前决定暂缓，见 §9）。
4. **其它层**：**L08 参考版已迁 P9/P2/P1，孪生版 P1/P2 于 2026-11-08 镜像**
   （P3/P10/P11/P5/P8 仍未迁）；**L09 架构已分叉、模板不适用**（c1 栈溢出、
   c2 接受，均已记录）；**L10–L13 未评估**（后世代引擎，需逐层分析，不能预设同构）。
5. **R2（VSub 多 σ 盲区）**：`occurs_transitive` 的 VSub 臂需非物化 compose
   的多 σ 查找，留独立轮（§9）。

## 8. 回滚

单分支、无数据迁移；可整体 `git revert master..HEAD` 或按 commit 逐个 revert。语义变化集中在
`src/L07_sum_type/{unification,pattern_match,struct_eq,mod,pretty}.rs`，恢复 master 版本即回到旧行为。

## 9. review 修复轮（2026-11-08）

本 PR 合并（`008f42ed`）后，2026-11-08 的独立 review（三份分报告 + 终报，
`docs/archive/review-l07-hardening-2026-11-08/`）确认 **1 个 S1 接受集回归 + 若干
S2/S3/S4 项**（编号 R1–R16）。修复轮在**不改变本 PR 语义方向**的前提下逐项
处置（明细见 `L07-RISKS.md` §0.1「2026-11-08 review 修复轮」）：

| review 项 | 级别 | 处置 | 说明 / 落点 |
|---|---|---|---|
| R1 P3 分档不完整 ⇒ 合法空类型零臂 match 被拒（基线接受） | S1 | ✅ 已修 | `unify_no_arm` 的 definite 判据补全为「两侧都是规范值/类型头（Sum/SumCase/LiteralType/LiteralIntro/U/Pi/Lam）即 Absurd，否则 Undecided」；钉 `test_empty_type_zero_arm_match_accepts_canonical_conflicts` + `parity_empty_type_zero_arm_match` |
| R2 `occurs_transitive` 的 VSub 臂丢外层 σ（P1 部分闭包） | S2 | ⚠️ **未修（文档化 + 限制钉）** | 需"非物化 compose 的多 σ 扫描"：`frcs(outer, VSub(v,s2)) = frcs(compose(outer,s2), v)` 照做会物化整条替换链（深/长链 O(n²)、栈爆），与槽位"只包裹不物化"纪律冲突；`test_occurs_transitive_vsub_nested_is_documented_limitation` 钉住 false |
| R3 参考版递归深度 40 vs 孪生总次数 64 不同构 | S2 | ✅ 已修 | 统一 `MATCH_CMP_BUDGET = 64` 总次数 / 每顶层合一入口、结构快路径后计数（参考 `unify_catch`+`unify_indices` reset，孪生每次 `unify_iter` 一份） |
| R4 L08 迁移只落参考版（L08 ref/twin 判定分裂） | S2 | ✅ 已修 | L08 孪生镜像 P1/P2（`bump_spine_iter/subst.rs` + `unify.rs`）；`l08_fast_parity` 增 c1/c2 verdict + 计时守卫 |
| R5 L08 `no named implicit arg {:?}` Span Debug 泄漏 | S3 | ✅ 已修 | L08 参考版 `elaboration.rs` / 孪生版 `machine.rs` 改 `{}` 直出名字 |
| R6 语法错误 span 指向失败 decl 首 token | S3 | ✅ 已修 | `many1_sep` 保留首个 item 的底层 `IError` + `p_decl` 改用 `or_far` 保留最远失败分支；切片断言钉 `test_parse_error_span_points_at_failing_token` |
| R7 span 偏移基于预处理文本坐标（非 ASCII 注释错位） | S3 | ✅ 已修 | `preprocess` 注释替换保持字节长度；`test_parse_error_span_matches_raw_source_with_unicode_comment` |
| R8 预算检查在结构快路径之前（注释与实现相反） | S3 | ✅ 已修 | 快路径先试、失效才计数/查预算；预算改为总次数口径后不再有"深度边界" |
| R9 `UnifyKind` 的 note 不随 meta 快照回滚 | S3 | ✅ 已修 | `flex_flex` 反向重试前恢复 kind 水位（`meta_restore` 后 `unify_kind.set(kind_before)`） |
| R10–R16 | S3/S4 | 文档/数字同步 | R10/R11/R15 的精确表述 → L07 README §7.6b（quote 仅 Sum/SumCase/Obj 迭代、VSub 臂 move、pretty 截断仅 `pretty_tm`、端到端 Drop 未解）；R12 → P5「有界化」/P8 provenance；R13 → 本节与 §4/§5 的数字修正；R14 → parity 耗时断言；R16 → 未动代码 |

数字口径（review R13 更正；括号内为修复轮后的静态核对值，终值以 Lead 实跑为准）：

- `Error::new`：**60 处 + 1 处带 span 的二元构造**（参考 29 / 孪生 31 处
  `Error::new`；另 1 处在参考版 `pattern_match.rs` 的模式错误拼接点）——PR §4
  原写"30 处"已过期；
- 全库 `cargo test --lib`：本 PR HEAD 实测 **990 passed / 0 failed / 6 ignored
  （81.85 s）**（PR 原记录 987 已过期）；修复轮新增 4 个 L07 lib 测试 →
  **静态核对 994**，以 Lead 实跑为准；
- L07 套件 HEAD：lib 66 / blackbox 48+1 / v2 51+2 / v3 112+1 / parity 92；
  修复轮新增 4 个 lib 回归钉与 1 个 parity 守卫 → **静态核对 lib 70 /
  v3 117（116 可跑 + 1 ignored）/ parity 97（27 自有 + 70 引入）**；
  blackbox / v2 无新增；以 Lead 实跑为准；
- L08 套件 HEAD：lib 60 / blackbox 57+1 / v2 51+2 / parity 93；本轮新增 c1/c2
  两个守卫 → **静态核对 parity 95**；以 Lead 实跑为准；
- commit 表第 6 行（`1e1562e4`）描述已修正：修复前**两侧都 Err、只是慢**
  （256 s / 26.3 s），不是"run=Ok/fast=Err"——后者是 `0c73b65d` 的 pending
  值用例；
- PR §4 旧表述「孪生只镜像 P2/P1/P9、parity 不受影响」已改为精确表述：
  P3 未镜像**不止文案**（判定分档不同，review R1 实测 ref Err / twin Ok），
  P5/P8 也未镜像且属语义面；本轮已补空类型 parity 钉与两侧判定守卫。

**未修（留待后续）**：R2（VSub 多 σ 盲区）；R16 的 API 扩面 nit（`Error` 两字段
pub、`Span::PartialEq` 只比 `data`、`quote_arm` 不可达臂等）；L08 的 P3 三档 /
quote/pretty / Error span / P5/P8 仍未迁移（与 L07 剩余项同构）。

---

附：变更统计

```
docs/l07-dpm-refactor-design.md              |  10 +-
 src/L07_sum_type/README.md                   |  35 +-
 src/L07_sum_type/bump_spine_iter/compiler.rs |  28 +-
 src/L07_sum_type/bump_spine_iter/entry.rs    |   2 +-
 src/L07_sum_type/bump_spine_iter/machine.rs  |  41 ++-
 src/L07_sum_type/bump_spine_iter/subst.rs    | 125 +++++++
 src/L07_sum_type/bump_spine_iter/unify.rs    |  41 ++-
 src/L07_sum_type/elaboration.rs              |  36 +-
 src/L07_sum_type/mod.rs                      | 421 +++++++++++++++++++++++-
 src/L07_sum_type/parser/mod.rs               |  45 ++-
 src/L07_sum_type/parser/syntax.rs            |  24 ++
 src/L07_sum_type/pattern_match.rs            | 144 +++++---
 src/L07_sum_type/pretty.rs                   |  29 ++
 src/L07_sum_type/struct_eq.rs                |  12 +-
 src/L07_sum_type/tests.rs                    | 475 ++++++++++++++++++++++++++-
 src/L07_sum_type/unification.rs              | 174 ++++++++--
 tests/l07_blackbox_v2.rs                     |   5 +-
 tests/l07_fast_parity.rs                     |  96 ++++++
 18 files changed, 1594 insertions(+), 149 deletions(-)
```
