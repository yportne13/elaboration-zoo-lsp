# L07 最近改动详细 review（终报）

> 评审对象：`F:\projects\hermes\elaboration-zoo-lsp` · `master` HEAD `008f42ed`
> （merge：分支 `fix/l07-match-unify` → master，基线 `641c52fe`，tag `v432-008f42e`）
> 范围：20 个 commit（17 个 L07 加固 + 3 个 L08 迁移），25 个文件，+1817/−155；
> 全部落在 `src/L07_sum_type/**`、`src/L08_product_type/**`、`tests/l07_*`、`tests/l08_*`、`docs/`。
> 评审方式：3 名独立评审员（健全性核心 / 孪生+parity+L08 / 工程面+API+文档）各写一份分报告，
> Lead 独立复核关键结论并实测（测试、release 构建、merge 卫生、4 个一次性探针）。
> 分报告：`docs/review-l07-hardening-2026-11-08/findings-{soundness,twin-parity,eng-api-docs}.md`。

## 0. TL;DR

**总体：方向正确、工程质量高于本仓库往期改动，但有 1 个 S1 接受集回归 + 2 个 S2（P1 未闭全、
双引擎/预算语义分裂）+ 3 个 S3 诊断正确性缺陷。分支尚未 push（领先 SSH origin 21 个 commit），
建议先修 S1/S2 再推送。**

已实测确认的关键事实：

| 结论 | 状态 |
|---|---|
| 全套 L07/L08 测试绿（含 PR 声称的每个计数，除「全库 987」→ 实际 **990**） | ✅ Lead 实测 |
| `cargo build --release` 通过（6m11s） | ✅ Lead 实测 |
| merge 干净：merge 树 == 分支头 `d06d4c56` 树，`git diff d06d4c56 008f42ed` 为空；无越界改动 | ✅ Lead 实测 |
| **S1**：P3 分档不完整 ⇒ **合法的空类型零臂 match 被拒**（基线接受），且判定随冲突值形态不一致 | ❌ **Lead 已复现**（见 R1） |
| **S2**：P1 `occurs_transitive` 的 `VSub` 臂**丢弃外层 σ** ⇒ P1 未闭全 | ❌ **Lead 单元级已证实**（见 R2） |
| **S2**：参考版预算 = 递归深度 40、L07 孪生 = 总次数 64 —— **不是逐点同构**，可构造双向判定漂移 | ❌ 代码已核实，构造未跑（见 R3） |
| **S2**：L08 只迁参考版，L08 孪生未镜像 P1/P2 ⇒ **L08 参考版/孪生版判定已分裂**（c1：ref Err / twin Ok） | ❌ **Lead 已复现**（见 R4） |
| **S3**：语法错误 span 指向「失败 decl 首 token」而非失败 token；span 偏移是**预处理文本**坐标，中文注释后整体错位 | ❌ **Lead 已复现**（见 R6/R7） |
| P15（struct_eq pending）S1 修复：真修、完整、方向安全 | ✅ 复核确认 |
| `Error` 的 `Display`/`Debug({:?})` 逐字节不变；L07 无仓内外部消费者 | ✅ 复核确认 |
| PR/`L07-RISKS` 的若干数字与声明过时或不准 | ❌ 见 R16 |

**评级**：L07 参考版单机语义「已知三项清零」基本成立、但 P3 引入回归（R1）且 P1 只是部分闭包（R2）；
L07 双引擎（ref/twin）在 P3 语义面已经不一致（R1 实测 R1 用例 ref Err/twin Ok）；
L08 双引擎在 P1/P2 面已经不一致（R4 实测）。建议按 §6 的优先级修复后再合并/推送。

> **2026-11-08 修复轮已实施**（见 §0.1）；§1–§6 保留**修复前 review 原文**供追溯，现状以 §0.1 为准。

## 0.1 修复轮（2026-11-08，已实施并全量验证）

> 本节是实现后的状态。所有测试为 Lead 在本工作区统一实测（不是引用）；release 构建另行验证。

**验证结果（修复轮后）**

```
cargo test --lib L07_sum_type         # 70 passed, 5.41s（+4 新回归钉）
cargo test --test l07_blackbox        # 48 passed + 1 ignored, 0.52s
cargo test --test l07_blackbox_v2     # 51 passed + 2 ignored, 0.01s
cargo test --test l07_blackbox_v3     # 116 passed + 1 ignored, 5.27s（+4 引入的 lib 钉）
cargo test --test l07_fast_parity     # 97 passed, 5.44s（26 自有 + 70 引入 + 1 新 parity）
cargo test --lib L08_product_type     # 60 passed, 0.86s
cargo test --test l08_blackbox        # 57 passed + 1 ignored, 0.56s
cargo test --test l08_blackbox_v2     # 51 passed + 2 ignored, 0.01s
cargo test --test l08_fast_parity     # 95 passed, 0.82s（+2 新 c1/c2 verdict+计时钉）
cargo test --lib                      # 994 passed / 0 failed / 6 ignored, 71.40s
cargo build --release                 # 通过, 6m02s（仅 warning）
```

| 发现 | 状态 | 实施内容 | 回归钉/证据 |
|---|---|---|---|
| R1 S1 合法空类型零臂 match 被拒 | ✅ **已修** | `unify_no_arm` 改为「两侧都是规范值/类型头（Sum/SumCase/LiteralType/LiteralIntro/U/Pi/Lam）⇒ Absurd；其余中性头 ⇒ Undecided」（`is_canonical_head`）；`T Bool`/`T String` 两种空类型零臂 match 恢复接受 | lib `test_empty_type_zero_arm_match_accepts_canonical_conflicts`；parity `parity_empty_type_zero_arm_match`；Lead 探针实测两者 Ok |
| R2 S2 `occurs_transitive` VSub 嵌套丢外层 σ | ⏳ **未修（文档化 + 钉限制）** | 尝试 `compose(outer,s2)` 会沿解链反复物化、链长指数增长：深嵌套模式测试从 ~5s 恶化到 >60s/4GB 后栈溢出，已回滚；恢复内层 σ 并写明已知限制，正式钉住当前行为 | lib `test_occurs_transitive_vsub_nested_is_documented_limitation`（nested=false / single=true，注释写明独立轮应改 true）；README §7.2 与 RISKS 记录 |
| R3 S2 两引擎预算语义不同构 | ✅ **已修** | 参考版从「递归深度 40、快路径前检查」改为与孪生同口径：`MATCH_CMP_BUDGET = 64` **总次数 / 每顶层合一入口 / 结构快路径先试、慢路径才计数**；参考版在 `unify_catch` + `unify_indices` 每方程 reset，孪生每次 `unify_iter` 一份；常量/注释/README/RISKS 同步 | `parity_stuck_match_equation_bounded` 新增两侧计时 <10s；既有 lib bounded 钉；`cargo test` 全绿 |
| R4 S2 L08 孪生未镜像 P1/P2（ref/twin 判定分裂） | ✅ **已修** | L08 孪生 `bump_spine_iter/subst.rs` 移植 `occurs_transitive`（2048 预算、`VSub` 内层 σ）；`unify.rs` 两处可解 rigid 臂接入 + `MATCH_CMP_BUDGET=64` 快路径后计数；`l08_fast_parity` 新增 c1/c2 verdict+计时守卫 | `parity_l08_occurs_transitive_chain`（10s）/`parity_l08_stuck_match_equation_bounded`（30s）实测绿；`cargo test --test l08_fast_parity` 95 passed |
| R5 S3 L08 P9 漏迁（`no named implicit arg {:?}`） | ✅ **已修** | L08 参考版 `elaboration.rs` 与孪生 `machine.rs` 改 `{}`/`{name}`，与 L07 同款 | 代码 grep；L08 两套件绿 |
| R6 S3 语法错误 span 指 decl 首 token | ✅ **已修** | L07 `IError` 实现 `ErrorProgress`（`msg.start_offset`）；`p_decl` 改 `p_def.or_far(p_print).or_far(p_enum)` 保留最远失败错误；`many1_sep` 保留首个 item 底层错误 | Lead 探针：`"def f : Nat = )\n"` → span=(14,15) 切片 `")"`；lib `test_parse_error_span_points_at_failing_token`；`parse_error_carries_span` 增强为切片断言 |
| R7 S3 span 偏移基于预处理文本（中文注释错位） | ✅ **已修** | `preprocess` 注释替换改为按 `len_utf8` 逐字节补空格（L07 + L08 同步），预处理文本与原源同字节长度 | lib `test_parse_error_span_matches_raw_source_with_unicode_comment`（断言 `preprocess(src).len()==src.len()` + 原文本切片 `";"`）；Lead 探针 (27,28)→`";"` |
| R8 S3 预算检查在快路径之前 | ✅ **已修** | 随 R3 重写：先 `struct_eq` 快路径，失败才查/消耗预算（参考版与 L08 参考版） | 同 R3 |
| R9 S3 `UnifyKind` 不随 meta 快照回滚 | ✅ **已修** | `flex_flex` 反向重试前保存并恢复 `unify_kind` 水位（`kind_before`），旧 Undecided/Fuel 不再污染真 Absurd 终判 | 代码路径（无独立程序钉，注释说明） |
| R10/R11 S3 quote 范围与 VSub clone | ✅ **已修** | README §7.6b 明确 quote 深链仅 Sum/SumCase/Obj（Lam/Pi/Match 仍递归）；`quote()` 的 `VSub` 臂改回 **move**（`*v`），去掉 `Box::clone` | 代码 + 文档 |
| R12/R13/R16 S4 文档/数字/声明 | ✅ **已修** | L07 README §7.2/§7.6b/§8/§10、L08 README §6/§8、L07-RISKS §0.1（删自相矛盾行、P5 改「有界化」、P14 计数、新增修复轮小节）、PR 文档（994、60+1、commit 表第 6 行修正、"parity 不受影响"精确化）均已更新 | 见各文档 diff |
| R14/R15 S4 parity/测试强度 | ✅ **已修** | L07 parity：病理用例加两侧计时、新增零臂 parity 钉、struct_eq pending 显式双 Err；L08 parity：新增 c1/c2 verdict+计时；深值声明限定为「遍历不爆栈，释放仍递归 Drop」 | 见 §0.1 验证计数 |

**仍未修/未迁（有意留作后续）**

1. **R2**：`occurs_transitive` 的 VSub 嵌套已知限制。正确修法需要「非物化 compose 的多 σ 查找」（例如携带 outer/inner 双 σ 并由 lookup 按优先级查），否则会沿解链反复物化导致指数链长/深模式性能崩溃（本轮实测）。已文档化 + 测试钉住当前行为，留独立轮。
2. **L08 仍未迁**：P3 三档（`UnifyKind`）、P11（quote/pretty 深值）、P10（Error span）、P5/P8 孪生侧；L08 参考版 c2 仍按旧口径报「分支不可达」（文档已登记）。
3. **R15 残余**：深值「释放」仍是 Rc/Box 链递归 Drop（README §7.6a）；本轮只限定声明，未改实现。

---

## 1. 范围与方法

### 1.1 merge / 卫生

- `008f42ed` 是 merge commit，两个父：`641c52fe`（master 基线）与 `d06d4c56`（分支头）。
- `git rev-parse 'd06d4c56^{tree}' '008f42ed^{tree}'` 相同（`45fbccfb…`）；`git diff d06d4c56 008f42ed` **为空**
  ⇒ merge 无冲突解决副作用，结果即分支头内容。
- 变更 25 个文件全部在 L07/L08/对应 tests/docs 内；L09–L13、LSP、引擎、`vscode_extension/` 零改动
  （L09 实验已回滚，与 PR 一致）。
- 分支领先 `ssh-origin/master` 21 个 commit（20 + merge），尚未 push。

### 1.2 本次实际执行（Lead）

```
cargo test --lib L07_sum_type         # 66 passed, 5.58s
cargo test --test l07_blackbox        # 48 passed + 1 ignored, 0.55s
cargo test --test l07_blackbox_v2     # 51 passed + 2 ignored, 0.01s
cargo test --test l07_blackbox_v3     # 112 passed + 1 ignored, 5.52s
cargo test --test l07_fast_parity     # 92 passed, 5.45s
cargo test --lib L08_product_type     # 60 passed, 0.22s
cargo test --test l08_blackbox        # 57 passed + 1 ignored, 0.59s
cargo test --test l08_blackbox_v2     # 51 passed + 2 ignored, 0.01s
cargo test --test l08_fast_parity     # 93 passed, 0.23s
cargo test --lib                      # 990 passed / 0 failed / 6 ignored, 81.85s
cargo build --release                 # 成功, 6m11s（仅 warning）
```

### 1.3 一次性探针（均已删除，`git status` 干净；源见本报告附录 A）

1. **occurs_transitive 嵌套 VSub**：单元级构造 `VSub(VSub(Rigid(0), ∅), σ)`、σ={0↦7,7↦9}，
   `force` 语义应看到 9，而 `occurs_transitive` 返回 `false` → 证实 R2。
2. **F1 空类型零臂 match**：`enum T(A : U) { c -> T Nat }`；
   `def ok1(e: T Bool): Nat = match e { }` → ref=Ok/twin=Ok；
   `def bad1(e: T String): Nat = match e { }` → **ref=Err「match 不完整：缺少构造子 c」/ twin=Ok** → 证实 R1、
   同时证明「P3 未镜像不影响 parity」**不成立**。
3. **解析/span 定位**：`"def f : Nat = )\n"` 的错误 span=`[0,3)` 切出 `"def"`（非 `)`）；
   `"// 中文注释\n\ndef x = U ;\n"` 的 leftover span=`(19,20)` 在原文本切出 `"f"`（应为 `;`）→ 证实 R6/R7。
4. **L08 双引擎 c1**：`L08::run` = Err「分支不可达：模式 refl(a) 与被匹配类型不相容」，
   `L08::bump_spine_iter::run_fast` = **Ok** → 证实 R4。

---

## 2. 逐 commit 评估

| # | commit | 评估 | 说明 |
|---|---|---|---|
| 1 | `2e598594` P2 比较预算（参考版） | ⚠️ | c2 由分钟级降到有界；但**预算检查在 struct_eq 快路径之前**、注释与实现相反（R8），且 40 层可能误拒合法深嵌套（R3） |
| 2 | `a474bf98` P1 传递 occurs（参考版） | ⚠️ | 两跳环主类已修（c1 由接受→分支不可达）；**VSub 嵌套丢外层 σ**、不跟随 meta 解、2048 预算按漏检处理（R2） |
| 3 | `503c3187` P9 诊断渲染 | ✅ | 参考版+孪生版已改；L08 迁移不完整（R5） |
| 4 | `2d73b66e` P3 第一刀（UnifyKind） | ⚠️ | 引入三档方向正确、真矛盾仍 Absurd；但 definite 列表不完整（R1） |
| 5 | `a70b5aaa` 孪生 P2 镜像 | ⚠️ | 镜像存在但**代理维度不同**（次数 64 vs 深度 40，R3） |
| 6 | `1e1562e4` parity 病理输入 | ⚠️ | **无耗时断言**，修复前两侧都 Err ⇒ 不会红（R14）；PR 表第 6 行描述错误（R16） |
| 7 | `0f8acc52` 孪生 P1 镜像 | ✅（含同缺陷） | 与参考版逐臂等价（含 VSub 缺陷同款；parity 因两侧同错而不可见，R2） |
| 8 | `a1f1bf36` parity 两跳环 | ⚠️ | 只在「参考已修、孪生未修」窗口有差分强度；基线两侧都接受 ⇒ 不是 P1 的绝对钉（R14） |
| 9 | `0c73b65d` P15 struct_eq pending（S1） | ✅ **真修** | 旧递归 oracle（`2309e2a4^`）证实丢的正是 pending 值比较；现比较 scrutinee/env/分支体/pending，缺省方向安全；回归钉反事实有效 |
| 10 | `691623f8` P3 第二刀 | ⚠️ | 方向保守（只缩不涨）；但把 solve/rename/invert 失败归 Undecided 后，配合不完整 definite 列表产生 S1 接受集回归（R1） |
| 11 | `75cad763` quote 迭代化 + pretty 截断 | ⚠️ | Sum/SumCase/Obj 三条深链逐分支等价、O(n)；Lam/Pi/Match 仍递归；`quote()` 的 VSub 臂 clone 而非 move；深值测试用 `ManuallyDrop` 泄漏、未覆盖端到端 Drop（R10/R11/R15） |
| 12 | `3221433e` Error 带可选 Span | ✅ | `Debug({:?})` 逐字节不变（黑盒有可执行证据）、`Display` 只打文案、`e.0` 老用法可用；twin 无 span 已文档化；字段 `pub` 属扩面非破坏 |
| 13 | `26108306` 解析错误带 span | ⚠️ | 文案契约不变 ✅；但语法错误 span 过粗（R6）、偏移基于预处理文本（R7） |
| 14 | `551ad1f2` σ 边界钉 + 计数/设计稿 | ✅ | 边界钉有效（只钉 decl 半边，R15）；设计稿 §10 已改掉 HashMap 旧口径；HEAD 的 README §8 计数与实际一致 |
| 15 | `30547abf` P5 跨 meta 环守卫 | ✅（限有界化） | 确定性、进出平衡、语义不变（仅剩确定性收益）；但 solve 仍可造环，RISKS 标「已修」偏乐观（R16） |
| 16 | `999d617f` P8 宽松合一收窄 | ✅ | 未登记名+非空 spine 改为 Undecided；构造点全量核对后**当前无程序级逃生舱**；判据仍是「名字登记」而非 provenance（未来风险，R13） |
| 17 | `86f431a4` with-K 文档警示 | ✅ | README §7.3 与设计稿同构；README §4.1/§7.2 仍有旧口径（R16） |
| 18 | `efbc9fa9` L08 P9 迁移 | ⚠️ | Pattern::pretty 一致；**漏迁** `no named implicit arg {:?}` 的 Span Debug 泄漏（L08 两引擎仍在，R5） |
| 19 | `3c6b656b` L08 P2 迁移 | ⚠️ | 与 L07 参考版同值同语义（40/深度）；**L08 孪生未镜像**（R4） |
| 20 | `d06d4c56` L08 P1 迁移 | ⚠️ | 与 L07 参考版逐字节同款；**L08 孪生未镜像**（R4） |

---

## 3. 发现清单（按严重度）

> 状态标记：**[实测]** = Lead 亲自运行/复现；**[代码]** = 已逐行核实（可复核）；**[未证]** = 路径已读通但反例未构造。

### R1 — S1：P3 分档不完整 ⇒ 合法空类型零臂 match 被拒（基线接受），且判定随冲突值形态不一致 **[实测]**

- 证据：
  - `unify_no_arm` 的 definite 集合只有 `SumCase×SumCase / Sum×Sum / LiteralIntro×LiteralIntro /
    SumCase↔LiteralIntro / U↔LiteralType`（`src/L07_sum_type/unification.rs:1232-1247`）；
    `Sum×LiteralType`、`U×Sum`、`Sum×Pi` 等**同为规范值且形态不同**的确定冲突仍落 `Undecided`。
  - 覆盖探测 `probe_accessible` 把非 `Absurd` 一律按**可达**处理（`pattern_match.rs:327-397`），
    `Undecided` 在无对应臂时产生「match 不完整：缺少构造子 c」（`:244-259`）。
  - 基线旧探测是 `unify_indices(...).is_ok() || infer.fuel_exhausted()`（`git show 641c52fe:src/L07_sum_type/pattern_match.rs:339-341`），
    旧 unify 对该冲突返回默认 `Err(UnifyError)`（旧 `unification.rs:1107`）且不烧 fuel ⇒ 探测判不可达 ⇒
    **基线接受**（未复跑旧版本，按代码路径确定）。
- Lead 复现（源见附录 A）：

  ```typort
  enum Nat { zero  succ(x: Nat) }
  enum Bool { true  false }
  enum T(A : U) { c -> T Nat }

  def ok1(e: T Bool):   Nat = match e { }   -- ref/twin 都 Ok（Bool≐Nat → Sum×Sum → Absurd）
  def bad1(e: T String): Nat = match e { }  -- ref=Err「match 不完整：缺少构造子 c」；twin=Ok
  ```

  `T String` 与 `T Bool` 语义上同为**空类型**（构造子 `c` 返回 `T Nat`，与 `String` 不相容），
  零臂 match 是合法的空类型消去 ⇒ 新版对 `T String` 的错误拒绝是**接受集回归**（S1：拒绝合法程序）。
  同时该用例在 L07 ref/twin 上已 **ref Err / twin Ok** —— 与 PR §4「P3 未镜像、parity 只比判定故不受影响」
  直接矛盾（见 R16）。
- 建议：①补全 definite 集合（「两侧都是规范值/规范类型头且形态不同」都应 Absurd），
  或②明确把「保守分档」作为接受集变化登记；③新增回归钉：Sum 形态与 LiteralType 形态各一条合法空类型零臂 match；
  ④把该输入加入 `l07_fast_parity`（即可抓到 P3 引起的 ref/twin 判定分裂）。
- 根因是 P3 第二刀（`691623f8`）+ definite 列表不完整，非 P15/P1/P2/P8 引入。

### R2 — S2（程序级可达则升 S1）：P1 `occurs_transitive` 的 `VSub` 臂丢弃外层 σ，P1 只是部分闭包 **[实测（单元级）]**

- 证据：`occurs_transitive` 的 `Val::VSub(inner, s2)` 臂执行 `go(inner, s2, …)`（`mod.rs:378-379`），
  而 `force/frcs` 的语义是 `frcs(outer, VSub(v, s2)) = frcs(compose(outer, s2), v)`（`mod.rs:884-888`，
  "内层先应用、外层后应用"）。嵌套 `VSub(VSub(·, s2_old), σ_new)` 时，经外层 σ_new 才解出的刚性变量
  会被漏查。
- Lead 单元探针（临时 integration test，已删除）：构造 σ={0↦7, 7↦9}、`v=VSub(VSub(Rigid(0), ∅), σ)`：
  按 force 语义 v 归约为 `Rigid(9)`，但 `occurs_transitive(v, 9)` 返回 **false**；单层 `VSub(Rigid(0), σ)` 则返回 true。
  ⇒ 函数语义与 force 组合语义不一致，P1 在「被多次包裹的槽值」上仍有漏环。
- 另两处已知不精确（有文档化的设计取舍，但应合并评估）：
  - `Flex/Decl/Prim` 臂只扫 spine、不跟随已解 meta 的值（`mod.rs:354-356`）——σ 环若经 meta 解值中转仍漏；
  - `BUDGET=2048` 耗尽按「未出现」（`mod.rs:336-341`）——>2048 节点的解值漏检；反向（`Rigid` 臂同时扫解值与
    spine 实参，`:343-353`）在「解值是丢弃实参的 λ」时可假报环、误拒合法分支，与「宁漏不误杀」取向不一致。
- 影响面：L07 参考版、L07 孪生版（`bump_spine_iter/subst.rs:304-420` 逐臂同款）、L08 参考版（`L08/mod.rs:325-400`
  逐字节同款）三处同病；parity 因两侧同错不可见。程序级可达性未构造（需要「嵌套依赖模式 + 外层 σ 先解 y、
  内层槽值被二次包裹」的输入）。另：pattern 头部精化写入点（`pattern_match.rs:722-725`）仍只有浅 occurs，
  有评审员提出同类链式环风险（**[未证]**，见 §5）。
- 建议：VSub 臂改为携带/组合外层 σ（`go(inner, &Subst::compose(sub, s2), …)` 或显式传双 σ）；
  把 Lead 探针转成正式 lib 单元钉；文档写明「VSub 槽内环目前不可检出」。

### R3 — S2：两处「卡住 match 预算」不是逐点同构（参考版深度 40 vs L07 孪生总次数 64），可构造双向判定漂移 **[代码]**

- 事实对照：

  | 维度 | 参考版 | L07 孪生版 |
  |---|---|---|
  | 常量 | `MATCH_CMP_DEPTH: u32 = 40`（`mod.rs:632`；L08 参考版 `L08/mod.rs:547` 同值） | `MATCH_CMP_BUDGET: u32 = 64`（`bump_spine_iter/unify.rs:36`） |
  | 维度 | 递归**深度**（进入 Match/Match 臂 +1、退出恢复） | 单次 `unify_iter` 内 Match/Match 臂**命中总次数**（局部变量，不恢复） |
  | 位置 | 臂**入口**、结构快路径**之前**（`unification.rs:1121-1131`） | 快路径**之后**计数（`bump_spine_iter/unify.rs:936-941`） |

- 可构造漂移（未实测）：
  - 孪生 Err / 参考 Ok：一次方程内 >64 个**兄弟**卡住 match 对（如 70 个 pending 实参各为 `g ai` vs `g bi`）；
  - 参考 Err / 孪生 Ok：41–64 层**合法**嵌套卡住 match（如 50 层嵌套 `match` 的 def）——参考版在深度 40 处
    `Undecided`+Err，孪生 50≤64 通过。这同时说明常量注释的论证（「超过该深度说明双方分支体在递归上互不相同」）
    对合法非递归深嵌套不成立（**S2 误拒面，[未证]**）。
- 文档：README §10「机制对齐/逐点同构」与 `L07-RISKS` §0.1 `P2′ ✅ 孪生版已跟修` 均未记录「代理维度不同、常量不同」；
  PR §4 的「孪生版只镜像 P2/P1/P9」也未提预算语义差异。改动单侧时 parity 现有负载抓不到（见 R14）。
- 建议：统一维度（孪生按路径恢复计数/给 `UItem` 带深度）或登记为已知偏差 + 把两侧构造用例加入 parity；
  同时修正常量注释口径。

### R4 — S2：L08 迁移只落参考版——L08 参考版/孪生版判定已分裂（c1 ref Err / twin Ok），`l08_fast_parity` 93 绿不构成一致性证明 **[实测]**

- 证据：`src/L08_product_type/bump_spine_iter/` 全目录 grep **无** `occurs_transitive` / `MATCH_CMP*`
  （`unify.rs:504-545` 仍是旧的 `val_mentions_lvl` 浅守卫）；只有 P9 的两处文案镜像（`bump_spine_iter/compiler.rs`）。
  `tests/l08_fast_parity.rs` 未新增 c1/c2 类用例。
- Lead 探针（附录 A）：c1 两跳环程序 → `L08::run` = Err「分支不可达：模式 refl(a) 与被匹配类型不相容」，
  `L08::bump_spine_iter::run_fast` = **Ok**。c2 在 L08 孪生侧无预算（未测，按代码即无 `MATCH_CMP_*`）。
- 影响：L08 孪生仍保留 P1 类健全性缺陷（接受循环 σ 的特化），且 L08 层的双 oracle 已不一致；
  「L08 已完成 P9/P2/P1 迁移」只能限定为**参考版**。PR §2.5 末尾虽提「以及 L08 孪生版镜像」未迁，
  但 §2.5 表头/§7.4 的表述容易被读成双引擎已同步（`l08_fast_parity` 93 绿加剧误读）。
- 建议：按 L07 模板镜像 P1（~125 行）/P2（~10 行）到 L08 孪生；或至少在 L08 README §6/§10 明确登记
  「孪生未镜像 P1/P2，c1/c2 判定分裂」，并把 c1 用例加入 L08 blackbox/parity（孪生侧单列计时）。

### R5 — S3：L08 的 P9 迁移不完整——`no named implicit arg {:?}` 的 Span Debug 泄漏仍在 L08 两引擎 **[代码]**

- 证据：L07 同码位已修（`src/L07_sum_type/elaboration.rs:64`、`bump_spine_iter/machine.rs:828`，`503c3187` 顺带修）；
  L08 两引擎仍是 `{:?}`：`src/L08_product_type/elaboration.rs:63`、`bump_spine_iter/machine.rs:813`
  → 用户可见 `no named implicit arg foo @ 12,15` 这类内部表示，与 L07 诊断口径分裂（LSP 接入后直接可见）。
- 建议：与 L07 同款改 `format!("no named implicit arg {}", name.data)`（参考版）/ `{name}`（孪生），补一条 L08 黑盒断言。

### R6 — S3：解析语法错误的 span 实际指向「失败 decl 的首 token」，与「失败 token 处」的声称不符；回归钉钉不住 **[实测]**

- 证据：`ParserExt::many1_sep` 的 EmptyVec 分支用 `i.first()`（剩余输入首 token）覆盖底层错误
  （`parser/mod.rs:84-97`）；首个 decl 失败时剩余输入是整份 token 表 ⇒ span = 文件首 token。
  Lead 实测 `"def f : Nat = )\n"`：`err.span()` = `(0,3)`，切出 `"def"`；`)` 在 `14..15`。
  残余 token 路径仍精确（`"println U ;"` → `(10,11)` 切出 `";"`，✅）。
- 测试缺口：`parse_error_carries_span`（`tests.rs:2095-2116`）只断言 `start<end`、`end<=len`、`path_id==0`，
  **不断言 span 内容**，因此位置错了也全绿。
- 建议：EmptyVec 分支保留底层 `IError`（有非零 span 优先用它）、EOF 用 `end_span()`；测试改为切片断言；
  若产品上接受「decl 级定位」，则改 PR/commit 声明并说明精度。

### R7 — S3：`Error::span` 偏移是「预处理后文本」坐标；注释中非 ASCII 字符使后续偏移前移（LSP range 会错位/切 UTF-8） **[实测]**

- 证据：`run` 先 `preprocess` 再 parse（`mod.rs:1907-1915`）；`preprocess` 把注释内非 ASCII 字符逐个替换为
  1 字节空格（`mod.rs:2112` 起，`:2138-2144/2150-2157`），`preprocess` 自己的注释已自认「后续偏移前移」
  （`:2106-2111`）。
- Lead 实测：`"// 中文注释\n\ndef x = U ;\n"` 的 leftover 错误 span=`(19,20)`，按原文本切片得到 `"f"`
  （正确 token `;` 在原文本 offset 27）；语法错误 span 也会切到中文注释中间。
  臂级 `pat_span` 同源受影响（模式 span 也来自预处理文本）。
- 影响：P10 的「LSP 前置」被高估——含中文注释的源（本仓测试语料大量存在）range 会错位甚至落在 UTF-8 中间。
- 建议：`preprocess` 保持字节长度（非 ASCII 注释字符按 `len_utf8` 个空格替换）或建立 offset 映射；
  补「中文注释 + 后续解析/臂级错误」回归钉；`Error::span` 文档写明偏移基准。

### R8 — S3：`MATCH_CMP_DEPTH` 检查在结构快路径**之前**，注释与实现相反；无 depth 边界钉 **[代码]**

- 证据：`unification.rs:1121-1131` 先查限、`:1133+` 才是 `struct_eq` 快路径；而 `mod.rs:625-632` 的注释宣称
  「结构快路径命中时根本不进这个预算」。后果：嵌套深度恰为 40 时，**字面相同的一对也会被直接判 Undecided**
  （与 R3 的参考版误拒面同源）；无 depth 39/40 + 快路径边界用例。
- 建议：先试快路径、失败再计/查深度；修正注释；补边界钉。

### R9 — S3：`UnifyKind` 的 note 不随 meta 快照回滚，旧 `Undecided/Fuel` 可污染后续真 `Absurd` 的终判 **[代码]**

- 证据：`note_unify_kind` 单调累积（`mod.rs:719-736`）；`flex_flex` 第一方向失败后 `meta_restore(snap)` 再反向重试
  （`unification.rs:765-807`，`:800` 为 restore 点），但 `unify_kind` 不在快照里 ⇒ 反向重试若命中真 `Absurd`，
  终判仍是 `Undecided`（放大 R1 的覆盖拒绝/文案失真）。
- 建议：`meta_restore` 一并恢复 kind 水位（或 flex_flex 重试前 `reset`）；补混合恢复路径单元钉。

### R10 — S3（残余风险）：`quote` 迭代化只覆盖 `Sum/SumCase/Obj`，`Lam/Pi/Match` 深链仍递归 **[代码]**

- 证据：`quote` 只把三种形态分派给 `quote_deep`（`mod.rs:1421-1434`），`quote_arm` 的 Lam/Pi/Match 仍递归。
  README §7.6b 已按形态限定，但 commit/PR 标题「quote 迭代化」与 `tests/l07_fast_parity.rs:8-10` 头注释偏宽。
  实际可达性低（深 Lam/Pi/Match 链难以由源程序构造），列为残余而非缺陷。

### R11 — S3（边缘）：`quote()` 的 `VSub` 分支由 move 改为 `Box::clone()`，与同 commit 的 move 纪律相反 **[代码]**

- 证据：`mod.rs:1428-1432` 现为 `Val::VSub(ref v, _) => { let inner = v.clone(); self.quote(decl, l, *inner) }`；
  旧版是 `*v` move。仅 `force` 返回顶层 VSub（fuel 耗尽）时可达；Rc 链为浅 clone，Box 链（Obj/Match）为递归深拷贝。
- 建议：改回 move 或按 `quote_deep` 的 `mem::replace` 纪律处理。

### R12 — S4：P5「已修」实为「有界化」；P8 判据仍是「名字登记」而非 provenance **[代码]**

- P5：`solve_with_pren` 仍无跨 meta occurs（`unification.rs:698-733`），m1:=?m2、m2:=?m1 仍可被创建，
  force 只是确定性停下；`L07-RISKS.md:37` 标「✅ 已修（环守卫）」应改为「环展开有界化」。
- P8：`loose_string`（`unification.rs:862-882`）判据是「名字是否在 decl 表登记」，且**已登记名分支完全忽略 spine**
  （用 `e.ty`）。当前构造点全量核对后无程序级逃生舱（安全），但属未来风险；P8 自己建议的 `Dynamic` provenance 标记未做。

### R13 — S4：文档/数字与声明漂移（可机械核验项） **[实测/代码]**

| 声明 | 实际 | 位置 |
|---|---|---|
| 全库 `cargo test --lib` **987** passed | **990** passed / 6 ignored / 81.85s | PR §5（`PR-l07-hardening.md:102`） |
| 「30 处已改 `Error::new`」 | 实际 **60 处 `Error::new` + 1 处带 span 二元构造**（参考 29 / 孪生 32） | PR §4（`:79`） |
| parity `1e1562e4`「修复前 run=Ok/fast=Err」 | 修复前**两侧都 Err**（256s / 26.3s，仅慢）；该描述属于 `0c73b65d` 的用例 | PR commit 表第 6 行（`:22`） |
| 「孪生只镜像 P2/P1/P9；P3/quote/pretty/Error span 未镜像，parity 只比判定故不受影响」 | P3 未镜像**不止文案**（探针可达性分档不同，已实测 ref Err/twin Ok，见 R1）；P5/P8 也未镜像且属语义面；L08 parity 还比较 Err 正文；quote/pretty 实际共享/本就迭代 | PR §4（`:83-84`） |
| `L07-RISKS §0.1`「P10/P11 ⏳ 未做」「P4–P8 ⏳」 | 同表上方已写 P10 🟢 / P11 ✅ / P4–P8 ✅，**自相矛盾**；P14 行仍写 lib 64/v3 111/parity 90（HEAD 实际 66/113/92） | `L07-RISKS.md:28-53` |
| L08 README 测试计数 | 仍写 lib **49** / parity **77**；迁移后实际 **60** / **93**；§6 已知偏差未登记「孪生未镜像 P1/P2、P9 span 泄漏、P3/P10/P11 未迁」 | `src/L08_product_type/README.md:266-284` |
| README §10 已知偏差 | 未记「参考版 depth 40 vs 孪生 count 64」这一语义差异 | `src/L07_sum_type/README.md` §10 |
| README §4.1「失败=分支不可达」/§7.2「(fuel exhausted) 尾注」/§6 表末行「quote/pretty 深路径残留」 | 分别已被 P3 三档、691623f8、§7.6b 处理，正文未回改（自相矛盾） | README 对应节 |
| `tests/l07_fast_parity.rs:8-10` 头注释「参考版递归 quote」 | 已迭代化（Sum/SumCase/Obj） | 头注释 |

### R14 — S4：回归钉强度不足/反事实偏弱 **[代码]**

- `parity_stuck_match_equation_bounded`（`l07_fast_parity.rs:568-592`）：**无耗时断言**；修复前两侧都 Err ⇒
  不会红，只让 suite 变慢（~4.7 分钟）；孪生侧没有任何 lib 级计时钉（参考版有 `tests.rs:225-228` 的 `<30s`）。
  即 `MATCH_CMP_BUDGET` 目前没有会红的回归钉。
- parity oracle 本身（`:50-65`）：只比「Ok 字节相等 / Err-Err 通过」，不比文案、类别、span、性能；
  对「两侧同错」零能力（基线 P1 就是共同 bug）。
- `parity_occurs_transitive_chain`（`:542-560`）：只在「参考已修、孪生未修」窗口有差分强度；基线两侧都接受 ⇒ 绿。
- `parity_struct_eq_match_pending`（`:503-539`）：修复前 ref=Ok/twin=Err ⇒ 真差分钉 ✅；但只断言「两版一致」，
  双版同时回归成 Ok 也会过（拒绝语义由 lib 测试钉住）。
- `test_occurs_check_keeps_legit_refinement`（`tests.rs:68-90`）：不触发新路径（首方程 acc 空、次方程两侧都是未解
  bare rigid ⇒ 前置筛选 false），**无法抓假阳性回归**。
- `parse_error_carries_span`：见 R6（不断言内容）。
- `visibility_boundary_decl_value_is_not_refined`（`:2126-2154`）：只钉 decl 缓存半边；README §1.3 还称
  「meta 解值也不可见」，无钉。
- `test_stuck_match_equation_bounded`（`:190-229`）：注释仍写「判定（分支不可达）与文案不变」，与断言
  「必须含无法判定/不含不相容」矛盾。

### R15 — S4：深值钉的端到端覆盖与 PR 声明 **[代码]**

- `deep_value_iterative_under_default_stack`（`tests.rs:1831-1916`）是普通 `#[test]`（默认约 2 MB 测试栈），
  实测证实「默认栈」声明成立；但输入值与返回 `Tm` 均 `ManuallyDrop` 泄漏（`:1866/1876/1882/1885/1899`），
  **只证明「遍历/打印不爆栈」**，不证明端到端安全：真实 `run` 的 println 路径（`mod.rs:1925`）的深 `Tm` 会在语句末
  Drop（Box 链递归 Drop；孪生 `entry.rs:287-291` 的 `CTm` 同）。README §7.6a 已列该残留，但 PR §3 表
  「10 万层深值 nf/错误显示 → 正常」应限定为「显示遍历不爆栈；释放仍递归 Drop，未解」。

### R16 — S4：其它 API/维护 nit

- `{:#?}` 下 `Error` 手写 Debug 与旧 derive 输出不同（多行 vs 单行）；仓内无使用，非现实漂移，但「逐字节不变」应限定 `{:?}`。
- `Span<T>` 的既有 `PartialEq` 只比 `data`（`src/parser_lib.rs:82-86`）⇒ 两个 `Span<()>` **恒等**（偏移不参与）；
  LSP 消费无碍，但「用 `assert_eq!` 钉 span」是 footgun（现有测试用 offset+切片，做法正确）。
- `quote_arm` 仍保留 `Sum/SumCase/Obj/VSub` 四个不可达臂（`quote()` 已分派）；`fuel_exhausted`（`mod.rs:715`）与
  `Walk::matched`（`pattern_match.rs`）已成死代码。
- `Error` 两个字段均 `pub`（旧字段 0 是私有的）属 API 扩面；`Span` 位于私有 `mod parser_lib`，但 `Tm/PatternDetail`
  早已暴露 `Span`，非本 PR 新增类别；外部 crate 不能命名该类型（LSP 同 crate 可用）。

---

## 4. 已验证为「好」的部分（避免误伤）

- **P15（struct_eq pending 值）是真修**：与旧递归 oracle（`git show 2309e2a4^`）对照，丢的正是 pending 值比较；
  现臂比较 scrutinee/env/分支体/pending，缺省方向 `false` 回落慢路径安全；两条 lib 钉 + parity 钉反事实有效。
- **UnifyKind 方向安全**：任何 kind 都是 Err，不存在「旧拒绝→新接受」路径；规范值冲突仍 Absurd（`test_unify_kind_...` 钉住）；
  solve/rename/invert 失败归 Undecided 在语义上正确（这些本就不是矛盾）。
- **P5 环守卫**：确定性（Vec 顺序）、进出平衡、环早退在 push 之前、保留剩余 fuel（测试反事实有效）。
- **P8 收窄**：未登记名+非空 spine 不再静默放行，构造点全量核对后当前无程序级逃生舱。
- **Error 载体**：`Display`/`Debug({:?})` 与旧版逐字节一致（`tests/l07_blackbox_v2.rs:112` 有可执行断言）；
  解析/臂级文案零漂移；L07 未接入 LSP、仓内无外部 `Error` 构造者 ⇒ 破坏性变化实际无受害者。
- **quote/pretty**：Sum/SumCase/Obj 三条深链与旧递归逐分支等价、O(n) 无复杂度退化；pretty 截断仅作用于显示层、
  既有 golden 零命中、判定侧无「截断造假」风险；100k 层深值在默认 2 MB 测试栈下通过。
- **测试/构建**：PR 中 L07/L08 各套件计数全部实测吻合；release 构建通过；merge 卫生干净。

---

## 5. 未能验证 / 建议后续实测（按优先级）

1. **R1 基线行为**：未复跑 `641c52fe` 旧版本确认 `bad1` 接受（按旧代码路径确定：旧探测 `is_ok()||fuel_exhausted()`
   + 默认 `Err`）。建议用 worktree 复跑一次留证。
2. **R2 程序级可达性**：需要「嵌套依赖模式 + 外层 σ 先解 y + 内层槽值被二次包裹」的源程序；未构造。
   建议先把 Lead 单元探针转正式 lib 钉（不依赖程序级）。
3. **R3 两个漂移构造**：70 个 pending 实参的兄弟对（预期 twin Err/ref Ok）与 50 层合法嵌套（预期 ref Err/twin Ok）；
   未跑。应作为修 R3 的验收用例。
4. **R8/参考版 40 层误拒**：41–64 层合法嵌套卡住 match 的可观测误拒；未构造。
5. **R9 污染触发路径**：flex-flex 第一方向失败（note Undecided/Fuel）后第二方向真 Absurd 的源程序；未构造。
6. **pattern 头部精化写入点是否可写链式环**（评审员提出，三实现共享）：嵌套依赖模式 + `VSub(bare y)` 看不穿；
   未构造，若成立则升级为 S1。
7. **L08 c2 孪生无预算的耗时**：未测（代码无 `MATCH_CMP_*`，按推理为分钟级）。
8. **深值端到端 Drop**：用 def 链 + `println` 在 2 MB 线程跑 `run`，确认是 quote/pretty 先过还是递归 Drop 先爆；
   未实测（测试用 ManuallyDrop 绕开）。
9. **`{:#?}` 反例**：未运行（仓内无使用）。
10. **P8 未来逃生舱**：未构造（当前无程序级路径）。

---

## 6. 修复建议（按优先级）

**P0（合并/推送前）**
1. **R1**：补全 `unify_no_arm` definite 集合（规范值/规范类型头形态不同 ⇒ Absurd）或明确登记接受集变化；
   补两条空类型零臂 match 回归钉；把该输入加进 `l07_fast_parity`（顺手抓 P3 ref/twin 分裂）。
2. **R4**：L08 孪生镜像 P1/P2（或登记已知偏差 + 加 L08 parity/blackbox 用例并明确「93 绿≠双 oracle 一致」）；
   同时修正 PR/README 的「L08 已完成迁移」口径。
3. **R3**：统一/登记预算语义，修正常量注释；至少给 `parity_stuck_match_equation_bounded` 加耗时断言（R14）。

**P1**
4. **R2**：`occurs_transitive` 的 VSub 臂组合外层 σ；加单元钉；文档写清预算/meta 的已知盲区。
5. **R6/R7**：解析错误 span 保留底层失败 token；`preprocess` 保持字节长度（或做 offset 映射）并补中文注释用例。
6. **R8/R9**：预算检查移到快路径之后；`meta_restore` 一并恢复 kind 水位；补边界钉。
7. **R5**：L08 两引擎修 `no named implicit arg {:?}`。

**P2**
8. R10/R11/R12/R13/R14/R15/R16：文档与数字同步（990/60+1/PR 表/ RISKS §0.1/L08 README/README §10 预算差异）、
   测试强度补强（span 内容断言、occurs 正向钉、parity 差分能力说明）、死代码清理、`quote` VSub 改回 move。

---

## 附录 A：Lead 探针源码（已删除，仅存档关键断言）

```rust
// 1) occurs_transitive 嵌套 VSub（集成到 #[path] 引入 L07 mod 的临时 test）
let empty: Rc<Subst> = Rc::new(Subst::default());
let s = Subst::extend(&Subst::extend(&empty, Lvl(0), rigid(7)), Lvl(7), rigid(9));
let nested = Val::VSub(Box::new(Val::VSub(Box::new(rigid(0)), empty.clone())), s.clone());
assert!(!s.occurs_transitive(&nested, Lvl(9)));       // 当前实现：漏检（force 语义应为 true）

// 2) F1 空类型零臂 match（run / run_fast 各跑一次）
// enum T(A : U) { c -> T Nat }
// def bad1(e: T String): Nat = match e { }   // ref=Err「match 不完整：缺少构造子 c」/ twin=Ok

// 3) span 定位
// "def f : Nat = )"            → err.span()=(0,3) 切片 "def"
// "// 中文注释\n\ndef x = U ;" → err.span()=(19,20) 原文本切片 "f"（应为 ";"）

// 4) L08 c1：L08::run=Err / L08::bump_spine_iter::run_fast=Ok
```

## 附录 B：分报告

| 文件 | 范围 | 最高级别 |
|---|---|---|
| `docs/review-l07-hardening-2026-11-08/findings-soundness.md` | unification/struct_eq/pattern_match/mod（7 commits 的健全性） | S1（F1=R1） |
| `docs/review-l07-hardening-2026-11-08/findings-twin-parity.md` | 孪生镜像、parity 守卫、L08 迁移 | S2（预算不同构、L08 双引擎分裂） |
| `docs/review-l07-hardening-2026-11-08/findings-eng-api-docs.md` | quote/pretty、Error/Span、解析 span、文档/计数 | S3（解析 span 定位与坐标） |
