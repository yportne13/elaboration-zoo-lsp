# L01–L13 跨章节继承连贯性评审 · 共同简报（BRIEF）

> 本文件是 7 个子 agent 的共同作业规范。每个 agent 只拥有自己的切片，禁止越界编辑。
> 工作树：`F:/projects/hermes/elaboration-zoo-lsp`（master，直接在工作树修改，**不 commit**）。

## 0. 任务定位（与上一轮评审的区别，必读）

本项目是 elaboration-zoo 风格的分层依赖类型语言：`src/L01_nbe` … `src/L13_namespace`，
每层在**前一层完整代码拷贝**的基础上增量添加一个特性。因此任意相邻两层共享文件的
diff 应当**只包含新特性的演进**。

此前已完成的评审（`docs/review-l01l12/`，已合入 master）针对的是**各层内部的正确性
bug**。**本轮的任务不同：跨章节的"继承连贯性"**——

> 用户判据：整个项目连贯延续，**下一章节是在完整继承上一章节代码基础上做相关特性
> 演进的**。**重点关注性能版（快版孪生 `bump_spine_iter.rs`）**。

也就是说：一个优秀的改动（bug 修复、性能优化、护栏、诊断改进）如果只落在了部分章节
的对应文件里，其余章节的同源文件没有同步，就是**继承裂缝**，要找到并补齐。方向是
双向的：

- **正向继承缺口**：第 N 章有、第 N+1 章的同源位置却没有（N+1 没继承全 N）→ 补进 N+1；
- **优秀改动下沉**：第 N+1 章发现的通用修复/优化（尤其 L13 的），低层同源位置同样
  受益却没移植 → 评估后移植（移植判据见 §2）。

每条 diff 分类必须三选一：**演进**（新特性该有的差异）/ **裂缝**（补齐）/
**刻意分歧**（有测试或文档锚定的设计决定，保留并确保文档记录在案）。

## 1. 项目结构背景（必读）

- `L02_tyck`…`L12_canonical`：每层两层实现，必须保持**双 oracle 一致**：
  - **参考版** `mod.rs` 的 `run(...)`（可读优先，递归求值）；
  - **快版孪生** `bump_spine_iter.rs` 的 `run_fast(...)`（bump arena、packed-word 值
    表示、显式栈求值）——**这就是"性能版"，本轮重点**。
  - L06 起代码拆分为 `syntax.rs / cxt.rs / elaboration.rs / unification.rs /
    pattern_match.rs / pretty.rs / parser/`（参考版），快版仍集中在
    `bump_spine_iter.rs` 单文件。L13 另有 `bump_spine_iter/compact.rs`（arena 压实，
    commit d711fde，常驻 1835MB→429MB）。
  - `L01_nbe`：同一 NBE 算法的 22 种表示/求值策略变体（含多个性能变体），独立成篇。
- **parity 判据**（改动必须保持）：Ok 输出逐字节一致 / Err 判定一致；Err 文案里的
  Span 偏移与 `?N` meta 编号在比对前归一化，属**已文档化偏差**，不算裂缝。
- 测试锚点：`tests/l07..l13_fast_parity.rs`（快版 parity）；`tests/l02..l08_blackbox*.rs`
  （各层对外行为契约，l02–l06 的快版经 blackbox v2/v3 行使）；L13/LSP 侧还有
  `twin_engine_*`、`namespace_tests` 等。
- 基准 bin：`src/bin/l01bench.rs … l08bench.rs、l13bench.rs`（`#[path]` 直编译各层，
  与 typort 解耦）。**l09–l12 缺 bench bin**（由 A7 补）。
- 必读文档：`docs/review-l01l12/FINAL.md`（上轮修了什么、遗留什么——§3.3 列了 L13
  同族缺陷，先核对 master 现状再决定是否仍开放）、`docs/l13-to-low-layer-port-audit.md`
  （L13→低层移植判据与"不移植"清单）、本层 `readme.md`。

## 2. 移植判据（何时补、何时保留分歧）

移植一个改动前问三个问题：

1. **适用性**：该机制在目标层是否**可触发/有意义**？（例：L06 无 Match/pm 机制，
   unify/force fuel 无失控类可防 → 不移植，`l13-to-low-layer-port-audit.md` 已论证。）
2. **契约**：是否与该层**被测试锁定的公开契约**冲突？（例：低层 `?0` 洞显示、
   枚举构造子裸名"后注册者覆盖"、L13 no_metas 不回灌——这些是刻意分歧，不许"修"。）
3. **代价**：是否需要架构级重构（如上轮 SB 别名 P0）？需要专项验证的高危重构只记录，
   不盲改。

保留的刻意分歧必须在报告中列明锚点（测试名 / 文档行），并在本层 `readme.md` 的
已知分歧小节有一句话记录（没有就补一句，最小 diff）。

## 3. 复核维度（按优先级）

1. **快版孪生链连贯性（重点）**：对每对相邻层，`git diff --no-index src/LN/x.rs
   src/LN+1/x.rs`（快版与参考版都要），逐 hunk 分类演进/裂缝/刻意分歧。特别核对：
   - 上轮修复是否全链落地：`#[repr(align(8))]` + `align_of` 静态断言、全局哨兵
     `>= GLOBAL_BASE` 边界、η applicability 守卫（`v_applicable`/`vapp_ok`）、
     `prune_ty` 掩码反转、`intersect_go` 可恢复化、宏展开深度守卫（MacroDepthGuard）、
     trait 实例单向一阶匹配（`match_typ(goal, pattern)`）、`to_typ`/u64 字面量可恢复化。
   - L13 快版独有的性能机制（arena 压实 compact.rs、packed 布局优化、fuel、
     显式栈/推土机求值改进）中，哪些是**通用机制**可以下沉、哪些是 L13 专属
     （namespace/HDL/twin 引擎）不适用——逐项给出判断和证据。
   - L01 的性能变体结论（`readme.md`）与 L02+ 快版的选型是否一致延续。
2. **参考版链连贯性**：同上，对 `mod.rs`/`elaboration.rs`/`unification.rs`/
   `pattern_match.rs`/`pretty.rs`/`cxt.rs`/`syntax.rs`/`parser/`。
3. **历史改动扫描**：`git log --oneline --stat -- src/L13_namespace`（及各层）找
   "只落在单层"的 fix/perf commit（例：d4c05ea 只写 L10-L11、f51a0e4 只写 L11-L12、
   d711fde 只写 L13-twin），核对其余层同源位置现状。
4. **护栏/诊断一致性**：同类错误在各层的文案、span、恢复路径是否同族；护栏上限
   （宏深度、fuel、递归）数值与机制是否同源。
5. **文档与 readme**：模块头注释是否与代码一致；readme 是否如实记录该层与相邻层
   的差异及原因；上轮报告里的 P3 文档漂移是否残留。
6. **测试锚点连续性**：parity/blackbox 覆盖缺口（只评估+最小补齐，见各自任务书）。

严重度定义沿用：P0 内存安全/崩溃/挂起/静默错误；P1 逻辑错误/可达 panic/parity 裂缝/
诊断错位；P2 稳健性/性能/可维护性实质问题；P3 nit。

## 4. 切分与所有权（严格）

| Agent | 拥有（可编辑） | 评审继承对（按继承方向，N→N+1 由 N+1 的 owner 主审） |
|---|---|---|
| A1 | `src/L01_nbe/**`, `src/L02_tyck/**`, `src/L03_holes/**`, `tests/l02_*`, `tests/l03_*` | L01→L02, L02→L03 |
| A2 | `src/L04_implicit/**`, `src/L05_pruning/**`, `src/L06_string/**`, `tests/l04_*`, `tests/l05_*`, `tests/l06_*` | L03→L04, L04→L05, L05→L06 |
| A3 | `src/L07_sum_type/**`, `src/L08_product_type/**`, `tests/l07_*`, `tests/l08_*` | L06→L07, L07→L08 |
| A4 | `src/L09_mltt/**`, `src/L10_typeclass/**`, `tests/l09_*`, `tests/l10_*` | L08→L09, L09→L10 |
| A5 | `src/L11_macro/**`, `src/L12_canonical/**`, `tests/l11_*`, `tests/l12_*` | L10→L11, L11→L12 |
| A6 | `src/L13_namespace/**`, `tests/l13_*`, `tests/twin_engine_*` | L12→L13（+L13 快版深审、compact.rs 下沉评估） |
| A7 | 新文件 `src/bin/l09bench.rs`/`l10bench.rs`/`l11bench.rs`/`l12bench.rs`，`Cargo.toml`（只许追加 [[bin]] 条目） | 横切：全链快版连续性只读审计 + bench 连续性补齐 |

**共享文件，任何人都不得编辑**（发现问题只写报告，由 orchestrator 处置）：
`src/lib.rs`、`src/main.rs`、`src/list.rs`、`src/bimap.rs`、`src/parser_lib*.rs`、
`src/prelude/**`、`src/sim/**`、`src/client.rs`、`src/ls.rs`、`src/emit.rs`、
`src/config.rs`、`src/quick.rs`、`src/tutorial.rs`、`src/sampler.rs`、`src/bin/cli.rs`
及 A7 未拥有的其余 `src/bin/**`、`vscode_extension/**`、`.github/**`、README*。

报告文件（仅自己写）：`docs/review-continuity/a<N>-r<R>.md`。

**跨边界发现**（需要改邻居章节文件）：不得直接改，写进报告 §4"需转交"，由
orchestrator 下一轮转交对应 owner。

## 5. 硬约束

1. **禁止运行 `cargo`（build/check/test/clippy/run）**：并发 agent 会互踩 target 锁。
   编译与测试由 orchestrator 每轮集中执行。需要证据时只做静态推理 + 读测试源码 +
   只读 bash（diff/grep/git log/git show/wc）。
2. **禁止 `git commit`/`checkout`/`restore`**；不碰 git 状态。
3. **保持 parity 与行为契约**：不得改变输出字节、Err 判定，除非证明当前是 bug 且给
   触发用例；改测试断言必须有独立证据。
4. **最小 diff**：不做大重构、不重命名 API、不换依赖。移植改动要同源文件对齐贴齐
   （含注释风格），不要顺手重排代码。
5. **每条发现必须给 `文件:行号` + 证据**；不能确定的标 needs-verify，不许臆造。
6. **诚实**：没有裂缝就写"无"，不要为凑数制造伪问题。刻意分歧不算裂缝。
7. **快版（性能版）文件的任何改动，必须同步检查参考版同源位置**（反之亦然），
   两侧一致才算修完。

## 6. 报告格式（`docs/review-continuity/a<N>-r<R>.md`，固定小节）

```
# A<N> Round<R> — <切片>
## 1. 连贯性判定（verdict）
- 继承对逐对结论：LN→LN+1 连贯 / 有裂缝（列表）
- P0: n  P1: n  P2: n  P3: n  needs-verify: n
- 本切片是否收敛（0 个未处置 P0–P2）：是/否
## 2. 裂缝/分歧清单（逐条：位置、证据、分类[裂缝|刻意分歧|演进]、处置[已修|仅报告|转交]）
## 3. 本轮改动清单（文件 → 一句话）
## 4. 需 orchestrator 转交邻居章节的事项
## 5. 刻意分歧登记（锚点：测试名/文档行）
```

## 7. 收敛判据（orchestrator 用）

一轮收敛当且仅当：
1. 7 个 agent 自审切片 0 个未处置 P0–P2（P3 可留清单）；
2. 跨边界/横切交接项全部闭环（下一轮被转交方修复或论证不修）；
3. `cargo check --all-targets` 通过；`l0*_fast_parity`、`l0*_blackbox*`、
   `twin_engine` 相关测试全绿。
连续一轮满足即收敛；最多 3 轮，3 轮后如实报告未收敛项。
