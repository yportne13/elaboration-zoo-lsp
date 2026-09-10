# L01–L12 多轮评审 · 共同简报（BRIEF）

> 本文件是 5 个子 agent 的共同作业规范。每个 agent 只拥有自己的切片，禁止越界编辑。
> 工作树：`F:/projects/hermes/elaboration-zoo-lsp-review`（分支 `review/l01l12-perfect`）。
> 主线 `F:/projects/hermes/elaboration-zoo-lsp`（master）绝不能被修改。

## 0. 项目背景（必读）

这是 `elaboration-zoo` 风格的分层依赖类型语言实现，L13 是主引擎（含 namespace / HDL /
LSP），**L01–L12 是逐层语言特性的独立实现**，用来教学、基准与互检：

- `L01_nbe`：同一 NBE 算法 22 种表示/求值策略变体，独立 `l01bench` 基准。
- `L02_tyck`…`L12_canonical`：每层在前一层基础上加一个特性（类型检查 → 元变量 →
  隐式参数 → pruning → 字符串 → 和类型 → 积类型 → MLTT → typeclass → 宏 → canonical）。

多数 L 模块内部有两套实现，必须保持**双 oracle 一致**：

- **参考版**：`mod.rs` 的 `run(...)`（可读优先，递归求值）。
- **快版孪生**：`bump_spine_iter.rs` 的 `run_fast(...)`（bump arena、手写 packed-word
  值表示、显式栈/推土机求值）。
- 判据（写进 `tests/l**_**_fast_parity.rs`）：**Ok 输出逐字节一致 / Err 判定一致**；
  Err 文案里的 Span 偏移与 `?N` meta 编号在比对前归一化，属已文档化偏差。
- 另有 `tests/l**_blackbox*.rs` 锁定各层对外行为契约。

因此：**任何改动都必须保持 parity 与 blackbox 契约。** 刻意分歧（例如低层 `?0` 洞显示、
枚举构造子裸名别名"后注册者覆盖"、L13 专属的 no_metas 检查不回灌）是**被测试锁定的
设计决定**，不要"修"掉它们；若认为设计有问题，写进报告标为 design-decision 讨论项。

## 1. 现有基线（orchestrator 已测）

- `cargo check --lib`：通过（约 20s，复用主仓 target 目录）。
- L02–L12 全部 23 个集成测试 target：**全绿**（约 1600 用例，3m52s）。
- 已知无关问题：`cargo test --lib` 约 3 分钟后在 L13 的 legacy 测试区间
  `STATUS_ACCESS_VIOLATION` 崩溃 —— 属 L13，不在本次范围（可注明，勿改 L13）。
- 存在大量 `unused variable/import` 警告 —— 属本次可清理项（只清你自己切片的）。

## 2. 收敛判据（orchestrator 用）

一轮评审中，当且仅当以下条件全部满足，视为"该轮收敛"：

1. 5 个 agent 在本轮**自审切片**中报告 0 个 P0/P1/P2 问题（P3 级 nit 可保留，需明确列出）；
2. 轮转交叉审计（见 §5）中，对方切片报告 0 个 P0/P1/P2；
3. `cargo check` 通过，L02–L12 集成测试全绿，行为契约未被破坏。

收敛即终止；否则进入下一轮，重复直到连续一轮满足。**最多 3 轮**（token/时间预算），
3 轮后若仍有问题，如实报告未收敛项，不得谎称完美。

严重度定义：
- **P0**：内存安全 UB、可被用户程序触发的崩溃/挂起、静默错误结果（soundness 破洞）。
- **P1**：明确的逻辑错误、可达 panic、parity 裂缝、诊断错位。
- **P2**：稳健性/性能/可维护性的实质问题（非风格）。
- **P3**：nit、风格、命名、注释措辞。

## 3. 复核维度（每个 agent 都要覆盖自己的全部切片）

按重要性从高到低，逐项给结论（有/无/不适用 + 证据）：

1. **语义正确性**：eval/quote/force/unify/occurs-check/pattern-match/exhaustiveness 是否
   正确；参考版与快版是否真的等价；是否有 silently accept 的 ill-typed 项。
2. **内存安全与 unsafe 正确性**：packed-word tag 不变式（`v.0 & !7`、低 3 位 tag）、
   arena lifetime 擦除 transmute、`get_unchecked` 边界、bump 别名规则。每个 `unsafe`
   块应有 SAFETY 注释，且注释所述不变式必须真的成立。找**反例**。
3. **稳健性/全函数性**：`unwrap/expect/panic!/unreachable!/todo!`、切片下标、`as` 截断、
   整数溢出、递归深度/栈溢出、可触发死循环或发散。区分"仅内部不可达"与"用户可触发"。
4. **性能与分配**：O(n²)、无谓 `clone`/`to_string`/`format!`、重复遍历、每次分配、
   哈希表顺序不确定性是否会泄漏到输出。
5. **错误处理与诊断**：span 保真、错误文案、错误累积 vs 首错即停、恢复路径。
6. **API/封装/类型安全**：pub 面是否过大、不变式是否被类型编码、能否被安全 API 误用。
7. **可维护性/重复**：跨 L 模块的双胞胎代码重复（同一 bug 在多份拷贝里）、死代码、
   注释掉的代码、命名、`#[allow]` 掩盖的警告、模块头与代码是否一致。
8. **测试质量**：覆盖缺口、恒真断言、被 `#[ignore]` 的测试（原因？）、归一化是否掩盖
   真实分歧、缺少负例/边界例、测试是否只测了不会失败的分支。
9. **文档准确性**：`readme.md`/`README.md`/模块头/`mod.rs` doc comment 与代码是否一致，
   unsafe SAFETY 注释、已知偏差是否有记录。
10. **与 L13 的一致性**：有意移植缺口 vs 意外分歧；低层契约与 L13 行为的差异是否有据。

另可自由扩展：确定性、并发/线程模型（Rc 非 Send）、MSRV/wasm 构建、UTF-8 词法偏移、
资源上限（fuel/recursion bound）、`unsafe` 之外的 alias/UB 风险。

## 4. 切分与所有权（严格）

| Agent | 拥有（可编辑） |
|---|---|
| A1 | `src/L01_nbe/**`, `src/L02_tyck/**`, `src/L03_holes/**`, `tests/l02_*.rs`, `tests/l03_*.rs` |
| A2 | `src/L04_implicit/**`, `src/L05_pruning/**`, `src/L06_string/**`, `tests/l04_*.rs`, `tests/l05_*.rs`, `tests/l06_*.rs` |
| A3 | `src/L07_sum_type/**`, `src/L09_mltt/**`, `tests/l07_*.rs`, `tests/l09_*.rs` |
| A4 | `src/L08_product_type/**`, `src/L10_typeclass/**`, `tests/l08_*.rs`, `tests/l10_*.rs` |
| A5 | `src/L11_macro/**`, `src/L12_canonical/**`, `tests/l11_*.rs`, `tests/l12_*.rs` |

**共享文件，任何人都不得编辑**（发现问题只在报告里提，由 orchestrator 集中处置）：
`src/lib.rs`、`src/main.rs`、`src/list.rs`、`src/bimap.rs`、`src/parser_lib.rs`、
`src/parser_lib_resilient.rs`、`src/bin/**`、`src/prelude/**`、`src/L13_namespace/**`、
`Cargo.toml`、`rust-toolchain.toml`、`.github/**`、`docs/` 下非评审目录文件。

报告文件（仅自己写）：`docs/review-l01l12/a<N>-r<R>.md`、`docs/review-l01l12/a<N>-cross-r<R>.md`。
（A1→a1-…，A5→a5-…；不要写别人的报告文件。）

## 5. 轮次协议

- **第 1 轮**：各自审计自己的切片，**直接修复**确凿问题（最小 diff），写 `a<N>-r1.md`。
- **第 2 轮起**：各自 (a) 复验上轮改动、(b) 继续深挖自己切片、(c) **轮转交叉只读审计**
  下一个 agent 的切片（A1→A2→A3→A4→A5→A1），把交叉发现写进 `a<N>-cross-r<R>.md`；
  **交叉发现不得直接改别人文件**，由 orchestrator 转交所有者下一轮修。
- 每轮结束 orchestrator 统一 `cargo check` + 集成测试；编译错误按文件归属回退给所有者。

## 6. 硬约束

1. **禁止修改主线** `F:/projects/hermes/elaboration-zoo-lsp`。
2. **禁止运行 `cargo`（build/check/test/clippy/run）**：5 个 agent 并发会互相踩 target
   锁与半成品源码。编译/测试由 orchestrator 集中执行。需要验证语义时，只做**静态推理**
   与阅读测试源码。
3. **保持行为**：不得改变输出字节、错误判定、panic/Err 语义，除非你**证明**当前行为是
   bug 且给出触发用例。改测试断言必须有独立证据（新发现的真实 bug），否则视为破坏契约。
4. **最小 diff**：不做大重构、不重命名公共 API、不换依赖。风格清理仅限被警告且零风险的项。
5. **只改拥有文件**；报告写进指定文件。
6. **不许臆造**：每条发现必须给出 `文件:行号` + 代码证据。不能确定的标 "needs-verify"。
7. 诚实：无发现就写"无 P0–P2 发现"，不要为凑数制造伪问题。

## 7. 报告格式（Markdown，固定小节）

```
# A<N> Round<R> — <切片>
## 1. 结论（verdict）
- P0: n  P1: n  P2: n  P3: n  needs-verify: n
- 本轮是否收敛：是/否（判据见 BRIEF §2）
## 2. 发现列表
### [P?] 标题
- 位置：`path:line`
- 证据：<代码/测试引用>
- 机制/影响：<为什么是问题，如何触发>
- 处置：已修（diff 摘要）/ 仅报告 / needs-verify
## 3. 本轮改动清单（文件 → 一句话）
## 4. 需要 orchestrator 处置的事项（共享文件/跨切片）
## 5. 设计决定讨论（不属 bug，只记录）
```

## 8. 已知线索（起点，非穷尽）

- `unsafe` 集中在：packed-word 解引用 `&*((v.0 & !7) as *const XCell)`、
  `&mut *(p as *mut Vec<_<'static>> as *mut Vec<_<'a>>)` 生命周期擦除、
  lexer `get_unchecked(..ident_len)`。逐块核对不变式与 SAFETY 注释。
- `todo!()`：`L09_mltt/pretty.rs:52`、`L09_mltt/pattern_match.rs:581`、
  `L10/L11/…/typeclass.rs`（LiteralType/LiteralIntro/Prim 臂）、
  `L12_canonical/elaboration.rs:576`、`L11_macro/elaboration.rs:528`。
  判断这些臂是否**用户可达**。
- `//TODO:todo!()`：`L09_mltt/unification.rs:634`、`L10_typeclass/unification.rs:704`、
  `L11_macro/unification.rs:750`、`L12_canonical/unification.rs:799`（同一处拷贝 4 份）。
- 跨模块双胞胎：同一文件在多个 L 目录几乎逐字重复（`bump_spine_iter.rs`、`unification.rs`、
  `typeclass.rs`、`parser/lex.rs`…）。找"某一份修了、其他拷贝没修"的分叉。
- 大量 `unused variable/import` 警告。
```
