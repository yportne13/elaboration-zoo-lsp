# L07–L12 多维并行评审 · 共同简报（BRIEF）

> 本文件是 6 个按**维度**切分的子 agent 的共同作业规范。全部评审为**只读**：
> 除自己的报告文件外不得写任何文件。主线 `F:/projects/hermes/elaboration-zoo-lsp`（master）。

## 0. 项目背景（必读）

`elaboration-zoo` 风格分层依赖类型语言实现。L13 是生产引擎，**L01–L12 是逐层
语言特性的独立实现**（教学/基准/互检）。本次评审范围：

- `src/L07_sum_type`（和类型，14.7k 行）
- `src/L08_product_type`（积类型，15.3k 行）
- `src/L09_mltt`（MLTT，12.6k 行）
- `src/L10_typeclass`（typeclass，15.5k 行）
- `src/L11_macro`（宏，18.4k 行）
- `src/L12_canonical`（canonical，18.8k 行）
- 对应测试：`tests/l07_*` … `tests/l12_*`

每层内部两套实现，须保持**双 oracle 一致**：

- **参考版**：`mod.rs` 的 `run(...)`（可读优先，递归求值）。
- **快版孪生**：`bump_spine_iter.rs` 的 `run_fast(...)`（bump arena、packed-word
  值表示、显式栈求值）。
- 判据：`tests/l{XX}_fast_parity.rs`（Ok 输出逐字节一致 / Err 判定一致；Err 文案
  里 Span 偏移与 `?N` meta 编号比对前归一化，属已文档化偏差）；
  `tests/l{XX}_blackbox*.rs` 锁对外行为契约。

### 关键历史（2026-09）

L07 完成"精化机制从事实表/上下文改写 → **显式替换**"重构（对齐 dpm-nbe），
随后按蓝本移植到 L08–L12（参考版+孪生版同批）。必读文档：

- `docs/l07-dpm-refactor-design.md` —— **§4 槽位纪律、§9 实现口径注记是评审必读**；
- `docs/l08-l13-refactor-plan.md` —— 各层移植口径与"删除清单"
  （`unify_pm` / `update_cxt` / `refresh` / `Infer.global` 应已不复存在）；
- `src/L07_sum_type/README.md` §1.2/1.3/4/5/6/10 —— 机制表述的权威口径；
- 最近提交：`2129975`(L11)、`58073dd`(L12) 显式替换移植；`dbe79cd` L10/L11/L12
  孪生版补齐精化燃料池（此前第三轮评审的 P1 修复）。

**刻意分歧是设计决定，不是 bug**：低层 `?0` 洞显示、构造子裸名别名"后注册者覆盖"、
归一化后的 Span/`?N` 偏差等被测试锁定。认为设计有问题就写 design-decision 讨论项，
不要当 bug 报。

## 1. 基线（orchestrator 已实测，2026-09-15）

- 6 个 parity 套件（l07~l12_fast_parity）**全绿**（退出码 0，L12 36 用例等）。
- 历史包袱：`docs/review-l01l12/` 是**显式替换重构之前**的旧架构评审，其发现
  可能已被重构消解，引用前必须核对当前代码。
- 环境坑：Git Bash 下 cargo 链接会被 coreutils `link` 劫持；禁止 `cargo clean`
  （F 盘紧张）。**本次评审一律禁止运行 cargo**，验证靠静态推理与读测试源码。

## 2. 严重度定义

- **P0**：内存安全 UB、用户可触发的崩溃/挂起、静默错误结果（soundness 破洞）。
- **P1**：明确逻辑错误、可达 panic、parity 裂缝、诊断错位。
- **P2**：稳健性/性能/可维护性的实质问题（非风格）。
- **P3**：nit、风格、命名、注释措辞。
- **needs-verify**：不能完全确证的怀疑（必须写明验证方法）。

## 3. 维度切分与报告文件

| Agent | 维度 | 报告文件 |
|---|---|---|
| D1 | 显式替换重构语义正确性（蓝本一致性） | `docs/review-l07l12/d1-subst-semantics.md` |
| D2 | unsafe / 内存安全（孪生版 packed-word 与 arena） | `docs/review-l07l12/d2-unsafe-memory.md` |
| D3 | 稳健性 / 全函数性（panic·溢出·燃料·发散） | `docs/review-l07l12/d3-robustness.md` |
| D4 | parity 与孪生/跨模块分叉 | `docs/review-l07l12/d4-parity-drift.md` |
| D5 | 性能与分配（含确定性） | `docs/review-l07l12/d5-performance.md` |
| D6 | 测试质量与文档准确性 | `docs/review-l07l12/d6-tests-docs.md` |

## 4. 硬约束

1. **只读评审**：除自己的报告文件外不得写/改任何文件；不得运行 cargo。
2. **证据优先**：每条发现必须给出 `文件:行号` + 代码证据；不许臆造。
   不能确定的标 needs-verify。
3. **诚实**：无发现就写"无 P0–P2 发现"，不为凑数制造伪问题。
4. **设计决定 vs bug**：被测试锁定/文档记载的偏差不报 bug。
5. git 只读命令（log/show/diff）可用，用于定位"修了一份没修其他份"。

## 5. 工作方法提示

- 六层大量文件**近乎逐字复制**（`bump_spine_iter.rs`、`unification.rs`、
  `pattern_match.rs`、`parser/lex.rs`…）。先精读 L07（蓝本），再用
  `diff`/`grep -F` 机械比对 L08–L12 的同名文件找分叉，不要线性通读 95k 行。
- `bump_spine_iter.rs` 单文件数千行：按结构采样 + 关键不变式定点核对。
- 报告用中文。

## 6. 报告格式（Markdown，固定小节）

```
# D<N> <维度名> — L07–L12 只读评审
## 1. 结论（verdict）
- P0: n  P1: n  P2: n  P3: n  needs-verify: n
- 覆盖范围与方法（读了哪些文件、用了什么机械比对）
## 2. 发现列表
### [P?] 标题（影响面：L07/L08/…/全部）
- 位置：`path:line`
- 证据：<代码/测试引用>
- 机制/影响：<为什么是问题，如何触发>
- 处置建议：<一句话>
## 3. needs-verify 清单（验证方法）
## 4. 设计决定讨论（不属 bug，只记录）
```
