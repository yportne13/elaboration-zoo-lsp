# L07 ⟷ L13「共有部分」实现差异 · 事实底稿与协作约定

> 用户问题：**L13 和 L07 共有的那部分实现，到底是不是同一份（一脉相承）？差异在哪、性质是什么？**
> 本目录是 2026-11-24 一轮**新**分析（HEAD `911628b3`，master，工作区仅 `tmp/` 未跟踪）。
> 上一轮 `docs/compare-l07-l13/`（L07..L13 逐层剖面，时点 `0464150c`/`8443586e`）可作背景，
> **但数字与结论必须在本轮代码上重新核**（那边已过期；DELTA.md 的 L12→L13 结论尤其要复核）。

## 0. 怎么定义「共有部分」

L07 = 和类型 + 依赖模式匹配（教学层，7199 行参考版 + 9051 行孪生）。
L13 = 命名空间/HDL/LSP 生产层（24946 行参考版 + 19111 行孪生 + 15270 行测试）。
两者**同路径文件 27 个**（L07 有 32 个 .rs，L13 有 62 个）。这些同路径文件就是名义上的"共有部分"：
值表示、NbE 内核、合一、模式编译、上下文、pretty、面板。

**关键提醒**：同路径 ≠ 同一份代码。本轮用「6-token shingle 保留率」量化：

## 1. 同路径模块清单（按双方 token 量降序）

口径：`src/**/*.rs` 去注释/去字符串后的 token；`jac` = 6-token shingle Jaccard（双方各占一半）；
`keep` = **L07 侧 shingle 有多大比例原样出现在 L13**（重命名会掉分，故另给 ident-norm 列：
把标识符统一替换为 ID 后再算，可按"结构同、名字不同"识别等价改写）。
复算脚本口径见 §7，原始数值 `tmp/l07l13_similarity2.tsv`。

| 同路径文件 | L07 tok | L13 tok | jac(文字) | jac(归一) | L07 保留(文字) | L07 保留(归一) |
|---|---:|---:|---:|---:|---:|---:|
| mod.rs | 17,243 | 46,810 | 10% | 28% | 26% | 57% |
| bump_spine_iter/machine.rs | 14,133 | 39,369 | 16% | 32% | 52% | 74% |
| parser/mod.rs | 5,303 | 35,004 | 11% | 21% | 67% | 88% |
| elaboration.rs | 7,217 | 32,711 | 9% | 22% | 42% | 75% |
| unification.rs | 9,605 | 10,641 | 20% | 36% | 36% | 56% |
| bump_spine_iter/entry.rs | 3,418 | 14,613 | 17% | 23% | 63% | 77% |
| bump_spine_iter/unify.rs | 6,366 | 9,138 | 29% | 42% | 54% | 70% |
| cxt.rs | 3,022 | 12,318 | **5%** | 16% | **19%** | 48% |
| bump_spine_iter/rename.rs | 6,419 | 6,387 | 60% | 72% | 76% | 86% |
| bump_spine_iter/force.rs | 4,824 | 5,650 | 13% | 27% | 25% | 49% |
| pattern_match.rs | 4,972 | 5,305 | 12% | 30% | **22%** | 48% |
| bump_spine_iter/compiler.rs | 4,434 | 5,679 | 13% | 30% | 28% | 55% |
| bump_spine_iter/prim.rs | 2,339 | 7,283 | 13% | 24% | 47% | 65% |
| bump_spine_iter/quote.rs | 4,635 | 4,212 | 41% | 50% | 56% | 67% |
| bump_spine_iter/eval.rs | 3,537 | 4,745 | 51% | 57% | 77% | 83% |
| pretty.rs | 827 | 7,023 | 5% | 12% | 34% | 54% |
| parser/syntax.rs | 820 | 3,705 | 12% | 26% | 51% | 66% |
| parser/lex.rs | 1,771 | 2,428 | 63% | 76% | **89%** | 95% |
| bump_spine_iter/syntax.rs | 1,834 | 1,680 | 60% | 61% | 70% | 69% |
| bump_spine_iter/spine.rs | 1,078 | 1,369 | 46% | 49% | 72% | 79% |
| surface.rs | 1,431 | 834 | 20% | 22% | 26% | 27% |
| bump_spine_iter/env.rs | 787 | 877 | **86%** | 85% | **98%** | 98% |
| shape.rs | 689 | 943 | 49% | 61% | 76% | 86% |
| bump_spine_iter.rs（根聚合） | 328 | 745 | 18% | 32% | 51% | 91% |
| bump_spine_iter/bench_src.rs | 262 | 701 | 44% | 58% | 95% | 99% |
| syntax.rs | 229 | 720 | 12% | 23% | 38% | 60% |
| raw_pretty.rs | 237 | 288 | 57% | 61% | 79% | 84% |

**读法（重要，别只抄数字）**：保留率高 = 确实是同一份代码被搬过去（lex/env/spine/rename/eval/raw_pretty/
shape/syntax(twin) 都在 70–98%）；保留率低 = 同角色但已重写（cxt、force、pattern_match、pretty、
surface、elaboration、mod）。**低保留可能是三件事之一**：①同机制重写；②L13 加了大量新功能把文件撑大；
③L07 在 11 月加固轮里改过、L13 没回灌。必须逐条分辨——这正是各分析员的核心工作。

## 2. 一侧独占的文件（"共有"的边界）

**只有 L07 有（L13 没有对应路径）**：
| 文件 | 字节 | 说明 |
|---|---:|---|
| struct_eq.rs | 16,125 | L13 无顶层 struct_eq（L09 起删）；L13 有 `struct_refine_probe.rs`（10,688），关系待查 |
| observe.rs | 13,951 | L13 顶层无 observe；**孪生侧**有 `bump_spine_iter/observe.rs`（60,342） |
| tests.rs | 65,750 | L07 层内 64 例；L13 用 17 个 `*_tests.rs`/probe 文件替代（15,270 行） |
| bump_spine_iter/struct_eq.rs | 17,005 | 孪生侧同删 |
| bump_spine_iter/subst.rs | 20,896 | σ 显式替换；**L13 已删**（精化载体回退到 update_cxt） |

**只有 L13 有（与共有部分同角色）**：`canonical.rs`、`typeclass.rs`、`eval_budget.rs`、
`struct_refine_probe.rs`、`parser/derive.rs`、`parser/macros.rs`、孪生 `compact.rs`/`debug.rs`/
`observe.rs`/`termination.rs`/`typeclass.rs`。

## 3. 血缘（git 事实，本轮已核）

- L13 是 **L12 的后代**（命名空间生产化），不是 L07 的直接拷贝；两者的"共有部分"是
  **L07 与 L13 各自迭代 5–6 代后的同名模块**。
- 2026-11 有一条**显式回灌线**：L07 的加固轮（P1–P11）与 L13 的观察面工作在**成对提交**里同步：
  `d12a8ed2 feat(L07): 源码注解渲染` ⟷ `a68605ff feat(L13): 源码注解渲染`；
  `6f7e245e feat(L07): 形状认回 decl` ⟷ `c824c43a feat(L13): 形状认回 decl`；
  `7a68abc7 chore(L07): 封印孪生` ⟷ `80f7cbc1 chore(L13): 封印孪生`。
  ⇒ **最近的做法是"选定的机制双向对齐"，而不是整层 copy-forward**。评估"一脉相承"必须按机制分档。
- L07 侧 11 月改动很密（`git log -- src/L07_sum_type`：Rc 值表示、Locals Rc、VSpan、PrimFunc、
  UNIFY_FUEL 覆盖、声明式缓存、加固 P1–P11 等）。L13 侧同期只有 LSP 观察面系列。
  ⇒ 时间轴上"谁抄谁"在同名文件里是**双向**的，不能假设 L13 是 L07 的超集。

## 4. 各分析员的分工与写作口径

| 文件（每人只写自己这一个） | 角度 | 覆盖文件 |
|---|---|---|
| `01-kernel-nbe.md` | NbE 内核（孪生） | `bump_spine_iter.rs` + `bump_spine_iter/{machine,eval,force,quote,rename,spine,env,syntax,bench_src}.rs` |
| `02-unify.md` | 合一/结构相等 | `unification.rs`、`bump_spine_iter/unify.rs`、L07 `struct_eq.rs`+`bump_spine_iter/struct_eq.rs`、L13 `struct_refine_probe.rs` |
| `03-cxt-refine.md` | 上下文与精化载体 | `cxt.rs`、`elaboration.rs`（σ vs `update_cxt`/`refresh`） |
| `04-match.md` | 模式匹配编译 | `pattern_match.rs`、`shape.rs`、`bump_spine_iter/compiler.rs` |
| `05-names-parser.md` | 名字世界/表面/解析 | `mod.rs`、`surface.rs`、`syntax.rs`、`parser/{mod,syntax,lex}.rs` |
| `06-observe-pretty.md` | 观察面与渲染 | `pretty.rs`、`raw_pretty.rs`、L07 `observe.rs`/L13 孪生 `observe.rs`、`surface.rs` 的契约 |
| `07-evidence.md` | 行为证据与门禁 | 测试套件对照、`.audit/raw-correctness`、预编译二进制差分、parity 覆盖 |

写作约定（沿用上一轮 CONVENTIONS.md，必要项复述）：
1. **只读**。不改 `src/`、不改别人的 md。
2. **禁止 `cargo build/check/test`**（整仓巨大，会长时间占住共享 `target/`）。允许：
   `git diff --no-index`、`git log`、grep、读文件、运行**已存在**的 `target/release/*.exe`。
   （注：上一轮文档里"F 盘 <1GB 禁止构建"已过期，现在是 26.5 GB；但仍然禁止构建，
   理由换成"共享 target + 时间成本"。）
3. 每条断言带锚点 `src/L13_namespace/xxx.rs:LINE`（两版都要给时写 `L07 …:LINE / L13 …:LINE`）。
4. 差异分级（每条差异必须落一档）：
   - **E0 逐字节相同**（或仅注释/格式差异）
   - **E1 等价改写**（改名、拆函数、换容器，语义应相同；要给出"为什么等价"的理由）
   - **E2 机制漂移**（同角色、不同机制，语义/行为**可能不同**；必须指出可观察后果）
   - **E3 缺失**（一侧有、另一侧没有）
   - **E4 单边新增**（L13 的新功能，不算"共有部分的差异"，但要在表里列出来避免误算）
5. 中文，表格优先，120–200 行。§末尾必须给：**本角度"一脉相承"评级**（强/中/弱/断 + 一句话理由）
   和 **Top-3 差异条目**（每条一行，带锚点，标注 E 档）。
6. 拿不准写 `[未核实]`，推断写 `[推断]`。**不要复述 README 当事实**（两版 README 都有过期数字）。

## 5. 分类判据：什么才算"共有的部分"

只有同时满足才算共有：**同一角色**（同样的抽象职责）+ **同一位置**（同路径/同模块）+ **两边都在用**
（不是死代码）。L13 独有特性（命名空间、HDL、prelude、typeclass、termination、eval_budget、
canonical、LSP）里，凡是被新代码路径**复用/改写**的旧机制（例如 `update_cxt` 用在 match 精化上），
算"共有部分的漂移"；完全新写的机制算 E4。

## 6. 已知的地雷（各分析员都请复核）

1. `pattern_match.rs:591` 附近有作者自注"L13 精化载体是 update_cxt，不是 σ/wrap_sub"——这是**语义断点**
   的第一手证据，请核对两侧对应位置的真实代码。
2. L07 有 `MATCH_CMP_BUDGET` / `UNIFY_FUEL` 等预算与守卫，L13 是否等价（`eval_budget.rs` 是不是替代品）？
3. 孪生两侧都被"封印"（不再参与默认门禁/parity）：`7a68abc7`、`80f7cbc1`。
   ⇒ 孪生层的差异**没有任何门禁会报警**，这本身是结论的一部分。
4. `mod.rs` 两侧都是巨兽（L07 2175 行 / L13 7749 行）：不要试图通读，用 `grep` 建符号表后**按机制**抽查。

## 7. 复算方法（Lead 的度量脚本口径）

- token：手写 Rust 扫描器，正确跳过 `//`、嵌套 `/* */`、`"…"`、`r#"…"#`、char/lifetime；
- shingle：连续 6 个 token 的串联串；`jac` = 交/并，`keep` = 交集大小 / L07 侧 shingle 数；
- ident-norm：标识符统一替换为 `ID`（关键字保留）。复算：`tmp/l07l13_similarity2.tsv`。
  **这只是筛子**：它只能说明"逐字保留了多少"，不能判断语义是否等价——那是分析员的工作。


## 8 勘误（分册核对后修正本底稿）

1. **§2 "L09 起删 struct_eq" 是错的**：L09/L10/L11/L12 都保留 `struct_eq.rs`（`L12_canonical/mod.rs:38`、`unification.rs:1253-1264` 在用），**L13 才是第一个没有它的层**（详见 `02-unify.md`）。
2. **§3 "L13 是 L12 的后代、两者的共有一部分是 L07 与 L13 各自迭代"这句要补方向**：解析器是 **L07 于 2026-09-05（`67273831`）向 L13 对齐**（`05-names-parser.md` §3.3）；`pretty/raw_pretty/surface` 家族是 **L06–L12 逐字节同、L13 才是离群点**（`06-observe-pretty.md` §2）。
3. **§6.3 "孪生层差异没有任何门禁会报警"说过头**：封印只封了 `lNN_fast_parity`（feature 默认关、编成空）；`tests/twin_engine_tests.rs` 仍逐条比对 L13 ref↔twin 诊断，且 **L13 孪生是 LSP 默认引擎**（`src/lib.rs:297-302`）。真正无人管的是 **L07 孪生**（`01-kernel-nbe.md` §6、`07-evidence.md` §4.3）。
4. **§6.2 的 PM_FUEL 前提不存在**：`grep -i pm_fuel` 在两章均为 0；真实预算是 `MATCH_CMP_BUDGET=64`+`UNIFY_FUEL=4096`（两侧同值）、`eval_budget` 是 L13 另一职责（`04-match.md` §4.3）。
5. **`fn-matrix.tsv` 有误配**：`quote_iter`/`machine::unify`/`infer_decl`/`pretty::go` 等为同名不同物，引用前请对照各分册给的"真配对"数值。
