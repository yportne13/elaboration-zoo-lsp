# L13 + 共享基础设施 多轮评审 · 共同简报（BRIEF）

> 本文件是 7 个子 agent 的共同作业规范。每个 agent 只拥有自己的切片，禁止越界编辑。
> 工作树：`F:/projects/hermes/elaboration-zoo-lsp-review-l13`（分支 `review/l13-shared-perfect`）。
> 主线 `F:/projects/hermes/elaboration-zoo-lsp`（master）**绝不能被修改**。

## 0. 为什么是这块（背景，必读）

本仓已经做过两轮评审，都已并入 master：

| 已完成 | 范围 | 报告 | 结论 |
|---|---|---|---|
| 第 1 轮 | `src/L01_nbe` … `src/L12_canonical` + 对应 tests | `docs/review-l01l12/`（21 份） | 5 agent × 3 轮，A1–A3 收敛，A4/A5 条件收敛 |
| 第 2 轮 | L01–L13 **继承连续性**（跨层一致性） | `docs/review-l01l12/*`、`cac125a`/`7f88a55`/`bb5fe18` | 6 agent × 3 轮，收敛 |

**从未被真正深挖的是 L13（48k 行主引擎）+ 共享基础设施**（本次范围）。第 1 轮的
`docs/review-l01l12/FINAL.md` §3.3 明确把 L13 同族缺陷列为"建议按同款补丁跟进"，
**其中一部分后来已修**（已核对：`bump_spine_iter/syntax.rs:253` 有 `#[repr(align(8))]`；
`parser/mod.rs:197-225` 有 `MacroDepthGuard`；`bump_spine_iter/rename.rs:808` 已 `.rev()`；
L13 已无 `intersect_go` 的 `unreachable!`）。本轮的职责是**独立复核这些"已修"是否真的
修对了**，并覆盖前两轮完全没看过的部分。

**本仓历史遗留的、需要回答的具体问题**（不是全部，是起点）：

1. `docs/review-l01l12/FINAL.md` §3.1 记录的 **[P0] Stacked Borrows 别名 UB 尚未修**，
   声称位置在 L10–L13 的 `bump_spine_iter` 整机重借路径。L13 版本请独立复核刻画是否成立。
2. 前 1 轮 §3.3 声称的 L13 同族缺陷，**逐条复核修复是否完整、是否只修了副本中的一份**
   （本仓特色：同一逻辑常有多份逐字拷贝，极易"修一漏三"）。
3. 本环境**没有 Miri**，所以 alias/UB 类问题只能做**静态刻画**，不得盲改（见 §6.3）。

## 1. 基线（Lead 已实测，2026-09-30，master@350b35a）

- `cargo check --all-targets`：**0 error / 3218 warning / 54.3s**（警告绝大多数来自
  `src/bin/*bench*.rs` 用 `#[path]` 交叉编译 L04–L12，**不在本次范围**）。
- 工具链：`rustc 1.98.1`、`edition 2024`、MSRV 1.87。
- 共享 `target/`：`CARGO_TARGET_DIR=F:/projects/hermes/elaboration-zoo-lsp/target`
  （磁盘仅剩 ~8 GB，**不要**新建 target 目录）。
- 基线测试结果见 `docs/review-l13/BASELINE.md`（Lead 会写入）。
- 已知历史问题：`cargo test --lib` 约 3 分钟后在 L13 legacy 段 `STATUS_ACCESS_VIOLATION`
  崩溃 —— **本次范围内**，是重点线索，见 §8。

## 2. 收敛判据

一轮评审中，当且仅当以下条件全部满足，视为"该轮收敛"：

1. 7 个 agent 本轮自审切片中报告 0 个 P0/P1/P2（P3 nit 可保留，需列出）；
2. 轮转交叉审计（§5）中，对方切片报告 0 个 P0/P1/P2；
3. `cargo check --all-targets` 通过，L13/LSP/HDL 相关测试全绿，行为契约未被破坏。

收敛即终止；否则进入下一轮，直到连续一轮满足。**最多 3 轮**。3 轮后若仍有问题，
如实报告未收敛项，**不得谎称完美**。

严重度定义：
- **P0**：内存安全 UB、用户程序可触发的崩溃/挂起、静默错误结果（soundness 破洞）。
- **P1**：明确的逻辑错误、可达 panic、两个引擎间的 parity 裂缝、诊断错位。
- **P2**：稳健性/性能/可维护性的实质问题（非风格）。
- **P3**：nit、风格、命名、注释措辞、文档行号漂移。

## 3. 复核维度（每个 agent 都要覆盖自己全部切片）

按重要性从高到低，逐项给结论（有/无/不适用 + 证据）：

1. **语义正确性**：eval/quote/force/unify/occurs-check/pattern-match/exhaustiveness/
   模块解析/命名空间解析是否正确的**反例**；参考版与快版是否真的等价；是否有 silently
   accept 的 ill-typed 项。
2. **内存安全与 unsafe 正确性**：packed-word tag 不变式（`v.0 & !7`、低 3 位 tag）、
   arena lifetime 擦除 transmute、`get_unchecked` 边界、bump 别名规则、`&mut` 重借。
   每个 `unsafe` 块应有 SAFETY 注释，且**注释所述不变式必须真的成立**。找反例。
3. **稳健性/全函数性**：`unwrap/expect/panic!/unreachable!/todo!`、切片下标、`as` 截断、
   整数溢出、递归深度/栈溢出、可触发的死循环或发散。区分"仅内部不可达"与"用户可触发"。
4. **性能与分配**：O(n²)、无谓 `clone`/`to_string`/`format!`、重复遍历、每次分配、
   哈希表顺序不确定性是否泄漏到输出（**本仓特别关注：输出字节稳定性**）。
5. **错误处理与诊断**：span 保真、错误文案、错误累积 vs 首错即停、恢复路径。
6. **API/封装/类型安全**：pub 面是否过大、不变式是否被类型编码、能否被安全 API 误用。
7. **可维护性/重复**：**跨副本分叉**（同一逻辑在多份拷贝里"修一漏三"是本仓头号风险）、
   死代码、注释掉的代码、`#[allow]` 掩盖的警告、模块头与代码是否一致。
8. **测试质量**：覆盖缺口、恒真断言、`#[ignore]`（原因？）、归一化是否掩盖真实分歧、
   缺少负例/边界例、测试是否只测不会失败的分支。
9. **文档准确性**：`readme.md`/`README.md`/模块头/doc comment 与代码是否一致，
   SAFETY 注释、已知偏差是否有记录。
10. **与 L01–L12 的一致性**：有意移植缺口 vs 意外分歧；低层契约与 L13 行为的差异是否有据。

另可自由扩展：确定性、`Rc` 非 Send 的线程模型、MSRV/wasm 构建（`wasm32-wasip1-threads`）、
UTF-8 词法偏移、资源上限（fuel/recursion bound）、`unsafe` 之外的 alias/UB 风险。

## 4. 切分与所有权（严格，禁止越界）

| Agent | 拥有（可编辑） |
|---|---|
| **A1** | `src/L13_namespace/{elaboration,cxt,pattern_match,canonical,pretty,syntax}.rs`、`src/L13_namespace/{calc_tests,class_tests}.rs` |
| **A2** | `src/L13_namespace/{unification,typeclass}.rs`、`src/L13_namespace/bump_spine_iter/{unify,typeclass,observe,quote,rename,compact,force,eval,prim}.rs`、`tests/{l13_fast_parity,trait_system_tests,trait_nat_param_tests}.rs` |
| **A3** | `src/L13_namespace/bump_spine_iter.rs`、`src/L13_namespace/bump_spine_iter/{machine,spine,env,syntax,entry,compiler,debug,bench_src}.rs`、`src/L13_namespace/{prim_safety_tests,debug_test}.rs`、`tests/{twin_engine_tests,twin_engine_bench}.rs` |
| **A4** | `src/L13_namespace/mod.rs`、`src/L13_namespace/legacy_tests.rs` |
| **A5** | `src/prelude/**`、`src/emit.rs`、`src/sim/**`、`src/L13_namespace/{hdl_assert_tests,hdl_blackbox_tests,hdl_check_graph_tests,hdl_enum_tests,hdl_fsm_tests,hdl_stream_fix_tests,verilog_compat_tests,struct_refine_probe}.rs`、`examples/hdl/**`、`tests/{hdl_check_locations,emit_tests,sim_tests}.rs` |
| **A6** | `src/L13_namespace/parser/**`、`src/L13_namespace/{module_tests,module_probe_tests}.rs`、`src/{parser_lib,parser_lib_resilient,list,bimap}.rs`、`tests/{namespace_tests,cross_file_tests,impl_goto_tests,macro_goto_tests,parser_error_tests,implicit_comma_args,repro_sumcase_panic}.rs` |
| **A7** | `src/{lib,lsp_stdio,client,ls,config,main,tutorial,quick,sampler,pmab_gen}.rs`、`src/bin/**`、`src/doc/**`、`src/format/**`、`tests/{lsp_protocol_robustness,completion_tests,completion_handler_tests,hover_tests,hover_stress,format_handler_tests,docgen_tests,config_tests,large_did_open_no_hang,test_rope_offset,println_two_phase_tests,quick_cheatsheet_tests,known_bug_pins,zz_tmp_l13_debug}.rs` |

**共享文件，任何人都不得编辑**（发现问题只写进报告的 §4"需要 orchestrator 处置"）：
`src/L01_nbe/**` … `src/L12_canonical/**` 及其 `tests/l0*`/`l1*`（已评审过）、
`Cargo.toml`、`Cargo.lock`、`rust-toolchain.toml`、`.github/**`、`vscode_extension/**`、
`README.md`、`README.zh.md`、`docs/**` 下除 `docs/review-l13/` 之外的文件、
`tests/{l02..l12}_*.rs`、`tests/twin_engine_tests.rs` 之外的 `tests/*`（未在本表列出的）。

报告文件（仅自己写，仅自己这一份）：`docs/review-l13/a<N>-r<R>.md`、`docs/review-l13/a<N>-cross-r<R>.md`。

**注意**：`src/L13_namespace/mod.rs` 是唯一声明 `mod *_tests;` 的地方（如 `mod.rs:335
mod verilog_compat_tests;`）。**不要新增测试文件**；把新测试加进已有的测试文件里，
或者放进你拥有的文件内的 `#[cfg(test)] mod tests`。

## 5. 轮次协议

- **第 1 轮**：各自审计自己的切片，**直接修复**确凿问题（最小 diff），写 `a<N>-r1.md`。
- **第 2 轮起**：各自 (a) 复验上轮改动、(b) 继续深挖自己切片、(c) **轮转交叉只读审计**
  下一个 agent 的切片（A1→A2→A3→A4→A5→A6→A7→A1），写进 `a<N>-cross-r<R>.md`；
  **交叉发现不得直接改别人的文件**，由 orchestrator（Lead）转交所有者下一轮修。
- 每轮结束由 Lead 统一 `cargo check --all-targets` + 相关测试；编译错误按文件归属回退给所有者。

## 6. 硬约束

1. **禁止修改主线** `F:/projects/hermes/elaboration-zoo-lsp`。所有改动只落在
   `F:/projects/hermes/elaboration-zoo-lsp-review-l13`（分支 `review/l13-shared-perfect`）。
2. **禁止自己运行 `cargo`（build/check/test/clippy/run）**：7 个 agent 并发会互相踩 target
   锁与半成品源码（共享同一个 `CARGO_TARGET_DIR`，磁盘只剩 8 GB）。编译/测试由 Lead
   集中执行。需要验证语义时，只做**静态推理**与阅读测试源码。
3. **保持行为**：不得改变输出字节、错误判定、panic/Err 语义，除非你**证明**当前行为是
   bug 且给出触发用例。改测试断言必须有独立证据（新发现的真实 bug），否则视为破坏契约。
4. **最小 diff**：不做大重构、不重命名公共 API、不换依赖。风格清理仅限被警告且零风险的项。
   **不要**去清 `src/bin/*bench*.rs` 交叉编译产生的 L04–L12 警告（不在范围）。
5. **只改拥有文件**；报告写进指定文件。
6. **不许臆造**：每条发现必须给出 `文件:行号` + 代码证据。不能确定的标 "needs-verify"。
7. **unsafe/UB 类问题在没有 Miri 的情况下不得盲改**：刻画清楚 + 给最小复现 + 标
   needs-verify / 设计讨论，比盲改一个正在工作的依赖类型语言实现安全得多。
8. 诚实：无发现就写"无 P0–P2 发现"，不要为凑数制造伪问题。

### 6.5 工具注意事项（重要）

- **读中文文本一律用 `read`/`grep` 工具，不要用 `Get-Content`**：本机 PowerShell 是 5.1，
  默认按 GBK 解码，会把 UTF-8 中文显示成乱码（文件本身没问题，别误报）。
- 用 `grep` 工具搜索（不要 `Select-String`），用 `glob` 工具找文件（不要 `find`/`Get-ChildItem -Recurse`）。
- **绝对不要碰 `node_modules`**（`vscode_extension/**/node_modules` 有上百 MB）。

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

- **`cargo test --lib` 在 L13 legacy 段 `STATUS_ACCESS_VIOLATION` 崩溃**（历史记录，
  Lead 正在复现）。这是**用户不可触发但开发者必踩**的崩溃，优先级最高。先确认还能不能复现、
  定位到哪个测试/哪行代码。
- **§3.1 的 Stacked Borrows 整机重借 UB**：`unify` 取 `let mach_ptr = self` 后解构字段
  `&mut`，在字段借用存活时 `unsafe { (&mut *mach_ptr).solve_multi_trait_ref(..) }` 重建整机
  `&mut` 并写 `metas`。L13 的对应位置在 A2/A3 交界，**A3 主查、A2 会签**。
- `todo!()`：L13 是否还有？（前轮列的是 L09/L10/L11/L12，L13 待查）
- `unsafe` 密度最高的 L13 文件：`mod.rs`(44)、`machine.rs`(17)、`entry.rs`(5)、
  `unify.rs`(5)、`typeclass.rs`(3)、`prim.rs`(1)、`rename.rs`(1)。逐块核对不变式与 SAFETY 注释。
- 本仓特色风险：**同一逻辑多份逐字拷贝**（L04–L13 各有一份 `bump_spine_iter.rs`、
  `unification.rs`、`typeclass.rs`、`parser/lex.rs`）。找"某一份修了、其他拷贝没修"的分叉。
  已知一处：前轮修的 `prune_ty` 掩码反转、哨兵 `>= GLOBAL_BASE`、`Synth` 假匹配
  （`match_typ` 单向匹配）—— 请确认 L13 是否对齐。
- **双引擎（参考版 vs 快版）**：`src/lib.rs` 的 `Engine::{Reference,Twin}` 路由与
  `twin_can_own` 归属闸；LSP 默认走 twin，`cargo test` 默认走参考版 ⇒ **测试覆盖偏向参考版**，
  快版的正确性主要靠 `tests/l13_fast_parity.rs` 与 `tests/twin_engine_tests.rs` 钉住。
- `src/L13_namespace/mod.rs` 里有一批以 `test_n1..n11` 命名的测试，其中
  `test_n6_checked_ret_cache_unsoundness`、`test_n7_sentinel_unreachable`、
  `test_n8_n9_n10_n11_doc_only`、`test_n3_vals_eq_ground_doc_only` 名字里直接带
  "unsoundness"/"doc_only" —— 这些很可能是**被记录但没有真正钉住**的已知问题，重点查。
- `src/prelude/**` 是 `.typort` 源（HDL 库在其中：Verilog 生成是 prelude 库函数
  `designVL`，不是 Rust），`src/emit.rs` 是取文本的通道。
- 前轮报告 `docs/review-l01l12/FINAL.md` §3.4 的 needs-verify 清单，L13 部分请逐条复核。
