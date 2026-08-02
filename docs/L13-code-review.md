# L13_namespace 代码审查报告

> 复审日期：2026-08-01（基于当前 master 代码，行号已与代码同步更新）
> 本文档由两次审查合并：初版审查 + 2026-08-01 复审新增发现（见 §12）。

## 1. 总体概览

L13_namespace 是整个 elaboration-zoo 项目的**主入口模块**，实现了完整的依赖类型语言 "Typort"，包括：

- 依赖类型系统 (Π 类型、宇宙、元变量)
- 归纳类型 / 和类型 / 积类型
- GADT 模式匹配 (含穷尽性检查)
- 隐式参数推断
- Typeclass / Trait 系统
- 宏系统
- 命名空间 / 包系统
- HDL Verilog 代码生成
- LSP 服务器集成 (hover, completion, diagnostics, rename)

### 代码规模（2026-08-01 实测）

| 文件 | 行数 | 职责 |
|------|------|------|
| `mod.rs` | 4639 | 核心类型定义 (`Tm`, `Val`, `Infer`) + eval/quote/force + 测试 |
| `elaboration.rs` | 1777 | 类型推断/检查引擎 |
| `unification.rs` | 917 | 统一算法 + trait 求解 |
| `pattern_match.rs` | 1270 | 模式匹配编译 (决策树 + 穷尽性) |
| `typeclass.rs` | 516 | Typeclass 求解器 |
| `cxt.rs` | 681 | 上下文管理 + 内置函数 |
| `pretty.rs` | 284 | 美化打印 |
| `canonical.rs` | 141 | IDDFS 项合成 |
| `syntax.rs` | 80 | 语法辅助类型 |
| `parser/mod.rs` | 2580 | 解析器主逻辑 |
| `parser/lex.rs` | 398 | 词法分析器 |
| `parser/syntax.rs` | 283 | 解析器 AST 类型 |
| `parser/macros.rs` | 270 | 宏匹配/转录 |
| `parser/derive.rs` | 362 | Derive 宏展开 |
| `legacy_tests.rs` | 3135 | 遗留测试（80+ 用例） |
| `debug_test.rs` | 103 | 调试测试 |
| `struct_refine_probe.rs` | 285 | GADT refinement 探针 |
| **总计** | **~17,721** | |

> 注：`debug_cut_test.rs` 已从模块中移除（初版审查时存在）。

---

## 2. 架构设计评价

### 优点

1. **增量式架构**: L01→L13 的分层设计清晰，每个模块引入一个语言特性，便于理解和测试。
2. **无 unsafe 代码**: 除 `lex.rs` 的 2 处 `get_unchecked` 外，核心逻辑全部是安全 Rust。
3. **持久化数据结构**: 使用 `List<T>` (Rc 共享链表) 实现持久化环境/脊，避免深拷贝。
4. **Rc 共享而非 Box**: 类型别名 `type Rc<T> = Arc<T>`，所有 `Val`/`Tm` 通过 `Arc` 共享，减少内存分配。
5. **错误累积**: elaboration 支持累积多个错误而非首个即停（`accumulated_errors`）。
6. **LSP 集成**: `Infer` 结构体内置 `hover_table`、`completion_table`，设计合理。
7. **prelude 缓存**: `PRELUDE_CACHE` (OnceLock<Mutex>) 缓存预编译的 prelude 状态，测试/CLI 提速显著 (126s→3.9s debug)。

### 架构缺陷

1. **`mod.rs` 过于臃肿**: 4639 行中约 2900 行是测试代码，核心定义 (~1700 行) 仍偏大。`DeclTm`、`Tm`、`Val`、`Infer`、`Closure`、`PatternDetail` 全部挤在一个文件。
2. **`Infer` 结构体职责过重**: 同时承担求值、引用、强制、统一、trait 求解、内存分析、LSP 数据收集——是典型的 God Object。
3. **`run()` 和 `run_with_prelude()` 代码重复**: 两函数的声明处理循环几乎完全相同 (各约 40 行，见 §4.1)。
4. **递归无栈保护**: `eval()`、`quote()`、`rename()`、`unify()`、`compile_aux()`、`pretty_nat()` 均为深度递归，无显式栈或 trampoline 机制（见 §3.3）。

---

## 3. 关键问题清单

### 3.1 可能导致 panic 的代码（含 2026-08 复审新增）

| 位置 | 严重度 | 问题 |
|------|--------|------|
| `unification.rs:792-805` + `mod.rs:1147` | **高(新增)** | **eta 展开 panic**：unify 的 `(_, Val::Lam(..))` / `(Val::Lam(..), _)` 分支对任意非函数值调用 `v_app`，`Sum` 等值落入 `panic!("impossible apply")`。**用户可触发**：类型错误（期望 lambda 得到 sum 值）崩溃整个进程而非报错 |
| `elaboration.rs:946` | **高** | `todo!()` — `ImplDecl` 非 Def 方法的 `need_create` 分支直接 panic |
| `elaboration.rs:1182/1185` | **高** | `Derive`/`Class` 变体直接 `panic!`，期望在 elaboration 前被展开 |
| `mod.rs:1147` | **中** | `panic!("impossible apply")` — eval 中遇到意外值 |
| `mod.rs:1172` | **中** | `panic!("impossible")` — `v_app_pruning` 中 env/pruning 不匹配 |
| `mod.rs:1181` | **中** | `panic!("var {:?} not found")` — eval 中 `Tm::Var` 越界 |
| `mod.rs:1196/1201` | **中** | `panic!("impossible")` / `.unwrap()` — `Tm::Obj` 字段访问时 typ 不是 Sum 或字段不存在 |
| `cxt.rs:224/236/252/277` | **中** | 文件 I/O 函数 `unwrap_or_else(panic!)` — 文件操作失败直接崩溃 |
| `cxt.rs:191` | **中(新增)** | `get_global` 双 `unwrap()` — `write().unwrap()` + `get().unwrap()`，访问未 `create_global` 的 key 直接 panic |
| `cxt.rs:315-395` | **中** | 所有 `add_builtin().unwrap()` — 内置注册失败直接 panic |
| `parser/mod.rs:461` | **中** | `x.parse::<u64>().unwrap()` — 无效数字字面量 panic |
| `typeclass.rs:404/426` | **中** | `panic!("Too much effort :(")` / `panic!("Cannot resume with empty subgoals")` |
| `typeclass.rs:460` | **中** | `class_instances.get(...).unwrap()` — 未注册的 trait panic（当前触发路径有前置检查，脆弱） |
| `pretty.rs:224-226` | **低(新增)** | `panic!` — `SumCase` 的 typ 不是 `Tm::Sum` 时（pretty 阶段） |
| `unification.rs:151/223/231/404/433/704` | **低** | `unreachable!()` — 内部不变量违反 |
| `mod.rs:283-285` | **低(新增)** | `lvl2ix` 无保护减法 `l.0 - x.0 - 1` — level 不一致时 debug 下溢 panic / release 下回绕 |

### 3.2 昂贵的克隆操作

| 位置 | 严重度 | 问题 |
|------|--------|------|
| `elaboration.rs:708` | **高** | `self.clone()` — 克隆整个 `Infer` 状态用于错误恢复 (IDDFS 闭包) |
| `elaboration.rs:629` | **高** | `self.meta.clone()` — 克隆整个元变量向量用于 Nat 默认化 |
| `parser/mod.rs:1073/2209` | **高** | `state.1.clone()` — 每次宏展开克隆整个宏 HashMap |
| `cxt.rs:439-453` | **中** | `clone_without_src_names()` — 克隆 Cxt 的全部字段 |
| `elaboration.rs:1203-1342` | **中** | hover table 推送中 `cxt.decl.clone()` + `cxt.locals.clone()` 重复 10+ 次 |
| `unification.rs:855-864` + `mod.rs:1359-1368` | **中(新增一处)** | Match 统一/重命名/quote 中重建整个 decl HashMap (每 case 一次，O(decl×case)) |
| `elaboration.rs:1023-1024` | **低(新增)** | `trait_definition.get(...).cloned()` — 每个 ImplDecl 克隆全部 trait 方法 Raw |

### 3.3 递归栈溢出风险

| 函数 | 风险 | 说明 |
|------|------|------|
| `Infer::eval()` | **高** | 深度嵌套项 (Let 链、Match) 无栈保护 |
| `Infer::quote()` | **高** | 与 eval 对称，同等深度 |
| `rename()` | **高** | 对每个 Val 变体递归，Match 有嵌套递归 |
| `pretty_nat()` | **高(新增)** | 递归深度 = 数字大小；`def x = 1000000` 的 pretty/quote 会递归 100 万层崩溃（`count_nat` 是迭代的，两处不一致） |
| `unify()` | **中** | 仅 Decl 情况有 fuel 限制 (100)，其他情况无限递归 |
| `compile_aux()` | **中** | 深度嵌套模式可导致深度递归 |
| `check_pm ↔ infer_expr_pm` | **中** | 互递归，App 链可导致深度调用 |
| 宏展开递归 (parser) | **中(新增)** | `p_raw` 宏展开后递归调用自身，**无深度限制**——自引用宏（如 `macro_rules a { ($x: raw) => { a $x } }`）无限递归栈溢出，LSP 场景可被用户触发 |

### 3.4 TODO / 技术债务

| 位置 | 内容 |
|------|------|
| `canonical.rs:18/38` | `//TODO: this is incorrect` — `avoid_recurse` 参数逻辑有误 |
| `unification.rs:734` | `//TODO: a temp fix for test_user_provided, but I dont think this fix is correct` |
| `elaboration.rs:763` | `//TODO:vt may be wrong` |
| `elaboration.rs:822` | `//TODO: need to check the basic ret is this sum type or not` |
| `elaboration.rs:1359` | `//TODO:below may be wrong` |
| `elaboration.rs:1538` | `//TODO: universe need to consider cases?` |
| `elaboration.rs:392/398` | `//TODO:revPruning?` (出现 2 处) |
| `typeclass.rs:322` | `//TODO:` — Match 比较逻辑未完成 |
| `pattern_match.rs:388` | `//TODO:check patcon is clean` |
| `mod.rs:1438/1607` | `//TODO: do not print err. return error` — run 函数错误处理 |
| `mod.rs:64/67/70` | `DeclTm::Enum/Trait/TraitImpl` 内部字段标记 `//TODO:` |
| `mod.rs:1556` | magic number：`if id == 3` 注册 `nat_to_dec`，依赖 prelude 数组顺序 |
| `parser/mod.rs:457` | `//TODO:do not unwrap` — Type 级别数字解析 |

---

## 4. 代码重复分析

### 4.1 高严重度重复

| 重复项 | 位置 | 影响 |
|--------|------|------|
| `infer_expr_pm` vs `infer_expr` 的 `Raw::App` 处理 | `elaboration.rs:192-270` vs `1373-1452` | ~80 行近乎完全相同，仅 `check_pm` vs `check::<false>` 不同 |
| `run()` vs `run_with_prelude()` 声明处理循环 | `mod.rs:1442-1481` vs `1611-1650` | 两个 ~40 行重复的 match arms |
| hover table 推送模式 | `elaboration.rs` 全文 | 同一 4 参数模式重复 10+ 次，应提取为方法 |
| decl table 重建 | `unification.rs:855-864` vs `mod.rs:1359-1368` | Match 重命名/统一/quote 中完全相同的 boilerplate |
| `HoverCxt::names()` vs `Cxt::names()` | `cxt.rs:81` vs `455` | 相同的内部 `go()` 函数 |

### 4.2 中等重复

| 重复项 | 位置 |
|--------|------|
| `val_match` vs `vals_eq_ground_impl` | `typeclass.rs:208-276` vs `283-333` |
| Where-clause 处理 | `parser/mod.rs:1115-1181` vs `1288-1338` |
| `collect_app_args` / `collect_app_args_trait` | `parser/mod.rs:1156` vs `1315` |
| Class 展开 let-binding 链 | `parser/mod.rs` 中 3 处 |
| 测试中 Nat/Bool/Vec 定义 | `legacy_tests.rs` 中内联 ~12 次 |

---

## 5. 死代码与未使用导入（2026-08 验证）

| 位置 | 项目 |
|------|------|
| `mod.rs:48-51` | `enum BD { Bound, Defined }` — 从未使用（已确认） |
| `mod.rs:64-71` | `DeclTm::Enum/Trait/TraitImpl` 空变体（已确认） |
| `mod.rs:1` / `elaboration.rs:3` / `unification.rs:1` | `use colored::Colorize` — 所有彩色输出已注释（已确认） |
| `legacy_tests.rs:1991` | `test_hdl_slice_assign` 缺少 `#[test]` 属性，永远不会运行（**仍然存在**） |
| `parser/macros.rs:128` | `RepetitionOp` 枚举定义但从未使用（已确认） |
| `parser/macros.rs:8` | `OwnedTokenSlice` 类型别名未使用（已确认） |
| `parser/mod.rs:1735-1806` | 大块注释掉的 `p_macro_transcriber_sequence` 函数 |

---

## 6. 错误处理模式评估

| 模式 | 使用情况 | 评价 |
|------|---------|------|
| `Result<T, Error>` + `?` | elaboration, unification, cxt | ✅ 良好 |
| `UnifyError` 三变体 | unification | ✅ 区分 Basic/Stuck/Trait |
| `accumulated_errors` | elaboration | ✅ 错误累积而非首个即停 |
| `Option<Rc<Val>>` | 内置函数 (cxt) | ✅ None = 不适用 |
| `panic!` for "impossible" | eval, force | ⚠️ 应使用 `unreachable!` 或返回 Result |
| `todo!()` | elaboration:946 | ❌ 生产代码不应有 `todo!()` |
| `panic!` on I/O error | cxt:224-277 | ❌ 应返回 `Result` |
| `panic!` in typeclass | typeclass:404/426/460 | ❌ 应传播错误 |
| `panic!` on parse failure | parser/mod.rs:461 | ❌ 应使用 `?` 或返回 Result |
| `unwrap_or(cxt)` 吞错误 | elaboration.rs:176 (`check_pm_final`) | ❌(新增) 分支最终 unify 失败被静默降级 |

---

## 7. 安全性审查

### 7.1 unsafe 代码

`lex.rs:194-197` 和 `lex.rs:221-223` 使用 `get_unchecked` 进行标识符切片。虽然当前逻辑保证了安全性 (先检查前缀匹配)，但这种优化是脆弱的——如果词法逻辑变更，可能导致 UB。建议改用安全的 `get(..len)` 替代。

### 7.2 并发安全

- `mutable_map` 使用 `RwLock`，但错误处理为 `.ok()?` 和 `if let Ok(mut x) = ...` — 锁中毒时静默忽略；`get_global` 则直接 `write().unwrap()` 会 panic。
- `Infer` 实现了 `Clone`，但内部 `Arc` 共享意味着克隆后的实例共享元变量状态；`mutable_map` 在普通 `clone()` 中**共享同一个 RwLock**（仅 `run_with_prelude` 缓存路径做深拷贝）——IDDFS 错误恢复闭包里的 Infer 与主实例共享可变状态。
- `Infer::clone()` 重置 `accumulated_errors`（mod.rs:399）——有意的设计，但 clone 用于错误恢复时语义需注意。

---

## 8. 性能关注点

| 问题 | 位置 | 影响 |
|------|------|------|
| `self.clone()` for error recovery | `elaboration.rs:708` | O(n) 克隆整个 Infer 状态，频繁发生 |
| 宏展开克隆 HashMap | `parser/mod.rs:1073/2209` | O(macro_count) 每次展开 |
| Nat 默认化保存/恢复 meta | `elaboration.rs:626-663` | O(meta_count) |
| Match 引用重建 decl table | `unification.rs:855-864` / `mod.rs:1359-1368` | O(decl_count) per case per Match |
| trait_wrap 全量扫描 | `elaboration.rs:1652-1720` | O(traits × methods) |
| IDDFS 搜索 | `canonical.rs` | 指数级分支 × 深度，有 effort limit 兜底 |
| `unify` 中 Decl 展开 | `unification.rs:765-778` | 每步 quote+eval 整个定义体 |

---

## 9. 测试质量

| 维度 | 评价 |
|------|------|
| 测试数量 | 80+ 遗留测试（legacy_tests.rs）+ 模块内测试，覆盖良好（HDL、GADT、trait、supertrait、where、证明） |
| 测试组织 | ❌ 缺乏模块化，所有测试内联在 mod.rs 和 legacy_tests.rs |
| 测试数据重复 | ❌ Nat/Bool/Vec/Eq 等定义在 ~12 个测试中重复 |
| 无断言的测试 | ⚠️ `debug_cut_test`（已删除）、`summary`、部分探针无断言 |
| 死测试 | ❌ `test_hdl_slice_assign` 缺少 `#[test]`（legacy_tests.rs:1991，仍未修复） |
| 测试排序 | ❌ test0-test8 不按数字顺序排列 |
| 负面测试 | ✅ 有穷尽性检查、refutable pattern、错误恢复等负面测试 |
| prelude 一致性 | ✅ prelude_tests 模块检查每个 prelude 文件可解析 + 整体可类型检查 |

---

## 10. 改进建议 (优先级排序)

### P0 — 必须修复（含 2026-08 复审新增）

1. **消除 eta 展开 panic**（`unification.rs:792-805`）：eta 分支先检查值是否可应用（Lam/Flex/Rigid/Decl/Obj/Call），否则返回 `UnifyError::Basic`。这是最容易被用户触发、后果最严重的 panic。
2. **`preprocess` 跳过字符串字面量**（`mod.rs:1661-1694`）：`"http://x"`、`"a//b"` 等字符串中的注释标记被破坏，需在替换前识别并跳过 `"..."` 字面量。
3. **消除生产代码中的 `todo!()` 和 `panic!("impossible")`**：`elaboration.rs:946` 的 `todo!()` 应替换为正确的错误返回或明确的 `unreachable!()`。
4. **I/O 函数返回 Result**：`cxt.rs` 的文件操作函数和 `get_global`（cxt.rs:191）不应 panic，应传播错误或优雅返回。
5. **数字解析 panic**：`parser/mod.rs:461` 的 `parse::<u64>().unwrap()` 应使用 `?` 或 graceful error。
6. **宏递归加深度上限**（`parser/mod.rs:1050-1097`）：自引用宏可无限递归栈溢出。
7. **`pretty_nat` 改迭代实现**（`pretty.rs:271-284`）：大 Nat 打印/quote 栈溢出。

### P1 — 应该修复

8. **`prelude_aliases` 确定性**（`mod.rs:1561-1571`）：短名冲突依赖 HashMap 迭代顺序，同名短名解析结果不确定；应按 key 排序或冲突报错。
9. **`check_pm_final` 错误传播**（`elaboration.rs:176`）：`unwrap_or(cxt)` 吞掉分支最终 unify 错误，应向上传播或至少记录。
10. **错误累积时 meta 回滚**（`elaboration.rs:550-556`）：分支检查失败后 meta 已部分 solve，后续分支在污染状态上继续；应在分支边界快照/回滚。
11. **`run`/`run_with_prelude` 的 stdout 污染**（`mod.rs:1439-1447, 1606-1610`）：`println!` 直接输出声明名/解析错误/分隔线，应改走日志或返回值。
12. **`update_by_cxt` 补全或删除**（`syntax.rs:53-67`）：`Locals::Bind` 分支用 `Val::U(0)` 硬编码占位，是半成品。
13. **提取 hover table 推送为方法**：消除 10+ 处重复的 `(span, span, HoverCxt{...}, val.clone())` 模式。
14. **合并 `run()` / `run_with_prelude()`**：提取共享的声明处理循环。
15. **合并 `infer_expr_pm` 和 `infer_expr` 的 App 处理**：提取共享的 App 推断逻辑为内部函数。
16. **替换 `colored::Colorize` 导入**：三个文件中未使用的导入应移除。
17. **修复 `test_hdl_slice_assign`**：添加 `#[test]` 属性或删除（legacy_tests.rs:1991）。
18. **为 `canonical.rs` 的 `avoid_recurse` TODO 提供正确实现**：当前标记为 "incorrect"。

### P2 — 建议改进

19. **拆分 `mod.rs`**：将 `DeclTm`/`Tm`/`Val`/`Infer`/`Closure` 拆分到独立子模块。
20. **拆分 `Infer`**：使用 trait 或组合模式分离求值、引用、统一、trait 求解、LSP 收集。
21. **为递归函数添加栈保护**：考虑 trampoline、迭代加深、或显式栈。
22. **测试数据提取为共享 fixtures**：创建 `test_helpers` 模块定义 Nat/Bool/Vec 等。
23. **`lex.rs` 的 `get_unchecked` 改为安全版本**：性能差异微乎其微。
24. **typeclass 求解器错误处理**：将 `panic!("Too much effort")` 改为返回 `Result`。
25. **`lvl2ix` 加保护**：`mod.rs:283-285` 无保护减法，level 不一致时下溢。
26. **替换 `Lvl(u32::MAX)` dummy**（`elaboration.rs:442/446`）：若泄漏到 quote 会 `lvl2ix` 下溢 panic。
27. **`trait_definition` 巨型 tuple 类型重构**（`mod.rs:372`）：可读性差、易错。
28. **`file_exists` 返回 Bool 而非 String**（`cxt.rs:261-270`）：语义怪异。

---

## 11. 总结

L13_namespace 是一个**功能非常完整**的依赖类型语言实现，在 ~17.7K 行代码中涵盖了从词法分析到 Verilog 代码生成的全栈。核心类型理论实现 (eval/quote/force/unify) 遵循标准的 NbE (Normalization by Evaluation) 方法论，架构在学术层面是合理的。prelude 缓存、错误累积、决策树编译优化（1f7bf7a、1dc49ce）都体现了良好的性能意识。

主要技术债务集中在：
- **错误处理不一致**: 混用 Result、panic、todo、unreachable；最严重的是 unify eta 展开的用户可触发 panic
- **确定性缺陷**: `preprocess` 破坏字符串字面量、prelude 短名注册依赖 HashMap 迭代顺序、宏递归无深度限制
- **代码重复**: App 推断、声明处理循环、hover 推送、decl 表重建等多处复制粘贴
- **God Object**: `Infer` 结构体承担过多职责
- **栈安全**: 深度递归无保护（eval/quote/pretty_nat/宏展开）
- **~15 处标注为 "incorrect" 或 "may be wrong" 的 TODO**: 表明统一/elaboration 的某些边界情况尚未完全解决

---

## 12. 2026-08-01 复审新增发现（相对初版）

### P0（用户可触发崩溃 / 确定性错误）

| # | 位置 | 问题 |
|---|------|------|
| 1 | `unification.rs:792-805` + `mod.rs:1147` | **eta 展开 panic**：unify 的 `(_, Val::Lam(..))` 分支对任意非函数值调用 `v_app`，`Sum` 等值落入 `panic!("impossible apply")`。类型错误（期望 lambda 得到 sum 值）导致进程崩溃而非报错 |
| 2 | `mod.rs:1661-1694` | **`preprocess` 不识别字符串字面量**：`"http://x"`、`"a//b"`、`"a/*b*/c"` 中的注释标记被当注释替换，字符串内容被破坏 |
| 3 | `mod.rs:1561-1571` | **prelude 短名注册依赖 HashMap 迭代顺序**：同名短名（如多个 `mk`）冲突时 `or_insert` 先到先得 → 同名解析结果不确定 |
| 4 | `parser/mod.rs:1050-1097` | **宏递归无深度限制**：自引用宏无限递归 → 栈溢出（LSP 场景可崩溃服务器） |
| 5 | `pretty.rs:271-284` + `mod.rs:1514-1520` | **大 Nat 打印/quote 栈溢出**：`pretty_nat` 递归深度 = 数字大小（`count_nat` 是迭代的，两处不一致） |
| 6 | `cxt.rs:187-195` | **`get_global` 双 `unwrap`**：访问未 `create_global` 过的 key 直接 panic |

### P1（逻辑缺陷 / 静默错误）

| # | 位置 | 问题 |
|---|------|------|
| 7 | `elaboration.rs:176` | **`check_pm_final` 的 `unwrap_or(cxt)` 吞掉最终 unify 错误**：分支返回类型与目标不一致时静默降级 |
| 8 | `syntax.rs:53-67` | **`update_by_cxt` 半成品**：`Locals::Bind` 分支用 `Val::U(0)` 硬编码占位，`Define` 分支逻辑被注释 |
| 9 | `elaboration.rs:550-556` | **错误累积模式下的 meta 污染**：分支失败后 `self.meta` 已部分 solve，后续分支在污染状态上继续 |
| 10 | `mod.rs:1439-1447, 1606-1610` | **`run`/`run_with_prelude` 大量 `println!` 直接打 stdout**：CLI 输出被污染；若 LSP 走此路径会破坏协议 |
| 11 | `parser/derive.rs:28-31` | **未知 derive trait 静默忽略**：`#[derive(UnknownTrait)]` 无任何报错 |
| 12 | `mod.rs:1188-1207` | **`eval` 中 `Tm::Obj` 字段查找多处 `.unwrap()`/panic** |
| 13 | `mod.rs:283-285` | **`lvl2ix` 无保护减法**：level 不一致时 debug 下溢 panic / release 回绕 |

### P2（设计风险）

| # | 位置 | 问题 |
|---|------|------|
| 14 | `mod.rs:394` | `Infer::clone` 共享 `mutable_map`（RwLock）：IDDFS 错误恢复闭包与主实例共享可变状态 |
| 15 | `unification.rs:1388-1429` | `unify_catch` 失败后已 solve 的 meta 不回滚，错误累积模式下影响后续检查 |
| 16 | `mod.rs:1359-1368` + `unification.rs:855-864` | quote/rename/unify 中 `Val::Match` 每 case 重建整个 decl HashMap |
| 17 | `mod.rs:1556` | magic number `id == 3` 注册 `nat_to_dec`，依赖 prelude 数组顺序 |
| 18 | `elaboration.rs:442/446` | 用 `Lvl(u32::MAX)` 作 dummy Rigid，若泄漏到 quote 会 `lvl2ix` 下溢 |
| 19 | `mod.rs:372` | `trait_definition` 巨型嵌套 tuple 类型，可读性差 |
| 20 | `cxt.rs:261-270` | `file_exists` 返回 `String`（"true"/"false"）而非 Bool，语义怪异 |
| 21 | `mod.rs:399` | `Infer::clone` 重置 `accumulated_errors`（有意设计，但 clone 用于错误恢复时需注意） |

---

## 13. Val::Call 专项审查（2026-08-01）

> 范围：`Val::Call` 的完整数据流。由于 `Call.body` 恒为 `Val::Match`（见不变量），分析同时覆盖 `Val::Match`。

### 13.1 设计与数据流

- **定义**（`mod.rs:258-260`）：`Val::Call(SmolStr name, List<(Rc<Val>, Icit)> args, Rc<Val> body)` — 内联函数调用值。
- **产生**（`wrap_match_in_call` mod.rs:295-319 → eval mod.rs:1248-1257）：`def` 的 body 若形如 `x => ... => match ...`，最外层 Match 被包装成 `Lam(x, ..., Call(f, [x...], Match))`。eval 时只有 body 求值为 `Val::Match`（scrutinee 卡住、无法归约）才保留 Call，否则直接返回归约结果。
- **消费**：`force`（mod.rs:1045-1052，只 force body）、`v_app`（mod.rs:1146，应用参数递归到 body）、`unify`（unification.rs:734-747，同名快速路径 + 剥层比 body）、`rename`（unification.rs:366-371）、`quote`（mod.rs:1338-1342）、`typeclass::vals_eq_ground`（typeclass.rs:324-330）。

### 13.2 问题清单

| # | 严重度 | 位置 | 问题 |
|---|--------|------|------|
| C1 | **高** | `mod.rs:1146-1147` | **`v_app` 对 Call/Match 应用参数 → panic**：`Val::Call` 分支递归 `v_app(body, u)`，body 恒为 `Val::Match`，而 Match 不在 `v_app` 分支中 → 落入 `panic!("impossible apply")`。**对任何 Call/Match 值应用参数 = 100% panic**，且类型检查因 meta 推断放行（见复现） |
| C2 | **中** | `unification.rs:734-742` | **unify 快速路径只比 args 不比 body**（作者自标 `//TODO: ... not correct`）：依赖"同名函数必有同 body"不变量（def shadowing 时破坏）；`unify_sp` 失败后已 solve 的 meta 不回滚，带污染状态继续比较 body |
| C3 | **中** | `pattern_match.rs:1205-1215` | **`eval_aux` zip 截断**：`params.iter().zip(item_pats.iter())`（`.filter(Expl)` 被注释）。常规场景因 prepend 反转位置对齐而安全；**用户显式绑定隐式参数并在 body 引用时**（`case cons[l=lll](x, xs) => lll`）→ `Var(2)` 越界 → `panic!("var not found")`（mod.rs:1181）。同路径经 unify 剥层（unification.rs:897）可达 |
| C4 | **中** | `mod.rs:1045-1052` | **`force(Call)` 不 force args**：只 force body，args 保持原值（可能含未展开的 Decl/meta）；`ptr_eq` 优化失效，比较时逐个 force |
| C5 | **中** | `mod.rs:1248-1257` + `unification.rs:889-909` | **Call 值不自动归约**：scrutinee 后续被 solve 后 Call 保持卡住，仅 unify 剥层时才重新 eval_aux 归约 → 同一表达式在"已解/未解"两个时刻 quote 结果不一致，归约依赖检查顺序 |
| C6 | **低** | `mod.rs:295` | `wrap_match_in_call` 的 `_l: u32` 参数从未使用；只包最外层 Match（`x => let ...; match` 不包）→ 无 Call 快速路径，unify 全量比较 Match 树（O(cases×decl)，每 case 重建 decl HashMap） |
| C7 | **低** | `typeclass.rs:324-330` | `vals_eq_ground_impl` 对 Call 忽略 body（同样依赖同 name 同 body 不变量）；`visited` 参数（typeclass.rs:283）从未读写，死参数 |

### 13.3 复现（C1，类型检查通过但 eval 崩溃）

```
enum Nat { zero  succ(x: Nat) }

def t(x: Nat): Nat =
    (match x {
        case zero => y => y
        case succ(n) => y => y
    }) 1
```

路径：infer `match` 类型为 fresh meta（elaboration.rs:1523-1527）→ `(match ...) 1` 应用时 meta 非 Pi → Scala apply 回退（elaboration.rs:1404-1444）→ `unify(Pi, meta)` 把 meta 解成 Pi → 类型检查通过 → eval（println 的 nf）→ `v_app(Val::Match, 1)` → **进程崩溃**。

其他触发路径：
1. unify 的 eta 展开（unification.rs:792-805）：`(_, Val::Lam(..))` 对任意非函数值 `v_app`——`unify(Match/Call, Lam)` 剥层后命中
2. 过度应用：`def f(x: Nat, y: Nat) = match x {...}` 后 `f 1 2 3` 中 `(f 1 2)` 类型是未解 meta 时放行

### 13.4 已确认安全的不变量（排除项）

- **body 恒为 Match**：eval（mod.rs:1248-1257）保证非 Match 时直接返回值不包 Call ✓
- **`wrap_match_in_call` 的 icits 索引无下溢**（l=0 时循环体为空）✓
- **rename 的 occ 检查**（unification.rs:261-263）阻止 meta 自引用求解，Call 不参与构造循环 ✓
- **eval_aux zip 截断在常规场景安全**（prepend 反转使值位置与 body Var 索引对齐）✓
- **quote round-trip 稳定**：quote(Call) → Tm::Call → eval 还原 ✓

### 13.5 修复建议

1. **`v_app` 消除 panic**（C1，最高优先）：不可应用值（Match/Call/Sum/SumCase/Literal/Pi/U）返回"卡住的应用"而非 panic；unify 的 eta 分支（unification.rs:792-805）加可应用性前置检查
2. **eval_aux 对齐修复**（C3）：恢复 `.filter(Expl)` 或按 bind 位置对齐，保证绑定数与 body 引用一致
3. **unify 快速路径**（C2）：去掉 TODO 快速路径或补 body 比较；失败时回滚已 solve 的 meta
4. **`force` 同步 force args**（C4）
5. **Call 归约时机**（C5）：`force` 中对 `Call.body` 尝试 eval_aux 归约（与 unify 剥层一致）
6. **`wrap_match_in_call`**（C6）：去掉死参数；考虑对 `let` 包裹的 Match 也包装
