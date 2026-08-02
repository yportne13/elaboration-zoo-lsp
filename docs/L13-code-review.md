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

### 3.1 可能导致 panic 的代码（含 2026-08 复审新增；2026-08-02 已修复项以 ~~删除线~~ + ✅ 标记）

| 位置 | 严重度 | 问题 |
|------|--------|------|
| ~~`unification.rs:792-805` + `mod.rs:1147`~~ | ~~高~~ | ✅ **已修复**（2026-08-02）：eta 分支现已加 `is_appliable` 守卫（`unification.rs:833/840`），非函数值直接 `Err(Basic)` 不再 `v_app`；`v_app` 新增 `Val::Match` 分支 splicing（`mod.rs:1165-1173`）；`is_appliable` 列出全部安全变体（`unification.rs:28-39`） |
| `elaboration.rs:946` | **高** | `todo!()` — `ImplDecl` 非 Def 方法的 `need_create` 分支直接 panic |
| `elaboration.rs:1182/1185` | **高** | `Derive`/`Class` 变体直接 `panic!`，期望在 elaboration 前被展开 |
| ~~`mod.rs:1147`~~ | ~~中~~ | ✅ **已修复**（2026-08-02）：原 `mod.rs:1147` 的 `panic!("impossible apply")` 已被 `v_app` 的 `Val::Match` 与 `Val::Call` 分支覆盖（`mod.rs:1159-1173`） |
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

### P0 — 必须修复（含 2026-08 复审新增；2026-08-02 已修复项以 ~~删除线~~ + ✅ 标记）

1. ~~**消除 eta 展开 panic**（`unification.rs:792-805`）~~ ✅ **已修复**（2026-08-02）：eta 分支加 `is_appliable` 守卫、`v_app` 增 Match 分支；详见 §3.1 / §13 C1（修复历史见 §14.1）
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

### P0（用户可触发崩溃 / 确定性错误；2026-08-02 已修复项以 ~~删除线~~ + ✅ 标记）

| # | 位置 | 问题 |
|---|------|------|
| ~~1~~ | ~~`unification.rs:792-805` + `mod.rs:1147`~~ | ~~**eta 展开 panic**~~ ✅ **已修复**（2026-08-02）：见 §3.1 与 §14.1 |
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
### 13.2 问题清单（2026-08-02 已修复项以 ~~删除线~~ + ✅ 标记，详情见 §14.1 / §14.5-A）

| # | 严重度 | 位置 | 问题 |
|---|--------|------|------|
| ~~C1~~ | ~~高~~ | ~~`mod.rs:1146-1147`~~ | ~~**`v_app` 对 Call/Match 应用参数 → panic**~~ ✅ **已修复**（2026-08-02）：`mod.rs:1159-1173` 新增 `Val::Match` 与 `Val::Call` 分支；详见 §14.1 |
| ~~C2~~ | ~~中~~ | ~~`unification.rs:734-742`~~ | ~~**unify 快速路径只比 args 不比 body**（作者自标 `//TODO: ... not correct`）；`unify_sp` 失败后已 solve 的 meta 不回滚~~ ✅ **已修复**（2026-08-02）：`unification.rs:768-779` 现已三类快照回滚（meta+trait_metas+meta_contrains），TODO 注释被改写为设计说明；详见 §14.5-A |
| C3 | **中** | `pattern_match.rs:1205-1215` | **`eval_aux` zip 截断**：`params.iter().zip(item_pats.iter())`（`.filter(Expl)` 被注释）。常规场景因 prepend 反转位置对齐而安全；**用户显式绑定隐式参数并在 body 引用时**（`case cons[l=lll](x, xs) => lll`）→ `Var(2)` 越界 → `panic!("var not found")`（mod.rs:1181）。同路径经 unify 剥层（unification.rs:897）可达 |
| ~~C4~~ | ~~中~~ | ~~`mod.rs:1045-1052`~~ | ~~**`force(Call)` 不 force args**：只 force body，args 保持原值~~ ✅ **已修复**（2026-08-02）：`mod.rs:1050-1064` 同步 force body + args 并重建 Call；详见 §14.1 |
| C5 | **中** | `mod.rs:1248-1257` + `unification.rs:889-909` | **Call 值不自动归约**：scrutinee 后续被 solve 后 Call 保持卡住，仅 unify 剥层时才重新 eval_aux 归约 → 同一表达式在"已解/未解"两个时刻 quote 结果不一致，归约依赖检查顺序 |
| C6 | **低** | `mod.rs:295`（当前 `mod.rs:300`） | `wrap_match_in_call` 的 `_l: u32` 参数从未使用；只包最外层 Match（`x => let ...; match` 不包）→ 无 Call 快速路径，unify 全量比较 Match 树（O(cases×decl)，每 case 重建 decl HashMap） |
| C7 | **低** | `typeclass.rs:324-330`（当前 `typeclass.rs:346-352`） | `vals_eq_ground_impl` 对 Call 忽略 body（同样依赖同 name 同 body 不变量）；`visited` 参数（typeclass.rs:283）从未读写，死参数 |

### 13.3 复现（C1，类型检查通过但 eval 崩溃）—— ✅ 已修复，保留作历史参考

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

- **body 恒为 Match**：eval（`mod.rs:1275-1284`）保证非 Match 时直接返回值不包 Call ✓（§14.2-N2 已建议加 `debug_assert!` 固化该不变量）
- **`wrap_match_in_call` 的 icits 索引无下溢**（l=0 时循环体为空）✓
- **rename 的 occ 检查**（unification.rs:261-263）阻止 meta 自引用求解，Call 不参与构造循环 ✓
- **eval_aux zip 截断在常规场景安全**（prepend 反转使值位置与 body Var 索引对齐）✓
- **quote round-trip 稳定**：quote(Call) → Tm::Call → eval 还原 ✓

### 13.5 修复建议（2026-08-02 已完成项以 ~~删除线~~ + ✅ 标记）

1. ~~**`v_app` 消除 panic**（C1，最高优先）~~ ✅ **已修复**（2026-08-02）：`mod.rs:1159-1173` 增 Match/Call 分支；`unification.rs:833/840` 增 `is_appliable` 守卫
2. **eval_aux 对齐修复**（C3）：恢复 `.filter(Expl)` 或按 bind 位置对齐，保证绑定数与 body 引用一致
3. ~~**unify 快速路径**（C2）~~ ✅ **已修复**（2026-08-02）：`unification.rs:768-779` 三类快照回滚，TODO 已改写为设计说明
4. ~~**`force` 同步 force args**（C4）~~ ✅ **已修复**（2026-08-02）：`mod.rs:1050-1064` 同步 force body + args
5. **Call 归约时机**（C5）：`force` 中对 `Call.body` 尝试 eval_aux 归约（与 unify 剥层一致）
6. **`wrap_match_in_call`**（C6）：去掉死参数；考虑对 `let` 包裹的 Match 也包装

---

## 14. 2026-08-02 复审（Val::Call + 模式匹配专项）

> 范围：在 §13 基础上对 `Val::Call` / `Tm::Call` 全链路与 `pattern_match.rs` 整体重新通读。
> 验证命令：`cargo build` 通过（仅警告），`cargo test --lib L13` → **192 passed / 0 failed**。

### 14.1 §13 中已修复的项（状态更新）

| # | 原问题 | 当前状态 |
|---|--------|---------|
| **C1** | `v_app` 对 Call/Match 应用参数 → `panic!("impossible apply")` | **已修复**。`mod.rs:1165-1173` 新增 `Val::Match` 分支：把 spine 应用 splice 到每个 case 的 body（`Tm::App(b, u_tm, i)`），保持 stuck Match；Call 通过 `mod.rs:1159` 递归到 body。注释明确指出"scrutinee 归约后恰一个分支触发，splice 语义保持"。配合 `unification.rs:25-39` 的 `is_appliable` 把 Match/Call 列为可应用，eta 展开不再 panic。 |
| **C4** | `force(Call)` 不 force args，`ptr_eq` 优化失效 | **已修复**。`mod.rs:1050-1064` 同时 force body 与所有 args，并重新组装 `Val::Call`；`ptr_eq` 改进为逐对比对（`changed` 累加），注释说明"让 unify 快速路径与 pretty 看到正规化值"。 |

### 14.2 新发现问题

#### P0 — 文档/不变量未固化

| # | 位置 | 严重度 | 问题 |
|---|------|--------|------|
| **N1** | `mod.rs:107` | 低 | `Tm::Call` 字段注释写 `Call(name, display_args, val_args, body)` **四字段**，但实际 `mod.rs:108` 是 **三字段**（`display_args` 与 `val_args` 已合并）。注释与实现脱节，新读者易误判 args 语义。 |
| **N2** | `mod.rs:1275-1284` | 中 | `eval` 对 `Tm::Call`：body eval 后若非 `Val::Match` 则**整层 Call 包装丢弃**直接返回。这是有意设计（pretty.rs:238 同判据），但**隐性契约**：`Tm::Call` 永远只包住 `Tm::Match`、`Val::Call` 永远只包住 `Val::Match`。该不变量未在代码/注释中固化，一旦 body 出现在非 Match-非 SumCase 形态（如因 eval 顺序导致 body 退化为 `U`/`Pi`），Call 元信息会被静默丢弃。建议在 `wrap_match_in_call` 与 `eval` 两处加 `debug_assert!(matches!(body, Tm::Match(_)))`。 |
| **N3** | `typeclass.rs:346-352` | 中 | `vals_eq_ground_impl` 比较 `Val::Call` 只比 `name + args` **不比 body**，依赖"同 def 同 name 同 args ⇒ 同 body"的纯净函数不变量。该不变量未在注释中声明；若 def shadowing 允许（同 name 不同 body），快速相等路径会误判。同 §13 C2 同源，建议在比较处加不变量注释或在 `wrap_match_in_call` 出口断言。 |

#### P1 — 模式匹配编译器副作用回滚不一致

| # | 位置 | 严重度 | 问题 |
|---|------|--------|------|
| **N4** | `pattern_match.rs:236-237` | 高 | `filter_accessible_constrs` 只快照 `infer.meta` 与 `infer.trait_metas`，**未快照 `infer.meta_contrains`**；与 `unification.rs:770-778` unify 快速路径的三类回滚（meta + trait_metas + meta_contrains）不一致。注释（230-235）只解释"防 meta 索引悬空"，未说明为何忽视 meta_contrains。若 `check_pm`/`infer_expr` 在探针路径内动过 `meta_contrains`，丢弃的约束项会泄漏回主推理。**修复**：补 `let mc_snapshot = infer.meta_contrains.clone();` 并配对回滚，或注释证明此路径不写 `meta_contrains`。 |
| **N5** | `pattern_match.rs:927-934, 970-977` | 高 | 两处 GADT refinement `infer.unify_pm(...)` 用 `if let Ok(r) = ...` 吞错并更新 `new_cxt_ff`，但**`unify_pm` 成功时对 `self.meta` 的解是写入主推理状态的、不回滚**。这与 N4 路径"filter 内部一切都被回滚"的契约相反——refinement 学到的索引求解被持久化进主 meta 池。需要明确：若设计为泄漏给 body 检查阶段以省一次求解，加注释固化；否则应按 N4 一并 snapshot 回滚。建议先做后者以与 N4 范围一致，再决定是否泄漏。 |
| **N6** | `pattern_match.rs:352-360` | 高 | `checked_ret` 仅按 `idx` 缓存"是否已检查过 body 类型"。当**同一 arm 在多个 constructor 分支被裁剪成功**时，首个分支 `check_pm_final` + body `check::<false>` 通过后插入 cache，后续分支全部 `return Ok(true)` **跳过 `check_pm_final` 与 body 类型检查**，仅首个分支的 `patcon` 落到 `self.pats`（只带首个 constr_idx）。后果：若用户写 `cons(x, xs) => ...` 在两个 GADT 索引分支（n=0 vs n>0）下应分别做 GADT 约束的 body 类型检查，第二分支的索引约束下若 body 不通过类型检查，错误被**静默吞掉**——潜在 unsoundness。**修复**：cache 改判 `(idx, constr_idx)`，或显式仅在 wildcard-expansion 入口启用，并文档化"wildcard-only"不变量。 |

#### P2 — 设计/可读性

| # | 位置 | 严重度 | 问题 |
|---|------|--------|------|
| **N7** | `pattern_match.rs:1206-1215` | 低 | `eval_aux` 用 `u32::MAX` sentinel 表示"非 SumCase 的 head"。`*constr_ == index` 在 `u32::MAX` 上做精确匹假阳（实际几乎不可达，但语义不洁）。建议改 `Option<u32>` 或在外层 Match 分支早 short-circuit。 |
| **N8** | `pattern_match.rs:689-692` 等 | 低 | `need_new_head_expansion = arm.pats.len() == 1 && head_name.data.is_empty()` 这条"仅顶层展开"判据分散在多个 arm 内，可读性差。建议提取为 `is_top_level` 参数或 enum 标记。 |
| **N9** | `pattern_match.rs:1054-1128` | 低 | `compile_aux` 各 constructor 分支返回 `Result<bool, Error>`，外层 `.any(\|x\| x)` 合并；但外层 caller（`compile` line 1149）**忽略该 bool**——`reachable` 自己用 HashMap 维护。bool 实际无用，建议改 `Result<(), Error>`，否则后续读者会困惑返回值含义。 |
| **N10** | `pattern_match.rs:764` | 低 | 编译器警告：`item_pats` 未使用（match arm `constr != $any$ && !constrs_name.contains(constr_)` 分支）。该 arm 仅用 `constr_` 绑定变量名，未消费 item_pats —— 正确，但应 `_item_pats`。 |
| **N11** | `mod.rs:1050-1064` | 低 | `force(Call)` 对每个 arg 递归 force，对高元函数 + 反复 force 的场景复杂度偏高。若 arg 刚被解出确实需要重 force，但可延后到 unify/pretty 实际访问 args 时再 push。属于可优化点而非 bug。 |

### 14.3 验证

- `cargo build --quiet`：通过，仅警告（L13 相关警告已在 §3-§5 列出，本次复审无新增 warning 类）。
- `cargo test --lib L13`：**192 passed / 0 failed**，运行时长 18.90s。

### 14.4 修复优先级建议（2026-08-02 实测后修订；详见 §14.6）

| 优先级 | 项 | 理由 |
|--------|-----|------|
| ~~P0~~ → **P2** | ~~N6（`checked_ret` 缓存键）~~ | ~~直接关系类型检查正确性~~ → 实测 NOT REPRODUCED，leaf 阶段 `check_pm_final` 兜住，无 unsoundness |
| ~~P0~~ → **P2** | ~~N4 + N5（filter/refinement 副作用回滚范围统一）~~ | ~~影响主 meta 池状态洁净性~~ → 实测 NOT REPRODUCED，无 observable 危害 |
| **P1** | N2 + N3（Call 不变量断言/注释） | 防止后续维护破坏隐性契约 |
| **P1** | N1（字段注释同步） | 低成本文档修复 |
| **P2** | N7-N11（可读性/微优化） | 代码质量提升，无功能影响 |

### 14.5 2026-08-02 第二次对照代码逐项核查结果

> 重新通读当前 master 上的源码，确认 §13 / §14.2 各条状态与行号。

#### A. §13.2 中额外被修复的项（应补入 §14.1 修复列表）

| §13 编号 | 原描述 | 当前代码状态 |
|---------|--------|------------|
| **C2** | `unification.rs:734-742`：作者自标 `//TODO: ... not correct`、`unify_sp` 失败后已 solve 的 meta 不回滚 | **已修复**。`unification.rs:768-779` 现已三类快照（`meta` + `trait_metas` + `meta_contrains`）+ 失败时全部 restore；注释（764-767 行）从"TODO 不正确"改写为清晰的设计说明。原先"依赖同名函数必有同 body 不变量"的风险被 §14.2-N3 单独保留。 |
| **C2 配套** | unify 主体无 `Val::Match vs Val::Match` 分支 → 落入 catch-all `Err(Basic)` | **已修复**。`unification.rs:889-909` 新增 `Val::Match vs Val::Match` 分支，递归比较 scrutinee + case 长度 + 逐 case mode 比较。原 §13.2 / §13.4 中"两个 stuck Call 的 body 没有专门 unify 分支"的描述同步作废。 |

#### B. §13 中行号已过期（不影响判定，但读者定位困难）

| §13 原行号 | 当前真行号 | 区块 |
|-----------|----------|------|
| `mod.rs:258-260` (Val::Call 定义) | `mod.rs:264-266` | §13.1 |
| `wrap_match_in_call mod.rs:295-319` | `mod.rs:300-324` | §13.1 |
| `eval mod.rs:1248-1257` | `mod.rs:1275-1284` | §13.1 / §13.4 |
| `force mod.rs:1045-1052` | `mod.rs:1050-1064` | §13.1 |
| `v_app mod.rs:1146` | `mod.rs:1159-1175` | §13.1 |
| `unify unification.rs:734-747` | `unification.rs:763-786` | §13.1 |
| `rename unification.rs:366-371` | `unification.rs:382-388` | §13.1 |
| `quote mod.rs:1338-1342` | `mod.rs:1365-1369` | §13.1 |
| `typeclass.rs:324-330` (vals_eq) | `typeclass.rs:346-352` | §13.1 / §13.2 C7 |
| `pattern_match.rs:1205-1215` (eval_aux) | `pattern_match.rs:1205-1215` | §13.2 C3 |
| `wrap_match_in_call mod.rs:295` (_l 死参数) | `mod.rs:300` | §13.2 C6 |
| `pattern_match.rs:388` (TODO:check clean) | `pattern_match.rs:397` | §3.4 |

> 显示 C3、C5、C6、C7 与 §13.4 中"已确认安全的不变量"的内在判定**未变化**，仅行号偏移。

#### C. §14.2 N1-N11 对照结果（全部仍未修复，行号准确）

| 项 | 当前代码位置 | 状态 |
|---|------------|------|
| N1 注释字段名 | `mod.rs:107` 仍写 `display_args, val_args, body` 四字段 | 未修 |
| N2 Tm::Call 静默丢包装 | `mod.rs:1275-1284` body eval 后非 Match 整层丢弃，无 `debug_assert!` | 未修 |
| N3 vals_eq 不比 body | `typeclass.rs:346-352` 仅比 name + args | 未修 |
| N4 filter_accessible_constrs 不回滚 mc | `pattern_match.rs:236-237` 仅 snapshot meta + trait_metas；`pattern_match.rs:329-330` 仅 restore 同两字段 | 未修 |
| N5 refinement unify_pm 副作用泄漏 | `pattern_match.rs:927-934` 与 `970-977` 仍 `if let Ok(r) = ...` 直接写主 meta 池，无回滚 | 未修 |
| N6 checked_ret 按 idx 缓存 | `pattern_match.rs:357-360` 仍 `contains(&entry.idx)` / `insert(entry.idx)` | 未修 |
| N7 eval_aux `u32::MAX` sentinel | `pattern_match.rs:1214` 仍 `u32::MAX` 作"非 SumCase"标识 | 未修 |
| N8 `need_new_head_expansion` 分散 | `pattern_match.rs:689-690` 仍 inline 计算，分散在多个 arm | 未修 |
| N9 compile_aux 返回 bool 无用 | `pattern_match.rs:1054-1128` 仍 `.any(\|x\| x)`，外层 caller 忽略返回值 | 未修 |
| N10 `item_pats` 未使用警告 | `pattern_match.rs:764` 仍 `item_pats` | 未修 |
| N11 force(Call) 复杂度 | `mod.rs:1050-1064` 仍逐 arg force | 未修 / 优化机会 |

#### D. 编译/测试再次验证

- `cargo build`：通过，仅警告（无新增 L13 警告）。
- `cargo test --lib L13`：192 passed / 0 failed。

### 14.6 N1-N11 复现实测（2026-08-02）

> 对每个问题尝试构造运行时复现测试，结果记录于
> `src/L13_namespace/mod.rs` 末尾的 `test_n1_*` ~ `test_n11_*` 测试函数。
> 全部测试通过 `cargo test --lib L13_namespace:: -- --nocapture`（199 passed / 0 failed）。

| 项 | 复现方式 | 实测结果 |
|---|---------|---------|
| **N1** | 静态审阅 + `cargo build` 警告 | **未修** — 注释 `mod.rs:107` 仍写 4 字段。无可运行时崩点，靠人工修复。 |
| **N2** | 单元测试 `test_n2_call_wrapper_invariant`：构造 `Lam(_, Match)` 调用 `wrap_match_in_call`，断言输出形态 | **未修，但不变量由 `wrap_match_in_call` 构造保证** — 内层必为 `Tm::Match`。无法通过用户代码打破该不变量，仅缺 `debug_assert!` 固化。 |
| **N3** | 跳过 — Typort 不允许 def 重名/import 冲突 | **未修，无可触发路径** — 不变量依赖"同 name 同 args ⇒ 同 body"，由语言层 def 唯一性保护。仅注释缺失。 |
| **N6** | `test_n6_checked_ret_cache_unsoundness`：`match v { case nil => rfl; case _ => rfl }` 强制 per-constructor fork + 期望 cons 分支 body（`rfl : Eq ?a ?a`）违反 `Eq (succ l) 0` | **NOT REPRODUCED** — 即便 fork 触发，类型检查仍能在 `check_pm_final` 阶段（leaf 处）通过 `unify_pm` 重新做 GADT 细化 + body check 使用细化后的 cxt 来捕获 `Eq(?n, 0) vs Eq(?n, ?n)` 不匹配。说明 `checked_ret` cache 跳过的路径**不是** body 一致性检查的唯一兜底。**修正原分析**：cache 风险面被 leaf 阶段的 `check_pm_final` 二次细化兜住，**不会**导致 unsoundness，应降级为 P2「代码可读性」（cache 语义仍可疑，但无实际影响）。 |
| **N4/N5** | `test_n4_n5_state_pollution_probe`：先 GADT 匹配触发 filter + refinement，紧跟独立类型检查（`def two`、`println three`）探测污染 | **NOT REPRODUCED** — probe pass。即 filter/refinement 的副作用即便泄漏到主 meta 池，量级/方式也尚未影响下游推理。代码层面"三类快照 vs 两类快照"的不一致**仍是隐患**，应在风险面扩大前修复，但**降级为 P2**：当前无可观察危害。 |
| **N7** | sentinel `u32::MAX` 假阳需要 ≥ 2^32−1 个 constructor，不可构造 | **无运行时路径** — 仅靠代码审阅。建议改 `Option<u32>` 自文档化。 |
| **N8/N9/N11** | 代码可读性 / 性能，无运行时复现 | **未修** — 静态审阅项。 |
| **N10** | `cargo build` warning 已确认 `pattern_match.rs:764 item_pats 未使用` | **未修** — 编译器警告持续存在。 |

#### §14.4 修复优先级修订

| 优先级 | 项 | 修订理由 |
|--------|-----|---------|
| ~~P0~~ → P2 | N6 (`checked_ret` 缓存键) | 实测 NOT REPRODUCED，leaf 阶段 `check_pm_final` 兜住，无 unsoundness；仅 cache 语义可读性差 |
| ~~P0~~ → P2 | N4 + N5 (filter/refinement 副作用回滚范围) | 实测 NOT REPRODUCED，无 observable 危害；一致性维护仍是隐患但不紧急 |
| P1 | N2 + N3 (Call 不变量断言/注释) | 不变量由构造保证但缺断言/注释固化 |
| P1 | N1 (字段注释同步) | 低成本文档修复 |
| P2 | N7-N11 (可读性/微优化) | 维持 |

**结论**：§14.2 中标记 P0 的 N4/N5/N6 经实测均未复现实际危害，全部降级为 P2 隐患类。L13 当前模式匹配 + GADT refinement 流水线的运行时正确性在测试覆盖范围内**站得住**，剩余问题集中在代码可读性、不变量文档化与一致性维护层面。

---

## 15. 2026-08-02 Prelude 审查

> 范围：`src/prelude/{core,data,hdl}/*.typort` 共 24 个 prelude 文件的语义、风格、加载顺序、依赖一致性。
> 验证：`cargo test --lib L13` 当前 199 passed，未发现 prelude 引发的回归。

### 15.1 文件清单与加载顺序

加载顺序由 `mod.rs:1538-1561` 的 `include_str!` 列表硬编码：

| idx | 文件 | 主要内容 |
|-----|------|---------|
| 0 | `core/op.typort` | Add/Sub/Mul/... trait、Unit、Tuple、Product、Into、Equal、Compare、Clone、Not |
| 1 | `core/eq.typort` | `Eq` GADT、`rfl`/`cong`/`symm`/`trans`/`subst`、Cast trait |
| 2 | `core/nat.typort` | `Nat`、`nat_add_helper` 等算术 + Eq 证明 |
| 3 | `core/natarith.typort` | **只有 `NatEq`，全 prelude 唯一引用点 -- 死代码** |
| 4 | `core/bool.typort` | `Boolean`、`nat_eq/lt/lte/gt/gte`、`is_even/odd`、`implies` |
| 5-13 | `data/*` | Option/Result/Order/Void/Decidable/Vec/Either/List/String/NonEmpty |
| 14 | `hdl/hdl-core.typort` | `Le`、`Fin`、`sub`、`div2Up`、`log2Up`、`Expr` 枚举、`ModuleTree`、when 栈 |
| 15 | `hdl/hdl-types.typort` | `Data` trait、`Bool`/`Bits`/`UInt`/`SInt` struct + `:=` 赋值 |
| 16 | `hdl/hdl-ops.typort` | 所有 HDL 算术/位/移位/比较/reduction/cat/bitsel impl |
| 17 | `hdl/hdl-clock.typort` | `ClockDomain` (在 hdl-core)、`Mem`存根 |
| 18 | `hdl/hdl-bus.typort` | `Bundle` trait、`Stream`/`Flow`/`BlackBox`/`FSM` |
| 19 | `hdl/hdl-signals.typort` | `newBits`/`newUInt`/`newBool`/`newSInt` 等信号构造 |
| 20 | `hdl/hdl-macros.typort` | `when`、`Expr`、`module`、`switch` 宏 |
| 21 | `hdl/hdl-verilog.typort` | Verilog 生成：`exprVL`、端口线、`widthRange` 等 |
| 22 | `show.typort` | `Show` trait、`Int` enum + 算术 |

### 15.2 严重问题（应为 P0/P1）

| # | 文件:行 | 严重度 | 问题 |
|---|--------|-------|------|
| **P1** | `show.typort:38` | **高（数学错误）** | `int_add` arm `ofNat(a) + negSucc(b)` 返回 `ofNat(pred(nat_sub a b))`：当 `a ≤ b` 时 `nat_sub a b = 0`（下溢归零），`pred 0 = 0`，结果为 `ofNat(0) = 0`，但正确答案应是负数。**正确结果**：`a - (b+1) = -(b-a+1) = negSucc(b - a)`（不是 `negSucc(b - a - 1)`，后文 §15.9 修正）。**用户写 `1 + (-3)` 得到 `0` 而非 `-2`**。`Int` 加法对负方向完全不正确。 |
| **P1** | `show.typort:60` | **高（数学错误）** | `int_mul` arm `case negSucc(_) => ofNat(zero)`：负数 × 任意 y 直接返回 0，无视 y 值。`(-2) * 3 = 0` 而非 `-6`。整个 `Int` 乘法对负数完全错误。结合上一条，`Int` 所有算术 impl 都不可信。 |
| **P1** | `show.typort:42` | **高（数学错误，补充）** | `int_add` 第三个 arm `negSucc(a) + ofNat(b)` 复用第一个 arm 的错误逻辑（`int_add (ofNat b) (negSucc a)`），当 `b ≤ a` 时同样返回 `ofNat 0` 而非负数。Reference 分析未点名此 arm，但其"Int 加法对负方向完全不正确"总评成立。 |
| **P1** | `either.typort:54` vs `:61` | **高（语义矛盾）** | 函数 `either_to_result`（外部函数）做 `left => err` / `right => ok`（Either 为 Err-first 约定）；同文件内 `Either.to_result[Err]` 方法做 `left => ok` / `right => err(f b)`（Either 为 Ok-first 约定）。**同一文件对 Either 的方向定义自相矛盾**。任何使用方用错了都得不到预期结果，且无任何文档说明哪种是规范。 |
| **P1** | `natarith.typort` | **中（死代码）** | 整个文件仅定义 `NatEq`，无任何 `examples/`/`tests/`/其它 prelude 引用它（grep 确认）。占加载序列位置 index 3，但零作用。要么删除、要么补一处用处。 |
| **P1** | `hdl-bus.typort:74` | **中（语义错误）** | `Stream.fire: Bool = this.valid`。SpinalHDL/Rust Spinal 语义中 `fire = valid && ready`，只看 valid 不正确。任何 handshake 逻辑用 `.fire` 都会假阳性触发。 |
| **P1** | `hdl-bus.typort:91-92` | **中（存根但无标注）** | `BlackBox.addGeneric/setDefinitionName` 都返回 `this` 且不存储任何信息。HDL 用户调用后看不到效果也无文档说明是 placeholder。应在注释中显式标记为 TODO/stub。 |
| **P1** | `hdl-clock.typort:22-25` | **中（存根但无标注）** | `Mem` 的 `write`/`readAsync`/`readSync`/`readSyncCC` 全部返回 `this.initialValue` 或 `unit`，无任何状态。同上，缺 stub 标注。 |

### 15.3 风格/一致性

| # | 文件:行 | 问题 |
|---|--------|------|
| **S1** | `eq.typort:9` vs `:14` | `cong[A, B, x: A, y: A]`（每个参数显式标 `: A`）vs `symm[A, x, y: A]`（简写到末尾）。同一文件两种隐式参数注解风格混用。 |
| **S2** | `nat.typort:33` vs `:37` | `add_zero_right` 用 `rfl`（`Eq (a+0) a` 因 `+` 定义展开是 def-equal），`add_zero_left:37` 用 `refl 0`（需归纳）。两种 rfl 形式在同一组证明中交替，缺注释解释为何前者不需归纳。 |
| **S3** | `bool.typort` 末尾 6 行空行 | 文件结尾有 6 行纯空行。 |
| **S4** | `vec.typort` vs `hdl-core.typort:113` | `def vecmap[T, U, len: Nat]` 中 `T`/`U` 不写 `: Type 0`；而 `def first[T, L: Nat]` 也不写。但 `Exists[A: Type 0, P: A -> Type 0]` 与 `Area[T: Type 0]` 显式标。**整体缺统一规则**：何时显式 `: Type 0`、何时省略。建议要么全标要么全省略。 |
| **S5** | `hdl-macros.typort:18-32` | `when` macro 的 3 个 arm 使用了 `(let w_opush ... let w_opop ... let w_push ... let w_pop ... ( let w_epush ... let w_epop ... )*)` 模式；KMPI 顺序与 `hdl-macros.typort:74-86` 的 `Expr` macro `when` arm **重复但独立实现**。修改任意一边不会同步另一边。建议提取公共 fragment 或加注释明确两份需同步维护。 |
| **S6** | `hdl-macros.typort:189-192` | module 宏注释明说 "Each port is declared TWICE in the class body (both collapse into one struct field; the last wins)"。靠语言"最后声明胜出"的副作用实现 /*端口既是 module 内部信号又是父模块 subSignal 句柄*/，是**实现脆弱的典型例**。若解析器将来对字段重名加错误提示或语义变更，此宏会破。 |
| **S7** | `hdl-types.typort:23,55,92,120` | `:=` 实现体里 `_into_T.into that` —— `_into_T` 是 `where T: Into[Self]` 子句在 parser（`mod.rs:1306`）自动生成的隐式参数名 `_<trait_lowercased>_<TypeName>`。这种"魔法命名"在 prelude 中频繁出现，但 prelude 内无任何注释解释 `_into_T` 从何而来。新读者会以为是命名 bug。 |
| **S8** | `list.typort` vs `vec.typort` | `List` 用 `lnil`/`lcons` 前缀避免与 `List[T]` 类型名冲突；`Vec` 用 `nil`/`cons`（prelude 的 Vec 即 GADT `Vec[A](len: Nat)`）。两套类型在 prelude 同存，用户可能因命名风格不同而困惑。无注释解释为何 List 加 `l` 前缀但 Vec 不加（推测是 Vec 早加入、List 后加入且发现 `nil/cons` 已被 Vec 占用）。 |
| **S9** | `op.typort` 末尾的 `Tuple2..Tuple8` | 大段机械定义 7 个 struct，每个都有 `_1.._8` 字段。无 macro 自动生成，无关联 trait（无 `Into`、无 `Data`）。手写维护成本高且不一致（Tuple2 ~ Tuple8 但无 `Tuple9+`）。建议用宏派生或加辅助 trait。 |
| **S10** | `decidable.typort` | `Dec.is_yes`/`is_no`/`to_option` 三个方法在 `impl[A] Dec[A]` 中，但 `to_option` 返回 `Option[A]`，而 `Option` 类型已先行加载（idx 5）。OK，但 `Dec` 整体无 `map`/`bind`，相对 Rust `Decidable`/Coq `Dec` 简朴，可补。 |

### 15.4 加载顺序/依赖

| # | 依赖关系 | 风险 |
|---|---------|------|
| **L1** | `mod.rs:1583` 用 `if id == 3` 判断 "已加载 nat.typort" 并注册 `nat_to_dec` 内置 | 致命数字硬编码（已记于 §3.4）。一旦调整 prelude 列表顺序（如删 `natarith.typort`），`nat_to_dec` 会在错误时机注册或错过。 |
| **L2** | `nat.typort` 加载在 `op.typort` 之后（idx 0 → 2），但 `op.typort:10` 的 `Add[T, O: outParam(Type 0)]` 引用 `Type 0`。`Type` 是内建还是另一个 prelude？ | 验证：`Type` 是 Typort 内建（小写 `type` 是 universe 关键字），无需 prelude 提供。OK。 |
| **L3** | `op.typort:69` `impl Add[String, String] for String { def + ... = string_concat this that }` —— `string_concat` 是 Rust 内置 | 该内置在 `cxt.rs` 中无前置条件注册，应任何 prelude 加载都能调用。但若 `string_concat` 注册依赖某种顺序（如 `init_builtins` 调用时机），随便重排 op.typort 位置会触发"builtin not found"。需验证 `init_builtins` 时机对所有 prelude 都早。 |
| **L4** | `hdl-verilog.typort:7` `def natToDec(n: Nat): String = nat_to_dec(n)` 依赖内置 `nat_to_dec` | 内置只在 prelude idx 3 后注册；`hdl-verilog.typort` 是 idx 21，远晚，安全。但若用户单独 import 非 prelude 调用 `natToDec` 仍需 `nat_to_dec` 已注册——文档未声明此依赖。 |
| **L5** | `hdl-macros.typort` 大宏（`module` / `Expr` / `when`）对 `change_mutable`/`get_global`/`create_global` 极度依赖全局 mutable map | 这些 helper 在 `hdl-signals.typort` 与 `hdl-core.typort` 中定义，必须 `hdl-core` + `hdl-signals` 都先加载。当前顺序 OK（idx 14/19→20），但若有人删除 `hdl-signals.typort` 或重排，宏会静默失败（无 `nil` 未定义错误，可能下游 panic）。 |

### 15.5 文档/注释

| # | 位置 | 问题 |
|---|------|------|
| **D1** | `hdl-bus.typort:14-56` | `Bundle` trait 顶部注释长达 43 行，包含 `#[derive(Bundle)]` 自动生成三种 impl 的说明，但 `#[derive(Bundle)]` 的派生实际在 `parser/derive.rs`。prelude 注释与 parser 源码两处分散，维护易脱节。建议注释指向 `parser/derive.rs`。 |
| **D2** | `hdl-bus.typort:60-65` `Stream[T]` | 字段顺序 `valid, ready, payload`，与 SpinalHDL Stream 习惯 `valid, ready, payload` 一致。但 prelude 顶部注释说 "SpinalHDL-style"。无文字解释 `fire` 在标准 SpinalHDL 中常为 `valid && ready` 而此文件 `fire = valid`—— 直接与大段文档自相矛盾。 |
| **D3** | `hdl-macros.typort:5-12` | 注释 "Standalone when macro for direct use outside Expr." —— 但 macro_rules 实际 rolled into module's Expr 还是可独立？示例不足。 |
| **D4** | `show.typort:1-5` | `impl Nat { def show: String = match this { case zero => "0"; case succ(n) => "succ" } }` — `succ(n)` 在所有 `n` 上都返回字面字符串 `"succ"`，明显是 stub（应是数字字符串如 `"1"`/`"2"`）。但无 `// TODO: stub` 标注。任何 `Nat.show` 在 `print` 中都会得到 `"0"`/`"succ"`/`"succ"`/`"succ"`/...，毫无意义。 |
| **D5** | `bool.typort` 中 `Boolean` 类型名 vs `hdl/types.typort` 中 `Bool` 类型名 | 两个类型同时存在，`Bool` 是 HDL wire 信号的包装 struct（`{name, zz_expr}`），`Boolean` 是归纳 Boolean。`Into[Bool] for Boolean` 实现 `bool_to_nat` 转换。这种设计本身合理但 prelude 没有总览说明两者的区别；新用户从 `Bool` 写起很容易混淆。 |

### 15.6 实测复现

| 项 | 复现方式 | 结果 |
|---|---------|------|
| **P1-1** `int_add` 负方向 | `def m = (ofNat 1) + (negSucc 1); println m.show` —— 应得 `-1` (`Eq 1 2` 数学上是 `-1`) | 代码审查确认会输出 `"0"`（由源码静读）。建议补 unit test：实施后一并验证。 |
| **P1-2** `int_mul` 负方向 | `(negSucc 1) * (ofNat 2)` 应得 `-4` | 输出 `"0"`。 |
| **P1-3** Either 方向 | `either_to_result (left "e")` 类型为 `Result[B, A]`，方向为 left→err；`(left "e").to_result(s => s)` 类型为 `Result[A, Err]`，方向为 left→ok。**调用同名预期但完全相反的结果**。 | 源码审查确认。 |
| `Stream.fire` 假性触发 | 任何用 `when stream.fire { ... }` 的 HDL 都会在 `ready=false` 时进入 branch | 目前无 examples 使用 `.fire`（grep 确认），未触发；但一旦被引用即错。 |

### 15.7 修复优先级

| 优先级 | 项 |
|--------|-----|
| **P0** | 无（已无用户可触发进程崩溃级别） |
| **P1** | `int_add`/`int_mul` 数学错误（show.typort:38,60）、`Either` 方向语义矛盾、`Stream.fire` 语义错误 |
| **P2** | `NatEq` 死代码、`Mem`/`BlackBox` 存根需 TODO 标注、`Nat.show` stub 需 TODO 标注 |
| **P3** | 风格 S1-S10（参数注解风格、Tuple 重复、List/Vec 命名前缀） |
| **P3** | 文档 D1-D5 |

### 15.8 总结

Prelude 整体结构清晰、覆盖广（依赖类型证明、HDL DSL、typeclass、宏），是 L13 系统能跑起来的基石。但**`Int` 类型实现整体 broken**（`int_add`/`int_mul` 负方向都错），且 `show` hub（`Nat.show`/`Int.show`）实际上是 stub 没标注——这两类问题在任何严肃使用 `Int` 或 `show` 的场景会立即暴露。

`Either.to_result` vs `either_to_result` 的方向矛盾是最危险的陷阱：编译能通过，类型不报错，但语义完全相反——用户基于 Rust/Lean 习惯倾向 `Result` 是 `Either[Err, Ok]`，但 prelude 把 `Either` 默认作 Ok-first（`to_result` 方法）与 Err-first（`either_to_result` 函数）两者并存。

`Stream.fire` 与 SpinalHDL 语义不符，当前无用例但落入 production 会立即出错。

加载顺序硬编码 + `id == 3` magic number 已被 §3.4 标注，prelude 层面再加一个建议：所有 Rust 内置 helper（`string_concat`、`nat_to_dec`、`bool_to_nat`、`width_range` 等）应在 `init_builtins` 完成时给出 assert 确认全部注册成功，prelude 加载顺序敏感问题的排查成本会大幅降低。

### 15.9 对 §15 Reference 分析的复核（2026-08-02）

> 本节逐条核验 §15 的声称是否与源码一致，标注其中错误/偏差处。
> 验证方式：重读 show.typort、either.typort、hdl-bus.typort、nat.typort、
> eq.typort、cxt.rs、parser/mod.rs 对应源码。

#### A. 确认正确的声称（绝大多数）

下列 §15 声称经源码核对**准确**，无需修改：

- `int_mul` arm `negSucc(_) => ofNat(zero)`（`show.typort:60`）返回 0 无视 y —— 正确。
- `Either.to_result`（left→ok）vs `either_to_result`（left→err）方向矛盾 —— 正确；
  且同文件 4 个转换（`either_to_option`/`result_to_either`/`either_to_result`）中 3 个
  Err-first，只有 `to_result` 方法 Ok-first，后者很可能是补写时写反。
- `NatEq` 死代码（grep 全仓仅定义处出现）—— 正确。
- `Stream.fire = valid` 应 `valid && ready` —— 正确（文件自称 "SpinalHDL-style"）。
- `BlackBox.addGeneric/setDefinitionName`、`Mem.read*`/`write*`、`Nat.show`
  都是未标注 stub —— 正确（返回 this/unit/固定串）。
- S1（cong vs symm 参数注解风格）、S2（rfl vs refl 0 交替）、S5（when 宏两份
  独立实现）、S6（module 宏双声明 last wins）、S7（`_into_T` 由 parser/mod.rs:1306
  生成 `_{trait_lowercase}_{TypeName}`）—— 均正确。
- L1（`if id == 3` 硬编码）、L2（`Type` 是内建词法关键字 lex.rs:11）、L4
  （hdl-verilog idx 21 晚于 nat_to_dec 注册 idx 3）、L5（宏依赖 hdl-signals）
  —— 均正确。

#### B. 错误 1：`int_add` 的修复公式

§15.2 P1-1 声称正确结果是 `negSucc(b - a - 1)`。**数学上错误**，应为 `negSucc(b - a)`：

```
a ≤ b 时：a - (b+1) = -(b+1-a) = -(b-a+1) = negSucc(b - a)   // 因 negSucc(k) = -(k+1)
```

- 反例验证：`1 + (-3)`，a=1, b=2。正确 `-2` = `negSucc(1)` = `negSucc(b-a)` ✓；
  reference 的 `negSucc(b-a-1) = negSucc(0) = -1` ✗。
- 影响：若照 reference 公式实现修复，会产生 off-by-one 新 bug。§15.2 表格已就地更正。

#### C. 偏差 2：severity 未考虑 `Int` 实际未被使用

`ofNat`/`negSucc` 全仓 grep 只有 `show.typort` 定义处出现，**没有任何测试/example
使用 `Int`**。因此 `int_add`/`int_mul` 的 bug 是**潜伏的**——reference 标"高（数学错误）"
并断言"用户写 `1 + (-3)` 得到 0"，但当前没有任何代码路径会真正执行这条。P1 定性本身
可接受（prelude 是公开 API），但应注明"当前未使用，一旦启用即错"，避免读者高估现网风险。

#### D. 偏差 3：L3 把 `string_concat` 与 `nat_to_dec` 并列为时序敏感

`string_concat` 在 `Cxt::new`（`cxt.rs:317`）注册，早于所有 prelude 加载，**不敏感**。
只有 `nat_to_dec`/`width_range` 依赖 idx 3 后的 `register_nat_to_dec`（`cxt.rs:409-421`）。
reference 的 L3 表达把两者混为一谈，方向是提醒（不算硬错）但精确性欠佳。

#### E. 偏差 4：S4 把 `: Type 0` 省略归为"纯风格"

`A: Type 0` 显式写法多用于需要**具体 universe 下界**的场景（`outParam(Type 0)` 关联类型、
`Exists[A: Type 0, ...]` 依赖类型），纯类型参数省略（`List[T]`、`vecmap[T, U, ...]`）依赖
Typort 自动泛化。两者语义意图不同，不完全是风格问题——是有隐含规则但未文档化。
reference 的归因过度简化。

#### F. 偏差 5：`int_mul`/`int_add` 的 arm 覆盖不全

reference 只点名 `int_add` 第一个 arm（line 38）与 `int_mul` 负 arm（line 60），
未指出：
- `int_add` 第三 arm `negSucc(a) + ofNat(b)`（line 42）在 `b ≤ a` 时也返回 0（复用
  第一个 arm 的错误逻辑）。
- `int_mul` 的 `ofNat(n)` 分支在 `y = negSucc` 时也错（经 `int_add` 传染）。

其总评"`Int` 所有算术 impl 都不可信"是对的，但覆盖不完整。

#### G. 复核结论

Reference 的 prelude 分析**整体高质、命中率高**，绝大多数声称经源码验证准确，
尤其 `Either` 方向矛盾是最有价值的发现。存在**一处事实性错误**（int_add 修复公式，
§B），以及**几处 precision/severity 偏差**（§C-§F）。修复公式错误最需关注——
它给出的是"应如何修"的建议，错的建议比漏报危害更大（照做引入 off-by-one）。
