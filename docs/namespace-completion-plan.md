# L13 namespace 功能完善方案

> 状态：规划（三轮回合 + 三轮子 agent 独立评审后定稿；评审③引入根因归并与 import_map 替代方案）
> 日期：2026-08-08
> 评审①：核验全部 G/I/V 断言属实，发现 6 处方案缺陷（G6 fallback 第二通道、G1 指针比较/覆盖 prelude、G1b 体内裸名、G2 双侧前缀、G4 无解、V2 必然丢失）
> 评审②：复核修订，确认 G1 只防"删"不防"覆盖污染"、G6 需 namespace 可见性限域、G1b 须限 alias 映射、G2 漏 remove_file、I3 同 package 错配、I4 键名实测有误、parse 失败残留
> 评审③：纠正 G8 方向（旧边残留实为保守正确）；提出"20+ 项 ≈ 6 根因"归并；提出 **import_map 替代方案**（import 别名不插 decl、lookup 时解析）为根因 A 首选；重排执行顺序（零纠缠快赢先行、G6 单独立项）
> 评审④：import_map **代码验真有条件通过**（4/6 成立）——修正优先级矛盾（prelude 例外优先）、S2 带点别名转正为必需（mk 特例 elaboration.rs:1738-1742 走精确查表）、G1a' 升为独立 commit（值快照簿记）、Phase 4 排除 import_map 写回、G6 与 import_map 非完全解耦；确认 per-file clone 即 G6 可见集载体（Phase 3 自述错误，利好）
> 终审⑤：**裁决 A 可以开工**——import_map 放 Infer 证实正确（Cxt 克隆无收益）、"约 45 行"实测 ~70-80 行、现有测试无一依赖别名进全局、`cargo build` 干净；补 2 个实现注意项（I2 wildcard 时序、类型位置走同一 infer_expr）；阶段 6/7 可移出主线、V2 降级文档化；三步高风险项均有回退策略
> 实施记录（阶段 0-2 + I3/I4/X3 + L1/L2）：import_map 落地 24/24 测试绿 + 全量回归绿；**G7/G5/G8/G2/G3 已修**；**I4/I3b/X3 已修**；**L1 已实现**（ambiguous import 建议，测试 `ambiguous_name_offers_import_fixes`）；**L2 已实现**（import 上下文补全，lib.rs unit 测试）；**G1a' 实测降级**
> 范围：`src/L13_namespace/`（语言层）+ `src/lib.rs`（LSP 依赖图/增量重编译）
> 验证基线：`cargo test --lib L13`、`cargo test --test cross_file_tests`、`cargo test --test completion_tests`

## 1. 现状盘点

### 1.1 语言层（`src/L13_namespace/`）

- `package mylib.utils` → 置 `cxt.namespace_prefix`，后续 decl 经 `prefix_decl_name` 加前缀
  （`elaboration.rs:36`，`infer` 入口对 Package/Import 放行：`elaboration.rs:800-805`）。
- `import` 三种形态（通配/花括号/单名）→ 把 `cxt.decl` 里全名剥离成别名**克隆插入**当前 cxt
  （`elaboration.rs:1475-1507`）。
- 变量解析顺序：局部 `src_names` → `cxt.decl` 精确 → `namespace_prefix` 限定
  → `.name` 后缀 fallback（唯一否则 ambiguous）（`elaboration.rs:1671-1733`）。
- `a.b.c` 限定访问经 `qualified_path_str` 查表（`elaboration.rs:2381`）。
- 固有 impl 方法注册进 `cxt.namespace`，成员访问 `x.method` 走 `trait_wrap` 探测
  （`elaboration.rs:1168`、`elaboration.rs:2123`）。
- prelude 自动别名：`Nat.zero → zero` 裸名插入全局 decl（`mod.rs:2355-2376`），永久全局。

### 1.2 LSP 层（`src/lib.rs`）

- D4 跨文件增量重编译：`file_symbols/file_deps/file_namespace/ns_providers/ns_dependents`
  + `update_deps`/`rebuild_set`/`visit_dep`（`lib.rs:595-704`）。
- `elaborate`：克隆全局 cxt → 移除本文件旧 key → infer（import 从全局读）
  → diff new_keys → 无错误**整表写回**全局 + 更新 file_symbols（`lib.rs:721-763`）。
- `process_file` 仅解析成功才 `update_deps`（`lib.rs:887-889`）。

## 2. 已确认问题清单（按根因归并）

> **评审③：20+ 项 ≈ 6 个根因**。修复应按根因成批做，勿逐条碎片化。

| 根因 | 问题项 | 一句话 |
|------|--------|--------|
| **A. import 别名进 decl map + 整表写回 + 全局 fallback** | G1、G1a、G1b、I1、I2、G6、S2 | decl map 污染 → 泄漏/覆盖/裸名/冲突全部由此而生。**首选 import_map 替代**（§3.1，消 G1/G1a(import 部分)/G1b/I1/I2）。注：**G6 与 G1a' 单独分阶段**——G6 与 import_map 非完全解耦（带点别名/fallback 兜底）；G1a'（真实 def 覆盖 prelude）import_map 不修复，独立 commit |
| **B. 依赖图记录形状错误** | G2、G3 | ns_providers/ns_dependents 精确匹配，子命名空间/多 provider 断裂 |
| **C. prelude 别名注入不一致** | G7 | LSP 路径 vs 测试路径行为分叉 |
| **D. 宏导出生命周期** | G5 | 只 insert 不 remove |
| **E. trait/impl 注册不随文件同步** | I3、I4、I5 + X2/X3/X4 | 跨文件 trait/固有方法/class 均缺注册同步，且 package 内同文件可能已断 |
| **F. 单名 import 依赖缺失** | G4、G8 | 依赖图边界情况（G8 已降级为文档化） |

### 根因 A 明细（import 别名 / decl map 污染）

| # | 问题 | 位置 |
|---|------|------|
| G1 | **import 别名泄漏进全局**：整表写回 `*cxt.decl = local_cxt.decl.clone()`（lib.rs:757），`Decl::Import` 插入的剥离别名（`foo`）随之进全局 → 不 import 的文件 C 也能裸用 `foo`；B 关闭时 `foo` 被移走而 C 不在依赖图，不重建 → 脏分析 | `lib.rs:757` + `elaboration.rs:1484` |
| G1a | **prelude 别名覆盖污染**：`import mylib._` 若 mylib 有与 prelude 别名同名构造子（`zero`），本地 `insert` 覆盖 prelude 的 `zero`，整表写回后全局 `zero` **永久**变成 mylib 的值（`zero`∈before_keys 不进 new_keys、file_symbols 不追踪、关闭不回退） | `lib.rs:757` + `elaboration.rs:1486` |
| G1a' | **~~真实 def 覆盖 prelude 别名~~ 实测降级**：评审③④推断"非 package 文件写 `def zero` → 写回永久替换全局 prelude zero"。**实现期实测：不可触发**——top-level def 的 `fake_bind`（elaboration.rs:838）对已存在的 decl key 报 `redefine zero`，def 直接失败、`has_error` 使写回整体跳过。enum/struct/trait/impl 同样走 fake_bind；唯一未检查的 `Cxt::decl` 直插点是 enum case_key（elaboration.rs:1130），但需"`Foo.bar` 存在而 `Foo` 不存在"的极端前置，现实中不可达。**结论：redefine 检查已守护，无需修复**（曾加的 O(N) 写回快照已回滚，避免每按键性能开销） | `elaboration.rs:838` + `elaboration.rs:1130` |
| G1b | **体内裸名**：真实符号体内引用别名的 Tm 是裸名 `Tm::Decl("foo")`（elaboration.rs:1692）——别名从全局移除后 Tm 级名字悬空 | `elaboration.rs:1689-1692` |
| I1 | import 别名静默覆盖：`import a._` + `import b._` 同出 `add` 时后者覆盖，无冲突报错 | `elaboration.rs:1480-1505` |
| I2 | import 不存在的 namespace/名字 = 静默 no-op，无诊断 | `elaboration.rs:1475` |
| G6 | **后缀 fallback 限域 → 已实现**：`.name` fallback 只匹配"首段是 decl key 或可见命名空间"的候选（`Expr.mux`→`Expr`、`Add.Add.mk`→`Add`；`mylib.foo` 首段 `mylib` 非 decl key 且未 import 则排除）——不 import 的文件裸写 `foo` 不再经全局 fallback 解析。可见命名空间由 **`cxt.namespaces` 死字段**承载（Decl::Package/Import 记录，D4 顺带解决）。测试 `non_importing_file_does_not_leak_via_fallback`；L1 的 not-in-scope import 建议路径随之可达 | `elaboration.rs:1714-1732` |
| S2 | 通配 import 插入带点别名（`Tree.leaf`），与显式限定访问混叠。**评审④转正为必需**：`Tree.mk` 特例（elaboration.rs:1738-1742）走精确查表不走 Raw::Obj 分支，import_map 至少存 `X.mk` 档带点别名，否则 `import mylib.Tree` 后 `Tree.mk` 断 | `elaboration.rs:1481-1482` |

### 根因 B 明细（依赖图形状）

| # | 问题 | 位置 |
|---|------|------|
| G2 | **子命名空间 import 依赖错配**：`import mylib.MyType.member` / `import mylib.MyType._` 的 dep 记为 `"mylib.MyType"`，provider 只注册 `file_namespace="mylib"` → provider 变更不重建 dependent。`rebuild_set`（lib.rs:686）、`visit_dep`（lib.rs:662）、`remove_file` 收集 dependents（lib.rs:907）**三处**全精确匹配，都不命中 | `lib.rs:617` vs `lib.rs:622` |
| G3 | **单文件多 `package` 只记最后一个**：两个 package 符号都写回全局，但 `ns_providers` 只注册最后一个 → 关闭/重建错乱 | `lib.rs:621-626` |

### 根因 C/D/F 明细

| # | 问题 | 位置 |
|---|------|------|
| G7 | **prelude 别名注入两处不一致**：`mod.rs:2362-2376` 有 `ns_method_keys` 过滤 + 排序确定性 first-wins；`lib.rs:365-381` 无过滤无排序 → 实例方法（`Bool.mux`）也被做成裸别名，winner 不确定 | `lib.rs:365-381` vs `mod.rs:2362-2376` |
| G5 | **宏导出泄漏**：`exported_macros` 只 insert 不 remove；宏名从文件消失、文件关闭、parse 失败时旧规则残留。跨文件同名宏需防误删 | `lib.rs:717-719` |
| G4 | **`import foo`（prefix 空）不进依赖图**（`!prefix.is_empty()` 守卫 lib.rs:616），但空 prefix 分支（elaboration.rs:1496-1497）能解析。**修复：拒绝单名 import 并诊断**（裸名不唯一无法反查 provider；全库测试无单名 import，拒绝安全） | `lib.rs:616` |
| G8 | **parse 失败依赖边**：`process_file` 仅解析成功才 `update_deps`。**评审③修正**：新增 import 但别处语法错 → 边没建（旧 decls 里无新 import，无法用旧 decls 补）；旧边残留实为**保守正确**（超集=多重建不漏）。**降级**：parse 失败仅清理 exported_macros（并入 G5），依赖边残留文档化接受 | `lib.rs:887-889` |

### 根因 E 明细（trait/impl 注册同步）

| # | 问题 | 位置 |
|---|------|------|
| I3 | **trait 声明跨文件不可用**：`import mylib.Trait` 只拷 Sum 别名，`trait_definition`/`trait_out_param`/`set_trait_out_params` 注册不同步（跨文件部分待 Phase 4）。**package 内同文件已修**：(a) trait 名称解析——`impl Trait for X` 的 `trait_name` 按 `namespace_prefix` 解析（`trait_full`）；(b) **TraitDecl + ImplDecl 方法名均不再前缀**（保留书面名）——`trait_wrap` 按书面名派发、trait-impl 方法匹配书面名，前缀会双双断裂。测试 `trait_impl_in_package_resolves`（含 `f.getVal` 实例派发）。**跨文件部分待 Phase 4** | `elaboration.rs:1436-1438`、`elaboration.rs:1235-1236` |
| I4 | **固有 impl 跨文件与 package 内 → 均已完成**：package 内（方法不前缀 + `infer_after_prefix`，测试 `inherent_method_in_package_dispatches`）；**跨文件**——`elaborate` 写回把本文件的 inherent namespace 条目合并进全局 `cxt.namespace`（按类型值指针去重，`file_namespace_regs` 跟踪，编辑/关闭时移除），import 文件的 `x.method` 可派发（测试 `cross_file_inherent_method_dispatches`）。**namespace 在 Cxt 上同步，避开 infer 写回陷阱** | `elaboration.rs:1168` + `lib.rs` 写回 |
| I5 | 跨文件 trait 实例同步（**未做，待单独设计评审**）：`trait_solver`（Synth: class_instances/head_index/trait_out_params）+ `trait_definition/assoc_defaults/symbol_table` 不随文件同步。**难点**：prelude 等共享 trait 的实例是追加进 `class_instances[name]` 的，关闭时按 trait 名整删会误删 prelude 实例 → 需实例级 diff/移除 + head_index 一致性；首次引入 local→global infer 写回（import_map 泄漏陷阱）。建议按"文件内注册记录（`trait_decls`/`trait_instances` 字段）→ `merge_trait_regs`/`remove_trait_regs` 方法"方案设计，单独评审后启动 | `mod.rs:770-802` |
| X2 | **class 在 package 下 items 未前缀**：`prefix_decl_name` 的 Class 分支（elaboration.rs:77-82）只前缀 `name`，items 不前缀 → class phase-B 生成的方法 def 可能以未前缀名进全局（裸全局名污染）。无测试覆盖，探针 | `elaboration.rs:77-82` |
| X3 | **supertrait 同文件未平移 → 已修**：`trait B: A` 在 package 内，supertrait 名称按 `namespace_prefix` 解析（`resolved_supertraits`，elaboration.rs:1426-1444；prelude trait 保持裸名）——传递方法继承 + 存储的 supertraits 都用解析后名。测试 `supertrait_in_package_inherits_methods`（继承方法要求实现）。**附带**：package 内 trait 双前缀已修（`infer_after_prefix`） | `elaboration.rs:54` |

> 注：I3(b)/I4/X2/X3 的共同根因是 **package 前缀只加了部分名字**（method/trait_name/supertrait/class items 各少加一层）。修 prefix 平移时按名称解析规则做（decl 精确→namespace 限定），**勿盲加前缀**（会把 prelude 的 `Show` 误译为 `mylib.Show`）。

### P1/P2 LSP 与其余

| # | 问题 | 位置 |
|---|------|------|
| L1 | auto-import quick-fix 缺失 → **已实现**：ambiguous bare name 报错时每候选附 `add import <full>` 修复（可达）；not-in-scope 唯一匹配也附（当前被 G6 fallback 泄漏掩盖，G6 落地后生效）。测试 `ambiguous_name_offers_import_fixes`。注：现有 quick-fix 机制只显示文本（show_message），非 text-edit | `elaboration.rs:1731` |
| L2 | import 上下文补全缺失 → **已实现**：`import mylib.<prefix>` / `import mylib.{ <prefix>` 时按前缀过滤全局 decl 第一层成员；parse 中途也能工作（不走 hover_table）。lib.rs unit 测试 `namespace_l2_tests`（`import_completion_prefix_parses_forms` + `import_context_completion_offers_first_level_members`） | `lib.rs:1376-1456` |
| L3 | rename 完全未实现 → **已实现**：声明 rename_provider + `rename_at`（复用 L4 引用机制，覆盖定义 + 全部跨文件引用；qualified `mylib.foo` 只替换最后一段）。lib.rs unit 测试 `rename_edits_def_and_all_uses_across_files` | `ls.rs:101` |
| L4 | references 仅单文件 → **已实现跨文件**：`cross_file_references` 按 def span（path_id+offsets，Span PartialEq 只比 payload 需手动比）遍历所有打开文件的 hover_table 收集引用。lib.rs unit 测试 `cross_file_references_find_uses_in_other_files` | `lib.rs:1338` |
| L5 | qualified 路径 `a.b.c` 中间段 hover → **已实现**：`push_qualified_hover` 为限定访问的每个前缀段压 hover 条目（`mylib.Tree.mk` 的 `Tree` token 可 hover 出类型）。测试 `qualified_access_hovers_intermediate_segments` | `elaboration.rs:1744-1761` |
| V2 | **跨文件 `mutable_map` 必然丢失**：与全局共享 Rc 但每文件 `elaborate` 结束 `.clear()`（lib.rs:776）→ 跨文件模块可变状态（ModuleTree 副作用）不可用。探针后定修复 | `lib.rs:776` |
| V3 | 类型级 import 无测试 → **已补**：`imported_type_in_type_position`（import 的类型在函数参数/返回类型位置可用，走同一 `infer_expr`） | — |
| S1 | 非通配 import 不带入前缀段（`import mylib.MyType.member` 只插 `member`），与通配不对称 | `elaboration.rs:1494-1504` |
| S3 | `import mylib.{x,y}` 的 prefix 本体不别名，与通配不一致 | `elaboration.rs:1494-1504` |
| D1 | prelude 自动别名永久 shadowing：用户包 `mylib.zero` 裸用永远解析到 prelude 别名，无警告 | — |
| D2 | `import a.b.c` 语法二义：c 一律当成员 | — |
| D3 | 多文件同 `package`：合并靠写回顺序，半删除状态需定义语义 | — |
| D4 | `cxt.namespaces`（cxt.rs:103）死字段：仅内存统计读取，从未填充 | — |
| D5 | 磁盘文件发现：`did_change_watched_files`/workspace folders 空实现——单独立项 | — |

> V1（qualified 模式 `case mylib.Ctor(...)`）已改判移除：parse error（pattern 头只接受单 Ident，`parser/mod.rs:1047-1062`；`.` 独立 token `lex.rs:239`）。

## 3. 设计决策（先定语义再动手）

1. **import 是文件级可见性**：import 别名不进全局符号集；prelude 自动别名是永久全局的例外。**解析优先级定稿（评审④）**：任何全局 decl 精确（own def / 其他文件裸 def / prelude 别名）> import_map > namespace_prefix > 后缀 fallback——prelude 例外优先，无需排除集，文档化这一确定性语义。
2. **import 冲突语义**：`import a._` + `import b._` 同名 → 报 `ambiguous import`；本地 def 覆盖 import → 合法 shadowing。
3. **`package` 是绝对路径**：不嵌套叠加（`infer` 入口已对 Package 放行，勿在重构中引入）。
4. **依赖图匹配改为前缀语义**（修复 G2/G3）：provider 注册的 namespace `N` 覆盖所有以 `N.` 为前缀的 import 路径；`rebuild_set`、`visit_dep`、`remove_file` **三处一致**用"注册 namespace 是 dep 的最长前缀"匹配。前缀匹配是超集（保守多重建），与 `cross_file_tests` 全精确匹配兼容。
5. **根因 A 首选 import_map 方案**（见 §3.1）；若坚持"插入+写回回删"，须实现 G1/G1a/G1b 全部簿记。
6. **G6 fallback 限域与根因 A 解耦、单独立项**：不塞进 G1 的验收闸门。
7. **trait/impl 注册跟随文件同步**（根因 E）：复用 import_map 的 `alias→full` 映射对齐键名；同 package 平移按名称解析规则做。

### 3.1 import_map 替代方案（评审③④验真：根因 A 首选实现）

**思路**：import 别名**不插入 `cxt.decl`**，改为 Infer 上一个独立的 `HashMap<alias, full>`（import_map），变量 lookup 时查表。评审④代码验真：6 条中 4 条成立、2 条需修正（已并入下文）；无泄漏已验证（全局 infer 的 import_map 恒空——elaborate 从不把 local_infer 写回全局 infer，仅 hover_table 存 per-file clone）。

**能消掉**：G1（无泄漏）、G1a 的 import 部分（不碰 decl，无从覆盖 prelude）、G1b（体内 Tm 始终引用全名，无需规范化）、I1（重复别名精确检测）、I2（不存在检测天然在 import 分支发生）；Phase 3 直接复用现成映射。
**消不掉**：G6（fallback 泄漏独立于 import 别名）；**G1a'（真实 def 覆盖 prelude 别名）独立 commit，import_map 不修复它**。

**改动量**：
- `Infer` 加字段 `import_map: HashMap<SmolStr, SmolStr>`（`mod.rs:804-825` Clone + `mod.rs:1110-1128` new，两个点；clone 自动传播，与 hover 存 infer clone 的模式一致）。
- 改 `Decl::Import` 分支（elaboration.rs:1475-1507，约 20 行）：不再 make_mut 插 decl，改填 import_map。通配/花括号/单名的存在性判断逻辑（1480-1482 / 1501）原样可复用为 I2 校验。**"bring prefix itself"（elaboration.rs:1489-1492）必须一并进 import_map**。
- `Raw::Var` 解析插查表：位置在"decl 精确命中失败之后、namespace_prefix 之前"（elaboration.rs:1671-1733）。hover 的 def_span 从 `cxt.decl.get(&full)` 取（1691/1700/1725 模式复用）；self-import 时该 key 已被 lib.rs:725-730 移除 → def_span 缺失，接受为边界。
- `Raw::Obj` 限定路径首段查表（elaboration.rs:1744-1758，约 15 行）：`Tree.leaf` → 首段 `Tree` 经 import_map → `mylib.Tree` → 拼 `.leaf`。**additive 顺序**：先原样全路径、再头段查表——pattern 侧（pattern_match.rs:287-291/608-612）用 Val::Sum **全名**构造 Raw::Obj 路径，全名必须先试，头段查表不得抢先。
- `lib.rs` 写回（753-763）**不用动**（import 不再进 decl，new_keys/file_symbols 更干净——今天带点 key `Tree.leaf` 会进 file_symbols，改后消失）。

**评审④修正项（落地门禁，全部小成本）**：
1. **优先级决策**：方案原写"own def > import > prelude"与"查表插在 decl 精确之后"**矛盾**（prelude 别名就在 decl 里，decl 精确先命中）。定稿为：**任何全局 decl 精确（含 own def / 其他文件裸 def / prelude 别名）> import_map > namespace_prefix**——即 prelude 例外优先，无需排除集；文档化这一确定性语义。
2. **S2 带点别名转正为必需**：`Tree.mk` 特例（elaboration.rs:1738-1742）改写成 `Raw::Var("Tree.mk")` 走**精确查表**，不走 Raw::Obj 分支 → import_map 至少存 `X.mk` 档带点别名，否则 `import mylib.Tree` 后 `Tree.mk` 断。**带点别名是必需项，非"待定义"**。
3. **G1a' 独立 commit**：值快照簿记是新增机制（见根因 A 表），不随 import_map 落地。
4. **Phase 4 陷阱**：首次引入 local_infer→全局 infer 写回（trait 同步）时，import_map 会突然泄漏——Phase 4 设计**必须显式排除 import_map 字段**。

**裁决**：作为根因 A 的首选实现，第一个 commit = import_map 本体（单 commit，不混 G6/G1a'），附失败测试后落地；write-back 方案作保底备选。

## 4. 分阶段实施

### 阶段 0【先行】零纠缠快赢（评审③：避免 G1 被 G6 卡死）

- **G7 ✅ 已完成**：`lib.rs:365-381` 对齐 `mod.rs:2362-2376`（`ns_method_keys` 过滤 + 全名排序确定性 first-wins）。测试：`prelude_alias_excludes_instance_methods`。
- **G3**：`update_deps` 收集所有 `Decl::Package` 路径（`Vec`），`file_namespace` 多值/前缀集（与 G2 共用前缀索引设计）。
- **探针**：I4 同文件 `x.method` 在 package 下是否已断；X2 class items 未前缀；X3 supertrait 平移；V2 跨文件模块 create。
- **G8 降级 ✅ 已并入 G5**：parse 失败清 exported_macros（`remove_file_macros` 在 parse 失败分支调用）；依赖边残留文档化。
- **G5 简化 ✅ 已实现**：`file_macros: DashMap<uri, HashSet<macro_name>>` 按文件记录导出宏名；每次变更经 `update_file_macros`（新增/更新的名字 last-writer-wins 插入，移除的仅在无其他文件导出时删），关闭/parse 失败经 `remove_file_macros`。无需引用计数。测试：`closing_file_removes_exported_macro`、`closing_one_of_two_same_name_macros_keeps_it`、`parse_failure_clears_exported_macros`。

### 阶段 1【P0】根因 A：import 别名机制（import_map 落地）

- 实现 §3.1 import_map，**落地门禁**（评审④，全部小成本）：
  1. 优先级定稿：全局 decl 精确（含 prelude 例外）> import_map > namespace_prefix；
  2. import_map 存**首段别名 + 带点别名**两档（S2 转正必需，至少 `X.mk`）；
  3. `mk` 特例路径（elaboration.rs:1738-1742）确认走带点别名，**阶段 1 内不得删 fallback**；
  4. 同文件 import 必须先于 `package` 声明才可见（跨文件顺序由依赖图保证）；
  5. **G1a' 独立 commit**（值快照簿记），不随本阶段。
- **I1 冲突检测 + I2 存在性校验**：import_map 插入前检查；无匹配 → 报 `cannot import 'mylib': not in scope`（带 span，quick-fix 钩子留给 Phase 4）。
- **G4**：拒绝单名 `import foo` 并诊断。
- **G6 单独立项**（见阶段 3），**不作为本阶段验收闸门**——本阶段验收用"B 关闭后全局无泄漏别名、import 不覆盖 prelude、本地 def 覆盖 import 合法、`Tree.mk`/`Tree.leaf` 限定访问保持可用"。

### 阶段 2【P0】根因 B：依赖图形状 ✅ 已完成

- **G2+G3 合并实现**：
  - `file_namespace`（单值）→ `file_namespaces`（`DashMap<uri, HashSet>`，G3 记录文件声明的**所有** package）。
  - 新增段边界前缀匹配辅助：`ns_prefix_of`（`p == ns || p.starts_with(ns + ".")`）、`dependents_under`（provider→dependents）、`providers_under`（dep→providers）。
  - `rebuild_set`/`visit_dep`/`remove_file` **三处**统一改用前缀查询（修复子命名空间 import 依赖断裂 + 多 package 只记最后一个）。
- 测试：`sub_namespace_import_dep_recorded`、`editing_sub_namespace_provider_rebuilds_dependent`（用 `type_map` 长度观测重建——决策 1-a 掩盖全局 key 变化）、`multi_package_file_registers_all`。
- 已知：前缀查询为 O(#namespace) 扫描，workspace 规模小时可接受；索引优化留作后续。

### 阶段 3【P1】G6 fallback 限域（单独立项设计）

- namespace 可见性限域：仅当前文件声明/导入的 namespace 成员 + prelude 例外。
- **评审④修正载体认知（利好）**：方案原声称"hover/completion/trait_wrap 走全局 infer，per-file 集会丢"——**实际** hover/completion 全走 per-file hover_table clone（lib.rs:1047/1302/1342/1404），trait_wrap 走 elaborate 中的 local_infer。**per-file clone 本身就是 G6 可见集的现成载体**（与 import_map 同一模式），注入机制不像方案写的那么隐蔽。
- **复用 `cxt.namespaces` 死字段**（D4）：实现为"当前文件可见 namespace 集"，一举两得。
- 可见集要同时处理整键 namespace 前缀与导入的剥离键（S2 带点别名），非简单 HashSet。
- **与 import_map 的衔接**：imported alias 的 member（`Tree.leaf`）必须计入可见集，否则打断阶段 1 已通过的限定访问用例。

### 阶段 4【P1】根因 E：trait/impl 注册同步（I3/I4/I5/X2/X3）

- **先做阶段 0 的探针**，确认真实失败面与 key 形态。
- I4 先行：`cxt.namespace` 条目按 namespace 粒度 diff 同步 + `alias→full` 映射对齐（含同文件 package 下已断的修复）。
- I3 次之：`trait_definition`/`trait_out_param` 同步 + 同 package trait_name/supertrait 平移（按名称解析规则，勿盲加前缀）。
- I5 最后（风险最高）：`trait_solver`（Synth）+ `assoc_defaults`/`symbol_table` 同步，delta 跟踪 + 回滚。
- X2：class items 前缀补全。
- 各步均需失败保留旧注册、关闭移除。

### 阶段 5【P1】LSP（L1-L2）与探针收尾

- L1 auto-import quick-fix：`name not in scope` 时找唯一 `TypeName.name` → 生成 `import`。G6 限域后此查找显式走全局 decl 而非共享解析路径。
- L2 import 上下文补全：光标在 import 语句内时按前缀过滤全局 decl。
- V2：探针后定修复（elaborate 后不 clear 共享 mutable_map / 按文件 diff 回写）。

### 阶段 6【P2】LSP（L3-L5、V3、S1/S3）

- L3 rename（至少声明 provider + 单文件）；L4 references 跨文件；L5 qualified 中间段 hover/goto；V3 类型级 import 测试；S1/S3 形态对齐或文档化。

### 阶段 7【P3】清理与设计项（D1-D4）

- D4：实现为可见 namespace 集（阶段 3 复用）或删除。
- D1/D2/D3 文档化 + 必要时报诊断。
- D5 磁盘文件发现：单独立项。

## 5. 验证计划

- 新增 `tests/namespace_tests.rs`（按根因分文件/分组）：
  - **根因 A（import_map）**：B 关闭后全局无泄漏别名；`import mylib._` 不覆盖 prelude `zero`（G1a）；`Tree.mk`/`Tree.leaf` 限定访问保持可用（带点别名门禁）；`import mylib.Tree` 后裸 `Tree.mk` 可用；import 冲突报错（I1）；不存在 import 报错（I2）；单名 import 报错（G4）；本地 def 覆盖 import 合法；双通配冲突报错。
  - **G1a'（实测降级）**：`real_def_cannot_clobber_prelude_alias` —— `def zero` 被 redefine 检查拒绝，prelude 别名保持可用（替代原"值快照恢复"测试）。
  - **根因 B**：`import mylib.MyType._` 后改 provider 重建 dependent；关闭 provider 时子命名空间 dependent 重建；单文件两 package 均注册为 provider；深层包+浅依赖前缀用例。
  - **G7**：LSP backend 路径下实例方法不出现在裸名别名里（确定性）。
  - **G5/G8**：关闭文件后导出宏不可用；两文件同名宏互不影响；parse 失败清理宏、符号保留。
  - **根因 E**：跨文件固有方法 `x.method`；package+impl 同文件 `x.method`（探针）；跨文件 `impl Trait` / trait 实例；同 package 内 `impl Trait`；class items 前缀；supertrait 平移。**Phase 4 写回陷阱回归**：trait 同步写回后 import_map 不泄漏。
  - **G6**：不 import 文件裸写 `foo` 报 not in scope；`def t: Foo = bar` 表达式裸构造子仍可用；pattern 裸构造子 `case mux` 仍可用；prelude 成员裸用仍可用；imported alias 的 member（`Tree.leaf`）计入可见集。
  - V2/V3/S1/S3。
- 复用 `process_file` + 全局 decl key 断言模式（`tests/cross_file_tests.rs`）。
- 回归：`cargo test --lib L13`、`--test cross_file_tests`、`--test completion_tests`。
- 宏泄漏/别名泄漏类改动注意 prelude 自动别名（`mod.rs:2355`）不得被破坏。

## 6. 建议执行顺序

**阶段 0（零纠缠快赢：G7+G3+探针+G8 降级+G5 简化）→ 阶段 1（根因 A：import_map 替换，附失败测试）→ 阶段 2（根因 B：前缀索引）→ 阶段 3（G6 单独立项设计）→ 阶段 4（根因 E）→ 阶段 5-7。**

**最小起点（终审⑤定稿：第一个 commit 具体范围）**：
- **第一个 commit = import_map 本体**（单 commit，不混 G6/G1a'）：
  1. `Infer` 加 `import_map: HashMap<SmolStr, SmolStr>`：mod.rs:770-802 字段 + 804-826 Clone + 1110-1128 new，三处。
  2. 重写 `Decl::Import` 分支（elaboration.rs:1475-1507，约 30 行）：wildcard/brace/single 三形态 + bring-prefix 进 import_map；存首段 + 带点两档别名；I1 重复冲突报 `ambiguous import`；I2 不存在报错；**不碰 cxt.decl**。
  3. `Raw::Var` 查表插入 decl 精确之后、namespace_prefix 之前（1694-1696 之间）：命中则 hover def_span 用全名、返回 `Tm::Decl(全名)`。
  4. `Raw::Obj` 首段查表（1748 后、1753 prefix 分支前），**as-is 优先的 additive 顺序**。
  5. `lib.rs` 不改（写回/deps 均不动，update_deps 只读 AST 的 Decl::Import，lib.rs:616）。
  6. 新增失败测试：B 关闭后全局无泄漏别名、import 不覆盖 prelude zero、双通配冲突、不存在 import 报错、`import mylib.Tree` 后 `Tree.mk`/`Tree.leaf` 保持可用、本地 def 覆盖 import 合法、单名 import 报错。
  7. 验收：`cargo test --lib L13` + `--test cross_file_tests` + `--test completion_tests` 全绿。
- 或先提交零纠缠包：G7（已完成）+ G3 + 探针测试 + G8 降级文档 + G5 简化。
- **G1a' 已降级**（fake_bind redefine 检查使其不可触发，见问题表）——不再作为独立 commit。
- **G6、Phase 4 各独立 commit**，不得与 import_map 混批（G6 注入机制最不确定；Phase 4 首次引入 infer 写回有 import_map 泄漏陷阱）。

**实现注意项（终审⑤补充）**：
- I2 对 wildcard 的"namespace 尚未 elaborate"时序防误报：依赖图保证 provider 先重建，正常 load 序无碍；单测里"先 import 后定义"的写法会开始报错，测试须按顺序写。
- 类型位置的名字解析走同一 `infer_expr`（类型即 term），V3 只是补测试不是补机制。
- 阶段 1 内不得删 fallback（elaboration.rs:1714-1732 是 `def t: Foo = bar` 的依赖）；`mk` 特例路径不得断；I1/I2 的错误 span 需带诊断，给 Phase 4 的 quick-fix 钩子留位。

**范围裁减（终审⑤）**：阶段 6/7（rename/跨文件 references/D1-D4 文档化/D5）可移出主线，与"namespace 正确性 + 无泄漏"零贡献；V2（mutable_map）降级为文档化（跨文件共享状态 `.clear()` 是架构决定，修复收益低）。

## 7. 已排除项（复核确认非 bug）

- ~~嵌套 package 叠加前缀~~：**修正**——`infer` 入口对 Package 放行（Package 声明自身无叠加），但 **trait 经 `self.infer` 重入为 `Decl::Enum` 会二次加前缀**（实测 `mylib.mylib.HasVal`），已于探针期修复（改 `infer_after_prefix`，elaboration.rs:1444）。其余 decl 无叠加。
- ~~同文件 import 自身包~~：import_map 方案下无此问题（别名独立存、own def 优先级更高）。
- ~~qualified 模式 `case mylib.Ctor(...)`~~：parse error（pattern 头只接受单 Ident，`.` 独立成 token），不是匹配剥离问题，无需修复。
- ~~G8 用"上次成功 decls"重跑 update_deps~~：上次成功 decls 未存储，且新增 import 时旧 decls 不含新 import，补不上；旧边残留是保守正确行为。
- **G1a'（实测降级）**：top-level def 覆盖 prelude 别名被 `fake_bind` 的 `redefine` 检查拦截（elaboration.rs:838），不可触发；enum case_key 直插点（elaboration.rs:1130）需"Foo.bar 存在而 Foo 不存在"的极端前置。非 bug，测试 `real_def_cannot_clobber_prelude_alias` 记录该守卫。
