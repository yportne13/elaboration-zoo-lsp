# L12 真实场景语料（canonical 形式 / 类型类求解）

本目录是 `realbench --layer L12` 的语料：30 个 `.typort` 全部经 `--validate` PASS
（参考版全流程 `run` Ok + 孪生 `run_fast` 输出逐字节一致 + 孪生 `bench_check_nf` 非 0）。

口径：L12 参考版没有 `bench_check_nf`，realbench 的 basic 是全流程 `run`（含 parse+pretty）。

## 规模与耗时

- 文件数：30（抽取 20 + 手写 3 + 探针沉淀 4 + 规模阶梯 3）
- 总行数：2050
- 总 decl 数：1338
- 整目录 basic 合计：约 39 ms（`--rounds 1 --only basic`，本机）

## 覆盖特性

- 实例解析密集：多实例（Bool/Nat 各自 Show 实例）、默认方法 trait、覆写实例；
- 泛型约束求解：`[s: Show[T]]` 显式约束、`where T: Show + Get` 多约束、实例搜索；
- canonical 判定：outParam、重绑定构造子、显式隐式实参、索引精化与 GADT 索引等式；
- 类型宇宙与依赖结构：struct 宇宙塔、依赖字段、Exists 风格 struct；
- 匹配编译：Bool 矩阵完整覆盖、嵌套 List 覆盖、GADT Vec zip；
- 宏与可变全局：macro_rules module、create_global/change_mutable/get_global。

## 规模阶梯（实例解析，decl 数约 50/200/800）

`ladder_050/200/800.typort`：同一形态，每个 `def r_XXX : String = render <value>`
都触发一次 `Show[T]` 实例求解（Bool/Nat 两实例交替），形成实例解析密集的调用序列。
decl 数分别为 56 / 206 / 806。

## 文件清单

| 文件 | 行数 | decls | 来源 | 出处 | 覆盖特性 | 档位 |
|---|---:|---:|---|---|---|---|
| `ladder_050.typort` | 90 | 56 | 手写（生成） | 本任务生成（实例解析形态） | 每个 def 触发一次 Show[T] 实例求解，Bool/Nat 交替 | small ≈56 decls |
| `ladder_200.typort` | 240 | 206 | 手写（生成） | 本任务生成（实例解析形态） | 同上，规模档位 medium | medium ≈206 decls |
| `ladder_800.typort` | 840 | 806 | 手写（生成） | 本任务生成（实例解析形态） | 同上，规模档位 large | large ≈806 decls |
| `proj_dependent_vector.typort` | 103 | 39 | 手写 | 本任务手写 | 带长度索引 Vec 构造、List 构造、struct 投影、Nat 算术与 Bool 匹配 | 项目级 |
| `proj_hdl_bitwidth.typort` | 115 | 44 | 手写 | 本任务手写 | struct Bits/Port 投影、位宽算术、Bool 方向匹配（HDL 位宽规格） | 项目级 |
| `proj_typeclass_lib.typort` | 103 | 30 | 手写 | 本任务手写 | Show/Named/Tag 三 trait 多实例、双约束泛型、默认方法、实例解析调用点 | 项目级 |
| `scn_annotated_index.typort` | 9 | 4 | 抽取 | tests/l12_fast_parity.rs:637 | 显式标注隐式域 + 显式索引 GADT | — |
| `scn_bool_match.typort` | 11 | 2 | 抽取 | src/L12_canonical/mod.rs:2743（rev-fix） | Bool 通配 match（代码生成的模式形态） | — |
| `scn_bool_matrix.typort` | 24 | 5 | 抽取 | tests/l12_fast_parity.rs:714 | Bool 二元矩阵完整覆盖 match | — |
| `scn_constrained_render.typort` | 21 | 6 | 手写（探针） | 本任务小场景（实例解析探针沉淀） | 单 impl + [s: Show[T]] 泛型约束渲染 | — |
| `scn_default_method.typort` | 17 | 5 | 抽取 | src/L13_namespace/legacy_tests.rs:3736 | trait 默认方法 + 覆盖实例（默认实例语义） | — |
| `scn_gadt_vec_zip.typort` | 43 | 10 | 抽取 | src/L12_canonical/mod.rs:1731（test6） | GADT Vec zip（succ len 索引）+ 可变全局 + 宏 | — |
| `scn_implicit_enum_inst.typort` | 13 | 5 | 抽取 | tests/l12_fast_parity.rs:633 | 多隐式类型参数 + 显式实例化构造子 | — |
| `scn_list_coverage.typort` | 17 | 3 | 抽取 | src/L09_mltt/mod.rs:1514 | List 嵌套模式完整覆盖 match | — |
| `scn_method_resolution.typort` | 25 | 7 | 抽取 | src/L13_namespace/legacy_tests.rs:4230 | 方法名在多个 trait 中时按已实现实例解析 | — |
| `scn_multi_constraint.typort` | 30 | 8 | 抽取 | src/L13_namespace/legacy_tests.rs:4268 | where T: Show + Get 双约束、trait 方法经隐含实例调用 | — |
| `scn_mutable_globals.typort` | 12 | 3 | 抽取 | tests/l12_fast_parity.rs:394 | create_global/change_mutable/get_global | — |
| `scn_operator_trait.typort` | 29 | 5 | 抽取 | src/L13_namespace/legacy_tests.rs:4181 | 自定义算符 trait `<(that)` 实例与算符调用 | — |
| `scn_pack_rebind.typort` | 18 | 5 | 抽取 | src/L12_canonical/mod.rs:2617（rev-fix） | 构造子重绑定参数 Pack[A][B] + 显式隐式实参 | — |
| `scn_package_module.typort` | 14 | 5 | 抽取 | src/L13_namespace/mod.rs:7542 | package 命名空间 + def/enum 组合 | — |
| `scn_point_line.typort` | 21 | 6 | 抽取 | tests/l12_fast_parity.rs:257 | 嵌套 struct 投影（binder 下） | — |
| `scn_resolution_chain.typort` | 57 | 19 | 手写（探针） | 本任务小场景（实例解析探针沉淀） | Show 双实例上的实例解析调用链 | — |
| `scn_string_concat.typort` | 5 | 2 | 抽取 | src/L09_mltt/mod.rs:1392 | string_concat 字符串拼接 | — |
| `scn_struct_pair_proj.typort` | 10 | 4 | 抽取 | tests/l12_fast_parity.rs:635 | struct Pair 多类型参数 + 投影 | — |
| `scn_struct_universe_tower.typort` | 36 | 12 | 抽取 | src/L12_canonical/mod.rs:2009（test7） | struct 宇宙塔 Type N + 依赖字段 | — |
| `scn_trait_tostring.typort` | 21 | 5 | 抽取 | src/L13_namespace/legacy_tests.rs:3589 | ToString trait 实例 + 点号方法调用 | — |
| `scn_two_instances_constrained.typort` | 27 | 8 | 手写（探针） | 本任务小场景（实例解析探针沉淀） | 双实例 + 泛型约束双调用点 | — |
| `scn_two_traits_constrained.typort` | 29 | 8 | 手写（探针） | 本任务小场景（实例解析探针沉淀） | 双 trait + 单实例 + 泛型约束 | — |
| `scn_typeclass_show.typort` | 46 | 14 | 抽取 | src/L13_namespace/legacy_tests.rs:3631 | Show trait 双实例（Bool/Nat）+ 泛型约束函数 + 点号方法调用 | — |
| `scn_where_constraint.typort` | 24 | 6 | 抽取 | src/L13_namespace/legacy_tests.rs:4091 | where T: Show 约束 + 泛型实例解析 | — |

## 来源说明

- **抽取**：从仓库测试/README/生成器中抽取的真实程序（经 `--validate` 过滤，仅保留 PASS）；
- **手写**：为本任务新写的项目级程序（含宏 DSL / 类型类库场景）；
- **手写（探针）**：为确认实例解析可 PASS 形态而写的小场景，直接沉淀为语料；
- **手写（生成）**：规模阶梯由本任务脚本生成，形态与手写程序一致，只改变 decl 规模。

## 验证记录

命令：

```
.\.\target\release\realbench.exe --layer L12 --corpus tools\bench_corpus\L12 --validate
```

结果：`SUMMARY,pass=30,skip=0`（无 SKIP 文件）。
