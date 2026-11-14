# L11 真实场景语料（macro_rules 宏系统 / decl 表世界）

本目录是 `realbench --layer L11` 的语料：25 个 `.typort` 全部经 `--validate` PASS
（参考版全流程 `run` Ok + 孪生 `run_fast` 输出逐字节一致 + 孪生 `bench_check_nf` 非 0）。

口径：L11 参考版没有 `bench_check_nf`，realbench 的 basic 是全流程 `run`（含 parse+pretty）。

## 规模与耗时

- 文件数：25（抽取 19 + 手写 3 + 规模阶梯 3）
- 总行数：2629
- 总 decl 数：1476
- 整目录 basic 合计：约 20 ms（`--rounds 1 --only basic`，本机）

## 覆盖特性

- 声明级宏：展开 enum / impl / def，derive 风格宏生成 Describe 实现与构造子工具函数；
- 表达式级宏：`$x: raw` 捕获、嵌套宏调用（宏体里再调另一个宏）；
- 宏 DSL：`$body: Reg`/`$body: Expr` 嵌套宏片段、`$( ... )*` 重复、`$args: params` 参数捕获；
- decl 表世界：递归 def、重定义静默覆盖、可变全局（create_global/change_mutable/get_global）；
- trait/impl（L10 血统）：outParam、泛型约束、算符方法、结构体接收者；
- 匹配编译：逐臂下钻、嵌套覆盖检查、索引精化、GADT Vec/Fin。

## 规模阶梯（宏代码生成，decl 数约 50/200/800）

`ladder_050/200/800.typort`：同一生成形态，声明级宏 `svc` 每个调用生成一个业务
函数 `def`，函数体经表达式级宏 `addtwo` 展开，形成链式 service pipeline。
decl 数分别为 51 / 201 / 801。

## 文件清单

| 文件 | 行数 | decls | 来源 | 出处 | 覆盖特性 | 档位 |
|---|---:|---:|---|---|---|---|
| `ladder_050.typort` | 73 | 51 | 手写（生成） | 本任务生成（宏代码生成形态） | 声明级宏 svc + 表达式宏 addtwo，逐调用生成业务函数链 | small ≈51 decls |
| `ladder_200.typort` | 223 | 201 | 手写（生成） | 本任务生成（宏代码生成形态） | 同上，规模档位 medium | medium ≈201 decls |
| `ladder_800.typort` | 823 | 801 | 手写（生成） | 本任务生成（宏代码生成形态） | 同上，规模档位 large | large ≈801 decls |
| `proj_order_pipeline.typort` | 122 | 30 | 手写 | 本任务手写 | 声明级宏生成 enum/impl/构造子工具、derive 风格 Describe、表达式宏链、可变全局 | 项目级 |
| `proj_register_dsl.typort` | 106 | 28 | 手写 | 本任务手写 | 宏 DSL（$body: Reg 嵌套宏片段）+ 参数宏 + 可变全局构造寄存器规格 | 项目级 |
| `proj_service_codegen.typort` | 104 | 29 | 手写 | 本任务手写 | 宏 DSL 批量生成业务函数、嵌套宏调用（inc_twice 内层 inc）、多 enum 派生实现 | 项目级 |
| `scn_annotated_implicit_inst.typort` | 13 | 5 | 抽取 | tests/l11_fast_parity.rs:730 | 多隐式类型参数显式实例化 + 构造子 | — |
| `scn_annotated_index.typort` | 9 | 4 | 抽取 | tests/l11_fast_parity.rs:734 | 显式标注隐式域 + 显式索引 GADT Q[Nat] | — |
| `scn_dependent_proofs.typort` | 67 | 13 | 抽取 | src/L11_macro/mod.rs:1521（test4） | Eq 归纳证明（add_comm/add_assoc）、cong/symm/trans | — |
| `scn_fin_gadt.typort` | 28 | 6 | 抽取 | src/L11_macro/mod.rs:2371（test9） | Fin 索引 GADT + outParam Add 实例 | — |
| `scn_gadt_pack_rebind.typort` | 17 | 5 | 抽取 | tests/l11_fast_parity.rs:823 | 构造子重绑定参数 Pack[A][B] + 显式隐式实参 | — |
| `scn_gadt_vec_coverage.typort` | 17 | 3 | 抽取 | tests/l11_fast_parity.rs:847 | GADT Vec 长度 2 覆盖检查 + 索引精化 | — |
| `scn_gadt_vec_index.typort` | 39 | 11 | 抽取 | src/L11_macro/mod.rs:1827（test7） | GADT Vec 索引：len 投影、head、length | — |
| `scn_list_len_add.typort` | 23 | 5 | 抽取 | tests/l11_fast_parity.rs:911 | List 长度 + 递归 add | — |
| `scn_list_point_program.typort` | 123 | 43 | 抽取 | src/L11_macro/mod.rs:1595（test2） | List 构造、match、struct Point 投影、宇宙塔、依赖 eq 赋值 | — |
| `scn_macro_decl_enum.typort` | 12 | 3 | 抽取 | tests/l11_fast_parity.rs:333 | 声明级宏展开 enum（make_bool） | — |
| `scn_macro_dsl_project.typort` | 264 | 71 | 抽取 | src/L11_macro/mod.rs:2408（test11） | 宏 DSL 项目：macro_rules module/Expr 嵌套宏、可变全局、依赖证明 | — |
| `scn_macro_module_globals.typort` | 48 | 12 | 抽取 | src/L11_macro/mod.rs:1467（test6） | 多规则宏 module（params/raw 片段）、可变全局、macro 展开 def | — |
| `scn_mutable_globals.typort` | 12 | 3 | 抽取 | tests/l11_fast_parity.rs:350 | create_global / change_mutable / get_global 链 | — |
| `scn_point_line.typort` | 21 | 6 | 抽取 | tests/l11_fast_parity.rs:201 | 嵌套 struct 投影（Line.a.x） | — |
| `scn_proof_library_large.typort` | 197 | 58 | 抽取 | src/L11_macro/mod.rs:1934（test8） | 大型证明库：Exists 依赖 struct、Nat 定理族、Point/HighLvl | — |
| `scn_struct_pair_proj.typort` | 10 | 4 | 抽取 | tests/l11_fast_parity.rs:732 | struct 多类型参数 + 投影 | — |
| `scn_struct_universe_tower.typort` | 36 | 12 | 抽取 | src/L11_macro/mod.rs:1720（test5 邻近） | struct 宇宙塔（Type N）、依赖字段类型 | — |
| `scn_trait_library.typort` | 160 | 50 | 抽取 | src/L11_macro/mod.rs:1263（test_trait） | trait/impl、outParam Add、结构体实例、类型宇宙塔、Eq/refl、Bits 依赖赋值 | — |
| `scn_trait_pieces.typort` | 82 | 22 | 抽取 | tests/l11_fast_parity.rs:232 | 泛型 List map、ToString/Say/Add trait 实例、算符方法 | — |

## 来源说明

- **抽取**：从仓库测试/README/生成器中抽取的真实程序（经 `--validate` 过滤，仅保留 PASS）；
- **手写**：为本任务新写的项目级程序（含宏 DSL / 类型类库场景）；
- **手写（探针）**：为确认实例解析可 PASS 形态而写的小场景，直接沉淀为语料；
- **手写（生成）**：规模阶梯由本任务脚本生成，形态与手写程序一致，只改变 decl 规模。

## 验证记录

命令：

```
.\.\target\release\realbench.exe --layer L11 --corpus tools\bench_corpus\L11 --validate
```

结果：`SUMMARY,pass=25,skip=0`（无 SKIP 文件）。
