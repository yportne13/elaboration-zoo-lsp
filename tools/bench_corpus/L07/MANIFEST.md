# L07 真实场景性能语料（sum type / 依赖模式匹配）

本目录是 `realbench --layer L07` 的真实语料集：从仓库测试/README 抽取并经
语义验证的 Typort 程序（`ex_*`）、手写的项目级程序（`hw_*`），以及一组同形态
规模阶梯（`ladder_*`）。**目录内只有 `.typort` 文件与本 MANIFEST.md**；所有
文件均通过 `--validate` 闸门，无 SKIP。

## 验证结果

命令（HEAD 源码构建的驱动）：

```text
.\target\release\realbench.exe --layer L07 --corpus tools\bench_corpus\L07 --validate
```

结果：**PASS = 27，SKIP = 0**（`SUMMARY,L07,pass=27,skip=0`）。

闸门口径：参考版全流程 `run` 必须 Ok，且参考版与孪生版（`bump_spine_iter`）的
`bench_check_nf` 节点数一致且非 0。

规模与耗时（单轮 sanity，`--rounds 1 --only basic`；共享 CPU 下仅作量级参考）：

- 27 个文件合计 basic ≈ **253 ms**（`TOTAL,L07,27,1,1,253138,...`，µs 单位），
  落在验收区间 10–500 ms 内；其中 `ladder_l07_large.typort` 占大头。

## 文件清单

| 文件 | 来源 | 覆盖特性 | 行数 | decls | 档位 |
| --- | --- | --- | ---: | ---: | --- |
| ex_basic_lists_options.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_basic` | Bool/Nat/List/Option 基础 ADT、多态 map、println 输出 | 79 | 24 | 单例 |
| ex_bits_adder.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_eq_proofs`（内嵌 bits_adder 负载） | Vec GADT 索引族 + Product enum + 嵌套 match 全加器 | 54 | 9 | 单例 |
| ex_block_comments.typort | 抽取 `tests/l07_blackbox.rs :: bb_block_comments_ok` | 块注释词法（预处理保持 span） | 11 | 3 | 单例 |
| ex_church_strings.typort | 抽取 `src/L07_sum_type/tests.rs :: test_lambda_calculus_and_strings` | Church 编码、String builtin、enum Nat/add、λ 高阶 | 50 | 21 | 单例 |
| ex_dependent_match_vec.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_dependent_match` | Vec 依赖 match 传递（索引精化） | 18 | 3 | 单例 |
| ex_enum_vec_projection.typort | 抽取 `src/L07_sum_type/bump_spine_iter/bench_src.rs :: enum_src` | Vec 索引投影、Eq GADT、递归 length/rep | 48 | 13 | 单例 |
| ex_eq_reasoning.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_eq_reasoning` | Eq GADT + cong/symm/trans 等式推理 | 27 | 6 | 单例 |
| ex_even_odd.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_recursive_defs` | 互递归 Nat→Bool（even/odd） | 25 | 6 | 单例 |
| ex_indexed_vec.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_index` | Vec 索引族 + 投影 + head/length | 37 | 11 | 单例 |
| ex_let_match_forms.typort | 抽取 `tests/l07_fast_parity.rs :: parity_vsub_slot_applied_closure_workbuf` | let 绑定与 match 组合（let 形式 + 卡住 match） | 20 | 4 | 单例 |
| ex_line_comments.typort | 抽取 `tests/l07_blackbox.rs :: bb_line_comments_ok` | 行注释词法 | 9 | 3 | 单例 |
| ex_multi_index_gadt.typort | 抽取 `tests/l07_fast_parity.rs :: parity_multi_index_gadt_unannotated_impl_params` | 多索引 GADT + 索引投影（Pack） | 32 | 11 | 单例 |
| ex_nested_list_patterns.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_nested_patterns` | List 嵌套模式 `cons(h, cons(h2, t))` | 27 | 7 | 单例 |
| ex_proof_add_assoc.typort | 抽取 `src/L07_sum_type/tests.rs :: test_eq_add_assoc` | add 结合律归纳证明 | 32 | 7 | 单例 |
| ex_proof_add_comm.typort | 抽取 `tests/l07_blackbox.rs :: bb_inductive_add_comm` | add 交换律 + trans/symm/cong 全家 | 60 | 14 | 单例 |
| ex_proof_add_succ_right.typort | 抽取 `src/L07_sum_type/tests.rs :: test_eq_add_succ_right` | add a (succ b) 引理（索引精化） | 32 | 7 | 单例 |
| ex_proof_add_zero_right.typort | 抽取 `src/L07_sum_type/tests.rs :: test_eq_add_zero_right` | add a zero 引理 | 32 | 7 | 单例 |
| ex_proof_mul_one_right.typort | 抽取 `src/L07_sum_type/tests.rs :: test_eq_mul_one_right` | mul n 1 引理（let + 显式隐式实参） | 49 | 10 | 单例 |
| ex_proof_mul_zero_right.typort | 抽取 `src/L07_sum_type/tests.rs :: test_eq_mul_zero_right` | mul n 0 引理 | 35 | 7 | 单例 |
| ex_type_family_match.typort | 抽取 `tests/l07_fast_parity.rs :: parity_tests_rs_stuck_match` | 类型层 match（`V(n)` 依赖消除） | 27 | 7 | 单例 |
| hw_expr_interp.typort | **手写**（项目级） | 算术表达式解释器：6 构造子 `enum Expr` + 变量环境（`Name -> Nat`）+ 6 臂 `eval` + 常量折叠 `const_fold` + 语义引理（refl 精化） | 168 | 45 | 项目级 |
| hw_list_lib.typort | **手写**（项目级） | 多态列表库：length/map/fold/append/reverse/filter/repeat/sum/count + `length_map`/`length_append`/`length_repeat` 归纳引理 | 173 | 50 | 项目级 |
| hw_proof_suite.typort | **手写**（项目级） | 自然数等式推理库：rfl/cong/symm/trans + add 交换/结合/单位律 + mul 零/一律 + 组合用例 | 145 | 37 | 项目级 |
| hw_stack_vm.typort | **手写**（项目级） | 栈式字节码解释器：`enum Op` + 操作数栈（`List[Nat]`）+ 多层嵌套 match（指令×栈两层）+ 容错语义 + `run` 语义引理 | 123 | 28 | 项目级 |
| ladder_l07_small.typort | 生成（同形态阶梯） | 解释器前端流水线：每阶段「表达式定义 + 求值 + 累计」3 decls，13 阶段 | 83 | 48 | **small** |
| ladder_l07_medium.typort | 生成（同形态阶梯） | 同上，63 阶段 | 233 | 198 | **medium** |
| ladder_l07_large.typort | 生成（同形态阶梯） | 同上，263 阶段 | 833 | 798 | **large** |

合计：27 文件 / 2462 行 / 79,901 字节。

## 覆盖特性分布

- **enum 与 GADT**：普通和类型（Bool/Nat/List/Option）、索引族（`Vec[A](len: Nat)`）、
  GADT 返回类型（`Eq`、`Pack`）、类型层 match（`V n` 族）。
- **依赖模式匹配**：索引精化、嵌套模式、卡住 match（stuck match）、不可达分支、
  归纳证明（add/mul 引理、列表引理）。
- **多态与高阶**：隐式类型参数、`A -> B` 高阶参数、Church 编码、函数环境。
- **词法/预处理**：行注释、块注释。
- **真实程序形态**：解释器（Expr/eval/常量折叠）、列表库、证明片段、字节码 VM。

## 规模阶梯

`ladder_l07_{small,medium,large}` 三档同形态（同一生成模板，仅阶段数不同），
decl 数 48 / 198 / 798 ≈ 50 / 200 / 800。阶梯用「表达式定义 + eval + 累计求值」
模拟解释器前端的真实流水线，规模轴同时放大 decl 表与运行时求值链长度。

## 备注

- 抽取候选来自 `tools/bench_corpus/raw/L07`（`extract_tests.py` 从测试/README
  抽出后经本目录 `--validate` 复筛）；raw 池中的错误案例/片段均未进入本目录。
- 未做任何计时口径调优（只跑 `--validate` 与一次单轮 basic 量级 sanity）；
  正式计时由驱动统一执行。
