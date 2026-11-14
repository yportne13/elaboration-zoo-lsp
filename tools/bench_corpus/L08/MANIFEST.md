# L08 真实场景性能语料（product type / struct）

本目录是 `realbench --layer L08` 的真实语料集：从仓库测试/README 抽取并经
语义验证的 Typort 程序（`ex_*`）、手写的项目级程序（`hw_*`，侧重 struct/记录/
嵌套投影链），以及一组同形态规模阶梯（`ladder_*`）。**目录内只有 `.typort`
文件与本 MANIFEST.md**；所有文件均通过 `--validate` 闸门，无 SKIP。

## 验证结果

命令（HEAD 源码构建的驱动）：

```text
.\target\release\realbench.exe --layer L08 --corpus tools\bench_corpus\L08 --validate
```

结果：**PASS = 26，SKIP = 0**（`SUMMARY,L08,pass=26,skip=0`）。

闸门口径：参考版全流程 `run` 必须 Ok，且参考版与孪生版（`bump_spine_iter`）的
`bench_check_nf` 节点数一致且非 0。

规模与耗时（单轮 sanity，`--rounds 1 --only basic`；共享 CPU 下仅作量级参考）：

- 26 个文件合计 basic ≈ **77 ms**（`TOTAL,L08,26,1,1,76585,...`，µs 单位），
  落在验收区间 10–500 ms 内；其中 `ladder_l08_large.typort` 占大头。

## 文件清单

| 文件 | 来源 | 覆盖特性 | 行数 | decls | 档位 |
| --- | --- | --- | ---: | ---: | --- |
| ex_basic_lists_options.typort | 抽取 `tests/l08_fast_parity.rs :: parity_tests_rs_basic` | Bool/Nat/List/Option 基础 ADT、多态 map、println 输出 | 79 | 24 | 单例 |
| ex_bits_adder.typort | 抽取 `tests/l08_fast_parity.rs :: parity_tests_rs_eq_proofs`（内嵌 bits_adder 负载） | Vec GADT 索引族 + Product enum + 嵌套 match 全加器 | 54 | 9 | 单例 |
| ex_church_strings.typort | 抽取 `src/L08_product_type/tests.rs :: test_lambda_calculus_and_strings` | Church 编码、String builtin、enum Nat/add、λ 高阶 | 50 | 21 | 单例 |
| ex_dependent_match_vec.typort | 抽取 `tests/l08_blackbox.rs :: bb_dependent_match_runtime` | Vec 依赖 match（索引精化） | 25 | 7 | 单例 |
| ex_eq_reasoning.typort | 抽取 `tests/l08_blackbox.rs :: bb_eq_reasoning_print` | Eq GADT + cong/symm/trans 等式推理 | 41 | 14 | 单例 |
| ex_length_sum.typort | 抽取 `tests/l08_fast_parity.rs :: parity_tests_rs_generic_and_catch_all` | List 泛型函数 + catch-all 模式 | 37 | 8 | 单例 |
| ex_nested_list_patterns.typort | 抽取 `tests/l08_blackbox.rs :: bb_nested_patterns` | List 嵌套模式（second_or_zero） | 21 | 6 | 单例 |
| ex_option_map.typort | 抽取 `tests/l08_blackbox.rs :: bb_implicit_type_params` | Option 多态 map + 隐式类型参数 | 32 | 9 | 单例 |
| ex_proof_add_assoc.typort | 抽取 `src/L08_product_type/tests.rs :: test_eq_add_assoc` | add 结合律归纳证明 | 32 | 7 | 单例 |
| ex_proof_add_zero_right.typort | 抽取 `src/L08_product_type/tests.rs :: test_eq_add_zero_right` | add a zero 引理 | 32 | 7 | 单例 |
| ex_proof_symm.typort | 抽取 `src/L08_product_type/tests.rs :: test_occurs_check_keeps_legit_refinement` | Eq 对称 + occurs 检查路径 | 16 | 4 | 单例 |
| ex_struct_basic.typort | 抽取 `tests/l08_fast_parity.rs :: parity_product_basic` | struct Point/Unit、`new`、`Point.mk`、字段投影、println 显示 | 27 | 13 | 单例 |
| ex_struct_dependent_projection.typort | 抽取 `tests/l08_fast_parity.rs :: parity_product_dependent_check` | 依赖字段投影（`e.witness`/`e.proof` 精确类型） | 20 | 10 | 单例 |
| ex_struct_exists_proof.typort | 抽取 `src/L08_product_type/tests.rs :: test_product_dependent_check` | Sigma `Exists`：证明字段类型依赖 witness | 19 | 9 | 单例 |
| ex_struct_field_comments.typort | 抽取 `src/L08_product_type/tests.rs :: test_product_field_blank_lines` | struct 字段间注释/空行、`new P(...)` 投影 | 17 | 4 | 单例 |
| ex_struct_generic_point.typort | 抽取 `tests/l08_fast_parity.rs :: parity_product_generic` | 泛型 `struct Point[T]` + 记录加法（返回新记录） | 33 | 13 | 单例 |
| ex_struct_line_chains.typort | 抽取 `tests/l08_fast_parity.rs :: parity_product_chains_and_partial` | 嵌套 `Line`/`Point` + 投影链 `l.a.x` + `new` 部分应用 | 25 | 10 | 单例 |
| ex_struct_sigma_exists.typort | 抽取 `tests/l08_fast_parity.rs :: parity_product_dependent` | `Exists[A][P]` 依赖字段构造/投影/打印 | 32 | 14 | 单例 |
| ex_type_family.typort | 抽取 `tests/l08_blackbox.rs :: bb_stuck_match_typefamily` | 类型族 match（`V n` 依赖消除） | 28 | 8 | 单例 |
| ex_vec_indexed_projection.typort | 抽取 `tests/l08_blackbox.rs :: bb_indexed_family_projection` | Vec 索引投影 + head/length | 31 | 11 | 单例 |
| hw_geometry_records.typort | **手写**（项目级） | 几何记录库：`Point`/`Size`/`Rect`/泛型 `Box[A]`；类型级投影链（`r.origin.x`）与值级投影链（`(new Rect(...)).size.h`）、嵌套 `new`、记录更新（translate/widen/stretch/move）、`contains` 判定 | 180 | 75 | 项目级 |
| hw_record_algebra.typort | **手写**（项目级） | 泛型记录代数：`Pair[A,B]`（new 与 `Pair.mk` 两条构造路径、swap）、`Interval`/`Range`/`Wrapper` 嵌套记录 + 三层投影链（`w.inner.hi`）、区间交/裁剪/重叠、记录更新返回新记录 | 217 | 87 | 项目级 |
| hw_sensor_pipeline.typort | **手写**（项目级） | 传感器校准流水线：三层嵌套记录（`Sample`/`Reading`/`Calibration`）+ 深投影链 + 记录更新 + `List[Sample]` 上的 Option 查找/计数 + Sigma `Verified[A][P]` 依赖证明字段 | 215 | 77 | 项目级 |
| ladder_l08_small.typort | 生成（同形态阶梯） | 分层记录 schema：每层「`struct R_i` + `val_i = new R_i(zero, val_{i-1})`」2 decls，末尾多条不同深度投影链 | 187 | 55 | **small** |
| ladder_l08_medium.typort | 生成（同形态阶梯） | 同上，99 层 | 712 | 205 | **medium** |
| ladder_l08_large.typort | 生成（同形态阶梯） | 同上，399 层 | 2812 | 805 | **large** |

合计：26 文件 / 4974 行 / 87,666 字节。

## 覆盖特性分布

- **product type / struct**：`struct` 声明、`new Name(...)` 与 `Name.mk` 两种构造、
  空 struct（`Unit`）、泛型 struct、嵌套 `new`。
- **投影**：值级投影（接收者为构造子值）与 L08 新增的类型级投影（接收者只有类型，
  剥 `.mk` 类型链）；左结合多段投影链（`l.a.x`、`r.size.w`、`w.inner.hi`）。
- **依赖积（Sigma）**：`Exists[A][P]` / `Verified[A][P]` 的 proof 字段类型依赖
  witness，穿越依赖字段的投影得到精确类型。
- **和类型/依赖匹配（继承 L07）**：enum/GADT、索引族 Vec、嵌套模式、Eq 归纳证明。
- **真实程序形态**：几何记录库、泛型记录代数、传感器校准流水线（记录更新 +
  嵌套投影链）。

## 规模阶梯

`ladder_l08_{small,medium,large}` 三档同形态（同一生成模板，仅层数不同），
decl 数 55 / 205 / 805 ≈ 50 / 200 / 800。阶梯是「分层记录 schema + 嵌套记录值
+ 多深度投影链」，规模轴放大 struct 类型数、记录嵌套深度与类型级投影链长度。

## 备注

- 抽取候选来自 `tools/bench_corpus/raw/L08`（`extract_tests.py` 从测试/README
  抽出后经本目录 `--validate` 复筛）；raw 池中的错误案例/片段均未进入本目录。
- 未做任何计时口径调优（只跑 `--validate` 与一次单轮 basic 量级 sanity）；
  正式计时由驱动统一执行。
