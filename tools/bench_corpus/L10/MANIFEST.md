# L10 语料清单（trait / typeclass）

全部 22 个 `.typort` 均通过 `realbench --layer L10 --validate`（参考版 run Ok + 孪生 nf 闸门），合计 4838 行。

验证命令：

```bash
.\target\release\realbench.exe --layer L10 --corpus tools\bench_corpus\L10 --validate
```

| 文件 | 来源 | 覆盖特性 | 行数 |
|---|---|---|---|
| `extract_01.typort` | 抽取 | struct/投影、println输出、递归 | 22 |
| `extract_02.typort` | 抽取 | match、trait声明、impl/实例、println输出、隐式参数、lambda | 23 |
| `extract_03.typort` | 抽取 | Type-N宇宙分层、隐式参数、lambda、递归 | 8 |
| `extract_04.typort` | 抽取 | match、trait声明、impl/实例、println输出、隐式参数、lambda | 38 |
| `extract_05.typort` | 抽取 | Type-N宇宙分层、match、trait声明、impl/实例、outParam、println输出 | 28 |
| `extract_06.typort` | 抽取 | struct/投影、match、println输出、lambda、递归 | 29 |
| `extract_07.typort` | 抽取 | Type-N宇宙分层、println输出、递归 | 7 |
| `extract_08.typort` | 抽取 | match、println输出、lambda、递归 | 19 |
| `extract_09.typort` | 抽取 | match、println输出、隐式参数、lambda、递归 | 19 |
| `extract_10.typort` | 抽取 | println输出、递归 | 18 |
| `extract_11.typort` | 抽取 | match、println输出、lambda、递归 | 23 |
| `extract_12.typort` | 抽取 | println输出、递归 | 13 |
| `extract_13.typort` | 抽取 | struct/投影、println输出、递归 | 10 |
| `extract_14.typort` | 抽取 | Type-N宇宙分层、println输出、隐式参数、递归 | 9 |
| `fix_add_dotcall.typort` | 抽取+修补 | Type-N宇宙分层、match、trait声明、impl/实例、outParam、println输出 | 29 |
| `fix_add_generic.typort` | 抽取+修补 | Type-N宇宙分层、match、trait声明、impl/实例、outParam、println输出 | 35 |
| `fix_eq_rfl_witness.typort` | 抽取+修补 | struct/投影、println输出、隐式参数、递归 | 21 |
| `ladder_large.typort` | 手写骨架按规模生成 | struct/投影、match、trait声明、impl/实例、outParam、字符串拼接 | 3191 |
| `ladder_medium.typort` | 手写骨架按规模生成 | struct/投影、match、trait声明、impl/实例、outParam、字符串拼接 | 791 |
| `ladder_small.typort` | 手写骨架按规模生成 | struct/投影、match、trait声明、impl/实例、outParam、字符串拼接 | 191 |
| `proj_numeric_registry.typort` | 手写 | Type-N宇宙分层、struct/投影、match、trait声明、impl/实例、outParam | 157 |
| `proj_show_family.typort` | 手写 | Type-N宇宙分层、match、trait声明、impl/实例、outParam、字符串拼接 | 157 |

## 规模阶梯

| 文件 | 规模档位 | 声明的形状 |
|---|---|---|
| `ladder_small.typort` | ~50 decls | Tag trait + 字典 renderer + 逐 register 的 Tag 实例 |
| `ladder_medium.typort` | ~200 decls | 同上，实例注册表放大 |
| `ladder_large.typort` | ~800 decls | 同上，实例注册表放大 |

## 说明

- 抽取来源：`tests/l10_fast_parity.rs`（parity/golden 用例里参考版 run 为 Ok 的片段）；`fix_*.typort` 是抽取后补齐缺失前置声明（`outParam`、`rfl`）的修补版。原始候选与来源行号见 `tools/bench_corpus/raw/L10/manifest.jsonl`。
- 手写项目级程序覆盖：ToString/Pretty/Say/Num/Add(outParam) 的字典分发与 superclass 式默认实现（默认方法以库函数 + 显式字典实现）、`impl Add[Money, Money]` 等多实例数值类、`Tag`/`Report` 注册表（generated-looking register 类型 + 每类型实例 + 默认 renderer）。
- L10 语言面限制（已在语料中规避并在报告中登记）：无 supertrait、无 trait 默认方法体、无实例依赖（dependencies 恒空），故「superclass / 默认方法」以显式字典参数的库函数实现；复杂 inherent impl、泛型容器值、经 dot-call 的递归 def 会触发孪生 nf 闸门失败/panic，一律不进语料。
- 规模阶梯由固定骨架 + 等形态实例注册块生成（生成脚本仅作记录，不入目录）：声明数约 50 / 200 / 800。
