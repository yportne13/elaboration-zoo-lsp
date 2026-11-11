# L09 语料清单（MLTT 分层宇宙）

全部 34 个 `.typort` 均通过 `realbench --layer L09 --validate`（参考版 run Ok + 孪生 nf 闸门），合计 2508 行。

验证命令：

```bash
.\target\release\realbench.exe --layer L09 --corpus tools\bench_corpus\L09 --validate
```

| 文件 | 来源 | 覆盖特性 | 行数 |
|---|---|---|---|
| `extract_01.typort` | 抽取 | Type-N宇宙分层、println输出、隐式参数、递归 | 41 |
| `extract_02.typort` | 抽取 | Type-N宇宙分层、struct/投影、println输出、隐式参数、lambda、递归 | 30 |
| `extract_03.typort` | 抽取 | match、println输出、隐式参数、lambda、递归 | 37 |
| `extract_04.typort` | 抽取 | match、隐式参数、lambda、递归 | 18 |
| `extract_05.typort` | 抽取 | match、隐式参数、lambda、递归 | 20 |
| `extract_06.typort` | 抽取 | match、println输出、隐式参数、lambda、递归 | 32 |
| `extract_07.typort` | 抽取 | Type-N宇宙分层、match、println输出、lambda、递归 | 27 |
| `extract_08.typort` | 抽取 | match、println输出、lambda、递归 | 13 |
| `extract_09.typort` | 抽取 | match、println输出、lambda、递归 | 25 |
| `extract_10.typort` | 抽取 | Type-N宇宙分层、隐式参数、lambda、递归 | 8 |
| `extract_11.typort` | 抽取 | match、隐式参数、lambda、递归 | 32 |
| `extract_12.typort` | 抽取 | match、println输出、lambda、递归 | 27 |
| `extract_13.typort` | 抽取 | struct/投影、println输出、递归 | 15 |
| `extract_14.typort` | 抽取 | 字符串拼接、println输出、递归 | 8 |
| `extract_15.typort` | 抽取 | match、println输出、lambda、递归 | 23 |
| `extract_16.typort` | 抽取 | struct/投影、println输出、递归 | 17 |
| `extract_17.typort` | 抽取 | Type-N宇宙分层、字符串拼接、println输出、递归 | 14 |
| `extract_18.typort` | 抽取 | match、println输出、lambda、递归 | 33 |
| `extract_19.typort` | 抽取 | match、println输出、lambda、递归 | 23 |
| `extract_20.typort` | 抽取 | GADT索引枚举、match、lambda | 15 |
| `extract_21.typort` | 抽取 | match、println输出、隐式参数、lambda、递归 | 18 |
| `extract_22.typort` | 抽取 | match、隐式参数、lambda | 14 |
| `extract_23.typort` | 抽取 | match、println输出、lambda、递归 | 20 |
| `extract_24.typort` | 抽取 | struct/投影、println输出、递归 | 15 |
| `extract_25.typort` | 抽取 | println输出、递归 | 13 |
| `extract_26.typort` | 抽取 | struct/投影、println输出、递归 | 10 |
| `extract_27.typort` | 抽取 | Type-N宇宙分层、println输出、隐式参数、递归 | 9 |
| `extract_28.typort` | 抽取 | match、println输出、隐式参数、lambda、递归 | 48 |
| `ladder_large.typort` | 手写骨架按规模生成 | match、println输出、隐式参数、lambda、递归 | 829 |
| `ladder_medium.typort` | 手写骨架按规模生成 | match、println输出、隐式参数、lambda、递归 | 229 |
| `ladder_small.typort` | 手写骨架按规模生成 | match、println输出、隐式参数、lambda、递归 | 79 |
| `proj_ast_pipeline.typort` | 手写 | GADT索引枚举、match、println输出、隐式参数、lambda、递归 | 256 |
| `proj_container_lib.typort` | 手写 | Type-N宇宙分层、struct/投影、match、println输出、隐式参数、lambda | 360 |
| `proj_universe_stack.typort` | 手写 | Type-N宇宙分层、struct/投影、match、println输出、隐式参数、lambda | 150 |

## 规模阶梯

| 文件 | 规模档位 | 声明的形状 |
|---|---|---|
| `ladder_small.typort` | ~50 decls | Nat 字面量登记 + GADT Eq 证明 + Vec 快照 |
| `ladder_medium.typort` | ~200 decls | 同上，登记表放大 |
| `ladder_large.typort` | ~800 decls | 同上，登记表放大 |

## 说明

- 抽取来源：`tests/l09_fast_parity.rs`（parity/golden 用例里参考版 run 为 Ok 的片段）；原始候选与来源行号见 `tools/bench_corpus/raw/L09/manifest.jsonl`。
- 手写项目级程序覆盖：跨 Type 0/1/2 的容器库（GADT Vec + Eq 证明 + 依赖 record）、AST 解释器/常量折叠 + GADT 类型化 AST 的依赖遍历、宇宙分层库（高宇宙 enum / 嵌套 Type / 依赖 witness）。
- 规模阶梯由固定骨架 + 等形态登记块生成（生成脚本仅作记录，不入目录）：声明数约 50 / 200 / 800。
- 已剔除：从 bench 模板抽出的 `{i}` 占位片段（不是可执行程序）；故意写错的 parity 错误用例；缺前置定义（outParam/rfl 等）的残缺片段。
