# 04 · 硬封印的代价与善后清单（参考版视角）

> 对象：2026-11-24 的**硬封印**——L06–L12 孪生引擎默认不编译。
> 工作区 = HEAD `8f4287ae` + 本轮封印改动（Cargo.toml / 7 个 layer `mod.rs` / 11 个 `[[bin]]` / 6 个 `tests/*.rs`）。
> 口径：**只读**，未跑 `cargo build/check/test`。所有计数是静态计数（`#[test]` 行 + `macro_rules!` 展开，
> 2026-11-24 22:2x 快照），不依赖 Lead 的 `1269 passed`。
> 分级沿用 E0–E4。本文只判**封印的代价与善后**，不重复 01–03 分册的语义差异。

## 0 封印的机械事实（复核通过）

| # | 封印点 | 锚点 | 作用 |
|---|---|---|---|
| 1 | L06 孪生 mod 门 | `src/L06_string/mod.rs:24` | 默认不编译 `L06_string::bump_spine_iter` |
| 2 | L07 同上 | `src/L07_sum_type/mod.rs:106` | 同上 |
| 3 | L08 | `src/L08_product_type/mod.rs:57` | 同上 |
| 4 | L09 | `src/L09_mltt/mod.rs:51` | 同上 |
| 5 | L10 | `src/L10_typeclass/mod.rs:51` | 同上 |
| 6 | L11 | `src/L11_macro/mod.rs:49` | 同上 |
| 7 | L12 | `src/L12_canonical/mod.rs:50` | 同上 |
| 8 | umbrella feature | `Cargo.toml:219` | `twins = [l06-twin … l12-twin]` |
| 9 | 11 个 bin 的 `required-features` | `Cargo.toml:51,57,63,69,75,81,87,100,109,146,159` | bench／内存／复现工具默认不构建 |
| 10 | 6 个集成测试整 crate 关闭 | `tests/l06_blackbox.rs:1`、`l06_blackbox_v2.rs:1`、`l06_blackbox_v3.rs:1`、`l06_lsp_surface.rs:1`、`l07_blackbox_v3.rs:1`、`implicit_comma_args.rs:1` | 全部 `#![cfg(feature = "twins")]` |
| — | **L13 有意不在封印集** | `Cargo.toml:216` 注释 + `src/lib.rs:274`（`Engine::lsp_default`） | LSP 默认引擎仍是 L13 孪生 |

**11 个 bin 不是被误伤**：静态检索 `bump_spine_iter|run_fast|fast::` 命中数 l06bench 4 / l07bench 3 / l08bench 3 /
l09bench 3 / l10bench 3 / l11bench 8 / l12bench 9 / l11repro 7 / realbench 40 / smallttbench 42 / l06l13mem 63，
每个都真的驱动孪生 ⇒ `required-features` 属 E1（等价改写，无语义变化）。

## 1 (a) 覆盖损失盘点

### 1.1 lib 级：只丢 11 例，且对参考版是 0 损失

`cargo test --lib` 1280/1281 → 1269 的差额，全部来自被 gate 掉的**孪生内嵌测试模块**：

| 层 | 文件:行 | `#[test]` | 性质 | 对 ref 是损失吗 |
|---|---|---:|---|---|
| L06 | `src/L06_string/bump_spine_iter/entry.rs:471`（`:472 mod tests`） | 10 | C：孪生自身闭环 | 否 |
| L07 | `src/L07_sum_type/bump_spine_iter/entry.rs:363` | 1 | C | 否 |
| L08–L12 | 孪生 `entry.rs` 无 `#[cfg(test)]`（逐文件核过） | 0 | — | — |
| **合计** | | **11** | | **0** |

⇒ 参考版单测**一个没丢**。`1280/1281` 与 `1269` 的 11–12 差额以 **11** 为准；
余下 1 例 `[未核实]`——可能是封印前即失败的那条，与本封印无关。

### 1.2 集成 target 级：6 个文件共 **177 例**整体消失

分档口径（逐测试体核过，见 §1.3）：

- **A ＝「参考版也需要的」**：体内有独立于孪生的参考版断言（golden 串 / `assert_out` / `assert_lines` /
  `assert_err` / `assert_eq!(run_basic …)`）。**删掉 parity 调用即可恢复**。
- **B ＝「只有孪生才有」的对照**：断言只有 ref↔twin 比较（`assert_parity` / `assert_error_parity` /
  `assert_full_text_parity` / `both()` / `parity_case!`）。孪生不在，断言无对象。
- **C ＝ 孪生自身行为**：只驱动 `fast::Tycker`（稳态复用、节点计数、`run_fast` 幂等）。

| 文件 | 总 `#[test]` | A 可救 | B 纯对照 | C 孪生自身 | 备注（锚点） |
|---|---:|---:|---:|---:|---|
| `tests/l06_blackbox.rs` | 28 | 12 | 13 | 3 | A 例是 inline golden + `assert_parity`（`:94-106`）；C 例 `:447`／`:462`／`:518` |
| `tests/l06_blackbox_v2.rs` | 10 | 6 | 3 | 1 | C 例跨轮隔离 `:174` |
| `tests/l06_blackbox_v3.rs` | 70 | **52** | 17 | 1 | A 例全走 `assert_out`，而 `assert_out` 在 `:79-83` **先把 `assert_parity(src)` 内联**——解耦只需删那一行 |
| `tests/l06_lsp_surface.rs` | 15 | 0 | 15 | 0 | 全部经 `both()`（`:45-50`）对拍，ref 侧断言不独立 |
| `tests/l07_blackbox_v3.rs` | 47 | 39 | 8 | 0 | A–E 节（`:174-996`）只用 lib 的 `run` + `assert_lines`；F 节（`:998` 起）才 `#[path]` 引入孪生 |
| `tests/implicit_comma_args.rs` | 7 = 1 + 6 | 1 | 6 | 0 | 6 例是 `parity_case!` 宏展开（`:39-66`）；1 例 `:111` 是 ref golden（`:128-131` 断言输出含 `Id::refl(`） |
| **合计** | **177** | **110** | **62** | **5** | A:B:C = 62% : 35% : 3% |

### 1.3 判读：**真损失是 110 例，且 64% 集中在 L06**

| 判读项 | 数字 | 依据 |
|---|---:|---|
| 参考版**真损失**（A） | 110 例（L06 70 / L07 39 / comma 1） | 这些断言钉的是 ref 的打印形态、错误文案、prim/global 语义 |
| 只有孪生才有（B） | 62 例 | 孪生不存在时没有第二实现可对比 |
| 孪生自身（C） | 5 例 | `fast::Tycker` 专用，与 ref 无关 |
| 连 ref 一起归零的**层** | **L06 一个** | 全仓 `git grep -l L06_string -- tests` 只命中这 5 个文件，**全部**已在 `:1` 挂 `twins` |
| L07–L12 的 ref 未受影响 | 15 个文件，含 `l07_blackbox.rs`(49) / `l07_blackbox_v2.rs`(53) / `l08_blackbox.rs`(58) … / `l12_blackbox.rs`(68) | 这些文件 `twinRefs=0`，天生 ref-pure |

⇒ **L06 的结构性不幸**：L06 没有独立的 `l06_fast_parity.rs`——它的 parity 就写在 blackbox 里
（`docs/test-catalog.md:46` 明写"fast_parity 仅 L07 起（无 `l06_fast_parity.rs`）"）。
于是"把 parity 关掉"等于"把 L06 的 ref 黑盒整套关掉"：**133 例 → 10 例（lib），损失 92%**。
L07 起 parity 已分家（`tests/l07_fast_parity.rs:1` 等 6 个），所以只是掉 parity，不掉 ref。E3。

## 2 (b) 残留引用清单（按"会不会误导/会不会挂"排序）

| 位置 | 现状 | 影响 | 处置 |
|---|---|---|---|
| `src/L07_sum_type/bump_spine_iter.rs:8`、`L08…:4`、`L09…:5`、`L10…:5`、`L11…:5`、`L12…:5` | 写"复核：`cargo test --features lNN-twin`" | **命令已不够**：`tests/l07_blackbox_v3.rs:1` 挂的是 `twins`，只开 `l07-twin` 时该文件编译成 0 例 | 改注释 → `--features twins`（P0） |
| `src/L06_string/bump_spine_iter.rs:1` | **没有 SEALED banner**（L07–L12 六层都有） | L06 是唯一被封印却没写"已封印/怎么复核"的层，最危险 | 补 banner（P1） |
| `docs/l07-twin-sealed-2026-11-22.md:34` | `--features l07-twin --test l07_fast_parity --test l07_blackbox_v3` | 后半条已失效（要 `twins`），照跑得 0 例 | 改文档（P0） |
| `docs/l07-final-scope-2026-11-23.md:40` | "`--features l07-twin`（fast_parity 99 / v3 118 全绿）" | 命令与例数都不再成立 | 改文档（P1） |
| `docs/test-catalog.md:46` | "L06–L08 … `bump_spine_iter::run_fast`；`tests/l0X_blackbox*.rs`" | 默认门禁里 L06 blackbox 已是 0 例 | 改文档（P1） |
| `docs/test-catalog.md:234`（G6-20） | 把 `tests/implicit_comma_args.rs` 当 comma 语法跨章护网 | 该护网默认 0 例，L06–L12 的 `f[A, B]` 无回归钉 | 改文档 + 补 ref 版（P1） |
| `tools/run_realistic_bench.ps1:31`、`tools/smalltt_bench.ps1:18`、`tools/run_crosslayer_ref.ps1:25,52` | 提示"先跑 `cargo build --release --bin realbench / smallttbench / …`" | 该命令现在**必然失败**（缺 `--features twins`） | 改提示（P1） |
| `tools/mem_peak_ws.ps1:21-22` | 硬编码 L06–L13 → `l06bench`…`l12bench` | 7 个 bin 默认不构建，脚本按名解析会落空 | 改脚本（P1） |
| `tools/gate_l13.sh:85` | `cargo test --test l13_fast_parity`（**无** `--features l13-twin`） | 0 例静默通过；`.ps1` 本轮已修（`tools/gate_l13.ps1:11`），`.sh` 未跟 | 改脚本（P0，见 §3） |
| `src/lib.rs:361/1457/1568`（`L13_namespace::bump_spine_iter::Tycker`）、`src/lib.rs:1724`（引 `bump_spine_iter/machine.rs:2822…`）、`src/L13_namespace/bump_spine_iter.rs:275`（`pub use force::twin_mem_stats`） | 全部指向 **L13** 孪生 | **不是残留**：L13 仍默认编译、仍是 LSP 默认引擎 | 保留 |
| `tests/twin_engine_tests.rs`（28 例）、`tests/twin_engine_bench.rs`（4 例） | 名字带 twin，未 gate | 跑的是 `Engine::Twin`（默认引擎，`src/lib.rs:274`），仍有效 | 保留（勿误删） |

全仓范围核过一轮：`README.md` 无孪生字样（无需改）；真正会**挂**的只有 `tools/gate_l13.sh:85` 与
4 个工具脚本的 build 提示，其余是**会误导**（照文档复核得 0 例）。

## 3 (c) 门禁缺口：**默认门禁对 L06–L12 孪生 0 覆盖，对 L06 参考版近乎 0 覆盖**

| 门禁 | 入口 | 覆盖 L06–L12 ref？ | 覆盖 L06–L12 twin？ | 备注 |
|---|---|---|---|---|
| CI job `test` | `.github/workflows/ci.yml:46` → `tools/gate_l13.sh` | **不覆盖**（只跑 `--lib L13_namespace::`） | 不覆盖 | 门禁口径只认 L13 |
| gate parity 件 | `tools/gate_l13.sh:85` | — | **0 例**（缺 `--features l13-twin`） | `test result: ok. 0 passed` → exit 0 |
| CI job `test-full` | `.github/workflows/ci.yml:96` `cargo test --no-fail-fast` | 覆盖 L07–L12；**L06 只剩 10 例 lib** | **0 例**（6 parity + 6 blackbox target 编译成空 crate） | 空 crate 算"通过" |
| `cargo check --examples --tests` | `.github/workflows/ci.yml:54` | 只类型检查；**12 个 gate 文件的正文不再进入类型检查**（`#![cfg]` 在 crate 根） | 同 | 孪生位腐不可见 |
| `gate_l13.ps1` | `tools/gate_l13.ps1:11`、`:118`（`MinParity=15`） | — | 恢复 L13 parity | 本轮已修，仅 .ps1 |

三条硬结论：
1. **L06 参考版在默认门禁里只剩 10 例**（`src/L06_string/eval_budget.rs` 5 + `mod.rs` 1 + `surface.rs` 4），
   而 L07 有 67 lib + 118 集成、L08–L12 各 79~84 lib + 64~116 集成。**L06 成为全仓 ref 覆盖最薄的层**，落差约 20×。
2. **"0 例即绿"是本轮最危险的副作用**：6 个 `lNN_fast_parity` + 6 个 blackbox 编译成空 crate，
   `cargo test --test l07_fast_parity` 会打印 `ok. 0 passed` 且 exit 0；`gate_l13.sh` 没有最小例数闸，
   CI 会长期"绿而空"（`.ps1` 的 `MinParity` 是唯一防线）。
3. **位腐已经开始**：`#![cfg]` 在 crate 根 ⇒ 这 12 个文件的**类型检查**也一并消失。
   ref API 一改，只有 `--features twins` 构建才会暴露——而默认 CI 永不构建它。

## 4 (d) 善后清单（可执行）

| 优先级 | 动作 | 目标 | 类型 |
|---|---|---|---|
| P0 | 加独立 job：`cargo test --features twins --no-fail-fast`（可拆 `--test` 矩阵） | `.github/workflows/ci.yml:96` 之后 | **补**（防位腐） |
| P0 | parity 件补 `--features l13-twin`，并加"最少例数"闸（当前 0 例即绿） | `tools/gate_l13.sh:85` | 改 |
| P0 | L06 ref 黑盒重建：把 A 类 70 例的 ref 断言抽成不挂 twins 的 `tests/l06_ref_blackbox.rs`（12+6+52） | 源：`tests/l06_blackbox.rs:94-106`、`tests/l06_blackbox_v2.rs:144`、`tests/l06_blackbox_v3.rs:79-83` | **补** |
| P1 | `l07_blackbox_v3` 拆两 crate：A–E 节（`:174-996`，38 例）不挂 twins，F 节（`:998+`）留 gated | `tests/l07_blackbox_v3.rs:1` | 补 |
| P1 | `implicit_comma_args` 的 6 个 `parity_case!` 拆出 ref-only 版（宏里 `$m::run` 那半保留） | `tests/implicit_comma_args.rs:39-66` | 补 |
| P1 | `l06_lsp_surface`：先把 3 个与孪生无关的（默认关闭／预算／失败通道）转 ref-only | `tests/l06_lsp_surface.rs:150`、`:364`、`:335` | 补（其余归档） |
| P1 | 复核命令统一为 `--features twins`（6 处 `//! 复核`） | `src/L07…:8`、`L08…:4`、`L09…:5`、`L10…:5`、`L11…:5`、`L12…:5` | 改注释 |
| P1 | L06 孪生补 SEALED banner | `src/L06_string/bump_spine_iter.rs:1` | 改注释 |
| P1 | 4 个工具脚本的 build 提示补 `--features twins` | `tools/run_realistic_bench.ps1:31`、`tools/smalltt_bench.ps1:18`、`tools/run_crosslayer_ref.ps1:25`、`tools/mem_peak_ws.ps1:21` | 改注释 |
| P1 | 更新测试目录与 G6-20 口径 | `docs/test-catalog.md:46`、`:234` | 改文档 |
| P2 | **不删**孪生源码：L13 仍编译它，且 6 层孪生是 L13 引擎的血缘证据 | `src/L06_string/bump_spine_iter.rs` … | 保留 |
| P2 | **不删** 11 个 bin：都真引用孪生；只在工具文档注明"需 `--features twins`" | `Cargo.toml:51…159` | 保留 + 注释 |
| P2 | 归档 2026-11 前的孪生复核文档，避免"照文档跑必失败" | `docs/l07-twin-sealed-2026-11-22.md` 等 | 归档 |

## 5 「章节有意增量」与「顺手改的漂移」的分界

| 本轮改动 | 归类 | 依据 |
|---|---|---|
| 7 处 `#[cfg(feature = "lNN-twin")]` | **封印本体的有意增量**（E1） | 只改编译期可见性，ref 语义零变化 |
| `twins` umbrella + 11 个 `required-features` | 有意（E1） | 11 个 bin 全部真引用孪生（§0 计数） |
| 6 个 `tests/*.rs` 的 `#![cfg(feature = "twins")]` | **有意的粗放**（E2 级代价） | 关掉的不是"孪生那半边"，而是 **110 例 ref 断言**；L06 因此掉 92% 覆盖 |
| `tools/gate_l13.ps1` 加 `--features l13-twin` | **顺手改的越界修复**（不在 L06–L12 范围） | 方向正确：不修则 L13 parity 件绿而空（`:211` 起注释即此意） |
| 只改 `.ps1` 未改 `.sh` | **顺手改的遗漏**（E3） | CI 跑的是 `.sh`（`ci.yml:46`），修的那份没人跑 |

判读：正文封印本身干净（E1），**代价全在测试侧**；而本轮顺手带出的 L13 门禁修复
是"对但只做了一半"——两个脚本从此不一致，CI 侧仍是空跑。

## 结论摘要

硬封印的编译侧代价≈0（11 个单测全属孪生自身，ref 一个不丢），代价全在门禁：
6 个集成文件 **177 例**整体消失，其中 **110 例是参考版自己也需要的**（A 类），
62 例是纯对照、5 例属孪生自身。损失极不均匀——**L06 掉 92%**（133→10 例），
因为 L06 没有独立 parity 文件、把 parity 写进了 blackbox（`docs/test-catalog.md:46`）；
L07–L12 只掉 parity 不掉 ref。门禁侧更险：12 个 target 编译成空 crate 后
`0 passed` 仍是成功，而 CI 的 `gate_l13.sh:85` 正好缺 `--features l13-twin`，
`.ps1` 修了、`.sh` 没修。善后不是"补孪生"，而是**把 A 类 110 例搬到 ref 侧**、
统一复核命令为 `--features twins`、并给门禁加"最少例数"闸。

## 要改的东西 Top-3

1. **【P0·E3】给默认门禁补 `--features twins` 的独立 job，并给 `.sh` parity 件补 `--features l13-twin` + 最小例数闸**
   —— `.github/workflows/ci.yml:96` 旁新增 job；`tools/gate_l13.sh:85` 补参数，对齐 `tools/gate_l13.ps1:118` 的 `MinParity=15`。
   不做则 12 个 target 长期"绿而空"，ref API 一改就位腐。
2. **【P0·E3】把 A 类 110 例在 ref 侧重建（先做 L06 的 70 例）**
   —— 新建 `tests/l06_ref_blackbox.rs`（不挂 feature），素材取自 `tests/l06_blackbox_v3.rs:79-83`（`assert_out` 去掉内联的 `assert_parity` 即得 52 例）
   与 `tests/l06_blackbox.rs:94-106` 的 12 例 inline golden。否则 L06 ref 在默认门禁里只剩 10 例。
3. **【P1·E2 误导】复核命令与 banner 统一**
   —— `src/L07_sum_type/bump_spine_iter.rs:8`（及 L08 `:4`／L09 `:5`／L10 `:5`／L11 `:5`／L12 `:5`）的 `--features lNN-twin` → `--features twins`；
   `src/L06_string/bump_spine_iter.rs:1` 补 SEALED banner；`docs/l07-twin-sealed-2026-11-22.md:34` 的命令同步改。
   照旧命令复核会静默跳过 `l07_blackbox_v3` 全部 47 例。
