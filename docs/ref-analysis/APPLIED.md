# 本轮已落地的改动（2026-11-24 / 25 凌晨）

> 承接 [FINAL.md](FINAL.md) §5 的 P0/P1 清单。**只列出真正改了的**，没改的见 §4。

## 1 验证结果（全部在本机实跑）

| # | 验证 | 结果 |
|---|---|---|
| 1 | `cargo check --all-targets`（默认 feature） | **通过**，0 error |
| 2 | `cargo test --test l06_ref_blackbox`（默认 feature） | **103 passed / 0 failed** |
| 3 | `cargo test --lib` | **1269 passed / 0 failed / 13 ignored** |
| 4 | `cargo test --features twins --tests` | **全部套件绿**（无 FAILED / 无 compile error） |
| 5 | `cargo test --features l13-twin --test l13_fast_parity -- --skip L13_namespace::` | **15 passed / 0 failed** |

## 2 P0

### P0-1 门禁堵漏（`tools/gate_l13.sh` + `.github/workflows/ci.yml`）

**问题**：被 feature 门关掉的 target 会编译成**空 crate**，此时 `test result: ok. 0 passed` 依旧
exit 0 —— 孪生硬封印后 L06–L13 的整套 parity/blackbox 都进入这个状态，门禁长期"绿而空"。

**改法**：
1. `tools/gate_l13.sh`
   - `run_suite()` 增加**例数下限**参数，解析 `test result` 行的 `N passed` 并与下限比较，
     低于下限直接 `fail=1`（日志里找不到 result 行也算失败）；
   - 下限与 `tools/gate_l13.ps1` 对齐：`MIN_LIB=500` / `MIN_PARITY=15` / `MIN_TWIN=27` /
     `MIN_HDL042=2`，均可用 `GATE_MIN_*` 环境变量覆盖；
   - **parity 件补上 `--features l13-twin`** —— 该 target 首行是 `#![cfg(feature = "l13-twin")]`，
     不带 feature 就是空跑（这正是它此前"绿而空"的原因）。
   - `bash -n tools/gate_l13.sh` 语法检查通过。
2. `.github/workflows/ci.yml` 新增 **`test-twins` job**：
   `cargo test --no-fail-fast --features twins,l13-twin`，独立 cache key
   （避免 feature 产物挤掉默认 profile 的缓存）。缺了它，默认 `cargo test` 永远看不到孪生面。

### P0-2 L06 参考版黑盒回收（`tests/l06_ref_blackbox.rs`，新建）

**问题**：`l06_blackbox*.rs` 全部改挂 `twins` 后，L06 的集成覆盖从 133 例掉到 10 例（**-92%**），
而其中大部分其实只依赖参考版。

**改法**：新建 1,457 行 / **89 个 `#[test]`** 的纯参考版套件（`L06_string::run`，零 feature 依赖）：
- `l06_blackbox_v3.rs` 回收 67/70、`l06_blackbox.rs` 回收 12/28、`l06_blackbox_v2.rs` 回收 10/10；
- `assert_parity` 删除，`assert_error_parity` → 只断言参考版；
- **3 例如实跳过**（`steady_state_redef_allowed_next_round` / `mixed_batch_parity_scan` /
  `redex_family_full_parity_scan`）——它们整体建立在 `fast::Tycker` 或纯 parity 网格上，无可断言面。
- 纯 parity 用例退化处理：保留参考版那半边并**用实测值钉住**（两处实测是 Err，用
  `assert_ref_rejects`，没有硬掰成 Ok）。

> 顺带发现：v1 里超出前 12 例的 16 例中还有 **13 例可参考版回收**，本次未越范围，可追加。

## 3 P1

### P1-4 `check_universe` 错误尾注去掉 Debug 转储

L07 的原始注释（`src/L07_sum_type/elaboration.rs:190-195`）明写"走 pretty 而非 Val 的 Debug 转储——
大值树会印出巨量结构且不可读"，L09 重写时把机制和理由一起丢了。已恢复：

| 层 | 锚点 | 改动 |
|---|---|---|
| L12 | `src/L12_canonical/elaboration.rs:214` | `"expected universe, got {:?}"` → `"{}" + pretty_tm(0, cxt.names(), &self.quote(...))` |
| L13 | `src/L13_namespace/elaboration.rs:994` | 同上（与本文件 `:1216` 的既有写法一致） |

前缀 `"expected universe, got"` 被 `l06_blackbox.rs:393-408` 等钉住，**只改尾部**，断言不受影响
（`--features twins` 下 6 个黑盒套件全绿已证）。

## 4 P2 与未做项

**已做（P2 的一部分）**：
- `src/L06_string..L12_canonical/bump_spine_iter.rs` 各加一段**硬封印说明**（默认不编译 + 正确的复核命令）；
- L07 banner 纠正：`l07_blackbox_v3` 改挂 umbrella `twins`，不再吃 `l07-twin`；
- `docs/l07-twin-sealed-2026-11-22.md:34` 的复核命令同步（照旧执行会静默跳过 47 例）。

**未做（按价值/风险排序，等你决定）**：

| 项 | 为什么没做 |
|---|---|
| **P0-3 给 L13 卡住 match 补值层实参** | **唯一可能出错答案的项**，但它是**产品引擎的语义改动**，必须先写 `(match x { cons(a,b) => a }) y` 的捕获回归用例、再动结构。一次改动同时影响 L13 全部匹配路径，不适合在长会话末尾盲改。**建议下一轮第一件事**。 |
| P1-5 回灌 `occurs_transitive` | 会改变合一失败判定，需配套环测试。 |
| P1-6 `solve_multi_trait` 无 trait 快路径 | ≤6 行，但会改解序；需要先有 trait parity 用例钉住解序不变。 |
| P1-7 `raw_pretty` 裸 `U` / `Tm::Call` 死节点 | 前者只影响渲染文本；后者要先决定"接线还是删"，是设计决策。 |
| P2-10 封印 L13 | 见 [03-lsp-on-reference.md](03-lsp-on-reference.md)，需先 `lsp_default` 改指 Reference + 解两处编译耦合。 |

## 5 插曲：磁盘写满

验证途中 `target/debug/incremental` 涨到 **84.3 GB**，把 F 盘写满（`os error 112`，构建归档
失败）。已删除该目录与 6 个历史 `target_*` 目录，回收 **73.9 GB**。
增量缓存是纯加速物，删除无副作用；但**这个仓的 `target/debug` 长期在 100 GB 量级，建议定期
`cargo clean -p` 或把 `CARGO_INCREMENTAL=0` 用在验证轮**。
