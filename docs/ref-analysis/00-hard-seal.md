# 孪生引擎硬封印 · 实施记录（2026-11-24）

> 承接 [../compare-l07-l12-shared/BACKPORT.md](../compare-l07-l12-shared/BACKPORT.md)（回灌撤销）
> 与 [../compare-l07-l12-shared/FINAL.md](../compare-l07-l12-shared/FINAL.md) §11（分类更正）。
> 目标：**"封印"从"不进门禁"升级为"默认不编译"**，让 L06–L12 孪生彻底退出日常构建。

## 0 结果

| 验证 | 结果 |
|---|---|
| `cargo check --lib`（默认，无 feature） | 通过；构建日志里 **L06–L12 的 `bump_spine_iter` 零命中**（只剩 L13，见 §3） |
| `cargo check --all-targets` | 通过 |
| `cargo check --all-targets --features twins` | 通过（bench 面完整恢复） |
| `cargo test --lib` | **1269 passed / 0 failed**（封印前 1280–1281；差的 11–12 例正是被排除的孪生单测） |
| `cargo test --tests` | 全绿，**唯一失败是 `namespace_tests` 的 2 例，与本轮无关**（见 §4） |

**退出默认构建的代码量**：L06 4,740 + L07 7,976 + L08 7,722 + L09 7,863 + L10 8,382 + L11 8,394 + L12 8,494
= **53,571 行**（按 `bump_spine_iter*` 目录统计）。

## 1 改了什么

### 1.1 `Cargo.toml`

- 新增 `l06-twin = []`（L07–L12 已有）；
- 新增 umbrella **`twins = ["l06-twin", "l07-twin", "l08-twin", "l09-twin", "l10-twin", "l11-twin", "l12-twin"]`**
  —— **L13 故意不在里面**（理由见 §3）；
- 11 个 `[[bin]]` 加 `required-features = ["twins"]`：
  `l06bench` `l07bench` `l08bench` `l09bench` `l10bench` `l11bench` `l11repro` `l12bench`
  `realbench` `smallttbench` `l06l13mem`。

### 1.2 模块门（7 个 `mod.rs`）

`L06_string` `L07_sum_type` `L08_product_type` `L09_mltt` `L10_typeclass` `L11_macro` `L12_canonical`
的 `pub(crate) mod bump_spine_iter;` 一律改为：

```rust
// 硬封印（2026-11-24）：孪生引擎默认不编译，见 Cargo.toml `twins`。
#[cfg(feature = "lNN-twin")]
pub(crate) mod bump_spine_iter;
```

### 1.3 测试门（6 个 `tests/*.rs` 加 `#![cfg(feature = "twins")]`）

`l06_blackbox.rs` `l06_blackbox_v2.rs` `l06_blackbox_v3.rs` `l06_lsp_surface.rs`
`l07_blackbox_v3.rs` `implicit_comma_args.rs`。

> `l07_fast_parity`…`l12_fast_parity` 本来就有 `#![cfg(feature = "lNN-twin")]`，无需改。

## 2 覆盖代价（**必须知道**）

封印后默认 `cargo test` 少了 L06–L12 的孪生单测（约 11–12 例），以及被 gate 掉的 6 个双 oracle 套件的
**全部**用例。其中一部分是"只有孪生才有"的对照（本来就该消失），但**另一部分是参考版也需要的行为断言**
——这部分是真损失，见 [04-hard-seal-fallout.md](04-hard-seal-fallout.md) 的盘点。

## 3 为什么 L13 没封（阻断点，已核）

`src/lib.rs` 的 `Engine::lsp_default` **默认选 L13 孪生**：

| 锚点 | 内容 |
|---|---|
| `src/lib.rs:274` | `/// **Default**: the LSP runs on the twin.` |
| `src/lib.rs:278-279` | `Engine::lsp_default`（server 唯一构造器）选 twin，除非 `TYPORT_LSP_ENGINE=reference` |
| `src/lib.rs:359-362` | `struct TwinResident { tycker: L13_namespace::bump_spine_iter::Tycker }` |
| `src/lib.rs:1457`、`:1568` | 两处直接 `L13_namespace::bump_spine_iter::Tycker::new()` |

**性能/内存代价（`src/lib.rs:264-279` 自述）**：HDL 负载 steady state 下
**359 ms → 102 ms / kick（约 3.5x）**；常驻内存 **200 MB → 730 MB peak（约 2.2x 内存换 CPU）**。

⇒ 封印 L13 = **LSP 引擎停摆或性能回退 3.5x**，这是产品决策，不是清理。
**前置条件**：先让 L13 参考版接管 LSP 路径。可执行清单见 [03-lsp-on-reference.md](03-lsp-on-reference.md)。

## 4 与本次封印无关的既有失败（已隔离证明）

`cargo test --tests` 里 `namespace_tests` 有 2 例失败：

```
cross_file_inherent_method_dispatches          panicked at src/L13_namespace/mod.rs:2756
closing_and_reopening_inherent_provider_keeps_dispatch  同上
index out of bounds: the len is 2869 but the index is 2874
```

判定"与封印无关"的三条证据：
1. 失败点是 `lookup_meta` 的 `&self.meta[m.0 as usize]`（`src/L13_namespace/mod.rs:2756`）——**L13 参考版**，
   本轮在 L13 上一行未改；
2. `tests/namespace_tests.rs` 全仓 **不引用任何 `bump_spine_iter`**（已 grep 全量）；
3. 工作区在本轮开始前就有 L13 未提交改动（`mod.rs`/`compiler.rs`/`debug_test.rs`/`pattern_match.rs`/`pretty.rs`）。

**但这是个真 bug**：`lookup_meta` 无界索引，越界即 panic 而非报错。MetaVar 可能指向已越界的槽
（meta 表在回滚/重放路径上被截断）。建议单开 issue，优先级高于本轮的封印工作。

## 5 复跑方式

```powershell
cargo check --all-targets                  # 默认：孪生不编译
cargo test --lib                           # 1269 passed
cargo check --all-targets --features twins # 恢复 bench / 双 oracle 套件
cargo test --features twins --test l12_fast_parity
```

> `twins` 是 umbrella；只复核某一层时用单层 feature，例如 `--features l07-twin`。
