# L07 孪生封印记录（2026-11-22）

> 决定：**L07 的孪生（`src/L07_sum_type/bump_spine_iter/`）不再参与门禁与 parity 契约**。
> 代码保留（作对照/取证），但默认构建的测试套件不再运行它；需要复核时用 feature 打开。

## 为什么封印

`tests/l07_fast_parity.rs`（99 例）和 `tests/l07_blackbox_v3.rs` 的 F/H 节（7 例，含
`redex_family_full_parity_scan`）对 ref 与孪生做**逐字节**比对，Err 文案也在内。这曾把参考版的
"解的 λ 命名 / 束定形状"钉死：向 smalltt 对齐的 `lams sp`（解的 λ 取自 spine、binder 名自动生成）
在语义上通过全部行为测试，却因错误文案里的 binder 名与孪生不同（ref `x2` / twin `z`）被 parity
扫描判失败（见 `docs/l07-vunfold-research-2026-11-21.md` §6.12）。

对齐 smalltt 的下一步（值层 arena / rigidQuote / pruning-context meta）必然改变解的内部形状，
因此必须先解除这条约束。

## 封印方式（可逆）

1. `Cargo.toml` 新增 feature `l07-twin`（**默认关闭**，`[features]` 段内）；
2. `tests/l07_fast_parity.rs` 首行 `#![cfg(feature = "l07-twin")]` —— 默认该目标 0 测试；
3. `tests/l07_blackbox_v3.rs` 的 F/H 节：`use ... as fast`、`run_fast`、`assert_parity`、
   `assert_full_parity`、`assert_terminates_full_parity` 与 7 个 parity/redex 测试全部
   `#[cfg(feature = "l07-twin")]`（embedded lib 测试**保留**，默认 111 = 118 − 7）；
4. `src/L07_sum_type/bump_spine_iter.rs` 顶部加 SEALED 说明；
5. 模块本身**仍然编译**（bench 的 `--only fast_ss` / `smallttbench` 的 twin 列可显式使用），
   只是不再是门禁的一部分。

## 复核方式

```powershell
# 默认（封印）：fast_parity 0 测试；v3 111 例
cargo test --test l07_fast_parity --test l07_blackbox_v3
# 打开封印（复核孪生）：fast_parity 99 例；v3 118 例
cargo test --features l07-twin --test l07_fast_parity
# ^ l07_blackbox_v3 在 2026-11-24 硬封印时改挂 umbrella `twins`（不再吃 l07-twin）：
cargo test --features twins --test l07_blackbox_v3
```

## 影响面

- 其他层（L01–L06、L08–L13）的孪生与 parity 契约**不变**；
- `l07_fast_parity` 之外没有任何 L07 门禁依赖孪生；
- `realbench` / `smallttbench` / `l07bench` 的 twin 列仍可运行（显式口径，不作默认）。

