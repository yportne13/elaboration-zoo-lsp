# 基线门禁（Lead 实测，2026-09-30）

- 评审工作树：`F:/projects/hermes/elaboration-zoo-lsp-review-l13`，分支 `review/l13-shared-perfect`
- 基线 revision：`350b35a27667f6197944fb886e2b66094bba1de4`（= master）
- `CARGO_TARGET_DIR=F:/projects/hermes/elaboration-zoo-lsp/target`（复用主线 target；磁盘仅剩 ~8 GB）
- 工具链：`rustc 1.98.1` / `cargo 1.98.1` / `edition 2024`

## 结果

| 门禁 | 结果 | 耗时 | 备注 |
|---|---|---|---|
| `cargo check --all-targets` | **0 error / 3218 warning** | 54.3s | 警告绝大多数来自 `src/bin/*bench*.rs` 用 `#[path]` 交叉编译 L04–L12，不在本次范围 |
| `cargo test --lib` | **885 用例：879 过 / 0 失败 / 6 ignored** | 72.2s（墙钟 2:41 含编译） | 见下方「历史崩溃」 |
| `cargo test --test l13_fast_parity` | **539 用例：533 过 / 0 失败 / 6 ignored** | 66.3s | 其中 411 个是 `#[path]` 重复执行的 lib 测试 |
| `cargo test --test twin_engine_tests` | **26/26 过 / 0 失败** | 94.3s | 孪生 LSP 接线唯一执行渠道 |
| `cargo test --test namespace_tests` | **30/30 过** | 8.4s | |
| `cargo test --test hdl_check_locations` | **2/2 过** | 9.1s | |
| `cargo test --test emit_tests` | **12/12 过** | 19.7s | |
| `cargo test --test lsp_protocol_robustness` | **11/11 过** | 0.09s | |

**基线全绿。**

## 历史崩溃的结论（重要）

`docs/review-l01l12/FINAL.md` 记录「`cargo test --lib` 约 3 分钟后在 L13 legacy 测试区间
`STATUS_ACCESS_VIOLATION` 崩溃」，并被该报告列为 L13 的已知问题。

**本次实测：已不复现。** `cargo test --lib` 退出码 0，885 用例全跑完（879 过 / 6 ignored），
无 ACCESS_VIOLATION、无 STACK_OVERFLOW。推测由 `review/l01l13-continuity` 轮次落地的两处
修复闭合（prelude 池 TLS 清缓存、twin `MetaSnap` 的 `Rc` 保命）。

⇒ 该条目作为「已修复并复验」记入最终报告，不再作为 open finding。

## 与基线的差异判据

任何后续改动只要导致以下任一情况，即为回归：

1. `cargo check --all-targets` 出现 error；
2. 上表任一测试套件的 passed 数下降或 failed 数上升；
3. 新增 `#[ignore]`（除非报告里给出理由并说明为何不能钉住）；
4. 输出字节/错误判定/panic 语义变化而没有独立证据。

## 复跑命令（Lead 专用）

```powershell
$env:CARGO_TARGET_DIR='F:\projects\hermes\elaboration-zoo-lsp\target'
Set-Location 'F:\projects\hermes\elaboration-zoo-lsp-review-l13'
cargo check --all-targets
cargo test --lib
cargo test --test l13_fast_parity
cargo test --test twin_engine_tests
```

仓库自带的 L13 门禁（`tools/gate_l13.sh`）等价于 lib + parity + twin_lsp 三件套，
可作为收尾门禁：`bash tools/gate_l13.sh`（需 bash；Windows 上 git-bash 可用）。

**注意**：CI（`.github/workflows/ci.yml`）的 `test` job 跑 `bash tools/gate_l13.sh` 但
runner 是 `ubuntu-latest`；历史上这个崩溃是 Windows 特有的，Linux CI 看不见它 ——
即「Windows 开发者必踩、CI 全绿」的盲区。本次复验已确认该盲区当前无害。
