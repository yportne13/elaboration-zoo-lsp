# `bench_pre/` —— 重构前 L07 的快照（仅在基准里使用）

本目录**不是**语言分层，只是一份用于 A/B 的历史快照：`L07_sum_type/`
是显式替换重构（`ad08c63`）**之前**的 L07，即 `pm_defs` 事实表精化版。

它只被 `src/bin/pmabbench.rs` 通过 `#[path]` 引用，用来把"重构前 L07"与
"当前 L07"编进同一个二进制做同源同进程对撞：

```bash
cargo build --release --bin pmabbench
./target/release/pmabbench.exe --impls l07pre,l07 --sweep deep --sizes 16,32,64,128 --rounds 5
```

用途与结论见 `docs/perf-ab-l07l12-2026-09-16.md` §3.5：量化显式替换给
L07 模式匹配编译带来的常数级回归（deep/flat/wild 三种形态 +10~22%），
这也是 `docs/review-l07l12/d5-performance.md` P2-4 一直缺失的那个负载。

`lib.rs` 不引用本目录，所以它不参与库构建、不影响任何其它 target。

## 重新生成

内容取自 `ad08c63^`（= `b9d54fe`）：

```bash
rm -rf src/bench_pre/L07_sum_type
mkdir -p /tmp/pre
git archive b9d54fe src/L07_sum_type | tar -x -C /tmp/pre
mv /tmp/pre/src/L07_sum_type src/bench_pre/L07_sum_type
# 该版的 parser 宏内部硬编码了 `$crate::L07_sum_type::...`，模块改名后会解析到
# 当前的 L07（TokenKind 不可见）。仅作纯改名，无语义改动：
sed -i 's/crate::L07_sum_type/crate::L07_pre/g' src/bench_pre/L07_sum_type/parser/mod.rs
```

快照一旦落盘就**不要**跟随上游更新——它的价值就是冻结在重构前那一刻。
