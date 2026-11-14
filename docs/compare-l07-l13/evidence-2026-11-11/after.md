# L07 加固回灌 L08/L09 · 回灌后验收与性能 A/B（after）

> 采集时点：2026-11-12 00:50–01:20（Asia/Shanghai）
> 分支 `port/l07-hardening-l08-l09`；旧基线 = HEAD `0464150c`（回灌前）；新 = 回灌后。
> 配套文档：`../BACKPORT-2026-11-11.md`（方案与结论）；回灌前证据 `before.md`。

## 1. 验收矩阵（全部实测，cargo test/build）

| 目标 | 命令 | 结果 |
|---|---|---|
| L07 回归（确认回灌未动 L07） | `cargo test --lib L07_sum_type::` | 70 passed / 0 failed |
| L08 单测 | `cargo test --lib L08_product_type::` | **81 passed / 0 failed**（=L07 64 + L08 12 + 其它 5；含全部 P1–P11 回归） |
| L08 黑盒 v1 | `cargo test --test l08_blackbox` | 57 passed / 1 ignored |
| L08 黑盒 v2 | `cargo test --test l08_blackbox_v2` | 51 passed / 2 ignored |
| L08 parity（参考 vs 孪生） | `cargo test --test l08_fast_parity` | **116 passed / 0 failed**（1 例 P3 分档文案不对称已显式登记） |
| L09 单测 | `cargo test --lib L09_mltt::` | **17 passed / 0 failed**（10 原有 + 7 回灌回归） |
| L09 parity | `cargo test --test l09_fast_parity` | 46 passed / 0 failed |
| L09 黑盒（新增） | `cargo test --test l09_blackbox` | **82 passed / 0 failed**（65 黑盒 + 17 带入 lib） |
| release 构建 | `cargo build --release` | 全绿 |

### 1.1 逐项能力验收（回灌前缺 / 回灌后证据）

| 能力 | 回灌前（before.md） | 回灌后实测 |
|---|---|---|
| P11 深值 quote/occurs/struct_eq | L08/L09 1MB 栈**栈溢出** | L08 `deep_value_iterative_under_default_stack` ✅；L09 同名测试 ✅（10 万层 occurs+quote+pretty、4000 层 struct_eq） |
| P5 跨 meta 环 | L08 烧尽 fuel；L09 栈溢出 | 两层 `cross_meta_cycle_force_is_bounded` ✅（L07 环守卫同款输出） |
| P3 三档诊断 | L08/L09 无 API，用例编译失败 | 两层 `test_unify_kind_separates_absurd_from_undecided` ✅ |
| L09 pending splice | `v_app` panic（impossible apply） | `test_stuck_match_splice` / `..._applied_with_outer_binder` ✅（原 panic 消除） |
| P2 卡住 match 预算 | L09 无 | `test_stuck_match_equation_bounded` ✅（有界） |
| struct_eq pending 比较 | L08 无差异；L09 无模块 | L08 ✅；L09 新增 `struct_eq.rs` + `struct_eq_compares_match_pending_values` ✅ |
| P8 宽松合一收窄 | L08 带实参未知名 Decl 被静默判等 | L08 `loose_string_requires_empty_spine` ✅（L07 语义） |
| P10 Error/parse span | L08 单字段 Error、无 parse span | L08 `error_carries_pattern_span` / `parse_error_carries_span` ✅ |
| 文件 IO 失败契约 | L08 旧版 panic | 回灌后改为**卡住值**（L07 口径），v2 黑盒 3 例已按新契约更新 |

## 2. 性能 A/B（参考版 basic 列；old-new 交错，取 min）

### 2.1 L08

| workload | k | old (HEAD) ms | new (回灌后) ms | new/old |
|---|---:|---:|---:|---:|
| l08_church | 9 | 0.381 | 0.395 | 1.04× |
| l08_church | 10 | 0.724 | 0.708 | 0.98× |
| l08_church | 11 | 1.475 | 1.534 | 1.04× |
| l08_church | 12 | 3.166 | 3.478 | 1.10× |
| l08_church | 13 | 9.508 | 9.468 | 1.00× |
| l08_enum | 9 | 0.161 | 0.170 | 1.06× |
| l08_match | 9 | 0.077 | 0.083 | 1.08× |
| l08_match | 10 | 0.081 | 0.090 | 1.11× |
| l08_match | 11 | 0.088 | 0.096 | 1.09× |
| l08_match | 12 | 0.094 | 0.103 | 1.10× |
| l08_match | 13 | 0.100 | 0.110 | 1.10× |
| l08_struct | 9 | 2.734 | 2.806 | 1.03× |
| l08_struct | 10 | 5.586 | 5.665 | 1.01× |
| l08_struct | 11 | 11.834 | 11.838 | 1.00× |
| l08_struct | 12 | 24.029 | 24.602 | 1.02× |
| l08_struct | 13 | 48.850 | 50.621 | 1.04× |

### 2.2 L09（含最终性能修复：去掉 deep_chain 探测、始终走帧收集器）

| workload | k | old (HEAD) ms | new (回灌后) ms | new/old |
|---|---:|---:|---:|---:|
| l09_church | 9 | 0.652 | 0.673 | 1.03× |
| l09_church | 10 | 1.230 | 1.287 | 1.05× |
| l09_church | 11 | 2.533 | 2.623 | 1.04× |
| l09_church | 12 | 5.131 | 5.177 | 1.01× |
| l09_church | 13 | 11.889 | 12.823 | 1.08× |
| l09_enum | 9 | 0.653 | 0.674 | 1.03× |
| l09_match | 9 | 0.093 | 0.099 | 1.06× |
| l09_match | 10 | 0.101 | 0.108 | 1.07× |
| l09_match | 11 | 0.108 | 0.122 | 1.13× |
| l09_match | 12 | 0.118 | 0.129 | 1.09× |
| l09_match | 13 | 0.128 | 0.138 | 1.08× |
| l09_struct | 9 | 13.359 | 13.438 | 1.01× |
| l09_struct | 10 | 50.105 | 48.012 | 0.96× |
| l09_struct | 11 | 196.851 | 201.067 | 1.02× |
| l09_struct | 12 | 1111.927 | 1103.539 | 0.99× |
| l09_universe | 9 | 1.137 | 1.170 | 1.03× |
| l09_universe | 10 | 2.355 | 2.370 | 1.01× |
| l09_universe | 11 | 4.567 | 4.775 | 1.05× |
| l09_universe | 12 | 11.700 | 11.534 | 0.99× |
| l09_universe | 13 | 26.016 | 27.751 | 1.07× |

读法：L08 基本持平（match 小幅 +8~11%，绝对量 0.077→0.083ms；struct 深值负载无退化）；L09 在修复浅值探测后 struct 恢复旧版水平（ratio≈1.00），其余 +3~13% 属宿主抖动区间。**无系统性性能回退**。

原始日志：`ab2/*.txt`、`ab3/*.txt`、`ab2/ab-summary.json`、`ab3/ab-summary.json`。

## 3. 说明与局限

1. 宿主负载：同机不同时段 k=13 绝对数可差 2× 以上（例如 L07 church k=13 在 7.0～20.7ms 间波动）。本 A/B 用**同场交错**，比值可信；绝对值仅供量级参考。
2. L08 的 old 二进制构建于 HEAD（`ezl-gap-evidence/target/release`，deps 与 HEAD 一致）；L09 old 同。new 为回灌后构建。
3. 未跑全仓 `cargo test`（数千用例，超出本轮范围）；已覆盖 L07/L08/L09 的单测、黑盒、parity 三层门禁。
4. 孪生版未回灌（用户要求先不看），L08/L09 参考版现在领先孪生；L08 parity 已登记 P3 文案不对称，L09 parity 语料未触达新分叉。
