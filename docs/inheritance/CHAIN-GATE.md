# 链继承门禁（P7）上线记录（2026-11-25）

## 为什么要它

2026-09 那次链重建之后，没有任何门禁能回答"第 N 章还是不是第 N-1 章的后代"。
结果就是本轮实测到的两个断点（L08 丢整份 `observe.rs`、L09 长在旧 L08 上）在半年里无人察觉。
本门禁把"完全继承"从**口头约定**变成**可复跑红灯**。

## 组成

| 件 | 作用 |
|---|---|
| `tools/inherit_audit.py` | 生成账本（条目级 identical/changed/missing + keep） |
| `docs/inheritance/*.tsv`（6 份） | 六对转换的实测账本（入库，是门禁的**数据源**） |
| `docs/inheritance/allow-L*.tsv`（6 份） | 白名单：每条非 identical 必须有"结论 + 理由" |
| `tools/gen_allow.py` | 从账本按规则重生成白名单（改代码后重跑） |
| `tests/chain_inheritance.rs` | 门禁本体（2 个测试） |

## 门禁判据（`tests/chain_inheritance.rs`）

1. **keep 阈值**：每个转换的加权 line_keep 不低于阈值——
   L08 ≥ **0.94**、L09 ≥ 0.98、L10/L11/L12 ≥ 0.99、L13 ≥ 0.51（L13 为架构分叉，见其 triage）；
2. **零未登记退化**：账本里任何 `changed`/`missing` 条目，必须在 `allow-L*.tsv` 里有一行
   （文件 / 条目 / 结论 / 理由）。没登记 = 继承面私自退化 = **红灯**；
3. **白名单是活的**：allow 里每行必须仍对应账本里的非 identical 行（否则"过期条目，请删掉"），
   且理由长度 > 8 字符（禁止无脑填 `ok`）。

## 白名单结论文档（当前值）

| 白名单 | FROZEN（孪生封印） | FEATURE（本章新特性） | RENAME/PATH |
|---|---:|---:|---:|
| allow-L08 | 76 | 15 | 4 |
| allow-L09 | 24 | 59 | 6 |
| allow-L10 | 2 | 11 | 4 |
| allow-L11 | 1 | 10 | 4 |
| allow-L12 | 5 | 25 | 4 |
| allow-L13 | 210 | 522 | 7 |

## 用法

```powershell
python tools/inherit_audit.py --prev src/L07_sum_type --next src/L08_product_type `
  --out docs/inheritance/L07_sum_type-to-L08_product_type.tsv
python tools/gen_allow.py          # 账本变了以后重生成白名单（已登记条目会保留结论）
cargo test --release --test chain_inheritance
```

## 实测

`cargo test --release --test chain_inheritance` → **2 passed**（2026-11-25）。

## 已知限制

- 账本是**快照**，不是现场比对：改代码后必须重跑 `inherit_audit.py` 再跑门禁，否则门禁只验证"上次的快照"。
  后续可把 `inherit_audit` 的扫描逻辑搬进 Rust 单测，直接在 `cargo test` 里实时算。
- `keep` 阈值对 L13 目前只有 0.51（架构分叉的现状值），一旦做载体升级应同步抬高。
