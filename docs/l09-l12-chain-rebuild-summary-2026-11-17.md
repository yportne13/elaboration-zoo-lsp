# L09–L12 链重建总结（2026-11-17）

本文件是“从 L09 开始逐章重构”这条工作的权威收口记录：方法、提交、每层
增量与门禁结果、跨层验证、偏差登记，以及“轻量复核 / 重型复核”的命令分层。
L13 的定位与决策见 `docs/l13-rebase-decision-2026-11-17.md`。

## 1. 方法

- 起点：`master 44a42f8b`；先做备份分支/标签（均已推远端）：
  `backup/master-pre-rearch-20261117`、`pre-rearch-20261117`。
- 规则：**第 N 层 = 第 N-1 层源码为基线 + 本章新特性**；上一层的实现思路
  （模块划分、decl 表名字世界、值表示、精化载体、守卫、双引擎、测试结构）
  原样承接；本章增量只做语言/机制新增。
- 每层完成后：层内 lib/parity/黑盒 + 跨层门禁全绿 → 提交 → 推送。

## 2. 提交与增量

| 层 | 提交 | 基线 | 本章增量 |
|---|---|---|---|
| L09 | `b6f4ca34` | L08（dpm-nbe/decl 表/双引擎） | `Type N` 分层宇宙：`Tm/Val::U(u32)`、`Type N` 语法、`check_universe`（meta 解 U(0)）、Π 取 max、enum `universe_lvl`；恢复 decl 表名字世界与 `tests.rs` |
| L10 | `1220b8a1` | 新 L09 | trait/typeclass：parser 的 `trait/impl/for/this`、共享 Prolog `Synth`、`Infer` 三表、`fresh_meta` trait 推迟、`solve_*_trait`、`TraitDecl/ImplDecl` 脱糖、`trait_wrap` 接收者方法 |
| L11 | `13c4e56f` | 新 L10 | macro_rules：宏文法（token/元变量/重复）、`MacroState`、解析期 token 拼接展开、深度护栏、`#[macro_export]`、内建 `stringify` |
| L12 | `73d68cf2` | 新 L11 | Val 级 trait 求解（去 `Typ` 桥接、`val_match` 单向匹配、孪生 `v_to_val`）、`Tm::Call`/`Val::Call` 节点与透明语义 |
| 文档 | `5b91c08e` | — | L13 决策 + 审计附录 D |
| 文档 | `cdd44a5e` | — | L13 重定基 P0–P5 方案（实测规模/delta） |
| 文档 | `6359cdc5` | — | L13 增量行为基线（脚本/说明/首批 11/32） |

## 3. 每层门禁（重建完成时的实测值）

| 层 | lib | parity | 黑盒 | 基准自检 |
|---|---:|---:|---:|---|
| L09 | 83 | 121 | 60 + 1 ignored | `l09bench --workload all` 7 负载互检通过；`realbench L09` common pass=6 |
| L10 | 86 | 128 | 65 + 1 ignored | `l10bench` 8 负载（含 traitchain）；`realbench L10` pass=6 |
| L11 | 88 | 133 | 67 + 1 ignored | `l11bench` 9 负载（含 macro）；`realbench L11` pass=6 |
| L12 | 88 | 136 | 67 + 1 ignored | `l12bench` 9 负载（含 traitchain/macro）；`realbench L12` pass=6 |

跨层门禁（L09–L12 重建完成后同一轮实测）：

| 套件 | 通过数 |
|---|---:|
| `tests/gadt_refine_cross_layer_tests.rs` | 265 |
| `tests/prim_identity_cross_layer.rs` | 258 |
| `tests/implicit_comma_args.rs` | 521 |
| `tests/audit_crosslayer_probe.rs` | 258 |
| `tests/backport3_pretty_l0910.rs` | 174 |

L13（未修改源码）同期实测：`cargo test --lib L13_namespace::` 615 passed +
6 ignored；`l13_fast_parity` 630 passed + 6 ignored。

## 4. 链一致性设计取舍（各层 README 有细节）

- 名字世界统一 decl 表（`Tm::Decl`/`Val::Decl`/`DeclEntry`），撤销 L09/L10 旧
  `Infer.global` + `1919810` 哨兵；
- 解析契约统一 L08 严格 `Err`（不再继承旧 L09+ 的恢复式 parser）；
- trait 身份按 decl 名在 `trait_out_param` 判形，不新增 `is_trait` 变体；
- prim 模型统一为“名字 + spine”（撤销 env 槽式 prim）；
- 双引擎同步：参考版（owned `Val`/`Rc<Tm>`）与 `bump_spine_iter` 孪生逐层
  同构，parity 判据 = Ok 逐字节 / Err 判定 + span 归一化正文；
- L12 偏差登记：canonical iddfs/search 不移植（新链无 Err-retry 消费点）、
  SmolStr 化不采用、算符中缀/namespace 不在继承面、Call 自动 quote 包装停用
  （避免 ref/twin 显示分叉）。

## 5. 复核命令分层（重要：不要随手跑重型套件）

**轻量（单次几秒，可随时跑）**

```powershell
git status --short; git log --oneline -3
cargo check --release --lib        # 增量编译后通常数秒
cargo test --release --lib L12_canonical::tests::test_trait -- --test-threads=1  # 单测
```

**重型（需专用窗口、拆批限时；2026-11-17 曾把 DSH 跑崩）**

- 全量层内 lib / parity / 黑盒（L13 615/630 各约 2 分钟）；
- `l13bench --file` 的 hdl prelude 批量（单个数秒；禁止一次性全量）；
- `realbench` 跨层矩阵与内存工具。

轻量复核只证明“能编译 + 抽查”，不能替代重型门禁；交付/合并前需在专用
窗口按“单层单套件、限时、失败即停”重跑。

## 6. 收口记录（2026-11-18）

- 用户指令“继续”且未选择 L13 完整重定基（B）；按本文件与审计报告的推荐默认，
  采用 **L13 产品层独立口径（A）** 收口：L09–L12 链重建完成，L13 源码零修改，
  其定位/差异/重定基方案与基线均已在 docs/ 登记（5b91c08e / cdd44a5e /
  6359cdc5 / 552a15de）。
- 收口时的轻量复核：cargo check --release --lib 通过（26.8s，0 error），
  git status 与远端同步（master 552a15de）。按用户要求，**未重跑** 615/630
  级重型套件与 hdl/prelude 批量基准；此前各层门禁/基准实测值见 §3。
- 若未来要做 B（L13 完整重定基）：从
  docs/l13-p1-double-carrier-design-2026-11-17.md 的 P1.1 小批 spike 开始，
  并先在专用重跑窗口冻结/校验基线。