# L13 重定基决策记录（2026-11-17）

## 背景

2026-11-17 起，L09–L12 已按“每章 = 上一章实现思路 + 本章新特性”完成重建并
逐层提交推送（`b6f4ca34` → `1220b8a1` → `13c4e56f` → `73d68cf2`）：

| 层 | 基线 | 本章增量 | 提交 |
|---|---|---|---|
| L09 | L08（dpm-nbe/decl 表） | `Type N` 分层宇宙 | `b6f4ca34` |
| L10 | 新 L09 | trait/typeclass（`Synth` 实例求解） | `1220b8a1` |
| L11 | 新 L10 | macro_rules（解析期展开） | `13c4e56f` |
| L12 | 新 L11 | Val 级 trait 求解 + Call 节点 | `73d68cf2` |

在此之后，按用户原始指令“从 L09 开始逐章重构”的最后一层是 L13。本文件记录
对 L13 的**评估结论**：本轮**不对 L13 做 copy-forward 重建**，并说明理由、
现状定位、与 L12 的核心差异以及后续可选路线。

## 评估

### 规模与耦合面

- L13 约 59.4k 行（参考版 17.8k / parser 7.2k / 孪生 19.1k / 层内测试 15.3k，
  25 个测试文件、613 个 `#[test]`；另有 LSP 端到端与 HDL/prelude 语料）。
- L13 是**产品层**：LSP（hover/completion/goto/quickfix/观察面）、HDL（reg/wire/
  always/模块图检查）、prelude/宏库、package/import/全限定 decl 键、原生 Nat、
  class 两阶段、Call/OpCall、termination/eval_budget 等，均与核心机深度耦合。
- 核心机血统与 L12 不同：`update_cxt`+refresh 精化路线（L07–L12 是 σ 显式替换）、
  原生 `u64` Nat、`Val::Decl` 按 package 限定键、prim 声明表、`Val::Call/OpCall`
  等；L13 的 25 个测试文件大量字面锁定这些行为。

### 若强行 copy-forward 重建的代价

- 需要把 L13 的产品面整体移植到新 L12 核心（或反向把新 L12 核心 graft 进 L13），
  涉及 40k+ 行非测试代码与全部 LSP/HDL 回归；
- 风险不在“编译”，而在 LSP 产品行为（语义 token、quickfix retry、prelude 加载、
  模块图约束）与 613 个层内测试/跨层语料的逐字节兼容；
- 收益主要是“链一致性”，而审计报告（`docs/l07-l13-implementation-audit-2026-11-16.md`
  §11.2/§7）已论证：L13 的定位是产品层，不应按章节 copy-forward 期待。

## 决策

1. **本轮 L13 保持现状**（不修改 `src/L13_namespace` 的代码）：它是产品层，
   独立维护；“L09–L12 链”与“L13 产品层”在文档中明确分层。
2. **停止在 L13 文档/模块头声称“继承 L05–L12 全部机制”**；L13 README 顶部
   增加链定位说明并指向本文件。
3. L13 的核心差异按“产品化增量 + 两条机制分叉”表述（见下表），不再要求与
   L12 逐机制同构。

## 新 L12 与 L13 的核心差异（对照表）

| 维度 | 新 L12（本轮重建） | L13（产品层，现状） | 影响 |
|---|---|---|---|
| 精化载体 | σ 显式替换（`Subst`/`Val::VSub`/`frcs`） | `update_cxt` + refresh | 同一 GADT/模式程序可能走不同路径；L13 的已知精化弱点与 L12 不同 |
| 名字世界 | decl 表（`SmolStr` 名键） | package/import + 全限定 decl 键 | 重定义/裸名/限定名解析行为分层 |
| 原生数据 | 无原生 Nat（Church 编码/构造子链） | 原生 `u64` Nat + 字面量守卫 | Nat 相关显示/性能/溢出语义不同 |
| prim 模型 | 名字 + spine（`Val::Prim(SmolStr, Spine)`） | prim 挂 decl 条目（`PrimFunc`） | 部分应用显示/归约时机差异 |
| Call/OpCall | `Tm::Call`/`Val::Call` 基础设施（不自动创建） | Call/OpCall 产品级内联（HDL regNext 等） | L13 的调用显示/内联语义更完整 |
| 终止/预算 | unify fuel + match 预算 | `eval_budget`/termination/看门狗 | L13 有产品级资源护栏，L12 无 |
| canonical 搜索 | 未移植（无消费点） | 保留 iddfs/search（quickfix retry） | L13 的 Err 重试路径独立 |
| LSP 观察面 | 无 | hover/completion/goto/quickfix/语义 token 等 | 产品层功能仅 L13 有 |

## 现状验证（本轮结束时的 L13 门禁）

- `cargo test --release --lib L13_namespace::`：通过（613 个层内用例；见本轮
  提交日志/终端记录）。
- `cargo test --release --test l13_fast_parity`：通过（参考版 ↔ 孪生 630 例，
  含 6 个 `#[ignore]` 深度探针）。
- 跨层门禁（含 L13）：`gadt_refine_cross_layer_tests` 265、
  `prim_identity_cross_layer` 258、`implicit_comma_args` 521、
  `audit_crosslayer_probe` 258、`backport3_pretty_l0910` 174，全绿。
- `realbench --layer L13` / `l13bench` 等产品层基准路径未改动（L13 源码零修改）。

## 后续可选路线（若未来要把 L13 也纳入 copy-forward）

1. **产品层维护模式（当前选择）**：L13 独立演进，只保证跨层语义/契约门禁通过；
   文档维护 L12↔L13 差异表（即上表）。
2. **大爆炸重定基**：以新 L12 为基线重建 L13 核心，再逐块移植 LSP/HDL/prelude；
   建议独立分支 + 备份，按“核心机 → prelude/宏 → HDL → LSP”分阶段，每阶段用
   现有 613 测试 + LSP 语料做门禁。工作量估计周级，风险集中在 LSP 产品行为。
3. **抽公共 crate**：把 parser/preprocess/pretty/bench harness 抽公共 crate，各层
   feature 化；L13 保留产品层差异作为 feature/配置而非复制（审计 §11.2 建议）。

## 复现与证据

- 备份：分支 `backup/master-pre-rearch-20261117`、标签 `pre-rearch-20261117`。
- L09–L12 重建提交：`b6f4ca34` / `1220b8a1` / `13c4e56f` / `73d68cf2`。
- 审计基线：`docs/l07-l13-implementation-audit-2026-11-16.md`。
