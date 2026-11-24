# 参考版（ref）差异与要改的东西 · 汇总

> 2026-11-24 第二轮。孪生已在 [00-hard-seal.md](00-hard-seal.md) 中硬封印（L06–L12 默认不编译），
> **从本轮起参考版是唯一在维护的实现**。四份分册：[01](01-ref-chain-delta.md) L06→L12 逐章增量、
> [02](02-l13-ref-outlier.md) L12→L13 离群点、[03](03-lsp-on-reference.md) L13 ref 接管 LSP、[04](04-hard-seal-fallout.md) 封印代价。
> 上一轮（L07↔L12，含孪生）见 [../compare-l07-l12-shared/FINAL.md](../compare-l07-l12-shared/FINAL.md)。

## 0 三句话

1. **参考版 L06→L12 是一条收敛的链**：L07 一次大改之后，各层只做"本章增量"（L10/L11 的声明级甚至是纯加法，
   L11 的引擎核心十个文件**逐字节零改动**）。真正的**非预期漂移只有 7 处**，且**全部集中在 L08/L09 两层的删改**。
2. **L13 不是"改坏"，是产品层膨胀 2.7×（81.3k→217.8k token）并换掉内核载体**。五条已知断点里
   **三条有意**、一条有意但漏了代价评估、一条只是文案顺手退化。
3. **封印的编译代价≈0（丢掉的 11 例全是孪生内嵌单测），代价全在测试与门禁**：
   177 例整体消失，其中 **110 例是参考版自己也需要的**；而 12 个 target 变成空 crate 后
   `ok. 0 passed` 仍算绿 —— 这是**我这次封印带进来的最大副作用**。

## 1 参考版血缘：收敛的链 + 一个膨胀的产品层

| 段 | 特性 | 关键事实 |
|---|---|---|
| L06→L07 | **一次大改** | 声明级 +160/−39；和类型 + 名字世界重构（`01` §2） |
| L08→L09 | **各删掉一整块与本章主题无关的基础设施** | L08 删 `observe.rs`+`prof`；L09 删 `println_spans`/`inlay_hint` 两通道 |
| L10/L11/L12 | **纯加法** | 各层只加 16/32/5 个符号；L11 引擎核心逐字节零改动 |
| L12→L13 | **膨胀 2.7× + 换载体** | 15 个同路径 ref 文件里只有 `unification.rs` 与 `pattern_match.rs` 还算同一机制（`02` §2） |

## 2 参考版"顺手改坏"的七项（`01` §3，本轮核心发现）

| # | 项 | 首次 | 性质 | 锚点 |
|---|---|---|---|---|
| 1 | `eval_budget` 被删 | L07 | E3 | — |
| 2 | `observe.rs` + `prof` 被删 | **L08** | E3（"减配"，非"从来没设计"） | `L08/elaboration.rs:375` |
| 3 | `println_spans` / `inlay_hint` 两通道被删 | L09 | E3 | — |
| 4 | 错误尾注 `{}`+`pretty_tm` → `{:?}` | L09 | **E2 退化**（L07 注释明文说过不能用 Debug） | `L12/elaboration.rs:214-216` ⟷ `L07:191-195` |
| 5 | `fin` 恒 `true`（丢"直取缓存 vs 重渲染"判定） | **L08** | E2 | `L08:375` → `L12:349` |
| 6 | 裸 `U` 渲染 `U` ⟷ `Type N` 两套 | L09 | E2（渲染不可回灌自解析） | `L12/raw_pretty.rs:29` ⟷ `pretty.rs:138` |
| 7 | `solve_multi_trait` 无 trait 也全扫 meta | L12 | E2（改解序 + 白扫） | `L12/unification.rs:751-765` |

## 3 L12→L13 五条断点的判定（`02` §3-§4）

| 断点 | 判定 | 依据 |
|---|---|---|
| 精化载体 σ/`subst_cxt` → `update_cxt`+`refresh` | **有意** | 提交与注释写明；`rebase/l13-on-l12` 上也没换回 |
| ~~缺 `VSpan`~~ | **E1，不是缺失** | L12 `VSpan(Rc<Span<String>>)` 只是"克隆不分配 + parity Debug 稳定"，L13 用 `Span<SmolStr>`（`mod.rs:909-915`）达同一目标 |
| 覆盖义务方向（Undecided 不计义务） | **有意** | `L13/pattern_match.rs:208-219` vs `L12:402-411` |
| 缺 `struct_eq` | **有意，但漏了代价评估** | 自比较从"结构相同⇒相等"退化为"重求值 64 次⇒判不出" |
| 诊断中文 Error → 英文 Warning | **通道有意、文案顺手退化** | severity **没变**：L13 `elaboration.rs:1174-1189` 仍把非空 warnings 转 Err；真实差异是语言、`Undecided` 独立变体、每错各带 span |

**反向发现（`02` §5，不在任何既有台账里）**：L13 **缺 5 项 L12 加固**，其中
**「卡住 match 的实参」是唯一可能出错答案的项**：L13 `mod.rs:3196-3204` 把实参 quote 进每个分支体
（`l = Lvl(env.len())`），L12 已改成值层 `pending`（`L12/mod.rs:285`、`:1494-1497`，其 `:281-285` 注释
明写项层 splice 会引到错误上下文）。

## 4 封印的真实代价（`04`）

- **编译侧≈0**：`cargo test --lib` 掉的 11 例 **全部**是孪生内嵌单测（`L06/bump_spine_iter/entry.rs:471` 10 例 +
  `L07/.../entry.rs:363` 1 例）。**参考版单测一个没丢。**
- **测试侧**：6 个集成文件 **177 例**整体消失，逐例分档 **A 类 110 例（参考版也需要）= 真损失**、
  B 类 62 例（纯 ref↔twin 对照）、C 类 5 例（孪生自身）。
- **损失极不均匀**：**L06 掉 92%（133→10）** —— 因为 L06 没有独立 `l06_fast_parity.rs`，把 parity 写进了 blackbox；
  L07–L12 只掉 parity。
- **门禁更险**：12 个 target 编译成空 crate 后 `ok. 0 passed` 仍算成功；CI 的 `tools/gate_l13.sh:85`
  恰好缺 `--features l13-twin`（`.ps1` 在工作区 WIP 里修了，`.sh` 没修）。

## 5 要改的东西（按优先级合流）

### P0 —— 不修会持续误导

| # | 事项 | 出处 | 锚点 |
|---|---|---|---|
| 1 | **门禁堵漏**：新增 `--features twins` 独立 job + 最小例数闸；`gate_l13.sh` 补 `--features l13-twin` 对齐 `gate_l13.ps1:118` 的 `MinParity` | `04`#1 | `.github/workflows/ci.yml:96`、`tools/gate_l13.sh:85` |
| 2 | **L06 参考版黑盒重建（70 例）**：新建不挂 feature 的 `tests/l06_ref_blackbox.rs`，素材是 `l06_blackbox_v3.rs:79-83`（去掉内联 `assert_parity` 即得 52 例）+ `l06_blackbox.rs:94-106` 12 例 + v2 6 例 | `04`#2 | 同上 |
| 3 | **给 L13 卡住 match 补值层实参**（唯一潜在正确性）：先加 `(match x { cons(a,b) => a }) y` 捕获断言再改结构 | `02`#1 | `L13/mod.rs:3196-3204` ⟷ `L12/mod.rs:285/1494` |

### P1 —— 参考版自身的退化

| # | 事项 | 出处 | 锚点 |
|---|---|---|---|
| 4 | `check_universe` 错误尾注 `{:?}` → `{}` + `pretty_tm`（前缀 `expected universe` 被 blackbox 钉住，只动尾部） | `01`#1 | `L12/elaboration.rs:214-216` |
| 5 | 回灌 `occurs_transitive`（L13 自述"solve 无跨 meta occurs check"） | `02`#2 | `L13/unification.rs:616`、`L12/unification.rs:1077-1088` |
| 6 | `solve_multi_trait` 加无 trait 快路径（`trait_out_param` 空即 `return Ok(())`，≤6 行） | `01`#2 | `L12/unification.rs:751-765` |
| 7 | 回退两处：`raw_pretty` 裸 `U` → `Type N`；`Tm::Call` 在 L12 是**死节点**（无构造点）⇒ 要么接线要么删净 | `01`#3 | `L12/raw_pretty.rs:29`、`L12/mod.rs:1968/2565` |

### P2 —— 口径与残留

| # | 事项 | 出处 |
|---|---|---|
| 8 | 复核命令统一：`L07..L12/bump_spine_iter.rs` 的 `--features lNN-twin` → `--features twins`（6 处）；`L06/bump_spine_iter.rs:1` 补 SEALED banner；同步 `docs/l07-twin-sealed-2026-11-22.md:34`、`docs/test-catalog.md:46,234` | `04`#3 |
| 9 | 给覆盖义务方向补跨层语义用例钉死口径（known-diff #7 仍"待定"） | `02`#3 |
| 10 | 封印 L13（见 §6） | `03` |

## 6 封印 L13 的可执行路径（`03` §4）

**好消息**：参考版**已经能接管 LSP**。实测 `TYPORT_LSP_ENGINE=reference` 灌 8 条 stdio 消息跑
`examples/alu.typort`，**hover / inlayHint / definition / publishDiagnostics 四项与孪生逐字节相同**。

**拦路虎只有编译期耦合，两处**：
1. `L13_namespace/typeclass.rs:144-181` 的 4 处 `super::bump_spine_iter::state_journal_record/StateUndo`
   （孪生侧帧空即 no-op）→ 换本模块空实现；
2. `L13_namespace/mod.rs:27-37` 的 `probe_count` / `twin_mem_stats` 拆半挂 `#[cfg(feature="l13-twin")]`
   —— 这是 `mod.rs:25` 挂 cfg 的**唯一硬阻塞**。

**步骤**：① `Engine::lsp_default()` 改指 Reference（保留 `TYPORT_LSP_ENGINE=twin` 回退）；
② 解掉上面两处；③ 建 `tests/l13_lsp_ref_surface.rs` 把四项等价钉成断言 + 给 `elaborate_reference` 补每 kick
`force_memo_clear()`；④ 按 `03` §4 的 7 条验收。

**代价方向要说准**：封印 L13 是**省内存、费 CPU** —— twin 常驻 429 MB / 峰值 730 MB vs ref ~200 MB；
CPU 每 kick 102 ms → 359 ms（3.5×）。不是"省 CPU"。

## 7 勘误（本轮对上一轮结论的修正）

1. FINAL §4 E2⑤「`fin` 退化 L12」→ **首现 L08**（`L08/elaboration.rs:375`），L09–L12 原样继承。
2. FINAL §8.2「L08 从来没有 `observe.rs` 设计」→ L08 的两次移植提交（`08b516fb` 11-23 16:28、
   `f26d4097` 19:54）**晚于** L07 的 `6f7e245e`（15:52），看过 `observe.rs` 却选择内联简化版并删 `prof`。
   更准的表述是「**L08 移植时减配**」。
3. 「L13 缺 `VSpan`」→ **E1 等价改写**（`Span<SmolStr>`），不是缺失。
4. 「L13 Error→Warning 严重性变了」→ **没变**，只是文案语言 + `Warning::Undecided` 变体 + 每错各带 span。
5. 工作区里 L13 的未提交改动（`MAX_DEPTH`、`unify_fuel_budget()`、`Warning::Unmatched`）**不是本轮改的**，
   是会话开始前就存在的 WIP；本轮在 L13 上零改动。
