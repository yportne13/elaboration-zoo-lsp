# L08–L13 显式替换重构计划（承接 L07 本轮重构）

## 0. 缘起

L07 参考版 + 孪生版已完成"精化机制从事实表/上下文改写 → 显式替换
（Subst/VSub/frcs + SpecSolve 穿参）"的重构，两轮多角度评审后定稿：

- 设计文档：`docs/l07-dpm-refactor-design.md`（§4 槽位纪律、§9 实现口径
  注记是**移植必读**）；
- 蓝本实现：`src/L07_sum_type/{mod.rs, unification.rs, pattern_match.rs,
  cxt.rs, struct_eq.rs}`（参考版）+ `bump_spine_iter.rs`（孪生版）；
- 机制表述：`src/L07_sum_type/README.md` §1.2/1.3/4/5/6/10。

## 1. 各层现状侦察（2026-09）

| 层 | 参考版精化机制 | 孪生版 | 移植含义 |
|---|---|---|---|
| L08 积类型 | **与 L07 重构前同构**：`pm_defs` 事实表 + `pm_solvable`（mod.rs 22 / unification.rs 5 / pattern_match.rs 20 处） | bump 版同机制（178 处） | 直接套用 L07 蓝本（参考版 → 孪生版） |
| L09 MLTT | **`unify_pm` 改写上下文**：`cxt.update_cxt(infer, x, v)` 重写 env 槽 + `refresh` 全量重引用 + `Infer.global: HashMap<Lvl, VTy>`；决策树编译（`DecisionTree`） | 同名机制（elaboration 11 处 + bump 文件内部实现） | 更换精化载体：决策树编译保留，`unify_pm`/`update_cxt`/`global` → Subst/VSub/frcs + SpecSolve |
| L10 类型类 | 同上（`unify_pm` 6 处 + 决策树） | 同上 | 同上（注意 trait 求解与精化的交互） |
| L11 宏 | 同上 | 同上 | 同上（宏展开产物进入 match 的路径） |
| L12 规范形式 | 同上 | 同上 | 同上（canonical 求解的读点） |
| L13 命名空间（生产版） | 自有 GADT 精化（`unify_pm` 10 处 + `pattern_match.rs` 1364 行；弱点分析见 `docs/pattern-match-refinement-analysis.md`） | bump 版 15k 行 | 最大；先读弱点分析，明确哪些是显式替换能按构造消除的、哪些是别的问题 |

**关键事实**：L09–L12 的 `unify_pm`+`update_cxt` 正是 L07 README §6 所
述"改写 env 槽 + 刷新"旧架构（已捕获旧上下文的值过期、槽位错位 bug 族
的载体）——这些层从未经过 L07 的上一轮重写。因此对它们，本重构首先是
**修复**（消除该 bug 族），其次才是机制统一。

## 2. 每层任务口径（参考版 + 孪生版同批）

1. **参考版**：按 L07 蓝本替换精化载体，保留本层既有编译策略（决策树 /
   逐臂等）、本层语言特性与错误文案。删除 `unify_pm` / `update_cxt` /
   `refresh` / `Infer.global`（或等价物）——若某层的这些设施还承载非精化
   职责，拆分之。
2. **孪生版**：以 L07 孪生版移植结果为模板（Rc 链 Subst / VSub 表示 /
   fuel 剖面 / 槽位纪律）。孪生版与参考版必须行为逐字节一致——本层
   parity 套件（`lXX_fast_parity`）是硬 oracle。
3. **不许动**：`tests/` 下文件、其它层的源码；不改 CI/构建配置。
4. **资源纪律**：每 agent 独立 `CARGO_TARGET_DIR=.../target_agLXX`；
   不 cargo clean；输出重定向到文件再 grep（`head` 截断会 SIGPIPE 杀
   cargo）；F 盘空间紧张，单次至多 2 个 agent 并发编译。

## 3. 验收口径（逐层）

- `cargo test --lib L{XX}_*`：本层全部单测；
- `cargo test --test l{XX}_blackbox*`：本层全部黑盒；
- `cargo test --test l{XX}_fast_parity`：参考版 vs 孪生版逐字节；
- L13 另需：`l13_into_probe.rs` 等专项套件 + examples 全量 `typort check`
  （生产层，Verilog 生成路径不得受影响）；
- 性能：本层 bench（l{XX}bench）fast 列不慢于移植前 1.5×。

## 4. 风险与对策

- **行为差异预期**：L07 的 frcs 对"已解 rigid + 非空 spine"做解析应用
  （旧机制卡住）——若某层 parity 因此失败，按 L07 的办法处理：把该行为
  差异用本层 tests 钉死，参考版与孪生版**同批**移植使其一致。
- **决策树层的特殊点**（L09–L12）：决策树的可达性/覆盖检查在编译期一次
  生成；显式替换的 `SpecSolve` 需接入其分支编译的合一调用点，probe 语义
  与该层既有 reachability 判定要对齐（决策树可能已内建可达集——不要双重
  实现）。
- **L13 的已知弱点**：先读 `docs/pattern-match-refinement-analysis.md`；
  显式替换未必解决其结构体精化的全部问题，评审时诚实标注哪些缓解、哪些
  仍存。
- **评审**：每层移植完成后，另起至少 1 个独立评审 agent 从正确性角度对抗
  （对照本层 parity 与黑盒）；L13 另加性能评审。

## 5. 阶段顺序

1. L07 孪生版移植（进行中）
2. L08 参考版（进行中）→ L08 孪生版
3. L09 / L10（并行，各含参考+孪生）→ 评审
4. L11 / L12（并行，各含参考+孪生）→ 评审
5. L13（单独，参考+孪生）→ 正确性 + 性能双评审
6. 汇总：全仓 L01–L13 套件回归 + 全层 parity + bench 矩阵复测
