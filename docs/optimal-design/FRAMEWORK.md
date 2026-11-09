# 最优编译器设计分析 · 评价框架与协作约定（Lead 维护）

本目录服务于一个新目标：**从"七层各有什么"推进到"最优写法应当是什么"**。
用户原话：目标是"最简洁优雅、性能超群、确保正确"的编译器；曾以为自己的设计已最优，后来又发现诸多可能更优的写法，
为测试改得乱七八糟，现在分不清哪个最优，怀疑各章各有优秀之处需要结合。
因此本报告不是文献综述，而是**带实验证据的设计决策报告**：每个设计轴给出候选方案、实测/证据、复杂度与正确性代价、
以及在"最优架构"中的取舍。

产出目录：
```
docs/optimal-design/
  FRAMEWORK.md            # 本文件：评价框架/实验协议/分工
  D1-design-space.md      # 设计空间地图（L01–L13 + 分支/WIP 的候选写法与代码锚点）
  D2-correctness.md       # 正确性/健全性/测试与形式化证据
  D3-elegance.md          # 复杂度、简洁优雅、模块边界、重复度
  D4-experiments.md       # 主实验记录（方法/原始数据/分析/局限）
  D5-techniques.md        # 性能技术矩阵（技术→实测增益→复杂度/unsafe 代价→取舍）
  D6-branches.md          # 分支/WIP/补丁考古：已测结果、可收割项、死胡同
  D7-architecture.md      # 最优架构提案 v1（由 principal-architect 起草）
  experiments/raw/        # 原始输出（日志/CSV），可复现实验的机器可读记录
  FINAL-OPTIMAL-DESIGN.md # Lead 汇总终稿
```

## 0. 用户目标到可评价问题（Q1–Q4）

- **Q1 设计轴**：本仓实际出现了哪些"写法选择"？每个选择在哪些层/分支被实现过？（D1 + D6）
- **Q2 优劣判定**：在每个轴上，哪个写法在复杂度/正确性/性能/优雅上更优？证据是什么？代价是什么？（D2–D5）
- **Q3 组合**：逐轴最优是否可组合？哪些选择互相冲突（例如"一个引擎的简洁"vs"双引擎的性能/orene"、σ 与 L13 规模、
  原生 Nat 与定义相等、逐臂匹配与路径感知诊断）？（FINAL）
- **Q4 路线**：从当前仓库到目标架构的**最小迁移路径**（砍什么/合并什么/保留什么/先做哪步），
  预期收益与风险，如何用实验守住正确性。（FINAL + D7）

## 1. 评价框架（六轴，权重可敏感性分析）

| 轴 | 定义 | 主要证据 | 权重 |
|---|---|---|---:|
| **A 正确性** | 类型检查健全性/完备性；已知缺陷与误判；UB/panic 面；诊断可信度；形式化/oracle 覆盖 | 测试套件实跑、known-bug 文档、Lean oracle、代码不变量、对抗样例 | 30% |
| **B 性能** | elaboration 吞吐、真实 prelude/HDL、LSP 交互延迟、峰值内存、扩展性（scaling）、稳定性 | 重建 HEAD 后实测（隔离进程、多轮 min/median）、现有历史实验审计 | 25% |
| **C 简洁/优雅** | 概念数、单一事实来源、模块边界、命名的自解释性、无重复、教学可读性 | LOC/概念清单/接口/重复代码测量、代码走查 | 25% |
| **D 复杂度** | 实现复杂度、耦合、不变量数量、unsafe/FFI、构建复杂度、认知负担 | 依赖图、跨模块调用、模块 LOC 分布、unsafe 计数 | 10% |
| **E 可维护/演进** | 改动成本、双实现/parity 维护、测试成本、文档腐化、实验可复现性 | 历史 commit/评审/文档腐化清单、机制改动波及面 | 5% |
| **F 生产就绪** | LSP/HDL/Verilog、错误恢复、平台、内存护栏、并发/池化 | LSP 套件、真实工程负载、已知生产问题 | 5% |

评分：1–5 分/轴 + 证据；总分 = 加权。**必须给敏感性分析**（权重变动是否改变结论）。所有"最优"结论都
必须写清"在什么约束下最优"（目标用户/规模/是否要 HDL/LSP）。

## 2. 证据与实验协议（强制）

1. **标注**：`[实测]`（本目录实验原始数据）/`[历史实测]`（仓库既有实验：bench-matrix、perf-*、wip 等）/
   `[码]`（源码核对）/`[文档]`/`[推断]`。
2. **环境**：CPU AMD Ryzen 5 5600（6C/12T）、34 GB RAM、Windows；工作区 F: 盘（源码），
   **构建/实验 target 在 `C:\ezl-target`**（F: 仅 0.8 GB）。禁止在 F: 上 cargo build/test。
3. **主实验（D4，仅 Lead + perf-experimenter 执行）**：
   - 先 `CARGO_TARGET_DIR=C:\ezl-target cargo build --release --bins`，以同一份 HEAD 二进制跑全部实验；
   - 每个数据点：独立进程、预热、≥3 轮取 min（同时记 median 与 max）；标注 k/规模/负载源；
   - 成对比较（A/B）必须同窗口交替执行，避免窗口漂移；报告比值而非只看绝对值；
   - 原始输出写到 `experiments/raw/<exp-id>.txt|json`；D4 中写命令、时间、机器负载提示；
   - 任何"仅文档数字"必须标 `[历史实测]` 并注明其采数日期（09-12/17/18/20 等）以及之后代码是否已变。
4. **实验设计模板**（每个实验必须回答）：假设 → 变量/控制 → 指标 → 结果表 → 解释 → 局限。
5. **并发纪律**：同一时间只允许一个 benchmark 进程组（Lead 或 perf-experimenter）；
   其他成员只做静态分析/读文档/小幅 grep，不跑 cargo、不跑 bench；实验开始前用文件锁通告
   `docs/optimal-design/experiments/.lock`（内容含 owner/exp-id/time），结束后删除。
6. **代码实验**（若需要）：不得改 master 工作树；用 `git worktree add` 建临时 worktree（C: 或 F: 仓根允许），
   所有构建用 `CARGO_TARGET_DIR=C:\ezl-target-<name>`；实验后 `git worktree remove` 并记录 commit/diff。
   任何"合并候选"必须给出 diff 摘要 + 重跑门禁结果。

## 3. 关键实验清单（D4/D5，按价值排序）

| ID | 实验 | 目的/假设 | 归属 |
|---|---|---|---|
| EXP-1 | `l01bench` 全部 NbE 表示 × {church, dup, guest} × 规模扫描 | 哪种值/求值表示在性能/简洁上真正占优；是否存在"简单且不慢"的甜点 | perf |
| EXP-2 | `pmabbench` {flat,wild,cart,deep} × impls {l07,l07pre,l09} | 逐臂 vs 决策树：编译期 scaling 与常数，复核 09-16 结论 | perf |
| EXP-3 | L07–L13 当前 HEAD 主矩阵（match/church/natadd/strchain/enum/struct/universe/traitchain/macro/global 按层） | 现役引擎质量与真实短板；孪生/参考比值；扩展性 | perf |
| EXP-4 | 消融开关 A/B（L02–L06 的 `*_NO_CONV_MEMO`/`*_NO_NAME_MAP`；`L07_LOOP`/`L08_LOOP`/`L11_LOOPCAP` 等） | 每项优化/机制的净收益与代价 | perf + techniques |
| EXP-5 | `l06l13mem` 分配计数/字节/直方图 + `--sizes` | 内存与分配热点：哪些表示/机制值得、哪些是税 | techniques |
| EXP-6 | 真实负载：L13 `prelude-core/prelude-hdl/examples-hdl`、`typort check examples/*`、LSP kick 采样 | "性能超群"必须体现在真实负载而非合成 match；生产路径的真实收益 | perf |
| EXP-7 | 正确性实跑：重建后的 lib/parity/blackbox 套件 + Lean oracle（若可用）+ 已知 bug 复现 | 每个设计选择的正确性证据；不是"没测出 bug" | correctness |
| EXP-8 | 分支/WIP 收割：候选分支/补丁的复现或重测 | 用户"改得乱七八糟"里哪些是真收益、哪些是死胡同 | branches + perf |

## 4. 团队分工（7 人 + Lead）

| 成员 | 交付 | 禁止 |
|---|---|---|
| design-cartographer | D1 设计空间地图 | 跑 cargo/bench |
| correctness-auditor | D2 + EXP-7（与 Lead 协调） | 跑 bench（测试构建/执行需 Lead 批准） |
| elegance-architect | D3 | 跑 cargo/bench |
| perf-experimenter | D4 + EXP-1/2/3/5/6 执行 | 改 master 源码 |
| twin-techniques | D5 + EXP-4/5 分析（与 perf 协调） | 独占 bench（与 perf 抢） |
| branch-archaeologist | D6 + EXP-8 候选清单 | 跑 cargo/bench（除非 Lead 批准） |
| principal-architect | D7 最优架构 v1 + 迁移路线 | 跑 cargo/bench |

Lead：框架、任务板、实验总调度（含 EXP-4/6/7 的最终执行）、独立复核、FINAL 汇总、交付。

## 5. 终稿结构（FINAL-OPTIMAL-DESIGN.md）

1. 执行摘要（≤1 页）：目标架构一句话 + 10 条关键决策 + 预期收益/成本。
2. 评价框架与权重、敏感性分析。
3. 设计空间全景图（轴 × 候选 × 是否被实测）。
4. 逐轴对决：候选 A/B/C 对比（含正确性/复杂度/性能三面），每轴给"胜者 + 适用条件 + 代价"。
5. 实验记录汇总（EXP-1…EXP-8，含原始数据索引与局限）。
6. **最优架构提案**：模块图、数据表示、算法选型、不变量清单、测试/形式化护栏、迁移路线（分阶段、每阶段门禁与回滚）。
7. 明确"不要做什么"（负结果清单）。
8. 证据索引（代码/文档/分支/实验 raw）。
