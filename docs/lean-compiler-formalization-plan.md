# Typort 编译器 Lean 4 形式化方案（2026-11-08）

> 背景：本轮 L07/L08 review 修复轮暴露出若干「语义分层/算法代理」类缺陷（R1 空类型零臂被拒、
> R2 occurs 丢外层 σ、R3 预算代理不同构、P15 struct_eq 漏比 pending 值）。用户问：
> **能否用 Lean 形式化这个编译器，以免再有此类 bug？**
>
> 结论先说：**能，但必须分层**——形式化「核心语义 + 算法不变式」可行且直接针对 bug 类；
> 形式化「整个 24.4 万行 Rust 编译器」不现实。建议按本文 M1（核心定理）+ M3（可执行 oracle）
> 两阶段推进，M2（精化式模式匹配）是长期攻坚，M4（Rust 实现细化证明）只对极小核心可行。

## 1. 现状盘点（本仓库已有基础）

| 项 | 事实 | 锚点 |
|---|---|---|
| 已有形式化 | 8 个 Lean 模块、1029 行、**57 条已证定理**，无 `sorry`/`axiom`/`unsafe` | `lean/README.md:7` |
| 覆盖范围 | **声明式类型论**：`Tm`/`Arms`/`Ctx`、重命名/替换代数律、`Step`(β/ζ/ι)/`EtaStep`/`Conv`、`HasType`（含 `matchE` 标准规则）、`Sig`/构造子类型/覆盖谓词、prelude 真实声明、示例推导 | `lean/Typort/*.lean`；`lean/README.md:29-40` |
| 明确未覆盖 | **① 精化式 match（方程求解→σ 上下文替换）；② meta/合一/invert/prune/occurs/fuel；③ NBE 引擎（`Val`/`eval`/`quote`/`force`/`frcs`/`VSub`/`struct_eq`）；④ 声明层 δ/global；⑤ 模式编译器（可达性/覆盖探测）；⑥ 隐式参数插入；⑦ parser/诊断** | `lean/README.md:92-140` |
| 工具链 | Lean 4.34.1（`$env:USERPROFILE\.lean4-toolchain\lean\lean-4.34.1-windows`），不依赖 Mathlib；`lake build` 实测 **Build completed successfully（0 warning）** | `lean/README.md:13-27`；本轮实测 |
| 规格文档 | `docs/tt-spec-l07-l08.md`、`tt-spec-l09.md`、`tt-spec-metas-typeclass.md`（逐条 file:line，已为形式化准备） | docs/ |
| Rust 体量 | `src/` 24.4 万行 / 424 文件；L07 18.6k、L08 16.9k、L13 59.3k（含 tests/twin/parser） | 本轮实测 |

**关键观察**：本轮所有 bug 都落在「明确未覆盖」的第 ①②③⑤ 项里。也就是说，
**现有形式化没有失败——它只是停在了会出 bug 的那一层之前**。这恰好验证了「补哪一层最值」。

## 2. 为什么现有形式化挡不住这些 bug（层级错位）

1. **声明层 ≠ 算法层**：`Conv`/`HasType` 是关系（存在解即可），实现是带元变量/预算/显式替换的算法。
   R3（预算代理不同构）、R2（算法漏检）都只存在于算法层；声明层没有「预算」「扫描方向」概念。
2. **双实现一致性未被形式化**：L07 参考版 vs `bump_spine_iter` 孪生版、L08 参考 vs 孪生，
   目前靠 `l07_fast_parity`/`l08_fast_parity` 差分测试（只比 Ok 字节/Err 判定，不比文案；
   且对「两侧同错」零能力——R1 就是两侧都错、R4 是一侧错）。形式化「细化关系」可以把
   「两实现语义等价」变成可证义务，或至少让 Lean 做第三 oracle。
3. **工程层（parser/span/诊断）不在类型论范围**：R6/R7 属于 parser 坐标契约，形式化收益极低；
   应继续用契约测试 + 差分/随机测试，不进入 Lean 范围。
4. **「规范写错」也是 bug 源**：R1 的根因是分类器对「规范冲突」的集合不完整；
   只有把「什么算 Absurd」写成 Lean 定理（`Absurd ⇒ 无解`），才能让规范本身被机器检查。

## 3. 目标：把 bug 类变成证明义务（M1 核心）

> 形式化对象：L07 参考版引擎的**值/替换/合一核心**（`Val` 13 构造子、`Subst` 持久化单链、
> `VSub`/`frcs`、`unify` 三档结果、occurs、`struct_eq` 快路径）。规模约 5–7k 行 Rust 对应，
> Lean 期望 800–1500 行（定义 + 定理）。

| 定理 | 陈述（非形式） | 直接针对的 bug | 难度 |
|---|---|---|---|
| T1 occurs 健全性 | 若 `σ` 无环且 `occursσ(x, v)` 检测通过（按组合语义扫描），则 `σ[x↦v]` 无环；并证明「只扫内层 σ」的版本存在反例 | **R2**（VSub 嵌套丢外层 σ） | 中 |
| T2 Absurd 健全性 | 若分类器返回 `Absurd`，则两侧值在任意合法替换下都不可相等（`¬ ∃σ. equal σ t u`） | **R1**（分类器缺 `Sum×LiteralType` 等） | 低-中 |
| T3 Undecided 保守性 | `Undecided`/`Fuel` 永远不被当作 `Absurd` 消费（可达性探测只把 Absurd 判不可达） | **R1 的后果面**、覆盖健全性 | 低 |
| T4 预算策略不变式 | 预算计数是「路径/次数」的单调函数；超限返回的档位不会伪装成 Absurd；参考版与孪生版计数口径可互相模拟（同一个 step 计数关系） | **R3/R8** | 低-中 |
| T5 struct_eq 健全性 | `val_eq a b = true ⇒ a ~ b`（结构快路径只会放过语义相等的值；`VSub` 异实例返回 false 是保守的） | **P15** | 中 |
| T6 精化合法性 | `unify_indices` 解出的 `σ` 使构造子返回索引与头部索引在 `Conv` 下相等，且 `subst_cxt` 后上下文良构（分支体判型保持） | 最近 bug 的「上游」；依赖 Cockx 理论 | **高** |
| T7 双实现细化 | 参考版 `unify` 与孪生 `unify_iter` 在公共可观测结果上一致（bisimulation 或 oracle 差分） | **R4/R5**、parity 盲区 | 高（或 M3 代替） |
| T8 解析/span | 预处理后偏移 = 原文本偏移、错误 span 指向失败 token | R6/R7 | 不形式化（契约测试） |

**诚实声明**：M1 的 T1–T5 能**证明规范/核心算法语义**，不能自动证明 Rust 实现符合规范——
后者需要 M4 的细化（Aeneas/Charon 或 Lean 提取替换核心），成本另计。M1 的现实收益：
把「分类器/occurs/预算/struct_eq」这几类最容易出错的判据变成机器检查的定理 + 反例钉。

## 4. 分阶段路线与成本

| 阶段 | 内容 | 产出 | 预估（agent 轮 / 人日） | 验收 |
|---|---|---|---|---|
| **M0** | 固定工具链、CI 化 `lake build`（可复用现有 4.34.1）；把本轮 4 个新回归钉的语义写成 Lean 注释锚点 | 1 个 CI job/脚本 | 0.5 轮 / 0.5 日 | `lake build` 绿、文档锚点齐全 |
| **M1** | `Typort/Engine/Val.lean`（值 + 显式替换 + `VSub`/组合）、`Occurs.lean`、`Classify.lean`（Absurd/Undecided/Fuel）、`StructEq.lean`；证明 T1–T5 + 反例定理 | 4 个新模块、~800–1500 行、~20–35 条定理 | **3–6 轮 / 1–2 周** | 0 sorry；T1–T5 编译通过；R1/R2 反例定理与 Rust 回归钉一一对应 |
| **M2** | 精化式模式匹配（Cockx 式统一化）：`unify_indices` 关系化、σ 良构、上下文替换、分支判型保持（T6） | `Refinement.lean`、~1.5–3k 行 | **多周–月**（理论攻坚） | 能形式化重演 prelude `trans`/`subst` 的判型 |
| **M3** | 可执行 Lean oracle：把 `unify` 核心 fragment 写成可运行函数，编 `lean_exe`；Rust 侧 `tests/lean_oracle_parity.rs`（`LEAN_ORACLE=1` 时启用）对回归语料跑第三 oracle；或 Lean `#eval` 生成 golden verdict JSON | 1 个 Lean exe + 1 个 Rust 测试 + golden 语料 | **1–2 轮 / 3–5 日** | 语料逐条判定一致；不一致即 bug 报告 |
| **M4** | 对极小纯核心（occurs/quote/替换）用 Aeneas/Charon 或 Lean 提取做「实现 = 规范」细化；其余层不做 | 可选 | 1–3 月 | 只覆盖选定的 2–3 个函数 |
| **M5** | 全 Rust 编译器验证 | — | **不可行**（24.4 万行，含 arena/FFI/LSP/HDL 代码生成） | 不建议 |

**推荐组合**：**M1（先） + M3（并行/随后）**。M1 让规范本身可证，M3 让实现漂移在 CI 里可见；
两者合计约 4–8 轮，能把 R1/R2/R3/P15 这一类「判据/代理/扫描方向」缺陷变成可机检项。
M2 单独立项；M4 只在有预算时做核心函数；M5 放弃。

## 5. 方案对比

| 方案 | 能防的 bug | 成本 | 局限 |
|---|---|---|---|
| **A. M1 核心定理**（推荐） | R1/R2/R3/P15 类规范/算法判据 | 中（1–2 周） | 不保证 Rust 实现符合规范（模型-实现漂移） |
| **B. M3 Lean oracle 差分** | 双实现分歧、接受集漂移、R4/R5 类；可在 CI 挡住「改 A 实现忘改 B」 | 低（3–5 日） | 覆盖取决于语料；oracle 自身也要信任/维护 |
| **C. Aeneas/Charon 验证 Rust 核心** | 选定函数的实现正确性 | 高（1–3 月，工具链成熟度风险） | 只适合无 arena/unsafe 的纯函数；L07 参考版部分可行，L13 难 |
| **D. 全验证** | 理论最强 | 不可行 | 24.4 万行 + 引擎/生成器/IO，无现实路径 |

## 6. 风险与边界

1. **模型-实现漂移**：Lean 规范若与 Rust 语义不一致，证明只能保证「规范自洽」。缓解：
   规格逐条带 `file:line` 锚点（本仓库已有惯例）；M3 oracle 作为漂移探针；关键变更必须同步改 Lean 规格。
2. **Lean 4 `induction` 不支持互归纳**（现有 README 已踩坑）：引擎层值/替换若写成互归纳，
   元定理归纳会受限，需要像现有 `HasType` 那样刻意拆环（这是 M1 的主要工程难点）。
3. **Cockx 精化理论**（M2）是长期投入，且与实现的三档判定/预算交互复杂；不要低估。
4. **无 Mathlib**：只能 core/Std，集合/关系库需自建（现有形式化已证明可行）。
5. **维护成本**：形式化 1k 行≈1 人周；引擎 1.5k 行规格 + 定理≈2 人周；且每次大改要同步。

## 7. 进度（2026-11-08 首轮）

| 阶段 | 状态 | 说明 |
|---|---|---|
| **M0** | ✅ 完成 | Lean 4.34.1 工具链复用；`lake build` 同时构建 `Typort`（声明层，57 定理基线绿）+ `TyportEngine`（新增）；零 warning；构建指令写进 `lean/README.md`。 |
| **M1** | ✅ 完成（第 6 轮收口；抽象边界见下） | 7 个模块（1009 行、38 条已证定理）：`Basic`（`Val`/`Subst`）、`Occurs`（组合语义 `Mentions` vs R2 错误算法 + 3 组机检反例 + T1 直接环半边）、`Rank`（**T1 精确刻画** `extend_acyclic_iff_no_reach`：图模型下「扩展无环 ⟺ check 通过」，含主定理/必要性/等级证书）、`Budget`（R3 代理互不蕴含）、`Classify`（T2/T3）、`StructEq`（T5/P15）、`Oracle`（M3）。**抽象边界**：`Mentions`（含 `VSub` 组合语义）与图模型 `OccursReach` 的等价桥属于实现细化（M4 方向），不在 M1 判据内；`Occurs.lean` 已用组合语义 + 具体反例覆盖 VSub 情形。 |
| **M2** | ⏳ 未开始 | Cockx 式精化 match（重演 prelude `trans`/`subst`）。 |
| **M3** | ✅ 完成（curated 语料） | `Typort/Engine/Oracle.lean` + `OracleMain.lean` + lake `engine-oracle` 可执行目标；`tests/lean_oracle_parity.rs`（`LEAN_ORACLE=1` 门控）在 c1/c2/空类型零臂/P15 四组语料上与 Rust 参考引擎判定比对，实测 4/4 一致（~1 s）；未设环境变量时自动跳过。边界：不解析 Typort 源码、不做完整 unify（curated corpus）。 |
| **M4** | ⏳ 未开始 | 仅对极小纯核心（occurs/quote/替换）尝试 Aeneas/Charon 或提取；`Mentions ↔ OccursReach` 的 VSub 细化桥可并入此方向。 |

**验收（第 6 轮）**：`lean/lake build` 绿（`Build completed successfully (20 jobs)`）、
`lake build engine-oracle` 绿；`LEAN_ORACLE=1 cargo test --test lean_oracle_parity` 2 passed；
无 `sorry`/`axiom`；T1（精确刻画）、T2/T3/T4/T5、R2/R3 反例/健全性均可由机器检查复现。

## 8. 后续（M1/M3 之外的路线）

1. **M2 精化 match**：Cockx 式统一化理论，形式化 `unify_indices` 解出的 σ 的良构性与
   分支判型保持（这是与实现对齐的最大缺口）。
2. **M3 扩展（可选）**：把 oracle 输入从 curated 语料扩展成值层目标序列化协议
   （Rigid/Sum/SumCase/Match/VSub + 解链），使 Rust 测试可提交自动生成的 value-level 目标。
3. **M4/细化桥**：`Mentions`（含 `VSub` 组合语义）与 `OccursReach` 图模型的等价性
   （T1 的实现层细化），或对极小纯核心做 Aeneas/Charon 验证。




