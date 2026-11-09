# 最优编译器设计：多维度分析、实验记录与架构提案

> 版本：v1.0（2026-11-09，HEAD `8443586e` + 本轮重建二进制）
> 目标（用户原话）：**最简洁优雅、性能超群、确保正确**；曾以为现有设计最优，后发现诸多可能更优的写法，
> 为测试改得乱七八糟，分不清哪个最优，怀疑各章各有优秀之处需要结合。
> 本报告回答四问：Q1 有哪些写法（设计空间）；Q2 各轴谁更优（证据+代价）；Q3 能否组合成一个最优架构（冲突与裁决）；
> Q4 如何从现状迁移（路线/门禁/回滚）。
> 证据分级：`[实测]` 本轮 `experiments/raw/`；`[历史实测]` 仓库既有实验（标日期/出处）；`[码]` 源码核对；
> `[文档]`；`[推断]`。并行分报告：`D1` 设计空间、`D2` 正确性、`D3` 复杂度/优雅、`D4` 实验记录、
> `D5` 性能技术矩阵、`D6` 分支/WIP 考古、`D7` 架构 v1、`D2b` 测试执行。

---

## 0. 执行摘要

### 0.1 一句话结论

**最优写法不是"某一层"或"更聪明的算法"，而是三个决定 + 一个规格的组合**：
**① 生产路径收敛到一个 arena 引擎（孪生内核的安全句柄版），② 保留一个可读、可证明的语义参考核心
（`refcore`，L07 σ+逐臂传统）作为 test-only oracle，③ 用"删死工作 + 有界记忆化 + 常驻 prelude + 单引擎"
替代"更多代码/更多开关/更多层"；并用 S（Lean M1/M3 规格）做判定终审。**

逐轴最优与整体最优不同：逐轴看，L01 的表示实验、L07 的 σ+单一 unifier+逐臂匹配、L09/L10 的复合环境与值级探针、
L13 的 decl 表/namespace/原生 Nat/观察面都已经给出赢家；但这些赢家**不能直接拼在一起**（D1 §7 的 9 条组合冲突）。
整体最优必须按"生产/参考"两层重新分工——这正是 D1/D3/D5/D7 与仓库既有 `l13-perf-replace-2026-09-27` 路线图的交汇点。

### 0.2 十条关键决策（建议）

| # | 决策 | 依据（简） |
|---|---|---|
| 1 | **四角色分工**：P 生产后端（arena 安全句柄版）唯一进 release；R 参考核心（`refcore`，L07 σ+逐臂语义）仅测试期差分；O 现 L13 参考版冻结过渡；S Lean M1/M3 规格终审 | L01 23 变体 + L02–L13 落地；LSP 已默认 twin（29/30、kick 1.64–1.78×）；D7 §5 裁决 |
| 2 | **参考核心 = L07 传统**（σ 显式替换 + 单一 unifier + 逐臂匹配 + 三档判定），作为 spec/oracle，不追性能 | σ 在 L07–L12 已证（六层逐字节 0、4013 例 0 失败）；L13 五轮失败是规模/耦合问题不是语义问题 |
| 3 | **生产引擎也采用 σ**，但作为"新架构内实施"：内容寻址 memo、观察面 owned+prelude 关表、meta 解链环检测、深链内存预算；P4 门禁失败则保留 `update_cxt` 并关门 | D2 A 轴：σ 按构造消除 update_cxt 槽位 bug 族；D6 C-2：σ 在 L13 孪生实测 prelude-core/examples-hdl −5.5%、417 parity 绿，但 prelude-hdl +9–11% 需解决 |
| 4 | **匹配 = 逐臂下钻 + 值级探测 + 独立 usefulness/覆盖 pass**（诊断补齐，不回到决策树） | pmab 受控实验：决策树最坏 14822× 慢且运行期无收益；逐臂的诊断弱化可独立补 |
| 5 | **名字世界 = 全限定 decl 表 + per-file Scope（import/package）**，禁止 de Bruijn 大下标哨兵 | L09/L10 哨兵是支线（L11 反手）；L13 namespace 已在生产语料验证 |
| 6 | **trait = Val 级 tabled 求解 + 单向前提 + coherence/确定性 + 预算耗尽诊断**；实例头索引；删 canonical/iddfs | L10 toy 化（多解 HashMap 序、effort panic、close 修复只孪生）；L12 Val 级更完备；canonical 仅 Err 路径、run/run_fast 不经 |
| 7 | **effect 显式化**：prim 入 decl 表 + `Effect{Pure,Stateful(...)}` 静态分类、replay 规则化、IO 返回 Result；原生 Nat 保留但定义相等必须影子对拍 | def replay 启发式已致 twin def-journal 崩溃；L13 原生 Nat 与特殊相等是最大未形式化面（D2 I 轴） |
| 8 | **观察面 = 分析产物 owned 快照（push 期渲染）**，prelude 装载 sink 空实现；内存/压实/常驻纳入一个 `PreludeSnapshot` 生命周期 | 跨引擎唯一安全形态；prelude 期渲染是纯死工作（21.1→9.3 s 补丁未落 master）；压实 908→181 MB/kick 但 +150–190 ms，需阈值 |
| 9 | **正确性 = 四角色 + 四路护栏**：S（Lean M1/M3）+ R/O 差分（T1 每次 CI；T2 全语料 Err 正文逐字节、`?N` 不归一化）+ 不变量 I1–I15 回归钉 + 属性/fuzz；**不删 oracle**（γ 不做） | D2：测试金字塔"塔尖薄、塔基厚而不齐"；同错类只能靠独立 oracle/生成式语料发现 |
| 10 | **复杂度门禁**：生产 core ≤18–30k 行、单文件 ≤1.2k、unsafe 313→≤60（最好 0）、环境开关 33→≤4、跨层复制/归档/`.bak`=0、bin ≤6 | D3：80% 复杂度来自"13 层 copy-forward × 2 引擎 × 归档入源码"，真正技术复杂度只占 ~1/5 |

### 0.3 预期收益与代价（量级）

| 维度 | 现状 | 目标 | 依据 |
|---|---|---|---|
| 生产实现 | 双引擎 ≈ 168k 行（参考 82.9k + 孪生 85.4k），仅 L13 一层就 25.7k | 单份 ≤30–34k 行（含 LSP/HDL） | D3 §5/D7 §7 |
| 可立即删除 | `bench_head`+`bench_pre` 25,334 + `.bak` 12,464 = **37,798 行** | 0 | D3/D6 |
| 性能 | match 参考/孪生差 1.25–10×；大值 23–867×（09-20，修复前）；真实 LSP 1.64–1.78× | 保持孪生性能（= 生产引擎）；oracle 只测试期跑 | 本轮 EXP-3 + D5 |
| 真实负载（本轮 EXP-6） | prelude-hdl 5172 ms basic vs 1366 ms fast_ss（3.8×）；prelude-core 55.7 vs 18.8 ms；examples ~55 vs ~19 ms；`typort check` CLI 5.2–5.5 s/文件 | 生产引擎 + 常驻 prelude 后按孪生路径验收（目标：prelude-hdl ≤当前 fast_ss、CLI 启动成本显著下降） | `exp6-*` |
| 正确性 | 双实现 parity（判据强度倒置：L07 只比 Err 判定）+ Lean 声明层/engine M1；**本轮 EXP-7：25 目标 2,255 passed/0 failed，Lean oracle 2/2** | oracle 差分 + 不变量 + Lean M1/M3 + 属性/fuzz；已知 bug 类 = 定理/钉子双覆盖 | D2 §5 + D2b |
| 维护 | 每机制改 2 处 × 13 层；文档 5.2 万行且 90 处过期 | 1 处实现 + 1 份 oracle + 生成式指标；文档 ≤8k | D3 §6/§8 |
| 迁移 | — | 18–34 人周（P0–P6），先做 R0 判据（1–2 周） | D7 §8（与 l13-perf-replace 22–44 人日部分重叠） |

**代价/风险**：σ 在 L13 规模能否压回 ≤1.5× 是 P4 生死门；arena 若按"句柄索引无 unsafe"重写，性能可能损失 3–10%（[推断]，需 EXP）;
跨文件会话/wasm 内存/观察面字段 span 是三条欠账；迁移期间的测试面改造不能"直接翻默认"。

---

## 1. 方法与证据分级

- **只读静态分析 + 受控实验 + 历史实验审计**三结合。本轮在 `C:\ezl-target` 重建 HEAD release 二进制
  （2026-11-09 01:29–01:30，`cargo build --release --bins`），消除 11-08 旧二进制与源码的偏差。
- **证据分级**：`[实测]`=本轮 raw（附文件/时间戳）；`[历史实测]`=既有 bench/perf 文档（标日期，窗口间不可比）；
  `[码]`=源码；`[文档]`；`[推断]`。任何跨窗口数字必须带日期，跨层倍率必须带口径（basic/fast_ss/fast/fast_run）。
- **本轮实验**：EXP-1 L01 表示对决；EXP-2 pmab 受控实验复跑；EXP-3 当前 HEAD 七层主矩阵；EXP-5 内存/分配；
  EXP-6 真实负载（L13 prelude/examples、`typort check`）；EXP-7 测试套件实跑（已完成，见 §5.6）；
  EXP-8 分支/WIP 收割（未执行，计划见 §5.7）。EXP-4 消融（11 项）已设计未执行（D5 §7），原因：实验线时间窗。
- **已知污染**：EXP-1/2 的首轮采集与构建尾部（rustc/LTO）重叠，已 clean 重跑（raw 中 `*-clean-*`）；
  EXP-3 的 l07–l10 部分与构建尾部重叠（01:33–01:35），l11–l13 与 `-match-clean` 在干净窗口（01:37–01:38）。

---

## 2. 评价框架与权重

| 轴 | 权重 | 判定 | 主要证据 |
|---|---:|---|---|
| A 正确性 | 30% | 健全性/完备性、已知缺陷、预算/诊断、UB、测试/形式化覆盖 | D2 + Lean + EXP-7 |
| B 性能 | 25% | 真实负载（LSP/prelude/HDL）+ 合成；扩展性/内存/启动 | D4/D5 + EXP-1/3/6 |
| C 简洁/优雅 | 20% | 概念数、SSOT、模块边界、去重、可读性 | D3/D7 |
| D 复杂度 | 10% | LOC/unsafe/不变量/耦合/构建 | D3 |
| E 可维护/演进 | 10% | 改动成本、双实现/parity、文档、复现 | D6/D7 |
| F 生产就绪 | 5% | LSP/HDL/CLI/wasm/错误恢复 | D7/l13-perf-replace |

**敏感性**（结论对权重的稳健性）：
- 若**性能权重↑**（30%）且正确性↓（25%）：结论不变（单生产引擎 + 冻结 oracle），因为性能收益只在生产引擎兑现。
- 若**简洁权重↑**（30%）：D3 的 C 方案（删参考版、只 golden+Lean）会变优；但 D2 判定"差分 oracle 是唯一可靠同错发现手段" ⇒ 只应在 golden 覆盖 ≥95% + Lean M3 扩展后考虑，v1 不采纳。
- 若**正确性权重↑**（40%）：P4（σ 统一）会推迟，先做 D2 的 G1/G2 护栏与 Lean M1/M3 扩展；架构主体不变。
- 若目标改为**纯教学/研究**（无 LSP/HDL 生产）：保留 L07/L09 参考实现作为主线、性能后端降为实验分支更优雅——但用户目标含生产，故不采纳。

---

## 3. 设计空间全景（Q1；详见 D1）

本仓实际上已是一份"被完整实现过的设计空间实验"：**L01 的 23 变体是唯一系统实测轴**；L02–L06 有消融开关；
L07–L13 把语言增量与机制选型绑在一起，多数轴只有 1–2 个候选、无干净 A/B。证据强度：

| 强度 | 轴 |
|---|---|
| 强（多候选+同窗口实测） | 值/环境/求值表示（L01 23 变体）、quote/conv 记忆化（L02–L06 消融）、名字解析/复合环境（L03 chain 表）、匹配编译算法（pmab+09-20） |
| 中（双引擎+矩阵但候选不完整） | 决策树 vs 逐臂、decl 表 vs 哨兵、trait Typ vs Val、LSP 观察面 |
| 弱（单实现/无对照） | 精化载体 σ vs update_cxt（L13 是整体替换不是 A/B）、原生 Nat、宏时机、内建/effect、测试/形式化 |

**18 条设计轴**（候选/实现层/倾向/证据档，详 D1 §1）：

1. **项表示**：Box / Rc / 字节码 / bump 引用树 / 指令数组 / 原生闭包 → **bump 引用树**（强）
2. **值表示**：24B 枚举 / 64 位打包字 → **打包字**（强，但 unsafe/UB 代价）
3. **环境表示**：Rc 链 / 下标 arena / bump 链 / bump 切片 / **复合环境**（defs 平坦 + bind 链）→ 复合环境（强）
4. **求值策略**：递归 / CEK / 双栈 / **双栈+右链快路径+稳态**（强）
5. **分配器**：系统堆 / **mimalloc** / arena / bumpalo → bumpalo + mimalloc（强）
6. **求值记忆化**：无 / quote memo / 内联槽 / conv memo / β-eval memo → quote+conv（按负载），内联槽/β-eval 否决（强）
7. **名字解析**：线性 walk / **name_map+trail**（强）
8. **元变量/pruning**：无类型 / **typed meta + AppPruning + intersect**（中；bug 高发区）
9. **合一器结构**：递归 conv / 工作表+位相等 / **单一 unify + `spec: Option<SpecSolve>`**（中；优雅度最高）
10. **模式编译**：决策树 / **逐臂**（强，A/B）
11. **覆盖探测**：推断级 / **值级**（强，4–5×）
12. **精化载体**：pm_defs / update_cxt / **σ**（中，非干净 A/B）
13. **全局名字**：哨兵 / decl 表 / **全限定键+Scope**（中）
14. **trait 求解**：Typ 桥 / **Val 级**（中）
15. **宏**：无 / **parser 期展开**（弱-中）
16. **内建/effect**：`Tm::Prim` / PrimId / **prim 入 decl 表 + effect**（中）
17. **原生 Nat**：一元链 / **`Val::Nat(u64)`+可归约桥**（中，与定义相等冲突）
18. **观察面/双引擎/测试**：无 / 三张 owned 表 / **owned 快照+单引擎+oracle**（中）

**组合冲突（D1 §7 摘要，决定"不能简单拼"）**：打包值↔UB/别名；σ↔生产规模；决策树↔诊断（已选性能）；
双引擎↔机制统一；原生 Nat↔统一定义相等；memo↔bump 生命周期；观察面↔引擎内存；可解集白名单↔旧层语义；
复合环境↔namespace 可变作用域。**这些冲突的最优解不是"逐轴赢家相加"，而是 §6 的两层分工。**

---

## 4. 逐轴对决（Q2）

> 每轴：候选 → 证据 → 选择 → 代价/适用条件。数字口径见 §5；详细锚点见 D1/D2/D5。

### 4.1 值/项表示与求值器：**arena + 打包值 + 扁平 spine + 迭代内核 + 稳态复用**

- 证据（最强）：L01 23 变体、n=4000 相对 `bump_spine_iter_ss`：naive 25.7×、cek 50.3×、
  `bump_tree` 7.1×、`bump_iter` 6.1×、`native_clo` 2.8×、`bump_spine` 3.0×、最优 `_ss` 1.00×；
  深 n=512k 时 `_ss` 6.18 ms vs cek 245.7 ms（40×）。抬速账本（单变量）：打包 −19% → 流式 quote −46%
  → 迭代化 −21% → 右链快路径 −43% → 稳态 −17%。`[历史实测] L01 readme；本轮 EXP-1 clean 复测同序`
- **选择**：生产引擎用这套；参考核心保留 Box/Rc 树（可读/可证明）。
- 代价/边界：① **非右链形状**（parigot/exponential）递归版反超迭代版 1.14–1.42×（未在带类型负载验证）；
  ② unsafe/打包/别名风险（wasm 对齐 UB 已发生过，Stacked Borrows 未清）；③ 稳态收益在 L02+ 只 2–8%，
  但 LSP 常驻 3.5× 才是真实价值；④ L01 已否决：native 闭包/指令数组/条目瘦身/内联 memo/`bytes_flat_value`。
- **生产取舍**：保留 arena+打包+迭代；把裸指针/`transmute` 换成**句柄索引**（D7 §4.1），性能损失待测（Q1）；
  双模 eval（递归快路径+迭代兜底）列为 P2 候选，先补混合形状负载实验。

### 4.2 元变量/pruning/合一器：**typed metas + 单一 unifier + `SpecSolve` + 三档判定**

- 证据：L03–L05 的正确性架构（pattern unification、invert/rename/prune、typed metas、`intersect`）是上游语义必需；
  L07 的"一个合一器 + `spec` 参数"消除 L07/L07a 双轨；σ 让可解性不再经全局通道（D2 A 轴）。
- **选择**：单 unifier + `SpecSolve`（生产与参考同构）；三档 `UnifyOutcome{Solved,Absurd,Undecided,Fuel}`；
  occurs 传递（Lean T1 精确刻画）；`MATCH_CMP_BUDGET=64` 口径统一。
- 代价：pruning 是全仓 bug 密度最高机制（L05 三代掩码 bug、L13 GADT 覆盖回归）；typed meta 的
  telescope 物化是未解性能税（L05 prune 8.7 s；文档有"增量闭前缀缓存"方案未做）；L09–L12 的 PM_FUEL
  耗尽静默降级必须改为诊断（D2 G1）。

### 4.3 模式匹配：**逐臂下钻 + 值级探测 + 独立 usefulness 诊断 pass**

- 证据（结论最硬）：决策树 vs 逐臂受控实验：臂数 5→65 从 10× 拉到 **2363×**；通配列 2→8 拉到 **14822×**
  （m=10 >900 s）；无通配交叉积对照只 6–17× ⇒ 爆炸来自通配臂复制，是算法级；运行期两版都是线性首匹配，
  **决策树无运行期收益**。逐臂 + 值级探测（L10 4–5×，判定逐例一致）已全仓统一 `[历史实测 2026-09-17/09-20]`。
- **选择**：逐臂负责编译/特化；**独立 usefulness/覆盖分析 pass**（Maranget 式）补回路径感知诊断，
  按需运行（LSP 诊断/错误路径），主路径不做覆盖扫描。不回到决策树。
- 代价：新诊断 pass 约 800–1200 行 + 诊断 golden 语料；L07 现状"只做顶层覆盖"会丢嵌套/组合缺口
  （L13 Bool×Bool 组合仍接受，D2 B 轴）。

### 4.4 精化载体：**σ（新架构内实施）**；失败则保留 update_cxt 并关门

- 证据：`pm_defs` 事实表 → 淘汰；`update_cxt`+`refresh` → 已捕获旧上下文过期/槽位错位 bug 族（L07 §6）；
  σ 在 L07–L12 六层落地（逐字节 diff=0、全量 4013 例 0 失败、L08 struct 32×/strchain 38× 的生产收益）；
  **反证**：L13 σ 五轮失败（纯 elab ~28×、12k meta 解链、FRCS_MEMO 13 GB、4 个 parity 失败、GADT 覆盖回归）。
  **本轮新增成本信号**（D4 §2）：旧事实表 l07pre 在 deep 模式上比 σ 版 L07 快 ~6×（代码整体不同，非严格 A/B）——
  σ 不是免费午餐，深嵌套模式路径必须单独量化。
- **选择**：生产引擎采 σ，但按 D7 §4.2 的前置条件实施（内容寻址 memo、观察面 owned/prelude 关表、
  meta 解链环检测、深链内存预算、逐列 refine 传播）；P4 门禁（prelude-core ≤1.5× baseline、GADT parity、
  全量差分零判定漂移、内存 ≤1.2×）不过则**保留 update_cxt**，负结果写档。
- 关键反证解读：L13 失败主因是"σ 消费点在生产规模扩散"，不是 σ 语义错误；D6 C-2 的孪生 σ 移植实测
  prelude-core/examples-hdl **−5.5%**、417 parity 全绿，但 prelude-hdl **+9–11%** 回归未解——这是"统一 vs 分层"的
  唯一实测材料，说明 **σ 可在生产规模工作但有反向交换，必须以门禁裁决，不能靠信念**。

### 4.5 名字世界：**全限定 decl 表 + per-file Scope**

- 证据：`Infer.global` 大下标哨兵（L09/L10）把全局编码进 de Bruijn，shift/rename 特判、双名字表、off-by-one 历史 bug；
  L11 反手切回 decl 表；decl 表 Rc 化实测 3.2–3.5×；L13 全限定键+package/import 已在 29/30 生产语料验证。
- **选择**：`Decl = FxHashMap<QualifiedName, DeclEntry>`；构造子只用限定键；`Scope`（imports/package/可见性）
  挂 AnalysisSession 而非 `Infer`；五级解析保持 L13 顺序、实现为纯函数。
- 代价：显式名字解析 API；Scope 快照成本（Rc）；跨文件会话仍需 §7 P3。

### 4.6 trait/typeclass：**Val 级 tabled + 单向前提 + 确定性/coherence 诊断**

- 证据：L10 `Typ` 桥 + `Synth` 是 toy（多解取 HashMap 迭代序、`effort>1000` panic、close O(n²) 修复只落孪生）；
  L12 Val 级 `val_match` 更完备（去掉有损桥）；L13 自写 typeclass + 真实 prelude 工作，但实例 Nat 参数 bug 未根治。
- **选择**：Val 级 tabled resolution；单向前提（正确性硬要求）；实例头索引；coherence/孤儿规则显式检查；
  预算耗尽返回 Diagnostic；删除 `canonical`/`iddfs`（仅 Err 重试路径、run/run_fast 不经，零测试）。
- 代价：约束 meta 的"延迟解"是架构级改动（L13 Nat 参数 bug 根治需要），列 P5/未决；短期先做"实例 unify 后重新 eval"。

### 4.7 宏 / prim / effect / 原生 Nat

- **宏**：parser 期 `macro_rules` 展开 + token 直接拼接（旧序列化重词法 fast_run −15~−18%）；深度/规模双预算（256）；
  把"宏展开后源"作为独立 IR（`ExpandedDecl`）而非字符串拼接；v1 不做卫生宏（与语言兼容；可 v2 立项）。
- **prim/effect**：prim 入 decl 表（L13 形态，单一名字世界）；`DeclEntry.effect: Effect{Pure,Stateful(...)}`
  在注册期由 AST **静态分析**（不靠 `def_needs_replay` 名字 memo——它已导致 twin def-journal 崩溃）；
  `Pure` 可记忆化，`Stateful` 显式重放；IO prim 返回 Result 进诊断（现在 `file_*` panic 且无锁）；可变全局挂 AnalysisSession。
- **原生 Nat**：保留 `Val::Nat(u64)` + 字面量直构 + eval 装配点折叠 + `quote_nat` 展开回链 + nat prim 惰性一步可归约；
  护栏：`NAT_CHAIN_LIMIT`、大整数字面量展开上限、孪生/参考"succ(原生 Nat) 折叠"对齐测试。
  这是**语言定义相等选型**，不是纯性能；D2 列为最高未形式化风险之一（unary↔native 无对拍），必须补影子对拍。

### 4.8 LSP 观察面：**owned 快照 + push 期渲染 + prelude sink 空实现 + 内存预算**

- 证据：live `Val` 句柄无法跨 bump 轮；owned 快照是跨引擎唯一安全契约（27 个 push 点）；
  prelude 期渲染是纯死工作（`lsp_collect` 总闸 21.1→9.3 s；master 参考版未落）；观察面在 wide_enum 可占 54–59%；
  twin 常驻 429 MB 稳态/730 MB 峰值 vs 参考 200 MB，压实后每 kick 908→181 MB 但 +150–190 ms。
- **选择**：`observe` crate 的 `Sink` trait；prelude 装载传空实现（零成本，不是运行期 `if observe`）；
  每次分析产不可变 `AnalysisSnapshot`（diagnostics/hover/completion/inlay/symbols/def-map）；LSP 只消费快照；
  prelude/常驻/压实/观察闸合并成 `PreludeSnapshot` 生命周期对象；字段投影 `def_span` 在新表示里直接修（不要观察面打补丁）。
- 代价：push 期 quote 成本（按 decl 惰性补表兜底）；wasm 内存硬顶（1.2 GB vs 2 GiB ⇒ wasm 先保参考引擎）。

### 4.9 双引擎：**四角色分工（S 规格 / P 生产 / R 参考核心 / O 过渡 oracle）**

- 三方输入：D1"不要统一成一个引擎"（P≠R 实现不合并）；D3"单生产引擎 + 冻结 oracle"（生产 46% 冗余消除）；
  `l13-perf-replace`"α 生产取代、β 参考降 cfg(test)、γ 永不退休 oracle"。D7 §5 裁决：**三者是同一方案的两个时间阶段**。
- 四角色（D7 §5.2）：
  | 角色 | 代码 | release | cargo test | 权威性/生命周期 |
  |---|---|---|---|---|
  | **S 规格** | Lean M1（38 定理）+ M3 oracle + `spec/` 锚点 | 否 | CI | 最高终审；永久 |
  | **P 生产后端** | arena 引擎（twin 血统重写为安全句柄版）+ LSP/HDL/观察面 | **唯一** | 是 | 用户可见行为以它为准；永久 |
  | **R 参考核心** | 新 `refcore`：**L07 的 σ+逐臂**语义基底生长到完整语言面；树形可读可证明；无 LSP/HDL/perf | 否 | 是（差分 oracle） | 永久；与 P 分歧 = bug 报告 |
  | **O 过渡冻结 oracle** | 现 L13 参考版冻结（22.8k，update_cxt 血统） | 否 | 是（P0–P5 差分） | 临时；R 达 T2 后删/归档 |
- **parity 不降级**（修正 v1 草案）：P/R 共享 `elab-parse`/`elab-diag`（诊断渲染器+Span+meta 命名），
  **T1** 每次 CI（判定 + Ok 输出逐字节 + 诊断 code/span/severity）、**T2** oracle job（全语料 Err 正文逐字节，`?N` **不归一化**）；
  豁免清单显式登记，禁止"参考版改了孪生没改"。
- **R 选层 = L07**（唯一有正向设计文档、Lean M1/M3 形式化对象同源、最小 4.3k 生产）；L12 作特性移植参照，
  L13 参考版只当 O，L09 否决（哨兵名字世界+决策树时代）。代价：R 需生长 ≈6–9k 行到 ≤14k。
- 为什么不是 A（双生产引擎）/ C（无 oracle）：A 违反简洁/可维护且已出现"只在孪生"机制导致语义分叉；
  C 删除独立判据后同错类（L13 单行 enum 假阴性）无从发现，D2 明确不认可。
- 与 D1 不矛盾：D1 的"不要统一"约束 **P≠R 实现不合并**；"产品只留 twin"约束 **生产入口唯一**。
  合起来终态 = P 唯一生产 + R 唯一测试期语义参考 + O 过渡 + S 机检。

### 4.10 测试 / 形式化 / 正确性护栏

- 证据：D2 盘点——测试金字塔"塔尖薄、塔基厚而不齐"：lib L07 70/L09 10/L13 612；parity 27/35/29/21/19/15/15；
  黑盒仅 L07/L08 厚；Lean 声明层 57 定理 + 引擎 M1 38 定理（零 sorry）+ M3 oracle 4 curated；
  **最关键的精化/元变量/NBE/fuel/名字层恰在形式化空白**（`trans`/`subst` 字面写法在标准规则下不可判型却被实现接受）。
- **选择**：四路护栏（D2 §5）：G1 三档判定全局化（预算耗尽永不判 Absurd/不可达，Lean T3）；
  G2 四路差分矩阵（ref↔twin parity；unary↔native Nat 影子对拍；σ↔update_cxt 跨载体对拍；Lean M3 生成式语料+第三方裁判）；
  G3 不变量 I1–I15 每条≥1 回归钉（关键项进 debug_assert）；G4 属性测试（subst 组合/occurs/quote∘eval/rename 往返/
  pretty∘parse 稳定）+ fuzz（parser/preprocess/macro/elaboration 入口，无 panic + 内存上限）+ 内存/UB（Miri/TSan 定期）；
  G5 CI：`lake build` + oracle 差分 + 全量 cargo test + 性能烟测（同批交错 + null 地板）。
- 代价：诊断类型统一要改所有层签名（一次性机械）；M2（精化 match 形式化）是长期攻坚，不 v1 承诺。

### 4.11 错误 / 预算 / 防护

- 现状缺陷类（D2 §3，18 条台账）：R1 分类器不完整、R2 occurs 丢外层 σ、R3 预算代理不同构、P15 struct_eq 漏 pending、
  R6/R7 span 坐标、R9 UnifyKind 不随快照回滚；L13 仍是旧口径（occurs/预算/三档 0 命中）；
  panic 面：`Too much effort :(`、`file_*` panic、`v_app`/`lvl2ix`/unwrap 族；PM_FUEL 耗尽静默降级。
- **选择**：单一 `Diagnostic{code,severity,span(原始坐标),message,related}` + 单一 `UnifyOutcome`；
  预算统一 step 计数口径（`MATCH_CMP_BUDGET=64` 总次数/每入口 reset/快路径先试）；
  所有用户输入路径 `Result<_, Diagnostic>`（无 panic 控制流）；深值 quote/pretty/Drop 统一显式栈 API；跨 meta 环守卫与 fuel=0 不入 memo。
- 代价：跨层签名机械改动；预算口径需跨引擎一致性测试（单引擎后自然消失）。

---

## 5. 实验记录（Q2 的数据面；完整 raw 见 `experiments/raw/`）

### 5.1 协议与环境

- 机器：AMD Ryzen 5 5600（6C/12T）、34 GB RAM、Windows；构建目录 `C:\ezl-target`（F: 仅 0.8 GB 空闲，禁止构建）。
- 二进制：HEAD `8443586e`，`cargo build --release --bins`，2026-11-09 01:25–01:32（Finished in 6m45s）。
- 每数据点独立进程、`--rounds 3`、取 min（同时记 med）；EXP-3 每层每负载一条命令。基准行口径：
  `basic`=参考版；`fast_ss`=孪生稳态（解析在计时外）；`fast`=孪生一次性；`fast_run`=孪生全流程（仅 L11/L12）。
  **basic 与 fast_ss 不同轴**，跨层比较只能用同轴口径或绝对时间。
- 原始文件：`experiments/raw/exp1-*`、`exp2-*`、`exp3-*`、`exp5-*`、`exp6-*`、`EXP-7-*`（见 §5.6）。

### 5.2 EXP-1：L01 表示对决（本轮 clean 复测，rounds=3）

`[实测]` `exp1-clean-*`（01:37）。`church_pair` n=1000（min ms）：`bump_spine_iter_ss` 0.008、
`bump_spine_iter` 0.008、`bump_spine_slim_ss` 0.009、`bump_spine_memo` 0.009、`bump_spine` 0.015、
`bump_spine_slim` 0.010、`bump_spine_rpn` 0.014、`bump_spine_memo_inline` 0.010、`bump_tree` 0.040、
`compiled` 0.051、`bump_arena` 0.065、`cek` 0.366（n=1000；n=2000/4000 同序）。
`guest/church_mul` n=200：`_ss` 0.146、`iter` 0.184、`memo` 0.200、`spine` 0.307、`tree` 0.793、`naive` 156.5。
`dup`/`dup_deep`：memo 对 iter 的收益随复制层数扩大（历史 1.8×/3.7×；本轮 clean raw 同方向）。
**结论**：与 L01 readme 的 23 变体结论一致——`bump_spine_iter(_ss)` 是默认赢家；**quote 记忆化是"共享形状专用"**：
本轮 clean 复测 guest/exponential ≈**2000×**、parigot ≈500×、dup_deep 3.9×，而 church_mul 无益（哈希税）；
非右链形状（parigot/exponential）递归版更快（历史 1.14–1.42×），是唯一未移植到带类型负载的"更优点"。

### 5.3 EXP-2：pmab 复跑——原题已不可复现，改测三个逐臂内核

`[实测]` D4 §2：**HEAD 已无决策树**（L09 于 2026-09-18 改成逐臂，`src/L09_mltt/pattern_match.rs:187`，
`pmabbench` 源码注释已过期）⇒ 原"逐臂 vs 决策树"在当前代码上不可测。已测三个逐臂内核的差异：
**deep 扫描 L09 差 22×**（L07 血统更优）；**旧事实表 l07pre 在 deep 上反快 6×**（σ 代价的首个量化证据，
但 l07pre 是重构前整体代码，非严格单变量 A/B）；flat/cart 平价；wild 上 L07 优 3.4×。
历史受控实验（2026-09-16，决策树仍在时）仍是"决策树→逐臂"的原始依据：臂数 5→65 10.4×→**2363×**、
列数 2→8 9×→**14822×**（m=10 >900 s）。结论：逐臂胜且无运行期收益损失；**σ 在深嵌套模式上的代价必须由
P5 门禁单独量化**（l07pre 对照是首个信号）。**教训**：基准工具要随实现演进而废弃/更新，否则会给出"过期结论"。

### 5.4 EXP-3：当前 HEAD 七层主矩阵（本轮 clean 段 l11–l13 + l07–l10 部分）

`[实测]` `exp3-*`（01:35–01:38；k=11，min ms）：

| 层 | match basic | match fast_ss | 备注（同文件其它负载） |
|---|---:|---:|---|
| L07 | 0.150 | 0.050 | enum k9 0.275/0.072；church k11 2.608/0.271 |
| L08 | 0.148 | 0.051 | enum k9 0.289/0.078 |
| L09 | 0.195 | 0.073 | enum 0.741/0.117；universe k11 6.724/1.646（vs 09-20 矩阵 3191 ms：D² 修复生效） |
| L10 | 0.094 | 0.053 | （L10 参考版 match 已优于旧矩阵 0.171） |
| L11 | 0.209 | 0.045 | natadd k11 1.863/0.833 |
| L12 | 0.205 | 0.047 | natadd k11 1.726/0.837（eprintln 已删，basic 从 1.431 回落） |
| L13 | 0.214 | 0.149 | gadt k9 0.402/0.207；moduletree 0.198/0.126 |

**读数**：① 孪生仍全面领先，但差距随层差异大（L07 3.0×、L10 1.8×、L13 1.44×）；② L09 的 universe 从 3192 ms
降到 6.7 ms 证明 09-20 矩阵的 L09 地板已被 D² 修复消除；③ **L10 参考版 match 全场最快（0.094 ms）**——
"无 decl 表 + σ 移植后的 L07 血统"在 match 上比 L07 还快，说明生产引擎的额外结构（decl 表/宏/namespace）是税；
④ L13 的 match 绝对值和 L07 同档（0.21 vs 0.15），"生产引擎必然更慢"不成立——慢在 prelude/观察面/规模，不在 match 内核。
⑤ **L10 traitchain k=9：参考版 23,791 ms vs 孪生 39.4 ms（≈604×）**，是全场最大同层差距；
EXP-5 同负载内存 **5.30 GB / 1.22 亿 allocs vs 30.6 MB / 25 万（173×/489×）**——独立复核了 L10 `close` 修复
只落孪生、参考版 trait 路径仍病态（D4 §3/§4）。

### 5.5 EXP-5/EXP-6：内存与真实负载（本轮已执行，raw 见 `exp5-*`/`exp6-*`）

**EXP-5 分配/内存**（`l06l13mem`，确定性口径，min/均值见 raw）：
- **L10 traitchain k=9**：参考版 **122,477,444 allocs / 5,298 MB 累计字节** vs 孪生 **250,364 allocs / 30.63 MB**
  ⇒ **489× allocs / 173× bytes**（参考版 trait 求解在方法链上的重复劳动是内存/分配主因之一；与 D5 "L10 参考版病态"一致）。
- **L13 prelude-core（208 decls）**：参考版 1,046,766 allocs / 151.06 MB vs 孪生 266,628 / 49.31 MB（3.1× bytes）；
  稳态 churn 参考版与孪生差距缩小但仍显著（36.23 MB/3 轮 vs 参考版未给 churn，见 raw）。
- **L06/L10/L13 church k=9**：alloc 比 basic/fast = 967×/166×/7.7×；**L13 的 fast 仍有 2,403 allocs/轮**
  （观察面/decl 注册/Tycker 结构，非核心），提示单引擎仍需 churn 预算。
- 结构尺寸（`exp5-sizes.txt`）：`V` 打包 8B 全层一致；`Tm` 56B；`MetaEntry` L13 40B（其余 24B）；
  `Machine` L06 536B → L13 1,616B；`Tycker` 560B → 2,632B（常驻结构随生产特性增长，需纳入内存预算）。

**EXP-6 真实负载**（`l13bench`/`typort check`）：
- **prelude-core（208 decls）**：basic **55.7 ms** vs fast **18.8 ms** / fast_ss 20.3 ms（**2.8–3.0×**）。
- **prelude-hdl（1439 decls，当前 prelude 规模）**：basic **5,171.7 ms** vs fast **1,800.0 ms** / fast_ss **1,365.9 ms**
  （**2.9–3.8×**）。注意这是 11-09 新 prelude（1439 decls）而非 09-20 的 943 decls，不能与旧矩阵数字直接比。
- **examples-hdl**（6 文件）：basic ~53–57 ms vs fast ~19–22 ms（~2.7–2.9×）；raw 标 `BOTH-FAILED`
  （两版都未跑完——与范式一致无关，需后续判定是 bench 期望/超时还是真实回归，**不能据此宣称功能正常**）。
- **`typort check` CLI（纯参考版管线）**：`examples/alu.typort` **5,212 ms**、`adder_proof.typort` **5,491 ms**（exit=0；
  LOG 显示 infer 仅 ~0.1 s，**几乎全是 prelude 装载**）⇒ CLI 墙钟大头是 prelude/参考引擎，而不是单文件 elaboration；
  这是"生产路径统一到单引擎 + 常驻 prelude"最直接的用户可见收益证据。
- 历史对照（09-20 旧 prelude 943 decls）：prelude-hdl 参考 3073 ms vs 孪生 1332 ms（2.3×）；LSP 稳态 kick 359→102 ms（3.5×）、
  常驻内存 429/730 MB vs 200 MB。**新旧不可混比**（prelude 规模已变）。

### 5.6 EXP-7：正确性套件实跑（本轮已跑核心套件，全绿；LSP/lib 其余待补，D2b）

**执行方式修正**：首版 runner 因本机 `NO_PROXY/no_proxy` 环境变量重复键使 `Start-Process` 抛异常（不是测试失败）；
改用**直接调用已构建 test exe**（`C:\ezl-target\release\deps\...-hash.exe --test-threads=1`）后正常。
`[实测]` `raw/EXP-7-summary.csv`（v2 runner，2026-11-09 01:58；Lead 直接调用交叉复核见 `raw/EXP-7-lead-run.txt`）：

| 套件 | passed | failed | ignored | 耗时 |
|---|---:|---:|---:|---:|
| lib-L07 / lib-L08 / lib-L13（filter） | 70 / 60 / 614 | 0 / 0 / 0 | 0 / 0 / 6 | 8.5 / 1.2 / 126 s |
| l07_blackbox / v2 / v3 | 48 / 51 / 116 | 0 | 1 / 2 / 1 | 0.8 / 0.2 / 7.1 s |
| l08_blackbox / v2 | 57 / 51 | 0 | 1 / 2 | 0.8 / 0.2 s |
| l07–l13 fast_parity | 97 / 95 / 39 / 46 / 52 / 50 / 629 | 0 | 0/0/0/0/0/0/6 | 8.4/2.1/0.1/0.1/0.2/0.1/129.9 s |
| known_bug_pins | 8 | 0 | 0 | 8.4 s |
| LSP namespace/hover/completion/cross_file | 全部绿（详见 D2b §3） | 0 | 0 | — |
| `LEAN_ORACLE=1` lean_oracle_parity | 2 | 0 | 0 | 1.0 s |

**汇总（D2b，最终版）**：**25 个运行目标 = 2,255 passed / 0 failed / 19 ignored，全部 exit=0**
（语言 17 目标 = 2,085 passed；LSP/lib 补充 8 目标 = 170 passed；Lead 独立直接调用 11 目标 = 1,115 passed，
与 v2 runner **逐项一致**）。**D4 数据独立复核**：4 个复跑点中 3 个计时点误差 +0.7%~+0.9%，
确定性分配计数（L10 traitchain 122,477,444 allocs / 5,298.18 MB）**逐值相同** ⇒ D4 数据可信。

**判读**：① 当前 HEAD 重建二进制上 **0 failed、0 新回归、0 panic/超时**；② parity 的 passed 数大于"套件自有"数，
因为 `#[path]` 把本层 lib 测试编入（如 l13_fast_parity 629 vs README 341 静态口径；`lib-L13` 单跑 614 = 612 静态 + 2 带入）；
③ **Lean oracle 真跑 2/2 通过**（非 skip）；④ 已知 bug 钉 8/8 通过；⑤ 历史文档"全量 lib 49 个既有失败"在 L07–L12
过滤下**不复现**（口径存疑，D2b §6 登记）。
**未跑/待补**：LSP 其余 7 套件、`twin_engine_tests`、手工 bug 复现（E7.6）、默认并行压力轮、L01–L06 套件
（D2b §8/§10）。**因此"全仓全绿"不成立；且已知假阴性与未覆盖轴（单行 enum、L09 卡住 match panic、effort cap、
with-K、Nat 定义相等）仍在，不得把"全绿"读作"正确性已证"。**

### 5.7 EXP-8：分支/WIP 收割（计划，D6）

D6 结论：90 本地分支中 58 已完全并入；真正值得回头收的只有 3 项：
1. **`analysis/l04-l07-perf`**：prune k=9 **7.9 s→36–76 ms（>100×）** + Machine 常驻 chain −12%，master 未收，
   且 09-20 矩阵仍复现 L05 prune 8.09 s；L05 孪生仅 603 行变动最易重落。**本轮未复测**（EXP-8 计划项，
   需要新 worktree + 构建）；若成立，这是"每章优秀之处"里最值得并入的一项。
2. **`l13-perf-replace` 的 R0/R1**：引擎归属对拍 + 项目会话/视野闸；文档未提交（风险：未跟踪文档随时丢失）。
3. **`perf/l13-twin-sigma`**：σ 可移植到 L13 孪生的实测（prelude-core/examples-hdl −5.5%、417 parity 绿、
   prelude-hdl +9–11%），作为 D5/D7 的"统一 vs 分层"证据，不直接合分支（269 commits 漂移）。
不要再碰：wip 五轮 σ 补丁重放、l13-perf-round3 四补丁（已证伪）、7–8 月结构实验三连、sync-quote（53 commits）、
8 月 backport 三连。**实验方法教训 12 条**见 D6 §5（口径/符号一致/<3% 门槛/负结果写档/未跟踪文档/架构拆分杀死补丁等）。

### 5.8 EXP-4：消融实验（已设计，未执行）

D5 §7 设计 11 项，真实可跑开关：`L0x_NO_CONV_MEMO`、`L0x_NO_NAME_MAP`、`L02_NO_BITEQ`、
`TYPORT_TWIN_NO_COMPACT`、`TYPORT_TWIN_NO_USER_OBSERVE`、`TYPORT_LSP_ENGINE`；需 worktree 重放的补丁类实验：
C2 尾任务寄存器化（12 行，−5.7…−7.4%，**唯一已判定待落地**）、NOBSERVE、FORCE_MEMO 开关、decl 表 COW vs 平铺、
fuel 耗尽行为。协议：一次构建、每臂独立进程（开关 `LazyLock` 只读一次）、同批交错 + 配对 + null 地板、≥21 reps。
未执行原因：时间窗与单实验线纪律（不能与 EXP-7 并发）。**这些是下一轮的第一优先级。**

### 5.9 实验局限

1. EXP-1/2 首轮与构建尾部重叠，已 clean 重跑；EXP-3 首轮参数 bug（PowerShell `$args`）已删除重跑。
2. EXP-3 覆盖 k=9/11、每层 2–4 负载，不是全矩阵；大值负载（strchain/struct）未在本轮重新全量跑。
3. EXP-7 完成 25 个目标（2,255 passed / 0 failed），但仍有 LSP 其余 7 套、twin_engine、手工 bug 复现、
   L01–L06 套件未跑；"全绿"不等于"正确性已证"（D2b §6/§10 列出未覆盖轴）。
4. EXP-4（消融）、EXP-8（分支收割）仅设计/未执行；EXP-5/6 已执行（见 §5.5）。
5. 本机 governor 档位噪声使 <3% 效应不可判（D5 §1）；所有"更快/更慢"的强结论必须以同窗口交错+null 地板为准；
   D4 的 4 点独立复核误差 ≤0.9%，确定性分配计数逐值相同。

---

## 6. 最优架构提案（Q3；以 D7 为基础，Lead 裁决）

### 6.1 一句话架构

**一个以 NbE 为核心的编译器：parser → 声明注册（全限定名字世界 + per-file Scope）→ 逐 decl elaboration
（σ 显式替换精化 + 逐臂模式编译 + Val 级 tabled trait 求解 + effect 分类）→ {不可变诊断/观察快照 → LSP,
HDL 模块树 → Verilog}；树形参考引擎只作为测试 oracle 存在（release 不含）。**

```
源文本 ─► [parser] 恢复式 lex/parse + 宏展开 + derive（保 span/字节长）
   │ Decl/Raw
   ▼
[names] 全限定 decl 表 + per-file Scope(import/package)
   ▼
[elaboration] 逐 decl: check/infer（meta、trait、effect/replay）
   ├─ [pattern] 逐臂编译 + 值级探测 + 独立 usefulness 诊断 pass
   └─ [refine] σ: Subst/VSub/frcs/SpecSolve + subst_cxt
   ▼                          ▼
[observe] owned AnalysisSnapshot   [hdl] ModuleTree → Verilog
   ▼
[lsp] Rope 文档 + PreludeSnapshot 会话 + 跨文件重建
```

关键性质：数据流单向；观察面是旁路 sink（不是 `Infer` 字段）；HDL codegen 是 elaboration 之后的纯函数；
生产构建不含 oracle；层差异是 golden 快照而不是源码副本。**四角色**：S（Lean 规格，CI 终审）/
P（本图的 arena 生产引擎，唯一进 release）/ R（`refcore`：L07 的 σ+逐臂语义，仅测试期差分）/
O（现 L13 参考版冻结，过渡 oracle；R 达 T2 后删/归档）。

### 6.2 模块与复杂度预算（D7 §3/§7，D3 §7）

**共享与不共享**（D7 §5.5）：三个共享 crate = `elab-parse`（lex/parse/derive/宏/span/preprocess）、
`elab-diag`（Diagnostic/schema/renderer/pretty/Span）、`elab-hdl`（ModuleTree/Verilog/自检，纯函数）；
**不共享**：值/项表示、eval/force/quote/rename、unify 内核、decl 存储/缓存、观察面/LSP/池化（P 专有）、
精化载体实现（P/R 都 σ，槽位纪律 I1–I4 是契约）。

| crate | 预算 | 职责 |
|---|---:|---|
| `syntax` | ≤1k | Span/Ix/Lvl/Raw/Tm/PatternDetail |
| `parser` | 4–5k | 恢复式 lex/parse、preprocess 保字节长、macro_rules 展开（深度/规模预算）、derive |
| `arena` | 0.5–1k | bump 分配 + 句柄索引（**无裸指针/无 transmute**，唯一 unsafe 白名单） |
| `core` | 5–6k | Val 14 变体、eval/quote/force、有界记忆化接口 |
| `unify` | 4–5k | meta 表、unify/invert/prune/rename、`UnifyOutcome`、预算 |
| `refine` | ~2k | Subst/VSub/frcs/SpecSolve/subst_cxt |
| `names` | ~2k | 全限定 Decl 表 + Scope + 五级解析纯函数 |
| `pattern` | ~3k | 逐臂编译 + 值级探测 + 独立 usefulness/覆盖 pass + 诊断 |
| `classes` | 1.5–2k | Val 级 tabled 求解、outParam、coherence、诊断 |
| `elaboration` | ~5k | check/infer、decl 各形态、class 两阶段、BindingName、effect 分析/replay |
| `prelude` | 0.5k + 35 `.typort` | 单一装载序（从文件生成，不手写双份） |
| `hdl` | ~4k | 模块树/端口/信号/Verilog emit/自检规则 |
| `observe` | ~1k | `Sink` trait + `AnalysisSnapshot`（owned） |
| `lsp` | 3–4k | Rope 文档、会话、worker、跨文件重建、请求分派 |
| `cli` | ≤0.5k | check/emit/tutorial/quick/stats |
| `refcore`（dev-only，R） | ≤14k，0 unsafe | L07 σ+逐臂语义基底生长：namespace → Val trait → 宏（shared parser）→ 原生 Nat/prim/effect；仅 `cargo test` 差分 oracle |
| `oracle-frozen`（dev-only，O） | 冻结 ≤23k | 现 L13 参考版冻结不改，过渡差分；R 达 T2 后删/归档 |
| `zoo`（dev-only，可选） | 冻结 | L01–L12 教学快照/golden，不进产品构建 |

产品实现 ≤30–34k 行（单份）；workspace 含测试 60–70k 行；其余历史层移出生产构建。
**门禁**：单文件 ≤1.2k；unsafe ≤60（理想 0）；环境开关 ≤4；生产 print/panic ≤20；跨层复制=0；
归档/`.bak`=0；bin ≤6；`#[path]` 重编译=0；文档 ≤8k 行；所有数字由 `tools/metrics` 生成。

### 6.3 不变量清单（I1–I15，D7 §3.2）

I1 force 顶层非 VSub；I2 槽位布局=运行时布局、subst_cxt 不增删槽；I3 σ 对 spine/参数槽只包裹不物化；
I4 "解前构建、解后消费"的值在消费点用当前 σ 包裹；I5 σ 无环、occurs 传递（Lean T1）；
I6 Absurd 仅当规范头冲突、Undecided/Fuel 永不当 Absurd（Lean T2/T3）；I7 预算计数单调、超限不伪装 Absurd（T4）；
I8 decl 键全限定、裸名只经 Scope；I9 分析产物不可变、观察表 owned、prelude 不收集；
I10 arena 值只经句柄访问、跨轮无悬挂；I11 effect 行注册期静态确定（纯可记忆化/有状态只重放）；
I12 诊断 span 指向原始源码坐标；I13 用户输入零 panic（全 Diagnostic）；I14 用户可见判定只由生产引擎产生；
I15 语义变更必须同步 Lean 规格/spec 锚点。每条至少 1 个回归钉；I2/I3/I5/I6/I7/I9/I10 进 debug_assert/运行时校验。

### 6.4 与"各章优秀之处"的对应（用户问题的直接回答）

| 来源 | 可继承的"优秀之处" | 在目标架构中的位置 |
|---|---|---|
| L01 | 23 变体实验方法 + arena/打包/spine/迭代/稳态赢家；负结果清单 | `arena`/`core` + `tools/bench`（测量方法论） |
| L02–L05 | 双向 elaboration 结构、typed metas/pruning、`spec` 单一 unifier、位相等/记忆化的正确性纪律（快速路径不能是唯一依托） | `unify`/`elaboration` + 属性测试 |
| L06 | decl 表/builtin/可变全局的初代形态与 `FILE_IO_LOCK` 教训 | `names`/`elaboration` effect |
| L07 | **σ 显式替换 + 逐臂下钻 + 卡住 match 一等值 + 三档判定 + P1–P11 加固**（全仓最高价值设计资产） | `refine`/`pattern`/`unify` + 不变量/Lean |
| L08 | 零核心机增量的"糖层"原则 + 强 parity（Err 正文逐字节） | 语言扩展的验收标准；golden 差分 |
| L09 | typed meta 的清晰教学 + `check_universe`/`check_ctor_wf` | `elaboration` 的检查规则 |
| L10 | 复合环境（defs 平坦 + bind 链）、值级探测、`close` 快路径思想 | `core` 环境表示/`pattern` 探测 |
| L11 | parser 内宏展开 + token 拼接 + `MacroExpansionInfo` + COW→平铺经验 | `parser`/`names` |
| L12 | σ 最完整参考实现、Val 级 trait 求解、Call 节点（渲染价值）、对照/负结果 | `refine`/`classes`/`oracle` |
| L13 | 全限定 decl 表/namespace/import、原生 Nat、effect/replay、观察面契约、prelude 池化/常驻/压实、LSP 真实负载 | `names`/`elaboration`/`observe`/`lsp` + `hdl` |

---

## 7. 迁移路线（Q4；D7 §8 摘要，Lead 调整）

> 原则：行为不变优先（先搬后改）、可回滚、门禁可机器判定；先测量后改语义。估时为量级（人周），非承诺。
> **两条轨道**（D7 §8）：P 轨（生产收敛：P0–P6）与 R 轨（参考核心：S0 冻结 O+契约 → S1 `refcore` 种子 →
> S2 生长 → S3 T2 交接 → S4 O 退休）；关键路径 = P0/S0 先行，P 轨与 R 轨在 T2 汇合。下表为 P 轨主表。
>
> **实现状态（2026-11-09）**：**P0 + P1 已落地**（分支 `p0-p1-baseline-cleanup`；实现报告
> `P0-P1-IMPLEMENTATION-REPORT.md`）。P1：`bench_head` 删除、`bench_pre` 迁 `tools/bench_snapshots/`、
> 105 个历史评审归档、17 个 `.bak` 删除（src 非空行 −25,334 = −11.0%）。P0：`tools/metrics.py --check`
> 基线（11 项）、34 文件双引擎 parity 报告（**panic 0**，并发现/修复一个 trait 重定义 panic）、
> Lean oracle 门禁脚本、CI optional gate。P2+ 未开始。

| 阶段 | 内容 | 门禁 | 回滚 | 估时 |
|---|---|---|---|---|
| **P0 基线与判据** | 引擎对拍报告（归属/回落类别/诊断字段/kick/RSS）；冻结 golden；CI 加 `lake build`+oracle 差分+全量测试；EXP-4/7 补跑 | 报告复现已知结论（29/30、18-utils、examples 1.78×）；golden 可重放 | 无写入 | 1–2 周 |
| **P1 零风险清理** | 删 `bench_head`（陈旧冻结快照）/17 `.bak`；`bench_pre` 迁 `tools/bench_snapshots/`；归档 `docs/review-*`；19 bench bin 合并与 Error 载体统一延后到 P2（非零风险） | 构建/测试不变；`cargo test` 绿；`cargo check --all-targets` 0 error | git revert | 3–5 天 |
| **P2 crate 抽取（行为不变）** | 建 workspace；抽 syntax/parser/arena/core/unify/refine/names/pattern/classes；产品暂用参考引擎、twin 作 bench/oracle | 全量测试绿；`typort check` 输出逐字节不变；构建 ≤1.2× | 逐 crate revert | 2–4 周 |
| **P3 生产引擎接管 CLI/check** | `typort check` 走统一生产管线；参考进 `oracle` feature；删 `on_change` 参考专线 | examples+tests 语料 check 逐字节一致；release 不含 oracle 符号 | env 切回参考（保留一版） | 2–3 周 |
| **P4 LSP 单引擎 + 跨文件会话** | 常驻 prelude 升级为项目会话（按 rebuild_set 拓扑序重放依赖段）；观察面分文件；删 twin_can_own/trust gate；wasm 视内存达标再翻 | 全语料 0 回落（`EXPECTED_FALLBACKS` 空）；LSP 套件+请求级 golden parity；wasm 峰值 ≤预算否则保参考 | 保留 `TYPORT_LSP_ENGINE` 一个 release | 4–8 周 |
| **P5 精化载体定稿（σ）** | 新架构内实施 σ（不背 L13 移植包袱）：内容寻址/canonical memo 键、观察面 owned+prelude 关表、meta 解链环检测、深链内存预算；参考 L13 round-6 清单 | prelude-core ≤1.5× baseline；GADT 覆盖 parity；全量差分零判定漂移；内存 ≤1.2×；d=400 不崩 | 保留 update_cxt 分支一个 release | 4–8 周（失败则关门） |
| **P6 诊断/effect/Nat 收敛** | 独立 usefulness pass；effect 行 + replay 规则化；Nat prim 规则表统一；IO→Result | 诊断 golden parity/显式升级清单；examples Verilog 逐字节一致；100% 用户输入无 panic | 旧诊断路径 feature | 3–6 周 |
| **P7 冻结与交付** | oracle 仅测试依赖；zoo 归档；删运行期开关；文档/CI 定稿；soak | release 无 oracle 符号；一个 release 真实编辑 soak 无漂移；复杂度预算达标 | 前一个 tag | 2–3 周 |

**最先做、性价比最高**：P0 + P1（零风险）+ P3/P4 中"桌面单文件 LSP 完全取代"一段（`l13-perf-replace` 判 8–14 人日）；
**最高风险**：P5（σ 门禁）与 P4 的跨文件会话；**不可逆点**：P7（删 oracle/开关前必须 soak）。

---

## 8. 负结果清单（"不要做"；来自 L01/L02/D5/D6/D2）

1. 原生闭包编译 / 指令数组 / spine 条目瘦身 / 内联记忆化槽 / `bytes_flat_value`（L01 实测否决）。
2. 决策树矩阵（编译期最坏 14822× 慢、无运行期收益）。
3. `Infer.global` 大下标哨兵 + 双名字表（L11 反手；off-by-one 历史 bug）。
4. σ 精化补丁在未做前置项时硬推 L13（五轮回退；只提取方案教训）。
5. Sum 臂 eval 记忆化（完整实现且正确，但 +5…+33% 回归，2026-08-14 撤销）。
6. L12 `canonical`/`iddfs` 重试搜索（成功路径不经、零测试；保留 Call 渲染价值即可）。
7. FRCS_MEMO 强持结果（8 GB）、FORCE_MEMO 1<<20 双强持（13 GB 长跑）——记忆化必须统一内存口径。
8. "预算耗尽静默降级为裸 rigid"（比缺预算更危险）；PM_FUEL/MATCH_CMP_BUDGET 口径必须可诊断。
9. 快速路径作为正确性唯一依托 / 未确认负载覆盖就否决优化（L02–L05 教训） / 单槽内联 memo（parigot 186× 慢）。
10. 把参考版与孪生都作为产品交付面；删掉 oracle（γ 永不）；无 oracle 的"单一实现"。
11. 把 `bench_head`/`bench_pre`/`.bak`/实验分支归档进源码树；未跟踪文档不归档（随时丢失）。
12. 没有负载画像的 micro-opt；跨窗口/跨构建比较；符号不一致的 A/B（当噪声处理）。

---

## 9. 结论

**"最优"不是一层，也不是一套新算法，而是一次分工重组**：
- **正确性**：把"两套实现互相盯"升级为"一个冻结的语义 oracle + Lean M1/M3 + 不变量 + 属性/fuzz"；
  σ/三档判定/occurs 传递/预算可诊断/with-K 定位是必须显式化的语义契约。
- **性能**：把已由 L01 系统实验证明的 arena 内核（打包值/扁平 spine/迭代/记忆化/稳态）作为唯一生产实现；
  真实负载（LSP/prelude/HDL）而非合成 match 作为验收口径；先删死工作（29.4×/28.6× 级收益）再谈微优化。
- **简洁优雅**：删掉 13 层 copy-forward 与第二生产引擎（37.8k 行零风险 + 82.9k 行降级为 oracle），
  把层差异变成 golden 快照；把 33 个环境开关收到 ≤4；把 5 个单文件巨兽拆到 ≤1.2k 行。
- **各章优秀之处的结合** = L01 的表示/测量 + L02–L05 的正确性纪律 + L07 的 σ/逐臂/三档 + L10 的复合环境/值级探测
  + L11 的宏/decl 表 + L12 的 Val 级求解/σ 参考实现 + L13 的 namespace/Nat/观察面/prelude 生命周期。

一句话：**"一个可读可证明的参考核心 + 一个性能超群的生产引擎 + 一套机器可检的正确性护栏 +
一个能持续删代码而不是加开关的工程纪律"** —— 这是本仓在当前约束下能达到的最优组合。

---

## 10. 附录：证据索引与未核实

### 10.1 证据索引
- 分报告：`FRAMEWORK.md`、`D1`–`D7`、`D2b`、`experiments/raw/`；上一轮描述性对比：`../compare-l07-l13/`。
- 历史实验：`docs/bench-matrix-2026-09-20.md`、`docs/perf-debt-2026-09-12.md`、`docs/pmab-per-arm-vs-decision-tree.md`、
  `docs/l13-perf-replace-2026-09-27.md`、`docs/wip/README.md`、`docs/lsp-twin-wiring-2026-09.md`、
  `docs/perf-l01-optimization-2026-10-06.md`、`docs/perf-l02-*`。
- 正确性：`lean/`、`docs/lean-compiler-formalization-plan.md`、`docs/archive/review-l07-hardening-2026-11-08/`。
- 代码锚点：D1–D7 各节（`src/...:line`）。

### 10.2 未核实/需下一轮（诚实清单）
1. **EXP-7 测试执行结果**（D2b）：**25 个目标 = 2,255 passed / 0 failed / 19 ignored，全部 exit=0**（见 §5.6/raw）；
   Lead 独立复跑 11 目标逐项一致；Lean oracle 2/2。未跑项：LSP 其余 7 套、twin_engine、手工 bug 复现、L01–L06。
2. **EXP-4 消融**（11 项）未跑：C2 寄存器化/L05 名称表/compact 阈值/observe 成本/FORCE_MEMO 等。
   本轮已执行的 EXP-5/EXP-6 见 §5.5（raw 已落盘，D4 报告若晚到以 raw 为准）。
3. **EXP-8 收割**：`analysis/l04-l07-perf` 的 >100× prune 修复未复现；`l13-perf-replace` R0 对拍未做。
4. **Q1/Q2 风险量化**：arena 句柄索引（无裸指针）性能损失 3–10% 是 `[推断]`；σ 在 L13 规模能否 ≤1.5× 未知。
5. **Grand 数字口径**：LOC 存在多种统计口径（物理行/非空行/PowerShell 漏行），本报告正文以 D3 非空行为 L01–L13、
   FACTS 物理行为 L07–L13 分别标注；终稿交付前应统一由 `tools/metrics` 生成。
6. **噪声**：EXP-2 原题（决策树）在 HEAD 已不存在，D4 已改测三个逐臂内核并注明；EXP-3 部分与构建尾部重叠（已标 clean 段）；<3% 差异不可判。

### 10.3 30 秒版
**单生产引擎（arena 内核对齐 L01 赢家）+ 冻结 oracle（L07 语义）+ 独立诊断/形式化护栏 + 删掉 13 层副本与第二引擎的工程纪律。**
先做 R0 判据与零风险清理，再做 CLI/LSP 单引擎接管，最后用门禁裁决 σ 是否统一；不追求"全编译器形式化"，也不接受"无 oracle 的单实现"。
