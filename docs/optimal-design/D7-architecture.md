# D7 最优架构提案 v1 + 迁移路线

> 作者：principal-architect。依据：master `8443586e` 代码/文档静态分析 + 仓库既有实验
> （`docs/bench-matrix-*`、`docs/perf-*`、`docs/wip/`、`docs/review-*`）。**未运行 cargo/bench**。
> 证据标注：`[码]`、`[文档]`、`[历史实测]`（引既有实测，注明日期）、`[推断]`（本提案判断）。
> D1–D6 在写作时尚未出现（`docs/optimal-design/` 仅 FRAMEWORK.md）；接口见 §10，收到后 v2 补引用。

## 0. 约束与"最优"的定义

本提案的"最优"是在以下约束下的最优（换约束则结论会变，见 §9）：

1. **产品目标**：桌面 + web 的 Typort LSP、HDL→Verilog 生成、CLI `check/emit`；单仓、小团队、
   Windows 开发机。用户诉求原话：*最简洁优雅、性能超群、确保正确*。
2. **语言面**：依赖类型 + 归纳族（GADT 索引）+ trait/typeclass + 宏 + 命名空间/package/import
   + 原生 Nat + HDL 宿主内建。**不新增语言特性**是本提案的显式前提（先整合，再扩展）。
3. **正确性优先于性能，性能优先于"层数/教学形态"**：7 层是开发史，不是产品形态。
4. 目标不是"把 24 万行改写成 2 万行"，而是**把产品路径收敛到单一实现、把重复与实验代码移出
   生产 crate**，并把已知缺陷类变成机器可检项。

现状规模（口径同 `FACTS.md`）：`src/` 362 个 `.rs`、213,804 行（不含 `tests/` 63 文件 32,726 行；
合计 ≈24.6 万行）`[码]`。L13 一层 52,723 行 = 参考侧 22,817（含 13,498 测试）+ 孪生 16,408。

## 0.1 D1–D3 输入后的裁决摘要（v1 写入时已吸收）

> 写作时 D1/D2/D3 已出现在共享文件系统（271/320/245 行），本节记录对 v1 草案的三处修订；
> 详细理由见 §5（单/双引擎）、§6（护栏）、§7（预算）。

1. **单/双引擎裁决收窄为三角色**（§5.2）：D1 说"不要统一成一个引擎"≠ 保留两个**生产**引擎；
   l13-perf-replace 说"生产只留 twin + 参考降级 cfg(test)"≠ 放弃可读语义核心。二者是同一方案的
   两个时间阶段：**P（生产后端，进 release）/ R（语义参考核心，仅 cargo test）/ O（过渡冻结
   oracle，R 达标后退休）/ S（Lean 规格）**。D1 的"不要统一"约束的是 **P≠R 的实现不合并**；
   "生产只留 twin"约束的是**生产入口唯一**。精确定义与共享/不共享清单见 §5.2/§5.5。
2. **parity 口径不降级**（修正 v1 草案）：采纳 D1 §8.6 的强 parity（Err 正文逐字节 + `?N` 不
   归一化），做法是让 P/R **共享诊断渲染器、meta 命名与 `Span` 类型**，使文本 parity 成为结构
   保证；门禁分 T1（每次 CI：判定 + Ok 字节 + 诊断字段）/ T2（oracle job：全语料 Err 正文）两级（§5.2）。
3. **规模口径与预算以 D3 为准**（修正 v1 草案）：D3 §1 指出 FACTS §2 的"生产 LOC"被低估
   1.5–2.6×，真实参考生产 82,946 / 孪生 85,411；目标预算采用 D3 §8（生产 core ≤18k、单文件
   ≤1.2k、`unsafe` ≤60、开关 ≤4 等）。本文件 §0 的 21.4 万行是 `src/` 实测口径，两者统计范围不同。

## 1. 一句话架构 + 数据流

**一句话**：*一个以 NbE 为核心、bump-arena 单生产引擎的编译器——parser → 声明注册（全限定
名字世界）→ 逐 decl elaboration（σ 显式替换精化 + 逐臂模式编译 + Val 级 tabled trait 求解）→
{不可变诊断/观察快照 → LSP, HDL 模块树 → Verilog}；树形参考引擎只作为测试 oracle 存在。*

```
源文本 ──► [parser] 恢复式 lex/parse + 宏展开 + derive
              │  Decl 序列（Raw，Span 保留）
              ▼
        [names] 声明注册：全限定键 decl 表 + per-file Scope(import/package)
              │
              ▼
        [elaboration] 逐 decl：check/infer（meta 求解、class 两阶段、effect/replay）
              │        ├─ [pattern] 逐臂编译 + 覆盖/可达性诊断（独立 usefulness pass）
              │        └─ [refine] σ 显式替换（Subst/VSub/frcs/SpecSolve）
              ▼
    ┌─────────┴───────────────┐
    ▼                         ▼
[observe] 不可变快照       [hdl] 模块树（语句/端口/信号）──► Verilog emit
 (diagnostics/hover/          （prelude .typort 提供 HDL 类型/宏/自检规则）
  completion/inlay/symbols)
    │
    ▼
 [lsp] 会话：Rope 文档 + 常驻 prelude 会话 + 逐文件/跨文件重建 ──► 客户端
```

关键性质：**数据流单向**（源→声明→推导→产物），无"推导期全局可变通道"；LSP 观察面是
elaboration 的**旁路 sink**，不是 `Infer` 上的字段；HDL codegen 是 elaboration 之后的纯函数。

## 2. 目标 / 非目标

### 2.1 目标（按权重）

| 目标 | 可验收指标（v1 目标值） |
|---|---|
| 正确性 | 已知缺陷类 R1/R2/R3/P15 类均有 Lean 定理或回归钉；用户输入零 panic；判定分类（Absurd/Undecided/Fuel）机器可检 |
| 性能 | 生产引擎：match 编译不慢于当前孪生（L13 fast_ss 0.172ms @k=11，`[历史实测]` 09-20）；真实负载 `prelude-hdl` ≤ 当前 1332ms；LSP 稳态 kick ≤ 当前 98ms；内存 ≤ 当前 429MB 稳态 |
| 简洁 | 产品 crate 生产代码 ≤ 30k 行（当前同类 ≈26k 但**重复两份** + 4k LSP 缝合）；概念清单见 §7；`unsafe` 目标 0 |
| 可维护 | 单一生产引擎；parity 从"两实现逐字节"降级为"oracle 差分 + golden 语料"；新增语言特性只改一处 |
| 生产就绪 | 零回落（LSP 全语料由生产引擎服务）；wasm 大文件不静默崩；错误恢复与诊断位置正确 |

### 2.2 非目标（v1 明确不做）

- 不做全编译器形式化（24 万行不可行，`docs/lean-compiler-formalization-plan.md §4 M5`）。
- 不做 without-K 安全论证（L07 定位为 with-K 教学检查器，`docs/l07-dpm-refactor-design.md` 开篇警示）。
- 不新增语言特性（除缺陷修复）；不重做 HDL 语言规范。
- 不追求"7 层每层都保持双引擎 parity"——层是历史，产品只保留一条路径（§5）。
- 不做 Aeneas/Charon 全核心细化（M4），只对 2–3 个纯函数可选尝试。
- 不为 micro-benchmark 做无负载画像的优化（`docs/perf-l01-optimization-2026-10-06.md §0.2`：
  测量能力不足时"测不出"不等于"没有"）。

## 3. 模块划分、数据表示与不变量

### 3.1 Workspace 布局（文件级）

建议 workspace + 每模块一个 crate（或至少一组 `mod`；crate 边界是编译器强制的不变量边界）：

| crate | 生产 LOC 预算 | 数据表示/职责 | 关键 API |
|---|---:|---|---|
| `syntax` | 0.8k | `Span<T>`、`Ix`/`Lvl`、`Raw`、`Tm`、`PatternDetail` | 纯数据 + quote/pretty 的输入类型 |
| `parser` | 4–5k | 恢复式 lex/parse、`preprocess`（**保字节长**）、`macro_rules` 展开（深度 ≤256）、derive | `parse_module(text) -> (Vec<Decl>, Vec<Diagnostic>)` |
| `arena` | 0.5–1k | bump 分配 + 句柄索引 `V: u32`/`u64` 打包；**无裸指针/无 transmute** | `Arena::alloc`, `V` accessor |
| `core` | 5–6k | `Val` 14 变体、eval/quote/force、`FORCE_MEMO`（内容键） | 迭代内核 + 记忆化 |
| `unify` | 4–5k | meta 表、`unify`/`invert`/`prune`/`rename`、三档结果、预算 | `unify(...) -> UnifyOutcome` |
| `refine` | 2k | `Subst`（持久化单链）、`VSub`、`frcs`、`SpecSolve`、`subst_cxt` | `wrap`, `compose`, `subst_cxt` |
| `names` | 2k | 全限定 `Decl` 表、per-file `Scope`（import/package/可见性）、五级解析 | `resolve(scope, name) -> Resolution` |
| `pattern` | 3k | 逐臂编译 + 可达性探测（值级）+ **独立 usefulness/覆盖 pass** + 诊断 | `compile_match(...) -> (CompiledArms, Diagnostics)` |
| `classes` | 1.5k | Val 级 tabled 求解：`Assertion`/`Instance`/Generator/Consumer、outParam、coherence | `solve(goal) -> Result<Subst, Diagnostic>` |
| `elaboration` | 5k | check/infer、decl 各形态、class 两阶段、BindingName、effect 分析/replay | `elaborate_decl(...) -> (Tm, Val, Diagnostics)` |
| `prelude` | 0.5k + `.typort` | 35 个 `.typort`（core/data/hdl/show）嵌入 + 装载序（单一事实源） | `PRELUDE` 表从文件生成 |
| `hdl` | 4k | 模块树、端口/信号、Verilog emit、HDL 自检规则 | `emit(module_tree) -> String` |
| `observe` | 1k | `AnalysisSnapshot`（owned diagnostics/hover/completion/inlay/symbols） | `Sink` trait，push 期渲染 |
| `lsp` | 3–4k | Rope 文档、会话、worker、跨文件重建、请求分派 | `analyze(uri, text) -> Snapshot` |
| `cli` | 0.5k | check/emit/tutorial/quick/stats | — |
| `refcore`（R，dev-only） | 新：L07 语义基底生长（§5.4/§5.6） | 可读/可证明的语义参考核心；仅测试 oracle；无 LSP/HDL/观察面 | `run_refcore(src)` |
| `oracle-frozen`（O，过渡） | 现 `src/L13_namespace` 参考版冻结 | 语料回归参照；R 达 T2 后删除/归档 | 同 `run()` / 冻结 API |
| `zoo`（dev-only，可选） | 冻结 | L01–L12 教学快照，不进产品构建（或移出 workspace） | — |

预算合计：生产 core ≈18k 行（D3 §8 目标）、共享前端/诊断/HDL ≈ 8k、LSP/observe ≈ 5.5k，
合计 ≈32k 行**单份**；R 参考核心 ≤14k（测试期）；O 冻结 22.8k（过渡，之后删/归档）。
测试 ≤25k 行，主要放 `tests/` 与 crate 外。对比现状：L13 单层两引擎（参考 9.3k 生产 + 孪生
16.4k）+ LSP/parser 等；全仓 ≈24.6 万行中，约 10 万行是可移出生产构建的层副本与归档
（D3 §3 的 C1/C2）。**预算的权威口径是 D3 §8，本表是其架构侧映射。**
### 3.2 不变量清单（实现必须钉住，回归测试/Lean 一一对应）

| # | 不变量 | 证据/现状 |
|---|---|---|
| I1 | `force` 返回的顶层不是 `VSub`（顶层不变式） | L07 设计 §4；L13 σ 移植中"VSub 透明解包"曾破坏它并导致 GADT 覆盖误报 `[文档 wip:110-113]` |
| I2 | 槽位布局 = 运行时布局；`subst_cxt` 不增删槽；`lvl` 不缩小 | L07 设计 §6；L12 `cxt.rs:320` |
| I3 | σ 对 spine/参数槽只包裹、不物化（保 invert 可逆） | L07 设计"槽位纪律"；复现案例内层臂误报 can't unify `[文档]` |
| I4 | "解前构建、解后消费"的值必须在消费点用当前 σ 包裹 | L07 设计 §6；L13 第五轮 GADT 修复（`ArmEntry` 带 `refine`）`[文档 status §4]` |
| I5 | σ 无环；occurs 检查必须沿解链传递（组合语义） | Lean T1 `Rank.lean` 精确刻画 + R2 反例 `[文档 lean plan §7]` |
| I6 | `Absurd` 仅当两侧规范头冲突；`Undecided`/`Fuel` 永不当 `Absurd` 消费 | Lean T2/T3；L07 修复轮 R1 `[文档 FINAL §0.1]` |
| I7 | 预算计数是路径/次数的单调函数；超限档位不伪装成 `Absurd` | Lean T4；R3 两引擎预算不同构 `[文档]` |
| I8 | decl 表键全限定；裸名解析唯一经过 `Scope`（无全局别名累积） | L13 `import_map` 挂 `Infer` 的替代（§4.4） |
| I9 | 分析产物是不可变快照；观察表 owned、push 期渲染；prelude 装载不收集 | lsp-twin-wiring §0；L13 `lsp_collect` 实测 21.1→9.3s `[文档 status §4]` |
| I10 | arena 值只经句柄访问，跨轮/跨会话无悬挂；会话边界显式 `reset` | L13 twin 的 `transmute<'a,'static>`/`*mut Machine` 是已发生 UAF/UB 源 `[文档 l13-parallel-test-uaf §4/§8]` |
| I11 | 每个 decl 的 effect 行在注册期静态确定：纯 decl 可记忆化，stateful decl 只可重放 | 现状 `def_needs_replay` 启发式导致 twin def-journal 崩溃 `[文档 review-2026-09-29 §四 HDL-0]` |
| I12 | 诊断 span 指向**原始源码**坐标（预处理保字节长） | L07 R6/R7；L13 仍是预处理坐标 `[文档 FINAL §0.1]` |
| I13 | 用户输入不产生 panic：只产生 `Diagnostic`（含预算耗尽、IO 失败、深层值） | 现状 `file_*` panic、`Too much effort :(`、`lvl2ix` 下溢 `[文档 l13-typeclass…md；README §6]` |
| I14 | 用户可见判定（Ok/Err 分类）只由生产引擎产生；oracle 只测试 | 现状 `twin_can_own`/trust gate 双跑+回落 `[文档 l13-perf-replace §1.3]` |
| I15 | 语义改变必须同时改 Lean 规格或 `spec/` 锚点（规格-实现漂移探针） | lean plan §6.1 |

## 4. 逐轴算法选型（证据 → 选择 → 代价）

> 每轴格式：候选 → 证据 → **选择** → 代价/边界。数字均为 `[历史实测]`，采数日期见引文。

### 4.1 值表示 / 求值器

- 候选：① `Box/Rc` 树 + 递归（参考版，L02–L13 ref）；② bump arena + 打包字 + 迭代内核 +
  记忆化 + 稳态复用（孪生，L05 起逐步定型）；③ 其他（`bump_tree`、`cek`、编译变体等 L01 的
  22 个变体）。
- 证据：L01 受控矩阵 `bump_spine_iter_ss` 最快（church 4000：0.069ms vs 树 0.194 / cek 0.237），
  深 n=64000 时 `_ss` 0.966 vs cek 30.76；共享形状记忆化 **337×–2095×**
  （`docs/perf-l01-optimization-2026-10-06.md §2`）。L13 真实负载上孪生 `prelude-hdl`
  1331.9ms vs 参考 3073.1ms（2.3×）、`strchain` 8.7 vs 4537（519×），大值负载 23–867×
  （`FACTS.md §5`）。
- **选择**：②。生产引擎 = arena + 打包值 + 迭代 eval/quote/unify + 记忆化；树形递归只保留为
  `oracle`（§5）。
- **代价/边界**：当前孪生的 `unsafe` 面（`transmute`、`*mut Machine`）是 UAF/UB 源
  （`docs/l13-parallel-test-uaf-2026-09.md §4/§8`）——**新架构改为句柄索引 + 无裸指针**
  （`[推断]`：索引版性能需 EXP-1 复核，可能损失 3–10%；若损失 >10% 再评估
  `&'a` 生命周期安全封装）。L01 的教训：表示优化在"一次性/稳态"两种口径下结论不同，
  产品按 LSP 稳态口径验收。

### 4.2 精化载体（本仓最重要的一条轴）

- 候选：① `update_cxt` 改写 env 槽 + 全量 `refresh`（L09–L13 旧路，L13 现状）；② σ 显式替换
  （`Subst` 持久化单链 + `Val::VSub` + `frcs` + `SpecSolve`；L07 定稿，L08–L12 已迁移）；
  ③ 事实表 `pm_defs`（更旧）。
- 证据：σ 让"解"成为合一器返回值，可解性不再经 `Infer` 全局可变通道，回滚 = Rc 指针赋值，
  且与 dpm-nbe/cctt 理论同名同构（`docs/l07-dpm-refactor-design.md §1/§10`）；L08–L12 六层
  `逐字节 diff = 0`、全量测试绿（`docs/explicit-subst-refactor-status.md §1–§3`）；
  旧 `update_cxt` 被定级为"已淘汰架构"（L07 §6 所述）。**反证**：L13 σ 移植五轮失败——
  纯 elaboration ~28×、12,287 层 meta 解链、FRCS_MEMO 13GB、4 个既有 parity 失败
  （`docs/wip/README.md`；`docs/explicit-subst-refactor-status.md §4`），但 GADT 覆盖回归
  已修、失败主因是**指针键 memo 失效 + 观察面渲染 + 规模**，不是 σ 语义本身。
- **选择**：②（σ），但作为**架构决策而非移植决策**：新架构里 σ 是一等公民，禁止把热路径
  memo 键绑在值指针身份上（改为内容寻址/canonical 键）、观察面 push 期渲染 owned（§4.8）、
  prelude 装载关闭观察面（§4.8）、solve 侧加 meta 解链环检测（§4.9）。若 Phase 4 实验仍无法
  把 prelude-core 压回 ≤1.5× 基线，则**保留 ① 并关门**（负结果写档，见 §8 Phase 4 门禁）。
- **代价**：σ 的槽位纪律（I1/I3/I4）是新增认知负担；深链/内存需专门预算（L13 证据）。
  不选 ① 的理由：全局可变通道 + O(n) 读点查找 + 无法组合（设计文档 §1），长期无法支撑
  "简洁优雅"目标；不选 ③：同 ① 且更旧。

### 4.3 模式编译 + 诊断

- 候选：① 决策树矩阵（L09–L13 旧路）；② 逐臂下钻（L07/L08 现行，09-18 全仓统一）；③ 逐臂编译
  + 独立 usefulness/覆盖分析 pass（本提案）。
- 证据：受控实验（同源，`docs/pmab-per-arm-vs-decision-tree.md §2`）：臂数 5→65，
  L09 决策树 vs L07 逐臂从 **10.4× 拉到 2363×**；通配列数 2→8 从 **9× 拉到 14822×**
  （m=10 超 900s 未返回）；而"完整交叉积无通配"对照组只有 6–17× ⇒ 爆炸来自**通配臂复制**，
  是算法级问题。运行期两版都是 `pats` 线性首匹配（树在调用点被丢弃），**决策树没有任何
  运行期收益**。逐臂的代价是诊断弱化：路径感知 `Unmatched`/`Unreachable` 由决策树遍历记账
  给出（`docs/l09l13-match-compiler-analysis-2026-09-17.md §2`）。
- **选择**：③。逐臂负责"编译/检查/特化方程"；**独立 `coverage` 模块**实现 Maranget 式
  usefulness（矩阵特化 + 通配处理 + memo），按需运行（LSP 诊断/错误路径），输出
  路径感知缺失模式与不可达臂；逐臂主路径不做覆盖扫描。`[推断]` usefulness 的复杂度对
  典型臂数（≤32）可接受，需 EXP-2 判据：`pmab` 三扫描全部 ≤ 当前逐臂 2×，且诊断语料
  parity ≥ 当前 L13（路径填充模式 + 不可达臂）。
- **代价**：诊断算法新增 ~800–1200 行；需重建诊断 golden 语料（当前 L09–L13 的警告文案
  是行为面）。**不做**：决策树作为运行期结构（无收益）；也不接受"只做顶层覆盖"（L07 现状，
  会丢嵌套/组合诊断——L13 Bool×Bool 组合缺口即此，README §6.1）。

### 4.4 名字世界

- 候选：① `Tm::Var(Ix(global_idx + 1919810))` 大下标哨兵 + `Infer.global: HashMap<Lvl,VTy>`
  （L09/L10）；② 名字键 decl 表 + `Val::Decl`（L06–L08、L11–L13）；③ 全限定键 decl 表 +
  per-file `Scope`（本提案，L13 已接近）。
- 证据：哨兵方案把"全局"编码进 de Bruijn 下标，shift/rename 需特判，`Infer.global` 是第二套
  名字表（`FACTS.md §8`）；L13 的 `import_map` 挂在 `Infer` 上、per-file 克隆（`mod.rs:1463`），
  跨文件数据面因此难以复用（`l13-perf-replace §1.4 A3`）。全限定键 + 五级解析已在 L13 真实
  语料验证（README §1.1）。
- **选择**：③。`Decl = FxHashMap<QualifiedName, DeclEntry>`；`Scope`（imports/package/可见
  namespace）是**每文件**的纯数据，挂 `AnalysisSession` 而非 `Infer`；构造子只在 decl 表用
  限定键，不设裸名别名；五级解析保持 L13 顺序（局部 binder → 精确键 → import 别名 →
  namespace 前缀 → 后缀唯一回退），全部经 `names::resolve` 纯函数（可单测、LSP 复用）。
- **代价**：名字解析从"顺手内联"变为显式 API；需要 `Scope` 快照/克隆成本控制（`Rc`）。
  不选 ①：与 de Bruijn 布局耦合，是 L09/L10 时代缺口。

### 4.5 Trait 求解

- 候选：① `Typ` 桥接求解（L10/L11？）；② Val 级 tabled resolution + canonical 搜索
  （L12/L13）；③ 编译期字典化（Rust 风格单态化）——本仓未实现。
- 证据：L12 把求解改到 Val 级 + canonical（`src/L12_canonical/README.md:1-19`）；L13 的
  `typeclass.rs` 是 Val 级 `Assertion`/`Instance`/`Generator/Consumer` 搜索树
  （`[码] typeclass.rs:10-45`），并在真实 prelude 上工作（29/30 examples 由 twin 接管）。
  known bug：实例 Nat 参数冻结/宽度静默退化（`docs/l13-typeclass-instance-nat-param-bug.md`），
  根因是 `MetaEntry::Solved(Rc<Val>)` 不支持"消费点参数化"。
- **选择**：②（Val 级 tabled），但**修接口**：约束 meta 的解允许**延迟形态**（Tm/延迟求值），
  使实例参数在消费点按 spine 实例化；outParam 保持；预算耗尽返回 `Diagnostic` 而非
  `panic!("Too much effort")`；coherence/孤儿规则显式检查（当前弱）。canonical/`iddfs`
  仅在 EXP-1/D1 证明有收益时保留（L12 `canonical.rs` 147 行只在 Err 重试路径，`FACTS §4`）。
- **代价**：延迟解是架构级改动（影响 quote/eval/meta 全链路，L13 bug 文档"剩余根治"同款），
  风险高，列入 Phase 5/未决问题；短期先做"实例引用 unify 后重新 eval"（A 复现已修，`[文档]`）。

### 4.6 宏

- 候选：① 解析级 `macro_rules` 展开 + prelude 导出宏累积（L11/L13 现状）；② 卫生宏；
  ③ 无宏。
- 证据：L11 引入、L13 沿用；`MAX_MACRO_EXPANSION_DEPTH = 256` 守卫已有
  （`parser/mod.rs`；`docs/review-2026-09-29.md §四` 勘误）；宏展开概率与 span 保真有已知坑
  （macro hover/goto 文档）。
- **选择**：①，但收敛为**独立 parser 子模块**：展开发生在 parse 后、注册前；展开必须
  (a) 保 span 映射；(b) 有深度/规模双预算；(c) 导出宏表挂在 per-file `Scope`（不是全局可变）。
  **v1 不做卫生宏**（与现有语言兼容；`[推断]` 卫生性可作为 v2 语言特性另立项）。
- **代价**：宏错误诊断仍弱；把"宏展开后源"作为独立 IR（`ExpandedDecl`）而不是字符串拼接。

### 4.7 prim / effect / 原生 Nat

- 候选：① `Tm::Prim`/`Val::Prim` 独立节点（L06–L12）；② prim 挂 decl 表（L13）；
  ③ ② + 显式 effect 行 + 分层执行器（本提案）。
- 证据：L13 取消 Prim 节点后 decl 表七元组含 `Option<PrimFunc>`（`cxt.rs:432`），
  单一名字世界；但副作用靠 `def_needs_replay` 名字 memo + 环敏感扫描**启发式**判定
  （`mod.rs:3119`），已导致 twin def-journal 崩溃（`review-2026-09-29 §四 HDL-0`：新增被调用
  def 即崩，根因按 index 对账）。文件 IO 五连 panic 且无锁（README §6.6）。
- **选择**：③。`DeclEntry` 增加 `effect: Effect`（`Pure` / `Stateful(Global|CheckIssues|IO)`），
  在 decl 注册期由 AST **静态分析**得出（不靠名字 memo）；`Pure` 可记忆化/可缓存，
  `Stateful` 显式重放且只能在会话级执行器里跑；IO prim 返回 `Result` 并进入诊断，不再 panic；
  可变全局状态挂 `AnalysisSession`（每次分析显式创建），不挂 `Infer`。
- **选择（Nat）**：保留 L13 原生 Nat：`Val::Nat(u64)` + 字面量直构 + eval 装配点折叠 +
  `quote_nat` 展开回 SumCase 链 + `nat_add…rem` prim 保留惰性一步可归约
  （`mod.rs:280/905/3798`；`docs/nat-primops-plan.md §3` 计算规则表）。理由：真实 HDL 负载
  大量位宽算术，一元链是数量级浪费；下游 pretty/nf/unify 逐字节保持的移植纪律已证明可行。
  **护栏**：大整数字面量 O(k) 展开需上限；`quote_nat` 的 u64→链有内存护栏（twin 已有）。
- **代价**：effect 分析要覆盖 class 两阶段/宏展开后的形态（`[推断]` 1–2 周）；HDL 的
  "语句累积"要明确定义为 effect（`CheckIssues`/模块树写入），否则 replay 语义仍脆。

### 4.8 LSP 观察面

- 候选：① 三张表存 live `Val` + 查询期 quote（旧参考版）；② push 期 quote→owned 串
  （L13 接线后的契约，阶段 0 定稿）；③ 事后从 typed AST 重建（离线重算）。
- 证据：阶段 0/1 论证——bump arena 给不了持久 `Val`，owned 是唯一跨引擎安全的观察面；
  `hover/completion/inlay` 共 27 个 push 点；prelude 期渲染是纯死工作（21.1s→9.3s 实测，
  `docs/wip/README.md §一`；参考版**尚未落地**总闸）。L13 现状：观察面 push 写进
  `elaboration.rs`（`[码]` 27 处量级），耦合已产生可测成本。
- **选择**：② + 结构改造：观察面是独立 `observe` crate 的 `Sink` trait（`push_hover`、
  `push_inlay`、`push_completion`…），elaboration 只调 sink；**prelude 装载 sink 为空实现**
  （零成本，不是运行期 `if observe`）；每次分析产出**不可变 `AnalysisSnapshot`**（含
  diagnostics/hover/completion/inlay/symbols/def-map），LSP 消费快照、不碰引擎内部。
- **代价**：push 期 quote 成本；用"按 decl 惰性补表"兜底（wiring §0）。
- **迁移注意**：A. `ObserveSnapshot` 需带 `path_id` 分文件过滤（跨文件会话前置）；
  B. 字段投影 `def_span` 降级问题（twin 表示不带 binder span）要在新表示里直接修掉
  （`l13-perf-replace §1.4`），不要留到观察面层打补丁。

### 4.9 错误 / 预算 / 防护

- 现状缺陷类：R1 空类型零臂被拒（三档分类不完备）、R2 occurs 不传递、R3 预算代理不同构、
  P15 struct_eq 漏 pending、R6/R7 span 坐标错、R9 `UnifyKind` 不随快照回滚
  （`docs/archive/review-l07-hardening-2026-11-08/FINAL.md §0`）；L13 仍是旧口径
  （`occurrences_transitive`/`MATCH_CMP_BUDGET`/`UnifyKind` 0 命中 `[码]`，见 `docs/compare-l07-l13/L13.md §9.2`）。
- **选择**：单一 `Diagnostic { code, severity, span(原始坐标), message, related }`；
  统一失败分类 `enum UnifyOutcome { Solved, Absurd, Undecided, Fuel }`（Lean T2–T4 对应）；
  预算用同一 step 计数口径（`MATCH_CMP_BUDGET = 64` 总次数、每入口 reset、快路径先试——
  L07 修复轮定稿，`FINAL §0.1 R3`）；所有用户输入路径 `Result<_, Diagnostic>`，
  **无 panic 作为控制流**；深值/深链：quote/pretty 迭代化 + 深度上限（L07 P11 口径），
  force 的跨 meta 环守卫（P5）与 fuel 下限（fuel=0 不入 memo）为硬性要求。
- **代价**：诊断类型统一要改所有层签名（一次性机械改动）；预算口径统一需要跨引擎一致性测试
  （若 §5 单引擎，则此问题自然消失）。

## 5. 单引擎 vs 双引擎：裁决（吸收 D1/D3，答 Lead 追问）

### 5.1 三方输入

| 来源 | 结论 | 关键理由 |
|---|---|---|
| **D1 §8.6** | **不要统一成一个引擎**；最优 = 可读可证明的参考语义核心（带完整诊断）+ 性能后端；共享 parser/pretty/printer 契约 + 强 parity（L08 式 Err 正文逐字节、`?N` 不归一化探针） | 两套值表示的差异是本质的（D1 §8.2：`trait Engine` 单代码双后端不可行）；强 parity 是防"参考版修了孪生没修"的唯一闸 |
| **D3 §5/§10** | 方案 B：单引擎（twin 血统）+ 冻结 oracle crate（test-only）；生产 core ≤18k 行；现状 26 套实现不可持续 | 生产 LOC 85k→18k；每机制改动点 2→1；差分证据保留在 CI oracle feature |
| **l13-perf-replace §5** | α 生产路径取代；β 参考引擎降级 `cfg(test)`；γ **永不退休 oracle**；R0 判据先行、R1–R6 分阶段 | 29/30 examples 已由 twin 服务；唯一回落 18-utils；wasm 内存/信任闸是剩余阻塞 |

### 5.2 裁决：三者是**同一方案的两个时间阶段**，精确定义为"1 规格 + 1 生产 + 1 参考核心 + 1 过渡 oracle"

不是"两个生产引擎"（现状 A），也不是"合并成一个代码库/一个后端"（D1 明确反对），而是**四角色**：

| 角色 | 代码 | 进 release 二进制 | 进 `cargo test` | 权威性 | 生命周期 |
|---|---|---|---|---|---|
| **S 规格** | Lean 模块（M1 38 定理 + M3 oracle）+ `spec/` 锚点（判定三档、预算步数、occurs 语义） | 否 | CI `lake build` + `LEAN_ORACLE=1` | **最高**：P/R 分歧终审 | 永久 |
| **P 生产后端** | arena 引擎（twin 血统重写为**安全句柄**版）；含 LSP/HDL/观察面 | **是（唯一）** | 是（产品语义测试） | 用户可见行为以它为准 | 永久 |
| **R 参考核心** | 新 `refcore` crate：L07 语义基底生长到完整语言面；树形递归、可读、可证明；**无**性能机器/LSP/HDL/观察面 | **否** | **是**（差分 oracle） | 与 P 分歧 ⇒ **bug 报告**，由 S/人工 triage 裁决；R 是规范的**可执行近似**，不自动等于正确 | 永久（oracle） |
| **O 过渡冻结 oracle** | 现 L13 参考版**冻结不改**（22.8k 行，含 update_cxt 与观察面） | 否 | 是（P0–P5 差分） | 语料回归参照（"今天的行为"） | 临时：R 达 T2 后删除/归档 |

- **D1 与 l13-perf-replace 不冲突**：D1 的"不要统一"约束 **P≠R 的实现不合并**（不许为了省代码把
  参考核心砍掉或把两个后端塞进一个 trait）；l13-perf-replace 的"产品只留 twin"约束 **生产入口唯一**
  （release 只含 P）。合并后终态 = P 唯一生产 + R 唯一测试期语义参考 + O 过渡 + S 机检。
- **强 parity 采纳**（修正 v1 草案的"parity 降级"）：P/R 共享诊断渲染器、meta 命名与 `Span` 类型，
  使 Err 正文逐字节可达；门禁分两级——**T1**（每次 CI：判定 + Ok 输出逐字节 + 诊断
  code/span/severity）、**T2**（oracle job：全语料 Err 正文逐字节，`?N` 不归一化）。豁免清单显式
  登记（计时/内存/引擎内部序号；跨文件 fallback 类诊断），**禁止**出现"参考版改了孪生没改"而不登记。
- **O→R 交接判据**：T2 在全部行为语料（examples 32 + prelude 35 + tests 语料 + 生成式语料）零差异，
  且 R 通过 D2 **G2** 四路对拍；之后 O 删除（或归档为 golden 输入）。

### 5.3 为什么不选 A（双生产引擎）与 C（无 oracle）

| 选项 | 判定 | 依据 |
|---|---|---|
| A 双引擎长期并存 | **否** | 违反简洁/可维护目标（D3 §3 C1：46% 层代码是第二实现；C2：机制文件复制 7–12 份）；D1 §7 组合冲突（双引擎↔机制统一）已记录判定分裂（R4/R5）；L13 已出现"只在孪生"的机制（池化/常驻检查点），语义面分叉 |
| C 单引擎、删参考版 | **否** | D2 §0：当下正确性证据"金字塔尖薄"，`trans`/`subst` 精化行为在形式化里恰不可判型；同错类假阴性（L13 单行 enum）只有独立 oracle 能发现；D3 §5 表格明说 C "证据需 D2 认可"，D2 未认可 |

### 5.4 参考核心 R 选哪一层的语义：**L07 的 σ + 逐臂**（L12 作特性移植参照）

| 候选 | 作为 R 的优点 | 为什么不是它 |
|---|---|---|
| **L07** | 唯一有正向设计文档（σ 载体、单一合一器 + `SpecSolve`、逐臂三纪律）；**Lean M1 形式化对象就是 L07 参考引擎的值/替换/合一核心**（lean plan §3）、M3 oracle 同源；最小（生产 4.3k 行，`FACTS §2`）；GADT 依赖 PM 的最难部分在此定型 | 缺 namespace/package、trait、宏、原生 Nat、HDL 宿主 ⇒ 需要生长（这恰好是"按规范生长"，不是兼容包袱） |
| L09 | 最小 MLTT | 大下标哨兵名字世界（D1 A13 判为教学层时代架构）、决策树时代、缺 trait/宏；作为语义核心会带入已淘汰架构 |
| L12 | σ + Val 级 trait + 宏，功能最接近 | 缺 namespace/import、原生 Nat；自带 `canonical`/`iddfs` 未接线路径（`FACTS §4`）；9.4k 生产且经决策树→逐臂改造史；**作移植参照最优，作基底会带入债务** |
| L13 参考版 | 功能最全 | `update_cxt` 血统（D2 §2A：槽位错位 bug 族）、观察面/prelude 池/LSP 污染、22.8k、L07 加固未回灌 ⇒ 只能当**过渡 oracle O**，不能当 R |

**裁决**：R = L07 语义基底 + 按规范顺序移植（见 §5.6）。理由：可读性最高、与 Lean 形式化同源、
语义纪律已被 L07–L12 六层验证（`explicit-subst-status §2`：逐字节 diff=0）；**代价**：R 需生长
约 6–9k 行（R-core 目标 10–14k），且 R 的 trait/Nat 语义按**规范**而非兼容 O——R 与 O 的差异必须
逐条 triage 登记（这张差异表就是 §5.2 的"语义契约"）。

### 5.5 共享 / 不共享（接口契约）

| 共享（唯一实现，P/R 都依赖） | 不共享（各自实现，受契约约束） |
|---|---|
| `elab-parse`：source→Raw（lex/parse/derive/宏展开/span/preprocess 保字节长） | 运行时 `Val`/`Tm` 表示（R：`Rc` 树；P：arena 句柄） |
| `elab-diag`：`Diagnostic` schema + 构造器 + **渲染器**；`Span`；pretty/printer | eval/force/quote/rename 内核 |
| prelude `.typort` 源 + 装载序（脚本生成 `PRELUDE` 表，单一事实源） | unify/invert/prune/solve 内核（R 简单版；P 优化版，契约=判定三档+预算步数） |
| 资源语义 `spec/resources.md`（三档判定、MATCH_CMP_BUDGET=64 总次数、occurs 传递、fuel 下限） | 精化载体实现（两者都 σ；槽位纪律 I1–I4 是契约） |
| golden 语料 + 差分 harness + CLI 表面 + LSP 消费者契约 | decl 存储与缓存（R：简单 `HashMap`；P：COW/平铺 + memo） |
| `elab-hdl`：模块树 + Verilog emit + HDL 自检规则（纯函数；R 不参与，由 golden Verilog 守护） | 观察面实现（仅 P）；LSP 会话/池化/常驻检查点（仅 P）；effect 运行时（R 用确定性最简模型） |

**module tree**（在 D3 §7 上拆出 R/O）：

```text
crates/
  elab-parse/     # 共享：lex/ast/parser/derive/macro + span + preprocess
  elab-diag/      # 共享：Diagnostic/schema/renderer/pretty
  elab-core/      # P：arena(唯一 unsafe≤40) + eval/unify/match/subst/cxt/features（≤18k，D3 §8）
  elab-hdl/       # 共享纯函数：ModuleTree + Verilog emit + 自检
  elab-observe/   # P only：owned 观察面 sink（≤1.5k）
  elab-lsp/       # P only：server/会话/Rope/跨文件重建（≤4k）
  refcore/        # R：L07 语义基底 + 生长；0 unsafe、无 LSP/HDL/观察面/perf（≤14k）
  oracle-frozen/  # O：现 L13 参考版冻结（过渡期；R 达标后删/归档）
  cli/            # typort（产品入口）+ l14bench（统一负载，D3 §7）
tests/
  golden/L02..L13/*.golden   # 层 = 快照，不是源码副本（D3 P5）
  oracle_diff/*.rs           # P↔R↔O 参数化差分（T1 每次 / T2 oracle job）
  lean_oracle_parity.rs
lean/                        # S：M1/M3 现行 + 扩展（M2 另立项）
```

release feature 装配 = `elab-core + elab-parse + elab-diag + elab-hdl + elab-observe + elab-lsp + cli`；
test 装配 = 上述 + `refcore` + `oracle-frozen`。**release 二进制不得含 oracle 符号**（CI 符号检查）。

### 5.6 R 的生长清单与验收（每项：语义来源 → 对拍门禁）

| # | 能力 | 语义来源（移植参照） | 维护门禁 |
|---|---|---|---|
| 1 | σ + 逐臂 + 单一 unify + 三档（种子） | L07（`docs/l07-dpm-refactor-design.md`） | `refcore` 自身单测 + M3 oracle |
| 2 | namespace/package/import + 全限定键 + 五级解析 | L13（README §1.1；D1 A13 判"生产必需"） | R↔P T1/T2 |
| 3 | Val 级 tabled trait + outParam + 实例注册 | L12（README §2.5/§5）+ L13 全限定形态 | R↔P + 实例顺序置换语料（D2 G4） |
| 4 | 宏展开（解析期，深度 256） | L11/L13（parser 共享后 R 无需实现） | 共享 crate 单测 |
| 5 | 原生 Nat + nat prim 规则表 | L13（README §1.4；`nat-primops-plan.md §3`） | **G2b unary 影子对拍**（同一语料 `Nat(k)` vs `succ^k zero`） |
| 6 | prim/effect（decl 表 + effect 行 + replay 语义） | L13 形态 + 本提案 §4.7 修正 | IO/global 语料（确定性模型） |
| 7 | 诊断（路径感知覆盖/不可达） | 独立 usefulness pass（§4.3） | 诊断 golden 语料（P/R 均过） |
## 6. 正确性护栏

| 层 | 手段 | 现状/落地 |
|---|---|---|
| 规范/判定 | Lean M1：`Val`/`Subst`/`Occurs`/`Rank`/`Budget`/`Classify`/`StructEq` 38 定理（1009 行，零 sorry） | 已有（`lean/`；`lean-compiler-formalization-plan.md §7`）`[文档]` |
| 第三 oracle | Lean 可执行 `engine-oracle` + Rust `tests/lean_oracle_parity.rs`（`LEAN_ORACLE=1`，curated 4/4） | 已有，未进 CI 强制 |
| 差分 | 生产引擎 vs 冻结参考 oracle：全语料（examples 32 + tests 语料 + prelude 35 文件）逐文件判定/输出/诊断字段；生成式语料用 `src/pmab_gen.rs` 已有生成器扩展 | 部分已有（`l13_fast_parity`/twin_engine_tests），口径要重定 |
| 不变量 | §3.2 的 I1–I15：每条至少 1 个回归钉；关键项（I2/I3/I5/I6/I7/I9/I10）进 debug_assert/运行时校验 | 需新建 |
| 属性测试 | `proptest`/`quickcheck`：subst 组合/occurs/quote∘eval 恒等/rename 往返/pretty∘parse 稳定性 | 需新建 |
| 模糊测试 | parser/preprocess/macro 展开/elaboration 入口（无 panic 断言 + 内存上限） | 需新建（`cargo-fuzz`，CI nightly 可选） |
| 内存/UB | 安全核心零 `unsafe`；arena 模块 `Miri`/`ThreadSanitizer` 定期（UAF 事故：`l13-parallel-test-uaf`） | 需新建 |
| 性能回归 | 同机同窗口成对 A/B（`tools/perf-l01` 的"同批空对照 + 中位数 + keep-alive"三件套），CI 只跑烟测（绝对阈值放宽） | 部分已有 |
| 快照/soak | LSP 请求级 golden（hover/completion/inlay/diagnostics）；release 前真实编辑序列 soak | 需新建 |
| CI | `gate_l13.sh`（lib+parity+twin_lsp+hdl042）+ `cargo check --examples --tests` + 全量 `cargo test` + `lake build` + oracle 差分 + 差分语料报告 | 现状 `.github/workflows/ci.yml` 已有前两项与全量；Lean/oracle 未强制 |

**护栏原则**：① 每个已知 bug 类（R1/R2/R3/P15/R6/R7/R9）必须有"规范定理或属性测试 + 回归钉"
双覆盖；② "两侧同错"类（L13 单行 enum 假阴性）只能靠独立 oracle/生成式语料发现
（`lean plan §2.2`）；③ 任何 parity/诊断口径变更必须同时改 golden 与文档锚点。

## 7. 复杂度预算与"不做什么"

### 7.1 预算（沿用 D3 §8，本提案追加 R/O 两项）

| # | 预算项 | 现状 | v1 目标 | 检验（静态/脚本） |
|---|---|---:|---:|---|
| 1 | 生产引擎 core LOC | 85,411（现 twin；另有参考 82,946） | **≤18,000** | `cloc`/nonblank `crates/elab-core/src` |
| 2 | 单文件非空行 | 7,872（L13 `mod.rs`） | **≤1,200** | 逐文件 max |
| 3 | 生产文件数 | 284 层文件 + 32 glue | **≤80** | `find` 计数 |
| 4 | `Val` / `Tm` 变体 | 14 / 25 | **≤16 / ≤26** | grep 去重 |
| 5 | 工作栈任务种类（twin） | 6–8 | **≤8** | `UItem::` 去重 |
| 6 | `unsafe` | 317 | **≤60**（arena ≤40 + lsp_stdio ≤20，其余 0） | grep |
| 7 | 环境/调试开关 | 33 distinct | **≤4**（LOG / STACK_MB / bench 消融） | grep `[A-Z]+_[A-Z_]+` |
| 8 | 生产路径 print / panic | 663 / ≈2,200 | **≤20 / ≤20**（全部诊断化） | grep |
| 9 | 跨层复制 | 机制族 33k + Jaccard 80%+ | **0**（同机制唯一文件） | 同名文件行集 Jaccard ≤40% |
| 10 | `.bak`/归档入 src | 12,464 + 25,334 | **0** | `find src -name '*.bak' -o -name 'bench_*'` |
| 11 | 构建目标 | 19 bin + 20 `test=false` + 118 `#[path]` | **≤6 bin、0 test=false、0 `#[path]`** | Cargo.toml / grep |
| 12 | 文档 | 51,873 行 / 234 文件 | **≤8,000 行 / ≤30 文件**；代码内禁日期数字 | `wc` |
| 13 | 测试 | 2,477 fn / 17 ignore | 保留黑盒 + golden；ignore ≤5 且 `#[cfg]` 门控 | grep |
| 14 | 口径 | FACTS 低估 1.5–2.6×（D3 §1） | 1 个 `tools/metrics` 生成所有数字 | 复现 diff=0 |
| 15 | **R 参考核心 LOC**（新增） | — | **≤14,000**，0 unsafe | `cloc crates/refcore/src` |
| 16 | **O 过渡 oracle**（新增） | 22,817（L13 参考侧） | 冻结 ≤23k，**不改语义**，带 `# DO NOT EDIT` 头 | git diff 空 |
| 17 | **P↔R 差分时长**（新增） | parity 套件逐层 ~44% 重复 | T1 ≤3min、T2 ≤10min | CI 计时 |
| 18 | **共享 crate 数**（新增） | parser 每层一份（L13 6.6k） | **3**：`elab-parse` / `elab-diag` / `elab-hdl` | 依赖图 |
### 7.2 "不做什么"（负结果清单）

1. **不在产品仓维护 7 层 × 2 引擎**。层是教学/实验产物，归档为 `zoo`（可构建但不进产品）。
2. **不做运行期双引擎/回落**（trust gate、`TYPORT_LSP_ENGINE`、`twin_fallback` 终态删除）。
3. **不做决策树运行期结构**（无运行期收益，编译期最坏 14822×，`pmab` 实验）。
4. **不用 de Bruijn 大下标哨兵表示全局**（L09/L10 缺口）。
5. **不把 `Infer` 当全局可变状态袋**（`pm_defs`/`pm_solvable`/`import_map`/`global` 一类）。
6. **不保留"两份错误文案逐字节 parity"** 作为硬门禁（成本高、收益低；改为判定+字段）。
7. **不用 panic 作为用户错误路径**（`file_*`、`Too much effort`、`lvl2ix`、`unwrap` 族）。
8. **不在没有负载画像时做 micro-opt**（L01 报告 §0.2：测量能力不足；先建测量）。
9. **不做 `canonical`/`iddfs` 重试路径**除非实验证明收益（当前只在 Err 路径、run/run_fast 不经，
   `FACTS §4`）。
10. **不做 wasm 上大常驻 twin**，除非内存预算达标（1.2GB vs 2GiB 顶 + 静默 trap，
    `l13-perf-replace §1.2/§5.1`）。
11. **不做全编译器形式化/全核心 Aeneas**（M4/M5 成本收益不成立）。
12. **不为"层间差异"保留特性门控**（功能开关只允许"实验性语言特性"一类，且默认关、
    有删除日期）。

## 8. 分阶段迁移路线（两条轨道 + 关键路径）

> 原则：**行为不变优先**（先搬后改）、可回滚、门禁机器可判定；**先测量后改语义**。
> P 轨 = 生产路径收敛（对应 l13-perf-replace R0–R6，重排为 P0–P6）；R 轨 = 参考核心生长
> （S0–S4）。两轨可并行：R 不阻塞 P0–P3；P4（σ 定稿）依赖 R 轨的 G2c 对拍；O 是两轨之间的
> 过渡桥（R 达标前承担差分 oracle）。估时为量级（1 人周 ≈ 5 人日），不是承诺。

| 阶段 | 轨道 | 内容 | 门禁（全绿才进下一阶段） | 回滚 | 收益 | 估时 |
|---|---|---|---|---|---|---|
| **P0 判据先行** | P | 引擎对拍报告（归属/回落类别/诊断字段/kick 墙钟/RSS）；冻结 golden 语料；CI 加 `lake build` + oracle 差分 + 全量测试 | 报告复现已知结论（29/30 拥有、18-utils 唯一回落、examples 1.78×）；golden 可重放 | 无写入 | 后续一切前提（R0 原则） | 1–2 周 |
| **S0 冻结 O + 共享契约** | R | 把现 L13 参考版冻结为 `oracle-frozen`（只读）；抽 `elab-parse`/`elab-diag` 共享 crate；写 `spec/` 契约（三档/预算/occurs/槽位纪律） | O 与改造前行为逐字节一致（冻结即基线）；共享 crate 被 P/O 两端使用且测试绿 | 逐 crate revert | 差分基础设施 + 契约单一来源 | 1–2 周 |
| **P1 crate 抽取（行为不变）** | P | workspace 化；elab-core 从 twin 抽 `arena/eval/unify/match/subst`；测试搬出 `src/`；`bench_*`/`.bak` 清理（D3 §9.3：零风险删 37.8k） | 全量 `cargo test` 绿；examples `typort check` 逐字节不变；构建时间 ≤ 现状 1.2× | 机械 revert | 边界显式化；立即减 37.8k 行 | 2–4 周 |
| **S1 R-core 种子** | R | `refcore` 实现 L07 语义（σ + 逐臂 + 单一 unify/spec + 三档）；复用共享 parser/diag；只支持 L07 语言面 | R 自身单测 + M3 oracle + 对 L07 语料与 O 判定一致 | 独立 crate，删除即回滚 | 可读可证明的语义核心诞生 | 2–4 周 |
| **P2 生产接管 CLI/check** | P | `typort check` 统一走 P 管线（`process_file` 口径）；删 `on_change` 参考专线；O 只进测试 | examples + tests 语料 `check` 逐字节一致；release 无 oracle 符号 | 环境变量切回参考（保留一版） | 单入口；CLI/LSP 语义统一 | 2–3 周 |
| **S2 R 生长语言面** | R | 按 §5.6 顺序移植 namespace/import → Val 级 trait → Native Nat/prim/effect；宏由共享 parser 承担；诊断 pass 后置 | 每项 T1（判定+Ok 字节+诊断字段）对 O 零差异；G2b unary 影子对拍；G4 生成式语料 | 逐特性 revert | R 覆盖产品语言面 | 4–8 周 |
| **P3 LSP 单引擎 + 跨文件** | P | 常驻 prelude 会话升级项目会话（按 `rebuild_set` 拓扑序重放依赖段）；观察面分文件；删 `twin_can_own`/trust gate；wasm 视内存达标再翻 | 全语料 0 回落（`EXPECTED_FALLBACKS` 空）；LSP 12 套 + 请求级 golden；wasm 峰值 ≤ 预算否则保持参考 | 保留 `TYPORT_LSP_ENGINE` 一个 release | 用户可见延迟/一致性；消 18-utils 双付 | 4–8 周 |
| **S3 T2 达标，O→R 交接** | R | P↔R 全语料 T2（Err 正文逐字节、`?N` 不归一化）；差异逐条 triage（登记"语义契约"）；修 R 或修 P | T2 零差异；四路对拍（G2a–d）全绿；R 无性能回退要求（不参与生产） | 保留 O 开关 | 语义参考核心取代冻结 oracle | 2–4 周 |
| **P4 精化载体定稿（σ）** | P | 在 P 内实施 §4.2 的 σ + 内容寻址 memo + 观察面 owned/关表 + meta 解链守卫；参考 L13 round-6 清单；**必须用 S1 的 R 做 G2c 对拍** | `prelude-core` ≤1.5× 当前 P 基线；GADT 覆盖语料 parity；T1 零漂移；内存 ≤1.2×；深模式 d=400 不崩 | 保留 `update_cxt` 分支一个 release | 精化机制统一（L07–L12 已证） | 4–8 周（失败即关门，见下） |
| **P5 诊断与 effect/Nat 收敛** | P | 独立 usefulness/覆盖 pass 替代弱诊断；effect 行 + replay 规则化；IO 改 `Result`；Nat prim 规则表与 unary 影子 | 诊断 golden parity；examples Verilog 逐字节；HDL 套件绿；用户输入 0 panic | 旧诊断 feature | 诊断完备性 + 副作用可判定 | 3–6 周 |
| **S4 O 退休/归档** | R | O 删除或归档为 golden；R 作为唯一测试 oracle；oracle feature 装配定型 | release 仍无 oracle；CI 只依赖 R + golden；O 归档可复现 | git tag 回滚 | 维护面收敛（少 22.8k 行） | 1 周 |
| **P6 冻结与交付** | P | `TYPORT_*` 运行期开关删除；zoo 归档（L01–L12 教学快照不进产品构建）；文档/CI 定稿；soak 一个 release | release 符号检查（无 oracle/zoo）；一个 release 真实编辑 soak 无漂移；§7 预算达标 | 前一 release tag | 目标架构成立 | 2–3 周 |

**关键路径与不可逆点**：
1. **P0+S0 必须先做**：没有可机器判定的 parity，后面每一步的"全绿"都只是自宣（l13-perf-replace §5.3-1）。
2. **S1 不能晚于 P4**：P4 的 σ 定稿需要 R 做跨载体对拍（D2 **G2c**）；若 R 未就绪，P4 延期而不是盲改。
3. **P3 的测试面改造最险**：`Backend::new` 默认翻 P 会同时动 L02–L12 黑盒与 parity 基准；建议
   "测试显式声明引擎 + 新增 P 默认下全绿独立门禁"跑满一个窗口再翻（l13-perf-replace §5.3-4）。
4. **P4 的关门条件**：若 σ 在真实 P 上仍无法 ≤1.5× 基线（R2/R3/R6 已排期）⇒ **保留 `update_cxt`
   并关门**，把负结果写入 D6/§9；不得无限重试（L13 已五轮）。
5. **P6 不可逆**：删 `TYPORT_LSP_ENGINE` 前必须完成一个 release 周期 soak；`twin_gate_distrusted`
   粘性早退管道保留（HDL 漏报类风险的重启点）。
6. **并行建议**：P1/S1 可同窗口（不同 crate）；P2 与 S2 可交叠；P3 完成后再做 P4（否则 σ 改的是
   会移动的目标）。

总估时：P 轨 ≈ 18–34 人周；R 轨 ≈ 9–17 人周（与 P 轨并行后关键路径 ≈ 20–30 人周）。
最先做、性价比最高：**P0+S0（2–4 周）** + P2/P3 中"桌面单文件 LSP 完全取代"一段（8–14 人日，
l13-perf-replace 口径）。
## 9. 风险与未决问题

### 9.1 D1 §7 组合冲突的逐条处置

| D1 冲突 | 本提案处置 | 落点 |
|---|---|---|
| 打包值/迭代内核 ↔ Stacked Borrows UB | P 的 arena 改**安全句柄索引**，禁 `transmute`/裸别名写；`unsafe` 只留 arena ≤40 行并 Miri 门禁 | §4.1、§7 #6、I10 |
| σ ↔ 生产规模 | P4 以"内容寻址 memo + 观察面关闭 + meta 解链守卫"对冲；≤1.5× 门禁；失败即关门保留 update_cxt | §4.2、§8 P4 |
| 决策树 ↔ 诊断 | 逐臂编译 + **独立 usefulness pass**（诊断按需运行），两者解耦 | §4.3 |
| 双引擎 ↔ 机制统一 | 角色拆分：P 只镜像**语义契约**（不镜像参考实现细节）；强 parity 由共享渲染器保证 | §5.2/§5.5 |
| 原生 Nat ↔ 统一定义相等 | R 用 unary 影子引擎做 G2b 对拍；`Val::Nat` 只作为 P 的加速表示，quote 后语义面同一 | §4.7、§5.6 |
| quote/conv memo ↔ bump 生命周期 | memo 按轮/会话代（epoch）失效并内容键化；跨轮复用只允许 owned 快照 | §4.1、§4.8 |
| 观察面 ↔ PreludePool 引用计数 | P 改句柄 arena 后无 `Rc` 跨线程池；观察表只存 owned 串；池化仅在无 unsafe 前提保留 | §4.8、I9 |
| 精化白名单 ↔ 层旧语义 | 单一语义核心（R）定义白名单；P 不保留各层旧边界 | §4.2、I5–I7 |
| 复合环境 ↔ decl 表世界 | P 保留"defs 平坦域 + bind 链"；namespace/import 放 `Scope` 层（不是 defs 域） | §4.4、§5.5 |

| # | 问题/风险 | 影响 | 需要的证据（D1–D6/EXP） || # | 问题/风险 | 影响 | 需要的证据（D1–D6/EXP） |
|---|---|---|---|
| Q1 | arena 改**句柄索引**后性能损失多少？ | 值表示选型的核心风险 | EXP-1/EXP-3 复测：索引版 vs 现 twin 的 match/prelude/大值 |
| Q2 | σ 在 L13 规模下能否压回 ≤1.5×？ | P4 生死门 | round-6 清单 + 新架构原型；D4/D6 |
| Q3 | 参考引擎降级后，哪些正确性证据必须补（同错类盲区）？ | 单引擎后错误发现能力 | Lean M1/M3 + 生成式语料 + golden 的覆盖统计 |
| Q4 | 诊断"升级"是否改变用户可见行为？ | 兼容性/测试面 | 诊断 golden 对比；D2 |
| Q5 | effect 分析的边界（class 两阶段/宏展开后/HDL 语句累积） | replay 语义正确性 | L13 def-journal 崩溃根因 + D6 分支考古 |
| Q6 | wasm 是否永远参考引擎（内存）？ | 产品形态 | R4 内存实验；D4 |
| Q7 | 教学层 `zoo` 是否继续可构建/进 CI？ | 仓库定位 | 用户/Lead 决策（本提案默认：不进产品构建、可选构建） |
| Q8 | 单一生产引擎 vs "一份代码两种表示"（泛型 monomorphize）是否可行？ | 可能的更简洁方案 | `[推断]` 未实测；需 EXP：后端 trait 化对性能/复杂度的净效果 |
| Q9 | 宏卫生性是否 v2 立项？ | 语言面 | D1 设计空间；用户优先级 |
| Q10 | 测量环境：开发机无 PMU、Windows 抖动 | 所有性能结论 | D4 协议（成对/空对照/中位数）；perf-experimenter 结果 |
| Q11 | 迁移期间双实现口径（P1–P3）与最终单一引擎的测试面改造顺序 | 破坏测试信心 | `l13-perf-replace §5.3 第 4 条`（不要直接翻默认） |
| Q12 | Lean M2（精化 match 形式化）是否值得投入 | 精化完备性证据 | D2；lean plan §4 |

## 10. 与 D1–D6 的接口（D1–D3、D5–D6 已读；D4 待 v2）

**已吸收**：
- **D1**（设计空间）：18 轴候选与证据强度；本提案 §4 逐轴选型均以 D1 的"证据档"为输入；
  §9.1 逐条处置 D1 §7 的 9 个组合冲突；采纳 D1 §8.6 的"参考语义核心 + 性能后端 + 强 parity"判断，
  并在 §5.2 给出四角色精确定义（这是对 D1"不要统一成一个引擎"与 l13-perf-replace"产品只留 twin"
  的合并解释）。
- **D2**（正确性）：§6 直接采纳 G1（三值判定纪律全局化）、G2（四路差分矩阵，本提案把它落为
  T1/T2 + O→R 交接判据）、G3（debug 不变量断言）、G4（生成式对抗语料）、G5（known-bug 钉子标准化）、
  G6（panic→诊断）、G7（CI 门禁清单）、G8（形式化优先级：refinement > NBE > subject reduction，
  不建议先形式化决策树/HDL）。D2 §0 的三条最大风险（原生 Nat 定义相等、trait coherence、
  层间加固不对称）分别落 §4.7、§4.5、§5.2/§6。
- **D3**（优雅/复杂度）：§7.1 预算表整表沿用 D3 §8（生产 core ≤18k、单文件 ≤1.2k、unsafe ≤60…）；
  §3.1/§5.5 的 module tree 以 D3 §7 为底稿；D3 §9.3 的零风险清理（删 37.8k 归档）列入 P1。

**D5/D6（写作中途出现，已读并吸收，细节 v2 对齐）**：
- **D5 §0 三档判决与本提案一致**：保留 bump arena/打包值/扁平 spine/迭代内核、有界记忆化、
  `Tycker` 稳态复用、push 期渲染 + `observe` 闸；**重写**记忆化基础设施（指针键/强持有 →
  内容寻址 + 分代/Weak + 预算）、prelude/resident/compact 收成一个"快照层"、decl 表
  `SmolStr` + 平铺快照、深值 Drop/quote/export/pretty 统一显式栈、fuel 从静默降级改诊断；
  **砍** Sum 臂 eval 记忆化（负结果：+5…+33% 回归）、L12 canonical/`iddfs`、L01 已否决变体、
  17 个 `.bak`。→ 本提案 §4.1/§4.2/§4.8 与之相容；其中 **C2 尾任务寄存器化（−5.7…−7.4%）**
  与 **递归快路径（非右链反超 1.14–1.42×）** 列入 P1/P4 的候选下沉项（待 D4 复测）。
- **D6 收割项**：C-1（`analysis/l04-l07-perf` 的 L04–L07 prune O(n³) 根治 + `Machine` 常驻，
  **最高价值未收割**）→ 并入 P1/P4 的输入；C-2（`perf/l13-twin-sigma` 的逐列精化 σ 设计证据）
  → P4 参考；C-3（`l13-perf-replace` 路线）→ §8 已引用；C-4（`docs/wip/` 五轮补丁：**可收割的
  是方案不是代码**）→ §4.2 的"为什么失败"已采其结论；其余 30+ 未并分支（含 11 个 backup）判定
  不收割，`.zcode/` 等未跟踪资产需先归档。→ 已补入 §11 索引。

**仍待（v2）**：**D4（实验）**：Q1 arena 句柄索引化的性能损失；Q2 σ 在"固定 prelude/LSP 关闭"
下的**干净 A/B**（D1 A12 指出的唯一缺口）；Q4 诊断升级的用户可见差异；Q6 wasm 内存；Q8
"共享核心 + 后端"的净复杂度；Q10 测量环境/协议。本提案所有"≤ 当前 X"的验收阈值须以 D4 基线复核。

## 11. 证据索引（本提案直接引用）

- 代码：`src/lib.rs:255-330`（Engine 选择）、`src/L13_namespace/{mod.rs,cxt.rs,elaboration.rs,typeclass.rs,bump_spine_iter/*}`、
  `src/L12_canonical/README.md`、`src/L07_sum_type/README.md`、`Cargo.toml`（bench bin/test 纪律）、
  `.github/workflows/ci.yml`、`tools/gate_l13.sh`。
- 实验/历史实测：`docs/bench-matrix-2026-09-20.md`、`docs/perf-l01-optimization-2026-10-06.md`、
  `docs/pmab-per-arm-vs-decision-tree.md`、`docs/perf-ab-l07l12-2026-09-16.md`、
  `docs/l13-twin-bench-2026-09.md`、`docs/l13-perf-replace-2026-09-27.md`。
- 机制/设计：`docs/l07-dpm-refactor-design.md`、`docs/explicit-subst-refactor-status.md`、
  `docs/wip/README.md`、`docs/lsp-twin-wiring-2026-09.md`、`docs/l09l13-match-compiler-analysis-2026-09-17.md`、
  `docs/nat-primops-plan.md`、`docs/review-2026-09-29.md`。
- 正确性：`docs/archive/review-l07-hardening-2026-11-08/FINAL.md`、`docs/lean-compiler-formalization-plan.md`、
  `lean/`、`docs/l13-parallel-test-uaf-2026-09.md`、`docs/l13-typeclass-instance-nat-param-bug.md`、
  `docs/pattern-match-refinement-analysis.md`（结论已被 status §4 订正）。
- 层剖面：`docs/compare-l07-l13/{L07…L13,CROSS,FACTS}.md`（本提案的现状基线）。
- 本轮输入：`docs/optimal-design/{D1-design-space,D2-correctness,D3-elegance,D5-techniques,D6-branches,FRAMEWORK}.md`（D4 待 v2 补）。
