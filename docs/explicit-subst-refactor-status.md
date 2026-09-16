# 显式替换重构进展（dpm-nbe 对齐，2026-09）

> 本文档记录本轮重构（L07–L13 精化机制统一为显式替换）的范围、进度、
> 提交与验收数字，兼作最终交付报告底稿。设计细节见
> `docs/l07-dpm-refactor-design.md`；分层计划见
> `docs/l08-l13-refactor-plan.md`。

## 0. 缘起与机制

参照 KonjacSource/dpm-nbe（Haskell：explicit substitutions + forcing；
特化合一取自 Norell / Cockx without-K）把 L07 及后续层的依赖模式匹配
精化从"事实表 / 上下文改写"改为 **显式替换**：

- `Subst`：持久化单链（链头 = 最新）。`extend` O(1) cons；`lookup_hit`
  沿链首个命中 + **条件包裹**（解值浅结构——含闭包 env 槽、Match 的
  scrutinee/captured env/pending——不引用已解层级时原样直通）。
- `Val::VSub`：值携带 σ；`force` 的 `frcs` 读点把 σ 推进值结构
  （Rigid 读点 lookup 命中烧 1 fuel、解析应用对齐 `napp`；spine/Sum/
  SumCase 槽只包裹不物化——保 invert 可逆；闭包 env 逐槽包裹；Match
  scrutinee 推进后交回 force 重选）。
- `SpecSolve{solvable, acc}` 穿参 `unify`：特化可解性不再经全局旁路；
  方程两侧在入口置于 acc 之下（dpm-nbe `subst ɑ vs` 的惰性等价物）。
- 编译器持有 σ：臂边界 Rc 回滚；分支体检查前 `subst_cxt`（槽位布局
  不变）。

**与旧机制的关系**：L07/L08 的 `pm_defs` 事实表（惰性精化）与 L09–L12
的 `unify_pm`+`update_cxt`（改写 env 槽 + 全量 refresh，L07 README §6
所述已淘汰架构）都并入同一显式替换实现。

## 1. 进度

| 阶段 | 状态 | 提交 |
|---|---|---|
| 设计文档 + dpm-nbe 分析 | ✅ | `docs/l07-dpm-refactor-design.md` |
| L07 参考版重构 | ✅ | `ad08c63` |
| L07 参考版评审轮 1（正确性/性能/风格 三路并行） | ✅ | 修复 `bbcf214` |
| L07 参考版评审轮 2（链式 σ 验证 + 92 例对抗测试） | ✅ | 修复 `a5eb72b` |
| L07 孪生版移植 | ✅ | `ea01207` |
| L08 参考版移植 | ✅ | `8931d78` |
| L08 孪生版移植 | ✅ | `efa47b9` |
| L09 参考版 + 孪生版 | ✅ | `ccfcb87` |
| L10 参考版 + 孪生版 | ✅ | `ad412ab` |
| L11 参考版 + 孪生版 | ✅ | `2129975` |
| L12 参考版 + 孪生版 | ✅ | `58073dd` |
| 第三轮对抗评审（覆盖 L08–L12） | ✅ | P1 修复 `dbe79cf` |
| L13（生产版） | ❌ 未落地（三轮尝试，根因已定位到函数级） | 见 `docs/wip/` |
| 全仓回归（66 目标 / 4013 用例） | ✅ 0 失败 | — |

## 2. 验收数字（已完成阶段）

| 层 | 层内/parity | 全 lib | 移植前后基线 diff | bench fast 列 |
|---|---|---|---|---|
| L07（参考+孪生） | 45 单测 + 63 parity + 48/51/91 黑盒 | 全绿 | — | 无回归 |
| L08（参考+孪生） | 49 单测 + 80 parity + 57/51 黑盒 | 全绿 | — | 0.81–1.17× |
| L09 | 31 parity | 705 全绿 | 72 源逐字节 = 0 | ≤1.24×（match/enum 变快） |
| L10 | 32 parity | 705 全绿 | 45 段逐字节 = 0 | 0.92–1.08× |
| L11 | 37 parity | 705 全绿 | 逐字节 = 0（REF/TWIN 亦一致） | 待补 |

**性能（L07 微基准，同会话 A/B）**：

| 负载 | 旧 pm_defs | 链式 σ（定稿） |
|---|---|---|
| deep40（深嵌套模式） | 16.9ms | 18.4ms |
| deep80 | 62.2ms | 67.5ms |

**孪生版 bench（fast 列，前后比）**：L07 多数负载持平或更快（church
1.0-1.1×、match 0.66×、enum 0.53×）；L08 最差 match +17%（绝对值
8µs），struct 0.93×、natadd 0.81×。均远低于 1.5× 回归线。

## 3. 评审发现与修复

### L07 两轮（正确性 / 性能 / 风格 + 对抗测试）

**轮 1**（正确性 / 性能 / 风格 三路并行）：

- 正确性：无 P0。两条 P1 为测试语料外的边界差异（frcs 对已解 rigid +
  非空 spine 的解析应用——比旧版更完备；quote 防御臂的降级保真度）。
- 性能：**发现真问题**——`extend` 写时整表重建 + 逐条深拷贝包裹是
  O(n³/6) 分配，深嵌套模式 2.5×@40 / 4.5×@80 回归。修复为持久化单链
  （写 O(1)、读沿链取最新），回归收敛到 ~9%。
- 风格：17 项，集中于文档过期与机制层单测缺失——全部落地。

**轮 2**（链式 σ 专项验证 + 92 例对抗黑盒测试）：

- 正确性：无 P0；四类修复经静态论证 + 9 个对抗反例验证封闭。
- 对抗测试：**发现 1 个 P1 回归**——fuel 燃烧剖面（每次 VSub 推开计
  1）使深嵌套模式安全边界从 d>2000 缩到 d≈380，耗尽被误报"分支不可
  达"。修复为燃烧点移到 lookup 命中，并加 d=400 回归测试。
- 其余 92 例全部与旧版逐字节一致。

### L08–L12 第三轮（对抗性正确性评审）

**结论：达到与 L07 同等可信度，8 项层特有适配中 7 项验证通过。**

- **P1（已修）**：L10/L11/L12 **孪生版没有燃料池**（参考版有、L09 孪生
  有）——frcs 的 lookup 命中/Match 重选无有界降级，meta 间接环等形态
  理论可无界递归（语料不触发）。已照 L09 孪生模板补齐（thread_local
  `PM_FUEL` 4096 + 入口充值 + 两处燃烧），并订正 L10/L11 注释里"参考版
  无 fuel"的错误断言。
- **P2（登记不修）**：
  - L10/L11/L12 的 `unify_pm` 无 `solvable` 白名单（任意裸 rigid 可解）
    ——忠实保留各层旧 `update_cxt` 边界，与 L07 白名单口径**有意不同**。
  - L09 可达性探测不显式播种 σ（经被包裹的 cxt 值间接生效）。
  - `force_deep`（trait 接收者/参数路径）无深度上限/visited。
  - occurs 扫描面跨层不一致（L10–L12 扫 Lam/Pi 闭包 env 槽、Decl 处理
    各异）——收窄可解集，未观察到位差。
  - L09 孪生平坦 defs 环境不做 Pi env 链式包裹（de Bruijn 可达面）——
    覆盖内无差异，登记为跨实现分歧。
- 验证通过项：occurs 对 Flex 不透明（L09–L12，有原则依据：其探测用
  `Raw::Hole` 实例化、pruning 收整组绑定器）；孪生 invert/prune 全层用
  `force_arg`；孪生影子索引（name_map/by_lvl）随 `subst_cxt` 同步与回滚；
  "未 force 就读 VSub"的读点全层补齐；SpecSolve 穿参覆盖面分层自洽
  （L09 全递归臂透传；L10–L12 特化限 `unify_pm`，与旧决策树边界逐条对应，
  求解路径不获得特化解能力）。

## 4. L13（生产层）：规模放大 + 语义回归 —— **未落地**

L13 移植代码曾完整实现（参考版 + 孪生版，8 文件；裸语言语料 65 例逐字节
diff = 0），但四轮尝试后仍未达验收，**已回退至 HEAD**。第四轮（2026-09-16）
的结论（完整数据见 `docs/wip/README.md`）：

- **prelude 期 LSP 表总闸已落地**：prelude 加载末尾本就清空 hover/
  completion/inlay 表，加载期渲染是纯死工作（hover 占 21s 中的 ~11s）；
  加 `Infer.lsp_collect` 后 `typort check` 全量 prelude **21.1s → 9.3s**
  （零行为变更；孪生版早有同款 `observe` 总闸，parity 表不分叉）。
- **12k 深 quote 真身＝meta 解链**：`?m₁ := succ(?m₂) := succ(?m₃) …` 逐层
  force 展开，深度仅受 fuel 约束 ⇒ 默认测试栈必溢出（parity 崩因）；
  触发于 `nat.typort` 的 `nat_div`。
- **纯 elaboration 仍 ~28×**（l13bench prelude-core basic：基线 22.4ms →
  移植 1242ms，去掉 LSP 表后 637ms）；quote 最外层调用 79% 来自模式编译器
  分支循环。
- **移植版有 4 个既有 parity 失败**（round-3 状态同样失败，非第四轮引入）：
  3 个 GADT 覆盖检查误报 non-exhaustive（`test_pm_vec_bool_exhaustive` /
  `test_pm_tuple_vec_gadt` / `..._no_prelude`）+ 孪生
  `resident_compaction_matches_fresh_replay_across_kicks`。
  **语义回归的优先级高于性能**。
- 第四轮的补丁（含 LSP 总闸、FRCS_MEMO 内存口径修复、unify_pm 重锚门槛、
  全套诊断探针）存于 `docs/wip/l13-explicit-subst-round4-patches.patch`。
- **L13 保持原精化机制**，本仓库其它层（L07–L12）的显式替换不受影响。

### L13 弱点分析文档的结论订正

用 `docs/pattern-match-refinement-analysis.md` 的全部复现程序做移植
前后对照：**显式替换未使任何"失败→成功"发生**（前后逐字节一致）。
逐条复核发现：weak01/02/04 与文档的 `vtail` 控制例**本身即类型错误**
（文档基线亦自认"正确拒绝"）；weak03 现状已通过（文档"仍需修复"已过
时）；weak05/edge01 属可达性与结构精化交叉传播的**另一类**问题，不在
"精化载体更换"的按构造消除范围内。⇒ 该文档的"一般性缺陷"论断过度概括。

## 5. 已知限制与有意偏差（诚实清单）

1. `frcs` 对"已解 rigid + 非空 spine"做解析应用（旧版卡住）——更完备、
   对齐 dpm-nbe；L07 以 `test_fn_typed_index_slot_applied_after_refine`
   钉死，**各层移植必须复刻**。
2. fuel 是有界降级而非纯防护：极深负载下仍可能假 absurd；默认 4096
   池的边界已回到旧版同档（d≥400 安全，测试钉住 d=400）。
3. σ 只对"被包裹过的值"可见：meta 解（Tm 层）与 decl 表条目不在包裹
   范围（与旧版同一边界）。
4. 孪生版的 O(1) 名字表（`name_map`）是参考版没有的影子结构，`subst_cxt`
   需同步维护（L07/L08 移植中各修出一个相关 bug）。
