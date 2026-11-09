# D1 · 设计空间地图（L01–L13 + 分支/WIP 的写法候选）

> 角色：design-cartographer。只读静态分析，**不跑 cargo/bench**。本文件回答 FRAMEWORK **Q1（设计轴）**，
> 并为 Q2（逐轴优劣）/Q3（组合）/Q4（路线）提供候选清单与代码锚点。
> 标注：`[历史实测]`（仓库既有 bench/perf 文档数字，注明日期）/`[码]`（源码核对）/`[文档]`/`[推断]`。
> 读法：每条轴给**候选 → 实现位置 → 现有证据 → 判断（哪种更可能最优 / 缺什么证据）**；最后的 §6 是
> "文档提过但未实现"清单，§7 是组合冲突，§8 是交给 D2–D7 的问题分解。

---

## 0. 一句话总览

本仓实际上已经是一份**被完整实现过的设计空间实验**：L01 用 23 个变体回答了"值/环境/求值表示"这一轴
（唯一有系统实测的轴）；L02–L06 用消融开关回答了 conv/quote 记忆化与名字解析；L07–L13 则把"语言特性
增量"和"机制选型"绑在一起演进，导致**除 L01 外的多数轴只有 1–2 个候选被实现、且没有干净的 A/B**。
因此 D1 的核心产出是：把"已实现的候选"与"被文档否决/搁置的候选"分开列清楚，指出哪些轴**已有可复用
的实测证据**、哪些轴**必须先补实验才能下结论**。

| 证据强度 | 轴 |
|---|---|
| 强（多候选 + 同窗口实测） | 值/环境表示与求值器（L01 23 变体）、quote/conv 记忆化（L02–L06 消融）、名字解析/复合环境（L03）、匹配编译算法（09-17 分析 + 09-20 矩阵） |
| 中（双引擎 + 矩阵，但候选不完整） | 决策树 vs 逐臂、decl 表 vs 哨兵、trait 求解 Typ vs Val、LSP 观察面 |
| 弱（单实现/无对照） | 精化载体（σ vs update_cxt 在 L07–L12 是"重构"而非 A/B）、原生 Nat、宏展开时机、内建/effect 表示、测试/形式化策略 |

---

## 1. 轴总表（18 轴，按代码层次排序）

| # | 轴 | 候选（括号=实现层） | 当前倾向（判断） | 证据档 |
|---|---|---|---|---|
| A1 | 项表示 | Box AST / Rc 树 / 字节码 / bump 引用树 / 指令数组 / 原生闭包（L01 全测；L02+ 只留 Box-Rc 参考版 + bump 孪生） | bump 引用树 = 明确赢家；其余为负结果 | 强 |
| A2 | 值表示 | 24B 枚举 / 64 位打包字（L01 `bump_spine`；L02+ 孪生） | 打包字 = 常数级赢家，但引入 unsafe/别名风险 | 强 |
| A3 | 环境表示 | Rc 链 / 下标 arena / bump 链 / bump 切片 / **复合环境**（定义域平坦 + 绑定域链，L03+ 孪生） | 复合环境 = 决定性（chain O(n²)→线性） | 强 |
| A4 | 求值策略 | 递归 / CEK / 双栈推土机 / 双栈+右链快速路径（L01） | 双栈 + 右链快速路径 + 稳态复用 | 强 |
| A5 | 分配器 | 系统堆 / mimalloc / 下标 arena / bumpalo | bumpalo；mimalloc 4× 于 Windows 默认堆（L01 readme:70-71） | 强 |
| A6 | 求值记忆化 | 无 / quote memo（值×level）/ 内联槽 / conv 工作表 memo / β-eval memo | quote+conv memo 视负载；内联槽、β-eval memo 已否决 | 强（L01/L02/L05） |
| A7 | 名字解析 | 线性 walk / `name_map` + trail 撤销（L03+ 孪生）/ declarative 链 | name_map 对长 let 链是 O(n²)→O(1) | 中-强 |
| A8 | 元变量与 pruning | 无类型 meta（L03/L04）/ typed meta + `AppPruning` + `intersect`（L05）/ 全 scope 剪枝 spine（L12） | typed meta = 上游语义必需；非对称掩码细节是本仓 bug 高发区 | 中 |
| A9 | 合一器结构 | 递归 conv（L02）/ 工作表迭代 + 位相等快速路径（L03+）/ 单一 unify 带 `spec: Option<SpecSolve>`（L07–L12） | 单一合一器 + spec 参数 = 优雅且少一份代码 | 中 |
| A10 | 模式编译 | 决策树矩阵（旧 L09–L13）/ **逐臂下钻**（L07/L08 原生，L09–L13 2026-09-18 重写）/ 不可达臂 usefulness 检查（未实现） | 逐臂胜在编译期 ~20×，输在诊断能力 | 强（有 A/B） |
| A11 | 覆盖探测 | 推断级（拼带洞 Raw 走 infer）/ **值级结构探测** + fuel 保守判可达 | 值级 = 明确更优（4–5× 且判定逐例一致） | 强 |
| A12 | 精化载体 | `pm_defs` 事实表（旧 L07/L08）/ `update_cxt`+`refresh`（L09–L13 旧路，L13 现行）/ **显式替换 σ**（L07 定稿 → L08–L12） | σ 在 L07–L12 成立；L13 未过验收 ⇒ 与规模/生产特性冲突 | 中（非干净 A/B） |
| A13 | 全局名字世界 | decl 表名字键（L07/L08/L11/L12/L13）/ `Infer.global: Lvl` 大下标哨兵（L09/L10）/ 全限定键 + package/import（L13） | 名字键 decl 表更适合跨文件/LSP；哨兵是教学层时代架构 | 中 |
| A14 | trait 求解 | `Synth` 表驱动 Prolog，Typ 级匹配（L10/L11，`Val::to_typ` 桥）/ Val 级 `v_to_ref_val`（L12，`RefVal` 标记值）/ 两者 + 方法分发（L12 `namespace`、L13 全限定） | Val 级省一层桥、能表达更多值形态；Typ 级更简单 | 中 |
| A15 | 宏展开 | 无 / parser 期 `macro_rules` 展开（L11–L13，`MacroDepthGuard` 256） | 解析期 = 最简单；深度守卫是必需项 | 弱-中 |
| A16 | 内建/effect | `Tm::Prim` 无名 λ 链 + `Val::Prim` 卡住（L06–L11）/ `Tm::Prim(typ, pid)`（L11+）/ prim 入 decl 表 7 元组（L13）/ 可变全局 `Infer.mutable_map` / 文件 IO | decl 表统一 prim = 最干净（L13）；L09 起 builtin 退化是时代缺口 | 中 |
| A17 | 原生 Nat | 无（L07–L12，Nat = `SumCase` 一元链）/ `Val::Nat(u64)` 折叠 + `NAT_CHAIN_LIMIT` 护栏（L13） | 生产必需；但与"统一定义相等"冲突 | 中 |
| A18 | 观察面 / 双引擎 / 测试 | 无观察面（L07–L11）/ 三张 owned 表 push 期渲染（L12 雏形、L13 完整）/ 双引擎 parity / 黑盒双 oracle / Lean oracle（部分） | L13 形态可复用；双引擎是最大工程决策 | 中 |

---

## 2. 轴 A：值/环境/求值器（唯一有系统实测的轴，L01）

L01 是**本仓最有价值的设计实验资产**：23 个变体 = 6 条正交轴（项表示/值表示/环境/求值策略/输出编码/分配器），
同一算法（lambda 演算 normalize）同一负载族（church·dup·guest），`[历史实测]` 全部有数字。

**关键读数**（`[历史实测]` `src/L01_nbe/readme.md`，Windows x64 release，n=4000，相对 `bump_spine_iter_ss`）：
`bump_spine_iter_ss` 1.00× / `bump_spine_iter` 1.20× / `bump_spine_memo` 1.30× / `bump_spine_slim` 1.47× /
`bump_spine_rpn` 2.77× / `native_clo` 2.80× / `bump_spine` 3.03× / `cek_bump` 6.10× / `bump_iter` 6.10× /
`compiled` 7.33× / `bump_tree` 7.13× / `env_slice` 7.33× / `bump_arena` 9.40× / … / `cek` 50.3× /
`bytes_flat_value` 2547×。

**抬速账本**（`[历史实测]` readme:156-163，单变量消融，n=4000）：
`bump_tree` 0.197 → 打包 8B + 扁平 spine 0.160（-19%）→ 流式右链 quote 0.086（-46%）
→ 迭代化 0.068（-21%）→ eval 右链快速路径 0.039（-43%）→ 稳态复用 0.030（-17%）。

**判断**：
- **最优组合已被找到且被 L02–L13 采用**：bump arena + 打包值 + 扁平 spine + 双栈迭代 + 流式 quote +
  右链快速路径 + `Machine` 稳态复用（L02 README:285-302 的"移植清单"就是这套组合的落地）。
  D5 不需要再重测"哪个表示快"，需要测的是"在**带类型的 elaborator 负载**上各机制的边际收益"
  （L01 是纯 NBE，L02 起共享/分配画像已变：L02 README:85-89 明确 `_ss` 收益在 L02 上消失）。
- **未复用的赢家**：`bump_spine`（递归版）在**非右链形状**（parigot/exponential）反超迭代版 ~2×
  （`[历史实测]` readme:317-320）。elaborator 的真实负载是混合形状（universe/traitchain/strchain），
  是否需要"递归快路径 + 迭代兜底"的双模 eval 是**未被回答的最有价值性能问题**（D5/EXP-3 定制负载可测）。
- **已否决、不要重试**：条目瘦身 16B（readme:179-188）、内联记忆化槽（322-343）、原生闭包（189-196）、
  `compiled` 指令数组（197-204）、`bytes_flat_value`（373-374）、`nth` 小下标 unroll / 2^18 预分配 /
  `target-cpu=native`（L02 readme:130-143）。
- `[推断]` L01 的 `env_slice` 7.33× 与 L03 的"复合环境"结论是同一件事的两面：**平坦数组只对
  "索引只读、无 β 扩展"的域有利**；把这个教训用于 elaborator ⇒ 定义域平坦、绑定域持久链（L03 已做）。

---

## 3. 轴 B：环境/名字解析（L02–L06 消融）

| 候选 | 实现位置 | 证据 | 判断 |
|---|---|---|---|
| 线性 walk + `EnvCons` nth | L02 参考版/孪生（无 name_map） | `[历史实测]` chain 负载 O(n²)（L03 readme:171-181：k=12 8192 defs 383 ms；k=14 ~7.7 s） | 仅小 scope 可接受 |
| `name_map` + trail 撤销 | L03+ 孪生（`L03_NO_NAME_MAP` 消融，`L03/bump_spine_iter.rs:2102`） | `[历史实测]` chain k=14 7.7 s → 3.43 s | 必需项 |
| 复合环境（defs 平坦 + bind 链） | L03+ 孪生 | `[历史实测]` chain k=12 205→5.93 ms、k=15 66.5 ms 纯线性；其余六负载零回归 | **决定性（~30×）** |
| 单 Vec 平坦（β 也拷贝） | 已试，否决 | `[历史实测]` 全线 ~2×；L01 `env_slice` 7.3× 同源（L03 readme:192-201） | 负结果 |
| 平铺插入（`Rc<RefCell<Decl>>`，孪生口径） | 仅孪生；参考版仍 COW | `[历史实测]` COW 残留 O(n²)（perf-l08l13 §3.4:95-99） | 参考版下一刀 |
| `SmolStr` 名字 | L02+（参考版）；孪生热路径是 bump `&str` | `[历史实测]` 参考版 conv +3–6%、parse −15–29%（L02 readme:154-172） | 采纳；未试 `Rc<str>` |
| 名字键 decl 表 vs 大下标哨兵 | 见轴 A13 | — | 见 §6 |

**判断**：这条轴已收敛（复合环境 + name_map + bump &str），D5 不必再挖；**缺的证据**是
"L09/L10 的 `Env = List<Val>` 按位走查（`env.iter().nth(i)`）在真实负载上的实际代价"——
`[历史实测]` 09-20 附录 C:430 记录"残余 D^1.93，根治需换孪生 flat/binder 混合表示（表示变更，需 owner 决定）"，
这是全仓**最明确的一次"知道更优但没做"**。

---

## 4. 轴 C：元变量 / pruning / 合一器

- **C1 元变量表示**：L03/L04 无类型 meta；L05 起 **typed metas**（`MetaEntry` 保留类型，闭类型 =
  `eval [] (close_ty locals (quote lvl a))`，L05 readme:27-31）——上游语义必需（`displayMetas` 要类型），
  代价是 telescope 物化 O(上下文深)（L05 readme:129-140，prune 负载 8.7 s / 80 s）。
  `[推断]` 这是本仓**最贵的未解性能税**之一；文档已给出更优做法（"节点缓存已闭前缀、增量补新层"），
  未实现——见 §6-1。
- **C2 pruning 掩码**：L04 `BdCons{bound: bool}` → L05 `PrCons{slot: Option<Icit>}`（= 上游 `Maybe Icit`），
  非线性用 `RenBuf` 哨兵 `NONE_MARK`。`[码]` L05 readme:62-97 记录了三代 bug（哨兵覆盖、掩码序反转、
  Π 层镜像配对）——**这是全仓 bug 密度最高的机制**，验证成本 > 实现成本。
- **C3 合一器结构**：L02 conv 递归；L03+ 工作表迭代 + 位相等快速路径（`L02_NO_BITEQ` 消融：conv ~2×，
  L02 readme:91-98）；L05 `intersect`（同头 flex-flex 取交）；L07+ **单一 unify 带 `spec: Option<&mut SpecSolve>`**
  （L07 README:57-64）——"一个合一器"是 L07 正向设计的第三条纪律，也是本仓**优雅度最高的机制统一**。
  `[推断]` 最优写法就是 L07 的 spec 参数版，但注意它的前提是"可解集白名单"（L07 有，L09–L12 没有，见 CROSS §2）。
- **C4 记忆化**：quote memo（键=值×level）与 conv memo（键=值对，无需 level）**键设计不同**（L02 readme:196-208）；
  内联槽否决（L01:322-343）；β-eval memo 否决（L02:144-152，教训：先确认负载覆盖触发条件）。
  判断：memo 应按"负载是否共享"开关而非默认（L01:361-367）；**代价**是跨轮生命周期必须与 `Bump::reset` 对齐。

---

## 5. 轴 D–N 逐条（L07–L13 机制选型）

### D. 模式编译与覆盖诊断（有干净 A/B，结论最硬）

| 候选 | 实现位置 | 证据 | 判断 |
|---|---|---|---|
| 决策树矩阵 | 旧 L09–L13（已删：`compile_aux`/`MatchContext`/`PatConstructor`） | `[历史实测]` 差距全在**编译期**：`filter_accessible_constrs` 占 elab 34%、决策树 360 节点/单 run；常量优化上限 ~1.25×（L11 README:107-121） | 失败：常数不可救 |
| 逐臂下钻 | L07/L08 原生；L09–L13 2026-09-18 重写（`09b9ee8`/`4e97743`/…） | `[历史实测]` L10 参考版 0.750→0.252 ms（3.0×）、孪生 0.946→0.186（5.1×）；L11 参考 1.250→0.542（L10/L11 README） | **胜者** |
| 覆盖探测：推断级 | 旧 `filter_accessible_constrs`（拼洞 Raw） | `[历史实测]` 热点 34% | 失败 |
| 覆盖探测：值级 | `probe_accessible`（`L09/pattern_match.rs:84`、`L10:88`、`L11:97`、`L12:87`、`L13:106`） | `[历史实测]` 4–5×（L10 README:175-176），判定逐例一致 | **胜者** |
| 路径感知诊断 / 遮蔽 usefulness | 决策树独有，未移植 | `[文档]` L09 README:196-200、L11:155-187：收窄为"通配臂后报 Unreachable"+`fmt_path` | 换算法的**已付代价** |
| 嵌套覆盖两段式 | L07 修复 5 → L09–L13 全部移植 | `[码]` L09 README:176-183、L13 README:206-216 | 正确性必需 |

`[推断]` 这条轴的最优解已经找到（逐臂 + 值级探测 + 两段式），**真正的剩余设计问题**是
"能否在不回到决策树的前提下补回路径感知诊断"——D2 应回答"诊断能力对用户价值 vs 一个独立
usefulness 检查（Maranget 算法）的成本"。

### E. 精化载体（σ vs update_cxt vs pm_defs）

| 候选 | 实现位置 | 证据 | 判断 |
|---|---|---|---|
| `pm_defs` 事实表（惰性精化） | 旧 L07/L08（已删） | `[文档]` L07 README:53-55/§6：全局通道、跨分支泄漏、被精化变量剔出 pruning | 被淘汰（历史） |
| `update_cxt`+`refresh` | L09–L13 旧路；**L13 现行**（`cxt.rs:998`，L13 README:165-176） | `[文档]` 旧架构缺陷族：值过期、槽位错位（L07 README:48-52）；L13 五轮 σ 迁移未过验收（explicit-subst-status §4） | 仍在服役，但已知有 bug 族 |
| **显式替换 σ** | L07–L12（`Subst`/`VSub`/`frcs`/`SpecSolve`） | `[历史实测]` L07 深嵌套 16.9→18.4 ms（+9%）；L08 最差 match +17%（8µs）；L09–L12 parity 逐字节 0（explicit-subst-status §2/§3） | **L07–L12 的胜者**；L13 与规模/生产特性冲突 |
| σ 的变体：事实表 + σ 混合 / 全局解表 | 无 | — | 未探索 |

`[推断]` 这是**组合冲突最尖锐的一条**：σ 在 L07–L12 的成功依赖"小规模 + 无 prelude + 无 LSP 观察面"；
L13 失败的三条根因（12k meta 解链爆栈、纯 elab 28×、GADT 覆盖回归）都与"生产规模 + update_cxt 血缘的
先验假设"耦合。**缺的证据**：没有一次"同规模下 σ vs update_cxt"的对照（L13 的迁移是整体替换，
不是 A/B），D4 若要判这条轴，最小实验是 L13 上只换精化载体、固定 prelude/LSP 关闭。

### F. 名字世界（decl 表 vs 哨兵）

| 候选 | 层 | 结构 | 证据 | 判断 |
|---|---|---|---|---|
| `Infer.global: HashMap<Lvl, VTy>` + `Tm::Var(Ix(1919810+idx))` | L09/L10 | 类型事实全在 `src_names` BiMap；无名字键 | `[码]` L09 README:85-110（哨兵边界必须 `>=`，off-by-one 历史 bug `fd25b74`） | 教学层可接受；**构造子类型获取必须绕道 `infer_expr`**，是匹配编译器适配点 |
| decl 表名字键 | L07/L08/L11/L12/L13 | `Cxt.decl: HashMap<name, 5/7 元组>`，`Tm::Decl(name)` | `[历史实测]` Rc 化后 L11 struct 2952→846 ms（3.2–3.5×）；L13 7 元组带 prim/typ_pretty | **胜者**（跨文件/LSP/重定义检查都要求名字键） |
| 全限定键 + package/import | L13 | `范围.名字`，`symbol_table`/`import` 表 | `[码]` L13 README:21-56 | 生产必需 |
| COW vs 平铺插入 | 参考版 COW / 孪生平铺 | — | `[历史实测]` 参考版 COW 残留 O(n²)（perf-l08l13 §3.4） | 参考版可再进一步 |

### G. trait 求解（L10–L13）

| 候选 | 实现位置 | 证据 | 判断 |
|---|---|---|---|
| `Synth` 表驱动 Prolog（generator/consumer/assertion 表） | L10/L11/L12/L13 各一份 `typeclass.rs` | `[码]` L10 README:69-81；答案缓存顺带 | 机制统一（四层同名同构）但**代码各一份** |
| 求解桥：`Val::to_typ`（L10/L11）vs `v_to_ref_val`（L12） | L10 typeclass.rs:45-58；L12 README §2.5/§5 | `[文档]` L12 去掉 Typ 桥、改 Val 级匹配（RefVal 标记值） | Val 级更完备；Typ 级更简单——**未做 A/B** |
| 实例匹配方向 | 单向一阶（L10 `match_typ` d4c05ea；L12/L13 `val_match`） | `[文档]` 双向无 occurs 会假匹配泛型目标 | **单向 = 正确性硬要求** |
| outParam | 布尔掩码 + `Typ::Any`/`Val` 级通配 | `[码]` L10 README:53-57 | 已收敛 |
| effort 护栏 | `effort ≤ 1000` → `panic!("Too much effort :(")` | `[码]` L10 typeclass.rs:219-224；L10–L13 各 1 处 | **应改为诊断**；`[推断]` 这是最容易在生产层暴露的 panic 面 |
| 方法分发 | L12 `Cxt.namespace`（接收者表）→ L13 全限定直查 | `[码]` L12 README:269-276、L13 README:21-56 | L13 形态可下沉 |

### H–J. 宏 / 内建-effect / 原生 Nat

- **宏**：解析期展开（L11 起，`MacroDepthGuard` 上限 256，parser 7 处）。`[推断]` 解析期是最简单且
  正确的选择（宏不参与 elaboration，仅 token/语法层）；成本是 parser 复杂度（L11 parser 3,217 行 vs L10 1,366）。
- **内建/effect**：五代形态——`Tm::Prim` 无名 λ 链 + `Val::Prim` 卡住（L06–L10）→ `Tm::Prim(typ, pid)` 5 个
  （L11/L12）→ **prim 入 decl 表 7 元组 + `PrimId`**（L13，L13 README:1.5）。可变全局 `Infer.mutable_map`
  （L11 起）/ 文件 IO（L06 `FILE_IO_LOCK`）。判断：L13 的"一切皆 decl 表条目"最统一；L09/L10 的退化
  （只有 `string_concat`、无文件 IO）是**时代缺口**不是设计选择（L09 README:113-118）。
- **原生 Nat**：L13 `Val::Nat(u64)` + `nat_step_value` 折叠 + `quote_nat` 展开回链 + `guard_nat_chain`
  （`NAT_CHAIN_LIMIT`，`src/L13_namespace/eval_budget.rs:25-31`）。`[码]` 动机是 HDL 负载；`[推断]`
  收益/代价未被单独测过（09-20 矩阵的 L13 natadd 6.595 ms 含 prelude 启动），**与"统一定义相等"直接冲突**：
  Nat 折叠后 `succ (succ zero)` 与 `Nat 2` 的相等是值层免费，但 quote/pretty 要展开、且 L07–L12 无对应物。

### K–M. LSP 观察面 / 双引擎 / 测试形式化

- **LSP 观察面**：无（L07–L11）→ L12 雏形（`hover_table`/`completion_table` 存 Cxt+类型值，L12 README:264-267）
  → L13 三张 owned 表 **push 期渲染定稿**（跨引擎契约，L13 README:249-281）+ `ctor_hover_memo` +
  `case_spans` memo。判断：L13 形态是**唯一能同时服务两引擎**的形态（渲染串不依赖引擎内存），
  代价是"渲染成本进 elaboration 路径"（L13 实测：prelude 期 LSP 表渲染 ~600 ms / 12 s，
  explicit-subst-status §4:122-127 → 已有总闸先例）。
- **双引擎**：参考版（Rc 树/可读）+ 孪生（bump/性能），62,687 行 = 七层代码 49.4%，parity 是闸门。
  `[历史实测]` match 1.25–10×、大值 3–800×（CROSS §3）。判断：本仓已用真金白银证明"两套值表示"
  的性能价值；但**它同时锁死了 A12/A13/A14 的选型**（孪生必须逐项镜像参考版，任何参考版独有机制都要
  手工复刻，见 P3/P5/P8/P10/P11 未镜像清单）。
- **测试/形式化**：静态 `#[test]` 约 L07 70 / L08 60 / L09 10 / L10 25 / L11 33 / L12 35 / L13 612；
  集成 parity 7 套；黑盒 L07/L08 三卷；Lean oracle（`lean/OracleMain.lean` + `tests/lean_oracle_parity.rs`，
  2026-11-08 `ca53c1da`，详见 D2）。`[推断]` 当前最大缺口不是"测试数量"而是**判据强度不对称**
  （L07 parity 只比 Err 判定、L08 比正文，见 CROSS §1.4）与**执行重复**（`#[path]` 带入 lib 测试）。

---

## 6. 文档提过、但**尚未实现**的候选（按预期价值排序）

| # | 想法 | 出处 | 预期收益 | 证据缺口 / 重启条件 | 归属 |
|---|---|---|---|---|---|
| 1 | L05 telescope **增量闭前缀缓存**（fresh_meta 摊还 O(1)，替代每次 O(深度) 物化） | L05 README:129-140 | prune 负载 8.7 s → 量级下降 | 无实测；需牵动 `close_meta_ty` 路径 | D5/EXP-4 |
| 2 | L09/L10 `Env` 换 flat/binder 混合表示（残余 D^1.93 根治） | bench-matrix-09-20 附录 C:430 | strchain/struct/universe 可能数倍 | "表示变更，需 owner 决定"；参考版与孪生会分叉 | D7 决策项 |
| 3 | 参考版 decl 插入改**平铺**（`Rc<RefCell<..>>`）或键 `SmolStr` | perf-l08l13 §3.4:93-103 | L11/L12 struct/strchain 5.3–5.8× 残留 | 参考版将不再是"写时复制语义 oracle" | D7 决策项 |
| 4 | L13 σ 迁移（五轮补丁存档） | explicit-subst-status §4、docs/wip/ | 若成功可统一 L07–L13 | 已实测否决：4 既有失败、纯 elab 28×、12k 链爆栈、孪生镜像未做 | D6 |
| 5 | L13 孪生**逐列精化 σ 镜像**（Arm 加 refine 字段，6 个构造点 + 探测点 wrap） | wip §5:186-207 | 消除唯一已知 REF/TWIN 语义分歧 | 结构性改动，需 round-6 首项排期 | D6 |
| 6 | L13 compiler **探测缓存** + meta **undo journal**（替代整表 clone）+ `constr_pi` 按名缓存 | wip 接续清单:238-256 | 编译器是 quote 最大发起方（63,953 次）→ 最大常开未缓存开销 | 需 σ 或仅 probe 缓存可独立做 | D5 |
| 7 | L13 `FRCS_MEMO` 双代清空 / `FORCE_MEMO` Weak 输入 | wip:266-277 | 长跑内存 13 GB → 有界 | 需长跑负载验证 | D5 |
| 8 | L13 可达性探测 **per-arm**（`accessible_set` 每列只按 `arms.first()` 的 refine） | wip:248-250 | 正确性面（多臂异 σ） | 需构造多臂异 σ 用例 | D2 |
| 9 | L07 **P10 第三步**：`Error::span` → LSP `Diagnostic.range` | PR-l07-hardening §7:140 | LSP 诊断质量 | L07 尚未接入 LSP | D7 |
| 10 | L07 深值**端到端递归 Drop**（现在测试用 `ManuallyDrop` 绕开） | L07-RISKS P11:48 | 10 万层深值可正常释放 | 需自定义 Drop/堆栈析构 | D3/D5 |
| 11 | 决策树的**路径感知诊断 / usefulness 检查**以独立组件补回 | L09 README:196-200 | 诊断质量（当前"通配臂后才报 Unreachable"） | 需评估用户价值 | D2 |
| 12 | L13 prelude 期 LSP 表总闸（补丁里有、master 没有；**只让参考版对齐孪生**） | explicit-subst-status §4:122-127 | `typort check` 21.1s → 9.3s（零行为变更） | 与 σ 补丁绑定（随回退撤下）；可独立重做 | D5/D6 |
| 13 | L01 未移植 guest 负载 `random` / `self_interp_size` | L01 readme:291-296 | 补混合形状覆盖 | 需项计数表/超时过滤 | D4 |
| 14 | Lean oracle 全量形式化（现为部分 parity） | docs/lean-compiler-formalization-plan.md | 正确性证据升级 | 见 D2 | D2 |
| 15 | `Too much effort` effort 超限改诊断 | L10 README:74-77 | panic 面收窄 | 需跨层统一错误形态 | D2 |

---

## 7. 组合冲突（Q3 的输入：逐轴最优不一定可组合）

| 冲突对 | 机制 | 后果 | 证据 |
|---|---|---|---|
| 值表示 vs 别名安全 | 打包 8B 值 + 迭代内核的工作栈重借 ⇒ Stacked Borrows UB（L10–L13 同族） | 性能最优伴随 unsafe 风险；Miri 未跑 | FINAL(review-continuity) §4:89-91（行号已刷新）；CROSS §2.1 |
| σ 精化 vs 生产规模 | σ 要求"解前构建、解后消费的值在消费点包裹"；L13 的 prelude/LSP/大值把"消费点"扩散到不可枚举 | L13 五轮失败（GADT 覆盖回归、12k meta 链、28×） | explicit-subst-status §4；wip §5 |
| 决策树 vs 诊断 | 逐臂下钻赢 20× 编译期，输掉路径感知覆盖/遮蔽诊断 | 全仓已选性能；诊断能力需独立补 | L09 README:196-200；L10:118-133 |
| 双引擎 vs 机制统一 | 孪生必须逐项镜像参考版 ⇒ 参考版独有机制（P3/P5/P8/P10/P11）在孪生缺失 | 判定分裂窗口（ref Err / twin Ok） | CROSS §1.5/§2.2；L07-RISKS §0.1 |
| 原生 Nat vs 统一定义相等 | L13 `Val::Nat` 折叠 succ/zero，与 L07–L12 的 `SumCase` 一元链语义分叉 | 任何"下沉 Nat"都要重做相等/quote/pretty | L13 README:1.4；CROSS §1.5 |
| quote/conv memo vs bump 生命周期 | memo 表必须随 `Bump::reset` 失效（悬垂键）⇒ 跨轮复用与 memo 只能二选一或按轮重建 | L02 已按轮新建表；L13 另做 FORCE_MEMO epoch | L02 README:188-189；L13 README:285-290 |
| LSP 观察面 vs 引擎内存 | push 期渲染串是跨引擎契约，但 `PreludePool` 的引用计数非原子 | 池化安全依赖"推池时持最后引用"前提 | L13 README:293-299 |
| 精化白名单 vs 层旧语义 | L07 有 bind-slot 白名单；L09–L12 无（忠实保留旧 `update_cxt` 边界） | 同一程序在不同层可解性不同 | explicit-subst-status §3 P2:100-106 |
| 复合环境 vs decl 表世界 | defs 平坦区假定"定义域只追加"；L13 的 import/namespace 是可变作用域 | 复合环境难直接用于 L13 | L03 readme:183-201 与 L13 README:21-56 的张力 |

---

## 8. 交接给 D2–D7（D1 的边界与问题清单）

1. **D2（正确性）**：①"逐臂 + 值级探测"下，覆盖诊断的收窄是否可接受？是否需要独立 usefulness 检查？
   ②`Too much effort`/`v_app Match panic`/`fuel 耗尽三档` 三类 panic→诊断改造的优先级；
   ③σ 与 update_cxt 在同一语义面上的可判定差异清单（用 L07–L12 的 parity 语料反向验证 L13）；
   ④Lean oracle 当前覆盖的语义面（哪些选择只能靠测试、不能靠证明）。
2. **D3（优雅）**：①"一个合一器 + spec 参数"（L07）是否应成为全仓唯一合一器？②decl 表 5/7 元组、
   `Cxt` 字段、`Machine` 稳态复用三者的概念数能否压缩；③双引擎是否应改为 `trait Engine` 单代码双后端
   （`[推断]` 不可行：两套值表示差异是本质的，见 CROSS §5-6）。
3. **D4（实验）**：按 §2/§5 的证据缺口排序——EXP-1 已由 L01 历史上完成（只需复测"带类型负载"的边际收益）；
   EXP-2 已有结论（逐臂）；**真正需要新实验的是**：L13 上"σ 载体 × prelude 关闭 × LSP 关闭"的最小 A/B（冲突 A12）、
   L09/L10 flat/binder 环境（§6-2）、L05 telescope 缓存（§6-1）、递归/迭代双模 eval（§2）。
4. **D5（技术矩阵）**：需为 §2 每个机制标注"是否在带类型 elaborator 上复现"（L01→L02 已证明部分不复现：
   `_ss` 收益、quote memo 键设计差异）；并把 §7 的 unsafe 代价纳入。
5. **D6（分支考古）**：§6 的 #4/#5/#12 是补丁系列，需按 `git apply --check` 复现；另 L01 的 5 个否决变体
   与 L02 的 6 个否决轴是**负结果金矿**，必须归档避免重试。
6. **D7（架构）**：D1 的判断是——**不要试图统一成一个引擎**；最优架构应是"**一个参考语义核心（可读、可证明、
   带完整诊断） + 一个性能后端（打包值/复合环境/迭代内核）**"，两后端共享 parser/pretty/printer 契约，
   并用 L08 式强 parity（Err 正文逐字节）+ 不归一化 `?N` 探针守门。差异清单应显式登记为"语义契约"
   （fuel 口径、探测隔离、判定三档），禁止"参考版修了孪生没修"。

---

## 9. 30 秒结论

**本仓的设计空间已被探索得很深，但证据分布极不均匀**：表示/环境/匹配算法三类轴有硬数字（L01 23 变体、
L03 chain 表、09-20 矩阵），精化载体/trait 桥/内建/Nat 四类轴只有"单实现 + 事后重构"，
无法下"最优"结论。D1 的判断：**最优架构不是选某一层，而是把 L01 的"表示实验结论" + L07 的"正向设计三纪律"
+ L09/L10 的"值级探测+复合环境" + L13 的"decl 表 + declb 缓存 + eval budget"拼起来**；
最需要补的证据是"带类型负载上各机制的边际收益"与"σ 在小规模 L13 上的最小 A/B"。
