# L07 ⟷ L12「共有部分」实现差异 · 最终报告

> 团队作业：Lead + 8 名分析员，8 个角度。HEAD `8f4287ae`（master，2026-11-24），只读、未构建。
> 底稿与口径 [MAP.md](MAP.md)，分角度证据 [01](01-kernel-nbe.md)–[08](08-evidence.md)。
> **用户原始预期：L12 与 L07 的共有部分应当一脉相承。**

## 0 结论摘要：**预期成立** —— 但要拆成三句说

**总判定：一脉相承成立（强）。** 这与上一轮 L07⟷L13 的「语义前提层断裂」结论**完全不同**，而且方向相反：
L13 才是断点，L12 不是。本轮的核心发现是 —— **L07 与 L12 之间的差异，98% 不是 L12 造成的。**

| 层次 | 判定 | 一句话 |
|---|---|---|
| **配方层**（算法骨架/设计纪律/预算口径） | **成立（强）** | 合一内核 21 个函数 keep=1.000、`UNIFY_FUEL=4096`/`MATCH_CMP_BUDGET=64`/`EQ_BUDGET=20_000` 同值同点、σ 载体 `SubstV/wrap_sub/frcs/SpecSolve` 逐点对位、逐臂下钻匹配器逐字节同 |
| **实现层**（同一段代码被搬过去） | **成立（强，参考版）/ 中（孪生版）** | `pattern_match.rs` 与顶层 `syntax.rs` **自 L07 起六层逐字节相同**；19 个同路径文件在 L12 里是「一字未改地从 L08/L09 继承」；孪生侧在 **L08 分叉**后另有 5 项加固没跟过来 |
| **语义前提层**（决定结果的机制） | **成立（不断）** | 精化载体仍是 σ/`subst_cxt`（13 处，与 L07 同）；L13 的 `update_cxt`/`refresh`/`FORCE_MEMO`/`eval_budget` 在 L12 **全为 0** —— L12 没跟 L13 走 |

**一句话**：这不是「两个层各自演进后碰巧相似」，而是**同一条链上的两个时间快照** —— 相隔四层，
中间只有 **L08 一次**结构分叉。**用户该担心的不是「L12 改坏了吗」，而是「L08 那次分叉丢了什么，
以及 L07 11 月新长的观察面有没有回灌」。**

### 0.1 三个必须一起看的数字

| 转换 | 加权 keep（前层 → 后层） | 含义 |
|---|---:|---|
| **L07 → L08** | **0.9323** | **全链唯一的实质性缺口（−6.8%），发生在 L08** |
| L09 → L10 / L10 → L11 | 0.9984 / 0.9992 | 几乎不动 |
| **L11 → L12** | **0.9858** | L12 自己只动了 1.4% |
| L07 → **L12**（累计） | **0.9237** | **与「L07 → L11」完全相同** ⇒ **L12 没有引入任何新增损失** |
| L12 → L13 | **0.7002** | 断点在这里 |

## 1 「共有部分」怎么界定，以及三个度量陷阱

L07 有 32 个 `.rs`、L12 有 34 个，**同路径 31 个**。L07 独占 1 个（`observe.rs`），L12 独占 3 个
（`typeclass.rs`、孪生 `typeclass.rs`、`parser/macros.rs`）。本报告只把**同角色 + 同位置 + 两侧在用**的算共有部分。

**陷阱 1：文件级相似度会被「L12 单边增量」稀释。** `parser/mod.rs` 的 keep07=0.977 但 keep12=0.476 ——
不是 L12 改写了 L07 的解析器，而是 **L12 在 L07 骨架上加了 2.5 倍的宏/typeclass/struct 语法**。
07 分册逐行复核：19 个递归下降规则函数里 **14 个在 L07→L12 之间 token 流完全相同**，其余 5 个只在链尾追加。

**陷阱 2：低分可能是「L08 换掉、L09–L12 忠实继承」，不是「L12 重写」。** 全部 7 个低分文件的差异首次出现层
**都在 L08（或 L08→L09）**，此后逐层冻结（MAP §10 A.2 有逐层定位表）。孪生 `subst.rs`/`compiler.rs`/
`spine.rs` 自 L08 起、孪生 `struct_eq`/`syntax`/`rename`/`unify`/`eval`/`quote`/`prim` 自 L09 起**逐字节未改**。

**陷阱 3：方向可能与直觉相反。** 不是「L12 比 L07 旧」，而是**两边各有各的新**：L07 孪生在 09-19 `fb89bb00`
落地了三项加固（深值任务化/`InlineStack`、`simpl_decl` 旁路缓存、`pending` cons 链），而 **L08 孪生在
09-15 `efa47b9c` 就分叉了**，因此那批从未进入 L08→L09→…→L12 这条线。反过来，L07 的观察面（`observe.rs`）
是 11-21~23 才长出来的，晚于 L12 的 11-17 重建。

## 2 血缘真相：一条被重建过两次的链，断点在 L08 与 L12→L13，不在 L07→L12

| 时间 | 事件 | 对「共有部分」的影响 |
|---|---|---|
| 2026-09-15 `efa47b9c` | **L08 孪生同步「显式替换精化」（bump arena 表示）** | **孪生线在此分叉** |
| 2026-09-19 `fb89bb00` | L07 孪生修复轮 + 三项 backlog + 拆目录模块 | 分叉**之后**才落地 ⇒ L08 线永远看不到 |
| 2026-09-23 `08bfc7cf` | L08「性能版」单文件拆成入口 + 15 子模块（8284 行） | 孪生 `struct_eq` 在此换成递归 `_go` 族 |
| 2026-11-10/12/14 | L07/L08 各自加固（PrimFunc prim、P1–P11 回灌、`UNIFY_FUEL` 覆盖） | **双向**，不是单向继承 |
| 2026-11-16 `c6c0e892` | L07/L08 加 literal equality 合一臂（ref+twin） | 同日 L09–L12 跟进 |
| **2026-11-17 `73d68cf2`** | **`refactor(L12): 以新 L11 实现思路重建 canonical 层（ref+twin）`** | **L12 唯一一次重建；只改了 11 个文件** |
| 2026-11-18 `246a4e33` | 文档：L09–L12 重建收尾，L13 走产品层例外 | **链与 L13 从此分家** ⇒ L13 成为断点 |
| 2026-11-21~23 | L07 参考版观察面（`observe.rs`、hover 渲染、形状认回） | L07 单边新增；L12 在 11-23 `2ad6b1b4` **只回填了渲染层** |

**11-17 重建只碰了 11 个文件**：`machine entry force bump_spine_iter.rs mod elaboration unification
pretty surface tests parser/mod`。**其余 19 个同路径文件是「一字未改地继承」的** —— 包括全部孪生
`struct_eq`/`subst`/`syntax`/`rename`/`unify`/`eval`/`quote`/`prim` 与顶层
`cxt`/`struct_eq`/`shape`/`raw_pretty`。

## 3 八个角度的独立评级

| 角度 | 评级 | 断/欠在哪里 |
|---|---|---|
| 01 NbE 孪生内核 | **中偏强** | 骨架逐字同源、6/8 文件逐字节继承；L07 09-19 的深值任务化 + `simpl_decl` 缓存未跟过来 |
| 02 σ 载体/VSpan/force | **中偏强**（ref 强 / twin 中） | σ 完整可用、VSpan 真在用；twin 丢 `InlineStack` 深值迭代、`pending` cons 链、`vapp1` β 守卫 |
| 03 合一/结构相等 | **强**（ref）/ **中**（twin） | 参考版只差宇宙载荷；twin `struct_eq` 的 `SEqTask` 工作栈 → 原生递归 |
| 04 上下文/精化载体 | **强** | 载体同位置同字节、`cxt.rs` 归一化后 1.0000；L12 只做本章增量 |
| 05 模式匹配编译 | **强** | `pattern_match.rs` 六层逐字节同，调用的 11 个方法签名逐字未变 ⇒ 匹配语义无差异 |
| 06 名字世界/观察面 | **强** | 名字世界与 `surface.rs` 契约逐字节继承；观察面是「通道在、生产者缺」的减配子集 |
| 07 解析与渲染 | **强** | 14/19 规则函数 token 流完全相同；L12 对解析器的实质改动为零 |
| 08 行为证据/门禁 | **强（偏强）** | 66 个用例零丢失、L10=L11=L12 实跑逐字一致；**但全仓无 L07⟷L12 对拍门禁** |

## 4 四档判定总表

**E0/E1 真继承（同一份代码或仅机械改写）**
`pattern_match.rs` 与顶层 `syntax.rs`（**自 L07 起六层逐字节同**）；`cxt.rs`/`struct_eq.rs`/`shape.rs`/
`raw_pretty.rs`/`parser/lex.rs` 与孪生 `rename/unify/eval/quote/prim/compiler/spine/subst`（L08/L09 起逐字节冻结）；
合一 21 个函数 keep07=1.000；`UNIFY_FUEL=4096`/`MATCH_CMP_BUDGET=64`/`EQ_BUDGET=20_000` 同值同点；
σ 载体 `SubstV/wrap_sub/frcs/SpecSolve` 逐点对位（`wrap_sub` 36/36、`SubstV` 44/44）。

**E2 机制漂移（同角色、不同机制）**
① 宇宙检查：`ty_precheck`（零副作用、不动 `?N`）→ `check_universe`（`overwrite_meta` 会解 meta），首次 **L09**；
② 报错尾部渲染：`expected universe, got {}` + `pretty_tm` → `got {:?}`（L07 注释专门说过不能用 Debug），**L09**；
③ name_map 的 σ 包裹面收窄（整表 + 轨迹回滚 → 仅 types 链 `source` 节点），**L08**；
④ `MacroState` 由 `Vec<IError>` 扩成三元组、内置 `stringify` 无条件注册，**L11**；
⑤ `decl_pretty` 的 `fin` 标记退化（恒写 `true`、使用处忽略），**L12**。

**E3 缺失或落后（本轮重点，共 8 项，全部首现于 L08/L09）**
① 孪生 `struct_eq` 的 `SEqTask` 堆上工作栈 → 原生递归 `struct_*_go`（深值可爆栈，L07 有 10 万层回归钉）；
② 深值扫描退回递归（孪生 `subst.rs`/`force.rs` 的 `InlineStack` 消失），唯一回归钉 `deep_value_tests` 被删；
③ 卡住 match 的 `pending` 由 cons 链（O(1) 头插）退回切片（每次整段重拷 ⇒ O(k²)）；
④ `simpl_decl` 旁路缓存 `SIMPL_CACHE` 在 L12 完全缺失，`clear_round` 也无失效调用；
⑤ `rename_iter` 深值任务化缺失（深 Sum/Obj 走原生栈）；
⑥ `vapp1` 缺 L07 的 VSub→闭包 β 守卫（L12 直接递归回用调用方栈，而 `eval_iter` 会 clear 外层任务）；
⑦ `Tm::Prim` 零元卡住头退回 env 全槽收集（quoted `Prim` 跨 env 重求值会捕获无关槽）；
⑧ 裸 `U` 关键字消失（L09 宇宙分层，**有意升级**）：实跑 3/27 个 L07 期共有语料在 L12 报 `name not in scope: U`。

**E4 L12 单边新增（不算差异）**
`Val::Call` 三处（`unification.rs:638-645`、`:1307-1313`）、Val 级 `solve_trait`（`:751-830`）、
`Val::U(x)` 全域载荷（L09 起）、`typeclass.rs`（378 行）、`parser/macros.rs`（345 行）、
`force_deep`（L12 新增，`force.rs` +173 token 的全部来源）、`pretty` 的 `Tm::Call` 渲染臂（15 行）。

## 5 十条最重的差异

| # | 差异 | L07 | L12 | 后果 | 档 |
|---|---|---|---|---|---|
| 1 | **孪生 `struct_eq` 遍历机器** | `SEqTask`+`seq_run` 堆上工作栈（51 处）`L07 twin struct_eq.rs:70-190` | 原生递归 `struct_*_go`（40 处），`L12 twin struct_eq.rs:54/71/142/251` | 深值栈溢出；`EQ_BUDGET` 虽同为 20_000 但 L07 的 10 万层回归钉没了 | **E3** |
| 2 | **卡住 match 的 pending** | cons 链 O(1) 头插 `L07 syntax.rs:248/265` | 切片，每次整段重拷 `L12 syntax.rs:252`+`force.rs:56-58` | 逐应用 O(k²) | **E3** |
| 3 | **深值迭代 vs 递归** | `InlineStack` `L07 subst.rs:208/:159`、`force.rs:172` | 递归 `L12 subst.rs:169`、`force.rs:138` | 深结构爆栈；回归钉 `deep_value_tests` 被删 | **E3** |
| 4 | **`simpl_decl` 旁路缓存** | `SIMPL_CACHE`+`machine.rs:200/1781` 失效 | 全无，`machine.rs:202-214` | 重复化简，纯性能 | **E3** |
| 5 | **`vapp1` β 守卫** | 私有草稿栈 `L07 force.rs:81-107` | 直接回用调用方栈 `L12 force.rs:74-79`（`eval_iter` 会 clear 外层任务 `eval.rs:182`） | **潜在正确性**，非性能 | **E3** |
| 6 | **观察面** | `observe.rs` 19 项职责 + 洞 inlay + 6 通道 | 14 项无对位、2 项部分承接，只剩 2 个采集点；`inlay_hint` 计数 0 | `surface.rs` 六通道**仍在**但生产者没了 ⇒ LSP 静默为空，不报错 | **E3** |
| 7 | **宇宙检查机制** | `ty_precheck` 零副作用 `L07 elaboration.rs:176-233` | `check_universe` 解 meta `L12:163-222`（L09 引入） | 同错源下 `?N` 编号/未解 meta 集可能不同；L07 会报错的注解被静默解成 `U(0)` | **E2** |
| 8 | **报错尾部渲染** | `got {}`+`pretty_tm` `L07:194` | `got {:?}` `L12:215` | 用户可见文本退化（Val 调试转储） | **E2** |
| 9 | **裸 `U` 关键字** | `("U", UKeyword)` `L07 lex.rs:90` | 只有 `("Type", TypeKeyword)` `L12 lex.rs:116` | 3/27 语料在 L12 报错（有意升级，非回归） | **E3** |
| 10 | **门禁真空** | `l07-twin` 默认关 | `l12-twin` 默认关；`audit_crosslayer_probe.rs` **0 个 assert**、只写 TSV | 上述 E3 **没有任何门禁会报警** | **E3** |

## 6 行为证据（不是读码推断）

1. **实跑**（`target/release/realbench.exe`，未构建）：27 个纯共有语料，**L07 27/27 通过、L12 23/27**；
   4 个失败的判定全部上溯到 **L08（孪生）与 L09（`U` 关键字）**，且 **L10 = L11 = L12 逐字相同**。
2. **测试零丢失**：`tests.rs` 66 个 `#[test]` 在 L12 一个没丢（差集为空），59 个正文逐字节同；
   整文件 diff 只删 45 行，**100% 是 `U`→`Type 0` + `l07_`→`l12_` 的机械替换**，零断言/零用例被删。
   L12 那 17 个「新增」用例首次出现层是 L08×12 / L10×3 / L11×2 —— **L12 自己 0 个**。
3. **逐字节冻结**：`pattern_match.rs` 与顶层 `syntax.rs` 的 SHA 在 L07–L12 **六层完全相同**。
4. **孪生不是 LSP 引擎**：`src/lib.rs:361` 用的是 `L13_namespace::bump_spine_iter`（`:262` 有注释
   「Default: the LSP runs on the twin」）。⇒ **第 5 节的孪生侧 E3 落在 bench 路径上**，不影响 LSP 产品行为，
   这是本报告愿意把评级放在「强/中偏强」而不是「弱」的关键理由。

## 7 风险清单

**高**
- **观察面「通道在、生产者缺」**：`surface.rs` 仍声明 6 条通道并用 `completion.is_empty() && inlay_hint.is_empty()`
  判空（`surface.rs:61-62`），但 `completion_table`/`inlay_hint_table`/`push_inlay_hint`/`inlay_wanted`/
  `hover_query` 在 elaboration 侧全为 0 ⇒ **静默为空，没有任何断言会失败**。
- **门禁真空**：全仓无 L07⟷L12 对拍；`audit_crosslayer_probe.rs` 0 个 `assert!` 永不变红；
  两侧孪生对称封印（`Cargo.toml` + `tests/*_fast_parity.rs:1`）。
- **`vapp1` β 守卫缺失**是唯一**潜在正确性**问题（其余 E3 都是性能或栈深度），建议优先核实。

**中**
- L07 孪生的 5 项加固（第 5 节 #1–#5）在两支上已分叉 2 个月，**再回灌的成本随时间上升**。
- `bump_spine_iter.rs` 根聚合的 `VSub 6→0 / subst_cxt 1→0` 是**文档漂移而非职责搬走**
  （子模块 `wrap_sub` 36/36、`SubstV` 44/44），且 L12 的导览文档描述了 `pm_solvable/pm_mark/pm_restore`
  三个**不存在**的机制 —— 会误导后续维护者。

**低但会误导人**
- `unification.rs:1159-1162` 注释自称「L09–L12 仍未补 literal 相等臂」，**实测 `:1163` 已有该臂**，是过期注释。
- 引用文档时注意：L12 与 L07 的 `struct_eq.rs` **不是逐字节同**（L07==L08、L09==L10==L11==L12，
  两段之间差 2 个 hunk / +11−2 行，即 `Val::U/Tm::U` 载荷穿线）。

## 8 勘误（对 MAP 与各分册的校正）

1. **MAP §10 A.3 的「同」只表示同一段内相同**：`struct_eq.rs` 的两个哈希段是 L07==L08、L09==L12，
   **L07 ≠ L12**（差 2 个 hunk）。
2. **MAP §6.1 结案**：`push_hover_rendered` 在 L12 grep=0 **既非漏移植也非刻意不做** ——
   职责以裸 push 内联在 `L12 elaboration.rs:350`，渲染路径（方案 3+4）完整，`tests/l12_lsp_surface.rs:39/51` 依赖其输出；
   丢的是 `hover_query` 双闸与 `decl_pretty` 的 `fin` 判定。根因是 **L08 从来没有 L07 的 observe.rs 设计**。
3. **MAP §6.2 结案**：**L12 孪生不是 LSP 默认引擎**（`src/lib.rs:361` 用 L13 孪生），`l12-twin` 默认关。
4. **唯一「L12 少于 L08」的项**：洞型 inlay 在 L08 存在（`L08 elaboration.rs:141-171`），L09 起消失。
   其余观察面缺口 L08 本来就没有（L07 更晚才加），归因应写「L07 单边演化 + 回填不全」。
5. **`shape.rs` 不是共有遗产而是新移植件**：2026-11-23 由 `6f7e245e`→`2ad6b1b4` 从 L07 移植回 L12，
   119/120 行同，唯一差 `Val::U`→`Val::U(_)`（L12 层号恒 0，判等价）。

## 9 如果要更「一脉相承」，三条路线

1. ~~**只补孪生 5 项加固（推荐，成本最低）**~~ **← 已撤回，见 §11。** 原建议是把 `struct_eq` 的
   `SEqTask` 工作栈、`InlineStack` 深值迭代、`pending` cons 链、`SIMPL_CACHE`、`vapp1` β 守卫回灌进
   L12 孪生。**这是错的**：孪生已被主动封印（`7a68abc7` / `2acc5231`），不在维护范围，
   正确分类是 **E3-冻结（只记录、不排期）**。
2. **补观察面（用户可见收益最大）**：L07 `observe.rs` 的 14 项无对位职责 + `inlay_hint` 生产者。
   注意先决定「要不要」，因为 L12 的 `surface.rs` 六通道是**声明了但不填**，属于主动设计选择还是欠账需要作者确认。
3. **加一条跨层门禁（防止未来再漂）**：现在没有任何门禁比 L07⟷L12。最小可行版本是把本轮
   §6.1 的 27 个语料判定 + `pattern_match.rs`/`syntax.rs`/`cxt.rs` 的哈希钉进 `tests/`，
   并把 `audit_crosslayer_probe.rs` 从「只写 TSV」改成「带断言」。成本：半天。

**不建议**：为 L12 做「copy-forward 重定基」。本轮证明 L12 已经是 L07 的忠实后代，
真正的问题只在 **L08 那一个分叉点**与**观察面回填** —— 重定基属于用周级成本解决天级问题。

## 10 附录

**分册**：[01-kernel-nbe](01-kernel-nbe.md)（孪生 NbE）、[02-subst-force-vspan](02-subst-force-vspan.md)（σ/VSpan/force）、
[03-unify-structeq](03-unify-structeq.md)（合一/结构相等）、[04-elab-cxt](04-elab-cxt.md)（上下文/精化载体）、
[05-match-compiler](05-match-compiler.md)（模式匹配）、[06-names-surface-observe](06-names-surface-observe.md)（名字世界/观察面）、
[07-parser-pretty](07-parser-pretty.md)（解析/渲染）、[08-evidence](08-evidence.md)（行为证据/门禁）。

**复算产物**：`tmp/l07l12-similarity.tsv`（31 文件 keep07/keep12/jac）、`tmp/l07l12-mechanism-matrix.txt`（跨 7 层机制矩阵）。
**口径声明**：全部结论基于静态读码 + 已编译二进制的有限实跑（`target/release/realbench.exe`），
**未执行 `cargo build/check/test`**；凡「运行时会怎样」均标 `[推断]`/`[未核实]`。
锚点行号对应 HEAD `8f4287ae`，重建章节后会漂移。

## 11 修订：孪生侧差异的分类更正（2026-11-24 晚）

**本节推翻 §4 的 E3 归类与 §9 建议 1 的一部分。** 起因：按 §9 建议 1 真实实施后，
被作者指出 L12 孪生**早已封印**，不该继续投入。

**事实（已核）**：

| 项 | 值 |
|---|---|
| 封印提交 | `7a68abc7`（2026-11-22，L07）、`2acc5231`（2026-11-23，L09–L12） |
| 封印语义 | "不再参与门禁/parity"：`lNN-twin` feature 默认关、`tests/lNN_fast_parity.rs` 编成空 |
| 是否产品路径 | **否**。`src/lib.rs` 对 `L12_canonical::bump_spine_iter` 零引用；LSP 默认引擎是 L13 孪生（`src/lib.rs:361`） |
| 仍存在的使用方 | 仅 `src/bin/{l12bench,realbench,l06l13mem}.rs`（基准） |

**分类更正**：§4 的 E3 清单里，凡落在孪生侧的 5 项（`struct_eq` 工作栈、`InlineStack` 深值迭代、
`pending` cons 链、`SIMPL_CACHE`、`vapp1` β 守卫）**一律从 E3 降级为 E3-冻结**：

| 分类 | 含义 | 处置 |
|---|---|---|
| **E3-活跃** | 该路径仍在门禁/产品/默认测试里 | 记缺口，排期 |
| **E3-冻结** | 已被封印、仅剩基准用途 | **只记录、不过问** |

**方法论教训**：本轮分析按"L07 的 token 有多大比例仍出现在 L12"排序找差异，这一步是对的；
但缺一道前置过滤——**这条代码路径还有人在维护吗？** 没有这道过滤，就会把"历史快照差异"
误报成"待修缺口"，进而产生真实但无价值的返工。§1 的度量陷阱应再加一条：

> **陷阱 4：先判路径活性，再判差异大小。** 冻结路径上的差异只需登记，不需要修。

**撤销状态**：按 §9 建议 1 做的改动已全部回退（`src/L12_canonical/` 工作区 clean），
补丁留档 [backport-l12-twin.patch](backport-l12-twin.patch)、经过见 [BACKPORT.md](BACKPORT.md)。

**§9 建议 2 与 3 不受影响**：观察面（`elaboration.rs`/`mod.rs`/`surface.rs`，**参考版**）与跨层门禁
都在活跃路径上，仍然成立。
