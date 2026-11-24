# 01 · NbE 求值内核（孪生）· L07 ⟷ L12 差异

> 角度：`bump_spine_iter.rs` 根聚合 + 孪生 `machine / eval / quote / rename / spine / env / bench_src`。
> 口径：`docs/compare-l07-l12-shared/MAP.md`（含 §10 附录 A）；只读分析，未构建；数字全部重核。锚点写法 `L07 …:N / L12 …:N`，前缀 `src/L{07,12}_{sum_type,canonical}/` 省略。

**结论先行**：孪生内核是**同一台机器**，不是两份实现。`eval/quote/rename/spine/env` 在 L12 侧是
**L08/L09 的逐字节原件**（§1 哈希），L07 侧在分叉后又各自演进过。因此本角度的全部差异 =
**L07 单边后改造 vs L12 原样继承的 L08/L09 快照**，没有一处是「L12 另写了一套内核」。

## 0 覆盖与底数

| 文件 | L07 行 | L12 行 | keep07 | keep12 | 我的判定 |
|---|---:|---:|---:|---:|---|
| `bump_spine_iter.rs` | 155 | 148 | 1.000 | 0.828 | E1：模块清单 + 导览重写；代码仅 3 处增项（`mod typeclass` / `DeclEntry` 别名 / bench 负载） |
| `machine.rs` | 2007 | 2724 | 0.917 | 0.746 | E2/E3/E4 混合，逐函数分解见 §3 |
| `eval.rs` | 516 | 514 | 0.995 | 0.968 | E1 骨架 + 1 处 E3（§2、§7） |
| `quote.rs` | 673 | 665 | 0.987 | 0.993 | E1 骨架 + 1 处 E3 |
| `rename.rs` | 923 | 837 | 0.921 | 0.969 | **E3：迭代化少了一层**（§4） |
| `spine.rs` | 210 | 198 | 0.965 | 0.991 | E1：`clear()` 内联搬位（§7-E1-1） |
| `env.rs` | 130 | 131 | 1.000 | 1.000 | **E0**：token 全同，仅注释差异 |
| `bench_src.rs` | 118 | 164 | 1.000 | 0.943 | **E4**：+`struct_src`/`natadd_src` 基准负载 |

## 1 硬事实：L12 的内核文件自 L08/L09 起逐字节冻结

sha256 前 10 位（同值 = 一字未改；差异首次出现的层加粗）：

| 文件 | L07 | L08 | L09 | L10 | L11 | L12 | 冻结起点 |
|---|---|---|---|---|---|---|---|
| `eval.rs` | d8af59a13b | e6c2d5ce4a | **8c6bbd4cfc** | 8c6bbd4cfc | 8c6bbd4cfc | 8c6bbd4cfc | **L09** |
| `quote.rs` | 3a62fe6bbe | b05311da6e | **d7fb9fd0e9** | d7fb9fd0e9 | d7fb9fd0e9 | d7fb9fd0e9 | **L09** |
| `rename.rs` | 3353cb95bd | cf7d7dd76e | **0060c3230a** | 0060c3230a | 0060c3230a | 0060c3230a | **L09** |
| `spine.rs` | da79a7c8a6 | **d8d6d15c83** | d8d6d15c83 | d8d6d15c83 | d8d6d15c83 | d8d6d15c83 | **L08** |
| `env.rs` | 6630c61a44 | **7519415ee4** | 7519415ee4 | 7519415ee4 | 7519415ee4 | 7519415ee4 | **L08** |
| `syntax.rs`（孪生） | 463ef8bee9 | fc72e06384 | **319a996b94** | 319a996b94 | 319a996b94 | 319a996b94 | **L09** |
| `machine.rs` | e4eb9944e4 | af33abf320 | 0771e36a38 | 24bc5e2d8c | 4cab0e320d | b7655aecd3 | 每层都改 |

⇒ 8 个文件里 **6 个原样继承**，只有 `machine.rs` 与根聚合逐层重建。`git log -1` 在 L12 路径上显示
`73d68cf2`(11-17)，是因为 L12 的**目录**在该提交新建，不代表内容被重写——内容哈希证明相反。

## 2 (b) 迭代化骨架：真同源，不是「同名不同物」

1. **同一套状态机**：`eval_iter` 的 `W` 变体与 `vals/icits` 双栈、`W::ChainWrap` 头计数、`vapp1` 分派
   两侧同名同序（`src/L07_sum_type/bump_spine_iter/eval.rs:227` 一带 / `src/L12_canonical/bump_spine_iter/eval.rs:222` 一带）。
   `quote_iter` 同为任务栈 + `QJob::{Q,Apply1,Lam1,EvalQ,ChainRun}`，`rename_iter` 同为 `RJob` 任务栈 +
   `done/popped/done_icits` 三缓冲（`L07 rename.rs:281 / L12 rename.rs:261`）。
2. **签名逐参同序**：`eval_iter(bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env, tm)`
   两侧完全一致（`L07 eval.rs:443-456` / `L12 eval.rs:514-527`），`quote_iter` 同。
3. **同名不同物的反证**：`L12 eval.rs:222` 与 `L07 eval.rs:227` 都做同一件事——把 `Tm::Prim` 求值成卡住头，
   差别只在**取实参的方式**（§7-E3-1），不是不同职责。
4. **文本差异量**：`eval.rs` 仅 27 插 / 29 删、`quote.rs` 19 插 / 27 删，约一半是 `use` 重排与注释；
   `machine.rs` 里 `prime_round`(217t)、`new_binder`(72t)、`force_v`(35t) 六层 token 完全相同，`check` 仅 438→439 t。

## 3 (a) `machine.rs` +4,956 token 加在哪：三块，不是重写

按函数取 token 数，跨 6 层同表（只列有变化的；`—` = 该层不存在）：

| 函数 | L07 | L08 | L09 | L10 | L11 | L12 | 首次出现层 / 性质 |
|---|---:|---:|---:|---:|---:|---:|---|
| `trait_wrap` | — | — | — | 254 | 254 | **290** | L10 → E4（本章 trait 增量） |
| `solve_trait_ref` | — | — | — | 179 | 179 | **214** | L10 → E4（L12 自己 +35） |
| `solve_multi_trait_ref` | — | — | — | 85 | 85 | 85 | L10 → E4 |
| `infer_decl` | 550 | 554 | 616 | **1140** | 1140 | 1135 | L10 +524 = trait 求解落点（E4） |
| `fresh_meta` | 118 | 118 | 118 | **166** | 166 | 166 | L10 +48（trait meta，E4） |
| `check_universe` | — | — | **382** | 382 | 382 | 382 | L09 → E4（Type N 宇宙） |
| `ty_precheck` | 83 | 83 | **—** | — | — | — | L09 被 `check_universe` 取代（能力更强） |
| `check_ty` | 112 | 112 | **22** | 22 | 22 | 22 | L09 缩到 1/5（同上） |
| `infer_expr` | 1057 | **1165** | 1174 | 1233 | 1233 | 1233 | L08 +108 / L09 +9 / L10 +59 |
| `subst_cxt` | 197 | **100** | 100 | 100 | 100 | 100 | L08 −97（责任拆分，见 §7-E1-2） |
| `wrap_names`/`restore_names` | — | **63/19** | 63/19 | 63/19 | 63/19 | 63/19 | L08 新增，承接 §7-E1-2 |
| `unify_spec`→`unify_with` | 94 | **96** | 96 | 96 | 96 | 96 | L08 改名 + 独立工作栈（E1-3） |

**答案**：(a) 的 +4,956 不是「把 L07 既有内核重写一遍」。它分解为
① **L10 的 typeclass 章增量 ≈ 1,111 t**：三个 `solve_*`/`trait_wrap` + `infer_decl` 的两个新分支
`Decl::{TraitDecl,ImplDecl}`（`L12 machine.rs:2027 / :2088`，`v_to_val` 在 `:2150/:2164`）+ `fresh_meta`；
② **L09 的宇宙检查 ≈ +209 t 净增**：`check_universe` 382 换掉 `ty_precheck` 83 与 `check_ty` 的 90；
③ **L08 的零碎 ≈ +112 t**：name trail 82、`infer_expr` +108、`decl_insert` +19、`subst_cxt` −97。
**L12 自己（11-17，相对 L11）在 machine.rs 只动 +71 t**：`trait_wrap` +36、`solve_trait_ref` +35、`infer_decl` −5，
与附录 A 的「L11→L12 = 0.9858」一致。

## 4 (c) `rename.rs` −541 token：L12 比 L07 **更不迭代**

`rename_iter` 384 行 → 314 行（fn 体内）是唯一实质差异。方向不是「L07 的优化被删」，而是
**L07 在 `fb89bb00`(09-19) 又做了一层「深值任务化」（README §7.6），L12 没有这一层**：

| 值形态 | L07 做法 | L12 做法 |
|---|---|---|
| `XCell::Obj` 头链实参 / 裸 `XCell::Obj` | `RJob::ObjSpineFold`（`L07 rename.rs:386`，收口 `:593`）/ `RJob::ObjWrap` | 直接递归（`L12 rename.rs:355`、裸值 `:430`） |
| `XCell::Sum` 参数 | `RJob::SumBuild`（`L07 rename.rs:485`，收口 `:609`） | 逐参递归（`L12 rename.rs:443/:447`） |
| `XCell::SumCase` | `RJob::SumCaseBuild` | 逐字段递归（`L12 rename.rs:469/:475`） |

L07 自己的注释写明动机：`头链内层是深值时不再按值深度递归`（`L07 rename.rs:384-385` 一带）。
**可观察后果**：深嵌套 Sum/Obj 值在 L12 上按值深度占原生栈，L07 只占堆——同一份深值输入，
L12 可能栈溢出而 L07 不会。L07 还带守护测试 `deep_value_iterative_under_default_stack`（L12 无对位）。

**反证（任务假设不成立的部分）**：`occ`（occurs/scope 守卫）与「原位 lift」**没有被删**——
`occ: Option<u32>` 与 `if occ == Some(m) { return None }` 两侧同址（`L07 rename.rs:293 / :690`，`L12 rename.rs:273 / :600`），
`// lift：binder 槽 (cod → dom)` 亦同；L12 的 `occ` 行数反而更多（25 vs 19），因为它走递归路径。

## 5 (d) 根聚合 `VSub` 6→0 / `subst_cxt` 1→0 / `SpecSolve` 5→2：文档漂移，职责没搬走

| 位置 | `VSub` | `subst_cxt` | `SpecSolve` | 说明 |
|---|---:|---:|---:|---|
| 根聚合 `bump_spine_iter.rs` | 6 / **0** | 1 / **0** | 5 / **2** | 只剩 `pub(crate) use` 与模块导览提到 |
| `subst.rs` | 9 / 8 | 0 / 0 | 4 / 4 | σ 定义本体，未动 |
| `force.rs` | 20 / 17 | 1 / 1 | 0 / 0 | `frcs`/`frcs_env` 仍在 |
| `machine.rs` | 4 / 3 | 3 / **5** | 3 / 3 | L12 反而多（`wrap_names` 注释 + 新调用点） |

⇒ **不是模块重组，也不是职责搬走**：σ 载体在子模块里**两版几乎等量**（`wrap_sub` 36/36、`SubstV` 44/44、
`VSUB_REGS` 6/6）。丢的是**根聚合的叙述**：L07 讲「模式特化 = 显式替换」（`L07 bump_spine_iter.rs:50-55`），
L12 同一位置讲的是**更旧的**「模式特化事实表 `pm_defs`/`pm_solvable`/`pm_mark`/`pm_restore`」
（`L12 bump_spine_iter.rs:44-47`），并加了一句「以下为 L07 增量机制的原始说明（保留备查）」（`L12 :33`）。
核过账：`pm_solvable` 在 L12 **为 0**，`pm_mark`/`pm_restore` **两版都为 0** —— 这段导览描述了三个不存在的机制。
同处另有两处差异：L12 不再导出 `PendingCons`（`L07 :152` / `L12 :144-148` 无，该类型自 L08 已删），
并新增 `pub(crate) use prim::DeclEntryF as DeclEntry` 兼容别名（`L12 :137-138`，E4）。

## 6 (e) 谁更旧：L07 孪生的**内容**更新，L12 的**目录**更新

| 事实 | 锚点 |
|---|---|
| L07 孪生最后内容提交 **2026-11-16**（`c6c0e892`），此前 11-14 / 11-10×2 / 11-08 / 11-01 / 10-31×3 | `git log -- src/L07_sum_type/bump_spine_iter/` |
| 其中 `77be5d06`(11-10) = "drop Prim construction in builtins"，是 L07 eval/quote 的最后一笔 | `L07 eval.rs:227` / `L07 quote.rs:305` |
| L08 孪生在 **09-15** 从 L07 分叉（`efa47b9c` 同步显式替换精化），09-23 才拆目录（`08bfc7cf`） | `git log --diff-filter=A -- src/L08_product_type/bump_spine_iter/eval.rs` |
| L07 的三项 backlog（`SIMPL_CACHE` / §7.6 任务化 / 零元卡住头）全在 **09-19 `fb89bb00`** 落地 = 分叉之后 | `git log -S` 三条命中同一 commit |
| L12 的 `eval/quote/rename/syntax` = L09 原件，`spine/env` = L08 原件 | §1 哈希表 |
| L12 根聚合自述「2026-09-23 拆分」（`L12 :68`），L07 自述「2026-09-19 拆分」（`L07 :77`） | 文件头注释 |

**判断**：**L07 更旧的是「层号」，更新的是「内核内容」；L12 相反。** 提交时间上 L12 孪生最后一次触碰
（11-17）晚于 L07 的 09-19，但那一次只重建了 `machine.rs` 等 11 个文件，`eval/quote/rename/spine/env`
是**原样搬过来的 L08/L09 旧件**。所以「L12 是更新的一支」只在**目录/章体**意义上成立；这 5 个内核文件的内容上 L12 落后 L07 约两个月（09-15/09-19 快照 vs 11-16）。`[推断]` L12 的内核快照点可定位到
L07 孪生 **09-15 前后**：09-15 的显式替换精化已同步（`VSub` 全套在），而 09-19 的三项 backlog 一项都没有。

## 7 分级总表

**E0 / E1（等价，已确认）**

| # | 项 | 锚点 | 为什么等价 |
|---|---|---|---|
| E0-1 | `env.rs` 全文 | `L07 env.rs:1-130 / L12 env.rs:1-131` | token 748/748，差异仅注释措辞；`align_of` 四条断言全同 |
| E1-1 | `Spine::clear()` 内联搬位 | `L07 spine.rs:36-47` + `L07 machine.rs:196` / `L12 machine.rs:209` | 同一句 `self.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES)`；字段本就 `pub(super)`（`L12 spine.rs:31-33`），调用点同在 `clear_round` |
| E1-2 | `subst_cxt` 拆成自由函数 + `wrap_names`/`restore_names` | `L07 machine.rs:664-744` / `L12 machine.rs:2510-2547` + `:231-254` | L07 一个方法做 env+types+name_map；L12 拆三件但**调用点同址成对**：`L07 compiler.rs:193` / `L12 compiler.rs:191+194+212`。env 侧 L12 复用 `frcs_env`（`L12 force.rs:715`），L07 在方法体内联同一逻辑（`L07 machine.rs:695-705`） |
| E1-3 | `unify_spec` → `unify_with` | `L07 machine.rs:568-614` / `L12 machine.rs:663-713` | 形参逐一同序（含 `spec: Option<&mut SpecSolve>`），仅改名 + 换独立栈 |
| E1-4 | `pending` 由 cons 链改切片 | `L07 quote.rs:404` / `L12 quote.rs:396`；`L07 rename.rs:552` / `L12 rename.rs:534` | 应用序不变（`pending_to_vec` 的恢复序 == L12 的天然序）；`PendingCons` 自 L08 已删 |

**E3（落后：L07 有、L12 没有或更旧）**

| # | 项 | 锚点 | 可观察后果 |
|---|---|---|---|
| E3-1 | **`Tm::Prim` 零元卡住头退回 env 全槽收集** | `L07 eval.rs:225-231`（自述「旧实现把 env 全槽收集进 spine」）/ `L12 eval.rs:220-230`（`:223 let n = env_len(env)`） | L12 的 `Prim` 值携带现场 env 全部槽；quoted `Prim` 在另一 env 下重求值会捕获无关槽，spine 长度与 η 展开形状失真。方向由 L07 自身注释钉死（它把 env 版称作「旧实现」） |
| E3-2 | **深值任务化缺失**（§4） | `L07 rename.rs:386/:485/:593/:609` / `L12 rename.rs:355/:430/:443/:469` | 深 Sum/Obj 值走原生栈 → L12 有栈溢出风险，L07 只有堆 |
| E3-3 | **`simpl_decl` 旁路缓存缺失** | `L07 subst.rs:471-502` + 失效点 `L07 machine.rs:200 / :1781` / `L12 subst.rs:409`（无缓存）+ `L12 machine.rs:202-214`（无失效调用） | 每个卡住 match 分支都重算整张简化 decl 表；纯性能，无正确性差异（无缓存反而没有悬垂风险） |
| E3-4 | **`pending` cons 头插改整段拷贝** | `L07 force.rs:56-68`（「cons 头插 O(1)（切片版整段…）」）/ `L12 force.rs:55-63`（`with_capacity(len+1)`+`extend_from_slice`+`alloc_slice_fill_iter`） | 卡住 match 吸收 k 个实参从 O(k) 变 O(k²) 拷贝；与 E1-4 是一体两面（force.rs 属 02 分册，交叉引用） |
| E3-5 | 根聚合导览描述已不存在的机制 | `L12 bump_spine_iter.rs:44-47` vs `L07 :50-55` | 文档级：`pm_solvable`/`pm_mark`/`pm_restore` 在 L12 计数 0/0/0，误导读者把 L12 当 pm_defs 版本 |

**E4（L12 单边，不算「共有部分」的差异，列出以免误算）**

| # | 项 | 锚点 |
|---|---|---|
| E4-1 | 三工作栈拆分 + 入口 `clear()`（L08 引入） | `L12 machine.rs:151-155` + `:513/:561-563/:692-693`（L07 只有一份 `machine.rs:153 workbuf`） |
| E4-2 | `Tm::U(u32)` 宇宙层级（L09）+ `check_universe` 382 t（取代 L07 的 `ty_precheck` 83 t） | `L12 eval.rs:206 / L12 machine.rs:961`；`L07 eval.rs:209 / L07 machine.rs:945` |
| E4-3 | trait 三函数 + `tstate` + `Decl::{TraitDecl,ImplDecl}` 分支 | `L12 machine.rs:1558/1678/1715/165/2027/2088`（L07 全无） |
| E4-4 | `bench_src` 的 `struct_src`/`natadd_src`；`DeclEntry` 兼容别名 | `L12 bench_src.rs:131/:154`；`L12 bump_spine_iter.rs:137-138` |

## 8 本角度的「共有部分」边界

MAP §9 三条件（同角色 + 同位置 + 两侧都在用）下孪生内核全部满足，`bump_spine_iter` 的 `Tycker`/`run_fast` 仍是唯一入口（`L12 bump_spine_iter.rs:128`）。但**两条都不被门禁覆盖**：`Cargo.toml` 无 `default` feature、
`l12-twin` 默认关；LSP 默认孪生引擎是 **L13 而不是 L12**（`src/lib.rs:262` 用 `L13_namespace::bump_spine_iter`，
`:274` 明写 "Default: the LSP runs on the twin"）⇒ E3-1..E3-4 这类退化没有任何测试会报警。

## 一脉相承评级

**中偏强** —— 判定为「同一台 NbE 机器」（骨架逐字同源、6/8 文件逐字节继承、主循环 token 相同），
但 L07 在分叉后（09-19 起）有 4 项单边优化未跟过来，属「同一实现的不同时间快照」，不是「两份实现」。

## Top-3 差异

1. **E3** `Tm::Prim` 零元卡住头被退回 env 全槽收集（quote→eval 跨 env 保真性丢失）—— `src/L07_sum_type/bump_spine_iter/eval.rs:227` / `src/L12_canonical/bump_spine_iter/eval.rs:222-230`
2. **E3** `rename_iter` 深值任务化（§7.6）在 L12 缺失，深 Sum/Obj 值走原生栈递归—— `src/L07_sum_type/bump_spine_iter/rename.rs:386,485` / `src/L12_canonical/bump_spine_iter/rename.rs:355,443,469`
3. **E3** `simpl_decl` 旁路缓存（`SIMPL_CACHE` + 轮界/写点失效）在 L12 完全缺失，`clear_round` 也无失效调用—— `src/L07_sum_type/bump_spine_iter/subst.rs:471` + `machine.rs:200,1781` / `src/L12_canonical/bump_spine_iter/machine.rs:202-214`
