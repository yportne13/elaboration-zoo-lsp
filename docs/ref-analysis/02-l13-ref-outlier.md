# 02 · L12 参考版 → L13 参考版：整条链唯一的离群点

> **角度 02 / 只分析参考版。** 孪生自 2026-11-24 起被 `#[cfg(feature = "lNN-twin")]` 硬封印（本轮 Lead 实施，
> 见 [00-hard-seal.md](00-hard-seal.md)），默认构建不再编译 L06–L12 的孪生引擎；**只有 L13 孪生还在编译**（LSP 默认引擎，
> `src/lib.rs:274`）。故本册对象 = L12_canonical 顶层 ↔ L13_namespace 顶层，孪生子模块只在需要时作旁证。
> 方法：自写 Rust token 扫描器（跳过注释/字符串/字符字面量/生命周期）+ **6-token shingle + 标识符归一化**，
> 逐同路径文件算保留率；SHA-256 判逐字节；`git log -S` 判"有意/无意"。**未构建**，锚点 `src/LNN_xxx/yyy.rs:LINE`，HEAD `8f4287ae`。
> 分级沿用 MAP §8 的 E0–E4；**E3 再分"E3-未跟进"（链上后来加的加固没回灌）与"E3-冻结"（已封印路径，只登记）**。

## 0 口径自查：先复现 Lead 的三个数，再往下用

我的扫描器与 Lead 同口径（6-token shingle + 标识符归一化）。三个数与 Lead 报告值的差 ≤0.0012，可直接互相引用：

| 转换 | 我复算（归一化） | Lead 报告 | 判读 |
|---|---:|---:|---|
| L07 → L12（全 31 同路径文件） | **0.9236** | 0.9237 | 一致；L12 未引入新增损失 |
| L07 → L13（全 27 同路径文件） | **0.6737** | 0.6725 | 一致；断点在此 |
| **L12 → L13（全 30 同路径文件）** | **0.7002** | 0.7002 | 完全一致 |
| L12 ref → L13 ref（**15 个非孪生文件**） | **0.6810** | — | 本册主指标 |

**关键量级**：L12 ref 81.3k token → L13 ref 217.8k token（**2.68×**）。其中同路径 15 文件 72.3k → 163.9k（2.27×）；
L13 另有 28 个 ref 文件 +53.9k（其中约 43.4k / 80% 是测试与探针），L12 另有 2 个（`struct_eq.rs` `tests.rs`，+9.0k）。
⇒ **"离群"不是"改坏了 15 个文件"，而是"L13 多长了一个产品层、同时内核换了载体"。**

## 1 逐模块对照（L12 ref → L13 ref，按 keep 升序）

| 文件 | L12 tok | L13 tok | Δ | keep→ | 判读 | 档 |
|---|---:|---:|---:|---:|---|---|
| `surface.rs` | 1,491 | 820 | −671 | 0.292 | L13 是**上游原版**（`surface.rs:1-6` 自述），L12 把 `span_union/raw_span` 搬了进来 | E1 |
| `pattern_match.rs` | 4,927 | 5,229 | +302 | 0.489 | 同一套逐臂下钻，诊断通道全换（§3 #5） | E2 |
| `cxt.rs` | 2,995 | 12,084 | +9,089 | 0.489 | 精化载体 + 名字世界双双重写（§2） | **E2** |
| `pretty.rs` | 2,177 | 6,779 | +4,602 | 0.562 | L13 自带 Nat/Sum/结构/HDL 渲染 + `decl_shapes` | E4 |
| `unification.rs` | 10,510 | 10,571 | **+61** | 0.566 | **同算法、24 个同名函数**；只换了穿参（`decl: &Decls` → `cxt: &Cxt`）与臂上多 Nat/prim | E2 |
| `syntax.rs`（顶层） | 229 | 719 | +490 | 0.598 | L12 六层逐字节冻结过；L13 侧是 `vspan` 家族的等价替代 | E1 |
| `mod.rs` | 17,227 | 45,274 | +28,047 | 0.599 | 产品层宿主（HDL/namespace/prelude/LSP 采集都在这）+ 尾部内联测试 | E4 |
| `parser/syntax.rs` | 975 | 3,658 | +2,683 | 0.692 | `Raw` 加 `Nat(Span<u64>)` / `Raw::Tm` / `is_trait`（`parser/syntax.rs:104/:118`） | E4 |
| `elaboration.rs` | 10,167 | 32,290 | +22,123 | 0.733 | 53 个 fn vs L12 的 14 个（§2） | E4 |
| `raw_pretty.rs` | 1,194 | 2,408 | +1,214 | 0.851 | L12 自 L09 逐字节冻结，L13 侧独立演进 | E2 |
| `parser/mod.rs` | 12,308 | 33,579 | +21,271 | 0.854 | HDL/struct/derive/namespace 语法都在这里脱糖 | E4 |
| `shape.rs` | 692 | 941 | +249 | 0.862 | L12 自 L09 冻结；L13 版多 HDL 形状 | E1/E4 |
| `typeclass.rs` | 2,662 | 4,303 | +1,641 | 0.912 | 同一 `Synth` 求解器；L13 多两阶段 class | E1/E4 |
| `parser/lex.rs` | 2,319 | 2,713 | +394 | 0.963 | 同一 lexer，多 HDL 关键字 | E1 |
| `parser/macros.rs` | 2,446 | 2,502 | **+56** | 0.984 | 宏系统两版几乎同一份 | **E0/E1** |

**L12 独有**：`struct_eq.rs`（2,778 tok，**L13 无**）、`tests.rs`（6,197；L13 拆成 `legacy_tests.rs` 14,241 + 22 个专题测试文件）。
**L13 独有（28 个 ref 文件）**：`canonical.rs`（iddfs/search，`:9`）、`eval_budget.rs`（`:72` `NAT_CHAIN_LIMIT`）、
`parser/derive.rs`（8,105 tok，`#[derive(Show/Bundle/HdlEnum)]`，`:18-24`）、`debug_test.rs`、`struct_refine_probe.rs`
+ 20 个 HDL/prelude/module/termination 测试文件。

## 2 (a) 哪些是产品层新增，哪些是同一机制被重写

**产品层新增（E4，占 diff 的绝大部分 token）**：

| 域 | L12 ref | L13 ref | 锚点 |
|---|---:|---:|---|
| 命名空间（package/import/全限定 decl 键/`Type.mk`/inherent） | 3 处 | **302 处** | `cxt.rs:332-334`（`namespace`/`namespace_prefix`/`namespaces` 三字段进 Cxt）；`elaboration.rs:44` `prefix_decl_name`、`:1401` `infer_after_prefix` |
| HDL / Verilog（脱糖在 parser、发射在 `src/emit.rs`） | 3 处 | **463 处** | `mod.rs:514` `PrimFunc`；`parser/derive.rs:18-24`；7 个 HDL/prelude 测试文件 |
| LSP 观察面（六通道 + 单通道入口 + 查询口径） | 契约在、采集点少 | 完整 | `surface.rs:21-34`；`elaboration.rs:2870` `push_hover_decl`；`surface.rs:90-104` 单通道 API |
| prelude 库（CORE/HDL/SHOW 三段 + 池化） | 0 | 41 处 | `mod.rs:4264/4283/4312`、`:4180` `PRELUDE_POOL` |
| termination / eval_budget（协作式中止 + Nat 链护栏） | 1 处 | 19 处 | `elaboration.rs:172` `check_def_termination`；`eval_budget.rs:77` `guard_nat_chain` |
| 原生 Nat（`Val::Nat(u64)`） | 无 | 有 | `mod.rs:906-925` |
| prim 挂 decl 表（无 `Tm::Prim`/`Val::Prim`） | `Val::Prim` | 无 | `mod.rs:514` + `decl_prim` |
| class 两阶段 / BindingName 隐参 / def replay / Call·OpCall | 部分 | 全 | `mod.rs:1449` `PrintlnJob`、`cxt.rs:338` `binding_name` |
| canonical iddfs/search（quickfix retry） | **明确不移植** | 有 | `canonical.rs:9`；不移植理由见提交 `73d68cf2` |

**同一机制被重写（E2，四条主脉）**：

| 机制 | L12 参考版 | L13 参考版 | 后果 | 档 |
|---|---|---|---|---|
| 精化载体 | σ 显式替换：`Subst`/`Val::VSub`/`subst_cxt` | `update_cxt` + `refresh`（**eager**：逐槽 quote+eval 重建 env） | 见 §3 #1 | **E2** |
| 名字世界 | `names: Rc<RefCell<NameState>>` + `name_mark` 轨迹回滚（`cxt.rs:153-155`） | `src_names: Rc<BiMap<SmolStr,Lvl,(Span,VTy)>>` 持久化 COW（`cxt.rs:330`） | L12 每次访问前必须 unwind；L13 每次 bind 走 `Rc::make_mut` | **E2** |
| 合一入口的穿参 | `unify(decl, l, cxt, t: Val, u: Val, spec)`（`unification.rs:989`） | `unify(l, cxt, t: &Rc<Val>, u: &Rc<Val>, fuel)`（`unification.rs:1055`） | L13 必须拿到 `Cxt` 才能精化；L12 只读 `Decls` | E2 |
| 值的形状 | `Val` 15 变体（`mod.rs:254-292`），`Match` 带 4 字段（`:285` 有 `pending`） | `Val` 14 变体（`mod.rs:906-941`），`Match` 只 3 字段（`:938`） | 见 §5 | **E2** |
| 诊断通道 | `Result<(), Error>` 单条拼接中文 | `Result<Vec<Warning>, Vec<Error>>` 中英混合 + 逐错 span（`pattern_match.rs:486-493`） | 见 §3 #5 | **E2** |

## 3 (b) 五条已知断点逐条核实

| # | 断点 | L12 锚点 | L13 锚点 | 机制差异 | 可观察后果 | 档 |
|---|---|---|---|---|---|---|
| 1 | **精化载体** | `cxt.rs:453-479` `subst_cxt`（env 槽包 `VSub`，槽位布局不动，惰性） | `cxt.rs:1327-1370` `update_cxt` + `:1372-1396` `refresh`（env 槽**当场**换成值，`fresh_val` = quote∘eval 逐槽重算） | L12：解不落地，读点 `frcs` 推开；L13：解立刻落地，代价 O(depth) 逐槽重求值 + `locals.update_by_cxt` | L13 在嵌套 match 里付出多次全槽重建；L12 在每个读点付 `VSub` 解包。**L13 另有一条硬约束**：探测 cxt 的层级不能超出上下文，否则 `lvl2ix` panic（`pattern_match.rs:179-180`） | **E2** |
| 2 | **无 `struct_eq`** | `struct_eq.rs:1-18`（卡住 match 自比较快路径）、`:36` `EQ_BUDGET=20_000`；调用点 `unification.rs:1247-1267` | 无该文件；`unification.rs:1250-1261` **L13 自述**"L13 无 σ 结构快路径，慢路径一律计数" | L12 先比纯结构再决定要不要逐分支重求值；L13 一律进入慢路径 | 卡住 match 自比较在 L13 更慢、更易烧穿预算；预算耗尽档也不同（#4）。**known-diff #8 已登记** | **E3-未跟进** |
| 3 | **无 `VSpan`** | `mod.rs:198-204`（`VSpan(Rc<Span<String>>)`）+ `:237-251`（`PartialEq` 只比名字） | 无 `VSpan`；直接用 `Span<SmolStr>`（`mod.rs:909-915`） | **不是丢信息，是换配方**：L12 用 `Rc<Span<String>>` 省克隆分配（`mod.rs:198-202` 自述继承 L09 2026-11-13 实验 B），L13 用 `SmolStr` 达到同一目的 | 两者都为"Val 克隆不分配 String"；L12 多一层 indirection。L12 的"`PartialEq` 只比名字"**是 `struct_eq` 的配套件**——没有 `struct_eq` 就不需要它 | **E1**（纠偏 MAP） |
| 4 | **覆盖义务方向** | `pattern_match.rs:402-411`：`k != Absurd` ⇒ 可达 ⇒ **要求覆盖**（注释明写"反方向会让非穷尽 match 被静默接受"） | `pattern_match.rs:208-219`：`Fuel→Matched`（要求覆盖）、`Absurd→Unreachable`、`Undecided→Undecided`（**不计义务**，`:20-21`/`:654-660` 重申） | 同一三态、**相反的产品口径** | 索引方程判不出的缺失构造子在 L13 被静默放过、L12 报缺构造子。L13 的理由：`update_cxt` 下臂上下文能解出探测期解不出的方程（`pattern_match.rs:210-215`） | **E2（L13 有意）** |
| 5 | **诊断：中文 Error → 英文 Warning** | `Error(String, span)`；`pattern_match.rs:187/:202/:254/:268/:317` 全中文；`:329` 一条 `Err` 拼接（`join("\n")`，只带首条 span） | `Warning` 枚举（`pattern_match.rs:31-47`）；`:53` `unreachable pattern: {}`（英文）、`:55` `match 不完整：缺少构造子 {}`（中文）；`elaboration.rs:1174-1189` 非空 warnings **仍转成 Err**，其余错误进 `accumulated_errors` | **语言与通道都变了，但严重性没变**（两版最终都拒） | 用户可见差 = ①不可达臂文案从"分支不可达：模式 succ(n) 被…遮蔽"退成 `unreachable pattern: n`，且 `Warning::Unreachable(Raw)` 装的是**臂体**不是模式（`pattern_match.rs:539`）→ 指错对象（known-diff #5 已记）；②L13 多错误各带 span 成为独立诊断，L12 只有一条多行 | **E2** |

> **纠偏**：`compare-l07-l13-shared` 与机制矩阵把这几条记成"L13 整块缺失"。逐条核完的正确说法是：
> **#1 #4 #5 是机制分叉（L13 有意保留自己的载体/口径），#2 是链上加固未回灌（L13 落后），#3 根本不是缺失。**

## 4 (c) 有意 / 无意：`git log -S` 的证据链

| 日期 | 提交 | 对"有意/无意"的意义 |
|---|---|---|
| 2026-05-11 | `f1392ad4 feat(L13): init namespace` | `update_cxt` 与 `Warning` 枚举**从 L13 出生就在**（`git log -S 'update_cxt' -- src/L13_namespace/cxt.rs` 最早一条即它） |
| 2026-05-14 | `9cb9aa01 feat(pm): better err msg` | 英文 `unreachable pattern` 是**明确的"改文案"提交**，非顺手 |
| 2026-08-29 | `c6b8ee2e feat(L07): 重写和类型与依赖模式匹配` | 中文 `分支不可达` 始于 L07 重写，**晚于 L13 三个半月** |
| 2026-09-15 | `ad08c633 refactor(L07): 精化机制从 pm_defs 事实表改为显式替换` | **σ 是链上后加的**；L13 从未参与（`git log -S 'subst_cxt' -- src/L13_namespace/` = 空） |
| 2026-09-18 | `448775c2 perf(L13): 匹配编译器逐臂下钻移植` | L13 的 `pattern_match` 是**从 L12 决策树移植**回来的——两版互为来源，不是单向 |
| 2026-09-23 | `c199d210 refactor(L13): 拆分目录模块` | 正文写明"**本层无 σ/struct_eq 分节**"，与 `bump_spine_iter.rs:171-175` 同款声明 → 缺这两项当时已是台账事实 |
| 2026-11-13 | `437136b0 perf(l07,l08): inherit VSpan ... from L09` | `VSpan` 源自 L09 的性能实验，专门服务链侧 |
| 2026-11-17 | `73d68cf2 refactor(L12): 重建 canonical 层` | 中文"无法判定"三档由**这次重建引入**；同提交明确"SmolStr 化不采用""canonical iddfs 不移植" |
| 2026-11-18 | `246a4e33` + `docs/l13-rebase-decision-2026-11-17.md` 决策 1 | **官方决策**：L13 不 copy-forward，"产品层独立维护" |
| 2026-11-20 | `0ef38783 refactor(L13): P1.2 覆盖探测三态` | 三态从 L12 回灌进 L13，但**保留 L13 口径**（"只有 Matched 要求覆盖"） |

**一行一句判定**：

| 断点 | 判定 | 依据 |
|---|---|---|
| `update_cxt`+`refresh`（无 σ） | **有意**：L13 从未引入 σ，11-17 决策明确不迁 | `c199d210` 正文、`bump_spine_iter.rs:171`、决策文件 |
| 无 `struct_eq` | **有意不移植 + 无意欠账各半**：缺它是台账内的，但"慢路径一律计数"的代价从未评估 | `bump_spine_iter.rs:172`、`unification.rs:1254` 自述 |
| 无 `VSpan` | **有意**（换 `SmolStr` 达成同目标）；MAP 记成"缺失"是误判 | `mod.rs:198-202` vs `mod.rs:909-915` |
| 覆盖义务方向 | **有意**：写进提交正文与代码注释两处 | `0ef38783` 正文、`pattern_match.rs:20-21/:208-219` |
| 诊断 Error→Warning | **通道有意、文案顺手退化**：通道是 L13 原设计；把 `Warning::Unreachable` 装成臂体、丢掉 `pat.pretty()` 属顺手退化 | `f1392ad4`/`9cb9aa01` vs `pattern_match.rs:539/:53` |

## 5 反向差异：L12 有、L13 没有的加固（本轮新发现，均不在 known-diff 表里）

| 项 | L12 | L13 | 后果 | 档 |
|---|---|---|---|---|
| **卡住 match 应用的实参** | `Val::Match(.., pending: Vec<(Val,Icit)>)`（`mod.rs:285`），`v_app` 只 push（`:1494-1497`）；注释明写项层 splice 会让实参自由变量**引用错上下文**（`:281-285`） | `Val::Match` 无 `pending`（`mod.rs:938`）；`v_app` **把实参 quote 进每个分支体**（`mod.rs:3196-3204`，`l = Lvl(env.len())`） | `[推断]` 实参引用外层变量且模式绑定数 >0 时产生 de Bruijn 捕获；L13 自己的注释（`:3191-3193`）称"splice 保义"，与 L12 的结论直接冲突 | **E3-未跟进（潜在正确性）** |
| 传递 occurs check | `occurs_transitive`（`unification.rs:1084/:1106`，P1 加固，挡两跳环） | 全仓 0 处；`mod.rs:1467` 自述"**solve 无跨 meta occurs check**"，靠 `UNIFY_FUEL` 兜底（`mod.rs:2879`） | `[推断]` 跨 meta 环得不到 occurs 失败，而是烧穿 fuel → 报成 `can't unify` | **E3-未跟进** |
| 深值迭代防护族 | `force_deep`(16) / `val_mentions_lvl`(34) / `rename_deep`+`frame_assemble`(12) / `InlineStack`(6) / `simpl_decl_cached`(5) | 全部 0–1 处 | L13 走另一族（`Drop for Tm`/`Val`、`quote_nat_chain`、`eval_budget`）：**不是没有防护，是没这一族** | E3-未跟进（性能/栈深） |
| `pretty` 深项上限 | `MAX_DEPTH = 1024` | HEAD 无 | 深值递归显示爆栈 | E3-未跟进（**工作区已修**） |
| `TYPORT_UNIFY_FUEL` | 有 | HEAD 无 | 基准无法放大 fuel | E3-未跟进（**工作区已修**） |

> **工作区状态（重要）**：HEAD `8f4287ae` 之后，Lead 已在**未提交**改动里补了三项：
> `pretty.rs` 的 `MAX_DEPTH=1024`、`mod.rs` 的 `unify_fuel_budget()`、`pattern_match.rs` 的
> `Warning::Unmatched(SmolStr)`（把 3000 字符的定长通配见证改成 `match 不完整：缺少构造子 {ctor}`）。
> 本表前两行的"HEAD 无"在提交后会失效，**别把它们再排进待办**。
> 另：`tests/namespace_tests` 的 2 例失败（`mod.rs:2756` 越界）已在 [00-hard-seal.md](00-hard-seal.md) §4 隔离，与本册无关。

## 结论摘要

L12→L13 不是改坏，是**产品层膨胀 2.7× + 内核换载体**：15 个同路径文件里只有 `unification.rs` 与
`pattern_match.rs` 还算同一机制。五条已知断点：**三条有意**（σ 载体、`VSpan`、覆盖义务方向）、
**一条有意但漏了代价评估**（`struct_eq`）、**一条通道有意而文案顺手退化**（诊断）。
反向看 L12 有 5 项加固未回灌，**「卡住 match 的实参」是唯一潜在正确性问题**，不在任何已有台账里。

## 要改的东西 Top-3

1. **给 L13 的卡住 match 补值层实参（修 `[推断]` 的 de Bruijn 捕获）**：`src/L13_namespace/mod.rs:3196-3204`
   现在把实参 quote 进每个分支体；改成 L12 的做法（`src/L12_canonical/mod.rs:285` 的 `pending: Vec<(Val,Icit)>`
   + `:1494-1497` 只 push、归约时在值层应用）。最小复现：`(match x { cons(a,b) => a }) y`（`x` 为 rigid、
   `y` 引用外层变量）——先写一个断言 `y` 不被 `a` 捕获的测试，再改结构。**Top-1，因为只有它可能给出错答案。**
2. **把 `occurs_transitive` 回灌到 L13 的 `solve_with_pren`**（`src/L13_namespace/unification.rs:616` 起，
   对照 `src/L12_canonical/unification.rs:1077-1088` 的"两跳环"守卫），或至少在 `mod.rs:1467` 旁把
   "靠 fuel 兜底"升级成 known-diff 条目 + 一个 `?m := ?n` / `?n := succ ?m` 的回归钉。
3. **给覆盖义务方向补一条跨层语义用例，把 L13 的口径钉死**（known-diff #7 目前"待定"）：
   L13 `src/L13_namespace/pattern_match.rs:208-219`（Undecided 不计义务）vs L12
   `src/L12_canonical/pattern_match.rs:402-411`（Undecided 要求覆盖）。用例要能在两版跑出**不同判定**
   （L13 接受 / L12 报缺构造子），否则这条"已知分叉"永远没人敢改。
