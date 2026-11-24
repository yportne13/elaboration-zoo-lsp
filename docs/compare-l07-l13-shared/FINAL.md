# L07 ⟷ L13「共有部分」实现差异 · 最终报告

> 团队作业：Lead + 7 名分析员，7 个角度（`01`–`07`），HEAD `911628b3`（2026-11-24），只读、未构建。
> 底稿与口径见 [MAP.md](MAP.md)，机械度量见 [fn-matrix.tsv](fn-matrix.tsv)；分角度证据见各分册。
> 用户原始预期：**L13 与 L07 的共有部分应当一脉相承。**

## 0 结论摘要

**「一脉相承」在三个层次上同时成立又不成立，必须拆开说：**

| 层次 | 判定 | 一句话 |
|---|---|---|
| **配方层**（算法骨架/设计纪律/显示启发式） | **成立（强）** | 逐臂下钻匹配器、两段式嵌套覆盖、值级可达探测、U2 短路、arena + 打包 tag、迭代化 eval/quote/rename、`MATCH_CMP_BUDGET=64`/`UNIFY_FUEL=4096` —— 在 L13 里都能逐段对上，多处注释直接写「L07 同款 / port L07 a78daec7」 |
| **实现层**（同一段代码被搬过去） | **一半成立（中）** | 叶子/工具模块是真继承（`parser/lex` 89%、`env` 98%、`raw_pretty` 79%、`shape` 76%、`eval` 86%、`quote` 78%、`rename` 76%、合一算法内核 0.6–0.9）；中枢模块被同名重写（`cxt` 19%、`force` 25%`*`、`pattern_match` 22%、`pretty` 34%、`mod` 26%） |
| **语义前提层**（决定结果的机制） | **不成立（断）** | 精化载体 **σ 显式替换 ⟷ `update_cxt`+refresh** 是两套机制；名字世界从裸键 flat map 换成"限定键 + 别名表 + 四级查找"；值表示按各自参考版重造（`Prim`/`VSub` ⟷ `Nat`/`Call`/`U(u32)`）；诊断通道从中文 Error 变成英文 Warning + 结构见证；卡住 match 的应用机制两侧互斥（pending 链 vs 逐分支 splice），**且两侧注释互相指认对方"错"** |

**七个角度的独立评级**（都指向同一结论，但强弱不同）：

| 角度 | 评级 | 断在哪里 |
|---|---|---|
| 01 NbE 孪生内核 | 中 | 骨架同源；**确定性燃料池整块消失**、σ/VSub 族 408 行（占 L07 `force.rs` 49%）在 L13 一行没有 |
| 02 合一/结构相等 | 中 | 算法内核同源；**`struct_eq` 整模块在 L13 消失**（L07–L12 都有），卡住 match 快路径随之消失 |
| 03 上下文/精化载体 | **断** | **σ ⟷ `update_cxt`**：`update_cxt` 只在 L13 存在，`subst_cxt` 只在 L07–L12 存在，零交集 |
| 04 模式匹配编译 | 中 | 骨架/预算纪律同源；**Undecided 的覆盖义务方向相反**（L07 要求覆盖、L13 不计义务），诊断面整体重写 |
| 05 名字世界/表面/解析 | 中 | `lex` 真继承；名字世界换基（键与查找路径都变）；`LspSurface` 同型只对结构、不对载荷 |
| 06 观察面/渲染 | 中偏弱 | 契约方法逐字节同（body_sim 1.000）；**hover 文案已分家**、`pretty` 丢 `MAX_DEPTH` 保护 |
| 07 行为证据/门禁 | 中 | 语义内核有跨层门禁互锁（prim 5 条）；**可观察层（文本/诊断/重定义）零门禁** |

\* `force.rs` 的 25% 是"少一半（σ 族）+ 多一层（memo/taint）"，不是"换了一套"——见 §1 度量陷阱。

**一句话**：这不是"L13 从 L07 长出来然后漂移"，而是**链在 L13 之下重建过、L13 明确拒绝重定基、之后双方按需互抄**。因此"共有部分"里既有逐字节的遗产，也有两套并行的语义机器，且**断代方向经常与直觉相反**。

## 1 「共有部分」怎么界定，以及三个度量陷阱

L07 有 32 个 `.rs`、L13 有 62 个，**同路径的只有 27 个**；L07 独占 5 个（`struct_eq.rs`/`observe.rs`/`tests.rs`/孪生 `struct_eq.rs`/`subst.rs`），L13 独占 30 余个（`canonical`/`typeclass`/`eval_budget`/`parser/derive`/`parser/macros`/孪生 `observe`/`compact`/`termination` 等）。
本报告只把**同角色 + 同位置 + 两侧在用**的算"共有部分"；L13 独有特性（命名空间/HDL/prelude/typeclass/termination/LSP）一律计入 E4，不混进差异清单。

**陷阱 1：文件级保留率会被"文件里的测试尾巴"稀释。** L13 `mod.rs` 自 5166 行起是成批内联测试程序（L07 把同类测试放在独立 `tests.rs` 65KB），所以 26% 里有相当一部分不是"核心重写"。
**陷阱 2：低保留率可能是"职责搬家"而非"实现消失"。** `surface.rs` 只有 26%，但 6 个字段同序、5 个方法 body_sim 全 1.000——真正走掉的是 AST span 折叠族 7 个函数（搬到 `Raw::to_span()`，且**有损**）。`observe.rs` 顶层"整个文件缺失"，但 13 项职责里 12 项在 L13 有承接点，唯一真缺失是 `push_hover_rendered`。
**陷阱 3：同名函数会被误配。** Lead 的 `fn-matrix.tsv` 里 `quote_iter` 0.005、`machine::unify` 0.012、`infer_decl` 0.001 都是"同名不同物"（本体被拆成 `quote_go`/`unify_catch`）；真配对实测是 quote 77.9%、eval 86.0%、`force↔force_inner` 33.6%。**引用任何保留率前先看它是不是真配对。**

## 2 血缘真相：不是一条链，而是一条被重建过的链 + 一个拒绝重定基的产品层

| 时间 | 事件 | 对"共有部分"的影响 |
|---|---|---|
| 2026-08-29 `c6b8ee2e` | L07 已是逐臂下钻匹配器 | 匹配算法源头在 L07 |
| 2026-09-05 `67273831` | **L07 把 parser 对齐 L13 设计**（resilient 组合子移植） | **解析器血缘方向是 L13→L07**，不是反过来 |
| 2026-09-15 `ad08c633` | **L07 单方面把精化载体从 pm_defs 事实表换成 σ 显式替换**，L13 没跟 | 精化载体的共同祖先停在 9 月之前 |
| 2026-09-18/19 `448775c2` 等 | L09–L13 把匹配编译器从决策树**移植**成逐臂（源自 L07） | 反方向的又一次对齐 |
| 2026-09-21 `8c53542f`+`a2989b81` | σ 移植进 L13 孪生，只留在分支 `perf/l13-twin-sigma`，**对 HEAD 非祖先** | 「载体统一」被试过一次并被弃用（唯一第一手证据） |
| 2026-11-10~13 `d411debe`/`65d4512a`/`437136b0` | L07 拿到 trail/NameState、Locals Rc（借用 L13 参考版）、VSpan（借用 L09） | L07 变成"更新的那一支" |
| 2026-11-17 `b6f4ca34`→`73d68cf2` | **L09–L12 按"上一章思路 + 本章增量"整条重建** | 链（除 L13）换了新底座 |
| 2026-11-17 `l13-rebase-decision` | **明确决策：本轮不对 L13 做 copy-forward 重建**；L13 = 产品层，独立维护；停止声称"继承 L05–L12 全部机制" | 这就解释了今天的一切 |
| 2026-11-18~20 `9e37627b`/`52b44535`/`b36270d4`/`0ef38783` | L13 的 **P1 选择性对齐**（合一三档诊断 + 卡住 match 预算 + flex_flex 反向重试 + prim/decl 调度 + 覆盖探测三态） | 部分机制被手工拉回一致 |
| 2026-11-22/23 `7a68abc7`/`80f7cbc1` | **两侧孪生封印**（`lNN-twin` feature 默认关，parity 套件编成空） | ref↔twin 的自动比对停了 |
| 2026-11-23 `6f7e245e`⟷`c824c43a`、`d12a8ed2`⟷`a68605ff` | 观察面**成对提交**：形状认回、源码注解渲染 | 这是"人工按需移植"，不是 copy-forward：L07 `shape.rs` +120 行 / L13 +147 行，L13 有 3 处必需改写 |

⇒ 所以"共有部分"不是一条连续分支的残留，而是**三个来源的叠加**：① 9 月之前共同祖先的遗产（lex/pretty/合一半成品）；② 9–11 月双向回灌的补丁（U2、形状认回、prim 判等、预算）；③ 各自独立演进的机制（σ、`update_cxt`、名字世界、值表示、诊断）。

## 3 共有部分四档判定（总表）

**E0/E1 真继承**（同一份代码或仅机械改写）：
`parser/lex.rs` 的 `string/ws`（body_sim 1.00，89%/95%）、`bump_spine_iter/env.rs`（98%）、arena+打包 tag 编码（逐字相同：L07 `syntax.rs:114-121` / L13 `syntax.rs:117-124`）、`spine/rename/quote/eval` 的迭代内核（72–86%）、`raw_pretty.go`（79%，且 L07–L12 之间逐字节同）、`shape.rs`（76%，成对提交真对齐）、合一算法内核（`intersect_go` 0.89/`invert` 0.88/`prune_vflex_go` 0.79/`intersect` 0.78/`unify_no_arm` 0.77）、`LspSurface` 三方法（1.000）、`MATCH_CMP_BUDGET=64`+`UNIFY_FUEL=4096`（同值同点）、逐臂下钻 + 两段式嵌套覆盖 + U2 + 值级探测。

**E2 换基/重写**（同角色、不同机制、有可观察后果）：
精化载体、名字世界、值表示、`unify` 入口契约、卡住 match 应用机制、覆盖义务方向、诊断通道、`pretty` 写入策略、hover 文案路由、`check_issues`/`println_spans`/`failed_decls` 载荷语义、确定性燃料 → 墙钟看门狗、`Cxt` 名字表（trail 惰性回滚 ⟷ `Rc<BiMap>` 克隆插入）。

**E3 L07 有、L13 无**（真正的"丢失"，共 7 项）：
`struct_eq` 模块（+孪生，含 `EQ_BUDGET=20_000` 与 Match/Match 快路径）、σ 族（`Subst/VSub/frcs/SpecSolve/wrap_sub`、孪生 `subst.rs`）、`VSpan`（**L06–L12 每层 37–39 处，L13 为 0**）、`occurs_transitive`、`quote_deep/rename_deep/meta_expanding` 环守卫、`pretty` 的 `MAX_DEPTH=1024`（L12 有、L13 无）、`TYPORT_UNIFY_FUEL` 环境覆盖与 `decl_cache`/`trail`。

**E4 L13 单边新增**（不算差异，但会污染"同源"读数）：
`update_cxt`/`refresh` + 反向索引 `get_by_key2_mut`、原生 `Val::Nat`、`U(u32)` 层级、`Call/OpCall`、prim 挂 decl（`PrimFunc`）、命名空间三字段、`eval_budget`/`termination`、`canonical` 的消费点、`parser/{derive,macros}`、LSP 消费者、孪生 `observe/compact/termination/typeclass`。

## 4 十条最重的差异

| # | 差异 | L07 | L13 | 后果 | 档 |
|---|---|---|---|---|---|
| 1 | **精化载体** | `Val::VSub`+`frcs`+`wrap_sub`+`SpecSolve`，臂上下文 `cxt_arm.subst_cxt(&self.sub)` `mod.rs:336,1092`、`pattern_match.rs:227` | `update_cxt`+`refresh`+`fresh_val`，`check_pm_final` 直接返回精化 Cxt `cxt.rs:1327,1372`、`pattern_match.rs:591`、`elaboration.rs:679-688` | 同一 GADT/索引方程走两条路径；`subst_cxt` 在 L07–L12 各 13–16 处、L13 为 0，`update_cxt` 只在 L13（36 处） | **E2** |
| 2 | **`struct_eq` 消失** | `struct_eq.rs`(346 行)+孪生(399 行)，Match/Match 先试结构快路径 `unification.rs:1143-1157` | 无该 mod（`mod.rs` 0 命中），该臂第一行就是预算 `unification.rs:1250-1261` | 自比较从"结构相同⇒相等"退化为"重求值 64 次⇒判不出"：**L07 能证的等式 L13 报不可信**（保守方向安全，但成功率不同） | **E3** |
| 3 | **名字世界** | 裸名 flat map `Decls{FxHashMap<SmolStr,Rc<DeclEntry>>+ver}` `cxt.rs:34-49` | 限定键 + `symbol_table`/`import_map` + 四级查找（exact>import>前缀>唯一后缀）`mod.rs:452,1515,1525`、`elaboration.rs:3032-3066` | 遮蔽/歧义语义不同：L13 的裸名可能因回退命中别处；`def` 撞构造子 L07 报 `redefine succ`、**L13 直接接受（且无测试）** | **E2** |
| 4 | **覆盖义务方向相反** | Undecided/Fuel 一律按**可达**，要求覆盖 `pattern_match.rs:402-411` | Fuel 按可达、Absurd 不可达、**Undecided 不计义务** `:203-214,653-659` | 同一"卡住索引方程"程序：L07 拒绝、L13 静默接受（L13 是自觉的产品口径，注释自述载体约束） | **E2** |
| 5 | **确定性燃料池消失** | `Fuel=Cell<u32>` 共享池 + `burn` 遍布 force/unify，耗尽写进错误文案 `prim.rs:62`、`machine.rs:197,620-627` | force **没有 fuel 参数**，unify 每对透传 `u32`、顶层写死 100，终止靠墙钟 `eval_budget` `force.rs:532-540`、`machine.rs:1570`、`eval.rs:288` | 预算从确定性降级点变成机器相关看门狗；`(fuel exhausted)` 文案在 L13 不存在 | **E2** |
| 6 | **卡住 match 的应用** | pending cons 链，O(1) 头插 `syntax.rs:265-270`、`force.rs:60-69` | 每次应用把实参 quote 成项 splice 进每个分支，O(分支数) `force.rs:157-191` | 两侧注释互相指认对方"错/不符参考版"（`force.rs:63-64` ⟷ `force.rs:158`）——"共有部分已不是同一份"最直接的文本证据 | **E2** |
| 7 | **诊断面** | 单条中文 Error + 模式 span：`match 不完整：缺少构造子 succ` / `分支不可达：…被前面的通配臂遮蔽` `pattern_match.rs:325-330` | `Vec<Warning>` 英文 + 错误落 scrutinee span：`non-exhaustive pattern: succ(_,…)` / `unreachable pattern: n` `:31-53`、`elaboration.rs:1174-1177`；缺失臂在 L07 是 **error**、L13 是 **Warning** | 跨版本断言不可平移；L13 缺失模式消息在 HEAD 是**单行 3116 字符 / 2005 个下划线**（独立缺陷，建议单开 issue） | **E2** |
| 8 | **观察面契约"同型不同物"** | 6 字段同序 + 3 查询方法（1.000）；`check_issues:(decl 下标, 行)`、`println_spans` 真串、`failed_decls` 有序 Vec `surface.rs:26-41` | 同 6 字段同序；但 `check_issues:Vec<String>`（丢 decl 下标）、`println_spans` **恒空**、`failed_decls:HashSet`（顺序不定）`surface.rs:21-34,133,143-148` | "与 L07–L12 同型"这句：**结构为真、载荷为假**；L07 的 span 折叠族 7 函数在 L13 全无（改 `Raw::to_span()`，`Match` 只取末臂、`Sum` 只取末构造子，**有损**） | **E2/E3** |
| 9 | **L13 缺 L07–L12 的加固/优化** | `VSpan` 35 处、`MAX_DEPTH=1024`、`occurs_transitive`、`decl_cache`、`trail`、深值守卫、`TYPORT_UNIFY_FUEL` 覆盖 | 全部为 0（`VSpan` 在 L06–L12 是 39/39/37/38/38/38） | L13 在**每一项上都是旧的一支**；深 Pi/深 Match 的 `pretty` 可爆栈，两跳 occurs 环只能靠 fuel 兜底 | **E3** |
| 10 | **门禁真空** | 孪生被封印：`l07-twin` 默认关，`l07_fast_parity` 编成空，无其他套件比 L07 ref↔twin | `l13_fast_parity` 同样编成空；但 `twin_engine_tests` 仍在跑，且 L13 孪生是 **LSP 默认引擎**（`lib.rs:297-302`） | 7 个 `lNN_fast_parity` 被 `#![cfg(feature="lNN-twin")]` 关死、CI/`gate_l13.sh` 不传 `--features` ⇒ 层内逐字节 parity 跑 0 例；**L07↔L13 跨层只剩 `prim_identity_cross_layer` 的 5 条断言** | **E3** |

## 5 行为证据（不是读码推断，是可复现的）

1. **旧审计矩阵**（`.audit/raw-correctness/probe-matrix.tsv`，39 程序 × 7 层，基线 11-16）：L07 与 L13 **30/39 判定或文本不同**；其中绝大多数是 L13 的语言面增量（struct/trait/macro/package 在 L07 是 `parse error`）。**只看纯共有核心（CORE 组 11 个程序）：7 个两侧都接受但输出文本不同**——Nat 十进制 vs succ 链、`List[A]::cons(…)` vs `List::cons(…)`、`x => x + 1` vs `x => Nat::succ(x)`、`string_concat hello world` vs `y => string_concat hello world y`；另有 1 个错误类别不同（`coverage` vs `other`）。
2. **本轮 HEAD 实跑**（`realbench.exe`/`l13bench.exe`，13 个纯共有语料）：7/13 判定一致；差异集中在诊断文案（见 §4 #7）、`def` 撞构造子（L13 接受）、裸构造子/泛型构造子值（`l13bench` 报 BOTH-FAILED，入口与 realbench 不同，标记 `[未核实]`）。
3. **唯一真·跨层门禁**：`tests/prim_identity_cross_layer.rs:88-105` 对 7 层同 5 条 prim 判等断言——这是"一脉相承"最硬的正面证据。
4. **旧结论已作废**：`.audit/correctness.md` 的 R1（L07 prim 假阴 / L09–L10 panic）与 R2（L12 丢索引投影）分别被 `c6c0e892`、`26c53eb7`、`73d68cf2` 修掉；**引用旧审计必须改成"曾发生、已回灌"**。

## 6 风险清单

**高**：
- **可观察层零门禁**：pretty 文本、诊断文案、`redefine` 规则都在无门禁区，且 L13 侧对 `redefine`/裸构造子值/泛型构造子值**完全没有测试**（445 个 L13 `#[test]` 全部绕开）。
- **L13 缺失模式诊断 3116 字符/2005 下划线**：用户可见垃圾，且无长度上界断言。
- **L13 缺 `pretty` 深项保护**（`MAX_DEPTH` 只在 L07–L12）：深 Pi/深 Match 的显示路径可爆栈。
- **σ→`update_cxt` 的语义后果未被系统性测试**：`check_pm_final` 用 `unwrap_or(cxt)` **吞掉**最后一次特化方程失败（`elaboration.rs:687`），L07 同位置是 `Walk::Unreachable` 报错。

**中**：
- **L13 孪生 `FORCE_MEMO`+`taint`** 是 L07 完全没有的一层（作者自己记了两条走过的弯路），只在 LSP 级测试里被间接覆盖。
- **L13 参考版与 L13 孪生自身不一致**：`clear_observation_tables` 清 6 张表（含 `println_spans`）vs 参考版刻意不清；`globals_src` 基准负载在 L13 孪生丢失。
- **`pattern_match` 臂体写死 `infer.check::<false>`**（`pattern_match.rs:617`），而顶层可按 `const CANONICAL` 二选一 ⇒ 同一表达式臂内/臂外可能走不同合一入口 `[推断]`。

**低但会误导人**：
- 文档/代码不一致 3 处：`L13 mod.rs:1474` 说预算耗尽记 `Undecided`（代码记 `Fuel`）；`bump_spine_iter.rs:172` 说"结构比较由 unify 快路径承担"（实际只有位相等 + memo）；`L07 README` 的 `PM_FUEL` 早已不存在（`grep -i pm_fuel` 两章均 0）。
- 上一轮文档的过期结论：MAP/DELTA 说"L09 起删 `struct_eq`"——**实际 L09–L12 都保留，L13 才是删除点**；"L07 是 parser/surface 的上游"——**实际 parser 是 L07 向 L13 对齐、surface 家族是 L06–L12 共有而 L13 独缺 span 折叠**；"L07 加固回灌 L13"——**literal equality 臂实际是 L13→L07**。

## 7 如果要"一脉相承"，三条路线

1. **产品层维护模式（现状，推荐继续）**：承认 L13 是产品层（2026-11-17 决策已写明），维护"L07⟷L13 差异表"而不是强求同构；把 §4 的十条登记成 known-diff 并给可观察层加跨层门禁。成本：天级。
2. **大爆炸重定基**：以新 L07–L12 为基线重建 L13 核心，再逐块移植 LSP/HDL/prelude。风险集中在 613 个层内测试与 LSP 产品行为；工作量周级。**注意**：`rebase/l13-on-l12` 分支上 L13 的 `cxt.rs` 仍是 `update_cxt=1/subst_cxt=0` —— 重定基也没换载体。
3. **抽公共 crate**：把 `parser/lex`、`pretty/raw_pretty`、`surface` 契约、bench harness 抽成公共 crate，各层 feature 化。前提是先统一值表示（否则 `pretty`/`surface` 的载荷类型对不上），成本最高、收益最持久。

**最低成本七件事（1–2 天，收益/风险比最高）**：
1. 修 L13 缺失模式诊断的 arity + 加长度上界断言（独立缺陷）。
2. 把 L07 的纯防护项回灌 L13 或**明确登记为不移植**：`occurs_transitive`、`pretty MAX_DEPTH`、`VSpan`、`TYPORT_UNIFY_FUEL`、`decl_cache`。
3. 把 `lNN-twin` 的封印从"永久关闭"改成 **nightly CI job**（`--features lNN-twin`），否则"封印"会变成"遗忘"。
4. 新增一条**跨层文本门禁**：把 7 个 CORE 程序的 Ok 输出与诊断文案钉进 `tests/`（现在没有工具能导出跨层 Ok 文本——`realbench --layer` 不收 L13、`l07bench` 无 `--file`）。
5. 把 `error vs Warning` 的等级差、`redefine` 规则差登记进跨层 known-diff 表（现在 `audit_crosslayer_probe` **不做断言**、永不会红）。
6. 补 `surface.rs` 的三处载荷语义差到契约文档（现有 `docs/l13-raw-pretty-2026-11-23.md` §11.3 只写了 2 处）。
7. 修三处文档/代码不一致（`mod.rs:1474`、`bump_spine_iter.rs:172`、L07 README 的 `PM_FUEL`）。

## 8 附录

**分册**：`01-kernel-nbe.md`（孪生 NbE）、`02-unify.md`（合一/结构相等）、`03-cxt-refine.md`（上下文/精化载体）、`04-match.md`（模式匹配）、`05-names-parser.md`（名字世界/表面/解析）、`06-observe-pretty.md`（观察面/渲染）、`07-evidence.md`（行为证据/门禁）。

**复算**：`tmp/l07l13_similarity2.tsv`（文件级 shingle 保留率）、`docs/compare-l07-l13-shared/fn-matrix.tsv`（同名函数体相似度）、`tmp/lead-fnmatrix.tsv`（同源）。
**关键命令**：`git diff --no-index --numstat <L07 文件> <L13 文件>`；`git log -S <机制名> -- src/L13_namespace`（判断某机制是否进过 L13）。

**口径声明**：全部结论基于静态读码 + 已编译二进制的有限实跑（`realbench.exe`/`l13bench.exe`），**未执行 `cargo test`**；凡"运行时会怎样"均标 `[推断]`/`[未核实]`。锚点行号对应 HEAD `911628b3`，重建章节后会漂移。
