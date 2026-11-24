# 06 · 名字世界 / 观察面 / typeclass 边界（mod.rs · surface.rs · syntax.rs · observe.rs · typeclass.rs）

> 范围：§5 分工表中 06 分册。归因口径按 MAP §10 / A.5——先问"差异首次出现在哪一层"，再决定写"L12 重写"还是"E3-继承"。
> 全部锚点为当前 HEAD `8f4287ae` 实测；`observe.rs` 实测 **351 行**（MAP §4 记 296 行，按 f6badca5 的 279 + 6f7e245e 的 72 推算应为 351，取实测值）。

## 0 一句话结论

名字世界与观察**契约**层是**一字未改的继承**（`cxt.rs` 自 L09 起逐字节同、`surface.rs` keep07=0.993、顶层 `syntax.rs` 六层逐字节同）；
本角度真正的缺口**只有一类**：L07 在 2026-11-21~23 单边长出来的观察面（`observe.rs` 19 项职责 + 5 个入口 + `prof` 探针），
L12 在 11-23 只回填了"渲染"这一层，没回填"采集 / 查询 / 通道"这三层。
**不是 L12 拆的，是 L07 后来长的、回填不全**——`git log -S` 全部指向 L07 单边提交。

## 1 文件级档位

| 条目 | 度量 | 结论 | 档 |
|---|---|---|---|
| 顶层 `syntax.rs` | `git diff --no-index` 空输出 | 逐字节同（六层） | **E0** |
| `surface.rs` 契约本体 | 12+/4-，改的 4 行全是 `Raw::U(_)`/`Raw::Sum(..,_)`/doc | 契约平移 | **E0/E1** |
| `cxt.rs`（名字世界） | L09–L12 SHA256 同；对 L07 只差 `Val::U`→`Val::U(0)` 9 处 | 裸名 flat map 原封不动 | **E0/E1** |
| `shape.rs` / `raw_pretty.rs` | L09==L12 同哈希；L07 不同哈希但 keep07=0.989/0.995 | 展示层平移 | **E1** |
| `mod.rs` | keep07=0.927 / keep12=0.960（唯一"对称"的大文件） | 删的是观察面与探针，不是机制 | **E1 + E3** |
| `observe.rs` | L12 无此文件 | 见 §2 | **E3** |
| `typeclass.rs` | 378 行（孪生 89 行），L10 起有 | 本章主题，不影响共有机制 | **E4** |

`mod.rs` 的对称性是本轮最容易被误读的数：keep07=0.927 与 keep12=0.960 几乎镜像，因为它的增（trait/Call）与删（观察面/prof）
在 token 量上互相抵消；逐条审查后**没有一条是 L07 语义机制被替换**（§5）。

## 2 (a) L07 `observe.rs` 19 项职责 → L12 承接表

L12 侧对每个函数名做了全目录递归 grep（含 `bump_spine_iter/`、`parser/`）。"部分"= 职责以**内联形式**存在、函数本体无对位。

| # | L07 `observe.rs` | L07 行 | L12 命中 | 承接 | L12 落点 / 说明 |
|---:|---|---:|---:|---|---|
| 1 | `hover_wanted` | 36 | 0 | 无 | `hover_query` 按偏移口径整层缺失（L12 `mod.rs` 无该字段） |
| 2 | `inlay_wanted` | 42 | 0 | 无 | 随 inlay 通道一起缺 |
| 3 | `render_val` | 47 | 0 | 无 | 引读管线被内联进 `elab:338-347` |
| 4 | `render_by_shape` | 59 | 2 | **有** | `L12 elaboration.rs:240`（整段搬移，`span_from_name` 内联） |
| 5 | `render_typ_pretty` | 115 | 0 | 无 | L12 用 `render_by_shape`+`quote` 手拼，且**丢掉 final 判定** |
| 6 | `tm_has_unsolved_meta` | 126 | 0 | 无 | 唯一消费者是 inlay/final，二者都没了 |
| 7 | `push_hover` | 182 | 0 | 无 | 局部名 hover 消失（def_span 从 `Locals` 回走的逻辑一并消失） |
| 8 | `push_hover_rendered` | 191 | 0 | 部分 | `L12 elab:350` 直 push，见 §3 |
| 9 | `push_hover_decl` | 199 | 0 | 部分 | `L12 elab:904-909` 内联，丢 final 判定与 query 闸 |
| 10 | `push_ctor_hover` | 214 | **1** | 无 | 唯一命中是 `L12 surface.rs:11` 的**过期注释**，不是代码 |
| 11 | `push_inlay_hint` | 229 | 0 | 无 | 洞型 inlay 缺失，见 §8 |
| 12 | `push_inlay_label` | 242 | 0 | 无 | 同上 |
| 13 | `push_println_span` | 250 | 0 | 无 | `println_spans` 通道无生产者 |
| 14 | `drain_check_issues` | 258 | 0 | 无 | `check_issue_lines`/`issue_drained` 均无 |
| 15 | `note_failed_decl` | 285 | 0 | 无 | `check_with_surface` 整条"遇错继续"驱动缺失 |
| 16 | `surface()` | 294 | 0 | 部分 | `L12 mod.rs:2219-2221` 只填 `hover` 一个字段 |
| 17 | `hover_entry_at` | 306 | 3 | **有** | `L12 surface.rs:45`（+ `hover_text_at:54`），契约级同源 |
| 18 | `local_binder_span` | 315 | 0 | 无 | 局部 binder 的 def_span 定位消失 |
| 19 | `peel_pi_collect` | 339 | 0 | 无 | `shape.rs:56` 有私有 `peel`，但不是同一职责（无 peeled 名字回流） |

**19 项中 2 项有承接、3 项部分承接、14 项无承接。** 但注意方向：缺失的 14 项全部服务于
"schema 级通道"（inlay / println / check-issue / completion / ctor / 局部名），而**渲染算法本体（`render_by_shape`、`shape.rs`、
`raw_pretty.rs`、`def_type_from_source`）全部在 L12 里**——`L12 elaboration.rs:339` 的 `def_type_from_source` 与 `:344` 的
`render_by_shape` 就是方案 3/4 的完整移植（对应 L07 `observe.rs:59`/`elaboration.rs:305-311`）。**血管移植了，末梢没接。**

## 3 (b) `push_hover_rendered` 在 L12 grep=0：漏移植还是刻意不做？

**判定：既不是 bug 式漏移植，也不是"刻意不做渲染"；是"移植时按最小模板裁剪，职责以裸 push 内联承接"。**

| 问题 | 证据 |
|---|---|
| L07 谁调它 | 唯一调用点 `L07 elaboration.rs:314`（`Decl::Def` 登记处，渲染串已由 `render_typ_pretty`/`raw_pretty` 算好）；定义在 `observe.rs:191` |
| L12 有对位渲染路径吗 | **有**。`L12 elaboration.rs:338-350`：源注解 `raw_pretty` → `render_by_shape` → `quote`+`pretty_tm`，三种都命中方案 3/4 |
| L12 的那一条 push 在哪 | `L12 elaboration.rs:350` `self.hover_table.push((name.to_span(), name.to_span(), s))` —— 裸 push，不经 helper |
| 丢了什么 | ① `hover_wanted` 的 `lsp_collect && hover_query.contains` 双闸（L12 只剩 `lsp_collect`，`L12 elab:331`）；② 采集口径从"按光标惰性"退化为"全量" |
| 为什么不算刻意不做 | 渲染路径完整存在，且 `tests/l12_lsp_surface.rs:39`、`:51` 两条断言**依赖**它的输出（`(n : Nat) → T n` / `(n: Nat) → T n`）。说"刻意不做渲染"与测试矛盾 |
| 真正的成因 | `2ad6b1b4`（11-23）对 L09/L10/L11/L12 打的是**同一份模板**（每层 `elaboration.rs` +88 行、`mod.rs` +44 行），模板里只有 2 个采集点；L07 的 `observe.rs` 从未被复制进 L08–L12 任何一层（全目录 `*.rs` 文件名检查：L08/L09/L10/L11/L12 均无 `observe.rs`；仅 L06 与 L07 有） |

⇒ 结论应写成 **E3（回填不完整）**，而不是"L12 删了 hover"。附带的可观察后果见 §7 末行的 E2（final 标记）。

## 4 (c) `typeclass.rs`（E4）有没有改坏 L07 的共有机制

`typeclass.rs`（`L12 typeclass.rs:1-6` 自述"Val 级重写、去 Typ 桥接"）本身是全新模块（ddbulp 式 Prolog 搜索：
`Assertion/Instance/GeneratorNode/ConsumerNode/Synth`，`typeclass.rs:17-102`）。它**没有改动** L07 的合一/结构相等/σ 机制，只做三件加法：

| 落点 | 性质 | 对 L07 代码的影响 | 档 |
|---|---|---|---|
| `mod.rs` 新增 4 字段 + `force_deep`/`take_trait_error` | 纯增 | 无 | E4 |
| `unification.rs:751-773` `solve_multi_trait`、`:780-815` `solve_trait` | **新函数** | 无 | E4 |
| `unification.rs:880/1152/1156` 三处在 flex 求解后追加 `solve_multi_trait` | 嵌入式钩子 | 非 trait 头时 `solve_trait` 立即 `Ok(None)`（`:788-790`），**无副作用** | E1 |
| `mod.rs:801-821` `fresh_meta` 顶部 `force` + trait 早返回 | **改写了 L07 已有函数**（L07 `mod.rs:853-857` 无此段） | 唯一的共有机理改动点 | E1（非 trait 路径）+ E4（trait 路径） |
| `parser/syntax.rs:109/118` `Decl::TraitDecl/ImplDecl` | 新 enum 分支 | 需要所有 `match Decl` 补臂 | E4 |

`fresh_meta` 那条是本节唯一需要留意的地方：L12 在创建 meta 前**无条件先 `force` 期望类型**（`mod.rs:808`），
于是 meta 类型存的是 WHNF 而非原样的 σ 包裹形态。对非 trait 的 Sum 头之外的类型，`force` 在 WHNF 上幂等、
后续 `quote/eval` 结果不变 ⇒ 判 E1；但"元变量类型被提前 WHNF 化"是否在某些 `VSub` 场景下改变 pruning 行为，**本轮 [未核实]**
（需要 02/03 的 σ 视角交叉验证）。

另需登记的边界：`typeclass.rs` 的 `val_match`/`vals_eq_ground`（`:127`/`:200`）是**求解器内部的单向一阶匹配**，
与 `unification.rs` 的 `eq`/`struct_eq.rs` **不共享代码**——同名易混，不能据此判"结构相等被改写"（MAP §6.6 的同名不同物陷阱）。

### 4.1 本角度涉及的 E4 清单（列出以免误算成"差异"）

| # | L12 单边新增 | 锚点 | 是否影响 L07 代码 |
|---:|---|---|---|
| 1 | `typeclass.rs` 378 行 + 孪生 `typeclass.rs` 89 行 | `L12 typeclass.rs:1-102` | 否（纯新模块） |
| 2 | `DeclTm::Trait` / `DeclTm::TraitImpl` | `L12 mod.rs:68-71` | 否（新 enum 分支，需补 `match DeclTm` 臂） |
| 3 | `Decl::TraitDecl` / `Decl::ImplDecl` | `L12 parser/syntax.rs:109/118` | 否（新 decl 形；`parser/syntax.rs` 因此与 L07 分家） |
| 4 | `Tm::Call` / `Val::Call` + 10 处透明臂 | `mod.rs:104-106`/`:284-285`；force `:1012`、frcs `:1105`、v_app `:1496`、eval `:1620`、quote `:1932`、`val_mentions_lvl` `:2082`、`tm_size_ref` `:2356`、`shift_tm` `:2551`、`Subst` `:379/451` | **否**：全是新增 match 臂，无 L07 旧臂被改 |
| 5 | `lookup_function_by_cases`（旧 L12 的 Call 显示外衣辅助，保留为死 API） | `mod.rs:2562-2563`（`#[allow(dead_code)]`） | 否 |
| 6 | `surface.rs:171-179` 为 `TraitDecl/ImplDecl` 补的 `failed_decl_names` 臂 | `L12 surface.rs:172` | 否——该函数在 L12 **无调用者**，属机械补 `match` 穷尽性 |

第 4 条值得留意：`L12 mod.rs:1964-1967` 明确写着"quote 不自动创建 Call"（因为孪生侧无 Call，自动包会造成 ref/twin 显示分叉），
所以 **Call 在 L12 是惰性节点**——本层没有任何代码路径会生成它，它只为 L13 产品层预留。这解释了为什么第 4 条没有可观察后果。

## 5 (d) `mod.rs` 被删的 7%（`git diff --no-index` 删除 252 行 / 新增 235 行）逐条

| # | 删除内容 | L07 锚点 | 首次出现在哪层 | 档 |
|---:|---|---|---|---|
| 1 | `observe.rs` 的职责载体：9 个 Infer 字段（`completion_table`/`inlay_hint_table`/`println_spans`/`check_issue_lines`/`issue_drained`/`failed_decls`/`hover_query`/`inlay_query`/`ctor_pretty`） | `mod.rs:742-771` | L07 11-21 单边新增；L08 起无 | **E3** |
| 2 | 5 个观察面入口 `run_with_surface_at`/`run_with_surface_query`/`check_with_surface`/`run_surface_impl`/`bench_check_nf_observe` | `mod.rs:2196/2205/2214/2255/2455` | 同上（`git log -S` 指向 `f6badca5`） | **E3** |
| 3 | `mod observe;` / `pub mod surface` 的旧排布 | `mod.rs:96-97` | 同上 | **E3** |
| 4 | `prof` 模块（8 个 AtomicU64 计数器 + enable/on/bump/reset/report） | `mod.rs:33-70` | L07 独有（`287e78ae`），L08 起无 | **E3** |
| 5 | 6 处 `prof::bump`（FORCE/VAPP/EVAL/QUOTE + UNIFY/UNIFY_SP） | `mod.rs:965/1467/1524/1649`、`unification.rs:748/903` | 同上 | **E3** |
| 6 | 模块头 doc（9 行"相对 L06 新增…"） | `mod.rs:1-11` | 每层重写 | E1 |
| 7 | `L07_DEBUG` / `L07_LOOP` 前缀 | `mod.rs:23-26`、`:2158-2161` | L08 起改 `L12_` | E1 |
| 8 | `DEMO_SRC` 的 `U` → `Type 0`、`l07_builtin_demo.txt` → `l12_builtin_demo.txt` | `mod.rs:2300-2375` | L09（Type N 宇宙） | E1 |
| 9 | `Val::U`/`Tm::U` 的旧形态（约 30 行；L12 侧 `Val::U(` 共 14 处 = 9 构造 `U(0)` + 2 搬运 + 3 通配） | 散布 | L09（`26c53eb7` args-preserving prim） | E1 |

**这 9 条里没有一条是"L07 的语义机制被替换"**：1-5 是 L07 单边新增设施的回填缺口（观察面/探针），
6-9 是链上游的机械改写（前缀、demo 文本、宇宙层级化）。`mod.rs` 的 0.927 因此是"**减法**"而非"改写"——
这一点与 `bump_spine_iter/struct_eq.rs`（0.527，真正的换实现）性质完全不同。
第 9 条为 E1 的理由：`Val::U` 的 `u32` 载荷在本文件内**只被搬运、不被比较**（构造恒 0：`:1284/1300/1324/1342/1388/1410/1428/1454/1829`；
搬运：`:1571`/`:1899`；通配：`:384/459/2110`）；层级是否在 `unification.rs` 侧参与比较属 03 分册。

## 6 (e) 名字世界：L12 仍是裸名 flat map + `ver`，没有限定键 / symbol_table / 四级查找

| 断言 | 锚点（两版） | 档 |
|---|---|---|
| 全局 decl 表 = `FxHashMap<SmolStr, Rc<DeclEntry>>` + `ver: u64`，**逐字段同** | `L07 cxt.rs:34-41` / `L12 cxt.rs:34-41`（SHA256 自 L09 同） | E0 |
| 读写走 `Deref/DerefMut` 到裸 map，键就是裸名 | `L07 cxt.rs:49-60` / `L12 cxt.rs:49-60` | E0 |
| `ver` 的唯一用途是 `simpl_decl` 的旁表缓存键（同 ver ⟹ 同实例），**不是名字版本/作用域代数** | `cxt.rs:27-32`（两版同文） | E0 |
| 限定键 `E.c` 只是 `format!("{}.{}", …)` 的**字符串键**，与裸名别名并列插入同一张 map | `L07 elab:481-486` / `L12 elab:930` | E1 |
| `symbol_table` / `import_map` 在 L07、L12 全目录 grep **均为 0**（对照组 L13 = 94 处） | — | E0 |
| 名字解析仍是"局部 `lookup_src` → 全局 `decl_get`"两级 | `L07 elab:567-581` / `L12 elab:912-919` | E1 |
| L12 自述与 namespace 分家 | `L12 mod.rs:8`"namespace 不在本次继承面内" | — |

⇒ **名字世界是本角度最强的正面证据**：它与 L12 的 chapter 增量（trait/Call）零耦合，
且与 L13 的"限定键 + symbol_table + import_map 四级查找"路线完全不同——L12 站在 L07 一侧，不是 L13 一侧。

## 7 已确认等价清单（不要误算成差异）

| 项 | 判定 | 理由 |
|---|---|---|
| 顶层 `syntax.rs` 228 tok | **E0** | diff 空输出；MAP A.3 六层同哈希 |
| `cxt.rs` 与 L07 的 9 处 `U(0)` | **E1** | 载荷不被读；语义等价 |
| `surface.rs` 的 `Raw::U(_)`/`Raw::Sum(..,_)` 补丁 | **E1** | 只为跟随 `parser/syntax.rs` 的形参增加，逻辑未变 |
| `render_by_shape` 搬家 | **E1** | `observe.rs:59-111` → `elab:240-292`，循环/Π 剥离/`head args` 合成逐行同构，仅内联 `span_from_name` |
| `Decl::Def` 登记处渲染 | **E1** | 方案 3+4 两种分支都在，输出与 L07 同（`tests/l12_lsp_surface.rs` 三条断言） |
| `inlay_label`/`failed_decl_names`/`split_issue_lines` 存在于 L12 | **E3（非差异来源）** | 三个 helper 在 L12 **无任何调用者**（`surface.rs:149/161/202` 仅定义）——契约在、生产者不在 |
| `unification.rs:1159-1162` 注释"L09–L12 仍未补" | **非差异** | 实测 `L12 unification.rs:1163` 已有 `(LiteralIntro(a), LiteralIntro(b)) if a.data == b.data` 臂；**注释过期**，代码不落后 |
| L12 `decl_pretty` 恒写 `fin = true` | **E2（不列 E3）** | 字段仍在（`mod.rs:724`），但使用处 `elab:904` 用 `Some((s, _))` 忽略标记，L07 `observe.rs:204` 用 `Some((s, true))` 才直取；后果：def 类型含未解 meta 时，L12 复用登记期串而 L07 在使用处重渲染 |

## 8 归因小结（对 MAP §10 的落点补充）

| 差异 | 首次出现层 | 之后 | 本分册结论 |
|---|---|---|---|
| 观察面通道 / 入口 / `prof` 大缺口 | **L07 自身**（11-21~23 四次单边提交） | L08 从未有；L09–L12 共用 11-23 的最小模板 | E3-回填不完整，不归 L12 |
| **洞型 inlay** | **L08 有 → L09 起无**（11-23 模板漏项） | L09–L12 一致 | 唯一"L12 比 L08 还少"的一条，E3 |
| `U`→`U(0)`、`Type N` | L09（`26c53eb7`） | L09–L12 冻结 | E1，链上游机械改写 |
| `TraitDecl/ImplDecl` / trait 钩子 | L10（`typeclass.rs` 引入）；L12 在 `73d68cf2` 重写为 Val 级 | — | E4 |

## 一脉相承评级

**强。** 名字世界（`cxt.rs:34-60`）与观察**契约**（`surface.rs`）是逐字节/近逐字节继承，顶层 `syntax.rs` 六层同哈希，
本章唯一大增量 `typeclass.rs` 是纯加法且不改 L07 语义；缺口集中在 L07 事后新增的观察面末梢（14/19 项无承接），
性质是"回填不全"而非"机制分叉"——所以本角度判**强**，但要标注"观察面是共有的**减配**子集，不是等价物"。

## Top-3 差异

1. **E3** 观察面末梢缺失：L07 `observe.rs` 19 项职责中 14 项无对位、2 项仅部分承接，L12 只剩 2 个采集点 —— `L07 observe.rs:33-351` / `L12 elaboration.rs:329-351`、`:896-911`。
2. **E3** 洞型 inlay 在 L08 有、L09–L12 无（唯一"L12 少于 L08"项）—— `L08 elaboration.rs:141-171`（`self.inlay_hint.push`） / L12 全目录 `inlay_hint` 计数 0（`L12 surface.rs:33` 只剩字段）。
3. **E2** `decl_pretty` 的 final 标记退化：L07 按 `fin` 决定"直取缓存 vs 使用处重渲染"，L12 恒写 `true` 且使用处忽略标记 —— `L07 observe.rs:204`、`L07 elaboration.rs:313-314` / `L12 elaboration.rs:349`、`:904-905`。
