# 07 · 解析与渲染：`parser/{mod,lex,syntax,macros}`、`pretty`、`raw_pretty`

> 角度：解析与渲染。对象 `src/L07_sum_type/**` ⟷ `src/L12_canonical/**`，HEAD `8f4287ae`。
> 口径：MAP §7（keep07 = L07 侧 6-token shingle 原样出现在 L12 的比例）、§8 分级、§10 附录 A（漂移考古）。
> 全程只读：未跑 `cargo build/check/test`；只用 `git diff --no-index`、内容哈希、`Select-String`、读文件。
> **归因口径按 §10 A.5 执行：凡差异先问"首次出现于哪一层"，不写"L12 重写"。**

## 0 一句话结论

**L12 的解析器 = L11 的解析器，逐字节；L11 的解析器 = L07 的 14 个递归下降规则函数（token 流一字未改）外面套了一层宏拦截壳。**
本角度内 **L12 这一层（`73d68cf2`）对解析的实质改动为零**：`parser/lex.rs`、`parser/syntax.rs`、`parser/macros.rs` 三文件**逐字节等于 L11**；
`parser/mod.rs` 的 L11→L12 差异是 **22 增 / 22 删**，内容全部是 `T!` 宏里 20 条 `$crate::L11_macro` → `::L12_canonical` 路径改名 + 2 条注释改成 `l12 blackbox`。
`pretty.rs` 的 L11→L12 差异是 **15 行纯新增**（`Tm::Call` 渲染臂）。**没有一处 L07 已保留段落被 L12 层改写。**

## 1 逐文件台账（tok/keep 取自 `tmp/l07l12-similarity.tsv`；层属与冻结区间为本次内容哈希自算）

| 文件 | L07 行 | L12 行 | tok 07→12 | keep07 | keep12 | 差异首次出现 | 冻结区间 | 判读 |
|---|---:|---:|---|---:|---:|---|---|---|
| `parser/mod.rs` | 592 | 1486 | 5065→12632 | 0.977 | 0.476 | 每层都变；**最大一跳在 L10→L11（+826/-37）** | 无 | E4-继承 + E1 |
| `parser/lex.rs` | 306 | 349 | 1976→2334 | 1.000 | 0.972 | L08/L09/L10/L11 各有小改 | **L11 起（L11≡L12）** | E4-继承，L12 零改 |
| `parser/syntax.rs` | 116 | 134 | 811→974 | 0.979 | 0.906 | **L09**（`Raw::U(u32)`/`Sum`+u32）、**L10**（`TraitDecl`/`ImplDecl`） | **L10 起（L10≡L11≡L12）** | E4-继承 + E2（U 载荷） |
| `parser/macros.rs` | 无 | 354 | — | — | — | **L11** 新增 | **L11 起（L11≡L12）** | E4-继承 |
| `pretty.rs` | 292 | 311 | 2027→2177 | 0.993 | 0.933 | L08(+9/-3)、L09(+1/-1)、**L12(+15/-0)** | L09–L11 逐字节同 | E1 + 1 条 E4 |
| `raw_pretty.rs` | 188 | 188 | 1189→1194 | 0.995 | 1.000 | **L09**（仅两处枚举元数补丁） | **L09 起（L09≡L10≡L11≡L12）** | E1（+1 条 E3-继承字面量） |

**哈希实测（SHA256 前 8 位，本人自算，可复核）**

| 文件 | L07 | L08 | L09 | L10 | L11 | L12 |
|---|---|---|---|---|---|---|
| `parser/lex.rs` | 9C043F19 | E736A9AE | BD4221C6 | 6E464B62 | E48A2690 | **E48A2690** |
| `parser/syntax.rs` | E286FE48 | **E286FE48** | A1A1B624 | F4619786 | F4619786 | **F4619786** |
| `parser/macros.rs` | — | — | — | — | 8877A096 | **8877A096** |
| `raw_pretty.rs` | F4C033F5 | 9542AF42 | 6879A927 | 6879A927 | 6879A927 | **6879A927** |
| `pretty.rs` | BA6B6066 | B170CF9C | 2EA7B025 | 2EA7B025 | 2EA7B025 | **CB4E240D** |
| `parser/mod.rs` | BE5CB633 | 0B6B69CC | AD1A012E | 653BDD3F | F5D2B8C5 | **79C7C6D4** |

## 2 分层的增删量（每层 diffstat，用于把每条差异钉到层）

| 转换 | `parser/mod.rs` | `parser/lex.rs` | `pretty.rs` | 该层做了什么 |
|---|---|---|---|---|
| L07→L08 | +91/−30 | +9/−1 | +9/−3 | `struct`/`new` 关键字、`p_struct`、`p_new`、投影改 `many0`、`SumCase` 去重 |
| L08→L09 | +24/−22 | +3/−3 | +1/−1 | `U`→`Type N`（`Raw::U(u32)`、`Sum` 第 4 字段）、pretty 改 `Type {uni}` |
| L09→L10 | +114/−22 | +17/−1 | 0 | `trait`/`impl`/`for`/`this`、`p_trait_def`、`p_impl`、`TraitDecl`/`ImplDecl` |
| L10→L11 | **+826/−37** | +29/−2 | 0 | **宏层**：`MacroState` 三元组、`macros.rs`、`p_raw`/`p_decl` 加壳 |
| **L11→L12** | **+22/−22** | **0** | **+15/−0** | **仅 crate 路径改名 + `Tm::Call` 渲染臂** |

⇒ 对 (a) 的直接回答：**`parser/mod.rs` 从 0.998（L10）掉到 0.977 是 L11 的宏层造成的；L12 把 0.977 原样接手，一点没再动。**

## 3 (a) L07 保留段落 ⟷ L12 逐行比对（8 处；另 3 个删除点 `MacroState`/`parser_with_span`/`T!` 见下段）

| # | L07 段落 | L12 对应段落 | 实际差异 | 首次出现 | 档 |
|---|---|---|---|---|---|
| 1 | `p_raw` `L07:497-510` | `p_raw_plain` `L12:881-895` | **14 行逐字相同**，尾部多 `+ .or(p_new)`（`L12:887`，**排在链尾、优先级最低**） | L08 | E1 |
| 2 | `p_decl` `L07:568-574` | `p_decl_plain` `L12:1506-1518` | `or_far` 链**前三分支顺序与文本不变**，尾部追加 `p_struct`(`:1514`)/`p_trait_def`(`:1515`)/`p_impl`(`:1516`) | L08/L10 | E1（见 §10 风险 2） |
| 3 | `p_def` `L07:512-531` | `L12:897-916` | **逐字相同**（21 行） | 无 | E0/E1 |
| 4 | `p_enum` `L07:539-566` | `L12:924-951` | **逐字相同**；case 名仍是裸 `Ident`，未加 `.mk` | 无 | E0/E1 |
| 5 | `p_match` `L07:481-495` | `L12:767-781` | **逐字相同**（含"臂间空行"容忍逻辑） | 无 | E0/E1 |
| 6 | `p_atom1` `L07:299-307` | `L12:576-587` | `kw(UKeyword).map(\|_\| Raw::U)`（`L07:302`）→ `Cut((kw(TypeKeyword), string(Num)))`（`L12:579-581`）+ `this` 臂（`:582`） | L09/L10 | **E2** |
| 7 | `p_atom` `L07:309-324` | `L12:589-602` | `(...).option()`+`match`（`L07:310-314`）→ `(...).many0()`+`fold`（`L12:591-592`）；0/1 段时构造同形 | L08 | E4→对 L07 输入 E1 |
| 8 | `p_pattern` `L07:468-479` | `L12:746-765` | 新增**首**分支 `Ident { .. }`→`Con(n.mk)`(`:747-754`)；L07 原分支**整体下沉为第二分支、逐字保留**(`:755-762`) | L08 | E4→对 L07 输入 E1 |

**"没偷偷改"的机械证据**：我用与 §7 不同（更粗）的分词器复算了 `parser/mod.rs` 的 6-gram，把 `L07_sum_type`↔`L12_canonical` 路径归一化后，
L07 侧 3118 个唯一 6-gram 里缺 118 个（keep=0.9622）。**这 118 个逐个归类后 100% 落在上表的替换点与 `MacroState`/`parser_with_span`/`T!` 三处（即 11 个删除点）**：
`p_lam`/`p_let`/`p_pi`/`p_lam_binder`/`p_pi_binder`/`fun_or_spine`/`p_arg`/`p_spine`/`p_match`/`p_def`/`p_print`/`p_enum`/`kw`/`string`/`paren`/`square`/`square_cut`/`brace`/`many1_sep` **零缺失**。
6-gram 对"函数体内插一行"同样敏感（会打断 5–6 个跨点 6-gram），所以这也是**没有在保留函数体内插过任何 token** 的证据。
⇒ **没有任何 `match` 分支优先级/优先级链被改写。** 我复算的绝对值与 §7 不同（分词器不等价），**只用其"缺失位置"这一结论**。

## 4 (b) `parser/lex.rs`：不是纯追加，但流水线函数体 0 缺失

L12 相对 L07 是 **+56/−5**（`git diff --no-index --stat`）。5 行删除全部是关键字/枚举表项替换，**没有一行落在 `ident`/`brace`/`string`/`num`/`op`/`err_token`/`lex` 的函数体里**：

| # | L07 | L12 | 性质 |
|---|---|---|---|
| 1 | `UKeyword, //Universe` `:9` | `TypeKeyword, //Universe: Type N` `:13` | 枚举替换；另加 `StructKeyword`/`NewKeyword`/`Trait`/`Impl`/`For`/`This`/`Macro` 7 个，及 `MacroIdent`(`:48`) |
| 2 | `TokenKind::UKeyword => write!(f, "`U`")` | `TypeKeyword => write!(f, "`Type`")` | Display 表替换 |
| 3 | `const KEYWORD: [..; 7]` `:85` | `[..; 14]` `:109` | 表长 7→14 |
| 4 | `("U", UKeyword),` | `("Type", TypeKeyword),` + 6 条新关键字 | 表项替换 |
| 5 | `ws(string.or(brace).or(op).or(num).or(ident))` `:235` | `ws(string.or(macro_ident).or(brace)...)` `:286` + 新增 `fn macro_ident` `:215` | 流水线插入 `$name` 分支 |

`macro_ident` 插在 `brace` 之前：`$` 不在 `OP` 表内，L07 下 `$x` 本来落到 `err_token`，**插入不改变任何既有 token 的归属**（E4-继承）。
⇒ keep07=1.000 是三位小数四舍五入的结果（我粗口径复算为 0.975，缺 37 个 6-gram，37 个**全部**聚在上述 5 处替换点的邻域）；
**"1.000" 的正确读法是"词法流水线的函数体一字未改"，不是"只增不删"。** 另注：`parser/lex.rs` 在 L12 层 **0 字节改动**（≡L11）。

## 5 (c) 宏层对 `parser/mod.rs` 的侵入点（L11 引入，L12 原样继承）

`parser/macros.rs`（354 行；MAP §4 记 345 行为旧值 [未核实]）只提供**数据与单点翻译**：`MacroMatcher` `macros.rs:17`、`MacroTranscriber` `:243`、
`MacroRule` `:354`、`OwnedToken` `:13`。**所有"接线"都在 `parser/mod.rs`**，共 8 个侵入点：

| 侵入点 | L12 锚点 | 侵入方式 | 对 L07 语义的影响 |
|---|---|---|---|
| 模块头 | `:4-5,10,14` | `use std::rc::Rc`/`FxHashMap`/`serde`、`use macros::*;`、`mod macros;` | 无 |
| `MacroState` 类型 | `:105` | `Vec<IError>`（L07:74）→ `(Vec<IError>, Rc<HashMap<String,Rc<Vec<MacroRule>>>>, Vec<MacroExpansionInfo>)` | **签名全改**，所有 `*_parser` 的 state 变三元组 |
| 展开深度守卫 | `:111,119-154` | `MAX_MACRO_EXPANSION_DEPTH = 256` + thread_local + `MacroDepthGuard` | 仅宏路径 |
| token 拼接/序列化 | `:156,177,198,218` | `owned/borrowed_tokens_to_string`、`splice_push`、`splice_transcriber` | 仅宏路径 |
| **`p_raw`**（表达式入口） | `:806-879` 包 `:881-895` | 先按首 token **原文**查宏表（`:807`），命中则展开后递归 `p_raw`；未命中才 `p_raw_plain` | 无 `macro_rules` 时等价 |
| **`p_decl`**（声明入口） | `:1404-1493` 包 `:1506-1518` | 同上；展开失败时**注入 `Decl::Println(Raw::Hole)` 占位**（`:1413`/`:1459`/`:1473`） | 仅宏路径 |
| `p_top` | `:1496-1504` | `macro_rules` 声明登记后返回 `None` 被过滤；`parser_with_span` 改调 `p_top`（`:401`）而非 `p_decl`（L07:165） | 无 `macro_rules` 时等价 |
| 匹配器辅助 | `:491`(kw_is) / `:513`(string_is) / `:1075`(paren_close_index) / `:1092`(err_expect) | 新增，供 matcher 用 | 无 |

⇒ `p_lam`/`p_let`/`p_pi`/`fun_or_spine`/`p_match`/`p_def`/`p_enum` **完全不知道宏的存在**（§3 的零缺失证据）。宏层的耦合面被控制在"两个入口 + 一个状态类型"。

## 6 (d) `pretty.rs` 的 MAX_DEPTH：同值、同点、同机制 —— E0

| 项 | L07 | L12 |
|---|---|---|
| 常量 | `pretty.rs:17` `const MAX_DEPTH: u32 = 1_024;` | `pretty.rs:17` **同一行、同值 `1_024`** |
| 计数器 | `thread_local! DEPTH` `:19-21` | 同 `:19-21` |
| RAII 守卫 | `struct DepthGuard` `:23-29` | 同 `:23-29` |
| 判定点 | `go()` 首部 `:83-89`（`depth >= MAX_DEPTH` → 推 `…`） | 同 `:83-89` |
| 回归测试 | `tests.rs:1995` | `tests.rs:1995`（同文件同址） |

两侧 `pretty.rs` 的 1–100 行 **逐字节相同**（`git diff --no-index` 在该区间无输出）。L12 对 `pretty.rs` 只在 `:241-255` 新增一个 `Tm::Call` 臂，**没有碰深项保护**。
注意 `Tm::Call` 臂的两个分支（`Match` 体打 `name(args)`，否则打 body）都经 `go()` 递归，因此**同样受 MAX_DEPTH 约束**，不构成新的爆栈口。

## 7 (e) `raw_pretty.rs` 的 +5 token：逐 hunk 只有两处（L09 引入）

`git diff --no-index` 全文只有 2 个 hunk，L12 层 0 字节改动（`≡L11≡L10≡L09`）：

| # | L07 | L12 | Δ token |
|---|---|---|---|
| 1 | `Raw::U => out.push('U'),` `raw_pretty.rs:29` | `Raw::U(_) => out.push('U'),` `:29` | `(` `_` `)` = **3** |
| 2 | `Raw::Sum(name, params, cases) => {` `:138` | `Raw::Sum(name, params, cases, _) => {` `:138` | `,` `_` = **2** |

3+2 = **5**，与 §1 的 `+5` 完全对上；两处都是 L09 改 `Raw` 元数时补的通配，**渲染逻辑一字未动**（`go()` 仍 `:14`，`def_type_from_source` 仍 `:165`，`has_source_type` 仍 `:193`）。
唯一实质问题见 §10 风险 1。

## 8 E4 单边新增清单（不算"共有部分的差异"，列出以免误算）

| 项 | L12 锚点 | 引入层 | 说明 |
|---|---|---|---|
| `p_new`（`new Name(args)` + 投影链） | `parser/mod.rs:787-804` | L08 | 契入 `p_raw_plain` 链尾；脱糖为 `Name.mk` 应用 |
| `p_struct`（脱糖单 case enum） | `:958-982` | L08 | case 名 `{Name}.mk`（`:976`），与 §3#8 的 struct 模式糖互为一体 |
| 投影链 `x.f.g` | `:591-592` | L08 | L07 只允许单段 |
| `p_trait_def` / `p_impl` / `this` | `:996` / `:1022` / `:582` | L10 | 本章 typeclass 主题的解析侧 |
| 整个宏解析/展开（`macros.rs` + §5 的 8 个侵入点） | `macros.rs:1-354` | L11 | — |
| `Tm::Call` 渲染臂 | `pretty.rs:241-255` | **L12（本层唯一）** | 配合 `mod.rs` 里 `Tm::Call`（L11 计数 0 / L12 计数 19） |

## 9 已确认等价（不必再查的清单）

1. `parser/mod.rs`：`ErrMsg`/`BaseMsg` 与外层 `Err("parse error")` 折叠逻辑、`span_of`（`:362` vs L07 `:141`）、`many1_sep`（`:314` vs L07 `:93`）、`kw`/`string`/`paren`/`square`/`square_cut`/`brace`、`p_lam`/`p_let`/`p_pi`/`fun_or_spine`/`p_match`/`p_def`/`p_print`/`p_enum`/`p_spine`/`p_arg` —— **token 流完全相同**。
2. `parser_with_span`（`:377-426` vs L07 `:156-192`）：差异仅为 `MacroState` 三元组初始化（`:386`）、内置 `stringify` 注册（`:387-400`）、`p_decl`→`p_top`（`:401`）、`err_collect.0.first()` 折行（`:419`）。错误折叠顺序与"leftover token 带 offset"文案**逐字保留**。
3. `parser/lex.rs`：`ident`/`brace`/`string`/`num`/`op`/`err_token`/`lex()` 函数体零改动（§4）。
4. `pretty.rs:91-209` 全部既有臂（`Var`/`Decl`/`Obj`/`App`/`Lam`/`Pi`/`Let`/`Meta`/`AppPruning`/`LiteralType`/`LiteralIntro`/`Prim`/`Sum`）**行号与文本都相同**；`fresh`/`go_ix`/`bracket`/`paren` 相同。
5. `raw_pretty.rs`：除 §7 两处通配外**整文件相同**（L07 与 L12 行数都是 188）。

## 10 风险与未核实

1. **【确凿 E3-继承】`raw_pretty` 的 `'U'` 字面量没跟上 L09 的 `Type N` 升级**：`Raw::U(0)` 由 `:29` 打成 `U`，而 `pretty.rs:138` 同值打成 `Type 0`；且 `U` 自 L09 起已不是 L12 关键字（`lex.rs:109` 的 KEYWORD 表只有 `Type`）。`def f(x : Type 1): Type 0` 的源码注解渲染会得到 `(x : Type 1) → U`（`raw_pretty.rs:176/:183/:188` 都走 `go`），**该串回灌给 L12 自己的解析器时，`U` 会退化为自由变量**（`lex.rs`→`p_atom1:577-578` `Ident→Raw::Var`）⇒ 渲染不可逆。**这是本角度唯一"确凿的落后项"**，但它属 L09 的漏改、L09–L12 逐字节继承，**不是 L12 引入的**。
2. **【E2-继承，诊断可有可无地漂移】** `p_decl_plain` 在 `or_far` 链尾追加 3 个分支（`:1514-1516`）：接受集不变（`struct`/`trait`/`impl` 都是 L07 没有的关键字，不可能抢走 L07 输入），但 `or_far` 取"最远失败"，**非法 decl 的报错 span 可能改由更远的分支给出**。只影响 LSP 诊断位置，不影响任何合法程序。
3. **【E2-继承，宏名字捕获】** 内置 `stringify` 在 `:387-400` **无条件**进表（不需要任何 `macro_rules` 声明），`p_raw:807` 按首 token **原文**查表 ⇒ 用户程序里出现名为 `stringify` 的标识符做函数应用的表达式（`stringify x`）会被宏优先拦截并展开成字符串字面量。[推断] L11 的 tests 是否覆盖此情形未查；因 `stringify` 是保留名，我把它算 E4 而非"共有部分漂移"。
4. **[未核实]** 宏展开失败时注入的 `Decl::Println(Raw::Hole)`（`:1413`/`:1459`/`:1473`）在下游 elaboration 里是否被静默吞掉。
5. **[未核实]** `MAP §4` 记 `parser/macros.rs` 为 345 行，实测 `(Get-Content).Count` = 354（差 9 行，可能是统计口径）。
6. **未做的验证**：没有可喂源码的 release 二进制（`target/release/l12bench.exe` 只跑内建负载，无文件/表达式入口），因此 §10.1 的"渲染不可回灌"是**读代码得出的结论**，不是运行结果。

## 一脉相承评级

**强。** 解析与渲染是本次六个角度里"两版同一份实现"最干净的一组：L07 的 19 个递归下降规则函数里有 **14 个在 L07→L12 之间 token 流完全相同**（`p_bind`/`p_arg`/`p_spine`/`p_lam_binder`/`p_lam`/`p_pi_impl_binder`/`p_pi_binder`/`p_pi`/`fun_or_spine`/`p_let`/`p_match`/`p_def`/`p_print`/`p_enum`），另 5 个只在链尾追加或整体下沉，L12 这一层对解析器的改动只有 20 条 `$crate` 路径改名 + 15 行 `Tm::Call` 渲染臂，`lex`/`syntax`/`macros`/`raw_pretty` 四文件在 L12 逐字节冻结；
所有实质差异可逐条钉到 L08/L09/L10/L11 某一层，且落地方式一致 —— **在既有骨架上"尾部追加或外加一层壳"，从不改写已保留的分支**。唯一的落后项（`raw_pretty` 的 `U`）是 L09 的漏改，且只影响渲染文本。

## Top-3 差异

1. **E3-继承**：`raw_pretty.rs:29` 仍把 `Raw::U(n)` 打成 `U`，而 `pretty.rs:138` 同值打 `Type {uni}` —— 两个渲染器分歧，且 `U` 自 L09 起不在 `lex.rs:109` 的 KEYWORD 表里，渲染结果不可回灌自解析（L09 漏改，L09–L12 逐字节继承；L07 版本 `raw_pretty.rs:29` = `Raw::U => out.push('U')` 是当时正确的）。
2. **E2-继承**：`MacroState` 由 `Vec<IError>`（L07 `parser/mod.rs:74`）扩成三元组（`L12:105`），`p_raw`/`p_decl` 两个入口被白套一层宏拦截壳（`L12:806`/`:1404` 包 `:881`/`:1506`），内置 `stringify` 无条件注册（`:387-400`）⇒ 名为 `stringify` 的用户标识符被优先拦截；L11 引入，L12 未改。
3. **E2-继承（有意升级，非回归）**：L07 的 `U` 关键字在 L12 已整体消失 —— `lex.rs:9`→`:13`、`KEYWORD` 表 `:85`→`:109`、`T![U]` 臂删除（L07 `parser/mod.rs:197`）、`p_atom1` 改 `Cut((kw(TypeKeyword), string(Num)))`（`L12:579-581`，`Cut` 使 `Type` 后缺数字成为硬失败）⇒ L07 源程序 `def f : U = ...` 在 L12 退化为自由变量；L09 引入，属分层宇宙的规范升级，**L12 忠实继承了它，不是 L12 丢功能**。
