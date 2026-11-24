# 05 · 名字世界 / 表面层 / 解析器：L07_sum_type ⟷ L13_namespace

分析员：names（task-5）。HEAD `911628b3` 工作区实测；只读 `src/`，未构建。行数为 `[IO.File]::ReadAllLines` 实测，token/保留率引自 MAP.md §1。
评级与 Top-3 见 §5；给 Lead 的三条越界提醒见 §6。

## 1 范围与方法

覆盖同路径 6 个文件：`mod.rs`、`surface.rs`、`syntax.rs`、`parser/{mod,lex,syntax}.rs`（另有 L13 独占 `parser/{derive,macros}.rs`，只计入 E4，不做逐行比对）。
方法：先 `grep '^\s*(pub )?fn {name}'` 两侧建函数名集合做差集 → 再对每个机制读 10–130 行窗口 → 用 `fn-matrix.tsv` 的 `body_sim` 定量校准"像不像一份代码"。
关键判据：**同名函数集合重合 ≠ 一份代码**。parser/mod.rs 有 30 个同名函数（L07 共 35），但其中 `p_spine`/`p_raw`/`p_decl` 的 body_sim 只有 0.16/0.07/0.02——骨架同名、心脏不同（§4A）。

## 2 模块对位表

| 文件 | L07 tok/行 | L13 tok/行 | 保留率(文字/归一) | 判读 |
|---|---:|---:|---:|---|
| `mod.rs` | 17,243 / 2,615 | 46,810 / 8,689 | 26% / 57% | **扩张 + 换基**：名字世界换载体（§3），且 L13 尾部 ~3,500 行是 `let input = r#"…"` 内联外部程序（首处 `mod.rs:5166`），L07 同类测试在独立 `tests.rs`(65,750B) ⇒ 该比率被测试尾巴稀释 |
| `surface.rs` | 1,431 / 196 | 834 / 166 | 26% / 27% | **契约同型、文件不同物**：`LspSurface` 6 字段同名同序 + 5 个方法 body_sim 全 1.00；L07 后半部（AST span 折叠 `raw_span` 等 7 个函数）在 L13 不在本文件 ⇒ 26% 是"文件级"假象 |
| `syntax.rs` | 229 / 35 | 720 / 80 | 38% / 60% | **扩张**：`Locals` 同构，L13 追加 `update_at`/`update_by_cxt`（精化改写 Locals 链） |
| `parser/mod.rs` | 5,303 / 534 | 35,004 / 4,637 | 67% / 88% | **骨架继承 + 语法面扩张**：30 个同名组合子，纯工具 `string/paren/square/square_cut/many1/parse_progress` body_sim=1.00，主循环全部重写 |
| `parser/syntax.rs` | 820 / 118 | 3,705 / 356 | 51% / 66% | **扩张**：`Raw` 12→14 变体、`Decl` 3→10 变体，名字原子 `String`→`SmolStr` |
| `parser/lex.rs` | 1,771 / 311 | 2,428 / 455 | **89% / 95%** | **真继承**（对照样本）：`string`/`ws` body_sim=1.00，漂移只在关键字表、`ident`、`lex` 驱动 |

## 3 逐机制差异表（核心）

### 3.1 名字世界载体

| 机制 | L07 实现(锚点) | L13 实现(锚点) | E | 可观察后果 / 风险 |
|---|---|---|---|---|
| decl 表类型 | `struct Decls { map: FxHashMap<SmolStr, Rc<DeclEntry>>, ver: u64 }` `cxt.rs:34-41`，`Deref` 到 map `cxt.rs:49` | `type Decl = FxHashMap<SmolStr, DeclEntry>`（7 元组条目）`mod.rs:439,452`；无 `ver` 代数，简化表缓存改走别处 | E2 | 表仍"字符串→条目"，但**键的语义变了**：L13 把命名空间塞进键字符串（`Foo.method`、`pkg.name`） |
| 键 / 限定 | 只用裸名；构造子名在 decl 表里也是裸名（`failed_decl_names` 用 `{enum}.{ctor}` 拼 `surface.rs:166`） | 键是**全限定串**：`symbol_table: FxHashMap<(SmolStr, usize), SmolStr>`（名+元数→限定名）`mod.rs:1515`、`import_map` `mod.rs:1525` | E2 | L13 一个原子的名字不再唯一确定条目；同名不同命名空间可共存 |
| 查找路径 | 单跳：按 `SmolStr` 直取（`cxt.decl.get` 直读 map） | 四级阶梯：**exact（含 prelude 别名）> import_map > namespace_prefix > 唯一后缀回退** `elaboration.rs:3032-3066`，后缀匹配要求恰好一个候选 `elaboration.rs:3051-3054` | E2 | 遮蔽/歧义语义不同：L13 的"裸名"可能因回退命中别处；L07 只可能 not-in-scope |
| 名字原子类型 | `Span<String>`（`syntax.rs:18-19`、`parser/syntax.rs:76-90`） | `Span<SmolStr>`（`syntax.rs:10-13`、`parser/syntax.rs:95-111`） | E1 | 仅分配策略；Error 文案仍需 `String` ⇒ L13 在表里存渲染串旁路（`DeclEntry` 位置 `.6`，`mod.rs:439`） |
| 名字轨迹 | `Tm::Decl(SmolStr)` `mod.rs:130`；`Val::Decl(SmolStr, Spine)` `mod.rs:305` —— **只带名字，不带定义处** | `Tm::Decl(Span<SmolStr>)` `mod.rs:525`；`Val::Decl(Span<SmolStr>, Spine)` `mod.rs:909` | E2 | L13 条目自带定义处 span，hover/references 可直出；L07 的定义处只能靠 `decl.get(key).0`（`DeclEntry` 首字段，`cxt.rs:37`→条目）二次查表 |
| 局部变量世界 | `Locals::{Here,Define,Bind}` `syntax.rs:16-20`，只服务 `close_ty` `syntax.rs:24` | 同名同构 `syntax.rs:10-14`，外加 `update_at` `syntax.rs:17`、`update_by_cxt` `syntax.rs:34` | E2 | L13 给模式精化有了"改写绑定值"的入口；L07 的 Locals 是纯只读链 |
| 内建/prim 名 | `Val::Prim(SmolStr, Spine)` 卡住的内建应用 `mod.rs:317`；`PrimFunc(Rc<dyn Fn(&Infer,&Decls,&[Val])->Option<Val>>)` `cxt.rs:71` | `Val` **无 Prim 变体**（`mod.rs:906-940`）⇒ 改 `PrimFunc(Rc<dyn Fn(&Infer,&Decl,&[Rc<Val>])->Option<Rc<Val>>>)` 存进 `DeclEntry.prim` 槽 `mod.rs:439,514` + `decl_prim` `mod.rs:445`；卡住形态换成 `Val::Call(SmolStr, List, Rc<Val>)` `mod.rs:940` | E2 | `x ++ y ≡ x ++ z` 这类"丢实参的单元 Prim"不健全判等（L07 `mod.rs:313-317` 的注释）在 L13 由 Call 携带实参规避；但两版卡住值的 unify/quote 分支不同源 |

「同一角色能否对上号」：**能对上角色，对不上表示**。6 组映射：

1. `cxt.rs:34 Decls{FxHashMap<SmolStr,Rc<DeclEntry>>+ver}` → `mod.rs:452 Decl{FxHashMap<SmolStr,DeclEntry>}` + `symbol_table`/`import_map`（同角色：全局名字表；不同表示：裸键 → 限定键 + 两张别名表）。
2. `mod.rs:130 Tm::Decl(SmolStr)` → `mod.rs:525 Tm::Decl(Span<SmolStr>)`（同角色：全局引用；L13 加定义处）。
3. `mod.rs:305 Val::Decl(SmolStr, Spine)` → `mod.rs:909 Val::Decl(Span<SmolStr>, Spine)`。
4. `mod.rs:317 Val::Prim(name, spine)` → `mod.rs:940 Val::Call(name, args, body)` + `DeclEntry` 的 `PrimFunc` 槽（同角色：内建调用；机制从"卡住的值"变成"闭包派发"）。
5. `syntax.rs:16 Locals`（只读）→ `syntax.rs:10 Locals`（可 `update_by_cxt` 改写）。
6. `observe.rs:182/199 push_hover / push_hover_decl` + `observe.rs:294 surface()` → `elaboration.rs:2889/2870 push_hover / push_hover_decl` + `surface.rs:127 lsp_surface()`（同角色：观察面采集；从独立 observe 模块搬进 elaboration/surface）。

### 3.2 表面层契约（`surface.rs` 26% 之谜）

| 契约项 | L07 `surface.rs` | L13 `surface.rs` | 判定 |
|---|---|---|---|
| `struct LspSurface` | 6 字段：`hover/completion/inlay_hint/println_spans/check_issues/failed_decls` `26-41` | 同 6 字段、同序、同 derive `21-34` | **真同型**（E0） |
| `HoverEntry` | `(Span<()>, Span<()>, String)` `surface.rs:22` | 同（但定义在 `mod.rs:1462`） | E0，仅位置不同 |
| `hover/completion/inlay_hint` 类型 | `Vec<(Span<()>,String)>` / `Vec<(u32,String)>` `31,33` | `completion` 是 `Vec<(Span<()>, SmolStr)>` `25`；其余同 | **E2（载荷类型）**：消费端不可直接互换 |
| `check_issues` | `Vec<(usize, String)>` = (decl 下标, 行)，由 `observe.rs:258 drain_check_issues(decl_idx)` 从可变全局 `CheckIssues` 排水 `observe.rs:262-281` | `Vec<String>` `31` = 只有渲染行，来自 `accumulated_errors` `surface.rs:133` | **E2（语义）**：L13 丢掉 decl 身份，无法按 decl 归并 |
| `println_spans` | `(span, rendered)` 实填 `observe.rs:254` | `(span, String::new())` **恒空**，渲染推迟到轮末作业 `surface.rs:143-148`、`PrintlnJob` `mod.rs:1449` | **E2**：同字段名、空载荷 |
| `impl LspSurface` 方法 | `hover_entry_at/hover_text_at/is_empty` `45,54,59` | 同三个，body_sim **1.00/1.00/1.00** | E0 |
| `SurfaceQuery` | `hover/inlay` `73-76` | 同 `65-68`；`hover_only/view` body_sim 1.00 | E0 |
| 采集开关 | `lsp_collect/hover_query/inlay_query` `mod.rs:2268-2270` | 同名 `surface.rs:108-122` `set_surface_query` | E0/E1 |
| 快照装配 | `observe.rs:294 surface()`，LSP 入口 `run_with_surface*` `mod.rs:2191-2253` | `Infer::lsp_surface()` `surface.rs:127` + 单通道 `lsp_hover/lsp_completion/lsp_inlay` `90-104`（L07 无单通道入口） | E2（性能路径单边新增） |
| AST span 折叠 | `raw_span`/`pattern_span`/`span_union`/`inlay_label`/`failed_decl_names`/`format_check_warning`/`split_issue_lines` 全在本文件 `91-196` | 本文件无；`format_check_warning` → `mod.rs:4650`、`failed_decl_names` → `mod.rs:1657`（返回 `Vec<SmolStr>`）；`raw_span`/`inlay_label`/`span_union`/`pattern_span` **在 `src/` 全仓只出现在 L06–L12 的 surface.rs，L13 一份都没有**（L08/L09/L10/L11/L12 与 L07 同行号 91/108/139/149） | E2/E3：L13 改用 `Raw::to_span()` 方法（`parser/syntax.rs:180-209`，且**有损**：`Match` 只取末臂 `198`、`Sum` 只取末构造子 `201-203`） |

补一条反向发现：L13 `surface.rs` 文件头自称是"L07/L08/L09–L12 的**上游原版**"`surface.rs:1-2`，但 L06–L12 那份 surface.rs 家族（含 L07，8,229B）比 L13 这份（7,300B）**多了整套 AST span 折叠**——即"上游"只对 `LspSurface` 结构与查询方法成立，span 折叠这一层是下游各层共有、L13 独缺。

结论（对 15dce930/71702814/87fdafd6 声称的"观察面收敛为 LspSurface 契约，与 L07–L12 同型"）：**结构层为真，语义层为假**。结构（6 字段名/序、3 个查询方法、`SurfaceQuery`、三个采集开关）确实同型且方法体逐字节相同；但 6 通道里有 3 条载荷语义不同（`completion` 类型、`check_issues` 丢失 decl 下标、`println_spans` 恒空），并且 span 来源从"surface 里的 AST 折叠"换成"AST 自带的有损 `to_span`"。⇒ 说"同一份契约"成立，说"同一份实现/可直接复用消费端"不成立。附带反向证据：L07 文件头自注"设计对齐 L06 …与 **L13 的「阶段 0 契约」**"`surface.rs:3-4`——这份契约的源头在 L13 侧。

### 3.3 解析器：`lex` 89% 保留 vs `mod` 67%

| 机制 | L07(锚点) | L13(锚点) | E |
|---|---|---|---|
| `string()` / `ws()` 词法 | `parser/lex.rs:116-152` / `225` | `parser/lex.rs:155-188` / `341`（body_sim 1.00/1.00） | E0 |
| 关键字表 | 7 个 `lex.rs:85-93`（含 `U`） | 20 个 `lex.rs:112-133`（`U`→`Type`、新增 `package/import/struct/trait/impl/for/this/static/macro_rules/where/class/by/new`） | E4 |
| `ident()` | `_` 走 `is('_')` 前置分支 `lex.rs:157` | 内联 `ident == "_"` `lex.rs:201`；`until` 降级为 `Op` `lex.rs:205-209` | E1/E4 |
| 标点通路 | `.`,`,` 在 `OP` 表 `lex.rs:95-112` | 移入 `brace()` `lex.rs:243-261`，且 `op()` 把 `.` 排除出算符字符域 `lex.rs:264-274` | E1（token 流等价） |
| `:=` | `AssignEq` 词法单元 `lex.rs:30,69,111`（parser 里**无使用者**，仅 `T![ := ]` 宏 `parser/mod.rs:213`） | 删除；`:`+`=` 会合成一个 `Op` | E3（死语法面） |
| EndLine | 纯换行 token，`ws(endline)` `lex.rs:223,236` | 换行 run **+ 下一行缩进**，`endline_indent()` `lex.rs:290-292,313-336` | E4（缩进感知续行的地基） |
| EOF | `Eof` 变体存在但从不产出 `lex.rs:41` | `lex` 尾部显式压一个合成 `Eof` `lex.rs:362-371` | E4 |
| 宏词法 | 无 | `macro_ident()` 认 `$x` `lex.rs:223-241` | E4 |
| BOM | 不特判 | 前导 `\u{feff}` 吞掉 `lex.rs:353` | E4 |
| 错误恢复 | `or_far` 保留最远失败；`p_decl` 注释明确"折叠为整体 `parse error`" `parser/mod.rs:568-573`；**无 Cut 恢复** | `Cut`/`or_far`/`push_error` + 同步点 `skip_until_decl` `parser/mod.rs:124`、`skip_until_inner`，逐声明恢复 | E2 |
| 声明分派 | `p_decl` 7 行三支：`p_def.or_far(p_print).or_far(p_enum)` `parser/mod.rs:568-573` | `p_decl` 105 行十支（`parser/mod.rs:3734`）：package/import/def/print/enum/struct/trait/impl/class/derive/macro（`kw(PackageKeyword)` `3021`、`kw(TraitKeyword)` `2411`、`kw(ImplKeyword)` `2469`、`kw(ClassKeyword)` `3379`） | E4 |
| 运算符优先级 | **无**（git `67273831` 提交正文自述"无运算符优先级"） | Pratt：`expr_bp` `parser/mod.rs:968`、`infix_binding_power` `1284`、`prefix_binding_power`/`postfix_binding_power` | E4 |
| 括号摊平 | **无** SPINE_ESCAPE | 有：哨兵 icit `SPINE_ESCAPE` `parser/mod.rs:1359`、`strip_spine_escapes` `1368`、`unescape_spine` `1420`、结算 `p_spine` 内 | E4（方向与"L07 有而 L13 丢"的假设**相反**） |
| Verilog 兼容 | 无（`p_atom1` 9 行 `parser/mod.rs:299-307`） | `p_atom1` 116 行：`{a,b}` 拼接、`Type N` 宇宙级、Nat 字面量溢出诊断 `parser/mod.rs:807-838` | E4 |
| AST 自省 | `Raw::U` 单元；无 `to_span` | `Raw::U(u32, Span)`、`Raw::Nat`、`Raw::Tm`（预检查值，`parser/syntax.rs:118`）、`Raw::to_span()` `180`、手写 `PartialEq/Hash`（`Raw::Tm` 按指针判等，`parser/syntax.rs:143,168`） | E4/E2 |

血缘佐证：L13 parser 首现 2026-05-11（`f1392ad4 feat(L13): init namespace`，远早于 L07 的解析器成熟形态）；L07 的 resilient 组合子/错误形态是 **2026-09-05 从 L13 设计回移植**（`67273831 refactor(L07): parser 对齐 L13 设计——resilient 组合子移植`，其正文逐条自述 L07 刻意不带的语法面）。⇒ 同名 30 个组合子不是"L13 从 L07 长出来"，而是**L07 向 L13 单向对齐后各走各路**：之后 L13 走宏/优先级/缩进/Cut 恢复（`242a227e`、`b4cf62ed`、`98777280`、`c22c3f26`、`820f9aa0`），L07 走错误定位与诊断可读性（`326d9f93`、`ac550fe5`、`c63a6b32`）。

## 4 抽样深挖

### A. `p_spine`：同名、10 行 → 75 行（E2 + E4）

```rust
// L07 parser/mod.rs:341-350 —— 纯 juxtaposition
let (input, head) = p_atom(input, state)?;
let (input, args) = p_arg.many0().map(|x| x.concat()).parse(input, state)?;
let result = args.into_iter().fold(head, |acc, (icit, arg)| Raw::App(...));
// L13 parser/mod.rs:1452-1454 —— 头是 Pratt expr，不是 atom
let (input, head) = expr(input, state)?;   // 实参循环手写展开 + 缩进续行 + 哨兵结算
```

为什么算 E2 而非 E1：不是拆函数或换容器——`p_spine` 的输入语言变了（L13 头位可解析 `a + b` 这样的中缀表达式，L07 的 `p_atom` 只吃原子），且 L13 在 `p_explicit_arg` 里加了 `LCurly` 拒绝分支 `parser/mod.rs:1335-1342`（否则 `impl X for T { … }`/`for i in 0 until 4 { … }` 会把体花括号当实参吃掉）。两侧对同一源码串可产出不同 AST ⇒ 语义可观察。E4 部分：`SPINE_ESCAPE` 与缩进续行是 L13 新增语言面，L07 根本没有对应输入。

### B. `check_issues` 通道：同字段名的两种东西（E2）

```rust
// L07 surface.rs:38   —— 下标是 decl 身份
pub check_issues: Vec<(usize, String)>,
// L13 surface.rs:31   —— 只有渲染行
pub check_issues: Vec<String>,
```

L07 的生产者是 `observe.rs:258-281`：从可变全局 `CheckIssues` 字符串按长度增量排水，逐行配 `decl_idx`；L13 是 `surface.rs:133` 把 `accumulated_errors: Vec<Error>`（`mod.rs:1501`）直接 `map` 成字符串。这不只是类型不同：**L13 侧已经没有"哪条错误属于哪个 decl"这个信息**，消费端若按 decl 归并/跳转必须换一套索引。同理 `println_spans` 在 L13 恒为 `String::new()`（`surface.rs:143-148`），L07 是实渲染串（`observe.rs:254`）。⇒ 同型的是字段名，不是契约语义。

### C. 对照样本：`string()` 逐字节继承（E0）

`parser/lex.rs` 的 `string` 在两侧 body_sim=1.00：L07 `:116-152` / L13 `:155-188`，含同一段 `if bytes[end] == b'\\' { end += 2 }` 转义跳过与同一闭引号终止判据。差别只有注释（L07 多一段"旧组合子版 `pmatch(c != '"')` 至少吃一字符"的返修记录 `:130-132`，L13 无）。这证明两侧确有"逐字节搬运"的通道，也就反面说明 `surface.rs` 26% 不能归因于"整体重写"——**低保留率是文件内职责搬家，不是实现消失**。

## 5 本角度评级与 Top-3

**评级：中（"换了基、保住了骨架"）**——词法与 AST 骨架是真继承（`lex.rs` 89%/95%、`string/ws/paren/square/many1` body_sim 1.00、`LspSurface` 结构与三个查询方法逐字节同），但名字世界本身换了基（裸键 flat map → 限定键 + 别名表 + 四级阶梯解析），解析主循环与整个语法面是 L13 独立演进；不能称"一脉相承"，也不能称"两条独立实现"。

Top-3 差异：
1. **名字查找从单跳变四级阶梯** —— 键从裸名变"字符串内嵌全限定名"+ `symbol_table`/`import_map`：`cxt.rs:34,49` / `mod.rs:452,1515,1525` / `elaboration.rs:3032-3066`；**E2**（遮蔽与歧义语义不同，L07 不可能"裸名命中别处"）。
2. **`LspSurface` 同型只对结构、不对载荷** —— 6 字段同序但 `completion` 换 `SmolStr`、`check_issues` 丢 decl 下标、`println_spans` 恒空：`surface.rs:26-41` / `surface.rs:25,31,143-148`；**E2**（消费端不可互换）。
3. **解析主循环与语法面重写** —— `p_spine/p_raw/p_decl` body_sim 0.16/0.07/0.02，且 L13 独有运算符优先级、`SPINE_ESCAPE` 摊平、缩进续行、宏、`Cut` 恢复：`parser/mod.rs:341,568` / `parser/mod.rs:1452,1359,3734`；**E2+E4**（两版接受的语言不是同一门语言）。

## 6 给 Lead 的提醒（超出本角度）

1. **`mod.rs` 的 26% 被三件事同时稀释**，别直接当"核心重写"的证据：①L13 `mod.rs:5166` 起是成批 `let input = r#"…"` 内联外部程序（≥20 处，`#[cfg(test)]` 块到 `mod.rs:8533`），L07 把同类测试放独立 `tests.rs`(65,750B)；②L13 加了 prelude/typeclass/namespace 装载机制（`PreludeState/PreludePool` `mod.rs:4124-4171`）；③核心函数被**抽薄**：`fn-matrix` 显示 `eval` 110→4 行、`force` 122→48、`quote` 17→4、`go` 48→22。第③点意味着 L13 的 NbE 主循环可能在别处另有实现（我只核了行数，**未核**其被委托去哪个函数——建议 01 号确认，若是委托则"共有部分"的边界要改判）。
2. **`surface.rs` 的"26%"和 `parser/lex.rs` 的"89%"都应写进总报告的"度量陷阱"段**：前者是文件内职责搬家（AST span 折叠搬走 + `impl Infer` 迁入），后者才是逐字节搬运；单看文件级保留率会把两者混为一谈。
3. `L13 mod.rs:439 DeclEntry` 仍是位置元组（`(span, tm, val, ty, vty, prim, typ_pretty)`），作者注释自述是给 `src/doc/collect.rs` 的 `.1/.6` 直读让步的**过渡形态**（`mod.rs:432-438`）；`DeclTm` 里 `Enum/Trait/TraitImpl/Class` 四个变体都是 `//TODO:` 空体（`mod.rs:497-508`）。⇒ L13 的 decl 表形态尚未定型，若 Lead 的结论要写"L13 已成生产形态"，需注明这一处未完成态。
