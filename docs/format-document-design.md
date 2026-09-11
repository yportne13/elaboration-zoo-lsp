# Format Document（`textDocument/formatting`）设计方案

> 状态：设计稿 v2（未实现）
> 调研基线：`master` @ f4d5da8
> 隔离工作区：worktree `task/format-document-design`
>
> v2 变更：架构方向由「另起独立 lexer」改为「**扩展现有 L13 lexer，增加 trivia 侧信道**」，
> 以满足「不另起炉灶、单一 tokenizer」的诉求；同时给出「改造 parser」的**安全边界**。

---

## 0. 结论先行

当前仓库**没有**任何 formatter，也没有 `document_formatting_provider`。
决定方案走向的核心事实：**现有 parser 对 trivia（注释/空白/换行）完全有损**——
注释在 lex 之前就被 `preprocess` 抹成空格（`src/L13_namespace/mod.rs:3976`），
空白被跳过、连续换行折叠成一个 `EndLine` token（`src/L13_namespace/parser/lex.rs:288-304`），
全仓库没有 CST / token 流留存。

因此方案定为：

- **拒绝** AST 打印：`Vec<Decl>` 丢注释，且 parser 会 desugar（见 §2），回写不了源码。
- **拒绝**改写 parser 的语法/token 契约：`EndLine` 载荷敏感（见 §2.2），改动会波及
  hover/goto/inlay/宏匹配/twin-engine 对齐。
- **采纳**「扩展现有 lexer」：
  1. 在**同一个** `L13_namespace/parser/lex.rs` 内新增 **trivia 侧信道**
     （注释 span + 换行信息，字符串感知，复用该文件既有的 string/operator 字符表）；
  2. parser 侧 token 流与 `EndLine` 语义**逐字节冻结**，调用路径不变；
  3. 新增布局引擎 `src/format/`，输入 = **既有 token 流 + trivia + 原文**，
     只决定 token 间空白与行首缩进，**绝不增删/重排 token**。
- **保留**后续可选步骤：把 `preprocess` 的注释处理并入 lexer（顺带修 `//`-in-string 缺陷），
  以 formatter 的 token 不变量测试为闸门（§3.4）。

一句话：**单一 tokenizer（改造 lexer），但 formatter 不依赖 AST、也不改 parser 契约。**

---

## 1. 需求与约束（从代码推导，均为硬约束）

| 编号 | 约束 | 依据 |
|------|------|------|
| R1 | **注释逐字保留** | 注释是用户数据；`preprocess` 已证明 parser 里拿不到 |
| R2 | **语义透明，不改写源码形态** | parser desugar：`parser/mod.rs:1352-1399`（where）、`1690-1701`（struct→enum+.mk）、derive 展开 |
| R3 | **幂等** `format(format(x)) == format(x)` | 格式化器通用要求，也是廉价测试手段 |
| R4 | **宁可不做，不可做坏** | 无法安全格式化时返回 `None`（LSP null = 无编辑），绝不返回被破坏的文本 |
| R5 | **wasm 兼容** | LSP 编译到 `wasm32-wasip1-threads`，`src/lsp_stdio.rs` 有 64KiB 分块；不得引入 native-only 依赖，响应体有界 |
| R6 | **换行符风格保持** | `FormattingOptions` 不携带 EOL；需探测并保持 CRLF/LF，保留 BOM |
| R7 | **宏体是「token 汤」** | `macro_rules` 的 matcher/transcriber 对相邻性与逗号敏感（`parser/macros.rs`），重排可能改变匹配语义 |
| R8 | **HDL 语法占语料一半** | `examples/hdl/*.typort` 含 `module`/`when`/`switch`/`:=`/`##` 等 |
| R9 | **不回归主线性能** | master 近期在做净收益优化；不得在分析热路径上常驻 token 流（§2.3） |

---

## 2. 为什么「改造 parser」要限定在 lexer 层

### 2.1 AST 无法用于回写源码——所以 formatter 只能基于 token 流

- parser **desugar**：`where` → 隐式参数（`mod.rs:1352-1399`）；`struct` → `Decl::Enum` + 合成 `.mk`
  （`1690-1701`）；`#[derive]` → 生成 decl；宏展开 → 重新拼文本再 lex（`owned_tokens_to_string`，`mod.rs:133-149`）。
  基于 AST 打印会把用户源码改写成另一种写法。
- span 不完整：`Decl` 无整体 span；`Decl::Import` 无任何 span（`syntax.rs:295-299`）；
  `Raw::U(u32)`、`Raw::App` 的 `Icit` 分支无 span。
- 宏定义**不进 AST**：真实 `p_macro_def` 返回 `()`，规则塞进旁路 `HashMap`（`mod.rs:2339-2386`）。

**推论**：即使用 parser 的输出，formatter 也必须回到 token/原文层。因此「改造 parser」
若指「改造 A**ST/文法/CST**」，收益只是更聪明的布局，而代价是把 3600+963+358 行递归下降
改造成无损结构——不值得。

### 2.2 parser 的 token 契约载荷敏感，`EndLine` 不能动

- `EndLine` 在 `parser/mod.rs` 出现 **76 次**，被用作 decl 分隔
  （`.many1_sep_skip(kw(EndLine), ...)` `:332`、`.many0_sep((kw(T![,]), kw(EndLine).option()))` `:559,639`…）。
- **宏匹配显式计数 EndLine**，源码注释即证据（`parser/mod.rs:255-288`）：
  「matcher skips one EndLine after a match」「the literal-Token matcher eats one EndLine after each」
  「put the trailing EndLine back」。
- `preprocess` **保留换行**（`replace_non_ws_preserve_bytes` 只替换非空白字符为等长空格），
  所以**多行块注释内部的 `\n` 当前照常产生 `EndLine` token**。

**危险**：若让 lexer 把注释当整体 trivia 吞掉，EndLine 数量改变 → 宏匹配与 decl 分隔可能错乱。
因此 **token 契约必须冻结**；trivia 只能走**旁路**，不能改变 parser 看到的 token 流。

### 2.3 不要在分析热路径上保留 token 流

formatter 是低频请求，**按需 lex 一次**（O(n)）即可。
若在 `parser_with_macros` 里把 token Vec 常驻进文档状态，会给每个文档增加内存/CPU 开销，
回退主线刚获得的性能收益（R9）。**结论：不保留 token，format 请求内现 lex。**

---

## 3. 推荐架构 v2：扩展 lexer + trivia 侧信道 + 独立布局引擎

### 3.1 组件

```
src/L13_namespace/parser/lex.rs      ← 扩展（同一文件，复用既有字符表）
    lex(...)                         既有入口，签名/语义不变
    lex_with_trivia(raw, id)         新增：token 流 + trivia 列表
    scan_comments(raw)               新增：字符串感知的注释扫描（供侧信道）

src/format/                          ← 新增
    layout.rs                        布局引擎（token + trivia → 文本）
    mod.rs                           入口 format_document / token_signature / FormatOptions
```

**不再新写第二个 lexer**：字符串/运算符字符表、关键字识别全部复用 `lex.rs`，从根上消除漂移。

### 3.2 trivia 侧信道的确切形态

```rust
/// 注释 trivia（原文坐标；preprocess 保字节偏移，故与 token span 对齐）。
pub enum TriviaKind { LineComment, BlockComment }
pub struct Trivia { pub kind: TriviaKind, pub start: u32, pub end: u32 }

/// 既有行为 + trivia。tokens 由既有算法在 preprocess(raw) 上产出，
/// 保证 parser 契约逐字节不变；trivia 从 raw 扫描，字符串感知。
pub fn lex_with_trivia(raw: &str, id: u32)
    -> Option<(OwnedInput, Vec<OwnedToken>, Vec<Trivia>)>;
```

要点：

- **token 流来源不变**：仍走 `lex(preprocess(raw))` 这条路径，`EndLine` 折叠/计数完全一致 ⇒
  hover/goto/inlay/宏/twin 不受影响。trivia 只是**附加输出**。
- **注释扫描必须字符串感知**（正确处理 `\` 转义），否则字符串里的 `//` 会被误判——
  这正是现有 `preprocess` 的缺陷所在，侧信道不能复制它。
- **换行信息不必单独存**：两个 token span 之间的原文 gap 里就含换行与注释；
  布局引擎按 offset 合并三者即可（token 文本/注释文本均从 **raw** 按 span 取，逐字保真）。

> 实现上 `lex_with_trivia` 可先 `let pre = preprocess(raw);`（调用方持有 `String` 保证生命周期），
> 再 `lex(Span{data:&pre,..})` 取 token，同时 `scan_comments(raw)` 取 trivia。

### 3.3 布局引擎 `format/layout.rs`

**核心不变量**：输出 = 遍历 lexeme（token ∪ trivia）流，只重新选择相邻元素之间的空白与行首缩进。
token 文本、注释文本**逐字照抄** ⇒ 结构上满足 R1/R2/R7。

- **缩进**：括号上下文栈（`{ [ (` 入栈，缩进 +1）。
- **换行（Phase 1 保守）**：**保留用户原有换行位置**，只重排缩进；≥2 连续空行折叠为 1（可配置）；
  删行尾空白；文件末尾恰好一个换行。
- **token 间空白（表驱动）**：依据 `docs/syntax.md` §4 优先级表 + 语料风格：
  `,`/`;` 前无空格后一空格；`)`/`]`/`}` 前无空格；`.` 两侧无空格；二元运算符两侧各一空格；
  前缀 `!`/负号后无空格；`[` 在前 token 为 Ident/`)`/`]` 时无空格（`Vec[A]`、`x[i]`）；
  `:` 前无空格后一空格；原子相邻（应用 `f x`）保持单空格。
- **冻结区**（原样保留，仅整体缩进）：宏体 `macro_rules NAME { ... }`（R7）、字符串/字符字面量、
  注释文本、多行块注释内部（含 ASCII art）。

**Phase 1 明确不做**：重排顺序、拆行、合行、改宏体、增删括号。

### 3.4 后续可选：把 `preprocess` 并入 lexer（修 `//`-in-string）

长期最干净的做法是让 lexer 自己识别并跳过注释（注释进 trivia），退役 `preprocess`，
顺带修掉字符串含 `//` 被抹掉的缺陷（现有 `preprocess` 对每行 `split_once("//")`，不区分字符串）。
但**必须精确复刻当前 EndLine 语义**：多行块注释内部的 `\n` 仍要产出等量 `EndLine`
（因为 `preprocess` 保留换行，parser 与宏匹配都依赖它）。
**前置条件**：`token_signature` 不变量测试已在全语料通过。**不作为第一步**。

---

## 4. 失败策略与自检（R4）

`format_document` 在以下情况返回 `None`：
未闭合字符串/块注释；括号深度为负或 EOF 非零；出现 lexer 无法识别的字符。

**双重安全网**：
1. `token_signature(output) != token_signature(input)` ⇒ 丢弃返回 `None`
   （证明注释不丢、token 不增删重排，即 R1+R2）；
2. `format(output) != output`（不幂等）⇒ 丢弃返回 `None` 并 log。

`token_signature(text)` 忽略空白后的 `Vec<(Class, String)>`，是本方案的核心可测不变量。

---

## 5. LSP 接线（精确落点）

| 位置 | 改动 |
|------|------|
| `src/lib.rs:45` | import 增加 `Formatting`（`lsp_types::request::Formatting`） |
| `src/ls.rs` | trait 增加默认方法 `fn formatting(&self, p: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>>`，默认 `Err(Error::method_not_found())` |
| `src/lib.rs:2635-2672` | `ServerCapabilities` 增加 `document_formatting_provider: Some(OneOf::Left(true)),` |
| `src/lib.rs:3016-3130` | `main_loop` 在 `ExecuteCommand` 分支后追加 `cast::<Formatting>` 分支（照抄现有样板） |
| `impl LanguageServer for Backend` | thin forwarder → 固有方法 `pub fn format_document_at(&self, uri, opts) -> Option<Vec<TextEdit>>` |

handler 要点：
- 取文本用 `self.document_buffers`（`did_change` 同步更新），而非 `document_map`（分析后更新，滞后）。
- 产出**单个全文 `TextEdit`**；若结果与原文相同 → `Ok(Some(vec![]))`（空编辑，避免弄脏 buffer）。
- 保持为可测试的固有 `pub fn`，沿用 `hover_at`/`completion_at`/`inlay_hint_at` 模式。
- **按需 lex**，不把 token 流挂到文档状态（R9）。

配置：`tab_size`/`insert_spaces` 取自每请求 `FormattingOptions`；额外项（`max_blank_lines`、
是否格式化宏体）从 `InitializeParams.initialization_options` 读。**不读 `Typort.toml`**
（`src/config.rs` 的 `Config::discover` 仅 CLI 使用，LSP 从不读；`did_change_configuration` 是 no-op，`lib.rs:2833`）。

---

## 6. VS Code 扩展

- **无需改客户端代码**：`vscode-languageclient` 依服务端 `document_formatting_provider` 能力自动接线。
- 可选：`vscode_extension/package.json` 增加 `"[typort]": { "editor.formatOnSave": false }` 默认值。
- web/wasm 变体共用同一 server：务必实现「无变化 → 空编辑」路径。

---

## 7. 测试策略

- **语料金标 + 幂等**：对 `examples/**/*.typort`（28 个）与 `tools/spinalhdl-verify/cases/*.typort`，
  断言 `format(format(x)) == format(x)` 且 `token_signature(format(x)) == token_signature(x)`。
- **注释保持**：注释数量与文本（除行首缩进外）不变。
- **聚焦用例**：空行折叠、行尾空白、末尾换行、嵌套括号、CRLF 保持、字符串内 `//` 不被当注释、
  宏体不动、未闭合输入 → `None`。
- **快照**：`tests/fixtures/format/*.typort`（input/expected），`UPDATE_SNAPSHOTS=1` 重生成。
- **handler 测试**：仿 `tests/completion_handler_tests.rs` / `tests/hover_tests.rs`，用 `CapturingClient`
  构造 `Backend`，`load_prelude()`，`process_file(...)`，调 `format_document_at`，断言单个 TextEdit。
- 命令：`cargo test`、`cargo test --test format_tests`。
  注意 `.github/workflows/ci.yml` **没有 `cargo test` 门禁**（仅打包 VSIX + 交叉编译 CLI）。

---

## 8. 分期与交付

| 阶段 | 内容 | 规模 |
|------|------|------|
| **Phase 0（打样）** | `lex_with_trivia` / `scan_comments`（字符串感知）+ `token_signature` + 全语料 round-trip 校验。**门槛：全语料 token 签名不变** | ~1d |
| **Phase 1（核心）** | `format/layout.rs`：缩进 + token 间空白 + 空行/行尾/末尾策略；冻结区；LSP 能力接线；幂等 + token 不变测试 | ~2-3d |
| **Phase 2（打磨）** | 关键字驱动的文法缩进（`match`/`case`/`module`/`when`）、长表达式续行、`max_width` 软换行、配置面、`textDocument/rangeFormatting` 复用同引擎 | ~2d |
| **Phase 3（可选）** | `src/bin/cli.rs` 增加 `typort fmt [--check] [--write]`；给 `ci.yml` 加 fmt-check/test 门禁 | ~1d |
| **Phase B（可选迁移）** | 把 `preprocess` 注释处理并入 lexer，修 `//`-in-string；以 token 不变量测试为闸门 | ~2d |

**Tier 0 兜底**：仅行尾空白 + 末尾换行 + 空行折叠（无结构重排），一天可交付、近乎零风险。

---

## 9. 风险与缓解

| 风险 | 缓解 |
|------|------|
| 词法布局覆盖不到的文法缩进（`match`/`case`/`where`） | Phase 1 保留原有换行，只按括号深度重排缩进；Phase 2 增量加关键字规则，以金标 + token 不变测试为闸门 |
| 误改 parser token 契约导致宏匹配/decl 分隔回归 | **冻结** token 流与 EndLine 语义；trivia 只走旁路；先跑 twin-engine + 语料回归 |
| 宏体 / 优先级敏感 token | 冻结区逐字保留；绝不增删 token |
| 字符串含 `//`（`preprocess` 缺陷） | 侧信道扫描器字符串感知；Phase 1 只保证不破坏，Phase B 迁移后修复 |
| CRLF/LF 抖动 | 探测主导 EOL 并保持；保留 BOM；可配置覆盖 |
| wasm 帧大小 / 性能 | 全文单编辑；O(n) 按需 lex；尺寸阈值（>1MB 直接 `None`） |
| 幂等失败 | handler 硬闸门：不幂等则 `None` 并 log |

---

## 10. 关键代码索引

- 注释抹除（保留换行）：`src/L13_namespace/mod.rs:3976`（`preprocess`）
- 换行折叠 / 空白跳过：`src/L13_namespace/parser/lex.rs:288`、`:299-304`
- 字符串/运算符字符表：`src/L13_namespace/parser/lex.rs:163-284`
- token 流产生点（局部、可加 trivia 出参）：`src/L13_namespace/parser/mod.rs:320-332`
- EndLine 载荷敏感证据：`src/L13_namespace/parser/mod.rs:76` 处使用，`:255-288` 宏注释
- desugar：`parser/mod.rs:1352-1399`（where）、`1690-1701`（struct→enum）、`p_macro_def` `:2339-2386`
- 无整体 span / `Import` 无 span：`parser/syntax.rs:290-356`、`:295-299`
- 能力声明：`src/lib.rs:2635-2672`；分发与 import：`src/lib.rs:3016-3130`、`:45`
- trait 默认方法模式：`src/ls.rs`
- 可测试固有 handler 模式：`tests/completion_handler_tests.rs`、`tests/hover_tests.rs`
- 风格与优先级：`docs/syntax.md` §1、§4
- 语料：`examples/hdl/*.typort`（23）、`examples/*.typort`
- wasm 分块：`src/lsp_stdio.rs`
- `FormattingOptions`/请求类型：lsp-types-0.95.1 `formatting.rs:28,42`、`request.rs:566-572`、`lib.rs:1983`

---

## 11. 深度路线：从 trivia 侧信道到无损 CST

### 11.1 现状可改造性评估（实测）

- parser 是组合子 parser，输入类型 `I` 在 trait 上是泛型（`parser_lib_resilient.rs:5`），
  但**所有实例都被具体绑定为 `&'b [TokenNode<'a>]`**：`ParserExt` impl（`parser/mod.rs:198`）、
  45 个 `p_` 产生式、136 处 `.parse(`。
- 直接操作 token 切片约 **57 处**（`input[i..]`、`.len()`、`.first()`、`&input[..]`）；
  其中宏逻辑用**切片长度差**计算 consumed：`let consumed = input.len() - i.len();`
  再 `input[consumed-1]` 反查 span/kind（`parser/mod.rs:1202-1290`、`:1457`）。
- **无任何 event / marker / node-range 机制**；AST 是 desugar 后的 `Vec<Decl>`，span 不全。
- 语料与内置库（`examples/`、`prelude/`）**0 个块注释**，多行块注释的 EndLine 语义风险
  只存在于用户文件。

### 11.2 三个深度

**D1（= v2）**：trivia 侧信道 + 括号深度启发式布局。
1 周级，风险最低，文法感知弱。

**D2：trivia 挂 token + 块级结构范围（CST-lite）。**
- lexer 产出 lossless token 流；trivia 作为 leading/trailing 挂在相邻 token 上，
  而 **parser 仍消费同一份「trivia-过滤后」的 token 切片** ⇒ token 契约不变。
- 在少量**块级**产生式（顶层 decl、`{}` 块、`match`、`module`、`trait`/`impl` body 等，
  约 10–20 个 hook）记录 token index 范围，产出 `Vec<NodeRange>` 侧表。
- 布局引擎据此做**文法感知缩进**（`case` 相对 `match`、`when/else`、`module` body、`where`）。
- parser 输入类型不变，改动收敛在 lexer + 十几个 hook；2 周级。
- **同时是 D3 的第一里程碑**（不浪费）。

**D3：无损 CST（green tree，rust-analyzer 事件模型）。**
- lexer：在**原始文本**上产出 trivia 化的 lossless token 流（注释/空白/换行），EndLine 语义需复刻。
- 把 parser 输入从 `&[TokenNode]` 换成 **Cursor**（透明跳过 trivia + 发事件
  `Start(kind)/Token/Finish`）；组合子 core 与 45 个产生式随类型改动；
  再加 `GreenNodeBuilder` 组装绿树。
- **关键边界**：宏展开产物是**合成的**（`owned_tokens_to_string` 拼接后 re-lex，
  `parser/mod.rs:133-149`），不来自用户文本，**不进 CST**；CST 只覆盖**写出来的源码**
  （`p_macro_def` 旁路 + 宏调用节点）。formatter 也只格式化写出来的源码，正好吻合。
- 代价：仓库**最高风险文件**（twin-engine parity、诊断、宏匹配全依赖它）的整体重构，周级偏月级。
- 收益：不止 formatter —— 语法级 rename/refactor、更好的错误恢复、语义 token 直出、
  增量解析、lossless round-trip（linter/外部工具）。

### 11.3 关键判断

- 若「更深」是为了 **format 质量**：D2 已覆盖约 90% 收益（文法感知缩进），D3 边际收益小。
- 若「更深」是为了**一个可复用的语法层**：D3 值得，且应作为**独立平台项目**立项，
  formatter 只是第一个消费者。
- 无论哪条，**D2 都是必经且无浪费的第一步**：它完成 lexer trivia 化与结构范围侧表，
  D3 在此之上换 Cursor 即可，不必推倒重来。

### 11.4 建议分期

D2（里程碑 1）→ 用真实语料验证文法感知缩进 → 再决定是否继续 D3。
每个阶段以 `token_signature` 不变量 + twin-engine 语料回归为硬闸门。

---

## 12. 实现状态

### 已完成（D2 / Phase 1）

- `src/format/mod.rs` + `src/format/layout.rs`：字符串感知 trivia 扫描器；基于真实 L13 lexer 的
  布局引擎（缩进、token 间空白、空行折叠、行尾/末尾规范化、CRLF 保持、注释/字符串逐字保留）。
- 文法感知缩进：括号深度、非花括号体续行（`=`/`=>`/`->`/`where`）、HDL `module NAME[params]`
  跨行头、行首 `{` 归位。
- 双重安全网：`token_signature` / `comment_signature` / `string_signature` 不变 + 幂等；
  不安全输入返回 `None`。
- LSP：`document_formatting_provider` 能力、分发、`format_document_at` 固有方法。

### 已完成（Phase 2）

- **长表达式续行**：行尾二元运算符（非前缀 `-`/`!`/`~`）触发续行缩进。
- **配置面**：`InitializationParams.initialization_options.format`
  （`indentWidth`/`useTabs`/`maxBlankLines`/`maxBytes`，camelCase）；显式配置优先，
  否则回退到每请求 `FormattingOptions.tabSize`/`insertSpaces`。
- **`textDocument/rangeFormatting`**：布局引擎输出「输出行 → 源行」映射，
  仅替换所选整行范围；能力、分发、`format_range_at` 与 `format_range` API 均已落地。

### 未做（有意延后）

- **`max_width` 软换行**：需要文法感知的断点选择，token 启发式做不到位，留给 D3（CST）。
- 字段/枚举项的列对齐：收益不明确，暂不做。

### 验证

- 单测 + 语料不变式（28 个 `examples/**/*.typort`）：token/注释/字符串不变 + 幂等 +
  「全选范围 == 全文格式化」。
- handler 端到端（含 range 与配置）：通过。
- 回归：库单测 680 通过（`--test-threads=1`；默认并行下的访问违例是既有的 worker 线程栈问题）；
  completion 12/12、hover 20/20、twin-engine parity 8/8。

### 下一步

D3（无损 CST / Cursor 重构）的 go/no-go 仍待决定——见
[format-deep-design.md](./format-deep-design.md)。
