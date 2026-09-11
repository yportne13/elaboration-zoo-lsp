# Format Document 深度路线详细设计（D2 → D3）

> 状态：设计稿（未实现）
> 基线：`master` @ f4d5da8
> 上游：[format-document-design.md](./format-document-design.md) §11（深度路线总览）
> 默认风险姿态：**不回归主线为硬前提，分小步合入，每步可回退**。

---

## 0. 一句话

- **D2（里程碑 1）**：lexer trivia 化 + 文法感知的**布局引擎**（token 驱动），配 3 个通用括号 hook
  取结构范围；不建树、不改 parser 输入类型。
- **D3（终点）**：把 parser 输入换成 **Cursor**，以 `Deref<Target=[TokenNode]>` 逐产生式迁移，
  加事件流 + `GreenNodeBuilder` 得到**无损 CST**；formatter 成为其第一个消费者。

两者共用同一套「trivia + token + 布局引擎 + 自检」，D3 只是把布局引擎的“上下文来源”从
启发式/侧表换成 CST。

---

## 1. 实测约束回顾

| 事实 | 出处 |
|------|------|
| parser 输入类型虽泛型，但所有实例钉死为 `&'b [TokenNode<'a>]` | `parser_lib_resilient.rs:5`；`parser/mod.rs:198` |
| 45 个 `p_` 产生式，136 处 `.parse(` | `parser/mod.rs` |
| ~57 处直接操作 token 切片；宏用 `input.len() - i.len()` 反推 consumed | `parser/mod.rs:1202-1290`、`:1457` |
| `brace`/`paren`/`square` 是通用括号 helper | `parser/mod.rs:487-541` |
| 无 event/marker/node-range；AST desugar 且 span 不全 | §11.1 |
| 语料与内置库 0 个块注释 | `examples/`、`prelude/` |
| 宏展开产物是合成文本（re-lex），不来自用户源码 | `parser/mod.rs:133-149` |

---

## 2. D2 详细设计：trivia 层 + 文法感知布局

### 2.1 lexer 改动（`L13_namespace/parser/lex.rs`）

```rust
pub enum TriviaKind { Whitespace, Newlines(u32), LineComment, BlockComment }
pub struct Trivia { pub kind: TriviaKind, pub start: u32, pub end: u32 }

/// 既有入口，签名/语义不变（parser 继续用它）。
pub fn lex(input: Span<&str>) -> Option<(Input<'_>, Vec<Token<'_>>)>;

/// 新增：在 raw 上扫 trivia（字符串感知），与 token 流并行输出。
/// tokens 仍来自 lex(preprocess(raw)) 以保证 EndLine 契约不变。
pub fn lex_with_trivia<'a>(raw: &'a str, id: u32)
    -> Option<(OwnedInput, Vec<Token<'a>>, Vec<Trivia>)>;
```

要点：
- **token 契约冻结**：tokens 仍旧走 `lex(preprocess(raw))`，`EndLine` 折叠/计数完全一致。
- **trivia 字符串感知**：正确处理 `"` 转义，避免把字符串内 `//`、`/*` 当注释（这是
  `preprocess` 的既有缺陷，侧信道不得复制）。
- **两种挂载形态**（择一，建议后者的轻量版）：
  - 侧表：`Vec<Trivia>` + 按 offset 与 token 合并（D1 已用）。
  - **挂 token**：`leading[i] = Vec<Trivia>` 并行数组，索引与 token 对齐 →
    布局引擎可 O(1) 取「某 token 前面的注释/空行」。parser 不读这个数组，契约不变。

### 2.2 布局引擎（`src/format/layout.rs`）

在 D1（括号深度 + token 间空白表）之上加**文法感知规则**，全部由 token 流驱动：

| 规则 | 触发 token | 效果 |
|------|-----------|------|
| 块体缩进 | 行尾 `{` / 行首 `}` | `{` 后 +1，`}` 行先 -1（已有） |
| match 臂 | `match` 后首个 `{` 内的 `case` | `case` 与其所在 `{` 同级缩进；`=>` 后换行时 +1 |
| HDL 控制块 | `when` / `else` / `switch` | 提高一层；`else` 与对应 `when` 对齐 |
| 模块/类型体 | `module` / `trait` / `impl` / `class` / `struct` / `enum` 后 `{` | body 缩进 +1（`{` 规则已覆盖） |
| where 子句 | `where` | 独立缩进层级，逗号后换行对齐 |
| 隐式应用 | `[` 前 token ∈ Ident/`)`/`]` | 无空格（`Vec[A]`、`x[i]`） |

**结构性 hook（可选增强）**：`brace`/`paren`/`square` 各插一处，记录其 token index 范围到
`MacroState` 侧通道（或一个独立 `Vec<BracketRange>`），得到精确的括号树。
但注意：**这 3 个 hook 能拿到的信息，与在 token 流上做括号匹配几乎等价**——
因此 D2 的真正增量在 §2.2 的关键字规则，而非 parser hook。**建议 D2 先不插 hook**，
用 token 流括号匹配即可，把 parser 改动压到零。

### 2.3 布局引擎输入/输出

```
输入：raw 文本、opts、trivia 表、token 流（含 span）
处理：按 offset 合并 token ∪ trivia → 逐「逻辑行」决定缩进与行内空白
输出：Option<String>（None = 拒绝格式化）
```

不变量：**输出只由「原始 lexeme 序列 + 空白决策」构成**，token/注释文本逐字照抄。

### 2.4 自检（硬闸门，D2/D3 共用）

```rust
fn token_signature(text: &str) -> Option<Vec<(Class, String)>>; // 忽略空白/换行
```
handler 内：
1. `token_signature(out) != token_signature(in)` → `None`（保注释、保 token）；
2. `format(out) != out` → `None`（幂等）；
3. 括号深度异常/未闭合 → `None`。

### 2.5 交付物与验收

- 新增：`src/format/{mod.rs,layout.rs}`；`lex_with_trivia`。
- 改动：`src/lib.rs`（能力 + 分发 + handler）、`src/ls.rs`（trait 默认方法）。
- 验收：全语料 `token_signature` 不变 + 幂等；金标文件人工 review；
  twin-engine 语料回归零差异（因为 parser 未被改动）。

---

## 3. D3 详细设计：Cursor 重构 + 无损 CST

### 3.1 目标形态（rust-analyzer 事件模型）

```
raw ──lex_lossless──▶ Vec<TokenNode>（含 trivia）
                         │
                    Cursor（透明跳过 trivia，发事件）
                         │  Start(kind)/Token/Finish
                         ▼
                  GreenNodeBuilder ──▶ GreenNode（无损 CST）
                         │
              layout/format 渲染 ──▶ 格式化文本
```

CST 只覆盖**用户写出来的源码**；宏展开产物（合成文本）不进树，对应节点标记为
`opaque`（`p_macro_def` 旁路 + 宏调用节点）。

### 3.2 lexer：trivia 化（lossless）

- 在 raw 上 lex，新增 `TokenKind::{Whitespace, LineComment, BlockComment}`（或独立 trivia 流）。
- **EndLine 语义复刻**：多行块注释内部的 `\n` 在当前 `preprocess` 下仍产生 `EndLine`。
  D3 要么复刻此行为，要么明确改变语义并以测试覆盖。语料 0 块注释 → 风险仅限用户文件，
  但仍需在 harness 中造样例。
- 退役 `preprocess`（可选，作为 D3 的一部分或稍后）：顺带修 `//`-in-string。

### 3.3 Cursor：用 `Deref` 把「大爆炸」变成「逐产生式」

**关键技巧**：新类型包住切片并实现 `Deref<Target = [TokenNode]>`：

```rust
#[derive(Clone, Copy)]
pub struct Cursor<'a, 'b> { toks: &'b [TokenNode<'a>], pos: usize }

impl<'a, 'b> std::ops::Deref for Cursor<'a, 'b> {
    type Target = [TokenNode<'a>];
    fn deref(&self) -> &Self::Target { &self.toks[self.pos..] }
}
```

这样 `input.first()`、`input.len()`、`input.get(1..)`、`input[i..]` 等
**~57 处切片操作可原样编译**；只有需要「发事件/推进 pos」的地方才显式用 Cursor API。
→ parser 可以**逐个产生式**从 `&[TokenNode]` 迁到 `Cursor`，每步跑基线回归，不必一次改完。

迁移顺序建议：
1. 引入 `Cursor` + `Deref`（零行为变化），全量基线回归；
2. `Parser` trait 的 `I` 实例化改为 `Cursor`，组合子 core（`parser_lib_resilient.rs`）
   与 `ParserExt` 适配；
3. 45 个 `p_` 产生式逐个改签名并跑回归（可分批）；
4. 宏的长度差逻辑改为 `cursor.remaining()` / 显式位置记录（`parser/mod.rs:1202-1290`、`:1457`）；
5. 引入事件 sink 与 `GreenNodeBuilder`，先只对 `Decl` + 块级节点建标记；
6. 逐步细化到表达式节点。

### 3.4 事件与绿树

```rust
enum Event { Start(SyntaxKind), Token, Finish }

// 在产生式内（示意）
let m = sink.start();            // 记录
... parse ...
sink.start_node_at(m, SyntaxKind::Def);
... bump tokens ...
sink.finish_node();
```

- `SyntaxKind`：先覆盖 `File / Decl 各类 / Block / MatchArm / ModuleBody / TraitBody / ImplBody /
  Comment / Whitespace / Error`，表达式子类后续增补。
- trivia 通过事件 `Token` 进入树，成为叶子的 leading/trailing，天然解决注释归属。

### 3.5 宏边界（必须明确）

- `macro_rules` 定义体：整段标 `opaque`，树中作为一个叶子/错误容忍区，不解析内部。
- 宏调用：CST 记录**调用点**（源码里的 token），展开产物不进树。
- 因此 CST 是「用户书写源码」的无损表示，与 formatter 的作用域一致。

### 3.6 代价与闸门

| 项 | 评估 |
|----|------|
| 触及面 | 组合子 core + 45 产生式 + ~57 直接切片点 + 宏长度逻辑 |
| 风险 | 最高风险文件；twin-engine parity / 诊断 / 宏匹配全依赖 |
| 量级 | 周级偏月级（用 Deref 迁移 + 分批回归可摊平） |
| 闸门 | 每步 ① 全语料 `token_signature` 不变 ② twin-engine 表零差异 ③ 现有测试全绿 |
| 回退 | 每步独立 commit，可单步 revert |

### 3.7 D3 的收益（超出 formatter）

语法级 rename/refactor、错误恢复、语义 token 直出、增量解析、lossless round-trip
（linter/外部工具）。**若这些不是目标，D3 对 format 的边际收益很小，应停在 D2。**

---

## 4. 备选：并行「结构扫描器」而非重构真 parser

不愿承担 Cursor 重构风险时，可写一个 ~300 行的**轻量结构扫描器**（只跟踪
decl / 块 / match 臂 / 关键字层级）在 lossless token 流上建**浅 CST**，供 formatter 用。

- 优点：零 parser 风险，D2 即刻可用。
- 缺点：**第二个解析器**，与「单一 tokenizer / 不另起炉灶」的目标相悖；
  语法演进时需同步维护，长期漂移。

**取舍**：若追求单一真源与长期平台价值 → D3（重构真 parser）；若只求 formatter 质量与低风险
→ D2 + 扫描器。二者的 formatter 上层（布局引擎、自检、LSP 接线）完全相同。

---

## 5. 建议执行顺序（默认方案）

1. **D2-a**：`lex_with_trivia` + `token_signature` + 全语料不变量 harness。门槛：签名全绿。
2. **D2-b**：布局引擎（缩进 + 空白表 + 空行/行尾/末尾 + 冻结区 + 关键字规则）。
3. **D2-c**：LSP 能力接线 + handler + 测试（仿 `completion_handler_tests.rs`）。
4. **D2-d**：用真实语料 review 效果，决定是否继续。
5. **D3-a**：`Cursor` + `Deref`（零行为变化）+ 基线回归。
6. **D3-b…**：逐产生式迁移、事件、绿树、formatter 切到 CST。
