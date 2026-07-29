# 解析器错误报告与恢复 — 升级笔记

## 动机

将 L13（Typort）解析器的错误报告与恢复升级为更像 chumsky。本文档记录设计决策、剩余想法以及当前手写解析器库与有原则的错误恢复系统之间的差距。

---

## 已应用的修复

### 定界符包装器吞掉声明分隔符（2026 年 7 月）

**问题。** `paren_cut`、`square_cut` 和 `brace` 在内层内容*之后*、闭定界符 token *之前*使用了一个单独的 `kw(EndLine).option()` 元素。当缺少闭定界符时，这个 `EndLine.option()` 消费了分隔声明的换行符，导致下一个 `def`/`enum`/`struct` 被视为畸形组内的错位内容，而不是新的声明。

示例输入：
```typort
def foo: Nat = (1 + 2

def bar: Nat = 3
```

`def bar` 被静默丢弃；报告了两个错误（都在 `def` 处）。

**修复。** 将尾部的 `kw(EndLine).option()` 与闭定界符合并为**单个** Cut 元素：

```rust
// 之前（4 个元素）
Cut((kw(LParen), kw(EndLine).option(), p, kw(EndLine).option(), kw(RParen)))

// 之后（3 个元素）——尾部 EndLine 和 RParen 是一个元素
Cut((kw(LParen), kw(EndLine).option(), p, (kw(EndLine).option(), kw(RParen))))
```

当组合元素失败时，Cut 宏的终止分支返回 `($input, None)`——即元素运行*之前*的输入，因此 EndLine 永远不会被消费。声明分隔符得以保留。

同样，将**前导** `kw(EndLine).option()`（开定界符和内容之间）与内层解析器组合以保持对称：

```rust
Cut((kw(LParen), (kw(EndLine).option(), p), (kw(EndLine).option(), kw(RParen))))
    .map(|c| c.1.map(|(_, result)| result))
```

受影响的函数：`paren_cut`、`square_cut`、`brace`。

---

## 剩余想法（尚未实现）

### 1. 嵌套定界符感知的 `skip_until_decl`

当前的 `skip_until_decl` 向前扫描 `EndLine` 后跟声明关键字（`def`、`enum` 等）。它**没有**考虑定界符嵌套：

```
fn skip_until_decl(input) {
    input.iter()
        .enumerate()
        .find(|(i, t)| {
            t.data.1 == EndLine
                && input.get(i + 1).map(|next| is_decl_kw(next.data.1)).unwrap_or(false)
        })
        .map(|(i, _)| &input[i..])
}
```

chumsky 风格的 `nested_delimiters` 恢复会在跳过时跟踪 `()`、`[]`、`{}` 的嵌套深度：

```rust
fn skip_until_decl_nested(input) -> Option<&[TokenNode]> {
    let mut depth: i32 = 0;
    for (i, tok) in input.iter().enumerate() {
        match tok.data.1 {
            LParen | LSquare | LCurly => depth += 1,
            RParen | RSquare | RCurly => {
                depth -= 1;
                if depth < 0 {
                    // 没有匹配开括号的闭括号——同步点
                    return Some(&input[i..]);
                }
            }
            EndLine if depth == 0 => {
                // 在任何括号外部——检查声明分隔符
                if input.get(i + 1)
                    .map(|next| matches!(next.data.1, DefKeyword | StructKeyword | …))
                    .unwrap_or(false)
                {
                    return Some(&input[i..]);
                }
            }
            _ => {}
        }
    }
    None
}
```

**为什么这有帮助。** 当 `(` 从未被关闭时，解析器可以向前跳过而不会被未闭组内的 `\n` 混淆。它只在 `depth == 0` 时将 `\n` 视为声明分隔符。

**集成。** `skip_until_decl_nested` 是 `recover_with` 的 `skip` 参数的即插即用替换——不需要其他更改。

### 1b. `skip_until_decl` 不应在当前位置匹配

当第一个 token 恰好是 `EndLine` 后跟声明关键字时，`skip_until_decl` 可能返回与输入**相同**的位置。这导致 `recover_with` 返回 `Ok((input, fallback))` 而没有取得进展，依靠 `many1_sep` 中的分隔符（`kw(EndLine)`）向前推进。错误确实被推送到状态，但"恢复"是虚假的——解析器实际上没有消费任何无效内容。

修复：扫描时跳过位置 0：

```rust
fn skip_until_decl(input) {
    input.iter()
        .enumerate()
        .skip(1)  // 不要在当前位置匹配
        .find(|(i, t)| { ... })
        .map(|(i, _)| &input[i..])
}
```

### 2. `.or()` 的错误合并

当前的 `.or()` 组合子静默丢弃第一个备选项的错误：

```rust
fn or<P>(self, rhs: P) -> impl Parser<I, A, S, E> {
    move |input, state| self.parse(input, state)
        .or_else(|_| rhs.parse(input, state))
}
```

chumsky 的 `or()`：
- 比较*最远进度*偏移量——哪个分支在失败前消费了更多输入？
- 如果两者在同一偏移量失败，*合并*它们的 `expected` 集合。
- 产生类似 `expected ')' or ']' or keyword 'def'` 的错误，而非仅仅是 `expected ')'`。

### 3. `found` 追踪

当前错误只存储*期望什么*，不存储*实际发现了什么*。chumsky 的 `Rich` 同时存储两者：

```rust
// 当前
Expect(RParen)                         // "expected ')'"

// chumsky 风格
expected ')' found `def`               // "expected ')', found `def`"
```

这需要在错误中存储实际的 token（或其文本）。

### 4. 嵌套上下文堆叠

`ErrMsg` 当前只有一级上下文：

```rust
enum ErrMsg {
    Base(BaseMsg),           // Expect(RParen)
    In(Ctx, BaseMsg),        // In(Expr, Expect(RParen))
}
```

`extract_base` 辅助函数在包装时剥离内层上下文：
```rust
// In(Atom, In(Expr, Expect(RParen)))  →  In(Atom, Expect(RParen))
//                                      ← Ctx::Expr 丢失！
```

chumsky 可以堆叠多个标签：
```
while parsing expression
while parsing atom
in definition of `foo`
  └─ expected ')'
```

为了在不丢失 `Copy` 的情况下支持堆叠，上下文栈可以是小数组或使用 `SmallVec` 代替 `Box`。

### 5. `infix_binding_power` 中的运算符优先级

`infix_binding_power` 有一个兜底 fallback，给任何未识别的运算符返回 `(7, 8)`（第 741 行）。这意味着 `@`（词法分析为 `Op`）获得了一个绑定优先级并被当作真正的中缀运算符，产生两个相同的 `In(Atom, Expect(LParen))` 错误而非一个。

**修复：** 将 fallback 从 `(7, 8)` 改为 `return None`，使未识别的运算符被表达式解析器忽略。

---

## 当前架构与 chumsky 的对比

| 方面 | 当前（`parser_lib_resilient.rs`） | chumsky 0.9 |
|--------|--------------------------------------|--------------|
| Parser trait | `parse(&self, I, &mut S) -> Result<(I, A), E>` | `parse(&self, I) -> Result<(I, O), ParseError<I, E>>` |
| 状态 | `&mut S`——完全泛型 | `&mut C`——约束 trait |
| 错误类型 | 完全多态 `E` | `E: ParserError<I>` 带 merge/label/expect |
| Cut / 恢复 | `Cut<P>` + `recover_with` | `nested_delimiters` + `skip_then_retry_until` |
| 错误合并 | 无（丢弃第一个 err） | `or()` 中自动合并 |
| 上下文 | 单级（`In(Ctx, BaseMsg)`） | 可堆叠 `.context("…")` 标签 |
| 期望/找到 | 仅期望 | 同时有期望和找到 |
| 诊断输出 | `format!("{:?}")`（原始枚举） | 带源码片段的 `Rich`（通过 `codespan-reporting`） |
