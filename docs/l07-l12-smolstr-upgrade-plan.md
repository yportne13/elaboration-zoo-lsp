# L07–L12 名字类型升级 SmolStr：可行性勘察（2026-11-26）

> 结论先行：**这不是机械替换，是表示层重构。** 单章 67 处 `Span<String>` + 8 处 `Vec<String>`，
> 但真正的难点是 L07–L12 把三种语义混用在同一 `String` 类型里，必须先拆开。
> 本轮只做了勘察与一次失败的机械替换实验（已回退），未提交任何代码改动。

## 1. 规模实测

| 章 | `Span<String>` | `Vec<String>` | 涉及文件 |
|---|---:|---:|---:|
| L07 | 67 | 8 | 10 |
| L08 | 67 | 8 | 10 |
| L09 | 67 | 8 | 10 |
| L10 | 87 | 8 | 11 |
| L11 | 93 | 8 | 12 |
| L12 | 90 | 8 | 12 |

（`bump_spine_iter` 孪生树未计入——它们是独立封印的模块树。）

对照 L13：`SmolStr` 出现 **959** 处、`Span<String>` **39** 处、`String` **581** 处。
L13 已经完成了这次升级，且规模比 L07–L12 的升级面大一个量级——因为它同时承载了 trait/macro/namespace 等新语法面。

## 2. 机械替换实验（失败，已回退）

做法：把所有 `Span<String>` → `Span<SmolStr>`（`LiteralIntro` 除外），补 `use smol_str::SmolStr`。

结果：**63 个编译错误**，分布如下：

| 文件 | 错误数 | 典型错误 |
|---|---:|---|
| `mod.rs` | 27 | `E0308` 类型不匹配（`Tm`/`Val`/`VSpan` 定义） |
| `cxt.rs` | 13 | `E0308`（名字表键类型、`names()` 返回 `List<String>`） |
| `pattern_match.rs` | 8 | `E0277` + `E0308`（`Vec<String>` 的 `ctor_names`） |
| `elaboration.rs` | 7 | `E0308`（`completion_table` 等） |
| `parser/syntax.rs` | 7 | **`E0599` `no method named push/push_str`** |
| `observe.rs` | 6 | `E0308` |
| `pretty.rs` | 5 | `E0308` |
| `surface.rs` | 5 | `E0271` + `E0308` |
| `unification.rs` | 3 | `E0308` |
| `parser/mod.rs` | 2 | `E0271` |
| `raw_pretty.rs` | 1 | `E0308` |

**63 个错误全部是「边界转换」问题，没有一个是逻辑错误**——这说明替换方向对，但缺一层转换。

## 3. 真正的难点：三种语义混用

L07–L12 的 `String` 同时承载三种语义：

| 语义 | 典型位置 | 该用什么 |
|---|---|---|
| **名字** | `Tm::Pi(Span<String>, ..)`、`Val::Sum(..)`、名字表键 | `SmolStr` |
| **字符串字面量** | `Raw::LiteralIntro(Span<String>)`、`Val::LiteralIntro` | **`String`**（用户内容） |
| **显示串** | `pretty()` 返回、错误消息、`report()` | **`String`**（一次性输出） |

L13 用两套类型把它们分开了；L07–L12 混在一起，所以机械替换必然在边界上炸。

失败实验里最典型的一类：`parser/syntax.rs` 的 `E0599 no method named push found for SmolStr`——
那是 `Pattern::pretty()` 里的 `let mut s = name.data.clone(); s.push('(');`，
**`s` 是显示串，不该变成 SmolStr**。这类地方机械替换必然误伤。

## 4. 正确的做法（下一步）

按 L13 的模板，分三步：

### 步骤 1：引入语义别名（低风险，可先做）

```rust
/// 名字（绑定、构造子、字段、模块）——短、反复比较与克隆，用内联表示。
pub type Name = SmolStr;
/// 字符串字面量内容——用户数据，可能任意长。
pub type LitStr = String;
```

然后把 `Span<String>` 按语义逐处改成 `Span<Name>` 或 `Span<LitStr>`。
这一步纯类型别名，行为等价。

### 步骤 2：边界转换

63 个错误里有 50+ 是「名字 ↔ 显示串」的边界，需要：

- `Lit(..)` 那一侧加 `SmolStr::new(...)`；
- `pretty()` 那一侧加 `.to_string()` 或 `.as_str()`；
- 名字表的键类型跟着变（`BiMap<String, ..>` → `BiMap<SmolStr, ..>`）。

### 步骤 3：逐章推进

每章独立做，因为它们各有自己的 `mod.rs`/`cxt.rs`/`parser`。按 L07 → L12 的顺序，
每章做完跑该章的 lib 测试 + 全量门禁。

## 5. 工作量估计与风险

| 项 | 估计 |
|---|---|
| 单章改动点 | 75 处（67 + 8），其中约 20 处需要人工判断语义 |
| 六章合计 | 约 450 处 |
| 每章需跑 | lib 测试 + chain_inheritance + oracle |
| 主要风险 | 误把显示串/字面量改成 SmolStr（编译能过但语义错，只有测试能抓） |

**测试是安全网**：L07 71 / L08 83 / L09 83 / L10 86 / L11 88 / L12 88 个 lib 测试全部通过，
其中含大量 `pretty` 输出比对，能抓住「显示层误改」这类错误。

## 6. 本轮状态

- 机械替换实验已 `git checkout` 回退，**工作区干净**；
- `cargo check --release --lib` 通过（check=0）；
- 未提交任何代码改动（只提交本文档）。
- 上一轮的 matchbench 提交（`8364a657` / `272eabd4` / `98cc00f8`）保持有效。
