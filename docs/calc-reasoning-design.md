# calc / reasoning 链式等式证明 — 设计

> 目标：为 Typort 引入 Lean4 `calc` / Agda `reasoning` 风格的链式等式证明，
> 把一串等号步骤组合成单个 `Eq a d` 的证明（用 `trans` 组合）。
> 本文档是**第一阶段（纯设计）**的产出：只做语法与实现路线决策，不涉及代码改动。

**当前状态（2026-08）**：设计已定并实现。2026-08 的 `by` 语法迁移（task/calc-by-syntax）
把每步从 `a = [p] b` 改为 Lean 风格的 `a = b by p`（详见 §9.5）。

---

## 0. 结论摘要

- **实现方式**：宏方案（一个 prelude 文件 + 三处 prelude 列表登记；parser 有两处
  小的兼容性改动，见 §9.3 —— 原设计“零 parser 改动”未兑现，但改动是通用的，
  对 when/switch 等既有宏无回归）。`by` 语法迁移额外加了词法器一个关键字
  （§9.5）。
- **语法形态**（v2，`by` 关键字版）：
  ```typort
  def foo: Eq a d =
      calc {
          a = b by p1
          b = c by p2
          c = d by p3
      }
  ```
  每步是 `term = term by proof`：`=` 分隔等式两端，`by` 引导证明（Lean
  `a = b := p` 的 Typort 版）。步骤以换行分隔；单行链 `calc a = b by p1 = c by p2`
  也可用。
  - **为什么 `by` 可行而 `:=` 不可行**：`by` 是新建的专用关键字 token
    （`TokenKind::ByKeyword`），既不是 Op 也不是 Ident —— 表达式解析器
    （`expr_bp` 只消费 Op/LParen/LSquare/Dot，`p_atom1` 只消费 Ident/数字/字符串/
    括号）**永远不会消费它**，所以 `$y: raw` 片段在 `by` 前干净停止。
    `:=` 则被 lex 成中缀 Op，`$y: raw` 会把 `b := (p1)` 整体吞掉（详见 §4.2）。
- **转写目标**：展开为带类型注解的 let 链（见 §4.1），比直接嵌套 `trans` 更能
  检查用户写出的中间项，且不依赖宏系统的重复转写能力生成嵌套括号。
- **目标类型**：不需要显式声明，链的结果类型 `Eq (首项) (末项)` 由证明自动综合；
  外围 `def`/`let` 的返回类型注解照常核对。
- **关系**：第一版只做 `Eq`（转写里硬编码 `Eq` 与 `trans`）。扩展 `≡`/`≤` 的代价见 §6。

---

## 1. 背景（已读代码）

| 主题 | 位置 | 要点 |
|---|---|---|
| Eq 与证明函数 | `src/prelude/core/eq.typort` | `rfl` / `cong` / `symm` / `trans` / `subst`；`def trans[A, x, y, z: A](e1: Eq x y, e2: Eq y z): Eq x z` |
| Nat 算术引理 | `src/prelude/core/nat.typort` | `add_assoc` / `add_comm` / `add_zero_left` 等，全部以 `Eq` 为结论 |
| 现有链式证明 | `examples/theorem_proving.typort` | `trans(trans(lhs, mid), rhs)`、`let step1: Eq ... = ...; trans(step1, step2)` 手工链 |
| 宏系统 | `src/L13_namespace/parser/macros.rs` + `parser/mod.rs` | matcher 字面 token 支持 Ident/Op/Num/`[]{}`/`let`/`=`/`.`/**`by`（ByKeyword）**；片段仅 `ident`/`raw`/`params`；重复 `$(...)*`/`$(...)+`；转写器按 token 原样输出 |
| 词法器 | `src/L13_namespace/parser/lex.rs` | `by` 是保留字（`TokenKind::ByKeyword`，KEYWORD 表），不是 Op、不是 Ident |
| 宏范本 | `src/prelude/hdl/hdl-macros.typort` | `when`/`Expr`/`module` 宏：raw 片段 + `$(...)` 重复 + 换行分隔 |
| 中缀运算符 | `src/prelude/core/op.typort` + `parser/mod.rs::expr_bp` | `a + b` 是方法调用 `a.+(b)`；绑定力表见 §4.2 |
| 测试入口 | `src/L13_namespace/mod.rs::run_with_prelude`、`legacy_tests.rs::test_prove_term_pure` | prelude 文件按数组顺序加载、宏跨文件经 `#[macro_export]` 累积；测试 = `run_with_prelude(源码)` 后断言 println 输出 |

---

## 2. 语法设计（推荐形态）

### 2.1 具体到每个 token 的语法

```typort
calc {
    <term> = <term> by <proof>
    <term> = <term> by <proof>
    ...
}
```

- `calc`：宏名（普通 Ident，不是关键字，无 lexer 冲突）。
- `{` … `}`：链的定界（LCurly/RCurly 是匹配器可用的字面 token），
  使 `calc` 后换行、`}` 前换行都允许（外层 `$(...)+` 的 Many1 会跳过前导 EndLine）。
- 每一步：`<term> = <term> by <proof>`：
  - `<term>`：`raw` 片段（任意表达式，可含括号/运算符/隐式参数 `f[x = 1]`）；
  - `=`：字面 `Eq` token（lexer 将 `=` 固定映射为 `Eq`，且 `=` **不是**表达式
    中缀运算符，所以 raw 片段在 `=` 处必然干净停止）；
  - `by`：字面 **ByKeyword** token（专用关键字）。`by` 既不是 Op 也不是 Ident，
    `expr_bp` 的中缀/后缀循环（只消费 Op/LParen/LSquare/Dot）与 `p_atom1`
    （Ident/数字/字符串/括号/洞）都不消费它 —— 所以 `$y: raw` 在 `by` 前
    干净停止，`$p: raw`（本步最后片段）停在换行（多行形式）或下一个 `=`
    （单行形式）。**这是 `a = b by p` 语法可行的关键**；
  - 步骤之间用换行分隔（重复匹配器 `Many0`/`Many1` 的 EndLine 分隔机制）。
- 单行链（第二条宏规则，无需大括号，首项必须与 `calc` 同行）：
  ```typort
  calc a = b by p1 = c by p2 = d by p3
  ```
- 历史：v1（task/calc-reasoning）用过 `a = [proof] b`（证明夹在两式之间），
  v2（task/calc-by-syntax）改为 `by` 引导的 Lean 风格，`[ ... ]` 写法**已移除**、
  无兼容 arm（§9.5）。

### 2.2 目标类型：不需要显式声明

链的结果类型由证明自动综合：

- 展开后第一个 let 的注解 `Eq ($x) ($y)` 确定首项 `$x` 的类型；
- `trans _c ($q)` 的隐式参数 `[A, x, y, z]` 由 `_c` 与 `$q` 的类型通过统一求解
  （`trans e1 e2` 的隐式推理在 `nat.typort` 的 `add_comm` 等中已被大量使用）；
- 最终 `_c : Eq (首项) (末项)`。

外围上下文照常核对：`def foo: Eq a d = calc {...}` 中 def 的返回类型注解检查
链的结果；`let h : Eq a d = calc {...}; ...` 同理。
（`calc (Eq a d) { ... }` 这类前置目标写法**不可行**：matcher 无法匹配 `(`/`)`
字面 token，且也不需要。）

### 2.3 关系：第一版只做 Eq

- 转写硬编码两个名字：`Eq`（注解）与 `trans`（组合子），都是 prelude 裸名。
- 扩展成本见 §6。

### 2.4 步骤间的 let / 中间引理

- 单个证明片段本身可以是任意表达式，包括 let 表达式：
  `a = b by let h = foo n m; trans h (bar n)` —— 中间引理写在证明片段里即可。
- `calc` 本身是普通表达式，可出现在 let 值、match 分支、函数实参、`(calc ...)` 内
  的任何表达式位置（宏在 `p_raw` 起始处展开）。
- 步骤之间**不能**插入独立 let 语句（宏匹配是连续的）；需要的话把引理放进
  某一步的证明片段，或在 calc 外用 `let` 先绑好。
- 步骤分隔**必须是换行**：`;`（Semi）不是匹配器可用的字面 token，
  `calc { a = b by p; b = c by q }` 不可行。

---

## 3. 使用示例

### 3.1 简单链（对应目标：`a = b := p1; b = c := p2` → `Eq a c`）

```typort
def zero_add_comm_calc(n: Nat): Eq (0 + n) (n + 0) =
    calc {
        0 + n = n by add_zero_left n
        n = n + 0 by symm (add_zero_right n)
    }
```

（对照 `examples/theorem_proving.typort` 里的 `zero_add_comm`：`trans(add_zero_left(n), symm(add_zero_right(n)))`。）

### 3.2 多行三步链

```typort
def add_permute_calc(a: Nat, b: Nat, c: Nat): Eq ((a + b) + c) ((a + c) + b) =
    calc {
        (a + b) + c = a + (b + c) by add_assoc a b c
        a + (b + c) = a + (c + b) by cong (x => a + x) (add_comm b c)
        a + (c + b) = (a + c) + b by symm (add_assoc a c b)
    }
```

（对照现有 `add_permute` 的手工 `trans(trans(lhs, mid), rhs)` + 三个带注解 let。）

### 3.3 与现有 Nat 证明结合（五步链）

```typort
def double_distrib_calc(x: Nat, y: Nat): Eq (double (x + y)) (double x + double y) =
    calc {
        double (x + y) = ((x + y) + x) + y by symm (add_assoc (x + y) x y)
        ((x + y) + x) + y = (x + (y + x)) + y by add_right_eq ((x + y) + x) (x + (y + x)) y (add_assoc x y x)
        (x + (y + x)) + y = (x + (x + y)) + y by add_right_eq (x + (y + x)) (x + (x + y)) y (add_left_eq (y + x) (x + y) x (add_comm y x))
        (x + (x + y)) + y = ((x + x) + y) + y by add_right_eq (x + (x + y)) ((x + x) + y) y (symm (add_assoc x x y))
        ((x + x) + y) + y = (x + x) + (y + y) by add_assoc (x + x) y y
    }
```

（对照 `legacy_tests.rs::test_prove_term_pure` 里手工嵌套五层 `trans` 的 `double_distrib` —— 该测试里
`let ret: Eq(s1, dA + dB) = trans(double_step(...), double_distrib(...)); ret` 的写法
正是 calc 要自动化的模式。）

### 3.4 负例（预期错误形态）

**负例 A —— 步骤证明类型与写出的项不符**（右端写错）：

```typort
def neg_a: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 = 7 by add_zero_right 7
        7 = 0 + 7 by add_zero_right 7        // add_zero_right 7 : Eq (7+0) 7，不是 Eq 7 (0+7)
    }
```

展开后（实现为 let 链，无每步检查 let，见 §9.2.1）第二行是
`let _c = trans (_c) (add_zero_right 7);`，`trans` 统一 `7 ≡ 7 + 0` 失败。
预期错误形态（`src/L13_namespace/elaboration.rs` 统一格式，形如）：

```
can't unify
  expected: Eq _ (0 + 7)
      find: Eq (7 + 0) 7
```

错误位置落在第二行证明片段的 span 上（`check` 的 `t_span`）。

**负例 B —— 链断裂（相邻证明的中间项不一致）**：

```typort
def neg_b: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 = 7 by add_zero_right 7
        5 = 0 + 7 by symm (add_zero_left 7)   // 上一行右端是 7，这一行左端写的是 5
    }
```

展开后 `trans _c (symm (add_zero_left 7))`：`_c : Eq (7+0) 7`，第二个证明 : `Eq 7 (0+7)`，
统一 `7 ≡ 5` 失败。预期错误形态：

```
can't unify
  expected: Eq 7 _   （trans 第二个参数应满足的类型）
      find: Eq 5 (0 + 7)
```

> 设计限制说明：中间步骤的**左端**（如负例 B 里写出的 `5`）在 2026-08 的修复后
> **已逐字核对**：每条后续步的转写都带一个显式检查 let
> `let _ : Eq ($x2) ($z) = ($q);`（两端都写全，不再用洞注解；见 §9.6）。
> 因此写出的左端/右端与证明真实端点不一致时直接报 `can't unify`，不再依赖
> trans 兜底。本负例（B）当前在**第二步的检查 let** 处即报错（`5` 与证明左端
> `7` 无法统一），错误信息形态见 §9.6。

**负例 C —— 缺 `by` 或 `by` 放错位置**（宏整体不匹配，`calc` 退化为普通标识符）：

```typort
def neg_d: Eq (7 + 0) (0 + 7) =
    calc {
        7 + 0 = 7            // 缺 `by 证明`
        7 = 0 + 7
    }
```

匹配器在字面 `by`（ByKeyword）处找不到 token → 规则失败 → 两条规则都失败 →
`calc` 退化为标识符。预期：解析期 `expected EndLine` 类错误 + 精化期
“name not in scope: calc”类错误（`calc_tests.rs` 的负例断言此形态）。
`by` 后没有证明（`7 + 0 = 7 by` + 换行）、`by` 出现在 `=` 之前
（`7 + 0 by p = 7`）同理。

**负例 D —— 误用 Lean 的 `:=` 语法**：

```typort
def neg_c: Eq (7 + 0) (0 + 7) = calc
    7 + 0 = 7 := add_zero_right 7
    7 = 0 + 7 := symm (add_zero_left 7)
```

宏匹配失败（`:=` 是 raw 片段会吞掉的中缀 token，见 §4.2），`calc` 退化为普通标识符。
预期：解析期 `expected EndLine` 类错误 + 精化期“未知名称 calc”类错误。这是已知限制，
文档与错误提示中应引导用户使用 `by` 写法。

---

## 4. 实现方案评估

### 4.1 宏方案（推荐）：匹配器与转写

**宏定义**（`src/prelude/core/calc.typort`）：

```typort
#[macro_export]
macro_rules calc {
    // 推荐主形式：{ ... } 块内换行分隔的链（首项可换行到 `{` 之后）
    ( { $( $x: raw = $y: raw by $p: raw $( $x2: raw = $z: raw by $q: raw )* )+ } ) => {
        let _c : Eq ($x) ($y) = ($p);
        $( let _ : Eq ($x2) ($z) = ($q);
           let _c = trans (_c) ($q); )*
        _c
    };
    // 单行形式：calc a = b by p1 = c = d by p2（首项必须与 calc 同行；
    // 链的 `=` 分隔符在每步 proof 之后，所以重复单元以 `=` 开头）
    ($x: raw = $y: raw by $p: raw $( = $x2: raw = $z: raw by $q: raw )*) => {
        let _c : Eq ($x) ($y) = ($p);
        $( let _ : Eq ($x2) ($z) = ($q);
           let _c = trans (_c) ($q); )*
        _c
    };
}
```

**匹配器要点**（为什么这个形状能工作）：

- 字面 token 全部落在 matcher 支持集内：`=`（`Eq`）、`by`（ByKeyword，
  `p_macro_matcher_single` 显式支持）、`{`/`}`（LCurly/RCurly）、`calc` 名称本身。
- `raw` 片段 + 跟随 token 的安全性：
  - `$x:raw` 后面是 `=`（Eq token）—— `expr_bp` 的中缀循环只读 Op/LParen/LSquare/Dot，
    `=` 不在其中 → raw 在 `=` 处停止（**安全**）；
  - `$y:raw` 后面是 `by`（ByKeyword）—— 不在上述循环集合、也不是 atom →
    停止（**安全**）；
  - `$p:raw` 后面是换行（多行形式）或 `=`（单行形式）→ 停止（**安全**）。
- 证明片段内部的 `[ ... ]`（隐式参数应用 `f [x = 1]`）会被 p_raw 作为表达式一部分
  消费，不与任何 calc 定界冲突。
- 换行分隔：外层 `$(...)+`（Many1）与内层 `$(...)*`（Many0）都先跳过前导 EndLine、
  用 `EndLine.option()` 分隔迭代 —— 与 `hdl-macros.typort` 的 `when`/`module` 宏同款机制。
- 步数：`$( $x2 = $z by $q )*` 捕获第 2..n 步（`$q`/`$z` 长度 n-1），
  第 1 步由 `$x`/`$y`/`$p` 捕获（长度 1，转写中可整体复用）。
- 每条重复单元以下一步的**左端**（`$x2: raw`）开头：换行（被重复分隔器跳过）后
  跟的是 ident，可以匹配；若以 `=` 开头则换行后必然失败。
- 两条规则的顺序无关紧要：花括号形式对无 `{` 输入、单行形式对 `{` 开头输入，
  都在第一个 raw 片段处干净失败（p_raw 无法以 `{` 起始），不会误匹配也不会产生
  伪错误（失败路径上的解析器在关键字检查处就退回，不经过 Cut 的错误注入）。

**转写要点**（展开成 let 链而非嵌套 `trans`）：

- 宏系统的重复转写 `$(...)*` 只是**扁平拼接**，无法生成嵌套括号，
  所以 `trans (trans p1 p2) p3` 这种左/右折叠**写不出来**（`trans $p $(trans $q)*`
  会拼成 `trans p1 trans p2 trans p3`，即错误的多重应用）。
  改用 let 链：首步一个带注解的 let + 每步一个累积 let，最后返回累积值。
- let 的作用：
  - 第 1 步 `let _c : Eq ($x) ($y) = ($p);` —— 同时做两件事：核对写出的
    `x`/`y` 与证明类型一致，并把 `_c` 绑定为链的累积证明；
  - 第 i≥2 步 `let _ : Eq ($x2) ($z) = ($q);` —— **逐字核对写出的两端**
    （2026-08 恢复，见 §9.6；此前只靠 trans 间接核对）；
  - 第 i≥2 步 `let _c = trans (_c) ($q);` —— 用累积证明与当前证明组合
    （`trans` 隐式参数自动求解中间项），并强制链连续性
    （上一步右端 == 下一步左端，经证明端点统一）；
  - 证明实参必须括号包裹：`trans (_c)` 而不是 `trans _c`（裸标识符实参精化失败，
    见 §9.2.2）。
- let 遮蔽：累积名 `_c` 每步重绑定。可行性依据：`Cxt::define`/`bind` 把名字
  映射到**当前最深 lvl**（`src_names` 是 BiMap，重复插入覆盖），而 let 的
  值在 `define` **之前**精化（`elaboration.rs` 的 `Raw::Let`：先 check 值、
  再 define 进上下文），因此 `trans (_c) ($q)` 里引用的 `_c` 总是外层绑定。
  （phase 2 第一步仍需用真实测试验证，见 §8。已实测通过。）
- 所有 metavar 在应用位置都加括号：`Eq ($x) ($y)`、`($p)`、`($q)` —— 防止
  片段内运算符与外围语法串读（如 `Eq (a+b) * c ...` 会把 `*` 读成中缀）。
- 空链（零步）不可表示（内层 `*` 虽允许零次，但第 1 步是必须的 `$x = $y by $p`）。
- 多实参证明的实参要用逗号形式（§9.2.3）。

**展开形态示例**（§3.2 的 add_permute_calc，缩写证明为 p1/p2/p3）：

```typort
let _c : Eq ((a + b) + c) (a + (b + c)) = (p1);
let _c = trans (_c) (p2);
let _c = trans (_c) (p3);
_c
```

（let 链由 `p_let` 的 `let x = e; body` 递归解析，`;` 在转写输出中是普通 token。）

### 4.2 为什么 Lean 的 `a = b := p1` 不可行、而 `a = b by p1` 可行（token 结构分析）

任务里问的 `x = y by p` / `x = y := p` 的 token 结构，逐 token 分析如下：

| token | lexer 归类 | 说明 |
|---|---|---|
| `x` | Ident | `$x:raw`，p_raw 在 `=` 处停止 |
| `=` | **Eq** | 不是 Op → 不是表达式运算符 → raw 片段干净停止；matcher 可字面匹配 `=`（`string(Eq)`） |
| `y` | Ident | `$y:raw`，在 `by`（或 `:=`）处停止 |
| `by` | **ByKeyword**（新建保留字） | 不是 Op、不是 Ident —— `expr_bp` 的中缀/后缀循环（Op/LParen/LSquare/Dot）与 `p_atom1`（Ident/数字/字符串/括号/洞）都不消费它 → `$y:raw` 干净停止；matcher 可字面匹配 `by`（`string(ByKeyword)`，`p_macro_matcher_single` 显式加了此分支） |
| `:=` | **Op**（单 token） | `:` 与 `=` 都在操作符字符范围（`':'..='@'`），且 `:=` 不在 OP 关键字表 → 整个 lex 为一个 Op token |
| `p1` | Ident | `$p:raw`，多行形式停在 EndLine、单行形式停在下一个 `=`（Eq 不是表达式延续） |

**`:=` 失败的原因**：**所有** Op token 在 `expr_bp` 里都是中缀运算符 ——
`infix_binding_power` 的兜底是 `Some((7,8))`，`:=` 因 `contains(':')` 得到 `(2,1)`。
因此 `$y:raw` 解析 `b := p1` 时会**贪心吞掉整个** `b := (p1)`（中缀应用），随后
匹配器在字面 `:=` 处必然失败 → `calc` 宏整体不匹配。

把 `:=` 从 `infix_binding_power` 里排除（让 raw 在 `:=` 处停止）需要改 parser，
且会破坏 HDL：`examples/alu.typort` 的模块体 `result := a + b`、`hdl_ops.typort` 的
`bit0 := a.apply[0]` 等**依赖 `:=` 中缀解析**（在 module 宏的 raw 兜底规则里被整体
消费），移除后需要同步迁移 HDL 语法。

**`by` 可行的原因**：与其动 `:=`（会破坏 HDL），不如新建一个**专用关键字 token**
`by`。关键字在词法层就不是 Op —— 表达式解析器对它没有任何消费路径，raw 片段
必然在它前面停止；同时 `by` 作为保留字，`p_macro_matcher_single` 只需补一行
`string(ByKeyword)` 就能在匹配器里字面匹配。代价是 `by` 成为全局保留字
（全仓库 typort 代码无此标识符用法，安全）。这就是用户提出“新建一个 token”的
依据，也是 v2 把 Lean 的 `a = b := p` 需求落实为 `a = b by p` 的方式。

顺带说明其它不可行分隔符：`;`（Semi）、`:`（Colon）、`(`/`)` 都不是 matcher
可用的字面 token；`=>` 是 DoubleArrow 同理不可匹配。`by` 关键字是
“可字面匹配 + raw 片段不吞它 + 不破坏现有语法”的组合解。

### 4.3 中缀运算符方案（`a =⟨ p1 ⟩ b`）评估：不可行于当前 parser

- **lexer**：`⟨`/`⟩`/`≡` 都不是操作符字符（`lex.rs` 的 op 范围全 ASCII），
  且 `=` 被 OP 表固定映射为 `Eq` token。要支持需要改 lexer 加非 ASCII token。
- **parser**：`expr_bp` 的中缀循环只消费 Op/LParen/LSquare/Dot —— `=`（Eq）
  根本进不了循环（`infix_binding_power` 里的 `s == "="` 分支是死代码）。
- 即使用 ASCII 替代（`=<`/`>`）：`>` 与比较运算符同 token 冲突；Agda 式
  `step` 语义需要右结合 + 续延编码，`expr_bp` 的中缀机制会产生
  `((a =< p1) > (b =< p2)) > c` 的错误分组，必须做绑定力工程（`=<` 高绑定、
  `>` 低于 `=<` 的右绑定……）—— 结论是“语法脆弱 + 双份修改”，不推荐。

**结论**：v1 用宏方案 + `[p]` 分隔；v2 用 `by` 关键字把 UX 提到 Lean 水准，
`[p]` 旧写法移除、无兼容 arm。

---

## 5. 推荐方案与备选

| 方案 | 改动范围 | 语法 | 判定 |
|---|---|---|---|
| **A. 纯宏（推荐）** | prelude（calc.typort）+ mod.rs prelude 数组一行 + lexer 一个关键字（v2） | `calc { a = b by p1 ... }` | v1 采用；v2 升级为 `by` 语法。错误定位靠 let 链的 span，检查充分 |
| B. 宏 + parser 排除 `:=` 中缀 | parser 一行 + HDL 迁移 + prelude | `calc a = b := p1`（Lean 原味） | 已被 v2 的 `by` 关键字取代（§4.2）：`by` 达到同等 UX 且不破坏 HDL |
| C. 中缀链（Agda 式） | lexer + parser 双改 | `a =⟨ p1 ⟩ b` | 不推荐。脆弱、改动大 |
| D. 泛化关系宏（typeclass） | prelude + 可能 typeclass 机制 | `calc Eq { ... }` | v2 候选，见 §6 |

推荐 A 的理由：需求全部落在现有宏系统能力内（raw 片段、字面 token `=`/`by`/`{}`、
换行重复、let 链转写、let 遮蔽），lexer 只加一个保留字，parser 只加一个字面 token
分支，回归风险最小；语法与 Lean 的 `calc` 对齐，与 Typort 现有块风格
（match/when 的 `{}` + 换行）一致。

---

## 6. 关系扩展（`≡` / `≤`）代价评估

- **自定义同构关系 `≡`**（用户定义、构造/消去与 Eq 同形）：复制 calc 宏并改名
  （注解里的关系名 + 组合子名）+ 该关系的传递引理，约 10 行。低代价。
- **`≤`（Nat 上的偏序）**：prelude 目前只有 `Compare` trait 的布尔方法，
  **没有** `Le` 命题类型（`data/order.typort` 只有 `Ordering` 枚举）。
  需要先定义 `Le`（如归纳类型）+ 传递引理，再复制宏改名。中代价（主要是引理本身）。
- **一个宏支持任意关系**：转写中 `Eq`/`trans` 是硬编码名字；可行的泛化路线是
  matcher 头部加 `$r:ident`（`calc Eq { ... }`）+ typeclass
  （`trait CalcStep[R, A] { def step[x, y, z](e1: R x y, e2: R y z): R x z }`，
  `impl CalcStep[Eq[A], A]`），转写用 `step` 函数 + 关系名的 where 约束。
  v1 不做：typeclass 对“关系”这种高阶参数的分辨行为需要单独验证。

---

## 7. 负例之外的已知限制（文档化）

1. `a = b := p1`（Lean 原味 `:=`）不解析，见 §4.2 —— 用 `a = b by p1` 代替。
2. ~~中间步骤的左端写出项不单独核对~~（2026-08 已修复：每步显式检查 let，见 §9.6）。
3. 步骤必须换行分隔（花括号形式），`;` 分隔不可行（matcher 无法匹配 `;`）。
   单行形式以 `=` 分隔（`= $x2 = $z by $q`）。
4. 单步链 `calc { a = b by p }` 合法（重复部分为零次），结果就是 `p` 的带注解拷贝。
5. `calc` 成为宏名后，用户无法再定义同名变量/函数（宏在 p_raw 入口优先于标识符）；
   `by` 成为保留字后同理无法用作标识符（全仓库无此用法，v2 迁移时已确认）。
6. 链的首项类型必须可推断（如 `Eq (_) (_)` 全是洞时结果也是洞，与手写 trans 一致）。

---

## 8. 实施清单（phase 2，用户确认后执行）

1. **验证三个假设**（先写临时测试）：
   - let 遮蔽：`let _c = ...; let _c = trans _c ...; _c` 精化通过；
   - `let _ : Eq _ ($z) = ($q);` 的洞注解可精化（洞被证明类型统一）；
   - 两条宏规则的失败回退不产生伪错误。
2. **落地宏**：新建 `src/prelude/core/calc.typort`（放 `#[macro_export] macro_rules calc`），
   并在 `src/L13_namespace/mod.rs` 的 prelude 数组（`load_prelude_state` 与其它
   列表位置）追加该文件 —— 注意 `nat_typort` 的 `register_nat_to_dec` 是按内容判断的，不受影响。
3. **测试**：仿照 `legacy_tests.rs::test_prove_term_pure`（`run_with_prelude` + println 断言）
   添加 §3.1–3.3 正例与 §3.4 负例（负例断言错误消息出现 `can't unify`）。
4. **回归**：`cargo test --lib L13` 基线 239 passed 不减少。
5. （可选）文档更新：把 `calc` 写进语言参考。

---

## 9. 实施记录（已完成）

### 9.1 实现结果（v1，task/calc-reasoning）

- `src/prelude/core/calc.typort`：`#[macro_export] macro_rules calc`，两条规则
  （花括号多行形式 + 单行形式），转写为 let 链（首步带注解，后续 `trans (_c) (q)`）。
- 登记位置（共三处，漏任何一处都会表现为“宏未注册”）：
  - `src/L13_namespace/mod.rs` `load_prelude_state` 的 prelude 数组（`run_with_prelude` 用）；
  - `src/L13_namespace/mod.rs` `prelude_tests::PRELUDE_FILES`（prelude 测试覆盖）；
  - `src/lib.rs` `load_prelude_impl`（LSP 内置文档加载）。
- 测试：`src/L13_namespace/calc_tests.rs` 7 个（§3.1 二步 / §3.2 三步 / 五步 + 单行 +
  let 内嵌 + 2 个负例）。`cargo test --lib L13`：246 passed，0 failed
  （基线 239 → 246，纯增量）。

### 9.2 与设计稿的偏差（都已实测，保留在实现中）

1. **放弃每步检查 let**：`let _ : Eq _ _ ($z) = ($q);` 精化失败 —— 洞注解会留下
   未解的 meta（`?x n n`），unifier 无法闭合（E-unify 限制）。改为只靠
   `trans` 的统一做连续性检查：首步两端由注解 let 核对；后续步**写出的左端不核对**
   （核对的是证明的真实中间项），右端与下一个证明的右端经 trans 统一核对，
   末项由外围注解核对。负例 B 因此只能捕获“写出的左端与证明真实左端不一致”，
   写错左端而证明类型恰好吻合的情形不报错（文档化限制，见 §3.4 注）。
2. **`trans (_c)` 必须括号包裹**：裸 `trans _c`（标识符实参）精化失败；
   括号包裹后走表达式路径通过。
3. **多实参证明要用逗号形式**：`add_right_eq A B y (add_assoc x y x)`（裸实参 + 括号）
   会被解析成对括号表达式的应用；必须写成 `add_right_eq(A, B, y, add_assoc(x, y, x))`。
4. **词形要求**：裸应用 `double x + double y` 不行，需 `double(x) + double(y)`
   （与现有语言一致，非 calc 特有）。

### 9.3 parser 兼容性改动（两处，均有回归覆盖）

1. **`many1_sep_skip` 的隐式分隔**（`src/L13_namespace/parser/mod.rs`）：literal
   Token 匹配器会吞掉匹配后紧跟的一个 EndLine（when/switch 等宏依赖此行为）。
   calc 的 matcher 以 literal `}` 结尾，会把 calc 块与下一个 decl 之间的换行吞掉，
   导致下一个 `def` 紧贴前一个 decl 出现。此时 `skip_until_decl` 只能找到
   “EndLine + decl 关键字”的位置，会**跳过当前紧贴的 decl** 造成丢失
   （症状：后续 decl 报 `name not in scope`）。修复：sep 失败且当前位置已是
   decl 关键字开头时，直接继续主循环（隐式分隔），不再报 `Expect(EndLine)`。
2. **展开 token 重 lex**（`p_raw` 展开处）：owned token 携带宏定义处的
   span/path_id，直接拼接会导致展开内容再解析失败（在定义处 span 上报
   `Expect(EndLine)`）。改为 `owned_tokens_to_string` + `lex()` + 过滤 EOF
   后得到干净的借用 token 流。
3. **调试期间曾移除 Token 的 EndLine skip**（实验）导致 switch/when 回归；
   **根因并非该 skip**，而是 calc.typort 漏登记 prelude（见 §9.1）。已恢复
   skip 原状，本分支对 `macros.rs` 零改动。

### 9.4 排障过程要点

- `PRELUDE id=3 exports=[]` 的 `id=3` 是 **bool.typort**（数组下标），不是
  calc.typort —— 用 `include_str!` 数组顺序对照，发现 calc.typort 根本不在列表里；
  与 Token skip 实验无关，是登记遗漏。
- 负例 B 的报错形态与设计稿略有出入：链断裂时是 `trans` 的 `can't unify`
  （expected/find 为两个 Eq 类型），不是设计稿中标注的 `Eq 7 _` 形态。

### 9.5 `by` 关键字语法迁移（v2，task/calc-by-syntax）

把每步语法从 `a = [p] b` 改为 Lean 风格 `a = b by p`，`[p]` 旧写法完全移除、
无兼容 arm：

- **词法**（`src/L13_namespace/parser/lex.rs`）：
  - `TokenKind` 枚举新增 `ByKeyword`（在 `ClassKeyword` 之后）；
  - `Display` 实现新增 `TokenKind::ByKeyword => "`by`"`（`Expect(ByKeyword)` 报错可读）；
  - `KEYWORD` 表新增 `("by", ByKeyword)`（数组长度 19 → 20），`by` 成为全局保留字。
- **宏匹配器**（`src/L13_namespace/parser/mod.rs` `p_macro_matcher_single`）：
  token_parser 新增 `string(ByKeyword)` → `MacroMatcher::Token(ByKeyword, span)`。
  `by` 在宏定义里 lex 成 ByKeyword，因此不会误走 `string(Ident)` 分支。
- **宏定义**（`src/prelude/core/calc.typort`）：两条规则的 matcher 改为
  `$x: raw = $y: raw by $p: raw`（重复单元 `$x2: raw = $z: raw by $q: raw`），
  转写体不变（`let _c : Eq ($x) ($y) = ($p);` + 每步 `trans (_c) ($q)`）。
  停止行为：`$y` 停在 `by`（ByKeyword 非表达式 token）、`$p` 停在 EndLine
  （多行）或 `=`（单行，Eq 非表达式延续）。
- **测试**（`src/L13_namespace/calc_tests.rs`）：全部正例改为新语法；新增三个负例
  —— 缺 `by`（断言退化 `calc` 标识符报错）、`by` 后无证明、`by` 位置错误；
  `:=` 负例保留（仍不可解析）。L13 全量：275 passed，0 failed（基线 272 →
  275，+3 个新负例）。
- **示例**（`examples/adder_proof.typort`）：46 处 calc 步骤全部改写，经
  `run_with_prelude` 实测通过。
- **文档/高亮**：本文档全部示例与 §4.2 分析更新；vscode 语法高亮
  （`vscode_extension/syntaxes/typort.tmLanguage.json`）关键字正则加入 `by`。
- **影响面确认**：全仓库 typort 代码无 `by` 标识符用法（仅注释），保留字安全；
  `calc` 本身仍是宏名（普通 Ident），`tests/trait_system_tests.typort` 的
  `def calc = ...` 不受影响。

### 9.6 恢复每步检查 let + 修复单行形式重复匹配（2026-08）

**背景**：§9.2.1 放弃的每步检查 let 用的洞注解 `Eq _ _ ($z)` 会留未解 meta
（`?x n n`）。2026-08 的悬停探针发现**后续步的写出项（`$x2`/`$z`）从未被检查**：
`garbage1 = garbage2 by <正确proof>` 零错误通过（连未定义名字都不报错）；
同时这些 token 不在展开里 → LSP hover/goto 无条目。

**修复 1 —— 恢复每步检查 let，两端写全**（`src/prelude/core/calc.typort`）：

```typort
let _c : Eq ($x) ($y) = ($p);
$( let _ : Eq ($x2) ($z) = ($q);
   let _c = trans (_c) ($q); )*
_c
```

- 两端都写全（`Eq ($x2) ($z)`）不再产生洞 meta —— 实测精化通过
  （§9.2.1 失败的根因是洞，不是检查 let 思路本身）；
- 效果：`garbage1 = garbage2 by symm(add_zero_right(n))` → `error name not in scope:
  garbage1`；`5 = 0 + 7 by symm (add_zero_left 7)`（左端写错）→ `can't unify
  expected: Eq[Nat](5, 0 + 7) / find: Eq[Nat](7, 0 + 7)`；右端写错同理；
- trans 链保留：仍负责链连续性（上步右端 == 下步左端）与结果类型合成
  （`Eq $x $z_last`），与检查 let 相互独立；
- 副产物：后续步 token 重新出现在展开里 → LSP hover/goto 恢复
  （第二步的 `n` 悬停显示 `Nat`，`+` 显示运算符类型）。

**修复 2 —— 单行形式的重复单元以 `=` 开头**：

- 旧 matcher `$( $x2: raw = $z: raw by $q: raw )*` 对单行链**永远匹配零次**：
  单行链步骤间以 `=` 分隔（`a = b by p1 = c = d by p2`），`$p` 之后紧跟 `=`，
  而 `$x2: raw` 无法以 `=` 开头 → 规则只消费第一步，剩余 `= c = d by p2`
  触发 `expected newline` 解析错误，第二项被静默丢弃；
- 旧正例 `calc_single_line`（输入 `= n + 0 by ...`，缺第二步的 `=`）是靠
  "1 步匹配 + 解析错误 + def 返回注解检查宽松" 侥幸通过的；
- 修复：重复单元改为 `$( = $x2: raw = $z: raw by $q: raw )*`；
  单行链的第二步正确写法为 `= n = n + 0 by symm (add_zero_right n)`
  （链分隔 `=` + 步骤自身的 `=`）。

**测试**（`src/L13_namespace/calc_tests.rs`）：
- 新增 4 个负例：`calc_err_garbage_step2_terms`、`calc_err_wrong_step2_left`、
  `calc_err_wrong_step2_right`、`calc_err_wrong_step2_single_line`；
- `calc_single_line` 输入修正为完整两步语法；`calc_err_broken_chain` 注释更新
  （现由检查 let + trans 双重核对）。
- 回归：`cargo test --lib calc` 19 passed；`cargo test --test macro_goto_tests
  --test hover_tests --test cross_file_tests` 9 passed；全量 `--lib` 失败数
  与修复前基线相同（49 个预存失败，与本次改动无关）。

---

## 附：与 Lean/Agda 的对照

| 语言 | 语法 | 中间项检查 | 实现 |
|---|---|---|---|
| Lean4 | `calc a = b := p1; b = c := p2` | 每步两端都核对 | 解析器内建（句法块 → trans 应用） |
| Agda | `a ≡⟨ p1 ⟩ b ≡⟨ p2 ⟩ c` | 每步两端都核对 | 库内运算符（`_≡⟨_⟩_` step + 右结合） |
| Typort（本设计） | `calc { a = b by p1 b = c by p2 }` | 每步两端都核对（2026-08 起；此前只核首步两端） | 库内宏（let 链转写 + 每步检查 let）+ `by` 关键字 |

Typort 的宏系统是纯 token 级的（无类型信息、无自引用重复），因此做不到
Lean/Agda 那种“每步两端全核对”，但核对覆盖面足以捕获绝大多数书写错误；
其余由 `trans` 的统一（含定义等价）兜底。
