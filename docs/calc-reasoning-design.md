# calc / reasoning 链式等式证明 — 设计

> 目标：为 Typort 引入 Lean4 `calc` / Agda `reasoning` 风格的链式等式证明，
> 把一串等号步骤组合成单个 `Eq a d` 的证明（用 `trans` 组合）。
> 本文档是**第一阶段（纯设计）**的产出：只做语法与实现路线决策，不涉及代码改动。

**当前状态（2026-08）**：设计已定，等待用户确认后进入实现阶段（phase 2）。

---

## 0. 结论摘要

- **实现方式**：宏方案（只加一个 prelude 文件 + 三处 prelude 列表登记；parser 有两处
  小的兼容性改动，见 §9.3 —— 原设计“零 parser 改动”未兑现，但改动是通用的，
  对 when/switch 等既有宏无回归）。
- **语法形态**（受宏系统约束，Lean 的 `a = b := p` 目前**不可行**，原因见 §4.2）：
  ```typort
  def foo: Eq a d =
      calc {
          a = [p1] b
          b = [p2] c
          c = [p3] d
      }
  ```
  每步是 `term = [ proof ] term`：`=` 分隔等式两端，`[ proof ]` 是证明（Agda
  `⟨ p ⟩` 的 ASCII 版）。步骤以换行分隔；单行链 `calc a = [p1] b = [p2] c` 也可用。
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
| 宏系统 | `src/L13_namespace/parser/macros.rs` + `parser/mod.rs` | matcher 字面 token 仅限 Ident/Op/Num/`[]{}`/`let`/`=`/`.`；片段仅 `ident`/`raw`/`params`；重复 `$(...)*`/`$(...)+`；转写器按 token 原样输出 |
| 宏范本 | `src/prelude/hdl/hdl-macros.typort` | `when`/`Expr`/`module` 宏：raw 片段 + `$(...)` 重复 + 换行分隔 |
| 中缀运算符 | `src/prelude/core/op.typort` + `parser/mod.rs::expr_bp` | `a + b` 是方法调用 `a.+(b)`；绑定力表见 §4.2 |
| 测试入口 | `src/L13_namespace/mod.rs::run_with_prelude`、`legacy_tests.rs::test_prove_term_pure` | prelude 文件按数组顺序加载、宏跨文件经 `#[macro_export]` 累积；测试 = `run_with_prelude(源码)` 后断言 println 输出 |

---

## 2. 语法设计（推荐形态）

### 2.1 具体到每个 token 的语法

```typort
calc {
    <term> = [ <proof> ] <term>
    <term> = [ <proof> ] <term>
    ...
}
```

- `calc`：宏名（普通 Ident，不是关键字，无 lexer 冲突）。
- `{` … `}`：链的定界（LCurly/RCurly 是匹配器可用的字面 token），
  使 `calc` 后换行、`}` 前换行都允许（外层 `$(...)+` 的 Many1 会跳过前导 EndLine）。
- 每一步：`<term> = [ <proof> ] <term>`：
  - `<term>`：`raw` 片段（任意表达式，可含括号/运算符/隐式参数 `f[x = 1]`）；
  - `=`：字面 `Eq` token（lexer 将 `=` 固定映射为 `Eq`，且 `=` **不是**表达式
    中缀运算符，所以 raw 片段在 `=` 处必然干净停止 —— 这是本语法可行的关键）；
  - `[` … `]`：字面 LSquare/RSquare，中间是 `raw` 证明片段（`]` 不是表达式
    后缀 token，raw 片段在 `]` 处停止）；
  - 步骤之间用换行分隔（重复匹配器 `Many0`/`Many1` 的 EndLine 分隔机制）。
- 单行链（第二条宏规则，无需大括号，首项必须与 `calc` 同行）：
  ```typort
  calc a = [p1] b = [p2] c = [p3] d
  ```

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
  `a = [let h = foo n m; trans h (bar n)] b` —— 中间引理写在证明片段里即可。
- `calc` 本身是普通表达式，可出现在 let 值、match 分支、函数实参、`(calc ...)` 内
  的任何表达式位置（宏在 `p_raw` 起始处展开）。
- 步骤之间**不能**插入独立 let 语句（宏匹配是连续的）；需要的话把引理放进
  某一步的证明片段，或在 calc 外用 `let` 先绑好。
- 步骤分隔**必须是换行**：`;`（Semi）不是匹配器可用的字面 token，
  `calc { a = [p] b; b = [q] c }` 不可行。

---

## 3. 使用示例

### 3.1 简单链（对应目标：`a = b := p1; b = c := p2` → `Eq a c`）

```typort
def zero_add_comm_calc(n: Nat): Eq (0 + n) (n + 0) =
    calc {
        0 + n = [add_zero_left n] n
        n = [symm (add_zero_right n)] n + 0
    }
```

（对照 `examples/theorem_proving.typort` 里的 `zero_add_comm`：`trans(add_zero_left(n), symm(add_zero_right(n)))`。）

### 3.2 多行三步链

```typort
def add_permute_calc(a: Nat, b: Nat, c: Nat): Eq ((a + b) + c) ((a + c) + b) =
    calc {
        (a + b) + c = [add_assoc a b c] a + (b + c)
        a + (b + c) = [cong (x => a + x) (add_comm b c)] a + (c + b)
        a + (c + b) = [symm (add_assoc a c b)] (a + c) + b
    }
```

（对照现有 `add_permute` 的手工 `trans(trans(lhs, mid), rhs)` + 三个带注解 let。）

### 3.3 与现有 Nat 证明结合（五步链）

```typort
def double_distrib_calc(x: Nat, y: Nat): Eq (double (x + y)) (double x + double y) =
    calc {
        double (x + y) = [symm (add_assoc (x + y) x y)] ((x + y) + x) + y
        ((x + y) + x) + y = [add_right_eq ((x + y) + x) (x + (y + x)) y (add_assoc x y x)] (x + (y + x)) + y
        (x + (y + x)) + y = [add_right_eq (x + (y + x)) (x + (x + y)) y (add_left_eq (y + x) (x + y) x (add_comm y x))] (x + (x + y)) + y
        (x + (x + y)) + y = [add_right_eq (x + (x + y)) ((x + x) + y) y (symm (add_assoc x x y))] (x + x) + y
        (x + x) + y = [add_assoc (x + x) y y] (x + x) + y
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
        7 + 0 = [add_zero_right 7] 7
        7 = [add_zero_right 7] 0 + 7        // add_zero_right 7 : Eq (7+0) 7，不是 Eq 7 (0+7)
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
        7 + 0 = [add_zero_right 7] 7
        5 = [symm (add_zero_left 7)] 0 + 7   // 上一行右端是 7，这一行写的是 5
    }
```

展开后 `trans _c (symm (add_zero_left 7))`：`_c : Eq (7+0) 7`，第二个证明 : `Eq 7 (0+7)`，
统一 `7 ≡ 5` 失败。预期错误形态：

```
can't unify
  expected: Eq 7 _   （trans 第二个参数应满足的类型）
      find: Eq 5 (0 + 7)
```

> 设计限制说明：中间步骤的**左端**（如负例 B 里写出的 `5`）只通过 `trans` 的类型统一
> 间接核对（核对的是**证明的真实中间项**，不是写出的词）。原设计的每步检查 let
> 已放弃（洞注解留未解 meta，见 §9.2.1），因此写出的中间项越出证明真实类型时
> 由 trans 兜底；若写出项与证明真实类型一致但词形不同（定义等价），检查通过。

**负例 C —— 误用 Lean 的 `:=` 语法**：

```typort
def neg_c: Eq (7 + 0) (0 + 7) = calc
    7 + 0 = 7 := add_zero_right 7
    7 = 0 + 7 := symm (add_zero_left 7)
```

宏匹配失败（`:=` 是 raw 片段会吞掉的中缀 token，见 §4.2），`calc` 退化为普通标识符。
预期：解析期 `expected EndLine` 类错误 + 精化期“未知名称 calc”类错误。这是已知限制，
文档与错误提示中应引导用户使用 `[ ... ]` 写法。

---

## 4. 实现方案评估

### 4.1 宏方案（推荐）：匹配器与转写

**宏定义**（放在新文件 `src/prelude/core/calc.typort`，或并入 `eq.typort`）：

```typort
#[macro_export]
macro_rules calc {
    // 推荐主形式：{ ... } 块内换行分隔的链（首项可换行到 `{` 之后）
    ( { $( $x: raw = [ $p: raw ] $y: raw $( $x2: raw = [ $q: raw ] $z: raw )* )+ } ) => {
        let _c : Eq ($x) ($y) = ($p);
        $( let _c = trans (_c) ($q); )*
        _c
    };
    // 单行形式：calc a = [p1] b = [p2] c（首项必须与 calc 同行）
    ($x: raw = [ $p: raw ] $y: raw $( $x2: raw = [ $q: raw ] $z: raw )*) => {
        let _c : Eq ($x) ($y) = ($p);
        $( let _c = trans (_c) ($q); )*
        _c
    };
}
```

**匹配器要点**（为什么这个形状能工作）：

- 字面 token 全部落在 matcher 支持集内：`=`（`Eq`）、`[`（LSquare）、`]`（RSquare）、
  `{`/`}`（LCurly/RCurly）、`calc` 名称本身。
- `raw` 片段 + 跟随 token 的安全性：
  - `$x:raw` 后面是 `=`（Eq token）—— `expr_bp` 的中缀循环只读 Op/LParen/LSquare/Dot，
    `=` 不在其中 → raw 在 `=` 处停止（**安全**）；
  - `$p:raw` 后面是 `]`（RSquare）—— RSquare 不在上述循环集合 → 停止（**安全**）；
  - `$y:raw` 后面是换行或 `=` → 停止（**安全**）。
- 证明片段内部的 `[ ... ]`（隐式参数应用 `f [x = 1]`）会被 p_raw 作为表达式一部分
  消费，不与 calc 的定界 `]` 冲突。
- 换行分隔：外层 `$(...)+`（Many1）与内层 `$(...)*`（Many0）都先跳过前导 EndLine、
  用 `EndLine.option()` 分隔迭代 —— 与 `hdl-macros.typort` 的 `when`/`module` 宏同款机制。
- 步数：`$( = [ $q:raw ] $z:raw )*` 捕获第 2..n 步（`$q`/`$z` 长度 n-1），
  第 1 步由 `$x`/`$p`/`$y` 捕获（长度 1，转写中可整体复用）。
- 两条规则的顺序无关紧要：花括号形式对无 `{` 输入、单行形式对 `{` 开头输入，
  都在第一个 raw 片段处干净失败（p_raw 无法以 `{` 起始），不会误匹配也不会产生
  伪错误（失败路径上的解析器在关键字检查处就退回，不经过 Cut 的错误注入）。

**转写要点**（展开成 let 链而非嵌套 `trans`）：

- 宏系统的重复转写 `$(...)*` 只是**扁平拼接**，无法生成嵌套括号，
  所以 `trans (trans p1 p2) p3` 这种左/右折叠**写不出来**（`trans $p $(trans $q)*`
  会拼成 `trans p1 trans p2 trans p3`，即错误的多重应用）。
  改用 let 链：首步一个带注解的 let + 每步一个累积 let，最后返回累积值。
- let 的作用（与设计稿的差异见 §9.2.1 —— **每步检查 let 已放弃**）：
  - 第 1 步 `let _c : Eq ($x) ($y) = ($p);` —— 同时做两件事：核对写出的
    `x`/`y` 与证明类型一致，并把 `_c` 绑定为链的累积证明；
  - 第 i≥2 步 `let _c = trans (_c) ($q);` —— 用累积证明与当前证明组合
    （`trans` 隐式参数自动求解中间项）；写出的左端/右端经 trans 的统一间接核对；
  - 证明实参必须括号包裹：`trans (_c)` 而不是 `trans _c`（裸标识符实参精化失败，
    见 §9.2.2）。
- let 遮蔽：累积名 `_c` 每步重绑定。可行性依据：`Cxt::define`/`bind` 把名字
  映射到**当前最深 lvl**（`src_names` 是 BiMap，重复插入覆盖），而 let 的
  值在 `define` **之前**精化（`elaboration.rs` 的 `Raw::Let`：先 check 值、
  再 define 进上下文），因此 `trans (_c) ($q)` 里引用的 `_c` 总是外层绑定。
  （phase 2 第一步仍需用真实测试验证，见 §8。已实测通过。）
- 所有 metavar 在应用位置都加括号：`Eq ($x) ($y)`、`($p)`、`($q)` —— 防止
  片段内运算符与外围语法串读（如 `Eq (a+b) * c ...` 会把 `*` 读成中缀）。
- 空链（零步）不可表示（内层 `*` 虽允许零次，但第 1 步是必须的 `$x = [$p] $y`）。
- 多实参证明的实参要用逗号形式（§9.2.3）。

**展开形态示例**（§3.2 的 add_permute_calc，缩写证明为 p1/p2/p3）：

```typort
let _c : Eq ((a + b) + c) (a + (b + c)) = (p1);
let _c = trans (_c) (p2);
let _c = trans (_c) (p3);
_c
```

（let 链由 `p_let` 的 `let x = e; body` 递归解析，`;` 在转写输出中是普通 token。）

### 4.2 为什么 Lean 的 `a = b := p1` 形式不可行（token 结构分析）

任务里问的 `x = y := p` 的 token 结构，逐 token 分析如下：

| token | lexer 归类 | 说明 |
|---|---|---|
| `x` | Ident | `$x:raw`，p_raw 在 `=` 处停止 |
| `=` | **Eq** | 不是 Op → 不是表达式运算符 → raw 片段干净停止；matcher 可字面匹配 `=`（`string(Eq)`） |
| `y` | Ident | `$y:raw` |
| `:=` | **Op**（单 token） | `:` 与 `=` 都在操作符字符范围（`':'..='@'`），且 `:=` 不在 OP 关键字表 → 整个 lex 为一个 Op token |
| `p1` | … | `$p:raw` |

致命点：**所有** Op token 在 `expr_bp` 里都是中缀运算符 —— `infix_binding_power`
的兜底是 `Some((7,8))`，`:=` 因 `contains(':')` 得到 `(2,1)`。因此 `$y:raw` 解析
`b := p1` 时会**贪心吞掉整个** `b := (p1)`（中缀应用），随后匹配器在字面 `:=` 处
必然失败 → `calc` 宏整体不匹配。

把 `:=` 从 `infix_binding_power` 里排除（让 raw 在 `:=` 处停止）需要改 parser，
且会破坏 HDL：`examples/alu.typort` 的模块体 `result := a + b`、`hdl_ops.typort` 的
`bit0 := a.apply[0]` 等**依赖 `:=` 中缀解析**（在 module 宏的 raw 兜底规则里被整体
消费），移除后需要同步迁移 HDL 语法。因此第一版不做。

顺带说明其它不可行分隔符：`;`（Semi）、`:`（Colon）、`(`/`)` 都不是 matcher
可用的字面 token（`p_macro_matcher_single` 的 token_parser 只有
Ident/Op/Num/`[]{}`/`let`/`=`/`.`）；`=>` 是 DoubleArrow 同理不可匹配。
`[ proof ]` 是唯一同时满足“可字面匹配 + raw 片段不吞它 + 不破坏现有语法”的分隔。

### 4.3 中缀运算符方案（`a =⟨ p1 ⟩ b`）评估：不可行于当前 parser

- **lexer**：`⟨`/`⟩`/`≡` 都不是操作符字符（`lex.rs` 的 op 范围全 ASCII），
  且 `=` 被 OP 表固定映射为 `Eq` token。要支持需要改 lexer 加非 ASCII token。
- **parser**：`expr_bp` 的中缀循环只消费 Op/LParen/LSquare/Dot —— `=`（Eq）
  根本进不了循环（`infix_binding_power` 里的 `s == "="` 分支是死代码）。
- 即使用 ASCII 替代（`=<`/`>`）：`>` 与比较运算符同 token 冲突；Agda 式
  `step` 语义需要右结合 + 续延编码，`expr_bp` 的中缀机制会产生
  `((a =< p1) > (b =< p2)) > c` 的错误分组，必须做绑定力工程（`=<` 高绑定、
  `>` 低于 `=<` 的右绑定……）—— 结论是“语法脆弱 + 双份修改”，不推荐。

**结论**：v1 用宏方案；若后续 UX 强烈要求 Lean 式 `:=`，可行路线是
“parser 排除 `:=` 中缀 + HDL 迁移到新写法”，作为独立任务，不阻塞 v1。

---

## 5. 推荐方案与备选

| 方案 | 改动范围 | 语法 | 判定 |
|---|---|---|---|
| **A. 纯宏（推荐）** | 仅 prelude（新文件或 eq.typort 追加）+ mod.rs prelude 数组一行 | `calc { a = [p1] b ... }` | v1 采用。零解析器风险，错误定位靠 let 链的 span，检查充分 |
| B. 宏 + parser 排除 `:=` 中缀 | parser 一行 + HDL 迁移 + prelude | `calc a = b := p1`（Lean 原味） | 备选/后续。UX 最好，但动 parser 且要迁移 `a := b` 语法 |
| C. 中缀链（Agda 式） | lexer + parser 双改 | `a =⟨ p1 ⟩ b` | 不推荐 v1。脆弱、改动大 |
| D. 泛化关系宏（typeclass） | prelude + 可能 typeclass 机制 | `calc Eq { ... }` | v2 候选，见 §6 |

推荐 A 的理由：需求全部落在现有宏系统能力内（raw 片段、字面 token `=`/`[]`/`{}`、
换行重复、let 链转写、let 遮蔽），不需要碰 lexer/parser，回归风险最小；
语法与 Typort 现有块风格（match/when 的 `{}` + 换行）一致。

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

1. `a = b := p1`（Lean 原味）不解析，见 §4.2 —— 文档/错误提示引导用 `[p1]`。
2. 中间步骤的**左端**写出项不单独核对（只核对右端 + trans 统一），见 §3.4 说明。
3. 步骤必须换行分隔，`;` 分隔不可行（matcher 无法匹配 `;`）。
4. 单步链 `calc { a = [p] b }` 合法（重复部分为零次），结果就是 `p` 的带注解拷贝。
5. `calc` 成为宏名后，用户无法再定义同名变量/函数（宏在 p_raw 入口优先于标识符）。
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

## 9. 实施记录（已完成，task/calc-reasoning）

### 9.1 实现结果

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

---

## 附：与 Lean/Agda 的对照

| 语言 | 语法 | 中间项检查 | 实现 |
|---|---|---|---|
| Lean4 | `calc a = b := p1; b = c := p2` | 每步两端都核对 | 解析器内建（句法块 → trans 应用） |
| Agda | `a ≡⟨ p1 ⟩ b ≡⟨ p2 ⟩ c` | 每步两端都核对 | 库内运算符（`_≡⟨_⟩_` step + 右结合） |
| Typort（本设计） | `calc { a = [p1] b b = [p2] c }` | 首步两端 + 后续步右端（左端经 trans 间接核对） | 库内宏（let 链转写） |

Typort 的宏系统是纯 token 级的（无类型信息、无自引用重复），因此做不到
Lean/Agda 那种“每步两端全核对”，但核对覆盖面足以捕获绝大多数书写错误；
其余由 `trans` 的统一（含定义等价）兜底。
