# Typort Language — 语法参考

> 面向用户的 Typort 语言语法文档。
> Typort 是基于 Martin-Löf 类型论（MLTT）的依赖类型语言，支持类型类、模式匹配、宏、命名空间。

---

## 1. 注释

```
// 单行注释
/* 多行注释 */
```

---

## 2. 声明（顶层）

### 2.1 函数定义 `def`

```
def name(param1: Type1, param2: Type2): ReturnType =
    body
```

**多参数**：逗号分隔或空格分隔：

```
def add(x: Nat, y: Nat): Nat = nat_add_helper x y
```

**隐式参数**：用 `[ ]` 包围：

```
def cong[A, B, x: A, y: A](f: A -> B, e: Eq x y): Eq (f x) (f y) =
    match e { case refl(a) => refl (f a) }
```

→ `A`, `B`, `x`, `y` 是隐式参数，调用时自动推导或手动填：`cong[Nat, Nat] f e`

**无参数函数**：

```
def fortytwo: Nat = 42
```

### 2.2 枚举 `enum`

```
enum Name[implicit_params] {
    Case1(arg1: Type1, arg2: Type2)  // 无返回值 = 指向自身
    Case2(args...) -> ReturnType     // 有返回值 = GADT 风格
}
```

**示例**：

```
enum Nat {
    zero
    succ(n: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] 0
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (l + 1)
}
```

**构造子访问**：`TypeName.Constructor`，例如 `Nat.zero`、`Nat.succ`。自动导入别名后可直接写 `zero`。

**构造子调用**（无参数）：`zero` / （有参数）：`succ(zero)` / `cons(x, xs)`

### 2.3 结构体 `struct`

```
struct Name[implicit_params] {
    field1: Type1
    field2: Type2
}
```

**示例**：

```
struct Product[A, B] {
    fst: A
    snd: B
}
```

**构造**：`new Product(value1, value2)` 或 `Product.mk fst snd`

**字段访问**：`value.field`

### 2.4 Trait 声明 `trait`

```
trait TraitName[params] {
    def method1(arg: Type): RetType
    def method2(arg: Type): RetType
}
```

**示例**：

```
trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

trait Data {
    def :=(that: Self): Unit
    def expr: Expr
}
```

`Self` 关键字表示实现此 trait 的类型。

### 2.5 Trait 实现 `impl`

#### 为类型实现 trait

```
impl[params] TraitName[trait_args] for Type {
    def method(...): Ret = body
}
```

**示例**：

```
impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = nat_add_helper this that
}
```

#### 为类型添加固有方法（非 trait）

```
impl[params] Type {
    def method(...): Ret = body
}
```

**示例**：

```
impl[width: Nat] UInt[width] {
    def +^(that: UInt[width]): UInt[width + 1] =
        UInt.mk(None, binary(this.expr, "+^", that.expr))
}
```

### 2.6 Package 与 Import

```
package mylib.utils

// 之后的声明会被自动加前缀 mylib.utils
```

- `package` 是**绝对路径**（不嵌套叠加）：后续所有声明（def/enum/struct/class/trait/impl 的方法）自动带上完整前缀。
- `package` 在包内只应出现一次；中途再次 `package x` 会**切换**前缀为 `x`（文件内可声明多个包，符号分别写入全局）。

`import` 三种形态：

```
import mylib.{ util1, util2 }    // 花括号：选择性导入（只带名字本身，不带 namespace/类型前缀）
import mylib._                   // 通配：导入该命名空间全部成员
import mylib.util1               // 单名：等同花括号单元素
import mylib.MyType._            // 子命名空间：导入类型 MyType 的成员（含 `MyType.mk` 等）
```

**实际语义（与字面直觉的差异）**：

- **S1 — 单名/花括号只带名字本身**：`import mylib.MyType.member` 只导入 `member`，**不**导入 `MyType`（要导入类型需 `import mylib.MyType` 或 `import mylib.MyType._`）。通配 `import mylib._` 会把 `MyType` 本体也带入。
- **S3 — 花括号不别名前缀本体**：`import mylib.{x, y}` 只带 `x`、`y`；`mylib` 本身不可用。通配则不同。
- **D2 — 末段一律当成员**：`import a.b.c` 的 `c` 被当作 `a.b` 的成员；一个字面名为 `c` 的包无法通过该路径导入（需 `import a.b.c._` 或 `package` 引用处显式写全名）。
- **变量查找顺序**（含 prelude 例外）：`局部变量 → 全局 decl 精确（含 prelude 裸别名）→ import 别名 → namespace_prefix 限定 → 后缀 fallback`。
- **D1 — prelude 裸别名永久优先**：prelude 自动导入的裸名（`zero`、`succ`、`true` 等）永久占用；`import mylib._` 中与 prelude 同名的成员（如 `mylib.zero`）**裸用时永远解析到 prelude 别名**（除非限定访问 `mylib.zero`）。这是有意的"prelude 例外优先"，无警告。
- **后缀 fallback 限域**：裸名只能解析到"首段是 decl key 或本文件可见命名空间"的候选（如 `mux` → `Expr.mux`）；`import` 一个命名空间后，其成员经 import 别名解析（不靠 fallback）。

### 2.7 Derive

```
derive Show, Eq for MyType
```

（当前实现中 derive 主要用于类型类实例的自动派生。）

### 2.8 调试输出

```
println(expr)
```

在 LSP 中打印表达式（显示为 information diagnostic）。

---

## 3. 表达式

### 3.1 变量与引用

```
x                           // 局部变量
MyType.Constructor          // 枚举构造子（全限定名）
module.function             // 命名空间+函数访问
```

### 3.2 函数应用

```
f x                         // 显式参数（空格分隔）
f(x, y)                     // 括号分组
f [arg]                     // 隐式参数（方括号）
f [name = arg]              // 按名传隐式参数
```

**示例**：

```
add (succ zero) zero
cong[Nat, Nat] f e
```

### 3.3 Lambda

```
x => body                   // 显式参数
[x] => body                 // 隐式参数
[Name = x] => body           // 命名隐式参数
```

**示例**：

```
x => x + 1
[x: Nat] => x
```

### 3.4 函数类型（Pi 类型）

```
(param: DomainType) -> CodomainType     // 显式参数
[param: DomainType] -> CodomainType     // 隐式参数
```

**示例**：

```
Nat -> Nat
[A: Type 0] -> A -> A
(x: Nat) -> Vec[Boolean] x
```

### 3.5 宇宙层级

```
Type 0    // 可写为 U0
Type 1    // U1
...
```

### 3.6 Let 绑定

```
let name: Type = expr;
body
```

**示例**：

```
let double: Nat = x + x;
double * double
```

### 3.7 占位符 / Hole

```
_   // 类型推导的占位符
```

Hole 会在编译期报 unsolved meta 错误。

### 3.8 字符串字面量

```
"hello, world"
```

字符串类型是 `String`，编译期操作通过内建函数（`string_concat`）。

### 3.9 字段访问

```
expr.field
```

用于 struct 字段、枚举构造子数据、命名空间成员。

**示例**：

```
myProduct.fst
myUInt.expr
```

### 3.10 模式匹配

```
match expr {
    case Pattern1 => body1
    case Pattern2 => body2
}
```

**模式语法**：

```
_                        // 通配（忽略值）
Name                     // 构造子匹配（零参数）
Name(pat1, pat2)         // 构造子匹配（带子模式）
```

**示例**：

```
match x {
    case zero => zero
    case succ(n) => n
}
```

---

## 4. 运算符优先级

Typort 的运算符优先级由 parser 内嵌。以下按**优先级从高到低**排列（同一格内的优先级相同，左结合）：

| 优先级 | 类别 | 运算符 | 结合性 |
|--------|------|--------|--------|
| 最高 | 原子 | 字面量、变量、`(...)`、`{...}` | — |
| | 字段访问 | `.` | 左 |
| | 函数应用 | `f x`（空格） | 左 |
| | 隐式应用 | `f [x]` `f [n = x]` | 左 |
| | 一元 | `!` `-`（前缀负号） | 右 |
| | 乘除/取余 | `*` `/` `%` | 左 |
| | 移位 | `<<` `>>` | 左 |
| | 加法/减法 | `+` `-` `+^` `-^` | 左 |
| | 位运算 | `&` | 左 |
| | | `^` | 左 |
| | | `\|` | 左 |
| | 拼接 | `##` | 左 |
| | 比较 | `<` `<=` `>` `>=` `===` `=/=` | 左 |
| | 赋值 | `:=` | 右 |
| | Lambda | `=>` | 右 |
| | Pi 类型 | `->`（函数类型箭头） | 右 |
| 最低 | 类型注解 | `: Type` | — |

**规则**：有歧义时用括号 `( )` 消除——使用风格与 Haskell/ML 类似。

### 优先级示例

```
a + b * c         // 解析为 a + (b * c)
a .field + b      // 解析为 (a.field) + b
\x => a + b       // 解析为 \x => (a + b)
f x + g y         // 解析为 (f x) + (g y)
(x: A) -> B -> C  // 解析为 (x: A) -> (B -> C)
a := b + c        // 解析为 a := (b + c)
!a + b            // 解析为 (!a) + b
a ## b + c        // 解析为 a ## (b + c)
```

---

## 5. 类型类系统

### 5.1 内置核心 Trait

| Trait | 方法 | 说明 |
|-------|------|------|
| `Add[T, O]` | `+(that: T): O` | 加法 |
| `Sub[T, O]` | `-(that: T): O` | 减法 |
| `Mul[T, O]` | `*(that: T): O` | 乘法 |
| `Div[T, O]` | `/(that: T): O` | 除法 |
| `Rem[T, O]` | `%(that: T): O` | 取余 |
| `And[T, O]` | `&(that: T): O` | 逻辑与 |
| `Or[T, O]`  | `\|(that: T): O` | 逻辑或 |
| `Xor[T, O]` | `^(that: T): O` | 逻辑异或 |
| `Into[O]` | `into: O` | 类型转换 |
| `Default` | `default: Self` | 默认值 |
| `Clone` | `clone: Self` | 克隆 |
| `Not` | `!: Self` | 逻辑非 |
| `Neg` | `-: Self` | 算术负 |
| `Cat[T, O]` | `##(that: T): O` | 位拼接 |
| `Cast[U]` | `cast(prove: Eq(Self, U)): U` | 安全类型转换 |

### 5.2 `this` 关键字

在 impl 块内部，`this` 指代被 impl 的类型的值。

### 5.3 outParam

`outParam(Type 0)` 标记输出类型参数——该参数由类型类求解器推导，不参与匹配。例如 `Add[T, O]` 的 `O` 由 `T` 和 impl 决定。

---

## 6. 内置类型

| 类型 | 说明 | 值示例 |
|------|------|--------|
| `Nat` | 自然数 | `zero`, `succ(zero)`, `1` |
| `Boolean` | 布尔值 | `true`, `false` |
| `String` | 字符串 | `"hello"` |
| `Unit` | 单元类型 | `unit` |
| `Vec[T](len)` | 类型化向量 | `nil`, `cons(x, xs)` |
| `Option[T]` | 可选值 | `None`, `Some x` |
| `Result[T, E]` | 结果类型 | `Ok x`, `Err e` |
| `Either[A, B]` | 二选一 | `Left a`, `Right b` |
| `List[T]` | 链表 | `Empty`, `Cons(head, tail)` |
| `Product[A, B]` | 积 | `new Product(fst, snd)` |
| `Eq[A](x, y)` | 等式 | `refl a` |

**Nat 字面量**：整数字面量是语法糖展开为 `succ^n(zero)`，例如 `3` = `succ(succ(succ(zero)))`。

---

## 7. 宏系统

文件可以 `export` 宏规则，供其他文件在解析阶段使用。

导出宏在文件顶部声明，宏匹配在 token 层面生效。宏展开在解析阶段完成，不影响类型系统。

---

## 8. 命名空间

- `package` 声明设定当前命名空间前缀，之后的声明自动加前缀（绝对路径，不叠加；文件内可多次切换）。
- `import` 导入其他命名空间的名称（见 §2.6 的三种形态与 S1/S3/D2 语义差异）。
- 变量查找顺序：`局部变量 → 全局 decl 精确（含 prelude 裸别名）→ import 别名 → namespace_prefix 限定 → 后缀 fallback`。
- 后缀 fallback 限域：仅匹配"首段是 decl key 或本文件可见命名空间"的候选（`Expr.mux`）；命名空间级裸名（`mylib.foo`）必须 `import` 才能解析。
- **跨文件可见性**：文件分析基于全局符号并集；`import` 使 provider 的符号按依赖图（前缀匹配）重建依赖者。trait/固有方法等注册已随文件同步（见 namespace-completion-plan.md）；trait **实例**跨文件同步未实现（受核心检查器 meta 管理 bug 阻塞）。
- **D5 — 磁盘文件发现未实现**：`import` 只对已打开的文件生效；未打开但存在于磁盘的文件不会被自动发现（`did_change_watched_files`/workspace folders 为空实现）。需打开 provider 文件或将来实现 workspace 扫描。

---

## 9. 快速参考

```
// 函数定义
def add(x: Nat, y: Nat): Nat = nat_add_helper x y

// 带隐式参数
def id[A](x: A): A = x

// 枚举
enum Option[A] {
    None
    Some(value: A)
}

// 结构体
struct Pair[A, B] {
    first: A
    second: B
}

// Trait
trait Show {
    def show: String
}

// Impl
impl Show for Nat {
    def show: String = nat_to_dec this
}

// 模式匹配
match opt {
    case None => "nothing"
    case Some(x) => x.show
}

// Lambda
x => x + 1

// 函数类型
Nat -> String
[A: Type 0] -> A -> A

// Let
let x: Nat = 5;
x + x

// Hole（占位）
_

// 字符串
"hello"

// 字段访问
pair.first
```
