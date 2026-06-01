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

```
import mylib.{ util1, util2 }    // 选择性导入
import mylib.*                     // 通配导入
```

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

- `package` 声明设定当前命名空间前缀，之后的声明自动加前缀
- `import` 导入其他命名空间的名称
- 变量查找顺序：`局部变量 → 当前声明 → namespace_prefix 限定 → 后缀匹配 fallback`

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
