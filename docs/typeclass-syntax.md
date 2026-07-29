# Typort Typeclass 系统语法说明书

> **对应模块**: `src/L13_namespace/`  
> **版本**: L13 (当前实现)  
> **状态**: ✅ 成熟 — 支持核心 typeclass 范式  
> **文件后缀**: `.typort`

---

## 目录

1. [概述](#1-概述)
2. [Trait 声明](#2-trait-声明)
3. [Impl 声明](#3-impl-声明)
4. [隐式参数与实例解析](#4-隐式参数与实例解析)
5. [方法调用语法](#5-方法调用语法)
6. [Derive 宏](#6-derive-宏)
7. [outParam 详解](#7-outparam-详解)
8. [Self 与 this](#8-self-与-this)
9. [错误处理](#9-错误处理)
10. [完整示例集](#10-完整示例集)
11. [实现架构](#11-实现架构)
12. [语法速查表](#12-语法速查表)

---

## 1. 概述

Typort 的 typeclass 系统受 Scala 3 (`given`/`using`) 和 Rust (`trait`/`impl`) 启发，结合了 ML 风格的一阶实例搜索。

| 概念 | 关键字 | 说明 |
|------|--------|------|
| **Trait**（类型类） | `trait` | 定义一组多态方法签名和可选默认实现 |
| **Impl**（实例） | `impl X for Y` | 为类型 `Y` 实现 trait `X` |
| **固有 Impl** | `impl X { }` | 为类型 `X` 添加方法（不涉及 trait） |
| **隐式参数** | `[c: Show[T]]` | 触发自动实例搜索 |
| **输出参数** | `outParam(Type 0)` | 标记由实例确定的输出类型参数 |
| **Supertrait** | `trait Sub: Super` | Trait 继承 |

---

## 2. Trait 声明

### 2.1 基本语法

```
trait <Name>[<泛型参数>] [: <Supertrait> + <Supertrait>] {
    def <方法名>(<参数>): <返回类型> [= <默认实现>]
    type <关联类型名> [= <默认类型>]
}
```

`trait` 关键字后跟 trait 名称和可选的泛型参数。可选地通过 `: SupertraitA + SupertraitB` 指定父 trait。

### 2.2 参数形式

Trait 的参数用 `[]`（隐式）或 `()`（显式）包裹：

```
trait Eq[A] { ... }                          // 隐式参数
trait Show[T] { ... }                        // 隐式参数
trait Add[A, O: outParam(Type 0)] {          // 输出参数
    def +(that: A): O
}
```

**重要规则**：

- **输入参数**（非 `outParam`）：参与实例匹配。
- **输出参数**（`outParam`）：不参与实例匹配，由实例自身类型确定。
- `outParam` 大致定义为 `def outParam[A](a: A): A = a`，只在类型层面起作用。

### 2.3 关联类型

```
trait Container {
    type Item                   // 关联类型，无默认
    def get: Item
}

trait Container {
    type Item = Nat             // 关联类型，有默认值
    def get: Item
}
```

关联类型内部被 desugar 为 `outParam` 隐式参数。

### 2.4 方法默认实现

```
trait Show {
    def show: String = "default"         // 有默认实现
    def custom_show: String              // 无默认实现，必须由 impl 提供
}
```

### 2.5 运算符方法名

```
trait Add[T, O: outParam(Type 0)] { def +(that: T): O }
trait Not                            { def ! : Self }
trait Less                           { def <(that: Bool): Bool }
```

运算符作为方法名时，作用在 `this` 上实现中缀/前缀操作符重载。

### 2.6 Supertrait（Trait 继承）

```
trait Base { def base_method: String }

trait Sub: Base {                              // 单一父 trait
    def sub_method: String
}

trait Mega: Show + Eq + Hash {                 // 多个父 trait
    def mega_method: String
}
```

**传递性**：`trait Deep: Mid` 且 `trait Mid: Base` 时，`Deep` 继承所有方法。

**循环检测**：编译器检测 `A: B; B: C; C: A` 等循环并报错。

---

## 3. Impl 声明

### 3.1 Trait Impl

```
impl[<泛型参数>] <TraitName>[<trait参数>] for <目标类型> {
    type <关联类型名> = <具体类型>
    def <方法名>(<参数>): <返回类型> = <实现体>
}
```

示例：

```
impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = nat_add_helper this that
}
```

### 3.2 泛型 Impl

```
impl[T] Show for T {
    def show: String = "generic"
}

impl[A, B] Pair[A, B] {
    def first: A = this.fst
    def second: B = this.snd
}
```

### 3.3 固有 Impl（inherent impl）

```
impl Nat {
    def double: Nat = this + this
    def triple: Nat = this + this + this
}

impl[A] Option[A] {
    def get_or_else(default: A): A =
        match this { case None => default; case Some(a) => a }
}
```

固有 impl 没有 `for X` 部分。内部编译器生成合成 trait（如 `$trait_name$Nat`）来管理这些方法。

### 3.4 关联类型的赋值

```
impl Container for Bool {
    type Item = Bool                   // 覆盖 trait 中的关联类型
    def get: Bool = true
}

impl Container for Nat {
    // type Item 省略，使用默认 Nat
    def get: Nat = succ zero
}
```

### 3.5 方法覆盖

```
trait Show { def show: String = "default" }
impl Show for Bool { def show: String = "override" }
// impl 的 show 覆盖了默认实现
```

### 3.6 Static 方法

```
impl Foo {
    static def create(...): Foo = ...    // 无 this
}
```

使用 `static def` 声明不接收 `this` 的静态方法。

---

## 4. 隐式参数与实例解析

### 4.1 隐式参数语法

函数参数用 `[]` 包裹时为隐式参数：

```
def describe_val[T][d: Describable[T]](x: T): String = d.describe x
def print_it[T][s: Show[T]](x: T): String = s.show x
```

**自动填充规则**：
1. 调用点自动搜索匹配的 trait 实例
2. `[name: Trait[T]]` 中的 `name` 匹配对应 trait 的实例
3. 不要求显式传递（除非用命名语法 `f[trait_name = ...]`）

### 4.2 Where 子句（语法糖）

```
def test[T](x: T): String where T: Show + Eq = _show_T.show x
```

等价于：

```
def test[T][_show_T: Show[T], _eq_T: Eq[T]](x: T): String = _show_T.show x
```

**绑定规则**：
- `where T: Show + Eq` → `[_show_T: Show[T], _eq_T: Eq[T]]`
- 参数名规则：`_<trait小写>_<类型名>`

### 4.3 实例解析算法

实例搜索使用带回溯的深度优先搜索：

```
1. head_index O(1) 筛选候选实例
   ↓
2. val_match 匹配输入参数
   ↓
3. 解析子目标（依赖关系）
   ↓
4. 全部解决 → 返回实例
   ↓ (失败)
5. 回溯到下一个候选
```

**关键特性**：

- **Head-indexing**：按第一个非 outParam 参数的 head constructor 建立索引
- **outParam 延迟**：outParam 为 Flex（未解析）时不参与匹配
- **Flex 默认**：尝试将多个非 outParam 统一到已解析的那个

---

## 5. 方法调用语法

### 5.1 Dot-call（点号调用）

```
obj.method              // 无参数方法
obj.method arg          // 单参数方法（函数式风格）
obj + arg               // 运算符方法（中缀）
obj.< arg               // 运算符方法（显式中缀）
!obj                    // 前缀运算符方法
obj.method[a, b] c      // 带隐式参数的方法调用
```

**解析优先级**：
1. 查 namespace（固有 impl 方法）
2. 查 trait 方法
3. 多个 trait 有同名方法且都满足 → 歧义错误

### 5.2 歧义检测

```
trait Foo { def method: String }
trait Bar { def method: String }
impl Foo for Bool { def method = "foo" }
impl Bar for Bool { def method = "bar" }

println (true.method)    // ERROR: ambiguous method `method`
                         // found in traits `Foo`, `Bar`
```

如果只有一个 trait 有实例满足条件，则无歧义：

```
impl Foo for Nat { def method = "foo_nat" }
// Bar 没有为 Nat 实现
println (two.method)     // OK → "foo_nat"
```

---

## 6. Derive 宏

### 6.1 语法

```
#[derive(Show, Bundle)]
struct Point[T] { x: T; y: T }

#[derive(Show)]
enum Bool { true; false }
```

`#[derive(...)]` 放在 `enum` 或 `struct` 声明之前。

### 6.2 内置 Derive

| Derive | 作用于 | 生成内容 |
|--------|--------|----------|
| `Show` | enum, struct | `impl Show for T { def show: String = ... }` |
| `Bundle` | struct（单构造器） | `impl Bundle for T { ... }` |

### 6.3 自定义 Derive

通过 Rust 端 `DeriveRegistry` 注册：

```rust
pub type DeriveMacro = fn(&Decl) -> Vec<Decl>;
pub fn register_derive(name: &str, derive_fn: DeriveMacro);
```

---

## 7. outParam 详解

### 7.1 定义

```
trait Add[T, O: outParam(Type 0)] {    // O 是输出参数
    def +(that: T): O
}
```

`outParam` 标记由 impl 确定、而非调用者提供的类型参数。

### 7.2 行为规则

| | 输入参数 | 输出参数 |
|--|----------|----------|
| 实例匹配 | 参与 | 跳过 |
| 调用者指定 | 需要 | 不需要 |
| 类型约束 | 可参与 | 可参与 |
| 多候选歧义 | 立即匹配 | 延迟匹配 |

1. outParam 不参与 `val_match`
2. outParam 为 Flex 且多候选时，延迟解析
3. 等待上下文约束缩小到唯一候选

---

## 8. Self 与 this

| 关键字 | 含义 | 可用位置 |
|--------|------|----------|
| `this` | 接收者实例（方法所属的具体值） | impl 方法体中 |
| `Self` | （示例名称）表示"实现此 trait 的具体类型" | trait 参数约定 |

注意：`Self` 不是语言关键字，而是 trait 声明中第一个隐式参数的约定名称。

---

## 9. 错误处理

### 9.1 缺失方法

```
trait Show { def show: String; def other: String }
impl Show for Bool {
    def show = "hello"
    // 缺少 other 且无默认 →
    // ERROR: "... has no default implementation"
}
```

### 9.2 Supertrait 缺失方法

```
trait Base { def base_method: String }
trait Sub: Base { def sub_method: String }
impl Sub for Bool {
    def sub_method = "sub"
    // 缺少 base_method → ERROR
}
```

### 9.3 歧义方法

```
error: ambiguous method `method`: found in traits `Foo`, `Bar`
```

### 9.4 找不到方法

```
error: `...` has no object `methodName`
```

### 9.5 Supertrait 循环

```
trait A: B { ... }
trait B: C { ... }
trait C: A { ... }   // ERROR: cyclic supertrait
```

---

## 10. 完整示例集

### 10.1 基本用法

```typort
trait Show {
    def show: String
}

impl Show for Bool {
    def show: String =
        match this {
            case true  => "true"
            case false => "false"
        }
}

def print_it[T][s: Show[T]](x: T): String = s.show x
println (print_it true)       // 通过隐式参数
println (true.show)           // 通过点号调用
```

### 10.2 运算符重载 + outParam

```typort
trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}

impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = nat_add_helper this that
}

def five = two + three
println five                  // → 5
```

### 10.3 泛型固有 Impl

```typort
impl[A] Option[A] {
    def get_or_else(default: A): A =
        match this {
            case None    => default
            case Some(a) => a
        }
}

impl[A, B] Pair[A, B] {
    def first: A  = this.fst
    def second: B = this.snd
    def swap: Pair[B, A] = new Pair(this.snd, this.fst)
}
```

### 10.4 Supertrait + 默认方法

```typort
trait Base {
    def base_method: String = "base_default"
}
trait Sub: Base {
    def sub_method: String
}
impl Sub for Bool {
    def sub_method = "sub_impl"
}
println (true.base_method)    // → "base_default"
println (true.sub_method)     // → "sub_impl"
```

### 10.5 关联类型

```typort
trait Container {
    type Item = Nat
    def get: Item
}

impl Container for Unit {
    def get: Nat = zero           // Item 使用默认 Nat
}

impl Container for Bool {
    type Item = Bool
    def get: Bool = true          // Item 覆盖为 Bool
}
```

### 10.6 Where 子句

```typort
trait Show { def show: String }
trait Get  { def get: String }

def test[T](x: T): String where T: Show + Get =
    _show_T.show x
```

---

## 11. 实现架构

### 11.1 核心模块

| 文件 | 职责 |
|------|------|
| `parser/mod.rs` | 解析 `trait`、`impl`、`where` 语法 |
| `parser/syntax.rs` | `Decl::TraitDecl`、`Decl::ImplDecl`、`Decl::Derive` 等 AST |
| `parser/derive.rs` | `#[derive(...)]` 宏展开 |
| `elaboration.rs` | Trait/Impl 语义 elaboration、`trait_wrap` 点号调用 |
| `typeclass.rs` | 实例搜索算法（`Synth`）核心数据结构与引擎 |
| `unification.rs` | `solve_trait` / `solve_multi_trait` 运行时解析 |
| `mod.rs` | `fresh_meta` 中 trait 元变量的延迟创建 |

### 11.2 解析流程

```
源码 → 词法分析 → 语法分析 → #[derive] 展开
  → Decl 列表
  → 对每个 Decl:
      TraitDecl → 注册到 trait_solver
      ImplDecl  → 注册实例 + 展开方法
      Def       → 类型检查 + 隐式填充 + trait 解析
```

### 11.3 搜索算法

- **GeneratorNode**：目标 + 候选列表 + 当前索引（回溯点）
- **ConsumerNode**：目标 + 剩余子目标（依赖链）
- **Waiter/TableEntry**：子目标间的依赖表

搜索从 `solve_trait(Assertion)` 进入，返回找到的实例的 `lvl`（decl 表中的键名）。

---

## 12. 语法速查表 (BNF)

```
┌─────────────────────────────────────────────────────────┐
│                     Typort Typeclass BNF                │
├─────────────────────────────────────────────────────────┤
│                                                        │
│ Decl        ::= Def | TraitDecl | ImplDecl | Enum       │
│              | Struct | Package | Import | Derive       │
│                                                        │
│ TraitDecl   ::= "trait" Ident                           │
│                 [":" SupertraitList]                    │
│                 ImplicitParams                          │
│                 "{" TraitBody "}"                       │
│                                                        │
│ SupertraitList ::= Ident ("+" Ident)*                   │
│                                                        │
│ TraitBody   ::= TraitItem (newline TraitItem)*          │
│ TraitItem   ::= "type" Ident ["=" Raw]                  │
│              | "def" (Ident | Op) Params ":" Raw        │
│                         ["=" Raw]                       │
│                                                        │
│ ImplDecl    ::= "impl" ImplicitParams                   │
│                 (TraitImpl | InherentImpl)              │
│                                                        │
│ TraitImpl   ::= Ident "[" Raw ("," Raw)* "]"           │
│                 "for" Raw "{" ImplBody "}"              │
│                                                        │
│ InherentImpl ::= Raw "{" ImplBody "}"                   │
│                                                        │
│ ImplBody    ::= ImplItem (newline ImplItem)*            │
│ ImplItem    ::= "type" Ident "=" Raw                    │
│              | ["static"] "def" (Ident | Op)            │
│                         Params ":" Raw "=" Raw          │
│                                                        │
│ Def         ::= "def" (Ident | Op)                     │
│                 ImplicitParams ExplicitParams           │
│                 [":" Raw]                               │
│                 ["where" WhereClause]                   │
│                 "=" Raw                                 │
│                                                        │
│ WhereClause ::= Ident ":" Ident ("+" Ident)*            │
│                 ("," Ident ":" ...)*                    │
│                                                        │
│ ImplicitParams ::= "[" Param ("," Param)* "]"*          │
│ ExplicitParams ::= "(" Param ("," Param)* ")"*          │
│ Param       ::= Ident ":" Raw                           │
│                                                        │
│ Annotation  ::= "#[derive(" Ident ("," Ident)* ")]"    │
│                                                        │
└─────────────────────────────────────────────────────────┘
```

---

> **文档维护者**: L13 开发团队  
> **最后更新**: 2026-07-10  
> **配套代码**: `src/L13_namespace/`
