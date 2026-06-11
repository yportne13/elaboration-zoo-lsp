# Typort (L13) Trait System — 与 Rust Trait 系统的全面对比

> 本文档系统性列举 Rust trait 系统的所有特性点，并与 Typort (L13) 语言的 trait 系统逐一对比。
> Typort 的 trait 系统是基于 Haskell typeclass 风格的设计，通过编译为枚举 + tabled resolution 引擎实现。

---

## 目录

1. [Trait 声明与定义](#1-trait-声明与定义)
2. [Trait 成员](#2-trait-成员)
3. [Trait 约束与 Where 子句](#3-trait-约束与-where-子句)
4. [Supertrait 与 Subtrait](#4-supertrait-与-subtrait)
5. [Trait 实现](#5-trait-实现)
6. [Coherence、孤儿规则与重叠](#6-coherence孤儿规则与重叠)
7. [Blanket 与条件实现](#7-blanket-与条件实现)
8. [分发：静态 vs 动态](#8-分发静态-vs-动态)
9. [Trait 对象 (dyn Trait)](#9-trait-对象-dyn-trait)
10. [对象安全规则](#10-对象安全规则)
11. [impl Trait（不透明/存在类型）](#11-impl-trait不透明存在类型)
12. [默认实现与特化](#12-默认实现与特化)
13. [Auto Trait 与 Marker Trait](#13-auto-trait-与-marker-trait)
14. [Unsafe Trait 与 Unsafe Impl](#14-unsafe-trait-与-unsafe-impl)
15. [Const Trait 与 ~const 约束](#15-const-trait-与-const-约束)
16. [Async Trait](#16-async-trait)
17. [Negative Trait 约束](#17-negative-trait-约束)
18. [高阶类型与泛型 Trait 特性](#18-高阶类型与泛型-trait-特性)
19. [Trait 别名](#19-trait-别名)
20. [Derive 宏](#20-derive-宏)
21. [方法解析与完全限定语法](#21-方法解析与完全限定语法)
22. [通过 Trait 的强制与转换](#22-通过-trait-的强制与转换)
23. [运算符 Trait](#23-运算符-trait)
24. [闭包相关 Trait](#24-闭包相关-trait)
25. [生命周期相关 Trait](#25-生命周期相关-trait)
26. [编译器内部特殊 Trait](#26-编译器内部特殊-trait)
27. [诊断与编译器属性](#27-诊断与编译器属性)
28. [不稳定/仅在 Nightly 可用的特性](#28-不稳定仅在-nightly-可用的特性)
29. [基于 Trait 的标准库模式](#29-基于-trait-的标准库模式)
30. [关联项上的约束](#30-关联项上的约束)
31. [Trait 解析与类型推断](#31-trait-解析与类型推断)

---

## 1. Trait 声明与定义

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 1.1 | 基本 trait 声明 | `trait Trait { fn method(&self); }` | ✅ `trait Trait { def method(...): Ret }` | 核心语法一致 |
| 1.2 | 带生命周期参数的 trait | `trait Foo<'a> { fn bar(&self, x: &'a str); }` | ❌ | Typort 无生命周期系统 |
| 1.3 | 带泛型类型参数的 trait | `trait Converter<T> { fn convert(&self) -> T; }` | ✅ `trait Convert[T, O] { def convert: O }` | 通过隐式参数实现 |
| 1.4 | 带泛型 const 参数的 trait | `trait Foo<const N: usize> { fn bar() -> [u8; N]; }` | ❌ | Typort 无比啦值泛型参数（与 Rust 相同方式） |
| 1.5 | 带默认泛型参数的 trait | `trait Add<Rhs = Self> { type Output; }` | ❌ | 无默认值语法 |
| 1.6 | Where 子句在 trait 定义上 | `trait Foo<T> where T: Debug { fn bar(&self, t: T); }` | ❌ | 无 where 子句语法 |
| 1.7 | 可见性修饰符 | `pub trait PublicTrait {}` | ❌ | Typort 无可见性系统（所有声明在包内可见） |
| 1.8 | Trait 属性 | `#[must_use] trait MyTrait {}` | ❌ | 无属性系统 |
| 1.9 | 密封 trait 模式 | 通过私有 supertrait | ❌ | 无私有项概念 |
| 1.10 | outParam 标记 | 不适用 | ✅ `outParam(Type 0)` | Typort 特有：标记输出类型参数 |

---

## 2. Trait 成员

### 2.1 方法

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 2.1.1 | 实例方法 (&self) | `fn method(&self);` | ✅ `def method(arg: ...): Ret` | Typort 统一用显式参数，第一个 `this` 参数由 trait 自动生成 |
| 2.1.2 | 可变实例方法 (&mut self) | `fn method(&mut self);` | ❌ | Typort 无可变引用概念 |
| 2.1.3 | 所有权方法 (self) | `fn method(self);` | ✅ | 通过 `this` 参数 |
| 2.1.4 | Pin 方法 | `self: Pin<&mut Self>` | ❌ | 无 Pin 概念 |
| 2.1.5 | 任意 Self 类型 | `self: Rc<Self>` | ❌ | 无 Deref 或任意 self 支持 |
| 2.1.6 | 静态方法 / 关联函数 | `fn new() -> Self;` | ✅ | 无 `this` 参数的方法 |
| 2.1.7 | 带泛型参数的方法 | `fn method<T: Debug>(&self, val: T);` | ✅ | Typort 方法可以带额外参数 |
| 2.1.8 | 带生命周期参数的方法 | `fn method<'a>(&self, x: &'a str) -> &'a str;` | ❌ | 无生命周期 |
| 2.1.9 | Self: Sized 约束 | `fn method(self) where Self: Sized;` | ❌ | 无 `Sized` 概念 |
| 2.1.10 | RPIT in Trait (RPITIT) | `fn method(&self) -> impl Iterator;` | ❌ | 无 `impl Trait` 语法 |
| 2.1.11 | 异步方法 | `async fn method(&self) -> Result<()>;` | ❌ | 无 async 支持 |
| 2.1.12 | const fn 在 trait 中 | `const fn method() -> u32;` | ❌ | 无 const eval 系统 |
| 2.1.13 | 默认方法实现 | `fn method(&self) { println!("default"); }` | ❌ | 方法必须提供定义（在 impl 中） |
| 2.1.14 | default 覆盖标记 | `default fn method(&self) {}` | ❌ | 无特化支持 |

### 2.2 关联类型

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 2.2.1 | 关联类型声明 | `type Item;` | ❌ | 无关联类型语法 |
| 2.2.2 | 带约束的关联类型 | `type Item: Debug + Clone;` | ❌ | — |
| 2.2.3 | 带默认值的关联类型 | `type Item = u32;` | ❌ | — |
| 2.2.4 | GAT（泛型关联类型） | `type Iter<'a>: Iterator<...>;` | ❌ | — |
| 2.2.5 | GAT 带 where | `type Map<F>: Iterator where F: ...` | ❌ | — |
| 2.2.6 | 生命周期 GAT | `type Ref<'a>: AsRef<Self::Item>;` | ❌ | — |
| 2.2.7 | Const GAT | `type Array<const N: usize>;` | ❌ | — |
| 2.2.8 | impl Trait 在关联类型位置 | `type Foo = impl Trait;` | ❌ | — |
| 2.2.9 | 投影语法 | `<T as Iterator>::Item` | ❌ | — |
| 2.2.10 | 短投影语法 | `T::Item` | ❌ | — |

### 2.3 关联常量

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 2.3.1 | 关联常量声明 | `const ID: u32;` | ❌ | 无关联常量语法 |
| 2.3.2 | 带默认值的关联常量 | `const ID: u32 = 0;` | ❌ | — |
| 2.3.3 | 复杂类型关联常量 | `const NAME: &'static str;` | ❌ | — |
| 2.3.4 | 关联常量约束（不稳定） | `const CAPACITY: usize;` | ❌ | — |

---

## 3. Trait 约束与 Where 子句

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 3.1 | 行内泛型约束 | `fn foo<T: Display>(t: T)` | ✅ | 通过隐式参数：`def foo[T][d: Display[T]](x: T): String` |
| 3.2 | Where 子句约束 | `fn foo<T>(t: T) where T: Display` | ❌ | — |
| 3.3 | 多 trait 约束 (+) | `fn foo<T: Clone + Debug>(t: T)` | ❌ | 可通过多隐式参数模拟 |
| 3.4 | 生命周期约束 | `fn foo<'a, T: 'a>(t: T)` | ❌ | — |
| 3.5 | T: 'static 约束 | `fn foo<T: 'static>(t: T)` | ❌ | — |
| 3.6 | 'a: 'b 约束 | `fn foo<'a, 'b>(x: &'a str) where 'a: 'b` | ❌ | — |
| 3.7 | HRTB | `fn foo<F: for<'a> Fn(&'a str)>(f: F)` | ❌ | — |
| 3.8 | HRTB on where | `where F: for<'a> Fn(&'a [u8])` | ❌ | — |
| 3.9 | HRTB on trait 定义 | `trait Foo: for<'a> Bar<'a> {}` | ❌ | — |
| 3.10 | 关联类型等号约束 | `fn foo<T: Iterator<Item = u32>>(t: T)` | ❌ | — |
| 3.11 | 关联类型约束 (ATB) | `fn foo<T: Iterator<Item: Debug>>(t: T)` | ❌ | — |
| 3.12 | 投影约束 | `where <T as Iterator>::Item: Debug` | ❌ | — |
| 3.13 | GAT 嵌套投影约束 | — | ❌ | — |
| 3.14 | ?Sized 约束放松 | `fn foo<T: ?Sized>(t: &T)` | ❌ | — |
| 3.15 | ~const 约束 | `fn foo<T: ~const MyTrait>(t: T)` | ❌ | — |
| 3.16 | ?const 放松 | `fn foo<T: ?const MyTrait>(t: T)` | ❌ | — |
| 3.17 | 结构体上的 where | `struct Foo<T: Debug> { inner: T }` | ❌ | — |
| 3.18 | impl 上的 where | `impl<T: Clone> Clone for MyType<T>` | ❌ | 通过隐式参数模拟 |
| 3.19 | 关联类型上的 where | `type Item where Self: 'static;` | ❌ | — |
| 3.20 | const 参数上的约束 | `fn foo<const N: usize>() where [(); N]: Sized` | ❌ | — |
| 3.21 | Self 上的 trait 约束 | `fn method(&self) where Self: Clone` | ❌ | — |

---

## 4. Supertrait 与 Subtrait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 4.1 | 简单 supertrait | `trait Subtrait: Supertrait {}` | ❌ | 无继承语法 |
| 4.2 | 多 supertrait | `trait A: B + C {}` | ❌ | — |
| 4.3 | 生命周期 supertrait | `trait A: 'a {}` | ❌ | — |
| 4.4 | 泛型 supertrait | `trait A: SuperTrait<T> {}` | ❌ | — |
| 4.5 | HRTB supertrait | `trait A: for<'a> Bar<'a> {}` | ❌ | — |
| 4.6 | where 子句 supertrait | `trait A where Self: B {}` | ❌ | — |
| 4.7 | 传递性 supertrait | 自动满足 | ❌ | — |
| 4.8 | Trait 对象向上转型 | `&dyn Subtrait -> &dyn Supertrait` | ❌ | — |
| 4.9 | trait_upcasting 特性 | `#![feature(trait_upcasting)]` | ❌ | — |
| 4.10 | Supertrait 范围 | supertrait 方法自动在 subtrait 范围内 | ❌ | — |

---

## 5. Trait 实现

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 5.1 | 基本 impl | `impl Trait for Type {}` | ✅ `impl Trait for Type { ... }` | 核心语法一致 |
| 5.2 | 泛型 impl | `impl<T: Clone> Clone for Vec<T> {}` | ✅ `impl[T] Clone for Vec[T] { ... }` | 同样支持 |
| 5.3 | 条件 impl (where) | `impl<T> Foo for Bar<T> where T: Debug {}` | ❌ | — |
| 5.4 | 为引用实现 | `impl<T: Clone> Clone for &T {}` | ❌ | 无引用类型作为实现目标 |
| 5.5 | 为原始指针实现 | `impl<T> MyTrait for *const T {}` | ❌ | 无指针类型 |
| 5.6 | 为 trait 对象实现 | `impl MyTrait for dyn OtherTrait {}` | ❌ | 无 trait 对象 |
| 5.7 | 为 dyn Trait + Send 实现 | — | ❌ | — |
| 5.8 | 为 unsized 类型实现 | `impl<T> Foo for [T] {}` | ❌ | — |
| 5.9 | 为 dyn* Trait 实现 | — | ❌ | — |
| 5.10 | unsafe impl | `unsafe impl Send for MyType {}` | ❌ | — |
| 5.11 | default 实现项（特化） | `default fn method(...) {}` | ❌ | — |
| 5.12 | 为外部类型实现 | — | ❌ | — |
| 5.13 | 关联类型赋值 | `type Item = u32;` | ❌ | — |
| 5.14 | 关联常量赋值 | `const ID: u32 = 42;` | ❌ | — |
| 5.15 | 为 ! 类型实现 | `impl MyTrait for ! {}` | ❌ | — |
| 5.16 | 固有 impl | `impl Type { ... }` | ✅ `impl Type { ... }` | 同样支持 |

---

## 6. Coherence、孤儿规则与重叠

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 6.1 | 孤儿规则 | impl 必须在同一 crate 定义 trait 或类型 | ⚠️ 部分 | Typort 无跨文件 coherence 检查 |
| 6.2 | 重叠规则 | 两个 impl 不能同时适用于同一类型 | ❌ | Typort 允许重叠，求解器选第一个匹配的 |
| 6.3 | 负面推理 | 编译器使用缺少 impl 做 coherence 检查 | ❌ | — |
| 6.4 | 覆盖/未覆盖类型参数 | 孤儿规则细化 | ❌ | — |
| 6.5 | Fundamental 类型 | `#[fundamental]` 放松孤儿规则 | ❌ | — |
| 6.6 | #[fundamental] 属性 | — | ❌ | — |
| 6.7 | Blanket impl 重叠规则 | blanket impl 创建大量重叠 | ❌ | — |
| 6.8 | 负面 impl | `impl !Send for MyType {}` | ❌ | — |
| 6.9 | 条件 impl 重叠 | 通过更具体约束解决 | ❌ | — |
| 6.10 | 余归纳 trait 求解 | auto trait 余归纳 | ❌ | — |
| 6.11 | 归纳 trait 求解 | 正常 trait 归纳求解 | ✅ | Tabled resolution 本质上使用归纳搜索 |
| 6.12 | Chalk 风格求解 | 实验性新引擎 | ❌ | — |

---

## 7. Blanket 与条件实现

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 7.1 | Blanket impl (所有 T) | `impl<T: Debug> Debug for Rc<T> {}` | ✅ | `impl[T] Trait for Type[T] { ... }` |
| 7.2 | 通过 From 的 blanket | `impl<T,U> Into<U> for T where U: From<T>` | ❌ | — |
| 7.3 | 转发 blanket impl | 通过 supertrait | ❌ | — |
| 7.4 | 引用的 blanket impl | `impl<T: Clone> Clone for &T {}` | ❌ | — |
| 7.5 | 条件 impl via where | `impl<T: PartialEq> PartialEq for Option<T> {}` | ❌ | — |
| 7.6 | 递归 blanket impl | 可导致求解溢出 | ❌ | — |

---

## 8. 分发：静态 vs 动态

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 8.1 | 静态分发（单态化） | 每个具体类型生成独立代码 | ✅ | Typort 所有 trait 方法调用均通过单态化 |
| 8.2 | 动态分发（虚函数表） | 运行时通过 vtable 分发 | ❌ | 无 dyn Trait 概念 |
| 8.3 | dyn 关键字 | `let x: &dyn Display = &value;` | ❌ | — |
| 8.4 | Vtable 布局 | 编译器内部 | ❌ | — |
| 8.5 | DispatchFromDyn | nightly | ❌ | — |
| 8.6 | CoerceUnsized | nightly | ❌ | — |
| 8.7 | dyn* 胖指针 | nightly | ❌ | — |
| 8.8 | dyn* 方法解析 | — | ❌ | — |

---

## 9. Trait 对象 (dyn Trait)

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 9.1 | 基本 trait 对象 | `&dyn Trait` | ❌ | 不支持 trait 对象 |
| 9.2 | 多 trait 约束对象 | `&(dyn Trait1 + Trait2)` | ❌ | — |
| 9.3 | 带生命周期 | `&(dyn Trait + 'a)` | ❌ | — |
| 9.4 | 带 auto trait | `&(dyn Trait + Send + Sync)` | ❌ | — |
| 9.5 | 默认生命周期省略 | `Box<dyn Trait>` = `Box<dyn Trait + 'static>` | ❌ | — |
| 9.6 | 匿名生命周期 '_ | `Box<dyn Trait + '_>` | ❌ | — |
| 9.7 | 括号消除歧义 | `&(dyn Fn() -> u32)` | ❌ | — |
| 9.8 | Trait 对象强制转换 | 具体引用 → trait 对象 | ❌ | — |
| 9.9 | 对象安全要求 | 只有对象安全的 trait 可用 | ❌ | — |
| 9.10 | 指针到 trait 对象 | `*const dyn Trait` | ❌ | — |

---

## 10. 对象安全规则

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 所有对象安全规则 | — | ❌ | 不适用，因为 Typort 没有 trait 对象 |

---

## 11. impl Trait（不透明/存在类型）

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 11.1 | 参数位置 impl Trait | `fn foo(x: impl Display)` | ❌ | 无 `impl Trait` 语法 |
| 11.2 | 返回值位置 impl Trait | `fn foo() -> impl Display` | ❌ | — |
| 11.3 | 多 impl Trait 参数 | `fn foo(x: impl Debug, y: impl Display)` | ❌ | — |
| 11.4 | impl Trait 带 + | `fn foo() -> impl Clone + Debug` | ❌ | — |
| 11.5 | impl Trait + 生命周期 | `fn foo() -> impl Debug + 'static` | ❌ | — |
| 11.6 | RPITIT | `trait Foo { fn bar() -> impl Debug; }` | ❌ | — |
| 11.7 | TAIT | `type MyType = impl Trait;` | ❌ | — |
| 11.8 | 关联类型中的 impl Trait | `type Foo = impl Trait;` | ❌ | — |
| 11.9 | const/static 中的 impl Trait | — | ❌ | — |
| 11.10 | 捕获 vs 非捕获 | RPIT 默认捕获生命周期 | ❌ | — |
| 11.11 | impl use<...> Trait | nightly 精确捕获 | ❌ | — |
| 11.12 | 不透明类型隐藏 | 隐藏具体类型 | ❌ | — |
| 11.13 | 不透明类型相等性 | 同一个函数的两个返回类型相同 | ❌ | — |

---

## 12. 默认实现与特化

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 12.1 | 默认方法体 | ✅ | ❌ | 必须在 impl 中完整实现 |
| 12.2 | 默认关联类型值 | ✅ | ❌ | — |
| 12.3 | 默认关联常量值 | ✅ | ❌ | — |
| 12.4 | default 关键字在 impl 中 | nightly | ❌ | — |
| 12.5 | 特化特性门控 | nightly | ❌ | — |
| 12.6 | min_specialization | nightly | ❌ | — |
| 12.7 | 默认 impl | 无更具体 impl 时使用 | ❌ | — |
| 12.8 | 固有方法 vs trait 方法覆盖 | 固有方法覆盖 trait 方法 | ✅ | Typort 通过命名空间优先级处理 |

---

## 13. Auto Trait 与 Marker Trait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 13.1 | Send auto trait | 自动安全线程间发送 | ❌ | 无并发模型 |
| 13.2 | Sync auto trait | 自动安全线程间共享 | ❌ | — |
| 13.3 | Unpin auto trait | 可安全移动 | ❌ | — |
| 13.4 | Freeze（编译器内部） | 无非安全单元 | ❌ | — |
| 13.5 | Sized marker trait | 编译时已知大小 | ❌ | — |
| 13.6 | Copy marker trait | 位拷贝 | ❌ | — |
| 13.7 | Clone marker-trait | 显式克隆 | ❌ | Typort 的 Clone 是普通 trait |
| 13.8 | Eq | 全等性 | ❌ | — |
| 13.9 | Default | 默认值 | ❌ | Typort 的 Default 是普通 trait |
| 13.10 | Auto trait 推导规则 | 所有字段满足则自动实现 | ❌ | — |
| 13.11 | 自定义 auto trait | nightly auto trait | ❌ | — |
| 13.12 | Auto trait 退出 | nightly impl !AutoTrait | ❌ | — |
| 13.13 | PhantomPinned | Phantom 类型 | ❌ | — |
| 13.14 | PhantomData<T> | 标记型变/drop check | ❌ | — |

---

## 14. Unsafe Trait 与 Unsafe Impl

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | Typort 无 unsafe 概念 |

---

## 15. Const Trait 与 ~const 约束

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | Typort 无比时计算/const 泛型系统 |

---

## 16. Async Trait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | Typort 无异步支持 |

---

## 17. Negative Trait 约束

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 17.1 | negative impl | nightly | ❌ | — |
| 17.2 | auto trait 退出 | nightly | ❌ | — |
| 17.3 | 负面约束语法 T: !Trait | 不可用 | ❌ | — |
| 17.4 | 负面推理在 coherence | 内部使用 | ❌ | — |

---

## 18. 高阶类型与泛型 Trait 特性

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 18.1 | GAT | `type Item<'a>;` | ❌ | — |
| 18.2 | 带生命周期约束的 GAT | `type Iter<'a>: Iterator where Self: 'a;` | ❌ | — |
| 18.3 | 带类型参数的 GAT | `type Output<T>;` | ❌ | — |
| 18.4 | 带 const 参数的 GAT | `type Array<const N: usize>;` | ❌ | — |
| 18.5 | GAT 上的 HRTB | — | ❌ | — |
| 18.6 | Lending Iterator 模式 | 通过 GAT 实现 | ❌ | — |

---

## 19. Trait 别名

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | 无 trait 别名语法 |

---

## 20. Derive 宏

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 20.1 | #[derive(Trait)] | `#[derive(Debug, Clone, PartialEq)]` | ✅ `derive Show for Type` | Typort 有简单的 derive 语法 |
| 20.2 | 自定义 derive 宏 | 用户定义 proc macro | ✅ | 通过 Rust 端的 `DeriveMacro` 注册 |
| 20.3 | Derive 辅助属性 | `#[my_trait_helper(attribute)]` | ❌ | — |
| 20.4 | 带泛型的 derive | `#[derive(Clone)] struct Foo<T>(T);` | ✅ | 生成 impl[T] ... |
| 20.5 | 条件 derive (auto_impl) | 库提供条件 derive | ❌ | — |
| 20.6 | 智能指针的 derive | 通过 Deref 工作 | ❌ | — |

内置 derive 宏：`Show`, `Bundle`（HDL 专用）

---

## 21. 方法解析与完全限定语法

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 21.1 | 自动引用方法调用 | 自动加 &/&mut/* | ❌ | 无引用语义 |
| 21.2 | Deref 链解析 | 沿 Deref 链查找方法 | ❌ | — |
| 21.3 | 方法优先级（固有 > trait） | 固有方法覆盖 trait | ✅ | `ns_result` 优先于 trait 方法查找 |
| 21.4 | 方法优先级（更具体 trait） | 更具体 trait 优先 | ❌ | 同方法名时仍可能报错 |
| 21.5 | 完全限定语法 | `<Type as Trait>::method(...)` | ❌ | — |
| 21.6 | Trait 项路径 | `Trait::Item` | ❌ | — |
| 21.7 | 短投影 | `T::Item` | ❌ | — |
| 21.8 | Turbofish (::<>) | `foo::<u32>(x)` | ❌ | 通过 `[arg]` 隐式参数语法 |
| 21.9 | Trait 在范围内要求 | 必须 use Trait 才能调用方法 | ❌ | Trait 方法始终可用（通过 `trait_wrap`） |
| 21.10 | 匿名 trait 导入 | `use Trait as _;` | ❌ | — |
| 21.11 | 歧义解析 | 多 trait 同名方法需限定 | ❌ | 当前实现取第一个匹配 |
| 21.12 | 自动解引用 | `x.method()` 自动解引用 | ❌ | — |

---

## 22. 通过 Trait 的强制与转换

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 22.1 | Unsized 强制转换到 dyn Trait | `T -> &dyn Trait` | ❌ | — |
| 22.2 | [T; N] -> [T] 强制 | — | ❌ | — |
| 22.3 | Trait 对象向上转型 | dyn Subtrait -> dyn Supertrait | ❌ | — |
| 22.4 | Deref 强制 | `&T -> &U` where T: Deref<Target=U> | ❌ | — |
| 22.5 | From/Into 转换 | `let s: String = "hello".into();` | ⚠️ 部分 | Into trait 已定义（`impl[T] Into[T] for T`） |
| 22.6 | TryFrom/TryInto 回退转换 | — | ❌ | — |
| 22.7 | AsRef/AsMut | — | ❌ | — |
| 22.8 | Borrow/BorrowMut | — | ❌ | — |
| 22.9 | ToOwned | — | ❌ | — |
| 22.10 | 强制转换点 | let、match、函数参数等 | ❌ | 无隐式强制转换 |

---

## 23. 运算符 Trait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 23.1 | Add, Sub, Mul, Div, Rem | ✅ | ✅ | 均通过 trait 定义 |
| 23.2 | Neg, Not | ✅ | ✅ | — |
| 23.3 | BitAnd, BitOr, BitXor, Shl, Shr | ✅ | ✅ | And, Or, Xor 已定义 |
| 23.4 | AddAssign 等复合赋值 | ✅ | ❌ | 无可变引用，无复合赋值 |
| 23.5 | Index, IndexMut | ✅ | ❌ | 无 Index/IndexMut |
| 23.6 | Deref, DerefMut | ✅ | ❌ | — |
| 23.7 | Drop | ✅ | ❌ | — |
| 23.8 | Fn, FnMut, FnOnce | ✅ | ❌ | — |

Typort 的运算符重载是通过同名 trait 方法实现的，语法糖让 `a + b` 自动解析为 `a.+(b)`。

---

## 24. 闭包相关 Trait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | 闭包在 Typort 中是普通 lambda，不涉及 trait |

---

## 25. 生命周期相关 Trait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | Typort 无生命周期系统 |

---

## 26. 编译器内部特殊 Trait

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 26.1 | Sized | 所有类型参数默认约束 | ❌ | — |
| 26.2 | ?Sized | 退出默认约束 | ❌ | — |
| 26.3 | Drop | 析构器 | ❌ | — |
| 26.4 | CoerceUnsized | nightly | ❌ | — |
| 26.5 | DispatchFromDyn | nightly | ❌ | — |
| 26.6 | Unsize | 编译器内部 | ❌ | — |
| 26.7 | Receiver | nightly | ❌ | — |
| 26.8 | Termination | main 返回类型 | ❌ | — |
| 26.9 | Pointer | 指针格式化 | ❌ | — |
| 26.10 | Any | 类型擦除动态类型 | ❌ | — |

---

## 27. 诊断与编译器属性

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | Typort 无属性系统 |

---

## 28. 不稳定/仅在 Nightly 可用的特性

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 nightly 特性 | — | ❌ | Typort 无对应概念 |

---

## 29. 基于 Trait 的标准库模式

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 29.1 | IntoIterator | 可转成迭代器 | ❌ | — |
| 29.2 | FromIterator | 从迭代器构建 | ❌ | — |
| 29.3 | Borrow/BorrowMut | map 查找等价 | ❌ | — |
| 29.4 | AsRef/AsMut | 廉价引用转换 | ❌ | — |
| 29.5 | ToOwned | 借用→所有权 | ❌ | — |
| 29.6 | Cow | 写时克隆 | ❌ | — |
| 29.7 | Deref Target | 智能指针 | ❌ | — |
| 29.8 | Error Chain | 错误链 | ❌ | — |
| 29.9 | Sealed Supertrait | 私有 supertrait | ❌ | — |
| 29.10 | Extension Trait | 外部类型添加方法 | ✅ | `trait_wrap` 机制允许对任意类型调用 trait 方法 |
| 29.11 | Newtype 模式 | 包装外部类型实现 trait | ✅ | 通过 `impl Trait for MyNewType { ... }` |

---

## 30. 关联项上的约束

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 全部 | — | ❌ | 无关联类型系统 |

---

## 31. Trait 解析与类型推断

| # | 特性 | Rust | Typort (L13) | 说明 |
|---|------|------|---------------|------|
| 31.1 | 通过模式匹配的 trait 求解 | 匹配 Self 类型 | ✅ | `val_match` 做结构匹配 |
| 31.2 | 余归纳 trait 循环 | auto trait 允循环 | ❌ | — |
| 31.3 | 溢出保护 | 递归深度限制 | ⚠️ 部分 | 1000 次循环硬限制 |
| 31.4 | 关联类型推断 | 从 impl 使用推断 | ❌ | — |
| 31.5 | 多变量类型推断 | 多个类型参数推断 | ❌ | — |
| 31.6 | 隐含约束 | supertrait 自动满足 | ❌ | — |
| 31.7 | Tabled resolution | — | ✅ | Typort 的类型类求解器使用 tabled resolution 算法 |
| 31.8 | Head-indexed 查找 | — | ✅ | O(1) 实例查找优化 |
| 31.9 | outParam 推理 | — | ✅ | 输出参数由求解器推理 |

---

## 总结

| 类别 | Rust 特性数 | Typort (L13) ✅ | Typort (L13) ⚠️ 部分 | Typort (L13) ❌ |
|------|------------|----------------|----------------------|-----------------|
| Trait 声明与定义 | 10 | 3 | 0 | 7 |
| Trait 成员（方法） | 14 | 3 | 0 | 11 |
| 关联类型 | 10 | 0 | 0 | 10 |
| 关联常量 | 4 | 0 | 0 | 4 |
| Trait 约束与 Where 子句 | 21 | 1 | 0 | 20 |
| Supertrait | 10 | 0 | 0 | 10 |
| Trait 实现 | 16 | 3 | 0 | 13 |
| Coherence/孤儿规则 | 12 | 0 | 1 | 11 |
| Blanket 与条件实现 | 6 | 1 | 0 | 5 |
| 分发 | 8 | 1 | 0 | 7 |
| Trait 对象 | 12 | 0 | 0 | 12 |
| 对象安全 | 11 | 0 | 0 | 11 |
| impl Trait | 13 | 0 | 0 | 13 |
| 默认实现与特化 | 8 | 0 | 0 | 8 |
| Auto/Marker Trait | 14 | 0 | 0 | 14 |
| Unsafe Trait | 4 | 0 | 0 | 4 |
| Const Trait | 6 | 0 | 0 | 6 |
| Async Trait | 6 | 0 | 0 | 6 |
| Negative Trait | 4 | 0 | 0 | 4 |
| 高阶类型/GAT | 6 | 0 | 0 | 6 |
| Trait 别名 | 4 | 0 | 0 | 4 |
| Derive 宏 | 6 | 2 | 0 | 4 |
| 方法解析 | 12 | 2 | 1 | 9 |
| 强制与转换 | 10 | 0 | 1 | 9 |
| 运算符 Trait | 8 | 5 | 0 | 3 |
| 闭包相关 | 5 | 0 | 0 | 5 |
| 生命周期相关 | 8 | 0 | 0 | 8 |
| 编译器内部 Trait | 10 | 0 | 0 | 10 |
| 诊断与属性 | 7 | 0 | 0 | 7 |
| 标准库模式 | 11 | 2 | 0 | 9 |
| 关联项约束 | 7 | 0 | 0 | 7 |
| Trait 解析与推断 | 7 | 4 | 1 | 2 |
| **总计** | **~310** | **~27** | **~4** | **~279** |

### Typort (L13) 已实现的核心 trait 特性

1. 基本 trait 声明 + 泛型参数
2. 基本 trait 实现 + 泛型 impl
3. 固有 impl（方法扩展）
4. 隐式参数 trait 约束（`def foo[T][d: Show[T]](x: T): String`）
5. 方法解析（`expr.method` 自动查找 trait 方法）
6. Derive 宏（Show, Bundle）
7. Blanket impl（`impl[T] Into[T] for T`）
8. 运算符重载（Add, Sub, Mul, Div, Rem, And, Or, Xor, Not, Neg 等）
9. outParam 机制（用于输出类型参数推断）
10. Tabled typeclass resolution（高效的 trait 求解器）
11. Head-indexed 实例查找（O(1) 复杂度）

### Typort (L13) 相比 Rust 缺少的关键特性

1. **关联类型** — trait 内不能定义类型占位符
2. **Supertrait/继承** — trait 之间无继承关系
3. **Where 子句** — 无条件约束语法
4. **默认方法实现** — trait 不能提供默认方法体
5. **动态分发** — 无 trait 对象 / dyn Trait
6. **生命周期** — 整个语言无生命周期概念
7. **Coherence/孤儿规则** — 无跨模块的 impl 冲突检查
8. **关联常量** — trait 内不能定义常量
9. **Auto trait** — 无自动推导的 trait
10. **Unsafe** — 无不安全代码概念

### 实测发现的已知问题 / Bug

以下 Bug 是在编写 comprehensive test 过程中发现的，当前版本 (L13) 存在这些问题：

| # | 问题 | 影响 | 根因 |
|---|------|------|------|
| 1 | **零参数 trait 方法通过点号调用失败** `expr.method` (方法无除了 this 之外的参数) 会留下未解析的 `$$` (trait 实例) 隐式参数，导致结果类型为函数而不是期望的类型 | `true.show`, `two.double`（通过 trait）等方法调用失效 | `trait_wrap` 中参数顺序为 `[Self](Impl), [$this](Expl), [$$](Impl)`，`insert_go` 只能插入开头的隐式参数，遇到 `$this`(Expl) 后停止，导致 `$$` 未能解析 |
| 2 | **运算符作为方法名时无法通过点号访问** `o.< x y` 会解析失败，因为 `<` 是运算符 token | 包含 `<`, `>`, `!` 等方法名的 trait 字段访问失败 | 解析器将 `<` 视为运算符而非标识符 |
| 3 | **Trait 构造器字段访问在 Rigid 类型参数下失效** `i.method x` (其中 `i: TraitName[T]`, `T` 是 Rigid 变量) 会字段查找失败 | 通过泛型函数参数 trait instance 调用方法不可用 | `c` 中的字段名 `Span` 比较包含位置信息，与调用处的 `Span` 不匹配 |
| 4 | **`.mk` 构造器的 span 比较** 字段名使用 `Span` 的全量比较（包含位置），导致相同名称但不同来源的字段无法匹配 | Sum 类型的字段访问依赖于位置匹配 | `Span` 的 `PartialEq` 比较了 `start_offset`, `end_offset`, `path_id` 等字段 |

### Verified Working Features

经过 comprehensive test 验证，以下功能在 `run` 模式下正常工作：

| 功能 | 示例 | 状态 |
|------|------|------|
| 运算符重载 | `a + b`, `a * b`, `a - b`, `!a` | ✅ |
| 固有 impl (方法扩展) | `impl Nat { def double: Nat = this + this }` | ✅ |
| 泛型固有 impl | `impl[A, B] Pair[A, B] { def swap: ... }` | ✅ |
| 具体类型固有 impl | `impl List[Nat] { def sum: Nat = ... }` | ✅ |
| Struct 定义与字段访问 | `struct Pair[A, B] { fst: A; snd: B }` | ✅ |
| 递归固有方法 | `def sum: Nat = ... h + t.sum` | ✅ |
| Not 一元运算符 | `!true` | ✅ |
| 多层运算符表达式 | `(two + three) * four - two` | ✅ |
| `def` 值定义 | `def five = two + three` | ✅ |
| 函数定义与调用 | `def factorial(n: Nat): Nat = ...; factorial three` | ✅ |
