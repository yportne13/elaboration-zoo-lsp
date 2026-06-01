# HDL Design — 重构方案

> 本文档承载 HDL 重构的设计决策和最终方案，不记录讨论过程。

---

## 一、类型系统

### 基础类型

| 类型 | 语法 | 说明 |
|------|------|------|
| Bool | `Bool` | 单 bit 布尔值 |
| Bits | `Bits[width]` | 无语义位向量 |
| UInt | `UInt[width]` | 无符号整数 |
| SInt | `SInt[width]` | 有符号整数（补码） |
| Bundle | `Bundle { ... }` | 结构体 |
| Data | `Data` | 所有硬件类型的超类型 |

### 类型关系

**Bool / Bits / UInt / SInt 全部分立，无子类型**：
- 互相不可隐式转换，跨类型操作必须显式转换（`.asBits` 等）
- 方法设计保证返回正确类型（如 `msb` 返回 `Bool`）

### 宽度设计

- 宽度**编码在类型上**：`UInt[8]` 有别于 `UInt[16]`
- 整数/自然数字面量与 UInt 的宽度关系需要检查
- 参数化宽度：`UInt[n]` 其中 `n` 是编译期 Nat

### Trait 层次

按功能拆分独立 trait：

**Bitwise** — `&` `|` `^` `~` `<<` `>>`（Bits, UInt, SInt）
- `<<` / `>>` 只接受编译期 Nat 常量作为移位量
- 动态移位用 `switch` 实现

**Arithmetic** — `+` `-` `+^` `-^` `*`（UInt, SInt）
- `+` `-` 保持位宽，溢出截断；`+^` `-^` 结果宽度 +1
- `*`：`UInt[w1] * UInt[w2] → UInt[w1 + w2]`（不丢失精度）

**Comparison** — `===` `=/=` `<` `<=` `>` `>=`（结果恒为 `Bool`）
- 两侧位宽必须完全相等，否则类型错误

**Cast** — `asBits` `asUInt` `asSInt` `asBool` `resize` `cast`
- 已定义在 `hdl.typort` prelude 中

**BoolLike** — `&&` `||` `!`（仅 Bool）

### Vec

- 复用 prelude 已有的 `Vec` 类型
- `Vec(size, DataType)`：`Vec(4, UInt[8])`

### Bundle 与命名

- 具名 struct 用 Typort struct 定义，不指定方向
- 方向在 impl 中通过 `mst`/`slv`/`flip` 方法定义
- 匿名 Bundle 用 `Bundle { let a = ...; let b = ... }` 语法
- 简单信号用 `in()`/`out()` 函数包裹
- 方向元数据存储位置待定（Expr 级别 vs 类型级别）

### Bundle 字段方向

- 遵循 SpinalHDL：
  - `in(UInt[8]())` — 输入方向
  - `out(UInt[8]())` — 输出方向
  - `master(Bus())` / `slave(Bus())` — 接口方向翻转
  - 方向不写在类型上，写在声明上

---

## 二、控制流语句

### when

**语法待定**（两种方案记录中）：
- 方案 A：链式调用 `when(cond) { ... }.elsewhen(cond2) { ... }.otherwise { ... }`
- 方案 C：块风格 `when(cond) { ... } elsewhen cond2 { ... } otherwise { ... }`

`when` 是否作为表达式（最后一行作为返回值）——待定。

### switch

```typort
switch(x, {
    is(0) { body1 };
    is(1) { body2 };
    default { fallback }
})
```

- `switch` 是语句（不是表达式）
- `is` 和 `default` 是普通函数，不是关键字
- 支持 `for` 展开生成多个 `is` 分支
- 不强制穷举检查，`default` 建议提供

### 三目/条件运算符

```
val result = cond ? a | b
```

---

## 三、算术运算与类型安全

### 运算符

| 类别 | 运算符 |
|------|--------|
| 算术 | `+` `-` `*` `/` `%` |
| 位运算 | `&` `|` `^` `~` `<<` `>>` |
| 比较 | `===` `=/=` `<` `<=` `>` `>=` |
| 布尔 | `&&` `||` `!` |
| 拼接/切片 | 待定 |

### Nat 宽度检查

- `UInt[16] + Nat(1)` → 检查 `1` 是否 ≤ 16 bits 可表示
- 当左侧宽度是**参数**（编译期未知的 Nat）时，需要用户提供证明：

```rust
val result = x + 114.cast(prove)  // 用户通过 cast + proof 保证宽度合法
```

- `prove` 可以是直接给值，也可以是 `core::cmp::min` 之类的约束

---

## 四、组件/模块层次

### 模块定义

```
Component MyModule {
  val io = Bundle {
    val a = in(UInt[8]())
    val b = out(UInt[8]())
  }

  // combinational logic
  io.b := io.a + 1
}
```

### 实例化

```
val sub = MyModule()
sub.io.a := 5
```

---

## 四、时序逻辑（SpinalHDL 风格）

### 寄存器声明

```typort
val r = Reg(UInt[8]()).init(0)  // 寄存器，复位到 0（r: UInt[8]）
val r = RegNext(value)          // 延迟一拍
val r = RegNextWhen(value, cond) // 条件延迟
val r = Reg(UInt[8]())          // 寄存器，无复位初值
```

- `Reg(type)` 返回 `T` 本身（不是包装类型 `Reg[T]`），寄存器属性由内部机制维护
- `:=` 赋值时自动识别目标是否为寄存器，走 `regAssign` 路径

## 五、时钟与复位（SpinalHDL 风格）

### 隐式 ClockDomain

- 每个 Component 自带隐式 `ClockDomain(clock, reset)`
- 时钟上升沿 / 复位电平可配置
- 同步 / 异步复位都可选

### 多时钟域

```
val cd = ClockDomain(clock, reset)
val area = ClockArea(cd) {
  // 该时钟域下的逻辑
}
```

## 六、Area（SpinalHDL 概念）

Area 提供逻辑分组，但不产生额外层次：

```
val a = Area {
  val x = UInt[8]()
  val y = UInt[8]()
}
// 访问: a.x, a.y
```

## 七、已定设计决策

### 位宽推导

- 遵循 SpinalHDL：**`+` 保持位宽**，溢出静默截断；**`+^` 显式扩位**（结果宽度 +1）
- **`*`**：`UInt[w1] * UInt[w2] → UInt[w1 + w2]`（不丢失精度）

### 类型关系

- **Bool / Bits / UInt / SInt 全部分立，无子类型**
- 跨类型转换必须显式：`.asBits` `.asUInt` `.asSInt` `.asBool`

### 比较运算

- 结果恒为 `Bool`
- 两侧位宽必须完全相等，否则类型错误

### 移位运算

- `<<` / `>>` 只接受编译期 Nat 常量
- 动态移位用 `switch` 实现

### 生成目标

- 首期目标：**Verilog**
- 后续可扩展 SystemVerilog

### 编译期 for 展开

- 支持 `for i in start until end { ... }`，编译期完全展开
- 循环变量 `i` 是 Nat，供索引、位宽参数化使用
- 需要定义 `Range` 类型和 `Iterator` trait
- 循环体内允许声明硬件类型，自动加 `_<迭代索引>` 后缀命名（嵌套格式 `x_i_j`）
- 循环体内声明的信号在循环外部可通过 `<name>_<idx>` 访问
- 不支持 break/continue（展开后不存在）
- `for` 是泛型 over `Iterator` 的（不限于 `Range`）

### 三目运算符

- 使用 `cond.mux(a, b)` 方法（`Bool.mux`），已在 prelude 实现

### 赋值语义

- 遵循 SpinalHDL：`:=` 作为硬件连接/赋值运算符，`=` 保留为 Typort 的 binding（变量/immut 绑定）
- `:=` 的签名：`def :=(that: Into[Self]): Unit`（接受 `Into[Self]`，允许 Nat 等通过 `.into` 自动转换）
- `when` 块内的 `:=` 自动条件化（follow Spinal）
- 组合信号多重驱动（非 when 分支外）→ error
- 多个 when 分支对同一信号赋值 → 允许（分支互斥）
- 输出端口未赋值 → error
- 声明但未读取 → warning

### 寄存器

- `Reg(type)` 返回 `T` 本身（不是包装类型 `Reg[T]`）
- `Reg(type).init(val)` 指定复位值
- `RegNext(value)` / `RegNextWhen(value, cond)` 语法糖
- `:=` 自动识别寄存器目标，走 `regAssign`

### 模块定义

- 关键字：`module`（而非 `Component`）
- IO 声明：SpinalHDL 风格 `val io = Bundle { in val a: UInt[8](); out val b: UInt[8]() }`
- 参数化：和 `def` 一致，隐式 `[ ]` / 显式 `( )` 均可
- 实例化：函数式 `val adder = Adder[8]()`，不需要 `new`
- 不允许嵌套 module（用 Area 替代）

### 编译期 for 展开

- 支持 `for i in start until end { ... }`，编译期完全展开
- 循环变量 `i` 是 Nat，供索引、位宽参数化使用
- 不由 for 循环体、不支持 break/continue（展开后不存在）

### Bundle 字段方向

- 遵循 SpinalHDL：
  - `in(UInt[8]())` — 输入方向
  - `out(UInt[8]())` — 输出方向
  - `master(Bus())` / `slave(Bus())` — 接口方向翻转
  - 方向不写在类型上，写在声明上

### switch 语句

```
switch(x, {
    is(v1) { body };
    is(v2) { body };
    default { fallback }
})
```

- `switch` 是语句（非表达式）
- `is` / `default` 是普通函数
- 支持 `for` 展开生成多个 `is` 分支
- 不强制穷举检查，`default` 建议提供

---

## 底座：L13 现有架构总结

### 语言分层

项目通过 L01-L13 逐层搭建类型系统：

| 层 | 功能 |
|----|------|
| L01 | Eval — 值求值 |
| L02 | Type checking — 基础类型检查 |
| L03 | Holes/Meta — 元变量 |
| L04 | Implicit — 隐式参数 |
| L05 | Pruning — 剪枝 |
| L06 | String — 字符串字面量 |
| L07 | Sum types — 和类型 (enum) |
| L07a | Dependent pattern match |
| L08 | Product types — 积类型 (struct) |
| L09 | MLTT — Martin-Löf 类型论 |
| L10 | Typeclass — 类型类 |
| L11 | Macro — 语法宏 |
| L12 | Canonical — 规范表达式 |
| **L13** | **Namespace — 命名空间 + LSP** |

实际使用中 L13 是**主入口**，L12 作为 legacy 测试的独立入口，两者共享 prelude。

### 核心类型定义

#### Tm（语法项 `mod.rs:80`）

```rust
pub enum Tm {
    Var(Ix),              // de Bruijn index
    Decl(Span<SmolStr>),  // 顶层声明
    Obj(Rc<Tm>, Span<SmolStr>), // field access
    Lam(Span<SmolStr>, Icit, Rc<Tm>),
    App(Rc<Tm>, Rc<Tm>, Icit),
    AppPruning(Rc<Tm>, Pruning),
    U(u32),  Pi(..),  Let(..),
    Meta(MetaVar),
    LiteralType,  LiteralIntro(Span<String>),
    Prim(Rc<Val>, PrimFunc),
    Sum(..),  SumCase { .. },  Match(..),
    Call(SmolStr, List<(Rc<Tm>, Icit)>, Rc<Tm>), // 内联
}
```

- `Ty = Tm`，`VTy = Val`
- `Lvl(u32)` — de Bruijn 层级（外→内递增）
- `Ix(u32)` — de Bruijn 索引（内→外递增），`lvl2ix(l, x) = Ix(l.0 - x.0 - 1)`

#### Val（值 `mod.rs:226`）

```rust
pub enum Val {
    Flex(MetaVar, Spine),  Rigid(Lvl, Spine),
    Decl(Span<SmolStr>, Spine),
    Obj(Rc<Val>, Span<SmolStr>, Spine),
    Lam(Span<SmolStr>, Icit, Closure),
    Pi(Span<SmolStr>, Icit, Rc<VTy>, Closure),
    U(u32),  LiteralType,  LiteralIntro(Span<String>),
    Prim(Rc<Val>, PrimFunc),
    Sum(..),  SumCase { .. },
    Match(Rc<Val>, Env, Vec<(PatternDetail, Rc<Tm>)>),
    Call(SmolStr, List<(Rc<Val>, Icit)>, Rc<Val>),
}
```

- `Spine = List<(Rc<Val>, Icit)>` — 实参列表
- `Env = List<Rc<Val>>` — 求值环境
- `Closure(Env, Rc<Tm>)` — 闭包
- Sum 系列的 params/cases 用 `Rc<Vec<..>>` 避免深拷贝

#### Cxt（上下文 `cxt.rs:51`）

```rust
pub struct Cxt {
    pub env: Env,                             // 求值环境
    pub lvl: Lvl,                             // 当前层级
    pub locals: Locals,                       // 局部变量链（hover 用）
    pub pruning: Pruning,                     // 剪枝
    pub src_names: BiMap<SmolStr, Lvl, (Span<()>, Rc<VTy>)>, // 名称↔Lvl 映射
    pub decl: Rc<HashMap<SmolStr, (Span, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>>, // 全局 decl
    pub namespace: List<(Rc<Val>, HashSet<SmolStr>, Raw)>, // 命名空间栈
    pub namespace_prefix: Option<SmolStr>,
    pub namespaces: HashSet<SmolStr>,
    update_from: Option<usize>,
}
```

| 字段 | 作用域 | 用途 |
|------|--------|------|
| `env` | eval/quote | 求值环境 |
| `lvl` | unify/quote | 层级追踪 |
| `locals` | hover/pretty | 名字打印 |
| `pruning` | unify | 剪枝算法 |
| `src_names` | infer/elab | 变量查找 + 显示类型 |
| `decl` | eval/infer | 全局声明（Arc 共享） |
| `namespace*` | infer | 包/命名空间解析 |
| `update_from` | unify | 更新追踪 |

关键方法：`bind()` `define()` `decl()` `new_binder()` `fake_bind()` `fresh_val()` `update_cxt()` `clone_without_src_names()`。

#### Locals 链（`syntax.rs:10`）

```rust
pub enum Locals {
    Here,
    Define(Rc<Locals>, Span<SmolStr>, Rc<Ty>, Rc<Tm>),
    Bind(Rc<Locals>, Span<SmolStr>, Rc<Ty>),
}
```

递归结构，用 Rc 共享前驱。`names()` 方法端序遍历提取名字列表。

#### Infer（推理引擎 `mod.rs:359`）

```rust
pub struct Infer {
    pub meta: Vec<MetaEntry>,
    pub meta_contrains: Vec<(Rc<Val>, Rc<Val>)>,
    trait_solver: Synth,
    trait_definition: HashMap<SmolStr, (..)>,
    trait_out_param: HashMap<SmolStr, Vec<bool>>,
    pub mutable_map: Rc<RwLock<HashMap<String, Rc<Val>>>>,
    pub hover_table: Vec<(Span, Span, HoverCxt, Rc<Val>)>,
    pub completion_table: Vec<(Span, SmolStr)>,
}
```

- `meta` — MetaEntry::Solved / Unsolved
- `trait_solver` — 类型类综合求解
- `mutable_map` — 全局可变状态（当前 HDL 用作模块表）
- `hover_table` / `completion_table` — LSP 收集

### 双向类型检查 (`elaboration.rs`)

核心算法：**`infer_expr` ↔ `check` 交替**。

#### infer_expr — 推导（`elaboration.rs:740`）

| 语法 | 行为 |
|------|------|
| `Var(name)` | `src_names` → `decl` → namespace fallback |
| `Obj(x, field)` | Sum/SumCase 的参数访问，或 trait method dispatch |
| `Lam(x, i, t)` | 新建 meta 作为参数类型，bind 后 infer body |
| `App(t, u, i)` | infer 函数 → Pi 域类型 check 参数 |
| `U(n)` | 类型 `U(n+1)` |
| `Pi(x, i, a, b)` | check_universe 两个分量 |
| `Let(x, a, t, u)` | check 绑定 → infer body |
| `Hole` | 创建 Unsolved meta |
| `Sum` | 推导各分量的类型 |
| `Match` | 拒绝（必须 check 下使用） |

**每步 push hover_table**：`HoverCxt { lvl, locals: cxt.locals.clone(), decl: cxt.decl.clone() }`

#### check — 检查（`elaboration.rs:239`）

| 语法+类型 | 行为 |
|-----------|------|
| `Lam` vs `Pi` | bind → check body |
| `Let` | check 绑定 → 扩展 cxt → check body |
| `Match` | 编译模式匹配 |
| `Hole` | fresh_meta |
| 一般 | infer_expr 推导 → unify |

辅助：
- `check_universe` — check 类型是宇宙
- `insert` / `insert_t` — 自动填充隐式参数
- `unify` / `unify_catch` — Miller 高阶统一化

### 统一化 (`unification.rs`)

基于 Miller pattern unification，核心操作：
- `flex_rigid` — 柔性-刚性统一
- `invert` — 部分换名（求 `PartialRenaming`）
- `prune` — 剪枝不可达参数

### 类型类系统 (`typeclass.rs`)

- `Synth` — auto 证明搜索
- `Instance` — 实例表
- 支持 multi-parameter + `outParam`

### Prelude 结构

**加载顺序**（`lib.rs:201` 硬编码）：

1. `op.typort` — 运算符 trait、基础类型
2. `eq.typort` — 等式
3. `nat.typort` — 自然数 + 算术 + 定理证明
4. 注册 `nat_to_dec` 内建
5. `natarith.typort`
6. `bool.typort`
7. `option` / `result` / `order` / `void`
8. `decidable.typort`
9. `vec.typort` — 索引向量
10. `either` / `list` / `string` / `nonempty`
11. `hdl.typort` — 当前 HDL
12. `show.typort`

每步走完整 `on_change`（parse → infer 全部 decl → 合并 cxt）。加载完毕后**自动导入别名**。

### 现有 HDL 实现（`hdl.typort`，纯 Typort 库）

#### Expr AST

```typort
enum Expr {
    create(name) | createIn(name) | createOut(name)
    createWidth(name, width) | createInWidth(name, width) | createOutWidth(name, width)
    createReg(name) | createRegWidth(name, width)
    literal(v) | binary(lhs, op, rhs)
    assign(lhs, rhs) | regAssign(lhs, rhs)
    when(cond, body, elseBody) | switch(value, cases)
    block(head, tail) | nop
}
```

#### Module 系统

`Module` + `module` 结构体，通过 `create_global` / `change_mutable` 操作**全局可变状态** (`Infer.mutable_map`)。信号声明和赋值都调用 `createSignalExpr` 插入当前模块。

when 块通过 `WhenState` / `WhenStack` 追踪上下文，赋值时自动包裹 `when(cond, e, None)`。

#### 硬件类型

```typort
struct Bool {     name: Option[String], expr: Expr }
struct Bits[width](name: Option[String], expr: Expr)
struct UInt[width](name: Option[String], expr: Expr)
struct SInt[width](name: Option[String], expr: Expr)
```

**Trait `Data`** — 所有硬件类型实现：

```typort
trait Data {
    def :=(that: Self): Unit
    def expr: Expr
}
```

`:=` 根据 `isRegExpr` 选择 `assign` 或 `regAssign`。

#### 运算符（通过 trait impl）

- `+` / `-`：同宽，结果类型不变
- `+^` / `-^`：结果宽度 +1（进位运算）
- `*`：`UInt[w1] * UInt[w2] → UInt[w1+w2]`
- `&` `|` `^`：同宽 bitwise
- `<<` `>>`：移位（宽度不变）
- `<` `<=` `>` `>=` `===` `=/=`：比较 → `Bool`
- `andR` `orR` `xorR`：归约 → `Bool`
- `##`：拼接（通过 `Cat` trait），结果宽度 = 左宽 + 右宽
- `msb` `lsb`：取最高/低位 → `Bool`
- `apply(idx: Fin width)`：取位 → `Bool`
- `resize[newWidth]` / `cast[newWidth](proof: Le(width, newWidth))`：位宽转换
- `asBits` / `asSInt` / `asBool`：类型转换

**Nat 宽度检查**：`natFitsIn(width, value: Nat) → Boolean`

#### Verilog 生成

通过 Rust 端内建函数 `nat_to_dec` 将 Expr 树转为 Verilog 字符串。

### LSP 集成概览

- **工作线程**：`mpsc` 通道去重 → 逐文件 parse + infer
- **`on_change` 流程**：parse → infer(逐 decl) → publish diagnostics
- **hover_table**：infer 完成后 `infer.clone()` 整份存入 `Backend.hover_table`（当前性能瓶颈之一）
- **`HoverCxt`**（已优化）：只存 `(lvl, locals, decl)` 替代完整 Cxt clone


