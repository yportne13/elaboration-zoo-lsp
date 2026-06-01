# HDL 语法设计 — 讨论议题

> 本文档列出需要讨论的 HDL 语法设计点，分类组织。已定的设计不会重复列出。

---

## A. 类型系统

### A1. Bool / Bits / UInt / SInt 的关系

**已定**：方案 B — 全部分立，无子类型。

- `Bool`、`Bits[w]`、`UInt[w]`、`SInt[w]` 都是独立的 `Data` 实现
- 互相不可隐式转换，跨类型操作必须显式转换（`.asBits` 等）
- 方法设计保证返回正确类型（如 `msb` 返回 `Bool`，不需要用户手动转换）

### A2. Bundle 的语法形式

**已定**：

```typort
// 具名 struct（无方向，纯数据结构）
struct AxiBus {
    addr: UInt[32]
    data: UInt[32]
    valid: Bool
}

impl AxiBus {
    def mst: AxiBus = newWithDir(this, Master)
    def slv: AxiBus = newWithDir(this, Slave)
    def flip: AxiBus = reverseDir(this)
}

// 匿名 Bundle
val io = Bundle {
    let a = in(UInt[8]())
    let b = out(UInt[8]())
    let bus = AxiBus().mst
}
```

- 具名 struct 不指定方向，方向在 impl 中用 `mst`/`slv`/`flip` 方法定义
- 匿名 Bundle 用 `let`（不用 `val`）
- 简单信号用 `in()`/`out()` 函数包裹
- 总线接口用 `Struct().mst` / `Struct().slv`

**遗留问题**：方向元数据存在哪？

- Expr AST 级别（当前方案：`createIn`/`createOut`）？
- 类型级别包装（如 `struct Directed[T] { inner: T, dir: Dir }`）？
- 需要大量详细讨论，暂挂。

### A3. Vec 与 Bundle 的关系

- `Vec(4, UInt[8])` 复用 prelude 的 Vec 类型，宽度索引参数是 `Nat`。这会带来一个 Nat 索引参数，信号访问时索引类型怎么定（`Fin 4` 还是 `Nat`）？
- Bundle 和 Vec 都实现 Data？这样 `:=` / `.expr` / `.asBits` 可以统一？

### A4. `UInt[8]` vs `UInt(8 bits)` 的语法

- `UInt[8]` 用方括号——Nat 类型参数，符合 Typort 隐式参数语法
- 是否允许 `UInt(8)`（圆括号，非隐式）？还是统一方括号？
- `Bits[8]` 宽度 0 合法吗？空向量？

### A5. Data 作为超类型

- `Data` trait 目前有 `:=` 和 `expr` 方法
- 是否保留这个设计？还是把 `:=` 提升为语言一级的赋值语句？
- `Data` 是否需要 `width: Nat` 方法返回位宽？

### A6. Trait 层次：Bitwise / Arithmetic / Comparison / Cast / BoolLike

**已定**：按功能拆分独立 trait，通过 supertrait + blanket impl 组合（详见 J1）。

各 trait 接口设计：

**Bitwise**
| 运算符 | 方法 | 实现类型 |
|--------|------|---------|
| `&` | `and` | Bits, UInt, SInt |
| `\|` | `or` | Bits, UInt, SInt |
| `^` | `xor` | Bits, UInt, SInt |
| `~` | `not` | Bits, UInt, SInt |
| `<<` | `shl` | Bits, UInt, SInt（右操作数: 编译期 Nat） |
| `>>` | `shr` | Bits, UInt, SInt（右操作数: 编译期 Nat） |

- `<<` / `>>` 只接受编译期 Nat 常量作为移位量
- 动态移位用 `switch` 实现

**Arithmetic**
| 运算符 | 方法 | 实现类型 |
|--------|------|---------|
| `+` | `add` | UInt, SInt |
| `-` | `sub` | UInt, SInt |
| `+^` | `addWithCarry` | UInt, SInt |
| `-^` | `subWithBorrow` | UInt, SInt |
| `*` | `mul` | UInt, SInt |

- `+` `-` 保持位宽，溢出截断
- `+^` `-^` 结果宽度 +1
- `*`：`UInt[w1] * UInt[w2] → UInt[w1 + w2]`
- `*` 结果从不丢失精度（SpinalHDL 风格）

**Comparison**
| 运算符 | 方法 | 实现类型 |
|--------|------|---------|
| `===` | `eq` | Bool, Bits, UInt, SInt |
| `=/=` | `neq` | Bool, Bits, UInt, SInt |
| `<` | `lt` | UInt, SInt |
| `<=` | `le` | UInt, SInt |
| `>` | `gt` | UInt, SInt |
| `>=` | `ge` | UInt, SInt |

- 结果恒为 `Bool`
- 两侧位宽必须完全相等，否则类型错误

---

## B. 模块/组件语法

### B1. 关键字

SpinalHDL 用 `class MyComponent extends Component`。Typort 选项：
- `Component MyModule { ... }`（如前文设计）
- `module MyModule { ... }`（更贴近 Verilog）
- `entity MyModule { ... }`

### B2. IO / 端口声明

SpinalHDL：

```scala
val io = new Bundle {
    val a = in UInt[8]()
    val b = out UInt[8]()
}
```

Typort 选项：
- `val io = Bundle { in val a: UInt[8](); out val b: UInt[8]() }`
- `val io = in(UInt[8]("a"))` + `out(UInt[8]("b"))`
- Component 自带的 `io` 字段是隐式的还是显式的？
- 是否支持没有端口的子模块？

### B3. 参数化

- `Component Adder(width: Nat) { ... }` — 用 Typort 的隐式/显式参数？
- 参数是编译期 Nat 还是运行时值？
- 是否允许参数有默认值？`Component Adder(width: Nat = 8)`

### B4. 实例化

- `val adder = Adder(8)` / `val adder = Adder[8]()`
- 子模块的 io 怎么访问？`adder.io.result`？
- 是否允许在 Component 定义内实例化其他 Component？

### B5. 层次结构

- 一个文件多个 Component？
- Component 嵌套定义（局部 Component）是否允许？

---

## C. 信号声明语法

### C1. 组合信号

SpinalHDL:

```scala
val x = UInt[8]()
```

Typort 应该类似，但：
- `val x = UInt[8]()` — `()` 是必须的吗？还是 `val x: UInt[8]` 足够？
- 信号创建时是否自动在模块表中注册？还是需要一个显式的 "声明" 语句？

### C2. 寄存器

**已定**：

```typort
val r = Reg(UInt[8]()).init(0)   // r: UInt[8]，不是 Reg[UInt[8]]
val r = RegNext(value)            // 延迟一拍
val r = RegNextWhen(value, cond)  // 条件延迟
val r = Reg(UInt[8]())            // 无初值寄存器
```

- `Reg(type)` 返回 `T` 本身（不是包装类型 `Reg[T]`），寄存器属性由内部机制维护
- `:=` 赋值时自动识别目标是否是寄存器，走 `regAssign` 路径
- 当前 `hdl.typort` 的 `Reg[T]` 包装类型设计需重构

### C3. 输入/输出信号

- `val a = in(UInt[8]())` — `in`/`out` 作为函数包裹
- 方向是用来标记 Bundle 字段的，还是可以用于独立信号？
- 在 Component 内部的非 io 信号可以有方向吗？

### C4. 默认值 / 初始化

- 信号是否有默认值？
- `UInt[8]()` 默认是 0 还是 undefined？

---

## D. 赋值语义

### D1. `:=` 的定位

当前：`:=` 是 `Data` trait 的一个方法，返回 `Unit`。

讨论：
- 应该提升为语言一级的**赋值语句**，不通过 trait 调用？
- 还是保留 trait 方式，让用户可以为自定义 Bundle 重写赋值逻辑？
- `:=` 是语句还是表达式？如果是表达式其值是什么？

### D2. 条件赋值

- `when` 块内部的 `:=` 是否自动生成 `when(cond, assign(...), None)`？
- 嵌套 `when` 怎么展开？
- `elsewhen` / `otherwise` 本质上就是 `when(!cond1 && cond2)` 的条件组合？

### D3. 多重驱动检查

- 同一个组合信号被多次 `:=` 是否报错？
- 寄存器可以多次赋值（最后一个是有效值）？
- 是否需要在 elaboration 阶段做单驱动检查？

### D4. 未赋值检查

- 输出端口没有被赋值是否报 warning？
- 未使用的信号是否报 warning？

---

## E. 控制流语法

### E1. `when` 链的语法

**记录中**（待定）：

**方案 A：链式调用**
```typort
when(cond) { body }.elsewhen(cond2) { body }.otherwise { body }
```
- `when` 返回 `WhenBlock[T]` 中间类型，`.elsewhen` / `.otherwise` 是方法
- 表达式：`let x = when(cond) { a }.otherwise { b }`，缺少 `.otherwise` 时类型不匹配
- SpinalHDL 用户熟悉
- 需要 `WhenBlock[T]` 类型

**方案 C：块风格**
```typort
when(cond) {
    body
} elsewhen cond2 {
    body
} otherwise {
    body
}
```
- Parser 一次性看到整个 when 树，无中间类型
- 表达式：`let x = when(cond) { a } elsewhen (cond2) { b } otherwise { c }`
- 所有分支类型合一 → 结果类型，类似 Rust `if {} else if {} else {}`
- 分支都是 `Unit`（赋值）时不强制 `otherwise`
- `elsewhen` / `otherwise` 变成保留字

**共同考虑**：`when` 是否作为表达式（最后一行作为返回值）。如果作为表达式，`otherwise` 在非 Unit 分支下必须出现。暂定。记录在案。

### E2. `switch` 的精确语法

**已定**：

```typort
switch(x, {
    is(0) { body1 };
    is(1) { body2 };
    default { fallback }
})
```

- `switch` 是**语句**（不是表达式），所有分支体赋值或 Unit
- `is` 是普通函数（不是关键字/保留字），返回 `Expr`
- `default` 也是普通函数
- 支持 `for` 展开生成多个 `is` 分支：
  ```typort
  switch(x, {
      for i in 0 until 4 {
          is(i) { body(i) };
      };
      default { fallback }
  })
  ```
- 穷尽性检查：不要求穷举，`default` 建议提供但不是严格强制

### E3. 三目运算符

**已定**：用 `Bool.mux` 方法。

```typort
val result = cond.mux(a, b)   // cond: Bool, a b: T
```

- 已在 `hdl.typort` prelude line 569 实现
- 无语法冲突问题

### E4. `for` 展开

**已定**：

```typort
for i in 0 until 4 {
    val x = UInt[8]()
    let y = UInt[8]()
}
// 展开为：
val x_0 = UInt[8]()   // i=0
let y_0 = UInt[8]()
val x_1 = UInt[8]()   // i=1
...
```

- `for` 编译期完全展开，循环变量 `i` 是 `Nat`
- 需要定义 `Range` 类型和 `Iterator` trait
- 循环体内允许声明硬件类型（信号等），自动加 `_<迭代索引>` 后缀命名
- 嵌套 for 支持，嵌套命名格式 `x_i_j`（每层下划线分隔）
- 循环体内声明的信号在循环外部可通过 `<name>_<idx>` 访问
- 不支持 break/continue
- `for` 是泛型 over `Iterator` 的（不限于 `Range`）

---

## F. 位宽系统与 Nat 证明

### F1. 类型层级求宽

- `UInt[8].width` 返回 `Nat` 类型的 `8`？
- 表达式级别怎么获取一个类型的宽度？
- 对 `UInt[n]`（n 是变量），其宽度在编译期可知还是需要运行时计算？

### F2. 自动扩位

- `UInt[8] := UInt[16]` — 右侧比左侧宽，直接报错？
- `UInt[16] := UInt[8]` — 左侧比右侧宽，自动零扩展？
- 是否需要类似 SpinalHDL 的 `s` 后缀（`U`/`S` 标注）？

### F3. `cast` / 证明接口

```
x.cast[newWidth](proof: Le(width, newWidth))
```

- `cast` 走哪个 trait？`Into[UInt[newWidth]]`？
- 证明 `Le(width, newWidth)` 怎么在 Typort 中构造？直接用 `le_refl` / `le_step`？
- 是否有语法糖让编译器自动搜索 `Le` 证明（当宽度是编译期常量时）？
- 编译期常量宽度的 cast 是否不需要显式 proof？

### F4. 类型层面的位宽运算

- `UInt[a] + UInt[b]` 结果宽度 = `max(a, b)`（Spinal 风格不扩位）
- 但 `UInt[a] +^ UInt[b]` 结果宽度 = `max(a, b) + 1`
- 这些宽度运算是在**类型层面**用 Nat 算术完成的。Typort 能做到这点，但编译期 Nat 算术（加法 `+`、`max`）的效率如何？
- 是否有性能问题？每次类型检查都要做 Nat 表达式的化简？

---

## G. 实现策略：mutable 状态问题

### G1. 当前方案的局限

目前 HDL 用 `create_global` / `change_mutable` 在 `Infer.mutable_map` 中维护全局模块表。问题是：
- 每次文件变更都重新跑整个 elaboration，mutable 状态从头来
- 没有类型安全：`mutable_map` 是 `HashMap<String, Rc<Val>>`，任意字符串 key
- WhenStack 也用同一机制，容易冲突

### G2. 重构方向

设计方案层面的几个方向：
- **函数式 Accumulation**：infer 时收集 `(Expr, Module)` pair，最后统一处理。不需要 mutable 状态
- **Cxt 扩展**：在 `Cxt` 中加一个 `hdl_state` 字段，通过 `Cxt::define` 式的纯函数更新传递
- **Effect/Writer**：infer 返回结果附带一个 "HDL 语句列表"，由 caller 组合
- **模块表在 Rust 端**：不做成 Typort 的全局变量，而是 Rust 端的专用结构

### G3. Verilog 生成的定位

- 生成 Verilog 的代码在 Rust 侧还是 Typort 侧？
- 当前通过 `nat_to_dec` 做 Rust 端导出——重构后是否保留这种设计？
- 能否把 Verilog 生成做成一个 Typort 函数，利用模式匹配处理 Expr AST？

---

## H. 与现有底座的兼容性

### H1. 现有 `hdl.typort` 的迁移

目前 `hdl.typort` 有 ~1200 行代码（所有运算符的 impl、when/switch 支持、信号声明 helper）。
- 重构后这些 impl 是保留为库代码，还是变成编译器内建实现？
- 向后兼容方案？

### H2. 语法冲突检查

- `|` 已被 `Or` trait 占用（`Boolean` 的 `|` 运算符）
- `?` 目前不是运算符但可能未来会用到
- `:=` 作为方法名在 Typort 中工作，但作为语法关键字呢？
- `--` 用于注释？Verilog 风格
- `/* */` 用于注释——和 Typort 一致

### H3. 与 LSP 的交互

- hover 时 HDL 类型怎么显示？
- completion 需要提供信号名、模块名
- goto definition：跳转到信号声明位置
- 这些都需要 infer 阶段保留 HDL 相关的 source map

---

## I. 其他设计

### I1. 切片与位提取

```
x(idx)            // 取某一位（返回 Bool/Fire 等）——x.apply(idx: Fin width)
x(high, low)     // 取范围（返回 Bits）——x.slice(high, low: Fin width)
x.take(high)     // 取低位到 high
x.msb / x.lsb    // 取最高/低位
```

- 括号索引 `x(i)` 在 Typort 中已经由 `Obj`（字段访问）和 `App` 区分？会不会有歧义？
- 是否需要 SpinalHDL 的 `x(7 downto 3)` VS `x(3 to 7)` 风格？

### I2. 拼接

- `a ## b` — 使用 `Cat` trait
- 拼接结果宽度 = `w(a) + w(b)`
- 是否支持链式拼接 `a ## b ## c`？

### I3. 类型转换

- `asBits`, `asUInt`, `asSInt`, `asBool` — 方法语法
- 是否需要 `bits(x)` 函数式风格？

### I4. 常量/字面量

**已定**：

- 整数/自然数字面量无类型标注时推断为**最小宽度**（如 `42` → `UInt[6]`，`0xFF` → `UInt[8]`）
- `:=` 的签名改为 `def :=(that: Into[Self]): Unit`，允许 Nat/其他类型通过 `.into` 自动转换
- `Into[UInt[width]] for Nat` — 只允许 `natFitsIn(width, value)` 的编译通过（具体约束实现待定）

**遗留问题**：Nat → Into[UInt[width]] 的宽度检查怎么表达（typeclass 约束 vs 编译器内置检查）。当前实现无条件接受所有宽度，是错误的。

### I5. 默认值 / 复位值

- `Reg(UInt[8]()).init(0)` — `init` 是方法
- `False` / `True` — Bool 字面量是否保留？
- 是否需要 `U(0)` / `S(-1)` 之类的字面量构造？

---

## J. 实现机制：Typeclass 组织

### J1. Supertrait + blanket impl

讨论记录：trait 层次设计（如 `Add`/`Sub`/`Mul` + `Arithmetic`）需要 Typort 底座支持 supertrait 约束和 blanket impl：

```typort
trait Arithmetic: Add + Sub + Mul {}          // supertrait
impl<T: Add + Sub + Mul> Arithmetic for T {}  // blanket impl
```

L13 的 typeclass 系统已有：
- `val_match` 中的 `Val::Rigid` 可作为类型变量匹配任意具体类型
- `Instance.dependencies` 支持子目标列表
- `try_resolve` 内的 `subst` 构建了绑定关系

缺失：
- `try_resolve` 未将 `subst` 应用到 dependencies 上（当前 line 313 直接 clone）
- Elaborator 不支持泛型 blanket impl 的解析
- 无 supertrait 语法

状态：**待定** — 是否在 Typort 底座加 supertrait 语法，还是先在 HDL prelude 用手动模式验证概念。

---

## K. 待实现功能

### K1. Scala 风格的 `apply`

如 `MyStruct(args)` 替代 `MyStruct.mk(args)`。需要在类型上定义一个特殊的 `apply` 方法，使类型名可以直接作为函数调用。

### K2. 宏展开功能（类似 Rust Analyzer）

编辑器中可以展开宏（`#[macro_export]` / `macro_rules`），查看展开后的代码。需要：
- LSP 端支持宏展开请求
- 编辑器端展示展开结果
