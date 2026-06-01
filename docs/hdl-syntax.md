# HDL 语法参考

> HDL 是 Typort 的硬件描述扩展，风格介于 SpinalHDL 和 Verilog 之间。
>
> **当前状态**：HDL 是作为 Typort 库（`hdl.typort`）实现的，不是语言内建语法。
> **目标状态**：HDL 将重构为语言内建语法（本文档描述的目标语法）。

---

## 1. 硬件类型

| 类型 | 语法 | 说明 |
|------|------|------|
| Bool | `Bool` | 单 bit 布尔值 |
| Bits | `Bits[width]` | 无语义位向量 |
| UInt | `UInt[width]` | 无符号整数 |
| SInt | `SInt[width]` | 有符号整数（补码） |
| Bundle | `Bundle { ... }` | 结构体 |
| Data | `Data` | 所有硬件类型的超类型 |

**宽度编码在类型上**：`UInt[8]` 有别于 `UInt[16]`。支持参数化宽度：`UInt[n]`（`n` 是编译期 Nat）。

Vec：复用 prelude 的 `Vec(size, DataType)`，如 `Vec(4, UInt[8])`。

---

## 2. 模块定义

```
Component MyModule {
    val io = Bundle {
        val a = in(UInt[8]())
        val b = out(UInt[8]())
    }

    // 组合逻辑
    io.b := io.a + 1
}
```

### 实例化

```
val sub = MyModule()
sub.io.a := 5
```

---

## 3. 信号声明

### 组合信号

```
val x = UInt[8]()           // 同一行可以写 val name = Type()
val y = Bits[16]()
```

### 输入/输出（Bundle 字段方向）

```
in(UInt[8]())               // 输入方向
out(UInt[8]())              // 输出方向
master(Bus())               // master 接口
slave(Bus())                // slave 接口
```

方向不写在类型上，写在声明上。

---

## 4. 时序逻辑（SpinalHDL 风格）

### 寄存器声明

```
val r = Reg(Bits[8]())          // 寄存器，无复位初值
val r = Reg(UInt[8]()).init(0)  // 寄存器，复位到 0
val r = RegNext(value)           // 延迟一拍
val r = RegNextWhen(value, cond) // 条件延迟
```

### 赋值

```
r := nextValue   // 寄存器更新（与组合逻辑 := 统一语法）
```

---

## 5. 时钟与复位

### 隐式 ClockDomain

每个 Component 自带隐式 `ClockDomain(clock, reset)`。时钟上升沿 / 复位电平可配置，同步/异步复位可选。

### 多时钟域

```
val cd = ClockDomain(clock, reset)
val area = ClockArea(cd) {
    // 该时钟域下的逻辑
}
```

---

## 6. Area（逻辑分组）

Area 提供逻辑分组，但不产生额外层次：

```
val a = Area {
    val x = UInt[8]()
    val y = UInt[8]()
}
// 访问：a.x, a.y
```

---

## 7. 赋值语义

- `:=` — 硬件连接/赋值运算符
- `=` — Typort 的变量/immut binding（与硬件赋值无关）

赋值根据左值是否为寄存器自动选择组合或时序赋值。

---

## 8. 控制流

### when

```
when(cond) {
    // body
}.elsewhen(cond2) {
    // body
}.otherwise {
    // body
}
```

### switch（穷尽检查）

```
switch(x) {
    is(value1) { ... }
    is(value2) { ... }
    default { ... }
}
```

`switch` 必须覆盖所有可能值，或显式提供 `default`。

### 三目运算符

```
val result = cond ? a | b
```

---

## 9. 运算符与位宽推导

### 运算符

| 类别 | 运算符 |
|------|--------|
| 算术 | `+` `-` `*` `/` `%` |
| 进位运算 | `+^` `-^` |
| 位运算 | `&` `\|` `^` `~` `<<` `>>` |
| 比较 | `===` `=/=` `<` `<=` `>` `>=` |
| 布尔 | `&&` `\|\|` `!` |
| 归约 | `andR` `orR` `xorR` |
| 拼接 | `##` |
| 取位 | `msb` `lsb` `apply(idx)` |
| 类型转换 | `asBits` `asSInt` `asBool` |
| 位宽操作 | `resize[newWidth]` `cast[newWidth](proof)` |
| 切片 | `take[high](low: Fin)` `slice[hi, lo](...)` |

### 位宽推导规则

- **`+` / `-`**：保持位宽（溢出静默截断）
- **`+^` / `-^`**：结果宽度 +1（进位/借位保留）
- **`*`**：`UInt[w1] * UInt[w2] → UInt[w1 + w2]`
- **`##`**：`Bits[w1] ## Bits[w2] → Bits[w1 + w2]`
- **比较**：结果恒为 `Bool`

### Nat 宽度检查

```
UInt[16] + 1          // 编译期常量 1 自动检查宽度
x + val.cast(prove)   // 参数化宽度需用户提供证明
```

`cast` 需要 `Le(width, newWidth)` 证明：

```
x.cast[newWidth](le_proof)   // 安全扩位
```

---

## 10. 编译期 for 展开

```
for i in 0 until 4 {
    // 编译期完全展开
    // i 是 Nat，可供索引或位宽参数化使用
}
```

- 不支持 break/continue（展开后不存在）

---

## 11. Verilog 生成

首期生成目标为 Verilog。

---

## 12. 设计路线图（本地）

- [ ] 类型系统重构：`Bool` `Bits[N]` `UInt[N]` `SInt[N]` `Bundle` 作为一等类型
- [ ] 语法支持：`when` / `switch` / `:=` / 三目
- [ ] 穷尽检查
- [ ] `Component` 语法
- [ ] `Reg` `RegNext` 时序语法
- [ ] `Area` 支持
- [ ] `ClockDomain` / `ClockArea`
- [ ] `for` 编译期展开
- [ ] 位宽推导 + Nat 证明系统
- [ ] Verilog 生成器
