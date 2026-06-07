# HDL Redesign Plan

## 1. 类型改名

```
struct Module { ... }  →  struct ModuleDef { ... }    // hdl-core.typort
```
新建 trait `Module`，包含 `def __tree: ModuleTree`，`module` 宏生成的 struct 自动 impl。

## 2. 层级数据结构

```typort
struct ModuleTree {
    name: String
    exprs: Vec[Expr]
    children: List[ModuleTree]
}
```

全局 `"module_stack": List[ModuleTree]` 做栈式管理。

- `pushFrame(name)` — 栈顶推入新 frame
- `popFrame()` — 弹出栈顶，返回其 `ModuleTree`
- `registerChildModule(child: ModuleTree)` — 将子 tree 注册到当前栈顶 frame 的 children
- `currentFrame` — 指向栈顶 frame，信号/赋值/instance 都写入它

## 3. Expr 新增变体

```typort
enum Expr {
    ...
    instance(instName: String, moduleName: String)   // 子模块例化记录
    subSignal(instName: String, signalName: String)   // 跨层级信号引用
}
```

- `instance` — 加入父模块 exprs，Verilog 生成时输出 `moduleName instName(...)` + 端口连接
- `subSignal` — 出现在父模块 assign 的 LHS/RHS，引用子模块实例的信号

## 4. `module` 宏展开模式

```
module MyAdder { ... }

// 展开为三个部分:
// Part 1: struct 定义
struct MyAdder {
    __tree: ModuleTree
    <ports + internal_signals + regs>
}

// Part 2: 构造函数
impl MyAdder {
    static def mk(): MyAdder =
        let _ = pushFrame("MyAdder")
        // 执行模块体（信号创建、赋值、when、switch 等）
        // 通过 createSignalExpr 写入栈顶 frame 的 exprs
        // 子模块例化通过 MyAdder2.mk() 调用自动管理
        let tree = popFrame()
        // 注册子模块到父模块
        let _ = registerChildModule(tree)
        MyAdder.mk(tree, <signals...>)
}

// Part 3: Module trait impl
impl Module for MyAdder {
    def __tree: ModuleTree = this.__tree
}
```

### 信号字段命名约定

信号字段名直接沿用 Expr 宏声明的标识符：
- `input a = UInt[8]` → struct 字段 `a: UInt[8]`
- `let b = Bool` → struct 字段 `b: Bool`
- `reg c = UInt[8]` → struct 字段 `c: UInt[8]`

### 信号创建

沿用当前 `createSignalExpr` 机制，但写入当前栈顶 frame。

子模块端口引用通过 `subSignal(instName, signalName)` 新建 Expr 变体，由合成时自动生成：
- 当用户写 `adder.a := 42` 时，宏自动将 `adder.a` 转换为 `subSignal("adder", "a")`

## 5. 子模块例化

```typort
module Top {
    let adder = MyAdder.mk()
    adder.a := 42.into
    let x = adder.result
}
```

`MyAdder.mk()` 内部：
1. pushFrame("MyAdder")
2. 执行模块体（创建 a, b, result，执行赋值）
3. popFrame() → 拿到 MyAdder 的 ModuleTree
4. registerChildModule(tree) → 注册到 Top 的 children
5. 为 Top 创建 instance("adder", "MyAdder") 写入 Top 的 exprs
6. MyAdder.mk(tree, a, b, result) 返回

对于外部信号引用 `adder.a`，`Top` 模块体内通过 `subSignal("adder", "a")` 引用。

## 6. Verilog 生成

### `moduleVL` 接收 `Module` trait

```typort
def moduleVL(m: Module): String
// 通过 m.__tree 访问 ModuleTree
```

### Verilog 生成流程

1. 输出 `module name (ports);`
2. 输出当前 frame 的 wire/reg 声明
3. 输出 assign / always 语句
4. 对每个 child（子模块实例）：
   a. 递归生成子模块的 wire/reg/assign/always
   b. 输出例化语句：`moduleName instName (.port1(wire1), .port2(wire2), ...);`
5. 输出 `endmodule`

### 端口连接推断

Verilog 生成器遍历父模块 exprs 中的 assign，检查 LHS/RHS 是否有 `subSignal`：
- 检测到 `subSignal("adder", "a")`，方向为 input → 生成 `.a(connected_wire)`
- 检测到 `subSignal("adder", "result")` 在 RHS，方向为 output → 生成 `.result(wire_name)`

## 7. Bundle 与其他信号类型

- `#[derive(Bundle)]` 生成 `impl Bundle` 和 `def create_TypeName(prefix)` 保持不变
- 后续改为 `TypeName.mk(prefix)` 风格，暂缓
- Bool/Bits/UInt/SInt 的工厂函数暂时保留 `newUInt`、`newBoolInput` 等不变
- 所有信号创建函数都写入当前栈顶 frame

## 8. 推拉函数 `pull()`

对于深层嵌套路径访问（如 `outer.inner.signal`），通过 `.pull()` 函数将所有中间模块的端口一路展开到当前层级。设计暂定，后续实现。

## 9. 不涉及 Rust 底层改动

全部实现在 typort 文件 + 宏层面。仅需：
- Rust 宏支持生成多个 Decl（Already planned）
- `macro_rules module` 展开为 struct + static impl + trait impl 三个声明
