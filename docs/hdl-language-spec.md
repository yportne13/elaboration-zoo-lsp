# HDL 语言规范（Typort HDL Language Specification）

> **状态：权威规范草案 · 2026-09-26。**
> 本文档是 Typort HDL（SpinalHDL 风格硬件描述扩展）的**权威语言规范**：以当前实现为准描述全部用户可见语法与语义，并对待定项逐条给出决策记录。
> 本文档**取代** `docs/hdl-syntax.md` 的目标语法描述（该文件保留为历史存档，不再维护）；`docs/hdl-design.md` / `hdl-design-discussion.md` 中的"待定"项以本文 §11 的决策记录为准。
> 覆盖范围：当前已实现的全部语法 + 待定项决策。二期大特性（硬件 Enum、Stream/FSM 完整化、BlackBox、自检阶段 2-4）只在 §12 留引用，不展开。
> 语法来源：`src/prelude/hdl/*.typort`（16 文件）、`examples/hdl/`（25 例）、`src/L13_namespace/module_tests.rs`、`src/L13_namespace/parser/mod.rs`。示例均可在 `examples/hdl/` 找到对应活样本。

---

## 0. 结论先行：待定项决策总表

历史文档（hdl-design / hdl-design-discussion / spinalhdl-gap）中的待定项，逐项决策如下；完整理由与影响面见 §11。

| # | 待定项 | 决策 | 性质 |
|---|--------|------|------|
| 1 | when 方案 A（链式）vs C（块风格） | **方案 C 块风格**，`when c { } elsewhen c2 { } otherwise { }`；链式 `.elsewhen()` 不做 | 已定（实现先于文档） |
| 2 | when 是否作为表达式 | **否**。when 恒为 `Unit` 语句；取值用 `cond.mux(a, b)` / 三目 | 已定（实现先于文档） |
| 3 | 方向元数据存储位置 | **Expr 级**（`createIn/createOut/createInOut…` 变体），类型不带方向 | 已定（实现先于文档） |
| 4 | `pull()` 跨层级信号展开 | **暂不做**；深层访问用中间模块端口手动提升 | 开放（推荐维持挂起） |
| 5 | RegInit 函数式 API | **不做**；`reg x = T init v` 宏 + `regNext`/`regNextWhen`/`auto*RegInit` 已覆盖 | 开放（推荐不做） |
| 6 | 常量移位 `<<`/`>>` 变宽 vs 保持宽度 | **保持宽度**（与 SpinalHDL `<<(Int)` 变宽为既知偏差，不迁移） | 已定（实现先于文档） |
| 7 | `/` `%` 位宽语义 | **已实现**：`/` 宽 = w(x)，`%` 宽 = w（等宽操作数下即 SpinalHDL 的 min 语义） | 已定（实现先于文档） |
| 8 | 饱和运算 `+\|` `-\|` | **暂不做**；用 when + 比较手写，等真实需求再加方法（不加新记号） | 开放（推荐暂缓） |
| 9 | muxList / priorityMux | **priorityMux / muxOH / ohMuxOr 已实现**（hdl-utils）；muxList 不补，用 switch / `vecAtUInt` 替代 | 部分已定 |
| 10 | `#*` 重复 / `reversed` | `#*` **不做**（用 for 展开）；`reversed` 已实现为 `reverse`（Bits/UInt） | 部分已定 |
| 11 | UFix/SFix 定点数 | **远期（三期）**，排在硬件 Enum、Stream/FSM、BlackBox 之后 | 开放（推荐排期） |
| 12 | 拼接/切片运算符终态 | 拼接唯一记号 `##`；切片用 `slice[hi, lo]` + 糖 `a[hi:lo]` / `a[N]`；不再引入独立 Verilog 风格运算符 | 已定（实现先于文档） |

实现过程中隐性定案、但旧文档仍标"待定/缺失"的其他项（详见 §7/§9/§10）：SInt `abs`、`expand`、宽度保持变量移位 `|<<`/`|>>`、inout 端口、Counter、BufferCC/真跨时钟域、Verilog 兼容层 M1-M3 **均已实现**；`cast` 的 `Le` 证明版本**已删除**，统一走 Eq 证明的等宽 `Cast`（§7.9）；`assert` 断言、HVec 填充工厂**未实现**（§8.3/§12）。

---

## 1. 总览与实现形态

### 1.1 HDL 是什么

HDL 是 Typort 的硬件描述扩展：**纯库实现**（`src/prelude/hdl/*.typort`，16 文件约 8500 行），不是语言内建语法。用户写的"硬件语句"经三层机制落到一棵可打印的模块树：

1. **宏转写**：`module` / `Expr` / `when` / `VExpr`（Verilog 兼容）四个 `#[macro_export]` 宏把表面语法转写为对 prelude 工厂函数的调用（`hdl-macros.typort`）。
2. **全局可变状态**：信号创建、赋值、when 条件栈、for 循环索引栈都通过 `change_mutable`/`create_global` 写入 `Infer.mutable_map` 的全局槽（`ModuleTree` / `WhenStack` / `HdlLoopIdx` / `ModuleRegistry` / `ModulePortTable` 等，`hdl-core.typort`）。
3. **代码生成**：`Expr` 树经 `moduleTreeVL` 等纯 typort 函数渲染为 Verilog-2001 文本（`hdl-verilog.typort`）。

### 1.2 组件作用域语义（def 体硬件语句）

硬件语句不只限于 `module` 宏体：

- `def f(): T = { <语句>* }` 花括号体逐条经 `Expr` 宏具名片段转写（与 module 体同一机制），**末条语句作为块值**（声明臂取被声明的 binder、控制链取 `unit`、裸表达式取自身）。
- def 在 module 体内被调用时，其硬件语句记录进**当前**模块树（组件作用域语义，与 SpinalHDL 一致）；def 在**顶层**（无 module 宿主）调用时副作用 no-op。
- 无参 def 含全局操作时走"副作用重放"路径（`def_replay_memo`）：每次调用在调用方上下文重新执行体；声明期不做 WHNF 缓存（`docs/hdl-def-body-hardware-statements.md`）。
- `case p => { <语句>* }` 花括号臂同理；match 的 scrutinee 是 **elaboration 期数据**（enum/Nat/Vec 值），只有命中臂的声明落树。

```typort
def delay(x: UInt[8]): UInt[8] = {
    reg d = UInt[8]      // 落进调用方 module 的树：reg [7:0] d;
    d := x               // d <= a（时钟块）
    d                    // 末条语句 = 块值
}
module top {
    input a = UInt[8]
    output out = UInt[8]
    out := delay(a)
}
println(moduleTreeVL(top.create.tree))
```

### 1.3 一个最小的完整模块

```typort
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w]
    input en = Bool
{
    sum := en.mux(a + b, a)
}
println(moduleTreeVL(myAdder.create[8].tree))
```

---

## 2. 词法与声明结构

### 2.1 module 宏

```typort
// 形态一：参数化 + 端口区 + 体（最常用）
module 名称[类型参数...] 端口区... {
    体语句...
}

// 形态二：显式时钟域（首个方括号参数是 ClockDomain 类型的标识符）
module 名称[myCd] 参数... 端口区... { 体语句... }

// 形态三：Verilog 兼容臂（ANSI 端口头 + endmodule）—— 见 §10.4 与 docs/verilog-compat.md
module top(input clk, input rst_n, input [7:0] a, output reg [7:0] q);
    ...
endmodule
```

宏展开（形态一/二）为一个 scala 风格 `class`，实现 `Module` trait：

- `struct 名称 { ..., a: UInt[w], ..., _res: ModuleTree }`——端口/体内声明的信号成为 struct 字段；副作用脚手架绑定折叠进 `_`/`_prev`/`_res` 字段。**类体内每个 `let` 都是字段**（无特例）。
- `def 名称.create[参数]`——急切执行副作用链：重置全局 → 压入模块 frame → 建端口 → 执行体语句 → `checkModuleTree` 自检（§10）→ 弹出并恢复 → 记录子模块实例（`mkInstanceIfParent`，顶层丢弃）→ 建父侧端口句柄（`subSignal`）。
- `impl Module for 名称 { def tree: ModuleTree = this._res }`——`tree` 读 **create 期快照**：体执行完、`checkModuleTree` 自检并注册进 `ModuleRegistry` 之后、把自身实例记录进父模块之前的不可变树。树不可变，重复访问幂等，不重放体。

约束与注意：

- 端口区（`{` 之前）按**连续分组**匹配，顺序必须为：`output reg` 带类型端口 → `output reg` Bool 端口 → 普通带类型端口 → Bool 端口；带 `init` 的端口必须独占一行（init 值按行尾截取）。
- 体内声明（`{}` 内部用 `Expr` 宏声明臂，§3.1）逐条转写，**无分组约束**，`input`/`output`/`inout`/`output reg` 同样生成真实端口（example 01a / 08d / 17c）。
- 体依赖"同名字段后者覆盖前者"的编译器行为（端口先建为信号、再覆写为 `subSignal` 句柄）。
- 顶层 `M.create` 不留幻影实例（无父模块时 `mkInstanceIfParent` 丢弃）。
- 不允许 module 嵌套定义（分组用 `Area` / def 函数）。

### 2.2 def 体语句块与 case 臂语句块

语法模板：

```typort
def f(参数): T = {
    <Expr 宏语句>...
    <末条语句>          // 块值
}
case 模式 => {
    <Expr 宏语句>...
    <末条语句>
}
case 模式 => 裸表达式    // 可以是 standalone when 宏（§6.1）
```

- 转写与 module 体同一机制；所有臂类型仍需一致。
- 前导 `{` 永远走语句块，裸表达式体与之无歧义（`p_block_body`）。

### 2.3 语句表（Expr 宏句法全集）

module 体、when/switch/for 体、花括号 def 体、花括号 case 臂共用的语句集（`Expr` 宏，`hdl-macros.typort`）：

| 语句 | 转写目标 |
|------|----------|
| `input x = T[w]` / `output x = T[w]` / `inout x = T[w]` | `new*Input/Output/InOut(w)` |
| `let x = T[w]`（T ∈ UInt/Bits/SInt）、`let x = Bool` | `new*(w)` |
| `reg x = T[w]` / `reg x = T[w] init v` / `reg x = Bool [init v]` | `new*Reg(InitNat)` |
| `output reg x = T[w] [init v]` / `output reg x = Bool [init v]` | `new*OutReg(InitNat)` |
| `let x = <表达式>` | `nameWire(<表达式>)` → `LetNamed`（§3.4） |
| `let _ = <表达式>` | 原样透传（不命名 wire） |
| `when c { } elsewhen c2 { } otherwise { }` | WhenStack 序列（§6.1） |
| `switch sel { is v { } default { } }` | when 链（§6.2） |
| `for i in lo until hi { }` | `rangeFor`（§6.4） |
| 其他裸表达式（含 `x := v`） | `let _ = <表达式>`（兜底臂） |

每条语句以自身 `;` 结尾；模块内语句按书写顺序执行（字段顺序 == 副作用顺序）。

---

## 3. 硬件类型与信号

### 3.1 基本类型

| 类型 | 语法 | Verilog | 说明 |
|------|------|---------|------|
| Bool | `Bool` | `wire`（1 位） | 单 bit；宽度不出现在类型参数 |
| Bits | `Bits[w]` | `wire [w-1:0]` | 无语义位向量 |
| UInt | `UInt[w]` | `wire [w-1:0]` | 无符号 |
| SInt | `SInt[w]` | `wire signed [w-1:0]` | 补码有符号 |

- 宽度编码在类型上：`UInt[8]` ≠ `UInt[16]`；宽度是编译期 `Nat`，可参数化（`UInt[w]`、`UInt[w + 1]`、`UInt[log2Up n]`）。
- 四类全部分立，无子类型，互不隐式转换；跨类型用 `.asBits/.asUInt/.asSInt/.asBool` 显式重标（§7.9）。
- 结构表示：`struct UInt[width: Nat] { name: Option[String], zz_expr: Expr }`；`name` 用于打印与自检，`zz_expr` 是 Expr 树节点。

### 3.2 方向与端口

方向不写在类型上，写在声明上（Expr 级元数据，决策 #3）：

| 声明 | Expr 变体 | Verilog 端口行 |
|------|-----------|----------------|
| `input x = T[w]` / `input x = Bool` | `createInWidth` / `createIn` | `input wire [w-1:0] x` / `input wire x` |
| `output x = T[w]` | `createOutWidth` | `output wire [w-1:0] x` |
| `inout x = T[w]` / `inout x = Bool` | `createInOutWidth` / `createInOut` | `inout wire [w-1:0] x` |
| `output reg x = T[w] [init v]` | `createOutRegWidth(Init)` | `output reg [w-1:0] x`（强制 reg） |

`output reg` 是"输出端口 + 寄存器"：`:=` 驱动走时钟块（`isRegExpr` 判定），`init v` 进异步复位块，端口自文档化不依赖 when 推断（example 17）。

端口声明的两个位置：
- **端口区**（module 头，`{` 前）：受 §2.1 分组约束；
- **体内**：`Expr` 宏声明臂，任意顺序（例：17c `bodyOutReg`）。

inout 语义：模块不驱动自己的 inout/input 引脚（三态驱动不在模型内）；Bundle 的 inout 方向在 `asMaster` 里声明后，master/slave 两侧都生成真 inout 端口（example 15）。

### 3.3 Bundle 与 IMasterSlave

```typort
#[derive(Bundle)]
struct AxiLite {
    awaddr: UInt[32]     // 字段不带方向标记
    awvalid: Bool
    awready: Bool
}
impl IMasterSlave for AxiLite {
    def asMaster: AxiLite =
        let _ = out(this.awaddr)     // master 视角逐字段声明 in/out/inout
        let _ = in(this.awready)
        this
}

module t {
    let master = AxiLite.create.asMaster   // out 字段 → output 端口，in 字段 → input 端口
    let slave  = AxiLite.create.asSlave    // 方向自动翻转
    master <> slave                        // 双向连接（§5.4）
}
```

- `#[derive(Bundle)]` 生成：`impl Bundle`（字段级批量 `:=`，自动跳过 input/inout LHS）、`impl Into[Self]`、**自动命名工厂 `TypeName.create[bn: BindingName]`**。
- 命名链：嵌套 bundle 工厂把绑定名前缀沿字段路径逐级下推（`bn.name + "_" + 字段名`），深层叶子得到全路径名（`m_aw_lane_data`，example 11）；3 层以上必须靠它避免同名冲突。
- `in()/out()/inout()` 是恒等函数（`hdl-bus.typort`），方向由 derive（`parser/derive.rs`）**语法读取 asMaster 体**生成 `asMaster`/`asSlave` 方法；用户只写 asMaster。
- 参数化 Bundle：`struct MyBus[w: Nat]` + `impl[w: Nat] IMasterSlave for MyBus[w]`，参数一一对应。

### 3.4 信号命名：BindingName 机制

所有信号工厂带隐式参数 `[bn: BindingName]`；编译器对**每个 let 绑定**自动以绑定名填充（`cxt.with_binding_name`）：

```typort
let mySignal = autoUInt(8)      // 信号名 = "mySignal"
let myInput = newUIntInput(8)   // 同理（legacy 名 new* 与 auto* 行为一致）
```

- `loopName(bn.name)`：for 循环内声明的信号自动加当前迭代索引后缀——`x_0, x_1, ...`；嵌套 for 为 `x_i_j`（外层在前）。空栈时原名。
- `let _ = <工厂>(...)`：丢弃绑定，无名字（`_` 是 Hole，不命名）。
- 显式命名变体 `new*Named(name, ...)` 供库内部（Bundle derive、RegNext、计数器、Verilog 兼容层）使用。
- **表达式 let 生成命名 wire**（`LetNamed` typeclass）：`let x = a + b` 落树为 `wire [7:0] x; assign x = (a + b);`，后续引用读 `x` 不再内联；已声明信号（工厂产物/端口/reg/mem）的 let 是纯别名，不额外建 wire。已知限制：宽度参数化 module 内（`module m[w: Nat]`）经 impl Nat 参数求得的宽度可能冻结为非落地数（HDL004 报告，`docs/l13-typeclass-instance-nat-param-bug.md`）。

### 3.5 信号工厂族总表（`hdl-signals.typort`）

| 族 | wire | input | output | inout | reg | reg init | out reg | out reg init |
|----|------|-------|--------|-------|-----|----------|---------|--------------|
| auto*（UInt/Bits/SInt） | `autoUInt(w)` | `autoUIntInput(w)` | `autoUIntOutput(w)` | `autoUIntInOut(w)` | `autoUIntReg(w)` | `autoUIntRegInit(w, v)` | `autoUIntOutReg(w)` | `autoUIntOutRegInit(w, v)` |
| auto* Bool | `autoBool` | `autoBoolInput` | `autoBoolOutput` | `autoBoolInOut` | `autoBoolReg` | `autoBoolRegInit(v)` | `autoBoolOutReg` | `autoBoolOutRegInit(v)` |
| new*（legacy 名，行为同 auto*） | `newUInt(w)` | `newUIntInput(w)` | `newUIntOutput(w)` | `newUIntInOut(w)` | `newUIntReg(w)` | `newUIntRegInitNat(w, v)` | `newUIntOutReg(w)` | `newUIntOutRegInitNat(w, v)` |
| 显式命名（库内部） | `newUIntNamed(n, w)` | `newUIntInputNamed` | … | … | `newUIntRegNamed` | `newUIntRegInitNatNamed` | … | … |

每列均有 Bits/SInt 同名变体与 Bool 无宽变体。时钟域变体：`autoUIntRegCd(w, cd)`、`autoUIntRegInitCd(w, v, cd)` 等（§9.3）。

派生构造：

| API | 说明 |
|-----|------|
| `regNext(value)` / `regNextWhen(value, cond)` | 任意 Data 延迟一拍 / 条件延迟（`RegNext` typeclass，泛型覆盖 UInt/Bits/SInt/Bool；寄存器按 let 绑定名命名） |
| `counter(w)` / `counterInc(w, en)` | 自增 / 使能计数器，返回 `Counter[w] { value: UInt[w], willOverflow: Bool }`（`willOverflow` = `~value == 0` 组合信号） |
| `memUInt(w, words)` / `memBits` / `memSInt` / `memBool(words)` | 存储器工厂（§8.2） |

### 3.6 Vec（硬件向量）

无独立 HVec 类型（gap §7 第 4 条未落地）：复用 prelude 的 `Vec[A] n`（nil/cons GADT）承载同宽信号集合。

- 静态构造/访问：`cons a0 (cons a1 nil)` + match / `::`。
- 硬件动态索引：`vecAtUInt(vec, idx, dflt)`（`hdl-ops.typort`）——`idx: UInt[log2Up n]`，展开为平衡 mux 链；`vecAtUIntHelp` 递归线性 mux。
- 无 fill 工厂、无批量 `:=`（`docs/spinalhdl-gap.md` §7 的 HVec 条目仅部分落地，见 §12）。

### 3.7 ClockDomain（类型形态）

```typort
struct ClockDomain {
    clockName: String
    resetName: String
    config: ClockDomainConfig   // Sync | Async
    clockEdge: ClockEdge        // RisingEdge | FallingEdge
    resetPolarity: ResetPolarity // ActiveHigh | ActiveLow
}
def defaultClockDomain: ClockDomain = ClockDomain.mk "clk" "reset" Async RisingEdge ActiveHigh
```

语义见 §9。注意：`ClockArea` **未实现**；`Area` 只是恒等分组函数（§6.5）。

---

## 4. 字面量与 Into

- `Nat` 字面量经 `Into[UInt[w]]` / `Into[SInt[w]]` 自动转 `literal(v)`，可直接参与赋值、运算、比较：`y := a + 5`、`a === 42`、`when cnt === 2 { cnt := 0 }`。
- `true` / `false` 经 `Into[Bool] for Boolean` 转换（`w := true`）。
- Verilog sized 字面量 `8'h2A` / `4'b1010`：parser 脱糖为 `sizedLiteral(v, w)`，代码生成输出 `8'd42` 形式（拼接内合法，IEEE 1364 要求 sized）；仅 Verilog 兼容层通道（§10.4）。
- **已知缺口**：`natFitsIn` 定义了但 `Into` impl 不做宽度检查——`UInt[2] := 100` 不会被拒绝（`docs/hdl-design-discussion.md` I4 遗留）。修法见 §11 补充记录。

---

## 5. 赋值与连接

### 5.1 `:=`

```typort
trait Data {
    def :=[T](that: T): Unit where T: Into[Self]
    def expr: Expr
    def <>(that: Self): Unit   // §5.4
}
```

语义：

1. RHS 经 `Into` 自动转换（Nat/Boolean 字面量、`MuxExpr` 等）。
2. `pickAssign` 分发：LHS 是寄存器（`isRegExpr`：`createReg*`/`createOutReg*`/bitsel/partsel 基寄存器）→ **`regAssign`**（时钟块 `<=`）；否则 `assign`（连续赋值 `=`）。
   - Verilog 兼容 `always @(*)` 上下文例外：reg 被组合驱动（`assign`）并报 HDV002（§10.4）。
3. when 栈内自动条件化（§5.3）。
4. LHS 支持位选：`t[0] := x`（`bitsel` 基）；部分选 LHS 在 Verilog 兼容层支持（`a[7:4] = x`），typort 风格以 `slice` 表达式 + 中间信号惯用。
5. Bundle `:=`：derive 生成的逐字段批量赋值，自动跳过 input/inout 端口 LHS（方向互补的 master/slave 可双向对连）。

约束（自检强制，全部 warning 级）：

- 同一组合信号多次无条件赋值 → HDL010；
- 无条件 + 条件混合 → HDL011；
- 组合 + 时钟混合 → HDL012；
- 多时钟域驱动同一寄存器 → HDL013；
- 驱动自己的 input 端口 → HDL023（`:=`/`<>` 也会结构性跳过 input LHS）。

### 5.2 `<>` 双向连接

```typort
master <> slave
// 等价：
master := slave
slave := master
```

两侧各驱动一次，各自跳过 input/inout 端口侧（`isInputPort`）；inout 字段不驱动。primitive 由 `Data` trait 默认方法提供，Bundle 由 derive 生成。两侧类型必须一致；方向互补的端口对是预期用法。

### 5.3 when 条件语义（赋值视角）

每个赋值记录**完整使能条件**（`WhenStack` 合成，`hdl-core.typort`）：

- 嵌套：所有活跃层条件合取——`when a { when b { x := v } }` → `cond = a && b`；
- elsewhen：对本链早前分支否定累积——`when c1 {...} elsewhen c2 {...}` → `c2 && !c1`；
- otherwise：本链全部分支之否定——`!c1 && !c2`。

生成器因此发射**独立 `if`**（不重建 else-if 链，独立 when 不耦合；`when_elsewhen_negation_accumulates` 回归）；`when` 节点的 body 恒为单条赋值。生成器另保留 else-if 重建路径（`when(c, b, Some(when(...)))` 形态），但标准管线从不产生该形态（`addWhenContext` 只包裹 `when(c, e, None)`）。信号声明（create*）不受 when 上下文包裹。

### 5.4 多驱动总约束

组合信号：恰好一个无条件驱动，或若干互斥 when 分支驱动；寄存器：`:=`（可条件化）；mem：`write` 端口。违反形态由 HDL010-013 报告。

---

## 6. 控制流

### 6.1 when / elsewhen / otherwise（决策 #1、#2）

**块风格（方案 C），两种实际形态：**

```typort
// 形态一：Expr 宏 when（语句位）——module 体、when/switch/for 体、
// 花括号 def 体、花括号 case 臂。以分号语句序列转写，无值。
when sel {
    out := a
} elsewhen sel === 1 {
    out := b
} otherwise {
    out := c
}

// 形态二：standalone when 宏——仅在"裸表达式位"可用：
// 未花括号 def 体（def f(): Unit = when c { ... }）、裸 case 臂。
// 转写与形态一相同（同一 whenBegin/whenElseBegin/whenOtherwiseBegin/whenEnd
// 序列），区别仅在末尾补 `unit` 值尾，使整体成为类型 Unit 的完整表达式。
def f(): Unit = when en { r := a } otherwise { r := b }
```

- 三种臂组合均合法：`when + otherwise`、`when + elsewhen*`（无 otherwise）、`when + elsewhen* + otherwise`。
- 整条链共享**一个** WhenStack 层（分支间不 `whenEnd`），这是否定累积能工作的前提。
- **两形态的关系**：转写逻辑逐字相同、独立维护两份（`hdl-macros.typort` 文件头 NOTE，修改必须同步）。**推荐**：module/块体内一律用形态一；形态二仅用于裸 def 体与裸 case 臂（语法上别无选择）。不引入链式 `.elsewhen()`（方案 A）。
- **when 不是表达式**：取值用 `cond.mux(a, b)` 或三目（§6.3）。

### 6.2 switch / is / default

```typort
switch sel {
    is 0 { result := a }
    is 1 { result := b }
    default { result := c }
}
```

- **语句**（不是表达式）；脱糖为 when 链：首臂 `whenBegin(sel === v1)`，后续臂 `whenElseBegin(sel === v2)`（否定累积），`default` 臂 `whenOtherwiseBegin`。
- `is` 值：Nat 字面量或信号（经 `===` 比较）；`is`/`default` 是宏片段的一部分，不是普通函数也不是关键字。
- **default 臂可省略（2026-09-26 放宽）**：无 `default` 的 switch 合法，脱糖为纯 when 链（未覆盖的选择子取值保持原值，SpinalHDL 语义）。枚举选择子的穷尽性检查经 `switchFinalEnum(sel, cases, false)` 显式调用（`hdl-enum.typort`，`#[derive(HdlEnum)]` 生成元素表），未覆盖元素报 **HDL040 WARNING**——详见 `docs/hdl-enum-design.md` §4.7；带 `default` 的 switch 不检查。
- 函数式替代形态（库内部/少用）：`switchOnExpr(sel.expr).isValueExpr(v.expr, { body }).default({ body })`（`SwitchBuilder`，`hdl-ops.typort`）。

### 6.3 三目 / mux

```typort
out := sel.mux(a, b)     // Bool.mux：返回 MuxExpr[T]，:= 右侧经 Into 落成 mux 表达式
out := cond ? x : y      // C 风格三目；parser 直接脱糖为 .mux 调用
let picked = sel.mux(x, a)   // let 捕获 MuxExpr，使用点再 Into
```

`mux(cond, whenTrue, whenFalse)` 是 `Expr` 变体；Verilog 生成 `cond ? a : b`。

### 6.4 for 编译期展开

```typort
for i in 0 until 4 {
    output x = UInt[8]     // 展开为端口 x_0, x_1, x_2, x_3
    x := a
}
for w in 0 until 3 {
    output v = UInt[w + 2] // 索引参与位宽
    v := a.slice[w + 1, 0]
}
```

- 转写：`let __hloop: Unit = rangeFor(lo until hi, i => <体>)`——term 级 Nat 递归（`Range`/`until`/`HdlLoopIdx` 栈，`hdl-core.typort`）。
- **半开区间** `[lo, hi)`；`hi <= lo` 时空展开（无信号、无语句，`module_for_loop_empty_range`）。
- 循环变量是当次迭代的 `Nat` 常量：可驱动位宽参数（`UInt[i + 1]`）、静态索引（`a.slice[w + 1, 0]`）。
- 循环体内**声明的信号**自动加索引后缀：单层 `x_0..x_{n-1}`；嵌套 `x_i_j`（外层在前，`loopName` 读 `HdlLoopIdx` 栈）。赋值与引用不加后缀。
- 无 break/continue（展开后不存在）。`for` 泛型 over 迭代域目前即 `Range`（`lo until hi`）。
- 输出带尾分号是宏转写硬约束（历史修复，`docs/for-hdl-blocker.md`）。

### 6.5 Area

```typort
let g = Area { let x = UInt[8]; x := a }   // 恒等分组：body(unit)，无命名空间、无字段访问
```

仅代码组织用（SpinalHDL Area 的近似）；不产生层次、不提供 `a.x` 访问。逻辑复用请用 def 函数（组件作用域语义，§1.2）。

---

## 7. 运算符全集与位宽语义

### 7.1 算术（UInt / SInt）

| 运算符 | 签名 | 结果宽度 | Verilog | 备注 |
|--------|------|----------|---------|------|
| `+` | `T[w] + T[w]` | `w`（溢出截断） | `+` | 同宽要求；`u + nat` 字面量右操作数（Into） |
| `-` | `T[w] - T[w]` | `w` | `-` | 同上 |
| `+^` | `T[w] +^ T[w]` | `w + 1` | `{1'b0, a} + b` | 进位保留；SInt 双符号扩展 `{a[w-1],a} + {b[w-1],b}`（嵌套安全，不靠上下文宽度） |
| `-^` | `T[w] -^ T[w]` | `w + 1` | `{1'b0, a} - b` | 借位保留，同上 |
| `*` | `UInt[w1] * UInt[w2]` | `w1 + w2` | `*` | 不丢精度；`u * nat` 字面量乘（结果同宽） |
| `*` | `SInt[w] * nat` | `w` | `*` | **`SInt * SInt` 未实现**（旧 gap 文档"SInt 同宽乘法"已过时） |
| `/` | `T[w] / T[w]`、`u / nat` | `w`（= w(x)） | `/` | SpinalHDL 语义；可综合 |
| `%` | `T[w] % T[w]` | `w` | `%` | 等宽操作数下即 SpinalHDL 的 `min(w(x), w(y))` |
| `.neg` | `SInt[w].neg` | `w` | `-a` | 取负 |

### 7.2 位运算（Bits / UInt / SInt，同宽）

`&` `|` `^`（二元，同宽）、`~a`（前缀，parser 脱糖为方法 `.not`，Verilog `~`）。Bool 另有 `&&` `||` `!`（逻辑，`!a` 即方法 `!`）与 `&` `|` `^`（位级，`And/Or/Xor` trait）。前缀 `-a` 脱糖为 `.neg`。

### 7.3 移位与循环移位（决策 #6）

| 形式 | 签名 | 结果宽度 | Verilog | 说明 |
|------|------|----------|---------|------|
| `<<` / `>>` | `T[w] << nat`（编译期 Nat 常量） | `w`（**保持宽度**） | `<<` / `>>` | 与 SpinalHDL `<<(Int)` 变宽语义为**既知偏差**；扩位用 `+^`/`##`/`expand` 显式表达 |
| `SInt >>` | `SInt[w] >> nat` | `w` | `>>>`（算术右移） | |
| `\|<<` / `\|>>` | `T[w] \|<< UInt[s]`（信号移位量） | `w`（保持宽度） | `<<` / `>>` 变量移位 | SpinalHDL `\|<<`/`\|>>` 对应物；可综合 |
| `SInt \|>>` | | `w` | `>>>` | 算术 |
| `rotateLeft` / `rotateRight` | `Bits[w] rotateLeft UInt[s]` | `w` | `(a << s) \| (a >> (w - s))` | 仅 Bits；s 可为信号 |

### 7.4 比较（结果恒为 Bool，两侧同宽）

`<` `<=` `>` `>=`（UInt/SInt）；`===` `=/=`（UInt/SInt/Bool）。Nat 字面量可直接作右操作数（`a === 42`、`a < 100`）。辅助：`eqNat` / `neNat`。Verilog 映射 `==` / `!=` / `<` …

### 7.5 归约

`andR` `orR` `xorR` → `Bool`（Bits/UInt/SInt）。前缀糖：`&a` / `|a` / `^a` 由 parser 脱糖为 `.andR` / `.orR` / `.xorR`（与 Verilog 前缀归约记法一致）。

### 7.6 拼接 `##`（决策 #12）

`Cat` trait，结果宽度 = 左宽 + 右宽，链式可用：

| 左 \ 右 | Bool | Bits[l] | UInt[l] | SInt[l] |
|---------|------|---------|---------|---------|
| **Bool** | `Bits[2]` | `Bits[l+1]` | `UInt[l+1]` | `SInt[l+1]` |
| **Bits[l]** | `Bits[l+1]` | `Bits[l+r]` | `Bits[l+r]` | — |
| **UInt[l]** | `UInt[l+1]` | `UInt[l+r]` | `UInt[l+r]` | — |
| **SInt[l]** | `SInt[l+1]` | `SInt[l+r]` | — | `SInt[l+r]` |

- "—" 无 impl：跨 UInt/SInt 拼接先 `.asBits`/`.asUInt`。
- 拼接裸 `literal` 不合法（`literal(0) ## x` 无法解析）：用 `Bool.mk(None, literal(0)) ## x` 或 sized 字面量（Verilog 兼容通道）。
- Verilog 生成 `{a, b}`；拼接内常量自动 sized（`{1'b0, a}`、`{4'd3, b}`）。

### 7.7 位选 / 切片

| 形式 | 签名 | 结果 | 说明 |
|------|------|------|------|
| `a.msb` / `a.lsb` | | `Bool` | 最高/最低位 |
| `a.apply[N]` / `a[N]` | `apply[idx: Nat]` | `Bool` | `[N]` 是 parser 对隐式参数的方括号糖 |
| `a.slice[hi, lo]` | | `T[hi - lo + 1]` | 类型级 Nat 参数 |
| `a[hi:lo]` | | 同 slice | parser 脱糖为 `a.slice[hi, lo]`（part-select 糖） |
| `t[N] := x` | | — | LHS 位选赋值（寄存器性随基信号，`isRegExpr` 递归） |

### 7.8 mux / 多路

- `cond.mux(a, b)` / `cond ? x : y`（§6.3）。
- `priorityMux(sel, vals, dflt)`：sel 第 i 位优先的优先选择（`Vec[T] width`，hdl-utils）。
- `muxOH(oneHot, vals)` / `ohMuxOr(oneHot, vals)`：one-hot 选择。
- `vecAtUInt(vec, idx, dflt)`：Vec 硬件动态索引（§3.6）。
- `muxList` 不做（§11 #9）。

### 7.9 位宽与类型转换

| API | 签名 | 语义 |
|-----|------|------|
| `resize[newWidth]` | `UInt[w] resize UInt[nw]` | **无检查**重标（同 Expr 换类型）；SInt 同 |
| `cast(prove)` | `def cast(prove: Eq(Self, U)): U` | core/eq.typort 的 `Cast` trait；**旧的 `Le` 证明版本已删除**，一切类型转换走 Eq 等宽证明（`x.cast(uint_cast_prove[w])`，example 13） |
| `asBits` / `asUInt` / `asSInt` / `asBool` | 各类型互转 | 纯重标，同 Expr，不改位形；Bool → 宽 1 |
| `abs` | `SInt[w].abs: UInt[w]` | 符号位 mux（`msb ? -x : x`） |
| `expand` | `SInt[w].expand: SInt[w+1]`；`UInt[w].expand: UInt[w+1]` | SInt 符号扩展 `{msb, x}`；UInt 零扩展**依赖 Verilog 赋值上下文**（同 resize 惯用法） |
| `reverse` | `reverse(bitsOrUInt)` | 位反转（SpinalHDL `reversed` 对应物） |

### 7.10 位宽工具函数（hdl-core）

`maxNat` / `minNat` / `div2Up` / `log2Up` / `natFitsIn`；类型级宽度计算用 Nat 表达式直接写（`UInt[w1 + w2]`、`UInt[log2Up n]`）。

---

## 8. 层次、存储与验收

### 8.1 模块实例化与子模块端口连接

```typort
module topWithPorts {
    input a = UInt[8]
    input b = UInt[8]
    input en = Bool
    output sum = UInt[8]
    let u = myAdder.create[8]   // 实例自动记录（instance(bn.name, "myAdder")）
    u.a := a                    // 父驱动子输入 → .a(a)
    u.en := en
    sum := u.sum                // 读子输出 → .sum(sum)
}
println(moduleTreeVL(topWithPorts.create.tree))
```

- 实例名 = let 绑定名（bn）；`u.port` 是带类型的 `subSignal("u", "port")` 句柄（create 时由宏覆写字段生成）。
- 端口连接由生成器从 assign 的 LHS/RHS `subSignal` 推断（`.port(wire)`）；未连接端口报 HDL022，方向反接报 HDL020/021，端口不存在报 HDL025。
- 单棵 `ModuleTree` 不携带子模块定义；全设计的注册表 `ModuleRegistry`（按模块名去重，首个注册者胜——**同一参数化模块的两次不同实例化会碰撞**，已知限制）。手动合并多树用 `buildMultiTree` 惯用法（example 09c）。
- 深层访问 `outer.inner.sig` 不支持（`pull()` 决策 #4）。

### 8.2 Mem

```typort
let myRam = memUInt(8, 64)          // 64 × 8 位，reg [7:0] myRam [0:63]
myRam.write(addr, data, en)          // 同步写：if (en) myRam[addr] <= data;
let rd = myRam.readSync(addr)        // 同步读：生成寄存器（bn 命名）+ 时钟赋值
let rc = myRam.readAsync(addr)       // 组合读：mem[addr] 表达式
let r2 = myRam.readSyncCC(addr, cc)  // 跨时钟域读——当前与 readSync 相同（无同步器）
```

- 工厂：`memUInt(w, wordCount)` / `memBits` / `memSInt` / `memBool(wordCount)`（宽度参先、字数参后，同 SpinalHDL 参数序）；显式命名 `newMemUIntNamed`。
- 无条件写：使能传 `Bool.mk(None, literal(1))` → 生成器省略 `if` 守卫。
- 同一条 mem 多次 write/read 可并出（端口独立记录），但**无显式双口 API/校验**。
- mem 必须被读（死内存 HDL002）；声明在 when 内/外的写语义一致（write 落时钟块）。
- 真 CDC 读用 `hdl-crossclock.typort` 的 `readSyncCCUInt[depth]`（BufferCC 链后端，§9.3）。

### 8.3 打印与验收

| API | 用途 |
|-----|------|
| `moduleTreeVL(m.create.tree)` | 单模块 Verilog（最常用验收口） |
| `allModulesVL(tree)` | 树内全部 ModuleDef 的 Verilog（手动多树合并时用） |
| `designVL(top.create.tree)` | 自包含设计输出：从 top 沿实例边拉取 `ModuleRegistry` 中全部被实例化定义（verilator 友好） |
| `designManifestVL(top.create.tree)` | JSON 设计清单（端口/时钟域/实例元数据），供 `src/sim` 仿真 harness 消费 |

隐式端口合成规则：模块含时钟块（任何 regAssign/memWrite）→ 自动补 `input wire clk`；含复位初值（`init`）→ 自动补 `input wire reset`；额外时钟域（regAssignCd/createReg*Cd）逐域补 clk（有 init 再补 reset）。

### 8.4 自检框架（阶段 1 已实现）

自检挂在 module 宏 **create 侧** `_res` 点（`checkModuleTree` → `runChecks`），每次模块声明被类型检查时运行；报告经 Rust builtin `report_check_issue` 排水为 LSP WARNING（行级去重）。规则集见 §10.2。设计文档：`docs/hdl-selfcheck-design.md`。

---

## 9. 时钟域与复位

### 9.1 模块默认域

每个 module 的 `ModuleDef` 在记录时**烘焙**一个 `ClockDomain`：未显式指定即为 `defaultClockDomain`（clk / reset / Async / RisingEdge / ActiveHigh）。模块全部表达式共享 `head.cd`。

### 9.2 显式模块域

```typort
def myCd: ClockDomain = ClockDomain.mk "myclk" "myrst" Async RisingEdge ActiveHigh
module foo[myCd] { ... }        // 首个方括号参数 = ClockDomain
println(moduleTreeVL(foo.create[myCd].tree))
```

域配置决定 Verilog：Async + init → `always @(posedge clk or posedge reset) if (reset) ...`；ActiveLow → `negedge rst_n` / `!rst_n`；Sync → 复位沿不进敏感表。

### 9.3 每寄存器域与跨时钟域

- 寄存器工厂带 Cd 变体：`autoUIntRegCd(w, cd)`、`autoBoolRegInitCd(v, cd)` 等（Expr 变体 `createRegWidthCd` / `createRegWidthInitCd`）；Verilog 生成按域分 always 块并补额外 clk/reset 端口。
- `regAssignCd`（Expr 变体）：显式域时钟赋值，目前**仅库内部使用**（hdl-crossclock），无用户语法——用户跨域惯用法是"在对应工厂里建寄存器 + 普通赋值"。
- 跨时钟域原语（`hdl-crossclock.typort`，已实现）：`bufferCCUInt/Bits/Bool`（默认 2 拍）、`bufferCC*Cd`（指定目标域）、`pulseCCByToggle`、`ccByToggleUInt`、`readSyncCCUInt[depth]`、`streamFifoCC`（example 21）。
- 旧 gap 表"readSyncCC 与 readSync 相同 / BufferCC 缺失"已过时：`Mem.readSyncCC` 仍无同步器，但库级同步器全套可用。

---

## 10. LSP / 自检用户可见面

### 10.1 诊断形态

全部为 **WARNING**（阶段 1，跑过回归语料后再逐条升级）。来源两条管道：HDL 规则（typort 自检，§10.2）与 Verilog 兼容层检查（§10.4）。

### 10.2 警告规则表（hdl-check.typort）

| 代码 | 一句话规则 |
|------|-----------|
| HDL001 | 信号被读取但从未被驱动（且不是 input/inout 端口、mem 或 output 端口） |
| HDL002 | 声明后从未被读取（死信号/未用输入/死 mem；时钟与复位名豁免） |
| HDL003 | output 端口（含 output reg）从未被驱动 |
| HDL004 | 信号宽度不是落地数（frozen width）——Verilog 中退化为 1 位（typeclass Nat 参数 bug 的可见化） |
| HDL010 | 同一信号多次无条件赋值 |
| HDL011 | 同一信号无条件与条件赋值混合（assign + always 冲突） |
| HDL012 | 同一信号组合与时钟赋值混合 |
| HDL013 | 寄存器被多个时钟域驱动 |
| HDL020 | 父模块驱动子模块的 output 端口 |
| HDL021 | 父模块读取子模块的 input 端口 |
| HDL022 | 实例端口未连接 |
| HDL023 | 模块驱动自己的 input 端口 |
| HDL024 | `instanceWithPorts`（原始端口串）绕过全部检查 |
| HDL025 | 连接的端口在子模块上不存在 |

实现细节：声明 vs 引用是**结构判定**（语句位 create* = 声明，嵌套 create* = 读取）；同结构语句去重（exprKey）；同名 wire 与端口并存时**端口优先**、遮蔽 wire（与生成器一致）；模块端口表 `ModulePortTable` 全局共享供父模块检查子模块方向。

### 10.3 LSP 集成

- 宏展开信息（`MacroExpansionInfo`）使 hover/goto-definition 锚定到 `when`/`Expr` 宏定义（`macro_goto_tests.rs`）。
- `BindingName` 命名机制让 def 体内 `let c = counter(8)` 正确命名（裸调用工厂才报诊断）。
- 诊断排水在每次 decl infer 后进行（per-file seen-set 去重，重放不重复上报）。

### 10.4 Verilog 兼容层（M1-M3 已实现）

常用 Verilog 语法可直接写在 `.typort` 文件里（module 宏 Verilog 臂 + `VExpr` 语句表）：ANSI 端口头/`endmodule`、`wire/reg [msb:lsb]`、`assign`、`if/else`、`begin/end`、`always @(posedge clk [or negedge rst_n])`、`always @(*)`、`case/endcase`、位选/部分选（读写两侧）、拼接 `{a,b}`、归约 `&|^`、sized 字面量、子模块实例化 `.port(sig)`（方向自动判定）。折叠端口：`input clk`/`reset`/`rst_n`（→ ActiveLow）成为真实端口并折叠进 ClockDomain。兼容层专用检查：

| 代码 | 一句话规则 |
|------|-----------|
| HDV001 | `always @(posedge ...)` 的时钟/复位实参必须与折叠的 `input clk`/`reset`/`rst_n` 一致 |
| HDV002 | reg 在 `always @(*)` 内被赋值——按组合驱动处理（发射 assign）并提示 |
| HDV003 | 端口方向串非法（期望 input/output/inout） |

完整映射表与未覆盖项（parameter 头/for/initial/generate/$display/延迟）：`docs/verilog-compat.md`。

---

## 11. 待定项决策记录（理由与影响面）

> 每项：一行决策 → 理由 → 影响面。"已定（实现先于文档）"指实现已隐性定案、本文追认。

### #1 when 方案 A（链式）vs C（块风格）

**决策：方案 C 块风格为唯一形态；方案 A 不做。**（已定，实现先于文档）

- 理由：块风格经 `Expr` 宏逐语句转写，与"每条赋值独立记录完整条件、生成独立 if"的树形模型天然契合；链式 `.elsewhen()` 需要 `WhenBlock[T]` 中间类型与表达式语义，与 #2（when 非表达式）互斥，且会让"整链共享一个 WhenStack 层"的否定累积机制复杂化。hdl-design-discussion §E1 记录的"SpinalHDL 用户熟悉"不构成收益——SpinalHDL 的链式本质也是块语义。
- 现状收敛：两种**实际形态**（Expr 宏 when / standalone when）转写逻辑逐字相同、独立维护两份；收敛方式不是合并实现（宏机制差异所致），而是规范上明确：形态一只用于语句位，形态二只用于裸 def 体/裸 case 臂，用户写法统一为块风格。
- 影响面：无用户可见变化；`hdl-design.md` §二、`hdl-design-discussion.md` §E1 的"待定"就此关闭。

### #2 when 是否作为表达式（取末行值）

**决策：否。when 恒为 `Unit` 语句。**（已定，实现先于文档）

- 理由：when 的作用是把赋值条件化（副作用落树），不是求值；`Expr` 宏 when 臂无值尾，standalone 宏补 `; unit` 值尾恰是为了让裸位语法成立而**钉死类型为 Unit**。末行取值与"body 是语句序列、赋值各自成节点"的树形不兼容。
- 取值需求由 `cond.mux(a, b)` / `cond ? x : y` 覆盖（§6.3）；多路值选择用 `switch` 语句或 `priorityMux`。
- 影响面：`let x = when ...` 不可写（parser 拒绝）；未来若要表达式化，需要重做 #1 的树形假设——不建议。

### #3 方向元数据存储位置（Expr 级 vs 类型级）

**决策：Expr 级。**（已定，实现先于文档）

- 理由：方向编码在 Expr 变体（`createIn/createOut/createInOut` + 全部 Width/Reg 变体），类型（`UInt[w]` 等）保持 `{name, zz_expr}` 纯净。类型级包装（`Directed[T]`）会污染全部运算符 impl 的 Self 匹配（`Add[UInt[w], UInt[w]]` 等数百 impl 都要面对方向参数），且 `isInputPort`/`isRegExpr` 等判定在 Expr 级是纯结构匹配。
- Bundle 侧同理：derive 工厂 + `asMaster`/`asSlave` 用 `in()/out()` 恒等函数 + 同名重建信号实现方向，落点仍是 Expr 级。
- 影响面：方向不可从类型读出（`UInt[8]` 不携带方向）——需要方向信息处（`:=` 跳过 input LHS、HDL020-021 端口方向检查）全部走 Expr 判定，已是现状。

### #4 `pull()`（跨层级信号展开，hdl-redesign-plan §8）

**决策：暂不做；深层访问用中间模块端口手动提升。**（开放，推荐维持挂起）

- 理由：`subSignal` 句柄是一层的（父↔子直连），多层 `outer.inner.signal` 需要"端口提升链"的代码生成支持（中间模块逐级加透传端口）；hdl-redesign-plan §8 本身标注"设计暂定，后续实现"，且 Verilog 层次习惯上中转端口本就显式。
- 推荐方案（若将来做）：宏级语法糖——`outer.inner.sig.pull` 展开为"沿路径逐层声明 output 中转端口 + 连接"，纯宏实现不碰 Rust；不引入新 Expr 变体。
- 影响面：无（现状即可写分层设计，只是多几行端口声明）。

### #5 RegInit 函数式 API

**决策：不做独立 API；现有宏 + 工厂 + regNext 已覆盖。**（开放，推荐不做）

- 理由：SpinalHDL `RegInit(t)` 的能力在本语言拆在三处：宏 `reg x = T[w] init v`（体内声明）、`auto*RegInit(w, v)` 工厂族（任意位置、BindingName 命名）、`regNext/regNextWhen`（函数式延迟）。再加 `RegInit(t)` 只是别名，且函数式形态拿不到比 `[bn: BindingName]` 更好的命名来源。
- 影响面：若做，仅 `hdl-signals.typort` 增一个泛型委托（`def regInit[bn, T][r: RegInitClass[T]](t: T): T`），成本极低，收益同样极低。

### #6 常量移位 `<<`/`>>` 变宽 vs 保持宽度

**决策：保持宽度（现状）；与 SpinalHDL 的偏差正式记录、不迁移。**（已定，实现先于文档）

- 理由：与变量移位 `|<<`/`|>>` 语义一致；与 Verilog 赋值上下文的宽度习惯吻合（LHS 宽度决定上下文）；"Nat 常量移位量悄悄改结果类型"在依赖类型语言里意味着每个移位表达式都要重推类型，收益（少写一个 `##`）不抵认知成本。需要扩位时语义显式：`x +^ y`、`x ## y`、`x.expand`。
- 迁移成本（若改 SpinalHDL 变宽语义）：`examples/hdl/03`、`14` 等所有常量移位点结果类型全部要改；`|<<` 与 `<<` 的职责要重新切分（SpinalHDL 的 `<<` 变宽、`|<<` 保宽、`<< UInt` 保宽三态）；`hdl-ops.typort` 全部移位 impl 重写。估计为一次破坏性大改，无对应需求牵引。
- 影响面：`docs/spinalhdl-gap.md` §2/§8 的偏差记录长期有效。

### #7 `/` `%` 位宽语义 与 `+|` `-|` 饱和运算

**`/` `%`：已实现，语义 = SpinalHDL。**（已定，实现先于文档）

- `/`：`UInt[w]/UInt[w] → UInt[w]`（宽 = w(x)）；`%`：等宽操作数 → `UInt[w]`（等宽下即 SpinalHDL 的 `min(w(x), w(y))`）。Nat 字面量除数有独立 impl（`a / 3`）。Verilog `/`/`%` 直接可综合。
- `docs/spinalhdl-gap.md` §2 的"`/` `%` ❌ 缺失"已过时。

**`+|` `-|` 饱和：暂不做。**（开放，推荐暂缓）

- 理由：新增记号要动 parser/宏表/宽度类型，而饱和路径（DSP/饱和累加）在当前示例与复刻组件中零出现；饱和可用 when + 比较手写（`when sum > max { sum := max } otherwise { sum := sum + y }`）。
- 推荐方案（若做）：以 trait 方法（如 `saddU(max: UInt[w])`）而非新记号实现，零 parser 改动。

### #8 muxList / priorityMux / `#*` 重复 / reversed

- **priorityMux / muxOH / ohMuxOr：已实现**（`hdl-utils.typort`；`priorityMux(sel, vals, dflt)` 用 `Vec[T] width` 承载候选，dflt 兜底）。gap §2"缺 muxList/priorityMux"部分过时。
- **muxList（switch 值选择 `x.muxList(...)`）：不做。** 用 `switch` 语句（语句位选信号）或 `vecAtUInt`（Vec 动态索引 mux 链）覆盖；表达式位多路选择本语言倾向显式 mux 链。
- **`#*` 重复拼接：不做。** for 展开 + `##` 链或 Vec cons 手写等价物；新记号需 parser/宏支持，无需求。
- **reversed：已实现为 `reverse`**（Bits/UInt，`hdl-utils.typort`；命名对齐函数式习惯，与 SpinalHDL 方法名不同）。

### #9 UFix/SFix 定点数排期

**决策：远期（三期），当前不做。**（开放，推荐排期如下）

- 排期建议：硬件 Enum（`docs/hdl-enum-design.md`，一期缺口中影响状态机建模最大）→ Stream/FSM 完整化（`docs/hdl-stream-fsm-design.md`）→ BlackBox/仿真（`src/sim` + designManifestVL 已有地基）→ **UFix/SFix**。
- 理由：定点数需要类型层面 Nat 有理缩放（Q(w, e)）与全套运算符实现，工程量数倍于 Enum/Stream，而用户可先用 `UInt` + 显移位缩放（`x * 3` / `x >> 4`）覆盖原型需求；SpinalHDL 自己也把 FixData 归为可选生态。

### #10 拼接 / 切片运算符终态

**决策：`##` 是唯一拼接记号；切片 = `slice[hi, lo]` + 糖 `a[hi:lo]`、`a[N]`；不引入更多 Verilog 风格运算符。**（已定，实现先于文档）

- 理由：`a[hi:lo]` 已是 parser 对 `slice[hi, lo]` 的 part-select 脱糖（`src/L13_namespace/parser/mod.rs` 后缀 `[` 分支），Verilog 兼容层与 typort 风格共享同一通道；再引入 `downto`/`to` 方向语义只会带来两套索引方向约定。位选 `a[N]` 是隐式参数方括号的自然结果。
- 影响面：`hdl-design.md` §三"拼接/切片：待定"就此关闭；`docs/hdl-design-discussion.md` §I1 的 `x(7 downto 3)` 风格不做。

### #11 补充记录（实现中发现、旧文档未列的决策）

| 项 | 决策 |
|----|------|
| 三目 `? :` | **已实现**：parser 直接脱糖为 `.mux` 方法调用（hdl-design 只记录了 `.mux` 方案） |
| `cast` 证明形式 | **Eq 证明等宽 cast**（core/eq.typort `Cast` trait）；hdl-design 的"`Le` 证明 cast"已删除 |
| 字面量宽度检查 | **仍开放**：`natFitsIn` 已定义但 `Into` impl 未接入；推荐在 `Into[UInt[w]] for Nat` 走 typeclass 约束时补 `natFitsIn` 检查（需编译器支持编译期 Nat 谓词） |
| switch 穷尽性 | **已放宽 + 显式检查**（2026-09-26）：no-default switch 合法（纯 when 链）；枚举选择子经 `switchFinalEnum` 显式调用报 HDL040 WARNING（hdl-enum.typort，`docs/hdl-enum-design.md` §4.7）；`is Enum.ELEM { }` 形态的自动记录未接线（`$val:raw` matcher 把点分 is 值当 apply-block 捕获），自动检查留二期 |
| Vec（HVec） | 动态索引 `vecAtUInt` 已实现；fill 工厂/批量 `:=` 未实现，归入二期 Stream/FSM 波次评估 |
| `assert` 断言 | **未实现**（gap §7 第 5 条未落地）；二期随自检阶段 2-4 评估 |
| `ClockArea` | **未实现**；模块级域 + 每寄存器域工厂已覆盖现有多时钟需求 |
| `moduleVL` | 不存在；验收 API 为 `moduleTreeVL` / `allModulesVL` / `designVL` / `designManifestVL` |

---

## 12. 范围边界（二期大特性，本文不展开）

以下特性**不在本规范覆盖范围内**，各自有设计稿，实现后应回填本文对应章节：

| 特性 | 现状 | 设计文档 |
|------|------|----------|
| 硬件 Enum（SpinalEnum：编码/位宽、`===` 硬件比较、枚举 switch、`reg [1:0] state` 生成） | 未实现（L07 enum 是纯 elaboration 期数据） | `docs/hdl-enum-design.md`（2026-09-26 设计稿） |
| 自检阶段 2/3/4（组合环、latch/位区间、CDC） | 阶段 1 已实现（§10.2） | `docs/hdl-selfcheck-phase234-design.md`（2026-09-26 设计稿） |
| Stream/Flow/Fragment 完整握手 + FSM | `Stream[T]`/`Flow[T]` struct 与 UInt/Bits/Bool 全套流水原语已实现（hdl-stream.typort）；FSM 仅占位 | `docs/hdl-stream-fsm-design.md`（2026-09-26 设计稿） |
| BlackBox 代码生成 | 语法占位 stub（hdl-bus.typort），无代码生成；仿真走外部 Verilog + `designManifestVL` | `docs/hdl-blackbox-sim-design.md`（2026-09-26 设计稿，含 assert 与仿真集成路线） |
| UFix/SFix 定点数 | 未实现 | 见 §11 #9 排期建议 |

---

## 13. 文档体系索引（HDL 相关文档地图）

> 阅读顺序建议：新读者按 ①→②→③ 建立语法与语义全景；追溯某个决策的来龙去脉再查④⑤；做二期特性时按各自设计稿入口进入。

| 文档 | 性质 | 内容与现状 | 阅读建议 |
|------|------|-----------|----------|
| **docs/hdl-language-spec.md**（本文） | **权威规范** | 以实现为准的全量语法 + 待定项决策 | 唯一需要精读的入口 |
| docs/hdl-syntax.md | **过时** | 早期目标语法（Component/val/Reg() 风格，与现状 `module`/`reg` 宏不符）；其 §12 路线图已全部完成或变形 | 仅作历史参照；被本文取代 |
| docs/hdl-design.md | 半过时（设计决策存档） | 早期设计决策 + L13 底座架构总结；"待定"项以本文 §11 为准；Expr/宏描述已过时 | 查底座（Tm/Val/Cxt/双向检查）时读 §底座；语法部分勿引用 |
| docs/hdl-design-discussion.md | 讨论存档 | 设计讨论过程（A-K 议题）；只取"已定"结论，且以本文 §11 校正 | 追溯决策来龙去脉时按议题号查阅 |
| docs/hdl-redesign-plan.md | 现状记录（已实现） | `module` 宏 → struct+create+tree 的重构方案（2026-08 完成）；§8 pull() 未实现 | 理解宏展开形态读 §1-§5；§8 已被本文 #4 决策接管 |
| docs/module-redesign-analysis.md | 现状记录（前置分析） | module 宏摊平链方案（C2）的性能与类型分析 | 宏实现细节/性能问题排查时读 |
| docs/task2-module-macro-notes.md | 存档（未合并尝试） | 上一次重构失败的教训（性能退化、debug 栈溢出） | 仅考古 |
| docs/hdl-def-body-hardware-statements.md | 现状记录（2026-08-27） | def 体/case 臂硬件语句的实现、副作用重放机制、三个底层坑 | 写 def 内硬件/排查"信号没落树"必读 |
| docs/for-hdl-blocker.md | 现状记录（已解决） | for 展开的 dependent-meta 泄漏与修复 | for 相关 bug 排查 |
| docs/hdl-selfcheck-design.md | 现状记录（阶段 1 已实现） | 自检框架架构、编号段位、排水管道 | 对照 §10.2 规则实现 |
| docs/hdl-selfcheck-phase234-design.md | **设计稿（未实现）** | 组合环 / latch·位区间 / CDC 规则设计（2026-09-26） | 做自检阶段 2-4 的入口 |
| docs/hdl-enum-design.md | **设计稿（未实现）** | 硬件 Enum 全案（2026-09-26） | 做硬件 Enum 的入口 |
| docs/hdl-stream-fsm-design.md | **设计稿（未实现）** | Stream/Flow/Fragment 完整化 + FSM（2026-09-26） | 做握手/状态机的入口 |
| docs/spinalhdl-gap.md | 半过时（差距对照） | SpinalHDL 能力对照表；§2 部分、§7 清单、§8 若干条目已被后续实现覆盖（本文 §0/§11 逐项校正） | 对照 SpinalHDL 找缺口时**必须**先过本文 §11 |
| docs/spinalhdl-lib-replication.md | 计划（进行中） | lib 复刻波次表 + 语言限制 + 仿真策略（外部 Verilog） | 复刻新组件前读 |
| docs/verilog-compat.md | 现状记录（M1-M3 已实现） | Verilog 兼容层完整映射表与未覆盖项 | 写 Verilog 风格代码/扩 VExpr 时读 |

---

## 附录 A：速查卡（cheatsheet）

```typort
// ── 模块 ─────────────────────────────────────────────
module name[w: Nat]                      // 参数化
    input a = UInt[w]                    // 端口区（output reg 在最前；Bool 端口在后）
    output reg q = UInt[8] init 0        // 强制 output reg + 异步复位
    inout io = UInt[8]
{
    let x = a + b                        // 表达式 let → 命名 wire
    let w2 = UInt[8]                     // 声明 let → wire
    reg r = UInt[8] init 1               // 寄存器（体内形态）
    r := x                               // reg 赋值 → 时钟块
    x := r                               // 组合赋值
    when c { ... } elsewhen c2 { ... } otherwise { ... }
    switch sel { is 0 { ... } default { ... } }
    for i in 0 until 4 { ... }           // x → x_i
    let u = child.create[8]              // 子模块实例
    u.pin := a                           // 子端口连接
}
println(moduleTreeVL(name.create[8].tree))

// ── 工厂 ─────────────────────────────────────────────
// let n = autoUInt(w) / autoUIntInput(w) / autoUIntOutput(w) / autoUIntInOut(w)
//         autoUIntReg(w) / autoUIntRegInit(w, v) / autoUIntOutReg(w)
// let n = regNext(sig) / regNextWhen(sig, en) / counter(w) / counterInc(w, en)
// let m = memUInt(w, words);  m.write(a, d, en);  m.readSync(a) / m.readAsync(a)

// ── 运算 ─────────────────────────────────────────────
// + - +^ -^ * / %   << >> (Nat)   |<< |>> (UInt 量)   rotateLeft/Right
// & | ^ ~   < <= > >= === =/=   andR orR xorR   ##   msb lsb a[N] a[hi:lo] slice[hi,lo]
// resize[nw]  cast(prove: Eq)  asBits asUInt asSInt asBool  abs expand neg reverse
// cond.mux(a,b)  cond ? x : y  priorityMux(sel, vals, dflt)  vecAtUInt(vec, i, dflt)

// ── 连接 ─────────────────────────────────────────────
// a := b（组合/reg 自动识别）    master <> slave（双向，跳过 input/inout）
// Bundle: #[derive(Bundle)] + impl IMasterSlave { def asMaster = ... out()/in()/inout() ... }
//         let m = Bus.create.asMaster / .asSlave
```

## 附录 B：与 SpinalHDL 的既知偏差清单

| 偏差 | 本语言 | SpinalHDL | 处置 |
|------|--------|-----------|------|
| 常量移位宽度 | `<<`/`>>`（Nat）保持宽度 | `<<(Int)` 变宽 | 记录偏差，不迁移（§11 #6） |
| SInt 乘法 | 未实现（仅 `SInt * Nat`） | `w1 + w2` | 二期随运算符补齐评估 |
| 拼接组合 | UInt/SInt 交叉组合缺 impl | 全组合 | 先 `.asBits`/`.asUInt` |
| RegInit | 无函数式 API | `RegInit(t)` | 决策不做（§11 #5） |
| pull | 无 | —（Spinal 无此概念，本语言自拟） | 挂起（§11 #4） |
| Mem.readSyncCC | 无同步器 | BufferCC 内建 | 用 hdl-crossclock 的 bufferCC*/readSyncCCUInt |
| Area | 恒等分组，无 `a.x` 访问 | Area 有字段访问 | 用 def 函数替代 |
| 命名 | `BindingName` 隐式参数（let 绑定名） | `Nameable`/`setName` | 行为等价，机制不同 |
