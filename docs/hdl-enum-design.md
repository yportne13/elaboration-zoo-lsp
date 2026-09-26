# 硬件 Enum（SpinalEnum 对应物）设计

> 状态：已实现 M1-M3（2026-09-26）。落点：`src/prelude/hdl/hdl-enum.typort`、`src/L13_namespace/parser/derive.rs`（`derive_hdlenum`）、`src/prelude/hdl/hdl-macros.typort`（无 default switch 臂）、`src/L13_namespace/hdl_enum_tests.rs`。与设计稿的偏差：① 元素复用 L07 构造子（EnumLit 包装被放弃——def 无法覆盖 L07 构造子的 decl 键）；② 穷尽性检查为显式 `switchFinalEnum` 直调 opt-in——HDL040 缺支自动上报未接线（宏臂不记录 case，见 §4.7 宏臂注释）；③ §8 验收基线中 §9 的 examples 新增用例未新增 examples 文件，改由 `hdl_enum_tests.rs` 承担；④ 示例命名避让 prelude 既有名——`State` 已被 `src/prelude/hdl/hdl-bus.typort:214` 的 `struct State[T]` 占用，全文示例统改 `FsmState`（§10-10）。原始设计稿如下（行号基于当时 master 工作树，示例名已按 ④ 统一为 `FsmState`）。

---

## 1. 背景与现状

### 1.1 缺口

- 语言已有 **L07 普通 enum**（和类型，`src/prelude/hdl/hdl-core.typort:71-92` 的 `ClockEdge`/`ResetPolarity`/`ClockDomainConfig` 即用例），但它是**纯 elaboration 期数据**：match 在 elaboration 期求值，与硬件位向量无关。
- HDL 硬件类型只有 `Bool/Bits/UInt/SInt`（`hdl-types.typort:66-165`）。没有：编码/位宽推导、枚举信号的硬件 `===`、switch over 枚举、`reg [1:0] state` 式的状态机建模。
- switch 现状（`hdl-macros.typort:203-225`）：基于 `===` 展开为 when 链，`is` 值只支持 Nat 字面量或信号，**无 default 臂不可用**（两个臂都要求 `default`），无穷尽性概念。
- 自检框架（`hdl-check.typort`，HDL001-025）按名字级 `SigKind`（kWire/kIn/kOut/kInOut/kReg/kOutReg/kMem，`hdl-check.typort:71-79`）分类，尚无 enum 概念。

### 1.2 SpinalHDL 参考事实（来自 spinalhdl-ref 使用点）

参考树只有 `lib/`（无 core/），从使用点可还原 API 形态：

- 声明：`object UartCtrlTxState extends SpinalEnum { val IDLE, START, DATA, PARITY, STOP = newElement() }`（`spinalhdl-ref/lib/src/main/scala/spinal/lib/com/uart/UartCtrlTx.scala:8-10`）。
- 编码参数：`object UartParityType extends SpinalEnum(binarySequential) { val NONE, EVEN, ODD = newElement() }`（`.../Uart.scala:22-24`）——编码挂在 **enum 定义**（默认编码），也可 per-craft 指定；内建编码对象为 `binarySequential` / `binaryOneHot` / `sequential` / `native`。
- 硬件信号：`val state = RegInit(IDLE)`（`UartCtrlTx.scala:47`）——craft 类型信号，复位到枚举字面量。
- 比较：`parity === UartParityType.ODD`（`UartCtrlTx.scala:66`）——craft 与枚举字面量的硬件比较。
- switch：`switch(state) { is(IDLE){...} is(START){...} ... }`（`UartCtrlTx.scala:56-98`）。
- SpinalHDL 的 Verilog 输出**不生成 localparam**，编码后的字面量直接内联。

### 1.3 可复用的既有机制（本设计的支点）

| 机制 | 位置 | 对 enum 的意义 |
|---|---|---|
| `#[derive(...)]` 注册表 | `src/L13_namespace/parser/derive.rs:9-23`（`DeriveMacro = fn(&Decl, &BundleSet) -> Vec<Decl>`）、展开入口 `src/L13_namespace/parser/mod.rs:2850-2905` | 硬件 enum 走同一条路：新增 `derive_hdlenum`，从 `Decl::Enum` 生成一组 decl。`derive_show`（derive.rs:925-963）证明 enum decl 已流入 derive 管线 |
| 点名 decl 解析 | `src/L13_namespace/elaboration.rs:2461-2497`：`Raw::Obj` 把 `A.b` 拼成完整路径查 decl 表 | `def FsmState.IDLE` / `def FsmState.craft` 这类**生成式点名 def** 可以按 `FsmState.IDLE` / `FsmState.craft` 访问（与 `AxiLite.create`、`Foo.create` 同机制） |
| 类型参数可为未在字段中出现的幻影参数 | `struct UInt[width: Nat]`（`hdl-types.typort:112-115`，width 不出现在字段中） | `EnumLit[E]` 用 E 做 phantom 实现跨 enum 类型安全 |
| 类型索引上的 def 调用 | `hdl-ops.typort:687`：`idx: UInt[log2Up n]` | `EnumCraft[FsmState, encWidthOf e n, encCodeOf e]` 合法 |
| 信号模型全部走 `create*` Expr 变体 | `hdl-core.typort:96-153` | 编码降级后 craft 信号就是 `createWidth/createRegWidth`，Verilog/自检零改动 |
| 自动命名 | `bn: BindingName`（`hdl-core.typort:9-12`）+ `newUInt`（`hdl-signals.typort:352-354`） | `let cur = FsmState.craft` 自动得名 "cur" |
| trait 首匹配注册序 | `hdl-types.typort:242-247`（LetNamed 兜底实例 "MUST stay last"） | switch 检查的兜底 impl 必须最后注册 |
| 自检上报通道 | `report_check_issue(code, module, sig, msg)`（`hdl-check.typort:601-603`）；运行中上报先例 `pickAssign` 的 HDV002（`hdl-core.typort:706-711`） | 穷尽性检查 HDL040 在 elaboration 期直接上报 WARNING |

---

## 2. 目标与非目标

### 目标（一期）

1. `#[derive(HdlEnum)] enum FsmState { IDLE RUN DONE }` 声明硬件 enum；元素为 elaboration 期纯值，**带 phantom 类型参数**阻止跨 enum 混用。
2. 四种编码 binary / sequential / native / oneHot：决定位宽与字面量编码值；编码选择编译进 craft 类型索引。
3. craft 信号：wire 工厂、reg/regInit 工厂（异步复位）、`===`/`=/=`（craft↔craft、craft↔元素）、`:=`（Into 隐式转换）、mux、`asUInt`/`asBits`。
4. switch over enum：现有宏臂原样工作（`===` 分派）；新增**无 default 臂**与**穷尽性检查**（HDL040 WARNING，缺哪个元素点名报出）。
5. Verilog 生成**零改动**（编码降级方案，见 §5）；自检框架零特判（见 §7）。

### 非目标（记录在案）

- `encNative` 的**显式元素值**（SpinalHDL `newElement(42)`）——需要带 payload 的构造子，远期。
- enum 类型作为 **module 端口 / Bundle 字段 / inout**（一期用 `UInt[w]` 端口 + `asUInt` 过渡）——二期（§8 M4）。
- `is(A, B)` 多值分支（SpinalHDL 支持）——二期宏臂扩展。
- FSM 库（spinal.lib.fsm）、EnumCraft 的 GrayCode 等自定义编码——远期。
- 跨编码自动重编码比较（SpinalHDL 允许）——不做，宽度不同即类型不同（§7 偏差 3）。

---

## 3. 语法草案

### 3.1 声明（复用 L07 enum + derive，不新增关键字）

```typort
#[derive(HdlEnum)]
enum FsmState {
    IDLE
    RUN
    DONE
}
```

- L07 语法原样：无名参构造子、空格分隔（同 `enum ClockEdge { RisingEdge FallingEdge }`，`hdl-core.typort:71-74`）。
- **为什么复用 L07 enum 而不是新语法**：
  - 备选 A「新增 `hdlenum` 关键字/语句」：要动 parser 与 L07 语义边界，收益仅是省一个属性。
  - 备选 B「纯 typort `macro_rules hdlenum`」：宏可以生成多条 `def`（模块宏先例），但 (1) 宏展开到顶层多 decl 的支持未验证；(2) `FsmState.craft` 的返回类型需要 per-enum 的**具体宽度 Nat**，宏无法按元素个数算 `log2Up`（macro_rules 不能计数），只能退到运行期查表，类型不精确；(3) LSP hover/goto 对宏产物支持弱。
  - 备选 C「Rust parser 内建 enum 声明」：过重。
  - **选定**：`Decl::Enum` + derive 注册（derive.rs:18-23 加一行），生成物是普通 decl，hover/goto/补全全部走既有机制。derive 校验：全部构造子必须无参，否则经 `expand_derives` 的错误通道（`parser/mod.rs:2850` 返回 `Vec<IError>`）报解析期错误。
- 与 L07 的关系：**复用声明、注入语义**。L07 enum 本身保留——元素构造子仍是纯 elaboration 值，可参与普通 match（FSM 的纯逻辑译码等）；硬件语义全部由 derive 生成的补充 decl 承载。

### 3.2 使用形态（一期全景）

```typort
module fsm {
    input start = Bool
    input doneIn = Bool
    output busy = Bool
    output outState = UInt[2]

    let st = FsmState.regInit(FsmState.IDLE)     // 状态寄存器，异步复位到 IDLE（编码后 0）
    let nxt = FsmState.craft                  // 组合信号，默认 binary 编码，宽 2

    switch st {                            // 无 default：穷尽 → 不报 HDL040
        is FsmState.IDLE { when start   { st := FsmState.RUN  } }
        is FsmState.RUN  { when doneIn  { st := FsmState.DONE } }
        is FsmState.DONE { st := FsmState.IDLE }
    }
    nxt := sel.mux(st, FsmState.IDLE)         // mux（sel 为 Bool 时省略）
    busy := st === FsmState.RUN               // 硬件比较
    outState := st.asUInt
}
```

oneHot：`let c = Cmd.craftAs[encOneHot]`。**编码选择在值上（`Encoding` 构造子），编译进 craft 类型索引**（§4.3），不放 enum 类型上（L07 enum 是纯类型，不能带硬件参数；`FsmState[oneHot]` 形态要求新语法）。

---

## 4. 语义规则

### 4.1 元素（EnumLit）——elaboration 期纯值，不是类型

```typort
struct EnumLit[E: Type 0] {
    enumName: String     // "FsmState"，用于 switch 穷尽匹配与 localparam 命名
    elemName: String     // "IDLE"
    elems: List[String]  // 本 enum 全部元素名（声明序）——序数/编码值的唯一事实源
}
```

- `E` 是 **phantom 类型参数**（字段不出现，`UInt[width]` 先例）：`state === Color.RED` 因 E 不匹配被类型系统拒绝。
- derive 生成（等价 typort 源，实际由 Rust 直接构造 Raw AST，参照 `derive_bundle` 的 `build_*` 系列手法）：

```typort
def FsmState.IDLE: EnumLit[FsmState] = EnumLit.mk[FsmState]("FsmState", "IDLE",
    lcons ("IDLE") (lcons ("RUN") (lcons ("DONE") lnil)))
def FsmState.RUN:  EnumLit[FsmState] = EnumLit.mk[FsmState]("FsmState", "RUN",  <同表>)
def FsmState.DONE: EnumLit[FsmState] = EnumLit.mk[FsmState]("FsmState", "DONE", <同表>)
def FsmState.count: Nat = 3
```

- 元素**序数**不在宏展开期计算（macro_rules 不能计数），而是携带元素名 + 全元素表，用时由纯函数查表：

```typort
def elemOrdHelp(ls: List[String], name: String, i: Nat): Nat = match ls {
    case lnil => 0                                        // 防御：E phantom 保证不触达
    case lcons(h, t) => match str_eq(h, name) {
        case true => i
        case false => elemOrdHelp(t, name, i + 1)
    }
}
def litOrdinal[E: Type 0](l: EnumLit[E]): Nat = elemOrdHelp(l.elems, l.elemName, 0)
```

- 元素访问用限定名 `FsmState.IDLE`（SpinalHDL 靠 `import UartCtrlTxState._` 得裸名；Typort 无 import，记录为偏差 §7.1）。L07 构造子 `IDLE` 本身仍可 bare 使用（纯 match 场景）。

### 4.2 编码（Encoding）

```typort
enum Encoding { encBinary  encSequential  encNative  encOneHot }

def encCodeOf(e: Encoding): Nat = match e {
    case encBinary => 0
    case encSequential => 1
    case encNative => 2
    case encOneHot => 3
}
def encFromCode(c: Nat): Encoding = match c {          // 逆映射（从 craft 类型索引还原）
    case zero => encBinary
    case succ(zero) => encSequential
    case succ(succ(zero)) => encNative
    case _ => encOneHot
}
```

| 编码 | value(pos) | width(count) | 说明 |
|---|---|---|---|
| binary | pos | max(1, log2Up(count)) | 0,1,2,…；宽度复用 `log2Up`（`hdl-core.typort:45-49`） |
| sequential | pos | max(1, log2Up(count)) | 与 binary 同值同宽（SpinalHDL 二者在无显式元素值时不可区分，保留两个名字对齐 API，记偏差 §7.2） |
| native | pos | max(1, log2Up(count)) | 同上；作为「默认编码」的名字存在（SpinalHDL 默认 native，我们默认 binary，见 §7.2） |
| oneHot | 2^pos | max(1, count) | 1,2,4,…；2^pos 用 `pow2(n) = match n { case zero => 1; case succ(m) => (pow2 m) + (pow2 m) }`（纯加法倍增，避免依赖 Nat 乘法） |

```typort
def encWidthOf(e: Encoding, count: Nat): Nat = match e {
    case encOneHot => match count { case zero => 1; case _ => count }
    case _ => match log2Up(count) { case zero => 1; case w => w }
}
def encValueOf(e: Encoding, pos: Nat): Nat = match e {
    case encOneHot => pow2(pos)
    case _ => pos
}
```

- **编码参数的归属（决策）**：编码选择是**值**（`Encoding` 构造子），在 craft 工厂处一次性消费，消费产物是 craft 类型上的两个 Nat 索引 `(w, c)`。编码身份**不进入** `Expr`、不进入 `ModuleTree`、不进入 Verilog——所有需要编码知识的地方（字面量赋值/比较/复位值）都在 elaboration 期把「元素 + 编码」解析成 `literal(Nat)`。这是 §5「编码降级」的语义基础。

### 4.3 craft（硬件信号）

```typort
struct EnumCraft[E: Type 0, w: Nat, c: Nat] {
    name: Option[String]
    zz_expr: Expr           // 恒为 createWidth/createRegWidth/createRegWidthInit(...) 等 create* 节点
}
```

- `w` = 编码位宽，`c` = 编码码（幻影索引，用于还原编码）。同 enum 不同编码 ⇒ w 不同（oneHot vs binary 恒不同宽）⇒ 类型不同 ⇒ **跨编码混用被类型系统拒绝**；binary/sequential/native 同宽可互比（编码值一致，无害）。
- derive 生成的工厂（每 enum 一组；`bn: BindingName` 自动命名，`loopName` 处理 for 展开后缀——与 `newUInt` 同构，`hdl-signals.typort:12-14, 352-354`）：

```typort
// 默认 binary。宽 2 / 码 0 由 Rust 在 derive 期算好（元素个数已知），生成具体 Nat：
def FsmState.craft[bn: BindingName]: EnumCraft[FsmState, 2, 0] =
    let e = createSignalExpr(loopName(bn.name), createWidth(loopName(bn.name), 2));
    EnumCraft.mk(Some(loopName(bn.name)), e)

// 显式编码：宽度在类型索引上调用 encWidthOf（UInt[log2Up n] 先例，hdl-ops.typort:687）
def FsmState.craftAs[e: Encoding][bn: BindingName]: EnumCraft[FsmState, encWidthOf e 3, encCodeOf e] =
    let n = loopName(bn.name);
    let w = encWidthOf e 3;
    let ex = createSignalExpr(n, createWidth(n, w));
    EnumCraft.mk(Some(n), ex)

// 寄存器（异步复位初值 = 编码后的 Nat 字面量，走 verilogLiteral 通道，hdl-core.typort:534）
def FsmState.reg[bn: BindingName]: EnumCraft[FsmState, 2, 0] =
    ... createRegWidth(loopName(bn.name), 2) ...
def FsmState.regInit[bn: BindingName](init: EnumLit[FsmState]): EnumCraft[FsmState, 2, 0] =
    ... createRegWidthInit(loopName(bn.name), 2, literal(encValueOf(encBinary, litOrdinal init))) ...
```

- 用户书写 `let cur = FsmState.craft` / `let c = Cmd.craftAs[encOneHot]` / `let st = FsmState.regInit(FsmState.IDLE)`。
  **无需新增宏臂**：module 宏体内 `let x = <raw>` 落入 Expr 宏通用 let 臂（`hdl-macros.typort:157`）→ `nameWire` → `LetNamed` 泛型兜底实例（`hdl-types.typort:245-247`）恒等放行——craft 的 `zz_expr` 已是 create* 声明节点（`isDeclaredSignal` 判真，`hdl-core.typort:186-215`），与端口/reg 工厂产物的 let 行为一致。**因此不给 craft 定义专门 LetNamed 实例**（若定义，须赶在 `hdl-types` 的兜底实例之前注册，而 hdl-enum 晚于 hdl-types 加载，必然被兜底遮蔽——索性不做，见 §8 M1 说明）。
- 隐式编码漏写的兜底：`FsmState.craftAs` 不带 `[enc]` 时 `e` 留为 unsolved meta → `encWidthOf e 3` 卡死 → 宽度非 ground → HDL004 报警（`hdl-check.typort:605-675`）。报错不直指「漏编码」，记入 §9。

### 4.4 赋值与隐式转换

```typort
impl[E: Type 0, w: Nat, c: Nat] Data for EnumCraft[E, w, c] {
    def :=[T](that: T): Unit where T: Into[EnumCraft[E, w, c]] =
        let converted = _into_T.into;
        let assignment = pickAssign(this.zz_expr, converted.zz_expr);   // reg LHS 自动 regAssign
        let dummy_expr = createSignalExpr("", assignment);
        unit
    def expr: Expr = this.zz_expr
}

impl[E: Type 0, w: Nat, c: Nat] Into[EnumCraft[E, w, c]] for EnumLit[E] {
    def into: EnumCraft[E, w, c] =
        EnumCraft.mk(None, literal(encValueOf(encFromCode(c), litOrdinal(this))))   // ← 编码在此一次性完成
}
impl[E: Type 0, w: Nat, c: Nat] Into[EnumCraft[E, w, c]] for EnumCraft[E, w, c] {
    def into: EnumCraft[E, w, c] = this
}
impl[E: Type 0, w: Nat, c: Nat] Into[EnumCraft[E, w, c]] for MuxExpr[EnumCraft[E, w, c]] {
    def into: EnumCraft[E, w, c] =
        EnumCraft.mk(None, Expr.mux(this.condExpr, this.trueVal.zz_expr, this.falseVal.zz_expr))
}
```

- `:=` 复制 `Bits` 的实现形状（`hdl-types.typort:101-108`）；`pickAssign`（`hdl-core.typort:697-713`）自动区分组合/时钟赋值——`st := FsmState.RUN` 落在 reg 上即 `regAssign`，`when` 内自动条件化（WhenStack 机制原样生效）。
- `Into` 即 SpinalHDL「元素字面量随 craft 编码自动重编码」的对应物：编码发生在 elaboration 期赋值点。

### 4.5 硬件比较

```typort
impl[E: Type 0, w: Nat, c: Nat] Equal[EnumCraft[E, w, c], Bool] for EnumCraft[E, w, c] {
    def ===(that: EnumCraft[E, w, c]): Bool = Bool.mk(None, binary(this.zz_expr, "==", that.zz_expr))
    def =/=(that: EnumCraft[E, w, c]): Bool = Bool.mk(None, binary(this.zz_expr, "!=", that.zz_expr))
}
impl[E: Type 0, w: Nat, c: Nat] Equal[EnumLit[E], Bool] for EnumCraft[E, w, c] {
    def ===(that: EnumLit[E]): Bool =
        let lit: EnumCraft[E, w, c] = that.into;
        Bool.mk(None, binary(this.zz_expr, "==", lit.zz_expr))
    def =/=(that: EnumLit[E]): Bool =
        let lit: EnumCraft[E, w, c] = that.into;
        Bool.mk(None, binary(this.zz_expr, "!=", lit.zz_expr))
}
```

- 与 `Equal[UInt, Bool]`（`hdl-ops.typort:269-281`）同形。生成 `binary(==/!=)` 节点 → Verilog `(st == 1)`。
- 类型安全：craft↔craft 要求同 E、同 w；craft↔lit 要求同 E（phantom）。**跨 enum、跨宽度（编码）比较都是类型错误。**

### 4.6 转换

```typort
impl[E: Type 0, w: Nat, c: Nat] EnumCraft[E, w, c] {
    def asUInt: UInt[w] = UInt.mk(None, this.zz_expr)     // 同 expr，零成本（hdl-ops.typort:575-584 同法）
    def asBits: Bits[w] = Bits.mk(None, this.zz_expr)
}
```

- 反向 `UInt → craft` 由 derive 生成 `def FsmState.fromUInt(u: UInt[2]): EnumCraft[FsmState, 2, 0]`（无检查重解释，SpinalHDL 语义；二期，§8 M4）——放 derive 是因为返回类型需要具体 w，且 E 无法从 UInt 推断。

### 4.7 switch 与穷尽性检查

**is 接受枚举元素（零改动）**：现有 switch 宏臂（`hdl-macros.typort:209-225`）把每个分支转成 `($sel === $val)` —— `$val` 为 `FsmState.IDLE` 时分派到 §4.5 的 craft↔lit `===`，`$val` 为 Nat 时仍是旧路径。**语法不变**：`is FsmState.IDLE { ... }`（现有 `is` 不带括号，与 `is 0 { ... }` 一致）。

**穷尽性检查（HDL040，新增）**：枚举元素集合在 elaboration 期完全已知——这是与 Nat switch（值域未知）的本质差异，值得检查。设计：

1. is 值统一擦除为 head 描述（宏无法按类型分支，用 trait 首匹配分派，兜底实例最后注册）：

```typort
enum SwitchHead {
    shNat(v: Nat)
    shEnum(enumName: String, elemName: String, elems: List[String])   // elems 随 lit 携带
    shOther                                                            // 信号等复杂 is 值
}
enum SwitchCases {
    scEmpty
    scCons(head: SwitchHead, rest: SwitchCases)
}

trait SwitchMark[T: Type 0] { def mark(v: T): SwitchHead }
impl SwitchMark[Nat] for Nat { def mark(v: Nat): SwitchHead = shNat(v) }
impl[E: Type 0] SwitchMark[EnumLit[E]] for EnumLit[E] {
    def mark(v: EnumLit[E]): SwitchHead = shEnum(v.enumName, v.elemName, v.elems)
}
impl[T: Type 0] SwitchMark[T] for T { def mark(v: T): SwitchHead = shOther }   // 兜底，必须最后注册

trait SwitchFinal[Sel: Type 0] { def finish(sel: Sel, cases: SwitchCases, hasDefault: Boolean): Unit }
impl[E: Type 0, w: Nat, c: Nat] SwitchFinal[EnumCraft[E, w, c]] for EnumCraft[E, w, c] {
    def finish(sel: EnumCraft[E, w, c], cases: SwitchCases, hasDefault: Boolean): Unit =
        switchFinalEnum(sel, cases, hasDefault)
}
impl[Sel: Type 0] SwitchFinal[Sel] for Sel {
    def finish(sel: Sel, cases: SwitchCases, hasDefault: Boolean): Unit = unit    // UInt/Bool：值域未知，不检查
}

def switchHeadOf[T: Type 0][m: SwitchMark[T]](v: T): SwitchHead = m.mark(v)
def switchExhaustiveCheck[Sel: Type 0][f: SwitchFinal[Sel]](sel: Sel, cases: SwitchCases, hasDefault: Boolean): Unit =
    f.finish(sel, cases, hasDefault)
```

2. 检查体（纯名字集合运算；构造子嵌套模式不可用，逐层分解——`hdl-verilog.typort:1096-1097` 的先例注释）：

```typort
def scUniverse(cases: SwitchCases): Option[List[String]] = match cases {     // 首个 shEnum 的 elems
    case scEmpty => None
    case scCons(head, rest) => match head {
        case shEnum(_, _, elems) => Some(elems)
        case _ => scUniverse rest
    }
}
def scCovered(cases: SwitchCases, enumName: String, acc: List[String]): List[String] = match cases {
    case scEmpty => acc
    case scCons(head, rest) => match head {
        case shEnum(n, e, _) => match str_eq(n, enumName) {
            case true => scCovered(rest, enumName, lcons(e, acc))
            case false => scCovered(rest, enumName, acc)
        }
        case _ => scCovered(rest, enumName, acc)
    }
}
def scHasOther(cases: SwitchCases): Boolean = ...   // 任一 shOther → 保守跳过
```

3. 判定与上报：`universe = scUniverse(...)`；`hasDefault = false` 且 `universe = Some(elems)` 且无 shOther 且 `covered ⊂ elems` 有缺 ⇒

```typort
let mname = headModuleDef((get_global_default("ModuleTree", ModuleTree.mk(0, nil))).data).name;  // pickAssign 同款，hdl-core.typort:708
let _ = report_check_issue("HDL040", mname, exprName(sel.zz_expr),
    "switch over enum is not exhaustive (missing: RUN, DONE) — add is-cases or a default branch");
```

（`exprName` 取自 hdl-check.typort:118-147，craft 的 `zz_expr` 是 createWidth ⇒ 得信号名。）有 default ⇒ 不检查。`universe = None`（无任何枚举 is 值）⇒ 跳过——此时 `===` 的类型检查会先硬报错。

4. 宏臂改动（`hdl-macros.typort` switch 段重写，仍是 typort 层）：

```
// 有 default（原两臂 + 检查调用；hasDefault=true）
(switch $sel:raw { is $val:raw {$( $body: Expr )*} $( is $val2:raw {$( $body2: Expr )*})* default {$( $default_body: Expr )*} }) => {
    let _ = switchExhaustiveCheck(($sel),
        scCons (switchHeadOf ($val)) $( scCons (switchHeadOf ($val2)) )* scEmpty, true);
    let _ = whenBegin(($sel === $val).expr);
    ...（其余与现臂逐字相同）...
};
// 新增：无 default 臂（现状是无 default 直接宏匹配失败；放开并对 enum 做穷尽性约束）
(switch $sel:raw { is $val:raw {$( $body: Expr )*} $( is $val2:raw {$( $body2: Expr )*})* }) => {
    let _ = switchExhaustiveCheck(($sel),
        scCons (switchHeadOf ($val)) $( scCons (switchHeadOf ($val2)) )* scEmpty, false);
    let _ = whenBegin(($sel === $val).expr);
    $( let _ = whenElseBegin(($sel === $val2).expr); $({$body2})* )*
    let _ = whenEnd(unit);
};
```

- 重复展开成嵌套 list 依靠**柯里化并列应用**：`scCons (h1) scCons (h2) scEmpty` ≡ `scCons(h1, scCons(h2, scEmpty))`（typort 应用为并列结合，`lcons a lcons b lnil` 同理）。
- 无 default 臂对 UInt switch 也生效（宏层面无类型信息；`SwitchFinal` 兜底实例对 UInt 是 unit）——这是**行为放宽**：原本无 default 的 switch 是宏匹配失败，现在合法生成 when 链；对 enum 由 HDL040 兜住非穷尽情形。
- **穷尽性是 WARNING 不是硬错误**：`report_check_issue` 通道只产 WARNING（lib.rs 按 `code|module|signal|message` 行收集，`hdl-check.typort:1-28` 头注释）。硬件语义与 SpinalHDL 一致：未覆盖值「保持原值」，由 default 缺失的 latch 风险提示承担（§9 开放问题 2）。

---

## 5. Verilog 生成

### 5.1 推荐方案：编码降级，复用既有 Expr 变体（零改动）

**结论：不新增 Expr 变体承载 enum 信号；编码在 elaboration 期降级为「宽度 + 已编码 Nat 字面量」，全部走既有变体与既有产码路径。**

| 用户构造 | ModuleTree 节点 | Verilog（既有产码函数） |
|---|---|---|
| `let cur = FsmState.craft` | `createWidth("cur", 2)` | `reg/wire [1:0] cur;`（when 驱动 → reg：`wireLineSingle` hdl-verilog.typort:447-467；`wireOrRegLine`:435-440） |
| `input p = UInt[2]`（过渡期 enum 端口） | `createInWidth` | `input wire [1:0] p;`（`portLineSingle`:375-391） |
| `let st = FsmState.reg / regInit` | `createRegWidth / createRegWidthInit(name, 2, literal(v))` | `reg [1:0] st;` + 异步复位 `st <= v;`（`collectRegLines`:482-532、`collectInitLinesCd` hdl-verilog.typort:911-948、`verilogLiteral` hdl-core.typort:534-537——只认 `literal(v)`，故 regInit 必须产 `literal` 而非 `sizedLiteral`） |
| `st := FsmState.RUN` | `regAssign(st, literal(1))`（when 包裹由 WhenStack 完成） | `st <= 1;`（`exprVL_proc` hdl-verilog.typort:131-136） |
| `st === FsmState.RUN` | `binary(st, "==", literal(1))` | `(st == 1)`（`exprVL`:217-233） |
| `outState := st.asUInt` | `assign(outState, st)` | `assign outState = st;` |

理由：

1. **字面量渲染（编码相关）发生在 elaboration 期**：`Into[EnumCraft] for EnumLit` 把元素编码成 `literal(Nat)`（§4.4），`exprVL(literal(v)) → natToDec(v)`（hdl-verilog.typort:214）直接出十进制。编码身份从此不需要在 Verilog 层存在——这是「值上编码 + 类型索引」设计的直接收益。
2. craft 在树中与 `UInt[w]` 信号不可区分，但这正是目标：**Verilog 里 enum 信号本来就是位向量**。自检、designVL/manifest、复位块、时钟推断全部免费复用。
3. 避免为每个 enum 形态（wire/reg/regInit/outReg/端口 × 4 编码）新增成套变体——那会重演 SInt 变体族（`hdl-core.typort:115-122`）的 15+ 处补臂成本（见 5.3 的实测面）。

已知限制：枚举字面量进入 `##` 拼接会是 unsized literal（IEEE 1364 禁止拼接内 unsized 常量；`catLitStr` 只处理 Bool 0/1，hdl-verilog.typort:58-62）。一期规约：**拼接前先 `asUInt`**；二期可让 `into` 改产 `sizedLiteral(v, w)`（渲染 `2'd1`，`sizedLitStr` hdl-verilog.typort:66-67），但需同步扩 `verilogLiteral`（hdl-core.typort:534 只认 `literal`）。

### 5.2 localparam（可选二期，可读性增强）

SpinalHDL 不生成 localparam，本设计一期对齐。若二期要生成：

- **命名规则**：`localparam [w-1:0] <EnumName>_<ELEM> = <value>;`，如 `localparam [1:0] FsmState_IDLE = 0;`。`<EnumName>` 是顶层唯一类型名，模块作用域内无冲突；元素名拼接保证跨 enum 不撞。
- **实现形态（推荐 B）**：
  - 方案 A「EnumRegistry 全局 + 产码期读取」：derive 生成注册调用（声明期求值，`ModuleRegistry` 先例 hdl-core.typort:646-658；`moduleDefVL` 读全局先例 designVL hdl-verilog.typort:1402）。缺陷：**无法判断某模块用了哪个 enum**（craft 在树中与 UInt 不可区分，§5.1 的代价），要么每个模块发全部 enum 的 localparam（污染），要么不做过滤（不可行）。
  - **方案 B（选定）**：新增单个声明变体 `createEnumLocalparam(enumName: String, elemName: String, w: Nat, value: Nat)`，由 craft 工厂随首个信号声明一并发射（每元素一个节点），**渲染期按 (enumName, elemName) 去重**——不需要全局状态，天然只出现在用到的模块。
- **补臂清单**（Expr 变体新增的真实成本，逐函数核实过）：
  - **编译错误面（无 `_` 兜底臂，必须补）**：`exprVL`（hdl-verilog.typort:187-279）、`exprVL_proc`（:84-175）、`exprKey`（hdl-check.typort:246-296）——共 3 处。
  - **语义面**：`createSignalExpr` 走默认臂即可插树（`hdl-core.typort:478-481`，注意 it 会被 WhenStack 包裹——localparam 节点须在语句位发射，遇 when 包裹时渲染收集不到，文档化为约束）；`collectAssignLinesFiltered`/`scanExpr` 等默认臂天然跳过；新增 `collectLocalparamLines` + `moduleDefVL` 拼接一段（hdl-verilog.typort:1222-1326 的 body 组装处）。

---

## 6. 实现落点（typort 层 vs Rust 层）

### 6.1 纯 typort 层（绝大部分）

**新文件 `src/prelude/hdl/hdl-enum.typort`**（预计 ~300 行），插入点：**`hdl-signals.typort` 之后、`hdl-utils.typort` 之前**（`src/lib.rs:1258/1259` 之间的 docs 列表加一行）。理由：依赖 `hdl-core`（Expr/create*/log2Up/WhenStack/pickAssign）、`hdl-types`（Data/LetNamed）、`hdl-ops`（Equal/MuxExpr 模式）、`hdl-signals`（`RegNext` trait，craft 的 RegNext impl 要实现它）；`hdl-check` 更早加载，其 `exprName`/`chkStrIn`/`report_check_issue` 可直接引用。hdl-macros 的 switch 新臂引用本文件函数属展开期晚绑定，但保持「先定义后引用」的文件序惯例。

内容清单：

1. `Encoding`/`encCodeOf`/`encFromCode`/`encWidthOf`/`encValueOf`/`pow2`（§4.2）。
2. `EnumLit[E]`/`litOrdinal`/`elemOrdHelp`（§4.1）；`EnumCraft[E,w,c]`（§4.3）。
3. `Data`/`Into`×3/`Equal`×2/`asUInt`/`asBits`（§4.4-4.6）。
4. `RegNext[EnumCraft[E,w,c]]` impl（mkReg/mkRegWhen，复制 `hdl-signals.typort:579-629` 形状：`createRegWidth(name, w)` + `regAssign`）→ `regNext(st)`/`regNextWhen(st, en)` 免费可用。
5. SwitchHead/SwitchCases/SwitchMark/SwitchFinal/switchHeadOf/switchExhaustiveCheck/switchFinalEnum/HDL040 上报（§4.7）。
6. `impl[w: Nat] ... ` 无需动 `UInt/Bits/SInt/Bool` 任何文件。

**`src/prelude/hdl/hdl-macros.typort`**：switch 两处现有臂前插检查调用 + 新增无 default 臂（§4.7 第 4 点）。其余宏臂不动。

### 6.2 Rust 层（最小面）

**仅 `src/L13_namespace/parser/derive.rs` 一处**：

1. `default_derive_registry`（derive.rs:18-23）注册 `"HdlEnum" → derive_hdlenum`。
2. `derive_hdlenum(decl: &Decl, _bundle: &BundleSet) -> Vec<Decl>`（预计 120-150 行）：
   - 匹配 `Decl::Enum { name, params, cases }`；要求所有 case 无字段（带 payload → 经 `expand_derives` 错误通道报「HdlEnum 构造子不能带参数」，parser/mod.rs:2850 返回 `Vec<IError>`）；空 enum 拒绝。
   - Rust 期计算 `count`、binary 宽 `max(1, log2Up(count))`、oneHot 宽 `count`、各元素编码值——**位宽与编码值在 derive 期即具体 Nat**，`FsmState.craft` 的返回类型是字面 `EnumCraft[FsmState, 2, 0]`。
   - 生成（全部是普通 `Decl::Def`，点名键 `"FsmState.IDLE"` 等经 `Raw::Obj` decl 查表解析，elaboration.rs:2461-2497；`bn: BindingName` 隐参自动填充与 `derive_bundle` 的 `TypeName.create` 同机制，derive.rs:655-670）：
     - `def FsmState.<ELEM>: EnumLit[FsmState]` × N（携带元素表）；
     - `def FsmState.count: Nat`；
     - `def FsmState.craft[bn]` / `def FsmState.craftAs[e: Encoding][bn]`；
     - `def FsmState.reg[bn]` / `def FsmState.regInit[bn](init: EnumLit[FsmState])`；
     - （M4）`def FsmState.regAs[e][bn]` / `def FsmState.regInitAs[e][bn](init)` / `def FsmState.regOut[bn]` / `def FsmState.regOutInit[bn](init)` / `def FsmState.fromUInt(u: UInt[2])`。
   - 生成体引用的全部符号（`createSignalExpr/createWidth/createRegWidth/literal/loopName/EnumCraft.mk/encValueOf/litOrdinal`）都在 prelude——**parser/elaborator/内建零改动**。

不动的 Rust 面（明确列出以示边界）：`parser_lib*.rs`（derive 属性解析已有）、`L13_namespace/elaboration.rs`（点名解析/隐式填充/trait 求解全复用）、内建操作（`create_global/change_mutable/get_global/report_check_issue` 原样）、`hdl-verilog.typort`（一期）。

---

## 7. 与 SpinalHDL 对应关系及有意偏差

| SpinalHDL | 本设计 | 说明 |
|---|---|---|
| `object X extends SpinalEnum { val A, B = newElement() }` | `#[derive(HdlEnum)] enum X { A B }` | 声明复用 L07 |
| `SpinalEnumElement[X]`（纯元素值） | `EnumLit[X]`（elaboration 期纯值）+ L07 构造子 | 元素不是类型 |
| `SpinalEnumCraft[X]`（craft 信号） | `EnumCraft[X, w, c]` | 编码进类型索引 |
| `X(binarySequential)` 默认编码 / `setDefaultEncoding` | `X.craft`（固定 binary）/ `X.craftAs[encOneHot]` | 无全局默认修改机制（全局可变默认会让类型索引依赖 elaboration 顺序，放弃） |
| `val state = RegInit(IDLE)` | `let st = FsmState.regInit(FsmState.IDLE)` | 语法形态不同，语义同（异步复位到编码值） |
| `state := START`（隐式重编码） | `st := FsmState.RUN`（Into 编码） | 编码点从 elaborate 元数据移到 elaboration 期赋值点 |
| `switch(state) { is(IDLE){...} }` | `switch st { is FsmState.IDLE { ... } }` | is 不带括号（对齐本仓既有 switch） |
| 比较自动重编码、跨编码可比较 | 同宽才可比（w/c 类型索引） | 更严格；跨宽度拒绝，同宽异码（binary/sequential/native）值一致可互比 |
| Verilog：内联字面量，无 localparam | 同（一期） | 可选二期 localparam（§5.2） |

**有意偏差（逐条）**：

1. **限定名访问**：元素用 `FsmState.IDLE`，不做 `import ... _` 裸名（Typort 无 import；且 prelude 内派生 enum 的点名 decl 会被自动别名成裸名——lib.rs:1285-1299——用户文件不受影响，但约定 derive 只在用户文件使用以免别名歧义）。
2. **默认编码 binary 而非 native**：本模型不支持显式元素值，native ≡ binary（value=position、width=log2Up），差异不可观测；保留 `encNative` 名字仅为 API 对齐。SpinalHDL 的 native 优势（允许乱值/非常量宽）依赖 `newElement(v)`，列非目标。
3. **编码身份编译进类型**：换取「跨编码混用 = 类型错误」的编译期保证；代价是失去 SpinalHDL 的跨编码自动重编码比较。需要跨编码时显式 `asUInt` 桥接。
4. **is 单值**：SpinalHDL `is(A, B)` 多值分支暂不支持（现有 Nat switch 同为单值，一致性优先）。二期可加 `,` 分隔多值臂（展开为 `c1 || c2` 单条件）。
5. **穷尽性检查是超集**：SpinalHDL switch 不做穷尽检查；HDL040 是本设计附加能力（枚举值域已知）。
6. **元素双重身份是超集**：L07 构造子仍可 bare 用于 elaboration 期 match（SpinalHDL 元素无法参与 Scala match 的硬件语义），FSM 纯逻辑译码免费获得。

---

## 8. 分阶段实施计划

### M1 — 核心类型与比较（typort ~200 行 + derive ~100 行）

- hdl-enum.typort：Encoding 系、EnumLit/EnumCraft、Data/Into×3/Equal×2/asUInt/asBits。
- derive_hdlenum：元素 defs + `count` + `craft`/`craftAs`。
- 验收：§9.1、§9.2。
- 说明：**不**为 craft 写 LetNamed 专门实例（§4.3：工厂产物已声明，泛型兜底恒等放行即正确；专门实例会因注册序被 hdl-types 兜底遮蔽）。

### M2 — 寄存器与 RegNext（纯 typort）

- derive 增发 `reg`/`regInit`；hdl-enum 增 `RegNext[EnumCraft]` impl。
- 验收：§9.2（FSM 状态寄存器 + 复位）。

### M3 — switch 穷尽性（纯 typort：宏臂 + 检查）

- SwitchMark/SwitchFinal/检查体 + hdl-macros switch 臂改写（§4.7）。
- 新增自检规则 **HDL040**（docs/hdl-selfcheck-design.md 规则表追加一行；编号说明：HDL030-039 已被自检阶段 2-4 设计 `docs/hdl-selfcheck-phase234-design.md` 预留，穷尽性检查取 HDL040，HDL041 起留作 switch 相关后续规则）。
- 验收：§9.3（穷尽无告警 / 缺支报 HDL040）。

### M4 — 增强（按需排期）

- localparam（§5.2 方案 B：新变体 + 3 处必补臂 + collectLocalparamLines）。
- derive 增发 `regAs`/`regInitAs`/`regOut`/`regOutInit`/`fromUInt`。
- enum 端口：module 宏新增端口组 `$( input $x:ident = $e:ident . craft )*`（连续组匹配规则同既有端口分组，hdl-macros.typort:268-272 注释）；Bundle 字段：`derive.rs` 的 `is_primitive_type`（derive.rs:277-286）+ `create_fn_name`（:335-362）识别 `EnumCraft[<Enum>, w, c]` 字段并生成 `<Enum>.craftAt(name)`（derive 需同步增发按名工厂）。
- `is` 多值臂、`sizedLiteral` 化枚举字面量（§5.1 限制）。

### 验收基线

- examples/hdl 新增 `26-enum.typort`（§9 全部用例）；既有 25 个例子 Verilog 输出逐字节不变（零回归面：不新增 Expr 变体的 M1-M3 保证）。
- legacy_tests 增加：派生宏产物解析、跨 enum 比较类型报错、HDL040 触发/不触发、oneHot 宽度。

---

## 9. 验收用例（typort 片段 + 期望 Verilog）

### 9.1 声明、比较、组合赋值（M1）

```typort
#[derive(HdlEnum)]
enum FsmState { IDLE RUN DONE }

module enumBasics {
    input hit = Bool
    output isRun = Bool
    output code = UInt[2]
    let cur = FsmState.craft
    when hit {
        cur := FsmState.RUN
    } otherwise {
        cur := FsmState.IDLE
    }
    isRun := cur === FsmState.RUN
    code := cur.asUInt
}
println(moduleTreeVL(enumBasics.create.tree))
```

期望 Verilog（cur 被 when 驱动 → reg + always @(*)，RUN 编码值 1）：

```verilog
module enumBasics (
  input wire hit,
  output wire isRun,
  output wire [1:0] code
);
  reg [1:0] cur;
  always @(*) begin
    if (hit) begin
      cur = 1;
    end
    if (!hit) begin
      cur = 0;
    end
  end
  assign isRun = (cur == 1);
  assign code = cur;
endmodule
```

### 9.2 状态机：regInit + mux（M1/M2）

```typort
module enumMux {
    input sel = Bool
    output q = UInt[2]
    let a = FsmState.craft
    let b = FsmState.craft
    let out = FsmState.craft
    a := FsmState.RUN
    b := FsmState.IDLE
    out := sel.mux(a, b)
    q := out.asUInt
}
```

期望 Verilog（mux 编码后即普通表达式）：

```verilog
module enumMux (
  input wire sel,
  output wire [1:0] q
);
  wire [1:0] a;
  wire [1:0] b;
  wire [1:0] out;
  assign a = 1;
  assign b = 0;
  assign out = (sel ? 1 : 0);
  assign q = out;
endmodule
```

FSM（对应 SpinalHDL UartCtrlTx 形态，UartCtrlTx.scala:44-99）：

```typort
module fsm {
    input start = Bool
    input doneIn = Bool
    output busy = Bool
    output outState = UInt[2]
    let st = FsmState.regInit(FsmState.IDLE)
    switch st {
        is FsmState.IDLE { when start  { st := FsmState.RUN  } }
        is FsmState.RUN  { when doneIn { st := FsmState.DONE } }
        is FsmState.DONE { st := FsmState.IDLE }
    }
    busy := st === FsmState.RUN
    outState := st.asUInt
}
```

期望 Verilog（嵌套 when 条件合取：`(st == 0) && start`；复位分支来自 regInit）：

```verilog
module fsm (
  input wire start,
  input wire doneIn,
  output wire busy,
  output wire [1:0] outState,
  input wire clk,
  input wire reset
);
  reg [1:0] st;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      st <= 0;
    end else begin
      if ((st == 0) && start) begin
        st <= 1;
      end
      if ((st == 1) && doneIn) begin
        st <= 2;
      end
      if (st == 2) begin
        st <= 0;
      end
    end
  end
  assign busy = (st == 1);
  assign outState = st;
endmodule
```

### 9.3 oneHot 编码（M1）

```typort
#[derive(HdlEnum)]
enum Cmd { NOP READ WRITE }

module cmdEnc {
    input fire = Bool
    output cmdOut = UInt[3]
    let c = Cmd.craftAs[encOneHot]
    when fire {
        c := Cmd.READ          // 1 << 1 = 2
    } otherwise {
        c := Cmd.NOP           // 1 << 0 = 1
    }
    cmdOut := c.asUInt
}
```

期望 Verilog（宽度 = 元素个数 3）：

```verilog
module cmdEnc (
  input wire fire,
  output wire [2:0] cmdOut
);
  reg [2:0] c;
  always @(*) begin
    if (fire) begin
      c = 2;
    end
    if (!fire) begin
      c = 1;
    end
  end
  assign cmdOut = c;
endmodule
```

### 9.4 switch 穷尽性（M3）

穷尽、无 default（期望：**无 HDL040**，Verilog 为三分支独立 if）：

```typort
module fsmDecode {
    input adv = Bool
    let st = FsmState.regInit(FsmState.IDLE)
    when adv { st := FsmState.DONE }
    let last = FsmState.craft
    switch st {
        is FsmState.IDLE { last := FsmState.RUN  }
        is FsmState.RUN  { last := FsmState.DONE }
        is FsmState.DONE { last := FsmState.IDLE }
    }
}
```

去掉任一 `is` 分支（如 `is FsmState.DONE`）→ 期望 WARNING：
`HDL040|fsmDecode|st|switch over enum is not exhaustive (missing: DONE) — add is-cases or a default branch`。

类型负例（均应**类型错误**，非 warning）：
- `let x = FsmState.craft  x := Cmd.NOP` —— `Into` 的 E phantom 不匹配。
- `st === Cmd.NOP` —— `Equal[EnumLit[Cmd], Bool] for EnumCraft[FsmState,...]` 无实例。
- `let c = Cmd.craftAs[encOneHot]  let d = Cmd.craft  c === d` —— 宽度 3 ≠ 2。
- `enum Bad { A B(n: Nat) }` + `#[derive(HdlEnum)]` —— derive 解析期报「构造子不能带参数」。

---

## 10. 风险与开放问题

1. **隐式编码参数漏写**：`FsmState.craftAs` 不带 `[enc]` 时宽度卡死为 unsolved meta，只能靠 HDL004 间接报警，报错信息不指因。缓解：文档强调；彻底解决需 elaborator 对「def 隐参 unsolved 且仅被类型索引消费」给专门诊断（Rust 层，二期）。
2. **穷尽性是 WARNING 而非硬错误**：`report_check_issue` 通道只有 WARNING；硬失败需 typort 增加「检查期错误」内建或 Rust 侧错误通道。一期接受 WARNING（与自检框架阶段 1 的名字级定位一致）。
3. **trait 首匹配注册序依赖**：`SwitchMark`/`SwitchFinal` 的泛型兜底实例必须最后注册（hdl-types.typort:242-247 的既有约定）；若类型类求解器将来改为最优匹配，需复核这三个 trait。
4. **无 default switch 的行为放宽**：新宏臂让 `switch u8 { is 0 {...} }` 从「宏匹配失败」变为「合法 when 链」。对 UInt 这是语义放宽（原本写不出来）；如需保守，可在无 default 臂内对非 enum 选择子也发一条 HDL041 提示（`SwitchFinal` 兜底实例里做，一行代价）。
5. **localparam 的 when 包裹约束**：craft 工厂若在 `when` 体内调用，`createEnumLocalparam` 节点会被 WhenStack 包进 when 节点，渲染收集不到（§5.2 方案 B）。约束：工厂在语句位使用（与所有信号工厂一致）；彻底解法是 createSignalExpr 对该变体加直插臂（二期顺手做）。
6. **craft 信号与 UInt 信号在树中不可区分**：是「编码降级」的刻意代价——换来 Verilog/自检零改动；后果是 (a) 工具层无法从 ModuleTree 反推 enum 语义（design manifest 不含 enum 信息），(b) localparam 需要显式节点（§5.2）。若未来需要「树内可辨识」，再评估 `createEnumWidth(name, w, enumName)` 变体族（成本：§5.2 补臂清单 × 变体数）。
7. **宏臂匹配次序**：switch 新旧臂共存后，有 default 臂必须在前（字面 `default` token 使二者互斥，顺序其实无关，但保持显式）。when 臂与 switch 臂共享 WhenStack 约定不变。
8. **元素表重复存储**：每个 EnumLit 携带全元素 `List[String]`（N 个元素 N 份表）。Val 层 Rc 共享可摊薄；如成瓶颈，derive 可生成单个共享 decl 再由各元素引用（开放）。
9. **后续大项**：FSM 库（spinal.lib.fsm 的 StateMachine/StateRegEntryPoint 风格）、enum 端口/Bundle 字段（M4）、GrayCode 等自定义编码、`encNative` 显式元素值（需带 payload 构造子 + 元素值校验）。
10. **示例命名须避让 prelude 既有名**：`State` 已被 `src/prelude/hdl/hdl-bus.typort:214` 的 `struct State[T]`（FSM 占位类型）占用——设计稿原示例 `#[derive(HdlEnum)] enum State { IDLE RUN DONE }` 及其 `craft/reg/regInit` 用法照抄无法编译，全文示例已统改 `FsmState`（与已落地的 `hdl_enum_tests.rs` 一致）。用户文件声明硬件 enum 时同样须避让 prelude 既有名：`State` 不可用。
