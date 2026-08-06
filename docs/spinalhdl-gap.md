# SpinalHDL 差距分析 (spinalhdl-gap)

> 分支 `task/spinalhdl-gap`，基线 master HEAD `a8a528d`（含 Mem 实现 `0ee24ca`）。
> 对照来源：SpinalHDL 官方文档 (spinalhdl.github.io/SpinalDoc-RTD) 的 Data types /
> Sequential logic / Semantic (when-switch) / Structuring (components, clock domain) 章节。
> 状态图例：✅ 已有　🟡 部分（缺子集）　❌ 缺失　— 优先级：必要 / 重要 / 可选。

## 1. 数据类型

| SpinalHDL 类型 | 状态 | 说明 | 优先级 |
|---|---|---|---|
| Bool | ✅ | 声明、`:=`、`===`/`=/=`、`&&` `\|\|` `!` `&` `\|` `^`、mux、`asBits/asUInt/asSInt` | — |
| Bits | ✅ | 宽度参数化、位运算、移位(Nat 常量)、rotate、归约 andR/orR/xorR、位选/切片、拼接、resize/asUInt/asSInt | — |
| UInt | ✅ | 算术 + - * +^ -^、位运算、比较、移位、位选/切片、resize/cast、asBits/asSInt/asBool、mux | — |
| SInt | 🟡 | 基本完备；缺 `abs`、`expand`、除法/取模、`\|<<` `\|>>` | 必要 |
| Enum (SpinalEnum) | ❌ | 语言有普通 enum，但无硬件 enum：无编码/位宽、无 `===` 硬件比较、switch 只支持 Nat 字面量、无 Verilog `reg [1:0] state` 代码生成 | 重要(二期) |
| Bundle | ✅ | `#[derive(Bundle)]`：批量 `:=`、`create_TypeName` 自动命名、`asMaster`/`asSlave`、`in()/out()/inout()` 标记（inout 目前当 input 处理） | — |
| Vec | ❌ | 语言内建 `Vec[A](len)` 是纯数据 GADT（nil/cons），无硬件向量：无 `Vec.fill` 信号工厂、无静态/动态下标、无批量赋值 | 必要 |
| UFix/SFix | ❌ | 无定点数 | 可选(远期) |

## 2. 运算符与宽度语义

| 运算符 | 状态 | 说明 | 优先级 |
|---|---|---|---|
| `+` `-` | ✅ | 同宽；SpinalHDL 为 max(w(x),w(y))，此处要求同宽（更严格） | — |
| `+^` `-^` | ✅ | 结果宽 +1，与 SpinalHDL 一致 | — |
| `*` | ✅ | UInt*UInt 结果宽 w1+w2（SpinalHDL 同）；SInt 同宽（SpinalHDL SInt 乘法为 w1+w2 — 🟡） | 可选 |
| `/` `%` | ❌ | UInt/SInt 均缺；SpinalHDL: `/` 宽 = w(x)，`%` 宽 = min(w(x),w(y)) | 必要 |
| `+|` `-|` (饱和) | ❌ | 无 | 可选 |
| `<<` `>>` (Nat 常量) | ✅ | 保持宽度（SpinalHDL 常量移位会变宽 — 记录偏差） | — |
| `\|<<` `\|>>` (变量/保持宽度) | ❌ | 缺；Verilog 变量移位原生支持 | 必要 |
| `<<` `>>` (UInt 移位量) | 🟡 | rotateLeft/Right 支持 UInt 移位量，但普通 `<<`/`>>` 不支持 | 可选 |
| 拼接 `##` | ✅ | Bits/UInt/SInt/Bool 全组合 | — |
| 比较 `< <= > >= === =/=` | ✅ | UInt/SInt/Bool，支持 Nat 字面量 | — |
| 归约 andR/orR/xorR | ✅ | 三类全有 | — |
| `abs` (SInt) | ❌ | 缺 | 必要 |
| `expand` | ❌ | 缺（UInt 零扩展 / SInt 符号扩展） | 重要 |
| `resize`/`cast` | ✅ | resize 无检查；cast 带 Le 证明 | — |
| `setAll`/`clearAll`/`getZero`/`getAllTrue` | ❌ | 缺（Bits 常量填充） | 可选 |
| mux | ✅ | `cond.mux(a,b)` + 三目 `? :`；缺 muxList/priorityMux/switch-mux | 可选 |

## 3. 控制结构

| 结构 | 状态 | 说明 | 优先级 |
|---|---|---|---|
| when/elsewhen/otherwise | ✅ | 宏展开为 if/else-if/else；Verilog 合并 always @(*) | — |
| switch/is/default | ✅ | 基于 `===` 展开为 when 链；is 值限 Nat 字面量或信号 | — |
| mux | ✅ | 见上 | — |

## 4. 寄存器

| API | 状态 | 说明 | 优先级 |
|---|---|---|---|
| `reg x = T[w]` / `init` | ✅ | 宏 + `auto*Reg(Init)` + `new*Reg(Init)` | — |
| RegNext / RegNextWhen | ✅ | 任意 Data 类型泛型（RegNext typeclass） | — |
| RegInit (函数式) | 🟡 | 只有宏形式 `reg x = T[w] init v`，无 `RegInit(t)` 函数式 API | 可选 |
| Counter | ❌ | 缺 `counter(w)` / 带使能计数、willOverflow | 必要 |
| 时钟域 (ClockDomain) | ✅ | ClockDomainConfig/Async 复位/`always @(posedge clk or posedge reset)` | — |
| 异步复位 | ✅ | reg init → 异步复位块 | — |
| 跨时钟域 | 🟡 | 模块级 ClockDomain 参数；`readSyncCC` 与 readSync 相同（无真正同步器） | 可选 |
| BufferCC / 同步器 | ❌ | 无 | 可选 |

## 5. 层次与方向

| 特性 | 状态 | 说明 | 优先级 |
|---|---|---|---|
| Component/Module | ✅ | `module` 宏 → ModuleDef/ModuleTree；`create` 实例化；子模块 `let u = child.create` + `u.port := sig` 层次连接 | — |
| in/out 端口 | ✅ | 宏、auto*、createPortExpr、Bundle 方向 | — |
| inout 端口 | ❌ | `inout()` 标记在 derive 中按 input 处理；无 `inout wire` Verilog 代码生成、无 Expr 变体 | 必要 |
| master/slave | ✅ | `asMaster`/`asSlave` + 端口方向翻转 | — |
| `:=` | ✅ | Data trait + Bundle derive；自动跳过 input LHS | — |
| `<>` | ❌ | 无（SpinalHDL 双向连接） | 重要 |
| 实例化端口连接 | ✅ | `u.a := sig` → `.a(sig)` 端口映射 | — |
| BlackBox | 🟡 | 语法占位 stub，无代码生成 | 可选 |
| Stream/Flow | 🟡 | 有 fire/stage 占位；无 `<>`、无握手机制 | 可选 |
| FSM | 🟡 | 占位 | 可选 |

## 6. 存储器与断言

| 特性 | 状态 | 说明 | 优先级 |
|---|---|---|---|
| Mem (单口) | ✅ | memUInt/memBits/memSInt/memBool + write/readAsync/readSync | — |
| Mem 双口 | 🟡 | 同一条 mem 上多次 write/read 可并出（端口各自独立记录），但无显式双口 API/校验 | 可选 |
| `assert` / 断言 | ❌ | 无；SpinalHDL `assert(cond, "msg")` 生成仿真断言 | 重要 |

## 7. 本轮实现清单（必要/重要级）

按"语言能力允许 + 高频使用 + 独立可测"选取 6 项：

1. **运算符补齐**（必要）：UInt/SInt 除法 `/`、取模 `%`；UInt/SInt/Bits 宽度保持移位 `|<<` `|>>`（UInt 移位量）；SInt `abs`；UInt/SInt `expand`；Bits `setAll`/`clearAll`。
2. **inout 端口**（必要）：Expr 变体 + Verilog `inout wire` 生成 + 工厂/宏/auto* 全套。
3. **Counter**（必要）：`counter(w)` 自增、`counterInc(w, en)` 使能计数、`willOverflow`。
4. **Vec**（重要）：`HVec`（避开内建 `Vec[A](len)` 名）— fill 工厂（UInt/Bits/SInt/Bool）、静态下标、UInt 动态下标（mux 链）、批量 `:=`。
5. **assert 断言**（重要）：Expr 变体 + `always @(*)` 中 `$display` 仿真断言 + `def assert(cond, msg)`。
6. **`<>` 连接**（重要）：Data 各类型 + Bundle derive 生成 `<>`（SpinalHDL 双向连接；本模型下与 `:=` 同语义——驱动本方输出、跳过 input LHS）。

## 8. 未实现（记录在案，二期候选）

- 硬件 Enum（SpinalEnum）：需要 enum 编码/位宽、`===` 硬件比较、switch 枚举分支、Verilog 类型声明。
- UFix/SFix/Floating 定点/浮点。
- 饱和运算 `+|` `-|`、`muxList`/`priorityMux`、`#*` 重复、`reversed`。
- RegInit 函数式 API、BufferCC/同步器、真正的跨时钟域读写。
- BlackBox 代码生成、Stream/Flow 完整握手、FSM。
- 常量移位变宽语义（当前 `<<`/`>>` 保持宽度，与 SpinalHDL `<<`(Int) 变宽不同）。
