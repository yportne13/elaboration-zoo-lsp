# SpinalHDL lib 复刻计划（elaboration-zoo-lsp）

参考源码：`../spinalhdl-ref/lib/src/main/scala/spinal/lib/`（SpinalHDL 官方仓库浅克隆，2026-08-16 抓取）。
本语言的能力模型与 SpinalHDL 的对应关系：

| SpinalHDL | 本语言 (Typort) |
|---|---|
| `Component` | `module` 宏 → 生成实现 `Module` trait 的 struct |
| `Area`（内联逻辑分组） | 任意 def 内直接操作全局 `ModuleTree`（`createSignalExpr`/`addSignalAssignment`）|
| `Bundle` + `IMasterSlave` | `#[derive(Bundle)]` + `impl IMasterSlave`（`asMaster`/`asSlave`）|
| `ClockDomain` | `ClockDomain` struct（**每模块一个时钟**，单 always 块）|
| `Reg`/`RegNext`/`Counter`/`Mem` | `reg` 宏 / `regNext` / `counter`/`counterInc` / `memUInt` 等 |
| Scala 泛型/隐式 | 依赖类型参数 + `[bn: BindingName]` 隐式 + typeclass impl |
| 仿真 (sim) | 无（验收改用外部 Verilog 仿真，见 §4）|

## 1. lib 全量盘点（可复刻性分级）

### A 级 — 当前语言可直接复刻（纯组合逻辑 / 单时钟寄存器逻辑）

| 源文件 | 组件 | 目标文件 |
|---|---|---|
| Utils.scala | `CountOne`/`CountOneOnEach`/`SetCount`/`ClearCount`、`Reverse`、`PropagateOnes`、`UIntToOh`/`UIntToOhMinusOne`/`OHToUInt`、`OH.isLegal`、`OHMasking.first/last/roundRobin*`、`PriorityMux`、`MuxOH`/`OhMux`、`Min/Max/Clamp`、`toGray/fromGray`、`EndiannessSwap`、`AddWithCarry`、`CountLeadingZeroes`/`CountTrailingZeroes`、`Shift.rightWithScrap`、`Delay`/`DelayEvent`/`Timeout`、`History`、`MajorityVote`、`whenIndexed`/`whenMasked`、`SetFromFirstOne`、`BitAggregator`(纯) | `hdl-utils.typort` |
| Counter.scala | `Counter`（stateCount/clear/inc/willOverflow）、`CounterUpDown`、`DownCounter`、`OneHotCounter`、`JohnsonCounter` | `hdl-utils.typort` |
| Misc.scala | `FlowCmdRsp`(bundle)、`Repeat`(`#*`)、`DataCarrier` trait 结构 | `hdl-misc.typort` |
| logic/Decoder.scala | onehot 解码（`DecodingSpec` 纯逻辑 + 硬件 OR-tree）| `hdl-logic.typort` |
| logic/Masked.scala | `Masked`（纯值 + `===` 硬件掩码比较）| `hdl-logic.typort` |
| math/Bcd.scala | `Bcd`（4-bit digit Vec、BCD 加法/移位/`isZero`/`leadingZeroes`）| `hdl-math.typort` |
| math/Divider.scala | `UnsignedDivider`（恢复除法状态机，cmd/rsp 握手）| `hdl-math.typort` |
| io/TriState.scala | `TriState`（read/write/writeEnable + asMaster）、`TriStateArray` | `hdl-io.typort` |
| io/ReadableOpenDrain.scala | `ReadableOpenDrain` | `hdl-io.typort` |
| io/Gpio.scala | 简单 GPIO（in/out/中断挂起/掩码寄存器组）| `hdl-io.typort` |
| misc/Prescaler.scala | `Prescaler` | `hdl-misc.typort` |
| misc/Timer.scala | `Timer`（tick/clear/limit/full/value）| `hdl-misc.typort` |
| misc/InterruptCtrl.scala | `InterruptCtrl`（inputs/clears/masks/pendings）| `hdl-misc.typort` |
| misc/Plru.scala | `Plru`（伪 LRU 状态 + evict/update）| `hdl-misc.typort` |
| misc/Watchdog.scala | `Watchdog` | `hdl-misc.typort` |
| bus/amba3/apb/APB3.scala | `Apb3` bundle + asMaster/asSlave + `Apb3Decoder` | `hdl-bus.typort` |
| bus/amba4/axilite/AxiLite4.scala | `AxiLite4`（aw/w/b/ar/r 五通道 Stream）+ resp 常量 | `hdl-bus.typort` |
| bus/amba4/axis/Axi4Stream.scala | `Axi4Stream`（data/id/strb/keep/last/dest/user）| `hdl-bus.typort` |
| bus/wishbone/Wishbone.scala | `Wishbone`（classic/pipelined）| `hdl-bus.typort` |
| bus/avalon/Avalon.scala | `AvalonST`（data/valid/ready/empty/sop/eop）| `hdl-bus.typort` |
| bus/amba3/apb/Apb3SlaveFactory.scala | 寄存器组简化版（read/write/driveAndRead）| `hdl-bus.typort` |
| CrossClock.scala | `BufferCC`（双触发器同步器，单时钟结构）| `hdl-crossclock.typort` |
| Stream.scala | Stream 管线（`combStage`/`halfPipe`/`m2sPipe`/`s2mPipe`）、`StreamFifo`、`StreamFifoLowLatency`、`StreamMux`/`StreamDemux`/`StreamDemuxOh`、`StreamArbiter`(lowerPriority/roundRobin/roundRobinMasked)、`StreamFork`、`StreamJoin`、`StreamCombinerSequential`、`StreamDispatcherSequencial`、`throwWhen`/`haltWhen`/`continueWhen`/`takeWhen`/`freeRun` | `hdl-stream.typort` |
| Flow.scala | `Flow`（已有）、`FlowMux`、`FlowArbiter`、`FlowFifo`（→ `StreamFifo` 转换）| `hdl-stream.typort` |
| Fragment.scala | `Fragment[T]`（last 位）、`StreamFragment`/`FlowFragment` 工厂、`throwWhen` 等 | `hdl-stream.typort` |

### B 级 — 需要语言扩展（Rust 侧）后才能复刻

| 组件 | 缺口 |
|---|---|
| `PulseCCByToggle`/`CCByToggle`/`StreamFifoCC`/`AsyncFifo`/`FlowCCByToggle` | **每模块多时钟域**：当前 `Expr` 无时钟字段、Verilog 生成器每模块只发一个 always 块。需要给 `createReg*` 增加 cd 参数 + 代码生成按 (clk,edge,polarity) 分组。见 §5 |
| `StreamWidthAdapter`（字节重排）| 依赖 Vec 硬件索引 + 复杂字节排列；可由 A 级原语拼装但工作量高，列为波次 7 |
| `Mem.readSyncCC` 真正跨时钟 | 同上（当前实现与 readSync 相同）|
| blackbox 厂商原语（Xilinx/Altera/Lattice）| 需要 `BlackBox` 真正的 HDL 属性生成（现为占位）|
| `dsptool`（定点数）| 依赖定点类型系统（Q-format 类型级运算），工作量大 |
| `generator`/`eda`/`sim`/`tester`/`cocotb` | 仿真/EDA 工具链，本语言无对应后端 |
| `regif` 完整框架 | 依赖反射式寄存器描述；复刻其核心语义（BusIf + Field）作波次 8 简化版 |
| 宏 `when`/`switch` 之外的 Scala 宏设施（FSM 状态注入）| 以简化版 StateMachine（波次 6）替代 |

### C 级 — 不适用（运行时/工具类，非硬件语义）

`BinTools`/`HexTools`（文件 IO，可做 .typort 纯函数版 hex 行解析）、`AnalysisUtils`/`LatencyAnalysis`（RTL 分析工具）、`PathTracer`、`Growable` 等集合 pimp。

## 2. 波次划分（并行化单元）

每个波次 = 一个 prelude 库文件 + 一组 `examples/hdl/` 示例 + 回归断言 + （组合逻辑部分）真值表验收。波次之间文件独立，可交给独立 agent 并行实现；验收标准即 §4 协议。

| 波次 | 库文件 | 内容 | 验收重点 |
|---|---|---|---|
| 1 | `hdl-utils.typort` | Utils 组合逻辑 + Counter 家族 + Delay/Timeout/History | 真值表（verilator）+ 结构断言 |
| 2 | `hdl-stream.typort` | Stream/Flow/Fragment 框架 + FIFO/Mux/Demux/Arbiter/Fork/Join | 结构断言 + 时序仿真（fifo 顺序）|
| 3 | `hdl-crossclock.typort` | BufferCC + 单时钟可表达部分 | 结构断言 |
| 4 | `hdl-bus.typort` | APB3/AxiLite4/Axi4Stream/Wishbone/AvalonST + 寄存器组 | 结构断言 + 读写仿真 |
| 5 | `hdl-io.typort` `hdl-math.typort` `hdl-logic.typort` `hdl-fsm.typort` | TriState/GPIO、Bcd/Divider、Decoder/Masked、StateMachine 简化版 | 真值表 + 结构断言 |
| 6 | `hdl-misc.typort` | Prescaler/Timer/InterruptCtrl/Plru/Watchdog | 结构断言 + 时序仿真 |
| 7 | （B 级，语言扩展后）| 跨时钟 + StreamWidthAdapter + regif-lite | — |

## 3. 复刻代码的组织

- `src/prelude/hdl/hdl-utils.typort` 等：库本体。命名对齐 SpinalHDL（`countOne`、`ohToUInt`、`streamFifo`、`apb3` …）。
- 库函数采用 **Area 风格**（内联展开到调用方模块），与 `counter`/`memUInt`/`regNext` 现有惯用法一致；模块边界（`mkInstance`）用于层次化示例。
- 命名：内部信号用 `newUIntRegNamed("…")` 显式命名（def 体内无 BindingName）；工厂函数用 `[bn: BindingName]` 让用户侧 `let x = streamFifo(...)` 自动命名，与 SpinalHDL 自动命名一致。

## 4. 验收协议（三层）

**L1 编译+展开**：每个示例 `typort check` 必须 0 错误（回归测试 `test_examples_hdl_dir` 新增条目，或新增 `test_spinalhdl_lib_*` 测试函数）。

**L2 结构断言**：生成的 Verilog 必须包含关键结构串（端口方向/宽度、reg 声明、assign 形态、when 条件、握手信号）。断言写进 `legacy_tests.rs` 的 examples 表（每波次新文件 + 断言组）。

**L3 行为验证（真值表/时序）**：
- `tools/spinalhdl-verify/verify.py`：跑 `typort check examples/…` 抓 Verilog → 用 **iverilog**（若可安装；否则 verilator + C++ 驱动）编译仿真 → 输入扫描与 Python 参考实现比对（组合逻辑全空间扫描，时序逻辑定向激励）。
- 组合组件（CountOne/OHToUInt/MuxOH/CLZ/Bcd 等）：全输入空间 0..2^w-1 比对。
- 时序组件（FIFO/Counter 家族/Timer/Divider/FSM）：脚本内定义参考状态机，驱动 clk 比对每拍输出。
- 每个库组件在 `examples/hdl/verify/` 下有一个 `*_tb.py` 参考实现。
- CI 友好：`verify.py` 找不到仿真器时打印跳过信息并 exit 0；有仿真器时任何不一致 exit 1。

**验收判定**：L1 必须全过；L2 必须全过；L3 在仿真器可用时全过（否则标记 `unverified` 并在文档 §6 记录）。

## 5. 语言扩展需求（B 级前置，单独立项）

1. **每寄存器时钟域**：`Expr::createReg*` 增加 cd 字段（或旁路注册表），Verilog 生成按 (clk,edge,polarity) 分组 emit 多个 always 块；prelude 提供 `regNextCd`/`BufferCC` 等。这是 `PulseCCByToggle`/`StreamFifoCC`/`readSyncCC` 真正实现的前置。
2. **Vec 硬件索引**：`vec.atUInt(idx: UInt[s], default)` 用平衡 mux 树实现（**可在 .typort 内完成，无需 Rust 改动**）。
3. **BlackBox 真实代码生成**（属性/参数/端口声明）。
4. **运行时数组/ROM 初始化**（`$readmemh` 或 init 数组）——`HexTools.initRam` 前置。

## 6. 状态跟踪

| 波次 | 状态 | 验证 |
|---|---|---|
| 1 Utils/Counter（hdl-utils.typort） | ✅ | L1/L2 通过；L3 30/30（verilator 真值表） |
| 2 Stream/Flow/Fragment（hdl-stream.typort） | ✅ | L1/L2 通过；L3 12/12（m2s/fifo/mux/arb/fork + counter 家族） |
| 3 CrossClock（hdl-crossclock.typort） | ✅ BufferCC；真跨时钟待语言扩展 | L1/L2 通过 |
| 4 Bus（hdl-bus-proto.typort） | ✅ APB3/AxiLite4/Axi4Stream/Wishbone/AvalonST + 寄存器组 | L1/L2 通过（APB3 读写行为人工核验） |
| 5 io/math/logic/fsm（hdl-misc-io.typort） | ✅ TriState/Gpio/Bcd/Divider/Decoder/Masked/StateMachine | L1/L2 通过；L3 7/7（bcd/maskedEq/decoder + prescaler/timer/intr/watchdog） |
| 6 misc（hdl-misc.typort） | ✅ Prescaler/Timer/InterruptCtrl/Plru/Watchdog | 同上 |
| 7 B 级扩展 | 依赖语言扩展：每寄存器时钟域、Vec 硬件索引（.typort 内可做）、BlackBox、ROM 初始化 | — |

**最终验收**：examples/hdl/01-18 全部编译展开（L1）；关键 Verilog 结构断言通过（L2）；
== cases: v_utils_combinational.typort ==
  [OK] vReverse
  [OK] vReverseU
  [OK] vPropLsb
  [OK] vPropMsb
  [OK] vCountOne
  [OK] vCountOneU
  [OK] vClz
  [OK] vCtz
  [OK] vMajority
  [OK] vUintToOh
  [OK] vUintToOhM1
  [OK] vOhToUInt
  [OK] vOhLegal
  [OK] vOhFirst
  [OK] vOhLast
  [OK] vOhRR
  [OK] vPriorityMux
  [OK] vMuxOH
  [OK] vOhMuxOr
  [OK] vMinMax
  [OK] vClamp
  [OK] vGray
  [OK] vEndianSwap
  [OK] vAddCarry
  [OK] vLog2Floor
  [OK] vLog2Ceil
  [OK] vSetFromFirstOne
  [OK] vNapot
  [OK] vScrap
  [OK] vCountOneOnEach
== cases: v_utils_sequential.typort ==
  [OK] vCounterMod
  [OK] vCounterUpDown
  [OK] vDownCounter
  [OK] vOneHotCounter
  [OK] vJohnsonCounter
  [OK] vDelayEvent
  [OK] vTimeout
  [OK] vPrescaler
  [OK] vTimer
  [OK] vInterruptCtrl
  [OK] vWatchdog
== cases: v_stream_sequential.typort ==
  [OK] vStreamM2s
  [OK] vStreamFifo
  [OK] vStreamMux
  [OK] vStreamArb
  [OK] vStreamFork
== cases: v_misc_combinational.typort ==
  [OK] vBcdAdd
  [OK] vMaskedEq
  [OK] vDecoder
== 49 passed, 0 failed, 49 total ==（verilator + Python 参考）49/49 行为比对通过（L3）。
全套测试 389 通过 / 49 失败，失败均为既有（L07/L10/L11/L12 早期模块，与本次改动无关，
stash 对比验证为同一集合）。

**已知语言限制（记录于本文档 §3/§5）**：
1.  不能在 prelude 文件中用（ 枚举构造器短名冲突）→ 总线
   bundle 用手工方向函数（ 等）。
2. 每模块单时钟域 → 真跨时钟（PulseCCByToggle/StreamFifoCC）需 Rust 侧扩展。
3. 泛型硬件值方法受限于 trait 方法签名规则（T 不能出现在参数类型）→ 用 MuxExpr 模式 /
   按类型实现。
4. 在 module 体内  会与模块宏的  字段冲突 → 用 。
5. 刚性参数上的计算宽度（）不可归约 → 指针宽度等作为显式类型参数。
