# HDL Stream/Flow/Fragment 完整化与 FSM 设计（hdl-stream-fsm-design）

> 状态：设计稿 · 2026-09-26
> 范围：纯设计文档，不改源码。上游：`docs/spinalhdl-gap.md`（§5/§7/§8）、`docs/spinalhdl-lib-replication.md`（波次表 + 末尾语言限制）、`docs/hdl-selfcheck-design.md` 与 `docs/hdl-selfcheck-phase234-design.md`（规则编号段位）。
> SpinalHDL 参考：`F:\projects\hermes\spinalhdl-ref\lib\src\main\scala\spinal\lib\`（Stream.scala / Flow.scala / Fragment.scala / MasterSlave.scala / fsm\*.scala），下文以 `Stream.scala:行` 引用。

## 1. 背景与现状

### 1.1 既有资产（已逐一核实）

| 资产 | 位置 | 现状 |
|---|---|---|
| `Stream[T]` / `Flow[T]` struct | `src/prelude/hdl/hdl-bus.typort:169-178` | 泛型 struct，字段 `valid/ready/payload`（Flow 无 ready） |
| `fire` / `stage` 占位 | `hdl-bus.typort:180-188` | `fire = valid && ready` 正确；`stage = this` 是占位 |
| FSM 占位（StateAccess/State/FSMEntryPoint/SwitchKey） | `hdl-bus.typort:204-231` | 纯占位 enum/struct，无实现 |
| 简化版 StateMachine | `src/prelude/hdl/hdl-misc-io.typort:203-225` | `stateMachine[w](stateCount)` 单寄存器 + `stateGoto`（无条件 regAssign）+ `stateIs`；无状态上下文、无 default-hold、无 onEntry/onExit |
| 管线原语（按类型） | `src/prelude/hdl/hdl-stream.typort`（448 行） | freeRun/isFree/isStall（24-32）、streamConnectUInt/Bits（35-45）、combStage（51-64）、m2sPipe（73-104）、s2mPipe（110-122）、halfPipe（128-148）、throwWhen/haltWhen/continueWhen/takeWhen（154-184）——全部 UInt/Bits/Bool 三份手工展开 |
| StreamFifo（UInt） | `hdl-stream.typort:192-248` | RAM + 指针式，pw/ow 由调用方显式给（刚性参数上 `log2Up(n)` 不可归约） |
| StreamMux/Demux（UInt） | `hdl-stream.typort:255-307` | Vec 递归 mux 链 |
| StreamArbiter lowerFirst（UInt） | `hdl-stream.typort:316-363` | 固定优先级，无 roundRobin、无 lock |
| StreamFork（同步，UInt） | `hdl-stream.typort:371-390` | ready AND 汇聚 |
| Fragment/StreamFragment struct | `hdl-stream.typort:396-406` | 独立 struct 双轨（非 `Stream[Fragment[T]]`） |
| FlowMux（UInt） | `hdl-stream.typort:431-448` | 见 §1.2 缺陷 F5 |
| Bundle/IMasterSlave/`:=`/`<>` 机制 | `hdl-bus.typort:57-163` + `src/L13_namespace/parser/derive.rs` | 用户文件可用 `#[derive(Bundle)]`（`examples/hdl/10-bundle.typort`）；prelude 内禁用（§1.3 限制 1） |
| Data trait（`:=`/`expr`/`<>` 默认体） | `src/prelude/hdl/hdl-types.typort:38-60`；`driveExpr` 29；`isInputPort` 16-24 | payload 连接的底层原语 |
| RegNext typeclass | `src/prelude/hdl/hdl-signals.typort:561-632` | **payload 泛型化的既成范式**（receiver-only 方法 + 泛型自由函数） |
| 方向助手 in_u/out_u/in_b/out_b/in_bool/out_bool | `hdl-signals.typort:488-557` | 手工方向函数模式（apb3AsMaster 等在 `hdl-bus-proto.typort:29-36`） |
| 自检框架 | `src/prelude/hdl/hdl-check.typort`（901 行）+ `docs/hdl-selfcheck-design.md` | HDL001-004/010-013/020-025 已实现；**HDL030-050 已被自检阶段 2-4 预留**（组合环/latch/CDC，`docs/hdl-selfcheck-phase234-design.md` 规划 HDL030-039）；HDV001-003 属 verilog-compat |
| 跨时钟 StreamFifoCC | `src/prelude/hdl/hdl-crossclock.typort:182-222` | 已落地（wave 7，per-register 时钟域机制），不在本设计范围 |
| 示例 | `examples/hdl/19-stream.typort`（202 行）、`20-misc.typort:82-96`（miscFsm） | 现状用法基准 |

### 1.2 现有缺陷清单（实现期第一步先修，均可在 .typort 层修）

对照 `Stream.scala` 逐一核对发现 5 处语义错误（现有 L3 用例激励太弱未暴露）：

| # | 位置 | 缺陷 | 正确语义（SpinalHDL 依据） |
|---|---|---|---|
| F1 | `hdl-stream.typort:81/92/103`（m2sPipe） | `input.ready := rValid \|\| outReady` —— **满/空条件写反** | `self.ready := out.ready; setWhen(!out.valid)`（Stream.scala:493-495）→ `ready = outReady \|\| !rValid`（空时随时收、满时等下游） |
| F2 | `hdl-stream.typort:110-122`（s2mPipe） | 只把 ready 打了一拍（`RegNext(outReady)`），无 rValidN/rData/bypass —— 反压沿上会丢数据 | skid buffer：`rValidN = RegInit(True)`，`clearWhen(input.valid) setWhen(out.ready)`；`input.ready := rValidN`；`out.valid := input.valid \|\| !rValidN`；`out.payload := rValidN ? input.payload : rData`（Stream.scala:498-512） |
| F3 | `hdl-stream.typort:154-162`（throwWhen） | `input.ready := outReady`，缺丢弃拍强制消费 | `when(cond) { next.valid := False; this.ready := True }`（Stream.scala:577-586）→ `ready = cond \|\| outReady` |
| F4 | `hdl-stream.typort:164-184`（haltWhen/takeWhen） | `out.valid := input.valid` 未被 cond 门控；takeWhen 误实现为 haltWhen | `continueWhen`: `next.valid := valid && cond; this.ready := next.ready && cond`（Stream.scala:553-560）；`takeWhen = throwWhen(!cond)`（Stream.scala:600） |
| F5 | `hdl-stream.typort:435`（flowMuxPayload） | `binary(select, "==", literal(0))` —— 递归深度变量 `k` 误写成常量 0，FlowMux 永远选第 0 路 | `literal(k)`（对齐 259 行 muxSelValid 的写法） |

另有半偏差（记录在案、随 §4 重写对齐）：halfPipe 现实现（`hdl-stream.typort:128-148`）的 `ready := outReady || !rValid` 允许背靠背，不是 SpinalHDL 的带宽减半语义（`input.ready := !rValid`，Stream.scala:536-551）；s2mPipe 缺 Bool 版。

### 1.3 语言约束清单与本文对策

来自 `docs/spinalhdl-lib-replication.md` 末尾（注意：该清单第 2 条已过时，见下）：

1. **prelude 内不能用 `#[derive(Bundle)]`**（与 Expr 枚举构造器短名 `create` 冲突）→ Stream/Flow/Fragment 的方向化与 `<>` 走**手工方向函数 + typeclass**（§3.3），对齐 `hdl-bus-proto.typort:7-10` 头注的既有决策。
2. **每模块单时钟域** —— **已过时**：wave 7 在 .typort 层落地了每寄存器时钟域（`hdl-core.typort:108-111` 的 `createRegWidthCd/createRegWidthInitCd`、`hdl-core.typort:134` `regAssignCd`、`hdl-verilog.typort:551-672` 多 always 分组 + 额外时钟自动端口），`hdl-crossclock.typort:182-222` 的 StreamFifoCC 是现成证据。设计仍按"主时钟域默认、显式 cd 参数可选"推进，跨时钟组件继续留在 hdl-crossclock。
3. **trait 方法签名规则：`T` 不能出现在参数类型位置**（泛型 impl 的方法受限）→ 绕开范式有两类，本文以 RegNext 的 **receiver-only 方法**为主（§3.1）：trait 方法只把 T 用在 receiver/返回位置，双操作数操作下沉到 Expr 层原语（`driveExpr`/`isInputPort`）或泛型**自由函数**（自由函数参数不受此限制，`hdl-signals.typort:631-632` 的 regNext 即是）。
4. **module 体内 `tree` 名与宏字段冲突** → 库内不引入名为 `tree` 的绑定。
5. **刚性参数上的计算宽度不可归约** → FIFO 指针宽、occupancy 宽、FSM 状态位宽一律**显式类型参数**（调用方写 `fsmNew[2](4)`），运行期 Nat 值参数只做自检/文档用途（对齐 `hdl-stream.typort:204-206` 现状注释）。

补充约束 6（本文发现）：**prelude struct 不能暴露名为 `create` 的方法**（同限制 1 的冲突面），故 prelude 侧工厂一律 `fsmNew` / `streamFifo` / `Xxx.mk` 形态；`Xxx.create` 仅由用户文件里的 derive(Bundle) 生成。

## 2. 目标与非目标

### 2.1 目标（一期）

- G1 Stream/Flow/Fragment 的 **payload 泛型化**：同一份 API 覆盖 UInt/Bits/SInt/Bool 与用户自定义 bundle payload，消灭按类型三份的手工展开。
- G2 握手与连接语义对齐 SpinalHDL：`fire/isStall/isFree`、`connectFrom`、`<>`、方向函数，并修 §1.2 全部缺陷。
- G3 管线原语完整：combStage/m2sPipe/s2mPipe/halfPipe/validPipe + 门控原语（throwWhen/haltWhen/continueWhen/takeWhen/freeRun）。
- G4 组合原语：StreamFifo（泛型 + flush + almostFull/almostEmpty）、StreamArbiter（lowerFirst/roundRobin + TransactionLock）、Fork（同步/异步）、Join、Mux/Demux、Flow 家族。
- G5 Fragment 统一为 `Stream[Fragment[T]]`，提供 addFragmentLast（Bool/Counter 两版）与 isFirst/isLast/lastFire。
- G6 FSM：SpinalHDL fsm 语义的简化复刻（whenIsActive/whenIsInactive/onEntry/onExit/whenIsNext/goto/isActive），binary UInt 编码，落树过现有自检，新增 HDL060-064 转移覆盖检查。
- G7 全部原语给出验收用例（L1 编译 / L2 结构断言 / L3 行为仿真，协议见 `docs/spinalhdl-lib-replication.md` §4）。

### 2.2 非目标（一期不做，见 §9/§10）

- StreamFifoCC / StreamCCByToggle（已由 hdl-crossclock 承担，本设计不重复）。
- StreamWidthAdapter、StreamFifoLowLatency、StreamDispatcherSequencial、StreamCombinerSequential（SpinalHDL 次高频组件，二期候选）。
- 硬件 Enum（SpinalEnum）编码 —— FSM 一期用 binary UInt 承载（同日设计稿 `docs/hdl-enum-design.md` 已出：EnumCraft 类型 + HDL040 switch 穷尽性；其定型后 FSM 状态编码可迁移，迁移点见 §7.6）。
- FSM 的 StateBoot 显式 boot 态、StateDelay、StateFsm 子状态机、StatesSerial/Parallel（§7.5）。
- 任何 Rust 侧改动（一期全部 .typort 可达，§8）。

## 3. Stream/Flow 类型与握手

### 3.1 payload 类型约束：StreamData typeclass（决策 D1，推荐 typeclass，不用宏）

**结论：定义 `trait StreamData[T]` 作为"payload 可过 Stream"的 typeclass 约束，方法走 receiver-only 范式；宏生成方案否决。**

- struct 保持泛型不动：`struct Stream[T] { valid: Bool, ready: Bool, payload: T }`（`hdl-bus.typort:169-173`）。所有**不改 payload 值**的操作（freeRun/isStall/isFork 扇出等）本来就能写在 `impl[T] Stream[T]` 里（现状 24-32 行已证明）。
- 所有**触碰 payload 值**的操作（连接、寄存推进、方向化、mux 选路）需要从 `T` 拿到 Expr / 建同型信号。受 §1.3 限制 3 约束，约束 trait 采用 RegNext 同款 receiver-only 形态：

```typort
// hdl-stream.typort（新增，置于文件头）
// StreamData[T]：T 可作为 Stream payload。方法全部 receiver-only
//（T 只出现在 receiver/返回位置，规避 trait 方法签名限制 3）；
// 双 payload 值的连接由自由函数经 payloadExpr 下沉 Expr 层完成（driveExpr）。
trait StreamData[T] {
    def payloadExpr: Expr              // 取底层 Expr（Data.expr 的影子，供 driveExpr/isInputPort）
    def regNextNamed(name: String): T  // 同型寄存器（转发 RegNext.mkReg；宽度型由各 impl 自己持有 w）
    def portOut: T                     // 方向化：out_u/out_b/out_bool(this)
    def portIn: T                      // 方向化：in_u/in_b/in_bool(this)
}
```

- 前置约定：**payload 必须是 Data 家族**（`:=`/`expr` 语义成立，`hdl-types.typort:38-60`）——这是 StreamData impl 的隐含前提，写进 trait 头注。

- prelude 提供四个 impl（UInt[w]/Bits[w]/SInt[w]/Bool），每个 impl 内部直接持有自己的宽度参数写 reg 工厂（`newUIntRegNamed(name, w)` 等，`hdl-signals.typort:248-260`），`payloadExpr` 转发 `this.expr`。
- **用户扩展面**：用户文件为自己的 bundle 手写 3 行 impl（`def payloadExpr = this.zz_expr; def portOut = <逐字段 out_*>`，对齐 apb3AsMaster 模式）；二期给 derive(Bundle) 加 StreamData 派生项（§10 阶段 5，唯一 Rust 触点）。
- **多约束语法**（待验证点，见 §12）：泛型自由函数同时携带两个约束 `def f[bn: BindingName, T][sd: StreamData[T], rn: RegNext[T]](...)` —— regNext 已证明单约束形态（`hdl-signals.typort:631`），双约束按同构写法，若求解器不支持则退化为把 reg 能力并入 StreamData（`regNextNamed` 已在接口里，就是为了这个退化路径）。

**宏生成方案否决理由**：(a) Typort 宏无法覆盖用户后加的 payload 类型，typeclass 可以；(b) prelude 禁 derive（限制 1），宏转写没有挂载点；(c) RegNext 已验证 typeclass 是本语言复刻 Scala 隐式的既成惯例（`docs/spinalhdl-lib-replication.md` 能力对照表第 13 行）。

### 3.2 握手语义与默认驱动（D2）

- `fire = valid && ready`（保留 `hdl-bus.typort:182`）；`isStall = valid && !ready`、`isFree = !valid || ready`（现状 `hdl-stream.typort:30-31`，与 Stream.scala:348/360 一致，收进 `impl[T] Stream[T]`）。Flow 侧补 `fire = valid`（Flow.scala:58）。
- **ready 无隐式默认驱动**（与 SpinalHDL 一致：未驱动的 ready 就是悬空，由 HDL003/HDL001 兜底报警）。便利驱动显式化：
  - `freeRun()`：`ready := True`（保留现状 `hdl-stream.typort:27-29`，Stream.scala:114-118）；
  - `streamSlaveReady[T](s)`：`s.ready := True` 的显式别名（slave 侧默认消费的惯用法），文档标注"slave 侧默认 ready := True 是调用方责任，不是库行为"。
- master/slave 的方向责任划分（对齐 19-stream.typort 头注的现行约定）：master 驱动 `valid/payload`、消费 `ready`；slave 反之。模块端口层由用户用 `input/output` 声明，或用 §3.3 的方向函数。

### 3.3 方向函数与 `<>` 连接（D3，prelude 无 derive 的解法）

**方向函数**（对齐 `apb3AsMaster/apb3AsSlave` 手工模式，`hdl-bus-proto.typort:29-36`）：

```typort
def streamAsMaster[bn: BindingName, T][sd: StreamData[T]](s: Stream[T]): Stream[T] =
    Stream.mk(out_bool(s.valid), in_bool(s.ready), s.payload.portOut)
def streamAsSlave[bn: BindingName, T][sd: StreamData[T]](s: Stream[T]): Stream[T] =
    Stream.mk(in_bool(s.valid), out_bool(s.ready), s.payload.portIn)
// Flow：asMaster = out(valid) out(payload)；asSlave 全翻（Flow.scala:29-30）
```

（签名形态统一为已验证的两段式约束——首段放绑定名/类型/Nat 参数，末段放 typeclass 约束（`sd: StreamData[T]`），同 `hdl-signals.typort:631` 的 regNext 与 `hdl-stream.typort:240` 的 streamFifoConnect；下同，不再逐处重复标注。）

用法：`let m = streamAsMaster(Stream.mk(v, r, d))`（必须在 module 体内，`bn` 绑定名生效；不得对已方向化端口二次调用，同 `hdl-bus.typort:140-145` 的 NOTE）。

**`<>` 连接**：语义完全对齐 derive(Bundle) 生成的 `<>`——"双向各驱动一侧、`isInputPort` 跳过 input/inout LHS"（`hdl-types.typort:50-59` 的 Data 默认体 + `hdl-bus.typort:150-163` 的 Bundle `<>`）。实现为泛型**自由函数**（不占 trait 方法签名）：

```typort
// 单字段双向（对齐 Data.<> 默认体，hdl-types.typort:50-59）：各侧自驱、
// isInputPort 的 LHS 跳过 —— master/slave 端口组间只有互补方向真正落 assign。
def crossField(a: Expr, b: Expr): Unit =
    let _ = match isInputPort(a) {
        case true => unit
        case false => driveExpr(a, b)
    };
    let _ = match isInputPort(b) {
        case true => unit
        case false => driveExpr(b, a)
    };
    unit

// master 方向端口组 <> slave 方向端口组：一条语句全连通（对齐 10-bundle.typort 10c）
def streamCross[bn: BindingName, T][sd: StreamData[T]](m: Stream[T], s: Stream[T]): Unit =
    let _ = crossField(m.valid.zz_expr, s.valid.zz_expr);
    let _ = crossField(s.ready.zz_expr, m.ready.zz_expr);   // ready 反接
    let _ = crossField(m.payload.payloadExpr, s.payload.payloadExpr);
    unit
```

精确展开规则（与 derive(Bundle) `<>` 逐字段一致）：对 `valid/payload` 执行 `if (!isInputPort(m.x)) driveExpr(m.x, s.x)` + `if (!isInputPort(s.x)) driveExpr(s.x, m.x)`；`ready` 互换角色同型处理。因此 `streamCross` 定位为**两个方向化端口组之间的互连/pass-through**（10c 用法）；模块内部逻辑流之间禁止使用（两个非端口 wire 互驱会成组合环，阶段 2 组合环检查会抓），内部连接用：

```typort
// connectFrom：dst ← src 单向（Stream.scala:363-369 connectFrom 语义）
def streamConnectFrom[T][sd: StreamData[T]](dst: Stream[T], src: Stream[T]): Stream[T] =
    let _ = dst.valid := src.valid;
    let _ = src.ready := dst.ready;
    let _ = driveExpr(dst.payload.payloadExpr, src.payload.payloadExpr);
    dst
```

（现状 `streamConnectUInt/Bits`（`hdl-stream.typort:35-45`）被上式取代并删除。）

## 4. 连接与管线原语

全部泛型化（`[T][sd: StreamData[T]]`），一个函数取代现有按类型三份；展开所需的寄存器只落在 `valid`（Bool）与 `rData`（`sd.regNextNamed`）。除特别注明外语义对齐 `Stream.scala`，寄存器一律 `bn` 前缀自动命名（`newBoolRegInitNatNamed` 等，`hdl-signals.typort:260-290`）。

### 4.1 combStage（Stream.scala:416-427，纯改名连接）

```typort
def streamCombStage[bn: BindingName, T][sd: StreamData[T]](input: Stream[T]): Stream[T] =
    let outReady = newBoolNamed(loopName(bn.name) + "_ready");
    let _ = input.ready := outReady;
    Stream.mk(input.valid, outReady, input.payload)
```

无寄存器；只把 ready 落成命名线网（与现状 51-64 行一致）。附带把 `stage` 占位（`hdl-bus.typort:183`）重定向为 `m2sPipe` 别名（Stream.scala:429 `stage() = m2sPipe()`）。

### 4.2 m2sPipe（修 F1；Stream.scala:463-499，collapsBubble 恒 true）

引入寄存器：`rValid`（Bool，init 0）、`rData`（payload 同型）。

```
rValid  := input.valid  when input.ready      （init False）
rData   := input.payload when input.ready     （无 init）
input.ready := out.ready || !rValid           ← F1 修正点（原为 rValid || outReady）
out.valid   := rValid
out.payload := rData
```

- 代价：payload 宽 + 1 个 FF，延迟 1。
- `flush` 参数（`rValid clearWhen(flush)`，Stream.scala:495）与 `holdPayload`（rData 使能改用 `fire`）列为可选重载，一期先出基础版。
- 现有 `whenBegin(input.ready) + regAssign` 的落树手法（`hdl-stream.typort:77-80`）保留，仅改 ready 方程。

### 4.3 s2mPipe（修 F2；Stream.scala:498-512，skid buffer）

引入寄存器：`rValidN`（Bool，init 1）、`rData`（payload 同型）。

```
rValidN     := True init；input.valid 时清 0；out.ready 时置 1   （即 rValidN := (rValidN && !input.valid) || out.ready）
rData       := input.payload when rValidN                        （使能 = rValidN，即 input.ready；对齐 Stream.scala:498 的 RegNextWhen(self.payload, self.ready)）
input.ready := rValidN                                           （组合直通 → 零延迟）
out.valid   := input.valid || !rValidN
out.payload := rValidN ? input.payload : rData                   （Expr.mux）
```

- **rData 使能极性是正确性关键**：必须为 `rValidN`（= `input.ready`）——在反压**起始拍**（rValidN 尚为 1）锁存当前 payload，与 SpinalHDL `RegNextWhen(self.payload, self.ready)` 及已落地实现（`hdl-stream.typort` s2mPipe）一致；若误写成 `!rValidN`，首个反压拍的数据不会被锁存而丢失。

- 代价：payload 宽 + 1 FF + payload 宽 mux2，延迟 0。
- 现实现（`hdl-stream.typort:110-122`）整体重写；补 Bool 版。
- `rValidN` 的"init + 多条件"落树：`createRegWidthInit(name, 1, literal(1))` + 两条 `when` 内 `regAssign`（先 `when(input.valid){ rValidN := 0 }` 后 `when(out.ready){ rValidN := 1 }`，插入序即优先序，后者覆盖前者）。

### 4.4 halfPipe（对齐 Stream.scala:536-551，带宽减半）

```
rValid      := (rValid || input.valid) && !fire   （init False；fire = rValid && out.ready）
rData       := input.payload when input.ready
input.ready := !rValid
out.valid   := rValid；out.payload := rData
```

偏差修正：现实现 `input.ready := outReady || !rValid`（128-148 行）改为 `!rValid`——halfPipe 的卖点是切断全部路径、带宽减半，保留背靠背就变成另一个原语。`flush` 可选。

### 4.5 validPipe（新增，Stream.scala:520-534）

```
rValid      := (rValid || input.valid) && !fire   （init False）
input.ready := fire（= rValid && out.ready）
out.valid   := rValid；out.payload := input.payload   （payload 组合直通）
```

只切 valid 路径，1 个 FF。

### 4.6 门控原语（修 F3/F4；Stream.scala:553-600，全组合、无寄存器）

| 原语 | 展开 | 备注 |
|---|---|---|
| `streamThrowWhen(in, cond)` | `out.valid = in.valid && !cond`；`in.ready = cond || out.ready`；payload 直通 | F3：丢弃拍必须强制消费 |
| `streamTakeWhen(in, cond)` | = `throwWhen(in, !cond)` | F4 修正（原误为 haltWhen） |
| `streamHaltWhen(in, cond)` | = `continueWhen(in, !cond)` | |
| `streamContinueWhen(in, cond)` | `out.valid = in.valid && cond`；`in.ready = out.ready && cond`；payload 直通 | F4：out.valid 必须被 cond 门控 |
| `freeRun()` | `ready := True` | 已正确 |

`clearValidWhen`（Stream.scala:588-596，`out.valid = valid && !cond; in.ready = out.ready`——不强制消费）作为 throwWhen 的姊妹原语一并补上，供"丢弃但不回压"场景。

## 5. FIFO、仲裁与组合原语

### 5.1 StreamFifo（泛型化 + flush + almost 边界）

以现状 RAM 指针式实现（`hdl-stream.typort:192-248`）为基座，改动：

1. **payload 泛型**：`[T][sd: StreamData[T]]`；存储用 `createMem(name, depth, w)` 按位宽落（payload 经 `payloadExpr` 以位向量身份写入；UInt/Bits/SInt/Bool 同 expr 同宽，写读自然成立）。**接口返回 payload 需要知道类型** → 返回 `StreamFifoIO[w, ow, T]`（泛型第三参），或拆成 `streamFifo`（建核心，返回 `Stream[T]` push/pop + 状态信号的结构体）：
```typort
struct FifoStatus[ow: Nat] {
    occupancy: UInt[ow]
    almostFull: Bool
    almostEmpty: Bool
    full: Bool
    empty: Bool
}
def streamFifo[bn: BindingName, T, ow: Nat, pw: Nat][sd: StreamData[T]]
    (depth: Nat, almostThresh: Nat, flush: Bool, push: Stream[T], pop: Stream[T]): FifoStatus[ow]
```

（沿用现状 `streamFifoConnect` 的"传入两个 Stream、函数内接线、返回状态"形态——`hdl-stream.typort:240-248` 与 `examples/hdl/19-stream.typort:69`；`bn` 由 let 绑定名隐式填充，调用形如 `streamFifo[UInt[8]][3][3](4, 1, flush, push, pop)`。）
2. **宽度参数**：指针宽 `pw = log2Up(depth)+1`、occupancy 宽 `ow = log2Up(depth+1)` 仍是显式类型参数（限制 5）；`depth` 为 2 的幂时满/空判定用现成异或高位法（`hdl-stream.typort:217-218`），非 2 幂补"指针回绕到 0"的 when（对齐 Stream.scala:1556-1562 的非幂分支）。
3. **almostFull/almostEmpty**（本设计新增的边界输出，SpinalHDL StreamFifo 无此二信号——记录为有意增补）：`almostFull = occupancy >= (depth - almostThresh)`、`almostEmpty = occupancy <= almostThresh`，组合比较，供流量控制。
4. **flush**：`when(flush) { ptrPush := 0; ptrPop := 0 }`（Stream.scala:1566-1572）。
5. **延迟形态**：默认同步写 + 组合读（现形态，等效 SpinalHDL `withAsyncRead=true` 的 latency-1 形态）；与 SpinalHDL 默认 `latency=2`（读寄存一拍）**记录为有意偏差**（§9）；寄存读版列为二期可选重载。
6. `streamFifoConnect` 保留为便利封装（连 push/pop 两个 Stream，返回 occupancy）。

### 5.2 StreamArbiter（lowerFirst + roundRobin + TransactionLock）

现有 lowerPriority（`hdl-stream.typort:316-363`）保留为 `streamArbiterLowerPriority`，新增 roundRobin：

```typort
def streamArbiterRoundRobin[bn: BindingName, T, cw: Nat, iw: Nat][sd: StreamData[T]]
    (inputs: Vec[Stream[T]] n, count: Nat): StreamArbRet[T][cw]
```

展开（对齐 Stream.scala:800-815 RoundRobin + TransactionLock:842-854 + 901-955 核心骨架）：

```
reqBits      = Vec(inputs.map(_.valid)) 拼成 Bits[n]            （catVecBools，hdl-utils.typort:86）
maskProposal = ohMaskingRoundRobin(reqBits, maskLocked)          （现成 hdl-utils.typort:389-392）
maskRouted   = locked ? maskLocked : maskProposal                （Expr.mux）
maskLocked   = Reg(Bits[n])；when(out.valid) { maskLocked := maskRouted }   （Stream.scala:947-949）
locked       = RegInit(0)；when(out.valid){ locked := 1 }；when(out.fire){ locked := 0 }   （TransactionLock）
out.valid    = (reqBits & maskRouted).orR
out.payload  = muxOH(maskRouted, payload 向量)                    （现成 hdl-utils.typort:456）
inputs[k].ready = maskRouted[k] && out.ready                     （按位 and + 扇出）
chosen       = ohToUInt(maskRouted)（可选输出）；chosenOH = maskRouted
```

- Lock 策略一期只做 **NoLock / TransactionLock** 两个（构造参数 Nat 枚举值 0/1）；SetLock/LambdaLock/FragmentLock 依赖闭包参数，二期。
- SequentialOrder/AssumeOhInput 二期。
- 与 lowerFirst 的共用骨架（validOr/payloadSel/readyFanout，`hdl-stream.typort:316-352`）抽成内部函数，grant 位串来源换成 maskRouted。

### 5.3 StreamFork / StreamJoin

- **Fork 同步**（现状 `streamForkUInt`，`hdl-stream.typort:371-390`）：保留，泛型化；语义 = Stream.scala:1341-1389 synchronous 分支（`input.ready = AND(outputs.ready)`，`out.valid = input.valid && input.ready`，payload 复制）。
- **Fork 异步**（`streamForkAsync`，一期新增）：Stream.scala:1364-1389 异步分支——`linkEnable[n]` 寄存器组（init True），`out[k].valid = input.valid && linkEnable[k]`，`when(out[k].fire){ linkEnable[k] := 0 }`，`when(input.ready){ linkEnable := 全1 }`，`input.ready = AND(linkEnable || !out[k].ready)`…… 按源码逐条转写。AXI 握手兼容性说明随源码注释一并写入文档。
- **Join**：payload 聚合类型（TupleBundle）在 Typort 无对应物，一期只做 SpinalHDL 的 Event 形态与 fixedPayload 形态：
  ```typort
  def streamJoinFire(count: Nat, valids: Vec[Bool] count, readys: Vec[Bool] count, outFire: Bool): Unit
      // outFire = AND(valids)；readys[k] = outFire（Stream.scala:1421-1427 的 Event 形态）
  def streamJoinFixed[T][sd](sources: Vec[Stream[T]] n, out: Stream[T]): Unit
      // out.valid = AND(valids)；sources.ready = out.fire；payload 由调用方显式连（Stream.scala:1440-1443）
  ```

### 5.4 StreamMux / StreamDemux（泛型化 + 修 F5）

- `streamMux[T][sd](select, inputs)` / `streamDemux[T][sd](input, select, portCount)`：把现状 UInt 版（`hdl-stream.typort:255-307`）的 muxSelValid/muxSelPayload/muxSelReady 递归改为 `sd.payloadExpr` 上的 Expr.mux 链；demux 的 ready 分配语义按 Stream.scala:1252-1273 校准（`input.ready := False` 起底、选中分支 `ready := outputs[i].ready`，等价于现状的 per-port `m && input.ready` 形态，保留现状写法）。
- **修 F5**：`flowMuxPayload` 的 `literal(0)` → `literal(k)`（`hdl-stream.typort:435`）。

### 5.5 Flow 原语（Flow.scala）

| 原语 | 展开 | 依据 |
|---|---|---|
| `flowFire` | `fire = valid` | Flow.scala:58 |
| `flowM2sPipe` | `rValid := valid when fire`（init 0）、`rData := payload when fire`；`out.valid = rValid`；`out.payload = rData` | Flow.scala:145-173 |
| `flowTakeWhen/throwWhen` | `out.valid = valid && (!)cond`，payload 直通 | Flow.scala:102-125 |
| `flowToStream` | `Stream.mk(valid, True, payload)`（ready 恒 1） | Flow.scala:72-79 |
| `streamToFlow` | `freeRun()` 后 `Flow.mk(valid, payload)` | Stream.scala:121-127 |
| `flowArbiterLowerFirst` | `OHMasking.first(valids)` 选路 + payload muxOH | Flow.scala:319-330 + Utils |
| `flowMux` | 现状修 F5 后泛型化 | |

## 6. Fragment

**决策 D4：统一到 `Stream[Fragment[T]]`，废弃独立 `StreamFragment[T]` struct**（`hdl-stream.typort:401-406`）。理由：SpinalHDL 的 Fragment 只是 payload 的 Bundle（Fragment.scala:475-477：`class Fragment[T] { val last = Bool() }` + fragment 字段），独立 struct 会让每个 Stream 原语都要出 Fragment 变体（现状 409-425 已出现该苗头）；统一后所有 §4 原语对 `Stream[Fragment[T]]` 直接可用——条件是 payload 满足 StreamData。

**Fragment 的 StreamData impl 的边界（一期定论）**：Fragment 是复合 payload（fragment + last 两字段），无法提供单一 `payloadExpr`，而 `payloadExpr` 恰是泛型连接（streamConnectFrom/streamCross）与组合 mux 选路（Mux/Demux/Arbiter payload 选择）的支点。因此一期：

- `StreamData[Fragment[T]]` **不提供**泛型 impl（泛型 impl 转发内层 StreamData 约束需要"impl 体内访问自身隐式约束"的能力，未验证，见 O2）；
- Fragment 专用的管线/方向操作按 **per-type 展开**：`fragmentM2sPipeUInt/Bits/SInt/Bool`、`fragmentPortOut*` 等（payload 实践上只有四个标量类型，4×N 个小函数可接受；现状 `hdl-stream.typort:409-425` 即此形态的雏形）；
- Fragment 流**不进** streamMux/streamArbiter/streamConnectFrom（payloadExpr 不可得），需要时先 `fragmentToStream` 降级操作 payload 再重组——文档明示此边界；
- 硬件聚合连接（fragment 与 last 一起过 `<>`）留待二期，前置是 O2 的能力验证或 StreamData 接口的向量化改造（`payloadExprs: Vec[Expr] n`）。

工厂与操作（对齐 Fragment.scala + Stream.scala:603-635）：
  - `streamAddFragmentLastBool[T](in: Stream[T], last: Bool): Stream[Fragment[T]]`——arbitrationFrom 语义（valid/ready 透传）+ payload 重组。
  - `streamAddFragmentLastCounter[T](in, counter)`——`when(in.fire){ counter.inc }`，`last = counter.willOverflowIfInc`（Stream.scala:629-635；counter 家族已在 hdl-utils）。
  - `fragIsFirst/fragIsLast/fragLastFire`——`isLast = valid && last`、`lastFire = fire && last`（Fragment.scala:395-398）。
  - `fragmentM2sPipeUInt/Bits/SInt/Bool`——per-type（见上方边界）；落树 = §4.2 m2sPipe 对 valid + fragment/last 两路寄存。
  - 一期不做：insertHeader/filterHeader/reduce/fragmentTransaction（Fragment.scala:18-167，二期候选，工作量集中在 header 缓存 + 折叠累加器）。

## 7. FSM 设计

### 7.1 现状与目标形态

现状两处占位：`hdl-bus.typort:204-231`（纯 enum/struct 占位）与 `hdl-misc-io.typort:203-225`（`stateMachine`/`stateGoto`/`stateIs`——`stateGoto` 是无上下文的无条件 regAssign，只能塞在用户自己的 when 里，无 default-hold、无钩子）。新实现落在 **`src/prelude/hdl/hdl-fsm.typort`**（波次 5 计划文件，`docs/spinalhdl-lib-replication.md` §2 波次表），旧的简化版 API 迁入并删除（同步改写 `examples/hdl/20-misc.typort:82-96`）。

### 7.2 DSL 语法草案（一期纯 typort 函数/方法 API，无新宏）

状态编码：**binary，UInt[w] 承载**（一期不走 enum 承载，理由见 §2.2；`docs/hdl-enum-design.md` 的 EnumCraft 定型后可平移迁移；`log2Up(stateCount)` 因限制 5 不可在刚性参数上归约 → `w` 显式类型参数，`stateCount` 是普通 Nat 值参数仅供自检）。

```typort
module fsmDemo {
    input start = Bool
    input finish = Bool
    output done = Bool
    output st = UInt[2]

    // 声明：w=2 位编码、4 个状态；stateReg init 0（状态 0 = 入口态 = 复位态）
    let ctrl = fsmNew[2](4)

    // 状态句柄：SpinalHDL 风格
    let sIdle = ctrl.state(0)
    let sRun  = ctrl.state(1)
    let sDone = ctrl.state(2)

    // 状态体：whenIsActive 包裹转移（body 是 braced 语句块 → Unit -> Unit，
    // 转写先例：SwitchBuilder.isValueExpr 的 body 形态，hdl-ops.typort:654-657）
    sIdle.whenIsActive({
        when(start) { sRun.goto() }
    })
    sRun.whenIsActive({
        when(finish) { sDone.goto() }
        otherwise    { sIdle.goto() }
    })
    sDone.whenIsActive({
        done := True          // 无 goto → HDL062 提示（可卡死）
    })

    // 钩子
    sDone.onEntry({ done := True })        // 进入 done 的那一拍
    sIdle.onExit({ done := False })        // 离开 idle 的那一拍

    // 组合查询
    st := ctrl.stateReg
    let isRun = sRun.isActive              // stateReg === 1
}
```

API 全集（`hdl-fsm.typort`）：

```typort
struct Fsm[w: Nat] {
    stateReg: UInt[w]      // 寄存器，init 0（入口态）
    stateNext: UInt[w]     // 组合 wire（默认 = stateReg，被 goto 条件覆盖）
    stateCount: Nat        // 仅供自检记录（运行期不参与硬件）
    name: String           // bn 前缀，信号名 / 自检归属
}
def fsmNew[w: Nat][bn: BindingName](stateCount: Nat): Fsm[w]

struct FsmState[w: Nat] { sm: Fsm[w], idx: Nat }
impl Fsm[w: Nat] {
    def state(idx: Nat): FsmState[w]
    def isState(idx: Nat): Bool          // stateReg === idx（Equal[Nat,Bool] for UInt，hdl-ops.typort:276-281）
    def goto(target: Nat): Unit          // 裸 goto（当前 when 上下文，见 HDL064）
}
impl FsmState[w: Nat] {
    def goto(): Unit                     // sX.goto()：stateNext := this.idx（SpinalHDL State.goto 语义）
    def isActive: Bool                   // sm.isState(this.idx)
    def whenIsActive(body: Unit -> Unit): Unit    // when(stateReg === idx) { body() }
    def whenIsInactive(body: Unit -> Unit): Unit  // when(stateReg =/= idx) { body() }
    def whenIsNext(body: Unit -> Unit): Unit      // when(stateNext === idx) { body() }
    def onEntry(body: Unit -> Unit): Unit         // when(stateNext === idx && stateReg =/= idx) { body() }
    def onExit(body: Unit -> Unit): Unit          // when(stateNext =/= idx && stateReg === idx) { body() }
}
```

`goto` 与 SpinalHDL 的 `forceGoto` 无区别（一期）：条件全部由外层 when 表达，`goto()` 本身是无条件写 stateNext（StateMachine.scala:361-376 两者的差别只存在于 SpinalHDL 的 transitionCond 特性，一期不做）。

### 7.3 落树展开（ModuleTree 形态）

`fsmNew` 落树（`createSignalExpr` 路径，`hdl-core.typort:387-482`）：

```
createRegWidthInit("ctrl_stateReg", w, literal(0))      // createRegWidthInit 通道
createWidth("ctrl_stateNext", w)                         // 声明 wire（newUIntNamed）
assign(stateNext, stateReg)                              // 默认驱动（插入序在所有 goto 之前 —— fsmNew 时刻发射）
regAssign(stateReg, stateNext)                           // 时钟沿
```

`sX.goto()` 在用户 when 上下文内落树：`when(<全条件>, assign(stateNext, literal(idx)))`（WhenStack 合成完整使能条件，`hdl-core.typort:263-310`）。`onEntry/onExit/whenIsNext` 落同型 when+assign（body 是用户语句）。

生成 Verilog（生成器依据：when 驱动信号声明为 reg——`hdl-verilog.typort:435-459`；无条件 assign 若 LHS 属 when 驱动集则并入 `always @(*)` 作 blocking default——`hdl-verilog.typort:818-857`；fsmNew 先于状态体执行保证 default 在 if 之前）：

```verilog
  reg  [1:0] ctrl_stateReg;
  reg  [1:0] ctrl_stateNext;
  always @(posedge clk or posedge reset) begin
    if (reset) ctrl_stateReg <= 2'd0;
    else ctrl_stateReg <= ctrl_stateNext;
  end
  always @(*) begin
    ctrl_stateNext = ctrl_stateReg;
    if (ctrl_stateReg == 2'd0 && start) begin
      ctrl_stateNext = 2'd1;
    end
    if (ctrl_stateReg == 2'd1 && finish) begin
      ctrl_stateNext = 2'd2;
    end
    if (ctrl_stateReg == 2'd1 && !(finish)) begin
      ctrl_stateNext = 2'd0;
    end
  end
```

**自检冲突与 HDL011 细化（决策 D5）**：`stateNext` 的驱动事实是 uncondComb=1 + condComb≥1，按现行判定（`hdl-check.typort:739/756-758`）必报 HDL011。但该判定是假阳性：生成器对 when 驱动的组合信号把无条件 default 与条件覆盖**合并进同一个 `always @(*)`**（blocking default + if，`hdl-verilog.typort:827-853`），不存在 assign+always 双驱动。细化方案（.typort 层改 `ruleDrivers`）：

- HDL011 新判定：`uncondComb ≥ 1 ∧ condClk ≥ 1`（组合 default + 时钟 when 覆盖 —— 真非法，assign + always @(posedge) 冲突）。
- 原"uncondComb ∧ condComb"场景：当该信号同时有任何时钟驱动（anyClk）时由 HDL012 覆盖；纯组合的"default + 条件覆盖"是 FSM 的合法骨架，豁免。
- **与自检阶段 2-4 设计的衔接**：`docs/hdl-selfcheck-phase234-design.md` 已在开放问题 7 独立指出"HDL011 的措辞可能过严"（生成器实际会合并 default，hdl-verilog.typort:836-842），且其 latch 规则（HDL032）以 `uncondComb = 0` 为进入条件——本细化后，FSM 的 stateNext（uncondComb=1）既不触发 HDL011 也不进 latch 判定（有 default 即无锁存），两个设计互补无冲突；实现时两处改动应合入同一次 HDL011 语义调整。
- 兜底退化（若不想动检查器）：fsmNew 的 default 用 `whenBegin(literal(1))` 包裹发射（condComb 计数，绕开 uncond 组合）——生成 `if (1) begin ... end`，合法但难看；仅作备选记录。
- legacy_tests 无 HDL011 期望用例（已核对），细化无回归包袱。

### 7.4 转移覆盖检查（自检规则草案，HDL060-064）

编号从 HDL060 起，避开 HDL030-050（自检阶段 2-4 预留段——`docs/hdl-selfcheck-phase234-design.md` 实际规划 HDL030-039，040-050 留余量）与 HDV 段。机制：新增可变全局 `FsmCtx`（module 宏 prologue 重置，对齐 `hdl-macros.typort:434-437` 对 WhenStack/HdlLoopIdx 的处理——纯 .typort 改动）：

- `fsmNew` 登记 `{ name, w, stateCount }`；
- `whenIsActive` 执行时 push 当前 idx、结束时 pop（栈形态仿 `HdlLoopIdx`，`hdl-core.typort:749-798`）；
- `goto` 追加一行 `"mod|fsm|from|to"`；
- `checkModuleTree` 收尾（`hdl-check.typort` 内新增 `checkFsmLog`，挂在现有 HDL 规则之后）排水本模块记录并执行规则。

| 码 | 规则 | 判定 | 级别 |
|---|---|---|---|
| HDL060 | goto 目标越界 | `to ≥ stateCount` | warning（必错） |
| HDL061 | 不可达状态 | `idx ≠ 0 ∧ idx ∉ {所有 goto.to}`（无入边；入口态 0 由复位保证可达） | warning |
| HDL062 | 状态无出边（可能卡死） | `whenIsActive(idx)` 内无任何 goto 且 idx 无无条件出边 | warning（终态可显式豁免：`sX.noExitCheck()` 标记） |
| HDL063 | 入口态不一致 | 预留：一期入口恒 0；引入 `fsmSetEntry(idx)` 后检查 `init == entry ∧ 入口恰一个` | warning |
| HDL064 | goto 在状态上下文之外 | `goto` 时 whenIsActive 栈为空（对应 SpinalHDL 的 inGeneration assert，StateMachine.scala:362） | warning |

穷举性说明：HDL061+HDL062 合起来即"转移覆盖检查"——每个状态都有入边（可达）与出边（不卡死）。转移动机的穷举（每个状态的输入组合都覆盖）属 latch/条件覆盖范畴，归自检阶段 3（HDL040 段），本文不重复设计。

### 7.5 多状态机嵌套/子状态机范围

- **一期支持**：同一模块多个 FSM 并存（各自 `bn` 前缀隔离信号名，FsmCtx 按实例区分）；FSM 与普通 when/switch/for 混用；goto 前向/后向任意转移；FSM 输出驱动 Stream valid 等组合逻辑。
- **一期不做**：`StateFsm`（状态即子状态机，State.scala:273+）、`StatesSerial/Parallel`（State.scala:295/326）、`StateDelay`（State.scala:382+）、显式 `StateBoot` + `startFsm/exitFsm` 生命周期（StateMachine.scala:90/431）。替代写法写进文档：子状态机 = "父 FSM 状态里启停一个独立小 FSM"（父状态 goto 由子 FSM 的 `stateReg === 终态` 组合信号驱动），不需要库支持。
- **二期候选**：StateDelay（= `fsmWhenIsActive` + 内部 counter + `when(counter.willOverflowIfInc){ goto() }`，纯语法糖）；`derive(Bundle)` 式的 FSM surface macro（`fsm ctrl[2](4) { state idle { … } }`，需 Rust parser 扩展，§10 阶段 5）。

### 7.6 与硬件 Enum 的迁移点

`fsmNew` 的编码在一处收口（`createRegWidthInit` + `===` 比较 + `literal` 常量）。硬件 Enum（spinalhdl-gap.md §8 二期候选）落地后，只需替换该收口点的类型与比较实现（`Enum === 枚举值`），DSL 层 API 不变——`state(idx: Nat)` 换成 `state(sym: EnumSym)`。

## 8. 实现落点分级

| 项 | 纯 typort | 需 Rust | 说明 |
|---|---|---|---|
| StreamData typeclass + 全部原语泛型化 | ✅ | — | hdl-stream.typort 重写 + hdl-bus.typort 微调 |
| §1.2 缺陷 F1-F5 修复 | ✅ | — | 全在 hdl-stream.typort |
| Stream/Flow 方向函数与 `<>` | ✅ | — | 复用 in_u/out_* 与 driveExpr/isInputPort |
| StreamFifo/Arbiter/Fork/Join/Mux/Demux | ✅ | — | 复用 ohMaskingRoundRobin/muxOH/ohToUInt（hdl-utils） |
| Fragment 统一 + 工厂 | ✅ | — | addFragmentLast/isFirst/isLast/lastFire 纯 .typort；Fragment 管线 per-type（§6 边界） |
| FSM DSL + 落树 | ✅ | — | 新 hdl-fsm.typort + hdl-macros.typort prologue 加 `FsmCtx` 重置 |
| HDL060-064 自检 + HDL011 细化 | ✅ | — | hdl-check.typort + report_check_issue 现成通道（`docs/hdl-selfcheck-design.md` §4） |
| derive(Bundle) 派生 StreamData（用户 bundle 免手写 impl） | — | 阶段 5 | `src/L13_namespace/parser/derive.rs` 加派生项 |
| FSM surface macro（`fsm` 语句块） | — | 阶段 5 | parser/宏层，纯便利性 |
| StreamFifoCC/跨时钟家族 | 已有 | — | hdl-crossclock.typort:182-222，本设计不碰 |

结论：**一期零 Rust 改动**；全部落点为 prelude .typort + examples + legacy_tests 断言。

## 9. 与 SpinalHDL 对应及有意偏差

| SpinalHDL | 本设计 | 偏差说明 |
|---|---|---|
| `Stream[T] <: Bundle with IMasterSlave` | `struct Stream[T]` + StreamData typeclass + 手工方向函数 | 方向不进类型系统（限制 1）；`asMaster` 的 in/out 语义由 portOut/portIn 承担 |
| `fire/isStall/isFree/freeRun/connectFrom/<>` | 同名同义 | 一致 |
| m2sPipe(collapsBubble=true) | 同（恒 collapsBubble，flush/holdPayload/keep/crossClockData 参数不设） | 参数化瘦身：crossClockData 归 hdl-crossclock |
| s2mPipe / halfPipe / validPipe / combStage | 同 | halfPipe 恢复带宽减半语义（F 系列修正） |
| throwWhen/haltWhen/continueWhen/takeWhen/clearValidWhen | 同 | takeWhen 恢复 throwWhen(!cond) 本义 |
| StreamFifo(depth, latency=2, flush, occupancy/availability) | streamFifo(depth, almostThresh, flush) | 有意偏差：①默认组合读（latency-1 形态）；②新增 almostFull/almostEmpty；③availability 不设（= depth - occupancy，调用方可自算） |
| StreamFifoCC / StreamCCByToggle | 已在 hdl-crossclock（wave 7） | 非本设计范围；文档尾注"单时钟域限制"已过时（§1.3） |
| StreamArbiter（ArbitrationPolicy × LockPolicy 全组合） | lowerFirst/roundRobin × NoLock/TransactionLock | 其余策略二期 |
| StreamFork(synchronous) / StreamForkAsync | 同名两函数 | 一致 |
| StreamJoin(TupleBundle/Vec) | streamJoinFire（Event）/ streamJoinFixed | 无 TupleBundle 的对应物，payload 聚合交调用方 |
| StreamMux/Demux（含 joinSel/regSel 变体） | 基础版 | joinSel/regSel 二期 |
| Flow 全家族 | §5.5 | FlowFifo→经 flowToStream 复用 StreamFifo |
| Fragment[T] + StreamFragment/FlowFragment 工厂 | `Stream[Fragment[T]]` 统一 + addFragmentLast 两版 | StreamFragment 独立 struct 废弃 |
| FSM：State/StateMachine/StateEntryPoint/whenIsActive/whenIsInactive/onEntry/onExit/whenIsNext/goto | §7.2 全对应 | 有意偏差：①无独立 StateBoot——入口态即复位态（SpinalHDL 复位后先落 boot 态再 startFsm 跳入口，**入口态的 onEntry 在本设计永不触发**）；②编码 binary UInt（非 SpinalEnum）；③无 forceGoto/transitionCond 之分；④状态覆盖检查走 HDL060-064 warning（SpinalHDL 是 elaboration assert） |
| FSM：StateFsm/StateDelay/StatesSerial/Parallel | 不做（§7.5） | 文档给出替代写法 |

## 10. 分阶段实施计划

| 阶段 | 内容 | 交付 | 验收 |
|---|---|---|---|
| S1 修正与泛型化基座 | 修 F1-F5；StreamData typeclass；m2sPipe/s2mPipe/halfPipe/combStage/validPipe/门控原语/freeRun/isStall/isFire 泛型化；streamConnectFrom/streamCross/streamAsMaster/streamAsSlave；Flow 家族 | hdl-stream.typort 重写（预计 ~500 行） | §11 用例 19a'-19d'；L1+L2 |
| S2 组合原语 | StreamFifo 泛型化+flush+almost；Arbiter（lowerFirst 收编 + roundRobin + lock）；Fork 同步/异步；Join；Mux/Demux 泛型化 | hdl-stream.typort 扩展 | 用例 19e'-19h'；L1+L2+L3（FIFO 顺序性） |
| S3 Fragment | StreamData[Fragment[T]]；addFragmentLast 两版；isFirst/isLast/lastFire；废弃 StreamFragment struct | hdl-stream.typort + 示例改写 | 用例 19i'；L1+L2 |
| S4 FSM | hdl-fsm.typort；module 宏 FsmCtx 重置；HDL060-064 + HDL011 细化；删除 hdl-misc-io 简化版并改写 20-misc | hdl-fsm.typort + hdl-check/hdl-macros 增量 | 用例 26-fsm 全部；L1+L2+L3（状态序列） |
| S5（二期候选） | derive(StreamData)、FSM surface macro、StateDelay、StreamFifoLowLatency、Mux/Demux joinSel/regSel、Arbiter 其余策略、fragmentTransaction、硬件 Enum 迁移 | 各自立项 | — |

每阶段结束跑全量 examples 回归（L1）与 legacy_tests 断言（L2），L3 按 `tools/spinalhdl-verify/verify.py` 协议（仿真器缺席时标记 unverified）。

## 11. 验收用例

以下片段为验收基准（新增/改写 `examples/hdl/`），"期望 Verilog 关键行"即 L2 断言的 contains 串。

### 11.1 m2sPipe + s2mPipe 级联（改写 19a，S1）

```typort
module streamPipeFix {
    input push_valid = Bool
    output push_ready = Bool
    input push_data = UInt[8]
    input p2_ready = Bool
    let push = Stream.mk(push_valid, push_ready, push_data)
    let p1 = streamM2sPipe(push)
    let p2 = streamS2mPipe(p1)
    output outValid = Bool
    output outData = UInt[8]
    outValid := p2.valid
    outData := p2.payload
}
```

（示例统一用自由函数调用形态——现状 19-stream.typort 即是；`.m2sPipe()` 方法糖依赖泛型 impl 方法求解（与 freeRun/isStall 同族），支持与否不作为验收依据。）

期望关键行（命名按 `bn` 前缀展开）：

```verilog
  reg [7:0] p1_data;
  reg p1_valid;
  assign push_ready = (!p1_valid || p2_ready);        // F1 修正：空随时收/满等下游
  assign p2_valid = (push_valid || (!p1_validN));     // s2mPipe skid
  assign p1_valid = ...                               // rValid 寄存输出
```

### 11.2 throwWhen/takeWhen 门控（改写 19b，S1）

期望：`tw_valid = (h1_valid && (!cond))` 且 `h1_ready = (cond || tw_ready)`（F3）；`takeWhen` 生成 `(!(!cond))` 折叠的等价条件（F4）。

### 11.3 FIFO almost 边界 + flush（改写 19c，S2）

```typort
module streamFifoAlmost {
    input pushValid = Bool
    output pushReady = Bool
    input pushData = UInt[8]
    output popValid = Bool
    input popReady = Bool
    output popData = UInt[8]
    input flush = Bool
    output occ = UInt[3]
    output aFull = Bool
    let push = Stream.mk(pushValid, pushReady, pushData)
    let pop = Stream.mk(popValid, popReady, popData)
    let f = streamFifo[UInt[8]][3][3](4, 1, flush, push, pop)
    occ := f.occupancy
    aFull := f.almostFull        // occupancy >= 3
}
```

期望：`assign aFull = (3 <= occ)` 形态的比较行、`assign push_ready = (!full)`、`ctrl` 无关；L3 激励覆盖"满→almostFull 拉高→flush 清空"序列。

### 11.4 roundRobin 仲裁（S2）

两输入轮流请求时 grant 交替：期望含 `maskLocked` 寄存器声明、`locked` 寄存器、`assign out_valid = (...|...)`、`assign a_ready = (maskRouted[0] && out_ready)`。L3：A/B 持续请求下 chosen 序列 0,1,0,1（TransactionLock 保证同事务不被抢占）。

### 11.5 Stream[Fragment[T]] last 位（S3）

```typort
module fragLast {
    input inValid = Bool
    output inReady = Bool
    input inData = UInt[4]
    input str_ready = Bool
    output last = Bool
    let si = Stream.mk(inValid, inReady, inData)
    let cnt = counter(2)                    // hdl-utils counter 家族
    let fr = si.addFragmentLast(cnt)
    last := fr.payload.last
}
```

期望：`assign last = ...` 由 `willOverflowIfInc` 组合链产生；L3：5 元素一组的 last 脉冲周期核对。

### 11.6 FSM 基线（新增 examples/hdl/26-fsm.typort，S4）

§7.2 的 `fsmDemo` 全文即用例。期望 Verilog = §7.3 代码块（关键断言串：`ctrl_stateNext = ctrl_stateReg;` 默认行在 if 之前、`if (ctrl_stateReg == 2'd0 && start)`、`ctrl_stateReg <= ctrl_stateNext;`、复位行 `if (reset) ctrl_stateReg <= 2'd0;`）。

自检触发用例（L2 断言 warning 文本）：
- `sDone.goto()` 写 `sX.goto2()`（越界常量 4）→ HDL060；
- 4 状态只连 2 个 → HDL061；
- `sDone.whenIsActive({ done := True })` 无 goto → HDL062（加 `sDone.noExitCheck()` 后消失）；
- 状态体外的裸 `ctrl.goto(1)` → HDL064；
- FSM 模块不再出现 HDL011（D5 细化的回归断言）。

L3：`v_fsm.typort` 时序激励——start 脉冲后状态序列 0→1→(finish)2→(复位路径)0，逐拍与 Python 参考状态机比对（协议见 `docs/spinalhdl-lib-replication.md` §4）。

## 12. 风险与开放问题

- **O1 多 typeclass 约束语法**：`[sd: StreamData[T], rn: RegNext[T]]` 同函数双约束未在库中出现过（现库只证明单约束，`hdl-signals.typort:631`）。缓解：StreamData 自带 `regNextNamed`，必要时单约束闭环（§3.1 退化路径）。S1 第一天用 3 行探针验证。
- **O2 "impl 体内访问自身隐式约束"能力**：`impl[T][sd: StreamData[T]] StreamData[Fragment[T]]`（泛型 impl 转发内层约束）未验证——这是 Fragment 泛型化（摆脱 per-type）与用户 bundle 免手写 StreamData 的共同前置。失败不影响一期（§6 边界已给出 per-type 落点），决定二期的 StreamData 向量化改造（`payloadExprs: Vec[Expr] n`）是否需要。
- **O3 HDL011 细化的连带影响**：新判定下原"uncondComb ∧ condComb"纯组合场景不再报警——若未来生成器改变合并策略（不再把 when 驱动信号的 default 并入 always@(*)），该豁免会变成真双驱动。缓解：在 hdl-check 注释里显式声明与 `hdl-verilog.typort:827-853` 的耦合（对齐 `hdl-types.typort:26-28` "keep them in sync" 惯例）；与阶段 2-4 设计的 HDL010/011 区间感知抑制（`docs/hdl-selfcheck-phase234-design.md` §4.4）合并实施，避免两处独立改同一规则。
- **O4 现状 m2sPipe 的 L3 盲区**：F1-F5 能存活至今说明现有激励未覆盖满/反压场景——S1 的 L3 用例必须补"valid 保持 + ready 拉低 N 拍 + 恢复"的标准反压序列，否则修正无法判定。
- **O5 stateNext 的 always@(*) 依赖**：FSM 展开依赖"when 驱动 wire → reg 声明 + blocking default"生成器行为（`hdl-verilog.typort:435-459/827-857`）。该行为是现行既定语义（examples 大量使用），风险低，但 26-fsm 的 L2 断言会锁定它。
- **O6 状态计数与检查日志的归属**：FsmCtx 是文件级全局，跨模块 create 重放（`docs/hdl-selfcheck-design.md` §2 的 ~3 次重放）会重复记录 goto——沿用 CheckIssues 的行级去重 + seen-set 通道即可，规则侧按 `"mod|fsm|from|to"` 整行幂等。
- **O7 prelude 文件加载顺序**：hdl-fsm 依赖 hdl-check 的报告通道与 hdl-utils 的 counter；需排在 hdl-check 之后（对齐 hdl-check 现加载位次说明，`hdl-check.typort:62-67` 的 chkCdEq 本地拷贝先例）。
