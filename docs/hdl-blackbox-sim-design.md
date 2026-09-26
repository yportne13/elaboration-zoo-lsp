# HDL assert 断言 / BlackBox / 仿真集成设计（hdl-blackbox-sim）

> 状态：设计稿（2026-09-26）。P1（assert 全链）已实现（2026-09-26，commit ede8773 + 评审修复）；P2（BlackBox）/P3 未实现。
> 输入：docs/spinalhdl-gap.md §5（BlackBox 行）/§6（assert 行）/§7 第 5 项/§8；docs/spinalhdl-lib-replication.md §4（仿真验收策略）/§5（B 级语言扩展）。
> 结论先行：**assert 与 BlackBox 的全部语言侧机制落在 prelude .typort 文件**（`Expr`/`ModuleDef` 都是 typort enum/struct，宏系统也是 .typort 内的 `macro_rules`），Rust 侧只剩仿真失败回读（dut.rs ~30 行）与 `typort test` 退出码（cli.rs ~15 行）。**进程内仿真（SpinalSim FFI/VPI）不做**，以"Dut 协议 + 生成 testbench + in-design assert"替代。

## 1. 背景与现状

### 1.1 assert 与 BlackBox 的现状

- assert：完全缺失。`Expr`（src/prelude/hdl/hdl-core.typort:96-153）无断言变体，hdl-verilog.typort 的产码路径无 `$display`，examples 的 Verilog-compat 层把 `$display` 列为"仍未支持"（examples/hdl/23-verilog-compat.typort:21）。spinalhdl-gap.md:85 标记"重要"。
- BlackBox：语法占位 stub（src/prelude/hdl/hdl-bus.typort:191-202）——`struct BlackBox { name }` 只有两个恒等方法 `addGeneric`/`setDefinitionName`，不存储信息、不进 ModuleTree、无产码。spinalhdl-gap.md:75 标记"可选"、spinalhdl-lib-replication.md §5 把"BlackBox 真实代码生成"列为 B 级前置。
- assert 的使用模式在 SpinalHDL 参考库中真实存在：lib/src/main/scala/spinal/lib/Stream.scala:658（`assert(!(valid.fall...) , "Stream valid persistence failed")`）、Stream.scala:676 `formalAssertsMaster`（`when(past(isStall)) { assert(valid, ...) }`——when 包裹的时钟断言）。本设计落地后 hdl-stream.typort 可复刻这组不变量（P3 候选）。

### 1.2 仿真现状：外部仿真器 harness 已就位

src/sim/ 是一套完整的"Rust 宿主驱动外部仿真器"管线（不是进程内仿真）：

| 文件 | 契约 |
|---|---|
| mod.rs:239 SimConfig | `{top, sources, workdir, simulator, verilator_args, trace}`；`compile()`（mod.rs:257）= `emit::emit_design`（want_manifest=true）→ 写 `<top>.v` + `<top>.manifest.json` → 后端 build |
| mod.rs:46-147 manifest | `designManifestVL` JSON（hdl-verilog.typort:1538）反序列化为 PortDef/ClockDef/ModuleInfo；端口方向/宽度校验的依据 |
| runner.rs:22 Simulator | Verilator/Icarus/Vcs/Vivado 四后端，同一 `SimulatorRunner::build` trait（runner.rs:84） |
| runner.rs:64,77 | BuildPlan → CompiledModel `{exe, exe_args, workdir, manifest}`；vvp/xsim 用 exe_args 携带设计文件 |
| verilator.rs:92 harness_cpp | C++ harness：stdin/stdout 行协议（`set PORT HEX` / `get PORT` / `eval` / `finish`），cycle-accurate |
| iverilog.rs:95 build | `iverilog -g2005 -o model.vvp tb_<top>.v <top>.v`（:119）→ exe=vvp；tb 由 verilog_harness.rs:22 生成，同协议，eval/get 内 `#1` 让非阻塞赋值 settle |
| dut.rs:54 roundtrip | Dut 句柄：`set`（:163，方向/宽度校验）`get`（:199）`eval`（:205）`wait_edges`（:154）`clock().fork(period)`（dut.rs:257，SpinalSim forkStimulus 形状，注释见 dut.rs:1-14）；roundtrip 循环跳过 `VCD ` 前缀行（:72） |
| cli.rs:575 run_test | `typort test` = compile + spawn + 一次 smoke eval + finish（cli.rs:617-622）；`[test] simulator/trace` 配置在 src/config.rs:86-88 |
| tests/sim_tests.rs | 既有验收模式：工具缺失则 SKIP（:75-77），golden 向量逐端口比对（:251 reverse / :275 popcount），verilator/iverilog 交叉复检（:360），时序测试用手动 set("clk") 或 clock().fork |

**通过判据现状**：编译失败 → `SimError::CommandFailed`（mod.rs:216 run_tool 截尾 2000 字符）；行为不匹配 → 测试代码里宿主侧 `assert_eq!(dut.get(...), golden)`。**设计内部的失败（断言）目前无处发生**——这就是 P1 要补的洞。

### 1.3 本设计必须服从的既有机制（约束清单）

1. **语句落树只有一条通道**：`createSignalExpr`（hdl-core.typort:387）——create*/reg/mem/instance 直入 `ModuleTree`，其余走 `_ =>` 默认臂 = `addWhenContext(e)`（hdl-core.typort:379）包 `when(完整使能条件, e, None)` 再入树。when/elsewhen/otherwise/switch 全部编译为"每条语句带完整条件"的 when 节点（hdl-core.typort:263-277 注释），产码无需重建 else-if 链。**assert 走默认臂即免费获得 when 语境**。
2. **`:=` 分派**：`pickAssign`（hdl-core.typort:697）按 `isRegExpr(lhs)` 选 regAssign/assign，compat 的 `always @(*)` 上下文（CombCtx，hdl-core.typort:674）改写为组合驱动。regAssign 的"自动识别"识别的是**赋值目标的寄存器性**——assert 没有 LHS，这条路径对它无意义（§3.3 决策）。
3. **产码是纯 typort 函数**：moduleDefVL（hdl-verilog.typort:1222）按固定段落拼 `header + wire + reg + mem + assigns + clocked + always + instances`；clocked 块按 cd 收集（collectClockLinesCd，hdl-verilog.typort:624），额外时钟域由 collectClockCdsOne（:584）从 regAssignCd 收集并进端口表（extraCdPortsVL，:1198）。
4. **自检是纯 typort + report_check_issue builtin**：checkModuleTree（hdl-check.typort:893）在 create 侧 `_res` 处跑 runChecks（:867）；端口方向表 "ModulePortTable"（:514）按模块名幂等注册；HDL020/021/022/025 全部查这张表（ruleConnDir :787 / ruleInsts :846）。
5. **实例连接是原始字符串机制**：`u.a := x` / `x := u.a` 记录 assign(subSignal(...))，collectInstHelp（hdl-verilog.typort:1156）按 seenInsts/seenConns 平行表拼 `.a(x)`；方向不可知（:1132 NOTE：复杂 RHS 原样透传）。`instanceWithPorts` 是完全的手工逃逸口，HDL024 警告之（hdl-check.typort:850）。
6. **match 穷尽性是硬成本**：`Expr` 加变体会打破无 catch-all 的穷尽 match——现有仅 3 处：exprVL_proc（hdl-verilog.typort:84）、exprVL（:187）、exprKey（hdl-check.typort:246）。其余扫描器都有 `case _`。**注意反向坑**：`collectAssignLinesFiltered`（:750）的 `case _ => lcons (exprVL e)` catch-all 会把陌生语句节点当连续 assign 发射——assertExpr 必须加显式跳过臂。

## 2. 目标与非目标

**目标**

1. assert 一等公民：typort HDL 任意语句位置可写 `assert(cond, "msg")`，产码为 translate_off 包裹的时钟断言块；条件折叠 when 语境；额外时钟域支持。
2. BlackBox 真实产码：vendor 原语可声明（端口表 + Verilog `parameter`），`designVL`/`moduleTreeVL` 发射空 module stub（`#(parameter ...)` 头 + 端口 + `endmodule`），实例化自动带 `#(.K(v))`，自检 HDL020/021/022/025 全覆盖。
3. 仿真闭环：模型内断言失败 → stdout 标记行 → Dut 捕获 → cargo test 断言 / `typort test` 退出码 1。
4. 清账：spinalhdl-gap.md §7 第 5 项（assert）与 §8"BlackBox 代码生成"落地。

**非目标（本设计明确不做）**

- 进程内仿真（SpinalSim 的 verilator FFI / iverilog VPI）——§5.3 给出结论与替代程度。
- formal 后端（`assume`/`cover`/SVA/SymbiYosys）——§3.6 给结论：不同批。
- `initial` 断言、组合语境断言（`always @(*)` 内 `$display`）。
- 断言消息的运行时信号值插值（`%0d` of signal）——消息是 elaboration 期 String（SpinalHDL 语义相同：Scala 字符串插值在 elaborate 期求值）。
- BlackBox 行为模型的 typort 内表达（黑盒体非空）；inout 黑盒端口的驱动语义扩展（沿用现状：tri-state 不建模）。

## 3. assert 设计

### 3.1 API 草案与三语境落树

```typort
assert(cond, "msg")        // 默认严重级 error
assertFatal(cond, "msg")   // display 标记行 + $finish
assertInfo(cond, "msg")    // / assertWarning
assertSev(cond, "msg", AssertWarning)          // 通用入口
assertCd(cond, "msg", cd)  // 额外时钟域（assertSevCd 同构）
```

工厂为普通 typort def（`def assert(cond: Bool, msg: String): Unit`，签名含 String；`assert` 名字经全 prelude grep 确认无冲突）。**P1 不加宏臂**：module 体/when 体/def 体都是 `Expr` 片段语句表，裸调用经 raw 直通臂（hdl-macros.typort:240）即可工作；Verilog-compat 模块同样经 VExpr 直通臂（hdl-verilog-compat.typort:488）——**compat 层零改动**。`assert cond, "msg"` 无括号语句形态列为可选宏臂（一条 `Expr` 表臂，成本极低，后补）。

| 语境 | 触发 | 落树（ModuleDef.expr 里长什么样） |
|---|---|---|
| 模块体顶层 | `assert(c, "m")` | `assertExpr(c, "m", sevError)` 直入 expr 表 → 无条件时钟断言 |
| when 内 | `when c { assert(a, "m") }` | `when(c 的完整使能条件, assertExpr(a,"m",sev), None)`——createSignalExpr 默认臂 addWhenContext 自动包，与 assign 同机制，零新代码 |
| 时钟域内 | 模块声明 `module m[cd]` | def.cd = cd，断言进该 cd 的断言块（md.cd 主域；`assertCd(c,"m",cd2)` 进额外域） |

### 3.2 Expr 变体设计

hdl-core.typort:96 的 `Expr` 追加（放 memWrite 之后，紧邻层级变体）：

```
assertExpr(cond: Expr, msg: String, sev: AssertSeverity)
assertExprCd(cond: Expr, msg: String, sev: AssertSeverity, cd: ClockDomain)
```

- `AssertSeverity` 枚举（hdl-core.typort，ClockDomainConfig :81 旁）：`AssertInfo / AssertWarning / AssertError / AssertFatal`。Expr 变体携带自定义 enum 有先例（ClockDomain/ClockDomainConfig 字段）。
- 不带 kind 字段（不预埋 assume/cover）：为不会生成的分支留死代码路径不如二期加变体（Expr 枚举扩展成本低、match 波及面已枚举）。
- ModuleTree 落点：**不另立树**，与 memWrite 一样平铺在 def.expr 语句列表里；收集器按变体匹配。msg 为 elaboration 期 String（`nat_to_dec`/`string_concat` 可拼动态位宽文本）。
- 工厂实现（放 hdl-signals.typort 工厂族旁）：

```
def assertSev(cond: Bool, msg: String, sev: AssertSeverity): Unit =
    let dummy = createSignalExpr("", assertExpr(cond.expr, msg, sev));
    unit
```

走 createSignalExpr 默认臂 → when 语境自动折叠（§3.1）。不挂 `:=`/pickAssign（决策见 §1.3-2）。

### 3.3 Verilog 生成

新增收集与发射（hdl-verilog.typort，与 clocked 族逐一同构）：

| 新函数 | 镜像自 | 语义 |
|---|---|---|
| `hasAssert(e)` | hasRegAssign（hdl-core.typort:485） | 含 assertExpr、when/block 递归；**不含** assertExprCd、不含 memWrite 语义 |
| `hasAssertCd(e, cd)` | hasRegAssignCd（hdl-verilog.typort:558） | 额外域版本 |
| `collectAssertLinesCd(es, cd, isMain)` | collectClockLinesCd（:624） | assertExpr 归主域（isMain）、assertExprCd 按 cdEq 匹配、when 节点含匹配 assert 才整节点收集；行文 = exprVL_proc(节点) |
| `collectAssertCdsOne/es` | collectClockCdsOne（:584） | **必须并入 assertExprCd 的 cd**，否则额外域断言缺 `input wire cd2_clk`（extraCdPortsVL 只读 collectClockCds）。实现时与 collectClockCdsOne 合并为一个 walker |
| `assertsVL(es, cd)` | clockedBlockVL（:998） | 整块发射（见下） |

发射形态（一行断言一条 `if`，when 包裹 = 嵌套 if，与 when 产码同构）：

```verilog
  // synthesis translate_off
  always @(posedge clk) begin
    if (!(count < 100)) begin
      $display("TYPORT_ASSERT_ERROR %0t %m: count overflow", $time);
    end
    if (count >= 50) begin
      if (!(count < 100)) begin
        $display("TYPORT_ASSERT_ERROR %0t %m: half-way guard", $time);
      end
    end
  end
  // synthesis translate_on
```

决策明细：

- **合并策略：独立成块，不并入既有 always**。理由：(a) translate_off 整块包裹一次最干净（逐语句包裹产码噪声大）；(b) 敏感列表恒为 md.cd 的 `(posedge clk)`，与 clocked 块的复位/初始化语义无关——断言不复位；(c) 不污染 buildMergedAlwaysBlock（:849）的组合语义。落点：moduleDefVL（:1222）body 串 `clocked` 之后 `always` 之前。
- **clk 端口合成**：moduleDefVL 的 `has_seq`（:1248）扩为 `clocked 非空 || hasAssertLines`——纯组合模块带断言也要有 clk（SpinalHDL 同：断言恒为时钟语义）。复位端口条件（has_init）不受断言影响。Verilog-compat 模块已自声明 `input clk`（clk_declared 分支，:1272）不受影响。
- **条件发射**：`if (!(" + emitCondStr(cond) + "))`（emitCondStr :177 去冗余括号）。
- **严重级映射**（默认可移植目标 = iverilog `-g2005`（iverilog.rs:119）与 verilator `-Wno-fatal`（verilator.rs:204）都吃 `"$display"`/`"$finish"`）：

| AssertSeverity | 生成 |
|---|---|
| AssertInfo | `$display("TYPORT_ASSERT_INFO %0t %m: <msg>", $time);` |
| AssertWarning | 同上，WARNING |
| AssertError（默认） | 同上，ERROR |
| AssertFatal | ERROR 行 + `$finish;`（杀模型提前退出，宿主看到"model closed stdout"即致命失败信号） |

- **标记行格式**：`TYPORT_ASSERT_<SEV>` 单词前缀 + `%0t` + `%m`（层次实例路径，iverilog/verilator 均支持）——模块名不进树，由仿真器按作用域填充，比把模块名烘进 msg 更准（父模块里的子实例断言报全路径）。
- **SV-native 模式**（`$error/$fatal/$info/$warning` 系统任务 + verilator `--assert`）列为二期发射器开关；`verilator_args` 通道（mod.rs:249）已就位，只差产码分支。
- **translate 注释对齐 SpinalHDL**：`// synthesis translate_off/on`（yosys/DC/Quartus/Vivado 识别）；老 XST 的 `// pragma translate_off` 记开放问题。
- **穷尽 match 新臂**：exprVL_proc（:84）与 exprVL（:187）加 assertExpr/assertExprCd 两臂（渲染同上）；`collectAssignLinesFiltered`（:750）加显式跳过臂（防 catch-all 误发射为连续 assign）。
- **消息转义约束**：v1 消息原样透传进 `$display` 字符串——含 `"` 或 `%` 的消息会产非法 Verilog。P1 以文档约束 + 候选 lint（§3.5 HDL027）处理。

### 3.4 自检框架交互

- **assert 条件算一次"读取"**：scanStmt（hdl-check.typort:436）加两臂 `case assertExpr(c,_,_) => scanExpr(c, acc)`（Cd 同）。效果链：(a) 条件信号进 reads → **HDL002（死信号）不误报**只被断言读取的信号；(b) 未驱动的条件信号照常报 **HDL001**；(c) 断言**不是驱动**——不进 DriveFacts，HDL010/011/012/013 不受影响。
- when 包裹的 assert：scanStmt 的 when 臂（:464）递归 body 自然到达新臂，零额外代码。
- exprKey（:246）加臂：`"as:(c,msg,sev)"` / `"asc:(c,msg,sev,cd)"`——重放去重键，防检查期 ~3 次字段求值重复计数（hdl-check.typort:236-245 注释的同一问题域）。
- 新 lint（可选，P2/P3）：**HDL026** 条件恒真/恒假（literal(1)/literal(0)，与 isTrueLit（hdl-verilog.typort:24）同判据）；**HDL027** 消息含 `"` 或 `%`。

### 3.5 assume / cover：不同批（结论）

不做。理由：(1) assume 在事件仿真里语义退化为 assert，cover 需要覆盖率收集设施，二者只在 formal 后端（SVA/SymbiYosys）有真语义；(2) 本设计产码目标是行为仿真器，formal 后端是独立工程（发射器 + yosys 集成）；(3) SpinalHDL 侧 assume/cover 属 `spinal.core.formal`（Stream.scala:680-692 formalAssumesSlave/formalCovers），与 assert 不同 API 层。演进预留：加变体 `assumeExpr`/`coverExpr` 时复用本设计的收集器骨架（when 折叠 + cd 分组完全同构），只换发射器。

## 4. BlackBox 设计

### 4.1 语法草案（宏形态）

对齐 SpinalHDL vendor 黑盒形状（参考 lib/src/main/scala/spinal/lib/blackbox/lattice/ecp5/debug.scala:40-42 的 JTAGG：Generic case class + BlackBox + io 端口；xilinx/s7/MMCME.scala 同构）与既有 module 宏的端口分组机制（hdl-macros.typort:426 的连续 run 匹配）：

```typort
blackbox SyncRam[depth: Nat, w: Nat]
    generic WIDTH = w          // → Verilog parameter WIDTH，实例化时 #(.WIDTH(w 的实参))
    generic DEPTH = depth
    input  clk   = Bool
    input  we    = Bool
    input  addr  = UInt[log2Up depth]
    input  din   = UInt[w]
    output dout  = UInt[w]
{
}
```

- 新 `#[macro_export] macro_rules blackbox`（hdl-macros.typort，module 宏 :341 之后），单臂：类型参数 `$($args: params)*` + `generic K = v` 连续 run（key 为 ident → `stringify`；value 为 raw → Nat 或 String 表达式）+ 类型化端口 run + Bool 端口 run + 空体 `{}`。宏在 raw 位置由 p_raw 分发（standalone when 的同一机制，hdl-macros.typort:6-8）——需早期 spike 确认新宏名可分发，若不行 fallback 是给 parser 加关键字（唯一可能的 Rust parser 改动，见 §10）。
- 泛型值是 **elaboration 期** Nat/String（与端口宽度同层）；不支持运行时参数。宽度表达式引用参数（`UInt[log2Up depth]`）天然成立——参数就是类参数 Nat。
- 展开镜像 module 宏 plain 臂（hdl-macros.typort:426-455）：三明治 push/restore + 端口经同一 createPortExpr/createBoolPortExpr 工厂（hdl-signals.typort:427/:454）→ 端口进 ModuleTree、父级 handle 字段（subSignal）——**端口声明路径与 module 完全同一条**，`u.port := sig` 层次连接、`designManifestVL` 端口表全部免费复用。差异仅在两处：
  1. ModuleDef 记录带 bb 信息（§4.2）；
  2. generic 语句经工厂 `bbGeneric(key, bbGenNat(v) / bbGenStr(s))` 写入可变全局 "BlackBoxCtx"（CompatCD 模式，hdl-verilog-compat.typort:133 的 ensure-exists + 每宏 reset），ModuleDef 记录时读取（镜像 `let __vcd = compatCD(stringify $name)`，hdl-macros.typort:369）。

### 4.2 数据模型

ModuleDef（hdl-core.typort:221-226）追加字段（选扩展而非平行 registry：runChecks/端口表/designVisit/designManifestVL 的单遍扫描全部保持均匀）：

```
struct BbGenVal { bbGenNat(v: Nat); bbGenStr(s: String) }
struct BbGeneric { key: String; val: BbGenVal }
struct BlackBoxInfo { generics: List[BbGeneric] }
struct ModuleDef { name; cd; expr_num; expr; bb: Option[BlackBoxInfo] }   // 普通模块传 None
```

ModuleDef.mk 调用点机械更新，共 7 处：addExprToModuleHelper（hdl-core.typort:257/:259）、headModuleDef 兜底（:616）、lookupModuleDef 兜底（hdl-verilog.typort:1369）、module 宏 push（hdl-macros.typort:371/:408/:439）。

### 4.3 代码生成

- **module 头引用而非展开**：moduleDefVL（hdl-verilog.typort:1222）顶端分派 `blackboxDefVL(md)`：

```verilog
`ifndef TYPORT_BB_SyncRam
module SyncRam #(parameter WIDTH = 8, parameter DEPTH = 64) (
  input wire clk,
  input wire we,
  input wire [5:0] addr,
  input wire [7:0] din,
  output wire [7:0] dout
);
endmodule
`endif
```

  - 端口行复用 collectPortLines/portLineSingle（:394/:375）；无 wire/reg/assign/always/instance 段（黑盒 def 的 expr 表只有端口声明）；**不合成 clk/reset 端口**（has_seq/has_init 判定整段跳过——黑盒无 regAssign）；cd 恒 defaultClockDomain。
  - `ifndef TYPORT_BB_<Name>` 守卫：行为模型文件（用户手写 Verilog，经后端 extra_args 加入编译）首行 `` `define TYPORT_BB_SyncRam `` 即顶替 stub——否则重复 module 定义（iverilog/verilator 都报错）。不提供替身时 stub 照发（verilator/iverilog 对空 module 都能 elaborate）。
- **实例化 = instance 变体的特例**：`let ram = SyncRam.create[64, 8]` 走既有 mkInstanceIfParent → `instance(bn.name, "SyncRam")`，**零新 Expr 变体**。参数注入在产码侧完成：collectInstHelp（:1156）线程化 defs 参数（moduleTreeVL/designVL 调用点传入；单模块路径读全局 "ModuleRegistry"，同 designVL :1402-1404 的 ensure-exists + get_global 模式），instance 臂查 moduleName：命中且 bb 非空 →

```verilog
  SyncRam #(.WIDTH(8), .DEPTH(64)) ram (.clk(clk), .we(we), .addr(addr), .din(din), .dout(dout));
```

  参数值来自**注册的黑盒 def**（first-registration-wins 的既有语义），非实例点求值——与 ModuleRegistry 既有碰撞限制一致（hdl-core.typort:629 注释）：同一黑盒两种参数化（`create[64,8]` 与 `create[32,8]`）碰撞为同一 module 名，**记为已知限制**，workaround = 按参数化各声明一个黑盒（或二期补 setDefinitionName：stub 已有该方法名占位，hdl-bus.typort:201）。
- `instNamesOfDef`（:1359）/designVisit（:1378）不区分黑盒——黑盒 def 进 design 闭包，designVL 闭合发射 stub；designManifestVL（:1538）的端口/实例 JSON 自动含黑盒（instJsonSingle :1461 不带参数值，仿真工具不需要）。
- **与 instanceWithPorts 的关系：并存**。instanceWithPorts 保持手工逃逸口（外部无 typort 声明的模块 + 原始端口串，HDL024 警告不变）；声明过黑盒的实例走 instance 变体（可查表、可自检、自动参数）。不做 `instanceWithParams` 新变体——"为外部带参模块声明一个 typort 黑盒"即覆盖该需求（黑盒声明本身就是端口/参数表）。

### 4.4 自检适配

- **端口表注册零改动**：runChecks（hdl-check.typort:867）对黑盒 def 照常跑 `portTableAdd`（:534）——ins/outs/inouts 来自其端口声明（namesOfKind :518）。父级查表 → **HDL020/021/025 原样覆盖黑盒实例**；ruleInstPorts（:834）的 ins+outs 全连检查 → **HDL022 原样覆盖**（黑盒实例是 raw=false 的 instance 节点，:474）。
- **黑盒本体门控**：黑盒无体，五条体规则会全误报（HDL003 每个输出端口都"无驱动"、HDL001/002 端口读写缺失、HDL023/010-013 无意义）——runChecks 加：

```
let isBb = match md.bb { case None => false; case Some(_) => true };
// isBb=true 时跳过 ruleDanglingRead/ruleUnusedDecl/ruleOutUndriven/ruleDrivers/ruleOwnInputDriven
// portTableAdd 与 ruleWidthGround（HDL004）无条件保留——黑盒宽度退化同样要报
```

- HDL024 不触发（黑盒实例不走 instanceWithPorts）；HDL022/020/021/025 规则函数本体零改动。

## 5. 仿真集成路线

### 5.1 现状盘点（结论）

§1.2 已列。补充三点判读：(1) 四后端同协议 → 断言回读只需改协议层一处（dut.rs roundtrip），后端零改动；(2) `verilator_args`/extra_args 通道可携带黑盒行为模型 .v（iverilog.rs:122 在 `-o` 后追加、verilator.rs:212 在文件列表追加）；(3) 既有 tests/sim_tests.rs 的"golden 向量 + 工具缺失 SKIP"模式直接沿用为 assert/BlackBox 的验收骨架。

### 5.2 "typort assert → 外部仿真器执行 → 失败回读"工作流

```
.typort assert(cond,"msg")
  → tyck/elaboration: createSignalExpr 默认臂（when 折叠）→ ModuleDef.expr
  → hdl-verilog.typort assertsVL: translate_off 包裹 + TYPORT_ASSERT 标记行
  → emit_design → <top>.v + manifest.json（SimConfig::compile，mod.rs:257）
  → 后端 build（命令拼装不变：verilator --cc --exe harness.cpp top.v / iverilog -g2005 -o model.vvp tb.v top.v）
  → Dut::spawn + 宿主驱动（set/eval/wait_edges）
      模型 stdout: "ok"/值行 | "VCD ..."（现有跳过）| "TYPORT_ASSERT ..."（新：捕获）
  → Dut::assert_failures() / expect_no_asserts()
      → cargo test 断言失败（带 %m 全路径 + 消息）
      → `typort test`（cli.rs:575 run_test）：smoke eval 后查 failures → stderr 打印 + 非零退出
```

- **testbench 骨架生成：不加新 DSL**。激励是宿主 Rust 测试代码（既有模式），被检对象是设计内 assert——这正是 SpinalHDL 中 assert 的定位（Stream.scala:658 的不变量检查写在设计库代码里，不写在 testbench 里）。verilog_harness.rs / harness_cpp 仅受益于标记行透传（模型 $display 直通 stdout），**两文件零改动**。
- **失败诊断回流（LSP 边界）**：仿真失败是运行时产物，不进 LSP 诊断管线（CheckIssues 是 tyck 期管道，lib.rs 排水时仿真还没跑）。v1 的用户面是 `typort test` stderr + cargo test 失败信息（`%m` 层次路径 + 消息已足够定位到模块与实例）。源码级 squiggle 需要 assert 携带隐式 Loc——与自检阶段 2 源定位同一前置（docs/hdl-selfcheck-design.md §0），列 P3。
- **fatal 的交互语义**：AssertFatal 的 `$finish` 令模型提前退出 → 下一次 roundtrip 报 "model closed stdout"（dut.rs:66-69）——测试代码捕错后读 failures。文档化，不做通道复活。

### 5.3 SpinalSim 进程内仿真：不做（结论）

**结论：不做 SimConfig 的进程内对应物（verilator FFI / iverilog VPI 都不做）**。need 分级：

| SpinalSim 能力 | 现状等价物（dut.rs） | 判定 |
|---|---|---|
| `forkStimulus(period)` | `dut.clock().fork(period)`（:257，模块注释自称 "SpinalSim style"） | 已有 |
| `sleep(edges)` / `waitUntil` | `wait_edges(n)`（:154，按边计数而非墙钟） | 已有 |
| `poke/peek`（端口） | `set/get`（:163/:199，manifest 校验方向+宽度） | 已有 |
| fork 线程 / joining | clock 线程 + `finish()` 收敛（:220） | 已有 |
| poke/peek **DUT 内部信号** | 无 | assert（P1，内点条件变成被仿真器执行的检查）覆盖主用途；可选 P3：manifest 加 `internals` + harness get 分发表 |
| Scoreboard/Stream driver 测试库 | 无 | P3：tests/ 内基于 Dut 的 Rust helper 组合，非 sim 核心 |

拒绝 FFI/VPI 的理由：收益仅是去掉进程往返延迟（测试场景无关紧要）；成本是 C++ 构建集成、ABI/unsafe、四后端 ×2 形态的维护面。**替代程度**：SpinalSim 五件事里四件 Dut 已等价；第五件（内点观测）由"设计内 assert + 可选 internals peek"覆盖到 SpinalHDL 用户 90% 的实际用法（不变量检查、握手协议断言）——SpinalHDL 自己的 sim/ 目录（lib/src/main/scala/spinal/lib/sim/）本质也是"宿主语言写激励 + peek/poke"，与 Dut 模型同构，缺的只是语言而非管线。

### 5.4 分阶段实施计划

**P1 — assert 全链（先行，最重要）——已实现（2026-09-26，commit ede8773 + 评审修复）**

| # | 落点 | 内容 |
|---|---|---|
| 1 | hdl-core.typort | AssertSeverity 枚举；Expr 加 assertExpr/assertExprCd（:96）；工厂 assert/assertFatal/assertInfo/assertWarning/assertSev/assertCd/assertSevCd（放 hdl-signals.typort 工厂族旁） |
| 2 | hdl-verilog.typort | exprVL/exprVL_proc 新臂（:84/:187）；collectAssignLinesFiltered 跳过臂（:750）；hasAssert/hasAssertCd/collectAssertLinesCd/collectAssertCdsOne/assertsVL 新函数族；moduleDefVL：`has_seq` 并入 has_assert（:1248）、body 串插入 asserts（:1321）、collectClockCds 并入 assertExprCd 域（:584） |
| 3 | hdl-check.typort | exprKey 两臂（:246）；scanStmt 两臂（:436） |
| 4 | src/sim/dut.rs | Shared 加 `failures: Mutex<Vec<String>>`；roundtrip 循环（:63-76）捕获 `TYPORT_ASSERT` 前缀行；`Dut::assert_failures()`/`expect_no_asserts()` |
| 5 | src/bin/cli.rs | run_test（:575）smoke 后 expect_no_asserts → stderr 打印 + 非零退出 |
| 6 | examples/hdl/26-assert.typort + tests/sim_tests.rs | 验收（§7） |

**P2 — BlackBox 全链**

| # | 落点 | 内容 |
|---|---|---|
| 1 | hdl-core.typort | BbGenVal/BbGeneric/BlackBoxInfo；ModuleDef 加 bb 字段 + 7 处 mk 更新；bbGeneric 工厂 + BlackBoxCtx 全局（CompatCD 模式） |
| 2 | hdl-macros.typort | `blackbox` 宏（单臂；先行 spike p_raw 分发） |
| 3 | hdl-verilog.typort | blackboxDefVL（`#(parameter ...)` stub + `ifndef` 守卫）；moduleDefVL 分派；collectInstHelp 参数注入（线程 defs）+ moduleTreeVL/designVL 调用点 |
| 4 | hdl-check.typort | runChecks 体规则门控（:867） |
| 5 | examples/hdl/27-blackbox.typort + 行为模型 .v + tests/sim_tests.rs | 验收（§7） |

**P3 —（可选，按需排序）**：内部信号 peek（manifest `internals` + harness 分发表）；HDL026/027 lint；SV-native 断言发射器；hdl-stream.typort 复刻 Stream.assertPersistence / formalAssertsMaster；断言隐式 Loc → LSP squiggle；setDefinitionName；formal（assume/cover + SVA）。

## 6. 实现落点分级（typort vs Rust）

**核心判断：语言侧改动全部是 .typort 编辑，Rust 编译器零改动。** 依据：`Expr`（hdl-core.typort:96）与 `ModuleDef`（:221）是 prelude 里的普通 typort enum/struct；宏臂（Expr 表/module 臂/新 blackbox 宏）都是 .typort 内 `macro_rules`（L11 宏系统数据驱动）；Rust 侧无 Expr 硬编码（grep 确认仅 L11_macro/mod.rs 注释提及）。与自检阶段 1 的形态完全一致（机制全 typort，仅报告管道是 Rust builtin，docs/hdl-selfcheck-design.md §0）。

| 层 | 文件 | 工作量 |
|---|---|---|
| typort | hdl-core.typort（变体/枚举/工厂/ModuleDef 扩展/黑盒 ctx） | P1 ~80 行，P2 ~120 行 |
| typort | hdl-verilog.typort（收集器族 + 发射 + stub + 参数注入） | P1 ~150 行，P2 ~120 行 |
| typort | hdl-check.typort（scan/exprKey 臂 + 门控） | P1 ~20 行，P2 ~15 行 |
| typort | hdl-signals.typort（工厂）/ hdl-macros.typort（blackbox 宏） | P1 ~40 行，P2 ~80 行 |
| Rust | src/sim/dut.rs（标记捕获） | ~30 行 |
| Rust | src/bin/cli.rs（test 退出码） | ~15 行 |
| Rust | tests/sim_tests.rs（验收用例） | ~120 行 |
| （spike 失败才需要） | parser 关键字分发（blackbox 宏名） | 视结果 |

## 7. 验收用例

### 7.1 assert（P1）：examples/hdl/26-assert.typort

```typort
module aCounter {
    input en = Bool
    output reg count = UInt[8] init 0
    when en {
        count := count + 1
    }
    assert(count < 100, "count overflow")              // 顶层：无条件时钟断言
    when count >= 50 {
        assert(count < 100, "half-way guard")          // when 内：条件折叠
    }
}
println(designVL(aCounter.create.tree))
```

期望 Verilog 关键行（L2 结构断言）：

```verilog
module aCounter (
  input wire en,
  input wire clk,
  input wire reset
);
  reg [7:0] count;
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      count <= 0;
    end else begin
      count <= (count + 1);
    end
  end
  // synthesis translate_off
  always @(posedge clk) begin
    if (!(count < 100)) begin
      $display("TYPORT_ASSERT_ERROR %0t %m: count overflow", $time);
    end
    if (count >= 50) begin
      if (!(count < 100)) begin
        $display("TYPORT_ASSERT_ERROR %0t %m: half-way guard", $time);
      end
    end
  end
  // synthesis translate_on
endmodule
```

（clk 端口由 has_seq||has_assert 合成；count 带 init → 复位分支，断言不进复位分支。）

期望仿真行为（L3，tests/sim_tests.rs 两例，verilator + iverilog 双跑）：

- **守卫通过**：reset → en=1 → 跑 60 边（count 达 60，`count >= 50` 分支活跃但条件成立）→ `dut.expect_no_asserts()` 通过。
- **违规捕获**：en=1 跑到 count ≥ 100 → `dut.assert_failures()` 返回恰一行，含 `"count overflow"` 与实例路径（%m）；不依赖 fatal 即可继续跑完。

### 7.2 BlackBox（P2）：examples/hdl/27-blackbox.typort + stub_ram.v

```typort
blackbox SyncRam[depth: Nat, w: Nat]
    generic WIDTH = w
    generic DEPTH = depth
    input  clk  = Bool
    input  we   = Bool
    input  addr = UInt[log2Up depth]
    input  din  = UInt[w]
    output dout = UInt[w]
{
}

module ramWrap[depth: Nat, w: Nat] {
    input clk = Bool
    input we = Bool
    input addr = UInt[log2Up depth]
    input din = UInt[w]
    output dout = UInt[w]
    let ram = SyncRam.create[depth, w]
    ram.clk := clk
    ram.we := we
    ram.addr := addr
    ram.din := din
    dout := ram.dout
}
println(designVL(ramWrap.create[64, 8].tree))
```

期望 Verilog 关键行（L2）：

```verilog
`ifndef TYPORT_BB_SyncRam
module SyncRam #(parameter WIDTH = 8, parameter DEPTH = 64) (
...
endmodule
`endif
...
  SyncRam #(.WIDTH(8), .DEPTH(64)) ram (.clk(clk), .we(we), .addr(addr), .din(din), .dout(dout));
```

自检用例（L1）：注释掉 `ram.din := din` → HDL022 `ram.din: instance port left unconnected`；`ram.dat := din` → HDL025 端口不存在；黑盒本体零误报（HDL003 被门控）。

期望仿真行为（L3）：行为模型 stub_ram.v（~10 行同步 RAM，首行 `` `define TYPORT_BB_SyncRam ``）经 `verilator_args: vec!["stub_ram.v".into()]` 加入编译；Dut 序列：写 addr=3/din=0xAB → 读 addr=3 → `dut.get("dout") == 0xAB`（posedge 同步读延迟按模型）。

### 7.3 额外时钟域 assert（P1 回归）：examples/26 内追加

```typort
module aCounterCd {
    input en = Bool
    output reg count = UInt[8] init 0
    when en { count := count + 1 }
    assertCd(count < 100, "cd2 overflow", cd2)
}
let cd2 = ClockDomain.mk "clk2" "reset2" Async RisingEdge ActiveHigh
```

期望关键行：`always @(posedge clk2) begin ... TYPORT_ASSERT_ERROR ... "cd2 overflow" ...` 与端口表出现 `input wire clk2`（collectAssertCdsOne 并入的验收点）。

### 7.4 回归基线

- 全 examples/hdl L1（`typort check` 0 错误）+ 既有 L2 结构断言不回归（Expr 变体不改任何既有产码路径——新变体只在新增收集器中出现）。
- 全套测试对照既有失败集（spinalhdl-lib-replication.md §6 的 389 通过/49 既有失败基线）。

## 8. 与 SpinalHDL 的对应及偏差

| SpinalHDL | 本设计 | 偏差 |
|---|---|---|
| `assert(cond, "msg")`，clocked `always @(posedge clk)` + `// synthesis translate_off` | 同 | ① 默认严重级 **ERROR** 而非 FAILURE——$finish 杀模型会截断后续违规收集，宿主协议下"标记行 + 继续跑"信息量更大；② 产码默认 `$display`+`$finish`（可移植），SV `$fatal/$error` 为二期开关；③ 无 `initial` 断言；④ 消息为 elaboration 期 String（SpinalHDL 的 Scala 插值同为 elaborate 期求值——一致） |
| `assume`/`cover`（spinal.core.formal） | 不同批（§3.5） | formal 后端缺位，演进路径已预留 |
| `BlackBox` + `addGeneric(Generic case class)` + `val io = master(...)` | `blackbox` 宏 + `generic K = v` 语句 + 端口区声明 | ① 无 Bundle 方向翻转（黑盒端口直接 in/out 声明——SpinalHDL vendor 黑盒实际也多走 in()/out() 直标）；② 恒等价 `noIoPrefix()`（端口名即 Verilog 端口名）；③ `setDefinitionName` 未实现（参数化碰撞为已知限制）；④ 同样发射空 module stub（SpinalHDL Verilog 后端行为一致） |
| SimConfig / SpinalSimManager / fork / sleep / peek / poke | Dut 协议 + clock().fork/wait_edges/set/get（已存在，dut.rs:1-14） | 无进程内仿真器（FFI/VPI 拒绝，§5.3）；内部信号 peek 列 P3 |
| Stream.assertPersistence / formalAssertsMaster（Stream.scala:658/:676） | hdl-stream.typort 复刻候选（P3） | 依赖本设计 P1 的 when 内 assert |

## 9. 风险与开放问题

1. **match 穷尽性波及面**：exprVL_proc / exprVL / exprKey 三处无 catch-all（§1.3-6），漏臂即编译错（编译器兜底，安全）；反向坑是 collectAssignLinesFiltered 的 catch-all 误发射——P1 清单已列显式跳过臂。
2. **blackbox 宏的 p_raw 分发**：standalone when 证明宏名可在 raw 位置分发，但新关键字宏未验证——P2 第一步 spike；fallback：parser 加关键字 → 宏表分发（唯一可能的 Rust parser 改动）。
3. **消息转义**：含 `"`/`%` 的消息产非法 Verilog；P1 文档约束 + HDL027 候选 lint。
4. **参数化碰撞**：ModuleRegistry first-wins（hdl-core.typort:629）——同一黑盒两种参数化取首注册；workaround 多声明，二期 setDefinitionName。
5. **fatal 与 Dut 生命周期**：$finish 后模型通道关闭，测试代码需捕错后读 failures；`typort test` 的 smoke eval 遇 fatal 表现为 spawn 失败——报告文案要区分"编译失败/致命断言"。
6. **collectAssertCds 与 collectClockCds 的合并**：两 walker 同构但语义不同（regAssignCd vs assertExprCd 各自收集）——合并实现时注意 has_clock（collectClockLines 的 when 门控）与 has_assert 的判定互不污染（assert 不该让模块拿到"有 clocked 行"的资格去触发复位分支）。
7. **老综合器注释方言**：`// synthesis translate_off` 对老 XST 不生效（需 `// pragma translate_off`）——是否双注释并列，开放。
8. **开放问题**：Verilog-compat 模块的 `$display` 直通臂（compat 用户写裸 `$display(...)` 语句）是否顺手支持（VExpr 一臂，产码直通）；assert 携带隐式 Loc 的 Loc 参数管线（自检阶段 2 共享前置）。
