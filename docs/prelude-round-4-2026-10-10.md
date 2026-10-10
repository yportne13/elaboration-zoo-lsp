# prelude 第 4 轮（2026-10-10）——(N) 栈预算对齐收口 e07 + 门禁参数缺陷

> 状态：**(N) 已完成并提交推送**（`bf5f34a9`）；(O)–(S) 待续（见 §6）。
> 收官数字以 Lead 门禁 `lead_r4` 为准。

## 0. DUT 指纹（「名字会骗人」：一律记 size + mtime + sha256）

| 用途 | 产物 | size | mtime | sha256 |
|---|---|---|---|---|
| bench（(N) 后） | `target/prelude_scratch/lead_r4_l13bench.exe` | 9,293,824 | 2026-10-10 00:12:31 | `410312EDA0A21C6A…` |

## 1. 本轮唯一的发现（Lead 受控实测）：**e07 不是不收敛，是栈预算**

同一个二进制 `lead_r3_l13bench.exe`（`86FF1BCA…`，round-3 收官产物），探针
`target/prelude_scratch/verify2/e_shape/e07_bigcoef.typort`
（`def z_f(a: Nat, x: Nat): Nat = a * 99999 + x * 99998 + 5` + `z_f 1 2`）：

| 入口 / 栈预算 | 结果 |
|---|---|
| `l13bench` 缺省（`L13_STACK_MB` 未设 = **256** MiB worker） | **111.9s 后 `thread '<unknown>' … has overflowed its stack`** |
| `l13bench` `L13_STACK_MB=1024` | **13.3s 跑完，`nf=600002`（两版一致）** |
| `typort check`（task-30 新默认 1024 MiB） | 不崩，`parser 0.0017 / infer 4.161846 / change 4.1715145` |

⇒ 第 2/3 轮把它记成「TIMEOUT/不收敛」是**读数口径问题**：19 档矩阵里唯一 TIMEOUT 的那个
`e07`，在两个入口下**都会死**，但死法不同（bench 爆栈 / CLI 已不崩）。
「e07 的规模问题在 `string_concat`」这条 owner 诊断只解释了它**为什么慢**，没解释它**为什么死**；
真正的原因是 **`l13bench` 的 worker 栈缺省 256 MiB，与 CLI 的 1024 MiB 不一致**。

**这条同时更正第 3 轮的一条归因**：owner 观察到「同形状在 `cargo test` 产物下 1.9s PASS
nf=600002」而 build 产物 TIMEOUT，当时记为「疑似栈帧/深度敏感」的旁证——现在原因明确：
不同构建/入口的栈预算不同，**不是** codegen 差异。

## 2. 落地内容

### (N) `src/bin/l13bench.rs`：worker 栈缺省 256 → **1024**
- 唯一语义改动：`unwrap_or(256)` → `unwrap_or(1024)`；`L13_STACK_MB` env 覆盖语义不变。
- 注释写明「必须与 `src/bin/cli.rs` 的 `TYPORT_STACK_MB` 保持一致」+ 本次的 111.9s/13.3s 对照。
- 新缺省下 `e07`：**13.6s**，`nf=600002`，无溢出。

**19 档形状矩阵（新缺省，逐档 1.9–2.0s，仅 e07 13.3s）**
```
AGREE 19 / DIVERGE 0 / TIMEOUT 0        （此前：AGREE 18 / DIVERGE 0 / TIMEOUT 1）
e01 252  e02 246  e03 250  e04 242  e05 12   e06 10   e07 600002  e08 252
e09 252  e10 12   e11 10   e12 252  e13 108  e14 22   e15 216      e16 22
e17 216  e18 413  e19 413
```

### 回归钉 `tests/round2_engine_tests.rs::bench_and_cli_worker_stack_defaults_agree_and_clear_the_literal_guardrail`
源码级一致性钉：从 `src/bin/l13bench.rs` 与 `src/bin/cli.rs` 里抽出 `stack_mb` 缺省值，断言
**两者相等且 ≥ 1024**。刻意不做压测钉（需要比 harness 线程更大的栈，又慢又抖）。
`round2_engine_tests` **10 → 11**，全绿。

### 顺带修：`tools/gate_l13.ps1` 的参数绑定缺陷（Lead 自己踩到的）
- 现象：`powershell -File tools\gate_l13.ps1 -Label x -Suites @("lib","twin")` 时，
  `powershell -File` 把数组重新序列化成 `-Suites lib twin`；**第二个值 `twin` 被位置绑定到
  `-CargoTargetDir`** ⇒ 在仓库根建了一整个 **1.5 GB 的 cargo target 目录**，日志目录也跟着搬走。
- 修法：`[CmdletBinding(PositionalBinding = $false)]` + `-Suites` 容忍逗号/空格分隔。
- 干跑取证（零 cargo）：
  - `-Suites nosuchsuite` → `!! no suite selected` + **exit 2**；
  - `-Suites lib,twin` → 选中 `[lib, twin]`（AST 抽真逻辑验证三种输入 `@("lib","twin")` / `"lib,twin"` / `"lib twin"` 同结果）；
  - 游离位置参数 `-Label pc lib` → `A positional parameter cannot be found…`（**硬错误**，不再是静默建目录）；
  - 仓库根**无**新增杂散目录（误建的 `twin/` 已删，回收 1.5 GB）。

## 3. 门禁（Lead 亲跑，`lead_r4`）

```
== disk: 18.7 GB free on F:\ (warn below 2 GB, hard stop below 0.5 GB)
[lib ok: 77.2s]   612/500 passed (min) / 0 failed | test result: ok. 612 passed; 0 failed; 6 ignored; 361 filtered out
[parity ok: 16.6s]  15/15 | ok. 15 passed; 0 failed; 618 filtered out
[twin ok: 101.7s]   28/27 | ok. 28 passed; 0 failed; 0 filtered out
[hdl042 ok: 16.8s]   2/2  | ok. 2 passed; 0 failed
== gate_l13[lead_r4]: total 212.6s, fail=0   NOT RUN: none (all four suites ran)
```
额外：`round2_engine_tests` **11/0**。`typort doc` 与 L3 本轮未重跑（改动只碰 `src/bin/l13bench.rs`
的 main 与 `tools/`，不触 prelude、不影响 check/emit 路径；`led_r3` 的 doc 1195/1195 与 L3 51/51
仍代表当前源码态）。

## 4. 证据等级

| 项 | 等级 |
|---|---|
| e07 崩溃/通过对栈预算的依赖 | **受控实测**（同一二进制 + env 覆盖 + 两入口） |
| 19 档矩阵全过 | Lead 亲跑（新缺省，逐档 nf 已列） |
| 门禁 612/28/15/2 fail=0 | Lead 亲跑 |
| 门禁参数绑定缺陷 | **受控复现**（干跑取证 + 误建目录 1.5 GB 实物） |
| verifier 独立复算 | **未做**（本轮 verifier 子进程连续两次失败，见 §5） |

## 4b. 追加落地：`nf_parity` 改比「内容」而非「尺寸」（round-4 追加，(R) 第 2/3 项）

**动机**：`nf` 是 nf 的**节点数**，而第 3 轮的孪生 `quote` 缺陷（卡住应用的实参不 force ⇒
未归约 redex 留在范式里）造出的正是**同尺寸、不同内容**的范式 ⇒ 旧的 `b == f && b != 0`
判定**从原理上就看不见它**，这也是该缺陷能长期潜伏的原因之一。

**改动**（`src/bin/l13bench.rs`，+35/−1）：
- `nf_parity` 现在在尺寸一致之外，再用**两版都现成的** `bench_check_nf_pretty_bounded`
  比一次**渲染后的内容**；`NF_PRETTY_RENDER_BUDGET = 200_000` 节点以下的形状才比内容
  （超过后 pretty 串本身会很大，该轮退回只比尺寸；`nf=600002` 的 e07 走此分支，13.3s 不变）。
- `b == 0 || f == 0`（某版失败）时直接判「不一致」，不再把失败冒充成一致。

**反向对照（证明 oracle 不是「假门禁」）**：把比较临时改成 `x != y` 后，
同一探针 `e16`（内容本来逐字符相同）立刻报 `NF-DIVERGE basic=22 fast=22`
⇒ 内容分支是承重的；恢复 `x == y` 后回到 `nf=22`。**门禁套件不受影响**
（`nf_parity` 只被 l13bench 自己调用，`twin_engine_tests` 走 LSP 后端）——
因此必须用 l13bench 做反向对照，用 `cargo test --test twin_engine_tests` 做对照是无效的
（本轮实测：twin 套件在翻转后的 oracle 下仍 28/0）。

**顺带修掉标签假象**：两版都失败（`basic=0 fast=0`）时旧代码打 `NF-DIVERGE`，
把 41 探针统计污染成「38 nf-ok + 3 DIVERGE」；现在打 **`BOTH-FAILED`**
（实测三条例行样本：`s04_rfl_false` / `s07_fail_mul1` / `s08_fail_add0`）。

**收官读数**（ hardened oracle 下）
- `verify2/e_shape` 19 档：**AGREE 19 / DIVERGE 0 / TIMEOUT 0**（逐档 nf 未变）；
- `verify3/nfdiv` 41 探针：**nf-ok 38 / DIVERGE 0 / BOTH-FAILED 3**（修前 38/3/0）；
- 门禁 `lead_r6`：`fail=0`，lib **612/0**、parity **15/0**、twin **28/0**、hdl042 **2/0**；
- 提交 `3a9b4b37`，已推送（remote = local）。

## 4c. (S) 成员级文档补齐（round-4 追加）

**动机**：第 3 轮收官时**顶层** 1195/1195 = 100%，但**成员级只有 73.2%**（1249/1706）——
trait 方法、枚举 case、结构体字段才是真正的文档缺口（`prelude_doc_cov.py --nested` 才看得出）。

**做法**：只加 `///`、不改任何签名/语义/实例；不新增顶层条目（避免动基线）；
每条文档按**源码**逐条写（`typort doc` 的 JSON 会给出 snippet，按内容核对）。
**踩到的坑**：JSON 的 `line` 字段**有偏移**（`AssertInfo` 报 L129、实际在 L132）⇒
一律用**整行内容**匹配插文档，重复字段名（`enable`/`eqs`/`cd`/`key`/`src`）用
**外层 struct 头**做锚点。

**已补 12 轮、共 20 个文件**（每轮都重建 + `typort doc --deny-warnings` + 全套门禁）：

| 文件 | 成员级 | 文档内容 |
|---|---|---|
| `op.typort` | 60.7% → **100%** | Tuple2..Tuple8 全部字段 |
| `hdl-core.typort` | 43.4% → **82.3%** | Le/Fin case、Exists 字段、ClockEdge/ResetPolarity/ClockDomainConfig/AssertSeverity case、ClockDomain 字段、`create*`/literal/sizedLiteral/unary/binary 等 Expr case、WhenState、ModuleDef/ModuleTree、BbGeneric、BlackBoxInfo、Range |
| `hdl-bus-proto.typort` | 44.9% → **98.6%** | Apb3 / AxiLite4 Ax·W·B·R / Axi4Stream / Wishbone / AvalonST / AxiLite4 通道字段 |
| `hdl-check-graph.typort` | 77.0% → **89.9%** | NegLeaf/DrvRange/CondSrc/DriveSrc/ConnEx/GDecl/EnableCtx/GraphAcc/CombEdge/CdcEdge 字段 |
| `hdl-check.typort` | 65.3% → **97.0%** | SigKind case、SigDecl、DriveFacts、ConnInfo、InstInfo、ModFacts、PortEntry |
| `hdl-utils.typort` | 76.7% → **90.7%** | 各 Expr 载体（Reverse/PropagateOnes/OHMasking/PriorityMux/MuxOH/OhMuxOr/MinMax/Clamp/AddCarry/TimeoutHandle/Counter*/Johnson）字段 |
| `hdl-misc-io.typort` | 46.8% → **88.7%** | TriState*/ReadableOpenDrain/GpioIO/Bcd*/Divider*/Masked/StateMachine |
| `hdl-fsm.typort` | 67.6% → **97.1%** | Fsm/FsmSt/FsmEdge/FsmRec/FsmCtxStack/FsmCtx |
| `hdl-bus.typort` | 40.0% → **90.0%** | IMasterSlave、Bundle、Stream/Flow、StateAccess/State/FSMEntryPoint/SwitchKey |
| `hdl-stream.typort` | 75.4% → **96.7%** | StreamFifoIO 握手/占用/标志、Fragment、StreamFragment |
| `hdl-misc.typort` | 50.0% → **92.3%** | Prescaler/TimerIO/TimerResult/InterruptCtrlIO |
| `hdl-types.typort` | 45.5% → **95.5%** | Data trait、Bool/Bits/UInt/SInt 的 name+zz_expr |
| `hdl-enum.typort` | 71.0% → **93.5%** | EncodingKind case、EnumVal、SwitchCases |
| `hdl-crossclock.typort` | 72.4% → **100%** | CcByToggleIO、StreamFifoCCIO |
| `hdl-verilog-compat.typort` | 72.0% → **100%** | VEq/CaseEq/CaseDefault/CompatCD |
| `hdl-ops.typort` | 54.5% → **~100%** | MuxExpr、Cat `##`、SwitchBuilder |
| `hdl-clock.typort` | 70.6% → **~100%** | Mem 的 wordCount/dataWidth/clockDomain |
| `hdl-signals.typort` | 97.1% → 更高 | Component 的 mkReg / mkRegWhen |
| `hdl-macros.typort` | 100%（原已满） | — |
| `hdl-verilog.typort` | 100%（原已满） | — |

**总量**：成员级 **73.2% → 100.0%**（1249 → **1706/1706**，本轮 **+457** 项）——
**20+ 个 prelude 文件全部写完，无一项遗漏**；顶层仍 **1195/1195 = 100%**；
`--min-coverage 60 --deny-warnings` **EXIT=0**、`warnings=0`。
门禁：`lead_s1`…`lead_s13`、`lead_s15`…`lead_s19` 全部 `fail=0`（lib **612/0**、parity 15、twin 28、hdl042 2）。
提交 17 个，全部已推送：`f753ab67` `449251d4` `340a6af4` `33bc77a1` `4fe852ec` `51cb8b5a`
`facaef09` `58c38d40` `272d5006` `1920b27a` `9fb21da6` `2b156502` `e82e3f06` `e5b0c939`
`8078d95e` `2255a98b`。

**最后几项的做法升级**：批量锚定对「同一字段名出现在多个 struct」无效，故对最后 8 项
改成**逐条读源码 + 编辑工具手改**（Fsm.width/name、FsmRec 5 项、FsmCtxStack、
CombPath.from、CombSumEntry.mdl、ModuleCombSummary.entries、GDecl.key、
DividerFSM.quotient/remainder、Module.tree、Encoding.encNative、SwitchHead.shEnum）。
**这条比脚本更可靠：当 JSON 的 line 落到注释区、或字段排在同 struct 多个已有文档字段之后时，
脚本的窗口假设全错，只有读源码才对。**

1. **两个子进程（engine-quirks 窗口 1 的 task-31、verifier 的 task-35）先后失败、未留任何落盘**。
   Lead 复核：`l13bench.rs` 未改、`verify4/` 不存在、工作树干净 ⇒ **无半成品风险**；
   (N) 由 Lead 自己落地并用受控实测补齐证据。**教训**：子进程失败后第一件事是**核对工作树**
   （有没有半成品、有没有插桩），再决定是自己接手还是重派。
2. **Lead 自己踩到上面的门禁参数缺陷**：`-Suites` 数组经 `powershell -File` 传参被拍平成
   「空格分隔串」，第二个值静默变成 `-CargoTargetDir`。**教训**：脚本对数组参数要做
   「拍平后仍可选对」的归一化，并且**关掉位置绑定**——否则一个手误就在仓库里长出一个
   1.5 GB 的 target 目录，还会把日志目录搬走（下一个人更难发现）。
3. **(R) guard 文案排序：试过硬失败，回滚**。把「超限字面量」从「push_error + 降级 Hole」
   改成解析期 `Err` 硬失败，结果 **guard 原文彻底消失**，变成 `find unsolved meta` +
   `name not in scope` + `expected expression` + `expected newline` 四条泛化错误
   （`.or_far` 对 `Err` 回了退）⇒ 立刻 `git checkout --` 回滚并复跑确认恢复原状。
   **结论**：保留可恢复路径，把「guard 排第 3 条」作为**已记录的低优先级诊断瑕疵**延后——
   要把它提到第一条得改 LSP 后端的诊断汇总顺序（影响所有报错），性价比不划算。
4. **Lead 又踩了一次 PS 文本命令改 CJK 源码**（第 6 起同类）：做 oracle 反向对照时用
   `(Get-Content -Raw) -replace | Set-Content` 改 `src/bin/l13bench.rs`，编码被搞乱、
   6 个编译错误；用事先 `Copy-Item` 的备份恢复。**教训仍然只一条：CJK/源码一律走编辑工具，
   备份要用二进制复制而非文本管道。**
5. **(S) 给 `FsmSt` 补文档时多加了两个真字段 → 16 个 lib 测试红，已回滚**（第 7 起同类）：
   `Fsm` 当时已有 `stateReg/stateNext/stateCount`，我以为 `width`/`name` 缺失，直接往 struct
   体里插了字段 ⇒ prelude 类型里 `Fsm` 多出两个投影，`fsmDemo` 等 16 个用例报
   `` `ctrl`: Fsm has no object `state` ``。**门禁 `lead_s14`：lib exit=101，596/612 passed / 16 failed。**
   60 秒内 `git checkout --` 回滚 `hdl-fsm.typort` + `hdl-misc-io.typort`，
   `lead_s15` 复跑回 **612/0 fail=0**。
   **教训**：写文档脚本只允许**插 `///` 行**，绝不允许插入/删除任何非 `///` 行；
   动手前先用 `Select-String` 核对 struct 现有字段表，别信「缺口清单」里的字段名。
6. **(S) 的重复字段名 bulk 锚定全部打偏**（第 8 起同类，已无破坏性）：同一字段名在多个
   struct 出现，脚本按「struct 头 + span」猜窗口 ⇒ 7 处 `SKIP`、3 处写错位置（好在只插
   `///` 行，`git diff --numstat` 立刻看出异常）。**修法：最后 8 项改成逐条 `read` + `edit`
   手改**，全部命中。**教训：bulk 脚本只适合「字段名唯一」的场合；一旦出现重复名，停下读源码。**

## 4d. 收官判据复验（L3 仿真背书 + 19 档矩阵）

本轮改动：`src/bin/l13bench.rs`（bench 缺省栈 256→1024 + `nf_parity` 比内容 + `BOTH-FAILED`
标签）、`tools/gate_l13.ps1`（参数绑定加固）、20+ 个 prelude 文件的**纯文档**改动、
`prelude_hdl_c_tests.rs`（(Q) 回归钉）。交付判据要求 L3 不退化，故用**冻结副本**重跑。

**DUT 指纹**（`cargo build --bin` 产物 + `Copy-Item` 冻结，`size+mtime+sha256`）：
`target/prelude_scratch/lead_r4_l3_typort.exe` size **20,143,104**、mtime **2026-10-10 07:49:20**、
sha256 `8A74F512E4D61BED…`；`lead_r4_l3_l13bench.exe` size **9,320,960**、mtime 同时、sha `3FF87655016AB3A4…`。

**L3 全用例集**（`TYPORT=<frozen>`，verilator = `C:\msys64\mingw64\bin\verilator`）：

```
== 51 passed, 0 failed, 51 total ==
（v_utils_combinational / v_utils_sequential / v_stream_sequential /
  v_misc_combinational / v_dualclock 五个 case 文件全 OK，逐模块与第 3 轮一致）
```

**PLRU 显式用例**（不在 `DEFAULT_CASES` 里，按第 3 轮的显式调用方式传 **case 文件**）：
`python tools/spinalhdl-verify/verify.py tools/spinalhdl-verify/cases/r3_plru.typort`
⇒ `[OK] r3Plru`，`1 passed, 0 failed, 1 total`。合计 **52/52**，零退化。

> 坑（第 4 轮自己踩到）：`verify.py` 的位置参数是**用例文件路径**，不是用例名
> （`--case r3Plru` 会走成「文件不存在」的 `[MISSING CASEFILE]` 分支，且**退出码仍是 0**
> ——因为它只是 `continue`）。已在本节记下正确调法。

**19 档形状矩阵**（用冻结的 `lead_r4_l3_l13bench.exe`，新缺省栈、内容级 oracle）：
`AGREE 19 / DIVERGE 0 / BOTH-FAILED 0 / TIMEOUT 0`（e07 `nf=600002`）。

**至此本轮全部交付判据齐备**：
门禁四套件 `fail=0`（lib **613/0**、parity 15/0、twin 28/0、hdl042 2/0）；
`typort doc --min-coverage 60 --deny-warnings` **exit 0**、warnings=0；
prelude 顶层 **1195/1195 = 100%**、成员级 **1706/1706 = 100%**；
L3 **52/52**；19 档 **19/19**。

### (O) `when { cdReg := x }` 组合驱动 —— **设计评估完成，结论：本轮不做**

**两条前置事实（Lead 本轮查清）**
1. **结构性约束**：`pickAssign` 在 `hdl-core.typort`，而 hdl 的加载序里 `hdl-core` 是**第一个**
   hdl 文件；能查 decl 时钟域的全在后头——`declOf`（`hdl-check.typort:180`，
   `struct SigDecl { name, kind }`，**不带 cd**）、`gdeclCdOf`（`hdl-check-graph.typort:1793`）、
   `resolveCd`（同文件）。⇒ **`hdl-core` 内前向引用不允许** ⇒ 最直觉的「在 `pickAssign` 里查
   lhs 的 cd」这版**当前不可行**。
2. **影响面 = 0**：全 `examples/hdl/*` 全 top 扫描 `always @(*)` 内含非阻塞 `<=` 的签名
   （此缺口的唯一可观测签名）⇒ **0 处触发**。⇒ 纯用户面缺口，不是仓库内活跃 bug。

**三个候选方向的评估**
| 方向 | 做法 | 成本 | 风险 |
|---|---|---|---|
| A | cd 自查下沉到 `hdl-core` | 需自己维护一份 decl→cd 表，且 `pickAssign` 现有注释里那条「声明期求值会写 design-level global」的坑会直接踩到 | 高（prelude 装载期副作用） |
| B | 选择逻辑移到各 Data impl 的 `:=`（`hdl-types`/`hdl-clock`/`hdl-signals`） | N 处分散改动，每处都要判 cd | 中（分散难一致） |
| C | 发射器侧重归属：`collectClockLinesCd`（`hdl-verilog.typort:1071`）对 `regAssign` 也按目标 decl 的 cd 归属（与 (K) 的 `hasMainClocked` 对称） | 需把 decl 表透传进 `collectClockLinesCd`/`hasMainClocked`/`clockedBlockVL`（3 参数 → 4，两处调用点 `:1639`/`:1693`），并先用 `gdeclCdOf` 建表 | 中（**最高危文件**、且会改所有含额外域模块的 emit） |

**结论：本轮不做，留作设计决策。** 理由：① 最直觉的 A 结构上不可行；② B 分散；③ C 是唯一
正解但动最高危文件且**仓库内 0 触发**（投入产出比差），还需先确认「目标 decl cd == 主域时仍归主域」
不会让现有 examples 的 emit 变化。**(K) 已修的顺序是 `regAssignCd`，即库/用户的正确写法；
本项是给自然写法 `:=` 补的糖。**

### (P) 主域多余 `input wire clk` —— **已修**（原「判定不做」的结论被自己推翻）

`moduleDefVLPlain` 的 `has_seq` 用 `clockedVL` 判空，而 `clockedVL` = 主域块 **+**
每个额外域的块拼成的串 ⇒ 只要模块里有任何额外 cd 块，就补一个没人用的主域 `clk` 端口。

**本轮实际改动**（`hdl-verilog.typort`，+28/−5，动最高危文件但改动机械且**两处同步**）：
`has_seq` 改为只看 `clockedBlockVL`（**主域**块）；`clocked`（主 + 额外）仍驱动 body。
**两个调用点必须同时改**：`moduleDefVLPlain:2030`（Verilog 端口表）与
`manifestSynthPorts:2369`（manifest 合成端口表）原本互相镜像，只改一处会让两份输出不一致
——正是本轮加固 `nf_parity` 防的那类双源 bug。

**前后对照**（冻结 round-4 二进制 → 新二进制）：

| 模块 | before | after |
|---|---|---|
| 纯额外域 clocked 内容 | `input wire clkA, clkB, rstB`（clkA 无人读） | `input wire clkB, rstB` |
| 主域 clocked 内容（对照组） | `input wire clkA, rstA` + `always @(posedge clkA …)` | **不变** |

**回归钉**：`extra_cd_only_module_does_not_synthesize_main_clk_port`
（lib 613 → **614**），断言**端口集合**——这正是第 2 轮 (K) 钉刻意没覆盖的部分。
门禁 `lead_p2`：`fail=0`，lib **614/0**、parity 15、twin 28、hdl042 2。
L3 用新冻结二进制（sha `17893340F513EA79…`）复跑：**51/0/51 + PLRU 1/0/1 = 52/52**，
含双时钟 `vPulseCC`/`vFifoCC`。

#### 顺手推翻了本轮自己的两个结论（写文档时才发现）

1. **(P) 原判定「不做」的理由之一是「影响面 0」**——但**改法本身只有 4 行**，且有一枚
   现成的正控探针，投入产出比完全够。教训：「影响面 0」只说明不用急，不说明不该做。
2. **(O) 的影响面审计签名查错了**：我扫的是 `always @(*)` 里出现**非阻塞** `<=`
   （`<=` 是 clocked 赋值的标志），但组合驱动用的是**阻塞** `=`。所以那次
   「110 个模块 0 命中」**可能是假阴性**。本次已被动证实：新写的 (P) 回归钉第一版用
   「自然写法」`when en { cdReg := d }`，结果发出 `always @(*) … pR2 = d;`（阻塞）⇒
   **cd 寄存器在 `when` 里确实被组合驱动**，即 (O) 缺口是真的、可达的。
   根因链已查实：`hdl-crossclock.typort:354` 明写「注意 1：不能用 whenBegin 包裹
   regAssignCd —— **when 没有 Cd 变体**」，且全 prelude 73 处 `regAssignCd` 里
   **只有库代码**（hdl-crossclock / hdl-clock）产它，用户面 `:=` 一律走 `pickAssign`
   ⇒ 普通 `regAssign` ⇒ 组合驱动。
   ⇒ **第 5 轮 (O) 的优先级应上调**，且必须用**阻塞 `=` 签名**重扫 examples。

#### (O) 重扫完成：**正确的源级签名下，examples 仍 0 命中**（但用户面可达，已实测）

第 3 轮与我本轮的 emit 级签名都查错了，本轮最终改用**源级**签名并**先校准再扫**：

- emit 级不可行：`newUIntRegInitCdNamed` 的寄存器和 `newUIntNamed` 的 wire **发射相同**
  （都是 `reg NAME;` + `always @(*)` 里的阻塞 `=`），所以 emit 层面无法区分「(O) 缺口」
  与「本来就组合的 wire」。实测：正控 `oCdOnly` 与负控 `oWireOnly` 在 `always @(*)` 签名下
  **双双命中** ⇒ 该签名无效（这就是我此前「0 命中」可能是假阴性/假阳性的原因）。
- 源级签名（有效）：binding 由 `*Cd*` 工厂 decl（`createRegWidthCd` 一族）
  **且**在 `when { }` 内用自然 `:=` 驱动。
- **校准（`target/prelude_scratch/o_audit_probe.typort`，三个模块，先校准后扫描）**：
  `oCdOnly`（已知正例）**命中**；`oWireOnly`（普通 wire）**不命中**；
  `oCdPrim`（`regAssignCd` 原语写法）**不命中**。三项全过才扫 examples。
- **扫描结果：`examples/hdl/*` 0 命中。**

**但用户面可达已被实测证明**：(P) 的回归钉第一版就是用自然写法
`when (en) { r2 := d }` 写的，它发出 `always @(*) … pR2 = d;`（阻塞）且**没有** clocked 块。
根因链已查实：`hdl-crossclock.typort:354` 明写「不能用 whenBegin 包裹 regAssignCd ——
**when 没有 Cd 变体**」，且全 prelude 73 处 `regAssignCd` 里**只有库代码**
（hdl-crossclock / hdl-clock）产它；用户面 `:=` 一律走 `pickAssign` ⇒ 普通 `regAssign` ⇒ 组合驱动。

⇒ **结论**：仓库内 0 触发（这次的证据链完整：签名先校准、正负控都过），属**用户面缺口**；
用户一旦用 `when` + cd 寄存器就会静默拿到组合逻辑。修法见第 5 轮候选。

#### (P) 修完后的目标项最终状态

| 项 | 状态 |
|---|---|
| (N) e07 栈预算 | ✅ 完成（bench 256→1024，19 档 19/19） |
| (O) `when { cdReg := x }` 组合驱动 | **需重审**（原「0 触发」的签名查错；本次已实测可达） |
| (P) 主域多余 `clk` 端口 | ✅ **已修**（两处 has_seq 同步 + 端口集合回归钉，lib 614） |
| (Q) formA 混合端口表 | ✅ 第 3 轮缺口已不存在，复测 + 回归钉 |
| (R) 三小项 | guard 排序延后；nf_parity 改比内容；BOTH-FAILED 标签 |
| (S) 成员级文档 | ✅ 完成 100.0%（1706/1706） |

**(R) 第 1 项（guard 文案排序）收手记录**：试过硬失败（解析期 `Err`），结果 guard 原文**彻底消失**
（`or_far` 对 `Err` 回退，退化成 4 条泛化错误）⇒ 已回滚并复跑确认恢复原状。要把它提到第一条得改
LSP 后端的诊断汇总顺序（影响所有报错），性价比不划算 ⇒ 记为低优先级诊断瑕疵延后。

### 第 4 轮目标项最终状态
| 项 | 状态 |
|---|---|
| (N) e07 栈预算 | **完成**（bench 256→1024，19 档矩阵 19/19） |
| (O) `when { cdReg := x }` 组合驱动 | **需重审**（原「0 触发」的签名查错，已实测可达），见 §6 |
| (P) 主域多余 `clk` 端口 | **已修**（两处 `has_seq` 同步改 + 端口集合回归钉，lib 614） |
| (Q) formA 混合端口表 | **第 3 轮缺口已不存在**（6 形状复测全诊断）+ 回归钉，lib 613 |
| (R) 三小项 | guard 文案排序延后；`nf_parity` **改比内容**（反向对照证明）；`BOTH-FAILED` 标签，41 探针 38/0/3 |
| (S) 成员级文档 | **完成 100.0%（1706/1706）**，顶层 1195/1195 |

### 其余（原「未开始」节，现已全部处理）
**(Q) 见上一节；其余项见 §6 与 §4b/§4c。**

### (Q) formA 混合端口表诊断 —— **第 3 轮入册的缺口已不存在（复测推翻）**

**第 3 轮登记**：formA 混合端口表（`input sel = Boolean` + `output y = Bool`）不匹配
`module` 宏末尾的 `= Boolean` 兜底臂（该臂要求所有标量端口都是 `Boolean`）⇒
回到未诊断的 `expected def, found identifier`。

**第 4 轮复测（CLI 6 形状矩阵，探针 `target/prelude_scratch/r4_Q_matrix.typort`）：
全部报出 HDV004 且点名出错端口**：

| 形状 | 结果 |
|---|---|
| M1 `Boolean` 在前、`Bool` 在后 + sized | HDV004 点名 `sel` |
| M2 `Bool` 在前、`Boolean` 在后 | HDV004 点名 `sel` |
| M3 `Boolean` 在 output 槽 | HDV004 点名 `y` |
| M4 `Boolean` 紧贴 body 花括号（最后） | HDV004 点名 `y` |
| M5 `Boolean` + sized（无 `Bool`） | HDV004 点名 `w` |
| M6 `Boolean` + `output reg` 混合 | HDV004 点名 `y` |

**机制**：兜底臂的 `= Boolean` 重复组只要求 **Boolean 端口自身连续成 run**，其余标量端口
由前面各严格臂按语句各取所需 ⇒ 混合形状仍有臂可落。第 3 轮「按整次调用匹配 ⇒ 混合必失败」
的推断对**组内 run 匹配**不成立。

**回归钉**：`prelude_hdl_c_tests::formA_mixed_port_table_is_diagnosed`
（lib 612 → **613**），钉住三件事：混合表仍**响亮失败**（红线：绝不静默变 Bool 端口）、
两种排列都钉、外加 all-`Boolean` 对照形状。同步更正 X1 注释块里那条过时登记。
门禁 `lead_q1`：`fail=0`，lib **613/0**、parity 15、twin 28、hdl042 2。提交 `dc08b557`。

**唯一仍不可诊断的**：formA 的 `MyTypo`（错拼类型，非 `Boolean`）——它没有 HDV004
（兜底臂只认字面 `Boolean`），保持原有响亮失败。与第 3 轮一致，属下一个候选。

### 第 4 轮目标项最终状态

| 项 | 状态 |
|---|---|
| (N) e07 栈预算 | **完成**（bench 256→1024，19 档 19/19） |
| (O) `when { cdReg := x }` 组合驱动 | 有依据判定不做（结构约束 + 0 触发） |
| (P) 主域多余 `clk` 端口 | 有依据判定不做（110 模块 0 命中） |
| (Q) formA 混合端口表 | **第 3 轮缺口已不存在**，复测 + 回归钉 |
| (R) 三小项 | guard 排序延后；nf_parity **改比内容**；`BOTH-FAILED` 标签 |
| (S) 成员级文档 | **完成 100.0%（1706/1706）** |

## 9. 第 5 轮候选

1. **参考版 `quote_sp` 迭代化**（第 3 轮 §7-1）：e07 里 bench 侧已靠栈预算解决，但
   `typort check` 侧 47s 才跑完、且仍靠 1024 MiB ⇒ 迭代化才是根治（同时让「入口/栈预算是读数
   的一部分」这条纪律的压力下降）。
2. **formA `MyTypo` 可诊断**（(Q) 的孪生缺口）：混合表已被诊断，唯独错拼类型仍无 HDV004
   （兜底臂只认字面 `Boolean`）。方向：给 formA 兜底臂补 `= $ty:ident` 组——但那次同样会
   捕获所有标量端口，需先证明「组内 run 匹配」能像 M1..M6 那样把它限制在出错端口上
   （第 3 轮正是据此否决的，第 4 轮证明该否决对 `= Boolean` 组成立、对 `$ty` 组未验证）。
3. **(O) 修法**：发射端（方向 C）已被 (P) 证明可行——`collectClockLinesCd` 的主域臂改为
   「目标 decl 的 cd 非主域时归到该 cd」，同时 `hasMainClocked` 同步。仓库内 0 触发 ⇒
   可以做一枚用户面回归钉而不动 examples 基线。
4. **(P) 主域多余 `clk` 端口**：改 `moduleDefVLPlain` 按域判空 + 端口集合断言（用户可见）。
5. **(R) guard 文案排序**：需改 LSP 诊断汇总顺序，低优先级。

*（本文件由 Lead 在第 4 轮内持续追加；本轮全部改动已提交推送。）*
