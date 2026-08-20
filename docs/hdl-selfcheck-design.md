# HDL 自检框架设计（self-check / lint）

状态：阶段 1 实现中（2026-08-18 定稿）。
目标：一套在 **tyck 阶段** 运行、类似并部分超越 SpinalHDL 的硬件设计自检机制——
组合逻辑环、信号悬空、多驱动、端口方向反接、latch、CDC 等。

## 0. 核心决策（已拍板）

| 决策点 | 结论 |
|---|---|
| 实现宿主 | 纯 typort 库函数（与 `moduleTreeVL` 同层），仅"报告管道"是 Rust builtin |
| 源定位 | 阶段 1 名字级分析 + lib.rs 排水时按 signal 名回扫模块源码定位（声明/驱动/连接点 squiggle）；远期再加隐式 `Loc` 参数做全量精确覆盖 |
| 首批规则 | 悬空 + 多驱动 + 端口方向（名字级 def-use 即可，不依赖 Loc） |
| 严重度 | 全部先 warning，跑过回归语料校准误报率后逐条升级 error |
| 运行时机 | **tyck 阶段**：模块声明 elaboration 的字段求值期间自动触发，不是用户调用 `check()` 才跑 |

## 1. "tyck 阶段"的确切含义

本 elaborator 是 NBE 风格，tyck 与求值交错不分：模块宏把 side-effect 链摊平为
class 字段（`hdl-macros.typort`），class 字段在 Phase A 检查声明时即被求值
（约 3 次重放，靠 push/restore 幂等）。**ModuleTree 本来就是在模块声明的
tyck 期间构建完成的**，因此：

- 检查挂在三明治 create 侧的 `_res` 处（`let _res = get_global("ModuleTree")`
  之后、`_prev` 还原之前），此刻该模块的 def 已完整。
- 每条规则的检查代码是 typort 函数，产出通过 Rust builtin 注入
  `Infer.accumulated_errors` 同级的警告管道 → LSP 里与类型错误同一条
  诊断管线（`lib.rs` 的 per-decl 排水循环），CLI `typort check` 走
  `Backend::on_change` 免费获得。
- tree 侧（`def tree`）**不挂检查**：`.tree` 每次访问重跑链条，phase-2
  println 规范化会重复触发且无人排水。

三个深度层次（全部满足"tyck 阶段"）：

| 层 | 触发时机 | 规则 | 状态 |
|---|---|---|---|
| L1 类型系统层 | unification 时 | 位宽（已有）；端口方向句柄类型、字面量溢出 | 远期 |
| L2 语句位点层 | `:=` 求值时（驱动注册表） | 多驱动的更早报错 | 阶段 2 可选 |
| L3 模块收尾层 | create 侧 `_res` 处 | 全部首批规则 | **本次实现** |

组合环/悬空/latch/CDC 是整图性质，无法也不应编码进类型系统（需要线性/
效应系统）；L3 是不引入线性类型前提下最深的位置。

## 2. 架构

```
模块声明 tyck（Phase A 字段求值，重放 ~3 次）
  └─ create 侧: let _res: ModuleTree = checkModuleTree(get_global("ModuleTree"))
       ├─ 扫描 head ModuleDef → decls / reads / drivers / conns / insts
       ├─ 端口表注册到全局 "ModulePortTable"（幂等覆盖，供父模块查方向）
       └─ 规则 → report_check_issue(code, module, signal, message)   ← Rust builtin
            └─ 追加一行 "code|module|signal|message" 到全局 "CheckIssues" 字符串（行级去重）
lib.rs / run_with_prelude：每个 decl 的 infer 之后排水
  └─ take_check_issues() → 本次文件内 seen-set 去重 → (Error, WARNING) → 诊断
```

关键幂等性设计（字段重放 ~3 次 + 每次实例化重跑子模块构造器）：

- **create 侧 def 含重放语句（实现期发现的重要事实）**：class 字段在检查期被
  求值约 3 次，每次都把该字段的语句再追加进同一个 def（push 只在整条三明治
  重放时重置）。codegen 不受影响——它读 `.tree` 的单次干净重建——检查器是
  create 侧 def 的第一个消费者。对策：`exprKey`（Expr 的结构序列化键）在
  扫描时对顶层语句按键去重，重放坍缩为一次。
- 行级去重在 Rust builtin 内做（同内容行不重复追加）；
- 排水侧再用 seen-set（"CheckIssuesSeen" 全局）过滤一次：子模块在自己的
  class 声明处已报过，父模块体里 `child.create` 重放产生的重复报告被滤掉，
  同时保证警告归属到正确的 decl（模块声明本身）；
- 端口表注册**永不去重跳过**（每次覆盖同名条目）——跨文件场景
  `mutable_map` 每文件清空后，父模块实例化子模块时重放其构造器，
  端口表按需自愈重建，不依赖清空前的状态。

**Bundle 端口遮蔽归一化（实现期发现的第二个事实）**：`TypeName.create` 先产出
裸 wire，`.asMaster/.asSlave` 再用同名重建带方向端口，裸 wire 残留在 def 里，
Verilog 生成器靠"端口优先于同名 wire"去重。检查器必须做同样的归一化
（`dropShadowedWires`），否则端口方向查询会命中残留 wire 条目产生反向误报
（input 报 HDL001、output 报 HDL002）。

## 3. 规则清单

首批（阶段 1，全部 warning）：

| 码 | 规则 | 判定（名字级） |
|---|---|---|
| HDL001 | 读取了从未被驱动的信号 | 读取名 ∉ 驱动集 ∧ 非 in/inout 端口 ∧ 非 mem ∧ 非 out（out 交给 HDL003） |
| HDL002 | 声明后从未被读取（死信号） | wire/reg/in/mem 声明 ∧ 名字 ∉ 读取集 |
| HDL003 | out 端口无任何驱动 | kOut/kOutReg 声明 ∧ ∉ 驱动集 |
| HDL010 | 同信号 ≥2 个无条件赋值 | DriveFacts.uncondComb ≥ 2 |
| HDL011 | 无条件赋值与 when 条件赋值混合 | uncondComb ≥ 1 ∧ condComb ≥ 1（生成 assign + always 双驱动，非法 Verilog） |
| HDL012 | 组合与时钟驱动混用同一信号 | 任一 comb ≥ 1 ∧ 任一 clk ≥ 1 |
| HDL013 | 同一寄存器被多个时钟域驱动 | defClk ≥ 1 ∧ 显式 cds ≠ ∅，或显式 cds ≥ 2 |
| HDL020 | 父级驱动子模块 output 端口 | LHS subSignal(conn) ∧ 子端口 ∈ outs ∧ ∉ inouts |
| HDL021 | 父级读取子模块 input 端口 | RHS subSignal(conn) ∧ 子端口 ∈ ins ∧ ∉ inouts |
| HDL022 | 实例端口未连接 | 子端口 ∉ 该实例任何 conn |
| HDL023 | 模块内部驱动自己的 input 端口 | kIn 声明 ∈ 驱动集 |
| HDL024 | instanceWithPorts 绕过分析 | 存在 raw 实例节点（对分析器不可见） |
| HDL025 | 连接的子端口不存在 | conn 的端口 ∉ 子模块端口表（端口名拼写错误） |

后续阶段：

- 阶段 2 组合环：信号级驱动图 + Tarjan SCC + 环路径报告 + 条件结构互斥
  （when 条件已完整展平记录，`c && !c` / 同 switch 互斥分支可语法识别）；
  跨层次用子模块组合端口穿透摘要。
- 阶段 3 latch/条件覆盖 + 条件重叠多驱动升级（bitsel/partsel 位区间重叠）。
- 阶段 4 CDC：时钟域传播 + 2FF 同步器结构识别（bufferCC 的 `_sync1/_sync2`
  链）+ 多 bit 误用 2FF 报警（streamFifoCC 二进制指针是现成验收用例）。
- 阶段 5 超越项：位级 def-use、SAT 条件求解、隐式 Loc 全量 squiggle、
  Verilator lint 对拍（tools/spinalhdl-verify 已有环境）。

## 4. 阶段 1 实现地图

| 文件 | 改动 |
|---|---|
| `src/prelude/hdl/hdl-check.typort` | 新增：收集器（decls/reads/conns/insts/facts）+ 全部规则 + `checkModuleTree` |
| `src/prelude/hdl/hdl-macros.typort` | create 侧 `_res` 包裹 `checkModuleTree`（两个 arm，tree 侧不动） |
| `src/L13_namespace/mod.rs` | prelude 列表加 hdl-check（hdl-core 之后）；`take_check_issues()` 排水函数；`run_with_prelude` 逐 decl 排水到输出串 |
| `src/L13_namespace/cxt.rs` | `report_check_issue` builtin（4×String→Unit，行级去重追加 "CheckIssues"） |
| `src/lib.rs` | `elaborate()` / `on_change()` 逐 decl 排水 → 按 signal 名回扫模块体解析 span（`check_issue_span`，失败回退 decl span），(Error, WARNING) 诊断，seen-set 去重 |
| `src/L13_namespace/legacy_tests.rs` | 规则触发用例 + examples 回归不破 |

数据形态（typort 侧，全部不可变 + 头部 cons，查询 O(n) 名字级足够）：

```typort
enum SigKind { kWire kIn kOut kInOut kReg kOutReg kMem }
struct SigDecl { name: String, kind: SigKind }
struct DriveFacts { name, uncondComb/uncondClk/condComb/condClk: Nat,
                    defClk: Nat, cds: List[ClockDomain] }   // regAssign→默认域, regAssignCd→显式域
struct ConnInfo { inst: String, port: String, isLhs: Boolean }
struct InstInfo { inst: String, mod: String, raw: Boolean }
struct PortEntry { mod, ins/outs/inouts: List[String] }     // 全局 "ModulePortTable"
```

声明/引用的区分由树结构天然决定：Vec 顶层的 `create*` 节点是声明，
嵌在赋值/条件表达式里的 `create*` 节点是引用（`createSignalExpr` 的
追加纪律已经保证了这一点）。

## 5. 已知盲区与风险

- 名字级回扫定位：警告由 lib.rs 按 signal 名在模块体内回扫（声明规则指向
  `let/input/output/reg NAME`，驱动规则指向首个 `NAME :=`，连接规则指向
  `inst.port` 字面，未连端口指向实例声明 `let u = ...create...`）；
  自动生成名（`zz_` 等）找不到则回退到模块名 span。报文仍带信号名。
  阶段 5 再上隐式 `Loc` 参数做逐节点精确 squiggle。
- 同名信号：同模块内两个不同信号撞名（zz_ 自动名等）在名字级分析里合并，
  可能漏报/误报；模块重设计引入唯一 ID 时一并解决。
- **字面相同的重复语句被坍缩为一个驱动**（exprKey 去重的代价）：用户把
  `y := a` 原样写两遍不会被 HDL010 捕获——语义上它们是同一驱动；不同 RHS
  的多驱动（真冲突）正常捕获。
- `instanceWithPorts` 原始字符串连接对分析器不可见（HDL024 提示）；其涉及
  的信号不参与 HDL001/002/022 判定（当前 examples 无使用者）。
- 检查随字段重放跑 ~3 次：名字级扫描开销线性，可接受；组合环阶段再加
  per-module 分析结果缓存。
- 性能红线（docs/l13-perf-review-4.md）：不 force 任何条件表达式（当黑盒做
  结构比较）；`chkCdEq` 只比较 clockName/resetName 字符串。
- prelude 库自身无 module 声明，elaborate prelude 不会产生警告；
  PRELUDE_CACHE 深拷贝 mutable_map，测试间隔离成立。

## 6. 阶段 1 实测结论（2026-08-18）

- 规则触发用例 5/5（HDL001/002/003/010/020 + 干净模块零告警）；
  bundle 连接等价性回归（`<>` ≡ 双 `:=`）16/16。
- examples 误报校准：examples/hdl 各演示模块产生的告警**逐条核验均为真阳性**
  ——演示模块故意留悬空端点（未驱动的 push 侧、无下游的接收信号、裸实例
  的未连端口等），这是 lint 的正确行为；回归断言（contains 式）不受影响。
- typort 语法注意事项（写检查器时踩过的坑）：注释里不能出现 `*/`
  （preprocess 的块注释剥离会误伤，如 `create*/createMem`）；构造器模式
  arity 必须精确匹配（`createSIntOutRegWidthInit` 是 3 参）；穷尽枚举后
  不能再加 catch-all（报 unreachable pattern）；`f (g(x)) y` 形态的
  并置调用会被解析成 `f ((g(x)) y)`，复杂参数一律用逗号调用风格。
