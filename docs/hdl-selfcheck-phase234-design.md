# HDL 自检框架阶段 2/3/4 设计（组合环 · latch/位区间 · CDC）

状态：**阶段 2-4 已实现（2026-09-27）**。实现落点：hdl-check-graph.typort（新文件，入口
checkModuleTreeAll）、cxt.rs（check_comb_cycles builtin + twin 引擎 PrimId 镜像）、
hdl-check.typort（runChecks 加 rangeSafe 参数 + registerPortTable 拆出）、hdl-macros
（三处模块宏臂 + 黑盒宏臂的 `_res` 改调）、L13_namespace/mod.rs（prelude 表插入
hdl-check-graph）、hdl_check_graph_tests.rs（21 个验收/回归用例）。实现与设计的偏差
逐条记录在文末 §11（实现偏差清单，2026-09-27）。前置文档：docs/hdl-selfcheck-design.md
（阶段 1 已实现合入；编号、架构、幂等性设计全部延续它，本文不重复其内容，只引用）。

---

## 0. 背景与现状

### 0.1 阶段 1 架构回顾（代码锚点）

检查挂在模块宏 create 侧 `_res` 处（hdl-macros.typort:378/416/447 三个 arm 的
`let _res: ModuleTree = checkModuleTree(get_global("ModuleTree"))`），tree 侧不挂。
`checkModuleTree`（hdl-check.typort:893-901）→ `runChecks`（hdl-check.typort:867-885）：

- 名字级扫描：`scanAll`（hdl-check.typort:489-499）对顶层语句按 `exprKey`
  （hdl-check.typort:246-296，Expr 结构序列化键）去重后 `scanStmt`
  （hdl-check.typort:436-487）产出 `ModFacts`（hdl-check.typort:312-319）：
  decls / reads / conns / insts / facts（`DriveFacts`，hdl-check.typort:183-191，
  按 uncond/cond × comb/clk 四象限计数 + 显式域列表 cds）。
- 报告管道：`chkReport` → Rust builtin `report_check_issue`（cxt.rs:369-392，
  行级去重追加全局 "CheckIssues"）→ lib.rs / run_with_prelude 逐 decl 排水
  （`take_fresh_check_issues`，L13_namespace/mod.rs:4194-4221，"CheckIssuesSeen"
  seen-set）→ (Error, WARNING) 诊断；span 由 `check_issue_span`（lib.rs:1062-1122）
  按信号名回扫定位。报文格式 `code|module|signal|message`。
- 规则 HDL001-004 / 010-013 / 020-025 全部 warning；端口表全局
  "ModulePortTable"（hdl-check.typort:507-543）按模块名幂等覆盖注册。

关键幂等性事实（本设计必须继续满足）：

1. class 字段在检查期被求值约 3 次，每次把语句再追加进同一 def；
   `scanAll` 的 exprKey 去重把重放坍缩为一次（hdl-check.typort:236-245 注释）。
2. `mutable_map` 每文件清空（lib.rs:1320/1880/2503；"CheckIssuesSeen" 随之清空）。
3. 父模块实例化子模块时重放子构造器 → 子模块的 create 侧检查重跑；
   端口表/注册表靠"按需自愈重建"而非依赖清空前状态。
4. class 两段式 elaboration 在检查类型时另建一棵抛弃树（Phase A 轮），
   该轮所有宽度是 Rigid 变量、`nat_to_dec` 渲染成 0——HDL004 用
   "同模块至少一个 ground 宽度才报告"的门控识别它（hdl-check.typort:605-618）。
   阶段 3/4 的值敏感规则必须复用同一门控（§4.6）。

### 0.2 本设计依赖的既有机制

- **when 条件已完整展平**（hdl-core.typort:263-377）：每条赋值被
  `addWhenContext` 包成 `when(完整使能条件, 赋值, None)` 独立节点；
  嵌套合取 + elsewhen/otherwise 分支否定（`andCond`:294、`negatePrev`:304、
  `levelCond`:354、`wrapLevels`:360）。switch 脱糖为 when 链
  （hdl-macros.typort:209-225），条件形如 `sel==0`、`sel==1 && !(sel==0)`、
  `!(sel==0) && !(sel==1)`；`===` 产出 `binary(x, "==", y)`
  （hdl-ops.typort:270-278）。**语法层互斥识别的数据基础已经存在**。
- **时钟域**：`ClockDomain`（hdl-core.typort:86-92）+ 模块级单域
  （`ModuleDef.cd`，hdl-core.typort:221-226）；每寄存器显式域扩展已落地：
  `createRegWidthCd` / `createRegWidthInitCd` / `createSIntRegWidthCd` /
  `createSIntRegWidthInitCd` 声明变体 + `regAssignCd` 赋值变体
  （hdl-core.typort:108-111,134）。
- **跨时钟库**（hdl-crossclock.typort）：`bufferCC*Chain`（:13-47，
  内部名 `<bn>_sync`/`<bn>_sync<N>`）、显式域版 `bufferCC*ChainCd`（:77-120）、
  `pulseCCByToggle`（:126-138，sync1/sync2 + XOR 边沿检测）、
  `ccByToggleUInt`（:149-165）、`streamFifoCC`（:192-231，**二进制指针**
  + 两侧 2FF 同步链 wrPtrSync1/2、rdPtrSync1/2）。`readSyncCC` 与
  `readSync` 完全相同（hdl-clock.typort:54,68-72；hdl-crossclock.typort:171-174），
  无真正同步器——docs/spinalhdl-gap.md:61-62（跨时钟域 🟡 / BufferCC ❌ 两行）。
- **Verilog 生成器结构**（§4.1 latch 规则对齐的依据）：when 驱动的线网被声明为
  reg（hdl-verilog.typort:435-440 `wireOrRegLine`、:375 `outWireOrReg`），
  全部组合赋值汇入单个 `always @(*)`（:827-857 `collectAlwaysBodyLines` /
  `buildMergedAlwaysBlock`，独立 if + 源序阻塞默认赋值、last-wins）；
  无默认赋值且条件不全 → 综合 latch。
- **性能红线**（docs/hdl-selfcheck-design.md §5 引 docs/l13-perf-review-4.md）：
  不 force 任何条件表达式（当黑盒做结构比较）；`chkCdEq` 只比较
  clockName/resetName 字符串（hdl-check.typort:64-67 已是如此）。
  另：`Infer::force` 递归深度在既有 examples 上已达 502-752 层
  （docs/l13-force-recursion-stack-overflow.md §2 表）——这是阶段 2 算法
  选型的硬约束（§3.4）。

---

## 1. 目标与非目标

目标（本设计范围）：

1. 阶段 2：模块内与跨层次组合逻辑环检测（信号级驱动图 + SCC + 环路径 +
   条件互斥豁免）。
2. 阶段 3：组合 latch 推断（条件覆盖完备性）、bitsel/partsel 位区间重叠
   多驱动升级（含对 HDL010 的区间感知抑制）、死条件/重复条件驱动。
3. 阶段 4：模块内 CDC（时钟域传播、跨域读写识别、2FF 同步器结构识别、
   多 bit 误用报警）。
4. per-module 分析结果缓存（阶段 2 起生效，阶段 1 规则同门）。
5. 规则编号 HDL030 起连续分配，全部 warning，报文沿用
   `code|module|signal|message`，LSP/CLI 排水零改动。

非目标（记录在案）：

- 跨模块 CDC（父信号域 → 子模块寄存器域）：需要把父侧连接域信息传入子
  模块检查，且子模块摘要需记录每输入端口的采样域；推迟阶段 5。
- SAT/位向量求解级条件完备性（`c && d` 与 `!c || !d` 这类等价不识别）：
  阶段 5 超越项。
- 位级 def-use（`t[3]` 与 `t[2]` 的读写区分到 bit）：阶段 5；阶段 3 只做
  LHS 区间重叠（多驱动合法性），不做读侧区间。
- 抑制/豁免注释机制（`// chk-suppress HDL032`）：开放问题 §10.6。
- `instanceWithPorts` 原始字符串连接进图（HDL024 盲区沿用）。

---

## 2. 总体架构

### 2.1 检查管线中的位置

```
模块声明 tyck（Phase A 字段求值，重放 ~3 次）
  └─ create 侧: let _res = checkModuleTreeAll(get_global("ModuleTree"))   ← 宏三处改调新入口
       └─ checkModuleTreeAll (hdl-check-graph.typort，新文件)
            ├─ 0. cacheKey = md.name + "#" + Σ exprKey(顶层语句)   ← scanAll 顺带折叠
            ├─ 1. 缓存命中 → 直接 registerModuleTree(t) 并返回
            ├─ 2. 一次扫描产出 DriveSrc + 区间表 → rangeSafe（区间不重叠的部分驱动根名）
            ├─ 3. runChecks(md, rangeSafe)（阶段 1 全部规则；HDL010/011 对
            │      rangeSafe 信号做区间感知抑制，§4.4。ground 门控量在此统一算出，
            │      传给第 5/6 步的值敏感规则，§4.6）
            ├─ 4. 阶段 2：组合图 → Rust builtin check_comb_cycles（Tarjan SCC +
            │      互斥豁免 + 环路径 → 直接经 report_check_issue 报 HDL030/031）
            ├─ 5. 阶段 3：HDL033/034/035 + latch/覆盖（HDL032），typort 内闭环
            ├─ 6. 阶段 4：域传播 fixpoint + 同步链识别（HDL036-039），typort 内闭环
            └─ 7. 缓存落键 + registerModuleTree(t)（原 hdl-check.typort:900 行为不变）
```

要点：

- **一次扫描两份产出**。阶段 2-4 不再各扫一遍树：`scanStmtEx`（graph 文件内，
  复用 `scanExpr` hdl-check.typort:348-403 做 RHS 读取收集）在既有
  `scanStmt` 语义之上额外携带当前 when 使能条件，对每条
  assign/regAssign/regAssignCd/memWrite 产出一个 `DriveSrc`（§3.1）。
  阶段 1 的 `ModFacts` 扫描原样保留，两条扫描都是 O(语句总大小)。
- **Rust/typort 分界线**：Expr 形状敏感的工作（LHS 根名、mux 分支条件、
  条件叶子提取、区间提取、域传播、同步链识别）全部留在 typort；
  需要可变索引数组 + 深递归的工作（Tarjan SCC + 环路径重建 + 互斥豁免
  的成对比对）下沉为一个 Rust builtin。分界依据见 §3.4。
- **lib.rs 零改动**：HDL030-039 的 signal 字段都是信号名，`check_issue_span`
  （lib.rs:1062-1122）现有分支（:1100-1110 的 HDL001/010-013/022/024 特例 +
  默认 find_declaration）覆盖全部新码；HDL030/031 的环路径写在 message 里，
  signal 取环首节点。

### 2.2 文件落点

| 文件 | 改动 |
|---|---|
| `src/prelude/hdl/hdl-check-graph.typort` | **新增**：checkModuleTreeAll、DriveSrc 扫描、组合图构建、条件叶子、区间、域传播、同步链、缓存。加载序在 hdl-check 之后（L13_namespace/mod.rs:3826-3827 的 prelude 列表追加一行） |
| `src/prelude/hdl/hdl-check.typort` | 小改：`runChecks` 增加参数 `rangeSafe: List[String]`（区间感知抑制 HDL010/011，§4.4）；其余不动。hdl-check 无法反向调用后加载的 graph 文件（typort def 按文件序 elaboration），所以入口反转到 graph 文件 |
| `src/prelude/hdl/hdl-macros.typort` | 三个 arm 的 `_res` 行改调 `checkModuleTreeAll`（:378/:416/:447） |
| `src/L13_namespace/cxt.rs` | 新 builtin `check_comb_cycles(module: String, edges: List[String]) -> Unit`（§3.4），紧邻 report_check_issue（:369-392, :670）注册 |
| `src/L13_namespace/mod.rs` | prelude 列表追加 hdl-check-graph（:3827 之后） |
| `src/L13_namespace/legacy_tests.rs` | 规则触发用例 + examples 回归不破 |
| `src/lib.rs` | **零改动**（§2.1） |

备选方案（也成立，实施时可改判）：全部追加进 hdl-check.typort，宏不动、
不新增 prelude 条目。代价是单文件 901 → ~2200 行、评审面大。本设计取
新文件方案，理由：阶段 1 文件保持稳定可回归对照，graph 逻辑可以独立
回滚（删 prelude 条目 + 宏改回一行即退化为阶段 1）。

---

## 3. 阶段 2 设计：组合逻辑环

### 3.1 数据结构

typort 形态（延续阶段 1 的不可变 + 头部 cons 风格，全部在 hdl-check-graph.typort）：

```typort
// 一条驱动语句的"图侧"事实。target 为 LHS 根名（lhsRoot 语义，
// hdl-check.typort:407-411）；subSignal LHS 已归入 conns，不出现在这里。
struct CondSrc {                       // 一个 RHS 读取及其流经条件
    src: String                        // 读取的信号名
    leaves: List[String]               // 该读取的完整条件叶子键（语句使能 ++ mux 分支
                                       // 条件，下方 walkRhs 线程化携带 enable），空表 = 无条件
}

struct DriveSrc {
    target: String
    clocked: Boolean                   // true = regAssign/regAssignCd（时钟驱动，切断组合路径）
    cd: Option[ClockDomain]            // regAssignCd 显式域；regAssign 为 None（模块默认域）
    enable: List[String]               // 语句级使能叶子（when 包裹的完整条件）
    enableKey: String                  // 使能条件的 exprKey（HDL035 判定）
    srcs: List[CondSrc]                // RHS 读取（含 mux 分支级条件细化）
}

struct ModGraph {
    name: String
    nodes: List[String]                // 信号名（decls + 被读取名，去重）
    combEdges: List[CombEdge]          // 仅 assign（组合）语句产生
    clkEdges: List[CombEdge]           // regAssign/regAssignCd 产生（阶段 4 同步链用）
}

struct CombEdge {
    dst: String                        // 被驱动的信号
    src: String                        // 流入的信号
    cross: String                      // "" = 模块内边；否则 = 穿越的实例名（§3.5）
    leaves: List[String]               // 边条件叶子
}
```

从既有 ModuleTree 的产出方式：

- 语句遍历入口即 `md.expr`（`ModuleDef.expr`，hdl-core.typort:221-226），
  沿用 `scanAll` 的顶层语句 exprKey 去重纪律（重放坍缩）。
- `when(cond, body, None)` 语句：body 是单条赋值（createSignalExpr 追加纪律，
  hdl-core.typort:379-382），把 `leavesOf(cond)`（§3.3）作为该赋值的 enable；
  防御性处理嵌套 when（生成的树不出现，hdl-check.typort:341-344 注释）：
  enable 叶子表拼接。
- `assign(lhs, rhs)` → comb DriveSrc；`regAssign/regAssignCd` → clocked
  DriveSrc；`memWrite` → 不产生图边（存储器写口是时序端点，地址/数据/使能
  读取不向 mem 读侧组合穿透），只把 srcs 计入读取集合供阶段 4 使用。
- RHS 读取细化 `walkRhs(e, leaves, acc)`（leaves 起步为语句使能叶子表）：
  `mux(c, tv, fv)` → tv 侧 leaves ++ leavesOf(c)、fv 侧 leaves ++
  leavesOf(!c)（构造 `unary("!", c)` 后取叶子）；其余变体同 leaves 递归
  （unary/binary/bitsel/partsel/memRead）；`subSignal` 不入 srcs（跨层连接
  由 §3.5 的摘要边表达）；字面量跳过。**CondSrc.leaves 即累计结果**
  （含语句使能），图边直接取用。复杂度 O(RHS 大小)。
- **ConnInfo 扩展**（阶段 1 结构的最小增量）：`ConnInfo` 增加字段
  `enable: List[String]`（连接语句的 when 使能，"" 语义 = 无条件）。
  阶段 1 规则不读它；跨层边的条件来自它。
  同时扩展 ConnInfo/InstInfo 扫描处的 when 穿透（`when c { u.port := p }`
  目前进不了 scanStmt 的 conn 分支——生成的树里连接语句同样被
  addWhenContext 包裹，`scanStmt` 的 `when` arm 已经把 body 递归进
  underWhen 分支，补记 enable 即可）。

### 3.2 图构建算法

对每个模块（checkModuleTreeAll 第 3 步）：

1. 扫描产出 `List[DriveSrc]` + `List[ConnInfo]` + `List[InstInfo]`。
2. 模块内 comb 边：对每条 `clocked=false` 的 DriveSrc，对每个
   `CondSrc(src, leaves)` 产出 `CombEdge{dst=target, src, cross="",
   leaves}`。**时钟驱动的 RHS 不产生 comb 边**（寄存器切断组合路径——
   这是"组合环"区别于"任意数据环"的定义性裁剪）。
3. 跨层 comb 边（§3.5）：读全局 "ModuleCombSummary"。
4. 边数 E ≤ Σ|RHS 读取数|，节点数 V ≤ 信号数。构建 O(语句总大小)。

### 3.3 条件叶子与互斥豁免

**叶子提取** `leavesOf(e): List[String]`——对条件 Expr 做纯结构 match，
不 force 任何 Nat（与 exprKey 同级）：

```
flatten 规则：binary(_, "&&", _) → 递归两侧拼接
叶子编码：
  unary("!", x)                → "!" + exprKey(x)
  binary(x, "==", literal(v))  → "eq:" + exprKey(x) + ":" + nat_to_dec(v)
                                 （仅 nat_is_ground(v) 时取 eq 形，否则退化为全式 exprKey，见 §4.6）
  其他                          → exprKey(叶子整体)
```

生成的条件形状（hdl-core.typort:294-310 的 andCond/negatePrev）保证
"&&" 链是左结合平铺的，flatten 一次即得叶子集合。

**互斥判定** `contradicts(L1, L2)`：存在 l1 ∈ L1, l2 ∈ L2 使

1. `l1 == "!" + l2` 或 `l2 == "!" + l1`（`c` vs `!c`）；或
2. `l1 = "eq:s:v1"`、`l2 = "eq:s:v2"` 且 s 相同、v1 ≠ v2
   （同 switch 值域不同 is 分支：`sel==0` vs `sel==1`）。

叶子比对是 O(|L1|·|L2|) 字符串比较，叶子数 = 条件链长度（个位数）。

**豁免规则（拍板）**：环上所有边同时活跃才可能振荡；因此**环的边集中
若存在两条边条件互斥，则该环在语法上不可满足，豁免不报**。这是可满足性
的保守下近似：只豁免"保证不可满足"的情形，绝不豁免可能真实的环——
代价是语法等价但字面不同的条件（如 `a && b` vs `b && a`）不豁免（§10.3）。

验收例（§9.2 loopExempt）：`a ← b (sel)` 与 `b ← a (!sel)` 互斥 → 豁免；
cross-coupled mux（`a := sel ? x : b; b := sel ? a : y`）依赖 mux 分支
细化（§3.1 walkRhs）得到 `a ← b (!sel)`、`b ← a (sel)` → 豁免。

### 3.4 Tarjan SCC：纯 typort 可行性分析与拆分拍板

**纯 typort 实现的三个代价**：

1. **递归深度**：Tarjan DFS 深度 = |V|。`Infer::force` 递归在既有语料
   （无任何检查器递归）已达 502-752 层（docs/l13-force-recursion-stack-overflow.md
   §2 实测表，debug 测试线程 2 MiB 栈已顶爆过一次）；把 V 层 DFS 叠上去，
   数百信号的模块在 debug 构建下有确定的栈溢出风险。eval/force/force_chain
   都曾因同类问题迭代化（同文档 §1"同族问题"）。
2. **不可变结构下的状态更新**：index/lowlink/onStack 需要按节点更新的映射，
   typort 只能线程化传递持久化 List：每条边松弛 O(V) 查找 + O(V) 重建，
   总计 O(V·(V+E)) 的分配churn，且随 ~3 次字段重放重复（缓存只救一次内
   的前两遍，第一遍本身要付）。
3. **环路径重建**同样要可变 parent/栈结构，typort 化后常数再翻倍。

**拍板（拆分方案）**：图算法下沉 Rust builtin，typort 保留全部 Expr 侧工作。

```rust
// cxt.rs，紧邻 report_check_issue（:369）
fn check_comb_cycles(infer, _decl, args) -> Option<Rc<Val>>
// args: (module: String, edges: List[String])
// 每条边一行: "dst|src|cross|leaves"，leaves 为 ";" 连接的叶子键（可为空段）
```

builtin 内部（纯内存 Vec/HashSet）：

1. 解析边 → 邻接表（src → dst 方向即数据流方向）。
2. Tarjan SCC（迭代式或显式栈均可，Rust 无栈深顾虑）。候选环：
   |SCC| ≥ 2，或单节点自环（`t := t + 1` 自然产生自边）。
3. 互斥豁免（**per-cycle**，2026-09-27 评审修正）：先做 SCC 级**快速预筛**——
   内部边两两 `contradicts`（§3.3 规则原样移植到字符串比对），无任何互斥
   对则该 SCC 的环没有一条可能被豁免，直接跳过逐环判定；预筛本身**不豁免
   任何环**。豁免判定落在重建出的**每条简单环自身**：仅当该环的边集内存在
   互斥对才豁免这一条环。早期成文的"SCC 内任一互斥对 → 整环豁免"已被评审
   证伪为漏报：互斥对的两条边不必同属一条环（评审探针 `when c {x:=y}
   otherwise {x:=x}` + `y := x&&en`——SCC{x,y} 里保持环 x→x(!c) 与读边
   x→y(c) 互斥，真环 x→y→x(c∧en 可满足) 并不含这对边，旧实现连它一起
   豁免、零告警）。
4. 环路径：在 SCC 内从首个节点枚举经过它的**全部**简单环（步数界 100_000、
   环数界 4096），逐环豁免判定后渲染 `a -> b -> a`；搜索被截断且无一环
   获报时回退为"存在环"式报告（取第一条内部边，不带全路径）——宁误报
   不漏报。
5. 报告：该环的边全为模块内边 → `report_check_issue("HDL030", module, 环首节点,
   "combinational loop: a -> b -> a")`；该环自身含 ≥1 条 cross 边 → `HDL031`，
   message 带实例名（§3.5）。直接走既有行级去重管道，typort 侧零回传。

**降级方案（若未来要撤掉 Rust builtin）**：typort 不动点可达性
`R(v) = {v} ∪ ⋃_{v→w} R(w)` 迭代至不动点，环判定 = ∃边 (u,v)：u ∈ R(v)；
环路径用有限深度（≤ 32）的受限 DFS 重建，超深只报环存在不带路径。
复杂度 O(V²E) 上限、无深递归（每轮是浅层 fold），模块级规模可承受。
作为设计保留，不实施。

### 3.5 跨层次组合环（子模块组合穿透摘要）

**摘要构造**：每个模块在自身检查完成时（checkModuleTreeAll 第 5 步后），
在其组合图上做可达性：从各 input 端口节点出发沿 comb 边传播，凡到达
output 端口（kOut；kOutReg 是寄存器输出，切断）即记录一对穿透路径。
跨层边参与传播（子模块的摘要已在——子构造器先于父 `_res` 运行，与
端口表同一时序论证，hdl-selfcheck-design.md §2）。

```typort
struct CombPath { from: String, to: String }          // 子模块 input → output 组合对
struct CombSumEntry { mdl: String, paths: List[CombPath] }
// 全局 "ModuleCombSummary"：portTableAdd 式按 mdl 名覆盖注册（hdl-check.typort:534-535 同款）
```

复杂度 O(V·E)/模块（逐源 BFS 的 typort 化，端口数 × 图尺寸，小）。

**父图接线**：父模块对每对连接——`u.ip := p`（isLhs=true，条件取
ConnInfo.enable）与 `q := u.op`（isLhs=false）——若子摘要含 `ip→op`，
产出跨层边 `CombEdge{dst=q, src=p, cross="u", leaves=enable(q 侧) }`。
两侧条件拼接：`leaves = lhsConn.enable ++ rhsConn.enable`。
子摘要缺失（raw 实例 HDL024、或模块不在表）→ 不产边（保守漏检，
与 HDL022 对缺失端口表的行为一致，hdl-check.typort:795-796）。

**归因**：环内任一边 cross ≠ "" → HDL031，signal 取环首父信号，
message 形如 `combinational loop through instance 'u': x -> y -> x`。
纯子模块内部的环在子模块自己的检查里已报（HDL030），父图不重复。

### 3.6 per-module 分析结果缓存

```typort
// 全局 "CheckCacheDone"：List[String]，元素 = cacheKey
// cacheKey = md.name + "#" + Σ exprKey(顶层语句)（scanAll 的 seen 表本来就是它，折叠成一个串）
```

- **键设计**：模块名 + 全部顶层语句的 exprKey 拼接。exprKey 覆盖：信号名、
  宽度（nat_to_dec）、寄存器显式域名、字面量值、条件结构、连接对——
  任何影响图形态的变化都改键。同名参数化模块两实例（myAdder[8]/[16]）
  在 runtime 轮宽度 ground、键不同，不会互撞；Phase A 轮宽度全渲染 0、
  两实例同键——可接受：Phase A 轮是抛弃树，其值敏感告警本就被门控
  （§4.6），且阶段 1 对该轮同样不产出有效告警。
- **失效时机**：缓存放 mutable 全局，随 `mutable_map` 每文件清空
  （lib.rs:1320/1880/2503）自动失效；同文件内 LSP 每次按键重 elaborate
  即全新一轮。字段重放 ~3 次：第 1 次计算并落键，第 2/3 次命中跳过。
  **注册表/端口表注册不进门**（必须每次幂等覆盖，hdl-selfcheck-design.md
  §2"永不去重跳过"约束）。
- **粒度**：阶段 1+2+3+4 全部规则同门（它们都是树的确定性函数）。命中时
  跳过规则求值但保留 `registerModuleTree`。
- **键计算成本**：exprKey 在 scanAll 中已逐语句计算过（去重需要），缓存键
  只是复用结果做字符串拼接，O(语句总长) 增量，不构成新开销项。

---

## 4. 阶段 3 设计：latch / 条件覆盖 / 位区间重叠

### 4.1 与 Verilog 生成器 always 结构的对齐（规则的事实依据）

生成器把"when 驱动的信号"声明为 reg（hdl-verilog.typort:375/:435-440），
所有组合赋值汇入单个 `always @(*)`（:849-857）：每个 when 节点是独立
`if (cond)`（:809-816），**无条件 assign 是源序阻塞默认赋值**（:836-842，
注释明言 last-wins）。因此：

- 信号有任一无条件组合驱动 → 覆盖完备（default 存在），无论多少条件驱动。
- 无无条件驱动、条件驱动集合不覆盖全空间 → reg 保持旧值 = **latch**。
- regAssign 目标是寄存器，条件不覆盖是使能语义（保持），**不是 latch**——
  规则必须按目标种类分流。

注意 HDL011（uncond+cond 混合，hdl-check.typort:756-759）与 latch 判定
互补：uncondComb ≥ 1 → HDL011 管辖（且 latch 不报）；uncondComb = 0 才进
latch 判定。两规则不会对同一信号同时开火。

### 4.2 latch 推断（HDL032）

**判定**：信号 d 满足

1. `declIsKind(d, kWire) ∨ declIsKind(d, kOut)`（kReg/kOutReg 排除——寄存器
   使能语义；kIn 排除——HDL023 管辖；kInOut 不经 `:=` 驱动；kMem 排除）；
2. `DriveFacts.condComb ≥ 1 ∧ uncondComb = 0`（facts 复用，hdl-check.typort:183-191）；
3. 条件覆盖不完备（§4.3）。

→ `HDL032|<module>|<d>|inferred latch: conditional drivers do not cover all cases (no unconditional default)`

known-latch 与生成器行为一致：这类信号在 Verilog 里恰好被声明为
`reg` 且在 always@(*) 中缺 default——报的就是综合器会造 latch 的那件事。

### 4.3 条件覆盖完备性判定（语法）

设 d 的全部组合驱动使能条件为 C = [c1..cn]（叶子集 Li，§3.3 提取）。
**完备 ⟺ 满足 T1 ∨ T2 ∨ T3**：

- **T1（存在 default）**：uncondComb ≥ 1（进不了本规则，列出只为完备）。
- **T2（互补对）**：∃ i≠j：Lj = { ¬q | q ∈ Li }（逐叶取反、数量相等）。
  覆盖 `when c {} otherwise {}` 两分支形态（ci={sel}, cj={!sel}）。
- **T3（otherwise 收口）**：∃ k：Lk 的叶子全是否定形，且其否定对象集合
  恰等于其余条件中**全部肯定叶子**的集合（计重复）。覆盖 switch+default
  与 when/elsewhen*/otherwise 链：switch 两 is + default 生成
  {eq:sel:0}、{eq:sel:1, !eq:sel:0}、{!eq:sel:0, !eq:sel:1}——T3 用
  c3 的否定对象 {eq:sel:0, eq:sel:1} 恰等于 c1∪c2 的肯定叶子 → 完备。
  Bool elsewhen 链同理（p1 / p2&&!p1 / !p1&&!p2）。

复杂度 O(n²·L²)（n = 驱动数）。T2/T3 只依赖叶子键字符串比对，无 force。

**为什么三个形态就够**：宏只生成这三种形状（hdl-macros.typort:177-225 的
when/switch 全部 arm 都收敛为"每分支一条全条件 when 节点"）；库代码
（hdl-crossclock 等）同形态。用户绕过宏手拼 Expr 的情形不承诺覆盖。

### 4.4 位区间重叠多驱动（HDL033）与 HDL010/011 的区间感知抑制

**动机**：`t.slice[3,0] := a` 与 `t.slice[7,4] := b` 是合法的部分驱动，
但阶段 1 的 `lhsRoot`（hdl-check.typort:407-411）把它们折成同根两驱动 →
HDL010 误报。阶段 3 升级为区间感知：

**区间提取**（LHS 形状 → [hi, lo]，全部来自 Expr 变体的字面量参数）：

| LHS 形状 | 区间 |
|---|---|
| 裸 create*/createSInt*（带宽度 w） | [w-1, 0] 全区间 |
| bitsel(b, literal(v)) | [v, v] |
| partsel(b, literal(h), literal(l)) | [max(h,l), min(h,l)] |
| bitsel/partsel 的索引非字面量（动态） | 未知（该驱动不参与重叠判定，也不参与抑制） |
| 索引为 Rigid（Phase A 轮） | nat_to_dec 渲染 0 → 全体塌成 [0,0]，**必须门控**（§4.6） |

宽度 w 从 decl（createWidth 等变体参数）取；区间比较用递归 `chkNatLe`
（graph 文件内自写，Peano 结构 match，操作数都是小字面量）。

**判定（HDL033）**：同根两个 comb 驱动，双方区间均为已知静态，且
`lo1 ≤ hi2 ∧ lo2 ≤ hi1`（相交），且两边条件叶子不互斥（复用 §3.3）→
`HDL033|<module>|<root>|overlapping bit ranges [<hi1>:<lo1>] and [<hi2>:<lo2>] on multiple drivers`。

**对 HDL010/011 的抑制**：信号的全部 comb 驱动均为部分驱动（bitsel/partsel
LHS）、两两静态区间不相交（或条件互斥）→ 计入 `rangeSafe` 列表传给
`runChecks`（§2.2 的签名改动）；`ruleDrivers`（hdl-check.typort:732-769）
对 rangeSafe 信号跳过 uncondComb ≥ 2 与 uncond+cond 混合判定（HDL010/011）。
任一驱动是全区间（裸 LHS）或动态索引 → 不抑制（保持阶段 1 行为，无回归）。
HDL012/013（comb/clk 混用、多域）不受区间影响，不抑制。

### 4.5 死条件与重复条件（HDL034 / HDL035）

- **HDL034（条件永假，死驱动）**：某驱动自身叶子集同时含 `p` 与 `!p`
  （或 `eq:s:v1` 与 `eq:s:v2` 同 s 异 v）→ 该赋值不可达。
  `HDL034|<module>|<target>|driver condition is always false (contains both 'p' and '!p')`。
  这同时是互斥机制的退化自检：生成器照发这条 if，综合器剪掉。
- **HDL035（同条件重复，早者被遮蔽）**：同信号两驱动的 `enableKey` 相同
  （exprKey 比对）→ always 块源序下后者恒胜，前者死。
  `HDL035|<module>|<target>|conditional driver shadowed by a later driver with the same condition`。
  已知"误报"：用户故意 last-wins 风格连写两遍不同 RHS——warning 语义下
  可接受，文档明示。

### 4.6 Phase A（Rigid）轮门控

阶段 3/4 中一切**读 Nat 值**的判定（区间端点、eq 叶子的 v、宽度取值）
在 Phase A 轮会把 Rigid 渲染成 0 而失真。沿用 HDL004 的门控判据
（hdl-check.typort:605-618）：`widthScanAll` 的 groundCount = 0 的轮次
即 Phase A 产物 → HDL033/034/035/038 的值敏感部分整体跳过。
实现上 runChecks 已算过 WidthScan，把 `ground: Boolean` 随参数传给
graph 文件的规则入口即可（不重复扫描）。

---

## 5. 阶段 4 设计：CDC（模块内）

### 5.1 时钟域锚点与传播算法

**锚点**（优先级从高到低）：

1. `regAssignCd(l, _, cd)` → dom(l) = cd（驱动侧锚，DriveSrc.cd 直接可得）；
2. 声明变体 `createRegWidthCd / createRegWidthInitCd / createSIntRegWidthCd /
   createSIntRegWidthInitCd` → dom(name) = 声明 cd（graph 文件内独立小扫描
   `regCdDecl`，不扩阶段 1 的 SigDecl）；
3. 其余 regAssign 目标与全部组合信号 → 模块默认域 `md.cd` 起步；
4. **域中立**：input/inout 端口、字面量、`memRead`/`createMem`（存储器无域；
   这同时保证现版 readSyncCC ≡ readSync 不产生误报，hdl-clock.typort:68-72）、
   output 端口不设锚（由驱动传播）。

**传播**（fixpoint，纯 typort）：

```
dom(x) 初值：锚点域 / 组合信号 ⊤(未知)
迭代（≤ V 轮，每轮 O(E)）：
  对每条 comb DriveSrc：dom(target) ∪= ⋃ dom(src)，中立 src 跳过
  域集合以 List[ClockDomain] + chkCdInList（hdl-check.typort:193-199）去重，
  chkCdEq 只比对 clockName/resetName（性能红线内）
```

V、E 是模块级规模（几十），O(V·E) × 常数可忽略；不引入 Rust 依赖。

### 5.2 跨域读写识别

对每条 clocked DriveSrc（目标 R，域 D = 锚点解析结果）：

- 任一 src s 的 dom(s) = 单域 {D'} 且 D' ≠ D → **CDC 边 s→R**。
  源是组合信号（被传播赋了域）还是寄存器，写入 message 区分
  （"combinational" / "registered"）。
- |dom(s)| ≥ 2 → 该组合信号已被 HDL036 命中，不再对 R 重复报（去噪）。
- dom(s) 未知（端口/字面量/mem）→ 不报。

- **HDL036（组合信号多域汇聚）**：组合信号 x 的 dom(x) ≥ 2 域 →
  `HDL036|<module>|<x>|combinational signal mixes domains clkA/clkB`。
  这是"汇聚点处理"：不猜主域，直接报混合。
- **HDL037（跨域寄存采样无同步器）**：CDC 边 (s→R) 且 R 不属于任何
  已识别同步链（§5.3）→
  `HDL037|<module>|<R>|register 'R' (clkB) samples <combinational|registered> 's' (clkA) without a synchronizer chain`。
  链长为 1 的采样（只有一级就往外供）自然落进本规则（§5.3 步骤 4）。

### 5.3 2FF 同步器结构识别

在时钟驱动图上做链识别（节点 = 寄存器，边 = 单源无条件时钟驱动）：

1. 从每条 CDC 边的目标 R0 出发；**资格条件**（全部名字级，复用
   DriveFacts + DriveSrc）：
   - R0 恰有一个驱动：`uncondClk == 1 ∧ condClk = 0`；
   - 该驱动 srcs == {s}（单源）；
   - R0 的读者集合 = {R1}，R1 同为寄存器、无条件时钟驱动、同域（chkCdEq）。
2. 递归 R1 → R2 → ... 直到读者不再满足单一后继；得到链 R0..Rk。
3. **链长 ≥ 2（R0、R1 至少两级）→ 已识别同步器**：
   - R0 的 CDC 边豁免（HDL037 不报）；
   - 消费者只读**末级 Rk** → 合法；
   - **中段读取（HDL039）**：某中间级 Ri (i<k) 的读者 ∉ {R(i+1)} ∪
     {XOR 边沿检测形态}——XOR 豁免 = 某 RHS 的 exprKey 恰为
     `binary(Ri, "^", R(i+1))`（toggle 同步器的标准边沿检测，
     hdl-crossclock.typort:138/:164）→ 报
     `HDL039|<module>|<Ri>|synchronizer mid-stage read: consumer bypasses the chain head`。
   - **多 bit（HDL038）**：链首宽度（声明变体的 w）> 1 →
     `HDL038|<module>|<R0>|multi-bit (w) signal crossed to <clkB> through a 2-FF synchronizer — Gray coding required`。
4. 链长 = 1（R0 无合格后继）→ 不构成同步器，R0 的 CDC 边照报 HDL037
   （message 注明 chain length 1）。

**命名陷阱（实现注意）**：`bufferCCUIntChain`（hdl-crossclock.typort:13-23）
depth=2 时**先建 `_sync2`（第一级）后建 `_sync1`（第二级，返回值）**——
后缀数字与链序相反。识别一律走通用链 walk，禁止任何 "`_sync1` 是第一级"
式后缀假设；名字模式只可作为调试注释。

**验收映射**（examples/hdl/21-crossclock.typort）：

- `ccPulse`（21a）：pulseCCByToggle / ccByToggleUInt / bufferCCUIntCd 的
  sync 链全部被识别；sync1 被 XOR 边沿检测读取走 HDL039 的 XOR 豁免；
  data 为输入端口域中立 → **零 CDC 告警**。
- `ccFifo`（21b，streamFifoCC）：wrPtrSync1←wrPtr（主域→outCd，2 bit）、
  rdPtrSync1←rdPtr（outCd→主域，2 bit）两条链识别成功但宽度 > 1 →
  **两条 HDL038**（这正是文档注明的"二进制指针需 gray code"已知缺陷，
  hdl-crossclock.typort:178-180）；`empty = rdPtr == wrPtrSync2` 混合
  rdPtr(outCd) 与 wrPtrSync2(主域) → **一条 HDL036**。
  全部为预期真阳性，回归断言按 contains 式书写。

### 5.4 范围边界

跨模块 CDC（父信号 → 子模块寄存器）不做：子模块检查时看不到父侧连接域，
父侧检查需要子摘要记录"输入端口被哪域寄存器采样"。摘要结构已预留扩展位
（CombPath 加 sampledBy 域列表），列为阶段 5 首选项（§10.5）。

---

## 6. 规则总表（HDL030-039）

严重度全部 warning（阶段 1 校准流程完成后逐条评估升级）。
信号字段：HDL030/031 = 环首节点；HDL033 = 根名；其余 = 目标信号名——
全部是纯信号名，不引入新的 `inst.port` 形态。lib.rs 回扫：全部落入
`check_issue_span` 默认 find_declaration 分支（lib.rs:1109），既有连接分支
（lib.rs:1080-1093）不需要扩展。

| 码 | 名称 | 判定 | 严重度 | 已知误报/漏报场景 |
|---|---|---|---|---|
| HDL030 | 组合逻辑环 | 组合图 SCC ≥2 或自环，环边条件两两不互斥 | warning | 误报：条件可满足性只能语法判定（漏豁免）；撞名合并出虚假环（§10.2）。漏报：instanceWithPorts 边不可见 |
| HDL031 | 跨层次组合环 | 环含 ≥1 条子模块穿透边（cross ≠ ""） | warning | 漏报：子摘要缺失（raw 实例 / 未注册模块）时不产边 |
| HDL032 | 推断锁存器 | kWire/kOut ∧ condComb ≥1 ∧ uncondComb =0 ∧ 非 T2/T3 完备 | warning | 误报：完备但语法不可证（两个独立 when 联合完备、同条件异写法） |
| HDL033 | 位区间重叠多驱动 | 同根两静态区间相交 ∧ 条件不互斥 | warning | 漏报：动态索引对不判定；Rigid 轮已门控不误报 |
| HDL034 | 条件永假（死驱动） | 驱动自身叶子含 p 与 !p，或 eq:s:v1 / eq:s:v2 同 s 异 v | warning | 无已知误报；等价但非字面相反的永假式漏报 |
| HDL035 | 同条件重复遮蔽 | 同信号两驱动 enableKey 相同（早者被遮蔽） | warning | 故意 last-wins 风格会报（文档明示） |
| HDL036 | 组合信号多域汇聚 | 传播后 dom(x) ≥ 2 域 | warning | 漏报：跨模块域不传播；memRead 域中立 |
| HDL037 | 跨域寄存采样无同步器 | 时钟驱动读域 ≠ 目标域 ∧ 目标不在已识别链 | warning | 误报：派生/同源时钟域无法从名字识别；漏报：端口源域未知 |
| HDL038 | 多 bit 过 2FF 同步器 | 已识别链链首宽度 > 1 | warning | streamFifoCC 二进制指针为**预期**告警（验收用例） |
| HDL039 | 同步链中段被读取 | 中间级读者 ∉ {下一级, 相邻级 XOR} | warning | 其他有意中段读取会误报（抑制机制开放，§10.6） |

---

## 7. 性能预算（红线自查）

红线（docs/hdl-selfcheck-design.md §5）：不 force 条件表达式；chkCdEq 只比
clockName/resetName。逐条对照：

| 操作 | 层级 | 复杂度 | force 风险 |
|---|---|---|---|
| 顶层语句 exprKey 去重 + 缓存键拼接 | 名字级 | O(语句总大小)/模块 | 无（语句在 def Vec 中已是 WHNF；exprKey 与阶段 1 同一函数） |
| DriveSrc / walkRhs / leavesOf | 结构级 | O(语句总大小) | 无——只 match Expr 构造子；nat_to_dec 对 stuck Nat 渲染 0 不求值（hdl-core.typort:780-783 已证实的既有行为） |
| leavesOf 的 eq 叶子 | 结构级 | O(1)/叶子 | 无（nat_is_ground 是 Rust 结构判定，cxt.rs:804，不 force） |
| 互斥比对 | 结构级 | O(L²)/边对，L 个位数 | 无（字符串比对） |
| Tarjan SCC + 环路径 | Rust 内存 | O(V+E) | 无递归栈风险（对比：纯 typort DFS 深度=V 叠加 502-752 层 force 深度，§3.4 拍板依据） |
| 跨层摘要可达性 | 结构级 | O(V·E)/模块 | 无 |
| 区间两两判定 | 结构级 | O(k²)/信号，k=同根驱动数 | 无（chkNatLe 递归深度 = Nat 值位数，字面量小；Rigid 轮门控跳过） |
| T2/T3 完备性 | 结构级 | O(n²·L²)/信号 | 无 |
| 域传播 fixpoint | 结构级 | ≤ V 轮 × O(E)，cd 集合 ≤ 模块域数 | 无（chkCdInList 复用，字符串比对） |
| 同步链识别 | 结构级 | O(V+E)（读者/被读者索引一次建表） | 无 |
| 缓存命中路径 | 名字级 | O(键长) 字符串查找 ×2 次重放 | 无 |

总量级：单模块一次性 O(语句总大小 + V·E)；重放 ~3 次被缓存压成
1 次分析 + 2 次 O(键长) 命中检查。对比阶段 1（每次重放全量规则线性跑），
阶段 2-4 上线后**重放路径反而变便宜**。无任何新全局热路径、无 force 新增。

---

## 8. 实施计划

按依赖序三步，每步独立可回归（examples/hdl 全量 + legacy_tests）：

**第 1 步（阶段 2 主体，含基建）**

1. cxt.rs：`check_comb_cycles` builtin（解析 "dst|src|cross|leaves" 行、
   Tarjan、互斥豁免、环路径、report HDL030/031）+ 注册。
2. hdl-check-graph.typort：DriveSrc/ModGraph/CombEdge、scanStmtEx、
   leavesOf/walkRhs、contradicts、摘要 "ModuleCombSummary"、缓存
   "CheckCacheDone"、`checkModuleTreeAll` 入口（调 runChecks + 图检查 +
   registerModuleTree）。
3. hdl-check.typort：`runChecks` 加 `rangeSafe: List[String]` 参数
   （本步先恒传 lnil，行为不变）；ruleDrivers 读它。
4. hdl-macros.typort：三处 `_res` 改调 checkModuleTreeAll；
   mod.rs prelude 列表追加 hdl-check-graph。
5. 用例：combLoop / selfLoop / loopExempt / passthru+crossLoop（§9.1-9.2）。

**第 2 步（阶段 3）**

1. graph 文件追加：区间提取 + chkNatLe、HDL033、rangeSafe 计算（接线第 1 步
   的 runChecks 参数）、T2/T3 完备性 + HDL032、HDL034/035、Phase A 门控
   （ground 参数贯通）。
2. 用例：latchDemo / coveredCtrl / sliceOK / sliceOverlap / deadCond /
   shadowCond（§9.3）。

**第 3 步（阶段 4）**

1. graph 文件追加：regCdDecl 锚点扫描、域传播 fixpoint、HDL036、
   CDC 边分类 + 同步链 walk、HDL037/038/039（XOR 豁免）。
2. 用例：cdcDirect / cdcOneStage（§9.4）+ examples/hdl/21-crossclock
   预期告警断言（HDL036×1 + HDL038×2，§5.3）；全 examples 校准
   （流程同阶段 1 §6：逐条核验真阳性，回归断言 contains 式）。

---

## 9. 验收用例

报文格式对齐阶段 1：`code|module|signal|message`（LSP 展示为
`[hdl][warning] CODE [module] signal: message`，L13_namespace/mod.rs:4173-4185）。

### 9.1 阶段 2：真环与自环

```typort
module combLoop {
    input en = Bool
    output ao = Bool
    output bo = Bool
    let a = Bool
    let b = Bool
    a := b && en
    b := !a
    ao := a
    bo := b
}
```

期望：

```
HDL030|combLoop|a|combinational loop: a -> b -> a
```

```typort
module selfLoop {
    input d = UInt[8]
    output q = UInt[8]
    let t = UInt[8]
    t := t + 1
    q := t
}
```

期望：`HDL030|selfLoop|t|combinational loop: t -> t`

### 9.2 阶段 2：互斥豁免与跨层次环

```typort
// 互斥豁免：环两边条件 sel / !sel 语法互斥 → 不报 HDL030
module loopExempt {
    input sel = Bool
    input x = UInt[8]
    input y = UInt[8]
    output ao = UInt[8]
    output bo = UInt[8]
    let a = UInt[8]
    let b = UInt[8]
    when sel {
        a := b
    } otherwise {
        a := x
    }
    when sel {
        b := y
    } otherwise {
        b := a
    }
    ao := a
    bo := b
}
```

期望：无 HDL030（且 T2 完备 → 无 HDL032），零告警。

```typort
// 跨层次环：x →(子模块组合穿透) y →(父内组合) x
module passthru {
    input pin = Bool
    output pout = Bool
    pout := !pin
}
module crossLoop {
    input en = Bool
    let x = Bool
    let y = Bool
    let u = passthru.create
    u.pin := x
    y := u.pout
    x := y && en
}
```

期望：

```
HDL031|crossLoop|x|combinational loop through instance 'u': x -> y -> x
```

### 9.3 阶段 3：latch / 覆盖 / 区间 / 死条件

```typort
module latchDemo {
    input en = Bool
    input d = UInt[8]
    output q = UInt[8]
    let l = UInt[8]
    when en {
        l := d
    }
    q := l
}
```

期望：`HDL032|latchDemo|l|inferred latch: conditional drivers do not cover all cases (no unconditional default)`
（对照组：同模块加 `} otherwise { l := d2 }` 后零告警。）

```typort
// 区间不重叠：不报 HDL033，且 HDL010 被抑制（阶段 1 会误报）
module sliceOK {
    input a = UInt[4]
    input b = UInt[4]
    output q = UInt[8]
    let t = UInt[8]
    t.slice[3, 0] := a
    t.slice[7, 4] := b
    q := t
}
// 区间重叠：[5:0] ∩ [7:4] = [5:4]
module sliceOverlap {
    input a = UInt[6]
    input b = UInt[4]
    output q = UInt[8]
    let t = UInt[8]
    t.slice[5, 0] := a
    t.slice[7, 4] := b
    q := t
}
```

期望：sliceOK 零告警；sliceOverlap 报
`HDL033|sliceOverlap|t|overlapping bit ranges [7:4] and [5:0] on multiple drivers`。

```typort
module deadCond {
    input c = Bool
    input a = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when c && !c {
        s := a
    }
    q := s
}
```

期望：`HDL034|deadCond|s|driver condition is always false`（另 HDL032
照常报——死驱动不构成覆盖）。

```typort
module shadowCond {
    input en = Bool
    input a = UInt[4]
    input b = UInt[4]
    output q = UInt[4]
    let s = UInt[4]
    when en {
        s := a
    }
    when en {
        s := b
    }
    q := s
}
```

期望：`HDL035|shadowCond|s|conditional driver shadowed by a later driver with the same condition`。

### 9.4 阶段 4：CDC

```typort
def cdA: ClockDomain = ClockDomain.mk "clkA" "rstA" Async RisingEdge ActiveHigh
def cdB: ClockDomain = ClockDomain.mk "clkB" "rstB" Async RisingEdge ActiveHigh

// 单 bit 2FF 链（手动等价 bufferCC）：识别为同步器，零 CDC 告警
module cdcGood[cdA] {
    output q = UInt[1]
    let src = newUIntRegInitCdNamed("src", 1, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let r1 = newUIntRegCdNamed("flag_sync2", 1, cdB)     // 第一级（bufferCC 命名陷阱：_sync2 在前）
    let _ = createSignalExpr("", regAssignCd(r1.zz_expr, src.zz_expr, cdB))
    let r2 = newUIntRegCdNamed("flag_sync1", 1, cdB)     // 第二级 = 末级
    let _ = createSignalExpr("", regAssignCd(r2.zz_expr, r1.zz_expr, cdB))
    q := r2
}
```

期望：零 CDC 告警（src→flag_sync2 的跨域边被 2 级链豁免；中间级 flag_sync2
的读者只有下一级驱动；消费者只碰末级 flag_sync1）。

```typort
// 同一结构、链长 1：不构成同步器 → HDL037
module cdcBad[cdA] {
    output q = UInt[8]
    let src = newUIntRegInitCdNamed("src", 8, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let hop = newUIntRegCdNamed("hop", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(hop.zz_expr, src.zz_expr, cdB))
    q := hop
}
```

期望：`HDL037|cdcBad|hop|register 'hop' (clkB) samples registered 'src' (clkA) without a synchronizer chain (chain length 1)`

```typort
// 多 bit 过 2FF：链识别成功但宽度 > 1 → HDL038
module cdcWide[cdA] {
    output q = UInt[8]
    let src = newUIntRegInitCdNamed("src", 8, 0, cdA)
    let _ = createSignalExpr("", regAssignCd(src.zz_expr, literal(0), cdA))
    let r1 = newUIntRegCdNamed("w_sync2", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(r1.zz_expr, src.zz_expr, cdB))
    let r2 = newUIntRegCdNamed("w_sync1", 8, cdB)
    let _ = createSignalExpr("", regAssignCd(r2.zz_expr, r1.zz_expr, cdB))
    q := r2
}
```

期望：`HDL038|cdcWide|w_sync2|multi-bit (8) signal crossed to clkB through a 2-FF synchronizer — Gray coding required`
（signal 取链首声明名；streamFifoCC 的 wrPtrSync1/rdPtrSync1 同理。）

> 端口域中立（§5.1 锚点 4）意味着"输入端口直接进跨域寄存器"**不报**
> （端口真实域不可知，有意保守）；触发 HDL037 的可靠写法是经一个
> 显式域寄存器中转，如上。`regAssignCd` 直呼与库内部同形态
> （hdl-crossclock.typort:81/:135），低层 API 全局可见，检查器验收可用。

**examples 回归预期**（§5.3）：21-crossclock 的 ccFifo 产生
HDL036 ×1（empty）+ HDL038 ×2（wrPtrSync1 / rdPtrSync1 链），其余 examples
/hdl 新告警逐条核验后纳入断言。

---

## 10. 风险与开放问题

1. **Tarjan 递归深度（若回退纯 typort）**：force 深度已 502-752
   （docs/l13-force-recursion-stack-overflow.md），DFS 深度 = V 叠加会在
   debug 测试线程溢出。拍板 Rust builtin 后此风险消除；降级方案
   （§3.4 不动点 + 深度受限 DFS）已在设计内，但环路径报告会降级为
   "存在环"不带路径。
2. **名字级撞名盲区的升级路径**：同模块两个信号撞名（zz_ 自动名等）在图里
   合并为一个节点，可能造出虚假环或漏环（阶段 1 §5 已记录同类）。升级
   依赖模块重设计引入唯一信号 ID；届时 CombEdge/DriveSrc 把 String 换成
   ID 即可，算法不变。
3. **互斥豁免的完备性**：语法判定是可满足性的保守下近似。`a && b` 与
   `b && a`、`!(a || b)` 与 `a`（实际互斥）都不豁免 → 误报环（warning
   可容忍）；反向（把真环豁免掉）只可能发生在叶子编码碰撞上——eq 叶子
   已用 nat_is_ground 门控 Rigid 值，剩余风险为 exprKey 本身的表达力
   （与阶段 1 共用，无新增）。
4. **参数化模块双实例撞名**（hdl-core.typort:628-630 已知限制）：摘要表、
   端口表同病。缓存键在 runtime 轮含 ground 宽度可区分，Phase A 轮同键
   （可接受，该轮告警本被门控）。若未来模块重设计引入实例唯一名，三表
   （PortTable / Registry / CombSummary / Cache）一并换键。
5. **跨模块 CDC 的推进路径**：CombSummary 加 `sampledBy: List[ClockDomain]`
   （输入端口被子内哪些域的寄存器采样）+ 父侧连接域合并 → 即可在父侧报
   跨模块 CDC。列为阶段 5 首选项，本阶段不实现。
6. **抑制机制缺失**：HDL039 的非 XOR 中段读取、HDL032 的语法不可证完备
   等场景没有用户侧豁免手段。候选设计：`chkSuppress(code, signal)` 库
   函数向 "CheckSuppress" 全局注册 (code, module, signal)，排水侧过滤；
   涉及报告管道三方（builtin/排水/span），单独立项。
7. **latch 与 HDL011 的语义交叠**：uncond+cond 混合现在由 HDL011 报
   （"非法 Verilog"），而生成器实际用 whenSigs 优先 + 源序 default 处理了
   这种混合（hdl-verilog.typort:836-842）——HDL011 的措辞可能过严。
   本设计不动它；若 examples 校准中确认纯误报，随阶段 3 一起降级/改写
   消息（单列小改动，不并入本次规则表）。
8. **readSyncCC 语义升级的联动**：语言侧真正实现跨时钟同步读后
   （docs/spinalhdl-gap.md:61 的 🟡 项），memRead 域中立的假设需要重审
   （同步读端口有真实域属性），HDL036/037 的锚点表要加 mem 域。
9. **缓存与 seen 去重的叠加语义**：缓存命中跳过报告意味着重放期间
   CheckIssues 不再收到重复行——行级去重（cxt.rs:386）与 seen-set
   （mod.rs:4194）的行为不变，但"子模块构造器在父 elaborate 中重放"
   产生的报告现在依赖父文件轮次内的缓存命中。跨文件场景 mutable_map
   清空后缓存同步失效、子构造器重跑 → 自愈重建，与端口表同一论证，
   无新风险，但回归用例必须覆盖"父文件引用前文件模块"的组合。


---

## 11. 实现偏差清单（2026-09-27，阶段 2-4 实现实测）

以下为实现相对本设计的全部偏差，每条附原因（均为看门狗实测换来的引擎纪律或宏系统既有约束）：

1. **`_res` 改调共 4 处，非 3 处**：设计成文时 module 宏只有两个臂 + 黑盒臂；现文件还有
   Verilog-compat 臂（hdl-macros 内第 4 个 `let _res: ModuleTree = ...`）。4 处全部改调
   `checkModuleTreeAll`。
2. **Twin 引擎镜像（设计未预见）**：bump_spine_iter 孪生引擎有封闭的 `PrimId` 内建表，
   prelude 引用的每个 builtin 都必须登记。新增 `PrimId::CheckCombCycles`（prim.rs 枚举 +
   exec 臂 + entry.rs 挂载），纯算法核心提取为 cxt.rs `comb_cycle_reports`（返回报告元组，
   参考版/twin 各自推送 CheckIssues 通道）。
3. **builtin 签名从 `List[String]` 改为单 `String`**：edges 以换行拼接的单字符串传入
   （每行 `dst|src|cross|leaves`）。原因：`List` 类型在 `Cxt::new` 挂载时机不存在（同
   vconnT 注册注释），String-only 签名才能在参考版/孪生两引擎安全挂载。
4. **per-module 缓存（§3.6）取消**：实测发现 mutable 全局在 class 检查求值各轮的行为
   不一致（读在某几轮返回停滞值、第一轮的写入在后续轮不一定可见），任何全局门要么整条
   管线静默跳过（首版即如此：HDL001/010/020 全灭），要么从不命中。分析改为**每轮运行**，
   幂等性/正确性由 **nlDedup（使能规范化）+ dedupDrives（(target,rhsKey) 首见保留）+
   CheckIssues 行级去重（+ drain 侧 seen-set，阶段 1 同款）**承载（2026-09-27 评审更正：
   原文笔下的 dupFree/leafResidue 门并非防线，见 4a/4b）。性能：其余规则 O(语句 + V·E)
   每轮重跑，预算内（全量 L13_namespace 实测 527s vs 基线 ~450s，PEAK 2.6GB << 6GB；
   看门狗口径：527s 已超旧默认超时 420s，.git/watchdog.ps1 默认 `-TimeoutSec` 已上调
   **1500s**，内存红线 6GB 不变）。

   4a. **dupFree 门——冗余保险，非防线（2026-09-27 评审更正）**：round 2（第二次
   class-field 求值）确会把每条 when 包裹语句按 WhenStack 残留条件重录一份（`en` 变
   `en && en`、`!en` 变 `!en && en`），但**检测器恒真**：scanAllEx 把每条语句 key 无条件
   记入 seen（重复也记，hdl-check-graph.typort scanAllEx），seenLen 恒等于语句计数，
   `dupFree = 语句计数 == seenLen` 永远成立——leaf 规则（HDL032/033/034/035）实际**每轮
   都在运行**。真正挡住残留轮垃圾的是：nlDedup 在语句扫描时把每条使能规范化（重复叶
   key 首见保留）+ dedupDrives 按 (target,rhsKey) 保留首轮干净副本 + 行级去重兜底。
   该门保留为冗余保险，不承载正确性。

   4b. **leafResidue 标记——不可达冗余保险（2026-09-27 评审更正）**：驱动使能叶集合内
   同 key 两次（任意极性组合）即判残留的判定**恒假**：使能在进入 DriveSrc 之前已过
   nlDedup（scanStmtEx 的 EnableCtx 构造），存储的驱动从不含重复叶 key。保留为廉价
   跳线，防未来调用点漏掉 nlDedup 规范化。
5. **HDL034 检测范围缩小**：裸信号 p/!p 形态（设计 §4.5 的 `when c && !c`）与第 4 条的
   残留条件（`!en && en`）在叶层面**结构完全相同、不可区分**，为避免 latchOk/loopExempt
   类模块的必然误报，HDL034 只保留 **eq-term 同选择器异值**检测（`when (sel == 0) &&
   (sel == 1)`），并加"该选择器还出现在其它驱动的条件中 → 判为跨分支残留，跳过"的
   防误报护栏。验收用例 §9.3 deadCond 相应改为 eq 形态；附带的引擎缺口实测：表面语法
   `:=` 写在 `*Cd` 寄存器上会生成组合 assign（isRegExpr 不含 *Cd 变体，既有引擎缺口），
   该形态会被 HDL030 如实报出（实测 xorExempt 首版即触发，属真阳性）。
6. **HDL032 的轮次可见性**：leaf 规则每轮运行（dupFree 恒真，见 4a），但永不接收
   残留轮的垃圾使能——nlDedup + dedupDrives 已在源头把残留剥掉；HDL032 的 coverage
   计算同时排除 residue 驱动（同 key 双写使能，leafResidue 跳线）。
7. **验收 §9.2 crossLoop 的子模块端口必须声明在模块头**
   （`module passthru` 换行 `input pin = Bool` 再 `{`）。设计片段把端口写在 body
   内——body 内 `input/output` 是**模块内部信号，无 subSignal 句柄**（module 宏文档
   既有约束），`u.port := x` 不会形成连接、跨层边不存在。测试已按头声明形态改写。
8. **验收 §9.2 loop-exempt 的互斥必须位于环的两条不同边上**（如
   `when sel { u.pin := x }` + `when !sel { x := y }`）。原片段把互斥写在单条边条件的
   两侧（`!sel && sel`），该形态属 HDL034 的死条件语义而非环豁免（设计 §3.3 豁免本义即
   "两条边条件互斥"）。
9. **HDL034 消息为固定串** `driver condition is always false`（设计 §4.5 含具体
   `p`/`!p` 叶渲染；实现省略该拼接，contains 式断言不受影响）。
10. **21-crossclock 实测 HDL038x2、无 HDL036**（设计 §5.3 预期 HDL036x1 有误）：设计认为
    `empty = rdPtr == wrPtrSync2` 混合 outCd 与主域——实际 streamFifoCC 中 wrPtrSync2 声明
    于 outCd（hdl-crossclock.typort:201 `newUIntRegCdNamed(..., outCd)`），与 rdPtr 同域，
    不构成汇聚；`full`/`occupancy` 两侧均主域，亦无汇聚。实测输出仅 HDL038x2
    （wrPtrSync1 链 crossed to clkB、rdPtrSync1 链 crossed to clkA，宽度均 2），
    断言按实测写入（examples_21_crossclock_expected_warnings）。
11. **全部规则每轮运行**（dupFree 恒真，见 4a；正确性由 nlDedup + dedupDrives +
    行级去重承载，非轮次门控）；HDL030/031/036-039 同样每轮运行、行级去重兜底。
    因此对 leaf 规则而言"模块被创建与否"不影响结果；CDC/组合环规则对
    已创建模块在 create 轮必然覆盖。
12. **规则表 HDL034 的已知漏报更新**：裸信号 p/!p 死条件形态不再报（第 5 条）；
    eq 形态（同选择器异值，且该选择器不出现在其它驱动）仍然报出。
13. **组合环互斥豁免 per-cycle 化（2026-09-27 评审 P1 修复）**：SCC 级一票豁免对
    "互斥对不同属一条环"的真环漏报（评审探针 2 形态），改为 §3.4 修正后的
    预筛 + 逐环豁免 + 全简单环枚举（步数界 100_000 / 环数界 4096，截断回退
    "存在环"式报告）；HDL031 归因同步改为按该环自身的边判定。回归钉
    `hdl030_true_ring_survives_hold_ring_mutex`（真环+保持环共存必报
    HDL030 x→y→x）；`hdl030_loop_exempt_by_mutex` 单环互斥豁免语义不变。
14. **CDC 链识别域锚对齐 §5.1 优先级**：chainNextOf 原以 `resolveCd(x, None, …)`
    解析下一级域、忽略该级 regAssignCd 的驱动侧锚；现经 readerDriveCd 传递
    驱动显式 cd，与链头 `resolveCd(d.target, d.cd, …)` 同优先级（驱动锚 >
    声明锚 > 模块默认）。既有 CDC 用例中驱动锚与声明锚一致，行为不变。
15. **HDL039 XOR 豁免操作数序无关**：exprKey 按操作数序渲染 binary，原实现只认
    `binary(Ri, "^", R(i+1))` 一种顺序；XOR 对称，现 matcher 两个顺序都接受
    （typort 无字典序字符串比较可做键规范化，不为此扩 builtin 表）。回归钉
    `cdc_xor_edge_detect_operand_order_exempt`。
16. **已知限制（记录，不实现）**：(a) 跨文件 HDL031 盲区——跨层边依赖
    ModuleCombSummary，mutable_map 每文件清空（lib.rs 三处），父文件引用
    前文件模块时前文件模块不在父文件 elaborate 轮中重构造、摘要缺失 →
    跨层边不产 → HDL031 不触发（§3.5"摘要缺失不产边"的保守漏检在跨文件
    场景的体现）；(b) twin 引擎 `PrimId::CheckCombCycles` 臂（prim.rs）无
    独立自动化测试——纯核心 comb_cycle_reports 由参考引擎用例覆盖，twin 臂
    仅同源共享该核心，未在 twin 引擎端到端跑组合环用例。
