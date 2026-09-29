# Bug：prelude 加载发散（FSM 一期收口时的看门狗二分全记录）

> 2026-09-27，hdl-fsm.typort（FSM 一期）收口时发现并修复。
> 状态：**hdl-fsm.typort 内的发散与解析错误已修**（修复形状见 §规避模式）；
> 修复过程中**推翻了最初"参数化 struct 字段类型"的定性**（§二分证据链 6-9），
> 真实触发面是 `create_global` 的依赖类型检查路径（§机制链）。
> 另有 workspace 级的遗留失败（HDL060-064 警告通道、`if (1)` 折叠、三处
> 深递归栈溢出），证据显示均与 hdl-fsm 内容无关（§遗留问题）。

---

## 一句话

`hdl-fsm.typort` 只要包含对 `create_global("FsmCtx", v)` 的直接调用（v 的类型
是本文件声明的 struct/enum），prelude 加载就会在**该 def 的声明检查**处
发散（无限分配，6GB 看门狗击杀）或在 unify fuel 上限处报
`can't unify expected: Unit find: Type 0`；同文件的
`match <struct字段投影>`（字段类型为 `List[...]` 这类参数化类型应用）
独立触发同款发散。二者叠加一个既有的解析错误，使得加载发散表现为
"加什么炸什么"，最初被误诊为 struct 声明本身的问题。

## 现象

- 任意测试（每个测试都全量加载 prelude）进程内存无限增长，看门狗
  （6GB 阈值，`.git/watchdog.ps1`）击杀，EXIT=42 / `KILLED_MEMORY_PEAK_GB=6.0+`；
  现场曾致整机内存耗尽重启。
- 对照峰值：健康加载 0.19-0.28GB；发散运行 6.0GB+（击杀）。

## 最初定性（已被推翻）与最小复现

最初的主控二分结论是：

```typort
struct Fsm[w: Nat] {
    stateReg: UInt[w]      // 字段类型 = 用自身 Nat 参数实例化另一个参数化类型
    stateNext: UInt[w]
    ...
}
```

"仅声明即炸，无调用点、无 impl"。**本轮二分推翻了这一归因**：该结论的
"340 行净"切点其实落在 `fsmCtxModuleReset` 函数体中间（见 §二分证据链 2），
解析器在 `Expect(EndLine)` 处放弃整个文件 → hdl-fsm 整文档被跳过 →
内存自然健康；"362/368 爆"的切点包含完整的 C 段（含真正的炸弹
`fsmCtxModuleReset`）→ 必炸。struct 本身从未被独立验证过。

## 看门狗二分证据链（2026-09-27，全部实测）

每次切点都 rebuild（include_str! 编译期内嵌）+ 看门狗运行
`fsm_out_of_module`（单测试 = 单次全量 prelude 加载）。健康签名：
`PEAK_GB≈0.19-0.28、SECS≈30-45`、失败原因为干净的 "name not in scope"；
发散签名：`KILLED_MEMORY_PEAK_GB≈6.0`。

| # | hdl-fsm.typort 内容 | 结果 |
|---|---|---|
| 1 | 完整 502 行原版（参数化 Fsm[w]/FsmSt[w]） | **爆** 6.07GB |
| 2 | 主控切点 340 行（落在 fsmCtxModuleReset 体中间） | "净" 0.22GB —— **假象**：解析中止，hdl-fsm 整文档未加载 |
| 3 | 主控切点 362/368 行（含 struct Fsm[w]） | 爆 —— 归因错误（见 #6/#9，该切点含 C 段真炸弹） |
| 4 | 扁平化 struct Fsm/FsmSt（Expr 字段）+ 完整 C 段 + 原重置体 | 爆 6.05GB |
| 5 | 仅 `struct FsmZzz { name: String }` + 完整 C 段 | 爆 6.01GB（struct 形状无关） |
| 6 | **C 段完整（含原版 fsmCtxModuleReset），无任何 struct** | **爆 6.05GB —— 结构体彻底洗清，炸弹在 C 段内** |
| 7 | C 段到 fsmCtxDrainAll 为止（无 fsmCtxModuleReset） | 净 0.27GB → **炸弹 = fsmCtxModuleReset 体** |
| 8 | 重置体 = `unit`（平凡体） | 净 0.27GB → **体内容是触发面** |
| 9 | 体 = `match ctx.fsms {..}`（List 投影匹配，无 create_global） | 爆 6.01GB → **List 投影匹配独立发散** |
| 10 | 体 = 无匹配的无条件 drain + `create_global("FsmCtx", fsmCtxEmpty)` | 不再发散，但报 `can't unify expected: Unit find: Type 0`（fuel 上限把发散变成错误） |
| 11 | 体 = drain + `change_mutable_default("FsmCtx", x => fsmCtxEmpty, fsmCtxEmpty)` | **净 0.26GB，hdl_stream_fix_tests 11/11 绿** |

最小复现（6 行，把 hdl-fsm.typort 整文件换成以下内容即可复现 #10 的
can't-unify；struct/enum/List 字段三种变体全部同样失败，与字段形状无关）：

```typort
struct FsmCtx {
    fsms: List[Nat]
}
def fsmCtxEmpty: FsmCtx = FsmCtx.mk(lnil)
def fsmCtxModuleReset(): Unit = create_global("FsmCtx", fsmCtxEmpty)
```

报错原文：`can't unify expected: Unit find: Type 0 @ 25:148`
（path 25 = hdl-fsm 文档；148 = create_global 调用处）。

## 机制链（供主线排查）

1. **parse 层（既有问题，已在本文件修掉）**：`fsmGotoLog` 尾部的裸
   `match nat_is_ground(target) { ... };` —— 裸 match 语句后的 `;`
   触发 `Expect(EndLine)`（parser 对"表达式语句后跟分号"不接受）。
   解析错误使**整个文档被跳过**（加载继续、不报发散）——这是把整个
   二分搅成迷雾的根源。修复：`let _ = match ... { ... };`（语义等价）。
2. **发散层**：`create_global(K, v)` 的第二参数类型是依赖类型
   `string_to_global_type K`（cxt.rs:685-691 注册），check 期对
   `Tm::Decl(K)` 做 eval 并与实参类型 unify。当 K 指向本文件声明的
   类型、且调用位于 def 体顶层时，该 unify 不收敛：预 fuel 时代表现为
   无限 meta 生成（6GB 发散），`UNIFY_FUEL=4096` 在场时表现为
   `can't unify expected: Unit find: Type 0`。
3. **同族发散**：对 `get_global_default` 结果的**字段投影做 match**
   （`match ctx.fsms`，字段类型为 `List[FsmRec]`）同样发散；对普通
   enum 投影（`ctx.stack`）和对普通实参（哪怕 List 类型）的 match 均正常。
4. **lvl2ix 层**：把重置体重写成任何"匹配式"形状后，load 的 decl check
   （`check_pm_final → unify_pm → quote`）在引用该 def 的
   hdl-macros 模块 prologue 检查路径上 panic
   `lvl2ix: level 1 is out of scope for a context of level 1`。
   存活形状：**体内完全无 match**（见 §规避模式）。
5. **对照**：hdl-core 的 `initWhenStack`（`create_global("WhenStack",
   whenStackEmpty)`，enum 全局）一直正常——同款调用对 enum 全局 +
   let 绑定形状在 hdl-core 文件内可用，但同形状搬到 hdl-fsm 仍失败，
   说明还有未定界的文件/声明序敏感因素，留给主线（见 §遗留问题）。

## 规避模式（本次采用，已验证）

`fsmCtxModuleReset` 体**完全避开 match 与 create_global**：

```typort
def fsmCtxModuleReset(): Unit =
    let ctx = get_global_default("FsmCtx", fsmCtxEmpty);   // 纯读、不写 map（check 期安全）
    let _ = fsmCtxDrainAll(ctx.fsms);                      // 空表 drain = no-op
    let _ = change_mutable_default("FsmCtx", x => fsmCtxEmpty, fsmCtxEmpty);
    unit
```

- `change_mutable_default` / `get_global_default` / 投影作**实参**的
  def 调用，均为 C 段既有形状（fsmCtxRegister / fsmGotoLog 等），
  check 干净。
- 语义与原"非空才 drain+reset"等价：空表 drain 是 no-op，对空上下文
  reset 也是 no-op；唯一差异是 key 可能以**闭包安全的 ground 空值**
  存在于 cached map（原纪律是为避免残留 stuck 值，空构造值无悬空引用）。
- 结构体按任务 A 决策扁平化：`Fsm { stateReg: Expr, stateNext: Expr,
  stateCount: Nat, width: Nat, name: String }`、`FsmSt { sm: Fsm, idx: Nat }`，
  并补 `impl[width: Nat] Into[UInt[width]] for Expr` 恢复
  `st := ctrl.stateReg` 赋值路径（同 `Into[UInt[width]] for Nat` 先例，
  实测加载干净）。

**future（未测，勿断言）**：`struct Wrap[w] { xs: Vec[Nat] w }` 这类
"字段类型直接以参数实例化参数化类型"的形状本轮**未测**——参数化
struct + 非依赖字段的先例（Bits/EnumCraft/UInt）与本轮扁平化结果都正常，
但依赖字段路径没有独立实验数据。

## 遗留问题（证据显示与 hdl-fsm 内容无关，未修）

修复后以最终 hdl-fsm（546 行）跑看门狗协议：`hdl_stream_fix_tests`
11/11 绿（峰值 0.26GB）；全量 `L13_namespace`（跳过 3 个崩溃测试）
413 过 / 36 败。36 个失败的归属：

- `hdl_blackbox_tests` × 11：BlackBox agent 在补，任务书预期内。
- 警告通道全灭（HDL060-064 / HDL010 / HDL001-003 等全部不出现）：
  **非 FSM 的 `test_hdl_check_multi_driver`（HDL010）同样失败**，且换
  平凡重置体复测 hdl060 仍失败——report_check_issue → CheckIssues →
  per-decl drain 管道在当前工作区状态下游全局失效（涉及 hdl-check /
  hdl-verilog / mod.rs，均在他人所有权内）。
  （追记 2026-09-29：警告通道已随 `c42719a`（HDL 自检阶段 2-4）恢复——
  hdl_check_graph_tests 的 HDL030-039 断言全绿，全量 `cargo test`
  67 个测试目标通过（docs/review-2026-09-29.md §三）。上段为
  2026-09-27 在途工作区的快照，非 master 现状。）
- `fsm_acceptance_demo_verilog` 的 `if (1)` 默认驱动折叠断言：codegen
  属 hdl-verilog.typort（他人所有权）。
- `fsm_method_lambda_form` 的 `find unsolved meta with type 'Type 0'`：
  lambda 形式 + class 检查，for-hdl-blocker 同族，与重置体无关
  （平凡体重置下同样失败），归因待主线。
- 三处深递归栈溢出（`bump_spine_iter::observe` × 2、
  `verilog_compat_tests::m2_case_comb_default`）：**stub 化 hdl-fsm 后
  仍溢出**，与本文件无关。

## 相关文件

- `src/prelude/hdl/hdl-fsm.typort` — 修复落点（fsmGotoLog 解析修复、
  fsmCtxModuleReset 重写、扁平化 struct、Into 桥）
- `src/L13_namespace/cxt.rs:685-726` — create_global / change_mutable_default
  的依赖类型注册（机制链 2 的现场）
- `src/L13_namespace/mod.rs:1098-1112` — lvl2ix panic 点；`:4173` —
  take_check_issues（警告通道）
- `.git/watchdog.ps1` — 看门狗（6GB/420s 阈值）；`.git/hdl-fsm-*.typort` —
  二分过程的各阶段快照
- `docs/l13-typeclass-instance-nat-param-bug.md`、
  `docs/for-hdl-blocker.md` — 同族（悬挂 elaboration-time 变量 / 依赖 meta）
