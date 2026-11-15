# Module 扁平化重设计 — 诊断与进展记录（归档）

> **归档说明（2026-11-15）**：本文原为分支 `perf/diag-module` 的
> `docs/module-flat-redesign-notes.md`（2026-08-04，状态"进行中，已暂停"），从未并入 master。
> 它记录了 module 扁平化尝试的指数级性能根因（1.8ⁿ）与唯一可行结构（VN），
> 经分析后归档到 master `docs/archive/`，供后续参考。
>
> **口径与现状（务必与 [module-redesign-analysis.md](../module-redesign-analysis.md) 并读）**：
>
> - 本文的指数级退化触发条件是**"语句作为独立 class items"**（前端 `ClassItem::Local` +
>   栈式 moduleBegin/moduleEnd 的 task2 路线）。该前端从未进入 master。
> - master 在 2026-09-29 状态订正后采用**宏层副作用扁平化**（`hdl-macros.typort`：
>   "side-effect chain FLATTENED into class-body fields"，每个 class-body `let` 都是 struct
>   字段；constructor 按声明序 eager 执行一次；`def tree = this._res` 读 create 时快照，不再
>   每次访问重放链；ModuleTree push 保持常量形状以免 stuck GADT 索引导致 O(n²)）。
> - [module-redesign-analysis.md](../module-redesign-analysis.md) §2.1 的 2026-08-05 复核称
>   "扁平化→35x 不复现"，但该复核只测了**字段扁平**形态，**没有**测本文的"语句作为独立
>   class items"触发条件；两份结论口径不同，不能互相证伪。
> - 若将来重新打开"成员化 + 语句作 items"的设计，必须先在当前 master 上用本文 §2.1 的
>   h7/h10 微基准（N 个信号 + N 个 `a_i := a_j`）重测；注意 master 的 FORCE_MEMO 对含 meta 的
>   walk 是 taint 的（不缓存），L07–L12 没有 FORCE_MEMO —— L07 式 carrier 设计不能免疫本文的
>   指数风险。
>
> 以下为原文（未修改；仅去掉原文一级标题）。

---

> 状态：**进行中，已暂停**。本分支（`perf/diag-module`）完成了性能根因的实证定位和部分实现，
> 但遗留若干未决问题（见 §5）。用户将先仔细测试/修复 `class` 展开实现，之后再继续本工作。

## 1. 背景与目标

用户诉求（原话要点）：
- "我在 module 里写的代码，好像不是直接装在 class 里的，被某个 let 包了一层，
  导致那些 let 都没有变为那个 class 的成员。"
- 即：`module Foo { let a = UInt[8]; ... }` 展开后，`a` 应是生成的 class（struct）的**成员**
  （`u.a` 可访问），而不是被包在 `zz_tree` 字段初始化表达式的 let 链里（master 现状）。
- 历史：`task2/module-macro` 分支曾实现"扁平 class items"方案，功能正确但 35x 性能退化，
  根因"未证实"（见 `docs/task2-module-macro-notes.md`），被搁置。

## 2. 性能根因：实证定位（已完成，结论可靠）

### 2.1 复现

在 `perf/diag-module` 分支上移植 task2 改动（`ClassItem::Local` + 栈式 moduleBegin/moduleEnd +
typed 信号 let + 扁平 module 宏）后，用最小复现（N 个信号 + N 个 `a_i := a_j` 赋值）测量：

| 结构 | n=7 | n=10 | 增长 |
|---|---|---|---|
| master（body 嵌套在 zz_tree 值内） | ~1.5s | ~1.5s | 线性 |
| task2 扁平（语句作为独立 class items） | 49s | 243s | **~1.8ⁿ 指数** |
| 扁平 + 语句 let 带类型注解（`let _s: Unit = ...`） | 63s | 293s | 指数（注解无效） |

### 2.2 定位过程

1. **计数器插桩**（`solve_trait` / `solve_multi_trait` / `unify` / `infer_expr` / `eval` / `check` /
   `force` / `quote` / `v_app` / `closure_apply`，均为临时改动）：
   - 每次 `:=` 只增加 ~13 次 `solve_trait`、meta 表只线性增长（+11/语句）——**单次调用成本爆炸**。
2. **force 按 Val 变体计数**：`Val::Sum`/`SumCase`（结构体值）的 force 次数指数爆炸：
   lets7: 27万 → assign4: 670万 → assign7: 5730万（212x）。
3. **force 调用栈采样**（debuginfo 构建）：扁平结构下 force→force 递归链 **140+ 层**
   （`Flex→type→Rigid→Flex→...` 的 meta 引用链），而嵌套结构 2 层即触底到 eval。

### 2.3 触发条件（精确隔离）

用**手写 class**（绕过宏）逐一验证结构变体（同一模块体，同一栈式 hdl-core 机制）：

| 结构（手写 class） | n=7 | n=10~15 | 信号是成员? |
|---|---|---|---|
| hybrid：全部嵌套在 zz_tree 值内 | 2.2s | 2.2s | ✗ |
| **VN：信号为 class items + 语句嵌套** | 4.9s | 9.2s@12 | **✓** |
| 扁平：信号 + 语句都是 items | 49s | 243s | ✓（但指数） |

结论：
- **触发条件是"语句作为独立 class items"**——与 moduleBegin/moduleEnd 栈机制无关（hybrid 用同一
  机制且快）、与 when 臂顺序无关、与语句 let 类型注解无关。
- 根因在 elaborator 的 force/quote 对累积结构值的反复强制（无记忆化），属于编译器深水区，
  无浅层修复。
- **VN 结构是唯一同时满足"信号成为成员"且不指数爆炸的结构**（~线性，代价 ~3-5x/模块）。

## 3. 已实现的改动（工作区当前状态，全部未提交）

分支 `perf/diag-module`（基于 master），改动文件：

### 3.1 `src/L13_namespace/parser/syntax.rs`
- `ClassItem` 新增 `Local(Span<SmolStr>, Raw)`：无类型注解的 `let x = v` = ctor 作用域局部绑定
  （不成为 struct 字段）；带注解的 `let x: T = v` 仍为 `Field`（成员）。（移植自 task2）

### 3.2 `src/L13_namespace/parser/mod.rs`
- `p_class_body_item`：无注解 let → `ClassItem::Local`（原为带 Hole 类型的 Field）。
- `expand_class_as_struct`：
  - `ClassItem::Local` 展开为 `let x: Hole = v`（ctor 链内绑定）。
  - **新增"语句下沉"（statement sinking，仅对 `impl Module` 的 class）**：
    收集首个 item（moduleBegin）之后的全部 `Stmt`/`Local` items，把它们嵌套进
    `zz_tree` 字段的值里（`let _s0 = stmt0 in let _s1 = stmt1 in ... in <zz_tree value>`）。
    信号/端口保持 class-level Fields（成员）。这是避免指数爆炸的关键结构。
  - 此改动对非 Module class 完全无影响。

### 3.3 `src/prelude/hdl/hdl-macros.typort`
- `Expr` 宏：信号/端口/寄存器声明**加类型注解**（`let a: UInt[w] = newUInt(...)` → 成为成员）；
  **删除** `$m.create` 子模块例化特例臂（实例记录改由 create 内部完成）。
- `module` 宏：body 语句直接铺开为 class items（`moduleBegin` 开帧 → 端口字段 → body →
  `zz_tree` 字段（moduleEnd + mkInstance）→ 端口 subSignal 句柄字段 → `def tree`）。
  语句下沉由 expander 透明完成，源码所见即所得。

### 3.4 `src/prelude/hdl/hdl-core.typort`
- **栈式模块机制**：`moduleBegin`/`moduleEnd` + `moduleTreePushModule`/`moduleTreePop`/
  `moduleTreeHead`/`addToCurrentModule`（替代 master 的 `_init/_ws/_prev/_creat` 内联脚手架）。
- **修复前向引用**：`headModuleDef` 移到 `moduleTreeHead` 之前（原 task2 代码顺序会
  "error name not in scope"，wt2 工作区实为不可用状态）。
- `mkInstance`：**无守卫**（记录见 §5.1——尝试过的守卫方案触发指数）。
- `createSignalExpr` 改用 `addToCurrentModule`。

### 3.5 验证数据（实现"语句下沉"后）

- 扁平宏 + 下沉：h7 = 3.3s、h10 = 3.2s（**线性**；对比未下沉 49s/243s）。
- `examples/hdl/09-hierarchy.typort` 等：0 错误、输出正常（下沉后模块体执行正确）。
- 性能绝对值：单文件 ~5s（含 prelude 1.24s），master 基线 ~1.4s —— 模块检查代价 ~3-5x。

## 4. 诊断插桩（临时，未清理）

`src/L13_namespace/{mod.rs, elaboration.rs, unification.rs}` 与 `src/lib.rs` 中留有临时插桩，
**后续必须全部移除**：
- `Infer` 字段：`c_solve_trait`/`t_solve_trait`/`c_check`/`t_check` 等计数器与耗时累计。
- `mod.rs`：`FVAR_CNT`/`force_var_counts()`、`DIAG_EVAL`/`DIAG_FORCE`/`DIAG_VAPP`/
  `DIAG_CLOSURE`/`DIAG_QUOTE` thread_local、`force`/`eval`/`v_app`/`closure_apply`/`quote`
  的 wrapper + `_impl` 拆分、`force_impl` 内的 FDEPTH 深度采样与 eprintln。
- `lib.rs`：`on_change` 末尾的 `DIAG` eprintln。
- `mod.rs` `run`/`run_with_prelude` 末尾的 `DIAG` eprintln。
- 注意：`eval` 的 thread_local 计数器是**双实例 bug**（函数内声明与读取处声明是两个独立
  static，读数恒 0），移除即可。

## 5. 遗留问题（后续工作）

### 5.1 mkInstance 守卫的指数坑（重要教训）

尝试给 `mkInstance` 加"模块帧开启才记录"守卫（防止顶层 create 在全局树留垃圾帧），
两个版本都触发指数：
1. `match depth`（Nat 匹配，`ModuleDepth` 全局）——`change_mutable_default` 的 T 类型是
   `string_to_global_type(name)`，"ModuleDepth" 不是已定义类型 → 无法统一。
2. 读回 `get_global("ModuleTree")` + `t.num` + Boolean 匹配——**单次 mkInstance 调用触发
   ~3000 万次 force**（09-hierarchy 总 force 1.7M → 3.05 亿，FDEPTH 打印 3050 万行）。

结论：**在 create 热路径里读回全局树做任何匹配/判断都会触发同样的指数链**。当前取无守卫
版本，代价是顶层 create 在全局树留下一个无引用垃圾帧（O(1)/次，`create.tree` 返回的
始终是模块自己的树，垃圾帧不进输出）。若要真正清理，需在 elaborator 层面解决
force/quote 指数问题后再说。

### 5.2 未完成事项

- [ ] 移除全部诊断插桩（§4）。
- [ ] 性能门限验证：`test_examples_hdl_dir` 全量计时（master 基线 ~16s；当前结构预计 40-80s）。
- [ ] legacy_tests 更新：`test_example_hdl_hierarchy` / `test_example_hdl_ops` /
      `test_examples_hdl_dir` 的期望串（成员化后 Verilog 输出中信号名/顺序可能变化）。
- [ ] 新增测试：body 信号成员访问（`u.a`）、无特例例化（`let u = foo.create[8]`）、
      语句下沉的 when/switch 正确性。
- [ ] examples 是否需要重写为成员风格（当前 examples 用旧语法，经 4 个 legacy 宏臂兼容）。
- [ ] 文档：`docs/hdl-redesign-plan.md` / `docs/hdl-design.md` / README 更新。
- [ ] **（用户主导）先仔细测试/修复 `expand_class_as_struct` 的 class 展开实现**，
      确认成员/下沉语义符合预期后再继续。

### 5.3 后续优化方向（如果 class 展开修复后性能仍不达标）

- 深修 elaborator：force/quote 的记忆化或 meta 链压缩，使"语句作为 items"本身变快
  （当前 VN 结构的 ~3-5x 代价可被压回 ~1.5x 以内，但风险高、周期长）。
- 或接受 VN 代价，作为已知性能特征记录。

## 6. 关键文件索引

- `docs/task2-module-macro-notes.md` — task2 前情（35x 历史、未证实根因）
- `src/L13_namespace/parser/mod.rs` `expand_class_as_struct` — 语句下沉实现（§3.2）
- `src/prelude/hdl/hdl-macros.typort` — 扁平 module 宏 + typed Expr 宏
- `src/prelude/hdl/hdl-core.typort` — 栈式 moduleBegin/moduleEnd + mkInstance
- 临时测试文件（/tmp）：`h7.typort`（扁平指数复现）、`hybrid7.typort`（嵌套对照）、
  `vn7.typort`（VN 结构）、`sn7.typort`、`tn7.typort`（typed 语句）
