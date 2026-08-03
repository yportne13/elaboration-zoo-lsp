# Task 2: 模块宏重构 — 经验与教训（未完成，搁置）

> 状态：**未合并**。方案方向正确、功能验证通过，但存在严重性能退化与 debug 栈溢出，
> 根因指向编译器"let 绑定 prim 调用在 def-check 时被急切求值"的行为，需要专项攻关。
> 改动保留在分支 `task2/module-macro`（worktree `elaboration-zoo-lsp-wt2`）。

## 1. 用户诉求

1. **不要为"子模块例化"做特殊宏分支**：原 `Expr` 宏有一个专门分支
   `(let $x:ident = $m:ident . create $( [$w: raw] )* ) => { ...; let _zz_inst = mkInstance(...); }`
   处理 `let u = myAdder.create[8]`。用户认为这种特例不可接受。
2. **信号 let 应铺开在 class 层次**：模块宏展开后，模块 body 里的信号创建
   （`let a = UInt[8]` 等）被嵌套在 `zz_tree` 字段的超长 let 链
   （`_init/_ws/_prev/_creat` 脚手架）里，用户觉得"被包住了"，希望扁平铺开。
3. 用户自述"反正这部分很怪你仔细弄弄"——给了较大自由度。

## 2. 方案（已实现，功能正确）

### 2.1 class 展开：`ClassItem::Local`（parser 层）
`src/L13_namespace/parser/syntax.rs` + `parser/mod.rs`：

- `ClassItem` 新增 `Local(Span<SmolStr>, Raw)`：**无类型注解**的 `let x = v` 在 class body 里
  是构造函数作用域内的局部绑定（按声明顺序求值、对后续项可见），**不是 struct 字段**。
- **有类型注解**的 `let x: T = v` 仍是 `ClassItem::Field`（struct 字段）。
- `expand_class_as_struct`：Local 展开为 ctor 里的嵌套 let。

动机：无注解 let 的值类型在 parse 期未知（子模块实例、任意表达式、when/switch 脚手架），
若当字段处理会毒化 struct 字段列表（unsolved metas）。

### 2.2 Expr 宏：信号声明加类型注解
`src/prelude/hdl/hdl-macros.typort`：

```typort
// 旧：let $x = newUInt(stringify $x, $width);          → 无注解 → Local
// 新：let $x: UInt[$width] = newUInt(stringify $x, $width);  → 有注解 → class 字段
```

input/output/reg 同理。**删除了子模块例化特例分支**（`$m.create` 分支），统一走 generic let。

### 2.3 module 宏：栈式模块树（hdl-core.typort + hdl-macros.typort）
- `moduleBegin(name, cd)`：push 新 ModuleDef 到全局 ModuleTree 栈头 + 重置 WhenStack
  （替代旧的 `change_mutable_default`/`_prev`/`_restore` 脚手架链）。
- `moduleEnd(unit)`：pop 栈头，返回刚关闭模块的树。
- 模块宏展开为：
  ```
  let _zz_open = moduleBegin(name, cd);   // class body 第一项
  <端口字段> <body 项（信号字段/局部）>
  let zz_tree: ModuleTree = let _zz_tree = moduleEnd(unit); let _zz_inst = mkInstance(bn.name, name); _zz_tree;
  <subSignal 句柄字段>
  ```
- **子模块例化**：`mkInstance(bn.name, name)` 在 create 末尾执行——此时子模块树已
  pop，实例记录到**父模块**树——`let u = myAdder.create[8]` 自动记录
  `instance("u", "myAdder")`，无需调用点特例分支。顶层（空栈）时实例被丢弃。

### 2.4 验证通过的部分
- 所有 examples/hdl/*.typort 通过 `typort check`（release），包括：
  - 09-hierarchy 的子模块例化（`myAdder u ();`、`u.a := sig` 层次化连接、allModulesVL）
  - 07-registers、08-control-flow、10-bundle 等
- 子模块例化在删除特例分支后行为不变。

## 3. 致命问题：性能退化 + debug 栈溢出

| 指标 | master（旧宏） | task2 分支（新宏） |
|------|---------------|-------------------|
| `test_examples_hdl_dir`（release） | ~16s | **~572s（35x）** |
| 08-control-flow（when/elsewhen）| 2s | 23s（11x） |
| 09-hierarchy（嵌套模块） | 1s | 11s |
| 单 elsewhen 模块（最小用例） | 1s | 5s |
| `cargo test --lib "L13"`（debug） | 正常 | **STATUS_STACK_OVERFLOW** |

- 最小实验定位：简单模块/多模块/嵌套模块都正常（1-2s）；**when/elsewhen/switch 结构**慢 4-5 倍，
  多模块组合后进一步恶化。
- release 下 CLI check 单文件也慢（08: 23s vs 2s），排除测试框架因素。

## 4. 根因分析（未完全证实，指向以下机制）

1. **def-check 时的急切求值**：agent 在代码注释中自己确认了编译器行为——
   "the checker evaluates let-bound prim calls at def-check time"。
   新宏把模块 body 的副作用（`moduleBegin`/`moduleEnd`/信号创建/`whenBegin` 等 prim 调用）
   从"zz_tree 字段内的嵌套 let 链"改成"class body 的多个独立字段/局部"，
   导致这些副作用在 **def-check 阶段被额外求值**（旧宏因嵌套 let 结构求值次数不同）。
2. **重复执行**：模块 body 在 def-check 与 create 调用时都可能执行 → 全局 ModuleTree
   /WhenStack 状态被多次推进 → 数据积累 → 后续遍历（change_mutable 的 O(n)）变慢。
3. **debug 栈溢出**：深层嵌套 let / 递归求值在 debug（无优化）下栈深增加 → 溢出。

关键疑点代码（task2 分支的注释原文）：
```typort
// NOTE: change_mutable_default first — the checker evaluates let-bound prim
// calls at def-check time, so get_global must never see a missing key.
// NOTE: `succ t.num`, not `t.num + 1` — `+` doesn't normalize on rigid Nats.
// The dummy Unit parameter matters: zero-arg defs are eagerly evaluated at
// def-check time, so a side-effecting thunk must be applied explicitly
// (`moduleEnd(unit)`) to re-run at instance-creation time.
```

## 5. 后续建议（若继续）

1. **先弄清 class 字段的求值时机**：class 展开生成的 struct 字段值、ctor 里的局部绑定，
   分别在 def-check / create 调用时各求值几次？用 debug 打印或最小实验确认。
2. **目标**：让模块 body 的副作用**只在 create 调用时执行一次**——
   若 def-check 的求值不可避免，考虑把副作用包进"惰性 thunk"（如 `moduleEnd(unit)` 模式），
   或调整 class 展开使字段值不被 check 求值（如字段类型已知时跳过值求值）。
3. **性能回归测试**：恢复后补一个 `test_examples_hdl_dir` 的耗时断言（或至少手动对比
   08-control-flow 的 CLI 耗时），防止再犯。
4. 方案其余部分（Local/Field 语义、Expr 宏加注解、mkInstance 末尾记录）已被证明正确，
   可在修复求值时机后复用。

## 6. 已保留的资产

- 分支 `task2/module-macro`（worktree `elaboration-zoo-lsp-wt2`）：完整改动未提交
  （agent 异常退出前的工作区状态：5 个文件 + 若干 scratch 测试文件已清理）。
- 若需继续，从该 worktree 的工作区状态续接（`git diff` 可见全部改动）。
