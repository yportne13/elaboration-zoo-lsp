# Module 重新设计：body 直接装在 class 里（信号 let 成为成员）

## 目标（你的核心诉求）
- module body 的代码直接作为 class 的 items，不再被 `zz_tree` 的 let 链"包一层"
- body 里的 `let a = UInt[8]` / `input` / `reg` 成为 **class 成员**（struct 字段），`u.a` 可访问
- 性能不回归（当前基线：`test_examples_hdl_dir` release ~16s）

## 阶段 1：性能根因实证定位（前置，必须）
task2（wt2 worktree 在磁盘上，改动可读）已实现完整扁平结构且**功能正确**，唯一 blocker 是 35x 性能，根因"未证实"。步骤：
1. 在 scratch 分支把 wt2 的改动（parser `ClassItem::Local`、hdl-core 栈式 moduleBegin/moduleEnd、hdl-macros typed let 化 + 删除特例臂）移植到 master
2. 用笔记中的最小复现（单 elsewhen 模块）做 release 计时：master 基线 vs 扁平版
3. 结构性二分定位（每个假设一个变体，逐一测量）：
   - H1 双跑：用文件 I/O 探针数出 body 在 def-check/create 各执行几次
   - H2 moduleBegin/moduleEnd 是 def 而非内联 scaffold（def 的 body 在自身 def-check 时也会跑）
   - H3 信号 typed let（Field）vs 无注解（Local）——typed 是否触发额外求值/元变量
   - H4 when 臂发射顺序（task2 改成了 otherwise 先发）
   - H5 顶层 create 的 `mkInstance` 无深度守卫 → 残留全局树积累垃圾帧（task2 已知缺守卫）
   - H6 扁平化本身（把 body 重新嵌套进单表达式，仅保留"信号是成员"）
4. 锁定根因后，在正确层面修复：
   - 若为编译器求值机制（elaboration.rs:543-549 对每个 let 值无差别 `eval`）→ 编译器层修复（候选：已知类型且非依赖的绑定跳过 def-check 值求值；或延迟求值），改动限于 elaboration.rs 且用现有测试套件验证
   - 若为宏结构触发 → 调整宏展开
   - 无论哪种，补性能回归断言（测试耗时门限）

## 阶段 2：module 宏重新设计（扁平化）
以 wt2 已验证的机制为基础：
1. **parser**：合入 `ClassItem::Local`（无类型注解的 `let x = v` = ctor 局部绑定，不成为 struct 字段；带注解的 = 成员）——task2 已实现，直接移植
2. **Expr 宏**：信号声明加类型注解 → `let a = UInt[8]` 在 class 里展开为 `let a: UInt[8] = newUInt(...)` → **成为 class 成员**；`reg`/`input`/`output` 同理；删除 `$m.create` 特例臂（generic let 覆盖）
3. **module 宏**新展开（body 直接铺开为 class items，无包裹）：
   ```
   class Foo[w: Nat] impl Module {
       let _zz_open = moduleBegin(stringify Foo, defaultClockDomain)   // Local：开帧
       let a: UInt[w] = UInt.mk(Some("a"), createPortExpr(...))       // 端口自身信号（成员）
       <body 全部语句直接展开——信号 let 成成员，赋值/when/switch 为 Stmt>
       let zz_tree: ModuleTree = <moduleEnd + mkInstance(bn.name, name)>  // 关帧+实例记录
       let a: UInt[w] = UInt.mk(None, subSignal(bn.name, "a"))        // 端口句柄（u.a 层次访问）
       def tree: ModuleTree = this.zz_tree
   }
   ```
4. **hdl-core**：栈式 `moduleBegin/moduleEnd`（wt2 版本）+ `mkInstance` 加模块深度守卫（修复顶层 create 垃圾积累，H5 预防）
5. **正确性边界**（文档写明）：端口有 own+handle 双绑定，`u.a := sig` 层次连接可用；body 内部信号是自身信号成员（`u.x` 可读），跨层赋值语义受限——不在本期扩展
6. **验证**：examples/hdl 全量重跑 + legacy_tests 全量 + 新测试（成员访问、无特例例化、深度守卫）+ 性能对比（16s 基线门限）

## 阶段 3：文档
- docs/hdl-redesign-plan.md 更新（扁平结构设计 + 性能根因记录）
- README/README.zh module 示例更新

## 风险与对策
- **阶段 1 若证实需编译器改动**：改动最小化（单点：let 值求值时机），靠现有 test 套件（L13 lib tests + examples）回归，风险可控
- **若扁平结构即使修复后仍无法达标**：回退到"hybrid"——body 信号在 source 上扁平，但宏内部用单表达式（master 已知安全结构）+ 编译器求值修复，二者取性能达标者；并向你报告实测数据再定
- 不做 io Bundle 重构（你对它的方向没兴趣）、不动 hdl-verilog 生成器（unless 诊断需要）