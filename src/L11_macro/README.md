# L11_macro

宏（`macro_rules` / 展开信息记录）+ decl 表世界（`Val::Decl` 名字键全局，
无 L09/L10 的 `1919810` 数值哨兵——后者在本层的同源位置不复存在，属
架构演进而非缺口）。参考版 `mod.rs` + 分文件实现；快版孪生
`bump_spine_iter.rs`（L10 冠军配方移植，commit `5cae365`）。

## 已知分歧 / 刻意取舍（跨层连贯性评审登记）

- **SumCase 显示格式分层（comma + 头类型参数族）**：本章（及 L12/L13）的
  构造子值显示为 `{头}[{隐式实参}]::{分支}({显式实参 逗号连接})`，如
  `Point[Nat]::Point.mk(4, 6)`、`Vec[Bool]::cons(1, Bool::false, …)`——
  L09 起的血统格式，被本章内置测试（`mod.rs` test0/test2/test7/test8/
  test_trait、bits_adder）与 L13 `legacy_tests.rs:604/:716` 字面锁定；
  与 L08 的空格 + `[名]` 隐式格式**分层**，不得互贴（a4-r2 曾把 L08 格式
  误移植 L09-L12，终门禁回滚；`sum_head_name` 的非 Sum 头 panic 降级
  保留）。
- **快版孪生 `unify_sp_lockstep` 的实参位相等免比**：tag 7 与 Obj 头链
  不免比（字面量与卡住投影交回完整分派），由 (Obj, Obj) 合同臂接管判定。
- **`declb_of` 每次整表重建、无缓存**：L13 twin（`bump_spine_iter.rs:3226`）
  同构；指针键缓存可行（`Decls` 是 Rc 地址稳定）但与快版 bump 每轮
  `reset()` 的生命周期耦合（缓存持有 bump 指针），热点仅定理证明负载，
  2026-09 评审判定暂不做（a5-r1 §5）。
- **参考版 `no_metas` 为 quote 版**（已解 meta quote 后续查、无 visited
  set）：L13 的值图遍历 + 指针去重（71e11ae，`mod.rs:519-565`）未下沉；
  触发类（模块/bundle 链巨型解图）为 L13-only，本层无已知触发例。
- **无 unify/force fuel**：参考版与快版一致无燃料（快版
  `bump_spine_iter.rs` 头注释"无燃料（参考版无 fuel）"，对 L11 而言
  属实；注意 L12 参考版已带 fuel，见 L12 README）。
- **宏展开深度守卫 `MAX_MACRO_EXPANSION_DEPTH = 256`**（f51a0e4，
  `parser/mod.rs:134`）：自递归宏超限给解析错误，替代栈溢出。
