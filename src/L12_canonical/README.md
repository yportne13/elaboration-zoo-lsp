# L12_canonical

canonical 搜索（`canonical.rs` 的 `iddfs`/`search`，Err 重试路径专属）+
trait 求解器 Val 级重写（`typeclass.rs` 移除 `Typ` 桥接）+ `Val::Call`
（HDL regNext 泛型）。参考版全面 SmolStr 化；快版孪生
`bump_spine_iter.rs`（L11 冠军配方移植，commit `4c6552f`）。

## 已知分歧 / 刻意取舍（跨层连贯性评审登记）

- **SumCase 显示格式分层（comma + 头类型参数族）**：本章（及 L11/L13）的
  构造子值显示为 `{头}[{隐式实参}]::{分支}({显式实参 逗号连接})`，如
  `Point[Nat]::Point.mk(4, 6)`、`Vec[Bool]::cons(1, Bool::false, …)`——
  L09 起的血统格式，被本章内置测试（`mod.rs:1048/:1373/:1479/:1591/:1799`，
  test0/test2/test7/test8/test_trait、bits_adder）与 L13
  `legacy_tests.rs:604/:716` 字面锁定；与 L08 的空格 + `[名]` 隐式格式
  **分层**，不得互贴（a4-r2 曾把 L08 格式误移植 L09-L12，终门禁回滚；
  非 Sum 头的 `sum_head_name` panic 降级保留；L12 的 Nat 字面守卫臂
  `pretty_nat` 不受影响）。
- **快版孪生不移植 canonical/`iddfs`**：参考版只在 Err 路径的重试闭包
  （`elaboration.rs` 的 `ret = move || infer.iddfs(...)`）调用，不影响
  判定与 Ok 输出（`bump_spine_iter.rs:29-30` 模块头）。
- **`iddfs` 预算调度 `1, 3, 5, ...`（步进 2）**：作者 perf 调优
  （1c7e11→1c7e1aa，由初版 `*= 3` 改 `+= 2`）；调用方授予
  `target_limit = 6` 时最小预算恰为 6 的实例不会被尝试（完备性缺口
  仅此一角），改调度会改重试成功路径的合成结果字节，未盲改（a5-r1 §5）。
- **`vals_eq_ground` 把 Flex 视为等于一切**：与 `val_match` 的 Flex 宽放
  同一策略（实例匹配容忍未解实参），刻意语义（`typeclass.rs` 内注释）。
- **快版 `unify` 无 Decl 头展开燃料臂**：L12 参考版 `unify` 带 `fuel`
  （Decl 头 `quote+eval` 重试 + SumCase 重锚配额）；孪生无此机制
  （`bump_spine_iter.rs` unify_iter 头注释），`constraints`（Stuck 挂账）
  已移植。Decl 展开臂的孪生侧无对应口径，无已知触发例，登记不盲补。
- **快版孪生 `unify_sp_lockstep` 的实参位相等免比**：tag 7 与 Obj 头链
  不免比，由 (Obj, Obj) 合同臂接管判定。
- **`declb_of` 无缓存 / 参考版 `no_metas` 为 quote 版**：同 L11
  （见 L11 README；L13 同源机制 71e11ae / 指针键缓存未下沉的论证一致）。
- **宏展开深度守卫 `MAX_MACRO_EXPANSION_DEPTH = 256`**（f51a0e4，
  `parser/mod.rs:136`）。
