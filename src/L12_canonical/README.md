# L12：canonical 层（trait 求解 Val 级重写 + Call 节点）

本层按“每章 = 上一章实现思路 + 本章新特性”重建（2026-11-17）：实现上
**直接承接新 L11**——decl 表名字世界、`Rc<Val>` 内的值表示、σ 显式替换、
逐臂 match、P1–P11、Type N 宇宙、trait/typeclass、macro_rules、可变全局/
文件 IO builtin、层内 `tests.rs`、bump 孪生——只叠加本章增量：**trait 求解器
Val 级重写**（去掉 L10/L11 的 `Typ` 桥接）与 **`Tm::Call`/`Val::Call` 内联
节点基础设施**。

## 1. Val 级 trait 求解（本章主体）

- `typeclass.rs` 移除 `Typ` 世界：`Assertion { name: String, arguments: Vec<Val> }`、
  `Instance { assertion, dependencies, lvl }`；实例匹配直接对 `Val` 做**单向
  一阶匹配** `val_match`（只有实例侧裸 `Rigid` 可绑定；目标侧泛型 rigid 不得
  被实例构造子吃掉），相等性用 `vals_eq_ground`。
- 求解器仍是表驱动 Prolog（`Synth`：generator/resume 栈 + 断言表 + 答案缓存）；
  本次保留 L11 的 `class_instances: FxHashMap<String, Vec<Instance>>` +
  `assertion_table: Vec<(Assertion, TableEntry)>`（旧 L12 的 Vec 形态）。
- 参考版接口：`solve_trait` 把 trait Sum 的非 out 位实参 `force_deep` 后直接
  作为 Val 断言（任一仍为 `Flex` 则推迟）；`ImplDecl` 登记实例时实参也是 Val；
  `trait_wrap` 用 Val 断言 + `Flex(MetaVar(u32::MAX))` 通配实参。
- 孪生：新增 `v_to_val`（打包值 V 深解码成参考 Val，非构造子形态降级为永不匹配
  标记），断言边界转成 Val 后交**同一 Synth**——与旧 L12 孪生的 `v_to_ref_val`
  同款口径；`solve_multi_trait_ref` 的 unify 后宽松推进 + Def 臂严格求解不变。
- trait 身份仍按 decl 名在 `trait_out_param` 判形（不新增 `is_trait` 变体，
  沿用 L10/L11 重建口径）。

## 2. Call 内联节点（基础设施）

- `Tm::Call(名, 显示实参, 值实参, 体)` / `Val::Call(名, 实参值, 体)`：值层透明
  外衣——`force` 推进体、`v_app` 穿透、`quote`/`rename` 还原调用形态、`unify`
  只比体；`pretty` 在体是卡住 match 时打印 `名(显示实参…)`，否则打印体。
- **自动创建已停用（本链口径）**：旧 L12 的 quote 会按模式形状反查同名 def
  把卡住 match 包成 `Tm::Call` 显示外衣，而旧 L12 孪生没有 Call。本链孪生同样
  无 Call，自动包会造成 ref/twin 显示分叉（实测 5 个 parity/金标准用例失败），
  故 Call 只保留节点与透明语义（供 L13 产品层使用），quote 不自动创建；
  `lookup_function_by_cases` 辅助保留为 API。

## 3. 未继承的旧 L12 增量（偏差登记）

- **canonical 搜索（`canonical.rs` 的 iddfs/search）不移植**：旧 L12 只在 Err
  路径的重试闭包（`Error` 携带 `retry: Box<dyn Fn()->Option<String>>`）里调用；
  新链（L08 血统）没有 retry-closure 错误基础设施，`run`/`run_fast` 从不经此
  路径，故本轮以“无消费点”为理由不移植（旧 L12 孪生同样不含 canonical）。
- **SmolStr 化不采用**：参考版保持 `String` 名字（L09–L12 重建链的统一表示）；
  SmolStr 是参考版内部表示优化，不改变语言行为，留待全链统一治理。
- **算符方法/中缀 desugar 不继承**：旧 L12 的 `def +`、`x + y` 依赖旧 L11
  parser 的手写优先级/中缀面（属于旧血统偷带面，本链 L11 重建时未继承）；
  本章已用命名方法（`x.add y`）覆盖 trait 求解语义。
- **`Cxt.namespace` inherent 方法分发不继承**：旧 L11/L12 血统的面，新链未承接；
  trait 方法分发（trait_wrap）不受影响。

## 4. 测试

- `cargo test --release --lib L12_canonical::`：**88**（L11 套件继承）。
- `cargo test --release --test l12_fast_parity`：**136**（L11 双 oracle 套件
  继承 + 3 个 Val 级 trait parity：ToString 投影 / 毛毯 Say / outParam Add）。
- `cargo test --release --test l12_blackbox`：**67 + 1 ignored**（L11 黑盒基线
  含 5 个 trait 用例）。
- 跨层门禁（含 L12）：`gadt_refine_cross_layer_tests` 265、
  `prim_identity_cross_layer` 258、`implicit_comma_args` 521、
  `audit_crosslayer_probe` 258、`backport3_pretty_l0910` 174，全绿。
- 基准自检：`l12bench --workload all`（church/natadd/strchain/match/enum/
  struct/traitchain/universe/macro）参考版↔孪生互检通过；`realbench --layer L12`
  common 语料 pass=6。

## 5. 参考资料

- `../L11_macro/README.md`：本层核心机（含宏）的全部出处；
- 旧 L12 文档在 git 标签 `pre-rearch-20261117` 可查。

## 增补（2026-11-25）：继承 L11 观察面（三方合并 + Call 适配）

以 "上一章完整继承" 口径补齐继承面（`observe.rs` / `prof` / 新 `run_surface_impl` 管线）：

- 三方合并（base = 旧链 L11、ours = 新 L11、theirs = 本层），32/35 文件零冲突；
- 新增 `observe.rs`，并为本章新特性 `Tm::Call` **补一个走查臂**（`tm_has_unsolved_meta` 必须覆盖新变体）；
- `use` 去掉 `typeclass::Typ`（本章已用 Val 级求解替换 Typ 桥接）；
- `L11_DEBUG_ON`/`L11_LOOP` → `L12_*`；crate 路径改 `L12_canonical`。

账本：identical 835→**866**；8 项非孪生 missing 全部是本章**主动替换**的 Typ 桥接设施
（`to_typ`/`match_typ`/`apply_subst_to_*`/`Typ`/`Subst`/`Val`），按 D1 记为 Replaced。
门禁：lib 88、l12_blackbox 67+1 ignored、l12_lsp_surface 91，全绿。
对账见 `docs/inheritance/L12-triage.md`。
