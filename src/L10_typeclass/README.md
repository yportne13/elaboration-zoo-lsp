# L10：trait / typeclass 实例求解

本层按“每章 = 上一章实现思路 + 本章新特性”重建（2026-11-17）：实现上
**直接承接新 L09**——L08 血统的 decl 表名字世界、`Rc<Val>`、σ 显式替换、
逐臂 match、P1–P11 加固、`Type N` 分层宇宙、可变全局/文件 IO builtin、
层内 `tests.rs`、bump 孪生 `bump_spine_iter`——只叠加 trait/typeclass：
`trait`/`impl` 声明、接收者方法脱糖、`outParam`、实例表 Prolog 求解。
旧 L10（旧 L09 全局表血统）的 `Infer.global`/`1919810` 哨兵、`Val::Sum`
的 `is_trait` 标记、comma 显示与恢复式 parser 均不再保留。

## 1. 语言特性

```text
enum Nat { zero  succ(x: Nat) }

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this { case true => "true"  case false => "false" }
}

def t[T][s: ToString[T]](x: T): String = s.to_string x
println (t true)

trait Add[T, O: outParam(Type 0)] {
    def add(that: T): O
}
impl Add[Nat, Nat] for Nat {
    def add(that: Nat): Nat = nat_add_helper this that
}
def four = two.add two
```

- **`trait` 声明** = 单构造子 enum（构造子 `{Trait}.mk`）：第一个隐式参数是
  `Self`，每个方法签名成为构造子字段（`this: Self` 显式接收者 + 方法参数）；
  方法只有签名、没有体。
- **`impl` 声明**：`impl Trait for T { ... }` 与 inherent `impl T { ... }`
  （后者先补建合成 trait）。方法体登记为实例（`Synth` 实例表），并按实例
  类型合成一个构造 trait 值的 def（`ImplDecl` 臂）。
- **接收者方法调用**：`x.foo y` 在字段投影失败后由 `trait_wrap` 扫 trait
  方法表、以 `(接收者类型, Any×out位)` 构造断言试解；命中后拼 Let 包裹的
  「实例参数应用」项。
- **`outParam`**：trait 参数可标 `outParam(Type 0)`；out 位不参与实例查找
  （断言里填 `Typ::Any`，求解前按掩码过滤）。
- **毛毯实例** `impl[T] Say for T` 与泛型实例 `impl[T] List[T]` 均支持；
  实例匹配是**单向一阶匹配**（只有实例断言侧 `Typ::Var` 可绑定）。
- 其余语言面（enum/GADT/依赖 match/struct/new/投影链/Universes/builtin）
  全部继承自 L09。

## 2. 实现结构（相对 L09 的增量）

- `typeclass.rs`：`Typ` 世界 + 表驱动 Prolog `Synth`（`generator_stack` /
  `assertion_table` / `waiter`），`match_typ` 单向一阶匹配，`impl_trait_for`
  登记实例。参考版与孪生**共用同一求解器**（`typeclass.rs` 是共同模块）。
- `Infer` 三张表：`trait_solver: Synth`、`trait_definition`（参数表 + out 掩码
  + 方法表）、`trait_out_param`（名字 → out 掩码）。trait 与 enum 共用
  `Val::Sum`/`Tm::Sum` 表示，**不新增 `is_trait` 变体**：trait 身份按 decl 名
  在 `trait_out_param` 里判形。
- `fresh_meta`：期望类型 force 后是 trait Sum → 先尝试即时实例合成；无实例
  则挂**未解 meta 且不走 pruning**，等 def 体检查完的 `solve_multi_trait`
  统一求解/报错。
- `solve_multi_trait` / `solve_trait`：扫描未解 meta，按 `trait_out_param`
  过滤 out 位、经 `force_deep().to_typ()` 转 `Assertion` 交 `Synth`；命中后
  `infer_expr(Raw::Var(实例名))` 把实例名解析回值世界并与期望 trait Sum 合一。
  失败原因旁存（`UnifyError` 无字段），Def 臂转成可恢复 `Error`。
- `trait_wrap`：`Raw::Obj` 投影失败的回退路径（无同名 trait 方法时保留原
  `has no field` / `cannot project field` 错误；有方法无实例报 `has no object`）。
- 孪生镜像：`Machine.tstate`（每轮重建）、`val_to_typ`、`solve_trait_ref`、
  `solve_multi_trait_ref`（unify 成功后的**宽松推进** + Def 臂**严格求解**）、
  `infer_decl` 的 `TraitDecl`/`ImplDecl` 臂、`trait_wrap` 与投影回退。

## 3. 测试

- `cargo test --release --lib L10_typeclass::`：**86**（L09 `tests.rs` 继承 +
  3 个 trait 冒烟：ToString 投影 / 毛毯 Say / outParam Add）。
- `cargo test --release --test l10_fast_parity`：**128**（L09 双 oracle 套件
  继承 + 4 个 trait parity：ToString 投影、毛毯 Say、outParam Add、失败可恢复）。
- `cargo test --release --test l10_blackbox`：**65 + 1 ignored**（L09 黑盒基线
  + 5 个 trait 用例：ToString / Say / outParam Add / 未声明 trait / 无实例可恢复）。
- 跨层门禁（含 L10）：`gadt_refine_cross_layer_tests` 210、
  `prim_identity_cross_layer` 203、`implicit_comma_args` 413、
  `audit_crosslayer_probe` 203、`backport3_pretty_l0910` 174，全绿。
- 基准自检：`l10bench --workload all` 七类负载（含 traitchain）参考版↔孪生
  节点数互检通过；`realbench --layer L10` common 语料 pass=6。

## 4. 已知限制 / 与旧 L10 的差异

- 解析错误契约、显示形态、`Type N` 宇宙、builtin 注册表等按新 L09 继承
  （旧 L10 的 comma 显示与恢复式 parser 不再保留）。
- `Synth` 的 `effort ≤ 1000` 护栏失败形态仍是 panic（旧 L10 的既有已知缺陷，
  本轮未改；实例搜索的失控类护栏后续章节可统一治理）。
- 旧 L10 孪生的 solve 探针（`L10SOLVE_PROBE`）/temp-infer 快照换入换出未移植：
  新孪生用 `tstate` 每轮重建 + unify 后宽松扫描，语义对齐参考版。
- `force_deep` 只展开 Sum/SumCase/Obj 的结构槽（与参考版一致）；trait 求解的
  细粒度性能优化（实例表按 trait 分桶缓存等）留待后续。

## 5. 参考资料

- `../L09_mltt/README.md`：本层核心机（含 `Type N` 宇宙）的全部出处；
- 旧 L10 文档在 git 标签 `pre-rearch-20261117` 可查（trait 求解算法与示例的来源）。
