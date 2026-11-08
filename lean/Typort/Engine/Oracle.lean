/-
  `Typort.Engine.Oracle` — M3：Lean 侧可执行 oracle（curated review 语料）。

  用途：`engine-oracle <case>` 在 stdout 输出 `ok` / `err`；Rust 侧
  `tests/lean_oracle_parity.rs` 在 `LEAN_ORACLE=1` 时调用它，并与 L07 参考引擎
  `run(src, 0)` 的判定比对（差分测试）。

  每个 case 的裁决依据都来自 Engine 模块里已机检的定理/定义：

  * `occurs-transitive`（review R2 / c1）——`Occurs.r2_fixed_catches`：组合语义的
    发生检查能看到 `0 ↦ 7 ↦ 9` 的传递环，因此循环特化解会被拒绝 ⇒ `err`。
  * `stuck-match-bounded`（review R3 / c2）——预算耗尽路径
    （`Classify.fuel_exhaustion_not_absurd`）不判 Absurd，但整个方程仍失败 ⇒ `err`。
  * `empty-type-zero-arm`（review R1）——`Classify.classify_absurd_sound`：两侧规范头
    不同 ⇒ Absurd ⇒ 覆盖探测不要求该构造子被覆盖，零臂 match 合法 ⇒ `ok`。
  * `struct-eq-pending`（review P15）——`StructEq.p15_counterexample`：修复后的快路径
    会比较 pending 的值，两份不同的卡住 match 不再被判等 ⇒ `err`。

  **边界（诚实声明）**：oracle 只对 curated 语料裁决，不解析 Typort 源码、不实现
  完整 unify/pattern 编译；它是"语义判据的第三方裁判 + CI 漂移探针"，不是第二编译器。
-/

import Typort.Engine.Occurs
import Typort.Engine.Classify
import Typort.Engine.StructEq

namespace Typort.Engine.Oracle

/-- curated review 语料。 -/
inductive Case where
  | occursTransitive
  | stuckMatchBounded
  | emptyTypeZeroArm
  | structEqPending
  deriving Repr, DecidableEq

/-- 语料名（CLI 参数）。 -/
def Case.name : Case → String
  | .occursTransitive => "occurs-transitive"
  | .stuckMatchBounded => "stuck-match-bounded"
  | .emptyTypeZeroArm => "empty-type-zero-arm"
  | .structEqPending => "struct-eq-pending"

/-- 语料裁决：`ok` = 参考引擎接受，`err` = 参考引擎拒绝（任意 Err 档都算 err）。 -/
def Case.verdict : Case → String
  | .occursTransitive => "err"
  | .stuckMatchBounded => "err"
  | .emptyTypeZeroArm => "ok"
  | .structEqPending => "err"

/-- 解析 CLI 语料名。 -/
def parseCase (s : String) : Option Case :=
  match s with
  | "occurs-transitive" => some .occursTransitive
  | "stuck-match-bounded" => some .stuckMatchBounded
  | "empty-type-zero-arm" => some .emptyTypeZeroArm
  | "struct-eq-pending" => some .structEqPending
  | _ => none

/-- 可执行入口：`engine-oracle <case>`。 -/
def runMain (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      match parseCase name with
      | some c =>
          IO.println (c.verdict)
          pure 0
      | none =>
          IO.eprintln s!"unknown case: {name}"
          pure 2
  | _ =>
      IO.eprintln "usage: engine-oracle <case>"
      IO.eprintln "cases: occurs-transitive | stuck-match-bounded | empty-type-zero-arm | struct-eq-pending"
      pure 2

end Typort.Engine.Oracle
