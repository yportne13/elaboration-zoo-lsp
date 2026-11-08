/-
  `Typort.Engine.StructEq` — `struct_eq` 快路径的抽象形式化
  （2026-11-08 review T5 / P15）。

  背景（review P15，S1）：`struct_eq` 的卡住 match 臂原先只比较 pending 的
  **长度与 icit**，漏比 pending 的**值**，于是「scrutinee 是另一个 pending 不同
  的卡住 match」的两份值被判等；后果是 `refl` 可证明两个闭实例化结果不同的
  函数相等（进而证 False）。修复：Match 臂同时比较 pending 的值。

  本模块用最小值片段建模两版算法：

  * `eqBuggy`：Match 臂只比 scrutinee（漏 pending 值）——修复前；
  * `eqFixed`：Match 臂同时比 scrutinee 与 pending 值——修复后；
  * `levels`：值的可观测内容（全部刚性层级；pending 是值的一部分）。

  机检结论：
  * `p15_counterexample`：`match (rigid 0) [0]` 与 `match (rigid 0) [1]` 在
    `eqBuggy` 下判等、在 `eqFixed` 下不等，且可观测内容不同——旧快路径把不同
    的值判成相等（P15 的直接反例）。
  * `eqFixed_sound`（T5）：`eqFixed` 为 true ⇒ 两值可观测内容相同（修复后快路径
    健全；返回 false 只回落到慢路径，方向安全）。

  抽象边界：只保留 P15 的因果结构（scrutinee 递归 + pending 值）；省略捕获
  env、分支体、构造子字段、跨表名字、span 与 pending 的 icit（icit 在修复前
  也有比较，不是 P15 的漏项）。
-/

import Typort.Basic

namespace Typort.Engine.StructEq

/-- 最小值片段：刚性头，以及「卡住 match = scrutinee + pending 值」。 -/
inductive SM where
  | rigid (n : Nat) : SM
  | matchV (scrutinee : SM) (pending : List Nat) : SM

/-- 修复前算法：卡住 match 只比 scrutinee（**漏 pending 值**）。 -/
def eqBuggy : SM → SM → Bool
  | .rigid a, .rigid b => a == b
  | .matchV s _, .matchV t _ => eqBuggy s t
  | _, _ => false

/-- 修复后算法：卡住 match 同时比 scrutinee 与 pending 值。 -/
def eqFixed : SM → SM → Bool
  | .rigid a, .rigid b => a == b
  | .matchV s ps, .matchV t qs => eqFixed s t && (ps == qs)
  | _, _ => false

/-- 可观测内容：值的全部刚性层级（pending 也是值的一部分）。 -/
def levels : SM → List Nat
  | .rigid n => [n]
  | .matchV s ps => levels s ++ ps

/-! ## P15 反例

`pfun x` 在 `x` 卡住时返回一个卡住 match；两个 pending 不同的卡住 match
（`pending = [0]` vs `[1]`）在旧快路径下被判等。 -/

/-- 值 A：`match (rigid 0) [0]`。 -/
def p15A : SM := .matchV (.rigid 0) [0]

/-- 值 B：`match (rigid 0) [1]`。 -/
def p15B : SM := .matchV (.rigid 0) [1]

/-- **P15 机检反例**：旧算法判等（`true`）、新算法判不等（`false`），且两值
    可观测内容不同——旧快路径把不同的值判成了相等。 -/
theorem p15_counterexample :
    eqBuggy p15A p15B = true ∧ eqFixed p15A p15B = false ∧
      levels p15A ≠ levels p15B := by
  decide

/-! ## T5：修复后快路径的健全性 -/

/-- **T5（`eqFixed` 健全性）**：`eqFixed` 判等 ⇒ 两值可观测内容相同。
    按值结构递归证明（每个等式检查都归结为 `Nat`/`List Nat` 的 `==`-到-`=`）。 -/
theorem eqFixed_sound : ∀ (a b : SM), eqFixed a b = true → levels a = levels b
  | .rigid a, .rigid b, h => by
      have hab : a = b := by simpa [eqFixed] using h
      subst hab
      rfl
  | .rigid _, .matchV _ _, h => by simp [eqFixed] at h
  | .matchV _ _, .rigid _, h => by simp [eqFixed] at h
  | .matchV s ps, .matchV t qs, h => by
      have h' : (eqFixed s t && (ps == qs)) = true := by simpa [eqFixed] using h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨hst, hpq⟩ := h'
      have ih := eqFixed_sound s t hst
      have hpq' : ps = qs := by simpa using hpq
      simp [levels, ih, hpq']

end Typort.Engine.StructEq
