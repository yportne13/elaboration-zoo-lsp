/-
  `Typort.Engine.Classify` — 合一失败三档分类（`UnifyKind`：Absurd / Undecided / Fuel）
  的抽象形式化（2026-11-08 review R1/R3）。

  背景（review R1）：修复前 `unify_no_arm` 的 "definite" 集合不完整，把
  `Sum × LiteralType` 等**确定冲突**也归进 `Undecided`；而覆盖探测把
  `Undecided` 当可达 ⇒ 合法的空类型零臂 match 被拒。修复后的规则是：

  * 两侧都是**规范头**（Sum / SumCase / U / LiteralType / LiteralIntro / Pi / Lam）
    且头类不同 ⇒ `Absurd`（确定不可合一）；
  * 其余（任一侧中性 / 头类相同但没比出来）⇒ `Undecided`；
  * 预算耗尽 ⇒ `Fuel`（由调用方单独标注，分类器本身不产生）。

  本模块把 "Absurd ⇒ 无公共实例（不存在任何替换让它俩相等）" 机检化（T2），
  并证明覆盖探测的消费纪律（T3）：只有 `Absurd` 会被当作"分支不可达"，
  `Undecided` / `Fuel` 永远不会伪装成矛盾；`Fuel` 不会产生覆盖义务。

  抽象边界：`Canon` 是规范值片段（省略 spine/闭包体/VSub/Match 等中性结构——
  它们落在 "任一侧中性 ⇒ Undecided" 的非 definite 分支）；替换用 `Inst` 关系
  建模（存在某个替换使 t 实例化为 w），不建模预算实现本身。
-/

import Typort.Basic

namespace Typort.Engine.Classify

/-- 规范值片段。`var` 只用于让替换关系 `Inst` 有内容；真实引擎在分类前已
    `force`，规范值表面上看不到裸 rigid。 -/
inductive Canon where
  | var (n : Nat) : Canon
  | sum (name : String) (args : List Canon) : Canon
  | sumCase (name : String) (args : List Canon) : Canon
  | u (l : Nat) : Canon
  | litTy : Canon
  | lit (s : String) : Canon
  | pi (dom cod : Canon) : Canon
  | lam (body : Canon) : Canon

/-- 头类（与 Rust `is_canonical_head` 的 7 个规范头 + neutral 一一对应）。 -/
inductive HeadClass where
  | sum | sumCase | u | litTy | lit | pi | lam | neutral
  deriving DecidableEq, Repr

/-- 取值的规范头类；`var` 是中性头。 -/
def headClass : Canon → HeadClass
  | .var _ => .neutral
  | .sum _ _ => .sum
  | .sumCase _ _ => .sumCase
  | .u _ => .u
  | .litTy => .litTy
  | .lit _ => .lit
  | .pi _ _ => .pi
  | .lam _ => .lam

/-- 是否是规范头（Rust `is_canonical_head`）。 -/
def isCanonical (t : Canon) : Bool := headClass t ≠ .neutral

mutual

  /-- 单步实例化：σ 是任意替换，把变量替换成规范值。 -/
  inductive Inst (σ : Nat → Option Canon) : Canon → Canon → Prop where
    | var {n w} : σ n = some w → Inst σ (.var n) w
    | sum {name as bs} : InstList σ as bs → Inst σ (.sum name as) (.sum name bs)
    | sumCase {name as bs} : InstList σ as bs → Inst σ (.sumCase name as) (.sumCase name bs)
    | u {l} : Inst σ (.u l) (.u l)
    | litTy : Inst σ .litTy .litTy
    | lit {s} : Inst σ (.lit s) (.lit s)
    | pi {dom cod dom' cod'} : Inst σ dom dom' → Inst σ cod cod' →
        Inst σ (.pi dom cod) (.pi dom' cod')
    | lam {body body'} : Inst σ body body' → Inst σ (.lam body) (.lam body')

  /-- 列表逐点实例化。 -/
  inductive InstList (σ : Nat → Option Canon) : List Canon → List Canon → Prop where
    | nil : InstList σ [] []
    | cons {a b as bs} : Inst σ a b → InstList σ as bs → InstList σ (a :: as) (b :: bs)

end

/-! ## T2：Absurd 的健全性

规范头的类在实例化下不变 ⇒ 类不同的两个规范值不可能有公共实例。 -/

/-- 非中性头的规范值，其实例化结果的头类与原值相同。 -/
theorem inst_head_of_nonneutral {σ : Nat → Option Canon} {t w : Canon}
    (hc : headClass t ≠ .neutral) (h : Inst σ t w) : headClass w = headClass t := by
  cases h with
  | var hs => exact absurd rfl hc
  | sum _ => rfl
  | sumCase _ => rfl
  | u => rfl
  | litTy => rfl
  | lit => rfl
  | pi _ _ => rfl
  | lam _ => rfl

/-- **T2（Absurd 健全性）**：两个规范头不同的值，没有公共实例——
    即不存在替换 σ 与规范值 w 使二者都实例化为 w。 -/
theorem no_common_instance_of_head_ne {σ : Nat → Option Canon} {t u w : Canon}
    (ht : headClass t ≠ .neutral) (hu : headClass u ≠ .neutral)
    (hne : headClass t ≠ headClass u)
    (h1 : Inst σ t w) (h2 : Inst σ u w) : False := by
  have e1 := inst_head_of_nonneutral ht h1
  have e2 := inst_head_of_nonneutral hu h2
  exact hne (e1.symm.trans e2)

/-! ## 三档分类器与 T3 消费纪律 -/

/-- 合一失败三档（对齐 Rust `UnifyKind`）。 -/
inductive Kind where
  | absurd | undecided | fuel
  deriving DecidableEq, Repr

/-- 分类器：两侧规范头不同 ⇒ Absurd；否则 Undecided（中性头不判矛盾）。 -/
def classify (t u : Canon) : Kind :=
  if headClass t ≠ .neutral ∧ headClass u ≠ .neutral ∧ headClass t ≠ headClass u then
    .absurd
  else
    .undecided

/-- 覆盖探测的消费：只有 Absurd 判"分支不可达"（要求覆盖的反面）。 -/
def probeUnreachable : Kind → Bool
  | .absurd => true
  | .undecided => false
  | .fuel => false

/-- 通用分类器的 Absurd 只在"两侧规范头不同"时产生。 -/
theorem classify_absurd_heads {t u : Canon} (h : classify t u = .absurd) :
    headClass t ≠ .neutral ∧ headClass u ≠ .neutral ∧ headClass t ≠ headClass u := by
  unfold classify at h
  split at h
  · assumption
  · simp at h

/-- **T2'（分类器层面）**：`classify` 返回 Absurd ⇒ 不存在公共实例。 -/
theorem classify_absurd_sound {t u : Canon} (h : classify t u = .absurd) :
    ¬ ∃ (σ : Nat → Option Canon) (w : Canon), Inst σ t w ∧ Inst σ u w := by
  rintro ⟨σ, w, h1, h2⟩
  obtain ⟨ht, hu, hne⟩ := classify_absurd_heads h
  exact no_common_instance_of_head_ne ht hu hne h1 h2

/-- 探测消费纪律：`probeUnreachable k = true ↔ k = Absurd`。 -/
theorem probeUnreachable_iff_absurd (k : Kind) :
    probeUnreachable k = true ↔ k = .absurd := by
  cases k <;> simp [probeUnreachable]

/-- **T3（Undecided 保守性）**：任一侧中性 ⇒ 分类器不判 Absurd（不伪装成矛盾）。 -/
theorem classify_neutral_not_absurd {t u : Canon}
    (h : headClass t = .neutral ∨ headClass u = .neutral) : classify t u ≠ .absurd := by
  intro hc
  obtain ⟨ht, hu, _⟩ := classify_absurd_heads hc
  rcases h with h | h
  · exact ht h
  · exact hu h

/-- 预算耗尽路径：不产生 Absurd（Fuel 与 Absurd 是不同档）。 -/
def classifyBudget (fuel : Nat) (t u : Canon) : Kind :=
  if fuel = 0 then .fuel else classify t u

/-- **T3'（预算不伪装矛盾）**：预算耗尽时既不是 Absurd，也不会被判"分支不可达"。 -/
theorem fuel_exhaustion_not_absurd (t u : Canon) :
    classifyBudget 0 t u = .fuel ∧ probeUnreachable (classifyBudget 0 t u) = false := by
  simp [classifyBudget, probeUnreachable]

end Typort.Engine.Classify
