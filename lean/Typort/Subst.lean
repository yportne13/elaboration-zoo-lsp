/-
  `Typort.Subst` — 重命名与（并行）替换，以及它们之间的代数律。

  这是整份形式化的地基。方案采用 de Bruijn 索引的标准处理
  （PLFA `DeBruijn` 的 `rename` / `subst` / `ext` / `exts`）：

  * `ren ξ`   重命名自由变量；过 binder 时把 `ξ` 扩成 `ext ξ`
              （`0 ↦ 0`，`i+1 ↦ ξ i + 1`）。
  * `subst σ` 并行替换；过 binder 时把 `σ` 扩成 `extS σ`
              （`0 ↦ var 0`，`i+1 ↦ lift (σ i)`）。
  * `lift` **也是** `ren (·+1)`（过 binder 用 `ext`），因此
    `subst_ren` / `ren_subst` / `subst_subst` 三条标准律成立，
    其余引理都从它们派生。

  与 Rust 的对应：`L09_mltt/bump_spine_iter/subst.rs` 的显式替换
  （`Subst` 持久化单链 + `frcs` 读点推开）是**精化传播**这一层语义的
  实现手段；声明式类型论里对应的元运算就是这里的 `subst`
  （见 `lean/README.md` 的「实现层 vs 声明层」小节）。
-/

import Typort.Syntax

namespace Typort

/-- 重命名：自由变量 ↦ 自由变量。 -/
abbrev Ren := Ix → Ix

/-- 并行替换：自由变量 ↦ 项。 -/
abbrev Sub := Ix → Tm

/-- 重命名过 binder 的扩展：`0 ↦ 0`，`i+1 ↦ ξ i + 1`。PLFA：`ext`。 -/
def ext (ξ : Ren) : Ren := fun i => match i with
  | 0 => 0
  | j + 1 => ξ j + 1

mutual

  /-- 重命名（`ren ξ t`：把 `t` 的自由变量按 `ξ` 改名）。 -/
  def ren (ξ : Ren) : Tm → Tm
    | .var i => .var (ξ i)
    | .u n => .u n
    | .pi ic A B => .pi ic (ren ξ A) (ren (ext ξ) B)
    | .lam ic t => .lam ic (ren (ext ξ) t)
    | .app ic f a => .app ic (ren ξ f) (ren ξ a)
    | .letE A t u => .letE (ren ξ A) (ren ξ t) (ren (ext ξ) u)
    | .ind D => .ind D
    | .ctor D c => .ctor D c
    | .matchE s P arms => .matchE (ren ξ s) (ren ξ P) (renArms ξ arms)

  /-- 重命名（臂链版本）。 -/
  def renArms (ξ : Ren) : Arms → Arms
    | .nil => .nil
    | .cons c b r => .cons c (ren ξ b) (renArms ξ r)

end

/-- 自由变量整体 +1（过 binder 用 `ext`，因此不会误伤被绑定的变量）。 -/
def lift (t : Tm) : Tm := ren (fun i => i + 1) t

/-- 平移全部自由变量 `k`（cutoff 0）。 -/
def shiftN (k : Nat) (t : Tm) : Tm := ren (fun i => i + k) t

/-- 替换过 binder 的扩展：`0 ↦ var 0`，`i+1 ↦ lift (σ i)`。PLFA：`exts`。 -/
def extS (σ : Sub) : Sub := fun i => match i with
  | 0 => .var 0
  | j + 1 => lift (σ j)

mutual

  /-- 并行替换。 -/
  def subst (σ : Sub) : Tm → Tm
    | .var i => σ i
    | .u n => .u n
    | .pi ic A B => .pi ic (subst σ A) (subst (extS σ) B)
    | .lam ic t => .lam ic (subst (extS σ) t)
    | .app ic f a => .app ic (subst σ f) (subst σ a)
    | .letE A t u => .letE (subst σ A) (subst σ t) (subst (extS σ) u)
    | .ind D => .ind D
    | .ctor D c => .ctor D c
    | .matchE s P arms => .matchE (subst σ s) (subst σ P) (substArms σ arms)

  /-- 并行替换（臂链版本）。 -/
  def substArms (σ : Sub) : Arms → Arms
    | .nil => .nil
    | .cons c b r => .cons c (subst σ b) (substArms σ r)

end

/-- 恒等替换。 -/
def ids : Sub := fun i => .var i

/-- 把 `a` 接到替换 `σ` 前面（Rust 里 `env.prepend` 的项层对应物）。 -/
def cons (a : Tm) (σ : Sub) : Sub := fun i => match i with
  | 0 => a
  | j + 1 => σ j

/-- 单个替换：`t[0 := a]`（下标 0 换成 `a`，其余减一）。 -/
def subst0 (a : Tm) (t : Tm) : Tm := subst (cons a ids) t

-- ===========================================================================
-- funext 级的小引理（`ext` / `extS` 的代数）
-- ===========================================================================

theorem ext_id : ext (fun i => i) = fun i => i := by
  funext i; cases i <;> rfl

theorem ext_comp (ξ ξ' : Ren) : (fun i => ext ξ (ext ξ' i)) = ext (fun i => ξ (ξ' i)) := by
  funext i; cases i <;> rfl

theorem extS_var : extS ids = ids := by
  funext i; cases i <;> rfl

theorem extS_ext (σ : Sub) (ξ : Ren) :
    (fun i => extS σ (ext ξ i)) = extS (fun i => σ (ξ i)) := by
  funext i; cases i <;> rfl

-- ===========================================================================
-- 重命名
-- ===========================================================================

mutual

  theorem ren_id : (t : Tm) → ren (fun i => i) t = t
    | .var i => rfl
    | .u n => rfl
    | .pi ic A B => by
        simp only [ren]
        rw [ext_id, ren_id A, ren_id B]
    | .lam ic t => by
        simp only [ren]
        rw [ext_id, ren_id t]
    | .app ic f a => by
        simp only [ren]
        rw [ren_id f, ren_id a]
    | .letE A t u => by
        simp only [ren]
        rw [ext_id, ren_id A, ren_id t, ren_id u]
    | .ind D => rfl
    | .ctor D c => rfl
    | .matchE s P arms => by
        simp only [ren]
        rw [ren_id s, ren_id P, ren_idArms arms]

  theorem ren_idArms : (arms : Arms) → renArms (fun i => i) arms = arms
    | .nil => rfl
    | .cons c b r => by
        simp only [renArms]
        rw [ren_id b, ren_idArms r]

end

mutual

  theorem ren_ren (ξ ξ' : Ren) : (t : Tm) →
      ren ξ (ren ξ' t) = ren (fun i => ξ (ξ' i)) t
    | .var i => rfl
    | .u n => rfl
    | .pi ic A B => by
        simp only [ren]
        rw [ren_ren ξ ξ' A, ren_ren (ext ξ) (ext ξ') B, ext_comp]
    | .lam ic t => by
        simp only [ren]
        rw [ren_ren (ext ξ) (ext ξ') t, ext_comp]
    | .app ic f a => by
        simp only [ren]
        rw [ren_ren ξ ξ' f, ren_ren ξ ξ' a]
    | .letE A t u => by
        simp only [ren]
        rw [ren_ren ξ ξ' A, ren_ren ξ ξ' t, ren_ren (ext ξ) (ext ξ') u, ext_comp]
    | .ind D => rfl
    | .ctor D c => rfl
    | .matchE s P arms => by
        simp only [ren]
        rw [ren_ren ξ ξ' s, ren_ren ξ ξ' P, ren_renArms ξ ξ' arms]

  theorem ren_renArms (ξ ξ' : Ren) : (arms : Arms) →
      renArms ξ (renArms ξ' arms) = renArms (fun i => ξ (ξ' i)) arms
    | .nil => rfl
    | .cons c b r => by
        simp only [renArms]
        rw [ren_ren ξ ξ' b, ren_renArms ξ ξ' r]

end

-- ===========================================================================
-- 替换
-- ===========================================================================

mutual

  theorem subst_id : (t : Tm) → subst ids t = t
    | .var i => rfl
    | .u n => rfl
    | .pi ic A B => by
        simp only [subst]
        rw [extS_var, subst_id A, subst_id B]
    | .lam ic t => by
        simp only [subst]
        rw [extS_var, subst_id t]
    | .app ic f a => by
        simp only [subst]
        rw [subst_id f, subst_id a]
    | .letE A t u => by
        simp only [subst]
        rw [extS_var, subst_id A, subst_id t, subst_id u]
    | .ind D => rfl
    | .ctor D c => rfl
    | .matchE s P arms => by
        simp only [subst]
        rw [subst_id s, subst_id P, subst_idArms arms]

  theorem subst_idArms : (arms : Arms) → substArms ids arms = arms
    | .nil => rfl
    | .cons c b r => by
        simp only [substArms]
        rw [subst_id b, subst_idArms r]

end

mutual

  /-- `subst_ren`：先重命名再替换 = 用复合后的替换。 -/
  theorem subst_ren (σ : Sub) (ξ : Ren) : (t : Tm) →
      subst σ (ren ξ t) = subst (fun i => σ (ξ i)) t
    | .var i => rfl
    | .u n => rfl
    | .pi ic A B => by
        simp only [ren, subst]
        rw [subst_ren σ ξ A, subst_ren (extS σ) (ext ξ) B, extS_ext]
    | .lam ic t => by
        simp only [ren, subst]
        rw [subst_ren (extS σ) (ext ξ) t, extS_ext]
    | .app ic f a => by
        simp only [ren, subst]
        rw [subst_ren σ ξ f, subst_ren σ ξ a]
    | .letE A t u => by
        simp only [ren, subst]
        rw [subst_ren σ ξ A, subst_ren σ ξ t, subst_ren (extS σ) (ext ξ) u, extS_ext]
    | .ind D => rfl
    | .ctor D c => rfl
    | .matchE s P arms => by
        simp only [ren, subst]
        rw [subst_ren σ ξ s, subst_ren σ ξ P, subst_renArms σ ξ arms]

  theorem subst_renArms (σ : Sub) (ξ : Ren) : (arms : Arms) →
      substArms σ (renArms ξ arms) = substArms (fun i => σ (ξ i)) arms
    | .nil => rfl
    | .cons c b r => by
        simp only [renArms, substArms]
        rw [subst_ren σ ξ b, subst_renArms σ ξ r]

end

/-- `ext ξ ∘ extS σ = extS (ren ξ ∘ σ)`（`ren_subst` 的 binder 情形）。 -/
theorem ext_ren_extS (ξ : Ren) (σ : Sub) :
    (fun i => ren (ext ξ) (extS σ i)) = extS (fun i => ren ξ (σ i)) := by
  funext i; cases i with
  | zero => rfl
  | succ j =>
      show ren (ext ξ) (ren (fun i => i + 1) (σ j)) = ren (fun i => i + 1) (ren ξ (σ j))
      rw [ren_ren (ξ := ext ξ) (ξ' := fun i => i + 1) (t := σ j),
          ren_ren (ξ := fun i => i + 1) (ξ' := ξ) (t := σ j)]
      rfl

mutual

  /-- `ren_subst`：先替换再重命名 = 用逐点重命名后的替换。 -/
  theorem ren_subst (ξ : Ren) (σ : Sub) : (t : Tm) →
      ren ξ (subst σ t) = subst (fun i => ren ξ (σ i)) t
    | .var i => rfl
    | .u n => rfl
    | .pi ic A B => by
        simp only [ren, subst]
        rw [ren_subst ξ σ A, ren_subst (ext ξ) (extS σ) B, ext_ren_extS]
    | .lam ic t => by
        simp only [ren, subst]
        rw [ren_subst (ext ξ) (extS σ) t, ext_ren_extS]
    | .app ic f a => by
        simp only [ren, subst]
        rw [ren_subst ξ σ f, ren_subst ξ σ a]
    | .letE A t u => by
        simp only [ren, subst]
        rw [ren_subst ξ σ A, ren_subst ξ σ t, ren_subst (ext ξ) (extS σ) u, ext_ren_extS]
    | .ind D => rfl
    | .ctor D c => rfl
    | .matchE s P arms => by
        simp only [ren, subst]
        rw [ren_subst ξ σ s, ren_subst ξ σ P, ren_substArms ξ σ arms]

  theorem ren_substArms (ξ : Ren) (σ : Sub) : (arms : Arms) →
      renArms ξ (substArms σ arms) = substArms (fun i => ren ξ (σ i)) arms
    | .nil => rfl
    | .cons c b r => by
        simp only [renArms, substArms]
        rw [ren_subst ξ σ b, ren_substArms ξ σ r]

end

/-- `extS σ ∘ extS τ = extS (subst σ ∘ τ)`（`subst_subst` 的 binder 情形）。 -/
theorem extS_comp (σ τ : Sub) :
    (fun i => subst (extS σ) (extS τ i)) = extS (fun i => subst σ (τ i)) := by
  funext i; cases i with
  | zero => rfl
  | succ j =>
      show subst (extS σ) (ren (fun i => i + 1) (τ j))
        = ren (fun i => i + 1) (subst σ (τ j))
      rw [subst_ren (σ := extS σ) (ξ := fun i => i + 1) (t := τ j),
          ren_subst (ξ := fun i => i + 1) (σ := σ) (t := τ j)]
      rfl

mutual

  /-- `subst_subst`：并行替换的复合。 -/
  theorem subst_subst (σ τ : Sub) : (t : Tm) →
      subst σ (subst τ t) = subst (fun i => subst σ (τ i)) t
    | .var i => rfl
    | .u n => rfl
    | .pi ic A B => by
        simp only [subst]
        rw [subst_subst σ τ A, subst_subst (extS σ) (extS τ) B, extS_comp]
    | .lam ic t => by
        simp only [subst]
        rw [subst_subst (extS σ) (extS τ) t, extS_comp]
    | .app ic f a => by
        simp only [subst]
        rw [subst_subst σ τ f, subst_subst σ τ a]
    | .letE A t u => by
        simp only [subst]
        rw [subst_subst σ τ A, subst_subst σ τ t, subst_subst (extS σ) (extS τ) u, extS_comp]
    | .ind D => rfl
    | .ctor D c => rfl
    | .matchE s P arms => by
        simp only [subst]
        rw [subst_subst σ τ s, subst_subst σ τ P, subst_substArms σ τ arms]

  theorem subst_substArms (σ τ : Sub) : (arms : Arms) →
      substArms σ (substArms τ arms) = substArms (fun i => subst σ (τ i)) arms
    | .nil => rfl
    | .cons c b r => by
        simp only [substArms]
        rw [subst_subst σ τ b, subst_substArms σ τ r]

end

-- ===========================================================================
-- 派生引理
-- ===========================================================================

/-- 替换一个变量后把自由变量平移回去，得到原项。 -/
theorem subst0_lift (a t : Tm) : subst0 a (lift t) = t := by
  unfold subst0 lift
  rw [subst_ren (σ := cons a ids) (ξ := fun i => i + 1) (t := t)]
  have h : (fun i => cons a ids (i + 1)) = ids := by
    funext i; rfl
  rw [h, subst_id]

/-- `subst0` 与一般替换的交换律。 -/
theorem subst_subst0 (σ : Sub) (a t : Tm) :
    subst σ (subst0 a t) = subst (cons (subst σ a) σ) t := by
  unfold subst0
  rw [subst_subst]
  congr 1
  funext i; cases i <;> rfl

/-- 平移的复合。 -/
theorem shiftN_shiftN (j k : Nat) (t : Tm) : shiftN k (shiftN j t) = shiftN (j + k) t := by
  unfold shiftN
  rw [ren_ren (ξ := fun i => i + k) (ξ' := fun i => i + j) (t := t)]
  congr 1
  funext i
  exact Nat.add_assoc i j k
theorem subst0_lam (ic : Icit) (a t : Tm) :
    subst0 a (.lam ic t) = .lam ic (subst (extS (cons a ids)) t) := rfl

end Typort
