/-
  `Typort.Examples` — 在形式化的演算内部构造真实的判型推导与归约步。

  这些推导同时是「规则可用来判型 / 归约」的回归测试：
  `idTm_hasType` 走 Π 形成（层级取 `max`）、Π 引入、变量规则（含「绑定
  类型在其尾部上下文中是类型」的额外前提）；`beta_step` / `zeta_step` /
  `iota_step` 展示 `Step` 的三条主规则，`beta_conv` 展示 `Conv` 吸收计算步。

  依赖消去（match）规则本身就是 `Typort.Typing` 的 `HasType.matchE`；
  写一个完整的臂推导需要在每个臂上先证「构造子返回类型是类型」（变量规则
  的尾部前提），步骤繁复，作为后续工作记在 `lean/README.md`。
-/

import Typort.Typing
import Typort.Prelude

namespace Typort
namespace Examples

open Prelude

-- ===========================================================================
-- 判型
-- ===========================================================================

/-- `Type n : Type (n+1)`（非累积宇宙）。 -/
theorem u_hasType (n : Lvl) : HasType sig [] (.u n) (.u (n + 1)) := HasType.u

/-- 单 binder 上下文里下标 0 的变量：类型是 `shiftN 1 A`。 -/
theorem var_zero_single {S : Sig} {x : Name} {ic : Icit} {A : Tm} {l : Lvl}
    (hA : HasType S [] A (.u l)) :
    HasType S [⟨x, ic, A⟩] (.var 0) (shiftN 1 A) :=
  HasType.var (b := ⟨x, ic, A⟩) (l := l) rfl hA

/-- 两个 binder（内层 `A`，外层 `dom`）上下文里下标 0 的变量。 -/
theorem var_zero_cons {S : Sig} {x x' : Name} {ic ic' : Icit} {dom A : Tm} {l : Lvl}
    (hA : HasType S [⟨x, ic, dom⟩] A (.u l)) :
    HasType S [⟨x', ic', A⟩, ⟨x, ic, dom⟩] (.var 0) (shiftN 1 A) :=
  HasType.var (b := ⟨x', ic', A⟩) (l := l) rfl hA

/-- `(A : Type 0) → A → A`。 -/
def idTy : Tm := .pi .expl (.u 0) (.pi .expl (.var 0) (.var 1))

/-- `λ A x. x`。 -/
def idTm : Tm := .lam .expl (.lam .expl (.var 0))

/-- 恒等函数可判型。 -/
theorem idTm_hasType : HasType sig [] idTm idTy := by
  unfold idTm idTy
  apply HasType.lam
  · exact HasType.u
  · apply HasType.lam
    · exact var_zero_single (S := sig) (x := "A") (ic := .expl) (A := .u 0) (l := 1)
        HasType.u
    · exact var_zero_cons (S := sig) (x := "A") (x' := "x") (ic := .expl) (dom := .u 0)
        (A := .var 0) (l := 0)
        (var_zero_single (S := sig) (x := "A") (ic := .expl) (A := .u 0) (l := 1) HasType.u)

/-- `Nat` 是 `Type 0` 里的类型（归纳族常量规则）。 -/
theorem nat_hasType : HasType sig [] (.ind natIdx) (.u 0) :=
  HasType.ind sig_lookup_nat

/-- `Boolean` 是 `Type 0` 里的类型。 -/
theorem bool_hasType : HasType sig [] (.ind boolIdx) (.u 0) :=
  HasType.ind sig_lookup_bool

/-- `Eq` 有类型 `(A : Type 0) → A → A → Type 0`（族常量规则 + Π 链）。 -/
theorem eq_hasType :
    HasType sig [] (.ind eqIdx)
      (.pi .impl (.u 0) (.pi .expl (.var 0) (.pi .expl (.var 1) (.u 0)))) :=
  HasType.ind sig_lookup_eq

-- ===========================================================================
-- 归约
-- ===========================================================================

/-- β：`(λx. x) a ⟶ a`。 -/
theorem beta_step (a : Tm) : Step (.app .expl (.lam .expl (.var 0)) a) a :=
  Step.beta .expl .expl (.var 0) a

/-- ζ：`let x : Nat := a; x ⟶ a`。 -/
theorem zeta_step (a : Tm) : Step (.letE (.ind natIdx) a (.var 0)) a :=
  Step.zeta (.ind natIdx) a (.var 0)

/-- ι：`Nat` 上 `match zero { zero => a; succ n => b }` 选第一臂。 -/
theorem iota_step (a b : Tm) :
    Step (.matchE (.ctor natIdx 0) (.u 0) (.cons 0 a (.cons 1 b .nil))) a :=
  Step.iota natIdx 0 [] (.u 0) (.cons 0 a (.cons 1 b .nil)) a (by rfl)

/-- `Conv` 吸收 β 步。 -/
theorem beta_conv (a : Tm) : Conv (.app .expl (.lam .expl (.var 0)) a) a :=
  Conv.of_step (beta_step a)

end Examples
end Typort
