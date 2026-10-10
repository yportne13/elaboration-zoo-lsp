/-
  `Typort.Conversion` — 归约步（`Step`）、η-展开发生器（`EtaStep`）与转换关系
  （`Conv`）及其同余律。

  与 Rust 的对应：

  * β：值层应用命中 `Val::Lam` 时的 `closure_apply`
    （`src/L09_mltt/mod.rs:710-726`，唯一 β 点 `mod.rs:705-708`；
    `L02_tyck/mod.rs:95-98` 同款，且**忽略 icit**——形式化的 `beta`
    因此对 `ic` / `ic'` 不作限制）。
  * ζ：`let` 的急切求值 `eval(env.prepend(eval t), u)`
    （`src/L09_mltt/mod.rs:809-812`；`L02_tyck/mod.rs:101-104` 同款，
    类型标注槽被忽略——形式化的 `zeta` 里 `A` 只作占位）。
  * ι：运行时首匹配选臂 `eval_aux`（`src/L09_mltt/pattern_match.rs:361-411`）。
    声明式对应即 `Arms.find? arms c = some b` ⇒
    `match (ctor D c) args …` ⟶ `b args`（臂体是 λ telescope）。
  * 转换：值层 βη-转换 `conv`（`L02_tyck/mod.rs:135-171`）与合一器 `unify`
    （`L09_mltt/unification.rs:542-759`）。η 只有 **λ-η**（`unify` 臂 10/11），
    没有 sum/struct 的 η，因此这里 η 以**转换发生器** `EtaStep` 出现。

  不在本文件建模的部分（见 `lean/README.md`）：`VSub` 显式替换/精化传播、
  meta 求解、global 表展开（δ）、`string_concat`（`Prim`）归约、
  `struct_eq` 结构快路径、fuel 有界降级。
-/

import Typort.Subst

namespace Typort

/-- 计算步：β / ζ / ι 三条主规则加上同余。 -/
inductive Step : Tm → Tm → Prop where
  /-- β：`(λ x. t) a ⟶ t[a/0]`（icit 被忽略，同实现）。 -/
  | beta (ic ic' : Icit) (t a : Tm) : Step (.app ic (.lam ic' t) a) (subst0 a t)
  /-- ζ：`let _ : A := t; u ⟶ u[t/0]`（类型标注槽被忽略）。 -/
  | zeta (A t u : Tm) : Step (.letE A t u) (subst0 t u)
  /-- ι：构造子值上的 match（首匹配选臂，臂体应用到构造子实参）。 -/
  | iota (D c : Nat) (args : List Tm) (P : Tm) (arms : Arms) (b : Tm)
      (h : Arms.find? arms c = some b) :
      Step (.matchE (Tm.appAll (.ctor D c) args) P arms) (Tm.appAll b args)
  /-- 同余：函数位置。 -/
  | app_f (ic : Icit) {f f' a : Tm} : Step f f' → Step (.app ic f a) (.app ic f' a)
  /-- 同余：实参位置。 -/
  | app_a (ic : Icit) {f a a' : Tm} : Step a a' → Step (.app ic f a) (.app ic f a')
  /-- 同余：λ 体。 -/
  | lam_b (ic : Icit) {b b' : Tm} : Step b b' → Step (.lam ic b) (.lam ic b')
  /-- 同余：Π 的定义域。 -/
  | pi_A (ic : Icit) {A A' B : Tm} : Step A A' → Step (.pi ic A B) (.pi ic A' B)
  /-- 同余：Π 的余域。 -/
  | pi_B (ic : Icit) {A B B' : Tm} : Step B B' → Step (.pi ic A B) (.pi ic A B')
  /-- 同余：`let` 的类型标注。 -/
  | let_A {A A' t u : Tm} : Step A A' → Step (.letE A t u) (.letE A' t u)
  /-- 同余：`let` 的绑定量。 -/
  | let_t {A t t' u : Tm} : Step t t' → Step (.letE A t u) (.letE A t' u)
  /-- 同余：`let` 的体。 -/
  | let_u {A t u u' : Tm} : Step u u' → Step (.letE A t u) (.letE A t u')
  /-- 同余：match 的 scrutinee。 -/
  | match_s {s s' P : Tm} {arms : Arms} :
      Step s s' → Step (.matchE s P arms) (.matchE s' P arms)
  /-- 同余：match 的 motive。 -/
  | match_P {s P P' : Tm} {arms : Arms} :
      Step P P' → Step (.matchE s P arms) (.matchE s P' arms)

/-- η-展开（`f ⟶ λ x. f x`）作为**转换发生器**（实现里只有 λ-η，
    η 之前还有 `v_applicable` 守卫，见 `L09_mltt/mod.rs:324-330`）。 -/
inductive EtaStep : Tm → Tm → Prop where
  /-- λ-η：`f ⟶ λ x. f x`。 -/
  | eta (ic : Icit) (f : Tm) : EtaStep f (.lam ic (.app ic (lift f) (.var 0)))
  /-- 同余：λ 体。 -/
  | lam_b (ic : Icit) {b b' : Tm} : EtaStep b b' → EtaStep (.lam ic b) (.lam ic b')
  /-- 同余：函数位置。 -/
  | app_f (ic : Icit) {f f' a : Tm} : EtaStep f f' → EtaStep (.app ic f a) (.app ic f' a)
  /-- 同余：实参位置。 -/
  | app_a (ic : Icit) {f a a' : Tm} : EtaStep a a' → EtaStep (.app ic f a) (.app ic f a')
  /-- 同余：Π 的定义域。 -/
  | pi_A (ic : Icit) {A A' B : Tm} : EtaStep A A' → EtaStep (.pi ic A B) (.pi ic A' B)
  /-- 同余：Π 的余域。 -/
  | pi_B (ic : Icit) {A B B' : Tm} : EtaStep B B' → EtaStep (.pi ic A B) (.pi ic A B')
  /-- 同余：`let` 的类型标注。 -/
  | let_A {A A' t u : Tm} : EtaStep A A' → EtaStep (.letE A t u) (.letE A' t u)
  /-- 同余：`let` 的绑定量。 -/
  | let_t {A t t' u : Tm} : EtaStep t t' → EtaStep (.letE A t u) (.letE A t' u)
  /-- 同余：`let` 的体。 -/
  | let_u {A t u u' : Tm} : EtaStep u u' → EtaStep (.letE A t u) (.letE A t u')
  /-- 同余：match 的 scrutinee。 -/
  | match_s {s s' P : Tm} {arms : Arms} :
      EtaStep s s' → EtaStep (.matchE s P arms) (.matchE s' P arms)
  /-- 同余：match 的 motive。 -/
  | match_P {s P P' : Tm} {arms : Arms} :
      EtaStep P P' → EtaStep (.matchE s P arms) (.matchE s P' arms)

/-- `Step ∪ EtaStep` 的等价闭包（定义性相等 / 转换）。 -/
inductive Conv : Tm → Tm → Prop where
  /-- 自反。 -/
  | refl (t : Tm) : Conv t t
  /-- 吸收计算步。 -/
  | step {a b : Tm} : Step a b → Conv a b
  /-- 吸收 η-展开。 -/
  | eta {a b : Tm} : EtaStep a b → Conv a b
  /-- 对称。 -/
  | symm {a b : Tm} : Conv a b → Conv b a
  /-- 传递。 -/
  | trans {a b c : Tm} : Conv a b → Conv b c → Conv a c

namespace Conv

theorem of_step {a b : Tm} (h : Step a b) : Conv a b := Conv.step h

theorem of_eta {a b : Tm} (h : EtaStep a b) : Conv a b := Conv.eta h

/-- `Conv` 在 Π 定义域上的同余。 -/
theorem piA (ic : Icit) {A A' B : Tm} (h : Conv A A') : Conv (.pi ic A B) (.pi ic A' B) := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.pi_A ic hs)
  | eta he => exact .eta (.pi_A ic he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 Π 余域上的同余。 -/
theorem piB (ic : Icit) {A B B' : Tm} (h : Conv B B') : Conv (.pi ic A B) (.pi ic A B') := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.pi_B ic hs)
  | eta he => exact .eta (.pi_B ic he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 λ 体上的同余。 -/
theorem lam (ic : Icit) {t t' : Tm} (h : Conv t t') : Conv (.lam ic t) (.lam ic t') := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.lam_b ic hs)
  | eta he => exact .eta (.lam_b ic he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在函数位置的同余。 -/
theorem appF (ic : Icit) {f f' a : Tm} (h : Conv f f') : Conv (.app ic f a) (.app ic f' a) := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.app_f ic hs)
  | eta he => exact .eta (.app_f ic he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在实参位置的同余。 -/
theorem appA (ic : Icit) {f a a' : Tm} (h : Conv a a') : Conv (.app ic f a) (.app ic f a') := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.app_a ic hs)
  | eta he => exact .eta (.app_a ic he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 `let` 类型标注上的同余。 -/
theorem letA {A A' t u : Tm} (h : Conv A A') : Conv (.letE A t u) (.letE A' t u) := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.let_A hs)
  | eta he => exact .eta (.let_A he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 `let` 绑定量上的同余。 -/
theorem letT {A t t' u : Tm} (h : Conv t t') : Conv (.letE A t u) (.letE A t' u) := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.let_t hs)
  | eta he => exact .eta (.let_t he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 `let` 体上的同余。 -/
theorem letU {A t u u' : Tm} (h : Conv u u') : Conv (.letE A t u) (.letE A t u') := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.let_u hs)
  | eta he => exact .eta (.let_u he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 match scrutinee 上的同余。 -/
theorem matchS {s s' P : Tm} {arms : Arms} (h : Conv s s') :
    Conv (.matchE s P arms) (.matchE s' P arms) := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.match_s hs)
  | eta he => exact .eta (.match_s he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- `Conv` 在 match motive 上的同余。 -/
theorem matchP {s P P' : Tm} {arms : Arms} (h : Conv P P') :
    Conv (.matchE s P arms) (.matchE s P' arms) := by
  induction h with
  | refl => exact .refl _
  | step hs => exact .step (.match_P hs)
  | eta he => exact .eta (.match_P he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

end Conv

end Typort
