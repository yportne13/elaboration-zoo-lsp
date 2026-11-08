/-
  `Typort.Engine.Occurs` — 模式特化解链的环检测（`Subst::occurs_transitive`，
  L07 `mod.rs:335-399`）的抽象形式化。

  形式化对象是「按 σ 的传递闭包是否提到 x」：
  * `Mentions σ x v`：组合语义——`VSub(inner, s2)` 之下应把 **outer σ 与 inner s2
    组合**（`compose σ s2`）后再扫 inner（与 `force/frcs` 的 `compose` 语义一致）。
  * `MentionsInner σ x v`：2026-11-08 review R2 之前的**错误算法**——`VSub` 臂
    只跟随内层 `s2`、丢弃外层 σ（现实中对应 `go(inner, s2)`）。

  本模块的机器检查结论（对应 review R2）：

  * `r2_buggy_misses`：错误算法在嵌套 `VSub` 的显式反例上看不到目标变量；
  * `r2_fixed_catches`：组合语义的算法在同一个值上能看到；
  * `r2_buggy_accepts_cycle`：错误算法若被用作守卫，会接受循环解——把该值作为
    `9` 的解写入后，σ 在 9 上成环（`Cyclic`）。

  抽象边界：不建模 spine 应用、闭包体、budget（2048）与 shadowing 的完整包含关系；
  这些留待 M1 后续轮（见 `docs/lean-compiler-formalization-plan.md` §4）。
-/

import Typort.Engine.Basic

namespace Typort.Engine

/-- 组合语义下的发生检查：`v` 在 `σ` 的传递闭包下是否（经已解 rigid）提到 `x`。 -/
inductive Mentions : Subst → Lvl → Val → Prop where
  /-- 直接出现。 -/
  | rigid (σ : Subst) (x : Lvl) : Mentions σ x (.rigid x)
  /-- 经解链：`σ` 把 `y` 解成 `w`，且 `w` 传递地提到 `x`。 -/
  | solved {σ : Subst} {x y : Lvl} {w : Val} : Subst.lookup σ y = some w →
      Mentions σ x w → Mentions σ x (.rigid y)
  /-- 经结构的子值。 -/
  | child {σ : Subst} {x : Lvl} {v c : Val} : c ∈ Val.children v →
      Mentions σ x c → Mentions σ x v
  /-- `VSub(inner, s2)`：按**组合**语义 `compose σ s2` 扫 inner（R2 的修复方向）。 -/
  | vsub {σ : Subst} {x : Lvl} {v : Val} {s2 : Subst} :
      Mentions (Subst.compose σ s2) x v → Mentions σ x (.vsub v s2)

/-- R2 修复前的错误算法：`VSub` 臂只跟随内层 σ（丢弃外层）。 -/
inductive MentionsInner : Subst → Lvl → Val → Prop where
  | rigid (σ : Subst) (x : Lvl) : MentionsInner σ x (.rigid x)
  | solved {σ : Subst} {x y : Lvl} {w : Val} : Subst.lookup σ y = some w →
      MentionsInner σ x w → MentionsInner σ x (.rigid y)
  | child {σ : Subst} {x : Lvl} {v c : Val} : c ∈ Val.children v →
      MentionsInner σ x c → MentionsInner σ x v
  /-- 错误臂：只看内层 s2。 -/
  | vsub {σ : Subst} {x : Lvl} {v : Val} {s2 : Subst} :
      MentionsInner s2 x v → MentionsInner σ x (.vsub v s2)

/-- 「σ 在 x 上成环」：x 的解（传递地）提到 x 自己。 -/
def Cyclic (σ : Subst) (x : Lvl) : Prop :=
  ∃ v, Subst.lookup σ x = some v ∧ Mentions σ x v

/-! ## 反演引理

对「值头固定」的两种形态做 case 拆分，避免在具体反例里手工枚举全部构造子。 -/

/-- `MentionsInner` 在 rigid 值上的展开。 -/
theorem mentionsInner_rigid_inv {σ : Subst} {x y : Lvl}
    (hm : MentionsInner σ x (.rigid y)) :
    x = y ∨ ∃ w : Val, Subst.lookup σ y = some w ∧ MentionsInner σ x w := by
  cases hm with
  | rigid => exact Or.inl rfl
  | solved lk sub => exact Or.inr ⟨_, lk, sub⟩
  | child hmem => exact absurd hmem (by simp [Val.children])

/-- `MentionsInner` 在 vsub 值上的展开：唯一规则是错误臂。 -/
theorem mentionsInner_vsub_inv {σ : Subst} {x : Lvl} {v : Val} {s2 : Subst}
    (hm : MentionsInner σ x (.vsub v s2)) : MentionsInner s2 x v := by
  cases hm with
  | vsub h => exact h
  | child hmem => exact absurd hmem (by simp [Val.children])

/-- 空 σ 下在 rigid 值上的 `MentionsInner`：只能是直接出现（lookup 全 miss）。 -/
theorem mentionsInner_nil_rigid_eq {x y : Lvl}
    (hm : MentionsInner [] x (.rigid y)) : x = y := by
  rcases mentionsInner_rigid_inv hm with h | ⟨w, lk, _⟩
  · exact h
  · simp [Subst.lookup] at lk

/-! ## R2 的机器检查反例

σ = {0 ↦ Rigid 7, 7 ↦ Rigid 9}，v = `(Rigid 0 under ∅) under σ`（Rust 侧
`VSub(VSub(Rigid(0), ∅), σ)`）。按 `force` 的组合语义，v 归约为 `Rigid 9`；
错误算法只看内层 ∅，因此在 `target = 9` 上返回"未出现"。 -/

/-- R2 反例的 σ。 -/
def sigmaR2 : Subst := [(0, .rigid 7), (7, .rigid 9)]

/-- R2 反例的嵌套 VSub 值。 -/
def nestedR2 : Val := .vsub (.vsub (.rigid 0) []) sigmaR2

/-- 错误算法在反例上漏检（看不到 9）。 -/
theorem r2_buggy_misses : ¬ MentionsInner sigmaR2 9 nestedR2 := by
  intro h
  -- 外层 VSub：σ 切到内层 sigmaR2
  have h2 : MentionsInner sigmaR2 9 (.vsub (.rigid 0) []) :=
    mentionsInner_vsub_inv h
  -- 内层 VSub：错误臂切到 ∅
  have h3 : MentionsInner [] 9 (.rigid 0) := mentionsInner_vsub_inv h2
  have h4 : 9 = 0 := mentionsInner_nil_rigid_eq h3
  exact absurd h4 (by decide)

/-- 组合语义的算法在同一个值上**能**看到目标（0 ↦ 7 ↦ 9）。 -/
theorem r2_fixed_catches : Mentions sigmaR2 9 nestedR2 := by
  have h0 :
      Mentions (Subst.compose (Subst.compose sigmaR2 sigmaR2) []) 9 (.rigid 0) := by
    apply Mentions.solved (y := 0) (w := .rigid 7)
    · simp [Subst.compose, sigmaR2]
    · apply Mentions.solved (y := 7) (w := .rigid 9)
      · simp [Subst.compose, sigmaR2]
      · exact Mentions.rigid _ _
  have h1 :
      Mentions (Subst.compose sigmaR2 sigmaR2) 9 (.vsub (.rigid 0) []) := by
    apply Mentions.vsub
    exact h0
  exact Mentions.vsub h1

/-- 错误算法会**接受**循环解：按错误判定把 `nestedR2` 作为 `9` 的解写入后，
    σ 在 9 上成环（9 ↦ v，而 v 经 σ 的传递闭包回到 9）。 -/
theorem r2_buggy_accepts_cycle :
    Cyclic (Subst.extend sigmaR2 9 nestedR2) 9 := by
  refine ⟨nestedR2, ?_, ?_⟩
  · simp [Subst.extend]
  · -- 在**扩展后**的 σ 下，v 经 0 ↦ 7 ↦ 9 仍回到 9。
    have h0 :
        Mentions
          (Subst.compose (Subst.compose (Subst.extend sigmaR2 9 nestedR2) sigmaR2) [])
          9 (.rigid 0) := by
      apply Mentions.solved (y := 0) (w := .rigid 7)
      · simp [Subst.compose, Subst.extend, sigmaR2]
      · apply Mentions.solved (y := 7) (w := .rigid 9)
        · simp [Subst.compose, Subst.extend, sigmaR2]
        · exact Mentions.rigid _ _
    have h1 :
        Mentions (Subst.compose (Subst.extend sigmaR2 9 nestedR2) sigmaR2) 9
          (.vsub (.rigid 0) []) := by
      apply Mentions.vsub
      exact h0
    exact Mentions.vsub h1

/-- 浅层出现：`x` 在值的结构里直接出现（穿过嵌套结构/`VSub` 内层，但**不**沿 σ
    跟解链）。这是发生检查应检出的最基本情形，也是 T1 一般健全性的"直接环"半边。 -/
inductive OccursIn (x : Lvl) : Val → Prop where
  | rigid : OccursIn x (.rigid x)
  | child {v c : Val} : c ∈ Val.children v → OccursIn x c → OccursIn x v
  | vsub {v : Val} {s2 : Subst} : OccursIn x v → OccursIn x (.vsub v s2)

/-- **T1（直接环半边）**：浅层出现 ⇒ 组合语义的发生检查为真。
    （一般性 transitive 情形——`x` 只在沿 σ 解链后才出现——的"检查通过 ⇒ 无环"
    需要等级证书/无环见证，留待后续轮；本引理覆盖"直接/结构内"环，且对任意 σ。） -/
theorem occursIn_mentions {x : Lvl} {v : Val} (h : OccursIn x v) :
    ∀ σ : Subst, Mentions σ x v := by
  induction h with
  | rigid => intro σ; exact Mentions.rigid σ x
  | child hc h ih => intro σ; exact Mentions.child hc (ih σ)
  | vsub h ih => intro σ; exact Mentions.vsub (ih (Subst.compose σ _))

/-- **T1（直接环蕴含成环）**：把浅层提到 `x` 的值作为 `x` 的解写入 σ 后，
    σ 在 `x` 上成环（`x ↦ v` 且 v 提到 x）。这正是发生检查必须拒绝的形态。 -/
theorem extend_cycles_of_shallow_occurs {σ : Subst} {x : Lvl} {v : Val}
    (h : OccursIn x v) : Cyclic (Subst.extend σ x v) x := by
  refine ⟨v, ?_, ?_⟩
  · simp [Subst.extend]
  · exact occursIn_mentions h (Subst.extend σ x v)

end Typort.Engine
