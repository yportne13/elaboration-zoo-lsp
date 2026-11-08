/-
  `Typort.Engine.Rank` — occurs 健全性（T1）的**等级证书半边**：
  用「解链边严格降 rank」的证书刻画无环替换，并证明扩展解时证书保持。

  为什么需要它（review R2）：固定版 `occurs_transitive` 在解决问题时只做一次
  "传递扫描"，它**不构造**无环见证。要把 "check 通过 ⇒ 扩展后无环" 说清楚，
  需要给"无环"一个可证明的规范刻画。本模块取最常用的充分条件：

  * `Edge σ a b`：`σ` 把 `a` 解成包含 `b` 的值（浅层出现）；
  * `Path σ a b`：边的传递闭包；`Acyclic σ`：没有非空环；
  * `RankOK σ r`：存在等级函数 `r : Lvl → Nat`，使每条解链边 `a → b` 严格降
    （`r b < r a`）——这是无环的**等级证书**：
    `rank_acyclic`（T1 证书健全性）：`RankOK σ r ⇒ Acyclic σ`。

  扩展半边（`rankOK_extend` / `extend_acyclic_of_rank`）：若现有证书 `r` 已经
  把新解 `x ↦ v` 夹在中间——
    * v 的每个浅层出现 `b` 都满足 `r b < r x`；
    * `x` 的每个前驱 `y`（解值浅层含 x）都满足 `r x < r y`；
  则 `extend σ x v` 仍以**同一个 r** 持有等级证书，从而仍无环。

  这直接对应 review R2 的修复方向：只要"新解不把 x 放到自己下面"（以及不破坏
  已解链的等级序），扩展就安全；`occurs_transitive` 的传递扫描是该充分条件的
  一个（不完备的）检查。

  第 4 轮补充（T1 主体）：不构造 rank，也可以**直接证明无环性保持**——
  见本文件末尾的 `OccursReach` / `path_extend_decomp` / `extend_acyclic_of_no_reach`：
  若 σ 无环、且 v 的浅层出现都不能沿 σ 回到 x（`¬ OccursReach σ x v`），则
  `extend σ x v` 无环。证明核心是路径分解：`extend` 下的路径要么是 σ 路径、
  要么可分解为「a 到 x 的 σ 路径 + 新边 x→c（c 在 v 中）+ c 到 b 的路径」。

  抽象边界：`OccursInR` 不进入 `VSub` 内层（VSub 的组合语义与 R2 反例见
  `Occurs.lean`）；本模块的边/路径只覆盖非 VSub 结构。`Nat` 等级已足够。
  尚未机检的桥：`Mentions`（组合语义，含 VSub）与 `OccursReach` 的等价性。
-/

import Typort.Engine.Basic

namespace Typort.Engine.Rank

/-- 浅层出现（不进入 `VSub` 内层；`Val.children (.vsub ..) = []`）。
    边的目标只取值的浅层刚性层级。 -/
inductive OccursInR (x : Lvl) : Val → Prop where
  | rigid : OccursInR x (.rigid x)
  | child {v c : Val} : c ∈ Val.children v → OccursInR x c → OccursInR x v

/-- 解链边：`σ` 把 `a` 解成浅层出现 `b` 的值。 -/
def Edge (σ : Subst) (a b : Lvl) : Prop :=
  ∃ w : Val, Subst.lookup σ a = some w ∧ OccursInR b w

/-- 解链边的传递闭包（非空路径）。 -/
inductive Path (σ : Subst) : Lvl → Lvl → Prop where
  | single {a b : Lvl} : Edge σ a b → Path σ a b
  | trans {a b c : Lvl} : Edge σ a b → Path σ b c → Path σ a c

/-- 无环：不存在非空的解链环。 -/
def Acyclic (σ : Subst) : Prop := ∀ a : Lvl, ¬ Path σ a a

/-- 等级证书：每条解链边严格降 rank。 -/
def RankOK (σ : Subst) (r : Lvl → Nat) : Prop :=
  ∀ (a : Lvl) (w : Val) (b : Lvl),
    Subst.lookup σ a = some w → OccursInR b w → r b < r a

/-- 路径上 rank 严格递减。 -/
theorem rank_decreases_path {σ : Subst} {r : Lvl → Nat}
    (hr : RankOK σ r) {a b : Lvl} (h : Path σ a b) : r b < r a := by
  induction h with
  | single he =>
      obtain ⟨w, lk, occ⟩ := he
      exact hr _ w _ lk occ
  | trans he _ ih =>
      obtain ⟨w, lk, occ⟩ := he
      have hstep : r _ < r _ := hr _ w _ lk occ
      exact Nat.lt_trans ih hstep

/-- **T1（证书健全性）**：存在严格降 rank 的证书 ⇒ 解链无环。 -/
theorem rank_acyclic {σ : Subst} {r : Lvl → Nat} (hr : RankOK σ r) : Acyclic σ := by
  intro a h
  have hlt := rank_decreases_path hr h
  exact Nat.lt_irrefl _ hlt

/-- 空替换以任意 rank 为证书。 -/
theorem rankOK_empty (r : Lvl → Nat) : RankOK [] r := by
  intro a w b lk _
  simp [Subst.lookup] at lk

/-- **T1（扩展保持）**：若证书 `r` 已把新解夹在中间（v 的浅层出现都低于 x，
    x 的前驱都高于 x），则 `extend σ x v` 仍以同一 `r` 为证书。 -/
theorem rankOK_extend {σ : Subst} {r : Lvl → Nat} {x : Lvl} {v : Val}
    (hσ : RankOK σ r)
    (hv : ∀ b : Lvl, OccursInR b v → r b < r x)
    (hpred : ∀ (y : Lvl) (w : Val), Subst.lookup σ y = some w → OccursInR x w → r x < r y) :
    RankOK (Subst.extend σ x v) r := by
  intro a w b lk occ
  by_cases hax : a = x
  · subst hax
    -- 新条目：lookup (x ↦ v) x = some v，故 w = v
    have hw : w = v := by
      have : Subst.lookup (Subst.extend σ a v) a = some v := by simp [Subst.extend]
      rw [this] at lk
      exact (Option.some.inj lk).symm
    subst hw
    exact hv b occ
  · -- 旧条目：lookup 穿透到 σ
    have hx : ¬ (x = a) := fun h => hax h.symm
    have hlk : Subst.lookup σ a = some w := by
      have hsame : Subst.lookup (Subst.extend σ x v) a = Subst.lookup σ a := by
        simp [Subst.extend, hx]
      rw [hsame] at lk
      exact lk
    exact hσ a w b hlk occ

/-- **T1（扩展后仍无环）**：证书健全性 + 扩展保持 ⇒ 扩展解不引入环。 -/
theorem extend_acyclic_of_rank {σ : Subst} {r : Lvl → Nat} {x : Lvl} {v : Val}
    (hσ : RankOK σ r)
    (hv : ∀ b : Lvl, OccursInR b v → r b < r x)
    (hpred : ∀ (y : Lvl) (w : Val), Subst.lookup σ y = some w → OccursInR x w → r x < r y) :
    Acyclic (Subst.extend σ x v) :=
  rank_acyclic (rankOK_extend hσ hv hpred)

/-! ## T1 主体：无环性的直接保持（路径分解）

不依赖 rank 构造：`Acyclic σ` + 「v 的浅层出现都不能沿 σ 回到 x」⇒ `extend σ x v`
仍无环。核心是 `path_extend_decomp`：`extend` 下的路径要么本来就是 σ 路径，要么
经过唯一的"新边" x → c（c 是 v 的某个浅层出现）。 -/

/-- 图模型版的 check：`v` 的某个浅层出现 `c` 在 σ 下可达 `x`（即新边会接回 x）。 -/
def OccursReach (σ : Subst) (x : Lvl) (v : Val) : Prop :=
  ∃ c : Lvl, OccursInR c v ∧ (c = x ∨ Path σ c x)

/-- 路径传递。 -/
theorem path_trans {σ : Subst} {a b c : Lvl} (h₁ : Path σ a b) (h₂ : Path σ b c) :
    Path σ a c := by
  induction h₁ with
  | single he => exact Path.trans he h₂
  | trans he _ ih => exact Path.trans he (ih h₂)

/-- 路径分解：`extend σ x v` 下的路径要么仍在 σ 下、要么经过新边（第三种形式给出
    "a = x 或 a 沿 σ 到 x" + "新边目标 c 在 v 中" + "c = b 或 c 沿 σ 到 b"）。 -/
theorem path_extend_decomp {σ : Subst} {x : Lvl} {v : Val} :
    ∀ {a b : Lvl}, Path (Subst.extend σ x v) a b →
      Path σ a b ∨ OccursReach σ x v ∨
        ∃ c : Lvl, (a = x ∨ Path σ a x) ∧ OccursInR c v ∧ (c = b ∨ Path σ c b) := by
  intro a b h
  -- 用带显式 motive 的递归子，避免 `induction` 把外层 σ/x/v 也泛化掉
  refine Path.rec (motive := fun a b _ =>
      Path σ a b ∨ OccursReach σ x v ∨
        ∃ c : Lvl, (a = x ∨ Path σ a x) ∧ OccursInR c v ∧ (c = b ∨ Path σ c b))
    ?_ ?_ h
  · -- single：当前边是 `extend` 下的一条边
    intro a b he
    rcases he with ⟨w, lk, occ⟩
    by_cases hax : a = x
    · -- a = x：新边 x → b（w = v）
      rw [hax] at lk
      have hw : w = v := by
        have : Subst.lookup (Subst.extend σ x v) x = some v := by simp [Subst.extend]
        rw [this] at lk
        exact (Option.some.inj lk).symm
      subst hw
      exact Or.inr (Or.inr ⟨b, Or.inl hax, occ, Or.inl rfl⟩)
    · have hx : ¬ (x = a) := fun h' => hax h'.symm
      have hlk : Subst.lookup σ a = some w := by
        have hsame : Subst.lookup (Subst.extend σ x v) a = Subst.lookup σ a := by
          simp [Subst.extend, hx]
        rw [hsame] at lk
        exact lk
      exact Or.inl (Path.single ⟨w, hlk, occ⟩)
  · -- trans：当前边 + 尾部路径（IH 是尾部的分解）
    intro a b c he h₂ ih
    rcases he with ⟨w, lk, occ⟩
    by_cases hax : a = x
    · -- 当前边是**新边**：a = x，w = v，occ : OccursInR b v
      rw [hax] at lk
      have hw : w = v := by
        have : Subst.lookup (Subst.extend σ x v) x = some v := by simp [Subst.extend]
        rw [this] at lk
        exact (Option.some.inj lk).symm
      subst hw
      rcases ih with hσ | hreach | ⟨d, hbpath, hdv, hdb⟩
      · exact Or.inr (Or.inr ⟨b, Or.inl hax, occ, Or.inr hσ⟩)
      · exact Or.inr (Or.inl hreach)
      · -- 尾部还经过新边：b 本身在 v 中且（b = x ∨ b 沿 σ 到 x）⇒ OccursReach
        exact Or.inr (Or.inl ⟨b, occ, hbpath⟩)
    · -- 当前边是旧边：Edge σ a b
      have hx : ¬ (x = a) := fun h' => hax h'.symm
      have hlk : Subst.lookup σ a = some w := by
        have hsame : Subst.lookup (Subst.extend σ x v) a = Subst.lookup σ a := by
          simp [Subst.extend, hx]
        rw [hsame] at lk
        exact lk
      rcases ih with hσ | hreach | ⟨d, hbpath, hdv, hdb⟩
      · exact Or.inl (Path.trans ⟨w, hlk, occ⟩ hσ)
      · exact Or.inr (Or.inl hreach)
      · -- 尾部第三种形式 + 旧边 ⇒ a 沿 σ 到 x
        have haxpath : a = x ∨ Path σ a x := by
          rcases hbpath with hbx | hbp
          · exact Or.inr (by simpa [hbx] using Path.single ⟨w, hlk, occ⟩)
          · exact Or.inr (path_trans (Path.single ⟨w, hlk, occ⟩) hbp)
        exact Or.inr (Or.inr ⟨d, haxpath, hdv, hdb⟩)

/-- **T1（无环性保持，主定理）**：σ 无环、且新解不会经 σ 回到 x
    （`¬ OccursReach σ x v`）⇒ 把 `x ↦ v` 加入 σ 仍无环。 -/
theorem extend_acyclic_of_no_reach {σ : Subst} {x : Lvl} {v : Val}
    (hac : Acyclic σ) (hchk : ¬ OccursReach σ x v) :
    Acyclic (Subst.extend σ x v) := by
  intro z hz
  rcases path_extend_decomp hz with hσ | hreach | ⟨c, haz, hcv, hcz⟩
  · exact hac z hσ
  · exact hchk hreach
  · have hcx : c = x ∨ Path σ c x := by
      rcases haz with hazx | hazpath
      · rcases hcz with hczc | hczpath
        · exact Or.inl (hczc.trans hazx)
        · exact Or.inr (by simpa [hazx] using hczpath)
      · rcases hcz with hczc | hczpath
        · exact Or.inr (by simpa [hczc] using hazpath)
        · exact Or.inr (path_trans hczpath hazpath)
    exact hchk ⟨c, hcv, hcx⟩

/-- 在无环 σ 下，**终点为 x 的 σ 路径**可以提升到 `extend σ x v`：路径不会以 x 为
    中间源（否则 σ 已在 x 上成环），而其余边在扩展下逐条保持。 -/
theorem path_to_x_lift {σ : Subst} {x : Lvl} {v : Val} (hac : Acyclic σ) {a : Lvl}
    (h : Path σ a x) : Path (Subst.extend σ x v) a x := by
  refine (Path.rec (motive := fun a b _ => b = x → Path (Subst.extend σ x v) a b) ?_ ?_ h) rfl
  · -- single
    intro a b he hb
    rw [hb] at he
    rw [hb]
    rcases he with ⟨w, lk, occ⟩
    by_cases hax : a = x
    · -- a = x 且终点 x ⇒ σ 已有环 x → x
      have hp : Path σ a a := by
        simpa [hax] using Path.single ⟨w, lk, occ⟩
      exact absurd hp (hac a)
    · have hx : ¬ (x = a) := fun h' => hax h'.symm
      have hlk : Subst.lookup (Subst.extend σ x v) a = some w := by
        have hsame : Subst.lookup (Subst.extend σ x v) a = Subst.lookup σ a := by
          simp [Subst.extend, hx]
        rw [hsame]
        exact lk
      exact Path.single ⟨w, hlk, occ⟩
  · -- trans
    intro a b c he h₂ ih hcx
    rw [hcx] at h₂
    rw [hcx]
    have h2lift : Path (Subst.extend σ x v) b x := by simpa [hcx] using ih hcx
    rcases he with ⟨w, lk, occ⟩
    by_cases hax : a = x
    · -- a = x 且终点 x ⇒ σ 已有环
      have hp : Path σ a a := by
        have hpath : Path σ a x := Path.trans ⟨w, lk, occ⟩ h₂
        simpa [hax] using hpath
      exact absurd hp (hac a)
    · have hx : ¬ (x = a) := fun h' => hax h'.symm
      have hlk : Subst.lookup (Subst.extend σ x v) a = some w := by
        have hsame : Subst.lookup (Subst.extend σ x v) a = Subst.lookup σ a := by
          simp [Subst.extend, hx]
        rw [hsame]
        exact lk
      exact Path.trans ⟨w, hlk, occ⟩ h2lift

/-- **T1（反向/必要性）**：若 `v` 的某个浅层出现沿 σ 能回到 `x`，则把 `x ↦ v`
    加入无环 σ 后**必然成环**（新边 x→c 与 c→…→x 构成环）。 -/
theorem extend_cyclic_of_occursReach {σ : Subst} {x : Lvl} {v : Val}
    (hac : Acyclic σ) (h : OccursReach σ x v) :
    ¬ Acyclic (Subst.extend σ x v) := by
  intro hac'
  rcases h with ⟨c, occ, hcx⟩
  -- 新边：x → c（解值 v 浅层出现 c）
  have hnew : Edge (Subst.extend σ x v) x c := by
    refine ⟨v, ?_, occ⟩
    simp [Subst.extend]
  have hcycle : Path (Subst.extend σ x v) x x := by
    rcases hcx with hcx | hcxpath
    · subst hcx
      exact Path.single hnew
    · exact Path.trans hnew (path_to_x_lift hac hcxpath)
  exact hac' x hcycle

/-- **T1（精确刻画）**：σ 无环时，`extend σ x v` 无环**当且仅当**新解不会经 σ
    回到 x（`¬ OccursReach σ x v`）。这是 `occurs_transitive` 检查在模型层的
    健全性 + 必要性。 -/
theorem extend_acyclic_iff_no_reach {σ : Subst} {x : Lvl} {v : Val} (hac : Acyclic σ) :
    Acyclic (Subst.extend σ x v) ↔ ¬ OccursReach σ x v :=
  ⟨fun hae hreach => extend_cyclic_of_occursReach hac hreach hae,
   fun hno => extend_acyclic_of_no_reach hac hno⟩

end Typort.Engine.Rank
