/-
  `Typort.Signature` — 归纳族签名与由签名计算出的各种类型。

  与 Rust 的对应：

  * `IndDecl` / `CtorDecl` 对应 `enum` 声明及其构造子；Rust 侧声明在
    `L07_sum_type/elaboration.rs:268-365`（L08/L09/L13 同族）：
    族本体类型 = `Π params → Type universe_lvl`，构造子类型 =
    `Π(族隐式参数) → Π(构造子绑定器) → ret`。
  * **参数 vs 索引**：Rust 用 icit 区分——`[A]`（隐式，参数，使用点自动
    插入）与 `(len : Nat)`（显式，索引，由返回类型方程解出）
    （`docs/tt-spec-l07-l08.md` §1）。形式化里 `IndDecl.params` 与
    `IndDecl.indices` 分别对应两者。
  * **构造子良构性**（Rust `check_ctor_wf`，`L07/elaboration.rs:383-443`）：
    返回类型必须是本族；返回 Sum 的每个 **Impl 参数槽** 必须是构造子
    telescope 内的裸 rigid 变量（参数不得特化）。形式化把它编码成
    `CtorDecl.ctorType` 的构造方式：返回类型的参数位**就是**族参数
    （`params`，以 Π 绑定的裸变量出现），因此该条件在表示层即被强制。
    显式索引位不受限（`CtorDecl.retIndices` 可以是任意项）。
  * `CtorDecl.retIndices` 对应 Rust 构造子 `check_ctor_wf` 第二步里
    `force(ret)` 得到的 Sum 的索引实参。
  * `motiveType` / `armType` 对应 Rust 匹配编译器的「期望类型 + 索引方程
    精化」（`L07/pattern_match.rs:350-396` 的 `unify_indices` 与臂体
    `check`）：形式化取 Agda 式**显式 motive** 的表述，差异见
    `lean/README.md`。
-/

import Typort.Subst

namespace Typort

/-- 列表中第 `n` 个元素（Lean 4.34 core 无 `List.get?`，故自带一个）。 -/
def getAt? : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: rest, n + 1 => getAt? rest n

@[simp] theorem getAt?_nil (n : Nat) : getAt? ([] : List α) n = none := by
  cases n <;> rfl

@[simp] theorem getAt?_cons_zero (a : α) (l : List α) : getAt? (a :: l) 0 = some a := rfl

@[simp] theorem getAt?_cons_succ (a : α) (l : List α) (n : Nat) :
    getAt? (a :: l) (n + 1) = getAt? l n := rfl

theorem getAt?_isSome {l : List α} {n : Nat} {a : α} (h : getAt? l n = some a) :
    l.length > n := by
  induction l generalizing n with
  | nil => cases n <;> simp at h
  | cons b l ih =>
      cases n with
      | zero => simp
      | succ m => simpa using ih h

-- ===========================================================================
-- 上下文截断（变量规则里「绑定的类型在其尾部上下文中是类型」用得到）
-- ===========================================================================

namespace Ctx

/-- 去掉最外层的 `n` 条绑定。 -/
def drop : Ctx → Nat → Ctx
  | [], _ => []
  | Γ, 0 => Γ
  | _ :: rest, n + 1 => drop rest n

@[simp] theorem drop_zero (Γ : Ctx) : drop Γ 0 = Γ := by
  cases Γ <;> rfl

@[simp] theorem drop_cons_succ (b : Binder) (Γ : Ctx) (n : Nat) :
    drop (b :: Γ) (n + 1) = drop Γ n := rfl

theorem drop_one_cons (b : Binder) (Γ : Ctx) : drop (b :: Γ) 1 = Γ := by
  simp [drop]

theorem drop_nil (n : Nat) : drop ([] : Ctx) n = [] := by
  cases n <;> rfl

end Ctx

-- ===========================================================================
-- 声明与签名
-- ===========================================================================

/-- 构造子声明。 -/
structure CtorDecl where
  /-- 构造子名（只用于显示）。 -/
  name : Name
  /-- 构造子自己的 telescope，类型在 `族参数 ++ 之前的字段` 中。 -/
  tele : List Binder
  /-- 返回类型的**索引**实参，在 `族参数 ++ tele` 中。
      返回类型的**参数**位固定为族参数本身（对应 `check_ctor_wf` 的
      「Impl 参数槽必须是本 telescope 内的裸 rigid」条件）。 -/
  retIndices : List Tm

/-- 归纳族声明（`enum`）。 -/
structure IndDecl where
  /-- 族名（只用于显示）。 -/
  name : Name
  /-- 参数 telescope（`[A]`），类型在外层上下文中。 -/
  params : List Binder
  /-- 索引 telescope（`(len : Nat)`），类型在 `params` 中。 -/
  indices : List Binder
  /-- 本体所在的宇宙层级：族本体 `: Type level`。Rust：`universe_lvl`。 -/
  level : Lvl
  /-- 构造子表（下标即构造子编号，与 Rust 的构造子名一一对应）。 -/
  ctors : List CtorDecl

/-- 声明签名（全局声明表）。Rust：`Infer.global` / `global_names` 的项层投影。 -/
abbrev Sig := List IndDecl

namespace IndDecl

/-- 在 `params ++ tele` 上下文里，参数变量的 de Bruijn 项（按 telescope 书写顺序）。 -/
def paramVars (p k : Nat) : List Tm := (teleVars p).map (shiftN k)

/-- 族常量 `.ind di` 应用到一族实参。 -/
def app (di : Nat) (args : List Tm) : Tm := Tm.appAll (.ind di) args

/-- 族常量的类型（空上下文中的闭项）：`(params) → (indices) → Type level`。 -/
def type (D : IndDecl) : Tm := piTele D.params (piTele D.indices (.u D.level))

/-- 构造子常量的类型（空上下文中的闭项）：
    `(params) → (tele) → D params retIndices`。
    返回类型里的参数位是 Π 绑定的族参数（裸变量），索引位是 `retIndices`。 -/
def ctorType (D : IndDecl) (di : Nat) (_ci : Nat) (c : CtorDecl) : Tm :=
  piTele D.params (piTele c.tele
    (Tm.appAll (.ind di) (paramVars D.params.length c.tele.length ++ c.retIndices)))

/-- motive 的「未替换」形态（在族参数上下文中）：
    `(indices) → D params indexVars → Type l`。 -/
def motiveIn (D : IndDecl) (di : Nat) (l : Lvl) : Tm :=
  piTele D.indices
    (.pi .expl
      (Tm.appAll (.ind di)
        (paramVars D.params.length D.indices.length ++ teleVars D.indices.length))
      (.u l))

/-- 把「族参数上下文」中的参数变量替换为使用点的实际参数（按书写顺序给出）。 -/
def paramSub (p : Nat) (ps : List Tm) : Sub := fun j =>
  match getAt? ps (p - 1 - j) with
  | some t => t
  | none => .var j

/-- 使用点上的 motive 类型：`(indices) → D ps indexVars → Type l`。 -/
def motiveType (D : IndDecl) (di : Nat) (ps : List Tm) (l : Lvl) : Tm :=
  subst (paramSub D.params.length ps) (motiveIn D di l)

/-- 某构造子某条臂的期望类型（臂体写成 λ telescope 后的类型）：
    `(tele) → P retIndices (ctor D ci 应用到参数与 tele 变量)`，
    其中族参数已替换为使用点的实际参数。 -/
def armType (D : IndDecl) (di ci : Nat) (c : CtorDecl) (ps : List Tm) (P : Tm) : Tm :=
  subst (paramSub D.params.length ps)
    (piTele c.tele
      (Tm.appAll P
        (c.retIndices ++
          [Tm.appAll (.ctor di ci)
            (paramVars D.params.length c.tele.length ++ teleVars c.tele.length)])))

end IndDecl

namespace Sig

/-- 查第 `di` 个族声明。 -/
def lookup (S : Sig) (di : Nat) : Option IndDecl := getAt? S di

/-- 查第 `di` 个族的第 `ci` 个构造子。 -/
def ctor? (S : Sig) (di ci : Nat) : Option (IndDecl × CtorDecl) :=
  match lookup S di with
  | none => none
  | some D => match getAt? D.ctors ci with
    | none => none
    | some c => some (D, c)

end Sig

-- ===========================================================================
-- 臂链：覆盖与查找
-- ===========================================================================

namespace Arms

/-- 臂链中是否存在构造子下标 `i` 的臂（对应 Rust 的 `covers`）。 -/
def HasCtor : Arms → Nat → Prop
  | .nil, _ => False
  | .cons c _ rest, i => c = i ∨ HasCtor rest i

/-- 覆盖性：所有 `numCtors` 个构造子都有臂。
    Rust：`pattern_match.rs` 的顶层覆盖检查（`Unreachable`/`Unmatched`）。 -/
def Covers (numCtors : Nat) (arms : Arms) : Prop := ∀ i, i < numCtors → arms.HasCtor i

theorem find?_isSome_of_hasCtor : (arms : Arms) → (i : Nat) → arms.HasCtor i →
    ∃ b, arms.find? i = some b
  | .nil, _, h => by simp [HasCtor] at h
  | .cons c b rest, i, h => by
      by_cases hc : c = i
      · exact ⟨b, by simp [find?, hc]⟩
      · rcases h with h | h
        · exact absurd h hc
        · obtain ⟨b', hb'⟩ := find?_isSome_of_hasCtor rest i h
          exact ⟨b', by simp [find?, hc, hb']⟩

end Arms

end Typort
