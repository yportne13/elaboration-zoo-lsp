/-
  `Typort.Typing` — 声明式判型（对应 Rust 的双向 `check`/`infer` 走廊）。

  规则与 Rust 的对应：

  * `u`      `Type n : Type (n+1)`，**非累积**（无 `Type n <: Type (n+1)`）。
             Rust：`L09_mltt/elaboration.rs:822`
             `infer_expr(U n) = (Tm::U n, Val::U (n+1))`；`unify` 只有
             `(U x, U y) if x == y`（`unification.rs:569`）。
  * `pi`     层级取 `max`（Rust：`infer_expr(Pi) → max(check_universe 域,
             check_universe 余域) : Val::U max`）。
  * `lam`    只在期望类型是 Π 时可检查（Rust `check` 的 λ 臂）；形式化写作
             「由 Π 给出定义域」的规则。
  * `app`    `f : (x : A) → B`、`a : A` 推出 `f a : B[x := a]`；Rust 的 `App`
             先 `insert` 隐式实参再 `check(u, a)`，结果类型 `cl(eval u')`。
  * `letE`   ζ：Rust `check` 的 `Let` 臂 + `eval` 的 `Let` 臂（`mod.rs:101`）。
  * `ind` / `ctor`：族常量与构造子常量的类型来自签名；Rust 侧二者以
             `fake_bind`/`define_global` 登记后按 Π 类型当函数应用
             （`L09_mltt/README.md` §2、`elaboration.rs:503-529`）。
  * `matchE` 依赖消去：显式 motive + 逐构造子 λ telescope 臂 + 覆盖性前提。
             与实现的差别（实现用「索引方程 + 上下文精化」而非显式 motive，
             因而接受更强的程序，例如 prelude 里字面写法的 `trans`/`subst`）
             见 `lean/README.md`。
  * `convTy` 类型上的转换规则：Rust `check` 兜底 `unify_catch(expected,
             inferred)`。
  * 变量规则里额外的 `HasType S (Ctx.drop Γ (i+1)) b.type (.u l)` 前提表示
    「绑定的类型在其自身上下文中是类型」：它保证不能靠畸形上下文凭空判型，
    同时让 `HasType` 保持**非互归纳**——Lean 4 的 `induction` 对互归纳类型
    不可用，而元定理必须对判型推导做归纳。
-/

import Typort.Conversion
import Typort.Signature

namespace Typort

/-- 判型（声明式）。`S` 是全局声明签名。 -/
inductive HasType (S : Sig) : Ctx → Tm → Tm → Prop where
  /-- 变量：绑定的类型必须在其尾部上下文中是类型。 -/
  | var {Γ : Ctx} {i : Ix} {b : Binder} {l : Lvl} :
      Ctx.lookup Γ i = some b →
      HasType S (Ctx.drop Γ (i + 1)) b.type (.u l) →
      HasType S Γ (.var i) (shiftN (i + 1) b.type)
  /-- `Type n : Type (n+1)`（非累积）。 -/
  | u {Γ : Ctx} {n : Lvl} :
      HasType S Γ (.u n) (.u (n + 1))
  /-- Π 形成：层级取 max。 -/
  | pi {Γ : Ctx} {x : Name} {ic : Icit} {A B : Tm} {l₁ l₂ : Lvl} :
      HasType S Γ A (.u l₁) →
      HasType S (⟨x, ic, A⟩ :: Γ) B (.u l₂) →
      HasType S Γ (.pi ic A B) (.u (max l₁ l₂))
  /-- Π 引入。 -/
  | lam {Γ : Ctx} {x : Name} {ic : Icit} {A B t : Tm} {l : Lvl} :
      HasType S Γ A (.u l) →
      HasType S (⟨x, ic, A⟩ :: Γ) t B →
      HasType S Γ (.lam ic t) (.pi ic A B)
  /-- Π 消去（应用）。 -/
  | app {Γ : Ctx} {ic : Icit} {f a A B : Tm} :
      HasType S Γ f (.pi ic A B) →
      HasType S Γ a A →
      HasType S Γ (.app ic f a) (subst0 a B)
  /-- let。 -/
  | letE {Γ : Ctx} {x : Name} {A t u B : Tm} {l : Lvl} :
      HasType S Γ A (.u l) →
      HasType S Γ t A →
      HasType S (⟨x, .expl, A⟩ :: Γ) u B →
      HasType S Γ (.letE A t u) (subst0 t B)
  /-- 归纳族常量。 -/
  | ind {Γ : Ctx} {di : Nat} {D : IndDecl} :
      Sig.lookup S di = some D →
      HasType S Γ (.ind di) (shiftN Γ.length D.type)
  /-- 构造子常量（按 Π 类型当函数应用）。 -/
  | ctor {Γ : Ctx} {di ci : Nat} {D : IndDecl} {c : CtorDecl} :
      Sig.ctor? S di ci = some (D, c) →
      HasType S Γ (.ctor di ci) (shiftN Γ.length (D.ctorType di ci c))
  /-- 依赖消去（match）。motive 显式；臂写成 λ telescope，覆盖性由 `Covers` 要求。 -/
  | matchE {Γ : Ctx} {di : Nat} {D : IndDecl} {s P : Tm} {ps is : List Tm}
      {l : Lvl} {arms : Arms} :
      Sig.lookup S di = some D →
      HasType S Γ s (IndDecl.app di (ps ++ is)) →
      HasType S Γ P (D.motiveType di ps l) →
      Arms.Covers D.ctors.length arms →
      (∀ ci b, arms.find? ci = some b → ∀ c, getAt? D.ctors ci = some c →
          HasType S Γ b (D.armType di ci c ps P)) →
      HasType S Γ (.matchE s P arms) (Tm.appAll P (is ++ [s]))
  /-- 类型上的转换（Rust `check` 兜底 `unify_catch(expected, inferred)`）。 -/
  | convTy {Γ : Ctx} {t A B : Tm} {l : Lvl} :
      HasType S Γ t A →
      Conv A B →
      HasType S Γ B (.u l) →
      HasType S Γ t B

/-- 上下文良构。Rust：`Cxt` 的不变式 `env.len() == lvl == pruning.len()`
    （`L09_mltt/cxt.rs`）。 -/
inductive WF (S : Sig) : Ctx → Prop where
  | nil : WF S []
  | cons {Γ : Ctx} {b : Binder} {l : Lvl} :
      WF S Γ → HasType S Γ b.type (.u l) → WF S (b :: Γ)

/-- `A` 在 `Γ` 中是层级 `l` 的类型。 -/
def IsType (S : Sig) (Γ : Ctx) (A : Tm) (l : Lvl) : Prop := HasType S Γ A (.u l)

namespace WF

/-- 由构造规则的上下文扩展直接得到良构。 -/
theorem extend {S : Sig} {Γ : Ctx} {b : Binder} {l : Lvl}
    (hwf : WF S Γ) (h : HasType S Γ b.type (.u l)) : WF S (b :: Γ) :=
  .cons hwf h

end WF

-- ===========================================================================
-- 平移/替换的小引理（为元定理准备，均已证明）
-- ===========================================================================

@[simp] theorem shiftN_zero (t : Tm) : shiftN 0 t = t := by
  unfold shiftN
  rw [show (fun i => i + 0) = (fun i => i) from by funext i; rfl]
  exact ren_id t

/-- 平移的分解：`+(k+1)` 等于「先 `+k` 再 `+1`」。 -/
theorem shiftN_succ (k : Nat) (t : Tm) : shiftN (k + 1) t = shiftN 1 (shiftN k t) := by
  unfold shiftN
  have h : ren (fun i => i + 1) (ren (fun i => i + k) t) = ren (fun i => i + (k + 1)) t := by
    rw [ren_ren]
    exact congrArg (fun ξ => ren ξ t) (by funext i; exact Nat.add_assoc i k 1)
  exact h.symm

/-- `lift = shiftN 1`。 -/
theorem lift_eq_shiftN_one (t : Tm) : lift t = shiftN 1 t := rfl

/-- `ren (ext ρ)` 与「平移 1」交换。 -/
theorem ren_ext_shiftN_one (ρ : Ren) (t : Tm) :
    ren (ext ρ) (shiftN 1 t) = shiftN 1 (ren ρ t) := by
  unfold shiftN
  rw [ren_ren, ren_ren]
  exact congrArg (fun ξ => ren ξ t) (by funext i; rfl)

/-- `shiftN 1` 与 `subst` 的交换：两边的出现位置由 `extS` 对齐。 -/
theorem shiftN_one_subst (σ : Sub) (A : Tm) :
    shiftN 1 (subst σ A) = subst (extS σ) (shiftN 1 A) := by
  unfold shiftN
  rw [ren_subst, subst_ren]
  rfl

/-- `ren` 在 `appAll` 上的分布。 -/
theorem ren_appAll (ρ : Ren) (f : Tm) (args : List Tm) :
    ren ρ (Tm.appAll f args) = Tm.appAll (ren ρ f) (args.map (ren ρ)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a rest ih =>
      rw [show Tm.appAll f (a :: rest) = Tm.appAll (Tm.app .expl f a) rest from rfl]
      rw [ih]
      rfl

/-- 臂链重命名不改变构造子下标，体按同一重命名改写（`find?` 层面）。 -/
theorem Arms.find?_renArms (ρ : Ren) : (arms : Arms) → (ci : Nat) →
    (renArms ρ arms).find? ci = (arms.find? ci).map (ren ρ)
  | .nil, _ => rfl
  | .cons c b rest, ci => by
      simp only [renArms, Arms.find?]
      by_cases hc : c = ci
      · simp only [hc, ↓reduceIte]
        rfl
      · simp only [hc, ↓reduceIte]
        rw [Arms.find?_renArms ρ rest ci]

/-- 重命名保持覆盖性。 -/
theorem Arms.hasCtor_renArms (ρ : Ren) : (arms : Arms) → (i : Nat) →
    arms.HasCtor i → (renArms ρ arms).HasCtor i
  | .nil, _, h => by simp [Arms.HasCtor] at h
  | .cons c b rest, i, h => by
      rcases h with h | h
      · simp only [renArms, Arms.HasCtor]
        exact Or.inl h
      · simp only [renArms, Arms.HasCtor]
        exact Or.inr (Arms.hasCtor_renArms ρ rest i h)

end Typort
