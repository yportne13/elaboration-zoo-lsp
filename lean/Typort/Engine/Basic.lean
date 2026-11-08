/-
  `Typort.Engine.Basic` — L07/L08 参考引擎的**值层与显式替换**的抽象模型
  （2026-11-08 review 修复轮后新增，M1 形式化地基）。

  与 Rust 的对应：

  * `Val` ≈ `src/L07_sum_type/mod.rs` 的 `Val`（14 变体）。本抽象保留发生检查/
    结构相等/分类器需要的结构：`Rigid`、`Sum`/`SumCase`、`Lam`/`Pi`（只保留
    env 槽，闭包体不参与 occurs）、`Match`（scrutinee/env/pending）、`VSub`、
    `Flex/Decl/Prim/Obj`、`U/LiteralType/LiteralIntro`。
    **抽象边界**：省略 spine 的应用语义（`v_app`/β）与闭包体；见 `lean/README.md`
    「M1 抽象边界」。这足以形式化 R2 反例（其最小反例是空 spine 的 `Rigid`）。
  * `Subst` ≈ `src/L07_sum_type/mod.rs` 的 `Subst`：持久化单链，链头最新；
    `lookup` 取首个命中（对齐 `Subst::lookup_hit` 的"取最新"）。
  * `compose outer inner` = outer 的条目在前（先被查到）、后接 inner
    （对齐 `Subst::compose` 的"内层先应用、外层后应用"与链头覆盖）。
-/

import Typort.Basic

namespace Typort.Engine

/-- L07 值层的抽象片段。

    不在抽象内的部分（见 `lean/README.md`）：spine 的应用/β、闭包 Tm 体、
    meta 表（`Flex` 只作为中性头参与结构比较）、prim 归约、fuel。 -/
inductive Val where
  /-- 刚性变量（层级）。Rust：`Val::Rigid(Lvl, Spine)`。 -/
  | rigid (l : Lvl) : Val
  /-- 和类型头（族名 + 参数 + 构造子名表）。Rust：`Val::Sum`。 -/
  | sum (name : Name) (params : List (Name × Val × Val × Icit)) (cases : List Name) : Val
  /-- 构造子值（构造子名 + 实例化类型 + 字段）。Rust：`Val::SumCase`。 -/
  | sumCase (name : Name) (typ : Val) (datas : List (Name × Val × Icit)) : Val
  /-- 宇宙。Rust：`Val::U`。 -/
  | u (l : Lvl) : Val
  /-- `String` 字面量类型。Rust：`Val::LiteralType`。 -/
  | litTy : Val
  /-- 字面量值。Rust：`Val::LiteralIntro(Span<String>)`。 -/
  | lit (s : String) : Val
  /-- λ 闭包（只保留 env 槽；体不参与发生检查）。Rust：`Val::Lam`。 -/
  | lam (ic : Icit) (env : List Val) : Val
  /-- Π 类型（定义域 + 余定义域闭包 env）。Rust：`Val::Pi`。 -/
  | pi (ic : Icit) (dom : Val) (env : List Val) : Val
  /-- 元变量（中性头；只保留可见实参）。Rust：`Val::Flex`。 -/
  | flex (m : Nat) (sp : List Val) : Val
  /-- 卡住的 def 头。Rust：`Val::Decl`。 -/
  | decl (name : Name) (sp : List Val) : Val
  /-- 卡住的内建头。Rust：`Val::Prim`。 -/
  | prim (name : Name) (sp : List Val) : Val
  /-- 卡住的投影。Rust：`Val::Obj`。 -/
  | obj (v : Val) (name : Name) (sp : List Val) : Val
  /-- 卡住的 match：scrutinee + 捕获 env + pending 实参。Rust：`Val::Match`。 -/
  | matchV (s : Val) (env : List Val) (pending : List Val) : Val
  /-- 显式替换包裹。Rust：`Val::VSub(Box<Val>, Rc<Subst>)`。 -/
  | vsub (v : Val) (sub : List (Lvl × Val)) : Val

/-- 持久化单链替换：链头最新；`lookup` 从链头找首个命中（对齐 Rust
    `Subst::lookup_hit`：同键旧条目被新条目覆盖）。 -/
abbrev Subst := List (Lvl × Val)

namespace Subst

/-- 查解：首个命中即最新解；未命中 = 未解。 -/
def lookup : Subst → Lvl → Option Val
  | [], _ => none
  | (y, v) :: rest, x => if y = x then some v else lookup rest x

/-- `lookup` 在 cons 上的展开（simp 用；配合具体 Nat 的 decidable 判等即可
    把具体表上的 lookup 归约掉）。 -/
@[simp] theorem lookup_cons (y : Lvl) (v : Val) (rest : Subst) (x : Lvl) :
    lookup ((y, v) :: rest) x = if y = x then some v else lookup rest x := rfl

@[simp] theorem lookup_nil (x : Lvl) : lookup [] x = none := rfl

@[simp] theorem lookup_cons_self (y : Lvl) (v : Val) (rest : Subst) :
    lookup ((y, v) :: rest) y = some v := by
  simp [lookup]

theorem lookup_cons_other {y x : Lvl} (h : y ≠ x) (v : Val) (rest : Subst) :
    lookup ((y, v) :: rest) x = lookup rest x := by
  simp [lookup, h]

/-- 空替换。Rust：`Subst::default()`。 -/
def empty : Subst := []

/-- 叠加一条解到链头（O(1)）。Rust：`Subst::extend`。 -/
def extend (σ : Subst) (x : Lvl) (v : Val) : Subst := (x, v) :: σ

/-- 组合：`compose outer inner` 把 outer 的条目放在链头（先被查到），后接
    inner——对齐 Rust `Subst::compose`（"内层先应用、外层后应用"，满足
    `lookup (compose outer inner) x ≈ lookup outer x <|> lookup inner x` 的链头优先语义）。 -/
def compose (outer inner : Subst) : Subst := outer ++ inner

@[simp] theorem lookup_compose_empty_right (σ : Subst) (x : Lvl) :
    lookup (compose σ []) x = lookup σ x := by
  simp [compose]

end Subst

/-- 值的一层子值（发生检查/结构比较的遍历面；不含闭包体与大于一层的结构）。 -/
def Val.children : Val → List Val
  | .rigid _ => []
  | .sum _ ps _ => ps.flatMap fun (_, v, t, _) => [v, t]
  | .sumCase _ typ ds => typ :: ds.flatMap fun (_, v, _) => [v]
  | .u _ => []
  | .litTy => []
  | .lit _ => []
  | .lam _ env => env
  | .pi _ dom env => dom :: env
  | .flex _ sp => sp
  | .decl _ sp => sp
  | .prim _ sp => sp
  | .obj v _ sp => v :: sp
  | .matchV s env pending => s :: (env ++ pending)
  | .vsub _ _ => []

end Typort.Engine
