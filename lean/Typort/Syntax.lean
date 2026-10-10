/-
  `Typort.Syntax` — 核心语法（de Bruijn 索引项）。

  与 Rust 的对应：

  * `Tm` 对应各层的核心语法 `Tm`（`src/L02_tyck/mod.rs:47`
    `enum Tm { Var, Lam, App, U, Pi, Let }`）加上 L06 之后并入的
    常量/构造子/匹配（`src/L09_mltt/mod.rs` 的 `Tm` 变体
    `Var/U/Pi/Lam/App/Let/Sum/SumCase/Match/Proj/Prim`）。
  * 归纳族与构造子**常量**（`ind`/`ctor`）对应 L09 把 enum 本体与构造子
    经 `fake_bind`/`Cxt::define` 登记进值表后用名字引用（`L09_mltt/README.md`
    §2）：构造子是按 Π 类型当成函数被应用的，因此形式化里 `con` 不需要
    独立的「带实参列表」变体——应用统一走 `app`。
  * `matchE` 的第三参是臂链 `Arms`：对应 `Tm::Match(scrutinee, env, arms)`
    （`mod.rs:783`）。实现里的臂带模式（`PatternDetail`，先匹配先选），
    形式化在声明式层面取「按构造子下标选臂 + 把构造子实参喂给臂体」的
    标准 ι 规则；臂体写成 λ telescope（见 `Signature.ctorArmType`）。

  表示选择说明：形式化把 match 的 motive 显式写成 `Tm`（Agda 式消除子），
  实现里 motive 来自 `check` 的期望类型 + 索引精化（`pattern_match.rs`
  的 `check_pm_final`）；两者在声明式层面等价，差别记在 `lean/README.md`。
-/

import Typort.Basic

namespace Typort

mutual

  /-- 核心项。`Ix` 是 de Bruijn 索引（`var 0` = 最内层 binder）。 -/
  inductive Tm where
    /-- 变量（de Bruijn 索引）。Rust：`Tm::Var(Ix)`。 -/
    | var : Ix → Tm
    /-- 宇宙 `Type n`。Rust：`Tm::U(u32)`（L09 起带层级；L02 的裸 `U`
        是 `u 0` 的特殊情形）。 -/
    | u : Lvl → Tm
    /-- 依赖函数类型 `(x : A) → B`。Rust：`Tm::Pi(Name, Icit, A, B)`。 -/
    | pi : Icit → Tm → Tm → Tm
    /-- λ 抽象。Rust：`Tm::Lam(Name, Icit, body)`。 -/
    | lam : Icit → Tm → Tm
    /-- 应用。Rust：`Tm::App(Icit, f, a)`。 -/
    | app : Icit → Tm → Tm → Tm
    /-- `let x : A := t; u`。Rust：`Tm::Let(Name, A, t, u)`（类型槽只为
        打印/检查保留，求值时不看，见 `L02_tyck/mod.rs:101`）。 -/
    | letE : Tm → Tm → Tm → Tm
    /-- 归纳族常量 `D`。Rust：经 `fake_bind` 登记后以名字（哨兵下标
        `global_idx + 1919810`）引用的 enum 本体。 -/
    | ind : Nat → Tm
    /-- 构造子常量 `c`（族下标，构造子下标）。Rust：经 `Cxt::define`
        登记的构造子（`elaboration.rs:544`），按 Π 类型当函数应用。 -/
    | ctor : Nat → Nat → Tm
    /-- 依赖模式匹配：`match s { arms }`，motive 显式。Rust：`Tm::Match`。 -/
    | matchE : Tm → Tm → Arms → Tm

  /-- 臂链（构造子下标, 臂体）。臂体是 λ telescope（见 `Signature.ctorArmType`）。 -/
  inductive Arms where
    | nil : Arms
    | cons : Nat → Tm → Arms → Arms

end

namespace Tm

/-- 常量 `D` 应用到一串实参（左结合）。 -/
def appAll (f : Tm) (args : List Tm) : Tm :=
  args.foldl (fun acc a => .app .expl acc a) f

/-- 剥离 `app` 头，得到（头, 实参序列）。用于 ι 归约识别 `ctor` 头。 -/
def spine : Tm → Tm × List Tm
  | .app _ f a => let (h, args) := spine f; (h, args ++ [a])
  | t => (t, [])

/-- 剥离 `app` 头得到的实参个数。 -/
def spineArity (t : Tm) : Nat := (spine t).2.length

end Tm

namespace Arms

/-- 按构造子下标找臂体（先匹配先选）。 -/
def find? : Arms → Nat → Option Tm
  | .nil, _ => none
  | .cons c b rest, c' => if c = c' then some b else find? rest c'

/-- 臂链中出现的构造子下标（按书写顺序）。 -/
def indices : Arms → List Nat
  | .nil => []
  | .cons c _ rest => c :: indices rest

/-- 臂链长度。 -/
def length : Arms → Nat
  | .nil => 0
  | .cons _ _ rest => length rest + 1

end Arms

/-- 上下文中的一条绑定。 -/
structure Binder where
  /-- binder 名（只用于显示）。 -/
  name : Name
  /-- 显式/隐式。 -/
  icit : Icit
  /-- 类型（在「外层上下文 ++ 该 binder 之前的 binder」中）。 -/
  type : Tm

/-- 类型检查上下文（头 = 最内层 binder，`var 0` 取头部）。Rust：`Cxt.types`
    / `Infer.global` + `Locals` 的拼接（`L09_mltt/cxt.rs`）。 -/
abbrev Ctx := List Binder

namespace Ctx

/-- 追加一层绑定（新 binder 成为下标 0）。 -/
def extend (Γ : Ctx) (b : Binder) : Ctx := b :: Γ

/-- 查找第 `i` 条绑定（结构递归定义，便于随后的归纳证明）。 -/
def lookup : Ctx → Ix → Option Binder
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: rest, i + 1 => lookup rest i

@[simp] theorem lookup_nil (i : Ix) : lookup [] i = none := by cases i <;> rfl

@[simp] theorem lookup_zero (Γ : Ctx) (b : Binder) : lookup (b :: Γ) 0 = some b := rfl

@[simp] theorem lookup_succ (Γ : Ctx) (b : Binder) (i : Ix) :
    lookup (b :: Γ) (i + 1) = lookup Γ i := rfl

end Ctx

/-- 把 telescope 折成 Π 链：`(b₁ : A₁) → … → (bₙ : Aₙ) → body`。
    `telescope` 的顺序是「从外到内」，每条的 `type` 在前面的 binder 可见。 -/
def piTele : List Binder → Tm → Tm
  | [], body => body
  | b :: rest, body => .pi b.icit b.type (piTele rest body)

/-- 长度为 `n` 的 telescope 对应的「变量列表」，按 telescope 书写顺序
    （第 j 条 binder 的 de Bruijn 下标是 `n-1-j`）。 -/
def teleVars (n : Nat) : List Tm :=
  (List.range n).map (fun j => .var (n - 1 - j))

/-- 把 `telescope` 折成 λ 链（臂体的书写形式）。 -/
def lamTele : List Binder → Tm → Tm
  | [], body => body
  | b :: rest, body => .lam b.icit (lamTele rest body)

end Typort
