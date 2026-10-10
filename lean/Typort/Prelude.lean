/-
  `Typort.Prelude` — 仓库真实 prelude 的**签名**形式化。

  逐条对应（源文件在 `src/prelude/`）：

  * `Nat`     — `src/prelude/core/nat.typort:11-16`
               `enum Nat { zero  succ(n: Nat) }`
  * `Boolean` — `src/prelude/core/bool.typort:16-21`
               `enum Boolean { true  false }`
  * `Eq`      — `src/prelude/core/eq.typort:8-11`
               `enum Eq[A](x: A, y: A) { refl(a: A) -> Eq a a }`
               （**真归纳族**，不是 Leibniz 编码；`src/prelude/` 全仓唯一
               一处 `enum Eq`）
  * `Vec`     — `src/prelude/data/vec.typort:4-9`
               `enum Vec[A](len: Nat) { nil -> Vec[A] 0
                                         cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (l + 1) }`
               返回索引 `l + 1` 在形式化里写成 `succ l`（`nat_add` 按第二参数
               递归，`l + 1` 定义性归约为 `succ l`；仓库在 `nat.typort` 加载后
               进一步把 `+` 换成 u64 primop，见 `src/L13_namespace/mod.rs:4236`）。
  * `Void`    — `src/prelude/core/void.typort`：零构造子族（零臂 match 的宿主；
               `void.typort:1-7` 的 `absurd` 就是 `match v {}`）。

  **参数 vs 索引**按 icit 区分（`[A]` 隐式=参数，`(len : Nat)` 显式=索引），
  与 `docs/tt-spec-l07-l08.md` §1 一致。**构造子返回类型的参数位是族参数
  本身**，这正对应 Rust `check_ctor_wf`（`L07_sum_type/elaboration.rs:383-443`）
  的「Impl 参数槽必须是本 telescope 内的裸 rigid」条件。

  de Bruijn 约定：`IndDecl.params` / `indices` / `CtorDecl.tele` 均按**源码
  书写顺序**（外层在前）；`piTele` 折成 Π 链后，最内层 binder 的索引才是 0。
  因此例如 `Vec.cons` 的 `tele = [l, x, xs]` 在下文中索引为 `xs=0, x=1, l=2`。
-/

import Typort.Signature

namespace Typort
namespace Prelude

/-- `Nat` 在签名里的下标。 -/
def natIdx : Nat := 0
/-- `Boolean` 在签名里的下标。 -/
def boolIdx : Nat := 1
/-- `Eq` 在签名里的下标。 -/
def eqIdx : Nat := 2
/-- `Vec` 在签名里的下标。 -/
def vecIdx : Nat := 3
/-- `Void` 在签名里的下标。 -/
def voidIdx : Nat := 4

/-- `enum Nat { zero  succ(n: Nat) }`。 -/
def natDecl : IndDecl where
  name := "Nat"
  params := []
  indices := []
  level := 0
  ctors := [
    ⟨"zero", [], []⟩,
    ⟨"succ", [⟨"n", .expl, .ind natIdx⟩], []⟩]

/-- `enum Boolean { true  false }`。 -/
def boolDecl : IndDecl where
  name := "Boolean"
  params := []
  indices := []
  level := 0
  ctors := [⟨"true", [], []⟩, ⟨"false", [], []⟩]

/-- `enum Eq[A](x: A, y: A) { refl(a: A) -> Eq a a }`。
    telescope 约定：第 k 条绑定的类型在「params ++ 之前 k-1 条」中，故
    `y` 的类型里 `A` 是下标 1（`x` 占了下标 0）。 -/
def eqDecl : IndDecl where
  name := "Eq"
  params := [⟨"A", .impl, .u 0⟩]
  indices := [⟨"x", .expl, .var 0⟩, ⟨"y", .expl, .var 1⟩]
  level := 0
  ctors := [⟨"refl", [⟨"a", .expl, .var 0⟩], [.var 0, .var 0]⟩]

/-- `enum Vec[A](len: Nat) { nil -> Vec[A] 0
                              cons[l](x: A, xs: Vec[A] l) -> Vec[A] (l+1) }`。 -/
def vecDecl : IndDecl where
  name := "Vec"
  params := [⟨"A", .impl, .u 0⟩]
  indices := [⟨"len", .expl, .ind natIdx⟩]
  level := 0
  ctors := [
    ⟨"nil", [], [.ctor natIdx 0]⟩,
    ⟨"cons",
      [⟨"l", .expl, .ind natIdx⟩,
       ⟨"x", .expl, .var 1⟩,
       ⟨"xs", .expl, Tm.appAll (.ind vecIdx) [.var 2, .var 1]⟩],
      [Tm.appAll (.ctor natIdx 1) [.var 2]]⟩]

/-- `enum Void {}`（零构造子）。 -/
def voidDecl : IndDecl where
  name := "Void"
  params := []
  indices := []
  level := 0
  ctors := []

/-- 与仓库 `PRELUDE_CORE` 前缀同序的声明表
    （`src/L13_namespace/mod.rs:4095-4111` 的清单顺序：op → eq → nat → calc →
    bool → …；这里只收归纳族，故取 `nat`/`bool`/`eq`/`vec`/`void`）。 -/
def sig : Sig := [natDecl, boolDecl, eqDecl, vecDecl, voidDecl]

@[simp] theorem sig_length : sig.length = 5 := rfl

@[simp] theorem sig_lookup_nat : Sig.lookup sig natIdx = some natDecl := rfl
@[simp] theorem sig_lookup_bool : Sig.lookup sig boolIdx = some boolDecl := rfl
@[simp] theorem sig_lookup_eq : Sig.lookup sig eqIdx = some eqDecl := rfl
@[simp] theorem sig_lookup_vec : Sig.lookup sig vecIdx = some vecDecl := rfl
@[simp] theorem sig_lookup_void : Sig.lookup sig voidIdx = some voidDecl := rfl

end Prelude
end Typort
