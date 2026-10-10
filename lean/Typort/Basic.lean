/-
  `Typort.Basic` — 最底层的记法约定。

  与 Rust 的对应：

  * `Name`  — `src/L02_tyck/mod.rs:43` 的 `type Name = Span<SmolStr>`
    （形式化里丢掉源码位置，位置是诊断设施而非类型论的一部分）。
  * `Ix`    — `L02_tyck/mod.rs:26` `struct Ix(u32)`：de Bruijn **索引**。
  * `Lvl`   — `L02_tyck/mod.rs:29` `struct Lvl(u32)`：de Bruijn **层级**
    （`mod.rs` 的 `lvl`，quote/conv 的 `level`，L09 起同时是宇宙层级）。
  * `Icit`  — `L09_mltt/parser/syntax.rs` 的 `Icit::{Expl, Impl}`：
    显式 `(x : A)` / 隐式 `[x : A]` 绑定与应用的标记。
-/

namespace Typort

/-- binder 名。Rust：`Span<SmolStr>`（形式化里只保留字符串）。 -/
abbrev Name := String

/-- de Bruijn 索引。Rust：`Ix(u32)`。 -/
abbrev Ix := Nat

/-- de Bruijn 层级（也用作宇宙层级 `Type n` 的 `n`）。Rust：`Lvl(u32)`。 -/
abbrev Lvl := Nat

/-- 绑定/应用是显式还是隐式。Rust：`Icit::{Expl, Impl}`。 -/
inductive Icit where
  /-- `(x : A)` / `f a` -/
  | expl : Icit
  /-- `[x : A]` / `f [a]` -/
  | impl : Icit
  deriving DecidableEq, Repr

namespace Icit

def toString : Icit → String
  | .expl => "()"
  | .impl => "[]"

instance : ToString Icit := ⟨toString⟩

/-- 隐式标记翻转（`asSlave` 方向翻转等场景的通用工具）。 -/
def flip : Icit → Icit
  | .expl => .impl
  | .impl => .expl

end Icit

end Typort
