/-
  Typort 类型论的形式化（Lean 4.34.1）。

  本库把仓库 `elaboration-zoo-lsp`（Rust）各层实现的类型论抽取成一个自足的
  演算，并给出可编译的定义与已证明的引理。模块与 Rust 章节的对应、覆盖范围
  与已知边界见 `lean/README.md`。

  依赖：仅 Lean 4 core / Std（无 Mathlib）。
-/
import Typort.Basic
import Typort.Syntax
import Typort.Subst
import Typort.Conversion
import Typort.Signature
import Typort.Typing
import Typort.Prelude
import Typort.Examples
