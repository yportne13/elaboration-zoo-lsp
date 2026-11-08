/-
  `TyportEngine` — L07/L08 参考引擎（值层/显式替换/occurs/unify 判据/结构相等/预算）
  的 Lean 4 形式化（M1）。

  与声明层的 `Typort` 库分开：`Typort` 是类型论骨架（8 模块/57 定理），本库专注
  **elaborator 引擎**的算法语义与不变式（2026-11-08 review 修复轮后新增）。

  当前覆盖（逐轮扩展）：
  * `Typort.Engine.Basic`   —— `Val`/`Subst`/`lookup`/`compose`/`children`
  * `Typort.Engine.Occurs`  —— 组合语义 `Mentions` vs R2 旧算法 `MentionsInner`，
    以及 R2 的机器检查反例（漏检 → 接受循环解）

  构建：
  ```powershell
  $L = "$env:USERPROFILE\.lean4-toolchain\lean\lean-4.34.1-windows"
  $env:PATH = "$L\bin;$env:PATH"
  Set-Location lean
  lake build TyportEngine
  ```
-/
import Typort.Engine.Basic
import Typort.Engine.Occurs
import Typort.Engine.Rank
import Typort.Engine.Budget
import Typort.Engine.Classify
import Typort.Engine.StructEq
import Typort.Engine.Oracle
