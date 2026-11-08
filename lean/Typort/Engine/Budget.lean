/-
  `Typort.Engine.Budget` — 卡住 match 相等性比较预算的**代理维度**抽象
  （2026-11-08 review R3/R8）。

  历史背景（review R3）：修复轮之前，参考版预算是「递归深度 40、结构快路径
  之前检查」，孪生版是「单次 `unify_iter` 内命中总次数 64、快路径之后计数」。
  两者**不是同一维度的代理**，因此可以构造双向判定漂移：

  * 宽而浅：70 个兄弟比较、深度 2 ⇒ 深度口径通过（2 ≤ 40），次数口径拒绝（70 > 64）；
  * 深而合法：50 层嵌套比较 ⇒ 深度口径拒绝（50 > 40），次数口径通过（50 ≤ 64）。

  本模块把上述结论机检化：`r3_metrics_not_equivalent` 证明两个代理互不蕴含。
  修复方向（已落地于 Rust 实现）：两侧统一为「总次数 64 / 每顶层合一入口 /
  结构快路径之后计数」，即本模块的 `countBounded` 口径。

  抽象边界：`CmpTree` 只建模比较的**形状**（嵌套/兄弟），不建模每次比较的
  实际代价；Rust 侧见 `src/L07_sum_type/mod.rs` 的 `MATCH_CMP_BUDGET` 与
  `docs/review-l07-hardening-2026-11-08/FINAL.md` R3。
-/

import Typort.Basic

namespace Typort.Engine.Budget

set_option maxRecDepth 100000

/-- 一次卡住 match 相等性比较的抽象形状：叶子一次比较，节点把若干子比较
    组合起来（兄弟比较是同一节点的多个 child，嵌套比较是单 child 链）。 -/
inductive CmpTree where
  | leaf : CmpTree
  | node (children : List CmpTree) : CmpTree

mutual
  /-- 递归深度（参考版修复前的代理维度，上限 40）。 -/
  def depth : CmpTree → Nat
    | .leaf => 1
    | .node cs => 1 + depthList cs

  def depthList : List CmpTree → Nat
    | [] => 0
    | c :: rest => max (depth c) (depthList rest)
end

mutual
  /-- 节点总数（孪生版 / 修复后参考版的代理维度，上限 64）。 -/
  def size : CmpTree → Nat
    | .leaf => 1
    | .node cs => 1 + sizeList cs

  def sizeList : List CmpTree → Nat
    | [] => 0
    | c :: rest => size c + sizeList rest
end

/-- 参考版修复前口径：递归深度 ≤ 40。 -/
def depthBounded (t : CmpTree) : Bool := depth t ≤ 40

/-- 孪生版 / 修复后口径：总次数 ≤ 64。 -/
def countBounded (t : CmpTree) : Bool := size t ≤ 64

/-- 70 个叶子的兄弟列表（显式结构递归，保证 kernel 可归约）。 -/
def nLeaves : Nat → List CmpTree
  | 0 => []
  | n + 1 => .leaf :: nLeaves n

/-- `n` 层嵌套（单 child 链）。 -/
def nest : Nat → CmpTree
  | 0 => .leaf
  | n + 1 => .node [nest n]

/-- R3 方向 A：宽而浅的合法比较（70 个兄弟、深度 2）。 -/
def wideTree : CmpTree := .node (nLeaves 70)

/-- R3 方向 B：50 层嵌套的合法比较。 -/
def deepTree : CmpTree := nest 49

theorem r3_wide_depth : depth wideTree = 2 := by decide

theorem r3_wide_size : size wideTree = 71 := by decide

theorem r3_deep_depth : depth deepTree = 50 := by decide

theorem r3_deep_size : size deepTree = 50 := by decide

theorem r3_wide_ref_ok : depthBounded wideTree = true := by
  simp [depthBounded, r3_wide_depth]

theorem r3_wide_twin_rejects : countBounded wideTree = false := by
  simp [countBounded, r3_wide_size]

theorem r3_deep_ref_rejects : depthBounded deepTree = false := by
  simp [depthBounded, r3_deep_depth]

theorem r3_deep_twin_ok : countBounded deepTree = true := by
  simp [countBounded, r3_deep_size]

/-- R3 的机器检查核心：两个预算代理**互不蕴含**（存在两个方向的判定漂移），
    因此「参考版深度 40 / 孪生版次数 64」不能互相模拟。 -/
theorem r3_metrics_not_equivalent :
    (∃ t : CmpTree, depthBounded t = true ∧ countBounded t = false) ∧
    (∃ t : CmpTree, depthBounded t = false ∧ countBounded t = true) :=
  ⟨⟨wideTree, r3_wide_ref_ok, r3_wide_twin_rejects⟩,
   ⟨deepTree, r3_deep_ref_rejects, r3_deep_twin_ok⟩⟩

end Typort.Engine.Budget
