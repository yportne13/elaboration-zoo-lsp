# GADT Exhaustiveness Check Bug: 跨分支索引约束未传播

## Bug 描述

当对 `(l: Nat, x: Vec[Boolean] l)` 做 tuple pattern match 时，编译器报了 non-exhaustive error，
但实际上两个分支 `(zero, nil)` 和 `(succ(m), cons(_, _))` 已经覆盖了所有可能的组合，
因为 GADT 约束会消除不可达的交叉情况。

### 复现

```typort
def test[l: Nat](x: Vec[Boolean] l): Boolean = match (l, x) {
    case (zero, nil) => true
    case (succ(m), cons(_, _)) => false
}
```

### 报错

```
non-exhaustive pattern: `Tuple2.mk(zero, cons)` not covered
non-exhaustive pattern: `Tuple2.mk(succ, nil)` not covered
```

但实际上：
- `Tuple2.mk(zero, cons)` — `x: Vec[Boolean] zero` 不可能是 `cons`（cons 要求 length = succ _）
- `Tuple2.mk(succ, nil)` — `x: Vec[Boolean] (succ _)` 不可能是 `nil`（nil 要求 length = zero）

---

## 实验

### 实验设置

在 `pattern_match.rs` 中添加 debug 打印，追踪 `filter_accessible_constrs` 和 `compile_aux` 的决策树构建过程。

### 实验结果

| 实验 | 输入 | 结果 |
|------|------|------|
| 1. `match (l, x)` | tuple，先 Nat 后 Vec | ❌ non-exhaustive |
| 2. `match (x, l)` | tuple，先 Vec 后 Nat | ❌ non-exhaustive (对称) |
| 3. `match x` | 直接 match Vec（无 tuple） | ✅ exhaustive 正确 |
| 4. `match x` | Vec[Boolean] 0，只有 nil 分支 | ✅ cons 正确被过滤 |
| 5. nested match | `match l { zero => match x { nil => ... } ... }` | ❌ 其他错误 |

实验 3 和 4 表明，**单 head 时 GADT 过滤 (`filter_accessible_constrs`) 工作正常**。
问题只出现在 **multi-head（tuple）场景**。

### Debug Trace 分析

关键 trace（实验 1）：

```
head=Tuple2.mk, 2 arms
  head=_1(Expl), 2 arms, constrs: [zero, succ]
    constr=zero, remaining_arms=1  ← 第一个分支匹配 zero
    head=_2(Expl), 1 arms, constrs: [nil, cons]
      filter_accessible_constrs(Vec[Boolean] l):
        nil: Vec[Boolean] zero ~ Vec[Boolean] l  ✓ ACCESSIBLE
        cons: Vec[Boolean] (succ ?) ~ Vec[Boolean] l  ✓ ACCESSIBLE
      constr=nil, remaining_arms=1  ← nil 匹配成功
      constr=cons, remaining_arms=0  ← 没有分支匹配 cons → UNMATCHED!
```

问题核心：**`filter_accessible_constrs` 检查 Vec[Boolean] l 时，`l` 仍然是未约束的 Rigid 变量。**
匹配 `_1` 到 `zero` 没有产生对 `l` 的 GADT 约束，所以 nil 和 cons 都被认为 accessible。

---

## 根因分析

### 代码位置

`src/L13_namespace/pattern_match.rs`：
- `filter_accessible_constrs` (行 245-346)：检查构造器是否可访问
- `compile_aux` (行 348-993)：构建决策树
- GADT refinement (行 814-845)：匹配构造器时尝试类型细化

### 根本原因

当处理 tuple 匹配 `(l, x)` 时：

1. `(l, x)` 被展开为 `Tuple2.mk(l, x)`
2. Tuple2 的字段成为两个 head：`_1: Nat` 和 `_2: Vec[Boolean] l`
3. 处理 `_1` 匹配 `zero`——这绑定了**变量 `l` 的值**为 `zero`
4. 但匹配 Nat（无索引参数）产生的 GADT refinement 是平凡的：
   ```rust
   unify_pm(cxt, Nat, Nat, ...)  // 无实际约束
   ```
5. 处理 `_2: Vec[Boolean] l` 时，`l` 仍是自由 Rigid 变量
6. `filter_accessible_constrs` 检查 nil 和 cons——两者都统一成功 → 都 accessible
7. 对于 accessible 但没有 arm 匹配的 cons → Unmatched!

### 为什么单 head 没问题

当直接 `match x` 时，只有一个 head `Vec[Boolean] l`。`filter_accessible_constrs` 会尝试分别统一 nil 和 cons 的返回类型与 `Vec[Boolean] l`。两者都能统一（`l` 是自由的），但**当 `l` 已被具体化为特定值时**（如实验 4 的 `Vec[Boolean] 0`），nil 可以而 cons 不行 → 正确过滤。

### 本质

`l` 同时扮演两个角色：
- **值**: 作为 tuple 的第一个字段，被匹配为 `zero` 或 `succ`
- **类型索引**: 作为 `Vec[Boolean]` 的 length 参数

当从头 1（Nat）匹配时，值匹配产生了 `l = zero` 的约束，但这个约束没有被**传播到头 2 的类型 `Vec[Boolean] l`** 中。`filter_accessible_constrs` 检查时看到的仍然是未约束的 `Vec[Boolean] l`，而非细化的 `Vec[Boolean] zero`。

### 修复方向

在 `compile_aux` 处理完一个 head 后，需要将产生的约束（特别是对共享 Rigid 变量的绑定）应用到**剩余 heads 的类型**上，然后再递归。

具体来说，当 `heads = [Nat, Vec[Boolean] l]` 且 arm 匹配了 `_1 → zero`：
1. 不仅要在 arm entry 的 `cxt` 中绑定 `_1 = zero`
2. 还要将 `l = zero` 这个约束应用到 `_2` 的类型中，使得递归时 `head_typ` 变为 `Vec[Boolean] zero`
3. 这样 `filter_accessible_constrs` 就会正确地把 cons 标记为 inaccessible

当前代码在行 812-835 有 GADT refinement，但它只在**匹配构造器时**生效（统一 head 的 type 和 constr 的 return type）。对于 Nat 这种无索引类型，这个统一无意义。需要的是**将值级别的约束映射到类型级别的索引约束**。

## 尝试过的修复

尝试了两种方案，都因副作用问题失败。

### 方案一：new_heads 的值从 ori 提取

在 Pi peeling 中，把 `Val::vvar(...)` 替换为从 `ori` 提取的实际值。目标是让 `_1 = l`，匹配 `_1 = zero` 时 `l` 直接被约束。

**问题**：`ori` 是最顶层匹配值（Tuple2.mk），`ori.datas[pi_idx]` 的索引只对顶层构造器正确。内层构造器（如 Vec.cons）会用 `ori` 中不相关的数据，破坏了 prelude 中的 Vec 匹配。

### 方案二：在 GADT refinement 中追加 update_cxt

在 `constr == constr_` 分支的 GADT refinement 之后，用 `cxt.update_cxt(infer, l_lvl, SumCase{zero}, true)` 将 head 对应的 ori 字段值约束为当前构造器。

**问题**：`update_cxt` 虽然返回新 Cxt，但其内部 `refresh` → `fresh_val` → `infer.quote/eval` 与 inference state 的交互产生了副作用。即使 `new_cxt_ff` 只用于 `filter_accessible_constrs`，副作用链式反应破坏了后续的统一流程，导致函数调用时代入类型错误。

### 方案三：check_pm_final 做子约束 (失败)

在 `constr == constr_` 分支中，对当前 head 调用 `check_pm_final(sub_pat, sub_typ, sub_ori)`，期望 infer/check 子 pattern 后 unify 子值与构造器值。

```rust
// 对 _1 = zero:
sub_ori = ori.datas[_1]  // → l (Rigid)
pat = constr_raw  // → Obj(Var("Nat"), "zero")
// 对带参数的构造器加 Hole:
pat = App(constr_raw, Hole, Expl)  // → succ(?)
check_pm_final(cxt, pat, head_typ=Nat, sub_ori=l)
```

**问题 1**: 对构造函数器（succ, cons），`check_pm_final` 内部创建 meta 并通过 `infer_expr_pm` 求解。meta 求解调用 `lams_go` 遇到预期之外的值 → `unreachable!()` panic。

**问题 2**: `check_pm_final` 设计为在决策树**叶子节点**调用（完整 pattern + 完整 ori），在内部节点调用会导致 infer state 处于半编译状态，进一步触发 meta 求解异常。

### 方案四：infer_expr + unify_pm (失败)

尝试绕过 `check_pm_final`，手动 `infer_expr` 获取构造器的 value，再用 `unify_pm` 约束：

```rust
let (tm, _) = infer.infer_expr(cxt, constr_raw)?;
let val = infer.eval(cxt, tm);
unify_pm(cxt, sub_ori=l, val)
```

**问题**: `infer_expr` 对构造器名称（如 `Obj(Var("Nat"), "succ")`）返回的是**构造器的类型**（`Pi(n: Nat) → Nat`），而不是 SumCase 值。`unify_pm(l, Pi(...))` 类型不匹配。

## 根本原因

**`ori` 变量与值之间的连接在建决策树时不存在，只有在 `check_pm_final` 叶子节点才通过 `unify_pm(ori, pat_value)` 建立。**

级联 match 之所以能工作，是因为 `check_pm_final` 在 match l 的叶子节点就建立了 `l = zero`，然后 body（内层 match）在新的 Cxt 中编译。tuple match 中所有 head 在同一个决策树中顺序处理，`check_pm_final` 要到所有 head 都匹配完后才调用——此时 `filter_accessible_constrs` 早已跑完。

### 可行的修复方向

**方案 A：决策树分支级别隔离（推荐）**

核心难点是 inference state 全局共享导致的 arm 间干扰。在 `compile_aux` 的 `decision_tree_branches` 循环中，对每个构造器分支做 infer state 的 save/restore：

```rust
let decision_tree_branches = constrs.iter().map(|constr| {
    let branch_save = infer.save();  // 保存 meta/rigid 状态
    // ... 现有处理逻辑（含 GADT refinement + update_cxt）
    // 可以安全地 update_cxt(l=zero) 等
    let result = ...;
    infer.restore(branch_save);  // 恢复，不影响其他分支
    Ok(result)
});
```

这样 arm 1 的 `l = zero` 不会影响 arm 2 的 `l = succ(m)`。

**方案 B：post-processing 消除假阳性**

不影响决策树本身，在 `compile` 中对已收集的 `self.warnings` 做二次检查。对于 `Tuple2.mk(zero, cons)`，用 `check_pm_final` 验证这个 pattern 是否真的可达：

1. 解析 Unmatched pattern 得知 head 0=zero, head 1=cons
2. 提取 `ori` 中 head 0 的子值 → `l`
3. 在临时 Cxt 中约束 `l = zero`
4. 重新调用 `filter_accessible_constrs` 检查 cons
5. 若不可达则从警告中移除


