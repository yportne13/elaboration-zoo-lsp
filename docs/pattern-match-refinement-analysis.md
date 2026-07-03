# 模式匹配 GADT 类型细化薄弱点分析

## 概述

L13 的 GADT 模式匹配（`pattern_match.rs`）在匹配索引类型（如 `Vec[A] len`）时，存在一个
类型细化无法传播到已绑定变量的根本性缺陷。这使得所有「返回绑定子模式变量」的代码都无法
通过类型检查，即便语义上完全正确。

## 根因

### 代码路径

1. `elaboration.rs` 中的 `check_pm` 解析 match 表达式，调用 `Compiler::compile`
2. `Compiler::compile` → `compile_aux` 递归处理模式匹配
3. 核心循环：`compile_aux` 对 `heads`（待匹配的类型栈）逐一匹配构造函数
4. 每个 head 是一个 `(类型, 变量名, Expl/Impl)` 元组

### struct 的脱糖

```
struct WrapVec[A, len: Nat] { inner: Vec[A] len }
```

脱糖为单 case enum：
```
enum WrapVec[A](len: Nat) {
    mk(vec: Vec[A] len) -> WrapVec[A] len
}
```

### 细化流程

1. **外部匹配**：`match vh { case VecHolder { cons(x, xs), fzero } => ... }`
   - `heads = [(VecHolder[A,len], vh)]`
   - 匹配 `VecHolder.mk` 构造函数 → 不是 GADT（无索引参数），不做细化
   - 递归进入字段：`heads = [(Vec[A] len, vec), (Fin (succ len), last)]`

2. **字段匹配**：匹配 `cons` 构造器
   - `filter_accessible_constrs` 处理 Vec 上的 cons
   - 在**临时 cxt** 中统一 `len := succ l'`，判断 cons 可达
   - **临时 cxt 被丢弃**（第 226 行 `truncate_mvars`）

3. **叶节点细化**：`check_pm_final` 通过「模式作为表达式」与 scrutinee 类型统一
   - 模式 `VecHolder.mk(cons(x,xs), fzero)` vs scrutinee `VecHolder[A,len]`
   - 正确地将 `len` 细化为 `succ l'`（或 `0`）

### 缺陷：绑定变量类型「冻结」

```
match w: WrapVec[A,len] {
    case WrapVec { cons(x, xs) } => xs   // xs: Vec[A] l'
}
```

- 在步骤 2 的递归过程中，变量 `xs` 被绑定，其类型 `Vec[A] l'` 中的 `l'` 来自 cons 构造器的返回类型
- 步骤 3 的细化更新了 cxt 中 `len` 变量（`len := succ l'`）
- 但 **`xs` 的类型记录为 `Vec[A] l'`，其值 `l'` 是 Rigid 变量，与 `succ l'` 不同**
- 检查 body 时，返回类型 `Vec[A] len` 被细化为 `Vec[A] (succ l')`，但与 `xs : Vec[A] l'` 无法统一

### 核心矛盾

| 实体 | 组化前 | 细化后 |
|------|--------|--------|
| 函数签名返回类型 | `Vec[A] len` | `Vec[A] (succ l')` |
| body 推断类型（`xs`）| `Vec[A] l'` | `Vec[A] l'`（不变）|

两者一个是 `succ l'`，一个是 `l'`，统一失败。

## 控制实验

### 重建构造器 → 通过

```typort
def vid[A, len: Nat](v: Vec[A] len): Vec[A] len =
    match v {
        case nil => nil
        case cons(x, xs) => cons(x, xs)
    }
```

`cons(x, xs)` 的类型是 `Vec[A] (succ l')`，与细化后的返回类型 `Vec[A] (succ l')` 完全一致。

### 返回绑定变量 → 失败

```typort
def vtail[A, len: Nat](v: Vec[A] len): Vec[A] len =
    match v {
        case nil => nil
        case cons(x, xs) => xs
    }
```

错误：`expected: Vec[A](_l + 1), find: Vec[A](_l)`

这证明了缺陷**不是 struct 独有的**，而是 GADT 模式匹配的一般性问题，但在 struct
场景下因多层间接引用而更常见。

## 探测套件

详见 `src/L13_namespace/struct_refine_probe.rs`。

### 5 个通过的基线

| 测试 | 关键特征 |
|------|---------|
| `baseline_identity_vec` | 重建构造器，不返回绑定变量 |
| `baseline_direct_rebuild` | 直接 Vec 匹配，返回 `cons(x,xs)` |
| `baseline_preconstrained_element` | scrutinee 类型已约束为 `succ len`，返回 `x:A` |
| `baseline_nested_preconstrained` | 嵌套 struct + 预约束类型 |
| `baseline_arrow_field` | 返回函数应用结果，非索引依赖 |

### 5 个失败的薄弱点

| 测试 | 错误模式 | 本质 |
|------|---------|------|
| `weak01` | `Vec[A](_l+1) vs Vec[A](_l)` | 最简复现：直接 Vec + 返回绑定 `xs` |
| `weak02` | 同上 | struct 包装版 |
| `weak03` | `Fin(1) vs Fin(len+1)` | 两字段交叉索引依赖，`w` 的类型未随 `len:=0` 更新 |
| `weak04` | 同 weak01 | 嵌套 struct + 泛型 len |
| `weak05` | `Fin(_l+2) vs Fin(_n+1)` | 两字段细化未交叉传播 |

## 修复实现

### 修改 1：`unify_pm` — 不同 Rigid 级别时优先更新未细化变量

在 `unify_pm`（`elaboration.rs`）中新增处理：当两个不同级别的 Rigid 需要统一时，
检查各自的 env 条目。如果其中一个的 env 条目仍是自我引用（即未被 `update_cxt` 细化过），
而另一个已被细化，则更新未细化的那个，保留已存在的细化。

```
(Rigid(len_lvl), Rigid(n_lvl)) → 环境已有 len := succ l', n 是新鲜 Rigid
→ 更新 n := len (保留 len 的细化)
```

### 修改 2：`infer_expr(Raw::Var)` — 在细化环境中重求值变量类型

GADT 模式匹配经过 `check_pm_final` 后，`update_cxt` 可能会更新环境中的 Rigid 索引
变量（如 `len := 0`）。但绑定变量的存储类型（`src_names` 中的 `Rc<Val>`）仍然引用
原始的 Rigid 级别。当 `cxt` 已被细化时，`infer_expr(Raw::Var)` 会对存储的类型
执行 `quote` + `eval`，让 Rigid 引用通过环境查找解析为当前细化值。

```
w : Fin (succ len)  →  env[len] = 0  → 重求值 → Fin (succ 0) = Fin 1
```

### 仍开放的薄弱点（需要更深层修复）

跨字段索引依赖（weak03、weak05）仍然失败，因为：

1. `check_pm_final` 的模式推断会创建独立的元变量（不同于 Pi 循环中的 Rigid）
2. Pi 循环中 `unify_pm` 得到的细化会被 `check_pm_final` 覆盖
3. 绑定的 Rigid（如 `i : Fin n`）与模式推断创建的元变量（如 `?n`）不联通

深层修复需要在 `check_pm_final` 中复用 Pi 循环已经建立的 Rigid 绑定，或者
改变 `new_heads` 计算中 Impl 参数的变量类型（用元变量代替自我引用 Rigid）。

## 关键代码位置
因为 `Rc<Val>` 指向的是不可变值。

**可能的切入点**：

- `cxt.rs` 中的 `put_local`：存储变量类型为 `Rc<Val>`
- 在 `check` body 之前，对局部变量类型调用 `force`/`eval` 以解析当前值
- 或者在 `get_local` 时进行惰性正规化

### 方案 B：回溯代入

当 `update_cxt` 更新一个索引变量时，遍历所有已绑定的局部变量，用新值替换其类型中的
引用。

**复杂度**：O(n) 每次更新，可能影响性能。

### 方案 C：在分支处精确绑定

不在递归进入字段时绑定变量，而是记录绑定信息，在 `check_pm_final` 完成最终细化后
再统一绑定。这需要较大重构。

## 修复尝试

### 尝试 1：`infer_expr_pm` — `check_pm` 递归做参数检查

**思路**：在 `check_pm_final` 中使用专用版本的 `infer_expr`，该版本对 `Raw::App` 的参数
检查改用 `check_pm`（→ `unify_pm`）而非 `check::<false>`（→ `unify_catch`），使得
Rigid 模式变量得到细化。

**实现**：
```rust
fn infer_expr_pm(&mut self, cxt: &Cxt, t: Raw) -> Result<(Rc<Tm>, Rc<Val>, Cxt), Error> {
    // 非 App 情况 → 委托给 infer_expr
    // App 情况 → 用 check_pm 检查参数
}
```

然后 `check_pm` 和 `check_pm_final` 都改用 `infer_expr_pm`，形成：
```
check_pm → infer_expr_pm → (App) → check_pm → infer_expr_pm → ...  (互递归)
```

**结果**：测试基线 29/49（不变），`test_pm_struct_multi_field_gadt` 的错误从
`can't unify Fin(_l+1) vs Fin(_n)` 变为 `find unsolved meta with type Nat`。
错误类型变了但测试仍然失败。unsolved meta 表明 `rename()` 在外层 Rigid 跨作用域赋值
时无法处理 → 留下悬空 meta。

### 尝试 2：`check_pm_final` 始终走手工 fallback

**思路**：跳过 `infer_expr`，始终用 `collect_apps` 拆解 App 链 + `insert_t` 填充 Impl
参数 + `unify_pm` 逐参数处理。

**实现**：
```rust
fn check_pm_final(...) {
    let (func, args_raw) = Self::collect_apps(&t);
    let (mut t_acc, mut remaining_ty) = self.insert_t(cxt, ...)?;
    for field_raw in args_raw.iter() {
        // Val::Pi → infer_expr + insert + unify_pm
    }
    // 最后 unify_pm(a, inferred_type) + unify_pm(ori, eval(t_acc))
}
```

**结果**：测试基线 25/53（退步 4 个），`collect_apps` 把 Impl 参数也收集进来了，
导致 `insert_t` 已填充的 Impl 参数在循环中被重复处理。

### 尝试 3：`check_pm` 直接替换 `infer_expr` + `insert` + `unify_pm`

**思路**：`check_pm_final` 内部直接用 `check_pm`（它已经做了 `infer_expr` + `insert` +
`unify_pm`），然后用 `unify_pm` 处理 ori。

**实现**（最简洁）：
```rust
fn check_pm_final(...) {
    let (t_inferred, cxt) = self.check_pm(cxt, t, a)?;
    let new_cxt = self.unify_pm(&cxt, &ori, &eval(&cxt, &t_inferred), ...).unwrap_or(cxt);
    Ok((t_inferred, new_cxt))
}
```

同时配合 `default_ret` 修改（`elaboration.rs` 中 `Decl::Enum` handler 的 `default_ret`
包含所有 params，struct 的 Expl 参数自动转为 Impl）。

**结果**：测试基线 29/49（与原始持平）。`check_pm` → `infer_expr_pm` → `check_pm` 互递归
能正常处理 App 参数的 Rigid 细化，但对 body 检查无影响。

### 三个尝试的共同障碍：`unify_pm` vs `unify` 对 Rigid 处理不一致

**⚠️ 注意：以下分析已推翻最初的理解。** 问题不在 `rename()`，而在两条代码路径用了
不同的 unification。

#### 两条路径

`compile_aux` 中 wildcard handler（`pattern_match.rs` ~240）对每一条臂做两件事：

1. **类型检查臂的模式部分**（`check_pm_final`）：
   ```
   check_pm_final → check_pm → infer_expr_pm → (App) → check_pm → unify_pm
   ```
   `unify_pm` 认识 Rigid，遇到 `Rigid(_n) ≈ SumCase(succ, ...)` 就走
   `(_, Val::Rigid(x, sp)) if sp.is_empty()` 分支 → `update_cxt` 把 env 里 `_n`
   替换为细化后的值。**这步能过。**

2. **检查臂的 body**（`check::<false>`）：
   ```
   check::<false> → infer_expr → (App) → check::<false> → unify_catch → unify
   ```
   `unify` **不**认识 Rigid（`unification.rs:903`：`_ => Err(UnifyError::Basic)`）。
   当 body 中的表达式重新涉及 GADT 索引类型时（比如臂 3 的 `new VecHolder(xs, i)`
   涉及 `Fin n`），`infer_expr` 的 `insert_t` 会为隐式参数创建**全新的 meta**，
   这个 fresh meta 在 `unify_catch` → `unify` 中与包含 Rigid 的值相遇时，
   `unify` 没有对应的处理分支 → `UnifyError::Basic`。

#### 为什么 `check_pm_final` 的细化没有帮助

`check_pm_final` 确实通过 `update_cxt` 修改了 env——`_n` 的 env 条目被替换成了
`SumCase(succ, [Rigid(_l)])`。当后续 `infer_expr` 重新求值 `i` 的类型 `Fin n` 时：

```rust
// infer_expr, Var 分支中 is_refined() 为 true
let quoted = self.quote(&cxt.decl, cxt.lvl, &a.1);
self.eval(&cxt.decl, &cxt.env, &quoted)
```

`quote` 把 `Fin(Rigid(n))` 变成 `Tm::App(Tm::Decl("Fin"), Tm::Var(ix_n))`，
`eval` 在 refined env 里查 `ix_n` 拿到 `SumCase(succ, [Rigid(_l)])`，得到
`Fin(SumCase(succ, [Rigid(_l)]))` = `Fin (succ _l)`。**求值结果是正确的。**

但问题在于：处理 `new VecHolder(xs, i)` 时，`infer_expr` 对 `VecHolder.mk` 做
`insert_t`，为字段类型**新创建** meta（`?len`）。然后 `check::<false>` 逐个检查参数。
对于 `fsucc(i)`：

1. `infer_expr` 算出 `fsucc` 类型 `(n: Nat) → (i: Fin n) → Fin (succ n)`
2. `insert_t` 为隐式 `n` 创建 **fresh meta** `?n`（不是 pattern 里的 Rigid `_n`）
3. 参数 `i` 的类型在 refined cxt 里是 `Fin (succ _l)`
4. `unify_catch(cxt, Fin(?n), Fin(succ _l))` → `unify`
5. `unify` 里 `Flex(?n) ≈ SumCase(succ, [Rigid(_l)])` → `solve` → 如果 spine 非空
   或 Rigid 层级对不上 → `UnifyError::Basic`

所以**细化发生在 env 层面，但 body 检查的 `check::<false>` 走的 `unify` 不认识 Rigid**。

#### 修复方向

让 body 检查也使用 `check_pm`（→ `unify_pm`）来处理涉及 GADT 索引的类型约束，
而不是 `check::<false>`（→ `unify`）。这已经在 wildcard handler 的 body 检查中
尝试了 fallback（`check_pm` 兜底），但初始路径仍是 `check::<false>`。

另一个方向是在 `unify` 中增加 `Rigid ≈ _` 的处理分支（类似 `unify_pm`），
让常规 unification 也能细化 Rigid。这更通用，但需要确保不破坏非 pattern-match 场景。

## 当前 best state（2026-06-26）

以下改动已在工作树中：

1. **`elaboration.rs`**: `check_pm_final` 改用 `check_pm`（方案 3）；新增 `infer_expr_pm`
2. **`elaboration.rs`**: `unify_pm` 加入 debug trace
3. **`mod.rs`**: `PatternDetail::Any(Span<SmolStr>, Icit)`
4. **`pattern_match.rs`**: `to_raw`/`root_detail`/`detail_to_raw`；`patcon_raw`+`check_pm_final`
   送入；`Any(_, _)` / `Any(name, icit)` 变体
5. **`legacy_tests.rs`**: vec_last 测试

测试基线：29 passed / 49 failed

## 关键代码位置

| 文件 | 行号 | 作用 |
|------|------|------|
| `pattern_match.rs` | ~220 | `filter_accessible_constrs`：临时细化后截断 |
| `pattern_match.rs` | ~240 | `check_pm_final`：叶节点细化 |
| `pattern_match.rs` | ~447 | `constr_ == constr` 分支：struct constructor 匹配 |
| `pattern_match.rs` | ~540 | `remaining_arms` 分支转发 |
| `cxt.rs` | ~510 | `put_local` / `update_cxt` |
| `elaboration.rs` | ~320 | `check_pm`：match 入口 |
| **`unification.rs`** | **~265** | **`rename` 跨作用域 Rigid（修复瓶颈）** |

---

## 值层面跨字段精化薄弱点（2026-07-03）

### 问题描述

`match (b, b)` 中 `b: Boolean` 是**同一个变量**出现在元组的两个字段中。理论上只有
`(true, true)` 和 `(false, false)` 两种取值可能，`(true, false)` 和 `(false, true)`
是**不可能的**。但当前模式编译器报告：

```
non-exhaustive pattern: `Tuple2.mk(true, false)` not covered;
non-exhaustive pattern: `Tuple2.mk(false, true)` not covered
```

### 已有 GADT 类型索引精化的成功路径

对于 GADT 类型（如 `Vec[A] len`），`filter_accessible_constrs` 通过 `check_pm` 做
**类型统一**来判定构造器可达性：

```
filter_accessible_constrs
  → check_pm(cxt, constr_with_holes, forced_type)  // 如 nil vs Vec[Nat] n
  → unify_pm(Vec[Nat] n, Vec[Nat] 0)               // 绑定 n = 0
  → 只有兼容的构造器（nil）标记为可达
```

这是**类型层面**的精化——索引**本身就是类型的一部分**（`Vec[Nat] n`），所以统一后
`n = 0` 直接反映在类型上。

### `(b, b)` 场景的区别

| 维度 | GADT 索引精化 | 值层面相等精化 |
|------|--------------|---------------|
| 精化内容 | `len := 0` / `len := succ l` | `b := true` / `b := false` |
| 影响范围 | **类型** `Vec[Nat] len` → `Vec[Nat] 0` | **值** `b` → `SumCase("true")` |
| 对类型影响 | 类型参数变化，构造器可达性改变 | 类型 `Boolean` 不变 |
| 检测机制 | `check_pm` 做类型统一 | 需要值层面一致性检查 |
| 发生时机 | `check_pm`（决策树构建时） | `check_pm_final` 的 `unify_pm(ori, tmv)`（base case） |

### 根因：两个层面的精化发生在不同阶段

决策树构建流程：

```
for each head (逐字段):
  1. filter_accessible_constrs → 只看类型，返回可达构造器
  2. 对每个 arm，匹配构造器 → 生成剩余 arm 和剩余 heads
  3. 递归 compile_aux 继续处理后续 heads

base case (heads 为空):
  4. check_pm_final(cxt, patcon_raw, target_typ, ori)
     ├─ check_pm → 类型统一（GADT 索引精化）
     └─ unify_pm(ori, tmv) → 值层面精化  ← b := true 发生在这里
```

值层面精化（第 4 步）发生在**所有 head 都处理完之后**，而 `filter_accessible_constrs`
（第 1 步）在**每个 head 处理时**就需要知道哪些构造器可达。所以 `b := true` 的精化
来不及影响第二个字段的可达性判断。

### 为什么 e8ade22 的精化修复不适用

e8ade22 的修复：

1. **`unify_pm` 不同 Rigid 分支**：`Rigid(x1) vs Rigid(x2)` 时优先更新未细化变量
2. **`infer_expr(Raw::Var)` 重求值**：在 `is_refined()` 环境中重新 `quote+eval` 变量类型

这两个修复处理的是**类型索引精化在不同字段间的传播**。对 `(b, b)` 而言：
- `Boolean` 是**无索引类型**（`has_indices = false`），`filter_accessible_constrs`
  走快速路径无条件标记所有构造器可达
- `b := true` 是值层面的精化，不影响 `Boolean` 类型的构造器集合
- 即使 `cxt.env` 中有 `b = SumCase("true")`，`filter_accessible_constrs` 也从不检查 env

### 修复思路

#### 方案 A：值一致性检查（针对无索引类型）

在 `filter_accessible_constrs` 的快速路径中（`:276-282`），不再无条件标记所有
构造器可达，而是加上值一致性检查：

```
if !has_indices {
    for constr_def in all_constrs {
        // 检查环境中被匹配的变量是否已被 refine 到某个具体构造器
        // + 备选构造器与该细化值兼容
        if value_consistent(cxt, ori, constr_def) {
            accessible.push(...)
        }
    }
}
```

**难点**：
- `filter_accessible_constrs` 当前没有 `ori` 参数，需要从 arm tuple 传入
- `ori` 是完整的元组值 `(b, b)`，需要按字段投影得到当前字段的值 `b`
- 投影逻辑：对 `SumCase("mk", [b, b])`，第 k 字段的值是 `datas[k].1`

#### 方案 B：前置精化匹配

在处理每个 head 的 `constr_ == constr` 分支中，**立即执行**一次 `check_pm_final`
（不含 body 检查），将值精化提前应用到 `cxt`，然后传递给后续递归调用。

```
// 在 constr_ == constr 分支中：
let refined_cxt = infer.check_pm_final(
    &cxt,
    constr_raw,      // 构造器原始表达式
    typ.clone(),     // 当前字段类型
    field_ori,       // 当前字段的投影值
).ok().unwrap_or(cxt.clone());
// 用 refined_cxt 替代 cxt.clone() 传入递归调用
```

**难点**：
- `check_pm_final` 会创建临时 meta（对 `cons` 等有 Pi 参数的构造器）
- 调用后需要 `truncate` meta，但精化后的 `cxt.env` 可能引用已回收的 meta ID
- 对无索引类型（Boolean）不存在此问题（无 Pi 参数，无 meta 创建）

#### 方案 C：在 `unify_pm` 中增加值层面分支

在 `unify_pm` 中，匹配裸 `Rigid` 到 `SumCase` 时，若 `Rigid` 已被细化且细化值与
`SumCase` 冲突，返回错误：

```
(Val::Rigid(x, sp), Val::SumCase { case_name, .. })
    if sp.is_empty() && cxt.env[x] != self_ref  && cxt.env[x] != SumCase(case_name) =>
{
    Err("inconsistent refinement")
}
```

这可以在 `filter_accessible_constrs` 的 GADT 检查路径（而非快速路径）中被触发——
将无索引类型也放到 GADT 检查路径中，用统一的 `check_pm` 来检测值不一致。

### 当前代码位置

| 文件 | 行号 | 相关代码 |
|------|------|---------|
| `pattern_match.rs` | ~276-282 | `!has_indices` 快速路径 |
| `pattern_match.rs` | ~448-462 | `filter_accessible_constrs` 调用处 |
| `pattern_match.rs` | ~580-663 | `constr_ == constr` 分支 |
| `pattern_match.rs` | ~237-320 | `filter_accessible_constrs` 实现 |
| `elaboration.rs` | ~282-324 | `unify_pm` 的 Rigid/SumCase/Sum 处理 |
| `elaboration.rs` | ~225 | `check_pm` 定义 |
| `elaboration.rs` | ~233 | `check_pm_final` 定义 |
