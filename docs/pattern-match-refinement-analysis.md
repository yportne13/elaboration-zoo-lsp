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

**结果**：测试基线 29/49（与原始持平），但 `check_pm` 本身在遇到 Rigid-vs-Flex 时
仍然失败 → fall through 到 `unify_catch` → `unify` → `solve` → `rename` 外层 Rigid
无法映射 → `UnifyError::Basic`。即使加了 `rename` 对 `dom=0` 时的修补，`dom>0` 时
仍然失败。

### 三个尝试的共同障碍：`rename()` 无法处理跨作用域 Rigid

**根本原因**：当 `solve` 尝试把 `Flex(m, [])` （在 `insert_go`/`fresh_meta` 中创建，
位于某个 level 以下的作用域）赋值为 `SumCase(succ, [Rigid(_n)])`（`_n` 是来自外层
的上界变量）时，`rename()` 需要用 `PartialRenaming` 把 `SumCase(succ, [Rigid(_n)])`
从 meta 的创建上下文重命名到当前上下文。但 `Rigid(_n)` 的 level 在 `pren.ren` 中
不存在映射（因为 `_n` 是在 meta 的作用域外面定义的），且 `pren.dom > 0`（meta 的
上下文中有约束变量），`rename` 只能报 `Err(UnifyError::Basic)`。

**修补尝试**：在 `unification.rs:265` 处加了这个逻辑：

```rust
None => {
    if x.0 >= pren.cod.0 {
        // 外层 Rigid → 保持为 Var(Ix(0))
        let t = Tm::Var(Ix(0));
        self.rename_sp(decl, pren, t.into(), sp)
    } else {
        // 当前作用域内的 Rigid → 正常转换
        let t = Tm::Var(lvl2ix(pren.cod, *x));
        self.rename_sp(decl, pren, t.into(), sp)
    }
}
```

但这只能覆盖少数情况。更通用的修复需要让 `rename()` 能正确处理「逃逸 Rigid」——
在 `pren` 中为 Rigid 创建新的应变量条目。

**真正的修复方向**：在 `invert_go` 中，当遇到空 spine 时（`Flex(m, [])`），`dom = 0`，
`ren = {}`。解决方案中的 Rigid 如果有 `x.0 >= cod.0`，需要作为「刚性参数」保留在
求解后的项中（不进行重命名）。这会引入所谓「刚性 Skolem 常量」的概念，是一个较大的
架构改动。

## 当前 best state（2026-06-25）

以下改动已在工作树中：

1. **`elaboration.rs`**: `check_pm_final` 改用 `check_pm`（方案 3）
2. **`elaboration.rs`**: `default_ret` 包含所有 params，struct 的 Expl 参数转为 Impl
3. **`unification.rs`**: `rename` 对 `dom=0` 时不报错
4. **`mod.rs`**: `PatternDetail::Any(Span<SmolStr>, Icit)`
5. **`parser/mod.rs`**: `_` pattern 用 `data: false`
6. **`legacy_tests.rs`**: backup/current-wip 版本的测试

测试基线：29 passed / 49 failed（与 backup/current-wip 分支一致）

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
