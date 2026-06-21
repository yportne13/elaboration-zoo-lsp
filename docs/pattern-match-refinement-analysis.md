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

## 关键代码位置

| 文件 | 行号 | 作用 |
|------|------|------|
| `pattern_match.rs` | ~220 | `filter_accessible_constrs`：临时细化后截断 |
| `pattern_match.rs` | ~240 | `check_pm_final`：叶节点细化 |
| `pattern_match.rs` | ~447 | `constr_ == constr` 分支：struct constructor 匹配 |
| `pattern_match.rs` | ~540 | `remaining_arms` 分支转发 |
| `cxt.rs` | ~510 | `put_local` / `update_cxt` |
| `elaboration.rs` | ~320 | `check_pm`：match 入口 |
