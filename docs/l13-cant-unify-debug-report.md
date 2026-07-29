# L13 `can't unify` 调试报告

## 环境信息

- 分支：`fix/l13-eval-call-args`（基于 `a9e03f8`）
- 项目：`elaboration-zoo-lsp`
- 测试用例：`test_user_provided`（`src/L13_namespace/legacy_tests.rs:3062`）
- 语言：Rust edition 2024
- HashMap：`std::collections::HashMap`（标准库实现）
- `unsafe`：`src/L13_namespace/` 下**零** `unsafe` 代码

## 错误现象

```
FAIL: 'can't unify
  expected: Eq[Nat]❰nat_mul_helper(nat_add_helper(...), ...)❱
      find: Eq[Nat]❰nat_mul_helper(nat_add_helper(...), ...)❱
```

expected 和 find 两侧 `pretty_tm` 打印结果**完全一致**，但内部 Val 结构不同——expected 已全部固化（Rigid + solved metas），find 侧含未解 Flex metas。

## 失败路径

`unify` 函数（`unification.rs:878-898`）的 `(Val::Match, _)` 分支：

```
(Val::Call(_, _, t_body), _) → unfold → t_body = Val::Match
  → (Val::Match(s, env, cases), Val::Obj(Decl("Tuple2.Tuple2.mk", spine), "_1"))
  → 无法规约 Match（scrutinee 是 Rigid 变量）
  → fallback: (Rigid, Obj) ≠ (Rigid, Rigid) → Err(Basic)
```

## Obj(Decl("Tuple2.Tuple2.mk", spine), "_1") 的来源

find 侧类型索引中包含了 `g(succ(m))._1` 的求值结果。此值包含 `Tuple2.mk(double(g(m)._1), g(m)._2)` 构造子调用，但由于 `Decl` 的 body（`Val::Lam`）没有被 `v_app(Decl)` 内联展开，`v_app` 只是将参数累积到 `Decl` 的 spine 中。`Obj(Decl(...), "_1")` 无法从 Decl 中投影字段，因此保留为未规约形式。

关键代码：`v_app` 中 `Val::Decl` 分支（`mod.rs:1081-1096`）：
```rust
Val::Decl(x, sp) => {
    let acc = sp.prepend((u, i));
    if let Some(entry) = decl.get(&x.data) {
        if let Some(ref prim_fn) = entry.5 {
            // 仅处理 primitive 函数
            ...
        }
    }
    Val::Decl(x.clone(), acc).into()
    // ↑ 只积累 spine，不内联 entry.2 的 body
}
```

## Double-prefix 问题

`Tuple2.mk` 构造子的注册 key 是 `"Tuple2.Tuple2.mk"`（双重前缀），而非预期的 `"Tuple2.mk"`。原因：

### 1. Parser（`parser/mod.rs:1258`）生成 case name 时已带前缀

```rust
name.clone().map(|x| x.map(|x| SmolStr::new(format!("{x}.mk"))))
```

对于 `struct Tuple2[A, B]`，case name = `"Tuple2.mk"`（含 struct 名前缀）。

### 2. Elaborator（`elaboration.rs:798`）又加一次前缀

```rust
let case_key = c.0.clone().map(|n| SmolStr::new(format!("{}.{}", name.data, n)));
```

`name.data = "Tuple2"`，`n = "Tuple2.mk"` → `case_key = "Tuple2.Tuple2.mk"`。

### 3. 导致 lookup 失败

`infer_expr(Var("Tuple2.mk"))` → `decl.get("Tuple2.mk")` → **查不到** → fallback 行 1145-1160：

```rust
let fallback = format!(".{}", name.data);  // ".Tuple2.mk"
// 搜索 keys 以 ".Tuple2.mk" 结尾的 entry
```

找到 `"Tuple2.Tuple2.mk"` → 返回 `Tm::Decl(empty_span("Tuple2.Tuple2.mk"))`。

## 核心矛盾：`entry.2 = Lam` 写入、`Decl` 读出

### 证据 1：`decl()` 写入 `vt = Lam`

在 `cxt.decl()`（`cxt.rs:483-499`）中添加 `eprintln!`：

```
decl('Tuple2.Tuple2.mk'): vt=Lam("A" @ 2076,2077, Impl, Closure(...))
```

唯一一次 `decl()` 调用，`vt` 是 `Val::Lam`。

### 证据 2：`decl()` 返回后立即读回是 `Lam`

在 `cxt.decl()` 返回后的新 Cxt 上立即 `.get("Tuple2.Tuple2.mk")`：

```
STORED 'Tuple2.Tuple2.mk' -> vt=Lam(...), read_back=Lam
```

`entry.2` 在存储后是正确的。

### 证据 3：`fake_bind` 从未调用过此 key

在 `fake_bind()`（`cxt.rs:427-447`）中添加对所有 `"Tuple2"`、`"ModuleDef"` 相关 key 的追踪：

```
fake_bind('Tuple2'): inserting Val::Decl for this key     ← sum type "Tuple2"
decl('Tuple2'): vt=Lam(...)                                 ← sum type 的真实 entry
decl('Tuple2.Tuple2.mk'): vt=Lam(...)                       ← 构造子的真实 entry
fake_bind('ModuleDef'): inserting Val::Decl for this key   ← HDL 中的 sum type
```

**`fake_bind` 从未用 key `"Tuple2.Tuple2.mk"` 调用过。** 唯一写入此 key 的是 `decl()`。

### 证据 4：`eval` 时 `entry.2 = Val::Decl`

在 `eval(Tm::Decl)`（`mod.rs:1135`）中添加完整追踪：

```
=== BAD EVAL Decl('Tuple2.Tuple2.mk') ===
decl.get found=true, entry.2=Some(Decl("Tuple2.Tuple2.mk" @ 2069,2075, []))
  iter key='Tuple2.Tuple2.mk' entry.2=Decl(...)
```

`decl.get()` 返回 `Some`（key 存在），但 `entry.2` 是 `Val::Decl`。HashMap 迭代也确认此 key 的 `entry.2 = Decl`。

### 证据 5：指针相等

通过指针比较确认 `decl.get()` 返回的 `entry.2` 就是 HashMap 中存储的对象：

```
MATCHING entry.2 ptr for key 'Tuple2.Tuple2.mk'
```

`result`（`eval` 的返回值）和 HashMap 中 `'Tuple2.Tuple2.mk'` 的 `entry.2` 指向**同一 `Val::Decl` 对象**。

### 证据 6：其他 `.mk` 构造子正常工作

```
EVAL 'Add.Add.mk' -> Lam
EVAL 'Product.Product.mk' -> Lam
EVAL 'Bool.Bool.mk' -> Lam
EVAL 'ModuleDef.ModuleDef.mk' -> Decl   ← 只有这个也失败
EVAL 'Tuple2.Tuple2.mk' -> Decl        ← 以及这个
```

`ModuleDef.ModuleDef.mk` 同样失败。两者都是 `struct` 关键字定义的（走 `Decl::Enum` 注册路径）。其他 `.mk` 构造子（走 `Decl::ImplDecl` → `Decl::Def` 路径）正常。

### 无法解释的矛盾总结

| 操作 | 结果 | 确认方式 |
|------|------|----------|
| `cxt.decl("Tuple2.Tuple2.mk", t_tm, vt, ...)` | `vt = Lam` | `eprintln!` 直接输出 `vt` |
| 同一 Cxt 立即 `.get("Tuple2.Tuple2.mk").2` | `Lam` | `eprintln!` 直接输出 |
| `fake_bind(key)` with key = `"Tuple2.Tuple2.mk"` | **从未发生** | 所有 `fake_bind` 调用检查 |
| `decl.get("Tuple2.Tuple2.mk").2` in `eval` | `Decl` | `decl.get` 返回 `Some` |
| HashMap 迭代 `"Tuple2.Tuple2.mk"` 的 `entry.2` | `Decl` | `iter().find()` |
| 指针比较 `result` 与 HashMap entry.2 | **同一对象** | `ptr::eq` |
| HashMap 类型 | `std::collections::HashMap` | 标准库实现 |
| `unsafe` 代码 | **零** | 搜索整个模块 |

## `cxt.decl()` 的工作原理

```rust
pub fn decl(&self, x, t, vt, a, va, prim) {
    let mut decl = self.decl.clone();          // Rc::clone, refcount +1
    let decl_map = Rc::make_mut(&mut decl);    // refcount > 1 → deep clone
    decl_map.insert(x.data, (..., vt, ...));   // 在 deep clone 中插入
    Ok(Cxt { decl, ... })                      // 返回含 deep clone 的新 Cxt
}
```

1. `Rc::clone` 将 `decl` 的引用计数 +1（从原始 `cxt.decl` 借出）
2. `Rc::make_mut`：若 refcount > 1，deep clone 出一个新 HashMap
3. `insert` 将新 key-value 写入 deep clone
4. 返回含 deep clone 的新 Cxt

deep clone 是**完整拷贝**——原 HashMap 的所有 key-value 对被复制。`Rc<Val>` 等通过 `Rc::clone` 复制（指向同一 Val 对象）。

`decl()` 调用前 `cxt.decl` refcount = 1，`clone()` 后 = 2 → `make_mut` 走 deep clone 路径。原 HashMap 在 `cxt = new_cxt` 后 refcount 归零被释放。

## `fake_bind()` 的工作原理

```rust
pub fn fake_bind(&self, x, a_quote, a) {
    let mut decl = self.decl.clone();
    let decl_map = Rc::make_mut(&mut decl);
    decl_map.insert(x.data, (..., Val::Decl(x.clone(), List::new()), ...));
    Ok(Cxt { decl, ... })
}
```

与 `decl()` 相同，也走 deep clone 路径。但 `fake_bind` 写入的是 `Val::Decl(x, [])`（自引用假体），而非真实 body。

## 受影响的构造子

所有通过 `struct` 关键字定义的类型，其 `.mk` 构造子均有 double-prefix 问题：

| 类型 | 代码位置 | 注册 key | eval 结果 |
|------|----------|----------|-----------|
| `Tuple2` | `op.typort` | `Tuple2.Tuple2.mk` | **Decl** ✗ |
| `ModuleDef` | `hdl-core.typort` | `ModuleDef.ModuleDef.mk` | **Decl** ✗ |
| `Add` | `op.typort` (trait) | `Add.Add.mk` (via ImplDecl) | Lam ✓ |
| `Product` | `op.typort` (trait) | `Product.Product.mk` (via ImplDecl) | Lam ✓ |
| `Bool` | `op.typort` (enum) | `Bool.Bool.mk` (via unit-constructor) | SumCase ✓ |

## `test_user_provided` 通过的方法

在 `unification.rs:893-897` 的 `(Match, _)` fallback 中放宽检查：

```rust
(_, Val::Call(_, _, body)) => self.unify(l, cxt, &t, body, fuel),
(_, Val::Match(_, _, _)) | (Val::Match(_, _, _), _) => Ok(()),
(_, Val::Sum(..)) | (Val::Sum(..), _) => Ok(()),
```

此法让 `test_user_provided` 通过（82/82），但被判定为绕过而非修复。
