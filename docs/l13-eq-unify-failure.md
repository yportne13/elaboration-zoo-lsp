# L13 复杂依赖模式匹配下 Eq 类型合一失败调查

## 背景

在 `legacy_tests.rs` 中添加了一个定理证明风格的测试用例（`test_user_provided`），其中定义了
`g`、`are`、`ale`、`aa`、`dm`、`t` 等一系列函数，最终目标是在 `t` 中证明一个关于 `double(g(n)._1) * g(n)._2` 的等式。

该测试在 `t` 函数的 `succ(m)` 分支失败，错误信息为 `can't unify`，且 **expected 和 find 两边的打印结果完全一致**（`Eq[Nat]​(nat_mul_helper(…), nat_add_helper(…))`）。

---

## 实验方法

通过系统性的插针（`eprintln!("… {:?}", val)`）在以下关键位置输出 `Val` 的内部结构：

- `unify_catch`（`mod.rs`）：在合一失败时输出两边 `Val` 的 `Debug` 表示
- `unify` fallback（`unification.rs`）：在 `_ => Err(Basic)` 处输出未匹配的分支
- 各 `(Decl, Call)`、`(Call, Call)`、`(Obj, _)` 分支
- `Sum("Eq", …)` 参数比较处

---

## 核心发现

### 1. `lvl2ix` 下溢崩溃

`mod.rs:284`:
```rust
fn lvl2ix(l: Lvl, x: Lvl) -> Ix { Ix(l.0 - x.0 - 1) }
```

当 `x >= l` 时，`l.0 - x.0 - 1` 在 debug 模式下 panic。测试中共发生 **5 次**。

**原因**：`unify` 的 `(Decl, _)` 分支在展开 `Decl` 时调用 `quote(&cxt.decl, l, &t)`。如果 `t` 中含有 Rigid 变量，其 level 来自一个**更深（更多 binder）的上下文**，而 `quote` 使用的 `l` 是当前合一上下文的 level，此时 `x >= l` 导致下溢。

**影响**：该 panic 虽然被 `pattern_match.rs:842` 的 `catch_unwind` 捕获（用于 GADT 精化试探），但后续合一处理链条已被破坏，最终合一失败。

### 2. `entry.2` 是自引 `Decl`，不是 `Lam`

尝试在 `v_app(Decl)` 中添加非 primitive 函数的内敛逻辑时发现：对于 prelude 中定义的函数（如 `nat_add_helper`、`nat_mul_helper`），`decl.get(&name)` 返回的 `entry.2`（body Val）是 `Val::Decl(name, [])`——一个自引用，**不是**预期的 `Val::Lam`。

**原因**：函数定义在经 `fake_bind`（`cxt.rs:431`）时，临时插入的 body Val 是 `Val::Decl(x, [])`，用于递归调用。最终 `decl()` 调用（`cxt.rs:486`）应替换为真正的 body（`vt`，来自 `eval(body)`）。但插针显示替换后的 `entry.2` 仍是 `Decl`，说明 `vt` 本身就是一个 `Decl`，即 `eval` 对 function body 的求值结果意外地产生了 `Decl` 而非 `Lam`。

**影响**：`v_app(Decl)` 无法通过 `Val::Lam` 匹配来内敛函数体，只能继续 append spine，导致 `Decl` 的 spine 无限增长。

**怀疑**：`vt = eval(&fake_cxt.decl, &fake_cxt.env, &t_tm)` 中 `fake_cxt.decl` 的 `fake_bind` 条目可能干扰了求值——`t_tm` 内的递归调用 `Tm::Decl(name)` 查找 `entry.2` 得到 `Decl(name, [])`，而这个值又通过 closure 泄露到了 `vt` 中。

### 3. `(Decl, _)` unfolding 的 `quote + eval` 循环不收敛

当前 `(Decl, _)` → `quote + eval` 的设计意图是将 `Decl` 展开为可归约形式。但对于非 primitive 函数：
- `quote` 将 `Decl(name, [(arg, Expl)])` → `Tm::App(Tm::Decl(name), quoted_arg)`
- `eval` 对 `Tm::App(Tm::Decl(name), arg)` → `v_app(Decl(name, []), arg)` → `Decl(name, [(arg, Expl)])`
- 结果不变，回到起点

因此该分支在 fuel 耗尽前无限循环，最终返回 `Err(Basic)`。且中间循环中 `quote` 被反复调用，每次都可能触发 `lvl2ix` 下溢。

### 4. Expected 和 Find 的 Meta 状态不一致

通过 `Sum("Eq", …)` 参数的 Debug 输出发现：

| 参数 | expected | find |
|------|----------|------|
| `A` (implicit) | `Sum("Nat", …)` 已求解 | `Flex(MetaVar(542), …)` 未求解 |
| `x` (lhs) | `Call("nat_mul_helper", Rigid…, …)` | `Call("nat_mul_helper", Flex…, …)` |
| `y` (rhs) | 同上已求解 Rigid | 同上未求解 Flex |

**expected** 经过 `pattern_match.rs` 的 `quote + eval` 循环，所有 meta 已被固化（solved），
**find** 来自 `dm(…)` 的新推导，还带着未解的 meta meta。

合一时 `(Flex(Rigid_spine), Rigid)`：unifier 尝试 `solve(meta, Rigid)`，但 meta 的 spine 不为空且无法 invert，返回 `Stuck` 加入 `meta_contrains`。最终 `unify_catch` 检查 `meta_contrains` 非空 → 报告错误。

### 5. `(Call, Call)` 分支

已添加 `(Call, Call)` 分支（`unification.rs:735-742`），当两侧都是同一函数名的 `Call` 时逐参数合一。插针确认该分支被触发（`nat_add_helper`、`nat_mul_helper` 等）。但该分支不解决根因——失败发生在 `Call` 的参数内部（`Obj(Call("g", …), "_1")` 的 Rigid level 差异）。

---

## 根因总结

```
pattern_match.rs ret_type 重求值 (quote + eval)
  ↓
Val 中 meta 被固化 (Rigid)，但 binder 来自更深层上下文
  ↓
(Decl, _) unfolding: quote + eval 不收敛且触发 lvl2ix 下溢 (catch_unwind 接管)
  ↓
合一时 expected(Rigid) vs find(Flex) 状态不一致 → meta_contrains 非空 → can't unify
```

三处独立的代码问题相互叠加导致最终失败：

| 层面 | 问题 | 影响 |
|------|------|------|
| **evaluator** `v_app(Decl)` | 非 primitive 函数不内联，仅 append spine | `Decl` 无法归约，`(Decl, _)` 展开循环 |
| **unifier** `(Decl, _)` | 用 `quote + eval` 展开，不收敛且 `lvl2ix` 下溢 | 合一失败 + panic |
| **pattern_match** `ret_type` | `quote + eval` 产生不同 meta 状态 | expected/find 结构不一致 |

---

## 已尝试的修复及结果

| 修复 | 文件 | 结果 |
|------|------|------|
| `lvl2ix` 加 bounds check | `mod.rs` | 消除 panic，但不解决根因（用户要求撤回） |
| `v_app(Decl)` 内联 `Lam` body | `mod.rs` | 无效——`entry.2` 是 `Decl` 非 `Lam` |
| `Tm::Obj` 内联 `Call`/`Match` | `mod.rs` | 无效——不触发 |
| `(Decl, Call)` 分支 | `unification.rs` | 无效——不触发（两边都不是 `Decl`） |
| `(Call, Call)` 分支 | `unification.rs` | 触发但不解决根因（参数内部有差异） |
| `(Obj, _)` fallback | `unification.rs` | 无效——不触发 |
| `(Decl, _)` 改用直接 body 内联 | `unification.rs` | 无效——`entry.2` 是自引 `Decl` |

---

## 建议修复方向（按优先级）

### 方向 A：修复 `v_app(Decl)` 以正确内联（最根本）

**问题**：`entry.2` 对于 defined function 应是 `Lam`（实际 evaluator body），而非 `fake_bind` 的 `Decl` 自引用。

**方案**：在 `decl()` 写入最终 entry 后，验证 `entry.2` 的类型。如果仍是 `Decl`，则说明 `vt` 求值有误——检查 `eval(&fake_cxt.decl, …, &t_tm)` 过程中 `fake_bind` 的 `Decl` 如何泄露到 `vt` 中。

**代码位置**：`cxt.rs:431` (`fake_bind`)、`cxt.rs:486` (`decl`)、`mod.rs:657` (`vt` 求值)

### 方向 B：让 `(Decl, _)` unfolding 不使用 `quote + eval`

**方案**：改用 `entry.1`（body Tm）配合 `Tm::Call` + 逐层剥离 `Lam` 的方式做内联，避免 `lvl2ix` 下溢和循环。

**代码位置**：`unification.rs:754-766`

### 方向 C：在 `pattern_match.rs` 中保留 ret_type 的 motive closure

**方案**：不在分支中重新 `quote + eval` `self.ret_type`，而是存储返回类型的 lambda closure（motive），在进入每个分支时用精化后的 scrutinee 做 `closure_apply`，确保 meta 状态一致。

**代码位置**：`pattern_match.rs:387-393`

---

## 测试用例概要

新增测试 `test_user_provided` 位于 `legacy_tests.rs` 末尾，包含：

- `def g(n: Nat): Tuple2[Nat, Nat]` — 递归函数，返回配对
- `def are/ale/aa` — 等式推理辅助引理
- `def dm(x, z): Eq(double(x)*z, double(x*z))` — 乘法分配引理
- `def t(n): Eq(double(g(n)._1) * g(n)._2, double(g(n)._1 * g(n)._2))` — 目标定理

预期行为：输出 `"ok"`。当前行为：在 `t` 的 `succ(m)` 分支合一失败。
