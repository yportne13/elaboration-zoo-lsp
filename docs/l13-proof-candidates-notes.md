# L13 复杂证明用例探索状况

> 目的：为 legacy_tests 添加类似 `test_prove_term_pure`（纯 Agda 风格、只用 match/rfl/trans/symm/cong 的复杂证明）的用例。
> 用户从候选里选了 **候选 3（pow2 指数加法）** 和 **候选 4（Vec 按位取反与数值关系）**。
> 本文记录探索中发现的**语言限制**、各候选的**可行性与状态**。

---

## 1. 已确认可行的参考

- `test_prove_term_pure`（备份分支 `backup/prove-term-pure-test`）：加法器正确性证明，在完整输入中整体通过。
- 该输入自带引理链：`add_right_eq`、`add_left_eq`、`double_distrib`、`double_mul`、`ps_mul`、`mul_one_left` 等。

---

## 2. 探索中发现的**语言限制**（重要）

这些限制导致**自包含**（单独一个 legacy_tests 用例）的复杂证明**不可靠**：

### 2.1 `+`（Add trait）的定义性归约依赖上下文的 trait 解析状态

- 单独测试：`def t: Eq ((succ zero) + zero) (succ zero) = rfl` **失败**（can't unify）。
- 在完整 prove_term_pure 上下文里：**通过**。
- 先定义任意一个使用 `+` 的函数（如 `def dummy(x: Nat): Nat = x + zero`）：**通过**。
- `nat_add_helper`（prelude 顶层函数，`+` 的实现）直接调用时**始终可归约**（1 步 match）。

**含义**：候选用例若使用 `+`/`*` 做定义性归约，必须先建立 trait 解析状态（定义使用它们的函数，或依赖完整上下文）。

### 2.2 `add_comm` 对开放乘法项卡住

- `add_left_eq` 内部用 `add_comm(c, a)`。当 `a` 是开放乘法项（如 `(succ zero) * k`）时，`add_comm` 的归纳 match 无法对开放项归约，unify 卡住。
- 自建的 `add_left_cong`（构造子归纳，用 `add_succ_left`/`cong_succ`，不用 `add_comm`）可绕过，但仍需验证。

### 2.3 数字字面量在 `Eq` 里 ≠ 构造子

- `def t: Eq 1 (succ zero) = rfl` **失败**。
- `def t: Eq 0 zero = rfl` **通过**。
- 数字字面量（Raw::Nat → build_nat）在某些上下文不参与 1 步 WHNF 归约。

**含义**：候选尽量用构造子（`succ zero`）而非字面量（`1`）。

### 2.4 `rfl` 只支持 1 步定义性归约

- 多步归约（如 `myadd (succ zero) (succ zero)` 需 2 步）不能靠 `rfl`，必须用显式 trans/cong 链。
- `myadd 1 0 = 1`（1 步 match zero）可 `rfl`。

### 2.5 lambda 作为 `cong` 参数可能有问题

- `cong (y => 1 + y) ih`（lambda）失败；`cong double ih`（函数名）可靠。
- 建议用**函数名**或**显式引理**（如 `add_left_cong`）替代 lambda。

---

## 3. 候选 3：pow2 指数加法（`pow2(n+m) = pow2(n) * pow2(m)`）

- **在 prove_term_pure 完整上下文中已验证通过**（`prove_full.typort` + 追加 `pow2_mul`，输出 OK）。
- 依赖 prove_term_pure 的引理：`add_right_eq`、`add_left_eq`、`double_distrib`、`double_mul`、`ps_mul`、`mul_one_left`、`pow2`。
- **自包含版本不可靠**（因 2.1/2.2 的语言限制）。

**结论**：候选 3 可交付，但最好作为 **prove_term_pure 的扩展定理**（master 恢复 prove_term_pure 后追加），而非独立用例。

---

## 4. 候选 4：Vec 按位取反与数值关系

- 设计目标：`to_nat (vec_not v) + to_nat v = 2^len - 1`（或 `ones_val len`，避免减法）。
- 需要 Vec[Boolean] 的 GADT 匹配 + 逐位归纳 + Nat 加法重组引理（`(2a+c) + (2b+d) = 2(a+b) + (c+d)`）+ `bool_not` 互补（`bn(not b) + bn b = 1`）。
- **未完成验证**。构建成本高（需要额外的加法重组引理链，且受 2.x 语言限制影响）。

**候选 4 的可选降级**：
- `vec_not (vec_not v) = v`（双取反恒等，纯 Vec 层面、无减法、无 Nat 代数）—— 较易。
- `bool_not`/`bool_to_nat` 的互补（布尔层面）—— 更简单。

---

## 5. 结论与建议

1. **候选 3（pow2_mul）**：已在 prove_term_pure 上下文验证通过；建议 master 恢复 `test_prove_term_pure`（从备份分支），在其基础上追加 `pow2_mul`。
2. **候选 4（vec_not 数值关系）**：构建成本高；建议降级为 Vec 层面定理（双取反恒等），或继续投入调试。
3. **后续添加复杂证明用例时**，需注意 2.x 的语言限制（`+` trait 状态、add_comm 卡住、字面量、rfl 1 步）。
