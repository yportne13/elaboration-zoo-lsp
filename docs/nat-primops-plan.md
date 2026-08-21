# Nat 算术 primop 化 —— 设计分析与交接笔记

> 状态:**未实施**(仅完成调研与设计,代码零改动)。
> 前置工作:native u64 Nat 表示已落地(f02d975),其后续修复见下文「已完成」。

## 0. 背景与动机

native-Nat 提交(f02d975)把具体 `succ^n zero` 压缩为 `Val::Nat(u64)`,但 prelude
的 `+ - * / %` 仍是**用户层递归定义**(`src/prelude/core/nat.typort`):

- `nat_add_helper`:对 y 递归,`n+m` 总步数 O(m)
- `nat_mul_helper`:叠加加法,O(n·m)

native 表示只带来常数加速(每步 match O(1)、构建 O(1)、force 不重走链),
**算法复杂度不变**。Lean/Agda 的做法是把运算下沉为字长算术原语,即本文档方案。

唯一已有的算术类内建是 `nat_to_dec`(十进制打印),已经 O(1)
(`cxt.rs::count_nat_forced` 的 `Val::Nat(k)` 快路径)。

## 1. 已完成(本次交接前的 3 个 commit)

| commit | 内容 |
|---|---|
| `4c7fbcd` | fix(l13): val_match/vals_eq_ground 的 native Nat vs 卡住链交叉匹配 + 4 测试 |
| `b91a072` | refactor(l13): 共享 `is_nat_sum`(mod.rs)+ `nat_step_value` checked_add |
| `9968d9f` | fix(l13): unify_pm 交叉分支补 `is_nat_sum` 门控 |

基线:L13 335/335 通过。L07–L12 有 49 个**历史遗留**失败(父提交同样红,与本线无关)。
性能基线:`probe-out.txt`(每次全量跑 examples 后自动刷新的耗时日志);
prelude 固定成本约 16.1s(native-Nat 前 17.6s)。

## 2. 机制调研结论(已核实,含代码位置)

### 2.1 PrimFunc 执行路径

- decl 表项第 6 位携带 `Option<PrimFunc>`(`mod.rs:185` 的 `Decl` 类型别名)。
- **两个触发点**,行为一致:
  - eval 期 `v_app`(`mod.rs:1957`,Decl arm 在 1964-1979):应用参数时立即触发;
  - force 期(`mod.rs:1817-1829`):对卡住 `Val::Decl(x, sp)` 再尝试。
- prim 返回 `None` ⇒ 值保持为卡住的 `Val::Decl(name, spine)`(这就是"卡住的
  prim 应用"形态,后续 force 会再次尝试)。
- **spine 顺序约定**:spine 按 prepend 累积(iter 顺序 = 反序),取 args 时
  `collect()` 后 `reverse()` 得自然顺序(mod.rs:1819-1823、1968-1972)。
  手工构造卡住 Decl 时必须按同约定:`List::new()` 依次 `prepend(arg_n ... arg_1)`
  —— 即**从最后一个参数开始 prepend**。
- 注册模板:`Cxt::add_builtin` + `register_nat_to_dec`(`cxt.rs:437-459`),
  类型用 `tm_pi(&[("x", tm_decl("Nat")), ("y", tm_decl("Nat"))], tm_decl("Nat"))`。
  注册时机必须在 nat.typort 加载之后(同 nat_to_dec,挂点 mod.rs:2778 与 6023 两处)。

### 2.2 错误信息里的运算符恢复(不要破坏)

- `Infer.symbol_table: HashMap<(helper_name, argc), op_symbol>`(mod.rs:1004),
  impl 运算符方法注册时自动写入(elaboration.rs:1300、1544),键是**方法体头名**。
- 方法体从 `nat_add_helper this that` 换成 `nat_add this that` 后,恢复表自动变为
  `("nat_add", 2) → "+"`;守门测试
  `legacy_tests::test_operator_symbol_recovery_in_errors`(legacy_tests.rs:4845)
  断言错误信息含 `x + y` 且**不含**旧 helper 名——换名后天然满足,但必须跑它确认。

### 2.3 外部依赖盘点

- `show.typort:36-40` 引用 `nat_sub` 与 `pred`:nat_sub 变 primop 后调用方式不变;
  **pred 保持递归 def 不动**。
- `nat_max`/`nat_min`:无运算符绑定,非热点,**保留递归 def 不动**(少动少错)。
- calc_tests / legacy_tests / mod.rs 内嵌测试输入各自定义同名 helper,
  与 prelude 改动无关(已核实)。

## 3. 计算规则表(核心资产,逐条对应旧递归定义的 unfold 行为)

原则:**prim 必须精确复刻旧定义的可归约性**,否则 definitional equality 变化会
打碎 prelude 里以 `rfl` 写成的证明。`None` = 返回卡住 Decl(合法降级)。

记号:`Nat(k)` = 具体值;`succ⟨d⟩` = 卡住 succ 链
(`SumCase{ typ≈Nat, index:1, datas:[(_, d, _)] }`,判定用 `is_nat_sum(force(typ))`)。

### nat_add(x, y) —— 旧:`match y {0=>x; succ n=>succ(add x n)}`,归约性只看 y

| 条件 | 结果 | 保卫的证明/用法 |
|---|---|---|
| `y ≡ Nat(0)` | 返回 x(原值) | `add_zero_right(a): Eq (a+0) a := rfl` |
| `x,y ≡ Nat(a),Nat(b)` | `checked_add`,溢出则 None | 具体计算 fast path |
| `y ≡ Nat(k>0)`(x 非具体) | 迭代构建 `succ^k x`(O(k) 次 nat_succ_shape) | `len + 1` 等宽度表达式,count_nat_forced 依赖可走性 |
| `y ≡ succ⟨d⟩` | `succ⟨nat_add(x, d)⟩`(单步,内层交给后续 force) | `add_succ_right(n,m): Eq (n+succ m) (succ (n+m)) := rfl` |
| 其余(y 完全卡住) | None | 旧行为:match y 卡住 |

注意:x 是否具体**不影响** add 的归约性(旧定义只 match y),规则顺序如上即可。

### nat_mul(x, y) —— 旧:`match y {0=>zero; succ n=>add x (mul x n)}`

| 条件 | 结果 |
|---|---|
| `y ≡ Nat(0)` | `Nat(0)` |
| `x,y ≡ Nat(a),Nat(b)` | `checked_mul`,溢出则 None |
| 其余 | None |

部分展开(`x * succ n ⇒ add x (mul x n)`)**刻意不做**:prelude 无 mul 相关
rfl 证明,hdl 全具体。若未来出现依赖,再补(需构造嵌套卡住 add,复杂度高)。

### nat_sub(x, y) —— 旧:`match x {0=>0; succ k=>match m{0=>succ k; succ l=>sub k l}}`,归约性先看 x

| 条件 | 结果 | 备注 |
|---|---|---|
| `x ≡ Nat(a), y ≡ Nat(b)` | `a.saturating_sub(b)` | 截断语义与旧递归一致(n 耗尽得 0) |
| `x ≡ Nat(a)`,y 卡住 | None | 旧:外层 match 已进 succ 分支,内层 match y 卡住 |
| `x ≡ succ⟨dx⟩`,`y ≡ Nat(0)` | 返回 x | `succ k - 0 ≡ succ k` |
| `x ≡ succ⟨dx⟩`,`y ≡ succ⟨dy⟩` | 卡住 `Decl("nat_sub",[dx,dy])` | 让 force 迭代推进 |
| 其余(**含 x 为 rigid 的 `x - 0`**) | None | **陷阱**:rigid x 时旧定义卡住,不可返回 x! |

### nat_div(x, y) / nat_rem(x, y) —— 仅具体值 fast path

- `div`:两参数具体 ⇒ `y==0 ? x : x/y`(旧定义:x=0,y=0 → zero;x>0,y=0 → x,
  统一为"y==0 返回 x"恰好覆盖)。其余 None。
- `rem`:两参数具体 ⇒ `y==0 ? x : x%y`(抽样验证过 3%5=3、5%3=2 与递归一致)。
- 无证明依赖,无需部分展开。

### 辅助构造

```rust
fn nat_succ_shape(decl: &Decl, inner: Rc<Val>) -> Option<Rc<Val>> {
    let typ = decl.get("Nat").map(|e| e.2.clone())?;   // 与 quote_nat 同款查找
    Some(Val::SumCase {
        is_trait: false, typ, index: 1,
        datas: Rc::new(vec![(empty_span(SmolStr::new("n")), inner, Icit::Expl)]),
    }.into())
}
```

## 4. 实施步骤建议

1. cxt.rs:新增 5 个 prim 函数 + `nat_succ_shape`/卡住 Decl 构造 helper。
2. `register_nat_to_dec` 内追加注册(或改名 `register_nat_builtins`),
   名字:`nat_add` / `nat_mul` / `nat_sub` / `nat_div` / `nat_rem`
   (**nat_sub 与现有 def 同名,必须删掉旧 def**,见 §2.3)。
3. nat.typort:五个 impl 方法体改为 prim 调用;删除
   `nat_add_helper` / `nat_mul_helper` / `nat_div_helper` / `nat_rem_helper` /
   `def nat_sub`;更新第 32/36 行注释。
4. 跑验证清单(§5)。
5. 基准:对比 `probe-out.txt` 中 `T_02-arithmetic` / `T_12-arithmetic2` /
   prelude 固定成本;另可用大字面量脚本(如 `println (10000 + 10000)`、
   `println (300 * 300)`)前后计时,数字写进 commit message。

## 5. 验证清单(全部必须绿)

- [ ] 全量 L13(prelude 加载本身即回归:add_zero_right / add_succ_right /
      add_zero_left / add_succ_left / add_comm / add_assoc 都是 rfl 或归纳证明)
- [ ] `legacy_tests::test_operator_symbol_recovery_in_errors`(§2.2)
- [ ] `legacy_tests::test_custom_operator_symbol_recovery`(用户自定义运算符路径)
- [ ] 新增正确性测试:println 断言 `17+25=42`、`7*6=42`、`10-3=7`、`10-20=0`、
      `7/2=3`、`7%2=1`、`x/0=x`、`x%0=x`(x 具体)、`0-m=0`
- [ ] show.typort 相关输出(Ordered 比较)不回归
- [ ] hdl examples 输出字节一致(probe 流程既有断言)

## 6. 明确不做 / 已知取舍

- `pred` / `nat_max` / `nat_min` 保持递归定义(无热点证据,少动少错)。
- mul/sub/div/rem 的部分展开(符号情形逐步重写)不做,理由见各表备注;
  若做,须先补齐对应 rfl 级证明作为行为锚。
- u64 溢出策略:一律 None 回落卡住,不 panic、不回绕(与 nat_step_value 的
  checked_add 一致)。
