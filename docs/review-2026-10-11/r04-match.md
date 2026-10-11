# Review 2026-10-11 — 轮次 4:和/积类型、模式匹配、穷尽性与 GADT

> 主题:**enum/struct、模式匹配、穷尽性检查、依赖匹配(GADT)、终止性**。
> 43 个探针(`tools/review-1011/r04-match/`)。**结果:43/43 PASS**
> (2 项按"不支持的设计限制"记录为预期行为)。

## 0. 重大方法论事故:驱动判定器缺陷(波及轮次 2/3 的历史结论)

裁决本轮时发现驱动脚本的 `stdout` 判定在**合并输出文本**(含诊断)上做
正则匹配——渲染的行号(`3 │ ...`)和错误文本(`unreachable pattern: 3`)
都能满足 `/3/`,把真实失败的探针误判为 PASS(所谓"i33 时过时不过"的
非确定性假象即源于此,编译器本身完全确定)。修正:`stdout` 判定改为
①不得有任何 error;②只在 `note:` 行上匹配。新增 `warn` 判定类型(匹配
warning 行)。R2/R3 语料随后按修正判定器全部重跑重裁决——**此前"43/43、
44/44"的结论作废**,以本文与 r02/r03 修订后的数字为准。

## 1. 实验覆盖(43 个)

穷尽性 8(缺构造子/全覆盖/通配/Boolean/Nat/Opt/通配后具体臂/重复臂)、
嵌套与深层模式 4、依赖匹配/GADT 6(Vec 索引、Fin、Eq refl 的 J、
dependent motive、索引精化、scrutinee 先归约)、struct 8(基本/参数化/
嵌套/缺字段/错型/多参/构造子模式/字段做 scrutinee)、tuple 4、
sum 5(带数据构造子/递归 enum/限定名/空 enum absurd/单构造子)、
覆盖细节 8(零+通配、遮蔽、match 值参与算术、臂型错、scrutinee hole、
3 深模式、限定名表达式)。

## 2. 发现

### F4-1(已修)终止检查器拒绝注解驱动 λ 的结构递归
`def f: Nat -> Nat = n => match n { case succ(m) => f(m) }`(无参 def、
λ 体)被判 "cannot prove termination",而等价的参数形式
`def f(n: Nat): Nat = match n {...}` 通过。根因:walker 的结构根只取
`params.len()`(此处为 0),λ 绑定者不算根。修复(双引擎成对):
`leading_lam_arity`(数 t_checked 前导显式 λ),params 为空时计入结构根;
params 形式口径不变。钉:`tests/r4_termination_regression.rs`
(正例双引擎通过 + 负例 `def bad2: Nat -> Nat = n => bad2(n)` 双引擎仍拒)。

### 记录的限制(未改,预期化为 error)
- **struct 构造子模式不支持**:`case P6.mk(x, y) =>` 解析错误
  (`expected =>` 发现 `.`)。struct 只能整体绑定或走字段访问。
- **限定名构造子模式不支持**:`case Color7.red =>` 报 unsolved meta;
  模式里必须用裸构造子名。

### 记录的 quirk
- **重复臂静默接受**:`case zero` 出现两次无警告(首臂生效);
  unreachable 检测只在完全覆盖后的额外臂上报。
- **布局敏感恢复的灾难性错误信息**:单行 `match v { case a case b }` /
  单行多字段 struct 触发恢复路径后,报出 ~500 个 `_` 的
  `non-exhaustive pattern: false(_, _, ...)` 伪模式与误导性
  "can't unify (x: ?m) → ?m x"(对 struct)。
- **prelude 裸名优先(D1)在构造子上同样生效**:用户定义 `MyVec` 后,
  裸 `nil`/`cons` 仍解析到 prelude 的 `Vec`;必须限定 `MyVec.nil`。
  `Fin`、`Vec`、`unit`、`id`、`double`、`count`、`eq`、`Show`、`sum`
  等都是 prelude 占用名(探针命名需避开;语法文档可考虑列一份
  prelude 保留名清单)。
- 空 enum 的 `match v { }`(absurd)不支持(报错)。

## 3. 修正后的各轮终局(修正判定器下)
R1 43/43(1 quirk 记录)、R2 43/43、R3 44/44、R4 43/43(2 限制记录)。

## 4. 遗留
- 单行布局违规的恢复错误信息质量(P3,与 R1 e40/m02 同族);
- struct/限定名构造子模式是否支持(P4,设计决定);
- `match v { }` 空 absurd(P4)。
