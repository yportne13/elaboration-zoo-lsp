# Review 2026-10-11 — 轮次 3:Hole、隐式参数与 elaboration

> 主题:**hole(`_`)、隐式参数解析、双向 elaboration、meta 策略**。
> 44 个探针(`tools/review-1011/r03-implicit/`),全部实跑;FAIL 逐项判读。
> **终局:44/44 PASS**。
>
> ⚠️ **结论修订(2026-10-11 晚)**:本文初版声称的"44/44"建立在驱动
> 判定器缺陷之上(`stdout` 预期在含诊断的合并文本上匹配,行号即可满足
> `/3/`;见 r04 §0)。按修正判定器重跑重裁决后,初版有 11 个探针实为
> 失败(重定义 prelude 名 `id`、单行 match/struct 布局违规等探针侧错误,
> 外加 i44 需要 warn 判定类型)。修正探针后终局 44/44。本文其余分析
> (TY001、惰性 meta、Trait.method)按修正数据复核过,仍然成立。

## 1. 实验覆盖

| 组 | 数量 | 代表 |
|---|---|---|
| hole | 8 | body/let/match 臂/scrutinee/类型位/多 hole/println 直填 |
| 隐式参数 | 10 | 自动求解、显式 `f[Nat]`、命名 `f[A = Nat]`、隐式 lambda、依赖链、部分显式、注解驱动 |
| lambda 检查 | 5 | check 模式、隐式 Pi 插入隐式 lambda、域错报位置、柯里化 |
| meta 与错误 | 7 | 解失败的传播、trait 风格、GADT 隐式、遮蔽、未用隐式 |
| 双向性 | 8 | 无注解 lambda、注解驱动递归、struct 字面量、元数错位、高阶隐式 |
| 混合 | 6 | 显式/隐式参数交错、hole 作为显式隐式实参、三层隐式别名链 |

## 2. 发现

### F3-1(已修)Nat 默认化完全静默 → TY001 警告
`def t: Type 0 = _` 曾在无任何诊断的情况下把宇宙型 meta 默认化为
`Nat`(Lean 式回退,no_metas 检查后的默认化重试)。程序含义被隐形改变。
修复:参考版(elaboration.rs)与孪生(machine.rs,prim.rs ReportCheckIssue
同款推送:行级去重 + StateUndo 记账)在默认化成功时推送
`TY001|<def>||N unsolved type meta(s) defaulted to Nat; write the type
explicitly if this is wrong`,走 CheckIssues 通道(与 HDL 自检同一排水/锚定
机制);`format_check_warning` 按代码族选择前缀(HDL/HDV → `[hdl]`,其余
`[typort]`)。钉:`tests/r3_defaulting_regression.rs`(双引擎:警告出现、
不阻断、println 照常;unification 正常解出与惰性 meta 的场景**不**警告)。

### 记录的 quirk(未改)
- **惰性 meta / 首用单态化**:`def g = y => y` 后 `g(true)` 成功、再
  `g(1)` 报 can't unify——无注解 lambda 的域 meta 在**第一次使用**时求解,
  此后单态。有歧义风险但机制自洽(文档未提,建议记录)。
- **`Trait.method(x)` 静态形式不支持**(prelude `Show.show(3)` 与用户
  trait 同样报错);实例合成只走接收者语法 `x.method()`(`(3).show()` 正常)。
  文档未承诺该形式,按设计限制记录。
- **match 臂与 enum 构造子一样是布局敏感的**(需按行);单行 `match v {
  case ... case ... }` 触发恢复路径,错误信息质量差(报了 ~500 个 `_` 的
  non-exhaustive 伪模式)——错误恢复质量记 P3。
- 字面量无条件为 `Nat`(`Raw::Nat` 臂直接构造 Nat 类型,无 meta 参与)。

### 我方用法纠错
- `def eq:` 撞 prelude 名 → redefine;
- match 臂需按行写(布局);
- `_ = 3` 的类型 hole 由 unification 正常解出(不警告,正确);
- hole 在 codomain 由 body 解出(双向,正确);
- 无注解 lambda 不报 unsolved(惰性 meta,见 quirk)。

## 3. 门禁
全量 `cargo test --no-fail-fast`(含新 2 条 pin)见 commit 记录。

## 4. 遗留
- 单行 match 的恢复错误信息质量(P3);
- 惰性 meta 单态化语义入文档(P3);
- `Trait.method` 形式是否支持(P4,设计决定)。
