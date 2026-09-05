# L13 → L06/07/08 特性移植审计（2026-09-05）

背景：L06/07/08 已从 L13 分批移植了 resilient parser 组合子（1c6acf1 /
6727383 / 1c3afbe）、重定义报错（fake_bind，6816dba / 9ca7996 / 1ce7f44）与
类型注解的 universe 定向报错（check_universe 轻量移植，9129cc6 / 95b49b5 /
21bab3e）。本审计逐项核对 L13 还有哪些**属于低层语言范围的通用机制**、移植
落点是否完整，以及剩余差异哪些是移植缺口、哪些是 L13 的契约变更（不应回灌）。

## 结论一览

| L13 特性 | L06 | L07 | L08 | 处置 |
| --- | --- | --- | --- | --- |
| fake_bind 重定义查重 | ✅ | ✅ | ✅ | 已移植 |
| fake_bind 占位（递归 def） | ❌→✅ | ✅ | ✅ | **本次补齐 L06** |
| ty_precheck Var 的 decl 表回退 | ❌→✅ | ✅ | ✅ | **本次补齐 L06** |
| pretty 越界退化（go_ix / AppPruning） | ❌→✅ | ✅(部分) | ✅(部分) | **本次补齐 L06** |
| no_metas 未解 meta 检查 | ❌ | ❌ | ❌ | 不移植（契约冲突，见下） |
| check_universe Flex 主动求解 | ❌ | ❌ | ❌ | 不移植（架构冲突，见下） |
| 枚举构造子裸名别名查重 | — | ❌ | ❌ | 不移植（契约锁定，见下） |
| unify/force fuel | ❌ | ✅ | ✅ | 不移植（无可触发失控类，见下） |
| parser Cut / 顶层恢复 / 多错误外露 | ❌ | ❌ | ❌ | 刻意搁置（1c6acf1 明言），L12 已有整套，是否跟进属层目标决策 |
| namespace / typeclass / macro / derive / Verilog / hover / fixes | — | — | — | L13 专属，低层语言范围外 |

## 本次补齐（参考版 + bump 孪生同步，Ok 逐字节 / Err 判定 parity 保持）

### 1. L06 递归 def（fake_bind 的另一半）

L06 原移植只做了 `decls.contains_key` 查重（`redefine`），def 登记发生在体
检查之后，Var 臂只查 `src_names`——递归 def 报 `error name not in scope`，
而 L13 里 `def f = ... f ...` 合法（fake_bind 在体检查前插入指向自身的
中性占位，Var 解析有 decl 表回退）。

- `elaboration.rs` Def 臂：查重之后、体检查之前登记占位
  `Val::Decl(name, [])`（类型 = 已检查的 vtyp），体检查完成后真实值覆盖
  登记；检查失败时 run 整体 Err，占位不外泄。
- `elaboration.rs` Var 臂：src_names miss 后回退 decl 表，命中返回
  `Tm::Decl(name)` + 登记类型（检查期即占位的卡住 Decl 头，求值期查表）。
- `bump_spine_iter.rs`：同款三处（ty_precheck / infer Var / infer Def），
  占位为 `XCell::Decl` 单元。
- 语义边界（与 L13 一致）：bare 自引用（`def n = n`）的值是卡住自身头，
  可正常归约/打印；体**应用**自身的递归（`def f(x) = f x`）在归约层经
  decl 表 delta 展开，无基底情形即发散——`println f` 引读 λ 体同样发散。
  这是 eval 层展开的固有语义（L13 的 eval 同样无界），测试只钉
  elaboration 判定。
- 类型注解位先于占位插入检查（L13 同序）：注解位自指仍报
  name-not-in-scope。
- L06 ty_precheck 的 Var 臂同时补上 decl 表回退（L07/L08 的轻量移植
  本来就有，L06 漏了）——`ty_precheck` 对齐至此三层一致。

### 2. L06 pretty 两处 panic → 优雅退化（对齐 L13）

- `go_ix` 名字表短于索引时 `panic!("Variable index out of bounds")` →
  返回固定文案（L13 pretty 同款；显示路径绝不能崩）。
- `go_app_pruning` `unreachable!()` → 按 L13 `go_pr_inner` 移植：掩码槽
  与名字表按位置配对，保留槽打印 binder 名（`_` 槽退化 `@序号`），名字
  表不足时退化位置占位。
- 孪生版共用参考版 pretty，无需改动。

## 评估后不移植（附证据）

### no_metas 未解 meta 检查（L13 elaboration.rs:975-1089）

L13 在 Def 体检查后扫残留未解 meta 并报错。但低层的 `?N` 公理/洞显示是
**被测试锁定的公开契约**：`tests/l06_blackbox_v2.rs:194-195`、`:270` 断言
`def s : String = _; println s` 输出 `?0`；`tests/l07_blackbox.rs:579` 一带
断言 `def n: Nat = _` 输出 `?0` 且这是 L07/08 制造卡住值的标准习语（L13
自身无此习语——其测试无 `= _` 体，卡住值走 get_global prim 路线）。移植
即推翻三层自身的黑盒契约，属 L13 的契约收紧而非通用机制缺口。

### check_universe 的 Flex 主动求解分支（L13 elaboration.rs:533-586）

L13 的 check_universe = infer + 分类（Flex 经 invert/prune/rename 主动求解
为宇宙，带副作用）。低层的 ty_precheck 是**零副作用的语法预检**（注释明
言），宇宙把关交主检查路径的 unify——两套架构各自自洽。移植 Flex 分支需
把预检改成 infer 式带副作用检查，且 L13 的"注解必须先是宇宙"纪律与低层
"注解由体检查 unify 把关"的语义（含 `?N` 显示契约）冲突。

### 枚举构造子裸名别名查重（L07 elaboration.rs:340-345 / L08 同）

"裸名后注册者覆盖"是 L07/08 **被测试锁定的设计**：
`tests/l07_blackbox_v2.rs` `v2_dup_ctor_last_wins_with_dotted_disambiguation`
断言 `enum ColA { red }` + `enum ColB { red }` 后 `println red` 输出
`ColB::red`（限定名 `ColA.red` 消歧）。L13 只注册限定名、无裸名别名，无
"对齐"目标可言；改成查重即推翻该层自身语义。

### unify/force fuel（L07 mod.rs:936-952 一带）

fuel 在 L07+ 防的是 decl 展开的 force、Match 重选与 pm_solve 的失控类。
L06（参考版与孪生）的 force 只展开**无环**的已解 meta 链（solve→rename 带
occurrence check，环不可构造），force/unify 均不展开 decl 值，亦无
Match/pm 机制——原判"无限递归风险"在 L06 无可触发的失控类，移植即死代码。
递归 def 引入的 eval 层 delta 展开发散是真发散（与 L13 一致，L13 的 eval
同样无界），不是 fuel 的管辖范围。

## 移植落点核验汇总（既有特性）

- **重定义查重覆盖面**：L06 撞 builtin/String/先 def ✓（decls 含全部
  builtin）；L07/08 撞 builtin/def/enum 名 ✓（struct 经脱糖为 enum，同名
  路径被 Enum 臂覆盖）。
- **check_universe 轻量移植注解位**：Def 折叠类型 / let 注解 / Π 域余域 /
  enum 参数 / 构造子 binder 与 `->` 注解 / struct 字段（经 Pi 链）——三层
  全覆盖 ✓；L06 的 Var 分支 decl 表回退缺口本次补齐。
- **resilient parser 底料**（Parser trait、IError 带 span、双态错误、
  Expect* 消息、many1/many1_sep）三层在位 ✓；Cut/恢复/多错误外露未移植
  （刻意，见一览表）。
