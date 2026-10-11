# 全仓多维评审总审计(2026-10-11)

> 十轮评审,每轮 ≥30 实验,共 **~330 个实验**;所有改动分门别类 commit。
> 驱动基建:`tools/review-1011/run_round.py`(探针驱动)。
> 每轮报告:`docs/review-2026-10-11/rNN-*.md`。

## 一、轮次与实验计数

| 轮 | 主题 | 实验 | 结果 | 报告 |
|---|---|---|---|---|
| R1 | 解析器/表面语法 | 43 | 43 PASS(1 quirk 固化) | r01-parser.md |
| R2 | 核心求值/转换/宇宙 | 43 | 43 PASS | r02-core.md |
| R3 | hole/隐式/elaboration | 44 | 44 PASS | r03-implicit.md |
| R4 | 和/积类型/模式匹配 | 43 | 43 PASS(2 限制固化) | r04-match.md |
| R5 | 类型类/实例解析 | 40 | 40 PASS | r05-typeclass.md |
| R6 | 宏/规范形 | 35 | 35 PASS | r06-macros.md |
| R7 | 命名空间 + 双引擎一致性 | 30 + 33 | 30/30 + 矩阵全一致 | r07-namespace.md |
| R8 | HDL→Verilog 语义 | 30 | 30 PASS | r08-hdl.md |
| R9 | LSP 行为 | 30 测试(60+ 断言) | 30 PASS | r09-lsp.md |
| R10 | 性能(33 计时维度)+ 门禁 | 33 | 数据齐 | r10-perf.md |

回归钉套件(随轮新增,全部进 `cargo test`):`r1_parser_regression`(4)、
`r3_defaulting_regression`(2)、`r4_termination_regression`(2)、
`r5_typeclass_regression`(3)、`r7_engine_parity`(33 用例矩阵)、
`r9_lsp_probes`(27)。

## 二、修复清单(按 commit)

| commit | 类别 | 内容 |
|---|---|---|
| ffe5b2c2 | fix(parser) | `Raw::U` 携带 span(17 处);空文件合法(many0_sep_skip);twin 宇宙溢出 checked_add 对齐(F2 补孪生侧) |
| bcb4c8ab | fix(preprocess) | 块注释 Rust 式嵌套(全语料扫描确认无破坏) |
| bf268e2e | fix(derive) | 单 case 枚举 Show 走 match 绑定路径(原误用 struct 字段投影) |
| e6e185f0 | fix(class)+fix(term) | 实例记录按 trait 方法序(修静默错值);注解 λ 形式的终止检查误拒(双引擎) |
| c98349cf | feat(diag) | Nat 默认化不再静默:TY001 警告(双引擎 + [typort] 标签) |
| 4×/test+docs | test/docs | 回归钉、探针语料、十轮报告 |

## 三、重要方法论教训

1. **过期二进制**:R1 首轮 17 FAIL 中多数是 `target/release/typort.exe`
   停在 9 月 29 日(`cargo build` 指纹缓存未重编该 bin)。每轮实验前必须
   强制重编并核对时间戳。
2. **驱动判定器缺陷**:`stdout` 预期在合并文本上匹配,渲染行号
   (`3 │`)即可满足 `/3/`,掩盖真实失败(R2/R3 初版结论作废重裁决)。
   修复后:`stdout` 要求 stderr 干净且只匹配 `note:` 行;新增 `warn` 判定。
3. **探针命名纪律**:prelude 占用名(id/double/count/eq/Show/Fin/Vec/
   unit/sum…)会 redefine;match 臂/enum 构造子/struct 字段必须按行
   (布局敏感);宏规则以 `;` 分隔。

## 四、记录的 quirk/限制总表(未修,均已文档化)

- 类型论:惰性 meta 首用单态化;Backend 与直连引擎的错误消息分叉;
  最大可用层级 MAX-1。
- 匹配:struct/限定名构造子模式不支持;重复臂静默;空 match 不支持;
  单行布局违规的恢复错误信息质量差(500 个 `_` 的伪模式)。
- 类型类:父类字典不解析(F5-3,P2);impl 元数不校验(F5-4);约束下
  类型变量无接收者方法;泛型条件实例不支持(prelude 自述)。
- 命名空间:import 别名赢过同文件后置 decl(与文档矛盾);同包成员
  不自动可见;D1 prelude 裸名永久优先(实证)。
- 宏:两参匹配器实际不可用;未知片段种类静默接受;`param` 只匹配
  binder 列表。
- HDL:裸数字字面量是 Nat(易踩);UInt[8]+UInt[4] 不自动扩宽;
  mkInstance 端口连接未测;`module ()` 空名打印。
- LSP:Nat 字面量/binder 无 hover 条目;仅 println 文件 hover 表空。
- 性能:CLI 冷启动 4.9s(prelude 固定成本)是最大杠杆。

## 五、验证口径

- 十轮探针:R1–R8 语料 311 个 .typort 全 PASS(RESULTS.md 齐全);
- 双引擎一致性矩阵 33 用例(错误判定 + println 逐字节一致);
- LSP 探针 27 测试(串行;并行窗口为 harness quirk,已记录);
- 性能:33 计时维度,修复回归护栏通过;
- **终局门禁**:`cargo test --no-fail-fast` 68 个测试目标全绿、0 失败
  (含本轮新增的全部回归套件)。

## 六、遗留项优先级(给下一轮)

- **P2**:F5-3 父类字典解析(subtrait 约束传播);
- **P3**:impl 元数校验;struct/限定名模式;单行恢复错误质量;
  Nat 字面量 hover;import 优先级文档矛盾;两参宏;未知宏片段报错;
  大字面量级联顺序;
- **P4**:`module ()` 空名打印;空 match;`Trait.method` 静态形式;
  prelude 保留名清单入语法文档。
