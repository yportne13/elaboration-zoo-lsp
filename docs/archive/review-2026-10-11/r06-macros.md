# Review 2026-10-11 — 轮次 6:宏与规范形

> 主题:**macro_rules 定义/展开、片段种类、stringify、展开深度护栏**。
> 35 个探针(`tools/review-1011/r06-macros/`)。**终局:35/35 PASS**
> (若干 quirk/限制以预期固化)。

## 1. 语法事实(实验确证)
- **规则分隔符是 `;`**(`many1_sep((Semi, EndLine?))`)——规则漏分号时,
  第 2+ 条规则泄漏到顶层解析器报 "expected def, found ("(首轮 9 个失败
  的主因);prelude 的 Expr 宏每条规则都带 `;`。
- 片段种类 4:`$x:ident` / `$x:raw` / `$x:param` / `$x:name`;`param`
  匹配 **binder 列表**(`x: A` 形态),不接受 lambda 表达式。
- **表达式位置宏可用**:`macro_rules five { () => { 5 } }` + `def f: Nat =
  five`(首轮预期错了,已修正)。
- `stringify` 只接受标识符;数字实参报 not in scope。
- 未知片段种类(如 `$x:bogus`)**静默接受**,规则永不匹配(无定义期报错)。
- 宏展开的 match 保布局(展开后臂缩进语义正常)。
- 自引用宏在深度 256 处立即报 "macro expansion too deep"(不挂死)。
- 宏名可重定义(后者覆盖);宏名可作 let 绑定名(不触发展开);
  宏遮蔽 prelude 函数名会 redefine 报错。

## 2. 记录的 quirk / 限制(预期已固化)
- **两参匹配器 `($a:ident, $b:ident)` 要求调用形态完全一致**:
  `pair2 (p1, p2)` 调用不匹配(括号进 token 流);`pair2 p1, p2` 同报
  "expected newline"。两参宏实际不可用(P3)。
- `$n:ident` 在转写器里用两次会生成两个同名 def(redefine,预期)。
- 单行 transcriber 内多条 def 需要 `;` 分隔(`def $a: Nat = 1; def ...`)。
- 宏先定义后使用(自上而下);使用先于定义报 not in scope。
- 未匹配的调用报 not in scope(用宏名),错误信息不指向规则表(P3)。

## 3. 验证
- 轮内 35/35(RESULTS.md);R5 门禁 66/0 全绿(含 r3/r4/r5 全部 pin)。

## 4. 遗留
- 两参宏调用形态(P3);
- 未知片段种类应报定义期错误(P3);
- 未匹配调用的错误信息质量(P3)。
