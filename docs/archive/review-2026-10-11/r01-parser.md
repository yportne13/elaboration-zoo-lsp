# Review 2026-10-11 — 轮次 1:解析器与表面语法

> 目标:对 `elaboration-zoo-lsp`(Typort 依值类型语言 + LSP + HDL→Verilog,约 13 万行 Rust)
> 做十轮多维评审,每轮 ≥30 个实验。本轮主题:**解析器与表面语法健壮性**。
>
> 方法:`tools/review-1011/run_round.py` 驱动 43 个探针
> (`tools/review-1011/r01-parser/*.typort`,每个文件头带 `// probe:` 与
> `// expect:` 断言)逐一过 `typort check`(release 二进制),输出
> `RESULTS.md` 判定表。FAIL 项逐个人工判读:真 bug → 修复;语言 quirk →
> 记录并修正预期;驱动误判 → 修驱动。

## 0. 方法论事故与教训(重要)

首轮 17 个 FAIL 中有相当部分源自**过期二进制**:`target/release/typort.exe`
时间戳停在 9 月 29 日,而 `cargo build --release` 因指纹缓存未重编它
(`elaboration-zoo-lsp.exe` 更新了,typort.exe 没有)。`"a//b"`(字符串内
`//`)等"bug"在过期二进制上复现、在 HEAD 源码上完全正常(经
`run_with_prelude` 与 Backend 级探针双重验证)。**教训已固化进流程:
每轮实验前 `cargo build --release --bin typort` 强制重编并核对时间戳。**

## 1. 实验清单(43 个,全部实跑)

| 组 | 实验 |
|---|---|
| 注释 | e01 EOF 无换行行注释 / e02 嵌套块注释 / e03 未闭合块注释 / e04 多余 `*/` / e39 实参中间行注释 |
| Unicode | e05 CJK 标识符 / e06 NBSP 分词(应拒)/ e07 标识符内零宽空格(应拒)/ e08 BOM / e09 CRLF / e10 Tab 缩进 |
| 数字与宇宙 | e11 前导零与大十进制 / e12 `Type 4294967295` / e13 `Type 4294967296`(F2 钉)/ e14 10^21 大字面量 / e15 负数字面量 / e16 前导 `+` |
| 字符串 | e17 转义 / e18 未闭合 / e19 `//` 在字符串内 |
| 深度与规模 | e20 200 层括号 / e21 3000 层括号(不得崩)/ e22 8000 字符标识符 / e23 300 个顶层 def / e24 空文件 / e25 仅注释 |
| 恢复 | e26 缺函数体 / e27 未闭合 enum / e28 多余 `}` / e29 def 后分号 |
| 分隔符 | e30 调用尾逗号 / e31 参数尾逗号 / e32 括号内空格分隔实参 |
| 表达式 | e33 `*`/`+` 优先级 / e34 紧凑 `->` / e35 双参 lambda / e36 关键字作标识符 / e37 重复定义 / e38 hole / e40 derive / e41 let / e42 显式隐式实参 / e43 match 缩进 |

结果:42 PASS,1 项判读为 quirk(e14)。

## 2. 发现与修复

### F1-1(已修)空文件/仅注释文件被报"expected at least one element"
`parser_with_macros` 顶层用 `many1_sep_skip`,零声明即报错——编辑器里每个
新建空 `.typort` 缓冲区都是一条伪错误。修复:新增 `many0_sep_skip`
(零声明合法;纯垃圾仍由 leftover 检查报错),删除已无调用者的
`many1_sep_skip`。

### F1-2(已修)`Raw::U` 不携带 span(源码里的显式 `//TODO:`)
`Type 4294967295` 的"universe level too large"错误渲染在 **1:1(文件头)**,
不指向肇事 token。修复:`Raw::U(u32)` → `Raw::U(u32, Span<()>)`,parser
在 `Type <num>` 臂填入数字 token 的 span,合成位填 `empty_span`;参考版、
twin(machine.rs)、doc/collect 全部 17 处同步。钉:
`universe_max_level_error_has_real_span`(span=offset 12)。

### F1-3(已修)F2 宇宙溢出修复只落了参考版,twin 机器臂裸 `x + 1`
`bump_spine_iter/machine.rs` 的 `Raw::U` 臂是 `v_u(x + 1)`:u32::MAX 在
debug panic、release 静默回绕成 `Type 0`(`Type MAX : Type 0` 假通过)。
修复:与参考版同款 `checked_add` 错误路径。钉:
`twin_universe_max_level_does_not_wrap`。

### F1-4(已修)块注释不嵌套
`/* a /* b */ c */` 在第一个 `*/` 结束,残余 `c */` 变垃圾 token 触发伪
语法错误。修复:L13 `preprocess` 块注释分支按深度计数(Rust 式);
`tools/review-1011/scan_comment_nesting.py` 扫描全仓 .typort 确认无既有
代码依赖旧的提前闭合语义(0 命中)。钉:`nested_block_comments`
(嵌套 + 未闭合两向)。

### 记录的 quirk(未改,预期已修正)
- **e14**:超大 Nat 字面量(>u64)报 3 条错误且顺序颠倒——先报误导性的
  "find unsolved meta"再报真正的 "does not fit in u64"(parse 错误最后
  到达)。字面量护栏(NAT_LITERAL_ELAB_LIMIT=100000)与 u64 检查都在,
  只是级联噪音。低优先级。
- **e30/e31**:调用与参数列表尾逗号被接受(特性)。
- **e35**:`(x, y) => e` 双参 lambda 不支持(需柯里化)。
- **e40**:`enum { a b }` 单行多构造子不支持(布局敏感,构造子需按行)。
- **e12**:最大可用宇宙层级是 `Type 4294967294`(MAX-1);MAX 报错。
- **Backend/引擎报错分叉**:`def U: Type MAX = Type 0` 经
  `run_with_prelude` 报 "too large",经 Backend `on_change` 报
  "can't unify expected Type MAX-1"(报错路径不同、首错不同)。两路都
  拒绝,不回绕接受——正确性无虞,诊断一致性待后续轮次追。

## 3. 验证

- 轮内:43 探针 42 PASS + 1 quirk(RESULTS.md);
- 回归钉 4 条(`tests/r1_parser_regression.rs`)全绿;
- 全量 `cargo test --no-fail-fast` 门禁:见 commit 信息与本轮结文。

## 4. 遗留

- e14 大字面量错误级联顺序(P3);
- Backend 与直连引擎的错误消息分叉(P3,后续轮深挖);
- e40 单行构造子布局限制是否放开(P4,设计决定)。
