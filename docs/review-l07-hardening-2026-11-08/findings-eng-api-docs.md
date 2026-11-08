# L07 工程面 review（reviewer-eng-api-docs）

> 评审对象：`F:\projects\hermes\elaboration-zoo-lsp`，`git diff 641c52fe..008f42ed`
> 负责切片：`75cad763`（quote 迭代化 + pretty 定深截断）、`3221433e` + `26108306`（Error 可选 Span / 解析错误 span）、
> `551ad1f2`（σ 边界钉 + 计数 / 设计稿 §10）、`86f431a4`（with-K 文档）、`503c3187` 的 `Pattern::pretty` 部分。
> 方法：逐 commit `git show` + 逐分支对照 `75cad763^` / `75cad763` 的 `mod.rs` 全文、全仓 `git grep`、静态测试计数、
> 本机 `rustc 1.98.1` 栈探针（未运行 cargo；测试绿由 Lead 统一实测提供）。
> 标注：【证实】= file:line/diff/可复核计数；【推断】= 由代码推出未运行；【未验证】。

## 结论

工程面四项改动（quote 迭代化、pretty 截断、Error/Span 载体、解析错误 span）方向正确，PR 中大多数可机械核验的
声明成立：`Error` 的 `Display`/`{:?}` 输出逐字节不变【证实】；解析/臂级错误文案零漂移【证实】；
README §8 计数 66 / 49 / 53 / 113 / 92 与 HEAD 实际 `#[test]` 数一致【证实】；设计稿 §10 已改掉 HashMap 旧口径
且与实现（持久化单链 + 条件包裹）一致【证实】；with-K 警示在两份文档中同构【证实】；L07 确实未接入 LSP、
仓内无外部 `Error` 构造者【证实】。quote 的 Sum/SumCase/Obj 三条深链与旧递归实现逐分支语义等价、复杂度仍 O(n)【证实】。

**未发现 S1/S2**。发现 2 个 **S3（诊断正确性）**：
1. 解析语法错误的 span 实际指向「失败 top-level decl 的首 token」（首个 decl 失败时就是文件首 token），
   而非 commit/PR 声称的「失败 token 处」；`parse_error_carries_span` 只断言非空/不越界，钉不住位置。
2. `Error::span()` 的偏移是**预处理后文本**的字节偏移；`preprocess` 把注释里的非 ASCII 字符替换成 1 字节空格，
   后续偏移整体前移（`preprocess` 注释自认），LSP 拿到的 range 会错位/可能切在 UTF-8 中间。中文注释在
   本仓测试语料里很常见，P10 的「LSP 前置」因此被高估。

另有 1 个实现细节偏离：`quote()` 的 `Val::VSub` 分支从「move」变成 `Box::clone()`（`mod.rs:1428-1432`），
与同一 commit 记录的「必须 move 不能 clone」纪律相反；仅 fuel 耗尽路径可达，影响低（S3 边缘）。
其余为 S4：PR 的「30 处 Error::new」「全库 987」数字不实/过时、`L07-RISKS §0.1` 自相矛盾且过时、深值回归钉
用 `ManuallyDrop` 泄漏绕开递归 Drop 因此未验证端到端、pretty 截断范围（`Pattern::pretty`/`sum_head_name`/Debug
未截断）、parity 的 Ok 字节 oracle 在 >1024 层失明等。

## 逐项结论

### 1. 迭代 quote（75cad763）——⚠️ 语义等价成立；2 处可观测差异

逐分支对照 `git show 75cad763^:src/L07_sum_type/mod.rs`（旧递归 `quote`，:1359-1443）与 HEAD
`mod.rs:1421-1434`（分派）+ `:1440-1607`（`quote_deep`）+ `:1609+`（`quote_arm`）【证实】：

| Val 形态 | 旧递归 | 新实现 | 结论 |
|---|---|---|---|
| `Sum` | 参数逐个先 quote 值、再 quote 类型，顺序 v1,t1,v2,t2… | `pending=[v1,t1,v2,t2…]` 同序处理；assemble `it.next()` 同序 | 等价（含 `rc_take` 语义不变） |
| `SumCase` | typ 先、datas 声明序 | `pending=[typ,d1…]`、`done` 同序 | 等价 |
| `Obj` | `Tm::Obj(quote(x))` 然后 `quote_sp` 按 List 尾→头（最早应用先）quote 实参；外层 App 的实参序为 head（最后应用） | `pending=[x,a1(head)…]`，按头→尾 quote，assemble `zip(icits).rev()` 折叠 | **输出树等价**；但实参 force 顺序相反（见下） |
| `Lam`/`Pi`/`Match`/`Flex`/`Rigid`/`Decl`/`Prim`/`U`/`Literal*`/`VSub` | 各自臂 | 全部原样留在 `quote_arm` | 等价（逐行同文本） |

- **无漏处理**：`quote_deep` 每帧 `mem::replace` 取走 `pending[idx]`，`force` 一次后按 `Sum/SumCase/Obj` 推帧、
  `VSub` 原地解包重试、其余回落 `quote_arm`；逆向记录 `done` 顺序与旧递归写 `Tm` 的顺序一致。`frame_new` 的
  `unreachable!` 只可能被非法调用触发（仅 `quote()` 的三形态分派与主循环 match 会调用）【证实】。
- **差异 A（顺序，低风险）**：旧 `Val::Obj` 分支先递归 `quote_sp(t, tail)` 再 `quote(u.clone())`，即实参按
  List 尾→头（最早应用者先）force；新实现按头→尾（最后应用者先）。`force` 有燃料副作用（`burn`：solved meta
  展开、Match 重选、frcs lookup 命中各 1 点燃料），故**燃料耗尽窗口内**两侧打印结果可能不同；燃料充足时结果树
  逐字节同构。现有测试无「fuel 耗尽 + Obj 深链」用例【推断】。
- **差异 B（借用/Rc 语义，已证实）**：`quote()` 的 `Val::VSub` 分支现在是
  ```rust
  Val::VSub(ref v, _) => { let inner = v.clone(); self.quote(decl, l, *inner) }   // mod.rs:1428-1432
  ```
  旧版是 `Val::VSub(v, _) => self.quote(decl, l, *v)`（move Box，零拷贝）。新写法对 `Box<Val>` 做一次
  `clone`：对 Rc 深链（SumCase）是浅拷贝（Rc 计数），无爆栈；对 `Box` 深链（Obj/Match 嵌套）是**递归深拷贝**，
  可能多一次 O(n) 复制甚至爆栈；且 `t` 在臂尾 Drop 原值。该分支只在 `force` 返回顶层 `VSub`（fuel 耗尽）时
  可达，影响面小，但它正是 commit 信息里「待处理槽必须 move 出、不能 clone」纪律的反例【证实】。
- **复杂度**：无每步 clone/线性查找退化；每层 1 帧，`pending/done/datas_metas` 三个 `Vec`（≈3 次分配/层），
  总 O(n) 时间 + O(n) 堆；`frames` 增长无 O(n²) 搬移问题。相对旧递归常数上升（旧 SumCase 每层 1 次 `Vec`
  collect），100k 层约 3×10^5 次分配——与「0.17 s」量级不矛盾（测试耗时未跑 cargo 复核）。
- **deep 输出一致性**：fuel 充足时 Sum/SumCase 深链的 Tm 与旧递归产出的树逐层同构（typ 每层 `rc_take` 共享时
  clone 一次浅 `Val::Sum`，旧版同）；「唯一差别应是栈安全」基本成立，差异 A/B 见上。
- 维护性 nit：`quote_arm` 仍保留 `Sum/SumCase/Obj/VSub` 四个**不可达臂**（`quote()` 已先分派/解包），
  不产生警告但会误导后续改动【证实】。

### 2. pretty 定深截断——⚠️ 范围有限；对既有 golden 无影响；无判定造假风险

- 常量：`MAX_DEPTH = 1_024`（`pretty.rs:17`）；标记 `…`（U+2026，`pretty.rs:85`）；实现为 thread-local
  `Cell<u32>` + `DepthGuard`（`pretty.rs:19-29`），在 `go()` 入口判断 `depth >= MAX_DEPTH` 后直接写 `…` 返回、
  不入栈（`:81-89`）。
- 作用入口**只有** `pretty::pretty_tm`（`:260-264`）及其内部的 `go`/`go_app_pruning`/Pi 域 `pretty_tm`
  嵌套调用（`:73-75`、`:153`、`:185`）【证实】。**不覆盖**：
  - `Pattern::pretty`（`parser/syntax.rs:33-51`，递归 + 字符串拼接；`pattern_match.rs:190/242/258` 的诊断用它）；
  - `pretty.rs:268-275 sum_head_name`（沿 App 链递归）；
  - `prepend_pattern_ns`（`:299-308`）、`fresh`；
  - `#[derive(Debug)]` 的 `Tm`/`Val`/`Closure`（`mod.rs:179` 打印 `Rc<Tm>`）；全仓 grep 确认 P9 修复后
    L07 诊断已无 `{:?}` 打值/模式（只剩 `Error` 的 Debug 与注释）→ 当前不可达，但未来新增 Debug 诊断会绕过截断。
- 重入/并发：`DEPTH` 是线程局部，所有 `go` 路径成对 +1/-1，嵌套 `pretty_tm`（Pi 域、AppPruning）**共享同一
  深度预算**，语义正确；panic 展开时 guard Drop 仍会递减；无泄漏。不同线程互不影响【证实（代码）/未跑测试】。
  「截断路径不爆栈」已由 `tests.rs:1914-1915` 在默认测试栈上验证。
- 既有 golden：全仓 grep `…`（U+2026）在 `tests/*.rs`/L07 源码中只出现在注释与新断言 `shown.contains('…')`；
  黑盒 Ok/Err 期望文案无截断标记；深度 >1024 的期望输出不存在（唯一 400 层深值是 `test_deep_pattern_fuel_budget_regression`
  的 `big` def，打印结果是深度 2 的 `Nat::succ(Nat::zero)`）→ **理论上会改写 >1024 层打印文案，但实测试面零命中**【证实】。
- 「截断把不同值打印成相同字符串 → 假等价」：**判定侧无风险**——`pretty_tm` 全部用途都是文案/输出格式化
  （`mod.rs:1722-1723/1925`、`unification.rs:899/911`、`elaboration.rs:163`、twin `entry.rs:290`/`machine.rs:635-636`），
  没有任何等式/判定读 pretty 字符串【证实】。但**测试 oracle 被削弱**：`tests/l07_fast_parity.rs:54-57` 的
  Ok 逐字节对比依赖 pretty，两侧共用同一截断（ref/twin 都用 `super::pretty::pretty_tm`），>1024 层的差异
  会被 `…` 抹平（当前 parity 无深层输出用例，属潜在盲区）【推断】。
- 「截断后仍可能爆栈的未截断路径」：`sum_head_name`（App 链长度）、`Pattern::pretty`/`prepend_pattern_ns`
  （模式嵌套深度）未设深度上限；源码模式由 parser 递归构造，深到能爆栈时 parser 可能先爆，故实际风险低【未验证】。

### 3. Error 载体（3221433e）——⚠️ 声明基本成立，但「30 处」不实、Debug 有一个边角反例

- 实现（`mod.rs:545-585`）：`pub struct Error(pub String, pub Option<Span<()>>)`；`Error::new`（无位置）、
  `Error::at`（带位置）、`span()`；`Debug` 手写 `write!(f, "Error({:?})", self.0)`（`:570-577`）；
  `Display` 只 `f.write_str(&self.0)`（`:579-583`）；`impl std::error::Error`。
- **Debug 逐字节不变**：旧版是 `#[derive(Debug)] pub struct Error(String)`（`git show 3221433e^:.../mod.rs`），
  derive 的 `debug_tuple("Error").field(&self.0)` 与手写 `Error({:?})` 在 `{:?}` 下输出相同字节
  → `Error("...")` 一致【证实】；黑盒 `tests/l07_blackbox_v2.rs:112` 恰好断言 `"Error(\"parse error\")"` 逐字节
  → 该声明有可执行证据。
  **唯一反例**：`{:#?}` 下 derive 会输出多行 `Error(\n    "…",\n)`，手写实现仍是单行（内部 `{:?}` 不继承
  alternate flag）——全仓 grep `{:#?}` 无 L07 `Error` 使用（只有 L02/L09-L13 parser 调试打印和 L13 自有 Error），
  非现实漂移，但「逐字节不变」严格说应加「`{:?}` 下」限定【证实（实现语义）/未运行】。
- `Display` 只打文案 → 解析/臂级错误文案零前缀【证实】。
- `e.0`：旧字段其实**私有**（`Error(String)` 无 `pub`），`.0` 只在 `#[cfg(test)] mod tests` 内使用
  （`tests.rs:30`）；新结构两个字段都 `pub`，属**扩面**而非兼容问题【证实】。
- 全仓 `Error(` 构造/解构：L07 目录内唯一直接二元构造是 `pattern_match.rs:316
  Err(Error(self.errors.join("\n"), self.first_span))`（臂级错误带 span，预期内）；`Error` 结构体/`format!` 文本
  之外无解构模式（无 `Err(Error(msg))`）【证实（git grep）】。仓内其它层的 `Error` 是各自不同定义，不相关。
- `Span` 定义：`src/parser_lib.rs:64-70`（`data/start_offset/end_offset/path_id`），**既有类型**，不是本 PR 新增；
  **0-based 字节偏移**（u32），非 1-based、非字符偏移：lexer 全部按 `&str` 字节长度累计（`lex.rs:116-182`、
  `parser_lib_resilient.rs:401-423` 用 `input.data.len()-x.len()`），字符串内容 span 从开引号后 +1 起（`lex.rs:141-149`）。
  `Span<()>` 泛型语义 = 纯位置（data 为 `()`），`path_id` 随 `run(input, path_id)` 传入。
  `Span<T>` 在 `span` 的**私有模块** `mod parser_lib;`（`lib.rs:6`）里，但 `pub enum Tm`/`pub PatternDetail`
  早已在公开字段/变体中暴露 `Span`（`mod.rs:70-103`）→ `Error` 不引入新的「私有类型进公开接口」类别；
  crate 内 LSP 可正常使用；外部 crate 不能写类型名但可用类型推断读字段/调 `span()`【证实】。
- `Span` 的既有 `PartialEq` 只比 `data`（`parser_lib.rs:82-86`）→ 两个 `Span<()>` **恒等**（`()` == `()`），
  偏移完全不参与比较。对 LSP 消费这些范围本身没影响，但对「未来用 `assert_eq!` 钉 span」是 footgun：
  现有 `tests.rs:2084-2090` 用 `start_offset/end_offset` + 切片断言（正确做法），未踩坑【证实】。
- **twin 侧**：`bump_spine_iter` 复用 `super::Error`（同一类型，`compiler.rs:10`/`entry.rs:11` 的 `use`），
  构造全部 `Error::new`/`map_err(Error::new)`（compiler 12 + machine 19 + entry 1，仿射无 `Error::at`），
  `run_fast` 的错误 `span()` 恒 `None` → 类型一致、行为未镜像（PR §4 已声明）【证实】。
- **「30 处 Error(...) 构造改 Error::new(...)（参考版 + 孪生版）」不实**【证实】：
  commit 实际替换 61 处构造点——参考版 29 处（elaboration 18 + pattern_match 10 + mod 1）、孪生版 32 处
  （compiler 12 + machine 19 + entry 1 处 `map_err(Error)`）；其中 60 处变成 `Error::new(...)`，
  1 处（pattern_match 臂级错误）变成带 span 的二元 `Error(msg, span)`。HEAD 上 L07 目录内
  `Error::new` 调用点 61 个（含 `26108306` 在 `run` 新增的 1 个）、`Error::at` 1 个、直接二元构造 1 个。
  「30」等于「commit 前参考版三文件 `grep 'Error('` 的原始行数」（18+10+2，含 `pub struct Error(String);`
  这行结构体定义），不是构造成本数，也不是「参考版+孪生版」合计。

### 4. 解析错误 span（26108306）——⚠️ 文案零漂移成立；span 定位比声称的粗，且测试钉不住

- 文案逐字节不变【证实】：`parser` 变 `parser_with_span` 的瘦包装（`parser/mod.rs:104-106`）；两条消息的
  `format!` 串原样搬移（`:144-150` 与旧一致）；`run` 用 `map_err(|(msg, span)| …)` 映射（`mod.rs:1910-1915`）；
  `Error` 的 `Display`/`Debug` 不打印 span（见 3）→ 黑盒 `Error("parse error")`（`tests/l07_blackbox_v2.rs:112`）、
  leftover 断言（`tests/l07_blackbox.rs:1301`）不受影响。`tests.rs:2095` 新钉断言 `err.to_string() == "parse error"` ✓。
- **span 实际取点（与 commit 声称不符）**【证实（代码推导），建议 Lead 一行实测】：
  - 残余 token 路径：`Some(t.to_span())`（`parser/mod.rs:149`）→ 恰好该 token（新钉切片断言 `;` ✓ 强）。
  - 语法失败路径：`e` 是 `p_decl.many1_sep(...)` 的 `Err`。`ParserExt::many1_sep`（`parser/mod.rs:84-97`）
    在「零个 decl 被解析」时**用 `i.first()`（剩余输入首 token）新建 EmptyVec 错误**覆盖掉底层错误；
    对 `"def f : Nat = )\n"`，剩余输入是整份 token 表（第一个 decl 解析失败 ⇒ many0_sep 未推进），
    首个 token 是 `def`（偏移 0..3）→ **span = [0,3) 的 `def`，不是 `)`（14..15）**。
  - 非首个 decl 语法失败：`v` 非空 → `many0_sep` 返回 Ok((失败 decl 起点, 已解析)) → 走 leftover 路径，
    报告的不是「无法解析」而是「leftover token `def` @ …」（旧行为不变），span = 失败 decl 的首 token。
  - EOF/截断（如 `"def f : Nat = "`）：同样落到 EmptyVec，span = 文件首 token（而非 EOF 的 end_span）。
  - 因此 commit/PR 所述「语法失败取 `IError.msg` 的 span（**失败 token 处**）」只在「底层错误恰好带非空 span
    且未被 EmptyVec 覆盖」时成立；L07 顶层路径下基本不成立。`err_collect.first()` 回退（`:154-158`）在
    实际可达路径里几乎不可达（主 span 非 0,0 时优先主 span；0,0 只在空 token 流出现，此时收集器必空），
    若真被用到会引用「更早被软恢复的无关错误」，属误导来源。
  - 结论：span 的实用语义是「**失败 top-level decl 的起点**」（首个 decl 失败时=文件头），对 LSP 仍有用，
    但精度声明不实；`parse_error_carries_span` 只断言 `start<end`、`end<=len`、`path_id==0`，
    **没有断言 span 内容**，所以即使位置错误也全绿（`tests.rs:2095-2116`）。
- `Error::new` vs 带位置构造的使用一致性：代码里没有 `new_spanned` 这个名字（任务描述可能是提案名），
  实际 API 是 `Error::at`；`run` 对解析错误「有 span 用 at、无 span 用 new」，其余错误一律 new；
  孪生 `entry.rs:299` 仍 `parser(...).map_err(Error::new)`（无 span，PR 已声明）→ 一致【证实】。
- **额外 S3（新发现）**：span 偏移基于**预处理后文本**。`run` 先 `preprocess` 再 parse（`mod.rs:1910`），
  `preprocess` 把注释字符逐个替换：`out.push(if rc.is_whitespace() { rc } else { ' ' })`（`:2138-2144`、
  块注释 `:2150-2157`）——非 ASCII 注释字符从 `len_utf8` 字节缩成 1 字节空格，后续所有偏移前移
  （每个中文字符 −2 字节）。`preprocess` 自己的注释就写着「非 ASCII 注释内容会使后续偏移前移，仅影响错误消息中的
  偏移数字」（`:2106-2111`）——在 P10 之前这只是文案里的数字；现在它成为**机器消费的 range**，LSP 切片会错位、
  甚至切在 UTF-8 边界中间。臂级 `pat_span` 同源受影响（模式 span 也来自预处理文本）。
  新钉 `error_carries_pattern_span`/`parse_error_carries_span` 都用纯 ASCII 源，未覆盖【证实（代码）/未跑用例】。
- 错误恢复路径的误导 span：除上面的 EmptyVec/首 token 覆盖外，软恢复 `Cut` 会把内层错误 push 进
  `err_collect`（`parser_lib_resilient.rs:288-305`）；当前只在主 span 缺失时消费，故只在极端路径成为
  误导来源，低概率【推断】。

### 5. 深值测试有效性（`deep_value_iterative_under_default_stack`）——✅ 默认栈声明成立；⚠️ 未覆盖 Drop 端到端

- 测试代码 `tests.rs:1831-1916`：普通 `#[test]`，**没有** spawn 线程、没有 `stack_size`（对比同文件其它测试
  `check`/`check_err` 显式 64MB、`test_deep_pattern_fuel_budget_regression` 512MB）。libtest 默认会为每个测试
  spawn 线程：本机 `rustc 1.98.1` 实测探针（standalone `rustc --test`，`RUST_MIN_STACK` 未设）——
  2500 帧×~1KB 递归在默认多线程模式溢出（dl 栈 <2.5MB，与 std 默认 2MiB 一致）；`RUST_MIN_STACK=8MiB`
  时同用例通过、9000 帧仍溢出；`--test-threads=1` 下 `RUST_MIN_STACK=8MiB` 用例通过（说明仍 spawn 线程）。
  ⇒ **「默认 2 MB 测试栈」声明成立**；`.cargo/config.toml` 的 `/STACK:67108864` 只抬高主线程，不影响测试线程。
  注意：环境变量 `RUST_MIN_STACK` 可把该钉「调松」（仓内文档确实有采用 32MB 的实验记录）→ 钉强弱依赖运行环境【证实（本地探针）/未跑 cargo】。
- 10 万层构造方式：测试内直接用 `Val::SumCase` 链构造（`chain()`，`:1852-1862`），不经过源码/eval；覆盖
  ① `val_mentions_lvl`、② `struct_eq`、③ `quote`（迭代走链校验 100001 层）+ `pretty`（含 `…` 断言）。
  ③ 同时覆盖 quote 与 pretty 两条路径 ✓。
- **覆盖缺口**：③ 对输入值和返回 `Tm` 都 `ManuallyDrop` 泄漏（`:1866/1876/1882/1885/1899`，注释写明
  「返回的 Tm 是 Box 链，必须 ManuallyDrop 泄漏（测试基建）」）→ 该钉只证明「遍历/打印不爆栈」，
  **不证明端到端安全**：真实 `run` 的 println 路径 `ret += &pretty_tm(0, …, &infer.nf(...))`（`mod.rs:1925`）
  会把返回的深 `Tm` 在语句末 Drop（Box 链递归 Drop），孪生 `run_decls` 同（`entry.rs:287-291` 后 `CTm` Drop）。
  README §7.6a 确实把「深值释放是 Rc/Box 链递归 Drop」列为残留，但测试注释把它归为「测试基建行为、非被测路径」
  低估了它（tm drop 是产品路径）→ PR §3 表「10 万层深值 nf / 错误显示 → 正常」应改为「显示遍历不爆栈；
  释放仍是递归 Drop（未解）」【证实（代码）/未跑深值端到端】。
- 测试耗时「0.17 s」未复核（不跑 cargo）；构造量为 100k 节点 × 多次链，量级上可信【未验证】。

### 6. 文档一致性——⚠️ README/设计稿正文已对齐；L07-RISKS §0.1 与 PR 数字有问题

- README §7.3（`:320-327`）与设计稿开头警示块（`docs/l07-dpm-refactor-design.md:7-9`）同构、与实现一致
  （with-K、教学检查器≠证明助手、产品化需补 without-K），`86f431a4` 无代码副作用【证实】。
- README §7.6a/§7.6b（`:336-351`）与代码一致：quote 深链帧式收集器（`mod.rs:1440+`）、`rename_deep` 同构、
  `MAX_DEPTH=1024`/`…`、Sum/SumCase/Obj 三种形态、残留递归 Drop【证实】；`§6` 表末行（`:301`）仍写
  「残留边界见 §7.6（深值的递归 Drop 与 quote/pretty 深路径）」，与 §7.6b「已处理」**自相矛盾**（历史行未回改）。
- README §8 计数**:实际静态核对一致**：
  `tests.rs` 60 个 `#[test]` + 其余 6 个（`parser/mod.rs` 3、`parser/lex.rs` 1、`unification.rs` 1、
  `bump_spine_iter/entry.rs` 1）= 66 ✓；v3 = 47 自有（1 ignored）+ 66 引入 = 113（112 可跑+1 ignored）✓；
  parity = 26 自有 + 66 = 92 ✓；blackbox = 49 文件（48 跑+1 ignored）✓；v2 = 53（51 跑+2 ignored）✓。
  `551ad1f2` 当时写的 64 / 111 / 90 在其时自洽；之后 `30547abf`/`999d617f` 各加 1 个 lib 测试，并由
  `999d617f` 把 README 同步成 66/113/92。因此**任务描述里「README 写 lib 64 / v3 111 / parity 90」已过时**，
  它对应 `551ad1f2` 快照；PR §5 的 66/48/51/112/92 与 HEAD 实际一致【证实】。
- `L07-RISKS.md §0.1`（`:28-53`）**自相矛盾且过时**：
  - 同一表内既有 `P10 🟢 载体+解析已做`（:41）、`P11 ✅`（:42），又有 `P10/P11 ⏳ 未做（LSP 前置项）`（:48）、
    `P4–P8 ⏳ 未做`（:49）——后两行是旧版本残留，与上方 P4/P5/P6/P8 ✅ 冲突；
  - `P14 ✅ 已修` 行的验证列仍写「lib 64 / v3 111 / parity 90」——HEAD 实际 66/113/92（README 已更新），
    即 RISKS 没跟上；
  - 「孪生版现状：仅 P3 未跟修」（:51）与 PR §4「Error span 未镜像」矛盾（P10 也差孪生侧；
    quote 侧孪生本来就是 `quote_iter`（`bump_spine_iter/quote.rs:79`，覆盖前即迭代），pretty 是共享文件
    `pretty.rs`，所以「quote/pretty 未镜像」的说法也不准确）。
- 设计稿 §10（`:190-196`）：已改掉「HashMap O(1)」旧口径，改述「持久化单链 + 条件包裹」，并指向 §9.4
  （= §9 item 4，`:178-183`）；与实现一致（`mod.rs:260-273 lookup_hit` 条件包裹、`:399-409 extend` O(1) cons、
  `:414-431 compose`）【证实】。小瑕疵：「解值不引用已解层级时原样返回、零分配零 fuel」的「零分配」不严谨
  ——`lookup_hit` 走 `e.val.clone()`，`Val::SumCase/Sum/Match` 的 clone 仍会分配 Vec（只是不分配 VSub 包裹）；
  该措辞继承自 §9.4，非本刀新写【证实（代码）】。
- PR 数字：【证实】「30 处」→ 见 §3（实际 60 处 `Error::new` 替换 + 1 处带 span 构造，参考 29/孪生 32）；
  「全库 cargo test --lib 987 passed」（PR `:102`）与 Lead 实测 990 不符（PR 写于更早状态）；
  「孪生版未镜像 P3/quote/pretty/Error span」（PR `:83-84`）中 quote/pretty 表述不准（见上）。
- `tests/l07_fast_parity.rs:8-10` 头注释仍写「参考版递归 quote 的深度吃栈」——quote 已在 HEAD 对
  Sum/SumCase/Obj 迭代化，注释过时（`quote_arm` 的 Lam/Pi/Match 仍递归，措辞需限定）【证实】。
- `l07_fast_parity` 的 Err 判定只比「是否 Err」（`:58`），不比较错误文案 → `Error` 载体变化不受影响 ✓。

### 7. 「L07 未接入 LSP / 无外部消费者」——✅ 成立

- `git grep L07_sum_type`（全仓 tracked）：除 L07 自身目录外，引用者只有
  `README(.zh).md`/docs、5 个 bin（`l07alloc`/`l07bench`/`l07whoalloc`/`pmabbench`/`l06l13mem`，均以
  `#[path = "../L07_sum_type/mod.rs"] mod L07_sum_type;` **各自编入一份私有副本**）、以及 5 个测试文件
  （`l07_blackbox{,_v2,_v3}`、`l07_fast_parity`、`implicit_comma_args`）【证实】。
- `src/ls`、`src/lsp_stdio.rs`、`src/client`、`src/emit`、`src/sim`、`vscode_extension/` 中 **零** L07 引用
  → 未接入项目 LSP；span 的消费方（P10 第三步）确实尚不存在【证实】。
- 因此 `Error` 由 1 元变 2 元的破坏性变化**仓内无受害者**：无 `Error(s)` 直接构造、无 `Err(Error(x))` 解构；
  bins/tests 只用 `run` 的 Ok 输出或 `{:?}` 文本。`lib.rs:52` 的 `pub mod L07_sum_type` 仍是对外 API（本案是单 crate
  多 bin 仓库，无下游 crate），若将来外部 crate 直接用 `Error(s)` 会编译失败——PR 已声明，影响面实际为零
  （字段 0 私有→pub 的扩面反而更大）。LSP 在本 crate 内可访问 `crate::parser_lib::Span`，不阻塞后续接入【证实】。

## 发现表

| ID | severity | 标题 | 证据 | 影响 | 建议 | 置信度 |
|---|---|---|---|---|---|---|
| F1 | S3 | 解析语法错误 span 实际指向「失败 decl 的首 token」，非 commit 所称「失败 token 处」；新钉断言不到内容 | `parser/mod.rs:84-97`（EmptyVec 用 `i.first()` 覆盖底层错误）、`:138-160`；`tests.rs:2095-2116` 只断言非空/不越界；对 `"def f : Nat = )"` 推导 span=[0,3)=`def`，`)` 在 14..15 | LSP 画错 caret（首个 decl 内错误指到 decl 头）；EOF/截断也指到文件头；P10 精度声明不实 | EmptyVec 分支保留底层 `IError`（若有非零 span 优先用它）；EOF 用 `end_span()`；测试改为切片断言（预期会暴露 `def`）；如接受「decl 级定位」则改文案/PR 声明 | 高（代码路径确定；建议 Lead 一行实测确认） |
| F2 | S3 | `Error::span` 偏移相对**预处理文本**；注释中非 ASCII 字符使后续偏移前移 | `mod.rs:2106-2111`（preprocess 注释自认）、`:2138-2144/2150-2157`（非 ASCII→1 字节空格）、`:1910`（先 preprocess 再 parse）；新钉全 ASCII，未覆盖 | 含中文注释的源文件里，LSP range 错位/切在 UTF-8 中间；臂级 span 同样受影响。本仓测试语料大量中文注释，命中概率高 | preprocess 保持字节长度（非空白字符按 `len_utf8` 个空格替换）或建立 offset 映射；补「中文注释 + 后续解析错误」回归钉；在 `Error::span` 文档注明偏移基准 | 高（代码 + 自认注释） |
| F3 | S3 | `quote()` 的 `Val::VSub` 分支 clone 而非 move，违反同 commit 的「move 纪律」 | `mod.rs:1428-1432` vs `git show 75cad763^` 的 `Val::VSub(v,_) => quote(*v)`；commit 信息与 `quote_deep:1521-1524` 注释均强调必须 move | 仅 fuel 耗尽路径可达；Rc 链为浅 clone，Box 链（Obj/Match）为递归深拷贝，可能多 O(n) 复制/爆栈 | 改回 `Val::VSub(v, _) => self.quote(decl, l, *v)`；或按 `quote_deep` 的 `mem::replace` 纪律处理 | 高（diff 已证实；触发面小） |
| F4 | S4 | PR/commit「30 处 `Error::new`」不实 | `git show 3221433e -U0` 逐文件统计：参考 18(elab)+10(pm，其中 1 处改带 span 构造)+1(mod)、孪生 12+19+1(entry 的 `map_err(Error)`)=61 个构造点；其中 60 →`Error::new`。「30」= commit 前参考版三文件 `grep 'Error('` 原始行数（含结构体定义行） | 数字误导 reviewer/后续层移植；不影响功能 | 改为「60 处 `Error::new` + 1 处带 span 二元构造（参考 29 / 孪生 32）」 | 高（可复核计数） |
| F5 | S4 | `L07-RISKS.md §0.1` 自相矛盾且未更新 | `:41-42` 写 P10/P11 已做，`:48` 又写 P10/P11 ⏳ 未做；`:49`「P4–P8 ⏳」与上方 P4/P5/P6/P8 ✅ 冲突；`:39` P14 行仍写「lib 64/v3 111/parity 90」（HEAD 66/113/92）；`:51`「孪生仅 P3 未跟修」与 PR §4「Error span 未镜像」不一致 | 风险登记表不可作为当前状态依据 | 删旧汇总行；P14 行改 66/113/92；孪生现状补 P10 span；与 PR §4 对齐 | 高（file:line） |
| F6 | S4 | 深值回归钉用 `ManuallyDrop` 泄漏，未覆盖递归 Drop 的端到端路径；PR §3「nf/错误显示 正常」过度声明 | `tests.rs:1866/1876/1882/1885/1899`（泄漏输入值+返回 Tm，注释承认）；产品路径 `mod.rs:1925`（println 临时 Tm 会 Drop）、twin `entry.rs:287-291`；README §7.6a 已列残留 | 「quote 迭代 + pretty 截断」只保证遍历/打印不爆栈；`run` 的深值输出/错误显示仍可能在被 Drop 时爆栈；测试不能防回归 | 测试补一条「不泄漏、跑完 Drop」的用例（小深度即可验证 Drop 路径，或给产品路径加显式泄漏/迭代 Drop）；PR 表改为「显示遍历不爆栈；释放递归 Drop 未解」 | 高（代码/注释）；端到端是否实际爆栈未实测 |
| F7 | S4 | pretty 截断范围有限：`Pattern::pretty`/`sum_head_name`/`prepend_pattern_ns`/derive Debug 未设上限；parity Ok oracle 在 >1024 层失明 | `pretty.rs:17/81-89` 只在 `go`；`parser/syntax.rs:33-51`、`pretty.rs:268-275/299-308`；`l07_fast_parity.rs:54-57` 双侧共用同一截断 | 深嵌套模式的诊断渲染仍可能爆栈；>1024 层的 ref/twin 输出差异不会被 parity 发现（当前无用例） | 给 `Pattern::pretty` 也加深度上限（或复用统一深度守卫）；若在意深层 oracle，parity 加 depth>1024 的负向用例说明已接受截断 | 高（代码）；实际触发面低/未验证 |
| F8 | S4 | 新钉强度不足 / 覆盖缺口 | `parse_error_carries_span`（`tests.rs:2095-2116`）不断言 span 内容（F1 因此全绿）；`visibility_boundary…`（`:2126-2154`）只钉 decl 缓存值，README §1.3 还声称「meta 解值也不可见」（`:92-95`）无钉；`error_carries_pattern_span` 切片断言强 ✓ | 关键声明缺可回归证据；边界只钉一半 | 解析 span 加内容断言（按预期值）；σ 边界补 meta 解值半（或收窄 README 声明）；F1 修完后同步 | 高 |
| F9 | S4 | API/Debug 边角：`{:#?}` 输出与旧 derive 不同；`Span<()>` 的 `PartialEq` 恒真；公开字段暴露私有模块类型；`quote_arm` 四个不可达臂 | `mod.rs:570-577` vs 旧 `#[derive(Debug)]`（alternate 格式多行）；`parser_lib.rs:82-86`（只比 data）；`lib.rs:6`（`mod parser_lib;` 私有）vs `mod.rs:551` pub 字段；`mod.rs:1609+` quote_arm 的 Sum/SumCase/Obj/VSub 臂 | `{:#?}` 漂移仓内无使用；`Span` 比较 footgun；外部 crate 不能命名 Span（LSP 同 crate 无碍）；死代码误导维护 | 文档给 Debug 声明加「`{:?}` 下」；`Span` 若给外部消费建议加 `eq_offsets`/手写比较或文档警示；`quote_arm` 死臂删或注明 unreachable | 高（实现/代码）；`{:#?}` 未运行 |
| F10 | S4 | `Obj` 实参 force 顺序与旧递归相反（仅在 fuel 耗尽窗口可观测） | `mod.rs:1440+` `quote_deep` 头→尾处理 vs `75cad763^` `quote_sp` 尾→头；`force` 有 `burn()` 副作用（`mod.rs:765-869`） | 燃料耗尽时诊断文案可能与旧版不同（已是降级路径）；正常路径输出逐字节同构 | 无需改；如追求逐字节等价可让 Obj 帧按尾→头入列；或在 commit/README 记录该顺序差异 | 高（顺序差异）；实际可观测性未验证 |

## 未能验证 / 建议 Lead 实测

1. **F1 的 span 实际值**（预期 `"def f : Nat = )\n"` → span=`[0,3)`=`def`，而非 `)`）：可在
   `tests.rs:2095` 临时加 `assert_eq!(&src[sp.start_offset as usize..sp.end_offset as usize], "def");`
   一行实测（跑完删）。若断言通过则证实 F1；若实际是 `)` 则我对 `many1_sep`/`EmptyVec` 的路径判断有误。
2. **F2 的错位量**：构造「中文注释 + 后续解析错误」源（如 `// 中文\n def f : Nat = )\n`），打印
   `err.span()` 并 `&src[start..end]`；预期切片错位/不在 `)` 上。也可用 `error_carries_pattern_span`
   的模式源加中文注释复现臂级 span 偏移。
3. **F6 端到端**：用 def 链（约 10 万行 `def fN = succ fN-1` + `println fN`）在 **2MB 线程**里跑 `run`，
   观察是 quote/pretty 先过、还是 Tm/Val 递归 Drop（或 parser/eval 递归）先爆——决定 PR「nf 显示正常」的
   可复现结论与 README §7.6a 措辞。
4. **F9 的 `{:#?}` 反例**：`format!("{:#?}", Error::new("x"))` 与旧 derive 形态对比（需编译；预期旧版多行、
   新版单行）。仓内无使用，仅声明精度问题。
5. **PR §5「全库 987」vs Lead 实测 990**：我只静态核了 L07 的 66/112+1/92 等；全库数字以 Lead 实测为准
   （PR 陈旧）。
6. **性能常数**：`quote_deep` 每层 3 个 `Vec` 分配 + 每层 `rc_take` 共享 `typ` 的浅 clone；「0.17 s」声明
   与旧递归的常数对比建议用 Lead 的测试输出（`--nocapture` 或 bench）确认，非必须。
7. **孪生深值输出**：`run_fast` 的 `quote_memo → export → pretty_tm → CTm Drop` 链（`entry.rs:24/287-291`）
   没有对应深值测试；`export` 已迭代，但导出后的 `CTm`（参考版 Box 树）Drop 仍递归。是否与参考版同水平、
   是否需要在 P11 范围外单开一条，建议记录到 L07-RISKS 而不是 PR 表格。
8. **未跑 cargo**（按分工）：以上测试/计数均由静态计数或本机 rustc 探针支撑，`cargo test`/release 数字
   以 Lead 实测为准。
