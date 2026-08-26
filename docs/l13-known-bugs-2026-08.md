# L13 已知 Bug 记录（2026-08-06）

> 两个由 adder-tree / calc-example 任务中实测发现、已定位但**未修复**的编译器 bug。
> 记录触发条件、机制链（含代码位置）、影响与修复方向，供后续修复时参考。

---

## Bug 1：文件末尾的声明被静默丢弃（parser）

**严重度**：中。静默丢声明——既不报错也不生效，LSP 里表现为"最后一行不工作"。

**现象**：`def f = calc { ... }`（或任何匹配器以 `}` 字面量结尾的宏 body：calc / when / switch / module）
后面**紧跟的那条声明，如果是文件最后一条，会被静默丢弃**，只留一条 `Expect(EndLine)` 解析错误。
实测案例：`examples/theorem_proving.typort` 的 `println(subst_eg_calc)` 直接跟在 calc body 的 def 后且是最后一条，被丢；
当时用"文件末尾补一条非宏 println"（`println(subst_eg)`）绕过。

**机制链**（按代码顺序）：

1. **宏字面 token 匹配器吃换行**：`MacroMatcher::Token` 匹配成功后执行
   `kw(TokenKind::EndLine).option()`（`src/L13_namespace/parser/macros.rs:44-46`）——
   匹配到 `}` 后可选消费紧跟的一个 EndLine。when/switch 风格宏依赖此行为
   （`parser/mod.rs:241-243` 注释说明）。
2. **calc 宏匹配器以 `}` 结尾**（`src/prelude/core/calc.typort` 大括号形式），
   所以 def body 解析完时，def 与下一条声明之间的换行已被宏消费。
3. **顶层声明循环** `many1_sep_skip`（`parser/mod.rs:211-278`）用 `kw(EndLine)` 作分隔符；
   分隔符缺失时走 `skip_until_decl` 同步。救援检查 `is_decl_start → continue`
   （`parser/mod.rs:249-261`，处理"宏吃掉分隔符"的隐含分隔符情况）**被嵌套在
   `Some(at_sep)` 分支内部**。
4. **EOF 缺口**：受影响声明是**文件最后一条**时，`skip_until_decl` 在剩余输入中找不到
   任何"EndLine + 声明关键字"同步点 → 返回 `None` → 循环 `None => break`
   （`parser/mod.rs:273`）——`is_decl_start` 救援执行不到，残留声明未消费。
5. **leftover 处理**（`parser/mod.rs:324-328`）：剩余 token 非空（且非 EOF）→ 推一条
   `Expect(EndLine)` 错误，返回已收集的声明——**残留声明静默丢弃**。

**为什么空行救不了**：词法器把连续换行折叠成**一个** EndLine token（`lex.rs:286` 一带），
照样被宏吃掉。

**修复方向**（未修）：把 `is_decl_start` 检查从 `Some(at_sep)` 分支提出来放在 `skip(input)`
之前（先看当前位置是否直接以声明关键字开头，是则 `continue`）；或 `None => break` 前检查
剩余 input 是否非空且以声明关键字开头。注意保持 recover 语义（不要吞掉真正的错误恢复路径）。

---

## Bug 2：match 分支深处内联 trait 方法 → 元变量悬空 → `lvl2ix` 下溢 panic（checker）

**严重度**：高。debug 构建直接 panic（`subtract overflow`）；release 下 wrapping 成巨大
usize 行为随机。实测案例：加法树例子在 match 分支深处（5 层 binder）内联写
`t.cast(证明)` 触发；当时靠把 `.cast` 包进顶层助手函数 `cast_uint`（浅上下文调用）规避。

**机制链**：

1. **元变量带"剪枝 spine"**：`fresh_meta`（`src/L13_namespace/mod.rs:1142`）创建普通元变量时
   包成 `Tm::AppPruning(Tm::Meta(m), cxt.pruning)`——`cxt.pruning`（`cxt.rs:98`，每个 binder
   进入时 `prepend`，`update_cxt` 时 `change_n`）是 meta 解里**允许出现的变量集合**；
   unify 赋值时检查"解引用变量 ⊆ pruning"。
2. **trait 实例元变量**：类型为 `Val::Sum(_, _, _, true)`（trait 目标）时走 `solve_trait`
   （`fresh_meta` 第一行即尝试）；失败则 `new_meta(a, cxt.clone(), ...)` 并记入
   `trait_metas`。`.cast`（`Cast` trait 方法）的实例查找即此路径。
3. **触发**：分支深处创建 Cast[Self, U] 元变量时，当时的 pruning（按"出现变量"计算）只含
   `[7,6,5,4,0]`——**缺 `width`（level 1）**。即那一刻出现变量集合视图不完整（goal 类型
   spine 只含部分 binder，最外层参数未计入），但解**必须**引用 `width`（cast 目标类型
   `UInt[w + log2Up n]` 含 w）。
4. **后果链**：unify 赋值因解引用 pruning 外变量被拒 → **元变量悬空** → 顶层检查
   （`elaboration.rs:132` 一带的 `no_metas` 检查/quote）遇到悬空 meta → quote 出引用超出
   当前上下文的 level → `lvl2ix(l, x) = l - x - 1`（`src/L13_namespace/mod.rs:307-309`）
   在 `x > l` 时减法下溢 → debug panic（实测 `lvl2ix subtract overflow: l=3, x=5`）。

**修复方向**（未修，二选一或都做）：
- (a) 根治：trait 元变量创建时的 pruning 应基于**完整上下文**而非那一刻的"出现变量"视图
  （根因在 `solve_trait`/goal 处理时上下文视图不完整）；
- (b) 防御：`no_metas`/quote 对悬空 meta 报普通错误而非 panic；`lvl2ix` 改用 checked/
  saturating 运算把 panic 变成可诊断错误。

---

## 后续发现（2026-08-26 追记）

同族第三例：trait 实例的 **Nat 类型参数**未在调用点实例化——顶层报 `can't unify`，
参数化 module 内**静默**生成无位宽的 `wire x;` / `reg d;`（`regNext` 同样中招），
方法调用路径再叠加上述 `lvl2ix` 下溢。复现矩阵与机制链详见
**`l13-typeclass-instance-nat-param-bug.md`**。

**状态（同日）**：顶层固定宽度已修（`solve_trait` Phase 2 unify 后重新 eval，
方法闭包捕获已解实例参数）；参数化 module 场景已加 HDL004 显式警告（原静默）；
`lvl2ix` 改 checked 运算、panic 消息指名根因。参数化场景的根治需 meta 解支持
消费点参数化（架构级，见该文档"修复方向"3）。
