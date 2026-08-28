# HDL def 体硬件语句：实现与问题调研（2026-08-27）

> SpinalHDL 风格诉求：`reg x = UInt[8]` 这类语句不应只限于 `module` 宏体，
> 普通 `def` 函数里也应能写（def 在 module 体内调用时硬件落入当前模块）。
> 本文记录实现过程中发现并修复的三个底层问题，以及两个后续维护需要注意的坑。
> 代码改动见同批 commit（parser / mod.rs / hdl-core.typort / 测试）。

---

## 背景：目标形态

```typort
def delay(x: UInt[8]): UInt[8] = {
    reg d = UInt[8]
    d := x
    d
}
module top {
    input a = UInt[8]
    output out = UInt[8]
    out := delay(a)
}
println(moduleTreeVL(top.create.tree))
```

`module top` 的树里应有 `reg [7:0] d;` 与时钟块 `d <= a;` —— def 在 module 体内
被调用时，其硬件语句记录进**当前** module 树（组件作用域语义）。

实现落地为两部分：
1. **语法**（`parser/mod.rs` `p_def_body` / `p_def_stmt_block` / `p_expr_block_stmt`）：
   `def f(): T = { stmt* }` 花括号语句块，逐条复用 `Expr` 宏具名片段转写
   （与 module 宏体同一机制），末条语句作为块值。
2. **语义**（`mod.rs` `def_replay_memo`）：无参 def 的副作用重放（问题 1）。

---

## 问题 1：无参 def 的副作用被声明期缓存吞掉（核心）

**严重度**：高——静默丢失硬件，不报错。

**现象**：`def mkReg(): UInt[8] = { reg r = UInt[8] }` 在 module 体内调用，
生成的 Verilog 只有 `assign out = r;` 而**没有 `reg [7:0] r;` 声明**；
`def myCounter(w: Nat) = {...}` 之类**有参** def 却完全正常。初看差异在
"有无赋值语句"，实为"有无参数"：`def mkRegP(dummy: Nat) = { reg r2 = UInt[8] }`
调用 `mkRegP(0)` 即正常。

**机制链**（按代码顺序）：

1. **def 声明时缓存 WHNF**：`elaboration.rs` 的 `Decl::Def` infer 分支对体
   `t_tm` 求值得到 `vt`（`let vt = self.eval(...)`），随 `cxt.decl(name, t_tm, vt, ...)`
   存入声明表——`decl.2` 是**体的一次性求值结果**。
2. **求值发生在声明期**：decl 检查（infer）时体即被求值（探针：`def g() = let _ =
   file_read_all_text("缺文件")` 在声明时直接 panic；`checkModuleTree` 也因此在
   声明检查期被调用——见 hdl-check.typort 头注）。此时 mutable_map 尚无 module
   上下文，`createSignalExpr` 的 `change_mutable("ModuleTree", ...)` 静默 no-op。
3. **无参调用直接取缓存**：求值器 `eval_inner` 的 `Tm::Decl(x)` 分支
   （`mod.rs`）`decl.get(&x.data).map(|x| x.2.clone())` —— 无参 def "调用"就是
   裸 `Tm::Decl` 求值，**每次返回声明期的缓存值，体不再运行**，副作用永远不重放。
4. **有参 def 为什么正常**：有参调用是 `Tm::App` → `v_app` → 闭包应用，体
   每次应用都求值，副作用随调用上下文重放。
5. **module 宏为何"碰巧"工作**：module 宏的 `def tree` 是无参 def、体含
   `change_mutable`——它依赖同样的重放机制；`create` 侧是类字段（构造期求值），
   与 decl 缓存路径无关。`def tree` 此前能重放是隐式的，本次修复将其显式机制化。

**修复**（`mod.rs`）：`Infer::def_replay_memo` + `def_needs_replay` /
`scan_def_replay` / `tm_scan_global_ops`：

- 无参 def 的体 Tm 扫描是否含 `create_global` / `change_mutable` /
  `change_mutable_default` / `get_global`（直接或经其他 def 间接引用，递归跟随、
  防环、memo 化）。
- 命中者：`Tm::Decl` 求值改为重放体（`env = List::new(); tm = body; continue`），
  每次求值都在**调用方上下文**（当前 module 树）重新执行副作用；未命中者保持原
  缓存路径。
- `get_global` 一并列入：缓存读到的是旧树，重放才能读到当前树。

**实现过程中的坑**：builtin（prim）注册时 `add_builtin`（`cxt.rs`）把 body Tm 存为
**自引用占位** `Tm::Decl(name)`（`val_tm = Tm::Decl(...)`）。若把 prim 也判为
"需要重放"，求值 `Tm::Decl("create_global")` 会展开成自身 → **无限循环**。因此
`scan_def_replay` 对 `prim.is_some()`（decl 元组 `.5`）直接返回 false（不重放）。

**修复后行为**：无参硬件 def（`def mkFlag(): Bool = { reg f = Bool }`）、有参 def、
module 宏的 `def tree` 全部每次调用/访问重放体，硬件正确落树。

**遗留语义边界**（与 SpinalHDL 一致、未改）：def 在**顶层**（无 module）调用时，
副作用 no-op（骨架在但无宿主树）——与 module 宏自身顶层 `M.create` 丢实例一致。

---

## 问题 2：`diagnose_def_body_factories` 过度诊断（parse 期误报）

**严重度**：中——阻止合法代码，与问题 1 一起构成"def 里写不了硬件"的另一半。

**现象**：`def mkSig = let x = autoUInt(8); x` 被报
"`autoUInt` is called inside `def mkSig`: signal-creating factories have no
binding name there ... call it inside a `module` body instead"。

**机制链**：
1. 原诊断前提（`parser/mod.rs` `diagnose_def_body_factories` + `BN_FACTORY_NAMES`）
   是"def 体内工厂没有绑定名，信号名字为空"。该前提**对裸调用成立，对
   `let x = <factory>(...)` 不成立**。
2. `elaboration.rs` 对**所有** let 绑定设 `cxt.with_binding_name(x)`（Raw::Let
   检查分支，约 720 行；infer 分支约 2592 行）——def 体内的 let 同样命名工厂的
   `bn` 隐式参数。探针：`let c = counter(8)` 在 def 体内、module 内调用，信号正确
   命名为 `c`（`reg [7:0] c;`）。

**修复**：诊断改为 binder 感知——`walk` 递归时进入非 `_` 的 `Raw::Let` 即视为
"有名字"（value 与 body 子树均覆盖，与 elaboration 的 `binding_name` 上下文一致）；
`_` binder 不命名。裸调用（无 let 绑定保护）仍诊断。

---

## 问题 3：`loopName` 在 def 声明期求值下 `get_global` 缺键 panic

**严重度**：中——直接让检查进程崩溃（`unwrap` panic）。

**现象**：`def delay(x) = ...newUIntReg(8)...`（单行工厂形态）在声明期检查时
`thread 'main' panicked at cxt.rs:441:66: called Option::unwrap() on a None value`
——`get_global` 缺键。

**机制链**：
1. `hdl-core.typort` 的 `loopName` 假设"`HdlLoopIdx` 键由 `hdlLoopIdxGlobalInit`
   在 prelude 加载期建立"。该键在**加载期间**确实存在。
2. 但 `lib.rs` 在 prelude 加载完成后 `infer.mutable_map.write().unwrap().clear()`
   （约 1033 行，"per-file clones stay cheap"）——每个用户文件从**空** mutable_map
   开始。
3. module 宏 prologue 会 `create_global("HdlLoopIdx", ...)` 重建键，所以 module
   体路径从未暴露此问题；而 **普通 def 的声明期求值**（问题 1 的机制）走到
   `loopName` → `get_global("HdlLoopIdx")` → 缺键 panic。
4. 注释里提到的"Rigid 索引脏栈帧"（genFrom succ 分支体在加载期被求值）依然成立，
   `nat_to_dec` 把 Rigid 渲染成 0 —— 与本问题无关，未动。

**修复**（`hdl-core.typort`）：`loopName` 读前 `change_mutable_default("HdlLoopIdx",
xs => xs, hdlLoopIdxEmpty)` 兜底——缺键置空栈（与 prologue 语义一致），有键原样
保留。与 `addWhenContext` 对 `WhenStack` 的既有兜底同模式。

---

## 经验坑：`Cut` 元组的隐式 `Option` 包装（parser）

改动 p_def 时若在 `Cut((...))` 元组内给元素再套 `.option()` 会得到
`Option<Option<T>>`：`parser_lib_resilient.rs` 的 `tuple_cut_parser` 宏把
**第 2 个及以后**的元素输出类型定义为 `Option<$t>`（失败时 `push_error` + `None`
恢复），元素自身不要再 `.option()`。p_def 的 ret 元素 `.map(...).option()` 正是
靠这层包装变成 `Option<Option<Raw>>` 再 `flatten()` 的——初版 body 元素误加
`.option()` 导致 `body: Option<Option<Raw>>` 编译失败，去掉后恢复。

---

## 附记：L11 / L12 测试失败为预先存在

验证"无回归"时发现 `cargo test --lib` 有 44 个失败集中在 `L11_macro`（12 个）与
`L12_canonical`（31 个）。用 `git stash` 完全还原本批改动后重跑，同样的用例
同样失败——与本批改动无关（本机环境/既有问题）。`L13_namespace` 全量 353 个
测试（含 examples 回归 `test_examples_hdl_dir`）与其余层全部通过。

---

## 后续维护注记（2026-08-27 晚，同日第二批）

### 声明期存储求值：无参 replay def 已跳过

问题 1 的修复只改了 `Tm::Decl` 求值路径；`elaboration.rs` Def 分支在声明时仍会
对体做一次完整求值（`decl.2` 的缓存来源）。这次把这最后一次求值也收掉了：

- **只对无参 def 且扫描命中全局操作**（`tm_scan_global_ops` 与 `def_needs_replay`
  同一判据）的体跳过声明期求值，`decl.2` 改存 `Val::Decl(name)` 中性占位——与
  `cxt.rs` 缺名回退同款值，replay 路径永远不读它。
- **有参 def 不能跳**：其 `decl.2` 缓存的是闭包（求值无副作用），但下游
  elaboration（quote/force/投影链）会读回并应用这个闭包；换成中性占位会让整条
  依赖链卡死——16-utils 的 `historyUInt(a, 3).at(...)` 曾整段渲染成 stuck term
  （`assign de = (__run && (__cnt == 3))` 丢失），按参数有无收窄后恢复。
- 回归测试：`module_tests.rs` `def_body_global_ops_not_evaluated_at_declaration`
  ——文件首个声明 `def neverCalled = get_global("ModuleTree")`（裸表达式体、永不
  调用）在旧代码于声明期 panic（`cxt.rs:441` 缺键 unwrap），新代码干净通过，
  且后续 mkReg 调用仍正常落树。

**边界澄清（不要误修）**：def 体里 `let` 绑定值的 check 期求值
（`elaboration.rs` Raw::Let 分支，每 let 约三次）是依赖类型的既定设计——后续
类型要引用 let 的值。这类求值的副作用靠 prelude 既有模式兜底（module 宏的
push/pop 对消、`change_mutable_default` 缺键兜底），本修复**不覆盖**也不应覆盖。
裸 `get_global` 的其余调用点（hdl-macros/hdl-check/hdl-verilog）都在 module
运行期路径上（键由 prologue 建立），无需逐个加兜底。

### `tm_scan_global_ops` 补 `Tm::Sum` 扫描臂

原实现的 `_ => {}` 通配把 `Tm::Sum`（enum 声明）落掉了——其参数元组
`(name, value-tm, type-tm, icit)` 的 value 位可内嵌项。已补扫描臂；通配处加注：
**新增带 `Rc<Tm>` 载荷的 `Tm` 变体必须同步加臂**，漏臂会让副作用 def 被判为
可缓存（副作用静默丢失），且声明期跳过求值后该 def 的体一次都不会运行。
（`Tm::Match` 的 `PatternDetail` 只含名字/子模式，无需扫描；`SumCase` 的
`typ`/`datas` 原本已覆盖。）

### 性能嫌疑点备忘

`get_global` 列入 `REPLAY_GLOBAL_OPS` 意味着：体里读全局的无参 def 永久失去
WHNF 缓存，每次 `Tm::Decl` 引用都重放体（含其中的纯计算部分）。对硬件 def 是
正确性要求；但若将来某个纯计算 def 只是顺手读了全局（如配置），会退化为每次
重算。当前 prelude 无受害者；**L13 出现性能回归时先查这里**（配合
`docs/l13-perf-review*` 的既有基线）。

---

## 第三批（2026-08-27 深夜）：match case 体接入语句块 + 两个底层修复

### 语法：`case p => { <Expr statements> }`

braced def 体落地后，case 臂是最后一个没有语句能力的表达式位置。实现极小：
`p_match` 的臂体从 `(EndLine?, p_raw)` 换成 `p_block_body`（原 `p_def_body`
更名泛化：`{` 开头走 `p_def_stmt_block` 语句块，否则裸表达式）。块值规则与
def 体完全一致（末条语句为臂值：声明臂取 binder、控制链取 `unit`、裸表达式取
自身），所有臂类型仍需一致。`p_raw` 解析不了前导 `{`，两种形态无歧义。

语义边界（与 SpinalHDL 一致）：match 的 scrutinee 是 **elaboration 期数据**
（enum/Nat/Vec 值，payload 可以是信号），只有**命中臂**的声明落树（测试
`match_case_body_braced_reg` 断言未命中臂的信号不存在）；匹配信号的运行时值
仍是 `switch`/`when` 的领域。

### 修复 1：standalone `when` 宏补 `unit` 值尾

`macro_rules when`（hdl-macros.typort）此前只在两个位置"存在"：
1. **goto-definition 锚点**——module 体内 `when` 语句的 MacroExpansionInfo
   优先记录它的定义位置（`tests/macro_goto_tests.rs` 两处断言），**不能删**；
2. **p_raw 按名触发展开**——但它转写以 `let _ = whenEnd(unit);` 结尾（悬空
   分号、无值尾），重解析永远失败，即**没有任何可用调用点**。

修复：三个臂末尾各补 `unit` 值尾，转写成为完整表达式（类型 `Unit`），def 体
（`def f(): Unit = when c { ... }`）与裸 case 臂
（`case p => when c { ... }`，臂值 `Unit`）均可直接使用。与 `Expr` 宏内 when
臂的双份维护关系不变（区别仅尾部分号/值尾），文件头 NOTE 已更新。

### 修复 2：`p_raw` 宏展开的尾换行回退（根因修复）

**现象**：`def f(...): Unit = when c { ... }` 后跟任何声明都报
`expected newline`；裸 case 臂 `case p => when ... } otherwise { ... }` 后跟
下一臂报 `expected }`。

**机制链**：`MacroMatcher::Token`（macros.rs）在每匹配一个字面 token 后吞掉
**一个** EndLine（`}` 后的换行即被吃）。decl 级宏分发（`p_decl`）有回退补偿
（remainder 不以 EndLine 开头时退回一个 token）；decl 列表的分隔符补偿
（`many1_sep_skip`）也能兜住"下一 token 是声明关键字"的场景——但仅当
`skip_until_decl` 在后方还能找到 EndLine+声明关键字（`println` 若是文件最后
一个声明则返回 None），且 `module` 这类**宏名声明**根本不在关键字白名单里。
`p_raw` 的表达式级宏分发则完全没有回退——被吃的换行就是语句/臂/声明的分隔符。

**修复**（`parser/mod.rs` `p_raw` 宏分支）：展开成功后，若**最后消费的 token
是 EndLine** 且 remainder 不以 EndLine 开头，把该换行还回去（只还换行；
`twice 3` 的 `3` 之类真语句 token 不退）。case 臂分隔、let 链、decl 分隔全部
恢复正常；calc 在 def 体的场景也不再依赖 decl 列表补偿。

### 测试

`module_tests.rs` 新增 5 例：`match_case_body_braced_reg`（命中臂 reg 落树、
未命中臂不落）、`match_case_body_braced_when`（臂内 when + 混用裸表达式臂）、
`match_case_body_unbraced_when_chain`（裸臂 = standalone when）、
`match_case_body_inside_def_body`（def 花括号体 × match × braced 臂组合）、
`standalone_when_in_plain_def_body`（裸 def 体 when + 后跟 module 声明的分隔
回归）。