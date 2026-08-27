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