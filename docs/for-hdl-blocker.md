# HDL for 循环阻塞：class 展开期 dependent-meta 泄漏

> 状态：**已解决**（2026-08-27，详见文末「解决记录」）。
> 特性本身：`for i in 0 until N` 编译期展开，宏转写 + term 级 Nat 递归
> （`docs/hdl-syntax.md` §10；实现见 `prelude/hdl/hdl-core.typort` 尾部
> Range/rangeFor/HdlLoopIdx 段与 `hdl-macros.typort` 的 `Expr` 宏 for arm）。
> 验收：`cargo test module_for_loop` 4/4、`L13_namespace::module_tests` 28/28。

## 现象

任意 module 类体内出现对**含 `match` 的 prelude def** 的调用式绑定
（for 转写为 `let __hloop: Unit = rangeFor(0 until 4, i => ...)`；也复现于
手写 `let _ = whenEnd(unit)` / `let f = i => unit`），create/tree 检查报：

```
find unsolved meta with type `Type 0` @ 28:11426
（或 lvl2ix panic: level 6 is out of scope for a context of level 6 —
  dangling elaboration-time variable leaked into a quote）
```

**master 基线即可复现**：`module { let a = UInt[8]; let _ = unit; a := a }`
（同款报错）——非本特性引入，属 pre-existing。

## 机制链（本次定位）

失败发生在 class Phase B：`expand_class_decls` 生成的 **`Name.create` /
`Name.tree` def** 检查（`infer_after_prefix` 的 Decl::Def 分支，末尾
`t_tm.no_metas()` → Nat defaulting → 报错）。

诊断（meta 33971 现场）：

```
meta[33971] = Unsolved(
  Pi("bn" @ ... BindingName ...                          ← 类型含 bn 绑定（level 越界 1）
    Closure(..0, Let("_" @ 20835,
      AppPruning(Meta(MetaVar(33942)), [Some(Expl)]),    ← dependent 隐式参数未合
      App(Decl("change_mutable_default"), LiteralIntro("ModuleTree"), ...)) ...))
```

- 33942：`change_mutable_default("ModuleTree"...)` 的 `string_to_global_type`
  隐式参数 meta（返回类型依赖首参）——Phase A / create 头两遍检查未闭合。
- 33971：bn 语境（create 的隐式 `bn: BindingName` 参数）下无注解 let 的
  Hole 推断 meta；记录 cxt lvl=6，类型内引用 level-6 变量 → quote 越界。
- 与 `docs/l13-typeclass-instance-nat-param-bug.md` 的
  「Nat 参数运行期冻结」为同一族（悬挂 elaboration-time 变量泄漏进 quote）。
- 顶层（module 外）`rangeFor(0 until 3, i => ...)` 完全正常——泄漏只发生在
  class Phase A/B 语境（bn 参数 + Phase-A 复用项 Raw::Tm 的跨检查引用）。

## 已试路径（三变体各踩一类失败）

| for-arm 转写形态 | 失败 |
|---|---|
| `let _ = rangeFor(...)` | pre-existing `let _ = <调用>` 卡点（Type 0 @ 11426） |
| `let __hloop = rangeFor(...)`（无注解） | Hole 推断 meta（33971）未闭合 |
| `let __hloop: Unit = rangeFor(...)`（当前） | 仅剩 dependent-meta（33942/33971）泄漏 |

已排除：hook 命名（loopName 全部还原后仍挂）、Add typeclass（string_concat
已替换）、until/RangeSyntax typeclass（rangeFor2 Nat 双参同样挂）、转写解析
（`$($body)*` 裸链已确认可解析且展开正确；`$({$body})*` 的裸块尾值污染
lambda 类型，不可用）。

## 修复方向（供主线）

1. **根治**：`string_to_global_type` 的 dependent 隐式参数 meta 在
   class Phase A / create 检查之间不闭合——对应
   `l13-typeclass-instance-nat-param-bug.md` §机制链（instance 化时
   隐式参数 meta 悬挂），与本仓库已知家族一致；修法是该文档的修复方向。
2. **绕行（for 专用）**：给 module 宏加「辅助构造器」语句形式——
   把 for 转写为 `let __hloop: Unit = <一个 def 包装的迭代调用>`，参数
   全部显式 Nat（无 dependent 隐式参数路径），即可绕开
   `string_to_global_type` 悬挂链；待依赖 meta 泄漏根治后换回直调。

## 验证入口

- `cargo test module_for_loop -- --ignored`：4 个 for 测试（展开命名 /
  宽度参数化 / 嵌套命名 / 空区间），当前全部失败于上述泄漏。
- 顶层机制探针（可在任何非 class 位置直接跑）：
  `let _ = rangeFor(0 until 3, i => let _ = nat_add(i, 0); unit)` → 正常。

## 二次排查（2026-08-26 深挖续）

在 Phase A/let 分支为**无注解 Hole 推断 meta** 增加显式闭合（推断类型即该
meta 的答案：`MetaEntry::Solved(vt, mty)`）——语义正确、module 回归 22 项
全绿；它对 for 的 meta 报错**没有直接消除**（根因不在 Hole meta）。随后试过
「Nat defaulting 失败后把 oty 完全确定的余留 meta 自解」——能把
`find unsolved meta` 推过检查期，**但**暴露更深一层：`string_to_global_type`
的隐式参数 meta 被错误求解成 `U(0)`（unit 值）挂在 spine 上，`val_no_metas`
里对该 spine 的 quote/force（`NM_QUOTE_LVL` 分支）触发
`v_app: impossible apply U(0)`。**该自解兜底因此回退**（把明确诊断变成运行期
panic 是净退化），只保留两个 pin 化简。

新增（待修）事实：`v_app` 的 `Val::Match` 分支已存在（stuck match 应用
语义正确），**新的 panic 是「错解值 U(0) 被 apply」**——即**隐式参数 meta
的求解目标错误**（求解器把类型级/值级 meta 混解），根源仍在
`string_to_global_type` 依赖路径的 meta 处理，与
`l13-typeclass-instance-nat-param-bug.md` 的「实例化时隐式参数 meta 悬挂」
是同一个病灶的两个表象。

### 三次排查（2026-08-26 续 2）：item-local 闭合实验（验证后回退）

把「Nat defaulting 失败后对 oty 确定的余留 meta 自解」**下沉到 Phase A 逐
item**（item 检查后先 `solve_multi_trait` 再局部自解，语义上「已检查完的类
条目是无后约束的不动点」）：**无效**——这批 meta 的目标类型相互依赖（目标
类型内仍含未解 meta），单点闭合条件全部不满足；证明它们是**相互引用的一簇
约束**，只能由整体求解器（或 bug 报告 §修复方向 3 的「约束 meta 延迟解」）
处理。**已回退**，主线保持 `14c0805` 状态：两个 pin 化简 + 文档记录。

## 解决记录（2026-08-27）：根因不在 elaborator，在宏转写形状

用插桩（`new_meta` 创建点 backtrace、失败期 term pretty dump、宏展开文本
dump、全局原语写路径 trace）逐层定位后，三次排查赖以推断的「dependent 隐式
参数 meta 簇」其实是**下游表象**。真实缺陷链有三层，全部修在 prelude 宏 +
两处小 Rust 改动上，`MetaEntry` 架构（原修复方向 3 / 5.2）无需动：

1. **`Expr` 宏兜底臂包裹 let 表达式**（`hdl-macros.typort` 的
   `($x: raw) => {let _ = $x;}`）：`_` 不是 ident，用户的 `let _ = unit`
   匹配不到通用 let 臂，落入兜底被包成 `let _ = (let _ = unit; ...)` 嵌套
   链——链经 `;` 吞并后续语句、链尾由解析器补 recovery Hole。外层注解
   Hole meta（spine 含 bn）在整个 Phase A/B 中无求解者（值检查只统一内层
   链自己的 meta），Phase B 复用后 `no_metas` 报
   `find unsolved meta with type Type 0`——即本文档的「母版场景」。
   **修复**：新增丢弃名透传臂 `(let _ = $y:raw) => {let _ = $y;}`（含
   带注解变体）；为此给宏匹配器模式解析器补 `Hole`/`Colon` 字面量
   （`parser/mod.rs` `p_macro_matcher_single`）。
2. **for 臂输出缺尾分号**：`let __hloop: Unit = rangeFor(...)`（无 `;`）
   在 `def tree` 的单条 let-expr 链里接不到下一条模板 let，链尾补
   recovery Hole，`_res` 链丢失——tree 检查报
   `find unsolved meta with type ModuleTree`（meta 34024 一类）。
   **修复**：for 臂输出补 `;`。
3. **`loopName` 的全局栈生命周期**：`loopName` 旧版「读前
   `create_global` 清空」使循环索引命名永远不可能生效（cons 分支死代码）；
   但直接改成 `change_mutable_default`+恒等 或纯读都暴露两个更深的问题——
   (a) `genFrom` 的 succ 分支体在 **prelude 加载期的类型检查中就被求值**
   （检查器对应用逐个求值），把 `Rigid(Lvl(0))` 索引的帧推了 5 次、只弹
   1 次，脏栈被快照进 prelude 缓存，`nat_to_dec` 把 Rigid 渲染成 0，于是
   手写 class 的端口名出现 `a_0_0_0_0`（class_tests::
   class_module_shape_flattened_chain 曾因此回归）；(b) 早期（stuck）eval
   跳过 pop、留下未配对帧。
   **修复**：`hdl-core.typort` 中 `def hdlLoopIdxGlobalInit = create_global(...)`
   在加载期建立键（def 检查求值应用，恰好在 hdl-signals 之前）；`loopName`
   改纯读；Rust 侧在 prelude 加载**结束**时把键重置为 empty
   （`mod.rs` `load_prelude_state_impl` 尾部）；module 宏 prologue（create
   与 tree 两侧）各加一行运行期重置，与既有 `WhenStack` 重置同款。

附带：`l13-typeclass-instance-nat-param-bug.md` 的复现 B（参数化宽度静默
退化）不在本次范围（那是 trait 实例 Nat 参数冻结问题，见该文档），但 HDL004
警告路径未回归。原 §修复方向 1/2 的「已排除路径」结论仍然有效。
