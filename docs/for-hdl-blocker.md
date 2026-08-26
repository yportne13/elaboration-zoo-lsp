# HDL for 循环阻塞：class 展开期 dependent-meta 泄漏

> 状态：阻塞记录（2026-08-26，master `529368b` 合并后）。
> 特性本身：`for i in 0 until N` 编译期展开，宏转写 + term 级 Nat 递归
> （`docs/hdl-syntax.md` §10；实现见 `prelude/hdl/hdl-core.typort` 尾部
> Range/rangeFor/HdlLoopIdx 段与 `hdl-macros.typort` 的 `Expr` 宏 for arm）。

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
