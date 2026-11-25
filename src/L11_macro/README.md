# L11：macro_rules 宏（解析期展开）

本层按“每章 = 上一章实现思路 + 本章新特性”重建（2026-11-17）：实现上
**直接承接新 L10**——L08 血统 decl 表名字世界、`Rc<Val>`、σ 显式替换、
逐臂 match、P1–P11 加固、`Type N` 分层宇宙、trait/typeclass、可变全局/
文件 IO builtin、层内 `tests.rs`、bump 孪生——只叠加 **macro_rules**：
解析期宏定义登记 + 调用点 token 级展开。

## 1. 语言特性

```text
macro_rules make_bool {
    (yes) => {
        enum Yes {
            y
        }
    }
}

make_bool yes        // 声明级宏：展开为 enum 声明
println y            // Yes::y

println (stringify t123)   // 内建 stringify → 字符串字面量 "t123"
```

- **`macro_rules <name> { (matcher) => { transcriber } ; ... }`**：解析期登记
  宏规则表；宏定义本身不产出 `Decl`，展开结果重新进入声明/表达式解析。
- **匹配器**：字面 token（按 kind+文本）、`$name:fragment` 元变量（`ident` /
  `raw` / `params`）、`$(...)*` / `$(...)+` / `$(...)?` 重复（平衡括号感知），
  以及“引用另一宏规则的元变量”（`MacroFragment::Name`）。
- **转写器**：`Basic`（原样 token + `$name` 捕获替换）、`Sequence`、`Group`
  （按被引用元变量数逐次展开）、`BuiltIn`（stringify：捕获 token 转 `Str`）。
- **展开方式**：token 直接拼接（不做“序列化成文本 → 重词法”）——捕获 token
  借用调用点 span，模板字面量 span 改写为整个宏调用区间；同时记录
  `MacroExpansionInfo`（展开文本/调用位置/定义位置）供 LSP goto-definition。
- **护栏**：自递归宏有展开深度上限 `MAX_MACRO_EXPANSION_DEPTH = 256`，超限
  推解析错误而不是栈溢出；`#[macro_export]` 属性被记录（导出标记）。
- 其余语言面（enum/GADT/struct/投影/Universes/trait/builtin）全部继承自 L10。

## 2. 实现结构（相对 L10 的增量）

- `parser/macros.rs`：`MacroMatcher` / `MacroTranscriber` / `MacroRule` 与
  `replace`（旧转写路径，保留给宏内嵌宏/声明级展开）及序列化辅助。
- `parser/mod.rs`：
  - `MacroState = (错误流, Rc<宏表>, 展开记录)`：整表 Rc 快照、规则表 Rc，
    声明点 `Rc::make_mut` 增量插入；
  - `p_macro_def` / `p_macro_export_attr` / 宏匹配器与转写器文法（平衡括号
    感知，支持模式里出现字面括号）；
  - `p_raw` / `p_decl` 入口先查宏表：命中则拼接 token 后递归解析，未命中
    落回原有表达式/声明解析（`p_raw_plain` / `p_decl_plain`）；
  - `p_top` 把宏定义从 decl 流里吞掉（不产出声明）；入口预置内建 `stringify`。
- 孪生侧无增量：宏展开发生在 parser（参考版/孪生共用同一 parser）；孪生只
  为基准补了 `natadd_src` 与 `DeclEntry` 兼容别名。

## 3. 与旧 L11 的取舍

旧 L11 的 parser 是“宏 + 错误恢复 + 手写优先级 + Verilog 兼容 token + 数字
转 Church 数字 + 元组字面量 + package/import”混装体（2353 行）。本次重建严格
按“上一章实现思路”只承接宏能力：parser 以新 L10 为基线 + 宏文法（~1.2k 行），
旧 L11 的其余 parser 增量**不再保留**（它们属于旧血统的偷带面，不是本章 README
声明的语言特性）。可变全局/文件 IO 在新 L10 已继承，不再作为 L11 增量。

## 4. 测试

- `cargo test --release --lib L11_macro::`：**88**（L10 套件继承 + 2 个宏冒烟：
  stringify / 声明级展开）。
- `cargo test --release --test l11_fast_parity`：**133**（L10 双 oracle 套件
  继承 + 3 个宏 parity：stringify / 声明级展开 / 参数化宏）。
- `cargo test --release --test l11_blackbox`：**67 + 1 ignored**（L10 黑盒基线
  + 2 个宏用例）。
- 跨层门禁（含 L11）：`gadt_refine_cross_layer_tests` 265、
  `prim_identity_cross_layer` 258、`implicit_comma_args` 468、
  `audit_crosslayer_probe` 258、`backport3_pretty_l0910` 174，全绿。
- 基准自检：`l11bench --workload all`（church/natadd/strchain/match/enum/
  struct/macro/universe/traitchain）参考版↔孪生互检通过；`realbench --layer L11`
  common 语料 pass=6。

## 5. 已知限制

- 匹配器片段只实现 `ident` / `raw` / `params` 与引用其它规则；没有完整
  token-tree `tt` / `expr` / `ty` 语法片段（旧 L11 同口径）。
- 宏展开失败折叠为解析错误（`parse error`），不做逐宏诊断恢复（新链 parser
  契约为 L08 严格 Err，旧 L11 的错误恢复/同步点不在本次继承面内）。
- 数字字面量语法未引入：宏示例避免裸数字（与 L10 继承面一致）。

## 6. 参考资料

- `../L10_typeclass/README.md`：本层核心机（含 trait/Type N）的全部出处；
- 旧 L11 文档与完整宏实现细节在 git 标签 `pre-rearch-20261117` 可查。

## 增补（2026-11-25）：继承 L10 观察面（三方合并）

以 "上一章完整继承" 口径，把 L10 已补齐而本层此前仍缺的继承面（`observe.rs` / `prof` /
`run_surface_impl` 的 println+自检行管线）归位：

- 三方合并（base = 旧链 L10、ours = 新 L10、theirs = 本层），32/34 文件零冲突；
- 新增 `observe.rs` 并注册 `mod observe;`；
- 恢复被合并丢掉的 `use cxt::{Cxt, DeclEntry, Decls};`（本层旧 mod.rs 原本没有这行）；
- `L10_DEBUG_ON`/`L10_LOOP` → `L11_*`；`crate::L10_typeclass` → `crate::L11_macro`。

账本：identical 808→**839**，missing 1→**1**（仅 `L10_DEBUG_ON` 章名重命名），line_keep 0.9990。
门禁：lib 88、l11_blackbox 67+1 ignored、l11_lsp_surface 91，全绿。
对账见 `docs/inheritance/L11-triage.md`。
