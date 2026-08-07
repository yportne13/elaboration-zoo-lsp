# 宏调用中 hover / goto-definition 的剩余 bug 分析

> 日期：2026-08-07。基于 master @ 67519ae（`refactor(hdl): flatten module macro side-effect chain ...`）。
> 分析方式：`tests/probe_macro_bugs.rs`（探针测试，保留在仓库里，跑 `cargo test --test probe_macro_bugs -- --nocapture` 可复现全部行为）。
> 前置修复背景：`9795ec1`（宏体内 token goto 自己的定义）、`3810d4f`（module 体首 token 不再跳 Expr 宏）。

---

## 0. 当前处理链路（摘要）

- **goto**（`lib.rs::goto_definition_at`）三步：
  1. 宏名 token 匹配（`goto_macro_definition_name`，只认 `name_token_is_macro == true` 的展开）→ `macro_rules` 定义；
  2. 语义表（`hover_table`）最具体条目（span 最小者，平局取**先插入**者）→ 该条目的 def span；
  3. 整调用 span fallback（`goto_macro_definition`，`name_token_is_macro` **不过滤**）→ 覆盖光标的**最内层**展开的宏定义。
- **hover**（`lib.rs::hover`）：先 `type_map`（def 名 span），再 `hover_table.hover_entry_at`（path 过滤 + span 最小者，平局取先插入者）。
- **展开 token 的 span 规则**（`parser/mod.rs`）：
  - `p_raw` 路径（表达式级宏，如 `calc`、`twice`）re-lex 时：**捕获的 metavar** 保留调用点 span；**transcriber 字面量**映射到整个调用 span（`invocation_start..invocation_end`）+ 调用点 path。字面量判定启发式：`span_map` 里有条目且 `m.src_path_id == call_site_path`（`mod.rs:1173-1187`）。
  - `p_decl` 路径（声明级宏，如 `module`）re-lex 时（`mod.rs:2406-2411`）：**不重映射**，字面量保留宏定义处的 span/path（prelude path）。
  - Name 片段（`Expr` 片段驱动，`macros.rs:82-126`）：语句整体记一条展开（name=首 token，`name_token_is_macro = 首 token 是否为宏名`，def=实际匹配规则）。

---

## 1. Bug A：p_raw 展开的字面量 span 判定有缺陷（calc / 本地宏 / 任何表达式级宏）

### A1. 同文件宏：字面量被误判成"捕获 token"，条目落到 `macro_rules` 定义体里

**根因**：`p_raw` 的 span 恢复用 `m.src_path_id == call_site_path` 区分"metavar 捕获"与"transcriber 字面量"。宏定义与调用在**同一文件**时，字面量的定义处 path 与调用点相同，启发式失效——字面量拿到的是**宏定义体里的 span**，而不是整个调用 span。

**证据**（`probe_macro_bugs.rs` 的 local_probe / ctrl2_probe）：

```
macro_rules twice {
    ($x: raw) => { $x + $x }     // '+' 在定义体偏移 42..43 / 90..91
}
def y: Nat = twice 3             // 调用 [64..71]
```

- `parser_with_macros` 解析出的 d3 体：`(n.Some("+" @ 90,91) n)` —— 展开出的 `+` 的 span 是**宏定义体**里的 `+`（90..91），不是调用点。
- hover 表里 `+` 的条目（8 条，trait 解析生成）token span 全是 `[42..43]`（local_probe 里宏定义体的 `+`）——即 `twice 3` 调用区**没有任何条目**。
- 后果：
  - 悬停 `twice 3` 里的 `3` / `+` / 宏名 → **无 hover**（字面量条目都在宏定义体里）；
  - 悬停宏定义体 `$x + $x` 的 `+` → 混入 use-site 展开生成的条目（定义体 `+` 自身条目 + use 展开映射来的条目合并，内容其实一样，但语义上定义体被"污染"）；
  - goto `twice 3` 里的 `3` → 语义表无命中 → 第 3 步 fallback → 跳到 `macro_rules twice`（"整调用 fallback"语义，勉强可接受，但与 calc 表现不一致）。

### A2. 跨文件宏（prelude 宏）：字面量整调用 span + 调用点 path → hover 污染 + goto 劫持

**根因**：prelude 宏（`calc` 等）的字面量 path ≠ 调用点 path，启发式正确判定为字面量 → 映射到整调用 span + 调用点 path。elaboration 对这些字面量照常推 hover 条目（`Eq`、`trans` 等都是普通 decl），于是**每个字面量都有一条 token span == 整个调用的条目**。

**证据**（calc_probe，调用 `calc { ... }` 在 [55..151]）：

```
@  55 c   hover=[55..151] [A: Type 0] → (x: A, y: A) → Type 0   goto=eq.typort[7..9]   ← 宏名 `calc` 悬停显示 Eq 的类型！
@  60 {   hover=[55..151] [A: Type 0] → (x: A, y: A) → Type 0   goto=eq.typort[7..9]   ← 非语义位置也显示 Eq
@  80 b   hover=[55..151] [A: Type 0] → (x: A, y: A) → Type 0   goto=eq.typort[7..9]   ← `by` 关键字
@  70 0   hover=[55..151] [A: Type 0] → (x: A, y: A) → Type 0   goto=eq.typort[7..9]   ← 字面量 `0`
@ 108 n   hover=[55..151] [A: Type 0] → (x: A, y: A) → Type 0   goto=eq.typort[7..9]   ← 第二步的 `n`（$x2/$z 未被转写器重发，无自己的条目）
```

- 悬停宏名 `calc` / `{` / `by` / `=` / 第二步项 → 全部显示 **`Eq` 的类型**，hover 高亮范围是**整个调用** [55..151]；
- goto 这些位置 → 第 2 步语义命中 `Eq` 条目 → 跳到 **eq.typort 的 `Eq` 定义**（`[7..9]`），而不是 calc 宏定义；
- 与 module 情形对比（module 的 `{` 处 goto 正确落到 `macro_rules module`），行为不一致：module 的字面量走 p_decl 路径保持 prelude path，hover/goto 的 path 过滤把它们滤掉了；calc 的字面量被映射成调用点 path，滤不掉。

### A 的修复方向

1. **字面量 vs 捕获的判定不再依赖 path_id**：`span_map` 的条目显式标注"是 metavar 捕获"（或在恢复时区分字面量区间），同文件宏的字面量不再拿到定义体 span。
2. **字面量 span 策略**（二选一）：
   - (a) 字面量映射为**调用点起点的零宽 span**（`start == end == invocation_start`）：不产生任何可命中的 hover 条目；展开期错误仍落在调用点（注释里"errors stay inside the macro call"的意图保留）；goto 的第 2 步不再被劫持，第 3 步 fallback 恢复（`by`/`=`/`0` → calc 宏定义，与 module 行为一致）；
   - (b) 保留整调用 span，但在 hover/goto 语义匹配时排除"token span == 某个宏调用整 span"的条目（需要额外标记，改动面大）。
   推荐 (a)。
3. `p_decl` 路径（`mod.rs:2406-2411`）同样没有字面量/捕获区分：用户**自己文件里的声明级宏**（同文件调用）也有同样的定义体 span 泄漏。若修 A1，建议一并处理。

---

## 2. Bug B：module/when 体语句（Expr 片段驱动）的非语义 token，goto 跳到 `macro_rules Expr`

**根因**：第 3 步 fallback（`goto_macro_definition` → `macro_expansion_at(name_only=false)`）匹配**任意**覆盖光标的展开（`name_token_is_macro` 不过滤）。module 体语句的 Expr 片段展开（如 `let a = UInt[8]` 整条 [21..35]，name=`let`，`name_token_is_macro=false`，def=Expr 宏的 passthrough 规则）是最内层覆盖者，于是：
- 点击语句里的 `let` / `=` / `UInt[8]` / 空白 → 跳 **`macro_rules Expr`**（hdl-macros.typort[2903..2907]）；
- `3810d4f` 只修了第 1 步（name-token 匹配），第 3 步仍触发。

**证据**（mod_probe / when_probe）：

```
@  21 l   goto=hdl-macros.typort[2903..2907]   ← `let`（module 体语句首关键字）
@  27 =   goto=hdl-macros.typort[2903..2907]   ← `=`
@  29 U   goto=hdl-macros.typort[2903..2907]   ← `UInt`（$t 捕获但类型注解不推 hover 条目）
```
（对比：`module` 关键字 → 正确跳 `macro_rules module`；`{` → 正确；body 里 `sum`/`a`/`+^` 有语义条目的 → 正确。when 体同理。）

**修复方向**：第 3 步 fallback 只匹配 `name_token_is_macro == true` 的展开（真实宏调用）。效果：
- `let`/`=` 等 → 最内层"真实宏调用"展开 = 外层 `module` 调用 → 跳 `macro_rules module`（与 `{` 处行为一致）；
- when 体内的语句 gap → 跳 `macro_rules when`（而非 Expr）；
- 现有测试全部保持（`goto_module_macro_full_path_keeps_fallbacks` 的 `myAdder-1` gap、`when` 关键字、calc 关键字等展开的 `name_token_is_macro` 都是 true）。
- 注意 `goto_macro_definition`（`macro_expansion_at` 的 `name_only=false` 分支）与第 3 步共用，直接在该函数过滤即可。

---

## 3. Bug C：trait 方法运算符（`+` / `:=`）hover/goto 命中"trait 级"条目而非"方法级"条目

**根因**：trait 方法解析（`elaboration.rs:2212-2314`）对同一个 use-site token 推**多条同 span 条目**：合成 decl 内部 `Add`/`Self`/`$$` 等 Var（trait 级，def=trait 名 token）+ 最终方法条目（def=方法名 token）。平局（`min_by_key` 取先插入者）时**先插入的 trait 级条目赢**。

**证据**（calc 的 `+` [37..38]、module/when 的 `:=` [67..69]/[129..131]）：

```
+  : hover=[37..38] [Self': Type 0, T': Type 0, O': Type 0] → Type 0   goto=op.typort[375..378]  ← Add trait 名
     （同 span 条目里排第 1 的是 trait 级；方法级 def=[414..415] 的 `+` 条目在第 4/8 位）
:= : hover=[67..69] [Self': Type 0] → Type 0   goto=hdl-types.typort[232..236]  ← Data trait 名
     （方法级 def=[248..250] 的 `:=` 条目存在但排后）
```

- 悬停 `+` → 显示 trait `Add` 的 Pi 类型；goto → 跳到 `trait Add` 的名字 token；
- 悬停 `:=` → 显示 trait `Data` 相关类型；goto → 跳到 `trait Data` 的名字 token（hdl-types.typort[232..236]，`Data` 定义处；文件是 CRLF，字节验证过 `Data` 在 232..236，`:=` 在 248..250）。
- 对照：顶层 def 运算符 `+^`（hdl-ops）解析正常（def=[2982..2984] = `+^` token）。
- 注：这不只发生在宏里（普通表达式 `n + 3` 同样），但在宏体里非常显眼（calc 的 `+`、module/when 的 `:=`）。归属上它是 hover/goto 的通用问题，修法在 elaboration 侧。

**修复方向**：
- 方法解析时**回收合成条目**：`infer_expr(cxt, decl)` 前记录 `hover_table.len()`，解析后 truncate 掉这批同 span 的 trait 级条目，再推最终方法条目（`t.to_span()` + `methods_name.to_span()` + 方法类型）——用户期望的 hover/goto 目标就是方法条目；
- 或让合成 decl 内部的 Var 用**零宽/特殊 span**（不产生可命中条目），与 Bug A 的思路一致；
- 或改平局规则（如"def span 不等于 use span 且最短"）——不可靠，不推荐单独使用。

---

## 4. 次要观察（不阻塞，记录在案）

- `twice 3` 调用区无任何 hover 条目（A1 的结果）：悬停 `3`/`+` 显示空。修复 A1 后 `+` 会拿到整调用 span；若按 (a) 归零宽则仍无 hover（合理），若保留整调用 span 则会出现 calc 式污染（必须配套 (a)）。
- ~~calc 第二步的项（`$x2`/`$z` 未被转写器重发）天然没有自己的条目~~ —— **已修复（2026-08-07）**：这不是"设计"，而是 calc 宏的 bug（`$x2`/`$z` 被 matcher 匹配后从未重发，导致 (a) 后续步书面项完全不被检查——`garbage1 = garbage2 by <正确proof>` 零错误通过；(b) 第二步 token 无 hover/goto 条目，悬停落到 A2 污染条目显示 Eq 类型。修复：转写器恢复每步检查 let `let _ : Eq ($x2) ($z) = ($q);`（两端写全，§9.2.1 失败的洞注解不是思路问题），并修复单行形式重复单元缺前导 `=` 的匹配 bug。详见 `docs/calc-reasoning-design.md §9.6`。修复后第二步的 `n`/`+` 悬停恢复正常；剩余 A2 污染仅存在于无语义的字面量/关键字位置（`0`、`by`、`=`、`{` 等）。
- hover 的 `range` 跟随命中的条目：A2 污染时高亮整个调用体（[55..151]），观感很差，修 A2 自然消失。

---

## 5. 验证矩阵（探针已覆盖，回归必测）

| 场景 | 期望 |
|---|---|
| 悬停 `calc` 宏名 | 无 hover（或宏 hover）；**不是 Eq 类型** |
| 悬停 calc 体 `by`/`=`/`0`/第二步项 | 无 hover |
| goto calc 体 `by`/`=`/`0` | `macro_rules calc`（fallback 一致性）或 None |
| 悬停/goto calc 第一步捕获 token（`n`/`+`/proof） | 各自类型/定义（现状已正确，防回归） |
| 悬停/goto `twice 3` 内 token | 无 hover；goto → `macro_rules twice`（fallback）|
| goto module 体语句 `let`/`=`/`UInt[8]` | **不是** `macro_rules Expr`；应落 module 宏定义或 None |
| goto when 体内语句 gap | 不是 `macro_rules Expr`；应落 when 宏定义 |
| 悬停/goto `+`（calc 内）、`:=`（module/when 内） | 方法级类型；goto 到 `+`/`:=` 的 token（op.typort[414..415] / hdl-types.typort[248..250]）|
| 现有 6 个 goto 测试 + hover_tests | 全绿 |

---

## 6. 建议的任务切分（每项独立可并行，互不依赖）

1. **T1（Bug A1+A2）**：parser 字面量 span 修复——显式捕获标记 + 字面量零宽（或整调用但排除）。影响文件：`src/L13_namespace/parser/mod.rs`（`p_raw` re-lex 1162-1195、`p_decl` 2406-2411、`owned_tokens_to_string_mapped` 的 span_map 结构）。
2. **T2（Bug B）**：goto fallback 过滤 `name_token_is_macro`。影响文件：`src/lib.rs`（`macro_expansion_at`）。
3. **T3（Bug C）**：trait 方法解析条目回收。影响文件：`src/L13_namespace/elaboration.rs`（`trait_wrap` 2212-2314 附近）。

三者根因互不相交（parser span / goto fallback / elaboration 条目顺序），适合各自开 worktree 并行做，共用 `tests/probe_macro_bugs.rs` 与 `tests/macro_goto_tests.rs` 做回归。
