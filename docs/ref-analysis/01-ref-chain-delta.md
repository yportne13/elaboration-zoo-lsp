# 参考版（ref）逐章增量：L06 → L12

> **角度 01 / 只分析参考版。** 孪生自 2026-11-24 起被 `#[cfg(feature = "lNN-twin")]` 硬封印（`src/L12_canonical/mod.rs:51`），默认不编译，本册不涉及。
> 方法：逐相邻步 `git diff --no-index --unified=0` 统计增删行 + **声明级符号集合差**（`fn/enum/struct/trait/impl` 声明名）+ SHA-256 定逐字节冻结段；**未构建**。
> 锚点 `src/LNN_xxx/yyy.rs:LINE`，HEAD `8f4287ae`。分级沿用 MAP §8（E0/E1/E2/E3/E4）。

## 1 底稿：每一步 ref 侧改了什么

| 相邻步 | 改动文件 | 逐字节未改的引擎文件 | 增/删行（约） | 声明级符号 | 判读 |
|---|---:|---|---:|---|---|
| L06→L07 | 12 改 + 5 新 + 1 删 | — | +9.2k / −2.3k | **+160 / −39** | 和类型章 + 名字世界整体重构 |
| **L07→L08** | 11 改 + 1 删 | —（基线被重定） | +0.8k / −0.8k | **+23 / −13** | 章增量极薄，**删得比加得多** |
| L08→L09 | 14 改 | — | +0.3k / −0.3k | **+1 / −1** | 只有一处函数级增删（见 §4） |
| L09→L10 | 9 改 + 1 新 | `cxt` `struct_eq` `shape` `raw_pretty` `pattern_match` `parser/syntax` `pretty` | +1.2k / −0.08k | **+16 / −0** | 声明级纯加法 |
| L10→L11 | 6 改 + 1 新 | `elaboration` `unification` `typeclass` `cxt` `struct_eq` `shape` `raw_pretty` `pattern_match` `pretty` `parser/syntax` | +1.3k / −0.08k | **+32 / −0** | **引擎核心逐字节零改动** |
| L11→L12 | 9 改 | `cxt` `struct_eq` `shape` `raw_pretty` `pattern_match` `parser/lex` `parser/syntax` | +0.4k / −0.3k | **+5 / −7** | 单文件重写（`typeclass.rs`） |

> 全链唯一两次“文件消失”：L06→L07 删 `eval_budget.rs`（200 行）；L07→L08 删 `observe.rs`（352 行）。**两次都与所在章的主题无关。**

## 2 逐章「本章增量」清单

| 章 | 主题 | ref 新增文件 | 新增类型 / 函数 | 触及的既有函数 | 档 |
|---|---|---|---|---|---|
| **L07** | 和类型 + 依赖模式匹配 | `pattern_match.rs`(20 项) `struct_eq.rs`(8) `shape.rs`(7) `raw_pretty.rs`(4) `tests.rs`(81) | `Decls` `DeclEntry` `PrimFunc` `VSpan` `Subst/SubEntry` `SpecSolve` `UnifyKind` `PatternDetail` `PosCover` `MetaSnapshot` `InlineStack` `quote_deep` | `cxt.rs` 的 15 个 builtin 方法**整体搬走**成 decl 表条目；`unification` +1003/−219；`mod.rs` +2267/−565 | **E4** + E1 |
| **L08** | 积类型（struct / Sigma） | 无 | **仅 3 个**：`parser::p_new`(`:507`) `parser::p_struct`(`:603`) `elaboration::render_by_shape`（搬入） | `p_atom` `p_pattern` `p_decl` `pretty` `unification::unify` `elaboration::Raw::Obj` | **E4(薄)** + E3 |
| **L09** | 分层宇宙 `Type N` | 无 | **仅 1 个**：`elaboration::check_universe`(`:162`)，删 `ty_precheck` | 载荷穿线 12 文件（`Raw/Tm/Val::U` 加 `u32`） | **E4** + E2 |
| **L10** | trait / typeclass | `typeclass.rs`(25 项) | `trait_wrap`(`elaboration.rs:775`) `solve_trait` `solve_multi_trait`(`unification.rs:743`) `force_deep` `take_trait_error` `p_trait_def` `p_impl` | 3 处投影错误路径挂 `trait_wrap`；3 处 flex 解后挂 `solve_multi_trait` | **E4** + E2 |
| **L11** | macro_rules | `parser/macros.rs`(12 项) | `p_top`(`parser/mod.rs:1496`) `p_decl_plain`(`:1506`) `p_macro_def`(`:1354`) `splice_transcriber` `MacroDepthGuard` `MacroExpansionInfo` +15 | 无（旧解析器被 `p_top` **包裹**而非修改） | **E4 纯净** |
| **L12** | canonical / Val 级 trait 求解 | 无（`typeclass.rs` 重写） | `Tm::Call` / `Val::Call`(`mod.rs:108` / `:286`) `val_match`(`typeclass.rs:127`) `vals_eq_ground`(`:200`) `lookup_function_by_cases`(`mod.rs:2565`) | `force` `frcs` `v_app` `eval` `quote` `rename` `unify` `Subst` `pretty` 各加一臂 | **E4** + E2 |

### 2.1 L07 专题：这一章把“名字世界”整体换掉了

L07 的 +160 个声明里有一半不是和类型，而是把 L06 的**内建函数宿主**从 `Cxt` 的专用方法搬成 decl 表条目。这是全链唯一一次“同样是既有机制、但载体被换掉”的重构，级别 E1（等价改写），但它解释了 MAP §1 里 `cxt.rs` +370/−361 与 `unification.rs` +1003/−219 的来源：

| 面 | L06 | L07 | 档 |
|---|---|---|---|
| 15 个 builtin（`string_concat`…`file_delete`） | `cxt.rs` 上的方法 | 搬进 decl 表，统一走 `Val::Prim`/`PrimFunc` 与名字解析（`cxt.rs` 同名函数全部移除） | E1 |
| 全局名的查法 | `Cxt` 内直接持有 | `Tm::Decl` / `Val::Decl` + `Decls` / `DeclEntry` / `decl_get`（`unification` 与 `elaboration` 的分支全部改道） | E1 |
| 精化载体 | 直接改写值 | σ 载体 `Subst` / `wrap_sub` / `frcs` / `SpecSolve`（FINAL §3 已核 13 处 `subst_cxt`） | E4 |
| 模式匹配 | 无独立编译层 | `pattern_match.rs`（20 项）+ `shape.rs` + `struct_eq.rs` | E4 |

⇒ L07 之后 L08–L12 的“名字世界”一行未动：`cxt.rs` 自 L07 起只改 `Val::U` 载荷（L09）后冻结，`Decls`/`DeclEntry` 的接口在 L12 与 L07 逐字相同。

## 3 L08 专题：struct/record 到底改了哪些既有函数

章节增量本身只有 `p_new` / `p_struct` 两个新函数（**语法糖**：`struct` 脱糖成单 `mk` 构造子 enum，`new` 脱糖成限定构造子应用）。真正落点在既有函数内部：

| 既有函数 | L07 | L08 | 档 / 后果 |
|---|---|---|---|
| `parser::p_atom` | 单段投影 `.option()` | `many0()` 左结合链（`parser/mod.rs:311`） | E4；L07 语料 `x.f` 仍命中，**零回归** |
| `parser::p_pattern` | `Ident` + paren/square `many0().concat()` | 前置 `brace(many1_sep)` 分支（`:472`），失败回落原分支 | E4；靠 `nom` 回溯保序 |
| `parser::p_decl` | 3 路 `or_far` | 4 路（`:634` 加 `p_struct`） | E4 |
| `pretty::go`（`SumCase` 臂） | 恒拼 `head::case` | case 名已含 `head.` 则不拼（`pretty.rs:214-221`） | E2-**无后果**：L07 case 名是纯 Ident，不含 `.` |
| `unification::unify` | 无 `(Obj,Obj)` 臂 | 加“字段名同 ⇒ 比接收者 + spine”合同臂（`unification.rs:1087`） | E4（L07 潜伏缺臂，剥链精确化后暴露） |
| `unification::{unify,unify_sp}` | `prof::bump(UNIFY/UNIFY_SP)` | **两处删除**；`mod.rs` 的 `prof` 模块整体消失 | **E3**：`--prof` 计数面在全仓仅存在于 L07 |
| `elaboration` 的 `Raw::Obj` 臂 | 参数槽优先，否则报 `has no field` | `Val::Sum` 分支内嵌“单 case 且名含 `.mk`”的剥链（`:647/:654`），非 struct 仍走原错误 | E4 |
| `elaboration` def 登记 | `render_typ_pretty`→`(串,fin)`（`L07 :309`）+ `push_hover_rendered`（`:314`）+ def 站 inlay（`:330`） | 内联 `render_by_shape`（`:370`）+ 裸 `hover_table.push`（`:376`）+ `fin` 恒 `true`（`:375`） | **E2/E3，见 §6** |
| `surface.rs` / `shape.rs` / `raw_pretty.rs` | — | 仅 doc 首行、尾随空行、no-newline | **E0** |

## 4 L09 专题：宇宙分层波及了参考版的哪些地方

| 波及点 | L08 | L09 | 档 / 后果 |
|---|---|---|---|
| `Raw::U` | 单元 | `Raw::U(u32)`（`parser/syntax.rs:80`） | E4 |
| `Raw::Sum` | 3 元组 | 加第 4 位宇宙（`parser/syntax.rs:86`） | E4 |
| 字法 | `("U", UKeyword)` | `("Type", TypeKeyword)`（`parser/lex.rs:98`） | E4（裸 `U` 消失，FINAL §5#9 已记） |
| 语法 | `kw(UKeyword)` 直接映射 `Raw::U` | `Cut((kw(TypeKeyword), string(Num)))`（`parser/mod.rs:303`） | E4 |
| `Tm::U` / `Val::U` | 单元 | 带载荷（`mod.rs:83` / `:257`） | E4（穿线 12 文件、写 50+ 处） |
| `Raw::U(x)` 推断 | — | `(Tm::U(x), Val::U(x+1))`（`elaboration.rs:820`）；Π 取 `max`（`:831`） | E4（分层设计选择） |
| `struct_eq` | `(Val::U,Val::U)` 恒真 | 比层级（`struct_eq.rs:127`） | E4 必然 |
| `pretty` | `out.push('U')` | `Type {uni}`（`pretty.rs:138`） | E4 |
| `raw_pretty` | `Raw::U` → `'U'` | **仍渲染裸 `U`**（`raw_pretty.rs:29`） | **E2：与 `pretty` 不一致，且 L09 起该文本不可再解析** |
| 类型注解检查 | `ty_precheck`（零副作用，`L07 elaboration.rs:176`）+ `check(…, Val::U)` | `check_universe`（推断 + `overwrite_meta`，`elaboration.rs:162` / `:183` / `:209`） | **E2（有意）**；L07 注释点明预检“不造 meta、`?N` 编号不受扰动” |
| 错误尾注 | `got {}` + `pretty_tm`（`L07 elaboration.rs:194-195`） | `got {:?}`（`L12 elaboration.rs:214-216`） | **E2（顺手改）**：L07 注释明令禁止 Debug 转储 |
| enum 层级 | 字段域只 `check_ty` 一次 | 先 `check_universe` 扫 `universe_lvl`（`:386-396`），再 `check_ty` 复检 | **E2**：字段域推断两次 + meta 被提前解 |

**关键归因**：L08→L09 在**声明级只有 `check_universe` 替换 `ty_precheck` 一处增删**（+1/−1），其余全是载荷穿线。但这一处替换改了机制：预检曾是**只读**的，现在是**有副作用的推断**——它会给未解 meta 写 `Solved(Val::U(0))`。设计上这是 `Type N` 必需的（要拿回层级 u 只能解 meta）；**顺带改**的是错误渲染退成 `{:?}`。

## 5 L10 专题：typeclass 是不是“纯加法”

| 面 | 加法？ | 证据 |
|---|---|---|
| 声明级符号 | **是** | `+16 / −0`；无一个既有函数被删 |
| 新文件 / 关键字 | 是 | `typeclass.rs` 417 行；`KEYWORD` 9→13（`parser/lex.rs:103`） |
| 引擎文件的行 | **否** | `elaboration.rs` 三处投影错误路径改走 `trait_wrap`（`:775`）；`unification.rs` 三处 flex 解后加 `solve_multi_trait`（`:867` / `:1139`） |
| 热路径代价 | **否** | `solve_multi_trait`（`:743-765`）每次 flex 解都从 `start` 扫 `self.meta` 到尾、逐个 clone 未解类型再 `force` ⇒ 每解一次 O(#meta)，**无 trait 时也照扫** [推断：整体 O(n²)] |
| 语义副作用 | **否** | 同一次扫描会对**与本次无关**的未解 meta 调 `solve_trait` 并 `overwrite_meta`，改变解序（可观察：`?N` 解集、未解 meta 的报错时机） |
| 接收者路径 | 基本是 | `trait_wrap` 首句就 `pretty_tm`（`:783`）+ `trait_definition.clone()`（`:789`），早退前已付；但只在**原错误路径**上触发，正常程序不付 |

⇒ 结论：**语法层与数据结构层是纯加法，求解热路径不是。** 这是全链唯一一处“章节增量挂到既有热路径上”的改动。

## 6 顺手改的漂移清单（与本章主题无关的那些）

| # | 漂移 | 首现层 | 可观察后果 | 档 |
|---|---|---|---|---|
| 1 | `eval_budget` 整模块 + 带预算入口 `run_with_surface_budget`（`L06 mod.rs:543`）全删 | **L07** | 发散求值（`def f (x:U):U = f x`）不再有协作式中止，内联跑分析会让宿主挂死；`elab timeout` 文案消失 | **E3** |
| 2 | `observe.rs` 整文件 + 6 个 `run_with_surface_*` / `check_with_surface` helper 消失 | **L08** | hover 的 `hover_query` 双闸、def 站 inlay（`L07 :330`）无对位；FINAL §8.2 归因“L08 从来没有 observe.rs”，实测是 **L08 的 11-23 移植选择不搬模块**（`08b516fb` / `f26d4097`） | **E3** |
| 3 | `decl_pretty` 的 `fin` 恒写 `true` | **L08**（`:375`），非 FINAL §4⑤ 说的 L12 | 下游无法区分“定稿渲染 / 需再展开” | E2 |
| 4 | `raw_pretty` 仍输出裸 `U` | **L09**（`:29`） | hover 文本与 `pretty` 的 `Type N` 不一致，且该文本不可再解析 | E2 |
| 5 | `Infer.println_spans` / `inlay_hint` 两字段删除，`run_with_surface` 不再填 | **L09**（`mod.rs:2099` 只剩 `s.hover`） | `surface.rs` 仍声明 `:35/:63`、`inlay_label`（`:149`）成死代码；**LSP 静默为空，无断言会红** | **E3** |
| 6 | `ty_precheck` → `check_universe`（预检 → 解 meta） | **L09** | `?N` 解集与报错时机变化；L07 会报错的注解被静默解成 `U(0)` | E2（有意） |
| 7 | 错误尾注 `{}` + `pretty_tm` → `{:?}` | **L09**（`L12 :214-216`） | 用户可见文案退化为 `Val` 的 Debug 转储 | **E2（应回退）** |
| 8 | enum 字段域被 `check_universe` 预扫 + `check_ty` 复检 | **L09**（`:386-396`） | 声明期 2× 推断；预扫会写 meta | E2 |
| 9 | `solve_multi_trait` 无条件尾扫 | **L10**（`:743`） | 见 §5 | E2 |
| 10 | trait 声明的 `to_typ()` 校验删空（`L11 elaboration.rs:626` / `:633` 的 `"Not a type"` 消失） | **L12**（`:634` 直接 push） | 非类型 trait 实参不再报错 | E2 |
| 11 | `surface.rs:11` 注释引用 `observe.rs` 的 `push_ctor_hover` | L07 起（三处同样指错） | 文档指向不存在的模块 | E1(文档) |
| 12 | `L{NN}_LOOP` / `L{NN}_DEBUG` 与 `demo_path` 每层改名 | 每层 | 脚本/文档里硬编码的变量名逐层失效 | E1 |

## 7 L12 章内但“没接线”的两处

| 项 | 事实 | 后果 |
|---|---|---|
| `Tm::Call` / `Val::Call` | **无任何源头构造点**：`Tm::Call` 的 5 处出现全在 `quote` / `rename` / `pretty` / `tm_size` 的保持式重建（`mod.rs:1936`、`unification.rs:644`、`pretty.rs:241`）；`Val::Call` 同理（`mod.rs:1016/`:1109/`:1624`）。`quote` 明确不自动造节点（`mod.rs:1968` 注释：会造成 ref/twin 显示分叉） | `pretty.rs:241` 的 Call 渲染臂在 L12 是**死代码**；节点只为 L13 预留 |
| `lookup_function_by_cases` | `mod.rs:2565` 定义，**全仓零调用点**（仅 README 提及） | 同上，半成品 |

**唯一一处“改动即修复”**：L10/L11 收 trait 断言实参用 `filter_map(to_typ())`（`L11 unification.rs:787`）——任一实参不可转 `Typ` 就被**静默丢弃**，断言元数与 `out_param` 滤后的形参元数错位；L12 改成 `map(force_deep)` 保元数 + 遇 `Flex` 推迟（`unification.rs:797-801`）。**L12 在改机制的同时修掉了 L10 引入的潜伏缺陷**，这是本章唯一值得表扬的“顺手改”。

## 8 E0/E1 确认等价清单（供他人免于重复核实）

| 结论 | 证据 |
|---|---|
| `pattern_match.rs` 自 L07 起**六层逐字节相同** | SHA `5c5988a9` @ L07/L08/L09/L10/L11/L12 |
| 顶层 `syntax.rs` 自 L07 起**六层逐字节相同** | SHA `9d537a6a` @ L07–L12 |
| `cxt.rs` L07=L08、L09=L10=L11=L12 | SHA `340507a0` / `0fee0d38`；仅 L09 改 `Val::U(0)` 载荷 |
| `struct_eq.rs`（顶层）同理 | SHA `32e04d4d` / `e8af8f4f`；两段间仅 `(Val::U(x),Val::U(y))` 一臂 |
| `shape.rs` / `raw_pretty.rs` 自 L09 起冻结 | SHA `a397e53f` / `6879a927` @ L09–L12 |
| `parser/syntax.rs` L07=L08，L10=L11=L12 | SHA `e286fe48` / `f4619786` |
| `typeclass.rs` L10=L11 逐字节同 | SHA `63ff2302`；L12 重写为 `63deea63` |
| `parser/macros.rs` L11=L12 | SHA `8877a096` |
| L10→L11 引擎核心零改动 | `elaboration` / `unification` / `typeclass` / `cxt` / `pretty` / `shape` 的 SHA 在 L10 与 L11 相同 |
| `surface.rs` 每层只改模块注释首行 | 唯一实质差异是 `Raw::U` → `Raw::U(_)` 的模式匹配（L09） |

## 9 对 FINAL 的两处归因校正

| FINAL 原文 | 本册实测 |
|---|---|
| §4 E2⑤「`decl_pretty` 的 `fin` 标记退化……**L12**」 | **首现 L08**：L08 `elaboration.rs:375` 已恒写 `true`，L09–L12 逐层原样继承（该行在 L12 为 `:349`） |
| §8.2「`push_hover_rendered` 缺失……根因是 **L08 从来没有** L07 的 observe.rs 设计」 | L08 在 11-23 有两次“移植观察面”提交（`08b516fb` / `f26d4097`），**看过 L07 的 observe.rs 却选择内联简化版**；同时删掉 `prof` 探针模块。更准确的表述是“L08 移植时减配”，而非“从未有该设计” |

## 结论摘要

参考版从 L06 到 L12 的**章节增量逐层收敛**：L07 一次大改（+160/−39，和类型 + 名字世界重构），之后每层只加 1–16 个函数（L08 三、L09 一、L10 十六、L11 全在 parser、L12 单文件重写）。声明级“纯加法”只在 L10/L11 成立；L08/L09 各删掉一整块与本章主题无关的基础设施：L08 删 `observe.rs` 与 `prof`（观察面与探针，E3），L09 删两条 LSP 通道字段并让错误渲染退成 `{:?}`（E2/E3）；更早的 L07 还删了 L06 的 `eval_budget`（E3）。**故意的：分层宇宙、typeclass、宏、Call 节点；顺手改的：求值预算、观察面、探针、错误文案、`fin` 标记、`to_typ` 校验。** 后者七项无一被本章主题需要。

## 要改的东西 Top-3

1. **把 `check_universe` 的错误尾注从 `{:?}` 改回 `{}` + `pretty_tm`**（`src/L12_canonical/elaboration.rs:214-216`）。这是 L09 重写时唯一把 L07 明文理由丢掉的改动（`src/L07_sum_type/elaboration.rs:191-195` 原注释：“走 pretty，而非 Val 的 Debug 转储——大值树会印出巨量结构且不可读”）。改法：尾注换成 `pretty_tm(0, cxt.names(), &self.quote(cxt.decl(), cxt.lvl, inferred_type))`；前缀 `expected universe` 已被 blackbox 钉住，只动尾部。
2. **给 `solve_multi_trait` 加无 trait 快路径**（`src/L12_canonical/unification.rs:751-765` 与调用点 `:880` / `:1152` / `:1156`）。当 `self.trait_out_param` 为空（无任何 trait 声明）时直接 `return Ok(())`：既拿回“每次 flex 解都全表扫描”的成本，也把“无关 meta 被提前解”的语义副作用关在 trait 程序内。改动 ≤6 行，不碰求解逻辑。
3. **回退两处“顺手”的退化**：① `raw_pretty.rs:29` 的裸 `U` 改为与 `pretty.rs:138` 一致的 `Type N`（当前 hover 文本不可再解析）；② `Tm::Call` 已是死节点（`mod.rs:1968`），**要么**给它接上零调用点的 `lookup_function_by_cases`（`mod.rs:2565`）、**要么**删掉 Call 双向节点与 `pretty.rs:241` 的死臂，免得下一个维护者按 README 以为它是活的。
