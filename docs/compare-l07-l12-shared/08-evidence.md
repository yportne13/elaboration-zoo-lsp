# 08 · 行为证据与门禁：L07 ⟷ L12

> 角度：**不评价模块语义，只评价"证据面"**——层内测试用例集、孪生封印、跨层门禁、可跑二进制的实跑差分、git 时间线。
> 归因口径按 MAP §10/附录 A：先问"差异首次出现在**哪一层**"，不把 L08/L09 造成的差异记成"L12 重写"。
> 本轮复算覆盖 `src/{L07_sum_type,L12_canonical}/tests.rs`、`tests/` 全目录 84 个 .rs、`Cargo.toml`、`tools/gate_*`、`src/lib.rs`，
> 并用**已存在**的 `target/release/realbench.exe`（16:26 构建）对 27 个共有语料做了 6 层实跑。**全程未构建。**

## 0 结论速览

| 证据面 | 事实 | 档 |
|---|---|---|
| 层内 `#[test]` 集合 | 66 个一个没丢；L12 的 83 = 66 共有 + 17 "新增"，**新增全部来自 L08/L10/L11，L12 自己 0 个** | **E3 = 0** |
| 层内用例正文 | 59/66 逐字节同；余 7 个差异 = `U`→`Type 0`（L09）+ `l07_`→`l12_` 替换 | E1 |
| `tests.rs` 整文件 | L07→L12 只删 45 行 / 加 492 行，**45 行 100% 是宇宙关键字改名**；L11→L12 只改 9 行（全是 `l11_*`→`l12_*`） | E1 / **E0** |
| 孪生封印 | 两侧**对称**封印（L07 `7a68abc7`/11-22，L12 `2acc5231`/11-23），默认都关 | E1 |
| 跨层门禁 | **没有任何测试断言 L07 ≡ L12**；最近的 3 个是"同语料逐层各自钉" | E3（门禁面） |
| L12 孪生是否 LSP 默认引擎 | **不是**——LSP 默认孪生是 L13 的 | — |
| 二进制实跑 | 27 个纯共有语料：L07 **27/27**，L12 **23/27**；4 个失败**全部在 L08/L09 就出现**，L10=L11=L12 完全一致 | **E3-继承** |

## 1 (a) 层内测试用例差集：零丢失

### 1.1 规模（`src/*/tests.rs`）

| 项 | L07 | L12 | 差 |
|---|---:|---:|---:|
| 总行 / 非空行 | 2397 / 1925 | 2926 / 2358 | +529 / +433（任务书里的 1925→2358 是非空行口径） |
| 归一化 token（MAP §1） | 5,493 | 6,190 | +697 |
| `#[test]` 函数 | 66 | 83 | +17 |
| `#[ignore]` / 被 feature 条件包裹的用例 | 0 / 0 | 0 / 0 | 0 |

### 1.2 集合运算（`#[test]` 函数名，两侧全量抽取）

| 集合 | 数量 | 结论 |
|---|---:|---|
| 共有 | **66** | = L07 全部 |
| **仅 L07 有** | **0** | **没有丢任何用例** |
| 仅 L12 有 | 17 | 见 1.3 |
| 重名 | 0 | 两侧均无同名重载 |

⇒ 就 `tests.rs` 而言，L12 的用例集是 L07 的**严格超集**，"L07 有 / L12 没有"的差集**为空集**。

### 1.3 那 17 个"L12 新增"其实不是 L12 加的（按首次出现层归因）

| 首次出现层 | 用例数 | 用例 |
|---|---:|---|
| L08_product_type | 12 | `test_product_{basic,generic,dependent,field_err,vs_plain_enum,dependent_check,new_dot_chain,shadow,field_blank_lines}`、`test_string_empty_and_escape`、`test_nested_pattern_refine_two_phase`、`test_absurd_nested_pattern_not_missing_coverage` |
| L10_typeclass | 3 | `test_trait_tostring_projection`、`test_trait_blanket_say`、`test_trait_outparam_add` |
| L11_macro | 2 | `test_macro_stringify_builtin`、`test_macro_decl_expansion` |
| **L12_canonical** | **0** | — |

⇒ L12 本章的主题（typeclass/Call/canonical trait 求解）在 `tests.rs` 里**一个新单元测试也没补**；它是靠 `tests/l12_blackbox.rs` 与 `tests/l12_fast_parity.rs` 覆盖的（§3）。

### 1.4 共有 66 例的正文差异：只有 7 个，全部是机械替换

| 用例（L07 行 / L12 行同号） | 差异 | 归因层 | 档 |
|---|---|---|---|
| `struct_eq_vsub_pointer_identity` `tests.rs:1816` | `Val::U` → `Val::U(0)`（4 处） | L09 | E1 |
| `force_arg_unwraps_nested_vsub` `:1781` | 同上 | L09 | E1 |
| `subst_lookup_conditional_wrap` `:1748` | 同上 + 注释 `1 := U`→`1 := Type 0` | L09 | E1 |
| `visibility_boundary_decl_value_is_not_refined` `:2268` | 同上 | L09 | E1 |
| `cross_meta_cycle_force_is_bounded` `:2301` | 同上 + 断言文案 `展开为 U`→`展开为 Type 0`（L12 `tests.rs:2284`） | L09 | E1 |
| `loose_string_requires_empty_spine` `:2325` | `Val::U`→`Val::U(0)` | L09 | E1 |
| `test_file_io_builtins` `:1697` | 文件名 `l07_test_io.txt`→`l12_test_io.txt`、`: U`→`: Type 0` | L09 | E1 |
| 其余 **59 例** | 逐字节相同 | — | **E0** |

**为什么算 E1**：`Val::U`→`Val::U(0)` 是同一构造子加了层级字段（L07 `bump_spine_iter/syntax.rs:28` `U,` / L12 `bump_spine_iter/syntax.rs:27` `U(u32)`），断言的结构与语义角色（"裸 rigid 槽位"、"干净解值"、"σ 可见性边界"）一字未改，只是构造参数多写一个 `0`。

### 1.5 权威口径：整文件 `git diff --no-index` 的 45 行删除逐条归类

`git diff --no-index src/L07_sum_type/tests.rs src/L12_canonical/tests.rs` = **-45 / +492**。45 行**无一例外**属于三类：

| 类别 | 行数 | 例 |
|---|---:|---|
| 源码字符串里的宇宙关键字 `U` → `Type 0` | 24 | `def the(A : U)(x: A): A = x`、`def NatC : U =`、`enum T(A : U) {` |
| Rust 侧 `Val::U` → `Val::U(0)` / `ty: Val::U` | 14 | `let ty = Val::U;`、`assert!(matches!(s3.lookup(Lvl(1)), Val::U));` |
| `l07_` 前缀（测试 IO 文件名、注释里的 `l07_fast_parity`） | 7 | `println U ;`→`println Type 0 ;`（span 用例的源串，同步改） |

⇒ **零断言被删、零用例被删、零期望值被改。** 这是"没丢覆盖"的硬证据。

## 2 (b) 孪生封印与开关：两侧对称，不存在"L12 没封印"

| 项 | L07 | L12 | 锚点 |
|---|---|---|---|
| parity 套件首行封印 | ✅ | ✅ | `tests/l07_fast_parity.rs:1` / `tests/l12_fast_parity.rs:1` 均为 `#![cfg(feature = "...-twin")]` |
| 封印提交 | `7a68abc7` 2026-11-22 | `2acc5231` 2026-11-23 | `perf(L09-L12): let 洞快路径 + 孪生封印（与 L07/L08 对齐）` |
| `Cargo.toml` feature | `l07-twin = []` (189) | `l12-twin = []` (196) | **`[features]` 段无 `default = [...]`（0 处匹配）⇒ 全部默认关** |
| parity 用例数 | 27 | 48 | 都跑不到 |
| 有无 gate 传 `--features` | 无 | 无 | `tools/gate_l13.ps1:220` 只传 `--features l13-twin` |

⇒ **任务书里的"L12 待定"可以结案：L12 已封印，且与 L07 完全对称。** 后果是 MAP §6.2 说的那句——**孪生漂移没有任何门禁会报警**，这对 L07 和 L12 同样成立，不构成 L12 单边落后。

## 3 (c) 跨层门禁清单：**没有任何一个在比 L07 ⟷ L12**

逐个 `tests/*.rs` 检查（84 个文件），只列与"跨层"沾边的：

| 文件 | 比较对象 | 是否 L07⟷L12 | 能否变红 |
|---|---|---|---|
| `tests/audit_crosslayer_probe.rs` | L07..L13 全矩阵（`L07:198`/`L12:203`） | 同语料，但**只写 TSV** | **不能**：全文 `assert!` 计数 = **0**，唯一 `#[test]` 在 `:936` |
| `tests/prim_identity_cross_layer.rs` | 5 条 prim 性质 × 7 层各自断言（`L07:98` / `L12:103`） | 间接：两侧都要满足同一组性质 | 能（但只 5 条） |
| `tests/gadt_refine_cross_layer_tests.rs` | 5 个 case 家族 × 7 层，**每层各自写死期望**（`L07:177/196`、`L12:187/206/267/285/304`） | 间接 | 能 |
| `tests/implicit_comma_args.rs` | L07 内部字节等价（`:111`）+ L12 不回归（`:240`） | 否，两层各测各的 | 能 |
| `tests/backport3_pretty_tests.rs` | L11/L12 pretty 的 `[...]` 约定（对齐 L07/L08/L13 口径） | 只钉约定，不比对 L07 实跑 | 能 |
| `tests/l07_l13_known_diff.rs` | **L07 ⟷ L13** 逐程序钉 | **否**（且全仓无 `l07_l12_known_diff.rs`） | 能 |
| `tests/engine_parity_report.rs`、`r7_engine_parity.rs`、`twin_engine_tests.rs` | 同层 ref ↔ twin（L13 域） | 否 | 能/报告型 |

⇒ **结论：不存在直接的 L07⟷L12 对拍门禁。** 最近的三个是"同一批语料逐层各自断言一个期望值"——它们能在**某一层单独回归**时变红，但不会因为"L07 与 L12 彼此不同"而变红。这就是为什么本轮必须靠 §1 的集合运算 + §5 的实跑来取证。

## 4 (d) L12 孪生**不是** LSP 的默认引擎（L13 才是）

| 事实 | 锚点 |
|---|---|
| LSP 启动引擎 = `Engine::lsp_default()`，未设 `TYPORT_LSP_ENGINE` 即 `Engine::Twin` | `src/lib.rs:297-302`、`:4201` |
| **孪生 prelude 类型是 L13 的**：`twin_prelude: Mutex<Option<L13_namespace::PreludeParse>>` | `src/lib.rs:461` |
| 孪生求值预算走 `L13_namespace::eval_budget::scope` | `src/lib.rs:1597` |
| `src/lib.rs` 全文**没有** `L12_canonical::bump_spine_iter` 的任何引用 | grep 结果为空 |
| L12 孪生只被 `src/bin/{l12bench,realbench,l06l13mem}.rs` 与封印的 `l12_fast_parity` 使用 | `src/bin/realbench.rs:726-763` |

⇒ L12 孪生是**库内可见的基准件**（`pub mod L12_canonical`，`src/lib.rs:67`），不是产品路径。它漂移了不会影响 LSP 输出——这既降低了风险，也解释了"为什么漂移可以长期无声"。

## 5 (e) 已存在二进制的有限行为差分

**入口选择**：`realbench.exe` 是唯一能"同一份语料、任选 L07..L12"的已编译入口（`--layer L07|L12 --corpus <dir> --validate`，`src/bin/realbench.rs:138-200` 的 parse+语义闸门，输出 `PASS/SKIP,<layer>,<file>,reason=...`）。
语料用 `tools/bench_corpus/L07`（27 个 L07 期程序 = 纯共有核心）。**没有 cargo build。**

| 层 | pass | skip | SKIP 原因 |
|---|---:|---:|---|
| **L07** | **27** | **0** | — |
| L08 | 26 | 1 | `ex_let_match_forms` `twin_nf_fail` |
| **L09** | 23 | 4 | 上者 + `ex_church_strings`/`ex_multi_index_gadt`/`ex_type_family_match` `name not in scope: U` |
| L10 | 23 | 4 | 与 L09 逐字相同 |
| L11 | 23 | 4 | 与 L09 逐字相同（错误文案升级为 `ref_run_err`/`twin_run_err`） |
| **L12** | **23** | **4** | **与 L11 逐字相同** |

**差分定位**：L12 相对 L07 的 4 个行为差异**没有一个由 L12 引入**——

| 差异 | L07 | L12 | 首次出现 | 档 |
|---|---|---|---|---|
| 裸 `U` 关键字不再被接受（3/27 程序） | `("U", UKeyword)` `src/L07_sum_type/parser/lex.rs:90` | 关键字表只有 `("Type", TypeKeyword)` `src/L12_canonical/parser/lex.rs:116`；错误文案 `name not in scope: U`（`src/L12_canonical/elaboration.rs:918`） | **L09** | **E3-继承** |
| `let/match` 组合在**孪生**上判型失败：`can't unify Vec[[Nat], (y => y)] == Vec[[Nat], Nat::zero]`（ref 通过） | 双引擎均通过 | 仅 twin 失败 | **L08**（`twin_nf_fail`） | **E3-继承**（孪生现状） |

⇒ 在**行为层**，L10 = L11 = L12 完全一致；**L12 本章没有引入任何共有核心的行为回归**。这与 MAP §10 A.1 的 token 结论（L11→L12 只动 1.4%）在方法上互相独立地吻合。

**文本级差异**：`[未核实]`。现有二进制没有暴露"某层 `run` 的 stdout 原文"的开关（`typort check` 只走 L13 产品链；`l07bench/l12bench` 只打印计时与 parity 布尔）。可确认的文本级事实仅限错误文案：3 个失败在 L09/L10/L11/L12 四层的错误字符串**完全一致**（`name not in scope: U`）。

## 6 观察面测试覆盖：本章唯一确凿的 L12 侧 E3

| 套件 | L07 | L08 | L09 | L10 | L11 | **L12** |
|---|---:|---:|---:|---:|---:|---:|
| `tests/lN_lsp_surface.rs` 用例数 | **11** | 5 | 3 | 3 | 3 | **3** |
| `tests/lN_blackbox*.rs` 用例数 | **149**（v1 49 / v2 53 / v3 47） | 2 份 | 1 份 | 1 份 | 1 份 | **68**（1 份） |

- L07 的 11 例来自两次**晚于 L12 重建**的提交：`f6badca5`、`17b2058f`（11-21~23，`observe.rs` 引入期）；
- L09–L12 的 3 例来自 `2ad6b1b4`（11-23 "移植 L07/L08 的观察面"），**四个层共用同一份 3 例**；
- L07 有、L12 无对位的表面用例至少 8 个：`literal_hover_and_println_span`、`hover_query_renders_only_entry_at_offset`、`inlay_only_for_holes_in_view`、`check_issue_lines_are_drained_once`、`failed_decl_channel_records_and_continues`、`ctor_use_site_hover`、`completion_offers_enum_cases_after_qualified_receiver`、`hole_inlay_uses_expected_type`。黑盒面：`l12_blackbox` 的 68 个用例名**包含 `l07_blackbox.rs`(v1) 的全部 49 个**；但 `l07_blackbox_v2/v3` 的 100 个用例在 L12 **无同名对位** → 是否有等价覆盖 `[未核实]`（v2/v3 是 L07 专属攻击轮，未必属于"共有核心"）。

⇒ **E3（L12 落后）**：观察面的测试深度只有 L07 的 3/11。这与 MAP §6.1 的地雷（`push_hover_rendered` 在 L12 grep = 0）是同一块盲区——**没有用例会因为这个缺口变红**。首次出现在 L09（多轮黑盒实践在 L09 收缩为单文件），L12 原样继承。

## 7 已确认等价清单（不要重复计入差异）

| 项 | 判定依据 | 档 |
|---|---|---|
| `tests.rs` 66 个共有用例的名字集合 | 集合运算，差集为空 | E0 |
| 其中 59 个用例的正文 | 逐字节相同 | E0 |
| `tests.rs` 在 L11→L12 之间 | 9 行差异全是 `l11_*`→`l12_*` 文本 | E0 |
| 孪生封印策略 | 两侧同款 `#![cfg]` + 同款 commit 语义 | E1 |
| `l12-twin`/`l07-twin` 默认关闭 | `Cargo.toml` 无 `default` | E0 |
| 27 个共有语料在 L10/L11/L12 的判定 | 实跑，逐字相同 | E0 |
| 3 个 `U` 失败的错误文案在 L09–L12 | 实跑，字符串相同 | E0 |
| `implicit_comma_args.rs` 的 L07 字节等价钉 / L12 不回归钉 | 两层各自成立，且 L12 侧期望值为 L07 形态 | E1 |

## 一脉相承评级

**强（偏强）** —— 就"行为证据与门禁"这个角度：L07 的 66 个层内用例在 L12 里**一个没丢**（59 个逐字节同、7 个只差宇宙关键字改名），`tests.rs` 的 45 行删除 100% 是 `U`→`Type 0` 的机械替换，L11→L12 更是只改了 9 行层号；27 个纯共有语料的实跑判定在 L10=L11=L12 逐字一致，4 个与 L07 的差异全部定位到 L08/L09；唯一的 E3（观察面测试 11→3）也是 L09 起就有的、并被 11-23 的移植原样带过来。扣分项是**证据基础设施**：全仓没有任何 L07⟷L12 的直接对拍门禁，两侧孪生对称封印，`audit_crosslayer_probe.rs` 0 断言永不变红——所以"一脉相承"是靠本轮手工取证得到的，不是仓库自己会报警的。

## Top-3 差异

1. **E3（L09 起继承）** 裸 `U` 关键字在 L12 已不存在：`src/L07_sum_type/parser/lex.rs:90` `("U", UKeyword)` / `src/L12_canonical/parser/lex.rs:116` 只有 `("Type", TypeKeyword)`；实跑 3/27 个 L07 期共有语料在 L12 直接 `name not in scope: U`（L07 27/27 全过）。
2. **E3（L12 侧落后）** 观察面测试深度 11→3：`tests/l07_lsp_surface.rs`(11 例，`f6badca5`/`17b2058f` 11-21~23) vs `tests/l12_lsp_surface.rs`(3 例，`2ad6b1b4` 11-23 移植)；L07 的 8 个 hover/inlay/check-issue 用例在 L12 无对位，`push_hover_rendered` 类缺口无门禁可捕。
3. **E3（门禁面缺口）** 全仓无 L07⟷L12 直接对拍：最近的 `tests/audit_crosslayer_probe.rs`（`:198`/`:203` 含两侧）全文 **0 个 `assert!`**、只写 TSV，永不变红；`tests/l07_l13_known_diff.rs` 只钉 L07↔L13；`l07-twin`/`l12-twin` 对称封印（`Cargo.toml:189/196`，`tests/*_fast_parity.rs:1`），孪生漂移无声。
