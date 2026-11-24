# 06 观察面（hover/inlay/completion/goto 数据面）与 pretty/quote 渲染

## 1 范围与方法

覆盖 4 个同路径文件（`pretty.rs`、`raw_pretty.rs`、`surface.rs`，以及 L07 独占的 `observe.rs` / L13 孪生的 `bump_spine_iter/observe.rs`），外加 `src/lib.rs` 的 LSP 消费层（L13 单边）。方法：先 grep 建符号表 → 按机制抽查 → 用 Lead 的 `fn-matrix.tsv` 同名函数体相似度交叉验证 → 用 `git diff --no-index` 在 L07–L12 之间做"同质性对照"（这是本角度最有力的一把尺子：**L06–L12 是逐章 copy-forward 链，L13 是离群点**）。
行数取 read 工具 totalLines；token/保留率沿用 MAP §1（L07 pretty 827→L13 7,023 tok；raw_pretty 237→288；surface 1,431→834）。
**未运行任何二进制**（不跑 `src`，不 `cargo test`），故凡"行为会怎样"均以两侧测试断言或代码直读为锚点，不实测。

## 2 模块对位表

| 文件 | L07 tok/行 | L13 tok/行 | 保留率(文字/归一) | 判读 |
|---|---|---|---|---|
| `pretty.rs` | 827 / 308 行 | 7,023 / 852 行 | 34% / 54% | **重写（E2）**：L13 核心换实现（`go(out:&mut String)` → `pretty_tm_indent→String`），多出 Call/OpCall/U(u32)/Nat 四类项；852 行里 334 行（519–852）是内联测试，L07 无内联测试 |
| `raw_pretty.rs` | 237 / 195 行 | 288 / 319 行 | 79% / 84% | **继承 + 单边加固（E1→E2）**：`go` 体相似 0.683、两侧都是单缓冲写入；但 `def_type_from_source` 被 L13 重写（0.132）、`pattern` 完全两物（0.010） |
| `surface.rs` | 1,431 / 196 行 | 834 / 166 行 | 26% / 27% | **契约同源、周边不同**：5 个同名自由函数 `hover_entry_at/hover_text_at/is_empty/hover_only/view` 体相似 **全部 1.000**（fn-matrix）——"token 只留 26%" 是因为 L07 的 `span_union/raw_span/pattern_span/inlay_label/failed_decl_names` 全不在 L13 这个文件里了 |
| `observe.rs` | 13,951 B / 351 行 | **顶层无此路径** | — | L07 顶层独占；L13 顶层 `mod.rs:20-23` 只有 `pretty/raw_pretty/surface` |
| `bump_spine_iter/observe.rs` | L07 孪生**无**此文件 | 60,342 B / 1,366 行 | — | 孪生侧独占（`bump_spine_iter.rs:193` `mod observe;`）；**其中 impl 段仅 9–200 行**，205–1,366 是 `observation_tests`（≈85%），不要按 60KB 估实现量 |
| `src/lib.rs` LSP 层 | 无（`lib.rs:52` 仅 `pub mod L07_sum_type`） | `hover_at`/`hover_def_block`/`hover_code_block`/`with_hover_entries` | — | **E4 单边新增**：L07 的观察面**没有任何 LSP 消费者**，只被 `tests/l07_*` 调用 |

**跨章同质性（关键背景，建议全组共用）**：

| 文件 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `raw_pretty.rs` 行 | 195 | 195 | 195 | 195 | 195 | 195 | 319 |
| `pretty.rs` 行 | 308 | 312 | 312 | 312 | 312 | 329 | 852 |
| `surface.rs` 行 | 196 | 196 | 196 | 203 | 203 | 204 | 166 |

`git diff --no-index` 实测：`raw_pretty` L07 vs L08 = **1 行**、L07 vs L12 = **2 行**；`pretty` L07 vs L12 = 25+/4-；`surface` L07 vs L12 = 12+/4-。⇒ **L07–L12 是同一份文件的 6 次落盘**，L13 是唯一分叉点。把 L07 当"上游"只是编号小；就代码而言 L12≈L07，L13 才是异类。

## 3 逐机制差异表（核心）

| 机制 | L07 实现(锚点) | L13 实现(锚点) | E 档 | 可观察后果 / 风险 |
|---|---|---|---|---|
| `LspSurface` 六字段骨架 | `surface.rs:26-41` | `surface.rs:21-34` | **E1** | 字段名与顺序逐字对齐（L13 注释自称"字段顺序与 L07–L12 对齐"，`surface.rs:19`）；`is_empty` 体 1.000 |
| `completion` 元素类型 | `Vec<(Span,String)>` `surface.rs:31` | `Vec<(Span,SmolStr)>` `surface.rs:25` | E1 | 仅容器类型，语义同；下游 `lib.rs:708/720` 用 `SmolStr` |
| `check_issues` 通道 | `Vec<(usize, String)>`（decl 下标+行），`surface.rs:38`+`observe.rs:258-282` 只在 `lsp_collect` 时从 `CheckIssues` 全局排水 | `Vec<String>`，取自 `accumulated_errors`，`surface.rs:31/133` | **E2** | L07 有"每行归属哪个 decl"的索引，L13 丢了，且换数据源（全局 builtin vs 引擎错误表）；跨层诊断分组口径不同 |
| `println_spans` | 真渲染串：`observe.rs:250-255` | **恒空串**：`surface.rs:143-148` 只回 span（渲染延迟到 `lib.rs` 轮末 `println_jobs`） | **E2** | 同一字段两侧一个是内容、一个是空壳；任何按字段比对的 parity 断言都会假阳/假阴 |
| `failed_decls` | `Vec<String>`，插入序 + `contains` 去重（`surface.rs:40`、`observe.rs:285-291`） | `HashSet<SmolStr>`（`mod.rs:1508`）→ `.iter()` 进快照（`surface.rs:134`） | **E2** | **顺序不确定**；A2 根因抑制若依赖序，行为随哈希种子变 |
| 快照入口 | `pub(crate) fn surface()`（`observe.rs:294`，crate 内） | `pub fn lsp_surface()`（`surface.rs:127`，公开）；唯一消费者 `lib.rs:767` | E1 | 位置从 observe.rs 搬到 surface.rs；可见性收紧→放开 |
| 单通道 API | **无** | `lsp_hover/lsp_completion/lsp_inlay`（`surface.rs:82-104`，87fdafd6） | **E4** | L13 修 2.2× 回退用；L07 侧无对应问题域（无 LSP 常驻） |
| 查询期借用扫描 | **无**（只有采集期过滤 `SurfaceQuery`→`hover_query/inlay_query`，`surface.rs:73-88`+`mod.rs:2269-2270`） | `lib.rs:674 with_hover_entries`、`687/697`、`720/730`（911628b3，74–78×） | **E2（口径不同）** | 两侧都把方案叫"惰性采集"，但 **L07 在采集期省渲染、L13 在查询期省克隆**；L13 两者都有（`surface.rs:107-115` 保留了采集期过滤） |
| 清表范围 | 无此函数（每轮新建 `Infer`） | `clear_observation_tables` 只清 hover/completion/inlay+`decl_shapes`，**刻意不清** `accumulated_errors`/`failed_decls`（`surface.rs:150-165`，87fdafd6 修正确性） | **E4** | L13 的正确性修复；但孪生同名函数清 6 张表含 `println_spans`（`bump_spine_iter/observe.rs:12-19`）⇒ **L13 参考版与 L13 孪生自己就不一致** |
| def-site hover 文案来源 | 源码文本直接进 hover 表：`elaboration.rs:305-314`（`push_hover_rendered`） | 源码文本只进 `typ_pretty`(e.6)→`lib.rs` def 面板；hover 表条目走**值渲染**：`elaboration.rs:1688-1695` | **E2** | **同一程序 hover 串不同**（见 §4-A）；L13 有两条渲染口径、L07 只有一条 |
| 全局名 hover 复用登记串 | `decl_pretty` 旁表，**只在 `(s,true)`（无未解 meta）时复用**：`observe.rs:204` | `cxt.decl` 第 7 槽 `typ_pretty`，**只判非空**：`elaboration.rs:2879-2884`（9364b541） | **E2** | L13 少了"final"门 → 登记后才有解的 meta 可能把 `?N` 冻进使用处 hover。L13 孪生自己写着"不得用登记串"（`bump_spine_iter/observe.rs:47-53`）并按 `typ_pretty_final` 门控（:63）⇒ **参考版比孪生更激进** |
| 构造子 hover 记忆化 | 无条件入 `ctor_pretty`：`observe.rs:219-225` | 先 `no_metas` 再入 `ctor_hover_memo`：`elaboration.rs:2960-2963` | **E2（反向！）** | 这里 **L07 落后**：会把未解 `?N` 冻进后续同键 hover；L12/L13 修了，未回灌 L07 |
| inlay 标签截断 | 统一 `surface::inlay_label`（80 字符，`surface.rs:149`），两个站点都走它（`elaboration.rs:329`） | 两个站点各写一份：`:480-495` 截断、`:1711-1724` **不截断** | **E2** | L13 的 def 返回类型 inlay 可产出超长 label；L07 不会 |
| pretty 写入策略 | 单缓冲增量写，注释明确为消除 O(n²)（`pretty.rs:77-81`） | `format!` 自底向上拼串、返回 `String`（`pretty.rs:221-497`） | **E2** | L13 丢掉了 L12 已有的单缓冲优化（L12 `pretty.rs:81` 有 `out:&mut String`）；深层嵌套质量级退化 |
| pretty 定深截断 | `MAX_DEPTH=1024`+`thread_local`+`DepthGuard`（`pretty.rs:17-29,82-89`），有测试钉住（`tests.rs:1995`） | **完全无**（`grep MAX_DEPTH src/L13_namespace/pretty.rs` 空；L09–L12 都有） | **E3** | L13 只有 `pretty_nat` 对 Nat 链做了迭代化（`pretty.rs:499-524`），非 Nat 深项（深 Pi/深 Match）仍无保护 → 显示路径可爆栈 |
| 形状认回 `render_by_shape` | `observe.rs:59-111` | `elaboration.rs:2905-2945` | **E1** | 同日成对提交（6f7e245e ⟷ c824c43a），算法逐段同构；但 L13 版**丢了 pending 实参**（L07 :86-92 有，L13 :2923-2928 没有），只拼 `head scrut` ⇒ 多参卡住 match 会少参数（[推断]，未见测试覆盖） |
| `U` 的显示 | `Tm::U` 单元变体 → `"U"`（`pretty.rs:138`） | `Tm::U(u32)` → `"Type {uni}"`（`pretty.rs:289`） | **E2（语言级）** | `def f : U` 在两侧 hover 出 `U` vs `Type 0`；根因是项表示不同，不是渲染口味 |
| Nat 字面量显示 | 无原生 Nat（`grep Val::Nat/Raw::Nat src/L07_sum_type` 空）；`succ^k zero` 打成 k 层 `SumCase` | `pretty_nat` 迭代累加成十进制（`pretty.rs:409-411,499`） | **E4** | 同源提交 `d12a8ed2` 只解决"展开的 match"，`a68605ff` 才顺带绕开 `quote_nat`；**L07 侧不存在 `quote_nat`**，两提交不是同一件事 |
| 运算符/调用式显示 | 无（`Sum[...]` 全方括号、`SumCase` 构造子 `E::c(a b)`） | `head_symbol` 中缀还原、`go_call` 隐式/显式分组、`Sum[impl](expl)`、ZWSP（`pretty.rs:32-53,199-207,387-408,451-478`） | **E4** | L13 显示更接近源码；同一项在 L07 显示 `Nat::succ(x)` 而 L13 可能 `x + 1` |

### 3-A L07 `observe.rs`（351 行）职责去向：搬迁，不是 E3

| L07 `observe.rs` 项（行） | L13 承接处（锚点） | 判定 |
|---|---|---|
| `hover_wanted`/`inlay_wanted`（:36-44） | `L13 surface.rs:107-115`（同名同体，搬到 surface.rs） | E1 搬迁 |
| `render_val`（:47-55） | 无独立函数，内联进 `push_hover`（`elaboration.rs:2898-2900`） | E1 内联 |
| `render_by_shape`（:59-111） | `elaboration.rs:2905-2945` | E1（细节见 §3 表末行） |
| `render_typ_pretty`（:115-123） | 参考版无此函数（渲染内联 `elaboration.rs:1630-1637`）；孪生有 `machine.rs:1051` | E1/E3 混 |
| `tm_has_unsolved_meta`（:126-177） | 换成 `Tm::no_metas`（`elaboration.rs:1714`、`:2960`） | **E2**：不同谓词 |
| `push_hover`/`push_hover_rendered`（:182-196） | `elaboration.rs:2889`；`push_hover_rendered` **无对应** | E1 / **E3** |
| `push_hover_decl`（:199-210，带 `Val`） | `elaboration.rs:2870-2887`（不带 `Val`，返回 bool） | **E2**（签名+安全性，见 §3） |
| `push_ctor_hover`（:214-226） | `elaboration.rs:2952-2965` | **E2**（meta 门控） |
| `push_inlay_hint`/`push_inlay_label`（:229-247） | 两处内联（`elaboration.rs:480-495`、`:1711-1724`）；后者无截断 | **E2** |
| `push_println_span`（:250-255） | 延迟作业 `println_jobs`（`elaboration.rs:1743-`、`surface.rs:143`） | **E2** |
| `drain_check_issues`（:258-282） | `accumulated_errors`（`surface.rs:133`） | **E2** |
| `note_failed_decl`（:285-291） | `mod.rs:1643 note_failed_decl`→`:1650 note_failed_names`→`:1657 failed_decl_names`（`Vec<SmolStr>`） | E1/E2 |
| `surface()`（:294-310） | `surface.rs:127 lsp_surface()` | E1 |

**结论**：L07 `observe.rs` 的职责 12/13 项在 L13 **有承接点**，只是位置从"每章一个 observe.rs"变成"surface.rs 谓词 + elaboration.rs 内联 + mod.rs 名字集"。所以是 **搬迁+重写（E1 为主、6 处 E2）**，不是 E3。顶层的"文件缺失"是 E3，但"职责缺失"不成立。**唯一的 E3 是 `push_hover_rendered`**——L13 没有"已渲染串入表"的入口，这正是 §4-A 文案分叉的代码根因。

### 3-B `LspSurface` 契约方法级对照（"统一观察面"实测）

| 项 | L07 | L13 | 备注 |
|---|---|---|---|
| `hover_entry_at` / `hover_text_at` / `is_empty` | `surface.rs:45/54/59` | `surface.rs:38/47/52` | 体相似 **1.000**（fn-matrix），真同源 |
| `SurfaceQuery` + `hover_only`/`view` | `surface.rs:73-88` | `surface.rs:65-80` | 1.000，真同源 |
| `span_union`/`raw_span`/`pattern_span` | `surface.rs:91/108/139` | **无** | L13 不需要"从 AST 折 span"（span 由 elaborate 各站点带出） |
| `inlay_label` | `surface.rs:149` | **无**（截断逻辑内联两份，不一致） | 见 §3 表 |
| `failed_decl_names` | `surface.rs:161`（`Vec<String>`） | `mod.rs:1657`（`Vec<SmolStr>`） | 换模块 + 换元素类型 |
| `set_surface_query` | **无**（直接写字段，`mod.rs:2269-2270`） | `surface.rs:119-122` | L13-only 便捷入口 |
| `lsp_hover`/`lsp_completion`/`lsp_inlay` | **无** | `surface.rs:90/96/102` | L13-only（87fdafd6，单通道克隆）；**E4** |
| `println_spans`（方法） | **无**（`println_spans` 是字段） | `surface.rs:143` | 同名不同物：L07 是字段、L13 是"构造空串列表"的方法 |
| `clear_observation_tables` | **无** | `surface.rs:159` | L13-only；孪生另有同名不同体（`bump_spine_iter/observe.rs:12`） |
| `lsp_surface` | `surface()`（`observe.rs:294`，`pub(crate)`） | `lsp_surface()`（`surface.rs:127`，`pub`） | 同职责、异名异可见性（E1） |

⇒ "统一观察面"在**查询端**（`hover_entry_at` 三件套 + `SurfaceQuery`）是**逐字节统一**；在**采集端**（`wanted` 谓词同、入口不同）和**快照端**（3 个字段语义分叉 + 3 个 L13-only 方法）只是**同形**。这就是"契约同源、实现分家"的准确刻度。

## 4 抽样深挖

### 4-A `def` 名上的 hover 串：同一程序、两侧不同（E2）

L07：源码文本**直接进 hover 表**（`src/L07_sum_type/elaboration.rs:305-314`）：
```rust
let src_ty = has_source_type(&ret_type).then(|| def_type_from_source(&params, &ret_type));
let (s, fin) = match src_ty { Some(s) => (s, true), None => self.render_typ_pretty(&cxt, rendered_vtyp) };
self.decl_pretty.insert(key.clone(), (Rc::new(s.clone()), fin));
self.push_hover_rendered(name.to_span(), name.to_span(), &s);
```
而 `def_type_from_source` 是**逐参数一组**、冒号前带空格（`raw_pretty.rs:170-187`：`out.push_str(" : ")`、每组 `") → "`）。

L13：源码文本**不进 hover 表**，只进 `typ_pretty`；hover 表走值渲染（`src/L13_namespace/elaboration.rs:1688-1695`，注释自己写明"两者各有消费方"）：
```rust
// - typ_pretty（e.6）→ lib.rs 的 hover_def_block（源码形态）；
// - hover_table 的 def-site 条目 → 走 push_hover（折叠形态）。
self.push_hover(ret_cxt, name.to_span(), name.to_span(), &vtyp);
```

两侧测试各自钉死了不同文案：
- L07 `tests/l07_source_render.rs:46`：`assert_eq!(t, "(n : Nat) → T n")`；同文件 :95 无注解路径 `assert_eq!(t, "(n: Nat) → T n")`——**L07 自己两条路径空格就不一致**。
- L13 `debug_test.rs:523`：`assert_eq!(typ_pretty, "(n: Nat) → T n")`（源码形态，已折叠且无空格）；L13 hover 表侧 `debug_test.rs:72-75` 钉 `"(x: Nat, y: Bool) → Bool"`，`tests/hover_tests.rs:130-134` 钉面板 `"foo : (a: Nat, b: Boolean) → Boolean"`。
⇒ 为什么是 E2 而非 E1：不是"同一机制换写法"，而是**同一输入被路由到两个不同渲染器**。`def foo(a: Nat, b: Boolean): Boolean = b` 在 L07 的 hover 条目是 `(a : Nat) → (b : Boolean) → Boolean`（逐参数 + 空格），在 L13 是 `(a: Nat, b: Boolean) → Boolean`（折叠 + 无空格）[L13 侧有测试锚；L07 侧由 `raw_pretty.rs:170-187` 直读，属代码确定、无测试钉]。

### 4-B `raw_pretty` 高保留率下的两处静默漂移（E2）

`go` 体相似 0.683、且两侧都用"单缓冲 + 优先级常量"，看起来就是同一份。但：

1）`def_type_from_source` 被重写（fn-matrix 0.132）。L13 增加"独立参数分组折叠"+`mentions_group` 依赖判定（`src/L13_namespace/raw_pretty.rs:246-295`），输出 `(x: A, y: B) → C`；L07 仍是每组 `(x : A) → `（`raw_pretty.rs:170-187`）。**这是 71702814 加的、未回灌 L07**，也是 §4-A 里"面板文案"能对齐的唯一原因。
2）`pattern` 同名两物（0.010）：L07 直接 Rust Debug——
```rust
fn pattern(p: &Pattern) -> String {
    // 保守：模式只在 match 的臂里出现，类型注解里几乎不会有；给个形状即可。
    format!("{p:?}")
}
```
（`src/L07_sum_type/raw_pretty.rs:159-162`）；L13 是正经递归打印（`raw_pretty.rs:195-207`，`Con(n)(subs…)`）。若某个注解里真出现 `match`，L07 的 hover 会喷出 `Con("succ", [..])` 这类 Rust 调试文本。
⇒ 保留率 79%/84% 是**行级错觉**：`go` 这一层继承，上层两个入口一个重写、一个是占位实现。

### 4-C `pretty` 的两处"L13 相对其父 L12 的丢失"（E3）

L12（L13 的直系祖先）两份保护都在：`src/L12_canonical/pretty.rs:17` `const MAX_DEPTH: u32 = 1_024;`、`:81` `fn go(prec: i32, ns: List<String>, tm: &Tm, out: &mut String)`。L13 两样都没有：`pretty.rs:221` 是 `fn pretty_tm_indent(prec: i32, indent: usize, ns: List<SmolStr>, tm: &Tm) -> String`，全 `format!`。
所以 `pretty.rs` 的 34%/54% 保留率**不是**"L13 后来加了功能"，而是 L13 从一条**没吃到 P11/P3 加固**的分支长出来：L13 只在 `pretty_nat`（:499）局部迭代化了 Nat 链，其它深项裸递归。这条对"一脉相承"是负面证据，且**没有任何门禁会报警**（L13 无对应测试，L07 的 `tests.rs:1995` 也只测 L07）。

## 5 本角度评级

**一脉相承 = 中（偏弱的一侧）**。一句话：**契约（`LspSurface`/`SurfaceQuery`）是真同源——5 个同名函数体相似 1.000；但它的两个实现支柱已经分家：`pretty` 是 L13 单边重写且丢了 L12 已有的两项保护，`observe` 在 L13 顶层不存在（职责被拆进 elaboration.rs + surface.rs + 孪生），且两侧对同一程序的 hover 文案不相同。**

Top-3 差异：
1. **def-site hover 文案分叉**：L07 打源码文本（逐参数 `(a : Nat) → (b : Boolean) → …`，`L07 elaboration.rs:305-314`+`raw_pretty.rs:170-187`），L13 打值渲染折叠形态（`L13 elaboration.rs:1688-1695`；锚 `debug_test.rs:72-75`、`tests/hover_tests.rs:130-134`）— **E2**。
2. **`LspSurface` 三个字段语义不同**：`failed_decls` 有序 Vec vs HashSet 迭代序（`L07 surface.rs:40` / `L13 mod.rs:1508`+`surface.rs:134`）、`println_spans` 真串 vs 恒空（`L07 observe.rs:250` / `L13 surface.rs:143-148`）、`check_issues` 带 decl 下标 vs 裸行（`L07 surface.rs:38` / `L13 surface.rs:31`）— **E2**。
3. **`pretty` 核心单边重写且丢保护**：`format!` 树构建替换单缓冲增量写（L12 `pretty.rs:81` → L13 `pretty.rs:221`）、无 `MAX_DEPTH`（L12 `:17` 有 / L13 无）— **E3**。

## 6 给 Lead 的提醒（超出本角度）

1. **"L07 是上游"这个叙事在 git 上站不住**：`raw_pretty.rs` L07–L12 逐字节同（L07 vs L08 差 1 行、vs L12 差 2 行），`pretty/surface` 也只差十几行。真正的"共有祖先"更像 **L12**；L13 是唯一离群点。若各组按"L07→…→L13"叙述血缘，会被逐文件 diff 打脸。
2. **fn-matrix 在我这两个文件里有误配**：`pretty.rs go` 把 L07 的 178 行核心配到 L13 `:156`（31 行的 `mentions_outer_n` 辅助函数），`body_sim 0.040` 不可直接引用；L13 真正对应是 `pretty_tm_indent:221`（277 行）。同样 `surface.rs` 只覆盖自由函数，`impl Infer` 上的 `lsp_hover/set_surface_query/hover_wanted` 等（L13-only）完全没进矩阵 ⇒ surface.rs "5/5 全 ≥0.6" 是**低估**了差异，不是全部。
3. **L13 参考版与 L13 孪生在观察面上自己就不一致**：清表范围（`surface.rs:159-165` vs `bump_spine_iter/observe.rs:12-19`）、登记串复用是否 gate final（`L13 elaboration.rs:2879` vs 孪生 `observe.rs:63`）。孪生被"封印"（`80f7cbc1`）⇒ 这处分叉无门禁。【推断】若有人以孪生为 oracle 做 parity，会在泛型/struct 的 hover 上看到 `?N` 差异。
4. **反向证据（"L13 处处落后"这个叙事的例外）**：构造子 hover 记忆化上 L07 才是落后者（`L07 observe.rs:219-225` 无条件缓存，L12/L13 有 `no_metas` 门）。即"L07 加固、L13 落后"不是全局结论，逐机制方向不同。