# Typort 文档生成（`typort doc`）设计报告

> 目标：为 Typort（elaboration-zoo-lsp）增加一个类似 `cargo doc` / rustdoc 的功能，
> 从 `.typort` 源码生成可浏览的 API 文档站点。
>
> 状态：**P0 + P1 + P2 已落地**（分支 `task/docgen-design`，基线 `master@f4d5da8`），
> 并已为核心 prelude 补齐文档注释。
> 本文档同时是设计与落地记录；实现取舍见文末「13. 落地记录」。

---

## 13. 落地记录（P0 + P1）

### 13.1 交付物

| 文件 | 内容 |
|---|---|
| `src/doc/mod.rs` | `DocOptions` / `DocFormat` / `run` / `build_model` / 输入与输出目录解析 / `--open` |
| `src/doc/model.rs` | IR：`DocModel` / `DocItem` / `DocMember` / `DocImpl` / `DocPackage` / `ItemKind` / `SourceRef`（`serde::Serialize`） |
| `src/doc/collect.rs` | 采集：Backend 参考引擎 → `process_file` 逐文件 → `Cxt.decl` + 重解析 AST → IR |
| `src/doc/markup.rs` | `///` 抽取、HTML 转义、签名 linkify、Markdown 子集渲染 |
| `src/doc/render_html.rs` | item 页 + 索引页 + `search-index.js`；`assets/doc.css` / `doc.js`（`include_str!`） |
| `src/doc/render_json.rs` | `doc.json` |
| `tests/docgen_tests.rs` | 端到端（模型 + 站点）与 Markdown/抽取单测 |
| `src/bin/cli.rs` | `typort doc` 子命令（`-d`）：`[FILES]` / `--out` / `--format html,json` / `--no-prelude` / `--open` |
| `src/lib.rs` | `pub mod doc;` |

### 13.2 实测结果

对 `examples/typeclass_complex.typort` + `examples/hdl_ops.typort` + `examples/adder_proof.typort`（含 prelude）：

- **831 个 item**（def 681 / struct 83 / trait 29 / enum 29 / class 9），**签名缺失 0**（100% 覆盖）；
- 249 个 impl 块；挂到类型页的 inherent impls 125、trait impls 243；
- 0 warnings；`doc.json` 与 `index.html` 两次运行**逐字节一致**（确定性）；
- `--no-prelude` 时同一输入降为 34 个 item、1 个包（root）；
- `typort doc --help` 正常。

### 13.3 与设计的偏差（有意）

1. **合并入口用 `process_file`，不是 `on_change`。** 调研时以为 `on_change::<false>` 会把用户声明并入全局表；实测它只详细化一个临时克隆（不写 `cxt.decl`），真正合并的是 `elaborate` / `process_file`（`lib.rs:1992/2240`，写回在 `lib.rs:2088`）。已改用 `process_file`，并显式 `Backend::new_with_engine(_, Engine::Reference)` 固定参考引擎。
2. **`markup` 先独立实现，未重构 hover。** 设计原打算把 `hover_doc_text`/`render_doc_text` 抽成共享模块。为不触碰 LSP 热路径与 hover 回归面，P0 在 `src/doc/markup.rs` 自带一份抽取/归一化，语义对齐 hover；共享重构留到 P1。
3. **`--no-prelude` 只关页面，不关依赖。** 与设计一致：分析始终加载 prelude（否则用户签名引用无法解析），该开关只影响是否为 prelude 生成页面。
4. **trait impl 方法目前只显示方法名**（无签名）：`Cxt.decl` 不含 trait impl 方法，符合设计的已知缺口，`pretty_raw` / 旁表留到 P1。
5. **成员级文档、`//!` 包文档、Implementors 之外的源码链接**均按设计留到 P1。

### 13.4 观察到的语言侧现象（非本功能 bug）

- prelude/examples **没有任何 `///`**，因此实测 `docs non-null = 0`；文档注释功能首次有了消费方，建议同步在 `docs/syntax.md` §1 记录 `///` 约定。
- `UInt` / `Bool` 等 prelude 结构的签名会暴露内部字段（`name: Option [String], zz_expr: Expr`）——这是 prelude 里 struct 的真实定义，非渲染错误。
- 同一 trait 对同一类型出现重复 impl 条目时，页面会如实列出多条（来自源码中真实的多个 `impl`）。

### 13.5 P1 落地（已完成）

| 项 | 实现 |
|---|---|
| hover/doc 抽取共享 | 抽取逻辑收敛到 `doc::markup::extract_doc_prefix`；`Backend::hover_doc_text`（`lib.rs:673`）改为委托调用，行为逐字节不变（`tests/hover_tests.rs` 20 项 + `hover_stress` 全绿） |
| trait impl 方法签名 | `render_def_sig`（`collect.rs`）从 AST `Decl::Def` 渲染；实测 124/124 个 trait impl 方法都有签名（此前只有方法名） |
| 成员级文档 | enum 构造子 / struct 字段 / trait 方法 / impl 方法均抽取各自名 token 上方的 `///`；item 页新增 Members 区（只列有文档的成员） |
| inherent impl 去重 | 优先用 AST 的 `impl` 块（带 span/docs/签名），`Cxt.namespace` 只补 AST 未覆盖的类型；`UInt` 的 inherent impl 从 20 条虚高降到 10 条真实块 |
| `//!` 包文档 | `markup::extract_inner_doc` 读文件头部 `//!`；多文件同包拼接，渲染在索引页包标题下 |
| 覆盖率 | `DocModel.documented`；索引页与 CLI 摘要输出 `N/M documented (P%)` |
| 源码块 | 折叠为 `<details>` |
| raw 中缀修复 | `a + b` 的 `Obj(base, op)` 应用还原为源码中缀（此前会渲染成 `width.+ 1`） |

**P1 实测**：`examples/hdl_ops.typort` + `typeclass_complex.typort` 下 trait impl 方法签名覆盖 124/124；`def +^(that: UInt[width]): UInt[width + 1]` 渲染正确；`Describable` impl 方法显示 `def describe: String`。

### 13.6 P2 落地（已完成）

| 项 | 实现 |
|---|---|
| Markdown 子集扩展 | 新增引用块、水平线、表格、setext 标题（`markup.rs`）；**仍零新增依赖** |
| 源码浏览页 | 每个源文件生成 `src/<file>.html`，逐行锚点 `id="L{n}"`；item/member 的 `view source` 指向锚点（`render_html.rs`） |
| `--source-link <TEMPLATE>` | 外部模板，`{path}` / `{line}` 占位；设置后不再生成 `src/` 页面；builtin 路径去掉 `builtin:///` 前缀 |
| `--serve [PORT]` | 内置 `std::net` 静态服务器（loopback、无目录列表、拒绝 `..` 穿越），`0`/省略端口自动选空闲端口；实测 index/css/item 200、缺失 404、穿越 404 |
| 文档警告 | 未解析的 impl 类型（过滤掉泛型参数 `T` 与 `String`/`Unit` 等无页原语）、Markdown 死链（未生成的 `.html` 目标） |
| 覆盖率门禁 | `--deny-warnings`（有警告则非零退出）、`--min-coverage <PCT>`（覆盖率不足则非零退出） |

**未做（有意）**：增量再生成。`typort doc` 的成本主体是 prelude 详细化（进程级缓存已覆盖同进程多次调用），跨进程缓存 doc 模型省不下这部分；收益低而正确性风险高，故不做。

**P2 实测**：`--min-coverage 90` 对无文档输入返回 `Error: documentation coverage 14.7% is below --min-coverage 90.0%`；`--source-link 'https://example.com/{path}#L{line}'` 生成 `href="https://example.com/nat.typort#L11"`；`--serve` 探测通过；两次生成逐字节一致（含 `src/` 页）。

### 13.7 核心 prelude 文档注释（已完成）

- **15 个 core/data 文件**补齐 `//!` 模块文档 + 每个顶层 item 与 enum 构造子/trait 方法的 `///`：`op`(31) / `nat`(17) / `list`(14) / `bool`(12) / `eq`(9) / `show`(9) / `either`(5) / `result`(3) / `vec`(3) / `option`(2) / `order`(2) / `void`(2) / `string`(2) / `decidable`(1) / `nonempty`(1)，共 **113 个 item，覆盖率 100%**。
- **16 个 HDL prelude 文件**各加一行 `//!` 摘要，使 `builtin` 包概览完整。
- 实测：`Nat` 的 `zero`/`succ` 成员文档、`List` 模块文档、builtin 包 `//!` 拼接均正确渲染；prelude 详细化不受影响（767 items）。
- 仓库级覆盖率：`113/767 documented, 15%`（未文档化的主要是 HDL 的 ~650 个内部辅助项）。

### 13.8 下一步

若需完整 CommonMark，可引 `pulldown-cmark`（feature 门控 + wasm 体积核对）；否则当前子集已覆盖实际 doc 注释的常见写法。

---

## 0. 结论摘要

**可行性：高。** 仓库里已经存在文档生成所需的大部分零件，只是散落在 hover 路径上：

- 全局已类型化声明表 `Cxt.decl`（名称 → span/term/value/ty/vty/prim/`typ_pretty`），
  每个条目第 7 槽就是**声明处的签名渲染串**（`mod.rs:307`）。
- `pretty_sum_definition` 已能把 enum/struct/trait **连同成员列表**渲染成源码风格
  （`mod.rs:1418`），正是文档页面需要的形态。
- `///` 文档注释的抽取 + Markdown 归一化已实现（`lib.rs:672` / `lib.rs:719`），
  且跨文件、跨 prelude 可用（走 `document_map` + `document_id` 反查）。
- 无头分析管线已有成熟范例：`emit.rs` 用 `Backend` + 一个"捕获型 Client" + 逐文件
  `on_change::<false>` 完成整项目编译（`emit.rs:22/42/134`）。
- 项目配置 `Typort.toml` 已有源文件收集（`config.rs:150`）与产物目录
  （`config.rs:193`）。

**主要缺口（本设计要补的）：**

1. `ast_map` 声明了但**从未填充**（插入语句被注释，`lib.rs:1539`）——文档需要
   "item 的种类 / 顺序 / 成员 / impl 关系"，这些只在 AST 里，不在 `Cxt.decl` 里。
2. `///` 是**纯文本约定**，词法层不识别（`///x` 只是普通 `//` 行注释），AST 不携带文档；
   且全仓库 prelude/examples **零处使用** `///`（`grep` 计数 0）。文档生成必须能优雅处理
   "无文档"的绝大多数 item。
3. 无 Markdown→HTML 渲染器、无静态站点基础设施、无模板引擎（依赖极简）。
4. `class`（HDL module）没有现成的签名渲染器；trait impl 的方法签名在 `Cxt.decl` 里
   **取不到**（trait impl 的方法被包进 trait 记录值，而不是 `Type.method` 键）。
5. 签名串是"展示用"的、有损的（隐式参数可能被省略、名字可能非全限定），交叉引用需要
   "精确匹配 + 歧义跳过"的保守策略。

**建议路线：** 新增 `src/doc/` 模块 + `typort doc` 子命令，复用参考引擎
（`Infer`/`Cxt`，非 twin），分三期落地：

- **P0**：项目内 item 页面（签名 + 成员 + `///` 文档）+ 包分组 + JSON 输出 + 基础交叉链接。
- **P1**：搜索索引/UI、Implementations/Implementors、成员级文档、源码片段、`//!` 包文档、
  trait impl 方法签名改进。
- **P2**：源码浏览页、增量再生成、主题/样式、文档告警（坏链接）。

**不建议**照搬 rustdoc 的全部语义：Typort 是依赖类型 + 类型类 + 命名空间 + 宏 + HDL，
"item 可见性""crate 边界"等概念不存在，文档模型要按本语言重画。

---

## 1. 需求与范围

### 1.1 目标（做）

- 从 `.typort` 源文件生成**静态 HTML 站点**，可离线打开（`file://` 可用）。
- 每个顶层 item 一页：`def` / `enum` / `struct` / `trait` / `class`(module) / `impl`。
- 页面内容：签名、`///` 文档（Markdown 渲染）、成员列表（构造子/字段/trait 方法/impl 方法）、
  实现关系（inherent impls、trait impls / implementors）、源码位置。
- 支持整项目（`Typort.toml`）与显式文件列表两种输入。
- 交叉引用：签名/文档中的类型名可点击跳转。
- 提供机器可读的 JSON 模型（便于工具链、CI、后续文档站）。
- 确定性输出（同输入 → 字节一致，便于快照测试与 CI diff）。

### 1.2 非目标（暂不做）

- 不做 `rustdoc --test` 式的文档测试（Typort 无此约定）。
- 不做文档覆盖率强制门禁（可 P2 加统计）。
- 不改变语言语法（本设计只**记录** `///` 约定，不引入属性宏 / `#[doc]`）。
- 不改动 LSP 行为（仅把 hover 的文档抽取逻辑抽成共享函数，行为逐字节不变）。
- 不生成 PDF / man page。

---

## 2. 现状调研（关键事实，带位置）

### 2.1 声明模型

| 层面 | 类型 / 位置 | 内容 |
|---|---|---|
| 语法 AST | `Decl`（`parser/syntax.rs:291`） | `Package` / `Import` / `Def` / `Println` / `Enum{is_trait}` / `TraitDecl` / `ImplDecl{inherent,from_class}` / `Derive` / `Class{items,traits}` |
| 类体 item | `ClassItem`（`parser/syntax.rs:351`） | `Field` / `Method(Decl,bool)` / `Stmt` |
| 全局声明表 | `type Decl = FxHashMap<SmolStr,(Span,Rc<Tm>,Rc<Val>,Rc<Ty>,Rc<VTy>,Option<PrimFunc>,String)>`（`mod.rs:307`） | 槽 0 span、槽 1 term、槽 2 value、槽 3 ty、槽 4 vty、槽 5 prim、**槽 6 `typ_pretty`** |
| 每文件类型元数据 | `DeclTm`（`mod.rs:343`） | `Def{typ_pretty, body_pretty}` 等；仅顶层 def 有值，impl 方法是空壳 `TraitImpl{}` |
| 命名空间 | `Cxt.namespace: List<(Rc<Val>, HashSet<SmolStr>, SmolStr)>`（`cxt.rs:320`） | (类型值, 固有方法名集合, 类型名) —— 可枚举某类型的 inherent 方法名 |

**关键点：** `Cxt.decl` 能给出**签名**，但给不出**item 种类与成员归属**。
种类/成员/impl 关系必须来自 AST。`ast_map` 目前是空的（见 2.5）。

### 2.2 `///` 文档注释的现状

- 词法层：`//` 即行注释（`parser/lex.rs:268` 一带），`///` 就是普通注释，**AST 不记录**。
- 抽取：`Backend::hover_doc_text`（`lib.rs:672`）在源码文本里从声明名字 token 的 span 向上
  扫描连续的 `///` 行，剥掉 3 个斜杠 + 一个空格，返回原文。
- 归一化：`Backend::render_doc_text`（`lib.rs:719`）把原文变成 hover 友好的 Markdown：
  平衡代码围栏、标题降级（`#`→`####`）、行尾硬换行、空行折叠。
- 组装：`Backend::hover_def_block`（`lib.rs:600`）先给"签名/成员"代码块，再
  `\n\n` 追加文档。**这就是文档页面 item 正文的现成形态。**
- 现实：prelude + examples 中 `///` 出现次数为 **0**。文档生成必须把"无文档"当默认路径。

### 2.3 现成的渲染器

| 渲染器 | 位置 | 能力 |
|---|---|---|
| `pretty_tm(prec, ns, tm)` | `pretty.rs:190` | 任意 `Tm` 的源码风格渲染（用 `ns` 名字表解 de Bruijn） |
| `pretty_sum_definition(key, tm, decl)` | `mod.rs:1418` | `enum/struct/trait` 头 + 成员签名；struct 折叠为 `struct Point(x: Nat, y: Nat)`；trait 方法跳过 Self |
| `render_pi_signature` / `render_pi_member` | `mod.rs:1373` / `mod.rs:1305` | Pi 链 → `+(this: Self, that: T) → O` 形式（内部辅助） |
| `Backend::hover_def_block` | `lib.rs:600` | 完整 item 面板（签名 + 成员 + 文档） |

**没有** `class`/module 的渲染器；**没有** Raw（未详细化 AST）的源码风格渲染器
（`Raw` 的 `Display` 是调试风格，不能直接用）。

### 2.4 分析管线与复用面

- `Backend::on_change::<false>`（`lib.rs:1510`）逐文件分析：解析 → 逐 decl 详细化 →
  合并全局 `cxt.decl` → 记录 `file_symbols`（本文件新增的限定名集合，`lib.rs:2112`）→
  登记 `cxt.namespace`（inherent 方法，`lib.rs:2093`）→ 写 `document_map`/`document_id`。
- `Backend::load_prelude` / `load_prelude_impl`（`lib.rs:1113+`）：加载 31 个内置
  `.typort`（`PRELUDE_CORE`/`PRELUDE_HDL`/`PRELUDE_SHOW`，`mod.rs:3490/3509/3529`），
  并注册虚拟 URI `builtin:///xxx.typort` 到 `document_map`。
- `clone_prelude_state(include_hdl)`（`mod.rs:3762`）：返回 `(Infer, Cxt, macros)`，
  是参考引擎的进程级缓存，避免每次重放 prelude。
- `emit.rs` 的整项目模式（`emit.rs:134` `emit_design`）：`CapturingClient`（`emit.rs:42`）
  + `load_source_files`（`emit.rs:22`）+ 逐文件 `on_change`，最后从捕获的诊断里取产物。
  **`typort doc` 的骨架与之几乎同构，只是最后改读 `cxt.decl`/`document_map`。**
- 引擎选择：文档生成应固定用**参考引擎**。twin（`bump_spine_iter`）当前只服务
  per-file 观察面，跨文件数据面仍走参考路径（`lib.rs:212-244` 注释）。

### 2.5 现状缺口清单

1. **`ast_map` 从未填充**：`lib.rs:1539` 的 `ast_map.insert` 被注释掉；`backend_stats`
   仍会读它（`lib.rs:1063`），实际恒为 0。
2. **无 Markdown→HTML**：`Cargo.lock` 里没有 `pulldown-cmark`/`comrak`/模板引擎。
3. **`document_map` 里 prelude 是虚拟 URI**（`builtin:///...`），没有磁盘路径，
   源码链接/包归属需要特判。
4. **trait impl 方法签名缺失**：`impl Trait for T { def m ... }` 的方法不落
   `Cxt.decl`（它们构造 trait 记录值）；只有 inherent impl 落成 `Type.method`。
5. **`class`/module 无渲染器**：module 宏（`prelude/hdl/hdl-macros.typort`）展开为
   `Decl::Class`，端口/信号是 class item；需要新写。
6. **签名串有损**：隐式参数在 `typ_pretty` 里的呈现、名字是否限定，都不保证全限定。

---

## 3. 为什么不能直接照搬 rustdoc

| 维度 | Rust / rustdoc | Typort | 设计影响 |
|---|---|---|---|
| 可见性 | `pub`/私有，默认只文档化公开项 | **无可见性概念**，全局符号并集 | 默认全量文档化；无 `--document-private-items` 概念 |
| crate 边界 | crate/模块层级由 `mod` 定义 | `package` 是**声明期前缀**，文件可多次切换（`elaboration.rs:1746`） | 按"声明时生效的 package 前缀"分组，而非文件路径 |
| 类型系统 | 具体类型；泛型可显示 | 依赖类型，类型里有项（`Vec[A](len)`）；隐式参数 | 签名必须用 `pretty_tm` 的 de Bruijn 名字表，不能字符串拼接 |
| trait/impl | impl 块可枚举 | `Cxt.decl` 不含 trait impl 方法 | 必须收集全 AST 的 `ImplDecl` 建 impl 索引 |
| 宏 | `macro_rules` 不在文档里 | `module`/`when` 等宏**大规模生成** class item；span 指向宏规则源 | item 可能没有真实源码 span；文档/源码链接要降级 |
| 文档注释 | `///` 同时是属性可进 AST | `///` 是普通注释，**纯文本扫描** | 与 hover 共用抽取；成员级文档要按 token span 另扫 |
| HDL | — | module/端口/寄存器具一等地位 | 需要 class/module 页面与端口渲染（新写） |

结论：**文档模型（IR）自己设计，渲染器自建；只有"签名渲染串"复用现有 `pretty_*`。**

---

## 4. 总体架构

```
   .typort 源文件 / Typort.toml
            │
            ▼
 ┌──────────────────────────────────────────────┐
 │ collect 阶段（复用 Backend 参考引擎）          │
 │  1. load_prelude(+HDL)                        │
 │  2. 逐文件 on_change::<false> → 合并 cxt.decl  │
 │     file_symbols / cxt.namespace / document_map│
 │  3. parser_with_macros 重解析每文件 → AST      │
 │  4. AST × decl 表 × document_map → DocModel    │
 └──────────────────────────────────────────────┘
            │  DocModel (IR)
            ├──────────────► render_html  → target_typort/doc/*.html + assets
            ├──────────────► render_json  → doc.json
            └──────────────► render_md    → doc/*.md（可选）
```

分层原则：

- **collect 与 render 解耦**：模型是纯数据（owned String / usize 索引），不持有
  `Rc<Tm>`/`Rc<Val>`，渲染器不接触 elaborator 内部。这样 JSON/Markdown/HTML 共享一套模型，
  也便于快照测试。
- **只读不写分析状态**：doc 命令不改变 LSP 语义；对 `Backend` 的使用方式与 `emit` 相同。
- **文档抽取与 hover 共用一份实现**：把 `hover_doc_text`/`render_doc_text` 从 `lib.rs`
  抽到 `src/doc/markup.rs`（或 `src/doc_text.rs`），`Backend::hover_def_block` 改为调用它，
  保证 hover 与文档永不漂移（并有测试锁定）。

---

## 5. 详细设计

### 5.1 CLI 接口

在 `bin/cli.rs` 的 `Commands` 枚举（`cli.rs:198`）新增：

```rust
/// Generate API documentation for a project (like `cargo doc`).
#[command(visible_alias = "d")]
Doc {
    /// Source files (.typort); default: sources from Typort.toml
    files: Vec<String>,
    /// Output directory (default: <target>/doc from Typort.toml)
    #[arg(long, short)]
    out: Option<PathBuf>,
    /// Output format; repeatable: html, json, md
    #[arg(long, value_delimiter = ',', default_value = "html")]
    format: Vec<DocFormat>,
    /// Do not document the builtin prelude
    #[arg(long)]
    no_prelude: bool,
    /// Open index.html after generation
    #[arg(long)]
    open: bool,
    /// Only document this package (and its subpackages)
    #[arg(long, short)]
    package: Option<String>,
}
```

对齐命名：`--out`（cargo doc 用 `--target-dir`，但此处更直观）、`--open`、
`--no-prelude` ↔ `--no-deps`（语义相近：不包含依赖/prelude）。

输出目录默认 `<project.target_dir()>/doc`（`config.rs:193`，默认 `target_typort/doc`），
与 `build` 产物同域；`--out` 覆盖。

### 5.2 新模块布局

```
src/doc/
  mod.rs          // pub fn run(opts) -> Result<(), DocError>；编排 collect+render
  options.rs      // DocOptions/DocFormat（与 clap 解耦，便于测试/库内调用）
  collect.rs      // AST + Cxt.decl + document_map -> DocModel
  model.rs        // DocModel / DocItem / DocMember / DocImpl / SourceRef / ItemKind
  render_html.rs  // 模型 -> HTML 页面 + 索引页
  render_json.rs  // 模型 -> serde_json
  render_md.rs    // 可选：模型 -> Markdown
  markup.rs       // /// 抽取 + Markdown 归一化 + Markdown 子集 -> HTML
  search.rs       // 搜索索引构建
  assets/
    doc.css       // include_str!
    doc.js        // include_str!（搜索过滤/键盘导航，无框架）
```

`lib.rs` 增加 `pub mod doc;`。所有文件仅用 std + 现有依赖。

### 5.3 文档模型（IR）

```rust
// model.rs
pub enum ItemKind { Fn, Enum, Struct, Trait, Class, Package, Impl }

pub struct DocModel {
    pub project: ProjectInfo,          // name/version/root（来自 Typort.toml，可空）
    pub packages: Vec<DocPackage>,     // 按包路径排序
    pub items: Vec<DocItem>,           // 扁平表；渲染/搜索共用
    pub impls: Vec<DocImpl>,           // 全 AST 收集的 impl 块
    pub unresolved: Vec<String>,       // 签名缺失/无法定位等降级记录（供 --verbose/测试）
}

pub struct DocPackage {
    pub path: String,                  // "mylib.utils"；根包为 ""
    pub docs: Option<String>,          // P1: 来自 //! 或包首页
    pub items: Vec<usize>,             // 指向 model.items
    pub subpackages: Vec<usize>,
}

pub struct DocItem {
    pub kind: ItemKind,
    pub key: String,                   // 全限定名，如 "mylib.utils.foo"
    pub short: String,                 // "foo" / "Point"
    pub sig: Option<String>,           // 渲染好的签名（pretty_* / class renderer）
    pub docs: Option<String>,          // 原始 /// 文本（未归一化）
    pub members: Vec<DocMember>,
    pub source: Option<SourceRef>,
    pub inherent_impls: Vec<usize>,    // 指向 model.impls
    pub trait_impls: Vec<usize>,       // 别的类型为 self、trait=本 item
    pub is_trait: bool,
}

pub struct DocMember {
    pub kind: MemberKind,              // Ctor / Field / TraitMethod / ImplMethod
    pub name: String,
    pub sig: Option<String>,
    pub docs: Option<String>,
    pub source: Option<SourceRef>,
}

pub struct DocImpl {
    pub trait_key: Option<String>,     // None = inherent impl
    pub self_key: String,              // 被 impl 的类型
    pub trait_args: Vec<String>,       // 渲染后的 trait 实参（P1）
    pub methods: Vec<DocMember>,
    pub docs: Option<String>,
    pub source: Option<SourceRef>,
}

pub struct SourceRef { pub uri: String, pub path_id: u32, pub start: u32, pub end: u32 }
```

### 5.4 采集算法（`collect.rs`）

**步骤 A — 建立带状态的 Backend（与 `emit.rs` 同构）。**

```
let backend = Backend::new(DocClient::default());       // 捕获/静默 ClientLike
if !opts.no_prelude { backend.load_prelude(); }         // 内置 31 文件 + macros
for (uri, text) in sources {
    backend.on_change::<false>(TextDocumentItem { uri, text: &text, version: None });
}
```

`on_change::<false>` 会：合并全局 `cxt.decl`、写 `file_symbols`、登记 `cxt.namespace`、
把源码 Rope 放进 `document_map`。这正是文档所需的全部数据面。

**步骤 B — 重新解析每文件取 AST。**

`ast_map` 目前空（见 2.5），两条路：

- **B1（推荐，P0 采用）**：doc 命令自己调用 `parser_with_macros(&preprocess(text), path_id,
  &macros)` 重解析。宏表需按管线的真实顺序积累（prelude 宏先、然后按 `Typort.toml`
  的排序逐文件），这样 `module` 等宏展开结果与详细化时一致。解析成本相对详细化可以忽略
  （prelude 详细化是秒级，解析是毫秒级）。
- **B2**：恢复 `lib.rs:1539` 的 `ast_map.insert(uri, decls.clone())`。省一次解析，但需要
  在 `on_change` 里 clone AST，且会改变 LSP 常驻内存（每文件一份 AST）。**不建议为文档功能
  改动 LSP 热路径**；如走 B2，应作为独立可关闭的改动并测内存。

推荐 B1：文档功能自成一体，不改 LSP。

**步骤 C — 遍历 AST，维护 package 前缀。**

```rust
let mut prefix: Option<String> = None;
for d in &decls {
    match d {
        Decl::Package { path } => prefix = Some(join(path, ".")),   // 与 elaboration.rs:1746 语义一致
        Decl::Import { .. } | Decl::Println(_) => {}
        Decl::Def { name, .. } => push_item(ItemKind::Fn, qualify(&prefix, &name.data), d),
        Decl::Enum { is_trait: false, name, cases, .. } => push_enum_like(...),  // enum/struct
        Decl::Enum { is_trait: true, name, .. } | Decl::TraitDecl { name, .. } => push trait,
        Decl::Class { name, .. } => push class,
        Decl::ImplDecl { .. } => collect_impl(...),   // 不产生 item，进 impls 索引
        Decl::Derive { decl, .. } => collect_impl_like(...),  // 记录为派生 impl（P1 细化）
    }
}
```

注意：`prefix_decl_name`（`elaboration.rs:36`）是私有的前缀实现，且它对 case/method 名
**不加前缀**。doc 采集要复刻这个语义（或把它提升为 `pub(crate)` 复用，避免漂移）。
`Cxt.decl` 的键就是加过前缀的，故 `qualify(prefix, name)` 的正确性可用
`file_symbols`（`lib.rs:2112`）交叉校验。

**步骤 D — 逐 item 组装。**

1. **文档**：`markup::extract_doc_text(rope, name_span)`（从 `hover_doc_text` 抽出）。
   守卫 span 越界（宏生成项，参照 `lib.rs:680`）。
2. **签名**：
   - `Def` → `Cxt.decl[key].6`（`typ_pretty`）；缺失则 `pretty_tm(0, List::new(), tm)` 兜底。
   - `Enum/Struct/Trait` → `pretty_sum_definition(key, &tm, &decl)`（`mod.rs:1418`）。
     它返回 `Option`，`None` 时回退到 `Name : Type` 形态。
   - `Class` → **新写** `render_class`（见 5.5）。
   - 失败 → `sig = None`，记入 `unresolved`，页面显示"签名不可用"。
3. **成员**：
   - enum 构造子：`pretty_sum_definition` 已含成员行；但**成员级文档**需要按构造子名字
     token 的 span 另扫（AST `cases[i].0` 有 span）。签名可取 `Cxt.decl["Name.Case"]` /
     `["Name.Name.mk"]` 的 `typ_pretty`（struct/trait 构造子是双写键，见 `mod.rs:1547`）。
   - trait 方法：从 `Name.Name.mk` 的 Pi 链取（`pretty_sum_definition` 内部已做，
     `mod.rs:1496-1529`）。
   - inherent impl 方法：`Cxt.decl["Type.method"]` 直接有签名；也可用 `cxt.namespace`
     枚举方法名集合（`cxt.rs:320`）做交叉校验。
   - trait impl 方法：`Cxt.decl` **没有**；P0 从 AST `ImplDecl.methods` 取
     `Decl::Def{params,ret_type}`，用新增的 `pretty_raw`（源码风格）渲染；P1 改为
     在详细化时把每个 impl 方法的 pretty 签名写进一张旁表（改动 elaborator，需评估）。
4. **源码位置**：`Span.path_id` → 反查 `document_id` 找 uri（同 `hover_doc_text`
   的做法），保留 start/end 供"源码片段"与行号锚点。
5. **排序**：包按路径字典序，item 按 (`kind` 序, `key`)，成员按源码顺序。全部显式排序，
   杜绝 HashMap 迭代顺序导致输出不稳定。

**步骤 E — 交叉索引。**

- 遍历所有文件的 `ImplDecl` 建 `DocImpl`；按 `self_key` 挂到类型 item（inherent +
  trait impl），按 `trait_key` 挂到 trait item（implementors）。
- 类型 item 的 `self_key` 用 `ImplDecl.name`（`Raw`）渲染后的名字再解析回限定键
  （可以用 `pretty_raw` 得到短名，再在已知 item 键里做后缀匹配；匹配歧义则记入
  `unresolved`，不硬链）。

**步骤 F — prelude 处理。**

- 默认包含：prelude 文件解析后归入特殊包 `builtin`（或 `prelude`），页面上标注为内置。
- 它们的 `document_map` 是 `builtin:///xxx.typort`，源码链接降级为"内置源"。
- `--no-prelude` 只保留用户项目 item（对应 `load_prelude_skip_hdl` 不适合，因为 core
  prelude 是用户代码的依赖，跳过会导致很多签名引用未链接；故 `--no-prelude` 只影响
  **是否生成 prelude 的页面**，不影响分析依赖）。

### 5.5 `class` / module 渲染（新写）

`Decl::Class { name, params, items, traits }`。HDL 的 `module adder[w: Nat] { ... }`
经宏展开就是 class。渲染目标：

```
class adder[w: Nat] {
    input a: UInt[w]
    input b: UInt[w]
    output sum: UInt[w + 1]
}
```

实现要点：

- 头：`params` 用与 `pretty_sum_definition` 相同的 de Bruijn 名字表策略
  （`mod.rs:1443-1468` 的模式：先把所有参数名 fresh 化建完整 ns，再渲染每个显式参数的
  类型）。
- 成员：`ClassItem::Field(name, ty, value)` 渲染 `name: ty`（值/驱动作为可选注释）；
  `ClassItem::Method(Decl::Def{..}, is_static)` 按 def 渲染；`ClassItem::Stmt(_)` 跳过
  （HDL 语句，文档不展示）。
- 端口方向（input/output/inout/reg）在宏展开后如何呈现需要实测确认；P0 先原样展示
  field 名与类型，P1 再恢复方向标注（若 AST 里保留）。
- `traits`（class 的 `impl Trait`）显示为 `impl Trait for adder`。

> 风险：module 宏展开细节较绕（`hdl-macros.typort` 大段脚手架）。P0 可先只文档化
> class 的**字段与 def 方法**，不追求与源码逐字对应。

### 5.6 交叉引用（linkify）

- 建 `HashMap<String /*名*/, Option<String /*url*/>>`：同名多义 → `None`（跳链）。
  键集合 = 所有 item 的 `key` 与 `short`。
- 对 `sig`/成员签名做 **token 级**扫描：识别 `[A-Za-z_][A-Za-z0-9_]*` 以及点分链
  `A.B.C`；对每个候选：
  - 先按完整点分链查 `key`；
  - 再按最后一段查 `short`（唯一才链）；
  - 命中即替换为 `<a href="...">原文</a>`。
- **不链**：字符串字面量内部、已知的关键字（`def/enum/struct/trait/impl/class/let/match/
  case/Type/Self` 等）、数字、以及歧义名。
- HTML 转义必须先行：`& < > "` → 实体，再插入标签；否则签名里的 `<`（比较/泛型）会破页。
- 锚点：成员用 `id="method.<name>"` / `id="ctor.<name>"`，与 rustdoc 风格近似。

### 5.7 输出布局与静态资源

```
target_typort/doc/
  index.html                 # 项目/包索引 + 搜索框
  doc.css
  doc.js
  search-index.js            # window.TYPORT_SEARCH = [...]
  builtin/index.html         # prelude 包
  builtin/<key>.html
  mylib/index.html
  mylib/utils/index.html
  mylib/utils/foo.html
  mylib/Point.html
```

- **一页一 item**（rustdoc 风格），包页 = item 列表。这样链接最稳定。
- 文件名：item 短名 + 去歧义（同名跨包时用全限定路径，或加包前缀）。
- 资源内联 `include_str!`，不引 CDN，`file://` 可开。
- 搜索：`search-index.js` 写入 `{name, key, kind, url, doc_snippet}` 数组；`doc.js` 在
  索引页做客户端子串过滤 + 键盘上下选择。**无框架、无构建步骤。**

### 5.8 Markdown 渲染

P0 采用**自写子集渲染器**（`markup.rs`），与 `render_doc_text` 已支持的语法一致：

| 语法 | P0 | 说明 |
|---|---|---|
| 段落 | ✅ | 空行分隔 |
| ATX 标题 `#`..`######` | ✅ | 页面内 h2/h3，避免 h1 冲突 |
| 围栏代码 `` ``` `` / `~~~` | ✅ | 保留语言标签，代码块不转义内部结构（整体转义） |
| 行内代码 `` ` `` | ✅ | |
| 强调 `*x*` / `**x**` | ✅ | |
| 链接 `[t](u)` | ✅ | 站内相对/锚点原样，外链 `target=_blank rel=noopener` |
| 无序/有序列表 | ✅ | 单层 |
| 引用块、表格、脚注 | ❌（P1） | 不足时再引 `pulldown-cmark` |

- 保留原始 `docs` 文本在模型里；hover 继续用 `render_doc_text`（为小面板优化），
  文档页用 `markup::to_html`（为页面优化）。两者共享"围栏平衡/空白折叠"的底层函数。
- **P1 备选**：引入 `pulldown-cmark`（纯 Rust、依赖少）。需评估 wasm 产物体积
  （VS Code Web 版用 wasm 构建本库，见 `Cargo.toml` 注释与 CI）。

### 5.9 源码片段 / 源码链接

- **P0**：item 页附"Source"折叠块，从 `document_map` 按 span 截取声明原文
  （多行、去尾空白），代码块展示。不生成独立源码浏览器。
- **P1**：`--source-link <URL 模板>`，生成 `<a href="{url}/{file}#L{line}">`；
  或生成 `src/<file>.html` 带行号锚点（rustdoc 的做法）。需要文件路径映射：
  用户文件用磁盘路径，prelude 用 `builtin:///` 特判。

### 5.10 错误与降级

| 情形 | 行为 |
|---|---|
| 文件解析失败 | stderr 警告 + 跳过该文件的 item；退出码非 0（仅当**所有**文件失败时） |
| 某 decl 详细化失败 | 仍按 AST 生成 item，`sig=None`，标注"未通过类型检查" |
| `pretty_sum_definition` 返回 None | 回退 `Name : Type`，记 `unresolved` |
| 宏生成项 span 越界 | 不抽文档、不给源码位置，标"生成项" |
| impl 的 self/trait 名字无法解析 | 不建链接，记 `unresolved` |
| 同名跨包 | 页面文件名消歧；短名链接跳过 |

### 5.11 确定性与性能

- 全程不使用 HashMap 迭代顺序做输出顺序；所有列表显式 sort。
- 进程内只加载一次 prelude（`clone_prelude_state` 缓存，`mod.rs:3762`）。
- 解析 31 个 prelude 文件 + 用户文件一次；详细化一次。可接受的量级：
  prelude 详细化秒级（r13 prim 后约 4-5s），用户项目千行级亚秒。
- P2 增量：以文件 mtime/内容 hash 缓存模型分片；本期不做。

---

## 6. 依赖与构建影响

- **P0 不新增任何 crate 依赖**。使用 `clap`（已有）、`walkdir`（已有）、
  `config`、`Backend`。
- `Cargo.toml` 只加 `pub mod doc;`（`lib.rs`）与 `Doc` 子命令（`bin/cli.rs`），
  无 `[[bin]]` 变化。
- **wasm 兼容**：`src/doc/` 只用 std（`std::fs` 在 `wasm32-wasip1` 可用）。文档功能
  不在 LSP 热路径，WASM 版即使编进去也不会被调用。若 P1 引入 Markdown 依赖，需按
  目标 `cfg` 或 feature 隔离并核对 wasm 体积。
- MSRV 不变（`rust-toolchain.toml`，当前 1.87+/stable）。
- CI：`ci.yml` 目前只 build vscode/wasm；若加 doc 端到端测试，需在测试 job 里跑
  `cargo test docgen`（本仓库测试通过 `cargo test` 跑）。

---

## 7. 测试计划

| 测试 | 位置 | 断言 |
|---|---|---|
| 模型单元测试 | `tests/docgen_tests.rs` | 给定 fixture 源，`DocModel` 的 keys/kinds/members/docs 正确；无文档项 `docs=None` 不 panic |
| hover/doc 一致性 | 同上 | 对同一 item，doc 的签名片段 != null 且与 `Backend::hover_def_block` 的代码块内容一致（锁定共享实现不漂移） |
| 黄金 HTML 快照 | `tests/docgen_golden.rs` + `tests/fixtures/docgen/` | 固定输入 → 归一化（去时间戳）后逐字节比对 |
| 确定性 | 同上 | 连续生成两次，目录树逐字节一致 |
| JSON schema 冒烟 | 同上 | `doc.json` 可被 `serde_json` 解析；含预期字段 |
| CLI 端到端 | `tests/docgen_cli.rs` | `typort doc --out <tmp>` 后 `index.html`/`search-index.js` 存在；`--no-prelude` 不含 `builtin` 页 |
| 交叉链接 | 单元 | 唯一名可链、歧义名不链、`<`/`&` 正确转义 |
| Markdown 子集 | 单元 | 围栏未闭合被平衡、标题降级、行内代码不误解析 |
| 成员文档 | 单元 | enum case / trait method 上方的 `///` 归属到对应成员 |

**回归保护**：重构 `hover_doc_text`/`render_doc_text` 到共享模块时，
`tests/hover_tests.rs` + `tests/hover_stress.rs` 必须全绿且行为逐字节不变。

---

## 8. 实施分期

### P0 — MVP（建议 1 个里程碑）

1. `markup.rs`：抽取/重构 hover 的文档函数（行为不变 + 测试锁定）。
2. `model.rs` + `collect.rs`：Backend 管线、重解析、item/impl 采集、签名渲染
   （def/enum/struct/trait 复用现有；class 新写基础版）。
3. `render_html.rs` + 资源：item 页、包页、索引页、基础 linkify。
4. `render_json.rs`。
5. CLI `Doc` 子命令 + 项目配置接入。
6. 测试（模型、确定性、CLI、hover 一致性）。

**验收**：对 `examples/`（含 `examples/hdl/`）跑 `typort doc --out /tmp/ezdoc`，
生成的站点能打开、每个顶层 item 有页面、HDL module 有页面、JSON 可解析、两次运行字节一致。

### P1 — 可用性

- 搜索 UI（`search-index.js` + `doc.js`）。
- Implementations / Implementors 区块；`pretty_raw` 提升 trait impl 方法签名。
- 成员级 `///` 文档（enum case/struct field/trait method/impl method）。
- `//!` 包文档（新的文本扫描约定）。
- 源码片段块 + `--source-link`。
- 文档统计（覆盖率）输出。

### P2 — 打磨

- Markdown 渲染升级（`pulldown-cmark`，feature 门控 + wasm 体积核对）。
- 独立源码浏览页（带行号/高亮）。
- 增量再生成、`--serve` 本地预览。
- 坏链接/未解析名告警；`--document-private-items`（若未来引入可见性）。

---

## 9. 风险与对策

| 风险 | 等级 | 对策 |
|---|---|---|
| 签名串有损导致误链 | 中 | 只链"键或唯一短名"的精确匹配；歧义记 `unresolved` 不链 |
| `///` 全仓零使用 → 站点大面积无文档 | 中 | 无文档是正常路径；P1 提供覆盖率报告；本设计不改语言，但应在 `docs/syntax.md` §1 补 `///` 约定 |
| trait impl 方法签名缺失 | 中 | P0 用 `pretty_raw` 从 AST 渲染；P1 评估在 elaborator 侧落旁表 |
| class/module 宏展开形态复杂 | 中 | P0 只求字段/方法；实测展开后再补方向与端口语义 |
| `ast_map` 为空，重解析与详细化 AST 漂移 | 低 | 用同一 `parser_with_macros` + 同一宏表顺序；加测试比对 item 键集合与 `file_symbols` |
| prelude 详细化耗时 | 低 | 进程级缓存 + 单次加载；`--no-prelude` 只关页面（不关依赖） |
| 输出不确定（HashMap 顺序） | 低 | 全量显式排序 + 双跑字节比对测试 |
| 引入 Markdown 依赖影响 wasm 体积 | 低（P1 才涉及） | P0 零依赖；P1 用 feature/cfg 隔离并测体积 |
| 改动 hover 文档逻辑引入回归 | 中 | 重构后 `hover_tests`/`hover_stress` 全绿 + 契约测试 |

---

## 10. 验收标准（Verification Gates）

1. `cargo test` 全绿（含新增 docgen 套件），现有 hover/namespace/emit 套件不回归。
2. `typort doc` 对 `examples/` 生成站点，`index.html` 在 `file://` 下可导航。
3. 每个顶层 def/enum/struct/trait/class 都有页面；`impl` 出现在
   Implementations/Implementors 区块。
4. 无文档 item 不崩溃、不显示空壳；有 `///` 的 item 文案与源码一致（Markdown 渲染）。
5. `doc.json` 通过 JSON 解析且字段完整；同一输入两次生成逐字节一致。
6. `--no-prelude` / `--out` 行为符合预期；退出码对"全部文件解析失败"为非 0。
7. 不新增运行时依赖（P0）；`cargo build` 的 wasm 目标不受影响。

---

## 11. 开放问题（待决策）

1. **对默认输出目录**：`target_typort/doc`（与 built 产物同域，推荐）还是仓库根 `doc/`？
   是否在 `Typort.toml` 增加 `[doc]` 段（`out`/`format`/`no_prelude`）？
2. **文档注释语法**：是否正式支持 `//!`（包/文件级）与"成员上方 `///`"？
   建议支持并在 `docs/syntax.md` 记录（实现是文本扫描，成本低）。
3. **页面粒度**：一页一 item（推荐，rustdoc 风格）vs 一页一包（更少的文件）。
4. **实现页表达**：trait impl 的方法签名 P0 是否接受"来自 trait 声明 + 源码链接"
   的降级，还是一开始就做 `pretty_raw`？
5. **prelude 页面**：默认是否生成 `builtin` 包的大量页面（体积 vs 完整性）？
   建议默认生成但可用 `--no-prelude` 关闭。
6. **UI 语言**：站内固定文案用英文还是中英双语（仓库文档为中文，代码注释中英混排）？

---

## 12. 关键复用点索引

| 用途 | 位置 |
|---|---|
| 全局声明表（签名/成员） | `src/L13_namespace/mod.rs:307`（类型）、`cxt.rs:313-322`（`Cxt`） |
| 签名渲染 | `pretty.rs:190`（`pretty_tm`）、`mod.rs:1418`（`pretty_sum_definition`）、`mod.rs:1305/1373`（成员/Pi 签名） |
| 文档抽取/归一化 | `lib.rs:600`（`hover_def_block`）、`lib.rs:672`（`hover_doc_text`）、`lib.rs:719`（`render_doc_text`） |
| 分析管线 | `lib.rs:1113`（`load_prelude`）、`lib.rs:1510`（`on_change`）、`mod.rs:3762`（`clone_prelude_state`） |
| 无头整项目范例 | `emit.rs:22/42/134` |
| 符号归属 | `lib.rs:317`（`file_symbols`）、`lib.rs:2112`（写入）、`lib.rs:2115+`（namespace 登记） |
| package 前缀语义 | `elaboration.rs:1746`（应用）、`elaboration.rs:36`（`prefix_decl_name`） |
| prelude 清单/URI | `lib.rs:1138-1172`、`mod.rs:3490/3509/3529` |
| 项目配置 | `config.rs:120/150/193` |
| CLI 子命令 | `bin/cli.rs:198`（`Commands`）、`cli.rs:237`（`Emit` 范例） |
| 位置换算 | `lib.rs:3224`（`offset_to_position`）、`lib.rs:3241`（`position_to_offset`） |
| AST 类型 | `parser/syntax.rs:291`（`Decl`）、`parser/syntax.rs:351`（`ClassItem`） |
| 语言语法文档 | `docs/syntax.md`（§1 注释需补 `///`） |
