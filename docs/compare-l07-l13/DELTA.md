# L07–L13 章节间实现差异 · DELTA

> 用户问题：本项目原本"每一章 = 上一章 copy 再添加新特性"，但后来的优化尝试把链条搞乱了。
> 本报告逐对梳理 L07~L13 每个章节**除标题以外**的实现差异，并标出 copy-forward 断点。
>
> 核对时点：工作树 HEAD `0464150c`（分支 `bench/realistic-l07-l13`，2026-11-11，工作树干净）。
> 统计口径：`src/<Lxx>/` 下 `.rs` 的物理行（含空行/注释），测试数为静态 `#\[test\]` 计数（未执行）。
> **后续进展（2026-11-11/12）**：本报告 §4（L07→L08）与 §6（L08→L09）的"弱化"结论已转化为行动——L08 参考版以 L07 HEAD 重定基、L09 参考版回灌 L07 加固并补黑盒测试；方案、验收与性能 A/B 见 [BACKPORT-2026-11-11.md](BACKPORT-2026-11-11.md)。
> 数据源：`.deltawork/pairs/L07--L08`…`L12--L13.{diff,numstat.tsv,files.tsv,symbols.tsv}`、
> `.deltawork/inventory/*.tsv`、`.deltawork/presence-matrix.tsv`。原始数值可由这些文件复算。

## 0. 结论速览

**链条的性质不是"七次同构递增"，而是六类事件叠加（详见 §11.1）：再定基 ×3（L09 名字世界、L11 名字世界、L13 产品化）、滞后拷贝 ×1（L08 是 L07 旧快照）、双向补丁分叉 ×1（L10↔L11）、功能删除无替代、单边优化回填。下表按“相邻对”列出每次缝合的结果：**

| 相邻对 | 增量性质 | 代码净变化 | 文件增删 | 最重的非标题差异 | 链是否连续 |
|---|---|---|---:|---|---|
| L07 → L08 | 积类型语法糖层 + **滞后拷贝**（L08 是 L07 较早快照的副本） | rs 行 -1705；总 churn +3082/−5026 | 无增删 | 积类型本体是真增量且核心机零变体；但 L08 欠 L07 四类机制债：09-18 深值栈安全轮、10-11 月 P3/P5/P8/P10/P11 加固、decl 简化缓存、黑盒 v3 套件。反向 L08 孪生又领先 L07（常驻缓冲/name_map 修复） | 文件级连续，**机制级双向分叉** |
| L08 → L09 | **再定基（非 copy）**：换名字世界重写内核 | rs 行 -4015；churn +6868/−10911 | −4（struct_eq.rs、tests.rs、twin/struct_eq.rs、twin/prim.rs），+1（twin/debug.rs） | 名字世界 decl 表 → `Infer.global` 大下标哨兵；`struct_eq` 快路径整层删；**2018 行 lib 测试归零** | **不连续（设计性换基 + 测试断崖）** |
| L09 → L10 | 加 trait/typeclass | rs 行 +3251；churn +6981/−3731 | +2（typeclass.rs、twin/typeclass.rs），−1（twin/debug.rs） | 新增 trait/impl/outParam 语法与 `Synth` 求解器；**参考版 Val→Rc<Val> 全签名重构（改动量大于 trait 本身）**；删 L09 的 SpecSolve 可解集白名单（语义放宽）；孪生 machine +1587 中约 500 行是临时探针 | 功能面连续纯增量；文档/语义口径有偏差 |
| L10 → L11 | 加宏 + **再换基（回到 decl 表世界）** | rs 行 +2853；churn +7440/−4620 | +1（parser/macros.rs） | `macro_rules` 全部实现；名字世界从哨兵切回 `Val::Decl` 名字键 decl 表；cxt.rs +424 | **不连续（第二次换基）** |
| L11 → L12 | 回填/精化层 | rs 行 +84；churn +4054/−3900 | +1（canonical.rs），−1（twin/typeclass.rs） | 三件新机制（Val 级 trait 求解、`Call` 内联、canonical 搜索）＋ SmolStr 迁移；**嵌套覆盖精度回退、parser 括号修复丢失** | 不连续（语义/健壮性两处回退） |
| L12 → L13 | **产品化**（LSP/HDL 宿主）＋ 再定基（命名空间/原生 Nat） | rs 行 +39775；churn +48181/−8365 | +33，−1（twin/subst.rs） | 全限定命名空间 decl 键、原生 `Val::Nat`、prim 挂 decl 表、class 两阶段、`Call`/`OpCall`、终止检查、eval budget、观察面；单测从 35 → 612 | **不连续（最大断点：机制/测试/文档全线分叉）** |

**七条最重要的判断：**

1. **"A 章 = B 章 copy + 新特性"这个不变式只在 L10 上成立**（L10 在 L09 新基上加 trait，是唯一纯增量章）。L09、L13 是设计性再定基（README 都自认）；L08 是 L07 的滞后拷贝；L11 在加宏的同时把名字世界第二次换回 decl 表，并整体 Arc 化；L12 是回填/精化，同时带两处回退。
2. **测试连续性断在 L09**：L07/L08 各有 64/56 个 `tests.rs` 用例（2354/2018 行），L09 把 `tests.rs` 整文件删除且不再补 lib 测试（L09–L12 每层仅 10/25/33/35 个零星 `#\[test\]`），黑盒套件也从 L09 起消失（只剩 `lXX_fast_parity`）。L13 以 612 个用例回填，但其中 `legacy_tests.rs`（138 例）只回收了 L10–L12 内联用例中的 12 个；L07/L08 的 56–64 例族未回收（名字重合仅 1 个），其余 574 例是 HDL/prelude/LSP 新产品测试。
3. **精化载体在 L13 整体回退（最大语义断点）**：σ 显式替换（`Subst`/`VSub`/`frcs`/`SpecSolve`）只落在 L07–L12 参考版；L09–L12 里的 `update_cxt`/`refresh` 全部是注释/文档（代码命中 0），L13 两版才真正回到 `update_cxt`+refresh（代码命中 24：`cxt.rs:1327/1372`，`pattern_match.rs:591` 自注"L13 精化载体是 update_cxt，不是 σ/wrap_sub"），并删掉孪生 `bump_spine_iter/subst.rs`。L12 README 已自认"两条路线各一层代表"。
4. **健壮性加固不对称**：L07 加固轮的预算/守卫（如 `MATCH_CMP_BUDGET`）只存在于 L07/L08（11/9 处），L09–L13 为零；`PM_FUEL` 只在 L09–L12；`eval_budget` 只在 L13。同名问题在不同层的防护口径完全不同。
5. **同名机制在各层的实现载体不同**：trait 求解 L10–L11 走 `Val::to_typ` 归一到 `Typ`，L12 起改直接匹配 `Val`；值表示 L07–L09 以按值 `Val` 为主（L07/L08 各有 11/8 处 `Rc<Val>` 只是 11 月 Rc 值层回灌的局部），L10 起参考版大面积 `Rc<Val>`（L10 80、L11 105、L12 123、L13 266 处），L11/L12 用 `Arc` 别名而 L13 又换回 `std::rc::Rc`；名字世界在链上换了四次载体（NameState→BiMap+哨兵→NameState+轨迹→Rc<BiMap>+refresh）。
6. **解析器不是逐层演进的**：`parser/lex.rs` 在 L09→L12 之间**逐字节未变**（L09–L12 都是 407 行）；L11 的 parser/mod.rs（883→2408）不只有宏，还塞进了错误恢复、手写优先级解析、`SPINE_ESCAPE` 括号摊平与 HDL/Verilog 兼容 token；而 `SPINE_ESCAPE` 到 L12 整段消失、L13 又重新出现。L12→L13 表面 +3631 parser 行，其中 `parser/derive.rs` 1411 行是全新派生引擎。
7. **文档与实现脱节是常态**：每章 README 300–650 行，标题声称与实际实现有出入（L12 README 称 17 个 `#\[test\]`、实测 21；称孪生移植 6 个内建、实测 5 个；L13 README 称 341 个测试、实测 612，prelude 24 文件、实测 35；L09/L10/L11 的 README 互相把"决策树→逐臂"的改写归到自己头上，且行号大量指向重构前）。L07 README 645 行 vs L08 406 行（-37%）说明设计文档本身也在"缩水式 copy"。

## 1. 方法与口径

### 1.1 "标题"与"标题以外"的边界

本报告把**章节主题名及其纯标签性载体**视为"标题"，排除在"差异"之外：
- 每章 README 的 H1（"# L07：和类型与依赖模式匹配" 等）与主题段落措辞；
- 目录名/模块路径（`src/L07_sum_type/` → `src/L08_product_type/`）、层标签（`L07`/`L08`）、bench 名；
- 仅由上述标签导致的机械 diff（例如注释里把 L07 改成 L08）。

**但"标题宣称的增量"本身作为证据保留**，因为用户要判断"标题以外还有什么"：
每对报告 §"标题宣称的增量：声称 vs 实现" 会把 README 声称与代码逐条对照，
标出"一致/部分/未实现/另有出入"。

### 1.2 统计口径

- **行数**：`src/<层>/**/*.rs` 物理行（`\n` 计数 + 末行无换行补 1）；不含 `*.md`、不含 `.bak`（工作树当前无 `.bak`）。
- **churn**：`git diff --no-index --numstat` 的 `+/−` 行数（含 README 与文件增删）。
- **文件状态**：`added` 仅在该层存在、`removed` 仅在前一层存在、`changed` 两侧行数或内容不同、`unchanged` 逐字节相同。
- **测试数**：静态 `grep -c '#\[test\]'`，未执行；`tests/` 集成套件单独计。
- **锚点**：`src/L08_product_type/unification.rs:123`（仓库相对路径 + 当前工作树实测行号）。章内正文若只写
  `file.rs:LINE`，默认指**该对后一层（B）** 的同名文件；显式写了层名/全路径的以书写为准。
  无法核实的断言标 `[未核实]`，推断标 `[推断]`。

### 1.3 语义分类

每个"差异"归入六类之一（报告各节的 §3–§8 按此组织）：
- **A 语言面**：语法/解析/类型系统规则/内建/诊断/LSP 行为；
- **B 机制**：值表示、求值、force、quote、rename、unify、模式编译、精化载体、名字世界、trait 求解、canonical；
- **C 两版同步**：参考版与 `bump_spine_iter` 孪生的对位/分叉；
- **D 回退/丢失/弱化**：前层有、后层无（功能/机制/守卫/测试）；
- **E 性能与健壮性**：记忆化、预算、迭代化、栈安全、调试残留；
- **F 工程性**：命名、文件拆分、文档、格式、机械迁移（SmolStr 等）。

### 1.4 局限（先声明，免得误用）

- **纯静态分析**：不构建、不跑测试、不做性能实测；"语义丢失/弱化"类判断来自代码对照 + 层内测试方向，不等于实机行为回归。
- **历史只做交叉引用**：除 `.diff` 外，个别结论参考了 git log/commit（draft 内已标）；未审计 2026-09 之前的历史。
- **行号时效**：锚点是 2026-11-11 工作树；若之后重建章节（用户的既定计划），行号会漂移，方法不变。
- **L07 自身相对 L06 的增量**超出本任务范围（"L07~L13 之间"），只在 §3 给一句话状态，不展开。

### 1.5 小节编号约定

- 全报告级章节：§0–§3（总览/方法/标题核对）、§4–§9（六对增量；§9 又分 9.1 核心机、9.2 表层）、§10（跨层审计）、§11（综合判断）、附录 A–C。
- **§4–§10 每章内部沿用该单元草稿的编号**（§4–§9 为 0–11；§10 审计为 0–9）：章内"见 §2 表""§6 回退清单"指该章自己的小节（如 §5 章里的 §2 = 该章"标题宣称 vs 实现"），不是全报告 §2。跨章引用一律写"§10""§11""§9.1"这类全报告编号。

## 2. 总览矩阵

### 2.1 各层规模与形态

| 层 | rs 文件 | 物理行 | 参考版 | parser | 孪生 | 测试文件 | 形态 |
|---|---:|---:|---:|---:|---:|---:|---|
| L07_sum_type | 28 | 19135 | 6459 | 1041 | 9281 | 2354 | 参考版分文件 + 孪生 16 文件；tests.rs 内联 64 用例 |
| L08_product_type | 28 | 17430 | 5362 | 1081 | 8969 | 2018 | 同 L07（文件集合完全一致） |
| L09_mltt | 25 | 13415 | 4358 | 1308 | 7749 | 0 | 无 struct_eq/tests；孪生加 debug.rs |
| L10_typeclass | 26 | 16666 | 5631 | 1494 | 9541 | 0 | 加 typeclass.rs（两版各一份）；删孪生 debug.rs |
| L11_macro | 27 | 19519 | 7093 | 3408 | 9018 | 0 | 加 parser/macros.rs；parser 膨胀 +1914 |
| L12_canonical | 27 | 19603 | 6978 | 3609 | 9016 | 0 | 加 canonical.rs；删孪生 typeclass.rs |
| L13_namespace | 59 | 59378 | 17751 | 7240 | 19117 | 15270 | 产品层：+33 文件（派生/观察/终止/prelude 测试等）、+legacy_tests 5421 行 |

### 2.2 每对 churn、文件增删与分区变化

| 对 | numstat 文件数 | 新增 | 删除 | 改动 | 未变 | +行 | −行 | 净 churn | rs 净行 | 参考版 Δ | parser Δ | 孪生 Δ | 测试 Δ | README 行数 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| L07→L08 | 29 | 0 | 0 | 29 | 0 | 3082 | 5026 | −1944 | −1705 | −1097 | +40 | −312 | −336 | 645→406 |
| L08→L09 | 30 | 1 | 4 | 25 | 0 | 6868 | 10911 | −4043 | −4015 | −1004 | +227 | −1220 | −2018 | 406→378 |
| L09→L10 | 27 | 2 | 1 | 24 | 1 | 6981 | 3731 | +3250 | +3251 | +1273 | +186 | +1792 | 0 | 378→377 |
| L10→L11 | 27 | 1 | 0 | 26 | 1 | 7440 | 4620 | +2820 | +2853 | +1462 | +1914 | −523 | 0 | 377→344 |
| L11→L12 | 28 | 1 | 1 | 26 | 1 | 4054 | 3900 | +154 | +84 | −115 | +201 | −2 | 0 | 344→414 |
| L12→L13 | 60 | 33 | 1 | 26 | 1 | 48181 | 8365 | +39816 | +39775 | +10773 | +3631 | +10101 | +15270 | 414→455 |

口径注：新增/删除/改动/未变 = **`.rs` 文件**分类计数；numstat 文件数 = 改动 + 新增 + 删除 + README（README 计入"改动"）；"未变" = 与前层逐字节相同的 rs 文件（parser/lex.rs 或 syntax.rs）。"净 churn" = +行 −行（含 README/增删）；"rs 净行"只含 `.rs`（故与净 churn 的差 = README 行差 + 增删文件行数差）。

### 2.3 测试面（静态计数，未执行）

| 层 | lib `#\[test\]` | 本层集成套件（`tests/`） | `#\[ignore\]` | 备注 |
|---|---:|---|---:|---|
| L07 | 70（tests.rs 64 + parser 4 + unif 1 + twin entry 1） | l07_blackbox 49 / v2 53 / v3 47 / l07_fast_parity 27 | 0 | 黑盒套件最厚 |
| L08 | 60（tests.rs 56 + parser 4） | l08_blackbox 58 / v2 53 / l08_fast_parity 35 | 0 | 黑盒仍厚 |
| L09 | 10（mod.rs 7 + parser 3） | l09_fast_parity 29 | 0 | **tests.rs 整删，只留零星 inline** |
| L10 | 25（mod.rs 20 + parser 5） | l10_fast_parity 21 | 0 | 无黑盒套件 |
| L11 | 33（mod.rs 23 + parser 10） | l11_fast_parity 19 | 0 | 无黑盒套件 |
| L12 | 35（mod.rs 21 + parser 14） | l12_fast_parity 15 | 0 | 无黑盒套件 |
| L13 | 612（legacy_tests 138 + mod.rs 77 + 各 `*_tests`） | l13_fast_parity 15 + namespace 30 / hover 20 / completion 26 / macro_goto 9 / impl_goto 5 / round2 11 / twin_engine 28 等 | 9 | 产品层自建测试体系；`tests/` 全域 1366 个 `#\[test\]` |

### 2.4 机制标记矩阵（各层 `src/` 内 grep 原始计数，**含注释**；剔注释后的代码级计数见 §10 审计表；完整表见附录 A）

| 标记 | L07 | L08 | L09 | L10 | L11 | L12 | L13 | 读法 |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `struct Subst`（σ 载体） | 1 | 1 | 1 | 1 | 1 | 1 | **0** | σ 在 L13 消失 |
| `VSub` | 139 | 88 | 75 | 65 | 71 | 62 | **0** | 同上 |
| `frcs` | 42 | 28 | 35 | 31 | 30 | 32 | **0** | 同上 |
| `update_cxt`（旧载体） | 0 | 0 | 15 | 25 | 24 | 26 | 21 | L09 起旧载体与 σ 并存 |
| `pm_defs` | 14 | 11 | 2 | 1 | 2 | 2 | 1 | L09 起基本退役 |
| decl 哨兵 `1919810` | 0 | 0 | 16 | 18 | 1 | 1 | 0 | L09/L10 哨兵世界；L11 起换回 decl 表 |
| `Infer.global` | 0 | 0 | 6 | 7 | 2 | 2 | 1 | L09/L10 名字世界核心 |
| `Rc<Val>`（参考版） | 11 | 8 | 9 | **80** | 105 | 123 | 266 | L10 起值表示 Rc 化 |
| `Val::Prim` | 26 | 25 | 8 | 9 | 14 | 15 | **1** | L13 prim 挂 decl 表 |
| `Tm::Prim` | 31 | 26 | 18 | 20 | 36 | 32 | **1** | 同上 |
| `Val::Nat` | 0 | 0 | 0 | 0 | 0 | 0 | 78 | L13 原生 Nat |
| `MATCH_CMP_BUDGET` | 11 | 9 | 0 | 0 | 0 | 0 | 0 | 只 L07/L08 有该加固 |
| `PM_FUEL` | 0 | 0 | 4 | 8 | 7 | 7 | 0 | L09–L12 |
| `eval_budget` | 0 | 0 | 0 | 0 | 0 | 0 | 52 | 只 L13 |
| `Synth`（trait 求解） | 0 | 0 | 0 | 8 | 7 | 7 | 33 | L10 起 |
| `macro_rules` | 2 | 2 | 4 | 4 | 18 | 28 | 34 | L11 起真实现 |
| `canonical` | 0 | 0 | 0 | 0 | 0 | 16 | 6 | L12 引入 |
| `OpCall` | 0 | 0 | 0 | 0 | 0 | 0 | 41 | L13 引入 |
| `import_map` | 0 | 0 | 0 | 0 | 0 | 0 | 40 | L13 命名空间 |
| `blackbox/HdlEnum/IMasterSlave/fsmNew` | 5 | 3 | 0 | 0 | 1 | 1 | 136 | L13 产品面 |
| `prelude` | 0 | 0 | 0 | 0 | 1 | 32 | 711 | L12 起铺路、L13 消费 |
| `eprintln!` | 6 | 5 | 0 | 9 | 2 | 6 | 66 | 调试残留 |
| `panic!(` | 17 | 21 | 26 | 19 | 31 | 31 | 253 | panic 面 |
| `#\[test\]` | 70 | 60 | 10 | 25 | 33 | 35 | 612 | 与 §2.3 对应 |

### 2.5 文件谱系要点（完整 65 行矩阵见附录 B）

- **只在 L07/L08**：`struct_eq.rs`（374→188 行）、`tests.rs`（2355→2019）、孪生 `struct_eq.rs`、孪生 `prim.rs`（L07/L08）。
- **只在 L09**：孪生 `debug.rs`（395 行；L13 又有同名文件）。
- **L10 起**：`typeclass.rs`（参考版）；孪生 `typeclass.rs` 在 L10/L11 有、L12 无（并入 machine）、L13 又有（1031 行）。
- **L11 起**：`parser/macros.rs`（359→382 行）。
- **L12 起**：`canonical.rs`（155→149 行）。
- **L13 新增 33 个文件**：`parser/derive.rs`（1412）、孪生 `compact/observe/prim/termination/typeclass/debug`、17 个 `*_tests/probe`、`legacy_tests.rs`（5421）、`eval_budget.rs` 等。
- **L13 删除**：孪生 `bump_spine_iter/subst.rs`（σ 在孪生的最后痕迹）。

## 3. 标题宣称 vs 实现（七章一张表）

| 章 | 标题主题（README H1） | README 宣称的本章增量 | 实现核对结论 | 证据 |
|---|---|---|---|---|
| L07 | 和类型与依赖模式匹配 | enum 参数/索引/GADT、嵌套 match、覆盖性、卡住 match 参与类型检查/求值/合一；"按理论正向重构"，旧 `pm_defs` 改 σ | **范围外（本报告不展开 L06→L07）**：只确认 L07 是链的起点基线——28 文件、两版实现、新增 `pattern_match.rs`(851) 与 `struct_eq.rs`(374) 与内联 `tests.rs`(2354)、σ 与 `pm_defs` 并存（14 处）的过渡状态。L07 相对 L06 的增量不作为本任务结论 | §3 前注 / 附录 B |
| L08 | 积类型（product type / Sigma） | "核心机不新增任何 Tm/Val 变体"，struct 脱糖成单 `mk` 构造子 enum；只补接收者投影与一条 `unify (Obj,Obj)` 臂 | **增量一致、继承不一致**：核心机零变体为真、5 处脱糖/投影/合一实现都在；但 README §9"现行 L07 全量继承"为假——L07 的深值栈安全轮（quote_deep/EqTask/rename_deep/InlineStack）、P3 三档/ P5 跨 meta 环 / P8 宽松收窄 / P10 Error span / P11 quote+pretty 深值、decl 简化缓存 + MetaSnapshot undo-log 均未回灌（mod.rs −429、unification −381、struct_eq −186、tests −336 的来源） | §5 |
| L09 | MLTT 切片（Type N 分层宇宙 + 和类型/match） | "再定基层：以 MLTT 教学章为基底重写内核，非逐行继承 L08"；哨兵名字世界 | 一致且是**设计性换基**；但未说明测试面：`tests.rs` 整删（−2018 行）、黑盒套件不再有 L09 版本 | §6 |
| L10 | trait / typeclass 实例求解 | trait/impl、接收者方法、outParam、实例表 Prolog 求解；`Synth` 两版共用 | **基本一致但漏报两件大事**：参考版 Val→`Rc<Val>` 全签名重构（L09→L10 改动的相当比例是它而非 trait）；删掉 L09 的 `SpecSolve.solvable`+`bind_slots` 白名单（可解集=任意裸 Rigid，语义放宽）。另 README 称"L10 才把决策树改逐臂"与当前 L09 已是逐臂矛盾，`where`/实例依赖仍未实现（dependencies 恒空） | §7 |
| L11 | 宏（macro_rules）与 decl 表世界 | macro_rules 声明/表达式宏、可变全局 builtin；名字世界从哨兵换回 decl 表 | **一致但有反向失真**：宏/decl 表/Arc 化都属实；README 却把"匹配编译器五层第一个落地"算到自己头上（L10 已逐臂），且未提 parser 里宏以外的大量解析改动（错误恢复/手写优先级/`SPINE_ESCAPE`/Verilog 兼容 token）。另一个方向：L10 在 09-20/21 的补丁未回传 L11（bench_check、unsolved worklist、to_typ flat_map 语义），本对是双向分叉 | §8 |
| L12 | canonical 层（trait 求解 Val 级重写 + 宏 + canonical 搜索） | Val 级求解、`Val::Call`、canonical `iddfs/search`（Err 重试专属）、SmolStr | **部分不一致**：三件新机制属实；但"匹配编译器与 L10/L11 完全一致"不实（L12 把 L11 的 `PendingNode` 节点方程换成 `pending_pos` 两段式，导致合法程序回归）；README 测试数/内建数与实测不符 | §9 |
| L13 | 命名空间层（生产版：LSP / HDL 宿主） | 全限定 decl 键命名空间、原生 Nat、prim 挂 decl 表、SumCase 下标、`Call/OpCall`、class 两阶段、BindingName、replay、终止检查、观察面 | **宣称的增量都在，但"增量"实为整层再定基**：参考版核心三文件 +9298 行、孪生 +10101 行、+33 文件；两版同时删 σ 回到 `update_cxt`、孪生删 `subst.rs`、`Val::Match` 丢 origin；README 行号系统性过期（mod.rs:309→432 等）、测试数 341 vs 612、prelude 24 vs 35；生产代码 66 处 `eprintln!`、9 个 `#[ignore]` | §10 |

> 基线说明：**L07 是 L07–L13 区间的起点，本报告不审计它相对 L06 的增量**（那是另一段历史：L06 8→L07 28 个 rs 文件、+15k 行，新增和类型/依赖模式匹配/`struct_eq`/内联测试）。表中 L07 行只用于给出"标题口径"参照；真正的逐对结论从 L08 开始。

> 结论：**标题是可信的"设计意图"，但不是可信的"差异清单"**。七章里有四章的 README 存在"只讲新增、不讲删除/回退"的系统性偏差（L08/L09/L12/L13），这正是"优化尝试把链条搞乱"在文档面的投影。

## 4. L07 → L08：积类型（真增量）+ 滞后拷贝（L08 欠 L07 的机制债）

> 单元 delta-l07-l08 / 数据源 .deltawork/pairs/L07--L08.{diff,files,numstat,symbols}.tsv / 核对时点 HEAD 0464150c（工作树干净）
> 口径：行数 = .deltawork 物理行；churn = numstat；测试数 = grep 静态 `#[test]`；锚点行号已按当前工作树逐条 read/grep 核对。

### 0. 结论摘要

- **性质**：L08 不是 L07 的纯增量，而是「**滞后拷贝 + 积类型语法糖层**」。28 个 .rs 文件全部 changed、0 added/removed；rs 净 **−1705 行**（19135→17430），计入 README（645→406，−239）后全层 **−1944 行**；numstat churn +3082/−5026。
- **缩水主因不是删积类型功能，是 L07 侧整批机制未回灌**：L07 的 2026-09-18「深值栈安全轮」（quote/struct_eq/rename/val_mentions 迭代化 + InlineStack）、10-30~11-01 正确性批次（P3 三档 / P5 跨 meta 环 / P8 宽松合一收窄 / P10 Error span / P11 quote+pretty 深值）、以及 decl 简化缓存（ver 键）/MetaSnapshot undo-log 等性能内构，在 L08 全层 grep 均不可见。
- **L08 真增量**（两版同步）：`struct`/`new` 关键字与脱糖、左结合投影链、类型级 `.mk` 剥链（含依赖前字段精确实例化）、参考版 `unify` 的 `(Obj,Obj)` 合同臂、pretty 构造子去重、积类型专项测试 9+3 例、孪生 `struct_src` 负载。
- **声称核实**：「核心机不新增任何 Tm/Val 变体」为**真**（Tm/Val 枚举两版逐字一致，仅注释行移位）；「本次重构 = 现行 L07 全量继承」为**假**（L08 README 自己 §6 承认 P3/P10/P11/P5/P8 未迁，但漏报深值栈安全轮与 decl 缓存，二者合计才是缩水主项）。
- **链判断**：文件级连续（无删文件），**机制级断裂**：深值栈安全、三档诊断、span 诊断、decl 简化缓存四类回退；孪生侧另丢 SEqTask/InlineStack/PendingCons/RJob 深链任务/SIMPL_CACHE。反向地，L08 孪生独有「Machine 常驻工作缓冲 + name_map 同步」等先行优化（README §6 自称「L08 先行落地」）。
- **方向性提示**：L07 与 L08 是两条被分别优化的分支；本章对的「负 delta」应读作 **L08 欠 L07 的债**，而非 L08 对 L07 的删减设计。
- **底稿数字冲突**（报 Lead）：BRIEF §7 提示的「净 −2233」与 §2 表/底稿不符（实际 rs −1705，含 README −1944）；`.deltawork/pairs/summary.tsv` 的 `netLineDelta=2233` 也与 files/numstat 对不上，疑为旧快照/生成器口径问题。

### 1. 规模与文件级变化

28 个 .rs 全为 changed；README.md（第 29 个变更文件）被 files.tsv 排除，单独计。无文件新增/删除。

| 文件 | 状态 | A→B 行数 | churn +/- | 一句话性质 |
|---|---|---:|---:|---|
| mod.rs | changed | 2305→1876 | +230/−659 | 删 quote_deep/InlineStack/UnifyKind/Error span/MetaSnapshot/simpl 缓存；拆 eval/eval_ref；层名改名 |
| unification.rs | changed | 1327→946 | +162/−543 | 删 rename 深链收集器+三档注记+unify_no_arm；新增 (Obj,Obj) 臂；lift/skip 改按值 |
| struct_eq.rs | changed | 373→187 | +149/−335 | 迭代任务栈（EqTask）回退为递归 budget 版 |
| tests.rs | changed | 2354→2018 | +496/−832 | −20 个旧测试符号、+13 个（9 积类型+3 回归+1）；净 −336 |
| cxt.rs | changed | 504→453 | +26/−77 | Decls 结构体+ver 代数→裸类型别名；保留 Rc 条目 |
| elaboration.rs | changed | 757→804 | +134/−87 | 新增类型级 .mk 剥链；其余为 L07 perf 回灌 |
| parser/mod.rs | changed | 612→631 | +140/−121 | 新增 p_struct/p_new/投影链；删 ParseError 带 span 入口 |
| parser/lex.rs | changed | 311→332 | +22/−1 | 新增 StructKeyword/NewKeyword（关键字表 9 项） |
| pattern_match.rs | changed | 850→779 | +54/−125 | 删 IndexUnify/pat_span/三档集成 |
| pretty.rs | changed | 308→286 | +10/−32 | 删 MAX_DEPTH/DepthGuard；新增 .mk 去重 |
| parser/syntax.rs、syntax.rs | changed | 118→118、35→31 | 4/4、0/4 | 仅层名/常量改名（标题噪声） |
| bump_spine_iter.rs | changed | 145→138 | +46/−53 | 仅模块头注释与导览改名 |
| twin/machine.rs | changed | 2007→2092 | +319/−234 | 积类型 infer 臂 + name_map wrap/restore + 常驻缓冲导出 |
| twin/unify.rs | changed | 1040→1084 | +211/−167 | (Obj,Obj) 臂 + P2 预算 + P1 occurs；注释重排 |
| twin/struct_eq.rs | changed | 427→297 | +196/−326 | SEqTask 迭代栈回退为 *_go 递归 |
| twin/subst.rs | changed | 504→421 | +97/−180 | 删 InlineStack 与 SIMPL_CACHE；simpl_decl 无缓存 |
| twin/syntax.rs | changed | 307→253 | +18/−72 | pending cons 链→切片 |
| twin/rename.rs | changed | 923→837 | +76/−162 | 删 RJob 深链收集任务 |
| twin/force.rs | changed | 831→774 | +120/−177 | 卡住 match pending 头插→切片重拷；VSub→闭包草稿栈分支形状不同 |
| twin/entry.rs | changed | 417→367 | +13/−63 | 删内嵌 deep_value_tests；NO_NAME_MAP 迁入 |
| twin/quote.rs | changed | 673→665 | +17/−25 | 层名/pending 消费形态差异 |
| twin/prim.rs | changed | 357→369 | +26/−14 | builtin 注册形态微调（11-10 perf 回灌） |
| twin/spine.rs | changed | 210→198 | +4/−16 | 删 clear()（轮清改由 machine 直调） |
| twin/env.rs、compiler.rs、eval.rs | changed | +1、+3、−2 | 小 | 层名/常驻缓冲配套 |
| twin/bench_src.rs | changed | 118→150 | +34/−2 | 新增 L08 特色负载 struct_src |
| README.md | changed | 645→406 | +386/−625 | 删核心机复核章节，换成积类型文档；−239 |

**口径注**：files.tsv 的 oldSum/newSum = 19135/17430 → **净 −1705**；README 单独 −239 → 全层 −1944（= numstat 净额）。符号面：symAdded 85 / symRemoved 139。

### 2. 标题宣称的增量：声称 vs 实现

| README 声称（L08_product_type/README.md） | 实现锚点 | 判定 |
|---|---|---|
| 「核心机**不新增任何 Tm/Val 变体**」（:4-9） | Tm/Val 枚举两版逐字一致：L07 mod.rs:73/184 ↔ L08 mod.rs:73/189（仅注释行移位） | **一致**（事实） |
| `struct` 脱糖成单构造子 enum，构造子名 `{Name}.mk`（:36-43） | parser/mod.rs:546-569（p_struct 生成 `Decl::Enum{cases:[...mk...]}`） | 一致 |
| `new Name(e…)` ≡ `Name.mk e…`，可接投影链（:40-42） | parser/mod.rs:448-465（p_new 折叠 Raw::Var("{name}.mk") + App + Obj 后缀） | 一致 |
| L07 只允许单段投影，L08 扩左结合多段链（:88-94） | parser/mod.rs:254-260（`(kw(Dot), Ident).many0()` fold 成嵌套 Raw::Obj） | 一致 |
| 类型级投影：仅「单 case 且 case 名含 .mk」剥构造子类型链（:67-72） | elaboration.rs:526（`cases.len()==1 && cases[0].data.contains(".mk")`） | 一致；普通单 case enum 门控由该条件保证 |
| 显式字段 binder 以「接收者卡住投影值」实例化（:73-79） | elaboration.rs:549-557（`eval(Tm::Obj(接收者, bname))` 作为 Π 实参） | 一致 |
| 参考版 unify 新增 `(Obj,Obj)` 合同臂（:80-84） | unification.rs:802-805；孪生对位 bump_spine_iter/unify.rs:673-712 | 一致 |
| Pi 臂 quote 改用当前层级 l（修 L07 潜伏 lvl2ix 越界，:103-113） | unification.rs:662-675（注释逐字说明 cxt.lvl 破不变式） | 一致（L07 侧是否同修见 §6 注） |
| pretty 对 `{类型名}.mk` 去重（:96-101） | pretty.rs:185-194（`case_name.starts_with(&format!("{head}."))`） | 一致 |
| 「本次重构 = **现行 L07 全量继承** + §1–§4」（:316-320） | 反证：quote_deep/InlineStack/UnifyKind/Error span/MetaSnapshot/simpl 缓存/迭代 struct_eq/深链 rename 全缺（§6） | **未实现的声称**（README §6 只承认 P3/P10/P11/P5/P8 子集） |
| 「孪生侧机制**零新增**」（:118-119） | 实际孪生 machine +85：积类型 infer 臂、name_map wrap/restore、常驻缓冲导出、fuel_exhausted、unify_with 拆分 | 部分/表述过强（README 下文自己列 3 条） |
| 测试数：--lib 60 / blackbox 58 / v2 53 / fast_parity 静态 95（:292-314） | grep 实测：lib 60（tests.rs 56+parser 3+lex 1）、l08_blackbox 58(1 ignore)、v2 53(2 ignore)、l08_fast_parity 35 own+60 lib=95 | 一致（口径为 HEAD） |

### 3. 语言 / 语法 / 类型系统 / LSP 面增量

- **两个新关键字**：parser/lex.rs:10 `StructKeyword`、:12 `NewKeyword`；关键字表 :91-97（9 项，含 "struct"/"new"）；Display :55-56。
- **struct 声明**（按行分隔字段、参数单前导 `[..]` 隐式组）：parser/mod.rs:546-569 脱糖为单 case enum，字段全 `Icit::Expl`；空 struct → nullary mk。
- **new 构造**：parser/mod.rs:448-465；接入 p_raw 链 :473（`.or(p_new)`），故 `new P(a,b).x` 与嵌套 new 合法；裸 spine 实参位仍不接（p_arg 未动，README §7 限制不变）。
- **投影链**：parser/mod.rs:254-260；单段/无段行为不变。
- **类型级投影（唯一推理增量）**：elaboration.rs:519-562；参数槽优先，再 `.mk` 剥链；显式字段用卡住投影实例化（:549-557），依赖前字段字段类型精确化。
- **合一**：unification.rs:802-805 新 `(Obj,Obj)` 臂（字段名同 → 比接收者+spine）；孪生对位 bump_spine_iter/unify.rs:673-712。
- **显示**：pretty.rs:185-194；`Point.mk(...)` 不再打印成 `Point::Point.mk(...)`。
- **LSP/诊断面倒退**：L07 的 `Error(pub String, pub Option<Span>)`（mod.rs:553）、`Error::at/span`（:562/:567）、`parser_with_span`（parser/mod.rs:156）在 L08 不存在——L08 `Error(String)` 单字段（mod.rs:524），parse 入口 `Err(String)`（parser/mod.rs:111-137）。README §6 :229 自称「P10 Error span 未迁移」，属实且是 LSP 可观测回退。

### 4. 核心机制与实现性改动（A 怎么做 → B 怎么做）

| 子系统 | L07（A） | L08（B） | 动机/后果 |
|---|---|---|---|
| 值表示/核心枚举 | Val/Tm 同构 | 同构，零变体新增 | 积类型全部在 parser 脱糖，核心机无感（声称核实为真） |
| eval | `eval(&Tm)` 单函数（mod.rs:1347） | 拆 `eval(Tm)`+ `eval_ref(&Tm)`（mod.rs:1189/:1193） | [推断] 借用闭包体优化配套；L07 无同名函数 |
| quote | 深链分派 quote_deep 帧式收集器（mod.rs:1473/:1487） | 单函数递归 quote（mod.rs:1317-1425） | P11 未迁：10^5 层深值 quote 有爆栈风险（L07 README:376-390 已处理并回归钉） |
| 深值遍历基座 | `InlineStack` 内联小栈（mod.rs:1807；twin subst.rs:159） | 全层无此类型 | 随 09-18 深值轮一起缺席 |
| force | 有 `meta_expanding` 跨 meta 环守卫（mod.rs:624/:802） | 无该字段/分支 | P5 未迁：跨 meta 循环力有发散风险 |
| 合一失败分档 | `UnifyKind{Absurd,Undecided,Fuel}`（mod.rs:511-528）+ 21 处 note（unification.rs 多臂）+ pattern_match 集成（IndexUnify:118/:463） | 无 UnifyKind；stuck-match 失败仍按旧口径「分支不可达」（unification.rs:880-886 注释自认） | P3 未迁：诊断语义分层丢失 |
| 宽松合一 | `loose_string` 收窄到 bare heads（unification.rs:867，P8） | 仍按「名字是否在 decl 表登记」（unification.rs:592） | P8 未迁 |
| rename | Sum/SumCase/Obj 深链帧式收集器 rename_deep（unification.rs:360-370/:377-547）+ `unlift/lift_in_place` 就地 renaming | 直接递归 rename（unification.rs:298-411），lift/skip 按值返回（:58/:69） | 深值 rename 栈安全回退；代码反而更短 |
| 结构相等 | 迭代任务栈 EqTask/eq_run + InlineStack + 同址短路（struct_eq.rs:56/:64/:68-75） | 递归 `*_eq_go` + budget（struct_eq.rs:45/:111/:181） | 20k 预算内先爆栈风险（L07 注释 :10-18 说明） |
| 声明表 | `Decls` 结构体 + 实例代数 ver（cxt.rs:33-68）+ `simpl_decl_cached` 按 ver 缓存（mod.rs:1960） | `type Decls = FxHashMap<SmolStr, Rc<DeclEntry>>`（cxt.rs:24）；`simpl_decl` 每次全表重建（mod.rs:1524） | Rc 条目保留（370fb3f 成果），但 P1-2 缓存层缺失 → 卡住 match quote/rename/unify 反复 O(表) 重建 |
| meta 回滚 | undo-log：MetaSnapshot{undo_len,meta_len}+overwrite_meta（mod.rs:646/:673） | `meta_snapshot() -> Vec<MetaEntry>` 全量 clone（mod.rs:588/:592） | 回滚由 O(1) 轨迹降为 O(meta) 克隆 |
| parser 诊断 | `ParseError=(String,Option<Span>)`、span_of、parser_with_span（parser/mod.rs:139-156）；run 用 parser_with_span（mod.rs:1984） | `Err(String)` 契约（parser/mod.rs:111-137）；run 直接 parser（mod.rs:1547） | P10 未迁：解析错误位置信息丢失 |
| pretty | MAX_DEPTH=1024 + thread_local DEPTH + DepthGuard（pretty.rs:17/:19-29） | 无任何深度截断（pretty.rs:1-25 无相关项） | 深值打印可能爆栈/超长 |
| pattern_match | IndexUnify 区分 Kind/Msg（:118）；pat_span 带位置（:77） | 两者皆无 | 错误定位与三档联动丢失 |
| decl 写点 | [perf] 原地写/覆盖（L07 侧） | [perf] 原地写（同，见 cxt 注释） | 该项两版对齐 |

### 5. 参考版 ↔ 孪生版同步差异

> 结论：积类型特性两版同步；但「深值安全/缓存内构」是 L07 领先、「常驻缓冲/name_map 同步」是 L08 领先——两版是**各自被优化过的两条分支**，不是简单的一版先进。

- **积类型特性两版同步**：参考版 elaboration.rs:519-562 ↔ 孪生 machine.rs:1075-1126（逐句对应注释）；参考版 unification.rs:802 ↔ 孪生 unify.rs:673-712；parser/pretty 两版共用。README 声称「孪生侧 delta 仅 4 条」基本属实（:118-136）。
- **参考版独有**：`(Obj,Obj)` 合同臂在孪生侧「扁平 spine 头比较天然覆盖」，但 L08 仍补了显式统一臂（unify.rs:673-712），比 L07 孪生多。
- **孪生侧 L08 独有（领先 L07 孪生）**：Machine 常驻工作缓冲字段 `eval_work/quote_tasks/quote_work/unify_work/unify_stack`（machine.rs:148-156，构造 :179-184）；name_map 影子的 `wrap_names/restore_names`（machine.rs:224/:243，修 subst_cxt 后 name_map 不同步导致嵌套 match 丢外层精化）；`fuel_exhausted`（:211）；`unify_with` 拆分（:639）；独立 `subst_cxt`（:1878，L07 孪生为 `&mut self` 版 machine.rs:664）；`struct_src` 负载（bench_src.rs:120-150）。
- **孪生侧 L08 落后 L07 孪生**：SEqTask 迭代栈→`struct_*_eq_go` 递归（struct_eq.rs:42-52 对比 L07 同文件 :46-80）；pending cons 链→切片 `&[(V,Icit)]`（syntax.rs:245 对比 L07 :242-283）；`InlineStack`/`SIMPL_CACHE` 删除（L07 subst.rs:159/:456-500 → L08 subst.rs:409 无缓存）；RJob 深链收集任务删除（L07 rename.rs:257-273 的 ObjWrap/ObjSpineFold/SumBuild/SumCaseBuild 在 L08 rename.rs:241 的 RJob 中不存在）。
- **开关迁移**：`NO_NAME_MAP` 从 L07 孪生 machine.rs:2004 移到 L08 孪生 entry.rs:247（行为不变，属载体迁移）。

### 6. 回退 / 丢失 / 弱化清单

| A 中的功能/机制/守卫/测试 | B 状态 | 锚点 | 影响 |
|---|---|---|---|
| P11：quote 深链帧式收集器 + pretty 定深截断 | 缺席（quote 递归、pretty 无 MAX_DEPTH） | L07 mod.rs:1473/:1487、pretty.rs:17；L08 mod.rs:1317、pretty.rs:1-25 | 深值（succ^N 链）quote/打印栈溢出；L07 已有 10^5 层回归钉 |
| 深值栈安全轮（09-18）：IterativeEq / rename_deep / val_mentions 迭代 / InlineStack | 缺席（struct_eq、rename 回退递归；无 InlineStack） | L07 struct_eq.rs:56/:64、unification.rs:377、mod.rs:1807；L08 struct_eq.rs:45、unification.rs:298 | 深值结构比较/合一/遍历在默认栈下爆栈风险 |
| P3：UnifyKind 三档（Absurd/Undecided/Fuel） | 缺席；stuck-match 仍报旧「分支不可达」 | L07 mod.rs:511、pattern_match.rs:118、unification.rs:1233/:1242；L08 unification.rs:880-886 | 合法但判定不出的程序被误报为不可达；诊断分层丢失 |
| P5：force 跨 meta 环确定性守卫 | 缺席（无 meta_expanding） | L07 mod.rs:624/:802/:814 | 跨 meta 循环可能力发散/行为不确定 |
| P8：宽松 String 合一收窄到 bare heads | 缺席（旧判据） | L07 unification.rs:867；L08 unification.rs:592 | 宽 spine 的 String 合一仍可能误接受 |
| P10：Error 带 span / parser 带 span | 缺席（Error(String)、Err(String)） | L07 mod.rs:553/:1984、parser/mod.rs:131-156；L08 mod.rs:524、parser/mod.rs:111-137 | LSP/诊断定位能力回退 |
| P1-2：decl 简化表 ver 缓存 + MetaSnapshot undo-log | 缺席（simpl 每次重建、meta 快照全量 clone） | L07 cxt.rs:33-68、mod.rs:646/:1960；L08 cxt.rs:24、mod.rs:588/:1524 | 卡住 match 深链重求值成本上升（性能回退，语义不变） |
| 测试：P3/P5/P10/P11 回归钉共约 12 例 | 缺席 | L07 tests.rs:105/:282/:1913/:2141/:2301/:2325；twin entry.rs:364-377；unification.rs:1266 | 上述回退无回归保护，后续层无法察觉 |
| tests/l07_blackbox_v3（第三轮 47 例，2026-09-09 新增） | L08 无对应套件 | tests/l07_blackbox_v3.rs（git 7545ff06）；L08 仅有 blackbox/v2/fast_parity | 黑盒三轮用例族未随层复制 |
| 孪生简化缓存 / 深链任务 / pending cons / InlineStack | 缺席（见 §5） | L07 twin subst.rs:456-500、rename.rs:257-273、syntax.rs:242-283、struct_eq.rs:46-80；L08 对应处无 | 孪生性能/栈安全维度落后于 L07 孪生 |
| （核对补充）Pi η quote 层级修复 | **两版均在**（L07 已回灌） | L08 unification.rs:662-675；L07 unification.rs:935-950 | README §5「L07 已在连贯性评审回合」属实，不是差异项 |

### 7. 测试与文档变化

| 面 | L07 | L08 | 差异 |
|---|---|---|---|
| `--lib` 测试（grep `#[test]`） | **70**：tests.rs 64 + parser/mod 3 + lex 1 + twin entry 内嵌 1 + unification 内嵌 1 | **60**：tests.rs 56 + parser/mod 3 + lex 1 | **−10**；丢的 2 个内嵌测试 = entry.rs deep_value_tests（L07 twin entry.rs:364-377）、unification.rs deep_rename 收集器（L07 :1266） |
| tests.rs 用例族 | 64 | 56 | 新增 9 个 `test_product_*`（tests.rs:1371/1417/1467/1524/1562/1584/1613/1651/1698）+ 3 个 L08 回归（:1726 string_empty_and_escape / :1875 nested_pattern_refine_two_phase / :1906 absurd_nested_pattern）；删除 20 个符号（P 系列、subst、struct_eq、span、coverage 等） |
| `#[ignore]` | src 0 | src 0 | 同 |
| tests/ 黑盒族 | l07_blackbox 49(1 ignore)、v2 53(2)、**v3 47(1)**、fast_parity 27 | l08_blackbox 58(1)、v2 53(2)、fast_parity 35 | L08 blackbox = L07 49 + 9 product ✓；**v3 缺失**；parity +8 |
| README 结构 | 645 行：L07 核心机正向设计/模式编译/合一/旧实现对比/已知限制/测试/孪生/backlog | 406 行：积类型 §1-§5 + 孪生/已知偏差/测试/相对旧 L08 | **−239**：删去继承机制的复核章节（属文档分层选择），同时删去深值轮/三档/span 的同步披露 |
| README 失真点 | — | :316-320「现行 L07 全量继承」；:118-119「孪生机制零新增」 | 与实现不符（§2） |
| README 保留的诚实披露 | — | :229-254（P3/P10/P11/P5/P8 未迁、孪生镜像 P1/P2） | 属实，但未覆盖深值栈安全轮/decl 缓存/黑盒 v3 |

### 8. 工程性 / 性能 / 健壮性改动

- **L08 独有工程增量（孪生）**：Machine 常驻工作栈（machine.rs:148-156）替代每次 `&mut Vec::new()`；`clear_round` 补清 spine.stack（machine.rs:196-202 注释）；`decl_insert` 覆盖写免键重分配（machine.rs:1824-1832）；无参 def 零克隆（machine.rs:1410-1427 Cow 折叠）。README :132-136 称「L06/L07 孪生同款问题，本轮在 L08 先行落地」——核对属实（L07 孪生 machine 无这些字段）。
- **L08 独有健壮性修复（孪生）**：`wrap_names/restore_names`（machine.rs:219-247）在 subst_cxt 后同步 name_map 影子，修「嵌套 match 的 scrutinee 类型丢外层已解变量」；`fuel_exhausted`（:211）供诊断区分真冲突/预算耗尽。
- **回退型工程改动**：递归化（quote/struct_eq/rename）减少代码行但牺牲栈安全（§6 首两行）；删除 decl 简化缓存与 undo-log 增加深负载常数；删除 InlineStack/PendingCons 让热路径重新分配。
- **调试开关/命名**：`L07_DEBUG_ON`→`L08_DEBUG_ON`（L07 mod.rs:1978 ↔ L08 mod.rs:1542）；`L07_DEBUG`→`L08_DEBUG`；孪生 `L08_NO_NAME_MAP` 环境变量沿用 L06 名（L07/L08 README 均注为项目级约定）。eprintln 残留：L07 6 处 / L08 5 处（marker-matrix），非本章对重点。
- **基准新增**：bench_src.rs:120-150 `struct_src(k)`（4 层嵌套 Box + 2^(k+1) 浅值投影 def 链），README :216-225 说明刻意避深深值链，避免参考版 decl 写时复制 O(n³) 干扰双 oracle。
- **可疑/待核**：[未核实] L08 参考版拆 `eval`/`eval_ref` 的动机与收益（L07 无对应提交）；[未核实] 孪生 force 中 L07 的 VSub→闭包私有草稿栈分支（L07 twin force.rs:79-113）在 L08 是否等价迁移到 vapp1/force 内部（L08 force.rs:238-242 仅见总注释，未见同名 work2 分支）。

### 9. 标题噪声排除说明

- 纯改名类（已从「差异」中剔除）：`L07_`→`L08_` 前缀（模块名、调试开关、benchmark 文件名 l08_test_io/l08_builtin_demo）；`L07 sum-type 核心机` 注释→L08；DEMO_SRC 注释层名。
- 行数几乎中性的 `parser/syntax.rs`（118→118，churn 4/4）、`syntax.rs`（35→31）、`bump_spine_iter.rs`（−7 全为模块头注释/导览改名）即标题噪声本体。
- 章节 H1「# L08：积类型（product type / Sigma）」与 README 大量层名替换不计入实现差异。
- 注意：文件全部 changed 的观感很大程度来自「层名重命名 + 每文件重排/拆模块」，真正语义 diff 集中在 §3–§6 所列。

### 10. 证据锚点表（35 条，覆盖 §2–§8）

| # | 断言 | 锚点 |
|---|---|---|
| 1 | 核心枚举 Tm/Val 零新增，claim 为真 | src/L07_sum_type/mod.rs:73,184；src/L08_product_type/mod.rs:73,189 |
| 2 | struct 脱糖为单 mk 构造子 enum | src/L08_product_type/parser/mod.rs:546 |
| 3 | new 脱糖为 Name.mk 显式应用 + 投影链 | src/L08_product_type/parser/mod.rs:448 |
| 4 | 投影链左结合扩展 | src/L08_product_type/parser/mod.rs:254 |
| 5 | struct/new 关键字与关键字表 | src/L08_product_type/parser/lex.rs:10,91 |
| 6 | 类型级 .mk 剥链门控 | src/L08_product_type/elaboration.rs:526 |
| 7 | 依赖前字段精确实例化（卡住投影） | src/L08_product_type/elaboration.rs:549 |
| 8 | 参考版 (Obj,Obj) 合同臂 | src/L08_product_type/unification.rs:802 |
| 9 | 孪生 (Obj,Obj) 合同臂对位 | src/L08_product_type/bump_spine_iter/unify.rs:673 |
| 10 | pretty .mk 去重 | src/L08_product_type/pretty.rs:185 |
| 11 | L07 迭代 quote（P11）与深链分派 | src/L07_sum_type/mod.rs:1473,1487 |
| 12 | L08 quote 无深链收集器 | src/L08_product_type/mod.rs:1317 |
| 13 | L07 pretty 定深截断/守卫 | src/L07_sum_type/pretty.rs:17,23 |
| 14 | L07 迭代 struct_eq（EqTask/InlineStack） | src/L07_sum_type/struct_eq.rs:56,64 |
| 15 | L08 struct_eq 递归 + budget | src/L08_product_type/struct_eq.rs:45,111 |
| 16 | L07 rename 深链收集器与分派 | src/L07_sum_type/unification.rs:360,377 |
| 17 | L08 rename 直接递归、pren 按值 | src/L08_product_type/unification.rs:298 |
| 18 | P3 三档载体 UnifyKind | src/L07_sum_type/mod.rs:511 |
| 19 | P3 在 pattern_match 的集成（IndexUnify） | src/L07_sum_type/pattern_match.rs:118 |
| 20 | L08 自认未迁 P3、stuck-match 预算口径 | src/L08_product_type/unification.rs:880 |
| 21 | P5 跨 meta 环守卫载体 | src/L07_sum_type/mod.rs:624,802 |
| 22 | P8 loose_string 收窄（L07）vs 旧判据（L08） | src/L07_sum_type/unification.rs:867；src/L08_product_type/unification.rs:592 |
| 23 | P10 Error 带 span 与 parser_with_span | src/L07_sum_type/mod.rs:553,1984；src/L07_sum_type/parser/mod.rs:156 |
| 24 | L08 单字段 Error 与无 span parse | src/L08_product_type/mod.rs:524,1547；src/L08_product_type/parser/mod.rs:111 |
| 25 | Decls 结构体+ver 缓存 vs 类型别名 | src/L07_sum_type/cxt.rs:33；src/L08_product_type/cxt.rs:24 |
| 26 | simpl_decl_cached（L07）vs 无缓存（L08） | src/L07_sum_type/mod.rs:1960；src/L08_product_type/mod.rs:1524 |
| 27 | MetaSnapshot undo-log vs Vec 快照 | src/L07_sum_type/mod.rs:646；src/L08_product_type/mod.rs:588 |
| 28 | 孪生 name_map 同步 wrap/restore 与常驻缓冲 | src/L08_product_type/bump_spine_iter/machine.rs:224,148 |
| 29 | 孪生待迁移机制：SEqTask/PendingCons/SIMPL_CACHE/RJob | src/L07_sum_type/bump_spine_iter/struct_eq.rs:46；.../syntax.rs:242；.../subst.rs:456；.../rename.rs:257 |
| 30 | 测试面：lib 70→60、v3 套件缺失 | src/L07_sum_type/tests.rs:105,282,1913,2141；src/L08_product_type/tests.rs:1371,1726,1875,1906；tests/l07_blackbox_v3.rs |
| 31 | README 自认未迁项与「全量继承」矛盾 | src/L08_product_type/README.md:229,246,316 |
| 32 | 孪生 struct_src 负载与设计注记 | src/L08_product_type/bump_spine_iter/bench_src.rs:120 |
| 33 | 孪生 L07 RJob 深链任务删除 | src/L07_sum_type/bump_spine_iter/rename.rs:257；src/L08_product_type/bump_spine_iter/rename.rs:241 |
| 34 | L08 孪生 fuel_exhausted/unify_with/subst_cxt 载体 | src/L08_product_type/bump_spine_iter/machine.rs:211,639,1878 |
| 35 | Pi η quote 层级修复两版同码（非差异） | src/L07_sum_type/unification.rs:935-950；src/L08_product_type/unification.rs:662-675 |

### 11. 给 Lead 的一句话

> L07→L08 是滞后拷贝+积类型语法糖：语言面真增量两版同步，机制面欠 L07 深值安全/三档/span/缓存四笔债；BRIEF「−2233」与底稿「−1705（rs）/−1944（含 README）」不符，请统一口径后合并。

## 5. L08 → L09：再定基（MLTT 宇宙层 + 名字世界换哨兵）

> 单元 delta-l08-l09 ｜ 数据源 `.deltawork/pairs/L08--L09.*`（diff 22,321 行 / numstat / files / symbols）｜ 核对时点 HEAD 0464150c ｜ 只读分析（未 build/test）

### 0. 结论摘要（≤10 行）

- **性质：不是 copy-forward，是再定基（re-base）。** L09 README 自述「以 MLTT 教学章为基底重写内核，非逐行继承 L08 代码」（`src/L09_mltt/README.md:3-8`），代码核对一致：L08 的按名 decl 表世界被整体拆掉，换成「值表 + 大下标哨兵 + 局部名字表」的另一套名字世界。整层净 -4015 行（17430→13415）。
- 名字世界换载：L08 `Decls = FxHashMap<名, Rc<DeclEntry>>`、项层引用 `Tm::Decl(名)`、每个 eval/force/quote/unify 都带 `&Decls` 参数 → L09 无 decl 表：`Infer.global: HashMap<Lvl, VTy>` + `Infer.global_names` + 哨兵 `GLOBAL_BASE=1919810`，项层引用是 `Tm::Var(Ix(global_idx+1919810))`（`src/L09_mltt/mod.rs:442-472,501-528,793-801`；对照 `src/L08_product_type/cxt.rs:24,113`、`src/L08_product_type/mod.rs:650,1199`）。
- 语义回退：`Val::Match` 去掉 pending 实参槽，卡住 match 不能再被应用（`v_app` 直接 panic）。L08 有值层 splice，L09 只剩 README 登记的「时代缺口」（`src/L08_product_type/mod.rs:221-226,1154-1158` → `src/L09_mltt/mod.rs:192,715-731`）。
- 删 struct_eq 结构相等快路径（参考版 187 行 + 孪生 297 行）：Match/Match 合一改为「中性 global 视图下重求值」，且丢掉 L08 的 `MATCH_CMP_BUDGET=64` 总次数护栏（`src/L08_product_type/unification.rs:858-886`；`src/L09_mltt/unification.rs:695-756`）。
- 语言面缩减：L08 的 15 个 builtin（可变全局 / 文件 IO / str_eq / str_indent2 等）全删，L09 只剩 `string_concat`；`Val::Prim` 从「名字+spine」退化为无 spine 裸标记（`src/L08_product_type/cxt.rs:162-228`；`src/L09_mltt/cxt.rs:34-92`；`src/L09_mltt/mod.rs:859-868`）。
- 新增：`Type N` 分层宇宙（`Tm::U(u32)`/`Val::U(u32)`）+ `check_universe` + enum 的 `universe_lvl` 收集 + 构造子返回类型良构性 `check_ctor_wf`（`src/L09_mltt/mod.rs:70,178`；`src/L09_mltt/elaboration.rs:246,451-463,560-573`）。
- 载体迁移：模式特化方程从 L08 的 `pattern_match.rs` 内部挪到 `elaboration.rs` 的 `check_pm/unify_pm/spec_refine`；Cxt 从 NameState 轨迹表 + `Rc<Decls>` 换成 `src_names: BiMap` + `Rc<Locals>`（`src/L09_mltt/elaboration.rs:74,110,127,227`；`src/L09_mltt/cxt.rs:24-31,167`）。
- 测试：in-crate `tests.rs` 2018 行 / 56 个 `#[test]` 整文件删除；替代 = `tests/l09_fast_parity.rs` 29 个 parity 用例 + lib 10 个（README 声称 5，实际 10）。
- 链判断：文件级断 4 处、机制级断 3 处、测试断 1 处；L09 是从独立基底重接进链，L10–L13 在其上继续（L10 保留 `global_names` 形态，L13 才把 decl 表重新引入）。

### 1. 规模与文件级变化

口径：层总量取 `.deltawork/inventory/layers-summary.tsv`（物理行）；单文件 A→B 行取 `pairs/L08--L09.files.tsv`，churn 取 numstat（与 inventory 存在 ±1 末行差）。

| 口径 | L08 | L09 | 差 |
|---|---:|---:|---:|
| rs 文件数 | 28 | 25 | -3 |
| 合计行 | 17430 | 13415 | **-4015** |
| 参考版 | 5362 | 4358 | -1004 |
| parser | 1081 | 1308 | +227 |
| 性能孪生 | 8969 | 7749 | -1220 |
| 测试文件 | 2018 | 0 | -2018 |

numstat：+6868 / -10911（含 README 的 +363/-391，净 -4043；仅 rs 净 -4015）。改动性质 = **删多写少**：参考版 -1004 里 -2018 是删测试，其余靠删 decl 世界基础设施，同时 parser +227、elaboration +114 是新增能力。

**removed（4 文件，共 2871 行）**：

| 文件 | 行 | 内容 | 去向 |
|---|---:|---|---|
| `src/L08_product_type/struct_eq.rs` | 187 | 参考版结构相等快路径 `tm_eq/env_eq/val_eq` + `EQ_BUDGET=20_000` | 无替代，整体删除（全层 grep 仅剩注释） |
| `src/L08_product_type/bump_spine_iter/struct_eq.rs` | 297 | 孪生版结构相等（`struct_val_eq/struct_env_eq/struct_tm_eq`） | 同上，无替代 |
| `src/L08_product_type/bump_spine_iter/prim.rs` | 369 | `DeclEntryF`/`MutableMap`/`Fuel`/`UNIFY_FUEL`/`burn`/`lit_of`/`is_selfref_val`/`prim_reduce` | 燃料块搬 `force.rs`，`lit_of` 搬 `spine.rs:161`；decl 表接口与 prim 归约随世界删除而消失 |
| `src/L08_product_type/tests.rs` | 2018 | 56 个 in-crate `#[test]`（L07 全集 + 积类型十连 + builtin/globals/文件 IO） | 见 §7：29 parity + 10 lib；feature 删除族无对等替代 |

**added（1 文件，394 行）**：`src/L09_mltt/bump_spine_iter/debug.rs` —— 错误消息内嵌 `{:?}` 的 Debug 复刻（`debug_val`/`debug_tm` 等），服务 Err 正文 parity（`:1-3,45`）。L08 孪生全目录 grep `debug_val`/`fn dbg` 为 0，属净新增而非搬迁。

**主要 changed 文件**（只列语义相关，行数与 churn 见 files/numstat）：

| 文件 | A→B 行 | churn +/- | 一句话性质 |
|---|---:|---:|---|
| `mod.rs`（参考版） | 1876→1572 | +959/-1263 | 拆 decl 表世界，换 Infer.global/global_names/neutral/哨兵；删打印/bench/DEMO/测试模块 |
| `cxt.rs` | 453→219 | +126/-360 | 删 `Decls/DeclEntry/PrimFunc/NameState`；Cxt 只留局部 `src_names` + `Rc<Locals>` |
| `elaboration.rs` | 804→918 | +602/-488 | 新增 `check_universe`/`check_pm(_final)`/`unify_pm`/`spec_refine`/`check_ctor_wf`；删 `infer_owned`/`check_ty`/`ty_precheck` |
| `unification.rs` | 946→760 | +306/-492 | 全部函数去掉 `&Decls` 参数；SumCase 改比 typ+datas；删 `loose_string`/`REN_DEPTH` 调试护栏 |
| `pattern_match.rs` | 779→595 | +471/-655 | `Walk`/`matched`/`walk_con` 重写为 L07 口径 `walk_pat`，特化方程外移到 elaboration |
| `parser/mod.rs` + `parser/lex.rs` | 631→790 / 332→406 | +351/-192 / +105/-31 | 错误恢复（`recover_with`+`skip_until_decl`，返回 `Option<(Vec<Decl>, Vec<IError>)>`）；`Type`/`MacroIdent` token + `TokenKind: Display` |
| 孪生 `machine.rs` | 2092→2129 | +1210/-1173 | Machine 字段换 `globals/global_names/neutral`；`Names` 快照 + `fake_bind/define_name_in`；删 `name_map/name_trail` 轨迹与 decls 参数 |
| 孪生 `force.rs` | 774→531 | +252/-495 | 删 decl 展开/Prim 归约/投影再归约；收编燃料块为 thread-local `PM_FUEL`；frcs 保留显式替换 |
| 孪生 `unify.rs` | 1084→885 | +387/-586 | 删 Match 快路径/pending/预算；收编 `ConvScratch`/`ReclaimOnClear`；Match/Match 走中性视图 |
| 孪生 `quote.rs`/`rename.rs`/`compiler.rs` | 666→459 / 838→797 / 680→531 | -273 / -154 / -587 | 删 `simpl_decl` 空表分支；编译器改 `walk_pat` + `Warning` + `Compiler::new(ret_type)` |

### 2. README 宣称的增量：声称 vs 实现

| README 声称（L09） | 实现锚点 | 判定 |
|---|---|---|
| 「再定基，与 L06–L08 decl 表世界系统性不同，无名字键 decl 表」`:3-8` | `src/L09_mltt/mod.rs:442-472`（Infer 无 Decls）；`src/L08_product_type/cxt.rs:24`（A 有 Decls） | 一致 |
| `Type N` 分层宇宙 `Tm::U(u32)`/`Val::U(u32)`，pretty 同款 `:37-40` | `mod.rs:70,178`；`pretty.rs:153` | 一致 |
| 类型注解一律过 `check_universe`，未解 meta 两条解路径 `:40-44` | `elaboration.rs:246-294`（`pren.dom==0` 解 `U(0)`；否则 rename 造 `U(0)`） | 一致 |
| enum 收集 `universe_lvl`，本体类型是 `Type universe_lvl` 的 Π 链 `:45-48` | `elaboration.rs:451-463`（取 max）；`:496-498`（Π 链） | 一致 |
| 隐式参数域洞钉 `U(0)`（README 标 `elaboration.rs:429-450`）`:49-55` | `elaboration.rs:440-450` | 一致 |
| 构造子良构性 `check_ctor_wf` `:56-62` | `elaboration.rs:560-573`（enum 注册期调用 `:550`） | 一致 |
| 继承 L08 struct/new/投影；builtin 唯 `string_concat`，体是无名 `Tm::Prim`「README 标 mod.rs:742-752」`:63-67` | 脱糖 `parser/mod.rs:580-587,667-683`；`Tm::Prim` 求值在 `mod.rs:859-868`；注册在 `cxt.rs:43-65` | 一致，但 README 行号过期 |
| 名字登记两路：本名 `fake_bind` 占位（README 标 cxt.rs:111）`:87-91` | 实为 `Infer::fake_bind` `mod.rs:501-509`；`cxt.rs` 全文无 `fake_bind` | **README 锚点过期** |
| 「名字解析只走 `src_names`，一次查表覆盖局部+全局」`:100-105` | 实为两表：`src_names` 优先、`Infer.global_names` 回落（`elaboration.rs:638-644`；`pattern_match.rs:103-113`） | **README 与实现不符**（`global_names` 是 2026-09-20 修复后新增） |
| `v_app` 对卡住 match panic（README 标 mod.rs:641-657）`:111-118` | 实为 `mod.rs:715-731`（panic 在 `:729`） | 一致，锚点过期 |
| `UNIFY_FUEL=4096`（README 标 mod.rs:444-451）`:130-135` | 实为 `mod.rs:474-475`（字段 `:468-471`） | 一致，锚点过期 |
| 无 Match 重选 / decl 展开 / Prim 归约 / struct_eq 快路径 `:290-299` | `mod.rs:555-568`（force 只有 Flex+VSub 两臂）；grep `struct_eq` 全层仅注释（`bump_spine_iter.rs:82-83`） | 一致 |
| `tests/l09_fast_parity` 29 个 `#[test]` `:326-332` | 实测 29（`tests/l09_fast_parity.rs`） | 一致 |
| `cargo test --lib L09_mltt` 5 个（mod 2 / parser 2 / lex 1）`:360-364` | 实测 **10**：`mod.rs` 7（`test1/test2` + 5 个 2026-09-20 新增 `test_pm_*` 负例，`mod.rs:1192-1550`）+ `parser/mod.rs:700,774` + `parser/lex.rs:326` | **README 过期（漏 5 个负例）** |

### 3. 语言/语法/类型系统/内建/LSP 面增量

| 面 | L08 | L09 实现 | 锚点 |
|---|---|---|---|
| 宇宙 | `Tm::U`/`Val::U` 无层级（单一 U） | `Type N` 分层：`U(u32)`；pretty 输出 `Type {uni}` | `src/L08_product_type/mod.rs:82,198`；`src/L09_mltt/mod.rs:70,178`；`src/L09_mltt/pretty.rs:153` |
| 宇宙检查 | 无独立检查；类型注解走 `check_ty`/`ty_precheck` | `check_universe`：推断类型非 U 则定向报错；未解 meta 两解路径；应用于 `let` 域 / def 类型 / enum 参数 / 构造子域 | `src/L08_product_type/elaboration.rs:152,180`；`src/L09_mltt/elaboration.rs:246,321,394,505,545` |
| enum 宇宙层级 | 无（U 不分层） | 参数域 + 构造子字段域逐个 `check_universe` 取 max，本体 Π 链 cod 是 `U(universe_lvl)` | `src/L09_mltt/elaboration.rs:451-463,496-498` |
| 构造子良构性 | 无专门检查（L07 评审修复未回灌 L08） | `check_ctor_wf`：ret 必须是本 enum 的 Sum、隐式参数位必须是 telescope bare rigid | `src/L09_mltt/elaboration.rs:560-573` |
| 内建面 | 15 个 builtin：`string_concat/str_eq/str_indent2/string_to_global_type/create_global/change_mutable/get_global(_default)/file_*` 等 + `FILE_IO_LOCK` | 只剩 `string_concat`：Cxt::new 里一个 λ 链、体是无名 `Tm::Prim`；求值读 env 前两槽，全字面量则拼、否则卡 `Val::Prim` | `src/L08_product_type/cxt.rs:162-228`；`src/L09_mltt/cxt.rs:34-92`；`src/L09_mltt/mod.rs:859-868` |
| 可变全局 / 文件 IO | `mutable_map` + 文件读写 builtin | 全删（`MutableMap`/`PrimFunc`/`Prim{name,spine}` 一并消失） | `src/L08_product_type/mod.rs:538,959-1015,1538`；`src/L09_mltt/mod.rs:172-198` |
| struct/new 脱糖 | `{Name}.mk` 单构造子 enum + `new` 转限定构造子应用 | 原样继承（L09 从 L08 回搬的语言面） | `src/L08_product_type/parser/mod.rs:448,546`；`src/L09_mltt/parser/mod.rs:580-587,667-683` |
| parser 错误恢复 | 全量失败折叠成 `Err("parse error")`（契约被 blackbox 钉死） | 错误恢复：坏 decl 跳到下一个 decl 关键字并保留已解析前缀，返回 `Option<(Vec<Decl>, Vec<IError>)>` | `src/L08_product_type/parser/mod.rs:107-133`；`src/L09_mltt/parser/mod.rs:19,93,122,174,183-190` |
| 词法 | 无 `Type`/`MacroIdent`/后续层关键字（struct/new 有） | 增 `TypeKeyword`（`Type N` 用，`parser/mod.rs:330`）、`MacroIdent`（`$x`）与 `TokenKind: Display`；并**预置后续层关键字** `trait/impl/for/this/static/macro_rules`——parser 全层 0 引用（死 token 面，见 §9） | `src/L09_mltt/parser/lex.rs:10-20,46,58-97,124-129,223`；`src/L09_mltt/parser/mod.rs:330` |
| 错误载体 | `Error(String)`，无 span | `Error(pub Span<String>)`：错误带源码偏移（LSP 诊断友好） | `src/L08_product_type/mod.rs:524`；`src/L09_mltt/mod.rs:439` |
| 显示形态 | `.mk` 去重 + 实参空格连接 | comma 血统 `头::分支(…)`；`(unsolved match n)`；越哨兵 Var 显示 `recursive_N` | `src/L08_product_type/README.md:96-101`；`src/L09_mltt/pretty.rs:212-220,226-228,119` |
| LSP 面 | — | 本层无新增 LSP 特性；增量只在错误 span 与 parser 前缀恢复（为后续层 goto/hover 留接口） | `src/L09_mltt/mod.rs:439`；`src/L09_mltt/parser/mod.rs:174` |

### 4. 核心机制与实现性改动

#### 4.1 名字世界换载（本对最大改动）

| 维度 | L08（decl 表世界） | L09（值表 + 哨兵世界） |
|---|---|---|
| 全局存储 | `Decls = FxHashMap<SmolStr, Rc<DeclEntry>>`；`DeclEntry{ty,val,prim,eta,prim_names}`（`cxt.rs:24,36-45`） | `Infer.global: FxHashMap<Lvl, VTy>`（键=global_idx，只存值）+ `Infer.global_names: FxHashMap<String,(Lvl,Rc<VTy>)>`（名字→层级/类型，append-only）（`mod.rs:444,455`） |
| 项层引用 | `Tm::Decl(SmolStr)` 按名查表（`mod.rs:76`） | `Tm::Var(Ix(idx+1919810))` 大下标；`lvl2ix` 边界必须 `>=`（`mod.rs:398-408`） |
| 求值 | `eval Tm::Decl` 查 decl 得缓存 WHNF（`mod.rs:1199-1200`）；force 有 Decl 展开臂（`mod.rs:690-713`） | `eval Var` 越哨兵查 `global`，`neutral_globals` 置位时返回中性 rigid（`mod.rs:793-801`） |
| 递归 def | `decl_insert` 先占位后覆盖（写时复制，`cxt.rs:322`） | `fake_bind` 占名（global_names + 局部影子）→ global 先插自身 rigid → 体检查 → `define_global` 覆盖（`mod.rs:497-528`） |
| 名字解析 | `names: Rc<RefCell<NameState>>` 轨迹表 + `name_mark`（`cxt.rs:62-114`） | `src_names: BiMap<String,Lvl,Rc<VTy>>` 只装局部，顶层回落 `Infer.global_names`；`subst_cxt` 重建表（`cxt.rs:24-31,167-183`） |
| 函数签名 | `force(decl:&Decls)`/`quote(decl,…)`/`eval(decl,…)`/`unify(decl,…)` 全线带 decl（`mod.rs:650,1317,1189`；`unification.rs:609`） | 全部去掉 decl 参数，只吃 `&self`/`cxt`（`mod.rs:554-568`；`unification.rs:542`） |
| 孪生 | `Machine.name_map + name_trail` 可变表 + `wrap_names/restore_names/name_mark/unwind_names`（`machine.rs:134,136,224,243,365,370`）；`decls:&FxHashMap<String,DeclEntryF>` 穿参（`machine.rs:445,718,929`） | `Machine.globals/global_names/neutral`（`machine.rs:68,75,81`）+ Cxt 的 `Names` 快照（`machine.rs:40-47`）；`fake_bind:263`、`define_name_in:279`；eval 查 `globals[i-GLOBAL_BASE]`（`eval.rs:193-197,304-306`） |

动机/后果：① decl 表按名取值意味着「定义顺序无关」与按名 unfold，L09 改为终值表后**值层没有 unfold 算子**，L08 fuel 的六烧点里 decl 展开/Prim 归约/pm_defs 三族在本层无宿主（README `:288-310` 自述，代码相符）；② 名字表从 Cxt 搬 `Infer`（2026-09-20 修复，`mod.rs:445-455`）把每声明整表克隆的 O(D²) 降为 O(D)，孪生镜像 `global_names/neutral`（`machine.rs:69-81`）。

#### 4.2 卡住 match 的 pending splice：L08 有，L09 删

- L08：`Val::Match(sc, env, cases, pending)`，卡住期间累积应用实参；`v_app` 把 `(u,i)` push 进 pending，选臂后在值层逐个应用（`src/L08_product_type/mod.rs:217-226,1136-1158`）。孪生 `XCell::Match{pending}` + unify 的 pending 逐对比较 + Match-vs-other η 臂（`src/L08_product_type/bump_spine_iter/unify.rs:985-1070`）。
- L09：`Val::Match(scrutinee, env, arms)` 无 pending；`v_app` 落到兜底 panic（`src/L09_mltt/mod.rs:192,715-731`）。补偿只有两处：`v_applicable` 守卫使 η 臂不再 panic 而是 Err（`mod.rs:326-331`；`unification.rs:644-657`）；`frcs` 对 Match 只推进 scrutinee、捕获 env 只包裹（`mod.rs:656-663`）。孪生同步删 pending（A 侧 `force.rs:216` 的 val_mentions_lvl 扫 pending，B 侧 `force.rs:69` 不再扫；`subst.rs:232` 同）。
- 后果：合法源码（打印递归卡住 match 的函数值）可触发 panic，参考版与快版同崩——README `:290-294` 把它登记为时代缺口而非缺陷。这是相对 L08 的**能力回退**（L07 起已有的机制在 L09 丢失）。

#### 4.3 struct_eq 删除与 Match/Match 新比较口径

| 项 | L08 | L09 |
|---|---|---|
| 结构相等模块 | 参考版 `struct_eq.rs`（`EQ_BUDGET=20_000`，不 force 不展开）；孪生同构 | 无模块、无替代（全层 grep 只剩注释） |
| Match/Match | 先 `struct_eq` 快路径短路；失效后 `burn_match_cmp_budget()`（每顶层 64 次）→ 用 `simpl_decl` 简化表 eval 分支体再 unify；事后比 pending | scrutinee 合一 → 分支体在**中性 global 视图**下 `eval_neutral` 重求值再 unify；无快路径、无次数预算 |
| 依据 | `src/L08_product_type/unification.rs:858-886`；`mod.rs:554`；`simpl_decl:1524`；孪生 `unify.rs:985-1019` | `src/L09_mltt/unification.rs:695-756`；孪生 `unify.rs:854-880` + `Machine.neutral:81` |

判断：L08 注释明确写「逐分支重求值会把递归函数分支体再展开一层卡住 match，fresh rigid 层级递增永不收敛，必须短路」；L09 用中性 global 视图消解递归展开根源（`unification.rs:731-734`），机制上自洽。但 L08 的**总次数预算护栏**（预算耗尽按不可判定失败）没有对应物，深层嵌套 match 下成本是否有界只靠结构深度，属 [推断] 性能风险。

#### 4.4 模式特化方程与 Cxt 载体迁移

- L08：特化完全在 `pattern_match.rs` 内（`walk_con` 末尾把精化写进 `self.sub`；`Compiler::new()` 无返回类型参数；`elaboration.rs` 无 `check_pm`——grep 0 命中）。
- L09：方程搬到 elaborator：`check_pm_final`(`:74`)/`check_pm`(`:110`)/`unify_pm`(`:127`)/`spec_refine`(`:227`) 解两条方程并返回 `Rc<Subst>`；编译器只 `Compiler::new(ret_type)` + `walk_pat`（`pattern_match.rs:60,190,448`），`compile` 内结算每层 Con 的特化方程。
- Cxt：L08 `NameState`（单表 + 撤销轨迹 + mark，O(1) 插入，`cxt.rs:62-98`）+ `decl: Rc<Decls>` 字段；L09 `src_names: BiMap` 快照克隆 + `Rc<Locals>`，`subst_cxt` 逐条重建包裹表（`cxt.rs:24-31,154-183`）。语义等价（持久化视图），实现取舍从轨迹回退换成小表克隆。

#### 4.5 unify 语义与守卫变化

| 变化 | L08 | L09 | 影响 |
|---|---|---|---|
| SumCase/SumCase | 只比 datas + 比 Sum 头名（避免 typ 内的索引槽深递归）（`unification.rs:820-855`） | 比 typ + datas（`unification.rs:678-694`；孪生 `unify.rs:828-853`） | 更强判定，但把 L08 刻意回避的 typ 深递归放回比较面 |
| Match vs 其它（η） | 接受严格 eta（全通配臂 + 体为 scrutinee 本身）（`unification.rs:916-942`） | 无该臂，落 `_ => Err` | 保守化：更少误判，也更少可证等式 |
| LiteralType 宽松 | `loose_string`：未登记名放行、已登记名按登记类型把关（`unification.rs:592-607`） | 无条件 `(LiteralType, Prim)` 互认（`unification.rs:662-664`） | 登记表消失后该守卫无宿主；L08「registered prim 不能宽松当 String」语义不再存在 |
| occurs | 事后 `occurs_transitive`（工作栈 + BUDGET 2048，`mod.rs:344-346`；孪生 `subst.rs:255,263`） | 删；改为 solve 的 rename 带 `occ: Some(m)` 逐 meta 检查（`unification.rs:26,270,438`） | 机制换代；L08 的传递 occurs 用例无对等测试 |
| 燃料 | meta 展开 + decl 展开 + Match 重选 + Prim 归约多烧点，`UNIFY_FUEL=4096`（`mod.rs:549`） | 仅 frcs 的 Rigid lookup 命中烧 1（`mod.rs:592`）；`UNIFY_FUEL` 保留（`mod.rs:475`）；孪生 thread-local `PM_FUEL`（`force.rs:102-120`） | 无宿主的烧点删除属合理收敛（README `:288-310`） |

#### 4.6 孪生侧结构重组（文件级大搬家）

- 删 `prim.rs`：`DeclEntryF`/`MutableMap` 随 decl 世界消失；`UNIFY_FUEL/burn/refuel` 搬 `force.rs:102-120`；`lit_of` 搬 `spine.rs:161`；`is_selfref_val/prim_reduce` 无宿主。
- 删 `struct_eq.rs`：与参考版同步；`CACHE_SHRINK_MIN_ENTRIES/SPINE_SHRINK_MIN_ENTRIES/ReclaimOnClear/ConvScratch` 从 `machine.rs:37-107` 搬 `unify.rs:35-105`（符号表位移，非新能力）。
- 加 `debug.rs` 394 行：参考版 L09 错误消息开始内嵌值的 `{:?}`（`elaboration.rs:275,293`；`mod.rs:1043-1049`），打包值无法 derive Debug，须手工复刻才能让 Err 正文 parity（`tests/l09_fast_parity.rs:6-9` 要求归一化后逐字节比 Err 正文）[推断动机]。
- `spine.rs`：链头种类从 Decl/Prim/Obj/Other 降为 Flex/Obj/Other（A `spine.rs:15-17` → B `spine.rs:16-18`），`is_objheaded/xcell_head_name` 移入 unify（`unify.rs:152,324`）。
- `machine.rs`：`Names` 快照 + `fake_bind/define_name_in` 取代 name_map 轨迹；`wrap_names/restore_names/name_mark/unwind_names/is_flex_v/decl_insert` 删除；`wrap_types/str_pi/tm_pi/st2g_app/bind_prefix_of_telescope` 删除（`machine.rs:319-326` 注释说明 bind-prefix 快路径刻意不移植）。
- `entry.rs`：删 `NO_NAME_MAP` A/B 消融开关（A `entry.rs:245-249`），因名字解析已换载，消融对象不存在。
- `eval.rs`：`eval_aux` 由 `pub(super)` 降私有；`env.rs` 新增 `env_collect`（`env.rs:65`）；`compiler.rs`：`Walk` 枚举删除、`Compiler::new(ret_type)` + `Warning` 诊断（`compiler.rs:24,33,64,385`）。

### 5. 参考版 ↔ 孪生同步差异

| 项 | 参考版 | 孪生 | 是否同步 |
|---|---|---|---|
| 名字世界 | `Infer.global/global_names` | `Machine.globals/global_names/neutral` + Cxt Names 快照 | 同步（载体不同：HashMap vs Vec+缓存） |
| 中性全局视图 | `Cell<bool>` 开关（`mod.rs:456-467`，O(1)） | `neutral: Vec<V>` 预生成缓存（`machine.rs:76-81`） | 同步（语义同、实现不同） |
| struct_eq | 删 | 删 | 同步 |
| pending splice | 删（panic） | 删（同 panic，parity 覆盖） | 同步（同缺口） |
| 模式编译器 | `walk_pat` + elaboration 解方程 | 同构镜像（`compiler.rs:385`） | 同步 |
| debug 输出 | 真 Debug（Span 带偏移） | `debug.rs` 手工复刻（Span 全零） | 有文档化偏差：parity 前归一化 span（`tests/l09_fast_parity.rs:6-9`） |
| 燃料 | `Infer.unify_fuel: Cell` | thread-local `static PM_FUEL`（`force.rs:104`） | 同步语义，但跨 Machine/跨轮共享单线程全局状态 [推断 风险] |
| 文档一致性 | cxt.rs 已换 `subst_cxt`（`cxt.rs:167`） | 模块头仍称参考版走 `update_cxt/refresh`（`bump_spine_iter.rs:32-35`；`machine.rs:319-326`） | **不一致（孪生注释陈旧）**，L09 README `:288-310` 自认「源码注释待更新」 |

### 6. 回退/丢失/弱化清单

| A（L08）中功能/机制/守卫/测试 | B（L09）状态 | 锚点 | 影响 |
|---|---|---|---|
| 卡住 match 收 pending 实参、可再被应用 | 删除；`v_app` 对 Match panic | A `mod.rs:221-226,1154-1158`；B `mod.rs:192,729` | 合法程序 panic（README 登记为时代缺口） |
| `struct_eq` 结构快路径（省 force/eval） | 删除，无替代 | A `struct_eq.rs:26-34`、twin `struct_eq.rs:42` | Match/Match 比较变贵 [推断]，但语义自洽 |
| `MATCH_CMP_BUDGET=64` 总次数预算（耗尽保守失败） | 删除；无对应预算 | A `mod.rs:554`、`unification.rs:884`；twin `unify.rs:1015-1019` | 失去「不收敛时仍返回」的护栏 [推断 风险] |
| 可变全局 create_global/change_mutable/get_global 族 + 文件 IO + builtin 注册表 | 全删（builtin 只剩 string_concat） | A `mod.rs:536-547,959-1015,1538`；B `cxt.rs:34-92` | L08 程序不兼容；语言能力回退，README 以「时代口径」登记 |
| decl 表按名取值 / decl 展开 | 删除（值表 + 哨兵） | A `cxt.rs:24`；B `mod.rs:442-472` | 前向/重定义语义改变：重名静默覆盖无检查（README `:71-74` 自认） |
| `loose_string` 宽松臂的登记表守卫 | 删除（登记表不存在） | A `unification.rs:592-607`；B `unification.rs:662-664` | 「registered prim 不能宽松当 String」不再生效（无需生效） |
| 传递 occurs 检查（工作栈 + BUDGET） | 删除，改 rename 时逐 meta occurs | A `mod.rs:344-346`、`subst.rs:255-268`；B `unification.rs:26,270,438` | 深值/多跳环的检查面收窄 [未核实 语义等价性] |
| Match-vs-其它 η 臂 | 删除（保守 Err） | A `unification.rs:916-942` | 少证一些合法 η 等式；无错证风险 |
| 深值栈安全轮（quote/pretty/rename 工作栈化的其余项） | 未移植 | README `:314-321` 自认；L08 侧见 `mod.rs:1823`（shift_tm）族 | 深值可能栈溢出；parity/bench 用 256MB/128MB 栈兜底 |
| `LOOP_DEBUG`/`REN_DEPTH` 调试开关（会改运行时行为） | 删除 | A `mod.rs:32`、`unification.rs:299-311`；B 无 | 调试能力回退（非语义） |
| `NO_NAME_MAP` A/B 消融开关（孪生） | 删除 | A `bump_spine_iter/entry.rs:245-249` | 名字解析 A/B 实验能力消失（机制已换，合理） |
| in-crate 测试 2018 行 / 56 用例 | 整文件删除 | A `tests.rs:1-8`；见 §7 | 见 §7 覆盖缺口 |
| Cxt `Decls/DeclEntry/PrimFunc` 载体 | 删除 | A `cxt.rs:24-45`；B `cxt.rs:24-31` | 结构性，非能力 |

### 7. 测试与文档变化

**测试。** L08 in-crate `src/L08_product_type/tests.rs` = 2018 行 / 56 个 `#[test]`（L08 README `:292` 记为 `--lib` 60）；L09 该文件整体删除，lib 测试改在 `src/L09_mltt/{mod,parser/mod,parser/lex}.rs`。替代关系：

| L08 tests.rs 用例族 | L09 对应 | 判定 |
|---|---|---|
| `test_basic/index/dependent_match/_nested_eval/lambda_calculus_and_strings/generic_match` | `tests/l09_fast_parity.rs` 的 `parity_tests_rs_basic/index/dependent_match`、`parity_lambda_calculus` 等 | 有替代（parity 口径） |
| `test_eq_*` 等式推理族 | `parity_eq_reasoning` / `parity_eq_proofs` | 有替代 |
| `test_stuck_match_*` / `test_stuck_match_splice` / `_applied_with_outer_binder` | `parity_stuck_match`（只测卡死显示/行为）；splice 能力已删 | **部分丢失**（splice 用例随机制删除） |
| `test_string_builtins` / `test_file_io_builtins` / `test_decl_table_and_globals` / `test_get_global_missing_stays_stuck` / `test_registered_prim_not_loosely_string` / `test_string_to_global_type` | 无（builtin/decl 表/可变全局删除） | **随 feature 删除而丢失**（合理但无对等回归） |
| `test_product_*` 十连（struct/new/投影/Sigma） | `parity_struct_new_projection_l08_heritage` / `parity_struct_dependent_field_projection` | 有替代（parity） |
| `test_nested_coverage_gap*` / `test_ctor_wf_*` / `test_nested_pattern_refine_two_phase` | `parity_review_fixes_2026_09_18` + 5 个 `test_pm_*` lib 负例 | 有替代（且更强：负例显式断言） |
| `test_stuck_match_equation_bounded` / `test_occurs_check_transitive_chain` / `test_occurs_check_keeps_legit_refinement` | 无（预算与 occurs_transitive 删除） | **丢失**，无对等回归 |

数字：`tests/l09_fast_parity.rs` 29 个 `#[test]`（README `:326-332` 一致）；`src/L09_mltt` 内 10 个 `#[test]`（`mod.rs:1192,1380,1413,1441,1471,1498,1550`；`parser/mod.rs:700,774`；`parser/lex.rs:326`），README 称 5（`:360-364`）**已过期**——2026-09-20 新增 5 个 `test_pm_*` 负例（`mod.rs:1402-1410` 注释自述）。L09 无 `l09_blackbox` 套件（L08 有 `l08_blackbox.rs` 58 + `l08_blackbox_v2.rs` 53，仍在仓但服务 L08 黑盒面）。

**README。** 406→378 行、churn +363/-391，近重写；结构从「积类型增量」换成「再定基 + 已知限制」。过期/失真声明（详见 §2 表）：`fake_bind` 锚点、名字解析单表论、`string_concat` 行号、`v_app` panic 行号、fuel 行号、lib 测试数 5（实 10）、模式编译器锚点（compile:183/walk_pat:416/subst_cxt:156）均因 2026-09-20/09-23 重构漂移。孪生模块头仍写 `update_cxt/refresh`（`bump_spine_iter.rs:32-35`）与参考版现状 `subst_cxt`（`cxt.rs:167`）矛盾。

### 8. 工程性/性能/健壮性改动

| 项 | 内容 | 锚点 |
|---|---|---|
| O(D²)→O(D) 修复 | 顶层名表搬 `Infer.global_names`（append-only、不随 Cxt 克隆）；`locals` 改 `Rc<Locals>`；`src_names` 只装局部；孪生镜像 `global_names/neutral` 免每轮 O(D) 整拷 | `src/L09_mltt/mod.rs:445-455`；`cxt.rs:16-31`；twin `machine.rs:69-81`；README `:215-221` |
| 引擎入口健壮性 | 参考版 `run`/`run1` 对 parser `Option` 直接 `.unwrap()`（硬解析失败即 panic）；且无条件 `println!` 打 decl 名、parse error、整个 Cxt | `src/L09_mltt/mod.rs:1056-1082,1360-1378`；L08 同位置有 `L08_DEBUG_ON` 门控（A `mod.rs:1542-1553`） |
| 错误承载 | `Error(Span<String>)` 带 span；`unify_catch` 错误正文用 pretty 打印 find/expected | `src/L09_mltt/mod.rs:439,1043-1051` |
| parser 恢复 | `recover_with(skip_until_decl, || Decl::Println(Raw::Hole))` 占位；坏 decl 跳过、前缀保留、错误进 `Vec<IError>` | `src/L09_mltt/parser/mod.rs:19,183-190` |
| 燃料单线程化（孪生） | `static PM_FUEL: Cell<u32>` + `refuel/fuel_exhausted/burn` 自由函数（L08 为 per-Infer/per-Machine 字段） | twin `force.rs:102-120`；A `prim.rs:62-68` |
| 调试残留 | 参考版保留大量注释掉的 `println!`（`mod.rs:502,515,555,709,716,745,943,1041` 等）；`mod.rs:1060,1068,1076,1364,1376` 为**活跃** println；无 `.bak` | 同左 |
| 认知负担 | 孪生 2026-09-23 把原 `bump_spine_iter.rs` 拆成 14 个子文件（machine/force/quote/unify 等），并按原文件行序跨文件「拼装」注释段——接口不变、行号语义变脆 | `machine.rs:1-5`；`force.rs:1-4`；`subst.rs:1-6` |

### 9. 标题噪声排除说明

- README H1：`L08：积类型（product type / Sigma）` → `L09：MLTT 切片（Type N 分层宇宙 + 和类型 / match）`——纯层名/叙事替换，不计差异。
- 模块头「L09 核心机……L08 冠军配方向 MLTT/universe 层的移植」——层名标签，不计；但其中「参考版走 update_cxt/refresh」是**实质错误声明**（已计入 §5/§7）。
- `bump_spine_iter.rs` 顶部 `//!` 把差异写成「L07 拆分的差异」/「L08 冠军配方移植」——对 L08→L09 对，前者是更早层的说明、后者是真实 delta（翻译层名后保留）。
- 孪生文件名不变（`bump_spine_iter`）而参考版目录改名，diff 前缀显示为 rename——文件名不算语义差异。
- bench 负载族 `global`→`universe` 是**内容**差异（可变全局删除 + 宇宙负载新增），不是标题噪声。
- **半噪声/搬运残留**：L09 lexer 已有 `trait/impl/for/this/static/macro_rules` 关键字与 `$x` macro-ident（`lex.rs:15-20,70-75,124-129,223`），但 L09 没有任何 parser 消费它们（`parser/mod.rs` grep 0）——来自后续层（L10 trait/impl、L11 macro）的文本搬运，抬高 lex.rs +74 行但不构成本层语言面，已从语言增量中剔除、只记在 §3/§8。
- 层内提交注释（2026-09-18/09-20/09-23、`09b9ee8`、`ccfcb87`、`8101e8c`、`2a949ef`）不计入跨层 delta，仅用于解释载体。

### 10. 证据锚点表（断言｜锚点）

| # | 断言 | 锚点 |
|---:|---|---|
| 1 | L09 README 自述再定基、无名字键 decl 表 | `src/L09_mltt/README.md:3-8`；`src/L09_mltt/mod.rs:442-472` |
| 2 | L08 用按名 decl 表；L09 无 Decls 类型 | `src/L08_product_type/cxt.rs:24`；`src/L09_mltt/cxt.rs:24-31` |
| 3 | 项层全局引用换哨兵大下标 | `src/L08_product_type/mod.rs:76,1199`；`src/L09_mltt/mod.rs:398-408,793-801` |
| 4 | 全局值表 + 名字表分离 | `src/L09_mltt/mod.rs:444,455,501-528` |
| 5 | L08 全线带 decl 参数；L09 不带 | `src/L08_product_type/mod.rs:650,881,1189,1317`；`src/L09_mltt/mod.rs:554-568` |
| 6 | 卡住 match 的 pending 槽被删、v_app panic | `src/L08_product_type/mod.rs:221-226,1136-1158`；`src/L09_mltt/mod.rs:192,715-731` |
| 7 | struct_eq 两版删除、无替代 | `src/L08_product_type/struct_eq.rs:26`；`src/L08_product_type/bump_spine_iter/struct_eq.rs:42`；`src/L09_mltt/bump_spine_iter.rs:82-83`（仅注释） |
| 8 | Match/Match 改中性视图重求值 | `src/L09_mltt/unification.rs:695-756`（`:731-734` 注释）；twin `unify.rs:854-880` |
| 9 | L08 有 64 次 match 比较预算；L09 无 | `src/L08_product_type/mod.rs:554`；`src/L08_product_type/unification.rs:884`；twin `unify.rs:26,37` |
| 10 | SumCase 合一从 datas-only 改为 typ+datas | `src/L08_product_type/unification.rs:820-855`；`src/L09_mltt/unification.rs:678-694` |
| 11 | 新增 Type N 分层宇宙 | `src/L08_product_type/mod.rs:82,198`；`src/L09_mltt/mod.rs:70,178`；`pretty.rs:153` |
| 12 | 新增 check_universe 及两条 meta 解路径 | `src/L09_mltt/elaboration.rs:246-294` |
| 13 | enum universe_lvl 收集与 Π 链 | `src/L09_mltt/elaboration.rs:451-463,496-498` |
| 14 | 新增 check_ctor_wf | `src/L09_mltt/elaboration.rs:550,560-573` |
| 15 | 内建面 15→1（仅 string_concat） | `src/L08_product_type/cxt.rs:162-228`；`src/L09_mltt/cxt.rs:34-92`；`src/L09_mltt/mod.rs:859-868` |
| 16 | L08 有可变全局/文件 IO；L09 无 | `src/L08_product_type/mod.rs:536-547,959-1015,1538` |
| 17 | 特化方程从 pattern_match 移到 elaboration | `src/L09_mltt/elaboration.rs:74,110,127,227`；`src/L09_mltt/pattern_match.rs:60,190`；L08 elaboration grep `check_pm`=0 |
| 18 | Cxt 名字载体从轨迹表换 BiMap 快照 | `src/L08_product_type/cxt.rs:62-98,113`；`src/L09_mltt/cxt.rs:24-31,167-183` |
| 19 | L08 事后 occurs_transitive；L09 改 rename 内 occ | `src/L08_product_type/mod.rs:344-346`；`src/L08_product_type/bump_spine_iter/subst.rs:255,263`；`src/L09_mltt/unification.rs:26,270,438` |
| 20 | parser 改为错误恢复 + Option 返回 | `src/L09_mltt/parser/mod.rs:19,174,183-190`；`src/L08_product_type/parser/mod.rs:107-133` |
| 21 | lexer 增 Type/MacroIdent token、人读 Display、并预置死关键字 | `src/L09_mltt/parser/lex.rs:10-20,46,58-97,124-129`；`src/L09_mltt/parser/mod.rs:330`（Type） |
| 22 | struct/new 脱糖两版都在 parser | `src/L08_product_type/parser/mod.rs:448,546`；`src/L09_mltt/parser/mod.rs:580-587,667-683` |
| 23 | Error 从 String 改为带 Span | `src/L08_product_type/mod.rs:524`；`src/L09_mltt/mod.rs:439` |
| 24 | 显示形态 comma 血统 + unsolved match | `src/L09_mltt/pretty.rs:212-220,226-228` |
| 25 | 孪生名字世界换载体 | A `machine.rs:134,136,224,243,365,370`；B `machine.rs:40-47,68,75,81,263,279` |
| 26 | 孪生 eval 越哨兵查 globals | `src/L09_mltt/bump_spine_iter/eval.rs:193-197,304-306` |
| 27 | 孪生链头种类从 Decl/Prim/Obj 降为 Flex/Obj | A `spine.rs:15-17`；B `spine.rs:16-18` |
| 28 | 孪生删 prim.rs（DeclEntryF/MutableMap/prim_reduce） | A `bump_spine_iter/prim.rs:26,59,64,106`；B `force.rs:102-120`（燃料）、`spine.rs:161`（lit_of） |
| 29 | 孪生删 simpl_decl 与相关空表分支 | A `mod.rs:1524`；A `quote.rs:343`；A `rename.rs:505`；A `unify.rs:407` |
| 30 | 孪生新增 debug.rs 394 行 | `src/L09_mltt/bump_spine_iter/debug.rs:1-3,45` |
| 31 | 孪生删 NO_NAME_MAP 消融开关 | `src/L08_product_type/bump_spine_iter/entry.rs:245-249` |
| 32 | 参考版 run/run1 无门控 println + unwrap | `src/L09_mltt/mod.rs:1056-1082,1360-1378`；对照 A `mod.rs:1542-1553` |
| 33 | lib 测试实为 10（README 称 5） | `src/L09_mltt/mod.rs:1192,1380,1413,1441,1471,1498,1550`；`parser/mod.rs:700,774`；`parser/lex.rs:326`；`README.md:360-364` |
| 34 | parity 套件 29 用例、要求 Err 正文归一化后逐字节一致 | `tests/l09_fast_parity.rs:1-9`；`README.md:326-332` |
| 35 | O(D²) 修复的注释与实现 | `src/L09_mltt/mod.rs:445-455`；`src/L09_mltt/cxt.rs:16-31`；twin `machine.rs:69-81` |
| 36 | 孪生注释仍称参考版走 update_cxt/refresh（陈旧） | `src/L09_mltt/bump_spine_iter.rs:32-35`；`src/L09_mltt/bump_spine_iter/machine.rs:319-326`；对照 `cxt.rs:167` |
| 37 | 4 删 1 增的文件级断点 | `.deltawork/pairs/L08--L09.files.tsv`（struct_eq.rs/tests.rs/twin struct_eq/twin prim removed；twin debug added） |

### 11. 给 Lead 的一句话

L09 相对 L08 是「再定基换名字世界 + 删 3 项旧机制（decl 表/struct_eq/splice）+ 增宇宙层」，净 -4015 行；链在此处重接而非渐进，L10–L13 承其新基底。

> 待 Lead 裁决/交叉核对的可疑点：(1) README §2 的「名字解析只走 src_names 一次查表」与其 §4 的 `global_names` 修复自相矛盾（实为两表）；(2) README 称 lib 测试 5 个、实 10 个；(3) 孪生模块头仍写 update_cxt/refresh（参考版已 subst_cxt）；(4) L08 README 说 L08 是逐臂匹配编译器，而本 diff 显示 L09 才把 `Walk` 决策树重写成 `walk_pat`——与 delta-l07-l08 单元的 L08 现状描述需对齐（两边都对，但叙述方向相反，合并时勿写成「L09 重写 L08 编译器」）。

## 6. L09 → L10：trait / typeclass（纯增量之上叠 Val→Rc<Val> 全签名重构）

> 单元 delta-l09-l10 / 数据源 .deltawork/pairs/L09--L10.{diff,numstat.tsv,files.tsv,symbols.tsv} / 核对时点 HEAD 0464150c
> 只读审计，未跑 cargo；行号均为当前工作树实测。参考版 = src/L10_typeclass/ 分文件实现，孪生 = bump_spine_iter/**。

### 0. 结论摘要

- 性质：L10 = 在 L09 骨架上**新增 typeclass 子系统**（trait/impl 声明→enum 脱糖、Prolog 式实例求解器 Synth、接收者方法脱糖、outParam），同时进行两轮**跨切面改造**：参考版值表示 Val→Rc<Val>（全签名级）、模式匹配可解集白名单删除；孪生侧则拆文件 + 合入 debug + 加临时探针 + fresh_meta 关闭化。
- 规模：13415→16666 行（+3251）。参考版 4358→5631（+1273），parser 1308→1494（+186），孪生 7749→9541（+1792）；新增 typeclass.rs 430 + twin/typeclass.rs 307 = 737 行；删除 twin/debug.rs 394（内容并入 machine.rs）。
- 新增 top churn：twin/machine.rs +1587（探针 ~500 / trait 面 ~500 / fresh_meta 关闭化 ~250 / debug 合并 ~390）、mod.rs +707、elaboration.rs +186。
- 语言面：lex.rs 完全未变（406→406）——trait/impl/for 关键字 L09 词法已存在（parser/lex.rs:124-126），L10 只是接上语法/检查；新增 `this`（parser/mod.rs:329）、**多段投影恢复**（parser/mod.rs:340-347，L09 只有单段 parser/mod.rs:340）、Raw 的 Display。
- 实例求解：参考版与孪生**共用同一个 Synth**（twin/typeclass.rs:14）；但 Val↔Typ 桥（to_typ/val_to_typ）与三方法镜像各一份，符合 README 声称"语义以参考版为准"。
- 语义放宽（需 Lead 注意）：L09 `SpecSolve.solvable` 白名单 + `Cxt::bind_slots` 在 L10 被整体删除（L09 cxt.rs:191-207 / unification.rs:19-20 → L10 elaboration.rs:16-23）；可解集 = 任意裸 Rigid。
- 文档失真（跨单元冲突点）：L10 README:120 声称"L09–L13 都用决策树矩阵、L10 才改逐臂"与当前 L09 代码（L09 pattern_match.rs:84/448 已是值级探测+逐臂）矛盾；README:354-360 的测试数 21/42 与当前静态计数 25/46 不符；多处行号锚点漂移。
- 链连续性判断：**功能面连续且为纯增量**；断点只在文档口径、可解集语义放宽、以及 L09 两个旧覆盖测试被新测试族替代（非功能丢失）。孪生 debug.rs 的"删除"是载体合并，不是功能回退。

### 1. 规模与文件级变化

数据源 .deltawork/pairs/L09--L10.files.tsv / numstat.tsv。行数 = 物理行；churn = numstat +/-。

| 文件 | 状态 | A→B 行数 | churn +/- | 一句话性质 |
|---|---|---|---:|---|
| bump_spine_iter.rs | changed | 128→170 | 95/53 | 模块头重写 + 新增 typeclass 子模块 + re-export 面扩大 |
| bump_spine_iter/bench_src.rs | changed | 142→143 | 4/3 | +1：traitchain 负载生成器（README:276-283） |
| bump_spine_iter/compiler.rs | changed | 530→529 | 192/193 | 签名级重排（NestedCheck 去生命周期、Var 别名） |
| bump_spine_iter/debug.rs | **removed** | 394→- | 0/394 | 整文件并入 machine.rs:3232 起（内容保留） |
| bump_spine_iter/entry.rs | changed | 361→387 | 58/32 | tm_size pub(super) + Tycker 探针/新字段 |
| bump_spine_iter/env.rs | changed | 144→152 | 15/7 | +DN_TIP/DN_FB 探针原子计数 |
| bump_spine_iter/eval.rs | changed | 565→564 | 56/57 | eval_aux 可见性 + sampler tick |
| bump_spine_iter/force.rs | changed | 531→602 | 236/165 | frcs_env/force_deep pub + PM_FUEL pub(super) |
| bump_spine_iter/machine.rs | changed | 2129→3716 | 2118/531 | **+1587**：探针模块 + trait 三方法宿主 + Debug 复刻 + fresh_meta 关闭化 |
| bump_spine_iter/quote.rs | changed | 458→476 | 32/14 | is_trait 字段穿参 + 探针 |
| bump_spine_iter/rename.rs | changed | 796→883 | 133/46 | is_trait + 中性 globals 视图调用点 |
| bump_spine_iter/spine.rs | changed | 169→169 | 9/9 | 净 0：MetaEntry 注释/布局微调 |
| bump_spine_iter/subst.rs | changed | 264→234 | 110/140 | SpecSolve 去生命周期（保留在本文件） |
| bump_spine_iter/syntax.rs | changed | 253→260 | 30/23 | Tm/XCell 增 is_trait；GLOBAL_BASE 移出 |
| bump_spine_iter/typeclass.rs | **added** | -→307 | 307/0 | 孪生 trait 三方法 + TraitState + val_to_typ + neutral_of |
| bump_spine_iter/unify.rs | changed | 885→949 | 185/121 | 工作表 unify + trait/def 求解挂点 + unsolved worklist |
| cxt.rs | changed | 219→194 | 45/70 | **-25**：Rc 化 + bind_slots 删除 |
| elaboration.rs | changed | 918→1104 | 586/400 | +186：TraitDecl/ImplDecl 臂 + trait_wrap + Rc 化 |
| mod.rs | changed | 1572→2279 | 1298/591 | **+707**：Rc<Val> 全链 + trait 表/fresh_meta + 11 个新测试 |
| parser/lex.rs | **unchanged** | 406→406 | 0/0 | 词法无改动（关键字早已在） |
| parser/mod.rs | changed | 790→883 | 135/42 | +93：p_trait_def/p_impl/this/多段投影/2 个测试 |
| parser/syntax.rs | changed | 112→205 | 98/5 | +93：is_trait、TraitDecl/ImplDecl、Pattern span bool、Raw Display |
| pattern_match.rs | changed | 595→565 | 153/183 | -30：Rc 化 + 去 bind_slots/solvable + eval_aux_arm 合并 |
| pretty.rs | changed | 242→255 | 21/8 | bracket 提取 + is_trait 穿参（净显示不变） |
| syntax.rs | changed | 52→44 | 18/26 | Locals 载荷 Rc、close_ty 走 Rc |
| typeclass.rs | **added** | -→430 | 430/0 | 参考版 Typ/Assertion/Instance/Synth 求解器 |
| unification.rs | changed | 760→760 | 251/251 | 净 0：Rc 化 + solve_trait/solve_multi_trait 新增、SpecSolve 迁出 |

- added：src/L10_typeclass/typeclass.rs、src/L10_typeclass/bump_spine_iter/typeclass.rs。
- removed：src/L09_mltt/bump_spine_iter/debug.rs（394 行；功能迁入 machine.rs，见 §5/§6）。
- 口径提醒：本 pair 数据只覆盖 src/L09_mltt → src/L10_typeclass；tests/ 不在 diff 内（见 §7）。

### 2. 标题宣称的增量：声称 vs 实现

| README 声称（锚点） | 实现锚点 | 判定 |
|---|---|---|
| trait 声明脱糖为 is_trait enum，维护 trait_definition/trait_out_param（README:23-26） | elaboration.rs:624-658（TraitDecl 臂）、632-633（两表插入）；Val::Sum 第 4 位 bool mod.rs:177-182 | 一致 |
| impl 登记实例进 class_instances，支持泛型/毛毯实例（README:26-28） | elaboration.rs:535-622；589 impl_trait_for；编译用例 mod.rs:1287-1310（inherent+泛型）、1343（毛毯 Say for T） | 一致 |
| 期望 trait Sum → fresh_meta 放待解 meta，合成推迟到 def 后 solve_multi_trait（README:30-33） | mod.rs:569-586 实为**先立即试解**（573 solve_trait），失败才落待解 meta（575-577）；def 后 elaboration.rs:367 | **部分**（README 漏了立即试解；锚点 500-505 已漂移） |
| solve_trait 是 Val↔Typ 桥：滤 out 位→force_deep().to_typ→Synth→实例名回推（README:33-36） | unification.rs:467-508（476 trait Sum、482-488 滤 out+to_typ、489-493 synth、494-499 回推+合一） | 一致（行号 468→467 漂移 1 行） |
| trait_wrap 扫方法表、Any 填 out 位试解、拼 Let（$this/$$）（README:40-43） | elaboration.rs:1009-1103（1010 to_typ、1014-1030 试解、1031-1079 Let 构造、1086-1102 has no object） | 一致（行号 1003→1009 漂移） |
| 实例匹配单向一阶 match_typ，out 位 Any 通配（README:48-58） | typeclass.rs:398-430（405-410 pattern 侧 Var 绑定、413 Any 臂、415 goal rigid 拒绝）；out 位滤除 unification.rs:482-488 | 一致 |
| Synth effort≤1000 超限 panic（README:1.4） | typeclass.rs:219-224 | 一致 |
| Synth 为参考版与孪生共用（README:5-6） | twin/typeclass.rs:14 直接 use 参考版 Synth；两版各自 solve_* 镜像 | 一致 |
| "L09–L13 参考版与孪生都用决策树矩阵编译 match"（README:120） | 当前 L09 已是逐臂+值级探测：L09 pattern_match.rs:448 walk_pat、84 probe_accessible；L10 为同一路线的 Rc 版 | **不一致/历史混淆**（见 §7、§9） |
| "L10 相对 L09 恢复 (Obj,Obj) 臂"（README:90） | L09 已有该臂 L09 unification.rs:593；L10 unification.rs:753 | **不一致**（两版都有，非 L10 增量） |
| Match 中性视图 = avoid_recursive 整表克隆（README:110） | 当前实现为 neutral_globals Cell 开关 mod.rs:480、860-863、962-971；avoid_recursive 已不存在 | **过期** |
| 测试：lib 21（mod.rs 16+parser 5）、parity 42（README:354-360） | 静态计数：lib 25（mod.rs 20+parser 4+lex 1）、parity 46 | **过期**（README:364-365 自我矛盾地另说 42/21 为"当前数"） |

### 3. 语言/语法/类型系统/内建/LSP 面增量

- **trait/impl 语法**（词法零改动，语法层启用）：`trait Name [params] { def m(...): T ... }`（parser/mod.rs:698-720，方法只声明无体）；`impl[params] Trait[args] for Name { def... }`（parser/mod.rs:722-731）与 **inherent impl** `impl[params] Name { def... }`（731-744，合成 trait 名 + need_create=true，由 elaboration.rs:538-554 现场补 TraitDecl）。p_decl 注册 parser/mod.rs:756。
- **声明项**：Decl::TraitDecl / ImplDecl（parser/syntax.rs:192-204）；DeclTm 增 Trait/TraitImpl 空变体（mod.rs:49-54）；run() 对 TraitDecl/ImplDecl 打印（mod.rs:1129-1141）。
- **is_trait 标记**：Raw::Sum/SumCase 增 bool（parser/syntax.rs:64-70），Tm::Sum/Tm::SumCase/Val::Sum/Val::SumCase 全程穿参（mod.rs:177-189、unification.rs:314-341、quote.rs:355-396）；TraitDecl 脱糖时置 true（elaboration.rs:636）。
- **outParam**：无关键字/无专门语法，按 `Raw::App(Raw::Var("outParam"), ...)` 形状识别（elaboration.rs:628-631）；trait 自动加隐式 Self 参数（elaboration.rs:626）。
- **无 where 子句/实例依赖**：Instance.dependencies 恒为 List::new()（elaboration.rs:584）→ 实例求解无约束/子句，Synth 的 dependencies 机制未启用（typeclass.rs:206-208 恒空）。
- **`this` 关键字**：parser 增 ThisKeyword→Raw::Var("this")（parser/mod.rs:329-330），使 impl 方法体可引用接收者；编译用例 mod.rs:1288-1291、1381-1387。
- **多段投影恢复**：p_atom 由 L09 单段 `.option()`（L09 parser/mod.rs:340-347）改为 `.many0()` fold（L10 parser/mod.rs:340-347）→ `p.x.y` 链；测试覆盖 mod.rs test_trait 1382（this.x.add）等。
- **Raw Display**（parser/syntax.rs:101-175）新增：把 Raw 以伪语法打印，供诊断/调试；L09 只有 to_span。
- **运算符标识符**：p_raw 的 Ident 后接 `.or(string(Op))`（parser/mod.rs:611），支持 `+` 一类 Op 作为原子名（与 trait 方法名解析相关）。
- **Pattern::Any 的 span 载荷 Span<()>→Span<bool>**（parser/syntax.rs:19），解析处填 true（parser/mod.rs:549），为 L11+ 通配标记预留；L10 内无消费方（pattern_match.rs:419/488 均忽略）。
- **LSP 面**：本 pair 文件集全在 src/L10_typeclass/ 下，无 src/lsp/** 改动；trait/impl 的 goto/hover 支持不在本对增量内 [未核实：需另查 lsp 目录]。

### 4. 核心机制与实现性改动

#### 4.1 参考版值表示 Val→Rc<Val>（跨切面重构）

- L09：`Env = List<Val>`、`Spine = List<(Val,Icit)>`（L09 mod.rs:159-160），Val 内 Sum/SumCase/Match 用 Rc<Vec<..>>（L09 mod.rs:182-192）。
- L10：`Env = List<Rc<Val>>`、`Spine = List<(Rc<Val>,Icit)>`（mod.rs:154-155）；Val 内部改为 Vec（元素已是 Rc，mod.rs:177-189）；eval/force/quote/unify 全改引用签名（mod.rs:590、854、986；unification.rs:605），insert 返回 (Rc<Tm>,Rc<VTy>)（elaboration.rs:26-50）；Cxt::bind/define 收 Rc（cxt.rs:112-150）；Locals 载荷 Rc（syntax.rs:20-25）、close_ty 走 Rc（syntax.rs:34）。
- 动机/后果：Val 克隆变 O(1) 引用计数，服务 trait 求解/模式编译的大量值传递；代价是整层 API 签名变更——L09→L10 的 churn 中相当比例是这次机械改造（mod.rs 1298/591、unification 251/251、cxt 45/70）。孪生不受影响（一直是打包 V，复制即 u64）。
- 附带的 API 删除：L09 的 `rc_take`、`eval_ref`（拥有版 eval 入口）删除，eval 统一 `/&Rc<Tm>`（符号表 -eval_ref、-rc_take）。

#### 4.2 trait 求解链路（新增子系统）

- 建模：trait = is_trait 的 Sum；Synth 挂在 Infer.trait_solver（mod.rs:465），trait 元数据两张 FxHashMap（mod.rs:466-467）。
- 触发点（全部实测）：① fresh_meta 立即试解（mod.rs:573）；② def 体检查后 solve_multi_trait(0)（elaboration.rs:367）；③ unify 的 Flex 解出后（unification.rs:662-669）与 flex_flex（545）。
- solve_multi_trait：扫 `meta[m..]` 全部未解项逐个 solve_trait，命中改写 MetaEntry::Solved（unification.rs:450-465）；失败映射 UnifyError::Trait（mod.rs:430-433），错误文本直出（mod.rs:1112）。
- solve_trait：force→(trait Sum)→out 掩码滤参→force_deep+to_typ→Synth.synth→把实例名作为 Raw::Var 重新 infer/insert/eval→实例类型与期望 trait Sum 合一（unification.rs:467-508）。
- Synth 算法：表驱动 Prolog（generator_stack/consumer_stack/assertion_table，typeclass.rs:138-153），consume 兼作答案缓存（310-354）；new_subgoal 每子目标 clone 整份实例表（299，TODO 注释 298）；effort>1000 panic（219-224）。**无 occurs/无剪枝保护**，护栏只有 effort 崩溃面。
- trait_wrap：接收者方法 `x.foo y` → 对每个 trait 的同名方法构造 Assertion（out 位 Typ::Any）试解，取首个命中，拼 Let(实例参数) + Obj 投影 + 方法 β 应用；失败/接收者 to_typ None → has no object（elaboration.rs:1009-1103）。每次调用 clone 整个 trait_definition（1011-1012，TODO 自证）。
- 实例登记：ImplDecl 把方法体包成 λ 追加到 trait 构造子应用链（elaboration.rs:595-609），再以 Def 检查登记（610-620）；inherent impl 先补 TraitDecl（538-554）。
- 已知口径：实例求解走常规 unify，不带 spec（elaboration.rs:116-120 注释）——trait 合成中的合一拿不到模式特化解。

#### 4.3 名字世界与 global（继承 L09，未再重定基）

- 仍无 decl 表：global: FxHashMap<Lvl, Rc<VTy>>（mod.rs:454）+ 大下标哨兵 1919810（lvl2ix mod.rs:411-421；eval 回落 mod.rs:860-863）；顶层名字表 global_names append-only（mod.rs:464，随 Infer 不随 Cxt），局部 src_names 遮蔽优先（shadow_local mod.rs:505-508）。
- fake_bind/define_global 从 Cxt 迁到 Infer（mod.rs:514、526）；Cxt 只剩 env/lvl/locals/pruning/src_names（cxt.rs:22-29）。这是 cxt.rs -25 行的一部分。
- 中性全局视图载体更换：三处"整机 clone + 改 global 表"→ Cell<bool> 开关 + eval_neutral 包装（mod.rs:480、860-863、962-971），语义 O(1) 等价；L09 的 avoid_recursive 参考版实现消失。孪生侧仍保留物化的 neutral_of(&globals)（twin/typeclass.rs:226-232，rename.rs:537 调用）——两版载体不同但语义同款。

#### 4.4 模式匹配：Rc 化 + 可解集白名单删除

- L09：SpecSolve 带 `solvable: &'a [Lvl]`（L09 unification.rs:16-20），由 `cxt.bind_slots()` 生成（L09 cxt.rs:191-207），unify_pm 可解臂用 `solvable.contains(x)` 限制（L09 unification.rs:607/621）；pattern_match 两处构造（L09 pattern_match.rs:172-174、272-274）。
- L10：SpecSolve 只剩 acc（elaboration.rs:16-23），bind_slots 在 cxt.rs 与两版 pattern_match 全部删除；可解臂条件退化为"裸 Rigid 且 sp.is_empty()"（elaboration.rs:137-140 起）。
- 后果：可解集从"显式白名单"放宽为"任意裸 Rigid"，属**语义放宽**；README 将其记为 L10 定制口径（L10 README:214-218 附近），但代码差异本身是白名单删除，可能解出 L09 拒绝的槽——建议 Lead 在跨层审计里核对是否引入过度求解 [推断]。
- 其余为同一路线的机械同步：probe_accessible 值级探测保留（L10 pattern_match.rs:86-146），显式穿 lvl/init_sub、无 bind_slots 后的顶层/嵌套 probe 调用；eval_aux 合并 eval_aux_arm 内联（L09 pattern_match.rs:373/388 → L10:360），净 -30 行。
- 覆盖检查测试族换血：L09 的 test_pm_nested_coverage_gap_rejected / test_pm_coverage_controls_ok 删除，L10 换成 test_nested_coverage_gap/gap3/complete/refine_absurd（mod.rs:1975/2000/2026/2057）+ 遮蔽/通配 4 例（mod.rs:2168/2192/2220/2256）。

#### 4.5 fuel 与健壮性口径

- 参考版：UNIFY_FUEL=4096 保留（mod.rs:449，L09 mod.rs:475）；API 重构：L09 `burn(&Cell)`+`meta_refuel`（L09 mod.rs:345/530）→ L10 `burn_fuel`+`refuel`（mod.rs:548/557）；烧点扩面：L10 在 unify 入口烧 1（unification.rs:607）与 force 的 meta 展开烧 1（mod.rs:596），L09 仅 frcs lookup 命中烧（L09 mod.rs:592 单点）。→ L10 注释称"L09 重写时丢失、L10 恢复"（mod.rs:447-448）**与 L09 现状不符**（L09 有同值 fuel），实为扩面+改名。
- 孪生：PM_FUEL 由 private 改 pub(super)（force.rs:155-161；L09 force.rs:102-115 private）；新增 sampler tick 与 #[cfg(feature="sampler")] 钩子（机器侧多处）。
- 实例求解护栏薄弱面：effort 超限 = panic（typeclass.rs:219-224）；match_typ 单向匹配无 occurs（typeclass.rs:398-430）——靠"实例断言不含被剔形态"的口径兜底。
- fresh_meta close 常态化（孪生 2026-09-21 轮，README:301-330）：free_var_indices/remap_free_vars/close_tm_reduced（machine.rs:1779/1832/1988）取代 has_free_var 全构造，修正 impl 类型参数泄漏进 decl 上下文导致的 close O(n²) 内存；参考版对应仍是 close_ty 沿 Locals 链（syntax.rs:34-44）。README 称 k=9 内存 142.67→30.63MB（[未核实]，未跑测）。

#### 4.6 孪生机器增量（+1587 的构成）

- +512 @ machine.rs:14-524：solve_probe 临时探针（GLOBAL_BASE 移入 machine.rs:45、solve_probe/Cnt/TGuard/ItemGuard、L10SOLVE_PROBE dump machine.rs:416/470/512）。
- +~130 @ machine.rs:563-700：unsolved worklist（remove_unsolved:663；出表 5 处注释 563-575）、tstate 字段（610）。
- +~500：trait 面——trait_wrap（2259）、TraitDecl 臂（3003）、ImplDecl 臂（3043）、def 臂 solve_multi_trait_ref（2843-2851）、trait_err 出参（unify 1199/1206/1273；unify_catch 1305-1312）。
- +~250：fresh_meta 关闭化（1779-1988）。
- +~390：Debug 复刻并入（3232-3500，dbg_span_str:3236、debug_val:3265、debug_tm:3476）。
- 另加：resolve_name 抽公共解析（2469，探测与 Var 臂共用）、DeclOut 增 Trait/TraitImpl（3224-3230）、check_universe_inner 返回 Result（1582）、insert 改 pub(super)（1410）、unify_pm/solve_pm（2091/2175）。

### 5. 参考版 ↔ 孪生版同步差异

| 项 | 参考版 | 孪生 | 同步性 |
|---|---|---|---|
| trait 求解器 Synth | typeclass.rs:138-355（430 行） | 直接 use 参考版（twin/typeclass.rs:14） | **共用同一实现**（唯一完全共享的新机制） |
| 求解三方法 | unification.rs:450/467 | twin/typeclass.rs:32/86/105（镜像）；宿主 impl Machine | 语义镜像、独立代码；错误文案同形（twin:218 vs ref:503） |
| Val↔Typ 桥 | Val::to_typ typeclass.rs:19-70 | val_to_typ twin/typeclass.rs:249-307 | 两版各一份；**twin 注释 247-248 称参考版是 todo!()，但参考版已改 None（typeclass.rs:28-35）→ 过期注释** |
| trait 元数据表 | Infer 三张表 mod.rs:465-467 | TraitState（solver/definition/out_param）twin/typeclass.rs:237-245 | 结构同构，载体不同 |
| 中性 global 视图 | Cell<bool> 开关 mod.rs:480/962-971 | 物化 neutral_of Vec（twin/typeclass.rs:226） | 载体不同、语义同 |
| 未解 meta 扫描 | 后缀线性扫 unification.rs:451-456 | unsolved worklist + prepare 排序（typeclass.rs:39-48） | **性能载体不同**（孪生 A-2 优化） |
| debug 模块 | 无独立文件 | L09 debug.rs 删除→并入 machine.rs:3232 起 | 载体合并 |
| trait_wrap | elaboration.rs:1009 | machine.rs:2259 | 逐句镜像；twin 侧接收者均 force 后传（2574-2598） |
| 探针/采样 | 无 | solve_probe + sampler tick | 仅孪生（性能诊断用） |
| 错误文本 | 携带源码 span | 内嵌 Debug 的名字 span 全零（machine.rs:3232-3233 注释） | 已知偏差，parity 归一化 |

### 6. 回退/丢失/弱化清单

| L09 中项 | L10 状态 | 锚点 | 影响 |
|---|---|---|---|
| bump_spine_iter/debug.rs（394 行） | 文件删除，函数体并入 machine.rs | L09 bump_spine_iter.rs:92 mod debug；L10 machine.rs:3232-3500 | **无功能丢失**；只是文件级断点假象 |
| SpecSolve.solvable + Cxt::bind_slots（白名单） | 删除，可解集=任意裸 Rigid | L09 cxt.rs:191-207；L09 unification.rs:19-20；L10 elaboration.rs:16-23 | **语义放宽**（可能多解，README 记为定制） [推断：需回归验证] |
| L09 覆盖两测试（gap_rejected/controls_ok） | 删除，代之以 4+4 个新 pm 测试 | L09 mod.rs:1472/1499；L10 mod.rs:1975-2067、2168-2256 | 测试覆盖未减少 |
| eval_ref（拥有版 eval 入口） | 删除，eval 统一 `/&Rc<Tm>` | 符号表 -eval_ref；mod.rs:854 | 所有权重构，无功能丢失 |
| rc_take helper | 删除 | 符号表 -rc_take | Rc 化后无用 |
| meta_refuel / burn(cell) | 改名 refuel/burn_fuel 并扩烧点 | L09 mod.rs:530/345；L10 mod.rs:557/548 | API 改名 + 扩面 |
| 参考版 avoid_recursive（整机 clone） | 换成 neutral_globals Cell | README:110 旧锚点；L10 mod.rs:480/962-971 | 等价替换，非丢失 |
| README 声称的"无 fuel" | L10 有 fuel，且 L09 现状也有 | L10 README:88 自认过时；L09 mod.rs:475 | 文档失真（非代码回退） |
| trait 求解 where/依赖 | 未实现（dependencies 恒空） | elaboration.rs:584；parser 无 where 关键字（lex 未变） | 功能缺口（相对提示中的 where，本层未做） |

### 7. 测试与文档变化

- src 内嵌测试：L09 = 10（mod.rs 7 + parser/mod 2 + lex 1）→ L10 = 25（mod.rs 20 + parser/mod 4 + lex 1）。L09 mod.rs 测试：test1/test2（L09 mod.rs:1381/1193）+ 5 个 pm 回归；L10 新增 test_trait（mod.rs:1268-1456，覆盖 inherent/泛型 impl、ToString/Say/Add+outParam、this、多段投影）、test5/test6/test4（1459/1483/1509）、test_index（1815）、7 个评审钉（1975-2131）、4 个 pm 遮蔽/通配钉（2168-2256）。parser 新增 test_impl_for_parses / test_inherent_impl_parses（parser/mod.rs:838/852）。
- tests/ 套件：新增 tests/l10_fast_parity.rs（1214 行，静态 21 个 #[test]、6 个 #[path]；git 引入提交 aafa5ed8）。测试族：parity_basics(:135)、parity_trait_full_demo(:231)、parity_trait_pieces(:369)、parity_trait_errors(:462)、golden_trait_tostring_and_say_synthesis(:805)、golden_outparam_add_chain(:853)、golden_l09_heritage_values(:893)、golden_universe_levels(:933)、synth_rigid_generic_not_falsely_matched(:688)、parity_review_fixes_2026_09_18(:1024)、fast_substv_reclaimed_across_rounds(:1173) 等。判据 Ok 逐字节 / Err span 归一化（tests/l10_fast_parity.rs:1-7 头注）。
- 静态计数 vs README：README:354-360 写 lib 21 / parity 42，实测 25 / 46（25 个源内测试全部经 #[path] 编译进 parity 目标 + 套件自有 21）；README:364-365 又写 "42/21，即当前数"，自身矛盾。→ 文档过期。
- README 差异：L09 377 行 → L10 376 行（numstat 366/367），但内容几乎整体重写（L10 主线改为 trait/typeclass + 匹配编译器故事）。README 声称与实现核对见 §2；行号锚点多处漂移（elaboration.rs:1003→1009、1008→1012；mod.rs:448→449、500-505→569-585、959-975→962-971；unification.rs:468→467；mod.rs:1874→1975）。
- 层目录内无 tests.rs 增删（L09 无 tests.rs）；tests/ 的 l09_fast_parity.rs（29 个 #[test]）未在 L10 删除/改写（pair 范围外），L10 另立 l10 套件——"每层双 oracle"模式延续。

### 8. 工程性/性能/健壮性改动

- 孪生临时探针设施（L10SOLVE_PROBE / solve_probe）：machine.rs:52-230 全套计数器、TGuard/ItemGuard（340/363）、dump（395/416/470/512）、trait_wrap 分桶（155/199）；env.rs:36-37 DN_TIP/DN_FB；entry.rs:211 tm_size pub(super)。仅诊断用，发布不影响语义（`#[cfg(feature="sampler")]` 外壳）。
- 未解 meta worklist（A-2）：Machine.unsolved（machine.rs:563-575 注释、621/636 初始化、653 清空、663 remove_unsolved）+ metas 表严格同步 + run_pure_probe 回滚两表同换（machine.rs:2195-2199）；参考版仍是后缀扫（unification.rs:451-456）——性能面孪生领先。
- fresh_meta close 关闭化：见 §4.5/§4.6；README 内存/耗时数字 [未核实]（禁跑）。
- 参考版 O(D²) 修复延续：global_names 归 Infer（mod.rs:455-464）、locals Rc、close_ty 引用（syntax.rs:9-44）——L09 已做，L10 只是 Rc<Val> 化后同步调整。
- 热路径 clone 债：trait_wrap 每调用 clone trait_definition（elaboration.rs:1011-1012 TODO）；Synth::new_subgoal 每子目标 clone 实例表（typeclass.rs:299；TODO: local instances 亦未做，298）。
- 版本/提交层面：L10 目录在初建后经历多轮后续优化（ad412abd 显式替换、f32734c6 FxHashMap、aafa5ed8 评审修复、9b37c278 覆盖跳过、f2e28d50 fresh_meta 修复），本对的"L09 现状"同样被后续回移过（如 git 09b9ee8d 把逐臂下钻回移 L09）——导致 README/history 口径与当前代码错位（[git 事实]）。
- 残留：trait_wrap 内 `//TODO: can remove this clone?`（elaboration.rs:1012）、`//TODO: if traits.len() > 1, return err`（1080）、to_typ 的 `//TODO:`（typeclass.rs:58）；无 .bak 文件；debug 函数保留于孪生 machine 而非参考版。

### 9. 标题噪声排除说明

- README H1 从 `# L09：MLTT 切片…` 改为 `# L10：trait / typeclass 实例求解`（纯标题）。
- 路径/工具链改名：L09_mltt→L10_typeclass（所有 use/模块路径）、l09bench→l10bench、tests/l09_fast_parity→l10_fast_parity；这些 churn 不计入实现差异。
- 注释层名回指：孪生头注"L09 冠军配方向 typeclass 层的移植"（bump_spine_iter.rs:1-12）、"L09 才是仅 Rigid 卡"（44-48）、"L11 同款"（elaboration.rs:364）、"参考版 = L09 的 init 时期架构 + trait"（bump_spine_iter.rs:9-12）——属跨层对照/历史注记，不是本对新增机制。
- bench 头注与 src/bin 层名（l10bench）变化：属表层标签，未计入 §3 语言面。
- 孪生模块拆分（2026-09-23）是**同一层内的文件组织搬运**（bump_spine_iter.rs:76-112 自证"纯机械搬运"），不计为 L10 相对 L09 的机制增量；与本对真实增量的区分见 §4.6。

### 10. 证据锚点表

| # | 断言 | 锚点 |
|---|---|---|
| 1 | 新增参考版求解器文件 430 行 | src/L10_typeclass/typeclass.rs:138（Synth）、:398（match_typ） |
| 2 | 新增孪生 typeclass 307 行，复用参考版 Synth | src/L10_typeclass/bump_spine_iter/typeclass.rs:14、:32/86/105 |
| 3 | 删除孪生 debug.rs，内容并入 machine | src/L09_mltt/bump_spine_iter.rs:92；src/L10_typeclass/bump_spine_iter/machine.rs:3232、:3265 |
| 4 | twin machine +1587 | .deltawork/pairs/L09--L10.numstat.tsv（2118/531 行）；src/L10_typeclass/bump_spine_iter/machine.rs:52、:1199、:2259 |
| 5 | 参考版 Val→Rc<Val> | src/L09_mltt/mod.rs:159-160 → src/L10_typeclass/mod.rs:154-155 |
| 6 | Val 内部 Rc<Vec>→Vec | src/L09_mltt/mod.rs:182-192 → src/L10_typeclass/mod.rs:177-189 |
| 7 | eval/force/unify 签名 Rc 化 | src/L10_typeclass/mod.rs:590（force）、:854（eval）、unification.rs:605 |
| 8 | Cxt 收 Rc 且删 bind_slots | src/L10_typeclass/cxt.rs:112、:139；src/L09_mltt/cxt.rs:191-207 |
| 9 | SpecSolve 去 solvable | src/L09_mltt/unification.rs:16-20 → src/L10_typeclass/elaboration.rs:16-23 |
| 10 | 可解集白名单消费点删除 | src/L09_mltt/unification.rs:607/621；src/L10_typeclass/elaboration.rs:137-140 |
| 11 | pattern_match 构造 SpecSolve 变化 | src/L09_mltt/pattern_match.rs:172-174、:272-274；src/L10_typeclass/pattern_match.rs:174 |
| 12 | trait 声明脱糖 | src/L10_typeclass/elaboration.rs:624-658、:626（Self）、:628-631（outParam） |
| 13 | impl 登记实例 | src/L10_typeclass/elaboration.rs:535、:582-589、:595-620 |
| 14 | 实例 dependencies 恒空（无 where） | src/L10_typeclass/elaboration.rs:584 |
| 15 | trait 求解触发点 | src/L10_typeclass/mod.rs:573；elaboration.rs:367；unification.rs:662-669、:545 |
| 16 | solve_trait Val↔Typ 桥 | src/L10_typeclass/unification.rs:467-508（482-499） |
| 17 | solve_multi_trait 扫未解 meta | src/L10_typeclass/unification.rs:450-465 |
| 18 | UnifyError::Trait 与错误直出 | src/L10_typeclass/mod.rs:430-433、:1112 |
| 19 | trait_wrap 脱糖与 no object | src/L10_typeclass/elaboration.rs:1009-1103、:1011-1012（clone TODO）、:1086-1102 |
| 20 | Synth Prolog 三栈/effort panic | src/L10_typeclass/typeclass.rs:138-153、:219-224、:310-354 |
| 21 | outParam 掩码与 Any 通配 | src/L10_typeclass/unification.rs:482-488；typeclass.rs:413 |
| 22 | trait/impl 语法解析 | src/L10_typeclass/parser/mod.rs:698、:722、:731-744、:756 |
| 23 | lex 未变、关键字早已存在 | .deltawork/pairs/L09--L10.files.tsv（lex unchanged）；src/L10_typeclass/parser/lex.rs:124-126 |
| 24 | `this` 与多段投影新增 | src/L10_typeclass/parser/mod.rs:329-330、:340-347；src/L09_mltt/parser/mod.rs:340-347 |
| 25 | is_trait 字段穿参 | src/L10_typeclass/parser/syntax.rs:64-70；mod.rs:177-189 |
| 26 | Decl/DeclTm 新变体 | src/L10_typeclass/parser/syntax.rs:192-204；mod.rs:49-54 |
| 27 | Pattern::Any Span<bool> | src/L10_typeclass/parser/syntax.rs:19；parser/mod.rs:549 |
| 28 | neutral global 载体更换 | src/L10_typeclass/mod.rs:480、:860-863、:962-971（对照 README:110 旧锚点） |
| 29 | 孪生物化 neutral_of 仍保留 | src/L10_typeclass/bump_spine_iter/typeclass.rs:226-232；rename.rs:537 |
| 30 | fuel API 重构与烧点扩面 | src/L10_typeclass/mod.rs:449、:548、:557、:596；unification.rs:607；src/L09_mltt/mod.rs:475/530/592 |
| 31 | 孪生 PM_FUEL 可见性/pub | src/L10_typeclass/bump_spine_iter/force.rs:155-161；src/L09_mltt/bump_spine_iter/force.rs:102-115 |
| 32 | 孪生 fresh_meta 关闭化 | src/L10_typeclass/bump_spine_iter/machine.rs:1779、:1832、:1988 |
| 33 | 孪生探针设施 | src/L10_typeclass/bump_spine_iter/machine.rs:45、:52、:416/470/512；env.rs:36-37 |
| 34 | 孪生 unsolved worklist | src/L10_typeclass/bump_spine_iter/machine.rs:563-575、:663 |
| 35 | 孪生 trait 臂/trait_err | src/L10_typeclass/bump_spine_iter/machine.rs:1199-1206、:1273、:1305-1312、:3003、:3043、:2843-2851 |
| 36 | 孪生 trait_wrap | src/L10_typeclass/bump_spine_iter/machine.rs:2259、:2574-2598 |
| 37 | 测试计数 L09→L10 | src/L09_mltt/mod.rs:1192-1551（7 个 #[test]）；src/L10_typeclass/mod.rs:1267-2260（20 个） |
| 38 | tests/ 新增 parity 套件 | tests/l10_fast_parity.rs:1-7（头注）、:231、:805、:1024、:1173 |
| 39 | README 过期测试数 | src/L10_typeclass/README.md:354-360、:364-365 |
| 40 | README 决策树声称与当前 L09 矛盾 | src/L10_typeclass/README.md:120；src/L09_mltt/pattern_match.rs:84、:448（git 09b9ee8d 回移） |
| 41 | README (Obj,Obj) 恢复项不成立 | src/L10_typeclass/README.md:90；src/L09_mltt/unification.rs:593；src/L10_typeclass/unification.rs:753 |
| 42 | 参考版 fresh_meta 立即试解 vs README 推迟 | src/L10_typeclass/README.md:30-33；src/L10_typeclass/mod.rs:569-586 |
| 43 | impl 类型参数泄漏/close 债注记 | src/L10_typeclass/README.md:301-330（[未核实]，未跑测） |

### 11. 给 Lead 的一句话

L10 是"trait/typeclass 纯增量 + 参考版 Rc<Val> 跨切面重构 + 可解集白名单删除"的混合层，功能连续但文档声称（决策树、(Obj,Obj)、测试数、行号）与当前树多处不符，需在总表标注。

## 7. L10 → L11：宏（macro_rules）+ 名字世界第二次换回 decl 表

> 单元 delta-l10-l11 ｜ 数据源 .deltawork/pairs/L10--L11.{diff,files.tsv,numstat.tsv,symbols.tsv}、.deltawork/presence-matrix.tsv、.deltawork/inventory/* ｜ 核对时点 HEAD 0464150c（行号均按当前工作树 read/grep 实测；口径：行数 = git 物理行，测试数 = 静态 \#[test] 计数）

### 0. 结论摘要

- **性质**：L11 = L10 复制 + 三块实增量：①parser 内解析期 `macro_rules` 宏系统（新文件 + 解析器 883→2408 行）；②全局名字世界从"大下标哨兵"换成**名字键 decl 表**（`Tm::Decl`/`Val::Decl`，1919810 哨兵消失）；③参考版整体 `Rc = Arc` 化 + 名字表/decl 表持久化 + preprocess/pretty 单遍重写。孪生净 -523 行，主要是删 L10 临时探针（探针/计时/Atomic 命中 374 行→2 行）。
- **链在文件级连续**：27 个旧文件全部保留、1 个新增（parser/macros.rs），无删除文件；§2 规模 +2853 行与 BRIEF 一致。
- **链在"L10 后补补丁"处不连续（本单元最重要发现）**：L10 在 2026-09-20/21 之后打的一批补丁没有回传 L11——参考版 `bench_check/bench_check_nf/tm_size_ref` 被删（src/L10_typeclass/mod.rs:1161/1213/1227）；孪生 `unsolved` worklist 优化被删、退回 `metas[m..]` 后缀扫（src/L10_typeclass/bump_spine_iter/machine.rs:566-575,663 → L11 src/L11_macro/bump_spine_iter/typeclass.rs:24-48）；`Val::to_typ` 的 flat_map 刻意语义被换回 Option 收集（src/L10_typeclass/typeclass.rs:19 长注释明言"勿修"，L11 src/L11_macro/typeclass.rs:19-25 是另一套）。
- 宏在 parser 内展开，**类型检查器看不到宏**（AST 只有展开结果）；LSP 数据 `MacroExpansionInfo` 在本层只写不读（消费者在 src/lib.rs:2975/3009，属 L13）。
- 守卫新增：`MAX_MACRO_EXPANSION_DEPTH = 256`（src/L11_macro/parser/mod.rs:140）+ RAII 深度守卫（:148-169）；宏表/重解析零消费守卫（src/L11_macro/parser/macros.rs:145-162）。
- README 声称失真两类：§2 匹配编译器"L11 是五层第一个落地层"与代码不符（L10 已是逐臂下钻，无决策树符号）；§6 测试数 29/48 实测 33/52。

### 1. 规模与文件级变化

口径：.deltawork/pairs/L10--L11.files.tsv 逐文件 physical lines 合计 **16666 → 19519（净 +2853）**，与 BRIEF §2 合计一致；分栏按 BRIEF §2：参考版 5631→7093（+1462）、parser 1494→3408（+1914）、孪生 9541→9018（-523）、README 377→344（-33）。

| 文件 | 状态 | A→B 行数（files.tsv） | churn +/-（numstat） | 一句话性质 |
|---|---|---:|---|---|
| parser/macros.rs | **added** | –→358 | +358/0 | 宏匹配器/转写器/规则数据结构，全新 |
| parser/mod.rs | changed | 883→2408 | +1674/-149 | 宏定义+展开、表达式 bp 解析器、语句块/Expr 片段、LSP 展开记录、9 个测试 |
| mod.rs | changed | 2279→2994 | +1293/-578 | Arc/Decl 类型、DeclTm/PrimFunc、Decl 臂、declb、测试重组 |
| cxt.rs | changed | 194→618 | +481/-57 | 共享名字轨迹表、Rc<Decl>、5 个 builtin、lookup_src/clone_without_src_names、in-place 写 |
| elaboration.rs | changed | 1104→1249 | +397/-252 | infer_owned/in-place、trait 诊断细化、def 臂 pretty 收缩 |
| pattern_match.rs | changed | 565→604 | +348/-309 | 嵌套覆盖记账：NestedCheck→PendingNode 两段式 |
| pretty.rs | changed | 255→318 | +214/-151 | ShowS 闭包链→单输出缓冲增量写 |
| syntax.rs | changed | 44→77 | +57/-24 | Locals::update_at/update_by_cxt（旧 update_cxt 载体） |
| unification.rs | changed | 760→821 | +178/-117 | 全部 API 加 &Decl（decl 世界贯穿） |
| typeclass.rs | changed | 430→412 | +12/-30 | to_typ 加 Val::Decl 臂、class_instances 公开、SumCase 臂变化 |
| parser/syntax.rs | changed | 205→236 | +39/-8 | Raw::app/app_impl/to_span、Pattern Display |
| twin/machine.rs | changed | 3716→3085 | +816/-1447 | 删探针/global 哨兵，decl 表贯穿 |
| twin/typeclass.rs | changed | 307→227 | +62/-142 | 删 solve_trait_ref_inner/neutral_of/unsolved worklist 用法 |
| twin/{eval,force,entry,env,unify,compiler,bench_src,syntax,subst,rename,quote,spine,bump_spine_iter.rs} | changed | 见 files.tsv | 合计 +约 300 | decl 贯穿、PrimId、PM_FUEL、DECLB_CACHE、bench 负载 |

- **added**：`src/L11_macro/parser/macros.rs`（唯一新增文件）。
- **removed**：无。
- L10 的 `bump_spine_iter/typeclass.rs` 的 `solve_probe` 探针、`GLOBAL_BASE=1919810` 常量在 L11 孪生整体消失（src/L10_typeclass/bump_spine_iter/machine.rs:45,50-52 → L11 无；grep 全孪生仅 2 处 `eprintln!("TRACE")`）。

### 2. 标题宣称的增量：声称 vs 实现

| README 声称（L11_macro/README.md） | 实现锚点 | 判定 |
|---|---|---|
| 宏在 parser 内处理，`macro_rules` 声明点登记规则表，调用点 `p_raw` 展开（:24-25, :1310） | src/L11_macro/parser/mod.rs:1310-1395（宏优先、失败回退表达式）；src/L11_macro/parser/mod.rs:2098+（声明级） | ✅ 一致 |
| `MacroState` 三元组（:24, :134） | src/L11_macro/parser/mod.rs:134（错累积+宏表+`MacroExpansionInfo` 表） | ✅ 一致（行号精确） |
| `MacroExpansionInfo` 记调用点 span/展开文本/def 位置供 goto-definition（:38-41） | src/L11_macro/parser/mod.rs:9-29（结构）、:1333-1343/:1480/:2129（三处写入） | ⚠️ 本层只写不读；唯一消费者是 L13 的 src/lib.rs:2975/3009 |
| 深度守卫 256、RAII、超限推解析错误（:42-47） | src/L11_macro/parser/mod.rs:140,148-169,172-183；测试 tests/l11_fast_parity.rs:608 | ✅ 一致 |
| 直接 token 拼接（splice）不再"序列化→重词法"（:34-37） | src/L11_macro/parser/mod.rs:227-237（归一化）、:247-324（拼接）；旧 owned 路径仍存 src/L11_macro/parser/macros.rs:261-323 | ✅ 主路径一致；⚠️ 双实现并存（见 §4.7） |
| `#[macro_export]` 声明点解析（:48） | src/L11_macro/parser/mod.rs:2040-2046；标记写 `__exported__` 哨兵键 :2076 | ⚠️ 只写不读（L11 内无消费者；L12/L13 才过滤） |
| decl 表世界、`Rc<Decl>` 共享、1919810 哨兵不存在（:5-9, :57-76） | src/L11_macro/mod.rs:20,22,208,858；src/L11_macro/cxt.rs:92；L10→L11 删除点：src/L10_typeclass/mod.rs:412-416,516 | ✅ 一致（架构演进） |
| 5 个带类型 builtin（:77-81） | src/L11_macro/cxt.rs:97-161（5 实现）、:164-411（注册）、src/L11_macro/mod.rs:64（PrimFunc） | ✅ 一致；⚠️ 两处 fallback 错指 change_mutable（:129,:159） |
| `Rc<Decl>` 化后 struct/macro 负载 3.2–3.5×（:70-76） | src/L11_macro/cxt.rs:86-92（注释+字段）、:488-508（make_mut 就地） | ✅ 机制在；数字未复测 |
| **§2 匹配编译器"L11 是五层第一个落地层"（:12, :105）** | L10 已是逐臂下钻：src/L10_typeclass/pattern_match.rs:86(probe_accessible)/:246(check_pm_final)/:411(walk_pat)，全层无 compile_aux/MatchContext | ❌ **与实现不符**：L11 真实增量只是嵌套覆盖记账重构（L10 :40/:53/:299/:341 → L11 :46/:59/:277/:596） |
| 参考版 `no_metas` 为 quote 版无 visited（:289-292） | src/L11_macro/mod.rs:98-116；L10 同（symbols 无变化） | ✅ 一致（继承项，非增量） |
| 测试 29 个（mod 19+parser 9+lex 1）、parity 48（:318-325） | 实测 `#[test]`：mod.rs 23 + parser/mod.rs 9 + parser/lex.rs 1 = **33**；tests/l11_fast_parity.rs 19 → 合计 **52** | ❌ 数字过期（mod.rs 多发 4 个；parser 行数 9 正确） |
| §5 "参考版无 bench 口径：bench_check_nf 缺失"（:309） | L10 有：src/L10_typeclass/mod.rs:1213/1227（另 :1161 tm_size_ref）；L11 全无；孪生仍在：src/L11_macro/bump_spine_iter/entry.rs:336,345 | ✅ 自认，但**这是相对 L10 的口径回退**，不是天生缺失 |

### 3. 语言/语法/类型系统/内建/LSP 面增量

| 增量 | 实现锚点 | 说明 |
|---|---|---|
| `macro_rules` 声明语法 | src/L11_macro/parser/mod.rs:2049-2096（`p_macro_def`：规则 `(匹配器) => {转写器}` 用 `;` 分隔）、:1911-1939（平衡括号匹配器） | Verilog 兼容 token（`(`/`)`/`;`/`,` 等）被加进匹配器 token 集，:1886-1896 |
| 匹配器代数 | src/L11_macro/parser/macros.rs:11-33：Token / Metavar{fragment} / Many0 / Many1 / Optional / Sequence | 分隔符重复仍注释禁用（:24-30） |
| 片段种类 | src/L11_macro/parser/mod.rs:1823-1838：`ident`/`raw`/`params`，其余标识符走 **命名片段 `Name`**（读别的宏的规则表，src/L11_macro/parser/macros.rs:82-126） | 命名片段是语句块 `Expr` 展开的载体 |
| 转写器代数 | src/L11_macro/parser/macros.rs:237-257：Basic/Sequence/Group/BuiltIn（内建 `stringify`） | Group 重复按"元变量被引用集"选表（:286-309） |
| 内建 `stringify` | src/L11_macro/parser/mod.rs:432-...（注册一条无文本定义的 MacroRule，def_* 全 None，宏名行号规则 src/L11_macro/parser/macros.rs:348-358） | 验证 README :32-33 声称 |
| 表达式/声明调用点 | src/L11_macro/parser/mod.rs:1310-1395（表达式位）、:2098-2186（声明位） | 展开结果回灌 `p_raw`（:1350），非文本往返 |
| 语句块 / `module` 宏面 | src/L11_macro/parser/mod.rs:1447（`p_expr_block_stmt`）、:1625（`p_block_body`）、:1274（match 臂块体）、:1410（def 体块） | 通过 `Expr` 命名片段逐语句转写；有 `Expr` 规则才开，否则拒绝（注释 :1438-1441） |
| Verilog/HDL 兼容语法痕迹 | src/L11_macro/parser/mod.rs:1767（`always @ ( posedge $clk )`）、:1886（`module (...)`）、:88（`impl IMasterSlave`） | L11 层无 prelude 提供这些宏；测试里自建 `module`/`Expr` 宏（src/L11_macro/mod.rs:2654-2671） |
| 后缀括号消歧 / spine 逃逸 | src/L11_macro/parser/mod.rs:946（`SPINE_ESCAPE`）、:948、:955 | README 未记；parity 有 `parity_spine_escape_juxtaposed_paren`（README :239） |
| 手写优先级解析器 | src/L11_macro/parser/mod.rs:709（`expr_bp`）、:873（`expr`）、:877-900（prefix/postfix/infix binding power） | L10 解析器无这些符号（symbols.tsv 全为 +） |
| Span 精确化 | src/L11_macro/parser/syntax.rs:102-129（`Raw::to_span` 覆盖 Lam/Pi/Let）、:96/:99（`app`/`app_impl`） | 支撑宏 span 保持测试 src/L11_macro/parser/mod.rs:2333/2362 |
| LSP 观察表 | src/L11_macro/mod.rs:498-499（hover/completion 表）、:500-529（`collect_observations` 开关）、src/L11_macro/elaboration.rs:305/:829/:836/:1050（条目用 `clone_without_src_names`） | 新增"关收集"路径：hover 条目 clone Cxt 会钉住 decl 表 Rc、毁掉 in-place 写（src/L11_macro/mod.rs:500-503 注释） |
| 类型类面 | src/L11_macro/typeclass.rs:24-25 加 `Val::Decl` 两臂、:130 `pub class_instances`；src/L11_macro/elaboration.rs:387-429 细化诊断 | 与 L10 语义有出入（§6） |
| 泛型坑位 | src/L11_macro/mod.rs:461 起 `HashMap = rustc_hash::FxHashMap`（decl 表与 hot map 全 FxHash，键短字符串） | 性能项，不是语法面 |
| 语法面未变 | parser/lex.rs 406→406（unchanged）；但 lexer 早已定义 `MacroKeyword/PackageKeyword/ImportKeyword`（src/L10_typeclass/parser/lex.rs:20-23,113-129） | 词法先于语法就绪；L11 只用 MacroKeyword，Package/Import 仍悬空 |

### 4. 核心机制与实现性改动（按子系统）

#### 4.1 全局名字世界：Infer.global 哨兵 → 名字键 decl 表
- A（L10）：全局层 = `global_idx + 1919810`，`fake_bind` 写 `Infer.global`，eval 命中 `Val::Rigid(>=BASE)`（src/L10_typeclass/mod.rs:412-416,514-516,858-860 一带；孪生 `GLOBAL_BASE` src/L10_typeclass/bump_spine_iter/machine.rs:45）。
- B（L11）：`type Decl = HashMap<String,(Span,Rc<Tm>,Rc<Val>,Rc<Ty>,Rc<VTy>)>`（src/L11_macro/mod.rs:22），`Tm::Decl(name)`/`Val::Decl(name,spine)`（src/L11_macro/mod.rs:75,208）；eval 查表、未登记卡 Decl（src/L11_macro/mod.rs:858）；`Cxt.decl: Rc<Decl>`（src/L11_macro/cxt.rs:92）；孪生 `Rc<Decls>` 写时复制（src/L11_macro/bump_spine_iter/env.rs:19,31）。
- 后果：删掉下标边界/下溢整套守卫（孪生注释 src/L11_macro/bump_spine_iter/machine.rs:61-64 明言"无相应下溢边界"）；递归 def 靠 `fake_bind` 插 Decl 存根（src/L11_macro/cxt.rs:488-515）+ 检查后 `decl_mut` 静默覆盖（src/L11_macro/cxt.rs:551-562）；跨文件/全局名字解析变成字符串键查表。
- 换载体的连带删除：L10 的"中性 global 视图"机制 `eval_neutral`/`neutral_globals`（src/L10_typeclass/mod.rs:962-971）在 L11 删除，改由 **declb 存根表** 重求值 Match 分支体（L11 src/L11_macro/mod.rs:1023-1039；孪生 src/L11_macro/bump_spine_iter/unify.rs:154-206 带 TLS 指针键缓存）。

#### 4.2 cxt：共享名字轨迹（+424 行的主体）
- 旧（L10）：按值 BiMap，bind/define 深拷两表（O(n²)）。新（L11）：`NameState{by_name,by_lvl,trail}` + 每 Cxt `name_mark`，访问前 `unwind(mark)` 惰性回滚（src/L11_macro/cxt.rs:11-71,:448-452；bind :464-482；define :531-549）；`subst_cxt` 按轨迹改写类型包（:573-605，σ 空零开销）。
- 新增 `lookup_src`（:456-462，局部 binder 优先）、`clone_without_src_names`（:424-435，供 hover 快照不钉名字表）、`names()`（:437-446）。
- 顶层登记 in-place：`fake_bind_mut`（:488-508，`Rc::make_mut`）、`decl_mut`（:553-555）；旧 `&self` 持久包装保留（:511,:558），由 elaboration `infer_owned`（src/L11_macro/elaboration.rs:357,381,435）走快路径，`infer` 保留旧签名（:349-351）。

#### 4.3 宏解析/展开/卫生/span
- 展开算法：`splice_transcriber` 沿转写器树行走（src/L11_macro/parser/mod.rs:247-324）：元变量捕获 token **保留调用点 span/path**（:261-267）；模板字面量 token 的 span **改写为整个调用区间**（:271-276）——这是"卫生"的全部：无 gensym、无定义点解析，仅保证报错/高亮落在调用点而非定义点。
- 元变量捕获在匹配期即取调用点 token（src/L11_macro/parser/macros.rs:59-126），`$x: raw` 吃任意 raw、`$x: params` 吃 Π 绑定器串（src/L11_macro/parser/macros.rs:68-81）。
- 归一化复刻旧"序列化→重词法"：相邻 EndLine 折叠、丢 Eof（src/L11_macro/parser/mod.rs:224-237）；匹配器 `Token` 在每个 token 后吞一个 EndLine（src/L11_macro/parser/macros.rs:42-45），`p_raw` 末尾回补一个（:1356-1377），`p_decl` 只在"全 EndLine 错误"时放行（:2175-2183）——三处互补 hack，脆弱但必要（注释 :1356-1367 记录丢换行引发的残留错误）。
- 双展开实现并存：owned `MacroTranscriber::replace`（src/L11_macro/parser/macros.rs:261-323，命名片段路径 src/L11_macro/parser/macros.rs:86 用）与借用 `splice_transcriber`（src/L11_macro/parser/mod.rs:247）。前者不做"模板字面量 span 改写"，两条路径的 span 归一不一致；span 保真测试只覆盖直接调用路径（src/L11_macro/parser/mod.rs:2333,2362）。

#### 4.4 求值/quote/rename/unify 的 decl 贯穿
- `&Decl` 参数化：src/L11_macro/mod.rs:575(force)/:603(frcs)/:851(eval)/:955(quote)/:1049(nf)/:1068(unify_catch_at)；src/L11_macro/unification.rs:143,161,266,276,391,425,428,602；elaboration 全链。孪生侧等价物是 `&Cxt`/`&*cxt.decls`（src/L11_macro/bump_spine_iter/typeclass.rs:67 等）。
- `Val::to_typ` 加 Decl 臂（src/L11_macro/typeclass.rs:24-25），否则实例求解对全局头无类型；`class_instances` 提 pub（:130）供 def 臂报"available instances"（src/L11_macro/elaboration.rs:391-419）。
- 模式匹配：L11 把 L10 的 `NestedCheck` 记账改为 `PendingNode` 两段式——走查只记节点方程（src/L11_macro/pattern_match.rs:38-70,277,596），臂特化成功后以终态 σ 结算嵌套覆盖（:288 起）；`PosCover/cover_at/fmt_path`（src/L11_macro/mod.rs:142-171）两版共用；`unify_catch_at` 加显式 lvl（src/L11_macro/mod.rs:1064-1068）供延迟探测。

#### 4.5 性能/工程化重写
- `preprocess` 两遍 split+reduce（src/L10_typeclass/mod.rs:1248-1265，逐行 `a+sep+b` 折叠 O(n·行数)）→ 单遍扫描单缓冲（L11 src/L11_macro/mod.rs:1148-1258，含等字节长 `debug_assert!` :1256）。
- `pretty`：L10 `type ShowS = Box<dyn FnOnce(&mut String)>`（src/L10_typeclass/pretty.rs:8）→ L11 直接 `go(..., out: &mut String)` 增量写（L11 src/L11_macro/pretty.rs:13-19,:54-57，wrapper :303）。
- `Rc = Arc`（src/L11_macro/mod.rs:20）+ `pub mod pretty`（:17）；parser 仍用 `std::rc::Rc`（src/L11_macro/parser/mod.rs:4）——解析器单线程，无需 Send。
- decl 表/名字表/宏表/规则表全部 Rc 化 + `Rc::make_mut` 增量插入（src/L11_macro/parser/mod.rs:129-134 注释、:2076/:2090；src/L11_macro/cxt.rs:497,554）。
- 双保险守卫：unify fuel 4096（src/L11_macro/mod.rs:489,505-548）+ 宏深度 256；宏 Many0/Many1 零消费守卫（src/L11_macro/parser/macros.rs:145-162,171-174）。

### 5. 参考版 ↔ 孪生同步差异

| 项 | 参考版 | 孪生 | 同步? |
|---|---|---|---|
| decl 表世界 | `Cxt.decl: Rc<Decl>`（src/L11_macro/cxt.rs:92） | `Cxt.decls: Rc<Decls>`（src/L11_macro/bump_spine_iter/env.rs:31；src/L11_macro/bump_spine_iter/machine.rs:61-64） | ✅ 同构 |
| builtin 5 个 | `Rc<dyn Fn>` PrimFunc（src/L11_macro/mod.rs:64；src/L11_macro/cxt.rs:97-161） | `PrimId` 枚举逐句移植（src/L11_macro/bump_spine_iter/syntax.rs:17；twin 注释 :25-34） | ✅ 语义对位 |
| 名字表 | 共享轨迹 + name_mark 惰性回滚（src/L11_macro/cxt.rs:11-71） | **随 Cxt 克隆整表**（src/L11_macro/bump_spine_iter/machine.rs:48-59 注释自述"bind/define/fake_bind 克隆整表插入"） | ❌ 参考版新优化未跟（README :194-199 称"两版同构"失真） |
| trait 求解扫描 | `solve_multi_trait` 走 `meta` 表后缀（typeclass 侧） | L10 的 `unsolved` worklist 被删，退回 `metas[m..]` 后缀扫（L11 src/L11_macro/bump_spine_iter/typeclass.rs:24-48） | ❌ **相对 L10 回退**（src/L10_typeclass/bump_spine_iter/machine.rs:566-575,660-663） |
| declb 分支重求值 | 每次重建（src/L11_macro/mod.rs:1023） | TLS 指针键缓存 `DECLB_CACHE`（src/L11_macro/bump_spine_iter/unify.rs:166-206，unsafe transmute 'static） | ✅ 同构语义，孪生多一层缓存/风险 |
| 精化燃料 | `UNIFY_FUEL`（src/L11_macro/mod.rs:489） | `PM_FUEL` thread_local + `pm_fuel_exhausted`（src/L11_macro/bump_spine_iter/force.rs:166-190） | ✅ 对位 |
| bench 口径 | `bench_check/bench_check_nf` **已删**（src/L10_typeclass/mod.rs:1213/1227） | 保留（src/L11_macro/bump_spine_iter/entry.rs:336,345） | ❌ 不对称（README :247-249 自认） |
| 共用件 | parser / pretty / preprocess / trait `Synth`（twin 直接 `use crate::L11_macro::typeclass::{Synth}`，src/L11_macro/bump_spine_iter/typeclass.rs:14） | 同 | ✅ |
| 宏/LSP 记录 | `MacroExpansionInfo` 三处写入；hover/completion 表 | 共用同一 parser，无独立记录；无 LSP 表 | ✅ 设计如此 |

### 6. 回退/丢失/弱化清单

| A（L10）中功能/机制/守卫/测试 | B（L11）状态 | 锚点 | 影响 |
|---|---|---|---|
| 参考版 `bench_check`/`bench_check_nf`/`tm_size_ref` | 删除 | src/L10_typeclass/mod.rs:1161,1213,1227；L11 全层 grep 无 | 参考版 basic 只能计时全流程 `run`，与孪生 fast 口径不可比（README :247-253,309 自认） |
| 孪生 `unsolved` worklist + `remove_unsolved`（A-2 优化，避免 metas 全后缀扫） | 删除，退回线性后缀扫 | src/L10_typeclass/bump_spine_iter/machine.rs:566-575,660-663 → L11 src/L11_macro/bump_spine_iter/typeclass.rs:24-48 | trait 密集负载每轮多扫已解槽 [推断]：L10 注释记 traitchain 一轮 3076 次调用、Σscan 2.1M |
| `Val::to_typ` 的 flat_map 刻意语义（"勿修"，允许 `List[?m]` 接收者一阶匹配） | 改为 `map(...).collect::<Option<Vec<_>>>()?`；`SumCase` 由 None 变 `Some(Typ::Val(case_name))` | src/L10_typeclass/typeclass.rs:19 起长注释 vs L11 src/L11_macro/typeclass.rs:19-25,30-40 | 语义/诊断口径回退：L11 可能拒绝 L10 接受的接收者 trait 调用；构造子值参与实例匹配是新形态 [推断，未跑测] |
| `eval_neutral` / `neutral_globals`（中性 global 视图） | 删除，换成 declb 存根表 | src/L10_typeclass/mod.rs:962-971 vs L11 src/L11_macro/mod.rs:1023-1039 | 非功能丢失（机制换载体）；但 declb 逐次重建在参考版是 O(D)（孪生才有缓存） |
| parser 的 impl 头解析测试 3 个（`test_impl_for_parses`/`test_inherent_impl_parses`/`test_bad_decl_reported_prefix_kept`） | 删除；parser 测试改为 9 个宏/span/parser_test 用例 | symbols.tsv A 侧 src/L11_macro/parser/mod.rs:838,852,865 | impl 解析回归不再有钉（宏测试不覆盖） |
| L10 的 `Probe/MatchContext` 类诊断能力（README 自述决策树免费提供 usefulness 分析） | 无（L10 已先删） | L10 pattern_match.rs 无 compile_aux/MatchContext（grep 0） | 非本对增量，属 L09→L10 已发生的诊断收窄 |
| `PackageKeyword/ImportKeyword` 语法 | 词法有、语法未接线（只出现在错误恢复同步集 src/L11_macro/parser/mod.rs:60-64） | src/L10_typeclass/parser/lex.rs:22-23 vs L11 src/L11_macro/parser/mod.rs:61-63 | 悬空语法面（L13 才用），不构成回退 |

### 7. 测试与文档变化

- **lib 测试**：L10 mod.rs 20 + parser 4 + lex 1 = 25 → L11 23 + 9 + 1 = **33（+8）**。L11 新增 `test8/test9/test10/test11`、`test_nested_coverage_gap(:2694)`/`gap3(:2719)`/`vec_len2_ok(:2749)`、`test_stale_solvable_order_independent(:2775)`、`test_ctor_wf_*(:2809/2828/2852)`、`test_pm_*(:2886/2912/2941/2973)`；删除 `test1/check_err/test_nested_coverage_complete/test_nested_refine_absurd_ok`。parser 新增 5 个宏/span 测试（:2319/:2333/:2362/:2391/:2402）+ `test/test1/test2/test3`。
- **双 oracle**：tests/l11_fast_parity.rs 19 个 `#[test]`；`norm_err` 归一化 span 数字 + meta 编号 `?N`（:48-50，README :231-234 声称核对一致）；宏/全局 parity `:322`、自递归深度上限 `:608`、评审钉 `:752`（README :236-239 声称全部存在）。
- **README 重写**：377→344 行（+318/-351，几乎整篇改写）；H1 由 "trait/typeclass 实例求解" → "宏（macro_rules）与 decl 表世界"。
- **README 行号/数字失真清单（均可核）**：
  | README 位置 | 声称 | 实测 |
  |---|---|---|
  | :77-80 | builtin 在 src/L11_macro/cxt.rs:28-92 | 实现 src/L11_macro/cxt.rs:97-161，注册 :164-411 |
  | :65-69 | fake_bind src/L11_macro/cxt.rs:392-408、decl :438-454、subst_cxt :456-483 | fake_bind :511、decl :558、subst_cxt :573-605 |
  | :30-33 | MacroMatcher src/L11_macro/parser/macros.rs:10-27 | :11-33 |
  | :92-96 | Def 臂 body_pretty src/L11_macro/elaboration.rs:421、typ_pretty :420 | :432（`String::new()`）、:431 |
  | :98-101 | solve_multi_trait src/L11_macro/elaboration.rs:372、诊断 :375-418 | :383、:387-429 |
  | :61-63 | eval 未登记卡 Val::Decl src/L11_macro/mod.rs:844 | :858 |
  | :194-199 | Decls/DeclEntry/PM_FUEL/DECLB_CACHE 在 README 原文 `bump_spine_iter.rs:635`/`623-631`/`4505-4511`/`1020-1049`（均为拆分前单文件行号） | bump_spine_iter.rs 仅 171 行；实际 src/L11_macro/bump_spine_iter/env.rs:19,31；src/L11_macro/bump_spine_iter/force.rs:166；src/L11_macro/bump_spine_iter/unify.rs:166（2026-09-23 拆分后未同步） |
  | :318-325 | 29/48 测试 | 33/52 |
- **文档缺口（非失真）**：parser / Verilog 兼容 / 语句块 / spine 逃逸 / 宏双实现 / `__exported__` 哨兵 / TRACE 残留均未在 README 出现。

### 8. 工程性/性能/健壮性改动

| 项 | 变化 | 锚点 | 影响 |
|---|---|---|---|
| L10 临时探针整体删除 | 孪生 `solve_probe`（ON/Cnt/TGuard/ItemGuard/B_*/计时）删除；命中数 374→2 | src/L10_typeclass/bump_spine_iter/machine.rs:50-52,56-58,228,330-395 vs L11 twin 全目录 grep | 生产代码变干净；保留的 2 处 `eprintln!("TRACE ...")` 仍存在（env `L11_LOOPCAP` 门控）src/L11_macro/bump_spine_iter/machine.rs:1384-1386,:1508 |
| preprocess 单遍化 | O(字节×行数)→O(字节)，输出等字节长 | L11 src/L11_macro/mod.rs:1148-1258 vs src/L10_typeclass/mod.rs:1248-1265 | LSP 每次按键跑 2 遍，正向 |
| pretty 增量写 | ShowS 闭包链 → 单 String 缓冲 | src/L10_typeclass/pretty.rs:8 → L11 src/L11_macro/pretty.rs:54-57,303 | 消除深嵌套 O(n²) 拼接 |
| 名字表持久化 | 共享表 + 轨迹回退，bind/define O(1) | src/L11_macro/cxt.rs:11-71,448-452,464-549 | 参考版 struct/macro 负载主收益（README 声称 3.2–3.5×） |
| decl 表 COW 就地写 | `Rc::make_mut` + `infer_owned` 接管所有权；`collect_observations` 关表避免 Cxt clone 钉 Rc | src/L11_macro/cxt.rs:488-508,:553-555；src/L11_macro/elaboration.rs:357,381,435；src/L11_macro/mod.rs:500-529 | 顺序 def 路径 O(1) 写；LSP 路径仍退化深拷（有意） |
| 宏表 Rc 化 | 展开期 `state.1.clone()` 由整表深拷降为 Rc 克隆 | src/L11_macro/parser/mod.rs:129-134,1349 | 宏重解析快路径 |
| unsafe 新增 | `DECLB_CACHE` 以 `Rc` 分配地址为键，条目 'static 存放 + 反向 transmute | src/L11_macro/bump_spine_iter/unify.rs:154-206 | ABA 由"缓存内钉住源 Rc"规避；仍是手工内存风险 |
| 健壮性缺口（新增代码） | `create_global`/`get_global` 的非字面量 fallback 返回 **change_mutable**（复制粘贴）；`get_global` 缺键 `.unwrap()` | src/L11_macro/cxt.rs:129,:157,:159 | 用户程序可触发 panic/错误语义（[可疑]，无测试覆盖） |
| 健壮性缺口（解析器） | `p_macro_transcriber_single` 手写 `len = i_back.len() - input.len() - 1 - need_remove_endline` 一类下标算术；`__exported__` 哨兵键污染宏表 | src/L11_macro/parser/mod.rs:1986,2076 | 边界输入易错；哨兵在 L11 只写不读 |
| 死代码 | `RepetitionOp` 定义后仅出现在注释代码；`MacroFragment` 半数变体被注释 | src/L11_macro/parser/macros.rs:209-213,221-233 | 未用 API，不影响行为 |
| 残留打印 | `run` 打 `> {name}`、解析错误 eprintln 式 println | L11 src/L11_macro/mod.rs:1111-1125；src/L10_typeclass/mod.rs:1134 同款 | **继承非新增**，但对 LSP/CLI 输出来说是噪声 |

### 9. 标题噪声排除说明

- 章节 H1/README 层名（L10："trait / typeclass 实例求解" → L11："宏（macro_rules）与 decl 表世界"）、路径 `L10_typeclass/→L11_macro/`、crate 名 `L11_macro`、bench 标签：全部为标题/命名噪声，已排除。
- **注释层的层名引用**不是差异：L10 代码里有"L11 已修 flat_map…"（src/L10_typeclass/typeclass.rs:19 注释）、L11 代码里有"参考版 bench_check"（src/L11_macro/bump_spine_iter/machine.rs:2926）、"L13 meta journal 同款先例"（src/L11_macro/bump_spine_iter/unify.rs:162）——这些是跨层引用注释，不代表被引用层的行为出现在本层。
- **测试源码字符串伪符号**：symbols.tsv 把 `mod.rs` 测试里的 `enum Eq`/`struct Point`/`enum HighLvl`/`struct module`（src/L11_macro/mod.rs:1950-2100,2641-2645）识别为"新增 API"，实为测试输入；删掉同位置的 `impl List[Nat]`/`run1` 亦同。已按"非 API"排除。
- 行号型噪声：README 的 `src/L11_macro/bump_spine_iter.rs:NNNN` 类锚点来自拆分前单文件时代（现文件 171 行 + 目录），属文档噪声而非代码差异（见 §7）。
- 真实增量只有 §2/§3/§4 所列：宏系统、decl 世界、Arc/持久化、preprocess/pretty、测试重组。

### 10. 证据锚点表

| # | 断言 | 锚点（仓库相对路径:行） | 覆盖 |
|---|---|---|---|
| 1 | 规模 16666→19519（+2853），28 文件仅 1 个新增、0 删除 | .deltawork/pairs/L10--L11.files.tsv（合计复算）；presence-matrix.tsv | §1 |
| 2 | 唯一新增文件 = 宏数据/展开数据结构 | src/L11_macro/parser/macros.rs:1-8 | §1 |
| 3 | parser 883→2408 行、+1525/-149 | .deltawork/pairs/L10--L11.numstat.tsv（parser/mod.rs 行） | §1 |
| 4 | 孪生 machine 3717→3086（-631），探针/global 哨兵消失 | L10 src/L11_macro/bump_spine_iter/machine.rs:45,50-52；L11 同目录无 solve_probe | §1,§8 |
| 5 | MacroState 三元组 + Rc 宏表 | src/L11_macro/parser/mod.rs:129-134 | §2,§4 |
| 6 | MacroExpansionInfo 结构与三处写入 | src/L11_macro/parser/mod.rs:9-29,:1333,:1480,:2129 | §2,§3 |
| 7 | 深度守卫 256 + RAII + 错误文案 | src/L11_macro/parser/mod.rs:140,148-169,172-183 | §2,§8 |
| 8 | 直接 token 拼接 + span 改写 | src/L11_macro/parser/mod.rs:227-237,247-324,271-276 | §2,§4.3 |
| 9 | 双展开实现并存（replace vs splice） | src/L11_macro/parser/macros.rs:261-323；src/L11_macro/parser/mod.rs:247 | §4.3,§6 |
| 10 | 宏匹配器/片段/转写器/规则结构 | src/L11_macro/parser/macros.rs:11-33,216-257,348-358 | §3 |
| 11 | 命名片段 `Name` 读别家宏表并记展开信息 | src/L11_macro/parser/macros.rs:82-126 | §3,§4.3 |
| 12 | 内建 stringify 无文本定义注册 | src/L11_macro/parser/mod.rs:432（规则 def_* None：src/L11_macro/parser/macros.rs:348-358） | §2 |
| 13 | macro_export 解析与只写不读哨兵 | src/L11_macro/parser/mod.rs:2040-2046,2076；L12/L13 才过滤（src/L12_canonical/parser/mod.rs:440-445） | §2,§8 |
| 14 | 宏定义解析（平衡括号/Verilog 兼容 token） | src/L11_macro/parser/mod.rs:1798-1838,1886-1896,2049-2096 | §3 |
| 15 | 表达式/声明双调用点 | src/L11_macro/parser/mod.rs:1310-1395,2098-2186 | §3 |
| 16 | EndLine 归一三处互补 hack | src/L11_macro/parser/macros.rs:42-45；src/L11_macro/parser/mod.rs:1356-1377,2175-2183 | §4.3,§8 |
| 17 | 语句块/Expr 片段/module 宏用例 | src/L11_macro/parser/mod.rs:1447,1625；src/L11_macro/mod.rs:2654-2671 | §3 |
| 18 | spine 逃逸 + 手写优先级解析器 | src/L11_macro/parser/mod.rs:946,948,955,709,873,877-900 | §3 |
| 19 | Raw 新构造/span 覆盖 | src/L11_macro/parser/syntax.rs:96,99,102-129；Pattern Display src/L11_macro/parser/syntax.rs:44 | §3 |
| 20 | Arc 别名 + Decl 类型 + FxHashMap | src/L11_macro/mod.rs:20,22,461 | §4.1,§8 |
| 21 | 哨兵世界删除（L10 侧） | src/L10_typeclass/mod.rs:412-416,514-516,858-860 | §4.1 |
| 22 | Tm::Decl/Val::Decl 与 eval 查表 | src/L11_macro/mod.rs:75,208,858 | §4.1 |
| 23 | L10 中性 global 视图→L11 declb | src/L10_typeclass/mod.rs:962-971；L11 src/L11_macro/mod.rs:1023-1039 | §4.1,§6 |
| 24 | 名字轨迹表/惰性回滚/持久接口 | src/L11_macro/cxt.rs:11-71,448-452,464-549,573-605 | §4.2 |
| 25 | decl 表 Rc 共享 + in-place 写 + infer_owned | src/L11_macro/cxt.rs:86-92,488-515,551-562；src/L11_macro/elaboration.rs:357,381,435 | §2,§4.2,§8 |
| 26 | 5 个 builtin 实现/注册/错 fallback | src/L11_macro/cxt.rs:97-161,164-411,129,157,159 | §2,§8 |
| 27 | 观察表开关与 clone_without_src_names | src/L11_macro/mod.rs:498-529；src/L11_macro/cxt.rs:424-435；src/L11_macro/elaboration.rs:305,829,1050 | §3,§8 |
| 28 | LSP 消费者不在本层 | src/lib.rs:2975,3009（import 于 :101） | §2,§3 |
| 29 | decl 贯穿 unify/elaboration/trait | src/L11_macro/unification.rs:143,276,428；src/L11_macro/elaboration.rs:1125（trait_wrap t_span）；src/L11_macro/typeclass.rs:24-25,130 | §4.4 |
| 30 | 模式匹配 NestedCheck→PendingNode | src/L10_typeclass/pattern_match.rs:40,53,299,341；L11 src/L11_macro/pattern_match.rs:46,59,277,288,596 | §2,§4.4,§6 |
| 31 | 嵌套覆盖判定/文案共用 | src/L11_macro/mod.rs:142-171,1064-1068 | §4.4 |
| 32 | preprocess 单遍重写 | L11 src/L11_macro/mod.rs:1148-1258（:1256 不变量）vs src/L10_typeclass/mod.rs:1248-1265 | §8 |
| 33 | pretty ShowS→增量写 | src/L10_typeclass/pretty.rs:8 vs L11 src/L11_macro/pretty.rs:13-19,54-57,303 | §8 |
| 34 | 孪生名字表未跟随参考版轨迹表 | L11 src/L11_macro/bump_spine_iter/machine.rs:48-59 vs src/L11_macro/cxt.rs:11-71 | §5 |
| 35 | 孪生 trait 扫描回退（unsolved worklist 删除） | src/L10_typeclass/bump_spine_iter/machine.rs:566-575,660-663 → L11 src/L11_macro/bump_spine_iter/typeclass.rs:24-48 | §5,§6 |
| 36 | bench 口径不对称 | src/L10_typeclass/mod.rs:1161,1213,1227；L11 src/L11_macro/bump_spine_iter/entry.rs:336,345 | §2,§6 |
| 37 | declb TLS 缓存与 unsafe | L11 src/L11_macro/bump_spine_iter/unify.rs:154-206；PM_FUEL src/L11_macro/bump_spine_iter/force.rs:166-190 | §5,§8 |
| 38 | 测试数与套件 | L11 mod.rs 23 个 #[test]（:1261 起）；src/L11_macro/parser/mod.rs:2193-2408 共 9；src/L11_macro/parser/lex.rs:326；tests/l11_fast_parity.rs:48-50,322,608,752（19 个 #[test]） | §7 |
| 39 | README 数字/行号失真 | src/L11_macro/README.md:61-63,65-69,77-81,92-101,194-199,318-325 vs §7 表实测 | §7 |
| 40 | TRACE 残留与打印噪声 | src/L11_macro/bump_spine_iter/machine.rs:1384-1386,1508；src/L11_macro/mod.rs:1111-1125（src/L10_typeclass/mod.rs:1134 同款，非新增） | §8 |

（锚点合计 40 条，覆盖 §1–§8；每条均在当前工作树用 read/grep 核对过行号。）

### 11. 给 Lead 的一句话

L11 真增量 = 解析期 macro_rules + 名字键 decl 表 + Arc/持久化重构；但 L11 整体落后于 L10 后补补丁（to_typ 语义、孪生 worklist、bench_check），且 README 把 L10 已落地的匹配编译器改写冒充为自己的首个落地层——链的断点在"L10 被后期补丁分叉"，不在 L11 自身。

## 8. L11 → L12：canonical 回填层（含嵌套覆盖精度与 parser 修复两处回退）

> 单元 delta-l11-l12 ／ 数据源 .deltawork/pairs/L11--L12.{diff,numstat.tsv,files.tsv,symbols.tsv} ／ 核对时点 HEAD 0464150c ／ 物理行口径同 .deltawork/inventory/layers-summary.tsv

### 0. 结论摘要

- **性质**：L12 是“回填型”章节——主线（逐臂匹配编译器、σ/VSub 精化、decl 表世界、trait 求解）沿用 L11；本对真正的新机制只有 3 个：**Val 级 trait 求解（删 Typ 桥）**、**Call 内联节点**、**canonical 搜索（Err 重试闭包）**，外加 SmolStr 全量迁移。层目录含 2026-09-18 之后的评审回填（commit 45330e6 / f5bbf21a / 8eff89cf 等触达 L12 文件，git log 可证），不是冻结快照。
- **最重要的 7 条**：
  1. 新增 `canonical.rs`（154 行，numstat +154）：`iddfs`/`search`，唯一调用点是 elaboration.rs:456-473 的 Err 重试闭包；预算改 1..=target_limit 逐 1 递增（canonical.rs:24）。
  2. `typeclass.rs` 删 `Typ`/`Val::to_typ` 桥（L11 typeclass.rs:9/19），求解器直接匹配 `Val`（typeclass.rs:123 `val_match`、:196 `vals_eq_ground`）。
  3. 孪生删 `bump_spine_iter/typeclass.rs`（-227 行），求解三方法/状态/Val 桥并入 machine.rs（:658/:687/:2419/:2435），模块清单少一个文件（bump_spine_iter.rs:144-156）。
  4. 新增 `Tm::Call`/`Val::Call` 内联节点（mod.rs:98/283）与 `Val::Match` 第四字段 origin（mod.rs:281）；**孪生侧无任何 Call 对位**（grep L12 bump_spine_iter 零命中）——Call 只在参考版。
  5. 匹配编译器**回退**：L11 的 `PendingNode`+节点方程（pattern_match.rs:59/188）被 L12 的 `pending_pos`+`NestedCheck(σ 快照)`（:48/:59）取代；同一 Vec 长度 2 程序由 L11 Ok 变 L12 报“缺少构造子 nil”（mod.rs:2555-2564），L11 的正向钉 test_nested_coverage_vec_len2_ok 被删。
  6. parser 丢 L11 的 SPINE_ESCAPE 单实参括号摊平修复（L11 parser/mod.rs:946-1028；L12 无此符号），L12 的 `(` 后缀分支直接折叠（parser/mod.rs:808-816）——错分组风险回归 [推断]，无 L12 测试覆盖。
  7. mod.rs -198 = 删 test9/10/11 与 nested_coverage_vec_len2_ok（4 个）加 2 个新钉、其余为 SmolStr/Error/Call 改造；README 声称 17 个 `#[test]`，实测 21。
- **链是否连续**：**不连续**。断点 3 处：嵌套覆盖精度回退（语义）、spine-paren 解析修复丢失（健壮性）、trait/outParam 回归测试删除（测试）。其余机制（σ、decl 表、fuel、LSP 表）连续。

### 1. 规模与文件级变化

总物理行 19519→19603（+84）：参考版 7093→6978（-115）、parser 3408→3609（+201）、孪生 9018→9016（-2）；rs 文件 27→27（.deltawork/presence-matrix.tsv 行）。

| 文件 | 状态 | A→B 行数 | churn +/− | 一句话性质 |
|---|---|---|---|---|
| canonical.rs | **added** | –→154 | +154/0 | 新增 canonical 搜索（iddfs/search） |
| bump_spine_iter/typeclass.rs | **removed** | 227→– | 0/227 | 求解器并入 machine.rs |
| cxt.rs | changed | 619→465 | 247/401 | 名字表 O(1) 化 + builtin 改 eval 注册 + SmolStr |
| mod.rs | changed | 2995→2797 | 675/873 | Call/Error/UnifyError/测试增删 |
| bump_spine_iter/machine.rs | changed | 3086→3360 | 619/345 | 吸收 typeclass + MetaSnap/decl 条目 |
| parser/mod.rs | changed | 2408→2592 | 420/236 | 删 SPINE_ESCAPE、加 smolstr/parser_with_macros/宏信息测试 |
| elaboration.rs | changed | 1250→1311 | 326/265 | check<CANONICAL> + iddfs 重试闭包 |
| pretty.rs | changed | 319→394 | 144/69 | 缓冲式 go + Call/indent |
| pattern_match.rs | changed | 605→506 | 150/249 | PendingNode→pending_pos（回退） |
| typeclass.rs | changed | 413→415 | 215/213 | Typ 桥删除，Val 直匹配 |
| unification.rs | changed | 822→863 | 125/84 | unify(...,fuel) + solve_trait 公开 |
| bump_spine_iter/compiler.rs | changed | 539→459 | 128/208 | PendingNode/node_indices 删除 |
| bump_spine_iter/spine.rs | changed | 170→199 | 38/9 | +MetaSnap/meta_unsolved |
| bump_spine_iter/env.rs | changed | 165→144 | 3/24 | DeclEntry/Decls 移入 machine |
| bump_spine_iter/subst.rs | changed | 242→251 | 85/76 | +ZZ_TRACE_ON 调试闸 |
| bump_spine_iter/force.rs | changed | 633→622 | 53/64 | pm_fuel_exhausted→fuel_exhausted |
| README.md | changed | 344→414 | 399/329 | 重写；行号引用大量过期 |
| parser/lex.rs | unchanged | 407→407 | 0/0 | 未动 |

- 其余小改：bench_src −1、entry +8、eval −12、quote +1、rename +8、syntax(twin) −1、unify −1、parser/macros 0、parser/syntax +17、syntax.rs +3（numstat 行）。
- 删/加是**唯一文件级断点**：twin/typeclass.rs 消失、canonical.rs 出现；没有其它文件增删。

### 2. 标题宣称的增量：声称 vs 实现

| L12 README 声称（锚点） | 实现锚点 | 判定 |
|---|---|---|
| trait 求解器 Val 级重写、移除 Typ 桥（README.md:3-6） | typeclass.rs:123/196；L11 typeclass.rs:9/19 已删 | 一致 |
| `Val::Call` 内联节点（README.md:4-5,257-260） | mod.rs:98/283；force mod.rs:718、v_app :952、quote :1147、unify unification.rs:678 | 一致（仅参考版） |
| canonical 搜索 iddfs/search，Err 重试路径专属（README.md:5-6,306-308） | canonical.rs:8/32；elaboration.rs:456-473；commit f5bbf21a | 一致（唯一调用点） |
| 参考版全面 SmolStr 化（README.md:7） | mod.rs:24 Decl 键 SmolStr；cxt.rs:81；parser 全层 | 一致 |
| 孪生 L11 冠军配方移植、Ok 输出逐字节一致（README.md:7-10,290-324） | 孪生无 Call/canonical（§5）；tests/l12_fast_parity.rs 15 例 | **部分**：剔除面上成立 |
| 匹配编译器“与 L10/L11 完全一致，三处收窄”（README.md:96-121） | 记账机制其实从 L11 PendingNode 换成 L07 式 pending_pos（pattern_match.rs:48/59） | **不一致**：本对内的机制替换未承认 |
| 孪生 PrimId“语义逐句移植 cxt.rs 的 6 个内建”（README.md:309-310） | 孪生 PrimId 仅 5 变体（syntax.rs:16；eval.rs 五臂），无 ChangeMutableDefault；模块头亦写 5（bump_spine_iter.rs:47） | **不一致** |
| “mod.rs 17 个 `#[test]`”（README.md:396） | grep 实测 21 个 | 失真（且未记删 4 加 2） |
| 层内行号引用（README.md:75/81-83/226/229-235/264-266） | cxt.rs: builtin 注册 184-249、fake_bind 345、decl 400、subst_cxt 421；mod.rs: force_arg 909、force_deep 871、UNIFY_FUEL 606、hover_table 616-617 | 过期（为 L11 行号） |
| §4.2 hover/completion 表称“增量”（README.md:264-267） | L11 mod.rs:498-528 已有同名字段/闸 | 非本对增量（是相对 L07 的增量） |

### 3. 语言/语法/类型系统/内建/LSP 面增量

- **Call 内联**：`Tm::Call(name, display_args, val_args, body)`（mod.rs:98）、`Val::Call(name, args, body)`（mod.rs:283）；force 穿透到体（mod.rs:718-720）、v_app 透明（:952）、quote 还原（:1147-1149）、rename 还原（unification.rs:391-393）、unify 两侧透明（:678-679）、pretty 臂（pretty.rs:231）。目的：def 调用被内联后仍能显示调用形态（README 称 HDL regNext 泛型的基础）。
- 口径修正：BRIEF 提示的「Call/OpCall」在本层只有 Call——`OpCall` 是 L13 才引入（src/L13_namespace/mod.rs:533），L12 全层无 OpCall。
- **Val::Match 增 origin 字段**：`Option<(SmolStr, Vec<Rc<Val>>)>`（mod.rs:281）；卡住 match 的 quote 按模式形状反查 def 名（mod.rs:524-560 `lookup_function_by_cases`/`match_has_same_patterns`）再包 `Tm::Call`（mod.rs:1187-1193）。L11 的 Val::Match 仅 3 字段（L11 mod.rs:228）。
- **meta 上下文快照**：`MetaEntry::Unsolved(闭类型, Arc<Cxt>, 原始类型)`（mod.rs:30-32），L11 仅 1 字段（L11 mod.rs:28-31）；`no_metas` 随之由返回引用改为重建 `(Cxt, Rc<Val>)`（mod.rs:102；L11 mod.rs:98）。
- **builtin**：`Cxt::new(infer)` 改为经 `infer.eval` 生成登记值（cxt.rs:184-264，`add_builtin_mut` :260），并新增第 6 个内建 `change_mutable_default`（cxt.rs:142/:238）。L11 是手写 Tm/Val 链且无该内建（L11 cxt.rs:164-200）。
- **错误面**：`UnifyError` 由 2 变体扩为 `Basic/Stuck/Trait`（mod.rs:568-572；L11 mod.rs:463-467）；`Error` 由单元组扩为 `(Span<String>, Vec<Box<dyn Fn()->Option<String>>>)`（mod.rs:583-586），Debug 保持旧渲染以稳输出（:588-595），L11 为单元组（L11 mod.rs:478-479）。
- **parser 面**：新增 `smolstr` 组合子（parser/mod.rs:581）、`parser_with_macros` 公开入口（:439）与宏展开信息来源（MacroState 的 FxHashMap，:136）；删 `SPINE_ESCAPE`/`is_spine_escape`/`strip_spine_escapes`（L11 parser/mod.rs:946/948/955）；自定义算符优先级改动：含 `:` 者 (22,21)→(2,1)，未知算符回落 None→(7,8)（L12 parser/mod.rs:925-950 vs L11:895-920）[推断：影响自定义算符表达式分组]。
- **prelude/LSP 面**：新增 `run_with_prelude`（mod.rs:1307），include_str 装载 core/data/hdl 共 24 个 .typort（:1311-1334）并用 `parser_with_macros` 解析主文件（:1358）；L11 全层无该函数（grep）。README 未提（L13 才消费，属 forward-port）。

### 4. 核心机制与实现性改动

#### 4.1 trait 求解：Val→Typ 归一化 → 直接 Val 匹配
- 口径修正：BRIEF 提示「trait 求解 Tm 级→Val 级」不准确——L11 已不是 Tm 级：L11 的求解入口接收 `Val` 再经 `Val::to_typ` 归一化成 `Typ`（L11 typeclass.rs:19-51）。本对真正的变化是**删掉 Typ 归一化，直接匹配 Val**。
- L11：`Val::to_typ` 把值压成 `Typ`（Decl/Sum 非空 spine 一律 None，L11 typeclass.rs:19-51），断言参数是 `Vec<Typ>`（:55-59），实例匹配 `match_typ`+代换 `Subst=HashMap<u32,Typ>`（:339/380），dependencies 要 apply 代换（:188-190）。
- L12：删 Typ 全族（symbols -，typeclass.rs:9/19/339/342/360/380 无对位），`Assertion.arguments: Vec<Rc<Val>>`（:13-16），一阶匹配 `val_match`（:123）：Flex 宽放、Rigid 只允许**实例侧**绑定（:142；注释说明删掉旧 `(Rigid,_)` 备选是修“目标泛型被实例吃掉”的假匹配）、Decl/Sum/SumCase/Obj/U/LiteralType 逐结构；等式 `vals_eq_ground`（:196）对 Match 比分支体且用 `Rc::ptr_eq` 判同源（:235-246）。
- 连带删：`try_answer` 由 `Assertion: PartialEq` 改结构等值（:251-258），表项查找 `find_assertion_entry` 用同一判等（:296-303）——L11 里是 derive PartialEq（L11 typeclass.rs:55-59）[事实]。
- deps 代换被删：L12 `try_resolve` 直接 clone dependencies（:289-292，注“currently always empty”），L11 有 apply_subst（:188-190）。代价：本层 where 依赖（若有）不再被代换求解；本层 impl 依赖为空，故观察面相同 [推断]。
- 孪生：删独立文件，`solve_trait_ref`/`solve_multi_trait_ref`/`TraitState`/`v_to_ref_val` 进 machine.rs（:687/:658/:2419/:2435）；实参 force 后逐项解码成参考版 `Val`，非构造子链头以 always-match Flex 占位替代旧 unreachable（:2455-2460）——健壮性提升。

#### 4.2 canonical 搜索：何时调用、扫描什么
- 入口唯一：`check` 在 def 体检查后发现未解 meta（elaboration.rs:405-477），构造 `ret` 闭包（:456-473）调 `infer.iddfs(&meta_cxt, &[oty], &meta_cxt, &oty, head, depth=5, target_limit=6, avoid_recurse=name)`，成功后还要校验 `meta_contrains` 为空（:467-472）；闭包挂在 `Error` 第二字段上（:474-476）供 LSP quickfix 重试。即：**normal run 不走、不影响 Ok 输出与判定**（README:306-308 与 twin 注释一致）。
- `search` 机制（canonical.rs:32-153）：深度/预算剪枝（:44），对目标类型剥 Π 绑定显式 lambda 名（:51-58），候选枚举 = 名字表 + decl 表，剔除 6 个 builtin/outParam/avoid_recurse（:71-79）；每候选先实例化其 Π 链、用 `fresh_meta` 造实参（:85-95），再 `refuel()` 后 `unify(...,5)`（Ok 或 Stuck 均算通）并 `check::<true>` 复检（:113-115）；成功后递归搜索剩余目标（:127-146）；失败清 `meta_contrains`（:148）。预算循环 1..=target_limit 逐 1 递增（:24-29），已修旧的 `+=2` 跳档。
- 风险/代价：每候选一次完整 check（指数式），只在 quickfix 上跑；`avoid_recurse` 用 name 粗防自递归（:71-79），源码自注 “TODO: this is incorrect”（:17/:41）。孪生不移植（bump_spine_iter.rs:29-31）。

#### 4.3 匹配编译器：L11 精确节点方程 → L12 σ 快照两段式（回退）
- L11：走查记 `PendingNode{path, head, ret}`（pattern_match.rs:59），`check_pm_final` 成功后再逐节点跑 `node_indices`（:188-204，:308 调用）用精确索引方程解槽位，覆盖判定在终态 σ 下做全量精化。
- L12：走查只记 `(path, field Sum)`（pattern_match.rs:48），臂成功后提升为 `NestedCheck{path, field_sum, sub: σ, lvl}`（:59-64，:239-246），再做逐 ctor 值级探测（`probe_accessible` :87）。臂失败丢弃记账（:217-235）。两者都叫“L07 同款”，但 L12 少了节点方程解出的索引精化。
- 后果（已钉住）：Vec 长度 2 上 `cons(h, cons(h2,t))` 的尾部索引槽不在 σ 内，nil 被保守判可达 → 报“缺少构造子 nil”（mod.rs:2528-2564）。L11 的同一程序是 Ok（diff 8646-8676 删除的正向钉 `test_nested_coverage_vec_len2_ok`，注释称“两段式结算…不产生假阳性”）。结论：**语义收窄为“拒绝运行期完备程序”**，README 自认保守（README:157-161），但未与 L11 对照。
- 孪生同步回退：compiler.rs 删 PendingNode/node_indices（symbols），`covers`/`is_catch_all` 换 SmolStr（:309/:320），新 compile/walk_pat 在 :172/:334。

#### 4.4 名字世界与 cxt（-154 的主要来源）
- L11 `NameTrailEntry{name, old_lvl, lvl, old_val}` + by_name/by_lvl 双表（L11 cxt.rs:20-70）；L12 简化为单表 `FxHashMap<SmolStr, Rc<(Lvl,(Span<()>,Rc<VTy>))>>` + `Vec<(SmolStr, Option<旧值>)>` trail，按 `name_mark` 惰性回退（cxt.rs:26-61，unwind :37；访问前统一 unwind :295-304）。
- `lookup_src` 返回共享 Rc 条目（cxt.rs:301），消除 L11 的整值克隆（symbol 签名 - `-> Option<(Lvl, Span<()>, Rc<VTy>)>`）。
- `Cxt::new()`→`new(infer: &Infer)`（cxt.rs:184），空构造拆出 `empty()`（:266），builtin 经 eval 生成（见 §3）；代价：Cxt 不能脱离 Infer 构造，初始化顺序固定。
- 另一处值得注意：L12 内建实现**不再 force env 实参**（cxt.rs:84-161），L11 每个内建先 force（L11 cxt.rs:97-161，含注释称臂体引用被解槽时 env 带 VSub）——L12 是否把 force 挪到 Prim 应用点未核 [未核实]；若没有，σ 包裹的实参可能使内建不触发。
- namespace 表仅元素类型变 FxHashSet<SmolStr>（cxt.rs:81；L11 cxt.rs:93 为 HashSet<String>），机制自 L11 就在（非本对新增）。

#### 4.5 fuel / 守卫
- 共享池 `UNIFY_FUEL=4096` L11 已有（L11 mod.rs:487-489），L12 保留（mod.rs:606）；L12 增量是 `pub fn unify(..., fuel: u32)` 参数专护 Decl 头展开重试臂（unification.rs:662，:703-713 在 fuel==0 时停下而非继续 quote+eval），并在 CANONICAL 顶层入口 `refuel()` 后 `unify(...,100)`（elaboration.rs:342-345），非 CANONICAL 走 `unify_catch`（:358-359；实现 mod.rs:1216）。`UnifyError::Stuck` 为此新增（mod.rs:568-572）。
- 孪生：`pm_fuel_exhausted`→`fuel_exhausted`（force.rs:175），语义从“PM 探测燃料”泛化为共享池查询；仍无参考版 Decl 头重试臂（README:378-381 自述）。

#### 4.6 其它实现性改动
- pretty.rs 重写为单输出缓冲（go :59，`pretty_tm` :358），并加缩进参数（go_ix/pretty_nat 等）；与 Call 显示配合（:231）。
- `Decl` 别名键 String→SmolStr、值仍 5 元组（mod.rs:24），写入路径 decl_mut 不变。
- 孪生新增 `ZZ_TRACE_ON` LazyLock 环境变量调试闸（subst.rs:164，消费 :89/:115/:172），零成本默认关闭。

### 5. 参考版 ↔ 孪生版同步差异

| 机制 | 参考版 | 孪生版 | 是否同步 |
|---|---|---|---|
| trait 求解 Val 级 | typeclass.rs 直匹配 Val | machine.rs 三方法 + v_to_ref_val 解码桥（:2435） | 同步（载体不同） |
| 嵌套覆盖两段式 | pending_pos+NestedCheck（pattern_match.rs:48/59） | compiler.rs 同款（symbols：PendingNode/node_indices 删） | 同步回退 |
| Call/Val::Call | 有（mod.rs:98/283） | **无**（bump_spine_iter 全层 grep 零命中） | **不同步** |
| canonical/iddfs | canonical.rs | 无，模块注释自述不移植（bump_spine_iter.rs:29-31） | 刻意不同步 |
| builtin 数量 | 6（含 change_mutable_default，cxt.rs:238） | 5（PrimId 五变体，syntax.rs:16；模块头 bump_spine_iter.rs:47） | **不同步**（README 却称移植 6 个） |
| Error 重试闭包 | Error.1（mod.rs:583-586） | 无（错误归一化/不挂闭包） | 不同步 |
| meta 上下文快照 | MetaEntry::Unsolved 三元（mod.rs:30-32） | MetaSnap（spine.rs:146，meta_unsolved :167） | 同步（异构） |
| 求解器载体文件 | typeclass.rs（415 行） | typeclass.rs 删除，并入 machine.rs | 文件级断点 |

- 孪生文件增删：仅删 bump_spine_iter/typeclass.rs（-227）；无新增文件；env.rs 的 `DeclEntry`/`Decls` 迁入 machine.rs:50/62（symbols），spine.rs +MetaSnap（:146），syntax.rs `PrimId` 可见性 pub(super)→pub(crate)（:16）。
- 两版唯一“新机制不同步”是 Call；README 的 “Ok 输出逐字节一致” 因此只在 Call 不进 Ok 输出的前提下成立 [推断，parity 套件头注有归一化剔除]。

### 6. 回退/丢失/弱化清单

| L11 中功能/机制/守卫/测试 | L12 状态 | 锚点 | 影响 |
|---|---|---|---|
| 嵌套覆盖的节点方程精化（PendingNode/node_indices） | 被 L07 式 pending_pos+σ 快照取代 | L11 pattern_match.rs:59/188 vs L12 :48/59；L12 mod.rs:2528-2564 | **语义丢失**：合法 GADT 尾位置程序被拒（L11 Ok→L12 Err）；正向钉 test_nested_coverage_vec_len2_ok 删除 |
| parser 单实参括号组摊平（SPINE_ESCAPE 哨兵） | 全层无对位（grep L12 无 SPINE_ESCAPE/is_spine_escape/strip_spine_escapes） | L11 parser/mod.rs:936-1031 vs L12 parser/mod.rs:808-816 | **健壮性/正确性风险回归**：`lcons zero (lcons zero lnil)` 错分组类缺陷失去防护 [推断]；无 L12 用例覆盖（tests/spine_paren_args.rs:37-40 只挂 L13） |
| test9/test10/test11（trait outParam/Add/Fin/宇宙级/Exists 等） | 删除，无替代 | diff:7915/8246/8292；L12 mod.rs grep 无 test9 | **测试丢失**：Val 级重写后 outParam/高阶参数/宇宙级回归无钉 |
| test_nested_coverage_vec_len2_ok（正向对照） | 删除，反向钉 gadt_tail_position 顶替 | diff:8651-8678；L12 mod.rs:2536-2565 | 测试口径从“必须 Ok”改为“必须拒”，丢失原语义的回归保护 |
| L11 `NameTrailEntry` 的 lvl/old_val 双向表 | 单表+粗 trail | L11 cxt.rs:20-70 vs L12 cxt.rs:26-61 | 语义保持（mark 回退），按层级反向查名的能力消失；参考版无 by_lvl 消费 [未核实] |
| L11 `Infer::lookup`（返回 Val） | 删除，仅 lookup_hit→Option<Rc<Val>> | L11 mod.rs:288-290 vs L12 mod.rs:327 | 小 API 面收窄 |
| L11 typeclass `Subst`/apply_subst_to_assertion（deps 代换） | 删除，deps 原样 clone | L11 typeclass.rs:339/342/360/380 vs L12:289-292 | 本层 deps 恒空故无观察差 [推断]，但能力退化 |
| README 行号/测试数准确性 | 失真 | README.md:396（17 vs 21）；:75/81-83/226（cxt 行号偏移 20-100 行） | 文档可信度下降 |
| 孪生 builtin 第 6 个（change_mutable_default） | 未移植 | 参考 cxt.rs:238 vs 孪生 syntax.rs:16 五变体 | 两版内置环境不同；Ok 输出在这些源上可能分叉（README 称 6 个，不实） |

### 7. 测试与文档变化

- **参考版 lib 测试**：L11 mod.rs 23 个 `#[test]` → L12 21 个。删 test9/test10/test11、test_nested_coverage_vec_len2_ok；增 test_nested_coverage_complete_ok、test_nested_coverage_gadt_tail_position；`test_ctor_wf_rebind_params_ok` 改名 `test_ctor_rebind_params_ok`；test_index/其它用例断言扩充（diff 新增 `Point[Nat]::Point.mk(4, 6)` 等 4 行断言，diff:7905-7911）。README 声称 17 个，与实测 21 不符（README.md:396）。
- **parity 套件**：tests/l12_fast_parity.rs 新增（789 行、15 个 `#[test]`），由 commit 4c6552fe “feat(L12): bump_spine_iter 性能孪生…” 加入（git log --diff-filter=A）；断言 Ok 逐字节、Err 归一化正文一致，头注登记已知偏差族。
- **parser 内联测试**：+4 个 `test_macro_expansion_info_*`（parser/mod.rs:2443-2530），服务宏跨文件 goto 信息（宏来源 span），是宏面唯一新测试。
- **README**：344→414 行（+70；numstat 399/329）重写；新增 §2 匹配编译器、§5 孪生增量、§6 分歧等，但行号引用多为 L11 期（§2 表），测试计数与 builtin 数失真（§2/§6）。无新增 `#[ignore]` 迹象 [未核实]。

### 8. 工程性/性能/健壮性改动

- **SmolStr 全量**：短名内联免堆分配，波及 Decl 键（mod.rs:24）、Span（parser/syntax.rs:1）、pretty ns（pretty.rs:1）、pattern Constructor（pattern_match.rs:20）、typeclass 名（typeclass.rs:14）。属类型面迁移，非语义改动；diff 中大量行由此产生（机械噪声）。
- **canonical 的成本控制**：逐候选 `refuel()` 重置 fuel（canonical.rs:113）、depth/target_limit 双剪枝（:44）、失败清 `meta_contrains`（:148，mod.rs:1217/1246/1253/1256）防挂账泄漏——把指数搜索限制在 Err 重试/LSP 路径。
- **meta 快照**：Unsolved 三元保留闭类型+Arc<Cxt>+原始类型，使 `no_metas` 错误路径能重建 pretty/lvl/decls（mod.rs:113-117、102）；孪生 MetaSnap 需跨轮 transmute（bump_spine_iter.rs:14-18）——长生命周期 Tycker 下的生命周期技巧，风险已知。
- **错误重试闭包**：Error 携带 `Box<dyn Fn()->Option<String>>` 使 quickfix 可惰性重跑；代价：Error 变非 Send（tests/spine_paren_args.rs:43 明确注“Error 可能携带非 Send 的重试闭包”），跨线程测试需归一化。
- **健壮性**：`v_to_ref_val` 把旧的 unreachable! 降级为宽放占位（machine.rs:2455-2460）；twin 编译器 covers/is_catch_all 改 SmolStr 后无分配比较；`ZZ_TRACE_ON` 环境变量闸默认零开销（subst.rs:164）。
- **性能面（声称）**：README §5 基准表（README.md:326-350）为 L11 移植后的口径，非本对新增优化；本对未引入新的热路径数据结构，除 cxt 名字表 O(1) 化（属 L07 d411debe 回填，commit 12ca86db 触达 L12）。

### 9. 标题噪声排除说明

- H1 只改 “L12：canonical 层（…）”（README.md:1）；大量 diff 行是 `src/L11_macro/…`→`src/L12_canonical/…` 路径与 `String`→`SmolStr` 类型拼写造成的，属机械迁移，已从“功能差异”排除（§1 churn 的大头）。
- cargo/bench 名（l12bench）与 bin 不在本 pair 的章节目录内（pair 只含 src/L{11,12}_*），未计入行数。
- README 中“相对 L07 的增量”段落（§4.2 hover_table/completion_table，README.md:264-267）不是本对增量：L11 mod.rs:498-528 已有同名字段；同理 §1 的构造子显示格式、§3 的 σ/VSub 机制均为 L11 已有。已排除。
- README §2 的 commit 日期/编号（45330e6 等）是跨层回填记录，非本对提交；本对真正的 feature commit 是 f5bbf21a（canonical）。已在 §0 标注。
- presence-matrix 中 canonical.rs 计 155、numstat/newLines 计 154：尾行换行计数差，draft 统一用 numstat 口径（+154）。

### 10. 证据锚点表（≥25 条，覆盖 §2–§8）

| # | 断言 | 锚点 |
|---|---|---|
| 1 | canonical.rs 新增、唯一调用点在 Err 重试闭包 | src/L12_canonical/canonical.rs:8; src/L12_canonical/elaboration.rs:456-473; src/L12_canonical/mod.rs:20 |
| 2 | iddfs 预算 1..=target_limit 逐 1 递增（修 +=2 跳档） | src/L12_canonical/canonical.rs:24-29 |
| 3 | search 逐候选 refuel + unify(...,5) + check::<true> | src/L12_canonical/canonical.rs:113-115 |
| 4 | check 的 CANONICAL 常量开关顶层合一入口/fuel | src/L12_canonical/elaboration.rs:274,342-359 |
| 5 | Typ 桥删除、Val 直匹配 | src/L11_macro/typeclass.rs:9,19; src/L12_canonical/typeclass.rs:123,196 |
| 6 | 一阶匹配只允许实例侧 Rigid 绑定（假匹配修复） | src/L12_canonical/typeclass.rs:142-150 |
| 7 | vals_eq_ground 的 Match 分支体 Rc::ptr_eq | src/L12_canonical/typeclass.rs:235-246 |
| 8 | deps 代换删除（L11 有 apply_subst） | src/L11_macro/typeclass.rs:188-190; src/L12_canonical/typeclass.rs:289-292 |
| 9 | twin 求解器并入 machine（文件删除） | src/L12_canonical/bump_spine_iter/machine.rs:658,687,2419,2435; src/L12_canonical/bump_spine_iter.rs:132-137 |
| 10 | Call 节点定义与四处消费 | src/L12_canonical/mod.rs:98,283,718-720,952,1147-1149; src/L12_canonical/unification.rs:391-393,678-679 |
| 11 | Val::Match origin 第四字段 + 卡住 match 包 Call | src/L12_canonical/mod.rs:281,524-560,1187-1193; src/L11_macro/mod.rs:228 |
| 12 | MetaEntry::Unsolved 三元与 no_metas 重建 | src/L12_canonical/mod.rs:30-32,102,113-117; src/L11_macro/mod.rs:28-31,98 |
| 13 | 嵌套覆盖回退：PendingNode→pending_pos | src/L11_macro/pattern_match.rs:59,188,308; src/L12_canonical/pattern_match.rs:48,59,239-246 |
| 14 | 回退后果：Vec 长 2 程序被拒的钉 | src/L12_canonical/mod.rs:2528-2565 |
| 15 | 旧正向钉被删 | .deltawork/pairs/L11--L12.diff:8646-8678 |
| 16 | test9/10/11 删除 | .deltawork/pairs/L11--L12.diff:7915,8246,8292 |
| 17 | 测试数实测 21 而 README 称 17 | src/L12_canonical/mod.rs（grep #[test] 21）; src/L12_canonical/README.md:396 |
| 18 | parser 丢 SPINE_ESCAPE 及其理由注释 | src/L11_macro/parser/mod.rs:762-787,936-1031; src/L12_canonical/parser/mod.rs:808-816 |
| 19 | 自定义算符优先级/回落改动 | src/L11_macro/parser/mod.rs:895-920; src/L12_canonical/parser/mod.rs:925-950 |
| 20 | parser_with_macros/smolstr/宏信息测试新增 | src/L12_canonical/parser/mod.rs:439,581,2443-2530; L11 全层无（grep） |
| 21 | run_with_prelude 与 prelude 装载新增（README 未提） | src/L12_canonical/mod.rs:1307-1334,1358; src/L11_macro 无（grep） |
| 22 | Error 双字段 + 非 Send 重试闭包 | src/L12_canonical/mod.rs:583-595; src/L11_macro/mod.rs:478-479; tests/spine_paren_args.rs:43 |
| 23 | UnifyError 增 Stuck 变体 | src/L12_canonical/mod.rs:568-572; src/L11_macro/mod.rs:463-467 |
| 24 | unify(...,fuel) 的 Decl 头重试臂 | src/L12_canonical/unification.rs:662,703-713 |
| 25 | cxt 名字表 O(1) 化与 Rc 条目 | src/L12_canonical/cxt.rs:26-61,295-304,301; src/L11_macro/cxt.rs:20-70,456 |
| 26 | Cxt::new(infer) 与 builtin eval 注册、第 6 内建 | src/L12_canonical/cxt.rs:184-264,142,238; src/L11_macro/cxt.rs:164-200 |
| 27 | 内建不再 force 实参（L11 有） | src/L12_canonical/cxt.rs:84-161; src/L11_macro/cxt.rs:97-161 |
| 28 | 孪生 builtin 仅 5 个（README 称 6） | src/L12_canonical/bump_spine_iter/syntax.rs:16; eval.rs:236-307; bump_spine_iter.rs:47; README.md:309-310 |
| 29 | 孪生无 Call/canonical（刻意不同步） | src/L12_canonical/bump_spine_iter.rs:29-31; grep bump_spine_iter 零 Call |
| 30 | MetaSnap/decl 条目迁移/fuel 改名/ZZ_TRACE_ON | src/L12_canonical/bump_spine_iter/machine.rs:50,62; spine.rs:146,167; force.rs:175; subst.rs:164 |
| 31 | pretty 缓冲式重写 + Call 臂 | src/L12_canonical/pretty.rs:59,231,358 |
| 32 | parity 套件新增 15 例（commit 4c6552fe） | tests/l12_fast_parity.rs:1（grep 15）; git log --diff-filter=A |
| 33 | canonical 由 commit f5bbf21a 引入 | git log --diff-filter=A -- src/L12_canonical/canonical.rs |
| 34 | README 行号引用过期样例 | README.md:75,81-83,226,396 vs cxt.rs:184,345,400,421; mod.rs:909,871,606 |
| 35 | L12 目录含事后回填（提交触达 L12 文件） | git log -- src/L12_canonical/canonical.rs（12ca86db/cac125af/8eff89cf） |

### 11. 给 Lead 的一句话

L12 的新机制只有 Val 级求解/Call/canonical 三件，真正风险是“匹配覆盖精度与 parser 括号修复”两处回退 + 测试与 README 同时缩水。

## 9. L12 → L13：产品化 + 命名空间/原生 Nat 再定基（全链最大断点）

> 本章分两个单元：核心机（§9.1，`mod.rs`/`elaboration.rs`/`unification.rs`/`cxt.rs`/`pattern_match.rs`/`pretty.rs`/`canonical.rs`/`typeclass.rs` + `bump_spine_iter/**`）与表层（§9.2，parser/派生/prelude/HDL/测试/README）。两稿共享同一 `.deltawork/pairs/L12--L13.*` 数据源。

### 9.1 核心机

> 单元 delta-l12-l13-core ｜ 数据源 .deltawork/pairs/L12--L13.{diff,numstat,files,symbols}.tsv、.deltawork/inventory/* ｜ 核对时点 HEAD 0464150c（2026-11-11）｜ 行数=物理行、churn=numstat ｜ 范围：mod.rs / elaboration.rs / unification.rs / cxt.rs / pattern_match.rs / pretty.rs / canonical.rs / typeclass.rs / bump_spine_iter/**。parser/derive/prelude/HDL 面与测试清单归 delta-l12-l13-surface，本稿只按组计数不列清单。

#### 0. 结论摘要（≤10 行）
- **性质**：L13 不是 L12 的小步增量，而是按「产品层（LSP/HDL 宿主）」目标的内核重写：参考版三文件 mod.rs+elaboration.rs+cxt.rs 合计 +9,298 行，孪生侧 +10,101 行净增并**按子系统重新拆模块**；新增 33 个文件（其中 25 个测试文件 = 15,270 行；L12 为 0 个独立测试文件 / 35 个内联 #[test]，L13 为 612 个 / 9 个 #[ignore]）。
- **链判定：不连续**。最重断点是精化载体：L10/L11/L12 三层的显式替换 σ（Subst/Val::VSub/SpecSolve，孪生 subst.rs 250 行）在 L13 **两版引擎全部删除**，退回 L07 时代 update_cxt（env 槽改写 + refresh）血统；check_pm 返回类型从 (Tm, Rc<Subst>) 变回 (Tm, Cxt)。
- 名字世界换血：decl 键 = 全限定名、七元组（prim 槽 + typ_pretty）；package/import/inherent 方法/五级名字解析/后缀回退；构造子**不再有裸名别名**。
- 值表示：原生 Val::Nat(u64)（两版都做，快版 XCell::Nat）；SumCase 由 case_name 改构造子**下标** index: u32；Match 丢掉第 4 字段 origin。
- 内建：删 Tm::Prim/Val::Prim 变体，prim 挂 decl 表第 6 槽（Option<PrimFunc>/Option<PrimId>），执行点改 force/v_app 的 Decl 臂。
- 新增 Tm::Call/Tm::OpCall（快版合并为 Call，OpCall 由 export 在参考域重建）、def replay、终止性检查（Level A + 12 项 allowlist）、eval 时间预算 + Nat 链分配护栏。
- LSP 观察面落成产品能力：三张 owned 表（hover/completion/inlay 在 push 期渲染成 String）、FORCE_MEMO 记忆化、PreludeSlot/PreludePool 池化、孪生常驻检查点 + arena 压实（1835MB→429MB）、参考域 ExportedDecl 导出。
- 代价：σ 路线被放弃后，GADT 模式精化回到「改写环境槽 + 全槽重求值」，L12 对槽位过期 bug 族的修复不被 L13 继承；终止性检查为**放行式**（allowlist 12 项为临时口径），预算/护栏属于「兜底不健全」而非完备性证明。

#### 1. 规模与文件级变化
L12 27 文件 19,603 行 → L13 59 文件 59,378 行（+39,775 净增；其中测试新增 25 文件/15,270 行、parser/derive 1,411 行（归 surface）、三个千行新孪生模块 observe/prim/typeclass 合计 3,422 行、compact/debug/termination 合计 1,401 行、eval_budget 144 行）。

> 锚点写法：§3–§9 中未带目录的 X.rs 缺省 = src/L13_namespace/X.rs；bump_spine_iter/X.rs = src/L13_namespace/bump_spine_iter/X.rs；L12 X.rs = src/L12_canonical/X.rs。§10 全部为仓库相对全路径。

##### 1.1 参考版核心（本单元主战场）
| 文件 | 状态 | L12→L13 行 | churn +/- | 一句话性质 |
|---|---|---:|---:|---|
| mod.rs | changed | 2,796→8,526 | +7,734/−2,004 | 名字世界/值表示/观察面/预算/termination 全落这里；删除 σ 与 Prim 变体 |
| elaboration.rs | changed | 1,310→3,907 | +3,140/−543 | package/import/class 两阶段/五级解析/终止性检查/观察 push |
| cxt.rs | changed | 464→1,435 | +1,221/−250 | Cxt 增 namespace/import/binding_name 域；内置 15 prim；update_cxt 回归 |
| unification.rs | changed | 862→1,253 | +600/−209 | Call 快路径、Nat 臂、SumCase 下标；删 Prim/σ 相关臂 |
| pretty.rs | changed | 393→852 | +739/−280 | OpCall 中缀还原、限定名/原生 Nat 显示 |
| pattern_match.rs | changed | 505→760 | +572/−317 | 下标/限定键 detail、精化回 update_cxt、探测适配 |
| typeclass.rs | changed | 414→646 | +302/−70 | head_index 桶 + GENERIC_SELF_HEAD + out 参数 + allow_flex_defaulting |
| canonical.rs | changed | 154→148 | +10/−16 | 语义不变，仅适配 MetaEntry/名字世界签名（-6 净） |

##### 1.2 性能孪生
| 文件 | 状态 | L12→L13 行 | churn +/- | 性质 |
|---|---|---:|---:|---|
| bump_spine_iter.rs | changed | 193→292 | +238/−139 | 模块清单 +typeclass/prim/termination/observe/compact/debug，subst 移除 |
| bump_spine_iter/machine.rs | changed | 3,359→5,528 | +3,989/−1,820 | 名字世界/Cxt/指针导入表/class 两阶段/replay 汇入 |
| bump_spine_iter/entry.rs | changed | 400→1,842 | +1,522/−80 | 常驻检查点/prime_resident/observe_user/export 数据面 |
| bump_spine_iter/force.rs | changed | 621→1,034 | +901/−488 | FORCE_MEMO + 状态日志撤销 |
| bump_spine_iter/compiler.rs | changed | 458→916 | +721/−263 | 下标/限定键模式编译 |
| bump_spine_iter/unify.rs | changed | 979→1,401 | +777/−355 | Call/Call 快路径、Nat 臂、fuel 语义 |
| bump_spine_iter/quote.rs | changed | 478→679 | +236/−35 | quote_nat_chain + 预算 checkpoint |
| bump_spine_iter/rename.rs / spine.rs / eval.rs / env.rs / syntax.rs / bench_src.rs | changed | 812/198/629/143/278/218→906/244/692/147/298/315 | 净 +94/+46/+63/+4/+20/+97 | 随世界口径适配 |
| bump_spine_iter/subst.rs | **removed** | 250→— | −250 | σ 设施整体删除（本层无显式替换） |
| bump_spine_iter/observe.rs | **added** | —→1,362 | +1,362 | 观察面 push/查询 + observation_tests |
| bump_spine_iter/prim.rs | **added** | —→1,030 | +1,030 | PrimId/DeclEntry(含 prim 槽)/replay/原生 Nat/decl 表 |
| bump_spine_iter/typeclass.rs | **added** | —→1,030 | +1,030 | L11→L12 删掉的独立求解器模块在 L13 重建 |
| bump_spine_iter/compact.rs | **added** | —→666 | +666 | 常驻 arena 深拷压实 |
| bump_spine_iter/debug.rs | **added** | —→413 | +413 | 错误消息 Debug 复刻（L09 同款独立模块） |
| bump_spine_iter/termination.rs | **added** | —→322 | +322 | Level A 终止性检查镜像 + ALLOWLIST |
| bump_spine_iter/eval_budget（同目录） | **added** | —→144 | +144 | 时间预算 + Nat 链护栏（两版共用模块） |

#### 2. 标题宣称的增量：声称 vs 实现
来源：src/L13_namespace/README.md（H1 之后 1–338 行）与 src/L13_namespace/bump_spine_iter.rs:1-176 模块头。
| README/孪生头声称 | 实现锚点 | 判定 |
|---|---|---|
| decl 表七元组，比 L12 多 prim 槽 + typ_pretty | mod.rs:432；L12 mod.rs:66 五元组 | 一致（README 行号 mod.rs:309 已过期→实为 432） |
| 构造子只登记限定名 Enum.case，无裸名别名 | elaboration.rs:1875-1882（"no bare caseName alias"）；裸名走 suffix 回退 elaboration.rs:2926-2948 | 一致 |
| Var 五级解析链（局部>精确>import>prefix>suffix） | elaboration.rs:2916-2917 优先级注释、2918、2925、2943-2984；cxt.rs:332-334 | 一致（README :2323 过期→2916） |
| inherent 方法注册 TypeHead.method；算符方法登记 symbol_table | elaboration.rs:1887-1930、3613；mod.rs:1459 | 一致 |
| package/import 不写 decl 表、import_map 挂 Infer | elaboration.rs:2460-2467、2469-2547；mod.rs:1469 | 一致 |
| class 两阶段 + PrecheckedItems | elaboration.rs:2552-2697、2681-2687；parser/mod.rs:3441/3453（共享） | 一致（README :1961 过期→2552） |
| BindingName 隐参合成 | cxt.rs:338、1410；elaboration.rs:500-518、1129-1130 | 一致 |
| 原生 Nat（字面量直构、eval 折叠、quote 展开回链） | mod.rs:280-292、3551-3559；cxt.rs:25/49-51；bump_spine_iter/quote.rs:617 | 一致（README mod.rs:724-733 过期→905） |
| prim 挂 decl 表、删 Tm::Prim/Val::Prim | mod.rs:432/468-491；cxt.rs:965-981；L12 mod.rs:88/268 对照 | 一致 |
| Cxt::new 注册 String + 15 个内建（README:97 列表） | 实测 16 个 add_builtin（多 check_comb_cycles，cxt.rs:978-1086、:1010） | 另有出入（README 漏计 1 个） |
| SumCase 按下标；PatternDetail::Con 三→四字段 | mod.rs:912-917、744-756；L12 mod.rs:275-279、128-133 对照 | 一致（README :572-585 过期→744） |
| Call/OpCall 内联节点，quote→eval 往返恒等 | mod.rs:524-533、1314-1338；pretty.rs:451/776 | 一致 |
| def replay（REPLAY_GLOBAL_OPS + 按名 memo + 环敏感扫描） | mod.rs:3116-3196；bump_spine_iter/prim.rs:117-214 | 一致 |
| 不移植 canonical/iddfs、FUNC_PROF 计时、Tm/Val 迭代 Drop、PreludePool | 孪生头 bump_spine_iter.rs:84-86；实测孪生无 iddfs | 一致（Drop/PreludePool 仅参考版：mod.rs:559/3989） |
| 无 PreludePool 池化（每 kick 从 prime_round 重放） | bump_spine_iter.rs:75；entry.rs:898/1566 | 一致 |
| 「L13 精化载体是 update_cxt 血统，与 L12 的 σ 路线分叉」 | README.md:165-176；L12 README.md:12-16 也自认这条分叉 | 一致，且是**链不连续的自证** |
| README 引用的行号密集过期（mod.rs:1191/1316、cxt.rs:642-753/998、elaboration.rs:365/475） | 实际 1413/1549、965-981/1327、678/788 | 文档失真（结构内容对、行号漂移 400–900 行；surface 单元统一处理） |

#### 3. 语言/语法/类型系统/内建/LSP 面增量
1. **全限定 decl 键**：Decl 从五元组变七元组 (Span, Tm, Val, Ty, VTy, Option<PrimFunc>, String)（mod.rs:432）；第 7 槽 typ_pretty 是 def 登记处渲染缓存，供 LSP def-site 悬浮（twin 侧 prim.rs:303-335 注释；参考版 push_hover 实时渲染 elaboration.rs:2827）。
2. **package**：Decl::Package 设 cxt.namespace_prefix 并把包名加入可见 namespace 集（elaboration.rs:2460-2467；cxt.rs:333-334）。
3. **import**：Decl::Import 只产文件局部别名到 Infer.import_map（不写 decl 表），具名 import 附带 X.mk 点状成员别名，通配扫 decl 前缀键，冲突报 ambiguous，单名 import 直接拒绝（elaboration.rs:2469-2547）。
4. **后缀回退**：裸名先精确键→import→prefix，最后收 .name 后缀候选；必须**唯一**，且候选头须是可见 decl 头/namespace（G6 注释），多个则报歧义并逐候选给 add import 修复（elaboration.rs:2943-2984、2989-3005）。
5. **inherent 方法**：impl 的 inherent 分支把方法注册成 TypeHead.method 限定键（elaboration.rs:1887-1930、3613），并把 (类型值, 方法名集, 类型名) prepend 进 cxt.namespace 供 x.m 直查（elaboration.rs:1924）；算符方法同时登记 symbol_table（mod.rs:1459、8384-8464）。
6. **原生 Nat**：Val::Nat(u64)（mod.rs:905）替代一元 SumCase 链；eval 装配点用 nat_step_value 折叠 zero→0、succ(Nat k)→Nat(k+1)（mod.rs:280-292、3551-3559）；build_nat 直构（cxt.rs:49-51）；quote 经 quote_nat/quote_nat_chain 展开回链保持下游形状不变（twin quote.rs:616-617、rename.rs:490）；count_nat_forced 逐 step force 兼容未归一实参（cxt.rs:14-42）。
7. **prim 挂 decl 表**：删 Tm::Prim/Val::Prim（L12 在 mod.rs:88/268，L13 无）；Cxt::new 用 add_builtin 把 String 类型 + 16 个内建写进 decl（prim 槽 = Option<PrimFunc>，cxt.rs:965-1086；README 称 15 个，漏计 check_comb_cycles :1010）；求值走 force/v_app 的 Decl 臂，卡住留 spine。
8. **SumCase 下标**：Tm/Val 的 SumCase 的 case_name 换成 index: u32（mod.rs:517-522/912-917；L12 mod.rs:90-95/275-279 对照）；PatternDetail::Con 首字段同步 index 并加 Option<SmolStr> 全限定键（mod.rs:744-756），走查期查 decl 得键回写 Raw::Var，使 check_pm 精确命中而非后缀扫描（实现见 pattern_match 走查 + §2.2 声称）。
9. **Call/OpCall**：def 检查后把 λ 链体顶端 Match 包成 Tm::Call(name, args, body)（mod.rs:1314-1338）；eval 卡 Match 才包 Val::Call；quote 查 symbol_table 在实参全 Expl 且 1–2 个时产显示专用 Tm::OpCall（mod.rs:533；pretty.rs:451/776；twin 侧合并为 Call，由 export 重建 OpCall，syntax.rs:51-57）。
10. **LSP 面**：三张 owned 表 = HoverEntry=(src span, def span, String)（mod.rs:1408-1413）、completion/inlay（elaboration.rs:481/494、3187）；查询 hover_entry_at 取包含偏移的最小 span（mod.rs:1549-1554）；分支体错误逐条入 accumulated_errors（mod.rs:1443-1445）；失败 decl 名集 failed_decls 把二阶 not-in-scope 降级（mod.rs:1446-1452、elaboration.rs:3007-3014）。

#### 4. 核心机制与实现性改动（A=L12 → B=L13）
##### 4.1 名字世界与精化载体
| 子机制 | L12 怎么做 | L13 怎么做 | 锚点 |
|---|---|---|---|
| 全局名字 | decl 表五元组，裸名/限定名混用；Val 级 trait 求解 | 七元组全限定键 + package/import/namespace 集；裸名走后缀唯一回退 | L12 mod.rs:66 vs L13 mod.rs:432；elaboration.rs:2916-2984 |
| 模式精化载体 | σ：Subst 单链 + Val::VSub，check_pm 返回 Rc<Subst>，unify_pm 累加 SpecSolve，force 的 frcs 读点推进 | 无 σ：unify_pm 直接 cxt.update_cxt 改 env 槽 + refresh 重求值，check_pm 返回 Cxt | L12 elaboration.rs:105/124、mod.rs:288/305-307、twin subst.rs:1-6 vs L13 elaboration.rs:781/788、cxt.rs:1327 |
| 精化写入细节 | 不动槽位，值外层包 σ；臂边界回滚=指针赋值 | env.change_n 替换目标槽、update_from 记最早被改槽做增量刷新下界、update_prune 置空 pruning 槽 | L13 cxt.rs:1327-1366、1400-1410；L12 README.md:210-222（σ 口径） |
##### 4.2 值/项表示与求值
| 子机制 | L12 | L13 | 锚点 |
|---|---|---|---|
| Nat | 一元 SumCase 链 | Val::Nat(u64)；快版 XCell::Nat（打包 tag 已满走 bump 单元） | mod.rs:905；bump_spine_iter/eval.rs:40-42/618-619 |
| SumCase | case_name: Span<SmolStr> | index: u32（case 名反查 cases[index]） | mod.rs:912-917；bump_spine_iter/syntax.rs:43-48 |
| Match | Val::Match(scrut, env, arms, Option<(SmolStr, Vec<Rc<Val>>)>) | 去掉第 4 字段 origin | L12 mod.rs:281 vs L13 mod.rs:918 |
| Call | Tm::Call(SmolStr, Vec<Rc<Tm>>, Vec<Rc<Val>>, Rc<Tm>)（显示/值双实参域） | Tm::Call(SmolStr, List<(Rc<Tm>, Icit)>, Rc<Tm>) + Tm::OpCall 显示节点 | L12 mod.rs:98 vs L13 mod.rs:524-533 |
| 迭代 Drop | 无（L12 参考版递归 drop） | Tm::drop/Val::drop 迭代排水（drain_tm/drain_val + release_owned），防深链栈溢出与泄漏 | mod.rs:536-557、559-690、923-935 |
##### 4.3 unify / eval / quote / rename
- **unify**：新增 Call 三条臂——同名 Call 走 spine 快路径（bump_spine_iter/unify.rs:621 注释：无 Flex 免快照、有 Flex 三重快照回滚），异名/单侧退化为体比较（unification.rs:1008、1037-1039）。SumCase/SumCase 比 index + typ + datas，另加 (Nat, SumCase)/(SumCase, Nat) 跨形态臂（unification.rs:1144-1165）。原 Val::Prim 带类型合一臂随变体删除。
- **eval**：双栈迭代器保留 L12 形状；新增 Tm::Call 帧（twin eval.rs:323）、SumCase 装配点 Nat 折叠（mod.rs:3551-3559、twin eval.rs:618）、每 2^20 迭代 eval_budget::tick（mod.rs:3329/3823、twin eval.rs:288）。
- **quote/rename**：新增 quote_nat_chain（twin quote.rs:617，rename.rs:490 复用）与 OpCall 还原（pretty.rs:451）；参考版 quote 的 Call 臂查 symbol_table。
- **canonical**：L12 语义逐字保留（iddfs 步进 +=1 含端点、每候选 refuel、meta_contrains.clear），仅随签名适配：fresh_meta(..., empty_span(()))、src_names.get、decl 迭代滤除项从 6 个内建名缩为 outParam/avoid_recurse（canonical.rs:20-32、63-73；L12 canonical.rs:59-79 对照）。
##### 4.4 trait 求解
- 参考版 typeclass.rs +232 行：Synth 增 head_index: FxHashMap<(trait, head_fn), Vec<usize>>（src/L13_namespace/typeclass.rs:100）、GENERIC_SELF_HEAD="*" 通配桶（:133、:177-217）、trait_out_params（:97/:149）、allow_flex_defaulting 贯通 solve_trait（unification.rs:615/645/656、:674）；实例匹配从线性扫 class_instances 降为桶查 + 兜底扫。
- 孪生：L11→L12 删 twin/typeclass.rs、L12 把求解器留在 machine，L13 **重新**立 bump_spine_iter/typeclass.rs（1,030 行）并镜像 head_key 桶、trait_metas 登记表、GENERIC_SELF_HEAD、非 out 参数 Flex 推迟（bump_spine_iter.rs:59-64；typeclass.rs:1-8/40/65）。
##### 4.5 class / BindingName / replay / termination / budget
- **class 两阶段**：Phase A 在 create 参数上下文逐字段 check 并解未注解字段的 fresh meta，记录 prechecked + bn_refs；Phase B 组装 PrecheckedItems 喂共享 parser::expand_class_decls，再逐 decl infer_after_prefix（elaboration.rs:2552-2697；twin machine.rs:4868/5005-5024）。孪生 Phase B 经**指针导入表** tm_import/val_import 复用参考域 Rc<Tm>/Rc<Val>（machine.rs:1619-1629、433）。
- **BindingName 隐参**：insert 遇隐参类型为 BindingName 时不建 meta，合成 BindingName.mk「当前绑定名」；绑定名由 cxt.binding_name 携带（bind 清空、define 保留、with_binding_name 显式设）（cxt.rs:338/1410；elaboration.rs:500-518、1129-1130、2615、3406）。
- **def replay**：无参 def 体直接/传递调 create_global/change_mutable(_default)/get_global 时，登记值存 Val::Decl 占位；eval 的 Tm::Decl 臂命中 def_needs_replay 则清 env 重放 body；memo 按名 + 环敏感扫描，truncated 抑制毒化写（mod.rs:3116-3196；twin prim.rs:117-214；twin eval.rs:294）。
- **终止性检查**：新增 Level A walker——scrutinee 链根须落到 def 参数或已标模式变量层，递减实参须是已标模式变量；12 项 allowlist 为临时放行（elaboration.rs:118-131/172-188；twin termination.rs:30-57/99-115；错误文案 cannot prove termination of recursive call to；调用点 elaboration.rs:1445、孪生 machine.rs:3765）。
- **eval budget**：协作式时间预算（scope 收紧 deadline、scope_default、tick 每 2^20 迭代、超时 panic_any(ElabTimeout) 由边界 catch_unwind 落诊断/回落参考版）+ 无条件内存护栏 guard_nat_chain（NAT_CHAIN_LIMIT = 1<<22，起因是 nat_mul 100000 100000 显示展开把进程提交量顶到 121.8GB 导致主机重启）（eval_budget.rs:1-27、47、72、77、104、127）。
##### 4.6 LSP 观察面与性能设施（核心机内）
- 观察表从 L12 的 Vec<(Span, Span, Cxt, Rc<Val>)>（L12 mod.rs:616）改为 **push 期渲染的 owned String**（mod.rs:1408-1413），使 bump 引擎跨轮可填同一张表；clear_observation_tables 轮界清表（twin observe.rs:12）；prelude 装载段 observe=false 关 push（twin observe.rs:36、bump_spine_iter.rs:76）。
- FORCE_MEMO：force 结果按输入节点地址 memo，1M 条上限、epoch/taint/keepalive 三支柱（参考版 mod.rs:154-194；twin force.rs:202-297/445）；L12 无此设施（静态 grep 0 命中）。
- PreludeSlot/PreludePool：thread-local prelude 状态缓存 + 进程级池，libtest 每测试一线程免重装（参考版 mod.rs:3989-4066；L12 无）。
- 孪生常驻检查点：prime_resident 一次装载 + observe_user 多次复用 + 阶段 4 单文件诊断接管 + ExportedDecl 导出回参考域（entry.rs:898/1134/1566、41；mod.rs:440）。

#### 5. 参考版 ↔ 孪生版同步差异
| 机制 | 参考版 | 孪生版 | 同步判定 |
|---|---|---|---|
| 名字世界（package/import/五级解析/后缀回退） | elaboration.rs:2460-2547、2916-2984 | machine.rs 内嵌（symbol_table/import_map/namespace_prefix 字段 :478-484；tm_import 指针表） | 语义对齐，代码形态不同 |
| 原生 Nat | Val::Nat + nat_step_value + quote 展开 | XCell::Nat + 同规则 eval 折叠 + quote_nat_chain | 同步 |
| prim 挂 decl 表 | PrimFunc 闭包槽 | PrimId 枚举槽（bump 不能带闭包） | 同步（载体不同） |
| SumCase 下标/Con 四字段 | mod.rs:744-756/912-917 | syntax.rs:43-48 + PatternDetail 共享 | 同步（共享类型） |
| Call/OpCall | 两个 Tm 节点 | 合并为 Tm::Call；OpCall 由 export 重建 | 单侧机制（孪生无 OpCall 节点） |
| 精化载体 update_cxt | Cxt::update_cxt 全量实现 | machine.rs 镜像 + 状态日志撤销（update_pm 等） | 同步（两版都放弃 σ） |
| class 两阶段 | PrecheckedItems 直接复用 | Phase B 经 tm_import/val_import 指针桥复用参考域对象 | 同步（孪生多一层桥） |
| trait 求解器 | typeclass.rs（Val 级） | typeclass.rs（Val 经 v_to_ref_val 解码进出） | 同步；L12 曾删孪生模块，L13 重建 |
| canonical/iddfs | 保留，Err 重试闭包触达（elaboration.rs:1601） | 无 | 不移植（明示，不影响 Ok 输出） |
| FUNC_PROF | 计时+计数（mod.rs:24-97） | 仅计数（super::prof_count） | 单侧能力 |
| Tm/Val 迭代 Drop | 有（mod.rs:559-690） | 无（bump 免疫） | 单侧 |
| PreludePool 池化 | 有（mod.rs:3989） | 无（每 kick 重放） | 单侧 |
| FORCE_MEMO | 有 | 有（各自 bump 版） | 同步 |
| 观察三表 | owned String push | owned String push（observe.rs） | 同步（互检测试断「无缺失+无异质」） |
| 错误消息 Debug/span | 源码 span；独立 debug 无 | 名字 Span 全零；debug.rs 复刻 | 已知偏差（比对前归一化） |

#### 6. 回退/丢失/弱化清单
| L12 中已有 | L13 状态 | 锚点 | 影响 |
|---|---|---|---|
| σ 显式替换设施：Subst/Val::VSub/SpecSolve/frcs/mentions_level | **两版全部删除**；精化退回 update_cxt（env 槽改写 + refresh） | L12 mod.rs:288/305-307、elaboration.rs:105-124、twin subst.rs:1-6；L13 mod.rs（无 VSub）、elaboration.rs:781-788、cxt.rs:1327 | L12 对「槽值过期/槽位错位」bug 族的架构性修复不被继承；check_pm 返回 Cxt 让臂上下文快照变重（clone 整 Cxt 而非指针） |
| Tm::Prim/Val::Prim 带类型卡住形态 | 删除；prim 挂 decl 表，执行点改 force/v_app 的 Decl 臂 | L12 mod.rs:88/268；L13 mod.rs:432、cxt.rs:965-981 | 卡住 prim 的 unify 专用臂消失（改为不透明叶 + 对侧 Flex 先求解拦截）；string_to_global_type 未登记→卡 Decl 语义合并 |
| Val::Match 第 4 字段 origin（实例匹配追溯） | 删除 | L12 mod.rs:281 vs L13 mod.rs:918 | 卡住 match 的显示/实例来源信息丢失 [推断：仅诊断/显示依赖] |
| 孪生 subst.rs 250 行 + SUBSTV_ALIVE/VSUB_REGS 跨轮回收 | 删除（L13 无显式替换即无回收需求） | L12 bump_spine_iter.rs:154 vs L13 bump_spine_iter.rs:165-169 | 机制删除的连带清理，不是遗漏 |
| canonical/iddfs 孪生版 | 仍然不移植（L12 同） | L13 bump_spine_iter.rs:84-86；elaboration.rs:1601 | 非新增回退 |
| L12 的状态可差分撤销面（σ 回滚 = 指针赋值） | 改为 Cxt 全量 clone/重求值 + 孪生状态日志 | cxt.rs:1327-1366；twin machine.rs:113/197-208 | 臂边界回滚成本上升 [推断：由 Cxt clone 抵消] |
| σ 路线的回归保护 | 无对应新测试（测试总量反增） | 见 §7 | L12 的 σ 行为不再有回归保护 |

#### 7. 测试与文档变化（本稿只给计数，清单归 surface 单元）
- 测试口径：#[test] 静态计数 L12 = 35（0 独立测试文件，全内联）→ L13 = 612（25 个独立测试文件，15,270 行）+ 9 个 #[ignore]。新增测试族（按名）：module/class/calc/cong_projection/bare_ctor/debug/struct_refine_probe/prim_safety/termination_check/eval_budget/hdl_{assert,blackbox,check_graph,enum,fsm,stream_fix}/prelude_{core,data,hdl_a,hdl_b,hdl_c,stdlib}/legacy/verilog_compat。
- README：src/L13_namespace/README.md 440+/399− 行改动（numstat），内容覆盖新机制（§2 已核）；但**行号引用系统性过期**（见 §2 最后一行），docs/ 侧新增 20+ 篇 L13 专题分析（如 docs/l13-quirks-analysis-2026-10.md、docs/l13-typeclass-instance-nat-param-bug.md、docs/lsp-twin-wiring-2026-09.md、docs/prelude-round-2026-10b.md），README 的「已知偏差」与 docs 相互引用。
- 结论：L13 文档是**产品口吻**（LSP/HDL 效果、修复记录），L12 文档是**机制口吻**（σ 路线 vs L13 分叉自认）；两者对同一分叉的描述一致，README 失真只在行号。

#### 8. 工程性/性能/健壮性改动
| 改动 | 锚点 | 影响 |
|---|---|---|
| FORCE_MEMO（force 结果按节点地址记忆化，1M 上限，taint/epoch/keepalive） | mod.rs:154-194；force.rs:202-297/445 | prelude 装载 force 636M 次/188k 节点（~3400× 冗余）→ HDL prelude 11.0s→1.8s（README 声称） |
| Twin arena 压实 compact（可达根深拷到新 bump） | compact.rs:1-22 | 常驻态 1835MB→429MB（README/孪生头声称） |
| PreludeSlot/PreludePool（线程本地缓存 + 进程池） | mod.rs:3989-4066 | libtest 每测试重装 prelude 的 ~1.5s 成本消除 |
| eval 时间预算 + Nat 链分配护栏 | eval_budget.rs:1-27、72-81、104-144 | 循环定义不再冻结 LSP；nat_mul 1e5 1e5 显示展开不再 121.8GB 拖垮主机 |
| 终止性检查（Level A + 12 项 allowlist） | elaboration.rs:118-188；termination.rs:30-115 | 拒绝 def bad(x: Nat) = bad x；代价=12 个真递归定义被放行（不健全） |
| 孪生状态日志撤销（七表 + mutable/replay/trait_metas 写点） | machine.rs:113、197-208；entry.rs:1386-1393 | 失败 decl 回滚成本降低，替换整克隆恢复 |
| 调试残留 | eprintln! L12 6 处 → L13 66 处（elaboration.rs 4/entry.rs 11/force.rs 1/machine.rs 4/mod.rs 33/observe.rs 11/typeclass.rs 1；decl_probe_enabled 门控的 __probe 分支另计） | 需确认均受环境变量门控 [未核实：仅抽样见 decl_probe_enabled] |
| FUNC_PROF 计数探针 | mod.rs:24-97；孪生不取 Instant | 双引擎 A/B 调用量归因；孪生刻意免计时开销 |

#### 9. 标题噪声排除说明
以下差异只是层名/标题造成，已排除：各文件首行 //! L12/L13 … 层名与「冠军配方向 X 层移植」措辞；README H1「L12：canonical 层 / L13：命名空间层」与标题块；模块内「L13 自己的增量」「与 L12 共有」等分节标题；测试/基准名中的 l12_*/l13_* 前缀与 bench 标签；mod.rs 顶部 probe_count/twin_mem_stats 等产品化注释。这些不构成实现差异；真正差异已按 §3–§8 归类。

#### 10. 证据锚点表（≥25，覆盖 §2–§8）
| # | 断言 | 锚点 1｜锚点 2｜锚点 3 |
|---:|---|---|
| 1 | decl 七元组（prim 槽 + typ_pretty） | src/L13_namespace/mod.rs:432 ｜ src/L13_namespace/cxt.rs:965-981 ｜ L12 对照 src/L12_canonical/mod.rs:66 |
| 2 | 构造子限定键登记 | src/L13_namespace/elaboration.rs:1875-1882 ｜ src/L13_namespace/elaboration.rs:2926-2948 |
| 3 | 五级名字解析优先级 | src/L13_namespace/elaboration.rs:2916-2917 ｜ :2918 ｜ :2943-2984 |
| 4 | package 设 prefix + namespaces | src/L13_namespace/elaboration.rs:2460-2467 ｜ src/L13_namespace/cxt.rs:333-334 |
| 5 | import 只写 import_map、冲突/单名拒绝 | src/L13_namespace/elaboration.rs:2469-2547 ｜ src/L13_namespace/mod.rs:1469 |
| 6 | inherent 方法 TypeHead.method + symbol_table | src/L13_namespace/elaboration.rs:1887-1930 ｜ :3613 ｜ src/L13_namespace/mod.rs:1459 |
| 7 | Val::Nat 原生表示 | src/L13_namespace/mod.rs:905 ｜ src/L13_namespace/cxt.rs:25 ｜ src/L13_namespace/bump_spine_iter/eval.rs:40-42 |
| 8 | eval 折叠 succ(Nat k) | src/L13_namespace/mod.rs:280-292 ｜ :3551-3559 ｜ src/L13_namespace/bump_spine_iter/eval.rs:618-619 |
| 9 | quote 展开回一元链 | src/L13_namespace/bump_spine_iter/quote.rs:616-617 ｜ src/L13_namespace/bump_spine_iter/rename.rs:490 |
| 10 | 删 Tm::Prim/Val::Prim（L12 有） | L12 src/L12_canonical/mod.rs:88/268 ｜ src/L13_namespace/mod.rs:503-534/886-921（无 Prim） |
| 11 | prim 挂 decl 表并 Cxt::new 注册 | src/L13_namespace/cxt.rs:965-981 ｜ src/L13_namespace/bump_spine_iter/prim.rs:303-339 |
| 12 | SumCase 改 index | src/L13_namespace/mod.rs:912-917 ｜ src/L13_namespace/bump_spine_iter/syntax.rs:43-48 ｜ L12 src/L12_canonical/mod.rs:275-279 |
| 13 | PatternDetail::Con 四字段（index+限定键） | src/L13_namespace/mod.rs:744-756 ｜ L12 src/L12_canonical/mod.rs:128-133 |
| 14 | Call/OpCall 节点 | src/L13_namespace/mod.rs:524-533 ｜ :1314-1338 ｜ src/L13_namespace/pretty.rs:451/776 |
| 15 | 精化载体 σ→update_cxt（链断点） | L12 src/L12_canonical/elaboration.rs:105-124 ｜ L12 src/L12_canonical/mod.rs:288/305-307 ｜ L13 src/L13_namespace/elaboration.rs:781-788、src/L13_namespace/cxt.rs:1327 |
| 16 | 孪生 subst.rs 删除 | L12 src/L12_canonical/bump_spine_iter/subst.rs:1-6 ｜ src/L13_namespace/bump_spine_iter.rs:165-169（明确「无显式替换设施」） |
| 17 | class Phase A/B + PrecheckedItems | src/L13_namespace/elaboration.rs:2552-2697 ｜ :2681-2687 ｜ src/L13_namespace/bump_spine_iter/machine.rs:4868/5005-5024 |
| 18 | BindingName 隐参合成 | src/L13_namespace/cxt.rs:338/1410 ｜ src/L13_namespace/elaboration.rs:500-518 ｜ :1129-1130 |
| 19 | def replay 三件套 | src/L13_namespace/mod.rs:3116-3196 ｜ src/L13_namespace/bump_spine_iter/prim.rs:117-214 ｜ src/L13_namespace/bump_spine_iter/eval.rs:294 |
| 20 | 终止性检查 Level A + allowlist | src/L13_namespace/elaboration.rs:118-131/172-188 ｜ src/L13_namespace/bump_spine_iter/termination.rs:30-57/99-115 ｜ 调用点 src/L13_namespace/elaboration.rs:1445、src/L13_namespace/bump_spine_iter/machine.rs:3765 |
| 21 | eval 预算 + NAT_CHAIN_LIMIT | src/L13_namespace/eval_budget.rs:1-27 ｜ :47/72/77 ｜ :104-144 |
| 22 | 预算 tick 接入两版 eval/quote | src/L13_namespace/mod.rs:3329/3823 ｜ src/L13_namespace/bump_spine_iter/eval.rs:288 ｜ src/L13_namespace/bump_spine_iter/quote.rs:624 |
| 23 | unify Call 快路径/退化臂 | src/L13_namespace/unification.rs:1008 ｜ :1037-1039 ｜ src/L13_namespace/bump_spine_iter/unify.rs:621（三重快照注释） |
| 24 | unify SumCase index + Nat 跨形态 | src/L13_namespace/unification.rs:1144-1145 ｜ :1158-1165 |
| 25 | trait head_index/GENERIC_SELF_HEAD/out 参数 | src/L13_namespace/typeclass.rs:97/100/133/149 ｜ :177-217 ｜ src/L13_namespace/unification.rs:615-674 |
| 26 | 孪生 typeclass 模块重建 | src/L13_namespace/bump_spine_iter.rs:194 ｜ src/L13_namespace/bump_spine_iter/typeclass.rs:1-8/40 |
| 27 | LSP 三表 owned String + 查询 | src/L13_namespace/mod.rs:1408-1413/1549-1554 ｜ src/L13_namespace/elaboration.rs:481/3187 ｜ src/L13_namespace/bump_spine_iter/observe.rs:12/26/54/189 |
| 28 | FORCE_MEMO + 池化 | src/L13_namespace/mod.rs:154-194/3989-4066 ｜ src/L13_namespace/bump_spine_iter/force.rs:202-297/445 ｜ L12 无（静态 grep 0 命中） |
| 29 | 孪生常驻检查点/导出数据面 | src/L13_namespace/bump_spine_iter/entry.rs:41/898/1134/1566 ｜ src/L13_namespace/mod.rs:440 |
| 30 | canonical 与 L12 同构（仅签名适配） | src/L13_namespace/canonical.rs:20-32/63-73 ｜ L12 src/L12_canonical/canonical.rs:19-31/59-79 ｜ src/L13_namespace/elaboration.rs:1601 |
| 31 | 模式编译器下标/限定键/精化回 update_cxt | src/L13_namespace/pattern_match.rs:94/106/631-653 ｜ src/L13_namespace/cxt.rs:1327 ｜ src/L13_namespace/README.md:165-176 |
| 32 | 参考版迭代 Drop 防深链 | src/L13_namespace/mod.rs:536-557/559-690/923-935 |
| 33 | 文档声称与实现对照（行号过期） | src/L13_namespace/README.md:5-9/19-30/76-93/165-176 ｜ 实际 mod.rs:432/905/744-756 |
| 34 | 测试计数口径 | 25 个新增测试文件/15,270 行（.deltawork/pairs/L12--L13.files.tsv）｜ L13 612 与 L12 35 个 #[test]，L13 9 个 #[ignore]（静态 grep） |

#### 11. 给 Lead 的一句话
L13 相对 L12 是产品化重写而非累积优化：名字世界/原生 Nat/prim 挂表/class 两阶段/预算护栏齐备，但 σ 精化载体与 Call 显示节点谱系被拆、README 行号整体失真，链断点在「精化载体」与「孪生模块谱系」两处。

### 9.2 表层（parser / 派生 / prelude / HDL / 测试 / README）

> 单元 delta-l12-l13-surface｜数据源 `.deltawork/pairs/L12--L13.{diff,files,numstat,symbols}.tsv`｜核对时点 HEAD 0464150c
> 分工：核心机（mod/elaboration/unification/cxt/pattern_match/pretty/canonical/typeclass + `bump_spine_iter/**` 机制）由 delta-l12-l13-core 写；本文只写 parser、派生、prelude、HDL 面、tests 与 README，并对孪生新增文件只做清单级对位。
> 口径：行数 = .deltawork 物理行；churn = numstat；测试数 = grep 静态计数 `#[test]`；所有行号均按当前工作树实测。

#### 0. 结论摘要（性质 + 最重要差异 + 链是否连续）

L13 对 L12 的表层是**产品化包装层**：表层新增的代码集中在 parser 宏/派生/class、prelude 装载与 HDL 库、测试基建三块，核心机语义面由 core 单元负责。六条最重要事实：

1. parser 从"L11/L12 的宏解析器"扩成**产品语言前端**：`Decl` 5→9 变体（+Package/Import/Derive/Class），新 `parser/derive.rs`(1411) 落 Show/Bundle/HdlEnum/IMasterSlave 四个派生，class 解析+两阶段展开入口进 parser（§3.1–3.2）。
2. **package/import/class 三个关键字在 L12 已词法化但未解析**——L12 lex.rs:22-24 与 L13 同行，L12 `Decl` 无对应变体、parser 无 `p_package/p_import/p_class`；L13 是把"潜伏语法"激活，不是新造词法（§3.1）。
3. HDL 产品面**不在 parser 里**：`module/blackbox/when/Expr` 全是 `src/prelude/hdl/hdl-macros.typort` 的 `macro_rules`（:769/:222/:287/:366），HDL 自检码 HDL0xx 也全在 `.typort`（223 处）；Rust 侧只提供 `#[derive(..)]`、class/struct 语法与 15 个内建（§3.3）。
4. prelude 从 L12 的 **23 个内联 include_str!** 变为 **35 个共享常量表**（CORE 15 + HDL 19 + show 1），新增 calc.typort 与 11 个 hdl 文件；同时新增 PreludePool 跨线程复用、stdout→stderr 修正（§4）。
5. 测试面爆炸：L12 全层 35 个 `#[test]` → L13 **612 个**（+577），33 个新增文件里 25 个是测试文件（15270 行）；但 **README §7 仍写"341 个"**，其自列 9 个模块的现值已是 354（§2、§7.3）。
6. 表层无机制丢失，属"连续扩张 + 载体重组"；两处断点都在工程侧：`run_with_prelude` 的 path_id 硬编码 24（§6-1）、README 数字/行号全面过期（§7.3）。

#### 1. 规模与文件级变化

L13 目录 59 个 .rs / 59378 物理行，L12 为 27 个 / 19603（+39775 行）；numstat churn **+48181 / −8365**（净 +39816，与物理行差 41 行属增删计数口径差）。changed 25、added 33、removed 1。

| 文件 | 状态 | A→B 行 | churn +/- | 一句话性质 |
|---|---|---:|---|---|
| `parser/mod.rs` | changed | 2592→4637 | +2477/−432 | package/import/class/derive 解析 + Q1/Q2/Q3 解析质量修复 + 28 个 parser 内测试 |
| `parser/derive.rs` | **added** | –→1411 | +1411 | 新派生引擎：Show/Bundle/HdlEnum/IMasterSlave |
| `parser/syntax.rs` | changed | 253→356 | +112/−9 | `Raw::Tm` + 手写 Eq/Hash；`Decl` 5→9 变体（+4）；`ClassItem` |
| `parser/lex.rs` | changed | 406→455 | +60/−11 | EndLine 携带下一行缩进、`endline_indent` |
| `parser/macros.rs` | changed | 358→381 | +27/−4 | `get_used_metavars` 可见性微调 |
| `mod.rs` | changed | 2796→8526 | +7734/−2004 | prelude 常量表/PreludePool、测试模块声明（其余机制归 core 单元） |
| `README.md` | changed | 414→455 | +440/−399 | 重写为"产品层"叙事；数字与行号大量未同步 |
| 25 个 `*_tests.rs` 等 | **added** | –→15270 | +15270 | 测试基建（§7.1） |
| `eval_budget.rs` | **added** | –→144 | +144 | 协作式求值预算 + Nat 链分配护栏 |
| `bump_spine_iter/{compact,observe,prim,termination,typeclass,debug}.rs` | **added** | –→4823 | +4823 | 孪生单文件拆分（2026-09-23）；机制细节归 core 单元 |
| `bump_spine_iter/subst.rs` | **removed** | 250→– | −250 | σ 载体移除（性质归 core 单元） |

新增 33 文件分组（行数合计 21648）：**测试材料 25 个 15270 行**（含 legacy_tests 5420、module_tests 1051、class_tests 805、hdl_check_graph_tests 862、prelude_hdl_b/c 622/678、debug_test 440、struct_refine_probe 285、bare_ctor_member_tests 126 等）；**推导引擎 parser/derive.rs 1411**；**eval_budget.rs 144**；**孪生拆分 6 文件 4823**。删除仅 `bump_spine_iter/subst.rs`。

src/prelude 侧：仓库共 35 个 `.typort`（core 6 / data 9 / hdl 19 / show 1），L13 **逐一消费**；L12 只消费 23 个（14 core-data + 8 hdl + show）。

#### 2. 标题宣称的增量：声称 vs 实现

| # | README 声称（行） | 实现锚点 | 判定 |
|---|---|---|---|
| 1 | 宏深度守卫 `MAX_MACRO_EXPANSION_DEPTH = 256`（`parser/mod.rs:139`） | src/L13_namespace/parser/mod.rs:258（值确为 256；行号过期；L12 在 142 行） | 部分：值对、行号失真 |
| 2 | decl 表七元组（`mod.rs:309`） | src/L13_namespace/mod.rs:432 七元组 `(Span,Rc<Tm>,Rc<Val>,Rc<Ty>,Rc<VTy>,Option<PrimFunc>,String)` | 部分：结构对、行号失真 |
| 3 | package/import 在 `elaboration.rs:1869-1957` | 实现分发在 src/L13_namespace/elaboration.rs:2460 / :2469 | 部分：功能在、行号失真 |
| 4 | class 两阶段"（`elaboration.rs:1961` 起）" | src/L13_namespace/elaboration.rs:2552（Phase B 调用 `parser::expand_class_decls`） | 部分：功能在、行号失真 |
| 5 | 观察表 `hover_table mod.rs:1191` / `hover_entry_at 1316` | src/L13_namespace/mod.rs:1431 / :1550 | 部分：功能在、行号失真 |
| 6 | PreludeSlot/Pool（`mod.rs:3514-3569`） | src/L13_namespace/mod.rs:4017(pool) / :4029(slot) / :3989-3991(TLS) | 部分：功能在、行号失真 |
| 7 | 每测试线程重装 "~24 文件 prelude" | 实为 **35** 文件（mod.rs:4103-4119 15 + :4122-4148 19 + :4151 1） | 未实现/失真：24 是旧口径残影 |
| 8 | lib 测试"共 341 个"（legacy 129…module_probe 2） | 实测 **612**；README 自列 9 模块现值 **354**（legacy 138/class 35/verilog_compat 25）；且漏报 17 个新测试模块 | 未实现/失真 |
| 9 | `l13_fast_parity` "12 个 #[test]" | tests/l13_fast_parity.rs 实测 15 | 部分：数字失真 |
| 10 | 单行枚举声明不在语言面 | tests/l13_fast_parity.rs:11-17（同错假阴性说明）；枚举臂分隔用 `many0_sep(kw(EndLine))`（src/L13_namespace/parser/mod.rs:2258、:2281） | 一致（属共用 parser 形态约束，非 L13 新增） |
| 11 | HDL prelude 是产品面、LSP 宿主 | src/lib.rs:68-69 声明 L13 为 pub 模块、:100-104 LSP 直接用其 parser/pretty；HDL 面在 `.typort`（§3.3） | 一致 |

#### 3. 语言/语法/内建/HDL/LSP 面增量

##### 3.1 语法面：三个潜伏关键字被激活 + 派生/class 成为一等声明

- **词法早已存在**：`package/import/class` 在 L12 与 L13 的 `parser/lex.rs:22-24,113-114,131` 完全一致（L11 同）；差异在解析层——L12 `parser/syntax.rs:226-253` 的 `Decl` 只有 **5 变体**（Def/Println/Enum/TraitDecl/ImplDecl），无 Package/Import/Class/Derive；L13 `parser/syntax.rs:291-348` 增至 **9 变体**，新增 `Package{path}`(:292)、`Import{prefix,names,wildcard}`(:295)、`Derive{traits,decl}`(:338)、`Class{name,params,items,traits}`(:342)。
- 解析入口：`p_package` parser/mod.rs:3020、`p_import` :3037（支持 `ns._` / `ns.{A,B}` / `ns.A` 三种形态，:3051-3066）、`p_derive_attr` :3069（`#[derive(A,B)]`）、`p_class` :3377、`p_impl` :2467（inherent impl 新字段见 syntax.rs:326-336）、`p_trait_def` :2409 / `p_trait_body_item` :2334（supertraits/assoc_defaults）。
- 语义分发：Package/Import 在 src/L13_namespace/elaboration.rs:2460 / :2469 落到 `namespace_prefix`/`import_map`（机制归 core 单元与 README §1.2）。

##### 3.2 派生面（新文件 = 新语言面）

`parser/derive.rs` 注册表 `default_derive_registry()`（:18-24）含 `Show`(:926) / `Bundle`(:583) / `HdlEnum`(:1374) 三项；`IMasterSlave` 不走注册表，由 `expand_derives` 两遍扫描特判（parser/mod.rs:3225、:3230-3261；方向规格解析 derive.rs:688-732、校验 :736+、生成 :790+）。展开时机 = `parser_with_macros` 收尾（parser/mod.rs:511/516）与 `parser()`（:462-466），即**解析期语法糖**，不占核心机。

- Bundle：生成 `:="<>` impl、`Into[Self]`、带隐参 `bn: BindingName` 的 `Name.create`（derive.rs:594-623,643-667）；嵌套 bundle 经 `BundleSet`（:12-16）识别。
- HdlEnum：仅接受无参非空 enum（:1374-1382），生成 count/elems/ordinal/craft/craftAs/reg/regInit + Into/Eq 共 10 组 def（:1400-1410）。
- Show：struct 与多 case enum 两条路径分开生成（:942-952，注释记录 2026-10-11 R5 修复）。

##### 3.3 HDL 面：库而非内核特性

- `module` 宏 `src/prelude/hdl/hdl-macros.typort:769`，其 typort 臂展开为 `class Name [cd: ClockDomain] … impl Module { … def tree }`（:824 起）；Verilog-compat 臂在 :788-817；`blackbox` :222、`when` :287、`Expr` :366 同为宏。即 **parser 里没有 module/blackbox/fsm/stream 关键字**（grep 0 命中），HDL 语法 = 宏 + class/struct + derive。
- HDL 自检（HDL0xx）在 prelude 实现：src/prelude/hdl 共 223 处 HDL0xx，分布 hdl-check-graph 76 / hdl-check 70 / hdl-fsm 56 / hdl-enum 9 / hdl-macros 5（其余分散）；Rust 侧只留 `report_check_issue` 内建（cxt.rs，core 单元）。
- Verilog 兼容语法进 parser：尺寸字面量 `8'h2A`（`sized_lit_value` parser/mod.rs:1250，表达式入口 :1177，绑定强度 `'` :1291）、归约前缀算符 `&a/|a/^a`（:1264-1268）、拼接 `{a,b}`（`p_concat` :928）；语料见 examples/hdl/23-verilog-compat.typort、`verilog_compat_tests.rs`(25 test)、`hdl_stream_fix_tests.rs`(11 test)。
- 27 个 examples/hdl/*.typort 是 HDL 面真实语料（module_probe_tests.rs:7-21,42 逐一 include_str!）；`#[derive(Bundle)]` 用例集中在 examples/hdl/10-bundle.typort:19 起等 13 处。

##### 3.4 解析质量增量（Q1/Q2/Q3 与错误/护栏）

| 增量 | 实现 | 相对 L12 |
|---|---|---|
| Q1 单实参括号"逃逸哨兵"摊平（`f n (x) (y)` 读作 `f n x y`） | `SPINE_ESCAPE` parser/mod.rs:1359、`unescape_spine` :1420、`strip_spine_escapes` :1368、结算 :1499-1523 | 新增；L12 无哨兵机制 |
| Q2 缩进感知续行（同缩进断开，calc 步骤不被吞） | `MacroState` 第 4 元锚点 :239、`spine_continuation` :1436、`p_spine` :1467-1497、lex `endline_indent` lex.rs:290、EndLine 携带缩进 lex.rs:294-313 | 新增；L12 EndLine 不携带行布局 |
| Q3 宏展开错误落回源码 | `ExpansionSpan` :322-328、`owned_tokens_to_string_mapped` :334、re-lex 后按映射还原 span :1840-1876 | 重写；L12 走 `borrowed_tokens_to_string`+splice（符号表已删） |
| 空文件/纯注释文件合法 | `many0_sep_skip` :374/:403、调用 :499-502 | 新增；L12 `many1` 会在空编辑器上报 "expected at least one element" |
| 大数字面量护栏/宏错误提示 | `NAT_LITERAL_ELAB_LIMIT` :85 + 拒绝臂 :842/:862；MT18 ascription 提示 :679-715 | 新增；L12 无这两个符号 |

##### 3.5 LSP 面（表层部分）

`MacroExpansionInfo` 的 `def_start/end_offset/def_path_id`（parser/mod.rs:23-29）**在 L12 已存在**（L12 同名同字段 :10-30），故 goto-definition 的宏定义定位不是 L13 新增；L13 的 LSP 表层增量在（a）`pub mod lex` 公开词法（parser/mod.rs:33）供测试/工具读 `endline_indent`；（b）派生/class 展开后的 `Raw::Tm` 复用使观察面 hover 能覆盖 class 生成物（core 单元验证）；（c）lib.rs 直接消费 L13 parser/pretty（lib.rs:100-104）。观察面三表本身见 core 单元。

#### 4. 核心机制与实现性改动（表层子系统：A 怎么做 → B 怎么做）

| 子系统 | L12 做法 | L13 做法 | 锚点 | 动机/后果 |
|---|---|---|---|---|
| parser 状态 | `MacroState = (errs, Rc<FxHashMap<String,Rc<Vec<MacroRule>>>>, expansions)`，快照 O(1) | 4 元组：**owned std `HashMap`** + 续行锚点 u32 | L12 parser/mod.rs:136（类型）、:133（Rc 快照注释）；L13 parser/mod.rs:239、:1884/:2225/:3797 三处 `state.1.clone()` | 换取可变宏表（派生/class 展开期插入）与缩进锚点；代价是每次递归解析克隆整张宏表且用 SipHash [推断：宏密集输入（HDL prelude 35 文件、宏展开数百次）解析成本上升，需 bench 证实/证伪] |
| 宏展开文本 | 借用 token 拼接/splice（`borrowed_tokens_to_string`、`splice_push`、`splice_transcriber`） | owned token 拼串 + re-lex + ExpansionSpan 回映射 | 删除符号见 .symbols.tsv；新增 parser/mod.rs:322-365、:1840-1876 | 错误指向用户源码（LSP 质量↑）；每次展开多一次 String 分配 + 一次词法 [推断：小常数开销] |
| 派生展开 | 无（无 derive 语法） | 解析后处理两遍扫描；`ErrMsg::Custom` 报 derive 错误；class 派生走 legacy 展开 | parser/mod.rs:3225（两遍 :3230-3261）、:3213-3218（class 派生注释） | 语法糖工程化：派生失败不阻断其余 decl（恢复式解析延续） |
| class 两阶段 | 无 class 声明 | Phase A 预检入 `PrecheckedItems`（parser/mod.rs:3441），Phase B 走共享 `expand_class_decls`（:3453），生成物用 `Raw::Tm` 引用已检查项（syntax.rs:113-118 + 手写 Eq/Hash :121-171） | L12 syntax.rs:91 `Raw` derive(PartialEq) 无 Tm 变体；L13 syntax.rs:124/:149 | 一次 elaboration；代价：`Raw` 失去 derive 的结构比较，Eq 对 `Tm` 退化为指针比较（:143/:168） |
| prelude 装载 | `run_with_prelude` 内联 23 个 include_str!，顺序手写 | 三张 pub(crate) 常量表 + `load_prelude_state_impl` + `parse_prelude_files` 共享给 bench/孪生 | L12 mod.rs:1307-1358；L13 mod.rs:4103/:4122/:4151、:4226-4294、:4175 | 单一事实源；bench/孪生不再抄第三份（mod.rs:4098-4099 注释） |
| prelude 缓存 | 无（每次整套 elaborate） | thread-local `PRELUDE_CACHE` + 进程级 `PreludePool` 独占交接；`TYPORT_NO_PRELUDE_POOL=1` 可禁用 | mod.rs:3988-3991、:4017-4041、:4052+ | libtest 每测试一线程时避免重复装载（~1.5s/次）；unsafe Send 由注释论证（:3994-4015） |
| prelude 加载输出 | 解析错误/进度 `println!` 走 stdout | 解析错误 `eprintln!`（:4258-4263），PPROF 走 stderr（:4277/:4285） | L12 mod.rs:1344-1345、:1361-1365 | 防 LSP 的 JSON-RPC stdout 被污染（L13 才把该入口接进产品生态） |
| 内建注册时机 | 无 nat 算术 prim / vconnT | nat.typort 之后 `register_nat_builtins`（mod.rs:4248/:4291-4293），prelude 之后 `register_vconn_builtin`（:4295-4297），再建短名别名表（:4299-4320） | 同左 | 类型需先存在（README §1.2 声称，实现一致） |
| 观察面/测试钩子 | L12 mod.rs 无 `#[cfg(test)]`（0 处） | 25 个外置测试模块声明（mod.rs:350-425）+ 2 个内联测试模块（:7745、:8371） | 同左 | 测试与产品代码分离，单文件 2796→8526 的主因之一 |

#### 5. 参考版 ↔ 孪生版同步差异（表层视角）

| 项 | 参考版 | 孪生版 | 判定 |
|---|---|---|---|
| parser / pretty / preprocess / Synth | 共享 | 共享（模块头自述） | 同步；bump_spine_iter.rs:69-70 |
| 派生/class 生成物 | `expand_derives`→`Decl`；Phase B `expand_class_decls`（parser/mod.rs:3225/:3453） | 同一共享 parser 产物 + `Raw::Tm` 指针导入复用（模块头 :44-51） | 同步，孪生多一层指针桥 |
| prelude 池化 | PreludeSlot/Pool（mod.rs:4017-4069） | **无池化**，每 kick 从 prime 重放（bump_spine_iter.rs:74-75） | 有意不对称 |
| canonical/iddfs、FUNC_PROF 计时、Tm/Val 迭代 Drop | 有 | 不移植（bump_spine_iter.rs:84-90） | 有意不对称 |
| 单文件 vs 拆分 | 一直分文件 | L13 把 15k 单文件拆成入口+16 子模块（2026-09-23），新增 compact/observe/prim/termination/typeclass/debug | 载体重组；6 个新文件均为"逐行搬运+新增节"（各文件头 :1-8），细节归 core 单元 |
| 观察面测试 | 无独立表互检模块；靠 tests/twin_engine_tests.rs(28 test) 集成比对 | bump_spine_iter/observe.rs:205-206 内 `observation_tests`(21 test) | 测试放两侧：为何集成测试必须放 tests/ 见 tests/hdl042_engine_tests.rs:3-13（`#[path]` 编译进 bench/parity 目标时 `crate::Backend` 不存在） |
| 终止性检查 | 内联 elaboration.rs:172 / 调用 :1445 | 模块 bump_spine_iter/termination.rs（`mod` :193） | 同判据双实现，注释声明"逐句对齐"（elaboration.rs:102），回归钉 termination_check_tests(13) |

#### 6. 回退/丢失/弱化清单

| # | L12 中的功能/机制/守卫/测试 | L13 状态 | 锚点 | 影响 |
|---|---|---|---|---|
| 1 | `run_with_prelude` 用 `prelude.len()` 作主文件 path_id（=23，与 prelude 文件 id 0..22 不冲突） | 硬编码 `24`，而 prelude 装载占 id 0..34（35 文件） | L12 mod.rs:1358 vs L13 mod.rs:4568、:4247/:4287 | **[可疑→事实]** 测试专用入口的 path_id 与 hdl-utils(第24号) 撞号；多文件 span 的 path_id 归属可能错（生产 LSP 走 `now_id`，lib.rs:1937/:2546，不受影响） |
| 2 | 宏表快照 O(1) + FxHash 查表 | owned `std::HashMap` + 每次递归克隆 | L12 parser/mod.rs:4/:133 vs L13 parser/mod.rs:4/:1884 | 宏密集/派生多的 HDL prelude 解析可能变慢 [推断，未跑 bench] |
| 3 | 借用 token splice 宏展开 | 已删，改 owned+re-lex | .symbols.tsv 删除 3 符号；新增 parser/mod.rs:334 | 功能等价且 span 更准，但单次展开多一次分配+lex [推断:小] |
| 4 | README 数字/行号（测试数、prelude 文件数、各类 `xxx.rs:NNN` 指路） | 全面过期（§2 表 8 处可核验失真） | README.md:24/:39/:59/:106-108/:251-253/:293-299/:416-422 | 新读者被误导；设计取舍叙事变成文档债务 |
| 5 | L12 无 `#[ignore]` | L13 有 1 个真实 `#[ignore]`（慢探针写工作目录） | module_probe_tests.rs:4 | 门禁不含慢探针（有意，注释说明） |
| 6 | 单行枚举声明"两版同错" | 仍未修（语言面缺口） | 同上 §2-10；l13_fast_parity.rs:11-17 | parity 全绿不等于覆盖（README §6.2 诚实登记） |
| 7 | 派生错误只在 parse 期报 | 新增 derive `ErrMsg::Custom`（parser/mod.rs:174-178/:3225） | 同左 | 不回归；错误既入 parse 错误账也进 LSP 诊断 |

说明：语义级回退（如 `subst.rs` 删除、`Tm::Prim/Val::Prim` 移除）属 core 单元判定范围，本文不重复。

#### 7. 测试与文档变化

##### 7.1 lib 测试（口径：`grep "#\[test\]" src/L13_namespace/**/*.rs`）

- 总量：L12 **35**（mod.rs 21、parser/mod.rs 13、parser/lex.rs 1）→ L13 **612**（29 个文件有测试）。拆分：25 个外置测试模块（mod.rs:350-425，共 463 test）、mod.rs 内联 77（含 `prelude_tests` :7745、`symbol_recovery_tests` :8371）、孪生 `observation_tests` 21（observe.rs:206）+ 孪生零散 4；余下 47 为参考版分文件内联测试（pretty.rs 18、parser/mod.rs 28、parser/lex.rs 1）。[口径核对：463+77+21+4+47=612]
- 新增测试家族（行数 / `#[test]`）：legacy_tests 5420/138（旧 mod.rs 内联测试的整体搬迁+扩写）、module_tests 1051/39、class_tests 805/35、hdl_check_graph_tests 862/31、prelude_hdl_c 678/12、prelude_hdl_b 622/11、hdl_fsm 660/18、hdl_enum 500/17、verilog_compat 458/25、debug_test 440/15（多为 println 探针，非硬断言 [推断：探针用途]）、prelude_stdlib 416/9、hdl_blackbox 519/14、calc 372/19、hdl_stream_fix 363/11、hdl_assert 302/8、prelude_data 288/8、struct_refine_probe 285/4、termination_check 274/13、cong_projection 203/7、eval_budget_tests 179/6、prelude_core 144/4、prelude_hdl_a 134/3、bare_ctor_member 126/6、prim_safety 115/8、module_probe 54/2。
- 门禁相关：1 个 `#[ignore]`（module_probe_tests.rs:4）；HDL 测试全部 `run_with_prelude`（参考版口径），双引擎 HDL 行为另由集成测试钉（tests/hdl042_engine_tests.rs:1-22，2 test）。

##### 7.2 tests/ 下 L13 套件（仓库级集成测试，不参与 pairs diff 文件级表）

| 套件 | test 数 | 作用 | 锚点 |
|---|---:|---|---|
| tests/l13_fast_parity.rs | 15 | L13 双 oracle Ok 逐字节/Err 判定；`#[path]` 直编 L13（+list/bimap/parser_lib） | :1-4, :28-40 |
| tests/twin_engine_tests.rs | 28 | Engine::Twin 的 LSP 接线（hover/completion/goto/inlay）对参考版比对 | :1-7 |
| tests/namespace_tests.rs | 30 | import_map 文件局部可见性/诊断（命名空间阶段 1） | :1-8 |
| tests/hdl042_engine_tests.rs | 2 | HDL042 双引擎回归钉（F1 假阳性） | :1-22 |
| tests/known_bug_pins.rs | 8 | 已知缺陷钉 | — |

##### 7.3 README 变化与过期声明

README 414→455 行（+440/−399，几乎重写）：新增产品层叙事（LSP/HDL/prelude）、§1.1-1.5 语言特性、§3 LSP 观察面、§4 孪生设计、§6 诚实清单；删除 L12 的 canonical/iddfs 主线叙事。但**行号与数字未随重构更新**：§2 列出 8 处可核验失真（README.md:24/39/59/106-108/251-253/293-299/416-422），其中测试数 341 vs 612、prelude 24 vs 35、宏深度守卫 :139 vs :258、decl 表 :309 vs :432 影响最大。另 README:422 "12 个 #[test]" vs 实际 15。

#### 8. 工程性/性能/健壮性改动

| 项 | 改动 | 锚点 | 影响 |
|---|---|---|---|
| 求值预算 | 新增协作式 deadline（每 2^20 次迭代 checkpoint，`panic_any(ElabTimeout)`，边界 catch_unwind 识别；`scope` 只收紧） | eval_budget.rs:1-26、:31-33 | 拦"迭代多"的挂死；prelude prime 不设预算（:23-26） |
| Nat 链分配护栏 | `NatChainOverflow` + `NAT_CHAIN_LIMIT`（与预算无关、无条件生效） | eval_budget.rs:15-40 | 拦 `nat_mul 100000 100000` 这类提交量爆炸（注释记 121.8GB 事故） |
| Nat 字面量上限 | parser 拒绝 `> 100_000` | parser/mod.rs:85、:842、:862（含双入口栈预算实测表 :49-75） | 把原生栈溢出变成诊断；typort 入口对齐 1024MiB worker |
| 宏自递归守卫 | 保持 256 上限（RAII 深度守卫） | parser/mod.rs:258-301 | L11/L12 同款；L13 仅位置移动 |
| 空编辑器可用 | 空/纯注释文件解析为 0 decl | parser/mod.rs:374/:499-502 | LSP 新建缓冲区不再报错 |
| 预加载输出通道 | stdout→stderr | L13 mod.rs:4258-4263 vs L12 mod.rs:1344 | 防 JSON-RPC 通道污染 |
| PreludePool | TLS 缓存 + 跨线程池化 + `TYPORT_NO_PRELUDE_POOL` 诊断开关 | mod.rs:3988-4069 | libtest 并行套件提速；unsafe Send 有专门安全性论证（:3994-4015） |
| 共享 prelude 表 | bench/twin/ref 三方同源 | mod.rs:4098-4101、:4103/:4122/:4151 | 消除三份副本（旧实现各抄一份） |
| 测试架构约束 | `#[path]` 直编 L13 的目标里无 `crate::Backend`，故双引擎集成测试必须放 tests/ | tests/hdl042_engine_tests.rs:3-13 | 解释 25 个 src 内测试文件 + tests/ 集成测试的分工 |
| 可疑残留 | path_id 24 硬编码（§6-1）；README 数字（§7.3）；module_probe 写工作目录文件 probe-out.txt | mod.rs:4568；README.md:416-422；module_probe_tests.rs:4 | 待 Lead 裁决是否记为 bug |

#### 9. 标题噪声排除说明

以下差异只是章节标题/层名/目录标签造成，已排除、不计入增量：README H1 "L13：命名空间层（生产版…）"与 L12 的 H1 差异；`L12_canonical`→`L13_namespace` 路径改名（pairs diff 的 a/ b/ 前缀）；所有 `//! L13 的增量`、模块名注释、bench 负载名（l13bench/l13_fast_parity）；`bump_spine_iter.rs` 里"移植自 L12 冠军配方"的机制描述（机制本身在 L12 已存在）；parser/lex 中从 L11/L12 原样继承的注释块（只计新增 `NAT_LITERAL_ELAB_LIMIT`、`endline_indent`、`SPINE_ESCAPE` 等可核验符号）。相邻两层共有的 parser/pretty/preprocess 属"每层目录各自 copy"，不是 L13 增量。

#### 10. 证据锚点表（≥25 条，覆盖 §2–§8）

| # | 断言 | 锚点 |
|---|---|---|
| 1 | L12 全层仅 35 个 `#[test]`（mod 21/parser 13/lex 1） | src/L12_canonical/mod.rs:1513（首个测试）、src/L12_canonical/parser/mod.rs:2218（首个测试） |
| 2 | L13 全层 612 个 `#[test]`，README 称 341 | src/L13_namespace/legacy_tests.rs:3、src/L13_namespace/mod.rs:350-425 |
| 3 | README 的测试清单少报 16 个新模块 | README.md:416-421 |
| 4 | README 称 legacy 129/class 32/verilog_compat 24，实测 138/35/25 | src/L13_namespace/legacy_tests.rs、class_tests.rs、verilog_compat_tests.rs |
| 5 | l13_fast_parity 声称 12 test，实测 15 | README.md:422；tests/l13_fast_parity.rs:1-40 |
| 6 | Decl 5→9 变体 | src/L12_canonical/parser/syntax.rs:226-253；src/L13_namespace/parser/syntax.rs:291-348 |
| 7 | package/import/class 关键字 L12 已词法化未解析 | src/L12_canonical/parser/lex.rs:22-24,113-114；src/L13_namespace/parser/mod.rs:3020/:3037/:3377 |
| 8 | 派生注册表 Show/Bundle/HdlEnum | src/L13_namespace/parser/derive.rs:18-24 |
| 9 | IMasterSlave 方向规格解析/校验/生成 | src/L13_namespace/parser/derive.rs:688/:736/:790 |
| 10 | derive 展开在解析期两遍扫描 | src/L13_namespace/parser/mod.rs:3225、:3230-3261 |
| 11 | HdlEnum 生成 10 组 def | src/L13_namespace/parser/derive.rs:1374-1410 |
| 12 | class 两阶段载体 PrecheckedItems/expand_class_decls | src/L13_namespace/parser/mod.rs:3441/:3453；src/L13_namespace/elaboration.rs:2552 |
| 13 | `Raw::Tm` 与手写 Eq/Hash | src/L13_namespace/parser/syntax.rs:113-118、:124/:149 |
| 14 | Q1 哨兵常量与摊平 | src/L13_namespace/parser/mod.rs:1359、:1420、:1499-1523 |
| 15 | Q2 缩进续行锚点/判据/EndLine 缩进 | src/L13_namespace/parser/mod.rs:239、:1436、:1467-1497；src/L13_namespace/parser/lex.rs:290 |
| 16 | Q3 ExpansionSpan 映射回源码 | src/L13_namespace/parser/mod.rs:322-328、:334、:1840-1876 |
| 17 | 空文件合法（many0_sep_skip） | src/L13_namespace/parser/mod.rs:374、:499-502 |
| 18 | NAT 字面量 100k 上限 + 拒绝臂 | src/L13_namespace/parser/mod.rs:85、:842、:862 |
| 19 | 宏深度上限 256 实际 258 行（README 指 139） | src/L13_namespace/parser/mod.rs:258；README.md:106-108 |
| 20 | macro 状态 owned HashMap + 三处克隆（L12 为 Rc 快照） | src/L13_namespace/parser/mod.rs:239、:1884/:2225/:3797；src/L12_canonical/parser/mod.rs:136、:1302 |
| 21 | L12 23 个内联 prelude vs L13 35 个表项 | src/L12_canonical/mod.rs:1311-1335；src/L13_namespace/mod.rs:4103-4119、:4122-4148、:4151 |
| 22 | PreludeSlot/PreludePool 与禁用开关 | src/L13_namespace/mod.rs:3988-3991、:4017-4041、:4052+ |
| 23 | nat 内建/vconnT 注册时机与短名别名 | src/L13_namespace/mod.rs:4248、:4291-4297、:4299-4320 |
| 24 | prelude 解析错误改 stderr | src/L13_namespace/mod.rs:4258-4263；src/L12_canonical/mod.rs:1344-1345 |
| 25 | HDL 宏全部在 prelude .typort（module/blackbox/when/Expr） | src/prelude/hdl/hdl-macros.typort:769/:222/:287/:366 |
| 26 | HDL0xx 自检码在 prelude（223 处） | src/prelude/hdl/hdl-check-graph.typort、hdl-check.typort、hdl-fsm.typort（grep 统计） |
| 27 | Verilog 兼容字面量/拼接进 parser | src/L13_namespace/parser/mod.rs:1250、:1177、:1291、:928 |
| 28 | 33 个新增文件/25 个测试文件/15270 测试行 | .deltawork/pairs/L12--L13.files.tsv（added 段）；legacy_tests.rs:1、module_tests.rs:1 |
| 29 | 孪生 6 新模块为 2026-09-23 拆分（逐行搬运） | src/L13_namespace/bump_spine_iter/{compact,observe,prim,termination,typeclass,debug}.rs:1-8 |
| 30 | 孪生无 PreludePool/canonical/iddfs（有意不对称） | src/L13_namespace/bump_spine_iter.rs:74-90 |
| 31 | 观察面自检在孪生 observe.rs，双引擎测试必须在 tests/ | src/L13_namespace/bump_spine_iter/observe.rs:205-206；tests/hdl042_engine_tests.rs:3-13 |
| 32 | run_with_prelude path_id 硬编码 24（L12 为 prelude.len()） | src/L13_namespace/mod.rs:4568、:4247、:4287；src/L12_canonical/mod.rs:1358 |
| 33 | eval_budget 两种护栏 | src/L13_namespace/eval_budget.rs:1-40 |
| 34 | README 行号/结构引用大面积失真（8 处） | README.md:24/:39/:59/:106-108/:251-253/:293-299/:416-422 |
| 35 | L13 是 LSP 宿主：lib.rs 直接用其 parser/pretty | src/lib.rs:68-69、:100-104 |

（口径说明：#1/#2/#4/#8 的计数是 grep 静态计数 `#[test]` 的全量结果（L13 29 个文件逐个计数求和 612），行号锚点只给首个测试做定位；其余锚点均已 read/grep 当前文件核对。）

#### 11. 给 Lead 的一句话

L13 表层 = 潜伏语法激活 + 派生/prelude/HDL 产品化 + 测试基建爆炸；机制无丢失，债务集中在 README 数字/行号与 run_with_prelude 的 path_id 24 硬编码。

## 10. 跨层审计：65×8 文件谱系 / 机制载体谱系 / copy-forward 断点总账

> 单元 audit-cross-layer｜数据源 `.deltawork/presence-matrix.tsv`、`.deltawork/inventory/*`、`.deltawork/pairs/*`、`docs/compare-l07-l13/{FACTS,CROSS}.md`｜核对时点 HEAD `0464150c`（2026-11-11），工作树仅 `.deltawork/` 未跟踪。
> 口径：行数=.deltawork 物理行；"代码命中"=Node 全层 `*.rs` 逐行正则计数且**剔除整行注释**（`//`/`///`/`//!`）；"raw"=含注释。测试数=静态 `^\s*#\[test\]`。本审计不替代各对单元，只做"链"的总账。

### 0. 结论摘要（≤10 行）

1. **这不是一条单调 copy-forward 链**：L07↔L13 之间文件集每步都有增删（6 个有变化的边界共 **+46/−8 个 relpath**，净 +38；65=60 现存 +5 仅旧层有），机制层至少 5 处"换载体/回退"。
2. **最大断点（S1）**：L13 参考版与孪生版同时放弃 L07–L12 的 σ 精化载体（`Subst`/`Val::VSub`/`frcs`/`SpecSolve`/`wrap_sub`），回到 `update_cxt`+`refresh`。σ 簇代码命中 L07 202 → L12 125 → **L13 0**；旧载体 L13 = 24。L13 自述见 `src/L13_namespace/bump_spine_iter.rs:165`、`src/L13_namespace/README.md:165`（§2.3 承认分叉）。
3. **S1**：`struct_eq` 机制 L09 起消失，L09–L13 五个孪生模块头都写"结构比较由 unify 快路径承担"（`src/L09_mltt/bump_spine_iter.rs:82`、`src/L10_typeclass/bump_spine_iter.rs:111`、`src/L11_macro/bump_spine_iter.rs:107`、`src/L12_canonical/bump_spine_iter.rs:133`、`src/L13_namespace/bump_spine_iter.rs:166`）——是"宣称等价"，不是实测等价，全部 [未核实]。
4. **S1**：值/项载体来回换：`Val::Prim` 形态 L07(name,spine)→L09 单元→L10(PrimFunc)→**L13 删除入 decl 表**；`Val::Match` 的 pending 字段在 L13 消失；`Val::Call` 实参从 `Vec<Rc<Tm>>`(L12) 改为 `List<(Rc<Val>,Icit)>`(L13)。
5. **S1**：名字世界载体四次换：L06/L07/L08 `NameState` → L09/L10 `BiMap src_names`+`Infer::global_names` 哨兵 → L11/L12 `NameState`（L12 加撤销轨迹）→ L13 回 `Rc<BiMap>`+refresh。**copy-forward 的"回溯式复制"痕迹最重的一处**。
6. **S2（守卫）**：`MATCH_CMP_BUDGET=64` 只在 L07/L08；`PM_FUEL` 只在 L09–L12 孪生；L13 换成 `eval_budget`/`NAT_CHAIN_LIMIT`。`UNIFY_FUEL=4096` 七层同值但 L08 起从常量变成 per-Cxt `Cell`（`unify_fuel`）——"都有 4096"不是同等防护。
7. **S3（测试）**：参考版 src 内 `tests.rs`（L07 2355 / L08 2019 行）在 L09 被删；L09–L12 只剩 inline `#[test]` 10/25/33/35 个 + 各一层 `tests/lXX_fast_parity.rs`；L13 以 25 个 `*_tests/probe` + `eval_budget.rs`（root 层 26 个新文件）**一次性回填**（inventory test 15270 行、静态 612 个 `#[test]`）。
8. **S4（文档）**：L13 孪生头"继承 L05-L12 的全部机制"（`src/L13_namespace/bump_spine_iter.rs:3`）与其下载明"本层没有 subst / struct_eq"（同文件 :165-166）自相矛盾；L13 README 声称 341 个 `#[test]`（`README.md:417`），静态实测 612。
9. 前序文档基线是 `8443586e`（2026-11-08），到当前 HEAD 之间 L07–L13 有 **62 文件 +2676/−1168** 改动 ⇒ 至少 4 条前序结论已失真、1 条在其基线即错（见 §5）。
10. 链的连续性判断：**同层双引擎的 Ok 输出 parity 大体连续，跨层语义链不连续**——L09（删 struct_eq/prim/tests、换名字世界）与 L13（回 σ 前载体、换值表示、重排孪生模块）是两个"重定基点"，其余边界是增量。

### 1. 65×8 文件谱系（presence-matrix 全量）

矩阵共 **65 个 relpath**（63 个 `.rs` + `README.md`/`readme.md` 两个文档名），逐层 `.rs` 文件数 21/28/28/25/26/27/27/59。按"出现区间"归族：

| 族 | relpath（节选，全量见矩阵） | L06..L13 出现 | 事件 |
|---|---|---|---|
| 全 8 层常驻（20 个 `.rs`） | `bump_spine_iter.rs`、`bench_src/env/entry/eval/machine/quote/rename/spine/syntax(twin)/unify.rs`、`cxt.rs`、`elaboration.rs`、`mod.rs`、`pretty.rs`、`syntax.rs`、`parser/{lex,mod,syntax}.rs` | 8/8 | 无增删；文档名另有 `readme.md`(L06 191 行)→`README.md`(L07 645) 的大小写改名 |
| L07 新增核心（7） | `pattern_match.rs`、`struct_eq.rs`、`tests.rs`、`bump_spine_iter/{compiler,force,struct_eq,subst}.rs` | L07 起；前两者仅 L07/L08 | 见 §3-S1/S3 |
| L08→L09 增删 | +`bump_spine_iter/debug.rs`；−`struct_eq.rs`、`tests.rs`、`bump_spine_iter/{struct_eq,prim}.rs` | debug 仅 L09；`struct_eq.rs`/`tests.rs`/`twin/struct_eq.rs` 永久消失，`twin/prim.rs` 在 L13 复活（§6） | 净 −3 文件 |
| L09→L10 | +`typeclass.rs`、`bump_spine_iter/typeclass.rs`；−`bump_spine_iter/debug.rs` | L10–L13 / L10,L11,L13 | 停一层又清一层，见 §6 |
| L10→L11 | +`parser/macros.rs` | L11–L13 | 宏层唯一新文件 |
| L11→L12 | +`canonical.rs`；−`bump_spine_iter/typeclass.rs` | canonical L12/L13；twin typeclass 断 L12 | 求解器搬 machine.rs（§6） |
| L12→L13（+32） | root 层 26 个新文件（25 个 `*_tests/*_probe` + `eval_budget.rs`）、`parser/derive.rs`、`bump_spine_iter/{compact,debug,observe,prim,termination,typeclass}.rs`；−`bump_spine_iter/subst.rs` | — | **一次性回填 33 个文件**（其中 6 个孪生文件是从更早层"复活"的，见 §6） |

**谱系读法**：L07/L08 是"最完整的两层"（28 文件、含结构相等+参考版大测试）；L09 起显式替换重构把 4 个文件砍掉；L13 不是从 L12 线性生长，而是"L12 的 27 文件 − subst + 33 文件"的**换基**——它恢复了 L09 删掉的 `prim`、L12 删掉的 `typeclass`、L10 删掉的 `debug`（体积分别 1031/1031/414 行，均非简单复制，见 §6）。

#### 1.5 规模与热点（物理行口径，.deltawork/inventory）

| 边界 | 层总行 → 变化 | 最大增/减文件（A→B，行） | 解读 |
|---|---|---:|---|
| L06→L07 | 7913 → **19135（+11222）** | `mod.rs` 629→2306；`tests.rs` 0→2355；`pattern_match.rs` 0→851；`force.rs`(twin) 0→832 | 和类型+依赖模式匹配一次性落地，参考版首次分文件 |
| L07→L08 | 19135 → 17430（−1705） | `mod.rs` 2306→1877（−429）；`unification.rs` 1328→947（−381）；`tests.rs` 2355→2019；`struct_eq.rs` 374→188 | 积类型"语法糖化"：参考版机瘦身，测试同步缩 |
| L08→L09 | 17430 → 13415（−4015） | 删 `tests.rs` 2019、`struct_eq.rs` 188、`twin/prim.rs` 370、`twin/struct_eq.rs` 298；`mod.rs` 1877→1573；`cxt.rs` 454→220 | **第一次重定基**：换名字世界+删结构相等 |
| L09→L10 | 13415 → 16666（+3251） | `twin/machine.rs` 2130→3717（+1587）；`mod.rs` +707；新增 `typeclass.rs` 431 | trait 求解层；孪生 machine 膨胀 |
| L10→L11 | 16666 → 19519（+2853） | `parser/mod.rs` 883→2408（+1525）；`mod.rs` +715；`cxt.rs` 195→619（+424）；`twin/machine.rs` −631 | 宏层把复杂度堆到 parser/cxt |
| L11→L12 | 19519 → 19603（+84） | 新增 `canonical.rs` 155；删 `twin/typeclass.rs` 228；`mod.rs` −198；`cxt.rs` −154；`parser/mod.rs` +184 | 总量几乎不变，内部搬家 |
| L12→L13 | 19603 → **59378（+39775）** | `mod.rs` 2797→8527；`elaboration.rs` 1311→3908；`parser/mod.rs` +2046；`entry.rs` +1442；`twin/machine.rs` +2169；新增 observe 1363/compact 667/prim 1031/twin typeclass 1031 | **第二次重定基 + 产品化**（L13 测试 15270 行占全层 25.7%） |

### 2. 机制标记矩阵（层 × 机制，代码命中；raw 另注）

| 机制 | L06 | L07 | L08 | L09 | L10 | L11 | L12 | L13 | 相邻变化点 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| σ 簇（Subst/VSub/frcs/SpecSolve/wrap_sub 合计） | 0 | **202** | 154 | 142 | 128 | 129 | **125** | **0** | L07 引入；L13 归零（L13 raw 仅 2 条注释） |
| 旧载体 update_cxt+refresh | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **24** | L13 独家（与 σ 互斥） |
| 名字世界：`src_names`（代码） | 0 | 0 | 0 | 22 | 22 | 5 | 5 | 32 | L09 起用；L11/12 收窄（NameState 封装） |
| 名字世界：`Infer::global_names` 哨兵（代码） | 0 | 0 | 0 | **11** | **11** | 0 | 0 | 0 | 仅 L09/L10 |
| 值表示 `Val::Prim`（代码） | 0 | 21 | 21 | 7 | 8 | 12 | 13 | **0** | L07(name,spine)→L09 单元→L10(PrimFunc)→L13 删 |
| 值表示 `Val::Nat`（代码） | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **65** | L13 新增原生 Nat |
| 显式 `Rc<Val>` 包裹（代码） | 70 | 11 | 8 | 9 | 80 | 105 | 122 | 258 | L10/L13 两次上升（[推断] 与 Val 内嵌/Rc 化提交叠加） |
| trait 求解 `Synth`（代码） | 0 | 0 | 0 | 0 | 5 | 5 | 5 | 23 | L10 起；L13 大扩 |
| 宏 `parser/macros.rs` 行数 | - | - | - | - | - | 359 | 359 | 382 | L11 新增，L12 未动 |
| `preprocess` 命中 | 10 | 13 | 13 | 8 | 8 | 13 | 14 | **64** | L13 装载面放大 4.6× |
| `canonical` 标签 | 0 | 3* | 0 | 0 | 0 | 0 | **30** | 2 | L07 的 3 处是 `is_canonical_head`（合一内部判定，`unification.rs:1242`），与 L12 `canonical.rs`/`iddfs` 不是同一物；后者仅参考版 |
| `namespace`（代码） | 0 | 0 | 0 | 0 | 0 | 15 | 15 | **275** | L11 只有字段名残留，L13 真机制 |
| 调试残留 `eprintln!`/`dbg!`（raw） | 1 | 6 | 5 | 0 | 9 | 2 | 6 | **66** | L13 全层最多（含 legacy_tests:985）；`#[ignore]` 仅 L13 1 处 |

**关键相邻变化（"链断在哪"总表）**：

| 边界 | 机制级变化 | 结论 |
|---|---|---|
| L07→L08 | σ 框架不变；燃料载体改 per-Cxt `Cell`（`mod.rs:542`，常量 :549）；积类型进合一 | 增量，不断链 |
| L08→L09 | ①σ 保留但 `Val::Prim` 退化为单元；②删 `struct_eq`/`prim` 两子模块（参考+孪生）；③名字世界从 `NameState` 换 `BiMap`+哨兵；④删参考版 `tests.rs` | **第一次重定基（断链）** |
| L09→L10 | trait 求解两版各自新文件；删孪生 `debug.rs`；名字世界仍是 BiMap+哨兵 | 增量 |
| L10→L11 | 宏解析新文件；名字世界换回 `NameState`（`cxt.rs:83`）；删哨兵 | 载体回退 |
| L11→L12 | canonical 只在参考版；孪生 `typeclass.rs` 删、求解器并入 `machine.rs`；名字世界加撤销轨迹（`cxt.rs:12-24`） | 载体搬迁 |
| L12→L13 | **σ→update_cxt 回退**；名字世界回 `Rc<BiMap>`；原生 Nat/SumCase index/Call 节点/prim 入 decl 表；孪生 6 文件"复活" | **第二次重定基（断链）** |

### 3. copy-forward 断点总清单（按严重度）

#### S1 语义/机制丢失（影响判定或输出形状）

| # | A 层有 | B 层状态 | 锚点 | 影响 |
|---|---|---|---|---|
| S1-1 | σ 显式替换族（`Subst`/`VSub`/`frcs`/`SpecSolve`，整套 read-point 推开） | L13 两版都无；回到 `update_cxt`+`refresh` **全槽重求值** | `src/L12_canonical/mod.rs:288`、`src/L12_canonical/mod.rs:306`；`src/L13_namespace/cxt.rs:1327`、`src/L13_namespace/cxt.rs:1372` | 路线级分叉；L13 README 自认 `refresh` 更重（`README.md:409`）。**不是事故而是五轮回退的决策**（FACTS:104），但"继承 L05-L12 全部机制"的模块头表述失真 |
| S1-2 | `struct_eq.rs`（L07 374 行 / L08 188 行）+ 孪生 `struct_eq.rs`（428/298） | L09 起两版全无；5 层模块头写"由 unify 快路径承担" | 矩阵 `struct_eq.rs` 行；`L09:82`、`L10:111`、`L11:107`、`L12:133`、`L13:166`（均为 bump_spine_iter.rs） | 结构相等语义被并入合一；等价性无测试守护（L09–L12 无对应套件）[未核实] |
| S1-3 | `Val::Match` 携带 pending 应用实参（L07 `Vec<(Val,Icit)>`；L12 `Option<(SmolStr, Vec<Rc<Val>>)>`） | L13 变体只剩 3 字段 | `src/L07_sum_type/mod.rs:215`、`src/L12_canonical/mod.rs:281`、`src/L13_namespace/mod.rs:918` | 卡住 match 的实参承载点消失；[推断] 由 `Val::Call` 承担，须 core 单元核实 |
| S1-4 | `Val::Call` 实参 `Vec<Rc<Tm>>` | L13 `Call(SmolStr, List<(Rc<Val>, Icit)>, Rc<Val>)` | `src/L12_canonical/mod.rs:283`、`src/L13_namespace/mod.rs:920` | 内联节点从项层实参改为值层实参（quote 往返路径变化） |
| S1-5 | `Val::Prim` 带名字+spine（L07，丢失实参会把 `x++y`/`x++z` 判等——L07 自己注释的教训）→ 单元（L09）→ `Prim(Rc<Val>, PrimFunc)`（L10–L12） | L13 删除变体，`prim: Option<PrimFunc>` 挂 decl 表条目 | `src/L07_sum_type/mod.rs:200`、`src/L09_mltt/mod.rs:181`、`src/L12_canonical/mod.rs:268`、`src/L13_namespace/bump_spine_iter/prim.rs:1`（模块头） | 载体三变；L13 孪生 `prim.rs` 1031 行是 L06–L08 血统 + 新设施，不是 L12 的延续 |
| S1-6 | 名字世界载体 | L06/L07/L08 `NameState` → L09/L10 `BiMap`+哨兵 → L11/L12 `NameState`+轨迹 → L13 `Rc<BiMap>`+refresh | `src/L06_string/cxt.rs:314`、`src/L07_sum_type/cxt.rs:153`、`src/L09_mltt/cxt.rs:30`、`src/L11_macro/cxt.rs:83`、`src/L12_canonical/cxt.rs:73`、`src/L13_namespace/cxt.rs:330` | 四次换载体；L12 的 O(1) 撤销轨迹优化在 L13 全部丢失（L12 `cxt.rs:12-24` 明确说旧 BiMap 是 O(n²)） |
| S1-7 | `SumCase.case_name: Span<SmolStr>` | L13 `index: u32`（构造子下标），名字反查 `cases[index]` | `src/L12_canonical/mod.rs:278`、`src/L13_namespace/mod.rs:915` | 共享 `PatternDetail::Con` 首字段语义同步改变（L13 头 :19-21 声称"共享类型免费"）[推断] 需核实 parser 侧同步 |

#### S2 健壮性/守卫丢失或换形

| # | 机制 | 取值/分布 | 锚点 | 影响 |
|---|---|---|---|---|
| S2-1 | `MATCH_CMP_BUDGET=64`（卡住 match 相等性比较次数上限） | 仅 L07/L08，L09 起永久缺失 | `src/L07_sum_type/mod.rs:641`、`src/L08_product_type/mod.rs:554`；L09+ 全层 0 命中 | 卡住 match 比较从"有次数预算"变"无预算" |
| S2-2 | `PM_FUEL`（thread_local 精化展开燃料池，4096） | 仅 L09–L12 孪生 | `src/L09_mltt/bump_spine_iter/force.rs:104`、`src/L10_typeclass/bump_spine_iter/force.rs:157`、`src/L11_macro/bump_spine_iter/force.rs:166`、`src/L12_canonical/bump_spine_iter/force.rs:166` | L13 无该池（改 `eval_budget`）；L07/L08 无此机制（它们用调用级预算） |
| S2-3 | `UNIFY_FUEL=4096` 载体 | L07 常量；L08 起常量+per-Cxt `Cell`；L13 常量+Cell | `src/L07_sum_type/mod.rs:627`、`src/L08_product_type/mod.rs:542`、`src/L09_mltt/mod.rs:471`、`src/L13_namespace/mod.rs:1497`、`src/L13_namespace/mod.rs:1419` | 同值不同语义：L07 是每次入口 reset 的调用级预算，L08+ 是随 Cxt 传递的 Cell。CROSS §2.1 已警告，本次实测确认 |
| S2-4 | `eval_budget` / `NAT_CHAIN_LIMIT` | 仅 L13（参考+孪生共用边界） | `src/L13_namespace/eval_budget.rs:1`、`src/L13_namespace/eval_budget_tests.rs:107`、`:139` | L13 新增"循环求值看门狗"，前六层无（只在 L13 产品层补） |
| S2-5 | `occurs` 环守卫命中 | 46/34/12/16/16/13/32（L07..L13） | L09 `unification.rs:600` 注释"对齐旧 update_cxt 语义下的分支不可达" | L09 缩水一半，L13 回升（原生 Nat/SumCase 需要） |

#### S3 测试链断裂

| # | 内容 | 事实 | 锚点 |
|---|---|---|---|
| S3-1 | 参考版 `tests.rs` | L07 2355 行 / L08 2019 行，L09 删除；L09–L12 src 内 `#[test]` 仅 10/25/33/35 个 inline | presence-matrix；静态计数 |
| S3-2 | 黑盒套件 | `tests/l07_blackbox{,_v2,_v3}` 49/53/47、`l08_blackbox{,_v2}` 58/53 之后，L09–L12 **只有** `l09..l12_fast_parity`（29/21/19/15）；L13 才有 namespace/hover/completion 等 11 套 | `tests/` 静态计数 |
| S3-3 | L13 回填 | root 层 26 个新 src 文件（25 个 `*_tests/probe` + `eval_budget.rs`）；inventory test 15270 行、静态 612 个 `#[test]`（`legacy_tests.rs` 5421 行/138 个） | `.deltawork/inventory/files-L13_namespace.tsv`；静态计数 |
| S3-4 | 等价性断言 | `struct_eq` 删除、`Val::Match`/Call 改形均**没有**对应 parity 断言（L13 四类"既有分叉"明确剔除） | `src/L13_namespace/bump_spine_iter.rs:102`（GADT×trait 等分叉族） |

#### S4 文档失真（详见 §5）

| # | 声明 | 事实 | 锚点 |
|---|---|---|---|
| S4-1 | L13 孪生头"继承 L05-L12 的全部机制" | 同头 :165-166 自述缺 subst/struct_eq；σ 全无 | `src/L13_namespace/bump_spine_iter.rs:3` vs `:165` |
| S4-2 | L13 README 341 个 `#[test]` | 静态 612（ref 587 + twin 25） | `src/L13_namespace/README.md:417` |
| S4-3 | `struct_eq` 由 unify 快路径承担 | 5 个孪生模块头重复同一句，无任何验证 | 同 S1-2 的 5 个锚点 |

### 4. 标题噪声总清单（应排除的"假差异"）

| 类别 | 具体形态 | 例证（锚点） | 处理 |
|---|---|---|---|
| 章节标题 | 7 个 `src/Lxx/README.md` 的 H1 只差层号+副标题 | `src/L07_sum_type/README.md:1` … `src/L13_namespace/README.md:1` | 全排除；本审计只取正文声称 |
| 模块头层号 | `bump_spine_iter.rs` 第 1 行 "L0x 核心机（…）" 逐层只换数字 | `src/L06_string/bump_spine_iter.rs:1` … `src/L13_namespace/bump_spine_iter.rs:1` | 排除（L09 起该行清单不再列 `force`，但 `force.rs` 仍在——纯措辞，`presence` 表可证） |
| crate 路径 | `crate::Lxx::parser` / `use super::` 随层名改写 | `src/L09_mltt/bump_spine_iter.rs:108`、`src/L11_macro/bump_spine_iter.rs:136` | 排除 |
| bench 二进制 | `src/bin/l06bench.rs`…`l12bench.rs`、`realbench.rs` 只是负载驱动 | `src/bin/` 清单 | 排除（性能数字另标时效） |
| parity 套件名 | `tests/l07_fast_parity.rs`…`l13_fast_parity.rs` | `tests/` | 排除 |
| 复制注释层号 | 跨层复制时层号没同步："L10-L12 同款"（L13 文件里）、"L07 口径"（L09–L13 里） | `src/L09_mltt/pattern_match.rs:187`、`src/L13_namespace/pattern_match.rs:229`、`src/L13_namespace/bump_spine_iter.rs:152` | 排除文字，但其中"L10 先例/L09 同款"暴露了载体来源（§6） |
| 文档名大小写 | `readme.md`(L06)→`README.md`(L07+) | presence-matrix 两行 | 排除，不当作"新增文档" |
| 决策树字样 | L09–L13 注释里 7/4/8/4/15 处"决策树"，实现是逐臂（`pattern_match.rs:187`/`229`） | 同上 | 排除为历史注记，**不是**实现差异；当前两版均逐臂（`compiler.rs:280`） |

### 5. 前序文档与当前代码不符处（逐条 + 当前锚点）

> 前序基线 `FACTS.md:3` = HEAD `8443586e`（2026-11-08）；当前 HEAD `0464150c`。二者之间 `src/L07..L13` **62 文件 +2676/−1168**（`git diff --stat 8443586e HEAD`）。故分"过期"与"基线即错"两类。

| # | 前序声明 | 当前事实 | 定性 |
|---|---|---|---|
| D-1 | CROSS:42「相同的只有 syntax.rs 的 L07≡L08、L12≡L13 两对」 | `git show 8443586e` 下 L07≡L08 syntax.rs **确实逐字节相同**；但当前 L07 36 行 vs L08 32 行、MD5 不同，只剩 `syntax.rs` L12≡L13 一对 | **过期**（11-11 提交改动 L07/L08），引用须重核 |
| D-2 | CROSS:24-25「L11/L12 孪生 = **单文件** 7,873/7,864 行」 | 基线时 L11 孪生已是 14 文件目录（`git ls-tree 8443586e:src/L11_macro/bump_spine_iter`）；当前同为子目录（presence-matrix 14 行、`bump_spine_iter.rs` 仅 171/194 行聚合） | **基线即错**（形态与行数均不符；实际 twin 约 9,018/9,016 行） |
| D-3 | FACTS:24「L13 参考版 24946 / 测试 15270 / 孪生 19111 / 合计 59327」 | inventory：ref 17751 + parser 7240 + test 15270 + twin 19117 = **59378**；"参考版 24946"≈ref+parser 合算（24991，差 45） | **口径混淆 + 小漂移** |
| D-4 | CROSS §2.1「`UNIFY_FUEL` L08 `mod.rs:542`」等逐层行号 | 当前 L08:542 是 `unify_fuel: Cell<u32>` 字段，常量在 `:549`；L09/L10/L11/L12 常量分别在 475/449/489/606（字段在 471/484/508/627） | **行号漂移 + 常量/字段混淆**；数值 4096 与"L13 mod.rs:1419"仍准确 |
| D-5 | FACTS §7.1「L13 README 称 341，静态 612，legacy_tests 138」 | README:417 仍写 341；静态 612；legacy_tests 138 | **仍成立** |
| D-6 | CROSS §1.5「`Infer.global` L09/L10 5/6 处；L11/L12/L13 用 decl 表」 | L09/L10 代码命中 11/11；L11/L12/L13 也有 2/2/1 处，但全是"本层没有该哨兵"的注释（`L12 machine.rs:81`、`L13 machine.rs:368`） | **方向成立、计数口径不同**，不算错 |
| D-7 | CROSS:85「σ 分叉：L07–L12 已迁，L13 仅 5 处且为注释；L13 仍旧路」 | 当前 L13 σ raw 仅 2 处注释、代码 0；旧载体代码 24 | **成立**（且 L13 README:165 §2.3 明文承认） |
| D-8 | FACTS §3「L07 参考侧 69 个 `#[test]`」 | 当前静态 70 | **过期**（+1） |

### 6. 参考版 ↔ 孪生版：跨层的"单侧机制"与载体搬迁

| 机制 | 分布 | 锚点 | 解读 |
|---|---|---|---|
| `canonical`/`iddfs` | 只在参考版，L12 落地、L13 保留 | `src/L12_canonical/canonical.rs:8`、`src/L13_namespace/canonical.rs:9`；`src/L13_namespace/README.md:335` | 孪生从不移植（bump 版无 retry 闭包） |
| `FORCE_MEMO`/`prime_resident`/`compact`/`observe`/`termination` | 只在 L13（observe/compact 是孪生侧新增） | `src/L13_namespace/bump_spine_iter/compact.rs:1`、`observe.rs:1`、`termination.rs:1` | 产品层专属；前六层无 |
| `PM_FUEL` | 只在 L09–L12 孪生 | 见 S2-2 | 参考版从无此机制 ⇒ 孪生侧"额外防护"在 L13 消失 |
| 孪生 `typeclass` 模块 | L10/L11 有 → L12 **删模块搬进 machine.rs** → L13 **重新拆出 1031 行** | `src/L12_canonical/bump_spine_iter/machine.rs:44`、`:658`、`:687`；`src/L13_namespace/bump_spine_iter/typeclass.rs:732` | 同一机制两次换载体；"模块是否存在"不能当功能增删读 |
| 孪生 `prim` 模块 | L06–L08 有 → L09–L12 删 → L13 **复活 1031 行** | `src/L06_string/bump_spine_iter/prim.rs:1`、`src/L13_namespace/bump_spine_iter/prim.rs:1` | L13 的 prim 模块混入原生 Nat/def-replay/卡住存根，是"旧血统+新设施" |
| 孪生 `debug` 模块 | 仅 L09（395 行）→ L10 删 → L13 复活（414 行，头注"L09 同款"） | `src/L13_namespace/bump_spine_iter.rs:155` | 同上，跨代复制痕迹 |
| 孪生 `subst` | L07–L12 有（505/422/265/235/242/251 行）→ L13 删 | 矩阵 `bump_spine_iter/subst.rs` 行；L12 `subst.rs:23` | 与 S1-1 同步（σ 没了，模块也没了） |
| 求解器两套 | 参考版 `typeclass.rs` 与孪生 `typeclass.rs` 各自一份（L10–L13），"共用 Synth"是语义同源非代码共享 | `src/L13_namespace/typeclass.rs`（647 行）vs `src/L13_namespace/bump_spine_iter/typeclass.rs:732` | CROSS §1.2 "层内共用"结论仍成立 |

### 7. 工程性/性能/健壮性改动（跨层）

| 项 | 事实 | 锚点 | 后果 |
|---|---|---|---|
| 模块头"继承"表述 | L13 头声明继承 L05-L12 全部机制，但删 subst/struct_eq，且 canonical 不移植 | `src/L13_namespace/bump_spine_iter.rs:3`、`:165`、`README.md:335` | 读者若信头注会误判链连续 |
| 调试残留 | L13 全层 `eprintln!` 66 处（`[CLASS]`/`[PHA]`/`[TMEM]`/`[DECL]`），变量名 `__im0/__pa0/__pb0` | `src/L13_namespace/elaboration.rs:2562`、`:2619`、`src/L13_namespace/bump_spine_iter/entry.rs:948` | 无条件桩可能刷屏；L07/L08 只有 6/5 处，L09 为 0 |
| `#[ignore]` | 仅 L13 有 1 处 | 静态计数（L13） | 测试面残留 |
| 性能优化回退 | L12 `NameState` 撤销轨迹（O(1)）→ L13 回 `BiMap`+`refresh` 全槽重求值 | `src/L12_canonical/cxt.rs:12`、`src/L13_namespace/cxt.rs:1372` | L13 README 自认更重（`README.md:409`）；这是"产品层换基"的性能账单 |
| 新压实设施 | L13 `compact`：可达图深拷新 bump，旧 bump 丢弃（1.48GB 已用 → 稳态 ~200-300MB 参照） | `src/L13_namespace/bump_spine_iter/compact.rs:1` | 只有孪生有，前六层无 |
| 新看门狗 | `eval_budget` 协作式超时（每 2^20 次迭代 checkpoint） | `src/L13_namespace/eval_budget.rs:1` | 仅 L13；前六层循环求值会静默自旋 |
| `.bak`/临时文件 | 全层 0 命中 | 静态计数 | 无残留 |

### 8. 证据锚点表（断言 → 锚点；42 条，覆盖 §1–§7）

| # | 断言 | 锚点 1 | 锚点 2 / 补充 |
|---:|---|---|---|
| 1 | 65 relpath × 8 层谱系与出现/消失 | `.deltawork/presence-matrix.tsv`（65 数据行） | `.deltawork/inventory/files-L13_namespace.tsv` |
| 2 | L06 rs=21，L13 rs=59，测试列 0 直到 L13 | `.deltawork/inventory/layers-summary.tsv` | 上表读法 |
| 3 | L13 参考版 `update_cxt` 是活代码 | `src/L13_namespace/cxt.rs:1327` | — |
| 4 | L13 `refresh` 全槽重求值 | `src/L13_namespace/cxt.rs:1372` | `:1403` `is_refined` |
| 5 | L13 `update_from` 增量区间字段 | `src/L13_namespace/cxt.rs:335` | `:1365` |
| 6 | L13 名字表回到 `Rc<BiMap>` | `src/L13_namespace/cxt.rs:330` | `:1210` 插入点 |
| 7 | L13 命名空间三字段 | `src/L13_namespace/cxt.rs:332` | `:333`、`:334` |
| 8 | L12 σ 值变体 | `src/L12_canonical/mod.rs:288` | `:302` 旧 update_cxt 对照注释 |
| 9 | L12 `Subst` 持久单链 | `src/L12_canonical/mod.rs:306` | `:293-300` |
| 10 | L13 自述"无 subst/σ" | `src/L13_namespace/bump_spine_iter.rs:165` | `:166` 无 struct_eq |
| 11 | L13 头注"继承 L05-L12 全部机制" | `src/L13_namespace/bump_spine_iter.rs:3` | — |
| 12 | L13 精化载体自注 `update_cxt` 非 σ | `src/L13_namespace/pattern_match.rs:591` | `README.md:165` |
| 13 | L13 `Val` 枚举含 Nat / SumCase index | `src/L13_namespace/mod.rs:886` | `:905` Nat；`:915` index |
| 14 | L13 `Match` 无 pending 字段 | `src/L13_namespace/mod.rs:918` | L12 对照 `:281` |
| 15 | L13 `Call` 实参改值层 List | `src/L13_namespace/mod.rs:920` | L12 对照 `:283` |
| 16 | L13 `UNIFY_FUEL` 常量 4096 | `src/L13_namespace/mod.rs:1419` | `:1497` Cell 字段；`:2227` burn_fuel |
| 17 | L12 `Prim(Rc<Val>,PrimFunc)` | `src/L12_canonical/mod.rs:268` | — |
| 18 | L09 `Val::Prim` 退化为单元 | `src/L09_mltt/mod.rs:181` | — |
| 19 | L07 `Val::Prim(SmolStr, Spine)` 与实参不可丢的教训 | `src/L07_sum_type/mod.rs:200` | `:196-199` 注释 |
| 20 | L07 `Match` 带 pending 实参 | `src/L07_sum_type/mod.rs:215` | L12 对照 `:281` |
| 21 | L07 σ 变体 | `src/L07_sum_type/mod.rs:219` | `:237` `Subst` |
| 22 | L07 燃料常量/预算常量 | `src/L07_sum_type/mod.rs:627` | `:641` `MATCH_CMP_BUDGET=64` |
| 23 | L08 燃料改 per-Cxt Cell | `src/L08_product_type/mod.rs:542` | `:549` 常量、`:554` 预算 |
| 24 | L09–L12 同构的 Cell 化燃料 | `src/L09_mltt/mod.rs:471` | `:475`；`src/L10_typeclass/mod.rs:484`、`:449` |
| 25 | L11/L12 燃料 Cell | `src/L11_macro/mod.rs:508` | `:489`；`src/L12_canonical/mod.rs:627`、`:606` |
| 26 | 孪生 PM_FUEL 只在 L09–L12 | `src/L09_mltt/bump_spine_iter/force.rs:104` | `L10:157`、`L11:166`、`L12:166` |
| 27 | struct_eq 缺失五处自述 | `src/L09_mltt/bump_spine_iter.rs:82` | `L10:111`、`L11:107`、`L12:133`、`L13:166` |
| 28 | L12 孪生求解器搬入 machine.rs | `src/L12_canonical/bump_spine_iter/machine.rs:658` | `:687`、`:44` use Synth |
| 29 | L13 孪生 typeclass 重新拆出 | `src/L13_namespace/bump_spine_iter/typeclass.rs:732` | `src/L13_namespace/bump_spine_iter.rs:151`（导览） |
| 30 | L13 孪生 prim 复活 | `src/L13_namespace/bump_spine_iter/prim.rs:1` | `src/L06_string/bump_spine_iter/prim.rs:1` 血统 |
| 31 | L13 孪生 debug 复活（L09 同款） | `src/L13_namespace/bump_spine_iter.rs:155` | 矩阵 debug.rs 行 |
| 32 | L13 新增 compact/observe/termination | `compact.rs:1` | `observe.rs:1`、`termination.rs:1` |
| 33 | L13 eval_budget 看门狗 | `src/L13_namespace/eval_budget.rs:1` | `eval_budget_tests.rs:107`、`:139` |
| 34 | L13 调试残留 | `src/L13_namespace/elaboration.rs:2562` | `:2619`、`bump_spine_iter/entry.rs:948` |
| 35 | canonical 仅参考版 | `src/L12_canonical/canonical.rs:8` | `src/L13_namespace/canonical.rs:9`；`README.md:335` |
| 36 | 名字世界四代载体 | `src/L06_string/cxt.rs:314` | `L07:153`、`L09:30`、`L11:83`、`L12:73`、`L13 cxt.rs:330` |
| 37 | L12 NameState 撤销轨迹（对旧 BiMap O(n²) 的批评） | `src/L12_canonical/cxt.rs:12` | `:26`、`:37` unwind |
| 38 | 逐臂模式编译（非决策树） | `src/L09_mltt/pattern_match.rs:187` | `src/L13_namespace/pattern_match.rs:229`、`compiler.rs:280` |
| 39 | L13 README 自认 update_cxt 路线更重 | `src/L13_namespace/README.md:409` | `:165` §2.3 |
| 40 | L13 README 测试数失真（341 vs 612） | `src/L13_namespace/README.md:417` | 静态计数；`legacy_tests.rs` 138 |
| 41 | 前序文档基线与失真条目 | `docs/compare-l07-l13/FACTS.md:3`、`:24` | `CROSS.md:24`、`:42`、`:85` |
| 42 | L07 的 canonical 是另一概念（`is_canonical_head`） | `src/L07_sum_type/unification.rs:1242` | `:1234` |

### 9. 给 Lead 的一句话

链在两个点断（L09 删结构与测试、L13 换回 update_cxt），L13 是"换基+回填"，合并时应把 L13 当新基线而不是 L12 的增量。

## 11. 综合判断：这条链是怎么被"搞乱"的

> 本节是 Lead 汇总（不重复前文证据；每条断言都能在 §4–§10 找到锚点）。

### 11.1 六种断法（同一链条上叠了六类事件，不是"一次优化搞乱"）

| # | 断法 | 位置 | 关键证据（均见前文） | 性质 |
|---|---|---|---|---|
| B1 | **设计性再定基**（不 copy，重写内核） | L08→L09；L12→L13 | L09 README 自认"非逐行继承"；L13 两版同时删 σ 回 `update_cxt`、换名字世界/值表示 | 有意为之，但使"逐章递增"不可读 |
| B2 | **滞后拷贝**（后章是前章旧快照） | L07→L08 | L08 缺 L07 的 09-18 深值栈安全轮、10-11 月 P3/P5/P8/P10/P11、decl 简化缓存、黑盒 v3；反向 L08 孪生有 L07 没有的常驻缓冲/name_map 修复 | 两个分支各自演进，非单边刷旧 |
| B3 | **双向补丁分叉**（前章后来打的补丁没回传） | L10↔L11 | L10 的 bench_check / unsolved worklist / `to_typ` flat_map 语义在 L11 消失；L11 的 `SPINE_ESCAPE` 又在 L12 消失 | 补丁只在被优化那一层落地 |
| B4 | **单边优化回填**（同一问题的加固只落部分层） | 全链 | MATCH_CMP_BUDGET 仅 L07/L08；PM_FUEL 仅 L09–L12 孪生；eval_budget 仅 L13；Rc 值层 L07/L08 局部、L10 全量 | 各层健壮性/性能口径互不相同 |
| B5 | **功能删除/弱化无替代** | L08→L09；L11→L12；L12→L13 | L09 删 struct_eq、`Val::Match` pending（合法程序 `v_app` panic）、15 builtin→1、`tests.rs`；L12 删 `SPINE_ESCAPE` 摊平与嵌套覆盖节点方程（L11 Ok→L12 Err）；L13 删 σ、`Val::Match` origin | 大多数是"时代口径"下的主动取舍，但没留下等价性证明 |
| B6 | **文档漂移**（README 声称 ≠ 实现） | 全链 | L08"现行 L07 全量继承"为假；L09/L10/L11 互相认领"决策树→逐臂"；L12 测试数 17 vs 21、内建 6 vs 5；L13 测试 341 vs 612、prelude 24 vs 35、行号系统性过期 | 文档每章重写一次，但数字/锚点不随代码更新 |

### 11.2 每章"标题以外"最重要差异（一表速览；细节见对应章节）

| 章 | 标题说的是 | 标题没说的（标题外最重要的 2–3 条） |
|---|---|---|
| L08 | 积类型 | ① 它是 L07 的**滞后**拷贝，欠 L07 深值轮/三档诊断/span/缓存四笔债（mod.rs −429、unification −381 的来由）；② tests.rs 64→56、黑盒 v3 未随层；③ 孪生反向领先 L07（常驻缓冲/name_map 修复），是**两支独立优化** |
| L09 | MLTT 宇宙层 | ① 名字世界从 `decl` 表换成 `Infer.global`+哨兵（15 builtin→1、可变全局/文件 IO 全删）；② 删 `struct_eq` 与 match 比较总预算，`Val::Match` 丢 pending→合法程序 panic；③ 2018 行 `tests.rs` 整删，黑盒套件自 L09 起消失 |
| L10 | trait/typeclass | ① 参考版 `Val`→`Rc<Val>` 全签名重构，改动量大于 trait 本身；② 删 L09 的 `SpecSolve.solvable`/`bind_slots` 白名单（语义放宽）；③ 孪生 +1587 行中约 500 行是临时探针；④ `where`/实例依赖未实现（dependencies 恒空） |
| L11 | 宏 + decl 表世界 | ① parser 里宏以外还有错误恢复/手写优先级/`SPINE_ESCAPE`/Verilog 兼容 token（+1914 parser 行）；② 名字世界第二次换基（哨兵→decl 表）+ `Arc` 化 + 名字轨迹表重构；③ bench_check 口径丢失（相对 L10），README 把"逐臂落地"错记到自己头上 |
| L12 | Val 级求解/Call/canonical | ① 嵌套覆盖精度回退（`PendingNode`→`pending_pos`，L11 Ok 的 Vec len2 程序变 Err，正向钉被删）；② `SPINE_ESCAPE` 修复整段丢失；③ 删 4 个测试（test9/10/11 + nested_coverage_vec_len2_ok）；④ 孪生删 `typeclass.rs` 模块并入 machine（L13 又拆回来） |
| L13 | 命名空间/产品化 | ① 两版同时删 σ 回 `update_cxt`（最大语义断点）；② `Val::Match` 丢 origin、孪生删 `subst.rs`、模块谱系"复活/搬家"6 次；③ 核心三文件 +9298 行/孪生 +10101 行，测试 35→612、+33 文件，README 行号系统性失真，生产代码 66 处 `eprintln!` |

### 11.3 如果要把链条恢复成"可追溯的 copy-forward"：按优先级

**P0 · 语义/正确性（不改则会持续误导读者与回归）**

1. **定一条精化载体路线**：产品层 L13 已用 `update_cxt`（两版都是），σ 只活在 L07–L12。要么把 L13 的"分叉"写进孪生模块头（现头注"继承 L05-L12 全部机制"与 :165"无 subst/struct_eq"自相矛盾），要么回移 σ；不要维持"两套都算正统"的现状。
2. **裁定 L11→L12 的嵌套覆盖回退**：`pending_pos` 两段式把 L11 的 Ok 程序判成 Err。若接受保守语义，就把 L11 的 `test_nested_coverage_vec_len2_ok` 改写为"L12 起必须 Err"并记录；若不接受，回移 `PendingNode` 节点方程。
3. **回移 L13 的 `SPINE_ESCAPE` 到 L12**（L13 `parser/mod.rs:1359` 有现成实现，L12 为零）。
4. **L09 的 `Val::Match` pending panic**：要么恢复 pending 能力，要么在 `v_app` 处给可诊断错误（当前是 panic，LSP 进程可被打死）。
5. **L13 `Val::Match` origin 丢失**：若仅诊断/显示依赖则可接受，但需在 README 写明；若有实例匹配追溯用途，回移第四字段。

**P1 · 机制/守卫一致性**

6. **统一防护口径**：把 `MATCH_CMP_BUDGET`（L07/L08 有，L09+ 无）与 `PM_FUEL`（L09–L12 孪生有，L13 无）收敛成一套，或逐层写明"本层不设该护栏"的原因；`UNIFY_FUEL` 的"常量 vs per-Cxt Cell"也统一成一种。
7. **回灌 L07 的 P1–P11 加固到 L08–L12（至少 L13）**：否则同一程序在不同层的诊断语义不同，教学章节的可比性不成立。
8. **名字世界性能取舍写明**：L12 的 `NameState` 撤销轨迹（O(1) 回滚）在 L13 全部丢失，回到 `Rc<BiMap>`+refresh；若为产品层性能取舍，记录基准；否则回移。

**P2 · 测试与文档（性价比最高）**

9. **每层保留"跨层语义回归锚"**：L09–L12 目前只有 `lXX_fast_parity`（只验两版一致，不验跨层语义），至少把上一层 `tests.rs` 的核心用例族迁进 `tests/`。
10. **README 数字与行号自动化**：测试数、文件数、行号引用改为生成物或直接删掉；增量章必须新增"相对前章删除/弱化"一节（当前 L08/L09/L12 缺）。
11. **抽公共 crate 的可行性评估**：七层 × 两版 ≈16.4 万行，其中 parser/pretty/preprocess/Synth 已多份拷贝；若要长期维护"zoo"，共享底座 + 每层差异 feature 化比继续 copy 更可控。

### 11.4 一句话结论

> **这不是"上一章 copy + 新特性"的七级台阶，而是三条分支（L07/L08 旧值域、L09–L12 哨兵→decl 表值域、L13 产品域）被五次"再定基/滞后拷贝/补丁分叉"缝合起来的结果；真正符合 copy-forward 的只有 L10 一章，最能代表"被优化搞乱"的三处是 L08 欠 L07 的加固债、L11↔L10 的双向补丁分叉、L13 对 σ 的整体回退。**

## 附录 A. 机制标记矩阵（grep 原始计数，含注释）

计数方式：对每层 `src/<layer>/**/*.rs` 全文做正则计数（含注释/文档/测试代码）；代码级（剔注释）口径见 §10 的审计表，两者数值不同是口径差，不是矛盾。

| marker | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---|---|---|---|---|---|---|
| σ-Subst | 1 | 1 | 1 | 1 | 1 | 1 | 0 |
| σ-VSub | 139 | 88 | 75 | 65 | 71 | 62 | 0 |
| σ-frcs | 42 | 28 | 35 | 31 | 30 | 32 | 0 |
| σ-SpecSolve | 36 | 32 | 33 | 28 | 26 | 24 | 1 |
| σ-wrap_sub | 67 | 65 | 44 | 33 | 34 | 38 | 1 |
| old-update_cxt | 0 | 0 | 15 | 25 | 24 | 26 | 21 |
| old-refresh | 0 | 0 | 9 | 21 | 16 | 18 | 19 |
| old-pm_defs | 14 | 11 | 2 | 1 | 2 | 2 | 1 |
| old-pm_solvable | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| name-Infer.global | 0 | 0 | 6 | 7 | 2 | 2 | 1 |
| name-global_names | 0 | 0 | 17 | 17 | 0 | 0 | 0 |
| name-src_names | 4 | 3 | 38 | 36 | 6 | 7 | 30 |
| name-sentinel | 0 | 0 | 16 | 18 | 1 | 1 | 0 |
| val-RcVal | 11 | 8 | 9 | 80 | 105 | 123 | 266 |
| val-BoxVal | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| val-enumVal | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| val-Nat | 0 | 0 | 0 | 0 | 0 | 0 | 78 |
| val-Prim | 26 | 25 | 8 | 9 | 14 | 15 | 1 |
| tm-Prim | 31 | 26 | 18 | 20 | 36 | 32 | 1 |
| val-Decl | 36 | 31 | 0 | 0 | 24 | 28 | 58 |
| pm-decision | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| guard-UNIFY_FUEL | 16 | 16 | 8 | 6 | 6 | 6 | 3 |
| guard-PM_FUEL | 0 | 0 | 4 | 8 | 7 | 7 | 0 |
| guard-MATCH_CMP_BUDGET | 11 | 9 | 0 | 0 | 0 | 0 | 0 |
| guard-eval_budget | 0 | 0 | 0 | 0 | 0 | 0 | 52 |
| guard-occurs | 30 | 21 | 12 | 16 | 16 | 13 | 12 |
| trait-Synth | 0 | 0 | 0 | 8 | 7 | 7 | 33 |
| trait-outparam | 0 | 0 | 0 | 49 | 58 | 47 | 136 |
| macro-rules | 2 | 2 | 4 | 4 | 18 | 28 | 34 |
| macro-MacroRule | 0 | 0 | 0 | 0 | 6 | 11 | 17 |
| canonical | 0 | 0 | 0 | 0 | 0 | 16 | 6 |
| canonical-iddfs | 0 | 0 | 0 | 0 | 0 | 7 | 6 |
| ns-import_map | 0 | 0 | 0 | 0 | 0 | 0 | 40 |
| ns-namespace_prefix | 0 | 0 | 0 | 0 | 0 | 0 | 48 |
| ns-symbol_table | 0 | 0 | 0 | 0 | 0 | 0 | 72 |
| call-OpCall | 0 | 0 | 0 | 0 | 0 | 0 | 41 |
| obs-table | 1 | 1 | 0 | 0 | 0 | 0 | 108 |
| dbg-eprintln | 6 | 5 | 0 | 9 | 2 | 6 | 66 |
| dbg-dbg | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| test-attr | 70 | 60 | 10 | 25 | 33 | 35 | 612 |
| ignore-attr | 0 | 0 | 0 | 0 | 0 | 0 | 9 |
| todo | 0 | 0 | 13 | 22 | 29 | 29 | 23 |
| panic | 17 | 21 | 26 | 19 | 31 | 31 | 253 |
| hdl | 5 | 3 | 0 | 0 | 1 | 1 | 136 |
| prelude | 0 | 0 | 0 | 0 | 1 | 32 | 711 |


## 附录 B. 65×8 文件谱系全表（`src/` 下 relpath × 层，单元格为物理行数，`-` 表示该层无此文件）

| relpath | L06 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---|---|---|---|---|---|---|---|
| `README.md` | -` | 645` | 406` | 378` | 377` | 344` | 414` | 455 |
| `bare_ctor_member_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 127 |
| `bump_spine_iter.rs` | 114` | 146` | 139` | 129` | 171` | 171` | 194` | 293 |
| `bump_spine_iter/bench_src.rs` | 101` | 119` | 151` | 143` | 144` | 220` | 219` | 316 |
| `bump_spine_iter/compact.rs` | -` | -` | -` | -` | -` | -` | -` | 667 |
| `bump_spine_iter/compiler.rs` | -` | 677` | 680` | 531` | 530` | 539` | 459` | 917 |
| `bump_spine_iter/debug.rs` | -` | -` | -` | 395` | -` | -` | -` | 414 |
| `bump_spine_iter/entry.rs` | 413` | 418` | 368` | 362` | 388` | 393` | 401` | 1843 |
| `bump_spine_iter/env.rs` | 118` | 131` | 132` | 145` | 153` | 165` | 144` | 148 |
| `bump_spine_iter/eval.rs` | 334` | 517` | 515` | 566` | 565` | 642` | 630` | 693 |
| `bump_spine_iter/force.rs` | -` | 832` | 775` | 532` | 603` | 633` | 622` | 1035 |
| `bump_spine_iter/machine.rs` | 1386` | 2008` | 2093` | 2130` | 3717` | 3086` | 3360` | 5529 |
| `bump_spine_iter/observe.rs` | -` | -` | -` | -` | -` | -` | -` | 1363 |
| `bump_spine_iter/prim.rs` | 451` | 358` | 370` | -` | -` | -` | -` | 1031 |
| `bump_spine_iter/quote.rs` | 301` | 674` | 666` | 459` | 477` | 478` | 479` | 680 |
| `bump_spine_iter/rename.rs` | 737` | 924` | 838` | 797` | 884` | 805` | 813` | 907 |
| `bump_spine_iter/spine.rs` | 174` | 211` | 199` | 170` | 170` | 170` | 199` | 245 |
| `bump_spine_iter/struct_eq.rs` | -` | 428` | 298` | -` | -` | -` | -` | - |
| `bump_spine_iter/subst.rs` | -` | 505` | 422` | 265` | 235` | 242` | 251` | - |
| `bump_spine_iter/syntax.rs` | 211` | 308` | 254` | 254` | 261` | 280` | 279` | 299 |
| `bump_spine_iter/termination.rs` | -` | -` | -` | -` | -` | -` | -` | 323 |
| `bump_spine_iter/typeclass.rs` | -` | -` | -` | -` | 308` | 228` | -` | 1031 |
| `bump_spine_iter/unify.rs` | 521` | 1041` | 1085` | 886` | 950` | 981` | 980` | 1402 |
| `calc_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 373 |
| `canonical.rs` | -` | -` | -` | -` | -` | -` | 155` | 149 |
| `class_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 806 |
| `cong_projection_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 204 |
| `cxt.rs` | 482` | 505` | 454` | 220` | 195` | 619` | 465` | 1436 |
| `debug_test.rs` | -` | -` | -` | -` | -` | -` | -` | 441 |
| `elaboration.rs` | 367` | 758` | 805` | 919` | 1105` | 1250` | 1311` | 3908 |
| `eval_budget.rs` | -` | -` | -` | -` | -` | -` | -` | 145 |
| `eval_budget_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 180 |
| `hdl_assert_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 303 |
| `hdl_blackbox_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 520 |
| `hdl_check_graph_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 863 |
| `hdl_enum_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 501 |
| `hdl_fsm_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 661 |
| `hdl_stream_fix_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 364 |
| `legacy_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 5421 |
| `mod.rs` | 629` | 2306` | 1877` | 1573` | 2280` | 2995` | 2797` | 8527 |
| `module_probe_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 55 |
| `module_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 1052 |
| `parser/derive.rs` | -` | -` | -` | -` | -` | -` | -` | 1412 |
| `parser/lex.rs` | 267` | 312` | 333` | 407` | 407` | 407` | 407` | 456 |
| `parser/macros.rs` | -` | -` | -` | -` | -` | 359` | 359` | 382 |
| `parser/mod.rs` | 483` | 612` | 631` | 790` | 883` | 2408` | 2592` | 4638 |
| `parser/syntax.rs` | 38` | 119` | 119` | 113` | 206` | 236` | 253` | 357 |
| `pattern_match.rs` | -` | 851` | 780` | 596` | 566` | 605` | 506` | 761 |
| `prelude_core_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 145 |
| `prelude_data_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 289 |
| `prelude_hdl_a_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 134 |
| `prelude_hdl_b_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 623 |
| `prelude_hdl_c_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 679 |
| `prelude_stdlib_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 417 |
| `pretty.rs` | 199` | 309` | 287` | 242` | 255` | 319` | 394` | 853 |
| `prim_safety_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 116 |
| `readme.md` | 191` | -` | -` | -` | -` | -` | -` | - |
| `struct_eq.rs` | -` | 374` | 188` | -` | -` | -` | -` | - |
| `struct_refine_probe.rs` | -` | -` | -` | -` | -` | -` | -` | 286 |
| `syntax.rs` | 74` | 36` | 32` | 53` | 45` | 78` | 81` | 81 |
| `termination_check_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 275 |
| `tests.rs` | -` | 2355` | 2019` | -` | -` | -` | -` | - |
| `typeclass.rs` | -` | -` | -` | -` | 431` | 413` | 415` | 647 |
| `unification.rs` | 513` | 1328` | 947` | 761` | 761` | 822` | 863` | 1254 |
| `verilog_compat_tests.rs` | -` | -` | -` | -` | -` | -` | -` | 459 |


## 附录 C. 数据源、复算方法与校验记录

### C.1 时点与世界状态

- 仓库：`F:\projects\hermes\elaboration-zoo-lsp`；分支 `bench/realistic-l07-l13`；HEAD `0464150c0dd2b018c590ee085543af69d188fe06`（2026-11-11）；工作树在分析开始时干净（分析期间只新增未跟踪的 `.deltawork/` 与本文件）。
- 只读静态分析：未运行 `cargo build/check/test`，未执行 bench；测试数全部为静态 `#\[test\]` 计数。
- 行数口径：物理行（`\n` 计数，末行无换行补 1），不含 `*.md` 与 `.bak`（当前工作树无 `.bak`）。

### C.2 复算命令

```powershell
# 逐对 churn / 文件增删
git diff --no-index --numstat -- src/L07_sum_type src/L08_product_type
git diff --no-index --stat   -- src/L08_product_type src/L09_mltt
# 逐对完整 diff（本报告 §4–§9 的主证据源）
git diff --no-index -U3 -- src/L11_macro src/L12_canonical > L11--L12.diff
# 单层物理行/文件清单
Get-ChildItem src/L13_namespace -Recurse -File -Filter *.rs | ForEach-Object { ... }
# 静态测试计数
rg -c '#\[test\]' src/L13_namespace -g '*.rs' | Measure-Object -Property ... 
```

分析用机器底稿（未跟踪的临时工作目录，可复算也可删除）：

| 路径 | 内容 |
|---|---|
| `.deltawork/pairs/<TAG>.diff` | 相邻两层完整 unified diff（-U3，TAG 如 `L07--L08`） |
| `.deltawork/pairs/<TAG>.numstat.tsv` / `.files.tsv` / `.symbols.tsv` | 逐文件 churn / 状态与行数 / 符号增删 |
| `.deltawork/inventory/{layers-summary,files-*,symbols-*}.tsv` | 逐层规模与符号表 |
| `.deltawork/presence-matrix.tsv` | 65 relpath × 8 层的行数矩阵 |
| `.deltawork/inventory/marker-matrix.tsv` | §2.4 / 附录 A 的机制标记计数 |
| `.deltawork/drafts/*.md` | 8 个分析单元的原始草稿（§4–§10 的底稿） |

### C.3 校验记录

- 锚点机械校验：从 §4–§11 正文与附录抽取全部 `src/...rs:NNN`、`tests/...rs:NNN`、`.deltawork/...:NNN` 引用共 **698 条**，逐条检查"文件存在 + 行号 ≤ 文件行数"，**0 失效**。
- 抽样语义校验：对 16 条关键锚点（如 `L13 cxt.rs:1327` update_cxt、`L13 mod.rs:905` Val::Nat、`L12 mod.rs:283` Call、`L10 typeclass.rs:138` Synth、`L11 parser/mod.rs:140` 宏深度守卫）逐行比对内容，全部匹配。
- 跨单元一致性：σ 载体（L13 两版删除、L09–L12 的 `update_cxt` 仅注释）由 §9.1、§10 与 Lead 独立 grep 三方互证；`struct_eq` 删除、`SPINE_ESCAPE` 丢失/回归、`Val::Match` pending/origin 删除均至少两处独立锚点。
- 已知口径差（已在文中注明，不视为矛盾）：churn（numstat，含 README/增删）vs 物理行净差；presence-matrix 与 numstat 的末行计数差 ±1；grep 原始计数（含注释）vs §10 代码级计数。

### C.4 数字一览（本报告主表复算结果）

| 对 | numstat 文件数 | 新增 rs | 删除 rs | churn + | churn − | 净 churn | rs 净行 | README 行差 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| L07→L08 | 29 | 0 | 0 | 3082 | 5026 | −1944 | −1705 | −239 |
| L08→L09 | 30 | 1 | 4 | 6868 | 10911 | −4043 | −4015 | −28 |
| L09→L10 | 27 | 2 | 1 | 6981 | 3731 | +3250 | +3251 | −1 |
| L10→L11 | 27 | 1 | 0 | 7440 | 4620 | +2820 | +2853 | −33 |
| L11→L12 | 28 | 1 | 1 | 4054 | 3900 | +154 | +84 | +70 |
| L12→L13 | 60 | 33 | 1 | 48181 | 8365 | +39816 | +39775 | +41 |

### C.5 分析单元与分工（8 个单元，全部只读）

| 单元 | 范围 | 草稿 |
|---|---|---|
| delta-l07-l08 | L07→L08 | `.deltawork/drafts/L07-L08.md` |
| delta-l08-l09 | L08→L09 | `.deltawork/drafts/L08-L09.md` |
| delta-l09-l10 | L09→L10 | `.deltawork/drafts/L09-L10.md` |
| delta-l10-l11 | L10→L11 | `.deltawork/drafts/L10-L11.md` |
| delta-l11-l12 | L11→L12 | `.deltawork/drafts/L11-L12.md` |
| delta-l12-l13-core | L12→L13 核心机 | `.deltawork/drafts/L12-L13-core.md` |
| delta-l12-l13-surface | L12→L13 表层 | `.deltawork/drafts/L12-L13-surface.md` |
| audit-cross-layer | 跨层审计 | `.deltawork/drafts/AUDIT.md` |

