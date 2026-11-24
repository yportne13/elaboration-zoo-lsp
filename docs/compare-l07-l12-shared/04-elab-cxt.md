# 04 · 上下文与精化载体：`elaboration.rs` / `cxt.rs`

> 对象 `src/L07_sum_type/` ⟷ `src/L12_canonical/`，HEAD `8f4287ae`，只读分析、**无构建**。
> 口径：MAP.md §8（E0–E4）、§9（什么算共有）、**§10 附录 A（归因按"差异首次出现层"）**。
> 本册每条"L12 ≠ L07"都先问一句：**这是 L12 干的，还是 L08/L09/L10 干的、L12 原样继承的？**
> 一句话答案：**本分册范围内没有任何一条差异由 L12 引入**；L12 自己只改 22 增 14 删。

## 0 结论先行

| 问题 | 答案 | 档 |
|---|---|---|
| 精化载体是否同一台机器？ | **是**。σ / `Cxt::subst_cxt`，参考版+孪生各一个调用点，与 L07 同位置、函数体逐字节同；`update_cxt`=0、`refresh`=0、`check_pm_final`=0 | **E0** |
| `cxt.rs` 差在哪？ | 429 行对 429 行，**只有 9 行 `U`→`U(N)`**；归一化后 6-shingle 保留率 **1.0000** | **E1** |
| `elaboration.rs` 那 15%？ | **L07→L08 一次摘掉 15.0pp，L08→L09 再 -6.0pp，L11→L12 只 -0.2pp**；丢的主体是观察面产物 + 一处宇宙检查机制 | E3/E2 |
| 那 +3009 token 是谁加的？ | **84% 是 L10 的 typeclass 章节**，14% 是 L08 观察面重排，**只有 0.8%（+26）是 L12 自己** | E4 |
| 诊断口径？ | `Error` 结构逐字节同，`Warning` 两侧皆 0（L13 为 20）——**L12 没跟 L13 走** | E0 |

## 1 机械底数（本册复算，六层）

token = 去注释/去字符串后的记号数；keep07 = L07 侧 6-token shingle 保留率。**本册 tokenizer 与 MAP §1 口径不同，绝对数不可直接比，只用于层间增量。**

| elaboration.rs | L07 | L08 | L09 | L10 | L11 | L12 |
|---|---:|---:|---:|---:|---:|---:|
| 行数 | 833 | 856 | 856 | 1169 | 1169 | 1174 |
| token | 7,505 | 7,956 | 7,984 | 10,665 | 10,665 | 10,691 |
| keep07 | 1.0000 | **0.8504** | **0.7903** | 0.7884 | 0.7884 | **0.7882** |
| sha256[:16] | `6c72250a…` | `27cbd603…` | `c2aaf06b…` | `5da33a13…` | **同 L10** | `b345e51f…` |

| cxt.rs | L07 | L08 | L09 | L10 | L11 | L12 |
|---|---|---:|---:|---:|---:|---:|
| token | 3,083 | 3,083 | 3,110 | 3,110 | 3,110 | 3,110 |
| keep07 | 1.0000 | **1.0000** | 0.9903 | 0.9903 | 0.9903 | 0.9903 |
| sha256[:16] | `340507a0…` | **同 L07** | `0fee0d38…` | **同** | **同** | **同** |

相邻层 keep（elaboration.rs）：L07→L08 **0.8504** · L08→L09 0.9023 · L09→L10 0.9926 · L10→L11 **1.0000** · L11→L12 **0.9858**。
⇒ 与 MAP A.1/A.2 的形态一致：**坑在 L08，L12 只挪了 0.2pp**。

## 2 (c) 精化载体：σ / `subst_cxt` —— 本轮最硬的"不断"证据

### 2.1 机械计数（全层递归，含孪生）

| 机制 | L07 | L12 | 判读 |
|---|---:|---:|---|
| `subst_cxt` grep 命中 | 12 | **13** | 差 1 = L12 孪生 `compiler.rs:14` 的 `use` 行；**真实调用点相同** |
| `update_cxt` | 0 | **0** | L13 有（`L13_namespace/cxt.rs:1327`）|
| `refresh` | 0 | **0** | L13 有（`cxt.rs:1372`）|
| `check_pm_final` | 0 | **0** | L13 有（`L13_namespace/elaboration.rs:679`）|
| `VSub` / `wrap_sub` | 139 / 67 | 129 / 66 | MAP §3，量级同 |

### 2.2 关键调用点逐行对照

| 位置 | L07 | L12 | 档 |
|---|---|---|---|
| 载体定义 | `cxt.rs:453 pub fn subst_cxt(&self, sub: &Rc<super::Subst>) -> Self` | **同行号、同签名、函数体 27 行逐字节同**（`cxt.rs:453-479`） | **E0** |
| 臂上下文（最关键） | `pattern_match.rs:227 let cxt_arm = cxt_arm.subst_cxt(&self.sub);` | **同行、同字节**（整文件六层逐字节同） | **E0** |
| 臂体检查 | `pattern_match.rs:241 infer.check(&cxt_arm, body.clone(), ret_type)?` | 同 | **E0** |
| σ 回滚 | `pattern_match.rs:280 self.sub = sub_snap;` | 同 | **E0** |
| 孪生侧 | `bump_spine_iter/compiler.rs:193 mach.subst_cxt(bump,&self.sub,&cxt_arm)` | `compiler.rs:191 subst_cxt(bump,&mach.defs,&self.sub,&cxt_arm)` | E1（多传 `defs`，同角色；细节归 01/02） |

## 3 (d) `cxt.rs`：+27 token 的全部差异

429 行对 429 行，**无行数变化**；差异行 9 条，全部是 `Val::U`/`Tm::U` → `U(0)`：

| # | 行（两版同号） | 位置 |
|---|---|---|
| 1 | 201 | `String` 的 decl 条目 `ty:`（`cxt.rs:198-203`） |
| 2 | 211 | builtin `report_check_issue` 返回类型 |
| 3 | 213 | `string_to_global_type` 返回 |
| 4 | 217 | `create_global` 第 2 参 |
| 5 | 225 | `create_global` 应用版返回（`cxt.rs:219-228`） |
| 6 | 251 | `change_mutable_default` 返回 |
| 7 | 263 | `file_write_all_text` 返回 |
| 8 | 268 | `file_append_all_text` 返回 |
| 9 | 271 | `file_delete` 返回 |

`Cxt` 结构体字段（env/lvl/locals/pruning/names/name_mark/decl）、`bind`/`define`/`subst_cxt`/`bind_slots`/`add_builtin` 全部逐字节同。
归一化（`U (数字) → U`）后 6-shingle keep07 = **1.0000**（未归一化 0.9903）。
**E1**：`0` 只是分层宇宙的层级位（首次出现 **L09**，`cd41c476`/`b6f4ca34`），语义等价于 L07 的无层级 `U`。
**归因：L12 与 L09/L10/L11 同一哈希 `0fee0d38…`——一字未改继承。**

## 4 (a) L07 那 15% 去哪了（`L07→L12` = 557 增 / 221 删）

| 块 | L07 锚点 | 行 | 内容 | L12 对应 | 首次出现 | 档 |
|---|---|---:|---|---|---|---|
| A | `141-153` | 13 | 洞型 inlay（`push_inlay_hint`） | `141`（1 行） | **L08** | E3 |
| B | `176-208` | 33 | `ty_precheck` 零副作用预检 | `163-222 check_universe` | **L09** | **E2** |
| C | `210-233` | 24 | `check_ty` 的 Π 臂 + 按值 move（`deef97f7` 11-10 O(n²) 修复） | `223-225`（1 行委托） | L09 | E2 |
| D | `282-329` | 48 | def 观察面：`hover_query` 门控 / `render_typ_pretty` / 洞型 inlay label | `329-352` | **L08** | E3（inlay、门控）/ E1（渲染） |
| E | `476-487` | 12 | enum 与构造子的 `decl_spans` 登记 | 无 | **L08** | E3 |
| F | `569-580` | 12 | 局部/全局 `Var` 两条 hover 助手 | `894-911`（内联） | L08 | **E1** |
| G | `595-606` | 12 | `E.c` 投影补全候选 | 无 | **L08** | E3 |
| H | `616-628` | 13 | 接收者字段补全候选（`surface::raw_span`） | 无 | **L08** | E3 |
| I | `840-847` | 8 | `LiteralIntro` 自身类型 hover | `1194` | **L08** | E3 |
| J | `880-890` | 11 | `push_ctor_hover` 构造子使用处 hover | 无 | **L08** | E3 |

**量化**（本册口径）：L07 侧 4,726 个 shingle，L12 里丢 1,001 个。
**其中 L08 就丢了 707（15.0pp）、L09 再丢 284（6.0pp），L09→L12 只再丢 10 个（0.2pp）**。
`U`→`U(0)` 归一化只回收 0.57pp ⇒ **涟漪不是主因**。

**"被本章增量替换"还是"丢了"？两者都有，但性质分得清**：
- **被替换（B/C）**：L09 用全量 `check_universe` 换掉 L07 的轻量预检，有等价物 → **E2**。
- **真丢（A/D-门控/E/G/H/I/J）**：L12 里**没有等价生产者**——`completion_table` / `push_inlay_hint` / `inlay_wanted` / `hover_query` 在 L12 全层 grep 均 **0**，`push_ctor_hover` 只剩 `surface.rs:11` 一行注释引用、无实现。

### 4.1 观察面真丢的可观察后果（与 06 分册的边界）

- L12 的 `surface.rs` 仍声明 6 条通道（`surface.rs:28/31/33/35/38/40`），`surface.rs:61-62` 用 `completion.is_empty() && inlay_hint.is_empty()` 判"无观察结果"；
- 但 `mod.rs:2219-2221` 组装 `LspSurface` 时**只赋了 hover 一路**（`s.hover = infer.hover_table`），completion/inlay 永远空；
- 对照 L07：`mod.rs:2293 infer.surface()` → `observe.rs:296-298` 填满全部通道，且 `hover_query/inlay_query`（`mod.rs:2269-2270`）做采集门控。
- L12 的装配方式与 **L08 `mod.rs:2123 s.hover = infer.hover_table`** 完全同构 ⇒ **不是 11-23 移植漏项，而是 L08 起就没有 L07 的 `observe.rs` 设计**（L07 `observe.rs:59` 的 `render_by_shape` 在 L08 被内联进 `elaboration.rs:266`，L12 在 `elaboration.rs:240`——同一份）。细节归 06。

## 5 (b) +3186 token 的分层归属

| 阶段 | token | 行 | 加了什么 | 相对 L07 的档 |
|---|---:|---:|---|---|
| L07→L08 | +451 | +23 | 观察面从 `observe.rs` 内联进 `elaboration.rs`（`render_by_shape` L12:240-281、def 登记 L12:329-352、Var hover L12:894-911）；投影改为值级结构查找 | E3（门控/通道丢失）+ E1（渲染等价） |
| L08→L09 | +28 | 0 | **等量重写**：`ty_precheck`→`check_universe`（L12:163-222）、`Val::U`→`U(u32)`（19 处）、enum `universe_lvl` 扫描（L12:394-405）、Π 层级 `max(a_lvl,b_lvl)`（L12:1159） | **E2** + E4（分层宇宙能力） |
| L09→L10 | **+2,681** | **+313** | `Decl::TraitDecl`（L12:521-577）、`Decl::ImplDecl`（579-713）、`trait_wrap`（775-889）、`solve_multi_trait` 调用（318-323）、三处 `trait_wrap` 回落（1049-1054 / 1061-1066） | **E4** |
| L10→L11 | **0** | 0 | 逐字节同（`5da33a13…`） | — |
| L11→L12 | **+26** | +5 | **唯一本章增量**：拆 `Typ` 桥——`to_typ()`/`Typ::Any`（L11:625/631/785/798）→ `Val` 直用 + `Val::Flex(MetaVar(u32::MAX), List::new())` 通配（L12:788-795/806-808） | **E4**（L12 单边） |

⇒ **84% 是 L10 的 typeclass 章节增量，15% 是 L08/L09 的观察面重排与宇宙改写，只有 0.8%（22 增 14 删）是 L12 自己写的。**
所以正确的写法是"**L10 的 typeclass 增量被 L11/L12 原样继承 + L12 把求解从 `Typ` 降到 `Val`**"，不是"L12 新增了 typeclass"。

**E2（对 L07 既有精化路径的重写）具体三处，及可观察后果**：
1. `ty_precheck`+`check(…, Val::U)` → `check_universe`（`L07:210-233` → `L12:163-222`）。L07 明确"预检不推断、不造 meta，`?N` 编号不受扰动"（`L07:176-180`）；L12 会 `overwrite_meta` 解 meta（`L12:197/203`）。**后果**：同一条错源下 `?N` 编号与未解 meta 集合可能不同；L12 能把 L07 会报错的注解静默解成 `U(0)`。
2. 投影字段查找：L07 只有 `Sum`/`SumCase` 两条（`L07:636-712`）→ L12 增加单构造子 struct 的 `.mk` 剥链（`L12:955-985`）。**后果**：积类型上 `p.x` 从 `cannot project field`（`L07:710`）变为可解。
3. def 期渲染：L07 `render_typ_pretty` 返回 `(String, bool fin)`（`observe.rs:115`，`fin` 表"渲染未定"）→ L12 单路径 `render_by_shape` 回落 `pretty_tm`，且 `fin` 恒 `true`（`L12:349`）。**后果**：hover 文案的"未定"标记消失。

## 6 (e) 诊断与错误文案

| 项 | L07 | L12 | 档 |
|---|---|---|---|
| `Error` 定义 | `mod.rs: pub struct Error(pub String, pub Option<Span<()>>);` | **同，逐字节同**（含注释"文案不含行号/列号"） | E0 |
| `Error::at` 带 span | 有 | 有（`mod.rs:2205/2229`） | E0 |
| `Warning` / `Severity` | **0 / 0** | **0 / 0** | E0（L13 为 20 / 4） |
| `Error::new` 处数（全层） | 64 | 79 | +15 = typeclass/universe 新增 |
| `elaboration.rs` 中文文案 | 0 | 0 | 两侧均英文 |
| 中文诊断文案 | `pattern_match.rs:187/203/255/269` 等 | **同文件逐字节同** | E0 |

**唯一退化（E3，报错尾部渲染）**：

| L07 | L12 |
|---|---|
| `expected universe, got {}` + `pretty_tm(...)`（`L07:194`；注释 `L07:190-192` 明说「走 pretty（而非 Val 的 Debug 转储——大值树会印出巨量结构且不可读）」） | `expected universe, got {:?}`（`L12:215`）、`meta type {:?} is not a universe`（`L12:190`） |

后果：`Type` 位置写了长 Π 链时报错是 `Val` 的**调试结构转储**，不可读。前缀两边都在（L07 注释称被 blackbox v3 钉住），**只退化尾部**。

## 7 已确认等价清单（E0/E1，不必再查）

| 项 | 锚点（L07 / L12） | 理由 |
|---|---|---|
| `Cxt` 全量 | `cxt.rs:1-429` 除 9 行 | 归一化后逐字节等价，L09 起冻结 |
| `Cxt::subst_cxt` 正文 | `cxt.rs:453-479` 两边同 | 逐字节同 |
| 臂精化三连 | `pattern_match.rs:227/241/280` | 整文件六层逐字节同 |
| `check()` 的 λ/隐式 Π/let/match 各臂（洞臂另见 §4-A） | `elaboration.rs:81-140` / `82-141` | 仅注释措辞（E0） |
| 无注解 let 占位 `Tm::U(0)` | `L07:118` / `L12:118` | 同一"不物化"技巧；L12 注释改写为「L07/L08 同款，2026-11-23」（E1） |
| `insert`/`insert_until_*` 隐式插入 | `L07:19-80` / `L12:20-81` | 仅 `fn insert`→`pub(crate) fn insert`（E1；L12 新增 `unification.rs:808` 一个调用者，L07 无） |
| 投影 `Sum`/`SumCase` 字段查找 | `L07:614-712` / `L12:941-1066` | 判据与错误串同，L12 多 struct 剥链（1 条 E2 已列 §5） |
| `check_ctor_wf` 构造子良构性 | `L07:507-561` / `L12:715-774` | 同 |
| `infer_expr` 的 `Raw::Hole` 臂 | `L07:833-836` / `L12:1187-1190` | 双 `fresh_meta` 同构，仅 `Val::U`→`Val::U(0)`（E1） |

## 8 边界与未核实

- `[未核实]` L12 的 LSP 消费者是否真的读 `surface.completion` / `surface.inlay_hint`（本册只看引擎侧**产出**）。
- `[未核实]` `fin=false` 在 L07 显示层的实际效果，归 06。
- 孪生 `subst_cxt` 的签名差异（方法 vs 自由函数 + `defs`）归 01/02；`bump_spine_iter` 的 `name_map` 影子同步（`machine.rs:226-228`）属 01。
- 本册不引用上一轮 L07⟷L13 的任何数字；L13 仅作"载体不同"的对照锚点使用。

## 一脉相承评级

**强。** 理由：精化载体（σ/`subst_cxt`）在参考版与孪生上**同位置、同函数体、同调用点**，`cxt.rs` 归一化后逐字节等价且 L09 起冻结，`Error` 口径与中文诊断文案逐字节同，L12 自身只改了 22 增 14 删且全是本章的 Val 级求解增量——差异全部由 L08/L09/L10 引入并被忠实继承，没有一处是 L12 的倒退。

## Top-3 差异

1. **观察面真丢（E3-继承，量最大）**：L07 `elaboration.rs:141-153/595-606/616-628/840-847/880-890`（洞 inlay / 补全候选 / 字面量 hover / 构造子 hover）在 L12 无对应生产者，`mod.rs:2220` 只装配 hover 一路；首次消失于 **L08**（`L08_product_type/mod.rs:2123`），L12 原样继承。
2. **宇宙检查换机制（E2-继承）**：`L07:176-233`（`ty_precheck` + `check`，零副作用、不动 `?N`）→ `L12:163-222`（`check_universe` 会 `overwrite_meta` 解 meta）；首次出现于 **L09**，可观察后果是同错源下 `?N` 编号与未解 meta 集合可能不同。
3. **报错尾部渲染退化（E3-继承）**：`L07:194` `expected universe, got {}` + `pretty_tm` → `L12:215` `expected universe, got {:?}`（`Val` 调试转储）；L07 的注释 `L07:190-192` 专门说明过为什么不能用 Debug。
