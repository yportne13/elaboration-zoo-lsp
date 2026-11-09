# B 稿：L13「完全取代参考版」的阻塞项清单与删除条件（2026-09-27）

> 任务：task-2（接线阻塞项审计员）。本稿只读代码/文档，**未运行 cargo、未改任何被跟踪
> 文件、除本文件外未写任何路径**（唯一产物即本文件）。
>
> 证据分层：**[实测]** = 本轮用只读命令量到的数字/事实；**[代码]** = 本轮逐行读源码得出
> 的坐标；**[文档]** = 引自仓库既有文档；**[推断]** = 由代码结构推出、无直接数据；
> **[不确定]** = 明确标注、需要实验取数才能定价。行号以本轮读到的 HEAD 工作区为准。
>
> 与本轮 Lead 主稿（`docs/l13-perf-replace-2026-09-27.md`）的分工：主稿 §1/§5 已给出
> 事实基线与 R0–R6 路线；**本稿的增量为**：B1 穷尽路由表（含 CLI 逐子命令、测试侧默认、
> wasm 宿主、盲区登记）、B2 每项缺口的"会坏什么/最小修法/人天/风险/验收测试"、
> B3 逐请求 parity 表、B4 可勾选删除条件、B5 标出"必须先实验取数"的步骤，以及
> **4 条主稿未列的新发现**（见 §0.2）。

---

## 0. 一页纸：口径、结论、新发现

### 0.1 「取代」的三种含义（沿用主稿 §5.0，本稿给判据）

| 目标 | 本稿判据 | 本稿结论 |
|---|---|---|
| **α 生产路径取代** | LSP（桌面/web）+ CLI 正常输入下**零回落**，功能面逐请求 parity | 未达成：闸①（跨文件视野）仍拦所有 import/package 文件；1 个语料文件走 `untrusted-error` 回落 |
| **β 代码删除** | 参考引擎不进生产二进制（可 `#[cfg(test)]`/feature 门控），仅在测试里当判据 | **删除边界 ≠ 文件边界**：`Tm/Val/Decl/DeclTm/ExportedDecl/typeclass/pretty` 必须留在生产面，只有 `elaborator` 面可退场（§B2-9、§B4-F） |
| **γ 判据退休** | 连测试里也不留参考版 | **不可行（本轮新增证据）**：twin 自己的 21 个观察面单元测试就地调用 `Infer::infer` 当 oracle（`bump_spine_iter/observe.rs:297-303`、`:325-333`），删参考版＝连 twin 的判据一起删 |

### 0.2 本轮 4 条新发现（主稿 §1.4 未列）

1. **twin 接管文件上没有 quick fix / code action**。`twin_elaborate` 末尾把
   `quickfix_map` 写成空表（`src/lib.rs:1659`），而 twin 诊断不带 `data` id
   （`:1667-1670` 用 `Diagnostic::new_simple`）。参考版路径会给可修复错误挂
   quickfix 闭包（`build_diags`，`:2573-2584`）。⇒ 接管面扩大后，`textDocument/codeAction`
   + `typort.applyQuickFix`（`:3382-3430`）在 twin 文件上**静默失效**。当前
   `tests/` 侧对这一面**零测试**（全仓 grep `quickfix|applyQuickFix|code_action`：
   测试侧只有 `tests/namespace_tests.rs:1` 处命中）。
2. **`resident-unavailable` 是死标签**：`decline` 初值 `src/lib.rs:1447`，闭包内两条
   `return false` 路径都会改写它（`:1455` `prelude-prime-failed`、`:1474`
   `observe-failed`）⇒ 该 class 不可达。测试却把它列进 `KNOWN`
   （`tests/twin_engine_tests.rs:945`）——回落类别集合的可信度需要重估。
3. **参考版自己不跨文件共享 trait 实例**：`elaborate_reference` 的 `local_infer`
   被整体移进 `hover_table`（`src/lib.rs:2524`），全局 `self.infer` 自
   `load_prelude` 后**再无写入点**（全仓仅 `:1321`、`:1792`(MUT=false 只读克隆)）。
   ⇒ A3 的"trait 实例"半边的**跨文件**暴露面可能为零；真正的跨文件通道只有
   `cxt.decl` 与 `cxt.namespace`。这一条与文档口径（`lsp-twin-wiring:1515-1522`）不同，
   必须用两文件实验确认（**[不确定]**，见 §B2-2）。
4. **语料从不触发 `cross-file`**：`examples/**` 与 `tests/*.typort` **无一条**
   `import`/`package` 声明（[实测] 全目录 grep 为 0）⇒ `EXPECTED_FALLBACKS` 钉住的
   30 文件语料**完全覆盖不到闸①**，而 `tests/namespace_tests.rs`（30 例、91 处
   import/package）与 `tests/cross_file_tests.rs`（3 例）全部用 `Backend::new`
   跑参考版 ⇒ **twin 的 `cross-file` 路径今天没有任何自动化覆盖**。

### 0.3 五条最关键的阻塞项（按"不修就不能删"排序）

| # | 阻塞项 | 位置 | 为什么是阻塞 | 粗估 |
|---|---|---|---|---|
| 1 | **A2 跨文件视野**（闸①，依赖文件没进常驻 twin 会话） | `src/lib.rs:1398-1402`、`:2280-2304`；`bump_spine_iter/entry.rs:1118` | 所有 import/package 文件 100% 走参考版；参考版删不掉 | 6–13 人天 |
| 2 | **A3 导出面**（twin 不向参考域登记 `cxt.namespace` / inherent impl 条目；实例/`mutable` 面待实验） | `src/lib.rs:1616-1655`（只并 `cxt.decl`/`type_map`）；双端 `machine.rs:4010-4015`、`:4165` | 一旦 A2 落地，provider 侧由 twin 拥有 ⇒ 依赖者的 `x.method` 立刻丢成员 | 2–4 人天 |
| 3 | **字段投影 `def_span` 降级**（twin 项/值不持 binder span） | 表示：`bump_spine_iter/syntax.rs:27`、`:230-243`、`:269-281`；降级点 `machine.rs:3130-3132`、`:3157-3158` | 用户可见：F12 落在 `p.x` 不动；字段声明的 references/rename 看不到使用处；钉在 `tests/twin_engine_tests.rs:1073-1100` | 3–6 人天 |
| 4 | **信任闸 `untrusted-error`**（18-utils 的 `LetNamed` trait 求解分叉） | 判据 `src/lib.rs:1534-1562`；语料钉 `tests/twin_engine_tests.rs:797-799` | 只要有一个类别不敢发诊断，"零回落"就永远是例外清单；且晚回落＝双跑（twin+参考各跑一遍） | 3–5 人天 |
| 5 | **判据面不能删**（参考版必须留下当 oracle，只能 `cfg(test)` 降级） | twin 单测直接调参考 `Infer`（`observe.rs:297-333`）；4560 项测试默认引擎 = 参考版（`Engine::from_env`，`src/lib.rs:276-281`） | 决定 β 的形态与工作量；也决定"测试面改造"是本次最大的一块工程 | 2–4 人天（改造）+ 判据保留 |

> 附：**内存面**（native 429MB 稳态/730MB 峰 vs 参考 ~200MB；wasm 大证明文件 ~1.18GB vs 2GiB
> 硬顶）是限制 web 默认翻转的闸④，[文档] 主稿 §1.4 / `lsp-twin-wiring:1272-1318`；
> 本稿只在 §B2-7、§B4-D 给删除条件，不重复归因（归因属 A 稿）。

---

## B1 路由地图（穷尽表，每条 file:line）

### B1.0 入口总图

| 入口 | 代码位置 | 引擎来源 | 今天实际引擎 | twin 支持 |
|---|---|---|---|---|
| `elaboration-zoo-lsp`（wasm/web 用） | `src/main.rs:12` → `run_lsp_server` | `Engine::lsp_default()` | 取决于宿主注入的 env | ✅（web 默认 reference，见 B1.e） |
| `typort lsp` | `src/bin/cli.rs:386-388` → `src/lib.rs:3887` | `Engine::lsp_default()`（`src/lib.rs:3911`） | **twin**（unset 即 twin） | ✅ |
| `typort check` | `src/bin/cli.rs:390-393`、`668-738` | **硬编码** `Engine::Reference`（`:691`） | reference | ❌ |
| `typort emit` | `src/bin/cli.rs:396`、`499-546` → `src/emit.rs:154` | `Backend::new` → `Engine::from_env()` | reference（除非 `TYPORT_LSP_ENGINE=twin`） | ⚠️ 名义支持 |
| `typort build` | `src/bin/cli.rs:399`、`548-573` | 同上（`emit_design`） | 同上 | ⚠️ 同上 |
| `typort test` | `src/bin/cli.rs:403`、`575-…` | 同上（先 emit 再跑模拟器） | 同上 | ⚠️ 同上 |
| `typort stats` | `src/bin/cli.rs:407`、`741-825`（`Backend::new` 在 `:745`） | `Engine::from_env()` | reference（env=twin 时 prime 孪生并报 `twin_mem_stats`，`:796`） | ⚠️ 只为读数 |
| `typort tutorial` | `src/bin/cli.rs:411` → `src/tutorial.rs:357` | `Backend::new` | reference | ⚠️ 名义支持（未验证） |
| `typort quick` | `src/bin/cli.rs:421` → `src/quick.rs` | 无引擎 | — | N/A（纯文本） |
| `typort doc` | `src/bin/cli.rs:427`、`460-497` → `src/doc/collect.rs:75` | **硬编码** `Engine::Reference` | reference | ❌（注释：doc 需要参考版跨文件 decl 表） |
| 测试 harness | `tests/*.rs` 的 `Backend::new` | `Engine::from_env()` | reference | ⚠️ 需显式 `new_with_engine` |
| `l13lspsample`（采样工具） | `src/bin/l13lspsample.rs:49` | 命令行参数 | 可选 | ✅ |

`Engine` 本身：`Reference`/`Twin`（`src/lib.rs:243-247`）；`lsp_default`（`:255-260`，只有
`reference` 才回参考版）；`from_env`（`:276-281`，只有 `twin` 才选 twin）；`Backend::new`
= `new_with_engine(client, from_env())`（`:440`）。

### B1.a 文件级归属闸（闸①）

| 判据 | 代码位置 | 语义 | 现状 |
|---|---|---|---|
| `engine == Twin` | `src/lib.rs:1399` | 引擎选择 | 生产 LSP 恒真 |
| `!file_deps.contains_key(uri)` | `src/lib.rs:1400` | 该文件**声明了 import**（`update_deps` 扫 `Decl::Import{prefix}` 填表，`:2112-2156`，字段声明 `:406`） | 拦下所有 import 文件 |
| `!file_namespaces.contains_key(uri)` | `src/lib.rs:1401` | 该文件**声明了 package**（扫 `Decl::Package{path}`，`:2140-2143`，字段 `:409`） | 拦下所有 package 文件 |
| 回落记录 | `src/lib.rs:2280-2304`：先清 `twin_tables`（`:2286`），再 `note_twin_fallback(..., "cross-file", why)`（`:2301`），`why` 由 `:2291-2299` 拼出 "imports X" / "declares package Y" | | |
| 依赖图（供 A2 复用） | `update_deps` `:2112`；`rebuild_set` 拓扑序 `:2233-2259`；`visit_dep` `:2210`；`providers_under` `:2198`；`dependents_under` `:2187` | **已算好跨文件重放序**，A2 的 L2 就是喂这个序列 | 可用 |

### B1.b 运行期 decline 路径（`note_twin_fallback` 全集）

| class | 触发条件 | 代码位置 | 当前是否在用 | 语料触达 |
|---|---|---|---|---|
| `cross-file` | 文件有 import / 声明 package | `src/lib.rs:2301`（判据 `:1398-1402`） | **在用（主阻塞）** | **0/30**（[实测] examples 与 tests/*.typort 全无 import/package） |
| `untrusted-error` | 首条 ERROR 不属于信任名单（`can't unify…` / 确实未定义的 `name not in scope`） | `src/lib.rs:1549-1562`（分类器 `:1534-1548`） | **在用** | 1/30（`examples/hdl/18-utils.typort`，`tests/twin_engine_tests.rs:797-799`） |
| `symbol-defined-in-another-file` | 同一分类器判定"名字其实由别的文件定义" ⇒ 视图不足 | `src/lib.rs:1557` | 在用（需多文件工作区且无 import） | 0/30（单文件 harness 造不出） |
| `prelude-unavailable` | `self.twin_prelude == None`（`load_prelude` 从未跑，或引擎是 Twin 但 prelude 未装入） | `src/lib.rs:1438-1442`；写入点 `:1360` | 在用（防御；LSP 路径 `:3924` 先 load_prelude 再 main_loop） | 0 |
| `resident-unavailable` | `decline` 初值 | `src/lib.rs:1447` | **死标签**（两条失败路径都改写它，`:1455`/`:1474`） | 0（不可达） |
| `prelude-prime-failed` | `prime_resident` 返 Err（prelude 解析失败/装载失败） | `src/lib.rs:1450-1457` | 在用 | 0 |
| `observe-failed` | `observe_user(prelude, decls)` 返 Err | `src/lib.rs:1461-1476` | 在用 | 0 |
| `no-document-id` | `process_file` 未种 `document_id` | `src/lib.rs:2313-2318` | 理论上不可达（防御） | 0 |
| `no-parse-result` | `parser_with_macros` 返回 `None` | `src/lib.rs:2319-2335` | 理论上不可达（resilient lexer 恒 `Some`） | 0 |
| `hdl-check-gate` | — | 闸本体 2026-09-23 撤除，原址现为注释 `src/lib.rs:1564-1609`；**无任何调用点** | **已停用** | 0 |
| （非 class）粘性早退 | `twin_gate_distrusted` 命中即直落参考版、不记 class | `src/lib.rs:2306-2312`；管道字段 `:386`、清理 `:2692` | 管道保留、**无人置位** | 0 |

类别集合被测试钉住：`tests/twin_engine_tests.rs:939-950`（`KNOWN`）+ `:985-989`
（语料上只允许 `untrusted-error`）。**注意**：`KNOWN` 里含已死的 `hdl-check-gate` 与
不可达的 `resident-unavailable` ⇒ 这个"全集"是名义全集；新增/删除 class 时应同步（§B4-A）。

### B1.c CLI / 非 LSP 入口逐子命令

见 §B1.0 表。补充三点代码事实：

1. `typort check` 走 `Backend::on_change::<false>`（`src/bin/cli.rs:707`），而 `on_change`
   **没有 `self.engine` 分派**（`src/lib.rs:1762-1953`）：逐 decl `infer.infer` + 全局
   macro 合并（`:1787`）+ `type_map`（`:1866`），但 **不合并全局 `cxt.decl`、
   不记 `file_symbols`/`file_deps`、不做 `rebuild_set`** ⇒ 语义上"每个文件独立检查"。
   因此把 `check` 切到 `process_file` 会**顺带改变跨文件语义**（`import` 开始能解析），
   parity 必须逐文件逐字节验（§B2-9）。
2. `typort emit` 名义支持 twin（`process_file` 路径，`src/emit.rs:163`），但 emit 的
   **多文件**语义依赖 `mutable`/`ModuleRegistry` 的跨文件可见性；twin 的 `mutable` 是
   七表 journal 的一部分、**kick 末回滚**（`bump_spine_iter/entry.rs:1174-1178`、
   `:1305`）⇒ 多文件 emit 在 twin 下是否等价**未验证**（**[不确定]**，见 §B2-2）。
3. `src/doc/collect.rs:75` 是硬钉参考版（注释明说需要参考版跨文件 decl 表）；
   `src/tutorial.rs:357`、`src/quick.rs` 与引擎无关或未验证。

### B1.d 测试侧默认

| 事实 | 坐标 | 影响 |
|---|---|---|
| `Backend::new` 默认参考版 | `src/lib.rs:440` → `:276-281` | `cargo test` 的 LSP 面默认全跑参考版 |
| 17 个集成测试文件用 `Backend::new`（52 处） | [实测] `hover_tests`(20)、`completion_handler_tests`(6)、`twin_engine_bench`(4)、`twin_engine_tests`(4)、`println_two_phase`/`namespace`/`repro_sumcase_panic`/`zz_tmp_l13_debug`/`hdl_check_locations`(各2)、`trait_nat_param`/`cross_file`/`format_handler`/`hover_stress`/`impl_goto`/`macro_goto`/`quick_cheatsheet`/`probe_macro_bugs`(各1) | 这些文件的期望值＝参考版行为 |
| **没有任何 `tests/*.rs` 设置 `TYPORT_LSP_ENGINE`**（唯一提及是 `hover_tests.rs:46` 的注释） | [实测] | "8 套 LSP 守卫在 twin 下全绿"（`lsp-twin-wiring:924-927`）是**手工口径**，不进任何门禁 |
| 唯一自动化 twin-LSP 覆盖 = `tests/twin_engine_tests.rs`（26 例） | 助手 `:31-42`（`new_with_engine` 显式选引擎）；`tests/twin_engine_bench.rs` 4 例 `--ignored` | 门禁第 4 件（`tools/gate_l13.sh:85-89`，`GATE_NO_TWIN_LSP=1` 可跳） |
| L13 语言面 parity 以参考版 `run` 为 oracle | `tests/l13_fast_parity.rs:42/46/50/57`、`tests/l13_into_probe.rs` | 删参考版＝删这两套 oracle |
| twin 单测就地调参考 `Infer` 当 oracle | `src/L13_namespace/bump_spine_iter/observe.rs:297-333`（21 例一组） | 删参考版＝删 twin 自己的判据（§0.2-新发现③） |
| L13 参考引擎的单元测试 | `src/L13_namespace/{legacy_tests(134),mod(77),module_tests(39),class_tests(32),verilog_compat_tests(24),calc_tests(19),pretty(18),hdl_*_tests(61),debug_test(15),parser/mod(15),struct_refine_probe(4),…}` | [实测] `#[test]` 计数；直接驱动 `Infer`/`Cxt` |
| 全仓显式 `#[test]` 2181 个 / `cargo test` 69 target **4560 项** | [实测] src+tests 的 `#[test]` 计数；[文档] `docs/bench-matrix-2026-09-20.md:465` | "4560"是 cargo 汇总口径，两个数字不要混用 |

### B1.e wasm / web 宿主

| 事实 | 坐标 | 说明 |
|---|---|---|
| web 默认引擎 = reference | `vscode_extension/client/src/serverActions.ts:26-37`（`wasm: 'reference'` 在 `:35`，`cli: 'twin'` 在 `:36`）；`readEngine` `:49-55` | 显式 `twin` 才 opt-in |
| 引擎经 env 注入 guest | `extension.ts:96`（`env: { TYPORT_LSP_ENGINE: engine }`）；desktop 分支 `extension.desktop.ts:65-67`、`:217` | 服务端 `Engine::lsp_default` 读同一 env |
| 2 GiB 硬顶 | `package.json:137`（`--max-memory=2147483648`）；`extension.ts:69-70` 注释（孪生 ~730MB 峰） | 超限＝`RuntimeError: unreachable` 静默 trap（[文档] `lsp-twin-wiring:1272-1318`） |
| **设置说明与代码不一致** | `package.json:110` 写 "Defaults to `twin` on both backends"，但 `serverActions.ts:35` 的 wasm 默认是 `reference` | 文档/文案缺陷，顺手修 |
| 内存实测 | [文档] `lsp-twin-wiring:1296-1299`：adder_proof 页面 1.18GB（2GiB 顶）vs 参考 202–332MB | 闸④ |

### B1.f 周边开关与工具（不接管文件但影响"删除"）

- `TYPORT_LSP_ENGINE`：`src/lib.rs:256/277`；`typort lsp` 启动打印 `typort: lsp engine = {:?}`
  （`:3912`）；状态栏 `TyPort Ref|Twin`（`extension.ts:25-56`、`serverActions.ts:100-110`）。
- `TYPORT_TWIN_NO_COMPACT` / `TYPORT_TWIN_NO_USER_OBSERVE` / `TYPORT_KICK_DECLTIME` /
  `TYPORT_TWIN_BUMP_BUDGET_MB` / `TYPORT_TWIN_KICK_CLEAR_MEMO`：全部是 A/B 实验开关
  （`bump_spine_iter/entry.rs:1132-1157`、`:1218`），删参考版时**不构成阻塞**，但
  `force.rs:385 twin_mem_stats` 是 `typort stats` 的读数来源（`cli.rs:796`）。
- `L13_namespace::probe_count`（`mod.rs:24-26`）同时依赖两引擎 ⇒ 删参考版需保底实现。
- 看门狗 `typort-hdl/ping`（[文档] `lsp-twin-wiring:1322-1353`）与引擎无关，保留。

### B1.g 盲区登记（我确认"没有其它隐藏 Reference 路由"的方法与残余）

- 全仓 `Engine::Reference` 显式出现点只有 4 处：`src/lib.rs:245/257/279`（类型与两个构造器）、
  `src/bin/cli.rs:691`、`src/doc/collect.rs:75`（[实测] grep）。其余全部经
  `Engine::from_env()`/`lsp_default()`。
- `src/lsp_stdio.rs` 是纯传输层（chunked stdio + unbounded channel），**引擎无关**，不构成阻塞。
- 残余盲区：`src/bench_pre/**` 与 `src/bench_head/**` 是 L07 的**另一对**参考/快版（不属 L13），
  `tests/l07..l12_fast_parity.rs` 的 oracle 是各自层的参考实现 ⇒ 删除 L13 参考版
  **不影响**它们（[代码]）。L13 参考版删除**只**影响上表列出的面。

---

## B2 逐项缺口

> 每项统一六段：**删掉会坏什么 / twin 缺什么 / 最小修法 / 人天 / 风险 / 验收测试**。
> 人天为独立粗估，与主稿 §5.2 的 R0–R6 对齐处已注明；标 ★ 的是"必须先实验取数才能定价"。

### B2-1 ★ A2：跨文件视野（闸① 完整拆除）

- **删掉会坏什么**：`file_deps`/`file_namespaces` 命中即回落参考版（`src/lib.rs:2280-2304`）。
  删参考版后，**任何** import/package 文件无引擎可用；`tests/cross_file_tests.rs`（3 例）、
  `tests/namespace_tests.rs`（30 例）全部失去被测语义；多文件 HDL 工程（submodule 分文件）
  直接失效。这是 α 的唯一主阻塞。
- **twin 缺什么**：不是语言语义——twin **已实现** import/package（`machine.rs:4335-4346`
  package 前缀、`:4348-4451` import 别名/通配/冲突拒绝、`:2989-3008` 限定路径三试、
  `:3985-4014` namespace 方法分派）。缺的是**会话视野**：`observe_user(prelude, user_ast)`
  只接受**一个**文件的 AST（`bump_spine_iter/entry.rs:1118`），resident 检查点只固化
  prelude 稳态（`entry.rs:891`），调用点 `src/lib.rs:1461` 也只传该文件 `decls`。
- **最小修法设计**（分三级，与主稿 §5.1 L1/L2/L3 同构，这里补实现切口）：
  - **L1（0.5–1 人天）**：放宽闸到"import 的每个 namespace 的 provider **不在当前打开文件集**里"
    （`ns_providers`/`providers_under`，`src/lib.rs:2198`）＋"package 文件没有任何打开文件 import 它"
    （`ns_dependents`/`dependents_under`，`:2187`）。视野未变，只是承认"本来也解析不了"的情形
    ——两版应报同一句 `cannot import 'X': no such namespace in scope`（`machine.rs:4378-4386`）。
    切口：`twin_can_own`（`:1398-1402`）加两个谓词；`note_twin_fallback` 的 detail 复用 `:2291-2299`。
  - **L2（5–10 人天，主体）**：常驻 twin 升级为**项目会话**：按 `rebuild_set`（`:2233`）的
    拓扑序，把依赖文件段逐段重放进会话，最后放当前文件。切口：
    `entry.rs:1118 observe_user` 泛化为 `observe_segments(prelude, &[(uri, path_id, &[Decl])])`；
    每段末把该段的 `cxt.decls`/`cxt.namespace`/`mutable`/`import_map` 状态并入会话基线；
    观察表按 `path_id` 分文件过滤后只导出当前文件的 `ObserveSnapshot`（表结构已支持，
    `ObserveSnapshot::hover_entry_at` 已按 `path_id` 过滤，`src/lib.rs:326-336`）。
    同时消掉 `symbol-defined-in-another-file`（`:1557`）。
  - **L3（1–2 人天）**：删 `twin_can_own` 的两个判据，只留引擎判据；`EXPECTED_FALLBACKS` 中
    `cross-file` 归零。
- **人天**：L1+L2+L3 = **6–13 人天**（与主稿 R1 一致；其中 L2 的定价必须靠 §B5-P2 的实验）。
- **风险**：
  1. **逐段失效成本**（最大风险）：`bump` 不支持截断，`state_journal_rollback` 只能回到
     **kick 起点**（`entry.rs:1300-1305`），没有"段边界检查点"。要做"只重放被改动文件之后的段"，
     就得每段一个 arena 检查点；现成手段只有 `compact_state` 全量深拷（O(可达态)，~120ms/次，
     [文档] `lsp-twin-wiring:951-966`）⇒ 项目文件多时**可能比参考版更慢**。若实验证伪，
     退路是"每 kick 全量重放项目"（正确但成本随项目线性）。
  2. 观察面键：多文件重放时 `hover/completion/inlay` 的 push 会跨文件累积，必须按 `path_id`
     过滤导出，否则 A 文件的 hover 会串到 B（现有 `twin_tables` 是 per-URI，安全边界在导出处）。
  3. `twin_tables` 的失效时机：编辑 provider 时 dependent 会被重建（`rebuild_set`），
     旧快照必须清（现有 `src/lib.rs:2286` 的清理逻辑要扩到"会话段失效"）。
  4. 内存：会话段常驻会把 wasm 的 1.18GB 峰值进一步推高（闸④），可能与 B2-7 互锁。
- **验收测试**：
  1. `tests/cross_file_tests.rs` 3 例在 `Engine::Twin` 下全绿（0 回落、`global_decl_keys`
     语义等价），并新增"provider 关闭后 dependent 诊断与参考版逐字节一致"。
  2. `tests/namespace_tests.rs` 30 例在 twin 下跑通（或新增 twin 版对照），
     `import`/通配/限定/冲突拒绝的错误文案逐字节。
  3. 新语料 walk：`examples/**` + `tests/*.typort` + 内嵌多文件 fixture 的
     `EXPECTED_FALLBACKS` 只剩 `18-utils`。
  4. 回归闸：`l13_fast_parity`、`twin_engine_tests`、`lib L13_namespace::` 全绿（`tools/gate_l13.sh`）。

### B2-2 ★ A3：导出面（`cxt.namespace` / 实例 / `mutable`）

- **删掉会坏什么**：`twin_elaborate` 只把 `cxt.decl`（`:1616-1639`）与 `type_map`（`:1641-1655`）
  并回参考域；**不登记** `cxt.namespace`（inherent impl / trait 方法分派表）与
  `file_namespace_regs`（`:402-404`），也不登记 trait 实例。今天两端都是参考版所以看不见
  （[文档] `lsp-twin-wiring:1515-1522`）；A2 落地后 provider 侧由 twin 拥有 ⇒ 依赖者的
  `x.method` 解析会丢成员（`cxt.namespace` 是唯一的跨文件方法通道，`elaboration.rs:2485-2492`）。
- **twin 缺什么**：
  - twin 的 namespace 是 bump 持久链 `NsCons { val: V, methods: &[SmolStr], type_name: &str, next }`
    （`machine.rs:1918-1926`），需要转成参考域
    `List<(Rc<Val>, HashSet<SmolStr>, SmolStr)>`（`cxt.rs:320`）。转换所需的逃逸桥已存在：
    `v_to_ref_val`（twin → 参考值，`entry.rs:1282` 已在用）。
  - 实例面：twin 在 `tstate.solver.impl_trait_for`（`machine.rs:4165`）登记，属七表 journal，
    **kick 末回滚**（`entry.rs:1305`）。
  - **[不确定①]** 参考版是否**跨文件**共享实例：`elaborate_reference` 把 `local_infer` 整体
    移进 `hover_table`（`src/lib.rs:2524`），全局 `self.infer` 自 `load_prelude` 后无写入点
    （全仓仅 `:1321`、`:1792`（`MUT=false` 只克隆））⇒ 推断"实例不跨文件"。若是，则 A3 的
    实例半边只对**同文件后续 decl** 有意义，跨文件暴露面为零,工作量与优先级都要下调。
    **必须用两文件实验钉死**（§B5-P0）。同理 `mutable`（`Rc<RwLock<HashMap>>` 共享，但每文件
    结束被 `clear()`，`src/lib.rs:2503`）在 LSP 路径里也不是跨文件通道 ⇒ twin 的 kick 末回滚
    与参考版**等价**；但 `emit`（多文件 `process_file`）两侧都"清后再用"，
    多文件模块注册是否等价仍需实验（**[不确定②]**）。
- **最小修法设计**：
  1. `twin_elaborate` 导出结构体扩一项 `namespace: Vec<(Rc<Val>, HashSet<SmolStr>, SmolStr)>`
     （`ExportedDecl` 同址，`mod.rs:371-378` 旁加 `ExportedNamespace`）。
  2. `entry.rs:1266-1297` 的导出段遍历 `cxt.namespace` 链，用 `v_to_ref_val` 转 `val`，
     `methods.iter().cloned().collect()`，`type_name` 转 `SmolStr`。
  3. `src/lib.rs:1616` 之后的合并段按 `elaborate_reference:2469-2497` 的同款纪律合并
     （去重按 `Rc::as_ptr`，登记 `file_namespace_regs` 供 close/edit 撤销）。
  4. 实例面：视 §B5-P0 实验结论决定"只做同文件"还是"扩到跨文件"（后者需要把
     `class_instances` 增量导出并合并进全局 `Infer`，而全局 `Infer` 今天不回写 ⇒ 还需要先
     决定全局实例表的归属，工作量另计）。
- **人天**：namespace 半边 **2–4 人天**；实例半边 0–3 人天（取决于实验）。
- **风险**：`v_to_ref_val` 只覆盖固定形态（闭包/Pi 等 unreachable，[文档] `lsp-twin-wiring:46-48`）；
  namespace 条目的接收者值可能是 trait Sum / 复杂形态 ⇒ 需先扩桥或改走通用 `quote`。
  方法名集序、去重键（指针 vs 结构）必须与参考版一致，否则 `x.method` 歧义诊断会分叉。
- **验收测试**：两文件 fixture（A 声明 `impl`/`trait`，B import 后 `x.method`）在 twin 下
  与参考版逐字节（诊断 + goto + hover）；`cxt.namespace` 长度/条目在双引擎逐条相等；
  provider 编辑/关闭后 dependent 的成员解析同步更新。

### B2-3 字段投影 `def_span` 降级（binder span 进 twin 表示）

- **删掉会坏什么**：`p.x` 的 `def_span` 在 twin 侧退化成使用处 token（`machine.rs:3130-3132`
  结构体字段、`:3157-3158` 构造子字段），于是 F12 落在 `p.x` 不动、字段声明处的
  references/rename 看不到使用处（[文档] `lsp-twin-wiring:1505-1510`）。
  删参考版后**没有回退路径**，这是纯用户可见退化。现被测试显式钉住：
  `tests/twin_engine_tests.rs:1073-1100`（`twin_field_projection_def_span_is_known_degraded`），
  `tests/twin_engine_tests.rs:1002-1051` 逐 offset 比对时把该差异列为唯一允许项。
- **twin 缺什么**：binder 名字只存 `&str`，**没有 span 字段**：
  `Tm::Pi(&'a str, …)`（`syntax.rs:27`）、`Tm::Lam(&'a str, …)`（`:21`）、
  `PiCell { name: &'a str, … }`（`env.rs:129-135`）、`CloCell { name: &'a str, … }`（`:121-126`）、
  `SumParamV { name: &'a str, … }`（`syntax.rs:230-235`）、`SumDataV { name: &'a str, … }`
  （`:239-243`）、`XCell::Sum/SumCase`（`:269-281`）、`NsCons.type_name`（`machine.rs:1924`）。
  参考版对应位置全是 `Span<SmolStr>`：`Tm::Pi(Span<SmolStr>, …)`（`mod.rs:442`）、
  `Val::Sum(Span<SmolStr>, …)` / `SumCase{datas: SumCaseDatas}`（`mod.rs:827-838`）、
  `SumCases = Rc<Vec<Span<SmolStr>>>` / `SumCaseDatas = Rc<Vec<(Span<SmolStr>, …)>>`
  （`mod.rs:1081-1086`）；参考版推送点带真 `def_span`：`elaboration.rs:2600-2601`、
  `:2630-2634`。
- **最小修法设计**（两条路，建议先做 (a) 验证价值）：
  - **(a) 窄修（1–2 人天，先做）**：只给"字段槽"补 span——`SumParamT/SumDataT`
    （`syntax.rs:60+` 区域）与 `SumParamV/SumDataV` 各加一个 `span: Span<()>`（或
    `&'a Span`），构造点全部来自 `Decl` AST 的字段 token，可从 `parser::syntax` 直接取。
    改动点集中在 `syntax.rs`、`eval.rs`（构造点 `:42`、`:591-594`）、`force.rs:860-871`、
    `quote.rs:69`、`compact.rs:218-220`、`prim.rs:434-435`、`machine.rs:3130-3158`。
    打包值 `V` 是 64 位字，`SumDataV` 增字段会改 `XCell` 尺寸/对齐（`env.rs:137-147`
    的对齐断言）⇒ 需重新过 align/size 断言与 `compact` 深拷器。
  - **(b) 全量（3–6 人天）**：`Tm/PiCell/CloCell/SumParam*` 全体换 `Span<SmolStr>`，
    与参考版表示对齐（顺带消掉其它零 span 偏差）。代价是 pretty/quote/compact/force
    全链回归面大。
- **人天**：**(a) 1–2；(b) 3–6**（本稿推荐 (a)，把 (b) 留作"零 span 偏差"清理项）。
- **风险**：`XCell` 尺寸变化影响 packed `ptr|tag` 编码与 `compact_state` 深拷
  （`compact.rs:218-402`）——漏一处就是野指针；`SumDataV` 是 `Copy`（`syntax.rs:238`），
  加非 `Copy` 字段会级联改签名。收益（F12 与字段 references）用户可见但不算高频。
- **验收测试**：把 `twin_field_projection_def_span_is_known_degraded` 反转为
  "def_span = 字段声明 token"；`twin_goto_definition_matches_reference_on_owned_file`
  去掉"字段投影例外"豁免；`prelude_full_observation_tables_match_reference`
  （`observe.rs:1224+`）删掉第③类"允许的降级"；新增字段处 `references`/`rename`
  双引擎逐条对拍。

### B2-4 信任闸（`untrusted-error`；18-utils）

- **删掉会坏什么**：撤掉分类器（`src/lib.rs:1534-1562`）＝允许 twin 发布它**可能报错**的诊断；
  这类错误一旦分叉就是"错的诊断 > 慢的诊断"（注释 `:1520-1524`）。不撤＝`18-utils` 永远
  双跑（twin 段 + 参考段，[文档] `lsp-twin-wiring:901-905`、`:918-921`），且参考版删不掉。
- **twin 缺什么**：`18-utils` 的 `LetNamed` trait 求解分叉——twin 对用户 decl 多插入约
  246 次隐参 ⇒ 多注册 trait meta ⇒ 递归求解失败（[文档] 主稿 §5.1 面 2）。属**语义分叉**
  而非缺功能；需要逐 decl 的隐参插入计数对照来定位。
- **最小修法设计**：不改分类器，先修分叉：(1) 用 `TYPORT_DECL_PROBE`/`FUNC_PROF`
  把两版在 18-utils 上的 `implicit insertions`/`fresh_meta`/`solve_multi_trait` 调用序列
  对齐（工具已有：`l13lspsample`、`TYPORT_KICK_DECLTIME`）；(2) 定位差异点后最小修
  （历史同类根因：`tm_refs_bn` 索引公式、unifier 臂序、嵌套 unify 共享工作栈，
  [文档] `lsp-twin-wiring:983-1212`）；(3) 分类器退化为恒信任，保留 debug assert
  `debug_assert!(twin_errors ⊆ reference_errors)` 供测试期报警。
- **人天**：**3–5 人天**（与主稿 R2 一致；定位不确定，可能上浮）。
- **风险**：修错方向会把"真分歧"改成"沉默失配"；撤闸后失去运行期唯一保险
  ⇒ 必须先在语料+新增错误语料上量到 0 `untrusted-error` 再撤，且撤闸与"全语料对拍报告"
  同一次提交。
- **验收测试**：全语料 0 `untrusted-error`（`EXPECTED_FALLBACKS` 清空）；
  `twin_user_errors_match_reference_diagnostics` / `twin_diagnostics_match_reference`
  错误语料扩到覆盖历史每一类（solve-trait、歧义名、universe、隐参）；
  新增 `18-utils` 单文件 parity（ERROR+WARNING+INFORMATION 逐字节）。

### B2-5 quick fix / code action 面（**本轮新发现，用户可见**）

- **删掉会坏什么**：twin 拥有的文件上 `textDocument/codeAction` 与
  `typort.applyQuickFix`（`src/lib.rs:3382-3430`）**永远没有候选**——`twin_elaborate`
  把 `quickfix_map` 置空（`:1659`），twin 诊断无 `data` id（`:1667-1670`）。
  参考版路径下载有 fix 闭包（`build_diags:2573-2584`、`on_change:1894-1909`）。
  今天 29/30 语料文件已被 twin 接管 ⇒ **这个功能事实上已经在语料上消失了**，只是没人测。
- **twin 缺什么**：错误载荷里没有 canonical-fix 闭包（参考版 `Error(msg, Vec<fix_fn>)` 的第二元）。
  twin 的错误构造点遍布 `unify.rs`/`machine.rs`/`typeclass.rs`，多数只带 span+文案。
- **最小修法设计**：
  - **退路 A（0.5 人天，先做）**：twin 拥有时若该文件此前有参考版 quickfix（或按需触发
    一次参考版 elaboration）就沿用；成本是双跑，只对"用户真的调 codeAction"的文件付。
  - **正解 B（1–2 人天）**：把 twin 的几类可修复错误（同名 shadow、未定义名 typo 建议、
    universe 提示等）在 `twin_elaborate` 侧映射成已有的 fix 生成器；参考版 fix 闭包是
    `Box<dyn Fn() -> Option<String>>`（纯字符串重写），不依赖参考引擎状态 ⇒ 可直接复用
    生成逻辑（把生成器从 `elaboration.rs` 抽成独立函数即可）。
- **人天**：**1–2 人天**（退路 A 0.5）。
- **风险**：fix 闭包捕获参考域状态时退路 A 会引入双跑延迟；正解 B 需逐类核对 fix 语义
  （改错代码比没有 quick fix 更糟）。
- **验收测试**：新增 `tests/code_action_parity.rs`：对可修复错误语料在双引擎上比对
  `codeAction` 数量/标题/`applyQuickFix` 结果文本逐字节；断言 twin 拥有的文件
  `quickfix_map` 非空（或明确记录"该类无 fix"）。

### B2-6 诊断面其它偏差（历史清单 + 现状）

| 偏差 | 现状 | 阻塞性 |
|---|---|---|
| `?N` meta 编号跨引擎不同（偏差 3） | 直播渲染走 pretty，诊断文案不比对 meta（[文档] `lsp-twin-wiring:91-93`） | 否（对拍需归一化） |
| 零 span 条目（偏差 6） | twin 合成 binder 的 push 键为零 span；`observe.rs:1218-1223` 已列为"放行工件" | 是（B2-3 (b) 顺带清） |
| 参考版 `Val::Sum` cases span 丢 start（start=0 畸变） | `observe.rs:1218`、`:1258-1261` 放行 | 否（参考版侧 bug，删参考版后消失） |
| println 两阶段发布 | twin 立即口径也能两阶段（`src/lib.rs:1691-1707`）；`defer_println`/`println_jobs` 仅参考版（`:2406`、`:2512-2519`） | 否（已 engine-agnostic 化） |
| 解析错误完全一致 | 两引擎共用 `parser_with_macros`（`src/lib.rs:2319-2335`、`:2350-2356`） | 否 |
| twin 诊断无 quickfix | 见 B2-5 | **是（用户可见）** |

### B2-7 内存（闸④：web 翻转的前置）

- **删掉会坏什么**：web 宿主 2 GiB 硬顶下 twin 对大证明文件 ~1.18GB（参考版 202–332MB），
  余量不足以再装 A2 的"会话段"；超限＝`RuntimeError: unreachable` 静默 trap
  （[文档] `lsp-twin-wiring:1272-1318`）。参考版一删，web 的逃生口（`reference`）没了。
- **twin 缺什么**：每 kick 中间分配 ~850MB（[文档] 主稿 §5.1 面 3）；常驻 429MB 稳态
  /730MB 峰的构成本身是设计（bump + 压实），不是 bug。
- **最小修法设计**：随 A 稿（性能面）的收口项走；本稿只给门槛：
  (1) 每 kick 中间分配下降（复用/惰性化）；(2) 会话段内存预算独立核算；
  (3) 内存天花板探针 + 崩溃可见化（`typort-hdl/ping` 已有）必须能覆盖"装不下"。
- **人天**：**5–10 人天**（与主稿 R4 一致）；含 wasm 真机验证。
- **风险**：降到 2GiB 以下不代表安全——需**单文件峰值 + 会话增量 ≤ 预算**的硬约束，
  而非平均值；wasm 上 `--max-memory` 与 descriptor 必须同步（[文档] `lsp-twin-wiring:760-764`）。
- **验收测试**：native 峰值 ≤ 约定（当前 730MB）；wasm 上加 `adder_proof` + 多文件工程
  跑满 30 分钟无 trap；`resident_memory_growth_per_kick` 与 compaction 回归
  （`resident_compaction_matches_fresh_replay_across_kicks`）全绿。

### B2-8 CLI 入口统一（闸⑤：`typort check` 专线）

- **删掉会坏什么**：`typort check` 显式构造参考版（`src/bin/cli.rs:691`）并走 `on_change`
  （`:707`），而 `on_change` 无引擎分派 ⇒ 参考版删掉后 `check` 没有实现。
  同理 `typort doc`（`src/doc/collect.rs:75`）硬钉参考版。
- **twin 缺什么**：`on_change` 口径的等价物（逐文件独立、不跨文件、不写全局表）。
  `process_file` 是超集但**语义不同**（会带跨文件解析与 rebuild 顺序）。
- **最小修法设计**：(1) 给 `check` 切 `process_file`（`emit` 已证明可行），先逐文件
  逐字节对拍 `examples/**` + `tests/*.typort`；(2) `doc` 改为基于 twin 会话收集 decl
  （`doc/collect.rs` 只用 `cxt.decl` + 解析产物，A3/B2-1 落地后可移除硬钉）。
- **人天**：**2–4 人天**（与主稿 R5 的入口部分一致）。
- **风险**：`check` 的**跨文件语义变化**（import 开始能解析）会让现有 golden 输出改变；
  `check` 也是唯一"无 LSP 依赖"的用户可见诊断面，回滚成本高。
- **验收测试**：`typort check` 对全语料输出与改前逐字节一致（单文件情形）；
  新增多文件 `check` 用例并记录语义变化；`tests/emit_tests.rs`（10 例）、
  `docgen_tests.rs`（3 例）全绿；`tests/sim_tests.rs`（17 例）不受影响。

### B2-9 β 的删除边界（参考引擎"能删到哪"）

- **删掉会坏什么**：`L13_namespace/mod.rs` 不只装 elaborator，还装着 LSP 生产面**必须**的类型与
  工具：`Decl`（`:363`）、`ExportedDecl`（`:371-378`，twin 写、lib.rs 读）、`DeclTm`（`:399`）、
  `Tm`（`:434`）、`Val`（`:807`）、`SumParams/SumCases/SumCaseDatas`（`:1081-1086`）、
  `Infer`（`:1330`）、`format_check_warning`（`:4193`）、`take_check_issues`（`:4173`）、
  `take_fresh_check_issues`（`:4214`）、`pretty::pretty_tm`（lib.rs `:2600` 用）、
  `prim_version_bump`、`FUNC_PROF`、`clone_prelude_state`、`PreludeParse`/`parse_prelude_files`、
  `typeclass::{Instance, Assertion, Synth}`（**twin 自己就用**，`bump_spine_iter.rs:218`）。
  [实测] `src/lib.rs` 对 `L13_namespace::*` 的全部引用仅 26 处（上列即其全集）。
- **twin 缺什么**：不需要"缺"——这是**重构**问题：必须把"域类型 + 渲染 + typeclass 类型"
  与"参考 elaborator 本体（`elaboration.rs`、`unification.rs`、`pattern_match.rs`、
  `cxt.rs` 的 locals/refresh、`canonical.rs`、`syntax.rs` 的 `close_ty/Locals`）"切开，
  后者才可 `#[cfg(test)]`/feature 门控。
- **最小修法设计**：新增 feature（如 `reference-oracle`，默认**关闭**）包住参考 elaborator；
  `#[cfg(test)]` 下默认打开以维持现有测试与 twin 的 oracle。`L13_namespace::run`/
  `run_with_prelude` 只在测试/bench 面编译。生产 target（`elaboration-zoo-lsp`、`typort`）
  不再链接 `Infer::infer`。
- **人天**：**2–4 人天**（拆分 + 编译矩阵 + 文档）。
- **风险**：`mod.rs` 是 8158 行、且是主线正在改的文件（`mod.rs`、`legacy_tests.rs`）⇒
  必须与主线排期错开；feature 门控容易漏 `#[cfg]`（建议用 `cargo build -p` 的
  feature 矩阵 + `nm`/符号检查验证"生产二进制无参考 elaborator 符号"）。
- **验收测试**：`cargo build --release`（默认 feature）成功且 `nm` 无 `Infer::infer`/
  `solve_multi_trait` 符号；`cargo test`（含 oracle feature）全绿；
  `typort check`/`emit`/`doc`/LSP 冒烟通过。

### B2-10 观察面导出的其它小项

| 项 | 会坏什么 | 最小修法 | 人天 | 验收 |
|---|---|---|---|---|
| trait/ns 方法 hover 的 def_span 形态 | 已有移植（[文档] `lsp-twin-wiring:118`），但无独立对拍 | 并入 B2-3 的对拍 | 0.5 | 双引擎逐条 |
| `inlay`/`completion` 的整表互检覆盖 | 只有 `observe.rs` 的合成 fixture + `twin_engine_tests` 少数点 | 扩到 `examples/**` 全量三表 diff | 1 | 全语料三表逐条 |
| 宏/`builtin://` 的 path_id 归属 | 多文件会话后需按 path_id 过滤（B2-1 风险 2） | 随 A2 | — | 随 A2 |
| `engine` 文案/设置不一致 | `package.json:110` 与 `serverActions.ts:35` 矛盾 | 改文案 | 0.1 | 人工核对 |

---

## B3 功能面 parity 清单（逐请求）

| LSP 请求 / 功能 | 当前由谁服务 | twin 侧是否已具备 | 缺什么 / 备注 |
|---|---|---|---|
| `publishDiagnostics`（ERROR） | twin 拥有时 twin（`twin_elaborate:1663-1678`），否则参考版 | ✅ 语料 29/30 | 信任闸（B2-4）；quickfix 载荷缺失（B2-5） |
| `publishDiagnostics`（WARNING/HDL 自检） | 同上（`:1679-1690`） | ✅ | 闸③已撤，漏报**运行期不可自证**（残余风险，`src/lib.rs:1603-1609`） |
| `publishDiagnostics`（INFORMATION/println） | 同上，两阶段（`:1691-1707`） | ✅ | 有专门 parity（`twin_information_diagnostics_match_reference_on_proof_examples`） |
| `textDocument/hover` | 引擎分派：twin 快照优先、参考表兜底（`hover_at:509`、`hover_entry_owned:565-583`） | ✅ | 字段投影 `def_span`（B2-3）；跨文件 def 的 Path1 依赖导出表（A3） |
| `definition`（goto） | 由 hover 表驱动（`goto_definition_at:2806-2866`，读 `hover_entries_owned:593`） | ✅（含逐 offset 对拍测试） | 唯一已知差异＝字段投影（钉在 `:1054-1071`）；跨文件 goto 依赖 A2/A3 |
| `references` | `cross_file_references:2038-2081` 扫 `all_hover_tables_owned:647-662`（twin 快照优先） | ⚠️ 部分 | 字段声明的使用处找不到（B2-3）；跨文件 provider 未打开时视野不足（A2） |
| `rename` | `rename_at:2082-2110`（同上表） | ⚠️ 部分 | 同 references |
| `completion` | `completion_at:2871-2974` → `completion_entries_owned:605-612` | ✅ | 只覆盖成员补全 + import 前缀（`import_context_completions:2003`，与引擎无关） |
| `inlayHint` | `inlay_hint_at:2978-2997` → `inlay_entries_owned:615-622` | ✅ | 2 个移植点已验（[文档] `lsp-twin-wiring:123`） |
| `codeAction` / `executeCommand(typort.applyQuickFix)` | 参考版 fix 闭包（`build_diags:2573-2584`）；twin 置空（`:1659`） | ❌ | **B2-5（本轮新发现）** |
| `formatting` / `rangeFormatting` | 纯 parser/format（`format_document_at:3052`、`format_range_at:3075`），与引擎无关 | N/A | 无缺口 |
| `semanticTokens`（full/range） | **未实现**：`src/ls.rs:68-84` 返回 `method_not_found`，`initialize` 未声明（`src/lib.rs:3111-3149`） | N/A | 与"取代"无关，非阻塞 |
| `documentSymbol` | **未实现**（trait 无该方法，capabilities 未声明） | N/A | 同上 |
| `signatureHelp` | **未实现** | N/A | 同上 |
| docgen（`typort doc`） | CLI：`doc/collect.rs:75` 硬钉参考版 | ⚠️ 名义可迁 | B2-8 |
| emit Verilog（`typort emit/build/test`） | CLI：`emit.rs:154` `Backend::new`（env=twin 时 twin） | ⚠️ 名义支持、**未验证** | 多文件 `mutable`/模块注册在 twin 的 kick 末尾回滚（B2-2 [不确定②]）⇒ 需实验 |
| 诊断的 `?N`/span 归一化 | 两引擎文案归一化口径（[文档] `lsp-twin-wiring:91-93`） | ✅ | 对拍工具需持续维护 |

> 结论：**LSP 面唯一"已经坏了但没人发现"的是 codeAction/quickfix（B2-5）**；
> references/rename 的缺口是 B2-3；其余请求在"单文件、无 import"的口径下已 parity。

---

## B4 删除条件（Definition of Done，可勾选）

> 勾选前提：每一项要么有可复跑的命令/测试，要么有明确的人工核对记录。
> 建议把 A–F 做成 `tools/replace_ready.sh` 的输出清单。

### A. 判据与测试改造（必须最先做）

- [ ] `tools/engine_parity.sh`（新）：对 `examples/**` + `tests/*.typort` + 内嵌多文件 fixture
      逐文件输出 `归属引擎 / fallback class / ERROR+WARNING+INFORMATION 逐字节 / kick 墙钟 / RSS 峰`；
      能复现"29/30 拥有 + 18-utils 回落 + examples 1.78×"三个已知结论 ⇒ 判据可信（R0 退出判据）。
- [ ] `EXPECTED_FALLBACKS`（`tests/twin_engine_tests.rs:797-799`）从"examples 语料"扩到
      "全仓 `.typort` + 内嵌 fixture"，且只允许 `untrusted-error` 一项。
- [ ] `KNOWN` class 集合（`:939-950`）与 `note_twin_fallback` 实际调用点逐一核对：
      删死标签 `resident-unavailable`、标注 `hdl-check-gate`（无调用点）、
      为每个在用 class 各写一条"能造出它的最小 fixture"。
- [ ] 新增 twin 下的跨文件用例：`package`+`import` 两文件、provider 关闭、编辑 provider
      触发 dependent 重建、通配/限定/冲突拒绝的错误文案（对应 B2-1 验收 1/2）。
- [ ] 新增逐请求对拍：hover / goto / references / rename / completion / inlay
      **含 `t_span`+`def_span` 比对**（不只渲染串），覆盖 `examples/**`。
- [ ] 新增 codeAction/quickfix 对拍（B2-5）。
- [ ] 把"8 套 LSP 守卫在 twin 模式下全绿"（[文档] `lsp-twin-wiring:924-927`）从**手工口径**
      变成门禁件（显式 `Engine::Twin` 或 `TYPORT_LSP_ENGINE=twin` 跑同一批用例）。
- [ ] `tests/l13_fast_parity.rs`、`tests/l13_into_probe.rs`、`src/L13_namespace/*_tests.rs`、
      `observe.rs` 的 oracle 调用全部可由 oracle feature/`cfg(test)` 提供；默认 feature 下
      生产 target 不编译参考 elaborator（B2-9）。
- [ ] 文档化偏差清单（`?N`、span 数字、零 span、参考版 start=0 畸变、字段投影）随对拍更新，
      并注明"每一条都是主动放行，不是未发现"。

### B. 门禁

- [ ] `tools/gate_l13.sh` 增第 5 件：engine parity（全语料 0 未解释回落 + 逐请求对拍）。
- [ ] 门禁含 `--release` 一次（twin 的语义 bug 在 debug 下不一定复现）。
- [ ] 生产默认翻转前，"twin 唯一引擎"门禁先跑满一个窗口（≥1 周或 ≥1 release，二选一写死）。
- [ ] 6 个已知开关的矩阵至少跑一次：`TYPORT_TWIN_NO_COMPACT`、`TYPORT_TWIN_NO_USER_OBSERVE`、
      `TYPORT_TWIN_KICK_CLEAR_MEMO`、`TYPORT_TWIN_BUMP_BUDGET_MB`、
      `TYPORT_LSP_ENGINE=reference|twin|错拼`（最后一项验"错拼安全落 twin"）。

### C. Soak / 对拍

- [ ] 真实编辑序列 soak：≥200 次击键编辑（`examples/adder_proof.typort` +
      `examples/hdl/09-hierarchy.typort`）+ didClose/reopen + 252KB 大文件 didOpen
      （复盘 `lsp-twin-wiring:1402-1426` 的现场），全程无卡顿尖峰、诊断收敛。
- [ ] 多文件工程 soak：≥10 文件、有 `package`/`import` 依赖链，编辑 provider / 关闭 provider /
      重新打开，dependent 诊断与 goto 正确。
- [ ] 离线双跑窗口 ≥1 个 release 周期：twin 与 reference 对同一编辑序列出结果并 diff
      （不双付线上成本，只在 CI/夜里跑）。
- [ ] 崩溃可见化演练：人为把 wasm `--max-memory` 压到 512MiB 复现 trap，确认状态栏/看门狗
      能报警并可一键重启（[文档] `lsp-twin-wiring:1301-1318`）。
- [ ] native 长时内存曲线 ≥2h 编辑无单调增长；wasm 同样。

### D. 内存阈值

- [ ] native：稳态 ≤ **429MB**、峰值 ≤ **730MB**（当前基线），且"每 kick 中间分配" ≤ A 稿给出的目标。
- [ ] wasm：单文件峰值 + 会话增量 ≤ **1.5GiB**（2GiB 硬顶留 ≥25% 余量）；
      当前 `adder_proof` 1.18GB ⇒ 会话化后必须重测。
- [ ] 阈值写成断言/探针（不是文档承诺）：`resident_memory_growth_per_kick` 与
      `twin_mem_stats`（`force.rs:385`）接入门禁。
- [ ] 内存回归熔断：超阈值时门禁失败而不是仅打印。

### E. 回滚开关保留策略

- [ ] `TYPORT_LSP_ENGINE` 保留到 R6（删参考版生产代码）之后**至少一个 release**；
      删除前完成 §C 的 soak。
- [ ] 状态栏引擎选择（`serverActions.ts:100-110`）在 web 默认未翻 twin 前保持可见；
      翻转后仍保留 `reference` 逃生口直到 R6。
- [ ] `twin_gate_distrusted` 粘性早退管道（`src/lib.rs:2306-2312`）**永久保留**：
      HDL 警告漏报是运行期无法自证的风险，这是唯一重新开启点。
- [ ] `twin_fallback` 日志/`twin_fallback_reason`（`:380`、`:1370-1388`）：R6 后无"回落"概念，
      但建议保留一个版本的诊断日志（class=`own`）用于现场取证。
- [ ] web 默认从 `reference` 翻 `twin` 的判定写死为"单文件峰值 + 会话增量 ≤ 预算"，
      而不是"平均更省"（[文档] 主稿 §5.1 面 3）。

### F. 代码删除边界与固化（β）

- [ ] 参考版**分解**完成：域类型/渲染/typeclass 类型留生产面，elaborator 本体 feature 门控（B2-9）。
- [ ] 生产二进制符号核对：`elaboration-zoo-lsp`、`typort` 中无 `Infer::infer`、
      `unify`、`solve_multi_trait`、`pattern_match::Compiler` 符号。
- [ ] `L13_namespace::run` / `run_with_prelude` 只出现在测试/bench 编译面。
- [ ] `src/doc/collect.rs:75` 的 `Engine::Reference` 硬钉移除（或明确标注为 oracle 用途）。
- [ ] `typort check` 单管线（B2-8），`examples/**` 输出与改前逐字节一致。
- [ ] `package.json:110` 与 `serverActions.ts:35` 的默认引擎文案一致。

---

## B5 排序与去风险（阶段路线；★＝必须先实验取数才能定价）

| 阶段 | 目标 | 交付物 | 退出判据 | 粗估 | 不可逆性 |
|---|---|---|---|---|---|
| **P0 判据先行** ★ | 让"取代了多少、差在哪"可机器测量 | `tools/engine_parity.sh` + 全语料/全请求对拍报告（B4-A 全部） | 复现 29/30、18-utils、1.78×；cross-file 暴露面与 quickfix 缺口被量出来 | 0.5–1 | 无（纯新增） |
| **P1 视野 L1** ★ | 闸① 放宽到"视野本就完整/本就解析不了" | `twin_can_own` 加两个谓词 + 用例 | import 文件在"provider 不在打开集"时由 twin 拥有，且两版错误文案逐字节 | 0.5–1 | 无（有 env 回滚） |
| **P2 会话化 L2** ★★ | 依赖文件喂进常驻 twin（A2 主体） | `observe_segments` + 逐段失效 + 观察面按 path_id 过滤 | `tests/cross_file_tests.rs`/`namespace_tests.rs` 在 twin 下全绿；`symbol-defined-in-another-file` 归零 | 5–10 | **中**：数据面开始依赖会话；回退需重跑参考路径（代码仍在） |
| **P3 导出面 A3 + binder span** | 用户可见功能面 parity | `ExportedNamespace` + `cxt.namespace` 合并；字段槽 span | 字段投影降级测试反转；两文件 `x.method` 双引擎逐字节 | 3–8（A3 2–4 + span 1–2 窄修） | 低 |
| **P4 信任闸** ★ | 全语料 0 `untrusted-error` | 18-utils 分叉根因修复 + 分类器退化 | `EXPECTED_FALLBACKS` 清空；错误语料扩到历史全类 | 3–5 | **高**：撤闸后运行期无自证（建议保留 debug assert + 语料持续扩） |
| **P5 入口统一** | 闸⑤⑥：CLI 单管线 + 测试面显式引擎 | `check`→`process_file`；`doc` 去硬钉；测试显式声明引擎 | `typort check` 全语料逐字节；门禁在新默认下全绿 | 2–4 | 中（CLI 语义面） |
| **P6 资源收口** ★ | 闸④：内存预算 | 每 kick 分配下降 + 会话段预算 + wasm 真机验证 | native/ wasm 阈值达标且熔断生效 | 5–10 | 低（可回滚） |
| **P7 固化 β** | 参考引擎退出生产二进制 | feature 门控 + 符号核对 + 删除 env/状态栏逃生口 | 生产无参考 elaborator 符号；soak 一个 release | 2–3 | **不可逆（最高）**：删 env 后现场回滚能力归零 |

**必须先实验取数的步骤（定价前不可开工）**

1. **P0 的 cross-file 暴露面**：`examples/**`/`tests/*.typort` 零 import（[实测]）⇒ 需要
   先造多文件语料并量"两引擎在 import 场景下的诊断 diff 面"，否则 L1/L2 的验收标准无从写。
2. **P0 的实例/`mutable` 跨文件可见性**（[不确定①]/[不确定②]）：两文件实验
   （A 声明实例/inherent impl，B import 后使用）分别跑参考版与 twin，判定
   `self.infer` 不回写是否真的使实例不跨文件 ⇒ 决定 A3 的实例半边做不做（0–3 人天差）。
3. **P2 的逐段失效成本** ★★：`bump` 无截断、`compact_state` 全量深拷 ~120ms
   （[文档] `lsp-twin-wiring:951-966`）⇒ 需要实验回答"10 文件工程的每 kick 重放成本 vs
   参考版 280ms 单文件成本"，这决定 P2 是全量重放还是需要段检查点（工作量 5 vs 10 人天）。
4. **P4 的 18-utils 分叉**：先做隐参插入计数对照（`TYPORT_DECL_PROBE` + `FUNC_PROF`），
   量出差异点数量级再定 3 人天还是 5+ 人天。
5. **P6 的 wasm 会话增量**：当前 1.18GB 是"单文件"口径，会话化后需要真 Chrome 实测
   （`performance.measureUserAgentSpecificMemory()`，[文档] `lsp-twin-wiring:1283-1299`）
   才能定阈值；没有这个数就不能翻 web 默认。

**不可逆点**

1. **P2 之后**：会话数据面成为唯一跨文件路径，回退到"永远走参考版"需要在现场重跑参考路径
   （代码在，但用户的编辑会话已按会话语义建立）⇒ 建议 P2 期间保留"twin 会话失败即回落参考版"
   的兜底（今天已有 `cross-file` 回落，改成"会话构建失败回落"）。
2. **P4 之后**：撤信任闸＝失去"错的诊断"的运行期防线 ⇒ 只能靠语料/soak 自证，
   必须在 P0 的判据扩容之后做。
3. **P7（最高）**：删 `TYPORT_LSP_ENGINE`/状态栏逃生口后，线上唯一回滚手段是回退版本
   ⇒ 必须在 P7 前完成一个完整 release 周期的 soak + 现场遥测（引擎/回落/内存）。

---

## 附录 A：与主稿 §5.2 的差异（供合并时取舍）

| 议题 | 主稿 | 本稿 | 依据 |
|---|---|---|---|
| β 的形态 | "参考引擎降级为 `#[cfg(test)]` 判据" | 认同，但**删除边界 ≠ 文件边界**：域类型/渲染/typeclass 必须留生产面（B2-9） | `src/lib.rs` 的 26 处 `L13_namespace::*` 引用 + `bump_spine_iter.rs:218` 复用参考 `typeclass::Instance` |
| γ | "不建议" | 从"不建议"升级为**不可行** | twin 单测直接调参考 `Infer` 当 oracle（`observe.rs:297-333`） |
| A3 的优先级 | "优先级低于 A2" | 认同；但**实例半边**的跨文件暴露面可能为零（[不确定①]），需实验后重估 | `src/lib.rs:2524` 全局 `Infer` 不回写 |
| quickfix/codeAction | 未列 | 新增 B2-5：**已发生的用户可见功能退化**，1–2 人天 | `src/lib.rs:1659` vs `:2573-2584`；测试侧零覆盖 |
| 观察面缺口 | 字段投影 def_span | 认同，并给出**窄修 (a) 1–2 人天**先行的路径 + 明确的改动点清单 | `syntax.rs:230-243`、`machine.rs:3130-3158` |

## 附录 B：存疑与需要实验的条目（不允许含糊，逐条给判据）

| # | 存疑点 | 判据（做完即定论） |
|---|---|---|
| ① | 参考版是否跨文件共享 trait 实例 | 两文件 fixture，B 用 A 的实例；参考版若报 `solve trait failed` ⇒ 不共享 |
| ② | 多文件 `emit` 在 twin 下是否等价（`mutable`/ModuleRegistry 跨文件） | `typort emit` 双引擎对 2–3 文件工程（子模块分文件）输出逐字节 |
| ③ | P2 逐段失效成本 | 10 文件工程、编辑最后一个文件，量 twin "会话重放" vs 参考版整 kick 墙钟 |
| ④ | wasm 会话化后的峰值 | 真 Chrome + 多文件工程 + 30 分钟编辑，读整页内存 |
| ⑤ | `resident-unavailable` 是否真不可达 | 静态：闭包内所有 `return false` 都赋值 `decline`（`:1455`/`:1474`）；动态：跑 `twin_engine_tests` + 人工构造 prelude 形态切换，观察日志 |
| ⑥ | 字段投影窄修 (a) 是否会使 `XCell` 尺寸/对齐越界 | 编译期对齐断言（`env.rs:142-147`）+ `compact` 深拷回归 + `l13_into_probe` v7 探针 |

---

### 复现本稿结论的只读命令（不含 cargo）

```powershell
# 路由点（应只有 5 处显式 Reference）
Select-String -Path src/lib.rs,src/bin/cli.rs,src/doc/collect.rs -Pattern 'Engine::Reference|from_env|lsp_default'
# 语料从不触发 cross-file（应为空）
Get-ChildItem examples,tests -Recurse -Filter *.typort | Select-String -Pattern '^\s*(import|package)\s'
# 测试默认引擎（应全部是 Backend::new）
Select-String -Path tests/*.rs -Pattern 'TYPORT_LSP_ENGINE|new_with_engine'
# quickfix 面测试覆盖（测试侧应几乎为空）
Get-ChildItem tests -Filter *.rs | Select-String -Pattern 'quickfix|applyQuickFix|code_action'
```
