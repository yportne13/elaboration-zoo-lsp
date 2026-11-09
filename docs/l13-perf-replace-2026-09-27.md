# L13 性能分析与「性能版完全取代参考版」方案（2026-09-27）

> 本轮为**并行分析任务**：主线正在做 HDL 特性交付（682 未提交改动：`src/L13_namespace/mod.rs`、
> `legacy_tests.rs`、`src/prelude/hdl/*.typort`、`src/L13_namespace/hdl_*_tests.rs`、
> `docs/hdl-*.md`），本任务全程**零打扰**：不写 `target/`、不改任何被跟踪文件、
> 不运行会锁 `target/release/*.exe` 的进程；实测一律用隔离 `CARGO_TARGET_DIR=target_l13perf`
> 与复制出来的二进制副本。方法学与边界见 §6。
>
> 证据分层：**[实测]** = 本轮独立跑出来的数字（附二进制指纹与命令行）；
> **[文档]** = 引自仓库既有文档/提交（附坐标）；**[推断]** = 无直接数据、由代码/结构推出的结论。

---

## 0. 一页纸结论

（A/B 两份分稿已并入本文；C 稿未产出，独立实测暂缺——见 §4。）

---

## 1. 事实基线：两个引擎今天各自站在哪（Lead 亲自核对）

### 1.1 两个引擎是什么

| | 参考版（Reference） | 性能版 / 孪生（Twin） |
|---|---|---|
| 代码 | `src/L13_namespace/{elaboration,cxt,unification,pattern_match,typeclass}.rs` | `src/L13_namespace/bump_spine_iter/{machine,force,eval,entry,compiler,unify,quote,observe,prim,compact}.rs` |
| 表示 | `Rc` 共享 + COW（`Rc::make_mut`） | bump arena + 显式 spine/机器 |
| 主要用途 | 正确性基准、跨文件数据面、CLI `check`、wasm 宿主默认、绝大多数测试 | LSP 默认引擎（单文件）、bench `fast` 列、`typort emit` |
| bench 列名 | `basic` | `fast` |

### 1.2 谁在什么时候被选中（代码坐标，已逐条核对）

1. **LSP 服务器默认走 twin**：`Engine::lsp_default()`，`src/lib.rs:255-260` —— 只有
   `TYPORT_LSP_ENGINE=reference`（大小写不敏感）才回参考版；任何其它值（含拼错）都选 twin。
2. **通用构造 `Backend::new` 默认参考版**：`Engine::from_env()`，`src/lib.rs:276-281` ——
   只有恰好 `twin` 才选 twin。CLI 与 `cargo test` 走这条 ⇒ **测试套件的默认引擎仍是参考版**。
3. **`typort check` 是纯参考版管线**：`src/bin/cli.rs:684-707` 显式
   `Backend::new_with_engine(cli_client, Engine::Reference)` 并调用 `on_change`；
   注释说明原因：`on_change` 里没有 twin 分派，开了只会白付一次常驻 prime（+1.8~2.0 s）。
4. **`typort emit` 走 `process_file`** ⇒ 支持 twin（`Engine::from_env` 口径）。
5. **wasm / web 宿主默认参考版**：`vscode_extension/client/src/serverActions.ts:26-37`
   （`UNSET_ENGINE = { wasm: 'reference', cli: 'twin' }`），原因是 wasm 线性内存硬顶
   2 GiB（SharedArrayBuffer 上限）下 twin 常驻对一个大证明文件要 ~1.2 GB，而参考版
   ~0.33 GB；客人无法增长内存时会以 `RuntimeError: unreachable` 崩掉且客户端看不见。

### 1.3 文件级归属与运行期回落（这是「取代」的主战场）

**归属闸**：`Backend::twin_can_own`，`src/lib.rs:1398-1402` —— 仅当
`engine == Twin` **且** 该文件无 `import`（`file_deps`）**且** 未声明 `package`
（`file_namespaces`）时才由 twin 拥有。否则 `elaborate_with`（`src/lib.rs:2280-2305`）
以 `class = "cross-file"` 回落参考版。

**运行期 decline 类别全集**（`note_twin_fallback`，`src/lib.rs:1370-1381`）：

| class | 位置 | 触发条件 | 2026-09-27 状态 |
|---|---|---|---|
| `cross-file` | `lib.rs:2301` | 有 import / package | 在用（主阻塞） |
| `no-document-id` | `lib.rs:2316` | 防御分支，`process_file` 未种 id | 理论上不可达 |
| `no-parse-result` | `lib.rs:2331` | `parser_with_macros` 返回 `None`（resilient lexer 下不可达） | 理论上不可达 |
| `prelude-unavailable` | `lib.rs:1440` | 常驻 prelude 未装载 | 在用（启动竞态） |
| `resident-unavailable` | `lib.rs:1447` | TLS 常驻被弃用后重建失败 | 在用 |
| `prelude-prime-failed` | `lib.rs:1455` | `prime_resident` 失败 | 在用 |
| `observe-failed` | `lib.rs:1474` | `observe_user` 返回 `Err` | 在用 |
| `untrusted-error` | `lib.rs:1559` | 诊断类别不在信任名单：`can't unify…` 与「确实未定义的名字」之外的一切（trait 求解失败、歧义名、universe…） | 在用（`18-utils` 是语料内唯一触发者） |
| `symbol-defined-in-another-file` | `lib.rs:1557` | 未定义名在参考版全局表里由**别的文件**定义 ⇒ 视图不足 | 在用（跨文件缺口的直接后果） |
| `hdl-check-gate` / sticky | `lib.rs:1564-1609`、`2306-2312` | HDL 自检闸 **2026-09-23 已撤除**，`twin_gate_distrusted` 管道与粘性早退保留作重新开启点，当前无人置位 | 已停用（残余风险见 §3） |

**信任闸的判据**（`src/lib.rs:1504-1562`）：twin 可以拥有**错误态**，但只限
(a) `parse_errs`（两引擎同一次 `parser_with_macros`，逐字节相同）；
(b) 前缀 `can't unify`；(c) `error name not in scope: X` 且 X 不在参考版全局 decl 表里。
其余一律回落 —— 理由是「错的诊断比慢的诊断更糟」。

**这两张表是被测试钉住的**（改动时必须同步，否则门禁变红）：
类别全集由 `twin_fallback_classes_are_exactly_the_known_set`（`tests/twin_engine_tests.rs:936-990`）
钉住——新增一个 `note_twin_fallback` 调用点必须显式改那份 `KNOWN` 列表；
语料级归属由 `EXPECTED_FALLBACKS`（`:797-798`）钉住，当前**只有**
`examples/hdl/18-utils.typort: untrusted-error` 一条，且该套件断言
「语料上出现的类别恰好是 `["untrusted-error"]`」——**这就是「取代进度」的现成仪表盘**：
R1/R2 完成的判据之一就是把这两处收缩到空。

### 1.4 观察面与跨文件数据面的既有缺口（文档已钉住）

- **字段投影 def_span 降级**：twin 的项/值表示不携带 binder span（`Tm::Pi(&str, …)`、
  `SumDataV { name: &str, … }` vs 参考版 `Span<SmolStr>`），于是 `p.x` 的 `def_span`
  退化成使用处 token；用户可见后果是 F12 落在 `p.x` 不动、字段声明处的
  references/rename 看不到使用处。修它要贯穿整个 machine 表示。**[文档]**
  `docs/lsp-twin-wiring-2026-09.md:1505-1510`（测试
  `twin_field_projection_def_span_is_known_degraded` 钉住）。
- **A3：twin 不向参考域导出 `cxt.namespace`**（trait 实例、inherent impl 条目），
  `twin_elaborate` 只合并 `cxt.decl` / `type_map`。跨文件两端目前都是参考版，
  所以暴露面窄；一旦 A2（把依赖文件喂进常驻 twin）落地，A3 会立刻变成硬缺口。
  **[文档]** `docs/lsp-twin-wiring-2026-09.md:1515-1522`。
- **内存**：native 常驻 twin ~429 MB 稳态 / ~730 MB 峰值 vs 参考版 ~200 MB
  （~2.2× 的 CPU 换内存，压实落地前是 ~9× / 1.8 GB）；wasm 下大证明文件 ~1.2 GB vs ~0.33 GB。
  **[文档]** `src/lib.rs:232-236`、`serverActions.ts:27-34`。

### 1.5 语料级现状（截至文档最新记录）

- `examples/`（30 个文件）中 **29 个由 twin 接管**，唯一回落是 `18-utils`
  （`untrusted-error`）。**[文档]** `docs/lsp-twin-wiring-2026-09.md:1745-1751`。
- 同一份文档口径下，已实现成本从「几乎无收益」（18,461 ms/kick，0.93×）转为
  **11,281 ms/kick（0.57×）**，HDL 主力文件 2.7–4.1×；总比 **1.64×**，
  在 `adder_proof` 根因修复后为 **1.78×**。**[文档]** 同上 `:1530-1536`、`:1648-1649`。

---

## 2. 性能：现状与剩余空间

（合并 A 稿 `docs/wip/l13-perf-replace-2026-09-27/A-perf.md`）

---

## 3. 「完全取代参考版」的阻塞项

（合并 B 稿 `docs/wip/l13-perf-replace-2026-09-27/B-replace.md`）

---

## 4. 独立实测

（C 稿 `C-measure.md` 未产出，本节暂缺独立实测内容。）

---

## 5. 路线图（Lead 设计）

### 5.0 先把「完全取代」拆成三个不同的目标

混在一起谈会得出一堆互相矛盾的结论。它们是：

| 目标 | 含义 | 价值 | 现实性 |
|---|---|---|---|
| **α 生产路径取代** | LSP（桌面 + web）与 CLI 全部由 twin 服务，正常输入下**零回落** | 直接用户可见（延迟、内存换 CPU 的账要重算） | 可达，是本文主目标 |
| **β 代码删除** | 参考版源码可以从生产 crate 里删掉 | 维护面减半、编译时间下降 | 可达但代价高：4560 项测试拿它当**唯一独立判据** |
| **γ 判据退休** | 连测试里也不再保留参考版 | —— | **不建议**：删掉独立判据后，twin 的任何语义漂移都无从发现 |

**建议的终态**：α 做满；β 用 `#[cfg(test)]` / feature gate 把参考引擎降级为**测试专用判据**
（生产二进制里不存在，但 `cargo test` 还能对拍）；γ 永久不做。这也回答了「完全取代」到底要到哪一步——
用户可见面完全取代，判据面保留。

### 5.1 取代地图：四个面、六道闸

```
                          ┌─ 面 1 归属：谁能拥有这个文件 ──────────────┐
   twin_can_own           │ 闸 ① 无 import / 无 package（lib.rs:1398）  │
                          └────────────────────────────────────────────┘
                          ┌─ 面 2 信任：twin 的诊断敢不敢发 ───────────┐
   trust gate             │ 闸 ② untrusted-error /                  │
   （lib.rs:1504-1562）    │     symbol-defined-in-another-file        │
                          │ 闸 ③ HDH 自检闸（已撤，管道保留）          │
                          └────────────────────────────────────────────┘
                          ┌─ 面 3 资源：宿主能不能装下 ────────────────┐
   memory                 │ 闸 ④ native ~730MB 峰 / wasm 1.2GB vs 2GiB │
                          └────────────────────────────────────────────┘
                          ┌─ 面 4 入口：谁在构造 Backend ──────────────┐
   Engine::*              │ 闸 ⑤ typort check 的 on_change 参考专线    │
                          │ 闸 ⑥ Backend::new 默认 Reference（测试面） │
                          └────────────────────────────────────────────┘
```

**面 1 的阶梯（这是收益最大的一块，且比看上去便宜）**

关键事实（Lead 已核对）：twin **本身已经实现 import/package 语义**——
`package` 前缀（`machine.rs:4341`）、`import` 别名表（`machine.rs:4351-4448`）、
限定路径三试（`machine.rs:2989-3008`）、namespace 方法分派（`machine.rs:3985-4014`）。
面 1 的闸不是「语言不支持」，而是**会话视野只有 prelude + 当前文件**
（`lib.rs:230`、`entry.rs` 的 `observe_user(prelude, decls)`）。

同时，参考版路径**已经算好了跨文件重放序**：`process_file`（`lib.rs:2634`）
调 `rebuild_set`（`lib.rs:2233`，`update_deps`/`ns_providers`/`ns_dependents`/
`visit_dep` 拓扑排序）得到「改动文件 + 传递依赖者，依赖在前」，再逐个
`elaborate_with`。⇒ 跨文件取代 = **把这个已经算好的序列喂进常驻 twin 会话**，
不是重写名字解析。据此分三级：

- **L1（廉价档，¥0.5–1 人天）**：把闸从「无 import」放宽到「import 的每个 namespace 的
  provider 里**没有**当前打开的文件」（即视野在 prelude 内完整，或该 import 本就解析不了——
  两版应报同样的 `cannot import 'x': no such namespace in scope`，`machine.rs:4381`）。
  对 `package` 文件另需一条：若**没有**别的打开文件 import 它，才可拥有本文件——
  因为它的 namespace 条目要向参考域导出（A3），否则依赖者（仍在参考版）会丢成员。
- **L2（主体，¥5–10 人天）**：常驻 twin 升级为**项目会话**——按 `rebuild_set` 的拓扑序
  把依赖文件先重放进会话（每个文件一段），最后放当前文件；文件关闭/改动时按段失效重放。
  这是「闸 ① 完全拆掉」的正解，同时消掉 `symbol-defined-in-another-file`。
  风险点：每段要能独立失效（现在只有「会话级全局复位」+ prelude 后缀缓存）、
  观察面表按 `path_id` 分文件过滤、跨文件段的重放成本（可能需要 L1 的增量复用）。
- **L3（收尾，¥1–2 人天）**：删掉 `twin_can_own` 的 `file_deps`/`file_namespaces` 判据，
  只留引擎判据；`EXPECTED_FALLBACKS` 里 `cross-file` 相关行归零。

**面 2 的收口顺序（不能先做）**

trust gate 是「宁可慢也不要错」的最后一道保险，**只有在语料上量到回落类别为 0 才能撤**。
现在语料内唯一触发者是 `18-utils`（`untrusted-error`，trait 求解分叉：twin 对用户 decl
多约 246 次隐参插入 → 多注册 trait meta → `LetNamed` 递归求解失败）。
⇒ 顺序必须是：**先把判据可测（R0 对拍报告）→ 修 18-utils 类分叉 → 全语料 0 回落 → 再撤闸**。
撤闸后双跑消除还有**性能红利**：任何晚回落（`untrusted-error`/`observe-failed`）都是
「twin 跑一遍 + 参考版再跑一遍」的双付，`18-utils` 的 0.74× 正是这个形状。

**面 3 的两个预算**

- native：稳态 ~429MB / 峰 ~730MB，对桌面可接受；真问题是「每 kick 中间分配 ~850MB」
  （摊平链 3 遍 + spine 链）。
- wasm：2 GiB 硬顶（SharedArrayBuffer 上限），twin 对一个 proof 级文件 ~1.2GB ⇒ 剩下的余量
  不足以再装会话/依赖段，且超限是 `RuntimeError: unreachable` **静默崩**。
  ⇒ web 默认翻 twin 的前置条件不是「平均更省」，而是**单文件峰值 + 会话增量 ≤ 预算**，
  并且要有「内存天花板探针 + 崩溃可见化」（`typort-hdl/ping` 看门狗已有）。

**面 4 是纯接线，最便宜**

- 闸 ⑤：`typort check` 的 `on_change` 参考专线（`cli.rs:684-707`）。要么给 `on_change`
  加 twin 分派，要么把 `check` 切到 `process_file` 口径（后者还能顺手统一
  「check 的跨文件语义」）。¥1–2 人天，但**动的是 CLI 语义面**，要用
  `typort check` 对 `examples/` + `tests/*.typort` 做逐字节对拍。
- 闸 ⑥：`Backend::new` 默认（`Engine::from_env`，`lib.rs:276-281`）。改默认为 twin 之前，
  4560 项测试里凡是依赖参考版行为的都会变红——**这一步不是改一行，是测试面改造**，
  见 §5.3。

### 5.2 阶段划分（含退出判据）

| 阶段 | 目标 | 交付物 | 退出判据（必须全部绿） | 粗估 |
|---|---|---|---|---|
| **R0 判据先行** | 让「取代了多少、差在哪」可机器测量 | 一个可复跑的引擎对拍报告：全语料（examples + tests 语料 + 各 level fixture）逐文件输出 `归属引擎 / fallback class / ERROR+WARNING+INFORMATION 是否逐字节一致 / kick 墙钟 / RSS 峰` | 报告能复现文档已知结论（29/30 拥有、18-utils 回落、examples 1.78×）⇒ 判据可信 | 0.5–1 |
| **R1 视野** | 闸 ① 拆掉（L1→L3） | 项目会话 + 逐段失效 + 观察面分文件 | 多文件语料（`tests/cross_file_tests.rs`、`namespace_tests.rs`、`tests/*.typort`）0 回落且诊断 parity；`EXPECTED_FALLBACKS` 只剩 18-utils | 6–13 |
| **R2 信任** | 闸 ② 拆掉 | 18-utils 分叉根因修复（隐参插入计数对照）+ 全语料 0 untrusted | 全语料 0 `untrusted-error`；分类器退化为恒信任（保留 debug assert） | 3–5 |
| **R3 观察面** | 用户可见功能面 parity | binder span 进 twin 表示（字段投影 def_span）、A3（导出 `cxt.namespace`/实例）、跨文件 references/rename | 每个 LSP 请求在语料上 twin vs 参考版逐条对拍；`twin_field_projection_def_span_is_known_degraded` 转正 | 4–8 |
| **R4 资源** | 闸 ④ 拆掉 | 峰值预算收口（每 kick 中间分配、会话段内存）+ 内存探针/崩溃可见化 | native 峰 ≤ 约定值；wasm 大证明文件 ≤ 约定值且无 trap；`resident_memory_growth_per_kick` 重测通过 | 5–10 |
| **R5 入口** | 闸 ⑤⑥ 拆掉 | CLI 单管线；`Backend::new` 默认 twin；`typort check` 逐字节对拍 | examples 全量 `typort check` 输出与改前逐字节一致；测试套件在新默认下全绿 | 2–4 |
| **R6 固化** | β 目标 | 参考引擎降级为 `#[cfg(test)]` 判据；删 `TYPORT_LSP_ENGINE` / 状态栏引擎选择 / `twin_fallback` 管道 | 生产二进制不再含参考引擎符号；门禁全绿；一次 release 周期 soak 无对拍漂移 | 2–3 |

**总粗估 22–44 人天**，其中「单文件桌面 LSP 完全取代」（R0+R2+R3 的桌面部分）约
**8–14 人天**，是收益/成本最好的一段；跨文件（R1）与 wasm（R4）是两个大件。
这些数字是 Lead 的粗估，**待 D 稿对抗式复核**（尤其 R1/R4）。

### 5.3 不可逆点与顺序约束（做错的代价）

1. **R0 必须先做**：后面的每一步都以「可机器判定的 parity」为前提；没有 R0，
   R2/R5 的「全绿」只是自己宣布的。
2. **R1 早于 R3 的跨文件部分**：跨文件 references/rename 需要 twin 手里有依赖文件。
3. **R4 早于 web 默认翻转**：内存不可控时翻默认 = 静默崩。
4. **R5 的测试面改造是最险的一步**：`Backend::new` 默认翻 twin 会同时动
   L02–L12 黑盒测试与 parity 套件的基准。建议**不要**直接翻默认，而是
   「测试显式声明引擎」+ 新增「twin 默认下全绿」的独立门禁，跑满一个窗口再翻。
5. **R6 不可逆**：删 `TYPORT_LSP_ENGINE` 后现场回滚能力归零 ⇒ 必须在 R6 前完成
   至少一个 release 周期的 soak（真实编辑序列，不只是语料）。
6. **一直保留的**：`twin_gate_distrusted` 粘性早退管道（现在就留着），
   作为 HDL 警告漏报这类「运行期无法自证」风险的重新开启点。

---

## 6. 方法学与「不干扰主线」的边界

- 本任务全程**不修改任何被 git 跟踪的文件**；新增文件仅：
  `docs/l13-perf-replace-2026-09-27.md`（本文件）与
  `docs/wip/l13-perf-replace-2026-09-27/{A-perf,B-replace}.md`
  （C-measure/D-verify 分稿未产出）。
- 构建/实测一律隔离：`CARGO_TARGET_DIR=target_l13perf`（已被 `.gitignore` 的 `target_*/` 覆盖）；
  运行任何既有二进制前先复制出 `target/release`，避免 Windows 文件锁挡住主线重建。
- 主线正在改的文件（`src/L13_namespace/mod.rs`、`legacy_tests.rs`、`src/prelude/hdl/*.typort`、
  `docs/hdl-*.md`、`src/L13_namespace/hdl_*_tests.rs`）只读不写。
- 已知偏差：`target/release/*.exe` 构建于 2026-09-26 19:47–19:56（≈ `804c4dd`），
  之后主线提交了 HDL 特性与文档（`d416c3c`/`3a08b88`/`ede8773`/`5d710ea`/`52ba09b`），
  twin 内核未动但 HDL prelude 有变 ⇒ 二进制口径与源码 HEAD 存在偏差，实测结论均已标注。
