# A6 交叉审计 R2 — 对象：A7（`src/lib.rs` / LSP 协议层 / CLI-doc-format）

> 轮转规则：BRIEF §5（A6 审计 A7）。**只读**审计，未改动 A7 的任何文件。
> 输入：`docs/review-l13/a7-r1.md`（含 Lead 追加的 F2）、`docs/review-l13/LEAD-probes.md` F2、
> A7 本轮工作树 diff（`src/lib.rs`、`src/client.rs`、`src/bin/l13bench.rs`）。
> 本 agent 不运行 cargo（BRIEF §6.2）：结论均为静态阅读 + 依赖源码核对；改由 Lead 验证处已标注。

## 1. 结论（verdict）

- **P0: 0  P1: 0  P2: 0  P3: 3  needs-verify: 2**
- 本轮 A7 的三处改动（`drop(backend)` ×2 + panic→Err、值输出面闸、CLI UTF-16）**我全部独立复核为方向正确、
  实现与注释一致**（§3 确认清单 9 条，逐条给依据）；没有发现新的 P0/P1/P2。
- 3 条 P3 集中在**同一族**：**位置口径的边界一致性**（CRLF 终止符）、**回落类别表的漂移**、
  **修复缺少回归测试**；2 条 needs-verify 是"无错态的值分歧敞口"与"值输出面闸的性能量化"。
- 与 A7 自评的差异：A7 §2[P2] 说两个转换函数"两处口径一致"，我认为**只在 BMP/ASCII 上一致**；
  CRLF 下 `offset_to_position` 会把 `\r` 计入列（C1），这是我这轮交叉审计的独立发现。

## 2. 发现列表

### [P3 · C1] `offset_to_position` 把 CRLF 的 `\r` 计入 column，与 `position_to_offset` 的 clamp 口径差 1

- 位置：`src/lib.rs:3856-3871`（计数循环 `:3863-3869`）；对照 `:3873-3898`（`position_to_offset`）、
  `tests/test_rope_offset.rs:187-197`（CRLF 正向用例）。
- 证据（确定性静态推演，`rope.line()` 含行终止符是 ropey 的既定语义）：
  - `rope = "ab\r\n"`，`offset_to_position(3)`（3 = `\n` 的字节，`try_byte_to_line(3)` 归第 0 行）：
    循环依次 `'a'`(col 1)、`'b'`(col 2)、`'\r'`(col 3，因为 `line_byte_start+2 >= 3` 为假)，
    到 `'\n'` 才因 `line_byte_start+3 >= 3` 而 break ⇒ **column = 3，而行内容只有 "ab"（2 UTF-16 单元）**。
  - 反向：`position_to_offset(Position::new(0, 3))` 会把 `character` clamp 到 `content_utf16 = 2`
    ⇒ 返回 2（= `\r` 的字节）。**往返 3 → 2 不闭合**。
  - `tests/test_rope_offset.rs:191-193` 恰好把 `position_to_offset(0, 2/3/99) == 2` 钉住（clamp 到 `\r` 之前），
    而同一文件的 `test_roundtrip_conversion`（`:91-129`）把"position→offset→position"当不变量——
    只是它的语料（`:92-99`）没有 `\r`，所以两者从未在 CRLF + 终止符边界上相遇。
- 机制/影响：**任何 span 边界落在换行符上的诊断**在 CRLF 文档里都会发布 `character = 行内容 + 1`。
  最典型的可达来源正是本仓最近的改动：350b35a 的 found 追踪把错误锚在 **EndLine token** 上
  （例如 `expected \`=\`, found newline` 的 span 就是那个 `\n`；`ws()` 已提前吃掉 `\r`，
  所以 EndLine token 的 `start_offset` 正是 `\n` 的字节）。影响面：
  (a) 发布的 range 违反"character ≤ 行长"的 LSP 契约（VS Code 会 clamp，视觉上仍在行尾）；
  (b) 与 `position_to_offset` 的口径不一致 ⇒ 任何"把服务端 position 原样回传"的路径
      （如按 pos 反算字节、或客户端不 clamp）会落到 `\r` 上；
  (c) `format` 的 `TextEdit` 端点若恰好落在这个字节（`lib.rs:3192-3193`）也会差一个字节
      （`edit.end_byte` 停在 `\r` 与 `\n` 之间时会保留 `\r`）。
- 处置：**仅报告**（A7 的文件）。建议的最小修法（与 `position_to_offset` 的 `content_utf16` 对齐）：
  ```rust
  let mut chars = line_text.chars().peekable();
  for ch in chars {                       // 3863 起的循环
      if line_byte_start + byte_i >= offset { break; }
      if ch == '\r' && chars.peek() == Some(&'\n') { break; }   // 新增：终止符不计入列
      column += ch.len_utf16() as u32;
      byte_i += ch.len_utf8();
  }
  ```
  对 offset 落在 `\r` 自身的情形，`>= offset` 先 break，行为不变；只改变"offset 越过 `\r`"的 1 列。
  建议同时补一条测试：`assert_eq!(offset_to_position(3, &Rope::from_str("ab\r\n")), Some(Position::new(0, 2)))`
  （**注意**：该断言在当前实现上会失败，请与修法一起提交，不要单独加）。

### [P3 · C2] 回落类别表 `KNOWN` 与生产调用点漂移（A7 §4.1a 的建议：我独立枚举确认）

- 位置：`tests/twin_engine_tests.rs:983-994`（A3 的文件，只读）对 `src/lib.rs` 的回落调用点。
- 证据（我重新逐行枚举，不采信报告结论）：`note_twin_fallback(` 在 `src/lib.rs` 有 **9 个调用点**
  （`:1457`、`:1501`、`:1574`、`:1576`、`:1612`、`:2375`、`:2390`、`:2405` 与 `:1501` 的 `decline` 参数），
  其中 `:1501` 的 `decline` 可取 `resident-unavailable`/`prelude-prime-failed`/`observe-failed` 三值 ⇒
  **生产类别共 10 个**：`prelude-unavailable`、`resident-unavailable`、`prelude-prime-failed`、
  `observe-failed`、`symbol-defined-in-another-file`、`untrusted-error`、`error-state-with-println`、
  `cross-file`、`no-document-id`、`no-parse-result`。
  `KNOWN` 也是 10 项，但**多 `hdl-check-gate`（生产已无）、少 `error-state-with-println`**。
- 机制/影响：`twin_fallback_classes_are_exactly_the_known_set`（`:979-1034`）只在 `examples/**` 上采类别，
  且只断言 `KNOWN.contains(class)` + `seen == ["untrusted-error"]` ⇒ 新类别不在语料上出现时**不会变红**
  （A7 的判断成立）。但该测试自己的 doc（`:981-982`）写着"Adding a call site means editing this list
  on purpose"——本轮新增调用点没有编辑它 ⇒ **机制已事实上失效**：将来任何"只在非语料输入上出现"的新类别
  都可以静默加入。属文档/契约漂移（P3，不是行为缺陷）。
- 处置：仅报告（A3 的文件）；建议 Lead 要求 A3 补 `error-state-with-println` 一行，
  并考虑 A7 §4.1b 的收紧方案（把 `KNOWN` 拆成"生产可达/保留作重开点"或在 `lib.rs` 侧做静态比对）。

### [P3 · C3] A7 本轮 UTF-16 修复没有直接的回归测试；相邻测试的"期望值算法"本身按 char 计数

- 位置：`src/client.rs:21-43`（私有 `position_to_byte_offset`，全文件无 `#[cfg(test)]`）；
  `tests/test_rope_offset.rs:103-127`（`test_roundtrip_conversion`）。
- 证据：
  1. `position_to_byte_offset` 只被 `render_diagnostics_stderr`（`src/client.rs:62-63`）调用，
     而后者在 CLI 诊断渲染路径上——本仓**没有任何测试**直接或间接覆盖非 ASCII 的 CLI 渲染
     （A7 自己也把它记在 §2[P2] 的"处置"里，但只改了代码）；
  2. `test_roundtrip_conversion` 的期望值（`:111`）是
     `line_text.chars().take(utf16_pos as usize).map(len_utf8).sum()`——用 **char 个数**当 UTF-16 个数。
     这只在全 BMP 文本上等价；一旦语料里加 emoji，这条断言会给出**错误的期望值**（可能假红或假绿），
     而不是检出真问题。语料（`:92-99`）恰好全是 BMP。
- 机制/影响：A7 的修复方向正确（§3.3/§3.8 已确认），但"非 BMP 正确性"目前只有读代码这一层保障；
  这正是 A7 §2[P2] 自己点出的覆盖缺口（他建议补 2 行）。
- 建议（都在 A7 的文件/测试里）：补 `offset_to_position`/`position_to_offset` 的 emoji 正例
  （例如 `"🎉ab"`：offset 0→(0,0)、offset 4→(0,2)、`Position(0,1)`→clamp 到 4），
  并把 `:111` 的期望值改为按 `len_utf16()` 累计。

### needs-verify（2 项）

1. **[值输出面闸的残留敞口] "无错态的值分歧"仍无任何机制**
   - 依据：新闸的判据是 `!errors.is_empty() && !printlns.is_empty()`（`src/lib.rs:1610`）；
     也就是说，**只有孪生自报错误时**才对值输出设防。孪生报 0 错误、参考版也报 0 错误、
     但两边 `println` 值不同的情形（纯值分歧）会直接发布孪生结果。
   - 与 A7 的 needs-verify-1 是**镜像关系**：那条是"错误集本身错了（带 println 的实例已被闸拦住，
     无 println 的实例待证）"，这条是"错误集为空但值错了"。
   - 现有对拍：`tests/twin_engine_tests.rs:1126-1169` 的 INFO 对拍只跑
     `examples/theorem_proving` / `adder_proof` 两个文件（A7 §2[P1-3] 兼容性核对第 2 条），
     其余 30 个示例只对拍 error/warning（`errwarn`）。
   - 定案成本低：把 INFO 对拍扩到 `examples/**` 全量（参考版 32 个文件全绿 ⇒ 可直接对拍），
     或在 A3 修完恢复路径后由 R0 引擎对拍报告覆盖。**不改任何代码**即可验证。
2. **[值输出面闸的性能量化] 我判断"是实质回退、但方向正确、量级未知"**
   - 代价结构（静态确定）：回落路径 `elaborate_with:2412-2418` = 孪生整轮**之后**再
     `parse_file` 一次 + 参考版整轮（注释明说参考版按值消费 `Decl` 所以重 parse）；
     `note_twin_fallback` 只写日志，`twin_gate_distrusted` 的粘性早退是**死代码**
     （A7 §2[P3-2] 已核实）⇒ **每个 kick 都会重复双跑**，在"错误 + println"持续存在期间一直如此。
   - 我的判断：这**不是**新增了一类代价，而是把既有的回落集合（`untrusted-error`/`cross-file`
     一直双跑）扩大了一档；参考版成本占主导，且"错的**值**"远比一次双跑糟
     （F2 的实测反例：INFO 面板出现参考版根本不承认的 `add 2 2`）⇒ **取舍成立，可以接受**。
     需要量化的只是"最坏情况下每键多花多少毫秒"，用来决定要不要做下面的优化。
   - 可选优化（建议记入 §5，不必本轮做）：对"本次 kick 因本闸回落"的 URI 记一个标记，
     在**下一次 kick** 直接走参考版（跳过孪生），直到该文件重新解析成功且错误集为空为止
     —— 注意这与 `twin_gate_distrusted` 的"粘性到关闭"不同，必须带"重新探测"出口，
     否则修好错误后永远不再用孪生（A7 §5.3 已就这一点提过设计建议）。
   - 请 Lead 用 F2 语料测一次 twin-only vs fallback 的 kick 延迟（`LEAD-probes.md` 已有探针），
     若同量级（<2×）则无需优化，直接等 A3 修完恢复路径撤闸（A7 §4.2/§5.5）。

## 3. A7 R1 主张的独立复核（逐条给依据）

| # | A7 主张 | 我的复核 | 依据 |
|---|---|---|---|
| 1 | 正常 shutdown 后挂起 = writer 通道唯一发送端被 `backend` 钉住；`drop(backend)` 可解 | **成立** | `lsp_stdio.rs:157-164`（writer 线程 iter 到通道断开）、`:128-131`（唯一发送端进 `Connection`）；`src/lib.rs` 内无 `Arc::clone`/`backend.clone()`（全仓仅 `tutorial.rs:349`、`doc/collect.rs:685`、`bin/l13lsample.rs:49` 持有各自后端的 Arc）⇒ `drop`（`lib.rs:4026`/`:4067`）释放最后一份 ⇒ 发送端 drop ⇒ join 返回 |
| 2 | panic 分支应回 `Err` 而不是吞掉后 `Ok(())`；且不能先 join | **成立** | `lib.rs:4039-4061`（`catch_unwind` → 打印 → `return Err`）；不 join 就不会把崩溃表现成挂起；`09c78e9` 的口径（`:3819-3823`）被补齐 |
| 3 | CLI 渲染应按 UTF-16 而不是 char | **成立** | `client.rs:31-35` 改 `len_utf16()`；服务端 `lib.rs:3867/3885/3895` 同口径；全仓 grep `offset_encoding` 无命中 ⇒ LSP 默认 UTF-16 |
| 4 | 只有 `offset_to_position`/`position_to_offset` 两个转换函数（+CLI 侧一个），无第三条路径 | **成立** | `Position::new`/`Position{..}`/`.character` 的全部出现点：`client.rs:32/38/80`、`lib.rs:3159/3183/3615/3870/3874/3875/3891`；其中 `lib.rs:2015-2016`/`:2617-2618`（合成 "parse error" 诊断）与 `:3159`（整卷格式化）是**常量** Position，不做单位换算 |
| 5 | parse error 也走 `offset_to_position` | **成立** | `lib.rs:1688-1700`（reference 路径的 parse/elab 诊断）、`:2604-2605`（twin 拥有时的诊断）全部 `offset_to_position`；解析 span 是本文件字节偏移（R1 已核宏展开 span 回落/映射到 call-site，不会跨文件错配 rope） |
| 6 | `l13bench` 改引 `PRELUDE_CORE/PRELUDE_HDL` 常量可行 | **成立** | 常量 `pub(crate)`（`src/L13_namespace/mod.rs:3861/3880`），同 crate 的 bin 可直接 `const` 引用（`bin/l13bench.rs:129-130`）；Lead 的 `cargo check --all-targets` 0 error 佐证 |
| 7 | §4.1c：错误语料第 8 条会退化成"参考 vs 参考" | **已被 A3 在 R2 处理**（比 A7 预期更好） | `tests/twin_engine_tests.rs:206-238` 现为 `(src, Option<class>)` 语料：F2 形态标 `Some("error-state-with-println")`（`:231-234`），并新增**去 println 的对照条**（`:237`，断言孪生仍拥有）；`:267-280` 对 `None` 条目显式断言"孪生拥有"，比较不再可能静默退化 |
| 8 | 值输出面闸只在"信任类错误 + 有值输出"时触发 | **成立** | `lib.rs:1566-1579`（untrusted 早退）之后才是 `:1610`；`printlns` 来自 `entry.rs:1527-1531`（`DeclOut::Println` 的已算好 pretty 串，含 stuck 值）⇒ 语义是"产出了值"而不是"源码里有 println"；`parse_errs` 确实未参与 |
| 9 | F2 的机制（旧判据只看错误类别、println 从不参与） | **成立** | `classify`（`:1551-1565`）只看消息前缀；`:1505-1519` 采集 `printlns` 后旧代码只用于发布、不参与判据 |

## 4. 需要 orchestrator 处置的事项

1. **C1 的修法在 A7 切片**（`src/lib.rs:3863-3869` + `tests/test_rope_offset.rs` 补一条 CRLF 终止符断言）：
   请转 A7 下一轮；本项与我 R1 的会签项（`Span` 全字节偏移、LSP 侧唯一转换点是 `offset_to_position`）
   是同一族的收口——字节侧没有偏差（我已确认），偏差在**终止符的列口径**上。
2. **C2 在 A3 的 `tests/twin_engine_tests.rs:983-994`**：补 `error-state-with-println`（一行）。
3. **C3 在 A7 的测试**：补非 BMP 正例 + 修 `:111` 的期望值算法。
4. **needs-verify-1（无错态值分歧）**：建议 Lead 把 `twin_engine_tests.rs:1126-1169` 的 INFO 对拍
   扩到 `examples/**` 全量——这是**零代码改动**的验证，能一次性给"值面"一个覆盖率答案。
5. **needs-verify-2（闸的性能量化）**：Lead 已有 F2 探针，补一个 kick 延迟对比即可定案。

## 5. 设计决定讨论（不属 bug，只记录）

1. **"闸"的粒度与可信度**：本轮新增的值输出面闸是**保守近似**——它不判断"哪个值更对"，
   只在无法自证时把权威交回参考版。我认同这个方向，但要记录它的两个不对称：
   (a) 它对**错误态**设防，对**无错态**不设防（needs-verify-1）；
   (b) 它的判据里 `printlns` 只要非空即触发，不看值的形状（A7 §5.5 已说明为何不用 pretty 子串匹配：
   误判/漏判面不可控）。若日后要把闸收窄，正确的前置条件是 A7 §4.2 的 A3 侧修复，
   而不是继续加形状判断。
2. **"双跑"是本仓引擎架构的内建代价**：`elaborate_with` 的回落路径必然"孪生 + 重 parse + 参考版"。
   因此"某类文件是否回落"直接等于"该类文件的每键延迟"，本轮新增一档回落应该在
   `docs/l13-perf-replace-*.md` 那类文档里留一行（哪些类别会双跑），否则后续评审会反复问同一个问题。
3. **位置口径应该只有一个事实来源**：本轮 C1 的根因是两个函数各自实现"行内容"的概念
   （一个 break 在 `offset`，一个先量 `content_utf16`）。建议长期把"行内容长度（不含终止符）"
   抽成一个共享函数（`line_content_utf16(rope_line)`），让 `offset_to_position`/
   `position_to_offset`/`client.rs::position_to_byte_offset` 三处都引它——这是纯重构建议，不在本轮改动内。
4. **A7 的 `catch_unwind` + `Err` 与 `abort` 的取舍**（A7 §5.2）：我同意本轮选择（与 `09c78e9` 的
   `Box<dyn Error>` 链一致、CLI 能打人话）。补充一个观察：`vscode_extension` 只看 `State.Stopped`
   不读 exit code（A7 §4.4），所以这个修复的收益在 CLI/守护脚本/日志侧，别在扩展里按 exit code 加重启逻辑。
