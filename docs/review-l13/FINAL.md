# L13 + 共享基础设施 多轮评审 · 最终汇总报告

- **评审对象**：`src/L13_namespace/**`（48k 行主引擎，含 HDL→Verilog 与 namespace/LSP）、
  `src/lib.rs`（199KB 宿主路由）、`parser_lib*`、`lsp_stdio`/`client`/`ls`/`config`、
  `src/{sim,doc,format,bin}/**`、`src/prelude/**`、`examples/hdl/**`、相关 `tests/*.rs`
- **工作树**：`F:/projects/hermes/elaboration-zoo-lsp-review-l13`，分支 `review/l13-shared-perfect`
  （基于 `350b35a`；**主线 `F:/projects/hermes/elaboration-zoo-lsp` 全程未被触碰**）
- **方法**：7 个 agent × 2 轮（审计+修复 → 集中编译/测试 → 轮转交叉只读审计），
  所有 `cargo` 由 Lead 集中执行；Lead 另做**独立验证探针**（双引擎差分、LSP 进程级、宇宙逃逸实验）
- **已验证的 revision 指纹**（门禁通过时）：tracked-diff SHA256 `F17D71BC…0AC8`
- 未提交（按约定不擅自 commit）

## 1. 门禁结果

| 门禁 | 基线（350b35a） | 最终 | 变化 |
|---|---|---|---|
| `cargo check --all-targets` | 0 error / 3218 warn / 54.3s | **0 error** / 10.2s | 通过 |
| `cargo test --lib` | 879 过 / 0 败 / 6 ignored | **882 过 / 0 败 / 6 ignored** | +3 |
| `cargo test --test l13_fast_parity` | 533 过 / 0 败 / 6 ignored | **536 过 / 0 败 / 6 ignored** | +3 |
| `cargo test --test twin_engine_tests` | 26 过 | **27 过 / 0 败** | +1（收紧断言 + F2 回归钉） |
| `cargo test --test hdl042_engine_tests` | —（不存在） | **2 过** | 新增 |
| `cargo test --test parser_error_tests` | — | **107 过** | +6 |
| `namespace_tests` / `hdl_check_locations` / `emit_tests` / `lsp_protocol_robustness` / `known_bug_pins` | 30 / 2 / 12 / 11 / — | **30 / 2 / 12 / 11 / 8 全过** | 无回归 |
| **`bash tools/gate_l13.sh`（仓库自带门禁）** | — | **fail=0**（评审树 166s / 主线复跑 199s；lib 521 + parity 15 + twin_lsp 27 + hdl042 2） | 通过 |

**历史问题已复验修复**：`docs/review-l01l12/FINAL.md` 记录的 `cargo test --lib`
`STATUS_ACCESS_VIOLATION` **不再复现**（885 用例全跑完，exit 0）。A4 给出了代码侧论证：
推池前 `force_memo_clear() + declb_cache_clear()`（`mod.rs:3824-3845`）已闭合
"死亡线程递减池化节点引用计数"的机制；`unsafe impl Send for PoolState` 的唯一前提
（推池时持最后引用）经枚举全部持 `Rc` 的线程局部后成立。

## 2. 已修复（按价值排序，均经门禁）

### 2.1 P0：用户可触发的挂起 / 崩溃 / 构建破坏

1. **参考版 `change_mutable`/`change_mutable_default` 持写锁调用用户回调 → 自死锁（挂起）**
   - `cxt.rs:718-739`、`:846-864`。回调急切求值（`closure_apply`→`eval`），回调体里的
     `get_global`/`change_mutable*`/`create_global` 会同线程重入同一把**非递归** `std RwLock`。
     快版 `prim.rs:591-611/635-654` 本来就是"取值→释放→求值→回填"，**参考版缺这一步**。
   - **Lead 实测**：修复前该程序挂起；修复后 8.28s 正常返回、`errs=[]`。
     已加**看门狗回归钉**（`class_tests.rs:746-805`，超时即失败而非挂死门禁）。

2. **宏命名片段在「匹配阶段」无界递归 → 两行用户源码栈溢出**
   - `parser/macros.rs:82-140`。`macro_rules Loop { ($x: Loop) => { $x } }` + `def f = Loop 1`
     即无限递归；三个 `MacroDepthGuard` enter 点都在 re-parse 路径上，**一个都不覆盖匹配阶段**。
   - 已修（共享 thread-local 守卫；触顶**既 push 诊断又返回 Err**，因为调用方 `if let Ok(..)`
     会吞掉匹配器错误、只返回 Err 会静默退化成"标识符应用"）。钉子见 `parser_error_tests.rs`。

3. **构建破坏：一条新测试让仓库自带门禁直接变红**
   - 新增的双引擎 HDL042 测试最初写进 `src/L13_namespace/hdl_check_graph_tests.rs` 并引用
     `crate::Backend`/`crate::Engine`/`crate::client`。但 `tests/l13_fast_parity.rs` 用
     `#[path = "../src/L13_namespace/mod.rs"]` 把整个 L13 **再编译**进测试二进制，那里 `crate`
     不是 lib ⇒ 8 个 E0433/E0425 ⇒ **`tests/l13_fast_parity` 编译失败 ⇒ `tools/gate_l13.sh` 红**。
     `--lib` 却是绿的（`crate` = lib），所以自测发现不了。
   - 已搬到集成 target `tests/hdl042_engine_tests.rs`，并**注册进 `tools/gate_l13.sh`**。
     该陷阱已作为通用纪律写进 A5 报告 §4。

### 2.2 P1：可达 panic / 诊断错位 / 引擎分叉

4. **转写器 brace 分支 `usize` 下溢 → 畸形宏定义 panic**（`parser/mod.rs:2543`）：
   `macro_rules m { () => { $({)* } }` 在 `) *` 上零消费 break ⇒ debug 下溢 panic /
   release `i_back[..usize::MAX]` 越界。改 `saturating_sub`（正常路径逐位等价）。

5. **LSP 正常 `shutdown` 后进程永久挂起**（`lib.rs:3987`、`:4028` 缺 `drop(backend)`）：
   `Connection.sender` 是 writer 通道唯一发送端且被 `Arc<Backend>` 持有，不释放则 writer 线程
   `into_iter()` 永不返回；`shutting down server` 是死代码，编辑器只能强杀并留下常驻孪生内存。
   - **Lead 进程级实测（用 A7 的探针 + 本工作树二进制）**：
     `initialize` → `initialized` → `shutdown` → `exit` ⇒ **`process exited rc=0 after 0.1s`**，
     stderr 打出 `shutting down server`。**修复成立。**

6. **LSP `main_loop` panic 被吞掉后仍返回 `Ok(())` ⇒ 真崩溃 exit 0**（`lib.rs:4019`）：
   与 `09c78e9`"让宿主区分正常关闭与崩溃"的口径正好相反。改为 `return Err(...)` 且不 join。
   - **验证强度（如实）**：静态验证 + A6 独立会签；**未做进程级故障注入**——注入需要临时改
     `src/lib.rs`（A7 的切片），而 A7 当时仍在写入中，会违反 write-scope 纪律。

7. **孪生版对「无端口 + for 循环」的 module 误报 HDL042**（**Lead 探针发现**）
   - 同一源码 `Engine::Reference` 出 0 条 HDL042，`Engine::Twin` 出 2 条，生成 Verilog 逐字节相同。
     隔离实测：`no_for_control`（去掉 for）与 `for_with_ports`（有端口）均不触发。
     LSP **默认走孪生版**，所以编辑器里凭空多一条 warning——正是信任闸注释里
     "错的诊断比慢的诊断更糟"要防的事（信任闸只比 error，不比 warning）。
   - A5 定位为**检查器判据太宽**：`declKeysOf` 把所有声明都算进签名，内部声明在轮间
     因 `nat_is_ground` 门而**不稳定**（同一条 publish 的 warning 里同时有 `x` 与 `x_0..x_3` 残影）。
     `docs/hdl-language-spec.md:630/533` 本来就写的是"**端口**宽度集" ⇒ 收窄到端口是与文档对齐。
     已修 + **双引擎钉子**（`hdl042_engine_tests.rs` 2/2：F1 源码两版都静默；真碰撞两版必报）。

8. **`preprocess` 不识别字符串字面量 → 静默改字符串内容**（A6 发现、A4 修复）
   - `mod.rs` 的 `preprocess` 把任何 `//` 当行注释头、`/*` 当块注释头：
     `def u = "http://x"` 被截成未闭合字符串（伪解析错误）；`def s = "a/*b"` 被**静默改成** `"a  b"`。
     仓库自证：`src/format/layout.rs:503-511` 明写 "preprocess is not string-aware… decline"
     并绕过了它 ⇒ 格式化器承认、解析器主路径没绕过。已按 `L06_string` 的字符串感知实现移植
     （保持等字节长）。

9. **BOM（U+FEFF）文档开头产生伪解析错误**（`parser/lex.rs:310`）：U+FEFF 不在
   Unicode `White_Space` 里 ⇒ 落到 `err_token` ⇒ 每个带 BOM 的文件一条伪错
   （`bin/cli.rs` 的 `read_to_string` 不剥 BOM ⇒ 必然触发）。已修 + 钉子。

10. **CLI 诊断按 `char` 而非 UTF-16 计数 → 非 BMP 字符后诊断错位/整条丢失**（`client.rs:21-43`）：
    与 `offset_to_position` 的 LSP UTF-16 口径不统一。已改为 `len_utf16()`。

11. **信任闸新增值输出面闸**（`lib.rs:1610-1617`，新类别 `error-state-with-println`）：
    孪生曾把失败的 `decl` 当不透明 rigid 求值并打印参考版根本不承认的 `add 2 2`（Lead 探针发现）。
    现"孪生自报错误 + 又产出 println 值 ⇒ 整体回落参考版"。

### 2.3 P2：资源泄漏 / 缓存失效 / 输出确定性

12. **迭代 Drop 的 worklist 对「未 drain 的叶子」也 `forget` → 每个嵌套叶子泄漏一个堆块**
    （A4，`mod.rs:511/877/1017` + 5 处调用点）：三个 drain 改返回 `bool`，调用方
    `if drain { forget } else { 正常析构 }`。同族形态本仓典型：`Val` 侧修过、`Tm` 侧与叶子路径漏了。
13. **换 arena 后未失效「bump 地址为键」的缓存**：孪生 `ns_method_cache`
    （A3 `entry.rs` 三处 + A2 内聚进 `compact_state`）、五张 TLS 缓存
    （`FORCE_MEMO`/`FORCE_PRIM_MEMO`/`TWIN_DECLB_CACHE`/`QUOTE_NAT_TM`/`STUCK_DECL_INTERN`，A2）。
14. **`BindingName.mk` 限定名选取走 `HashMap::keys().find()` 任意序**（A1）：
    输出字节可跨进程漂移。改字典序最小 `min_by`（A1 给了唯一性证明；A7 补了
    "生产路径永远命中精确键 ⇒ 兜底分支不可达"的可达性论证）。
15. **`tools/gate_l13.sh` 现覆盖第四件套**（Lead）：新增 HDL042 双引擎钉子，堵住
    "auto-discovery 的测试不进显式门禁"这一缺口（CI 的 test-full 会跑，但 L13 门禁不会）。
16. **测试收紧（A3/A7）**：`twin_engine_tests.rs` 的回落类别表补 `error-state-with-println`、
    删陈旧 `hdl-check-gate`、新增 `include_str!("../src/lib.rs")` 静态 pin（扫
    `note_twin_fallback` 字面量 + `>=7` 金丝雀），并把"错误 + println"条目从**恒真守卫**
    改造成"声明归属 + 断言 reason"（**第一次运行就抓到一条既有标注错误**，见 §3.6）。

17. **prelude 装载器的解析错误打到 stdout**（A4，P3）：LSP 的 **stdout 就是 JSON-RPC 通道**，
    往那里打文本会污染协议流。已改到 stderr。
18. **`test_n1/n3/n6/n7/n8-n11` 的"记录 ≠ 钉住"**（A4）：这批名字里带
    `unsoundness`/`doc_only` 的测试**确实是零断言或粗粒度断言**（"只是记录"）。
    A4 已把 N1/N3 改成真断言、订正 N1/N3/N6/N10 的陈旧注释锚点；
    N7/N8-N11 的"仅记录"性质已在报告里明确定性。
    （Lead 原以为 `test_n6_checked_ret_cache_unsoundness` 藏着活的 soundness 洞——
    A4 核对后判定 `checked_ret` 全仓只剩测试注释，孪生亦无同类缓存，属"记录了但已不成立"。）

## 3. 残余问题（诚实记录；**§3.3 已于 2026-10-01 修复**，保留本节作根因与修复记录）

### 3.1 [P0] 快版 `Machine::unify` 整机重借 —— Stacked Borrows 别名 UB（**三方一致，仍未修**）
- **位置**：`bump_spine_iter/machine.rs:1310`（`let mach_ptr: *mut Machine = self;`）→
  `:1311-1324`（字段解构）→ `unify.rs:384`（`flex_flex_bump`）、`:1395`（`solve_flex_side_bump`）
  的 `unsafe { (&mut *mach_ptr).solve_multi_trait_ref(..) }`。
- **机制**（A3 主查、A2 独立复核并 `web_fetch` Miri `stacked_borrows/mod.rs` 逐条对照、A1 会签）：
  `mach_ptr` 是 `RetagMode::Raw`（`SharedReadWrite`、`access: None`），插入位置恰在 `&mut self`
  的 `Unique` 正上方；**紧接着的字段解构**产生 `Unique + access: Some(Write)` 的字段 retag，
  其 write-access `pop_items_after(parent_idx+1)` **把 raw tag 从该字段字节段弹掉**；
  随后整机 `&mut *mach_ptr` 的 retag 在那些字节段 `find_granting` 失败 ⇒ `access_error` ⇒ UB。
  **触发点是"求值该表达式本身"，与内层求解成败无关。**
- **"一步之遥"**：`unify.rs:691` 读 `(*mach_ptr).trait_metas.len()` 之所以安全，只因
  `trait_metas` 不在解构列表里；**把该字段（或任何新字段）加进 `machine.rs:1311-1324` 会立刻让它 UB**。
- **为什么没修**：修复要把 `solve_multi_trait_ref`/`solve_trait_ref` 改成接收不相交字段的自由函数，
  被调用侧需要的字段集 = 调用方 `unify_iter` 已持有的字段集 ⇒ 要穿整套 ~10 个 `&mut`；
  本环境**无 Miri**，盲改一个正在工作的依赖类型语言实现风险更高（BRIEF §6.7）。
- **两条反直觉的结论（供立项时避免走弯路）**：
  (a) 把 `let mach_ptr = self` 挪到解构**之后**不能修（只是把弹出方向反过来）；
  (b) 用 `let Machine{..} = unsafe { &mut *mach_ptr };` 这个**可编译变体**也不能修（其 write-access
      会弹掉字段 `&mut` 与那个新 `Unique`，返回后 `unify_iter` 继续用 `spine/metas/conv/stack` 仍 UB）。
- **正确验证方式**：`cargo +nightly miri test`，**用默认/permissive provenance**，
  **不要** `-Zmiri-strict-provenance`（packed-word 本身就是 `ptr→int→ptr`，strict 下直接报错；
  改用 `expose_provenance` 又会把访问退化成 wildcard 匹配、"forget everything" ⇒ 更难检出）。

### 3.2 [P0] `lvl2ix` 越界 panic —— 用户可触发的崩溃，且被测试固化成期望
- **位置**：参考版 `mod.rs:1126-1140`（panic `:1134-1137`）、孪生 `bump_spine_iter/syntax.rs:179-191`
  （panic `:185-190`，**同文案**）。
- **证据**：`tests/l13_fast_parity.rs:695-791` 的 `parity_into_add_nat_uint_field_projection`
  **把"两版都 panic 且文案逐字相同"写成期望**（`:784 assert_eq!(b, f)` + `:787-790 assert!(b != "Ok()")`），
  注释 `:745-748` 自述"本形态上双引擎都会 panic"。即：**用户可触发的崩溃被固化为预期行为**。
  `docs/l13-known-bugs-2026-08.md:51-79` 亦明写"Bug 2 仍未修复"。
- **暴露面**：`lib.rs:4039` 唯一的 `catch_unwind` 只包 `main_loop` ⇒ panic 会让整个 LSP 会话终止。
- **【重要限定，Lead 实测】**：该 fixture **仅在 bare 口径**（`L13_namespace::run(&src, 0)`，无 prelude）
  下 panic；经**真实 LSP 路径**（`Backend::process_file` + 全 prelude，两引擎各跑一次）
  **不 panic**（150s 内既不退出、stderr 也无 `main loop panicked`）。
  ⇒ "库/测试路径已证；LSP 路径未证（同一 fixture 不触发）"。要判定 LSP 面需要另一个触发样本。
- **修复三档**：遏制（per-request `catch_unwind` → 诊断 + 回落，最小项）/ 降级为可恢复 Err /
  根治（meta 解消费点参数化，架构级）。

### 3.3 [P1 · 已于 2026-10-01 修复] 孪生版会「拥有」一个错误集不完整的文件
- **位置**：孪生根因 `machine.rs:789-823`（`fake_bind` 就地写**调用方** `Cxt`，写入点 `:805`）
  + Def 臂三个错误出口 `:3543/:3552/:3616` 不回滚 stub + `entry.rs:1258` 保留同一 cxt。
- **Lead 实测**（同一源码、真实 LSP 面、只取最后一次 publish）：
  | 变体 | REF errs | TWIN errs | twin 回落 |
  |---|---|---|---|
  | 无 println | `can't unify…`, **`error name not in scope: add`** | 只有 `can't unify…` | **无** |
  | + 引用链 | 3 条（逐条 not-in-scope） | 1 条 | **无** |
  | 对照（普通类型错） | `can't unify expected Nat find Boolean` | 同 | 无（一致） |
  ⇒ 孪生拥有该文件并发布**不完整错误集**，真实病因（`add` 未定义）在编辑器里被隐藏。
  A7 的值输出面闸只覆盖"**错误 + println**"，**错误但无 println** 的文件不在保护范围内。
- **参考版为何不这样**：LSP 参考路径走 `Infer::infer(&Cxt)` → `elaboration.rs:1063-1066` 先
  `cxt.clone()` 隔离；其 `infer_in_place` 调用者全部首错即停。只有孪生把"就地 COW"与"错误不早退"交叉。
- **已修复（2026-10-01，用户批准后落地，commit `4d90850`）**：按方案 A 定点回滚——
  `fake_bind` 撞名检查前移（对齐 `cxt.rs:1230`，顺带修掉 redefine 时旧条目被存根覆盖）+
  `Machine.decl_stub: Vec<SmolStr>` 栈 + 成功路径在 Def/Enum 臂尾出栈 +
  失败路径出栈收口在 `infer_decl` / `infer_after_prefix`（`infer_after_prefix_mut` 的全部调用者），
  `infer_decl` 用 `Rc::make_mut(&mut cxt.decls).remove(&k)` 回滚表项。
  两处 Err 出栈带**栈深差守卫**——无条件 `pop()` 会在"内层 decl 在 `fake_bind` 之前失败、
  错误冒泡到外层入口"时偷弹外层的键，反使外层存根泄漏（这是落地时对原方案的一处收紧）。
  **验证**：双引擎错误集逐条相等（v0 与引用链 v1 两个变体）且**孪生未回落** ⇒ 修掉错诊断的
  同时保留孪生在错误态的速度收益；回归钉
  `tests/twin_engine_tests.rs::twin_reports_reference_error_set_after_failed_def`。
  **残余（另立项）**：失败的 **class** decl 经 Phase B 克隆表注册的多个名字仍不撤回
  （需 per-decl 的 decl 表写点 journal，即方案 B）。
- **方案 C（遇错即停、交参考版接管）不建议单独落地**：A3 量化结论是"会让错误态速度收益归零且略负"
  （打字期多数按键带错 ⇒ 孪生部分 pass + 参考版完整 pass = 双付）。

### 3.4 [P2] `prune_vflex` 折叠序：L13 与 L05–L08/快版口径不一致（**本轮按纪律回退**）
- `unification.rs:350-365` 的 `sp.iter().fold(...)`（`//TODO:need rev()?`）从**最内层**起折叠，
  与 `L05_pruning/mod.rs:32-37`（该 TODO 已被认定为旧移植 bug 并修）、`L06_string`（"sp 头 = 最内层"）、
  快版 `rename.rs` 的取向相反。精确判据：可观测 iff flex spine 有 **≥2 个 `Some` 槽**。
- **A2 穷尽核对后：现有 L13 语料一处都不能区分** ⇒ 给不出 L13 触发用例 ⇒ 不满足 BRIEF §6.3
  "改行为必须证明是 bug 且给触发用例" ⇒ **Lead 裁决回退**（已逐字节还原，`git diff` 该文件为 0）。
  残留记为"L13 与其余四份拷贝口径不一致，待立项"，移植配方见 `a2-r2.md §2.1`。

### 3.5 [P2] 测试与运行期的三处结构性弱点
- **L13 parity 套件缺 pruning / church / solve 三类负载**（A2）：`l13_fast_parity` 判据是
  "两版同判"，**没测的分支完全不可见**——"同错"与"都对"无法区分（§3.4 就是实例）。
  最小补齐：L06 场景 3 的 L13 适配 + L12 两源适配 + `church_src(8)`，≈4 条用例 /≤40 行。
- **`DECLB_CACHE` 以 decl 表裸指针为键，但 decl 表会被 `Rc::make_mut` 原地改写**（A4）：
  `mod.rs:1188-1249` + `cxt.rs:1227/1292` ⇒ 陈旧简化表 + ABA 面。修法需 `Cxt` 加代数计数器
  （跨 A1/A4 两个切片），本轮仅报告（needs-verify 最小复现）。
- **测试侧用 512 MiB 大栈"绕过"而非修复，运行期无递归深度上限**（A4）：
  `with_big_stack_legacy`(512 MiB) / `l13_fast_parity`(256 MiB) / `.cargo/config.toml`(64 MiB，
  且仅 `x86_64-pc-windows-msvc`/`-gnu` 生效)——**口径三档不统一**；`UNIFY_FUEL = 4096` 护的是
  计数型燃料，**不是递归深度**。用户从 LSP/CLI 走的是默认栈。

### 3.6 其他（P3 与文档）
- `ok` 是 prelude 构造子（`src/prelude/data/result.typort:6`），`twin_engine_tests` 的 CORPUS 条目
  `("def ok: Nat = zero", None)` 因此**一直是错误的标注**：孪生早已回落、诊断比对退化成
  "参考版 vs 参考版"，测试照样绿——**A3 本轮加的 `reason == None` 断言第一次运行就抓到了它**
  （已改为 `def okv`）。这是"收紧门禁抓到真东西"的实例。
- `typort check` **无退出码语义**（有 ERROR 也 exit 0），而 `quick.rs` 与两组 docs 把它当门禁。
  **裁决：本轮不改退出码（破坏性行为变更），只改错误文档**（`bin/cli.rs` 的 `--help` +
  `quick.rs` 两处已改；立项材料见 `a7-r2.md §5.1`，含"两阶段发布必须按每 URI max(ERROR 数) 计数"的坑）。
- 共享 docs 两处"check 是门禁"表述未改（`docs/spinalhdl-lib-replication.md:87`、
  `docs/l08-l13-refactor-plan.md:49`）——本轮 `docs/**` 按 BRIEF 只读。
- `offset_to_position`（`lib.rs:3863-3869`）把 CRLF 的 `\r` 计入 column ⇒ 往返不闭合
  （可达来源正是 `350b35a` 的 EndLine 锚点）；`test_rope_offset.rs:191-193` 恰好只钉了反向 clamp。
- `twin_gate_distrusted` 无任何写入点（"已停用"确认安全、无残留粘性早退）；**重启用前必须先补
  可恢复/非粘性的解除路径**（现在只有关闭文件才清除）。
- `tests/l13_fast_parity.rs` 的 `norm_err`（`:70-131`）把 `@ N`/`?N` 抹平 ⇒ parity 层看不见 span 漂移。
- `Engine::lsp_default`/`Engine::from_env` 的 twin 分支**零测试覆盖**（无任何测试设
  `TYPORT_LSP_ENGINE`）；LSP 进程生命周期无进程级测试（`gate_l13.sh` 不跑进程级，
  `large_did_open_no_hang` 结尾 `kill()` 而不驱动正常 shutdown）——**A7 的两个 P1 因此都不会被现有测试发现**，
  这正是 Lead 需要手工探针的原因。
- `lsp-server = "0.7.6"` 实际解析到 **0.7.9**，其 `Connection::handle_shutdown` 会**阻塞最多 30s 等 `exit`**。

## 4. 跨层同族未修（L01–L12 属本轮范围外只读，**已定位、建议跟进**）

| ID | 位置 | 同族理由 | 一行修法 |
|---|---|---|---|
| F-1 | `src/L12_canonical/parser/mod.rs:2010`、`src/L11_macro/parser/mod.rs:1986` | 与 L13 修复前的 `i_back.len() - input.len() - 1 - need_remove_endline` **逐字相同** | `saturating_sub(input.len() + 1 + need_remove_endline)`；钉子可复制 `parser_error_tests.rs:1736-1761` |
| F-2 | `src/L12_canonical/mod.rs:1381`、`src/L11_macro/mod.rs:1130` | 与 L13 `preprocess` 修复前同款（不识别字符串字面量） | 移植 `L06_string/mod.rs:379-434`，保 `debug_assert_eq!(len)` |
| F-3 | `L09_mltt/unification.rs:245`、`L10_typeclass/unification.rs:245`、`L11_macro/unification.rs:255`、`L12_canonical/unification.rs:258` | 与 L13 `prune_vflex` 同款 `//TODO:need rev()?` | **先补可区分测试、再统一修**（见 §3.4/§3.5） |

> 说明：这些文件在上一轮评审（`docs/review-l01l12/`）的**共享只读清单**内，且用户本次选定的范围是
> "L13 + 共享基础设施"，故**本轮按范围未修**。上面三条是可直接照抄的跟进条目。

## 5. 收敛判定（诚实版）

- **严格意义上未收敛。** 按 BRIEF §2 的字面判据，需要"自审与交叉均 0 个 P0–P2"；本轮的实际结果是：
  - **A1**：P0 1（已修 + 已验证 + 已钉）/ **P1 0**（原有 P1 经 Lead 两次实验判定为**未证实**，
    A1 已退回 needs-verify）/ P2 2（机制清楚、可达性未证）/ P3 3 / needs-verify 5
  - **A2**：会签 1（SB UB，既有）/ P1 0 / P2 2（含 §3.4 回退项与覆盖缺口）/ P3 2（已修）
  - **A3**：P0 1（SB UB，未修）/ **P1 1（F2 错误集面，已修 + 已实测验证 + 已钉）** / P2 0 新增 / P3 3 / needs-verify 11
  - **A4**：P0 0 / **P1 1（已修）** / P2 4（2 已修/加固、2 存量仅报告）/ P3 5（4 已修 / 1 仅记录）/ needs-verify 3
  - **A5**：P0 0 / P1 3（F1 已修 + 1 已修 + 1 仅报告）/ P2 4 / P3 7 / needs-verify 6
  - **A6**：P0 1（已修 + 实测背书）/ P1 1（已修 + 实测背书）/ P2 1（已修）/ P3 7 / needs-verify 2
  - **A7**：P0 0 / P1 3（全已修；其中 1 条降为孪生侧未闭合）/ P2 3（1 已修 + 2 待决策）/ P3 5 / needs-verify 1
- **未闭合项集中在两处**：§3.1 SB UB（需 Miri + 立项）、§3.2 `lvl2ix` panic（需立项）。
  两者**都不适合在没有 Miri 与专项验证的条件下盲改**——盲改一个正在工作的依赖类型语言实现
  的风险高于保留有据可查的已知项。
  （§3.3 的孪生错误集面已于 2026-10-01 落地修复并经双引擎探针验证，残留仅"失败的 class decl
  多名字回滚"，属方案 B 立项范畴。）
- **本轮的真实价值**：3 个 P0（自死锁挂起、宏栈溢出、构建破坏）与 10 余个 P1 被**实测确认并修复**，
  全部经门禁与仓库自带 `tools/gate_l13.sh` 验证；另有 2 个由 Lead 探针发现的引擎分叉
  （孪生 HDL042 误报、孪生错误集/值输出分叉）被定位并**全部修掉**。

## 6. 如何查看与复跑

```powershell
$env:CARGO_TARGET_DIR='F:\projects\hermes\elaboration-zoo-lsp\target'
Set-Location 'F:\projects\hermes\elaboration-zoo-lsp'   # 已合入 master
git log --oneline -10                                   # 10 个分类提交
bash tools/gate_l13.sh                                  # 仓库自带 L13 门禁（4 件套，主线复跑 fail=0 / 199s）
cargo check --all-targets
```

- **报告**：`docs/review-l13/` —— `BRIEF.md`、`BASELINE.md`、`LEAD-probes.md`（Lead 独立探针证据）
  - R1：`a1-r1.md` … `a7-r1.md`
  - R2：`a1-r2.md`、`a2-r2.md`、`a3-r2.md`、`a6-r2.md`、`a7-r2.md`
  - 交叉：`a1-cross-r2.md`、`a3-cross-r2.md`、`a6-cross-r2.md`、`a7-cross-r2.md`
  - 探针工具：`a7-probe.py`、`a7-probe-lvl2ix.typort`
- **状态**：10 个分类提交已**快进合并入主线 `master`**（`350b35a` → `8619512`），
  合并后在主线工作树复跑验证：`cargo check --all-targets` 0 error、`cargo test --lib` 882 过、
  `--test twin_engine_tests` 27 过、`bash tools/gate_l13.sh` **fail=0 / 199s**。
  用户在主线原有的两个未跟踪 docs 全程未被触碰。
  评审 worktree `F:/projects/hermes/elaboration-zoo-lsp-review-l13`（分支 `review/l13-shared-perfect`，
  已与 master 同点）保留备查，不需要时可 `git worktree remove` 后删分支。

## 7. 下一轮首选项（按性价比排序）

1. ~~**§3.3 方案 A 落地**~~ —— **已完成**（2026-10-01，commit `4d90850`；验收 = F2 无-println
   源码两版 errs 逐条相等且孪生未回落 + 全门禁绿 + 主线复跑 fail=0）。
   紧接着可做的是**方案 B**：失败的 class decl 经 Phase B 克隆表注册的多个名字仍不撤回。
2. **§3.5 补 pruning / church / solve 三类 parity 负载**（≈4 条用例 /≤40 行）：
   这是 §3.4 与 grad 族结论的前置条件——**先有可区分的测试，才有资格改行为**。
3. **§3.1 SB UB 立项 + CI 接 Miri**：`cargo +nightly miri test`（默认 permissive provenance），
   先让 UB 在 CI 上可见，再谈重构。
4. **§3.2 `lvl2ix` 遏制档**：per-request `catch_unwind` → 诊断 + 回落（把"用户可触发崩溃"
   降级为"可恢复错误"），并把该钉子从"两版都 panic"翻转成"两版都不 panic"。
5. **§4 的 F-1/F-2/F-3 跨层同族**：按"先补测试、再统一修"的纪律推进。
6. A2 提出的 `adder_proof` NF-DIVERGE（basic 26307 / fast 26357，用户可见渲染一致）——
   落点 `quote.rs` 正规形差异，属同一 parity 主题。
