# A3 Cross-Round2 — 只读交叉审计 A4 切片（`L13_namespace/mod.rs`、`legacy_tests.rs`）

> 轮转协议 BRIEF §5：**只读**，未改 A4 任何文件。
> 审计时点：2026-10-01（R2 期间），读到的修订含 A4 R1 已落改动（`a4-r1.md` §3：`mod.rs +70/−31`）。
> **A4 仍在 R1 中，`mod.rs` 可能正在被编辑 ⇒ 本文行号以我读到的版本为准**；引用处若与当前不同，
> 请以 `grep` 到的符号名为锚。
> 我的独特视角：孪生侧 owner（`Machine`/`prim.rs`/`bump arena`），`mod.rs` 同时定义两版共用的
> `Val`/`Tm`/`Infer` 与线程/池化边界。

## 1. 结论（verdict）

- **本切片未发现新的 P0/P1。** A4 R1 的两条 P2（迭代 Drop 泄漏已修；`DECLB_CACHE` 裸指针键）与
  其 needs-verify 处置（`preprocess` 字符串字面量）我**独立复核后同意**，理由见 §3。
- 1 条 **P3** 建议（推池前 TLS 缓存清单可执行化，§2.1）。
- 3 条**正面确认**（`unsafe impl Send` 论证成立；`RwLock` 无并发面 ⇒ 无写者饥饿；孪生侧无同类重入），
  2 条**交叉提示**（孪生的 `TWIN_DECLB_CACHE` 同族；`preprocess` 不是 parity 裂缝）。§4。

## 2. 发现

### [P3 · 建议] `unsafe impl Send for PoolState` 的论证前提靠"记得清缓存"维持，建议给出可执行护栏

- **位置**：`mod.rs:3752-3773`（`PoolState` 的 SAFETY 块 + `unsafe impl Send`）、
  `mod.rs:3824-3850`（`Drop for PreludeSlot` 的清缓存 + 入池）。
- **我独立复核的结论：论证成立**（证据见 §3.1），但"前提"是一条**人工维护的清单**：
  推池前必须清掉所有"可能仍钉着池化 `Rc` 图的线程本地缓存"。当前清单是两行硬编码
  （`force_memo_clear()` / `declb_cache_clear()`，`:3842-3843`），注释解释了漏一个就是
  use-after-free（该注释自己引用了历史 `STATUS_ACCESS_VIOLATION` 的溯源）。
- **风险**：未来任何人新增一个持参考域 `Rc<Val>`/`Rc<Tm>`/`Rc<Decl>` 的 `thread_local!`，编译期不会红，
  只在多线程测试里间歇崩。
- **建议（任选其一，都是几行）**：
  1. 把两行合成一个名字即契约的入口，例如 `fn pool_handoff_clear()`（`mod.rs` 内私有），
     注释写明"任何新增的参考域 Rc TLS 缓存必须挂这里"；
  2. 或在 `Drop` 里加一条 debug 断言的"版本计数"：每个 Rc 型 TLS 缓存在 `clear` 时自增一个
     `AtomicU64`（进程级），推池前快照两值、推池后比对——只能发现"漏清"的一部分，但比纯注释强。
- **处置**：仅建议（属 A4 文件，我不改）。可与 §4.2 的"换 arena 失效清单"合并为同一条工程实践。

## 3. 独立复核（A4 的结论我是否同意）

### 3.1 [确认] `unsafe impl Send for PoolState`（A4 §2 列为"42×ptr::read + 1×unsafe impl Send"，未展开）

我把**参考域里所有可能持有 Rc 图的 TLS 缓存**清点了一遍（`grep thread_local!` 于 `src/L13_namespace/**`，13 处）：

| 位置 | 类型 | 是否持参考域 Rc | 推池前是否清 |
|---|---|---|---|
| `mod.rs:162 FORCE_MEMO` | `RefCell<FxHashMap<usize,(Rc<Val>,Rc<Val>,u64,u64)>>` | **是** | ✓ `:3842 force_memo_clear()` |
| `mod.rs:1189 DECLB_CACHE` | `RefCell<Option<(usize,Rc<Decl>)>>` | **是** | ✓ `:3843 declb_cache_clear()` |
| `unification.rs:24 TRAIT_METAS_SNAP_POOL` | `RefCell<Vec<Vec<MetaVar>>>` | 否（索引） | 不适用 |
| `pattern_match.rs:71 PROBE_COUNT` | `Cell<u64>` | 否 | 不适用 |
| `mod.rs:277 PROF_STACK` | `RefCell<Vec<u64>>` | 否 | 不适用 |
| `mod.rs:3746-3749 PRELUDE_CACHE(_NO_HDL)` | `PreludeSlot`（本槽自身） | — | 推池者 |
| `parser/mod.rs:198`、`bump_spine_iter.rs:200`、`bump_spine_iter/{entry,force×2,typeclass,machine}` | 孪生侧计数/表 | 否（bump 键 `V`） | 见 §4.2 |

再加两条编译期事实：`Infer` 含 `Rc<Val>`/`Rc<Decl>`/`Rc<RwLock<..>>` ⇒ **`Infer: !Send`**（自动），
所以 `Infer::clone` 的结果**不可能**跨线程（`tests`/`observe.rs` 的克隆都在本线程栈上）；跨线程传输的
唯一通道就是 `PoolState`（`Mutex<Vec<PoolState>>` 提供 happens-before）。⇒ A4 未展开的这条 SAFETY
**在当前修订成立**，"清两缓存 + 独占所有权"两条件齐备。

### 3.2 [确认] `mutable_map` 的 `RwLock`：无写者饥饿/竞态；A1 修的自死锁我未找到新路径

- **并发面**：`mod.rs:1367 mutable_map: Rc<std::sync::RwLock<HashMap<String, Rc<Val>>>>` 挂在 `Infer`；
  `Infer: !Send`（§3.1）⇒ `Backend`（`lib.rs:361`，含 `hover_table: DashMap<String, Infer>`）也 `!Send`
  ⇒ `Arc<Backend>` 不可跨线程；唯二的 `thread::spawn`（`lib.rs:4087/4106`，`stdio-monitor` 特性）
  只搬 `crossbeam_channel` 的收发端与 `Arc<AtomicU64>`，**不碰 Backend**。⇒ 同一 map 不存在两个线程
  同时 read/write ⇒ **没有写者饥饿问题**；`read()` 化的唯一残余风险是"同一线程内 read 守卫未释放时再
  write"的自死锁（RwLock 不可重入）。
- **我抽查的自死锁路径**（都干净）：
  - `take_check_issues`（`:4221-4238`）：read 在**块作用域**内结束（`:4223-4231`），随后才 `write()`（`:4233`）✓；
  - `take_fresh_check_issues`（`:4262-4289`）：同样分块（`:4266-4274` / `:4283-4286`）✓；
  - `:2289 if let Ok(map) = self.mutable_map.read()`（detail/size 报告路径）：then 块只 `walk_val` 遍历值图，
    **不写** ✓；顺带一句：这里用 `if let Ok(..)` 而非 `unwrap`，锁 poisoned 时静默跳过 mutable 面
    （只影响 TYPORT_* 诊断输出，可接受，仅记录）。
- **与孪生的对照**：孪生用 `RefCell<Mutable>`（无并发面）且**从不跨线程**（无池化；`TWIN_RESIDENT` 是线程局部）。

### 3.3 [确认] 孪生 `prim.rs` 不存在参考版那类"持锁调回调"重入（Lead 点名的问题）

- `ReportCheckIssue`（`prim.rs:555-566`）：`borrow_mut()` 用 `drop(m)` 显式结束在返回前 ✓；
  `CheckCombCycles`（`:1003-1012`）作用域内只写行集、无回调 ✓。
- `ChangeMutable`（`:597-611`）/`ChangeMutableDefault`（`:642-655`）：顺序是
  **读 → `copied()` 拷出 → 借用结束 → `vapp1`(回调) → 再 `borrow_mut()` 写回** ⇒ 回调期无借用 ✓
  （这正是 A1 在参考版修掉的那类自死锁的对偶面，孪生天然没有）。
- `GetGlobal`（`:619`）/`GetGlobalDefault`（`:626-633`）/`CreateGlobal`（`:587`）：借用都是**语句级临时** ✓。
- `StringToGlobalType`（`:569-578`）：把 `&RefCell<Mutable>` 传进 `eval_iter`，自己不持借用 ✓。
- def-replay：`def_needs_replay`/`scan_def_replay`（`:123-172`）与 `eval.rs:284-290` 都是"传 `&RefCell`
  而非借用守卫"的风格 ✓。
- **一处需要注释级固定（P3 级、属 A2 的 `prim.rs`）**：`tm_scan_global_ops:193`
  `if let Some(m) = mutable.borrow().replay.get(*x) { … } else { … borrow_mut() … }` ——
  **then 块里仍持有读借用**（edition ≤2021 的 `if let` 临时作用域规则），当前 `borrow_mut()` 在 **else 块**
  （`:215`），而本 crate 是 **edition 2024**（BRIEF §1）⇒ else 前借用已释放，**安全**。
  但这一安全依赖"edition 2024 的 if-let 临时作用域收紧"这条不显眼的规则；建议在 `:193` 上加一句
  "注意：`borrow_mut` 必须在 else 侧（2024 的 if-let 临时作用域）"，否则未来把写操作挪进 then 块
  会立刻 `already borrowed` panic。

### 3.4 [确认] A4 对 `test_n6_checked_ret_cache_unsoundness` 的判定（`a4-r1.md` §2 P3）

- 全仓 `grep checked_ret`：只命中 `mod.rs:7799/:7806/:7812`（N6 测试自身的注释）与
  L10/L11/L12 的模块文档（`L10_typeclass/bump_spine_iter.rs:59`、`L11_macro/bump_spine_iter.rs:47`、
  `L12_canonical/bump_spine_iter.rs:69`）——**L13 参考版与孪生版都没有该缓存**。
- L13 参考版的臂循环对**每条臂**无条件调 `check_pm_final`（`pattern_match.rs:516-532`，失败臂
  `:525-531 push err` 后 `continue`）⇒ 原"按 idx 缓存跳过 body 检查"的机制不存在 ⇒
  A4 的"确定性结论（当前不可达）"**成立**；N6 的断言只判 `Err`（粗粒度）也如 A4 所述。
- **孪生侧补充**：`bump_spine_iter/compiler.rs` 也没有同类跨臂缓存——只有 per-match 的
  可达性探测 memo（`compiler.rs:259-274`，`constrs` 与 `memo` 都在同一次 match 编译内）与
  `case_spans_memo`（`:99-111`，键 = Sum 名，纯 span 渲染缓存）⇒ 两版同判，
  **N6 家族在孪生侧同样不可达**。

### 3.5 [确认] `preprocess` 的等字节长不变量：由构造保证（A4 的 needs-verify 是行为面而非长度面）

- 不变量：`mod.rs:4382` 注释 + `:4470 debug_assert_eq!(out.len(), s.len())`。
  逐分支核对：`emit_blanked`（`:4388-4401`）对非空白 char 写 `c.len_utf8()` 个空格、空白/`\n` 原样；
  `emit_raw`（`:4404-4444`）的 `//` 写 `"  "`（2 字节）、`/*`/`*/` 各写 2 字节（`:4456/:4464`）⇒
  **每个输入字节恰好对应一个输出字节**，对任意 UTF-8 输入成立。
- 字节边界安全：`emit_raw` 里按**字节**找 `/`（`:4428`）只在 ASCII 0x2F 上切；UTF-8 续字节 ≥0x80
  ⇒ 不会切在 char 中间；`line_blank` 分支的 `region[j..].chars().next().unwrap()`（`:4409`）
  依赖 `j` 始终在 char 边界（由 `j += c.len_utf8()` 与 ASCII 分支维持）✓。
- ⇒ A4 报的"字符串字面量里的 `//` 被吃掉"是**行为**面（`:4421` 不看是否在字符串内），与长度不变量无关；
  我同意其处置（**不盲改**：需全语料字节级差分 + LSP 面回归）。**并且它不是 parity 裂缝**：
  两版引擎共用同一个 `preprocess`（孪生 `bump_spine_iter/entry.rs` 的 `parse`/`run_input` 调
  `super::preprocess`，参考版 `mod.rs` 自带同名函数但输入相同）⇒ 同一输入两版得到同一预处理文本。
  若要修，应同时改所有副本（L06-L13 各一份，本仓"修一漏三"的老风险）。

## 4. 交叉提示（不属 A4 缺陷，供 Lead 归口）

1. **`#[path]` 二次编译与 `debug_assert`**：`mod.rs` 的 `debug_assert_eq!` 只在开启
   `debug_assertions` 的目标里生效（`cargo test`/`--all-targets` 的 debug 构建 ✓；release 二进制里关闭）。
   因为不变量由构造保证（§3.5），这不构成风险；但请注意 `src/bin/*bench*.rs` 用 `#[path]` 交叉编译
   L04–L12 的**副本**，其中 `preprocess` 也有各自的 `debug_assert`——**修任何一份都要同步其余副本**，
   否则"某副本修了、其他没修"的分叉会重新出现（BRIEF §8 的头号风险）。
2. **换 arena / 线程交接的失效清单应统一**：`compact_state`（A2 的 `compact.rs:593-638`）换掉
   `self.bump` 后必须失效的**指针键缓存**，目前散在调用方（R1 我在 `entry.rs` 三个 prime 调用点补了
   `ns_method_cache`；`compact_resident` 早已自己清）。孪生侧同族还有
   `bump_spine_iter/force.rs:250 TWIN_DECLB_CACHE: RefCell<Vec<(usize,usize,Rc<Decls<'static>>)>>`
   （`Rc<Decls<'static>>` 指向 bump，靠 `force_memo_clear()` 在每个 `bump.reset()`/换 arena 前清——
   我 R1 已核 7 处 reset 全部紧跟 `force_memo_clear()`；prime 的两处压实前也先清）。建议与 §2.1 合并成
   一个入口（`pool_handoff_clear()` / `arena_swap_clear()`），把"清单"变成代码而不是注释。
3. **A4 R1 未覆盖的正面结论**（供 A4 写 R2 时引用）：`unsafe impl Send`（§3.1）与 `mutable_map`
   并发面（§3.2）这两块在 `a4-r1.md` 里只是"记录/无发现"，本文给出了证据链，可直接并入。

## 5. 设计决定讨论（只记录）

- `Rc<RwLock<HashMap<..>>>` 在一个 `!Send` 的 `Infer` 里，`RwLock` 实际只承担"可共享的内部可变性"
  （与孪生的 `RefCell` 同角色）。若将来把 `Infer` 改成可跨线程（例如 LSP 多线程化或 prelude 池化更激进），
  `Rc` → `Arc` 的替换会同时引入**真正的**锁竞争与 `Rc<Val>` 值图的跨线程计数问题
  （§3.1 的 SAFETY 论证将不再成立），届时必须整体重新设计（值图改 arena/immutable + `Arc`）。
  这一条建议写进 `Infer` 的字段文档，避免有人只改 `Rc`→`Arc` 就以为安全。
