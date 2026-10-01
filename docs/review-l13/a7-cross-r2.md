# A7 Round2 (Cross) — A1 切片只读审计（L13 参考版语义核心）

> 交叉审计对象：A1 的 `src/L13_namespace/{elaboration,cxt,pattern_match,canonical,pretty,syntax}.rs`、
> `{calc_tests,class_tests}.rs`；依据 `docs/review-l13/a1-r1.md` 与工作树现状（HEAD `350b35a` + 各 agent 改动）。
> **本报告为只读审计，未改 A1 的任何文件**（BRIEF §5：交叉发现由 orchestrator 转交所有者）。
> A7 的独特视角：我是 `src/lib.rs`（`Arc<Backend>` / LSP 宿主）的 owner ⇒ 重点查
> **A1 把 `get_global` 从 `write()` 改 `read()`、把 `change_mutable*` 改成"释放锁再回填"之后的并发/重入后果**。

## 1. 结论（verdict）

- **交叉发现：P0 0 / P1 0 / P2 0 / P3 1 / needs-verify 2。**
- **A1 的 P0 修复（`change_mutable*` 自死锁）复核结论：成立、最小、且未引入竞态或写者饥饿**（详见 §2.1）。
  TOCTOU（两个调用者各读旧值再回填 ⇒ 丢更新）在本仓的并发模型下**类型级不可达**（§2.2）。
- A1 的 determinism 修复（`BindingName.mk` 字典序最小）：**生产路径（LSP/CLI，HDL prelude 已装载）上不可达**，
  因此 A1 §4.4 担心的"与快版取值不同"在生产上不成立（§2.3，needs-verify 低风险残留）。
- 未发现 A1 引入新的 panic/死锁/静默错判；他们的两条自留 needs-verify（宇宙漏算、`update_by_cxt` 的 `U(0)`）
  我按机制复核**成立**，可达性问题我也没有独立反例（与 A1 自评一致）。
- 收敛判定（交叉侧）：**无 P0–P2 需 A1 返工**；§2.4/§2.5 两条 needs-verify 各需一次实验，用于关闭 A1 的悬项。

## 2. 发现列表

### 2.1 [复核通过] `change_mutable*` 的锁纪律修复：确实消灭了唯一一类"锁内求值用户回调"，且无残留同族点

- 位置（A1 改动）：`src/L13_namespace/cxt.rs:718-739`（`change_mutable`）、`:846-864`（`change_mutable_default`）、
  `:753`（`get_global` 的 `write()`→`read()`）。
- 我独立做的四步核对：
  1. **全文件锁点枚举**（`grep '\.write()|\.read()' src/L13_namespace/cxt.rs`）：
     `:384`（`push_check_issue`）、`:709`（`create_global`）、`:731`/`:857`（修后回填）、
     `:728`/`:852`（修后取旧值）、`:753`/`:769`（只读 prim）。
     逐点看锁内代码：`:384` 只做 `format!` + `get` + `insert`（纯数据）；
     `:709` 只 `insert`；`:731`/`:857` 只 `insert`；`:769` 的读守卫只覆盖
     `map.get(..).cloned().unwrap_or_else(|| args[1].clone())`（`Rc` 克隆，无 `v_app`）。
     ⇒ **`v_app` 的三处调用（`:730`、`:854`、`:839-841`）现在都在锁外**，这正是快版的口径。
  2. **同族点搜索（本仓头号风险"修一漏三"）**：`v_app` 在 `cxt.rs` 内只出现在上述三处；
     `mutable_map` 的其余写者（`lib.rs:1337/1951/2577` 的 `clear()`、`mod.rs:4098/4233/4283` 的
     `insert`、`mod.rs:4190/4205` 的克隆/替换、`mod.rs:2289`/`:4223`/`:4266` 的只读遍历）
     全部是**纯数据操作**，没有一个在锁内存活期间再进入用户代码 ⇒ A1 的修法覆盖了整类。
  3. **与快版逐行对照**（parity 关键）：快版 `bump_spine_iter/prim.rs:591-614` 是
     `let old = mutable.borrow().map.get(name).copied();`（临时守卫、语句末即释放）
     → `vapp1(...)`（无守卫）→ `mutable.borrow_mut().map.insert(k, nx)`；
     `:635-660` 的 `ChangeMutableDefault` 同款（`Some→vapp1→insert`、`None→insert(default)`）。
     缺键时两版都**不调用**回调 ⇒ A1 的 `if let Some(old) = old { … }` 与快版逐分支同判
     （`cxt.rs:729` vs `prim.rs:598`；`cxt.rs:853-856` vs `prim.rs:643-659`）。
     `GetGlobal`：快版 `mutable.borrow()`（`prim.rs:619`）＝ A1 改后的 `read()`（`cxt.rs:753`）⇒ 口径统一。
  4. **行为差异边界**：旧实现是 `x.get_mut(k)` 后 `*x = v_app(..)`（原地替换），新实现是
     `insert(k, next)`。对**已存在的键**两者结果相同（`HashMap::insert` 只改值、key 集合不变 ⇒
     迭代序不变，输出稳定性不受影响；`old` 只是 `Rc<Val>` 克隆，无深拷贝成本）。
- 结论：修复**语义等价 + 消除死锁 + 提升与快版的纪律一致性**。唯一副作用见 §2.6（正向）。

### 2.2 [复核通过] "换成读写竞态/丢更新"这一担心**类型级不成立**；且 LSP 无并发分析路径

Lead 的问题："`get_global` 从 `write()` 改 `read()` 在 LSP 并发模型下是否引入读写竞态或写者饥饿？
`change_mutable` 释放锁再回填是否引入 TOCTOU（丢更新）？"——我的结论：**都不成立，且不是靠约定，而是靠类型**：

1. **`Infer` 根本不是 `Send`**：`src/L13_namespace/mod.rs:1367`
   `pub mutable_map: Rc<std::sync::RwLock<HashMap<String, Rc<Val>>>>`（另有 `def_replay_memo: Rc<…>`）。
   `Rc<T>` 既非 `Send` 也非 `Sync` ⇒ `Infer: !Send + !Sync` ⇒ `Mutex<Infer>` 不能是 `Sync`
   ⇒ `Arc<Mutex<Infer>>: !Send + !Sync` ⇒ **`Backend<C>` 无法跨线程传递或共享**（`src/lib.rs:67`
   用的就是这个 `Infer`）。第二个线程连这把 `RwLock` 都**拿不到**：跨线程读写竞态在类型层面不可能发生，
   "写者饥饿"同理（无第二个读者）。
2. **进程内确实只有一个分析线程**：`src/lib.rs` 里 `std::thread::spawn` 只出现在
   `:4087`/`:4106`（`#[cfg(feature = "stdio-monitor")]` 的 LSP 报文代理，只搬运 `Message`，
   不碰 `Backend`）；原"分析 worker 线程"已被删除并改为**主循环内联排水**
   （`drain_analysis_jobs`，`:1787-1795` 的文档注释原文："Previously a dedicated worker thread
   drained this queue; running it on the main-loop thread after every dispatched message is
   equivalent …"），`pending/processing/processed_signal` 只保留记账语义（`completion_at` 的等待
   已退化为 no-op）。CLI（`typort check/emit/doc/build/test`）与各 bench 也都是单线程串行。
   —— 这也是 `lib.rs` 敢把孪生常驻状态放 `thread_local!(TWIN_RESIDENT)`（`:328-331`）的前提：
   **单线程不是约定，是当前架构的硬不变式**（否则每个线程会各持一份孪生会话，共享 `cxt`/`infer` 直接失配）。
3. **TOCTOU 因此不可达**：丢更新需要"两个并发调用者"。同线程内唯一能制造"读到旧值后状态被改"的形态是
   **回调重入**（`x => change_mutable(k, …)`、`x => create_global(k, …)`），而那正是：
   - 旧实现：**自死锁**（写守卫存活时再取写锁）⇒ 没有任何既有程序依赖旧行为；
   - 新实现：内层先写、外层 `insert` 后写 ⇒ **后写胜**，与快版（§2.1 第 3 点）**同序**，即 parity 更紧。
   所以这不是"把死锁换成竞态"，而是"把死锁换成与快版一致的确定语义"。
4. **`read()` 相对 `write()` 的风险方向是重入，而非并发**：`std::sync::RwLock` 不可递归；
   同线程"持写守卫再 `read()`"会死锁——但 §2.1 第 1 点已证明**没有任何点在持写守卫时进入用户代码**；
   "持读守卫再 `read()`"在同线程且无排队写者时是安全的，而单线程不可能出现排队写者。
   另外栈式 `read()`（`get_global` 的临时守卫）比旧 `write()` **严格更宽松**：旧码在"回调里被 `get_global`
   读同一张表"的形态下必然死锁，新码只在"真的有人持写守卫跑用户码"时才死锁，而那种点已经不存在。
5. 顺带一个**正向**副作用：旧实现下回调 panic 会在锁内发生 ⇒ `mutable_map` 被 **poison**，
   之后 `get_global`（`.read().unwrap()`）与 `take_check_issues`（`:4223`）会连环 panic；
   新实现把回调移出锁外 ⇒ 用户回调 panic 不再污染这张表（`create_global`/`push_check_issue`
   的锁内代码对任意用户输入都不会 panic）。这条与 A7 在 `src/lib.rs` 修的"崩溃可见化/锁中毒"是同一纪律。

### 2.3 [needs-verify，低风险] `BindingName.mk` 的 `min_by` 改动在生产路径不可达 ⇒ 与快版的分歧不成立

- A1 的改动：`elaboration.rs:212-224`（`insert_go`）与 `:2557-2569`（接收者隐式参数展开）两处同款，
  把 `cxt.decl.keys().filter(|k| k.ends_with(".BindingName.mk")).find(..)` 改为 `.min_by(字典序)`。
- 我补的**可达性**分析（A1 未给，§4.4 留了个"取值可能不同"的口子）：
  两处都是 `if cxt.decl.contains_key("BindingName.mk") { 精确键 } else { 限定名兜底 }`。
  而 HDL prelude **在文件顶层**声明了这个结构（`src/prelude/hdl/hdl-core.typort:12 struct BindingName {…}`，
  该文件无 `package` 头）⇒ 只要 HDL prelude 装载，`cxt.decl` 里就必然有**精确键** `BindingName.mk`，
  兜底分支**不会被走到**。LSP 与 `typort check/emit` 都走 `load_prelude()`（全量），
  只有 `load_prelude_skip_hdl()`（部分单测/`--no-hdl`）与"用户 `package p` 里再声明 BindingName"
  的组合才可能让精确键缺失而存在 `p.BindingName.mk`——此时若存在 **2 个以上**前缀不同的限定键，
  参考版取字典序最小、快版取登记序首个（`bump_spine_iter/machine.rs:919-923`），二者可能不同。
- 处置：仅报告（needs-verify）。**生产路径无分歧**；若要彻底关掉这个口子，建议两侧统一规则
  （快版的"精确键优先 + 登记序"更贴近"先声明的赢"，但参考版没有登记序可用 ⇒ 也许统一成都取字典序最小更省事），
  属 A1/A3 的设计决定，不在本报告处置范围。
- 另：A1 把"确定性"写进注释是对的（BRIEF §3.4 的哈希序泄漏是实打实的输出不稳定面）；
  这一改动**只影响多候选**，0/1 候选时逐字不变（我核对了 `.min_by` 对 1 个元素的返回就是该元素）。

### 2.4 [needs-verify] A1 的宇宙漏算（`elaboration.rs:1399-1405`）：机制复核成立，可达性我也没有反例

- 机制（A1 §2 第 2 条）我逐行核对**成立**：`:1381` `let mut universe_lvl = 0;` 只被
  `:1382-1398` 的参数域扫描与 `:1399-1405` 的 case 字段扫描抬高，而后者用的 `cxt` 尚未绑定枚举参数
  （参数 Π 折叠在 `:1417-1432`/`:1440-1442`）；`check_universe` 对引用参数名的字段返回 `Err`
  并被 `if let Ok(..)` 静默吞掉 ⇒ 该字段贡献 0。后面 `:1492` 用绑定好参数的 cxt 重算等级却**丢弃**结果
  （`let (typ_tm, _) = …`），确实存在"算了不用"的可疑形态。
- 但**可达性=能否真造出宇宙逃逸**我没能独立判定（Lead 两次构造都卡在更早的声明失败，A1 已据此撤回 P1）。
  我同意 A1 的处理：不盲改（改法会让已接受的语料等级整体上移，必须整仓背书），
  且该段与 `L12_canonical/elaboration.rs:539-545` 同构 ⇒ 属跨层同族，应一次统一。
- 需要的一次实验（与 A1 §4.3 相同，我复述成最小口径）：把
  ```typort
  def T5 : Type 6 = Type 5
  def Box [A : Type 0] : Type 6 = T5
  enum Poly [A : Type 0] { mk(x: Box[A]) }
  def leak : Type 0 = Poly[Nat]
  ```
  喂给 `run_with_prelude`，看 `leak` 是否被接受；同时跑对照组 `enum Poly2 { mk(x: T5) }` ⇒ `leak2` 必须被拒。
- 若判定为"接受"，我的补充意见：修法不必"整体上移"——可以在字段扫描前用一个**只含参数 binder 的临时 cxt**
  单独算等级，再与结果等级取 max（不动 `Raw::Sum` 的其余语义），但这仍要全量测试背书，属 A1 排期。

### 2.5 [needs-verify] A1 的 `update_by_cxt` 的 `U(0)` 占位：我认同"不盲改"，但建议加一条**可观测性**探针

- 位置：`syntax.rs:53-67`（`Locals::Define` 的第三字段写成 `Val::U(0)`；`:61` 有注释掉的 `quote(v)`）。
- 交叉补充：A1 说的 panic 风险来自 `lvl2ix`（`mod.rs:1126`）在 v 越界时 `panic!`，
  而 `U(0)` 替换正是 `40a0243` 为躲它做的。我的补充：这条一旦真被触发，表现是**静默**错误的 meta 类型，
  没有诊断出口（不像 §2.4 至少有"漏算等级"可对照）。建议在 `fresh_meta` 的路径上加一个
  `debug_assert!` 或用现有 `TYPORT_*` 环境变量门控的探针（例如 `TYPORT_PROBE_LOCALS_U0=1` 时打印一次回溯），
  让"是否真的有人走到这条路"可测 —— 属下一轮可做的小事，不是本轮缺陷。

### 2.6 [P3，正向记录] 锁纪律应该写进 `cxt.rs` 模块头（防止下次又在锁内求值）

- 位置：`src/L13_namespace/cxt.rs:1-30`（模块头）与 `:718-727`、`:848-851` 的新注释。
- A1 已经在两个函数上写了完整的事故说明（很好），但**模块头没有锁纪律**；本仓的复现率很高
  （L06/L07/L08/L11/L12 各有一份 `cxt.rs` 拷贝，`L11_macro/cxt.rs:55/68/88`、`L12_canonical/cxt.rs:46/58/77/86`
  仍是旧的持锁形态——它们是旧层、不在本次范围）。建议在 L13 模块头加一句
  "`mutable_map` 的守卫只允许覆盖纯数据操作；任何进入用户代码（`v_app`/`eval`）的调用必须先释放守卫"。
- 处置：仅报告（A1 的文件；且属注释级改动，由 orchestrator 转交）。

### 已核对、未发现问题的项（A1 切片）

1. **`get_global` 的语义**：缺名仍返回 `None`（卡住），与快版 `GetGlobal`（`prim.rs:615-620`）同判；
   `.read().unwrap()` 的 poisoning panic 在新锁纪律下已无用户可达来源（§2.2 第 5 点）。
2. **`change_mutable*` 的缺键分支**：`change_mutable` 缺键不调回调（同旧码、同快版）；
   `change_mutable_default` 缺键写 default（`cxt.rs:853-856` 同 `prim.rs:657-660`）。
3. **`canonical.rs` 的 8 个导入删除**：我独立 grep 了 `Ty/VTy/Locals/Closure/Ix/Spine/close_ty/MetaVar`
   在 `canonical.rs` 内的出现次数（各 1 次，即导入行自身）⇒ 删除无风险；IDDFS 的 `+= 1` / `<=`
   与 `L12_canonical/canonical.rs:19-28` 同构（A1 §2.5 的结论我复核成立）。
4. **A1 新增的 P0 回归钉**（`class_tests.rs:755-805`）：看门狗线程 + `recv_timeout(180s)`，
   回归时**失败而非挂死门禁**；被阻塞的 worker 持有的是自己那份 `Infer` 的锁（不污染其它用例），
   进程退出时随主线程终结 ⇒ 设计正确。唯一成本：真回归时该用例要占 180s（可接受，且注释已写明）。
   它同时被 `tools/gate_l13.sh` 的 `--lib L13_namespace::` 覆盖 ✓。
5. **A1 未改动 `pattern_match.rs`/`pretty.rs`/`syntax.rs`**（除 §2.5 的既有 `U(0)`）：其 R1 报告里的
   穷尽性/`covers`/`is_catch_all` 正向结论我没有发现反例（只做了抽样复核：`:464-476` 的
   "可达性探测 ∧ 无臂覆盖"、`:730-747` 的兜底口径）——完整复核归 A1，本报告不重复计入结论。

## 3. 本轮改动清单（交叉审计方）

- **无**。按 BRIEF §5，交叉发现不得直接改对方文件；`§2.3/§2.4/§2.5` 三条均为 only-report/needs-verify。

## 4. 需要 orchestrator 处置的事项

1. **A1 的两条 needs-verify 需要实验**（不是改动）：
   a. `§2.4` 的 `Poly/Box/T5` + 对照 `Poly2` 一次运行即可判定宇宙漏算可达性；
   b. `§2.5` 若要观测 `U(0)` 路径，需要一个环境变量门控的探针（可让 A1 在下一轮加）。
2. **A1 的 P2 `check_universe` `unreachable!`（`elaboration.rs:646`）与快版 `machine.rs:1796` 同族**：
   若决定硬化，一处改两版（A1 已写在他们的 §4.4），我复核该 `unreachable!` 确实在
   `Val::Flex` 分支对"已解 meta"触发，而 `force` 的 fuel 门（`mod.rs` 的 `burn_fuel`）能造成该形态 ⇒ 机制成立。
3. **跨副本同族点（不在本次范围，仅记录）**：`L11_macro/cxt.rs:55/68/88`、`L12_canonical/cxt.rs:46/58/77/86`
   仍是"持写守卫 + 可能的用户代码"旧形态（这两层未在本轮评审范围，且 L11 的 `:88` 甚至有
   `.write().unwrap().get(..).unwrap()` 双重 unwrap）。若将来 L11/L12 也要"完美化"，这是同一颗雷。
4. **`tools/gate_l13.sh` 未覆盖**：A1 的看门狗回归钉在 `--lib` 里 ✓ 已覆盖；但**本仓没有"锁纪律"静态门禁**
   （例如禁止 `mutable_map.write()` 作用域内出现 `v_app`/`eval`），同类事故只能靠 review 发现。

## 5. 设计决定讨论（不属 bug，只记录）

1. **"修死锁 → 换成竞态"的通用判据**：本案的答案是"先问这把锁是不是跨线程原语"。
   `mutable_map` 的 `RwLock` 在类型上（`Rc` ⇒ `!Send`）就不可能跨线程，它的历史用途是
   "跨 `Infer` clone 共享 + 单线程内的重入保护"。因此正确的问题是**重入语义**，不是 TOCTOU。
   把这个判据写进本仓文档（哪个锁承担哪种职责）比逐个函数加注释更省事。
2. **释放锁再回填的语义选择**：A1 选了"后写胜（外层覆盖内层）"，与快版一致。
   另一种可选语义是"内层写生效、外层放弃回填"（CAS 风格，比较取出的 `old` 是否仍是当前值）。
   在本仓语境下 A1 的选择是对的——因为**必须与快版逐字同判**，而快版没有版本号可比。
   记录理由：这里"后写胜"不是随手选的，是 parity 驱动的最优解。
3. **单线程不变式值得一条编译期保险**：`Arc<Backend>` 目前靠 `Infer: !Send` 被动阻止跨线程。
   若哪天有人把 `mutable_map` 换成 `Arc<RwLock<…>>`（为了"以后上多线程"），
   这把锁会立刻从"重入保护"变成"真并发原语"，本节所有结论失效。建议在 `Backend` 上留一句
   doc comment 说明"不得改成 `Send`"，或加 `static_assertions` 风格的 `fn _assert_not_send<T: ?Sized>()`
   自检（属建议，不在本轮改动内）。
