# L07_sum_type 四角度代码评审（2026-09-18）

**评审对象**：`src/L07_sum_type/`（约 1.5 万行；参考版分文件 + 孪生版 `bump_spine_iter.rs` 8124 行），以当前工作树为准（L07 文件 mtime ≤ 16:01，评审期间无变动；`cargo check --lib` 绿色，L07 lib 测试 48/48 通过）。

**评审方式**：4 个独立评审视角（性能 / 正确性 / 代码风格 / 类型论）。前三个完成完整报告；正确性评审在收尾的 fuel 深度探针阶段被会话中断，其全部中间结论（含 15 组黑盒探针实证）从 `~/.zcode/cli/rollout/` 的 model-io 记录还原，关键论断已由主 agent 逐条对码复核（`mod.rs:511`、`unification.rs:606/186/257`、`pattern_match.rs:153-158`）。探针文件保留在 `tests/zz_review_l07.rs`（可编译，10 个用例含 `zz_nested_coverage_gap` / `zz_stale_solvable_*` 复现钉）。

---

## 〇、执行摘要

| 视角 | 结论 | 最重要发现 |
|---|---|---|
| 类型论 | 核心机制干净自洽，**外壳有洞** | **P0：嵌套模式覆盖检查完全缺失**——非穷尽 match 被静默接受、运行期卡死 |
| 正确性 | 回归全绿，但实证两个 P1 | **臂序影响可达性判定**（推翻代码注释的等价性声称）+ **fuel 耗尽 panic 窗口**（三处 `unreachable!()`） |
| 性能 | 孪生版接近最优；参考版有结构性分配族问题 | `closure_apply` 每次 β **深拷贝整个闭包体**（6 个热站点同族），是 basic vs fast 15× 差距主因 |
| 风格 | B（良好，局部需整改） | **vsub_reclaim 泄漏修复只落了 L07，同构的 L08–L12 未同步**；8124 行单文件应拆目录 |

**跨角度交汇的三个修复主题**（详见文末路线图）：
1. 嵌套覆盖缺失 = 类型论 P0 = 正确性实证 P0，双实现（参考/孪生）共有；
2. fuel 降级机制的两面：probe 侧开 unsound 口（类型论 P1-2）+ solve 侧 panic 窗口（正确性 P1），同一机制应一起修；
3. 陈旧 solvable 污染 = 正确性臂序实证 = README §7.4 probe/臂不同步的具体实例。

---

## 一、类型论评审（完整）

**方法**：全文精读 + 15 组黑盒探针实证（临时集成测试，已清理）。基线 `cargo test --lib L07_sum_type` 48/48 通过。

### P0-1 嵌套模式的覆盖检查完全缺失：非穷尽 match 被静默接受，运行期卡死

- **位置**：`pattern_match.rs:103-112`（覆盖检查只遍历**顶层** scrutinee 类型的构造子）、`pattern_match.rs:616-621`（`covers` 只看模式顶层名字）、`pattern_match.rs:456-469`（嵌套 `Con` 子模式递归 `walk_con`，无任何覆盖探测）；运行期卡住在 `pattern_match.rs:550-612`（`eval_aux` 返回 `None`）。
- **实证**：
  ```
  enum P { mk (a: Bool, b: Bool) -> P }
  def f (p : P): Bool = match p {
      case mk(true, true) => true
      case mk(false, false) => false
  }                     // ← 编译通过，零报错
  def probe : Bool = f (mk true false)
  println probe         // ← 打印卡住的 match（无规范形）
  ```
  带索引版本同样通过：`match v { case cons(x, cons(y, ys)) => x }`（单臂）在具体值上打印卡住 match。
- **理论论证**：Cockx–Abel 覆盖性定义在案例树上：每个构造子节点的每个子字段仍需递归覆盖（README §1.1 自己引用的正是这套理论）。本实现是"逐臂独立下钻 + 仅顶层 probe"，嵌套 `Con` 字段位置的可达性从未被枚举。后果：(1) 接受非法项；(2) 正则性（canonicity）破坏——封闭项无规范形；(3) 卡住 match 是中性值，用户看到的是"函数不归约"而非报错。
- **建议**：在臂走查的每个 `Con` 字段绑定处对字段类型的每个构造子跑一次与顶层同款的 `probe_accessible`，要求子模式集（含缺省通配与后续臂并集）覆盖全部可达构造子——把覆盖检查从"顶层一次"改为"沿模式下钻逐节点"。这也是向真正案例树编译（split tree）过渡的最小步。补 `mk(true,_)` 型嵌套覆盖正负例测试（现有测试只覆盖顶层）。修复面估计 100 行以内。

### P1-1 enum 构造子返回类型无良构性检查（可注册"外部类型构造子"）

- **位置**：`elaboration.rs:283-297`（构造子类型构造，对 ret 无约束）、`elaboration.rs:340-360`（检查恒真）。
- **实证**：`enum Foo { c -> Nat }` 通过；`def g (n : Nat) = match n { zero/succ }` 在 `g c` 上卡死——对 Nat 的**覆盖检查完备的** match 在封闭输入上卡死。参数非一致（`enum Foo[A] { c -> Foo[Bool] }`）也被接受。
- **论证**：归纳类型形成规则要求构造子 ret 以本类型为头、参数一致（仅索引可特化）。本层只查 `ret : U`，向构造子名字空间注入"类型正确但永不匹配"的 phantom 值。未找到升级为证伪等式的通路（refl 上 SumCase 异名 ctor 直接 Err），定 P1。
- **建议**：注册前检查 ret 的 WHNF 是 `Val::Sum` 且名字等于本 enum、隐式参数位逐位等于枚举参数（参数一致性），显式索引位任由特化（GADT 保留）。

### P1-2 fuel 耗尽使 probe 误判构造子"不可达"→ 覆盖检查放过该构造子（unsound 方向未在 README 披露）

- **位置**：`pattern_match.rs:172-239`（unify 失败——包括 fuel 耗尽——一律 `false`）、`pattern_match.rs:103-108`（`false` ⇒ 不要求覆盖）。
- **论证**：README §7.2 只承认了"把合法臂误判为不可达"（拒绝合法程序）方向；probe 侧方向相反：fuel 不足 → 方程失败 → 判不可达 → 覆盖检查不再要求它 → **非穷尽 match 被接受**。2026-09-17 起每个 ctor 探测独立充值（`pattern_match.rs:198`）已收窄窗口，但方向仍在。
- **建议**：`probe_accessible` 失败时区分 `infer.fuel_exhausted()`：fuel 耗尽按"可达但未知"处理（保守要求覆盖或报"预算耗尽"）。一行改动把降级从 unsound 翻到 incomplete。

### P1-3 `unify` 的 SumCase 臂只比 `case_name` 不比 `typ`——构造子身份判据不足

- **位置**：`unification.rs:938-961`；对照 `pattern_match.rs:572-576`（eval_aux 用"typ 的 ctor 名单 + case_name"双条件）。
- **论证**：跨 enum 重名构造子（README §2 明言允许共存）下 `E1.c` 与 `E2.c` case_name 同、typ 不同，unify 判相等。未构造出黑盒 exploit（方程先经齐型关卡挡下），但健全性论证是间接的（依赖"每个喂给 unify 的方程都齐型"这一未被检查的不变式），而 P1-1 恰证明此类前提不总成立。
- **建议**：SumCase 臂增加 typ 的 Sum 头名字相等检查（不必比值）；开销为零，把健全性从间接不变式变为局部可判定。

### P2 / P3（摘要）

- 空 enum 不可声明（parser `many1_sep`）：本层无 Bot/Void，不可能分支只能靠索引冲突表达；建议支持零构造子 enum（覆盖检查天然正确处理）。
- `U : U`、无严格正性、无终止检查：与上游教程层一致的已知取舍，建议 README "已知限制"与 K 并列明示（探针证实 `enum Bad { mk (f: Bad -> Bad) -> Bad }` 接受）。
- 期望类型 meta 跨臂保留 / probe 与臂内层级可能不同步：README §7.1/§7.4 已诚实披露，复核机制属实，均为 incomplete 方向，维持文档化即可（§7.4 的不同步本次被正确性评审实证构造出来，见下节）。
- scrutinee 类型为未解 meta 时直接报错（`pattern_match.rs:88-91`）：完备性小缺口。
- `val_mentions_lvl` 跳过 Lam/Pi 闭包（`mod.rs:1286-1327`）：真循环解靠 fuel 兜底成"耗尽失败"假象——设计内行为，两处口径一致自洽。
- Match-vs-Match 合一要求分支逐位同序同模式、带 pending 的卡住 match 不做 eta：**是标准依值 TT 判定式行为，不是 bug**（注意勿误报）。

### 核对通过的正面清单

NbE 表示与位移（层级/索引、quote fresh 变量、Match 臂三方同序同数——对 `cons(x, cons(y, ys))` 逐槽推演验证）；meta 求解器骨架（invert/prune/rename/solve/intersect/lams）与 eZ 逐点对齐；特化合一（方向约定、SpecSolve 可解集、occurs 硬拒绝、链式解传递可见性验证）；不可达臂按错误处理 + probe 快照回滚；VSub/frcs 显式替换抽查自洽；README 声称的偏离**逐条核对无虚假声明**。

---

## 二、正确性评审（从中断的 agent 记录还原，关键论断已对码复核）

**方法**：代码走查 + 14 个黑盒探针（保留在 `tests/zz_review_l07.rs`）。评审期间官方回归 48+51+94+70 全绿。跨 enum 重名构造子 / eta / 影子定义 / 依赖返回重锚 等探针均得到正确 Err。

### P0 嵌套覆盖缺失（与类型论 P0-1 同一发现，双实现共有）

实证输出（探针 `zz_nested_coverage_gap`）：
```
RESULT nested_coverage_gap => Ok("match List::cons(Nat::zero List::cons(Nat::zero List::nil))
  { case nil => zero; case cons(h, nil) => @1 }\n")
```
非穷尽（`cons(h, cons(_, _))` 未覆盖）被接受、运行期卡住，且卡住值显示为 `@1`（内部层级泄漏到用户输出，顺带的显示 bug）。孪生版 `covers`/`is_catch_all` 同为浅层判定（parity 保证同判）。

### P1 陈旧 solvable 污染 → 臂序影响可达性判定（实证推翻注释等价性声称）

- **位置**：`pattern_match.rs:153-158`——注释声称"solvable 不回滚……与旧 pm_restore 截断等价"。
- **实证**（探针 `zz_stale_solvable_*`）：
  - `big` 臂在前（绑定 5 槽）+ 荒谬 `ident` 臂在后 → **Ok**：big 的陈旧 solvable 条目让 ident 臂特化方程中的瞬态 η（层级 L+1）"可解"，解出 `η := succ zero`，方程成功，荒谬臂被静默接受；
  - `ident` 臂在前 → **Err 分支不可达**（正确）。
- **定性**：接受判定依赖臂序，与注释声称的截断等价性不符；是 README §7.4 "probe 与臂内方程可能不同步"的具体实例（probe 用干净 base_solvable，臂走查带陈旧条目）。实际危害为覆盖语义漂移（荒谬臂被接受而非报错），分支体在伪精化上下文中检查但 σ 中 `η:=succ zero` 位于无真实槽的层级、对体检查惰性，未升级为错误定型。
- **建议**：臂边界回滚 solvable 至快照（截断到臂前 `cxt.lvl` 对应深度），或最小改动：臂走查方程中的瞬态 η 仅允许引用 ≤ 本臂绑定槽的层级。

### P1 fuel 耗尽 panic 窗口（静态分析确凿，动态未触发）

- **机制链**（已对码逐行复核）：
  1. `mod.rs:511` `MetaEntry::Solved(t_solved, _) if burn(&self.unify_fuel)` ——fuel 为 0 时**已解 meta 不展开**，按 `Val::Flex(m, sp)`（未解）返回；
  2. `unification.rs:606-609` `solve_with_pren`：`match self.meta[m.0] { Unsolved => …, _ => unreachable!() }` ——若该 meta 实为 Solved 则 **panic**；
  3. 同型模式还有 `unification.rs:185-188`（prune_meta）、`unification.rs:256-259`（prune_vflex）。
- **触发窗口**：恰在把 fuel 从 1 递减到 0 的那个 unify 帧内，两侧（force 展开失败后）是已解 meta 的 Flex。深负载（≈4096 层递归内单次 unify_catch）才有机会。动态构造未成功：d=1200 先触发栈溢出（README §7.6 已文档化的深值/走查递归边界，其自带 d=400 测试用 512MB 栈），fuel 行为探针在 d=600/800 因评审中断与并发构建故障未跑完。
- **建议**：三处 `unreachable!()` 改为返回 `Err(UnifyError)`（fuel 耗尽按未解失败的既有降级故事），一行级改动 ×3。

### P2 VSUB_REGS 注册先于 clone 的顺序问题（孪生版）

- 注册记录指针在 arena cell 分配/克隆之前完成；若分配失败（panic）且被 `catch_unwind` 捕获，回收会过度递减引用计数。极远程（需分配失败），但修复简单：alloc 成功后再 push 注册（交换两条语句）。

### 遗留物

- `tests/zz_review_l07.rs`：本评审的探针（10 用例，可编译），含上述两 P1 的复现钉。建议保留至修复落地后并入正式回归，或现在即并入。
- 评审期间另一会话并发修改 L13 导致构建短暂中断（20:08–20:14），与 L07 无关，现已恢复。

---

## 三、性能评审（完整）

**关键背景**：参考版（语义 oracle）与孪生版（性能路径）问题清单截然不同。README §10：church 负载 basic 9.1ms vs fast 0.61ms（≈15×）。

### P0（参考版结构性问题）

- **P0-1 `closure_apply` 每次 β 归约深拷贝整个闭包体**：`mod.rs:956-958`（`*closure.1.clone()` 为 `Box<Tm>` 深拷贝）。同族热站点：`force` 展开已解 meta `t_solved.clone()`（mod.rs:515）、decl 展开 `e.val.clone()`（mod.rs:556、1019）、`v_app_sp` 逐实参 `u.clone()`（mod.rs:986-994）、quote/rename 的 Lam/Pi 臂（mod.rs:1129/1135，unification.rs:522/531）、unify Match/Match 慢路径（unification.rs:1000-1001）。这是 15× 差距的主要部分（Haskell 原版全共享，Rust `Box<Tm>` + 按值 eval 把共享变拷贝）。**根治 = eval 改收 `&Tm`（孪生版即存在性证明，约 22 个调用点签名手术）**；过渡方案 `Rc<Tm>` 只能降不能除。
- **P0-2 metacontext 全量深拷贝快照**：`unification.rs:681`（flex_flex 回滚 `self.meta.clone()`）、`mod.rs:463-465`；覆盖探测对每构造子一次快照（`pattern_match.rs:199`）→ C × O(M·size)。孪生版同站点是平面 memcpy。**建议** `Vec<Rc<RefCell<MetaEntry>>>` 或 undo-log（解 P0-1 后 undo-log 最优）。

### P1（值得改）

- **P1-1 `lift`/`skip` 每 binder 克隆整个 renaming HashMap**（`unification.rs:58-76`）：O(n·k) 哈希 + n 次分配；`rename_arm` 单分支 O(bind²)。**照抄孪生版 RenBuf**（`bump_spine_iter.rs:3931-4001`）或 `Rc<HashMap>` + `make_mut`。
- **P1-2 `simpl_decl` 每次消费卡住 match 全量重建 decl 表**（`mod.rs:1360-1370`；调用点 mod.rs:1174、unification.rs:543/990）：O(D·M)。README backlog 已自知。**建议** decl 版本号缓存或 overlay 旁表（后者改动面小且规避别名陷阱）。
- **P1-3 `Cxt::bind`/`define` 每 binder 克隆 `src_names` 且每个 entry 的 VTy 深拷贝**（`cxt.rs:240/266`、`subst_cxt` cxt.rs:282-299）：100 binder ≈ 10⁴ 次 String+Val 克隆。值改 `Rc<(Lvl, VTy)>` 立除深拷贝；彻底方案 = 回移孪生版 name_map + name_trail（bump_spine_iter.rs:5345）。
- **P1-4 参考版 `eval_aux` 每次匹配深拷贝分支体，嵌套 Con 按字段数放大**（`pattern_match.rs:561/583/591`）：match 负载 3× 差距主因。孪生版 `(&'a Tm, Env)` 签名（bump_spine_iter.rs:2019-2040）是蓝图，前提同 P0-1。

### P2（小优化，摘要）

- `Subst::lookup_hit` 命中时 `mentions_level` 全扫描 × 链长（mod.rs:223-290）：写入时预算层级集，读侧 `has` O(1)。
- `frcs` spine 收集一次性 Vec（mod.rs:634）：改调用方复用 scratch。
- `unify` Π 臂逐对构造完整 Cxt、`unify_catch` 无条件克隆两侧值（unification.rs:807-829、mod.rs:1210-1212）。
- elaboration 顶部"最后一次使用仍 clone"×6（elaboration.rs:207/228/313/328/358/360）：直接删除，零风险。
- 构造子查表 `format!("{}.{}")` 临时 String（pattern_match.rs:191/372）：入口预解析 entry 表。
- `struct_eq` 缺 Rc 槽位 `Rc::ptr_eq` 快速路径（struct_eq.rs:128-166；VSub 臂已做，Sum/SumCase 未做）。
- 孪生版 `subst_cxt` 后 env 退化为纯 cons 链（bump_spine_iter.rs:5800-5813）：传 `&mut defs` 追加平坦区，恢复 O(1) 寻址。
- 孪生版卡住 match pending 逐应用 O(k²)（bump_spine_iter.rs:1286-1295）：backlog 已列（pending cons 化）。

### 工程卫生

`src/bench_head/` 与 `src/bench_pre/`（588K+576K、28 文件）是 A/B 实测的 worktree 残留，不参与编译但污染 grep/评审面，建议删除或 gitignore。L07 模块本身无死代码。

### 总评

设计文档化程度极高、对自身性能边界认知清醒。孪生版接近该表示下的最优；最值得先动：simpl_decl 缓存 + subst_cxt 平坦区。参考版问题集中于一条主线（β 深拷贝 + metacontext 深快照 + HashMap 逐 binder 克隆）。改造顺序：零风险减法 → 回移 RenBuf/name_map 两个已验证模式 → 视收益决定 eval 借用化。

---

## 四、代码风格评审（完整）

### 关键背景澄清：bump_spine_iter.rs 为什么 8124 行

它是**整套 elaborator 的第二份完整实现**（bump arena + 打包指针值），与参考版构成"孪生"（Ok 输出逐字节一致，`tests/l07_fast_parity.rs` 双 oracle 互检钉住）。**L07 与 L13 的 fast 版并非孪生**（L13 无 VSub/SpecSolve，走旧 pm_defs 路线）；真正的孪生链是 L07 fast ↔ L08 fast（7920 行逐段同构）→ L09–L12 逐层复制。

### P1（应当整改）

- **P1-1 拆分 8124 行单文件**：按现有分节线切目录模块（syntax/subst/env/prim/kernel{eval,quote,unify,rename,force}/struct_eq/machine/compiler/entry），全部 `pub(crate)` 零逻辑改动；内嵌 `mod deep_value_tests`（L8077-8124）并入 tests.rs，基准源生成器（L7967-8076）移 `#[cfg]` bench 支持文件。
- **P1-2 vsub_reclaim 只落 L07，L08–L12 未同步（最实质工程风险）**：σ 克隆跨轮回收（VSUB_REGS）全仓库只命中 L07；L08–L12 同构代码的"arena 内 Rc 强引用跨轮不归还"无上界慢泄漏原样存在。且 L07 文件头注释（L29-32）仍写"待评估"，与已落地的修复不符。按项目"孪生同步"惯例逐层移植，或在 README 记录不移植的原因。
- **P1-3 builtin 注册表三处手写**（cxt.rs:78-153 / bump_spine_iter.rs:7486-7570 / 997-1248）：抽 const 数据表驱动类型项生成；prim_reduce 保留 match 但用 arity 字段收敛"元数不足"检查。
- **P1-4 clippy 实跑清单**：struct_eq.rs 14 处 unused 变量、elaboration.rs:501、unification.rs:158、parser/syntax.rs:1 unused import、unification.rs:763 `pub fn unify` 暴露私有类型（全库通病，L07 先示范）。
- **P1-5 孪生舰队缺机械化同步护栏**：本次 P1-2 漏同步即人工纪律失效实例。建议 CI 脚本对 L07/L08 同名函数做 strip 注释 diff 归一化对比，或 commit 模板强制列同步层清单。

### P2（建议，摘要）

- 25 处 `too_many_arguments` + 10-17 参自由函数线程化：引入 `Core<'a>` 上下文结构或改 `&mut self` 方法。
- 巨型迭代内核（unify_iter 674 行等）：分节注释升级为具名锚点；拆文件后优先级下降。
- 调试脚手架嵌生产路径（REN_DEPTH 原子计数、LOOP_DEBUG eprintln）：收进 debug.rs 或 cfg 门控。
- 用户可见错误文案中英混用：趁 parity 只钉判定不钉文案统一口径。
- 过时/受损注释若干（bump_spine_iter.rs:6959"事实表"措辞、unification.rs:810 被空行劈断的注释、syntax.rs:16 游离 use）。
- mod.rs 职责偏多：prim_reduce 抽 prim.rs、DEMO_SRC/bench 辅助抽 bench_support.rs，可瘦到 ~1000 行。
- parser 死变体（ExpectDecl/Custom/Eof）：`#[allow(dead_code)]` + 注释说明。

### 值得肯定

文档密度罕见地高（585 处 doc 注释、README 538 行含评审轮历史）；深值爆栈改造有确定性回归钉；unsafe 集中且均有 SAFETY 注释；测试组织佳（42 测试每个有来源说明）；跨层命名一致。

### 总评

**B（良好）**。参考版侧接近 A；拉低整体的是 fast 版组织方式与孪生运维。性价比最高的两个动作：拆目录（纯机械）+ σ 泄漏修复向 L08–L12 传播（消除真实长期泄漏）并建立同步护栏。

---

## 五、修复路线图（按风险/收益排序）

1. **零风险纯减法**（可立即做）：elaboration.rs 6 处末日 clone；struct_eq 加 `Rc::ptr_eq` 短路；clippy 清单；删 src/bench_head、src/bench_pre。
2. **一行级修复 ×4**（方向性纠偏）：三处 `unreachable!()` → `Err`（fuel 降级走既有故事）；`probe_accessible` 区分 fuel 耗尽（unsound → incomplete）；VSUB_REGS 注册后置；unify SumCase 臂加 Sum 头名字检查。
3. **P0 嵌套覆盖检查**（~100 行 + 测试）：沿模式下钻逐节点 probe_accessible；`tests/zz_review_l07.rs` 的 `zz_nested_coverage_gap*` 转正式回归；顺带修 `@1` 显示泄漏。
4. **陈旧 solvable 臂序污染**：臂边界截断 solvable；`zz_stale_solvable_*` 转正式回归；订正 `pattern_match.rs:153-158` 注释。
5. **孪生同步**：vsub_reclaim 移植 L08–L12 + 文件头注释更新 + 同步护栏脚本。
6. **构造子良构性**（P1-1）：ret WHNF 必须是本 enum + 参数一致性。
7. **性能结构改造**（最后，视 bench 收益）：RenBuf/name_map 回移 → metacontext Rc 化/undo-log → eval 借用化（22 调用点，孪生版为蓝图）→ 拆 bump_spine_iter.rs 目录。

---

## 六、修复轮记录（2026-09-18，当日完成路线图 1–4 + 6）

评审当日按路线图完成全部正确性修复（路线图第 1、2、3、4、6 项），参考版与孪生版同步落地，**全套测试通过**（lib 713 / blackbox v1-v3 48+51+99 / parity 76 / twin_engine 19）。

### 已修复清单

| # | 问题 | 修复 | 位置（参考版 / 孪生版） |
|---|---|---|---|
| 1 | P1 陈旧 solvable 臂序污染 | 臂边界同步回滚 solvable（快照/恢复），订正原"与 pm_restore 截断等价"的错误注释 | pattern_match.rs compile 臂循环 / bump_spine_iter.rs 同点 |
| 2 | P1 probe fuel 方向 unsound | `probe_accessible` 失败时区分 fuel 耗尽：按可达处理（保守要求覆盖，降级方向 unsound→incomplete） | pattern_match.rs / bump_spine_iter.rs 两版 probe 尾 |
| 3 | P1 fuel 耗尽 panic 窗口 | 三处（参考）/两处（孪生）`unreachable!()` 改按合一失败降级返回 Err/false/None | unification.rs prune_meta/prune_vflex/solve_with_pren；孪生 solve_with_pren_bump/prune_meta_bump |
| 4 | P1 SumCase 构造子身份判据不足 | SumCase/SumCase 合一臂增加 typ 的 **Sum 头名字**检查（跨 enum 重名构造子直接 Err），不比值避免互相引用深递归 | unification.rs SumCase 臂 / bump_spine_iter.rs unify_iter 同臂 |
| 5 | **P0 嵌套模式覆盖检查缺失** | 沿模式下钻逐节点检查：walk_con 的嵌套 Con 字段记 (路径, 字段Sum)，臂走查成功后以**终态 σ** 结算（两段式——字段走查时外层特化方程尚未解出，早记会把索引精化下不可达的构造子误判可达）；臂循环后对每条记账在记录臂实例化下 probe 可达构造子，覆盖集从已走查臂的 PatternDetail 沿路径结构求出（var/Any=全覆盖、祖先异 ctor=不可达、荒谬臂/被遮蔽臂天然不贡献）。错误如 `match 不完整：模式位置 cons#2 → cons#2 缺少构造子 cons` | pattern_match.rs（NestedCheck/pending_pos/cover_at）+ bump_spine_iter.rs 镜像；cover_at/PosCover/fmt_path 放 mod.rs 共享保证两版文案一致 |
| 6 | P1 构造子返回类型无良构性 | 新增 `check_ctor_wf`：实例化构造子 telescope 后 ret 的 WHNF 必须是本 enum 的 Sum 且隐式参数位是 telescope 内 **bare rigid**——拒绝 `c -> Nat`（phantom 构造子）与 `c -> Foo[Bool]`（参数特化）；**允许**构造子重绑定参数惯用法（`p[A,B](a,b) -> Pack[A][B] a b`，v3_multi_index_gadt 钉住的语义，使用点经特化方程解回枚举参数） | elaboration.rs check_ctor_wf / bump_spine_iter.rs Machine::check_ctor_wf |
| 7 | P2 VSUB_REGS 注册顺序 | 注册后置到 alloc 成功之后（消除 alloc 失败 + catch_unwind 下过度递减引用计数的极远程 UB 窗口） | bump_spine_iter.rs wrap_sub |

### 设计要点与踩坑记录

- **嵌套覆盖的两段式结算**：第一版在字段走查中途快照 σ，v3 套件的 `v3_len_two_nested_pattern_refine`（Vec 长度 2 的尾部上 nil 应不可达）立即抓包——外层构造子的特化方程在字段循环**之后**才解出，早记的 σ 里没有 `l := succ n`。改为臂走查成功后统一结算。
- **荒谬臂不产生覆盖义务**：整臂 Unreachable 时丢弃其 pending 记账（`v3_absurd_nested_pattern_both_errors` 钉住的语义：报"分支不可达"即完成语义承担，不再叠加缺覆盖报错）。
- **构造子重绑定惯用法**：第一版 WF 检查要求参数位逐一等于枚举参数 rigid，被 `p[A, B](a, b) -> Pack[A][B] a b`（构造子自带参数、使用点解回）打回；放宽为"telescope 内任意 bare rigid"后仍能封住 phantom/特化两个洞。
- probe_accessible / unify_indices 增加显式 `lvl` 穿参（顶层传入口 cxt.lvl；嵌套延迟探测传记账时的臂内层级，scratch 层级必须落在该臂全部真槽之外）。

### 新增回归钉

- `src/L07_sum_type/tests.rs`：test_nested_coverage_gap / test_nested_coverage_gap3 / test_stale_solvable_order_independent（双臂序一致报不可达）/ test_ctor_wf_external_ret / test_ctor_wf_param_specialized。
- `tests/l07_fast_parity.rs`：parity_review_fixes_2026_09_18——上述场景的双 oracle 判定一致 + 两个正向/侧向对照（重绑定参数 Ok 逐字节一致；索引精化下的臂荒谬 Err 一致）。
- 评审探针文件 `tests/zz_review_l07.rs` 已删除（关键场景全部转正）。

### 修复轮性能核账（同日，`target/release/l07bench`，矩阵同口径）

方法：隔离进程 + 每格 min（church/strchain/global/match 取 k=11，enum 固定源），未改动的 L06 同窗对照漂移（basic 列 0.99–1.00×，窗口干净）；另做**同窗消融 A/B**（注释两处 `check_ctor_wf` 调用重建二进制，交错 3 轮）隔离单项成本。

| 负载 | basic 修复前→后 | 孪生 fast 修复前→后 | 消融归因 |
|---|---|---|---|
| church | 3.968 → 3.971 ms（1.00×） | 0.317 → 0.318 ms | 无差 |
| strchain | 124.398 → 124.632 ms（1.00×） | 5.533 → 4.343 ms（0.78×，**变快**） | 变快来自 σ-reclaim（vsub_reclaim，基线矩阵先于该未提交改动），与本轮无关 |
| global | 139.742 → 142.852 ms（1.02×） | 7.780 → 7.947 ms（1.02×） | WF（其源含 enum 声明）+ 漂移内 |
| match | 0.148 → 0.150 ms（+4µs） | 0.047 → 0.048 ms | WF：2 个构造子 ≈ +3µs |
| enum | 0.323 → 0.337 ms（+16µs） | 0.071 → 0.072 ms（+2µs） | WF：~10 个构造子 |

结论：**嵌套覆盖检查（P0 修复本体）零可测成本**——基准负载的模式均为单层 Con，记账为空、延迟探测不触发；其成本只在真有嵌套 Con 模式的源上按"每嵌套位置 × 字段构造子数的一次探测"出现（编译期一次性）。**唯一可测成本是构造子良构性检查 ≈ 1.6µs/构造子（参考版）/ ~0.2µs（孪生版）**，声明期一次性；参考版偏贵是 telescope 走查踩中已知的 closure_apply 深拷贝问题（性能评审 P0-1）——若日后做 eval 借用化会一并摊薄。LSP 场景（每文档 elaboration 一次）可忽略：50 个构造子的文档 ≈ +80µs。solvable 回滚 / SumCase 头名检查 / probe fuel 分支均在噪声以下。

### 遗留（未在本轮做）

- 路线图第 5 项（vsub_reclaim 向 L08–L12 传播 + 同步护栏）与第 7 项（性能结构改造、拆文件）未动，见上文路线图。
- `@1` 显示残留（卡住 match 打印内部层级）未修——待嵌套覆盖修复后该场景不再静默通过，显示问题降级为纯 cosmetic。

---

## 七、孪生舰队移植轮（2026-09-19：L08 / L10 / L11 / L12）

路线图第 5 项落地：把第六节的 7+1 项修复（含 σ 跨轮回收，即 vsub_reclaim 传播）并行移植到 L08_product_type、L10_typeclass、L11_macro、L12_canonical，四层参考版 + 孪生版双落地。**L09 未在本轮范围**（用户指定；其匹配精化走旧 update_cxt 路线，移植需单独评估）。

**最终验证**：`cargo test --lib` 742 全绿；六层 parity（L07 76 / L08 89 / L09 31 / L10 42 / L11 47 / L12 46）全绿；l08_blackbox 57 绿。未 git commit。

### 各层要点

- **L08**（与 L07 逐段同构，基本机械移植）：7+1 项全落地。移植中发现并补齐一个 L07→L08 真实缺口：`run_decls` 缺 `ReclaimOnExit` 轮尾归还守卫，没有它最后一轮的 σ 克隆挂到下一轮才回收（回归钉实测 4 条/轮泄漏，补后归零）。新增 lib 钉 7 个 + parity 钉 `parity_review_fixes_2026_09_18` 与 `fast_substv_reclaimed_across_rounds`。
- **L10 / L11 / L12**（f5952cf/a8fcaef 值级探测形态，逐层适配）：
  - **不回退值级探测提交**：嵌套覆盖/可达性用各层现役探测机制实现，probe 加 `lvl`/`init_sub` 显式穿参（新增 `unify_catch_at`）。
  - **修复 1（solvable 回滚）在三层数据性 N/A**：无 solvable 白名单（可解集 = 任意裸 Rigid）且臂 σ 逐臂重建，污染通道不存在；以"臂序无关性"回归钉钉住该性质。
  - **修复 5 的架构适配（本轮最重要的设计分叉）**：三层的臂走查是 `walk_pat`（纯结构绑槽）+ `check_pm_final`（对 raw 重推断的 meta 解方程）——走查槽位在 σ 里没有解，直接照搬 L07"字段 Sum 置于 σ 下探测"会在 GADT 索引位置产生假阳性（探针实测）。修正为 **PendingNode 两段式**：每 Con 节点记 (头部 Sum, 槽位实例化 ret)，臂方程成功后根→叶把 `head.params ≐ ret.params` 逐槽解入 σ，再以终态 σ 结算嵌套记账。
  - 修复 3 的孪生侧为防御性降级（三层的孪生 force 当前对 meta 展开无 fuel 门，窗口不可达，与 L07 姿态对齐）。
  - L12 的常规 unify SumCase 臂本就比 typ 值（强于头名检查），缺口仅在 unify_pm（已补头名检查）。
- 各层新增钉：lib（L08 7 / L10 7 / L11 7 / L12 8）+ parity `parity_review_fixes_2026_09_18`（评审场景双 oracle 判定一致 + 正向对照）+ σ 回收钉。

### 移植轮修的测试基建 bug（L12 parity 死锁）

L12 agent 半成品留下 `SIGMA_SAMPLING_LOCK`（Mutex）自死锁：`deep_workloads_parity`/`steady_state_reuse` 外层持锁，内部 `assert_parity` 的 `run_basic` 再取同一把非重入锁。改为 **thread_local 深度计数 + 全局独占闸**（`SigmaGuard` 同线程可重入；`SigmaExcl` 供 σ 采样钉做精确静默窗口），死锁消除且采样互斥语义保持，全套 46 测试 0.03s 跑完。

### 各层遗留

- L11 已知既有缺陷（HEAD 同样失败，非本轮回归）：嵌套 Con 模式的**值级调用** `println (f (cons zero (cons zero nil)))` 报 `can't unify expected: (x: ?7) → ?8 x`——推断侧对嵌套模式绑定的函性处理缺口，已在钉注释记录。
- L10/L11/L12 的"特化失败 = 臂静默跳过"为文档化收窄语义（荒谬臂不报错），与 L07 的报错语义不同——各层 parity 钉按各自语义钉判定一致性，未强行拉齐。

---

## 八、性能结构批次（2026-09-19：路线图第 1、7 项部分落地）

零风险减法（主 agent 亲手）+ 三个并行 agent（L07 参考版 / L07 孪生版 / L09）。全部测试绿：lib 742、六层 parity 全绿、blackboxes 全绿。

### Phase A：零风险减法（L07 参考版）

- elaboration.rs 四处"最后一次使用仍 clone"删除（Def/Enum 的 typ_tm/t_tm eval 点）；`check_ctor_wf` 改收 `&Val`（API 中性，telescope 走查仍需内部 clone，属 P0-1 族）。
- struct_eq.rs：`val_eq` 入口同址短路（`ptr::eq`，不烧预算）+ EqTask::V 同址守卫 + Sum/SumCase 的 Rc 槽位 `Rc::ptr_eq` 短路（共享同源 decl 展开时免递归）；Tm 层同款循环的 unused 变量清理。
- clippy：parser/syntax.rs unused import、unification.rs prune 槽位 `(_, _, _)`、孪生两处 `typ_tm` 未用等全部清零。
- `src/bench_head`/`src/bench_pre` **保留**（评审建议删除，但 l07alloc/l07whoalloc/pmabbench 三个 bin 经 `#[path]` 引用，删除会破坏工具）。

### Phase B-1：L07 参考版性能（agent）

1. **P0-2 metacontext 改 undo-log**：`meta_snapshot` 从全量深拷贝降到 **O(1) 双水位**（undo 栈深 + meta 追加水位）；唯一覆写通道 `overwrite_meta` 写前入轨迹；恢复 = 逆放 + 截断。flex_flex 双向与嵌套探测的回滚语义逐位保持。
2. **P1-1 renaming 去 O(k²) 克隆**：`&mut` 穿线 + Lam/Pi 臂原位插拔 + 双路径回滚（孪生 RenBuf 的无 arena 版，不依赖"兄弟看不见"类隐不变式）；`rename_arm` 每分支 1+k 次表克隆 → 1 次克隆 + k 次原位插入。
3. **P1-3 src_names 双层 Rc**：`Rc<HashMap<String, Rc<(Lvl, VTy)>>>`，bind/define 值零深拷贝，new_binder/decl_insert 派生变 O(1)。
4. **P1-2 simpl_decl 旁表缓存**：`Decls` 结构化（`{map, ver}` + 全局代数），简化表继承 ver，按实例代数键缓存；参考版 decl 表创建后不可变 ⇒ 无需失效钩子。

### Phase B-2：L07 孪生版性能（agent，README backlog 三项落地）

1. **subst_cxt 平坦区恢复**：包裹槽经 `&mut defs` 追加为尾部新平坦区，臂体 `env_nth` O(深度)→O(1)；append-only 不破坏旧 env 共享，生命周期与当轮一致（已知取舍：同作用域 match 后再有 let-define 回落链走）。
2. **pending cons 化**：`XCell::Match.pending` 改 `Option<&PendingCons>` 头插链，vapp1 O(k²)→O(k)；8 个消费点适配，序敏感点（fuel 序/解方向序/栈序）逐字节保持。
3. **simpl_decl 单槽缓存**：地址键 + `decl_insert` 逐次失效 + 轮界失效；三处 Match 消费点共享 Rc。

### Phase B-3：L09 泄漏修复与评估（agent）

- **σ 回收全套移植**（VSUB_REGS/vsub_reclaim/SUBSTV_ALIVE/clear_round 伴生/ReclaimOnExit/wrap_sub 注册后置），SAFETY 论证按 L09 实际代码重核。回归钉用单窗 + 独占闸方案，并做了**消融灵敏度验证**（去掉 ReclaimOnExit 钉必红）——顺带发现 L11 式"多窗重试"钉会被下一窗轮首归还造成假绿，改单窗。
- **7 项修复评估**：修复 1 数据性 N/A（臂序无关性已钉）；修复 2/3/5/6/7 移植（嵌套覆盖走 L10/L12 PendingNode 路线，NestedCheck 存臂走查上下文以配 `spec_refine` 的 `x >= cxt.lvl` 守卫）；修复 4 部分移植（常规 unify 本就比 typ，缺口在 unify_pm，已补）。l09_fast_parity 31→34。
- **勘误**：评审记录称"L09–L13 走旧 update_cxt 路线"已过时——工作树中 L09 参考版已是显式 σ + subst_cxt 载体。

### 基准读数（诚实口径）

隔离进程、每格 min、L06 同窗对照 0.99×（窗口干净）。孪生 strchain/global 的表观改善被窗口方差淹没（3.65–5.6ms 摆动，**不下结论**）。稳定可复现的：

| 格 | 基线(09-18) → 本轮 | 说明 |
|---|---|---|
| L07 enum basic | 0.323 → **0.310–0.317** | Phase A clone 删除 + 参考版批次，抵掉 WF 的 +16µs 后净改善 |
| L07 global basic | 139.7 → **138.5** | ~1%，窗口边缘 |
| L07 church/match basic、孪生各格 | 持平 | 在噪声内 |

**结论**：本批 P1 结构改造对微基准增益有限——印证性能评审的预判：参考版 church 的 12.8× 差距主体是 **P0-1 eval 借用化缺席**（每次 β 深拷贝闭包体），renaming/src_names/meta 快照只在小面负载可见。**eval 借用化本轮不做**：参考版是语义 oracle 而非 LSP 生产路径（LSP 走孪生），22 调用点签名手术的风险/收益比不划算；孪生侧本轮三项 backlog 落地后已无低成本项，剩余为 force 草稿栈穿参与 XCell 拆 Big（预期个位数百分比）。结构性收益（O(k²)→O(k) 等）会在真实 LSP 负载（深上下文、长 pending）上比微基准更可见。本轮最大的实际收益仍是已落地的 **σ 泄漏修复传播至 L09**（LSP 长会话的无上界内存增长）。

---

## 九、收官轮（2026-09-19 下午：eval 借用化 + 拆分 + L13 移植）

第八节"不做 eval 借用化"的决策被用户推翻（"做吧"），三任务并行完成。**全量验证：lib 742 / 七层 parity 全绿（L07 76 / L08 89 / L09 34 / L10 42 / L11 47 / L12 46 / L13 411）**。未 git commit。

插曲：本轮派发时主机第二次崩溃，三个 agent 全部 "Turn execution failed"——eval agent 未启动；拆分 agent 无损失（尚未动手）；L13 agent 留下探针文件与评估结论，经 `~/.zcode/cli/rollout` 还原后随重派交接（其评估直接复用，节省一轮探针）。

### 1. eval 借用化 + Closure Rc 化（L07 参考版，P0-1 落地）

- `Closure(Env, Box<Tm>)` → `Closure(Env, Rc<Tm>)`：Val::Lam/Pi 克隆变 O(1)（构造点 4 处）。
- `eval` 签名 `Tm` → `&Tm`：47 处调用点适配；**`closure_apply` 的每次 β 整体深拷贝消失**；unify Match 慢路径 b1/b2 克隆、rename_arm tm 克隆、elaboration 全部 eval 前 clone 一并删除。
- `eval_aux` 借用化：返回 `(&Tm, Env)`，分支体运行时零克隆（3 处 body.clone + 递归临时切片消失）。
- Match 臂：卡住分支 `cases.clone()`（每卡住 match 值一次自身拷贝，对照术前"每次 β 先拷整个函数体再 move"净赢明确）；选中分支不克隆。
- 第 3 步（MetaEntry → Rc<Val>）评估后跳过：消费方需 owned Val，Rc::try_unwrap 必败零收益——诚实记录。
- **基准（L06 对照 0.99× 干净窗口）**：

| 负载 | basic 基线 → 术后 | 变化 |
|---|---|---|
| church k=11 | 3.968 → **2.493 ms** | **-37%**（孪生/参考差距 12.8× → 7.8×） |
| enum | 0.323 → **0.266 ms** | **-18%** |
| global | 139.7 → **133.7 ms** | -4% |
| strchain / match | 持平 | strchain 主导项是 decl 表增长 |

剩余深拷贝家族（诚实记录）：卡住 Match 的 cases 克隆（候选：Tm::Match cases 改 Rc，牵动面大未做）、Lam/Pi eval 臂 `Rc::new(体.clone())`（每次该项被求值一次，无嵌套 λ 的体零拷贝）、force 的 t_solved 克隆（已降为 O(深度) 廉价克隆）。

### 2. bump_spine_iter.rs 拆分（8471 行 → 15 文件）

入口 `bump_spine_iter.rs`（145 行导览 + mod 声明 + re-export，文件与同名目录并存，L13 先例）+ 15 个子模块（syntax/subst/env/spine/prim/force/eval/quote/unify/rename/struct_eq/machine/compiler/entry/bench_src）。行数精确守恒对账（8376 正文逐行搬运 + 64 文档 + 9 use）；可见性调整 141 处全部 `pub(super)`（无一升 pub(crate)）；原 `pub(crate)` 面 45 项原样恢复；`#[path]` 独立编译单元（l07_fast_parity、l07bench）验证成立；外部消费者零改动。

### 3. L13 移植 + 孪生 GADT 漂移修复（生产层）

- **P0 嵌套覆盖检查双落地**（NestedCheck 带臂上下文快照——L13 的 update_cxt 血统无 σ，两段式简化为"走查记账 → 臂特化成功后提升 → 终态探测"）；check_ctor_wf 双落地（`c -> Foo[Nat]` 参数特化现被拒，`c -> Nat` 的报错从误导性的 `no such constructor c` 变为准确的 `返回类型是 Nat，不是 Foo`）；probe fuel 方向（参考版）、5 处 unreachable 降级（参考版）、unify_pm SumCase 头名字（双版）。
- **既有 parity 漂移修复（意外收获）**：孪生 GADT 嵌套 match ref Ok / fast Err 的根因 = 孪生 `check_pm` 用普通 `infer_expr`（App 实参走 unify_catch，嵌套构造子应用的 rigid 冲突直接失败）而非参考版的 `infer_expr_pm`（走 unify_pm + update_cxt 精化）——补 `Machine::infer_expr_pm` 镜像后 iso_a/b/c 全部转 Ok，双版逐字节一致。这是 LSP 生产路径的真实用户可见 bug 修复。
- 组合维度缺口（Bool×Bool 2×2 需 4 臂覆盖 2 臂）实证为**与 L07 同语义的保守行为**（L07 参考版同样接受），需真正 split tree 才能关闭——已钉防误判。
- 新增 14 断言组钉（`parity_review_fixes_2026_09_19`），l13_fast_parity 410 → 411。

### 收官状态

评审路线图全部关闭：正确性 7 项修复（L07–L13 全舰队）、σ 泄漏修复传播（L08–L12）、性能结构批次（参考版 P0-1/P0-2/P1 全家 + 孪生 backlog 三项）、8471 行单文件拆分。遗留均为记录在案的低优先项：force 草稿栈穿参、XCell 拆 Big、Match cases Rc 化、split tree（组合维度覆盖）、L11/L13 共有的嵌套模式函性推断缺陷（值级调用 `(x: ?N) → ?M x`，双版同判，有钉）。

---

## 十、解析缺陷根治（2026-09-19 傍晚：第九节遗留"函性推断缺陷"的真相）

第九节遗留的"L11/L13 嵌套模式函性推断缺陷"（完整嵌套 match 值级调用报 `can't unify expected: (x: ?N) → ?M x, find: Nat`）由专项 agent 根治。**结论出乎意料：根因不在 elaboration，在 L13/L11 共用解析器。**

### 根因

L11/L13 的 Pratt 解析器 `expr_bp` 有一个**后缀 `(`-call**（绑定力 20，高于 `p_spine` 的相邻并置应用）：`lcons zero (lcons zero lnil)` 被解析成 **`lcons (zero (lcons zero lnil))`**——括号组折到了前一个实参上。elaborator 对 `zero (inner)`（对 Nat 值做函数调用）先试 Scala-apply 降级、再合成 fresh Π `(x: ?N) → ?M x` 跑 unify_catch——**误报的 can't-unify 是对被误解析程序的正确拒绝**。决定性反证：与 match 无关的 `println (two zero (succ zero))`（two 取两参）在双引擎报一模一样的错。

**L07 无此缺陷的原因**：其解析器没有后缀 `(`-call，`f a (b)` 天然 = `App(App(f,a),b)`。此前归因"σ-walk 架构更优"不成立——是解析器差异。此前所有"嵌套模式函性"假设链（check_pm/infer_expr_pm/insert/solve）全部证伪；今日落地的模式编译器成果零改动。

### 修复

消歧规则：**单实参括号组在后缀位 = 相邻实参**（`f (x)` ≡ `f x`，项相同），**多实参逗号组 = 真实调用**（`f(a, b)`，含 prelude 在用的带空格形态），空组不变。实现：后缀位单实参组以哨兵 icit 折叠，`p_spine` 统一结算拆回相邻实参，残留哨兵由 strip 就位剥回（覆盖全部 Raw 变体；用户标识符不可能撞哨兵名）。

- `src/L13_namespace/parser/mod.rs`（:780 后缀分支 / :1077-1162 哨兵 + p_spine 结算）
- `src/L11_macro/parser/mod.rs` 同款（两版解析器同构，一处修复双引擎生效）
- 语义保持面全有钉：`f(a,b)`/`f (a, b)`/`f()`/`f(x)`/`f(x)(y)`/`new X(..)`/`succ (x) + y`/`xs.map (f).length` 逐一同前；唯一行为变化即原 bug 形态 `f a (b)`（语料 grep 证实无既有依赖）。

### 顺带判定

- 单臂复现里 `non-exhaustive pattern: lnil(_, ×999)` 的失控渲染**非 bug**——`pattern_match.rs` compile 里字面写死的 999 通配（与 L10–L12 产出一致的设计产物）。
- 第九节的"既有 parity 漂移（孪生 GADT 嵌套）"与本缺陷**无关**（已在第九节由 infer_expr_pm 修复）；两者当时症状相似导致误并。
- 可选后续（诊断质量）：fresh-Π 回退的 `(x: ?N) → ?M x` 文案可改为"X 不是函数"——未做。

### 最终状态

**lib 742 / parity：L07 76 / L08 89 / L09 34 / L10 42 / L11 48 / L12 46 / L13 412，全绿。** 复现程序双引擎零错误、输出正确。L13 缺陷钉 ③b 转正为正向钉；L11/L13 各新增解析专项钉（7 组消歧形态）。`tests/zz_tmp_l13_debug.rs` 临时 harness 保留（另一会话所有物，未跟踪文件）。未 git commit。
