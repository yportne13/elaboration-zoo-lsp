# D5 性能、分配与确定性 — L07–L12 只读评审

## 1. 结论（verdict）

- **P0: 0  P1: 0  P2: 4  P3: 11  needs-verify: 4**

- 覆盖范围与方法：
  - 精读 L07 蓝本全部核心文件：`mod.rs`（Subst 链 / force / frcs / eval / quote / prim_reduce / bench 口径）、`unification.rs`（SpecSolve / unify / rename / flex_flex）、`pattern_match.rs`（Compiler / probe_accessible / eval_aux）、`cxt.rs`（Decls / subst_cxt / bind_slots）、`struct_eq.rs`、`elaboration.rs`。
  - 孪生版按结构采样 `src/L07_sum_type/bump_spine_iter.rs`（值编码 V/XCell、SubstV、force/frcs/force_arg、unify_iter + conv memo、quote_memo、subst_cxt、Tycker 轮口径），并 grep 比对其余各层孪生的对应函数。
  - 机械比对 L08–L12：以 L07 的热路径锚点（`lookup_hit` / `compose` / `extend` / `mentions_level` / `sp.iter().cloned().collect()` / `simpl_decl` / `meta_snapshot` / `avoid_recursive`）在六层逐一 grep 定位行号核对，未发现"修了一份没修其他份"的语义级分叉（发现的分叉均为各层 Val 表示差异：L07–L09 spine 存 `Val`，L10–L12 存 `Rc<Val>`）。
  - 确定性专项：对六层全部 `HashMap`/`HashSet`/`FxHashMap`/`FxHashSet` 的**迭代**（`.iter()`/`keys()`/`values()`/`for ... in`）逐一排查消费端。
  - 核对 `src/bin/l07bench.rs` … `l12bench.rs` 的负载生成器（`match_src` / `enum_src` / `natadd_src` 等）。
  - 未运行 cargo（遵守 BRIEF）；全部结论为静态论证 + 复杂度分析。

- **重要口径澄清**：设计文档 §3 初稿的 `Sub { map: FxHashMap }` 表示**已被废弃**（§9 注记 4），实现是**持久化单链 + 条件包裹**，参考版与孪生版一致。因此不存在"每次查表 clone Val 的 FxHashMap 重建"问题；取而代之的热路径代价是**沿链 O(|σ|) 扫描 + 命中点 mentions_level 全值扫描**（见 P3-1/P3-2），且孪生版移植的是链表终态（`SubstV`），无 FxHashMap 残留。extend 是 O(1) cons（不是任务提示里假设的"每个新解 O(|σ|) 包裹既有条目"——包裹推迟到读点条件触发）；compose 是 O(|outer|)（见 §2 P3-3 的量化）。

## 2. 发现列表

### [P2] L12 canonical 搜索：HashMap 迭代顺序泄漏到合成结果（确定性；影响面：L12）
- 位置：`src/L12_canonical/canonical.rs:67-79`（候选枚举）、`canonical.rs:129/132/144`（首个成功即 return）、`src/L12_canonical/elaboration.rs:432-446`（LSP quickfix 重试闭包入口）。
- 证据：`search()` 的候选迭代器是 `names.iter().chain(cxt.decl.iter().map(...))`，其中 `cxt.decl: HashMap<SmolStr, ...>`（`src/L12_canonical/cxt.rs:17`，**std HashMap + RandomState，进程级随机种子**）。循环体对每个候选做 unify+check 探测，`return Ok(ret)` 取**第一个**成功者。
- 机制/影响：HashMap 迭代顺序随进程种子变化 ⇒ 同一输入两次运行的 quickfix 合成结果（`Ok(String)`，即生成的项）可以不同；同时失败候选消耗 fresh meta 的顺序不同，会影响后续诊断的 `?N` 编号。`run`/`run_fast` 不经此路径（`bump_spine_iter.rs:29-30` 明确 iddfs 不移植、parity 测试不覆盖），故不裂 parity，但对 LSP 用户是可观测的非确定输出。
- 处置建议：候选名先收集进 `Vec` 按 decl **登记序**（或排序）遍历；或 decl 表改 `BTreeMap`/带序号索引。

### [P2] L09/L10 参考版：卡住 match 的 quote/rename/unify 路径整 `Infer::clone()`（影响面：L09/L10）
- 位置：
  - L09：`src/L09_mltt/mod.rs:837-841`（quote 的 Match 臂，**每分支一次**）、`src/L09_mltt/unification.rs:350-353`（rename 的 Match 臂，每分支一次）、`src/L09_mltt/unification.rs:726-730`（Match-vs-Match 合一，每次比较一次）；
  - L10：`src/L10_typeclass/mod.rs:926-930`、`src/L10_typeclass/unification.rs:351-355`、`src/L10_typeclass/unification.rs:721-726`（同款三处）。
- 证据：`let mut avoid_recursive = self.clone(); avoid_recursive.global.iter_mut().for_each(|x| *x.1 = Val::Rigid(*x.0 + 1919810, ...));`。`Infer`（L09 `mod.rs:406-412`）含 `meta: Vec<MetaEntry>` 与 `global: HashMap<Lvl, VTy>`，`#[derive(Clone)]` ⇒ **每次克隆深拷贝全部已解 meta 值 + 全部全局类型**（Π 链闭包的 `Box<Tm>` 体逐节点深拷贝）。
- 机制/影响：O(|meta| + |global|·|类型树|) 深克隆 per quote-per-branch。quote 在 println/nf 路径（`bench_check_nf` 对最后一个 def 的登记值 quote——`match_src` 负载下它就是含卡住 match 的 λ 值，**基准即触发**）与臂检查的期望类型重锚路径（L09 `pattern_match.rs:275`）上都热。L07/L08 已改用 `simpl_decl`（只中性化 decl 表，不 clone meta），L11/L12 内联重建 decl 映射——L09/L10 是六层中最重的实现，属"修了一份没修其他份"的移植缺口。
- 处置建议：对齐 L07 口径——构造"global 表 → 中性 Rigid 视图"的只读替身（可 Rc 共享缓存），删除 `Infer::clone()`。

### [P2] L07/L08 参考版：force 的卡住 Match 臂每次 force 深拷贝 scrutinee（影响面：L07/L08）
- 位置：`src/L07_sum_type/mod.rs:529`、`src/L08_product_type/mod.rs:538`：`let s2 = self.force(decl, (*s).clone());`，未选中分支时返回原值 `Val::Match(s, env, cases, pending)`（`mod.rs:546`）。
- 证据：force 以值接收 `Val`；为在不消耗原值的前提下探测 scrutinee，先把 scrutinee **整体深克隆**（Val::Match 的 scrutinee/env/分支体 Tm 全深拷贝），探测失败时克隆结果整份丢弃。
- 机制/影响：卡住 match 在递归 def 值里无处不在，force 又被 quote/unify/eval 高频调用 ⇒ 每次路过都付 O(|scrutinee|) 深拷贝；同值反复 force（每轮 unify 递归入口、quote 递归）时该成本乘性放大。`Compiler::eval_aux` 入口的 `head.clone()`（`pattern_match.rs:553`）同型。孪生版对应臂（`bump_spine_iter.rs:1566`）以 packed-word 传值，`force(scrutinee)` 零拷贝——参考版此处的 clone 纯属表示开销。
- 处置建议：改以 `&Val` 探测 scrutinee（或提供 `force_ref`），仅确认选中分支后克隆/移动一次。参考版定位可读优先，可标"刻意容忍"，但这是无语义收益的纯浪费，成本极低即可消除。

### [P2] 全部六层 bench：精化/σ 密集的深嵌套场景零覆盖（影响面：L07–L12 基准）
- 位置：`src/bin/l07bench.rs:80-101,144-164`（natadd/match/enum 负载编排）、各层孪生 `match_src`（如 `src/L07_sum_type/bump_spine_iter.rs:7603-7614`）、`enum_src`（`bump_spine_iter.rs:7619-7671`，**固定源，与 k 无关**）。
- 证据：`match` 负载 = k+1 个**互相独立**的双臂 Nat match（每臂恰 1 个模式变量，σ 链长 ≤ 2）；`enum` 负载固定尺寸只跑一行（`l07bench.rs:149-150`）；`natadd` = add 翻倍链（仍是双臂浅 match）。整个套件没有：①深嵌套 Con 模式（`case succ(succ(...(n)))` 深度 d）——设计文档 §9 注记 4 引用的"深嵌套模式 2.5×@depth40 回归"场景；②match-in-match 嵌套编译（§4 槽位纪律的触发形态）；③add_assoc 式多方程 σ 链传播在 d、|σ| 规模化下的表现。
- 机制/影响：本次重构的核心性能主张就是 σ 的读写代价剖面（链扫描 vs 哈希），但**仓库内没有任何基准能对它施压**——当初否决 FxHashMap 版的 depth40 实测无法从 repo 复现，未来对 `lookup_hit`/`compose`/`mentions_level` 的改动回归也无法被 bench 捕捉（`match` 负载的 σ 长度恒为 1-2，链扫描退化为 O(1)，测不出差别）。
- 处置建议：补 `nestedmatch_src(k)`（深度 d 的嵌套 Con 模式 + 嵌套 match）与 `sigmachain_src(k)`（多方程索引等式链）两个负载族，把 §9.4 的 depth40 口径固化进 bench。

### [P3] Subst 链读点成本：lookup_hit O(|σ|) 扫描 + 命中点 mentions_level 全值扫描，无记忆化（影响面：全部参考版+孪生版）
- 位置：`src/L07_sum_type/mod.rs:223-236`（lookup_hit）、`mod.rs:248-278`（mentions_level，内含逐 Rigid 的 `sub.has()` 再扫一遍链）；孪生版 `bump_spine_iter.rs:345-358, 408-482`。
- 证据：命中一个解要付出 ①沿链找 x 的 O(|σ|)（含每步 `Rc` clone/drop 流量，可用 `as_deref` 引用遍历消除）；②对解值做一遍浅结构扫描，每个内层 Rigid 再 O(|σ|) `has()`——单次命中 O(|解值|·|σ|)。同一 (x, σ) 的重复读点（unify 每轮入口重包裹 + force）反复重扫，无"该值不提及 σ"的负缓存。
- 机制/影响：深模式（σ 条目多）下精化读点从旧 pm_defs 的 O(n) 线性扫**换成了 O(|解值|·|σ|) 的扫描**——只是把"全局表线性扫"换成了"每值逐链扫"，是否净收益取决于解值大小；在 |σ|、深度有界的真实负载中可接受，但与 bench 缺口（上条 P2）叠加后不可验证。
- 处置建议：为 lookup_hit 增加按 (x, σ 指针) 的条件包裹结果 memo（Rc 指针即键）；或 mentions_level 改为对 σ 键集一次位集判定的单趟扫描。参考版可容忍，孪生版值得做。

### [P3] Subst::compose 每次嵌套 VSub 交叉付 O(|outer|) 个 Rc 分配（影响面：全部层；参考版另有深拷贝）
- 位置：`src/L07_sum_type/mod.rs:307-324`；孪生 `bump_spine_iter.rs:386-400`；frcs 的调用点 `mod.rs:603-606` / `bump_spine_iter.rs:1629-1631`。
- 证据：compose 为外层每条目 cons 一个新 `Rc<SubEntry>`；参考版条目值 `e.val.clone()` 是 **Val 深拷贝**（Lam/Pi 闭包深拷贝 `Box<Tm>`），孪生版 `val: e.val` 仅打包字拷贝。深度 d 的嵌套 match 中，值带 d 层 VSub，一次完整 force 逐层交叉 ⇒ O(d·|σ|) 个 SubEntry 分配（参考版再乘解值深拷贝）。
- 机制/影响：这是"包裹不物化"设计的固有代价（设计文档 §2/§4 有记载），非 bug；列出作为深嵌套负载下的成本剖面证据，与 bench 缺口 P2 互证。若要消，可在 compose 时共享"外层链本身"（单链结构下 `outer.head` 直接接到 inner 之前需要链尾指针，当前表示做不到——记录为表示取舍）。
- 处置建议：先补基准再谈优化；孪生版打包字已把每条目代价压到一次 Rc 分配，现状可接受。

### [P3] frcs 读点 spine 实参全量深拷贝 + 无条件 VSub 包裹；包裹随嵌套 σ 层数堆积（影响面：L07–L09 参考版为主）
- 位置：`src/L07_sum_type/mod.rs:629-633`（`let args: Vec<(Val, Icit)> = sp.iter().cloned().collect();` 深拷贝整个 spine 进堆 Vec，再逐实参 `wrap_sub` 各分配一个 `Box` + Rc）；L08 `mod.rs:638`、L09 `mod.rs:493` 同款；L10/L11/L12 的 Spine 存 `Rc<Val>`（`mod.rs:120` 等），clone 降为引用计数。孪生版 `bump_spine_iter.rs:1754-1760`（collect_args + 每实参一个 bump VSub 单元）。
- 证据：lookup_hit 对**头部**解值做了 `mentions_level` 条件直通（§4"零分配直通"），但对 **spine 实参**无条件包裹——不提及任何已解层级的实参也各得一个 VSub 盒；这些盒随后续每次 frcs 经过再包裹（wrap-don't-advance 纪律），嵌套 d 层下槽位可堆 d 个 VSub 层。
- 机制/影响：每次精化读点 O(|sp|) 次 Box/Rc 分配 × d 层堆叠；语义无害（正确性由"宁宽勿窄"包裹保证），纯分配churn。孪生版 bump 单元便宜但同样无界堆积。
- 处置建议：实参侧复用 `mentions_level` 做同款条件直通（两版同步改；需确认不破坏 `bind_slots`/invert 对槽位 raw 形态的解包假设——解包循环是逐层的，少一层无害）。

### [P3] 孪生版 force/frcs 每次调用新建 Vec 工作缓冲，未复用 Machine 常驻草稿（影响面：全部孪生版）
- 位置：`src/L07_sum_type/bump_spine_iter.rs:1390-1393`（force：`work/vals/icits/args` 四个 `Vec::new()` per 调用）、`1623-1625`（frcs：三个）；嵌套 force 调用点 `1461`（prim 实参）、`1479/1542`（Obj 内层）、`1566`（Match scrutinee）各自再分配。
- 证据：模块注释宣称"热路径草稿常驻"（`bump_spine_iter.rs:13`），eval/quote/unify 均走 `Machine.workbuf` 等常驻缓冲，唯独 force/frcs 每调用新开。`Vec::new()` 本身不分配，但**有展开动作的** force 必然触发 malloc + 倍增拷贝，深度递归时 O(展开深度) 次。
- 机制/影响：常数因子级（bump arena 已兜住大头），但与设计口径不一致。
- 处置建议：把 `work/vals/icits/args` 挂到 `Spine`/`Machine` 上按调用前 clear 复用（与 `unifybuf` 同法）。实测收益幅度 needs-verify（见 §3）。

### [P3] unify 特化模式每次递归入口按 acc 重包裹两侧并 force（影响面：全部层，两版同构）
- 位置：`src/L07_sum_type/unification.rs:637-642`；孪生 `bump_spine_iter.rs:3220-3231`。
- 证据：`spec` 非空且 acc 非空时，**每个递归节点**都 `wrap_sub(acc, t/u)`（参考版各一次 Box 分配）再 force 一遍。同一方程组的子方程共享同一 acc 时重复包裹。
- 机制/影响：dpm-nbe `subst ɑ vs` 的惰性等价物（文档化设计），语义正确；代价是模式编译期每方程节点 2 次 Box + force。方程密集（GADT 索引多）时可见。孪生版有 conv memo 抵消重复对，参考版无。
- 处置建议：参考版可为"acc 未变"加代际计数跳过重包裹；低优先。

### [P3] solvable 用 `Vec::contains` 线性查（影响面：全部层，两版同构）
- 位置：`src/L07_sum_type/unification.rs:682,696`（`s.solvable.contains(x)`）；孪生 `bump_spine_iter.rs:3263,3277`。模式编译期 `self.solvable.contains(x)`（`pattern_match.rs:527`）同款。
- 证据/影响：每条特化方程的匹配臂守卫 O(槽位数) 线性扫；槽位数 = 模式变量总数，通常个位数，方程密集时乘性。参考版 `pattern_match.rs:427` 的 `self.sub.has(*x)` 也是 O(|σ|) 链扫。
- 处置建议：槽位数大时（>16）换 `FxHashSet<u32>`/位集；现状可接受。

### [P3] meta 快照/回滚整表深拷贝（影响面：全部参考版+孪生版）
- 位置：`src/L07_sum_type/pattern_match.rs:195`（每构造子探测一次 `infer.meta_snapshot()` ⇒ `meta.clone()`）、`unification.rs:520`（每次 flex_flex 尝试 `self.meta.clone()`）；L09–L12 `pattern_match.rs:184/164/158/162` 同款；孪生 `bump_spine_iter.rs:3001`（`metas.clone()`）。
- 证据：`Vec<MetaEntry>` 的 clone 对每个 Solved 条目深拷贝值+类型。每构造子探测、每次 flex-flex 双向尝试各一份。
- 机制/影响：O(|meta|·|解值|) per 探测；宏/类解析密集（L10–L12 traitchain 负载）且 meta 多时可观。原因：unify 是 `&mut self`，快照回滚是 elaboration-zoo 骨架的固有做法。
- 处置建议：探测期改 undo-log（只记录探测期间新解出的下标区间，回滚 = 截断，旧 pm_mark 思路在 Vec 上天然成立）。

### [P3] L11/L12：卡住 match 分支重求值的中性 decl 表重建位于**每分支循环内**（影响面：L11/L12 参考版）
- 位置：`src/L11_macro/mod.rs:971-978`、`src/L12_canonical/mod.rs:1109-1116`（quote 的 Match 臂）、`src/L11_macro/unification.rs:361-368`、`src/L12_canonical/unification.rs:365-372`（rename 的 Match 臂）——`decl.iter().map(...).collect()` 在 `cases.iter().map(|x| ...)` **内部**。
- 证据：L07/L08 的同款逻辑把 `let declb = Rc::new(simpl_decl(decl));` 提升到分支循环外（`src/L07_sum_type/mod.rs:1190`、`unification.rs:382`）——每个 Match 一次；L11/L12 每分支重建一次，O(#分支 × |decls|) 次 key clone + 五元组克隆。unify 的 Match-vs-Match 臂（L11 `unification.rs:760-768`、L12 `unification.rs:813-821`）每比较一次重建，与 L07 同口径。
- 机制/影响：纯常数因子冗余（每次重建内容相同），match 臂多 + decl 多时乘性放大。
- 处置建议：照抄 L07 的提升位置，一行级改动。

### [P3] L12 force_deep 重建 Sum/SumCase 不做"未变原样返回"检查（影响面：L12 参考版）
- 位置：`src/L12_canonical/mod.rs:814-843`；调用点 `unification.rs:519`。
- 证据：递归 force 每个槽后**无条件** `Rc::new(Val::Sum/SumCase{...})` 重建整节点，即使所有槽 force 后位等同。孪生版同函数（`bump_spine_iter.rs:1371`）在 bump 上分配、代价低；L12 的 Obj 臂（`mod.rs:716` 附近 `_ => t.clone()`）反而有未变直通——同文件口径不一。
- 机制/影响：trait 求解的深读点上每趟 O(|Sum 树|) 次 Rc 分配，结果与输入等同。
- 处置建议：槽位全未变时返回原 Rc（对齐孪生 Obj 臂的 `v2.0 == val.0` 判等直通思路）。

### [P3] `Subst::lookup` 死代码（影响面：全部参考版）
- 位置：`src/L07_sum_type/mod.rs:239-241`（L08 `mod.rs:246` 附近、L09–L12 各自对应处；L12 为 `mod.rs:306` 附近 `lookup`）。
- 证据：`lookup(x) = lookup_hit(x).unwrap_or_else(vvar)` 全仓无调用点（仅 frcs 直接用 `lookup_hit`）。
- 机制/影响：无；设计文档 §3 的 API 残留。
- 处置建议：删除或标注 `#[allow(dead_code)]` + 设计出处。

### [P3] `lookup_hit` 注释"零分配零 fuel"与实现不符（影响面：全部参考版，文档准确性）
- 位置：`src/L07_sum_type/mod.rs:218-222` vs `227-231`。
- 证据：条件直通分支返回 `e.val.clone()`——`Val` clone 对 `Lam/Pi`（`Closure(Env, Box<Tm>)` 深拷贝）、`SumCase`（`Vec` + `Span<String>` 的 String 拷贝）**有堆分配**；真正零分配的只有孪生版（`V` 是 `Copy`，`bump_spine_iter.rs:349-352` 原样返回打包字）。
- 机制/影响：注释口径误导读者低估读点成本（"零分配"仅指"不做 VSub 包裹、不烧 fuel"）。
- 处置建议：措辞改为"无包裹分配、无 fuel；解值克隆仍按 Val 克隆语义付费"。

### [P3] `run` 顶层循环逐 decl 查环境变量（影响面：L07/L08）
- 位置：`src/L07_sum_type/mod.rs:1334`、`src/L08_product_type/mod.rs:1342`：`std::env::var_os("L07_DEBUG").is_some()` 在每个顶层 decl 迭代内。
- 证据：同文件 `LOOP_DEBUG`（`mod.rs:24-25`）已示范 LazyLock<AtomicBool> 的进程级一次性读法。
- 机制/影响：每 decl 一次 env 查询（含锁下的 getenv），常数级；与既有模式不一致。
- 处置建议：改 LazyLock 静态开关。

### [P3] 参考版 eval_aux 的 Con 路径每字段下钻克隆分支体 Tm（影响面：L07–L09 参考版）
- 位置：`src/L07_sum_type/pattern_match.rs:579-587`：`(body.clone(), env.prepend(head.clone()))` per 分支尝试 + 递归子模式时 `cur.0.clone()` per 字段。
- 证据/影响：运行时每次 match 归约对分支体（Tm 深树）按尝试次数克隆；失败尝试的克隆整份丢弃。孪生版用 `&Tm` 借用穿针（`bump_spine_iter.rs:1960-1975`）零克隆。
- 处置建议：参考版可先以 `&Tm` 匹配、命中后再 clone 一次。

## 3. needs-verify 清单（验证方法）

1. **孪生版 force/frcs 每调用 Vec 分配的实际占比**（P3-2 的量化）：打 `l07bench --workload church` 用 dhat/自绘分配计数器对比"Machine 常驻缓冲"补丁前后的 malloc 次数与耗时。当前禁止 cargo，未实测。
2. **mentions_level/compose 在深嵌套下的回归幅度**（P3-1/P3-3 的量化）：把设计文档 §9.4 的 depth40 嵌套模式负载固化为 bench（即 P2-4 的处置），跑链表 σ vs FxHashMap σ 对照，验证"2.5×@depth40"口径并确认现表示不再回归。
3. **L12 quickfix 合成结果的跨进程非确定性**（P2-1 的实证）：同一触发输入在两个独立进程里各跑一次 LSP quickfix（或直接单测里两次 new 进程调 `Infer::search`），diff 返回的 `Ok(String)`；用足够多 decl 使 RandomState 顺序分化。静态论证已成立，实测留档更稳。
4. **meta 快照深拷贝在 L11 宏密集负载下的占比**（P3-6）：`l11bench --workload macro` + 分配剖析，确认 `meta.clone()`（`pattern_match.rs:158`）是否进入热点；是则优先做 undo-log。

## 4. 设计决定讨论（不属 bug，只记录）

- **σ = 持久化单链 + 条件包裹（非 FxHashMap）**：设计文档 §9 注记 4 已定稿，参考版（`mod.rs:199-211`）与孪生版（`SubstV`）一致。链扫描读点 vs 哈希读点的取舍成立前提是 |σ| 有界——目前无基准守护（见 P2-4），建议补负载后复核。
- **decl 表写时复制（`Rc::make_mut` 整表克隆）**：每 def 一次 O(|decls|) 克隆，累积 O(n²)——`l07bench.rs:142-145` 注释明示"strchain/global 的参考版超线性、默认不排 basic"，属已记载取舍。孪生版镜像同款（`bump_spine_iter.rs:51`），未借机修复，保持双实现同构。
- **force/quote 对卡住 match 分支体的"重求值再 quote/rename"**：为 quote→eval 往返恒等所必需（`mod.rs:1184-1203` 注释），simpl_decl/中性 decl 表是配套防发散手段；成本归入语义而非浪费。
- **确定性其余排查结论（无发现）**：六层所有 decl/src_names/name_map/class_instances 的 HashMap **迭代**仅用于 ①重建同构映射（simpl_decl/declb/subst_cxt——消费端只 get，顺序无关）；②报错文案里的实例列表（L10–L12 `class_instances: HashMap<_, Vec<Instance>>`，内层 Vec 保登记序，`elaboration.rs:381-386` 逐 Vec 输出，确定性成立）；③instance 求解按 Vec 序从尾/首尝试（`typeclass.rs:299-305` 等，登记序确定）。`HashSet`（nlvars、checked_ret、conv memo）均仅 contains/insert。pretty 输入为 List/Vec，序确定。唯一泄漏点即 P2-1。
- **L11/L12 `mutable_map` 用 `Rc<RwLock<HashMap>>`**（L11 `mod.rs:459`）：单线程下 RwLock 开销可忽略，换取 `Infer` clone 共享安全，合理。
