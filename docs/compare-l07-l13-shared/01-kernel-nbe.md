# 01 · 孪生 `bump_spine_iter` 的 NbE 内核：L07 ⟷ L13

## 1 范围与方法

范围 = 两侧 `bump_spine_iter.rs`（根聚合）+ `{machine,eval,force,quote,rename,spine,env,syntax,bench_src}.rs` 共 10 个文件（L07 7,494 行 / L13 11,256 行，按本地文件行数实测）。
方法：① MAP §1 的 6-token shingle 当筛子；② **同名配对会误判**（函数被拆分/改名），故对 4 个关键函数自算"真配对"（L07 `quote_iter` ↔ L13 `quote_go` 等），再与 Lead 的 `fn-matrix.tsv` 交叉；③ 按"值表示 → eval → force → quote → rename"逐机制抽读，每条断言带行号。
口径限制：全程只读 `src/`、未构建（禁 `cargo build/check/test`），**所有结论是读码结论，无运行证据**。

## 2 模块对位表

（"保留率"取 MAP §1 的文字/归一列；"复核"列是本轮实证，含自算的真配对数与 `fn-matrix.tsv` 的 body_sim。）

| 文件 | L07 tok/行 | L13 tok/行 | 保留率(文字/归一) | 判读 | 本轮复核证据 |
|---|---:|---:|---|---|---|
| `bump_spine_iter.rs`（根） | 328 / 156 | 745 / 299 | 51% / 91% | 继承 + 扩张 | 模块清单与 `pub(crate) use` 面逐项对应（L07:108-155 / L13:184-289）；L13 多 5 个 `mod`、多 86 行 L13 增量注释；新增导出 `v_u_of/env_collect/meta_unsolved/DeclEntry/Decls/TraitState`（L13:281-289） |
| `machine.rs` | 14,133 / 2,008 | 39,369 / 5,529 | 52% / 74% | 扩张 + 局部重写 | 同名小函数大量 1.00（`close_tm/insert/insert_t`）、0.86（`has_free_var`）、0.67（`new_binder`）；但 `clear_round` 0.06（15→68 行，L07:190 / L13:603），`infer_expr` 0.26（341→736 行）——**同一文件里"内核外壳没动、elaboration 重写"** |
| `eval.rs` | 3,537 / 517 | 4,745 / 693 | 77% / 83% | 继承 | 自算 `eval_iter`↔`eval_iter` = **86.0%**（269 行窗口内 2,632/3,373 tok）；`W` 工作栈 13 项里 10 项逐字对应（L07:126-166 / L13:202-251） |
| `force.rs` | 4,824 / 832 | 5,650 / 1,035 | **25%** / 49% | **重写 + 整块增删** | 自算 `force`↔`force_inner` = **33.6%**、`vapp1`↔`vapp1` = 46.4%；L07 侧 49% 的行（408/832）是 L13 完全没有的 σ/VSub 族（见 §4.1） |
| `quote.rs` | 4,635 / 674 | 4,212 / 680 | 56% / 67% | 继承（被改名掩盖） | `fn-matrix` 报 `quote_iter` 0.005，实为 L13 把本体拆成 `quote_go`（L13:124，423 行）+ 6 行壳（L13:93）；**真配对 77.9%**（自算） |
| `rename.rs` | 6,419 / 924 | 6,387 / 907 | 76% / 86% | 继承 + 局部改写 | RenBuf 族 `reset/get/set/has_mark/clone_valid/alloc_xname` 全 1.00；`invert_bump` 0.90、`prune_vflex_bump` 0.92、`prune_ty_bump` 0.92、`rename_iter` 0.71；**例外 `solve_bump` 0.14**（9→44 行，L13 加常数解 fallback） |
| `spine.rs` | 1,078 / 211 | 1,369 / 245 | 72% / 79% | 继承 | `spine_head/collect_args/spine_len` 1.00；差异集中在 `HK_*`：L07 有 `HK_PRIM=2`（L07:17），L13 换成 `HK_FLEX=1` 且无 `HK_PRIM`（L13:22-25） |
| `env.rs` | 787 / 131 | 877 / 148 | **98%** / 98% | 继承 | `env_nth/env_len/env_ext/env_ext_defs` 全 1.00；L13 仅多 `env_collect`（L13:66）与 packed-word 对齐断言 |
| `syntax.rs` | 1,834 / 308 | 1,680 / 299 | 70% / 69% | 骨架继承 / **值表示改** | 15 个 `v_*` 访问器 14 个 1.00、`v_u` 0.00（无参→带层级）；`Tm`/`XCell` 的**变体集本身变了**（见 §3） |
| `bench_src.rs` | 262 / 119 | 701 / 316 | 95% / 99% | 继承 + 新增 | `strchain_src/match_src` 1.00、`enum_src` 0.83；L13 新增 `natadd/gadt/moduletree/struct/wide_enum`，**丢了 `globals_src`**（L07:38） |

读法：**保留率高 ≠ 语义同、保留率低 ≠ 机制换**。本角度最典型的两处误读就是 `quote.rs`（56% 其实是继承）与 `force.rs`（25% 的一半是"另一侧根本没有的机制"）。

三条读表纪律（本轮实际踩到的）：

1. **函数被拆/改名时，同名配对会给出近 0 的假分**——`quote_iter` 0.005 只是因为 L13 的本体被移进 `quote_go`，必须按"本体"重新配对（本轮自算了 4 组）。
2. **文件级 keep 低，常见原因是"另一侧整块机制不存在"**——此时相似度无信息量，要看行预算分解（§4.1），否则会把 E3 误报成 E2 重写。
3. **文件级 keep 高，只说明"这一层没人动过"**——env 98% 不代表内核同源，只代表环境表示没被 namespace/HDL 需求碰到。


## 3 逐机制差异表（核心）

| # | 机制 | L07 实现（锚点） | L13 实现（锚点） | E 档 | 可观察后果 / 风险 |
|---|---|---|---|---|---|
| 1 | arena + 打包值底座 | `V(u64)` 低 3 位 tag，bump 单元 8 对齐（L07 syntax.rs:114-121, 219）；同 8 个 tag 号 | 同（L13 syntax.rs:117-124, 254）——**同一套编码，逐字相同** | E0/E1 | 无。这是"共有部分"最硬的内核资产 |
| 2 | tag 7 变体集 | `Lit/Decl/Prim/Obj/Sum/SumCase/Match/VSub` 8 个（L07 syntax.rs:220-256） | `Lit/**Nat**/Decl/Obj/Sum/SumCase/**Call**/Match` 8 个（L13 syntax.rs:255-298） | E2 | `Prim`、`VSub` 消失；`Nat`、`Call` 进入。**逐变体做 match 的每个调用点都要重看**（force/quote/rename/unify 四族） |
| 3 | 原生 Nat | 无（`succ^n zero` 一元链） | `XCell::Nat(u64)`（L13 syntax.rs:260）；装配点折叠 `nat_step_value`（prim.rs:281-296）；quote 经 `quote_nat_chain` 展开回链（quote.rs:617） | E4(L13) | 深 Nat 从 O(n) 节点变 O(1)；L13 自己因为"字段不查 tag 就解引用"出过 `STATUS_ACCESS_VIOLATION`，现补 `v_tag==7` 守卫（prim.rs:290，根注释 L13:99-107）——**E2 级的坑被修在 E4 的新机制里** |
| 4 | 宇宙 `U` | 立即数 `V(3)`，**不携带层级**（L07 syntax.rs:136-138；`Tm::U` 单元变体 L07 syntax.rs:28） | 层级进打包字 `v_u(lvl)` = `lvl << 3` 再加 tag 3（L13 syntax.rs:139-141, 218）；`Tm::U(u32)`（L13 syntax.rs:26）；unify 比层级（unify.rs:813） | E2 | L07 里 `U` 恒等、不可区分；L13 里 `U(0)≠U(1)`。同一 tag 3 的**负载语义不同**，跨版本读代码会把"宇宙无关"当默认 |
| 5 | prim 挂载点 | `Tm::Prim`/`XCell::Prim` + `HK_PRIM` 链头（L07 syntax.rs:41,224；spine.rs:17；force.rs:373-398） | 无 `Prim` 变体；挂在 decl 条目 `prim: Option<PrimId>`（L13 prim.rs:335）；执行点 = force 的 Decl 臂（force.rs:727-858） | E3(L07) + E4(L13) | 归约时机从"应用点"移到"force 的 decl 链头"；L13 还加了 `lazy_pure_prim`（force.rs:71,99）把纯 prim 推迟到 force——**求值顺序变了**，L07 的"prim 在应用时触发"直觉失效 |
| 6 | 构造子标识 | `SumCase{case_name: &str}`（L07 syntax.rs:48-52, 237），值层存名字 | `SumCase{index: u32}`（L13 syntax.rs:43-48, 280），值层存下标，名字反查 `cases[index]` | E2 | 值层不再能自证构造子名（要回查 Sum 单元）；`PatternDetail::Con` 首字段同步为 index（L13 根注释 bump_spine_iter.rs:24-26）→ 与模式编译器、pretty 的接口一起变 |
| 6b | Sum 的 trait 标记 | `Tm::Sum(name, params, cases)` 3 元（L07 syntax.rs:46） | 4 元，末尾 `is_trait: bool`（L13 syntax.rs:39；值层同步 L13 syntax.rs:270-275） | E4(L13) | trait 脱糖成 enum 后，`fresh_meta` 走"实例合成"而非普通构造（L13 syntax.rs:38 注释）——**同一 Sum 变体在 L13 有两种语义** |
| 6c | Call / OpCall | 无 | `Tm::Call`（syntax.rs:57）+ `XCell::Call`（syntax.rs:285）+ `W::CallAsm`（eval.rs:240）；`Tm::OpCall` 只在 export 显示层（syntax.rs:51-56 注释） | E4(L13) | 内核多一种"卡住的内联调用"头；v_app 要 prepend 实参并递归体（force.rs:143-156） |
| 7 | 卡住 Match 的应用 | `PendingCons` 链，O(1) 头插（L07 syntax.rs:265-270; force.rs:60-69），选中后按序 `vapp1`（force.rs:513-519） | **无 pending 字段**（L13 syntax.rs:290-297）；每次应用把实参 quote 成项 **splice 进每个分支体**（force.rs:157-191） | E2 | 每次应用开销 = O(分支数 × quote) + bump 节点；L07 自己的注释断言"项层 splice 会把实参自由变量引到错误上下文"（force.rs:63-64）→ **两版作者对同一语义给出互斥判断**，见 §4.3 |
| 8 | force 的燃料 | 每次展开 `burn(fuel)`（force.rs:301,314,339,358,380,411,458,470；池定义 prim.rs:61-62，轮界充值 machine.rs:197） | **force 没有 fuel 参数**（force.rs:532-540 签名只有 7 参）；终止靠 `eval_budget` 墙钟（eval.rs:288, quote.rs:624）与 `NAT_CHAIN_LIMIT`（prim.rs:770） | E2 | 见 §4.2。deterministic 预算 → 机器相关看门狗 |
| 9 | unify 的燃料 | 共享池（`&Fuel`，unify.rs:120）；耗尽尾巴 `" (fuel exhausted)"`（machine.rs:624-626） | 随对携带 `fuel: u32`（unify.rs:83），SumCase 内层/intersect 回落硬编码 100（unify.rs:332,1221）；入口常数 100（machine.rs:1570） | E2 | 错误文案面变（无 fuel 尾注）→ parity 比对的口径已不同；两版"何时判不出"的边界也不同 |
| 10 | 记忆化 | quote memo（L07 quote.rs:77）+ unify 判等 memo（machine.rs:113）；**force 无 memo** | quote memo 同（L13 quote.rs:87）+ `FORCE_MEMO`（force.rs:216, 612-639）+ `FORCE_PRIM_MEMO`/`PRIM_STUCK`（force.rs:765-800）；taint 门（force.rs:623-638） | E4(L13) | L13 的 force 有一层 L07 不存在的"可缓存性"逻辑；**taint 判定错 = 错误缓存**，这是 L13 独有的正确性风险面（作者已写两条走过的弯路，force.rs:553-569） |
| 11 | 栈安全 / 重入 | 单个共享 `workbuf` 给 eval/quote/unify，靠"进入即排空"不变式（machine.rs:148-155）；force 用本地草稿栈（force.rs:294） | **6 个独立工作栈**（machine.rs:407-415），因为 trait 求解会 `unify → solve → unify` 重入，入口要保存/放回外层挂起项（machine.rs:1508-1549） | E2 | L07 的"一个 workbuf 够用"在 L13 不成立；照抄 L07 的栈纪律会静默丢待办对（L13 注释给了症状：`Eq ?x ?y` 只解第一个参数） |
| 12 | occurs / 环守卫 | 显式三层：`val_mentions_lvl`（force.rs:172-281）+ `mentions_level` + `occurs_transitive`（unify.rs:515-525） | **无任何 occurs 扫描**（L13 孪生 unify.rs 无 occurs/mentions 符号）；环守卫隐含在 `rename_iter(…, None, 0, …)` 失败里（rename.rs:251） | E1[推断] | 安全性质可能仍成立（rename 只产闭项），但"浅扫 + 传递扫"两级保险在 L13 无对应物；失败文案从 `can't unify …` 变 `can't unify for unsolved meta`（machine.rs:1577-1581） |
| 12b | quote 的 Prim η 族 | `QNoEta`（quote.rs:33-35）、`prim_eta_quote`(148)、`quote_arg`(210)、`shift_tm_bump`(81)——为 `Tm::Prim` 的 λ 链体做 η 展开 | **整族不存在**（无 `Tm::Prim` 可 η；L13 `QJob` 12 项里无 `QNoEta`，quote.rs:36-80） | E3(L13) | `quote.rs` 56% 的分差主要来自这一族；L13 的 `QJob` 与 L07 逐项对应到 `App1/ChainRun/Obj1/SumAsm/SumCaseAsm` 为止 |
| 12c | solve 的返回类型 | `solve_bump(...) -> bool`（rename.rs:215-239） | `-> SolveRes` 三态 + "非可逆 spine 常数解 fallback"（rename.rs:223-256：空 renaming 试 rename，λ 层数取 `min(spine, Π 链)`） | E2/E4 | L13 能解出 L07 判 Stuck 的一类 meta（反之不成立）→ **接受集不同**；具体影响面移交 02-unify 核 |
| 12d | decl 表条目 | `DeclEntryF`：`Copy`、4 字段（`ty/val/prim/prim_names`，prim.rs:26-33） | `DeclEntry`：`Clone`、8 字段含 `span/Rc<String>/ty/vty/prim: Option<PrimId>`（prim.rs:304-336）；`Decls<'a> = FxHashMap<SmolStr, DeclEntry>`（prim.rs:340） | E2 | L07 的条目可随意 `Copy` 穿参；L13 每条目带 Rc + 两个 `&Tm`，写时复制（`Rc::make_mut`）成为内核侧成本与借用复杂度的来源 |
| 13 | 层→索引换算 | 裸减法 `level - v_lvl_of(v) - 1`（quote.rs:277, 462） | `lvl2ix` + checked_sub + 带文档的 panic（syntax.rs:179-191；调用点 quote.rs:155,388、machine.rs:2797,2939） | E2 | 越界（本就是 bug 态）时：L07 release **静默 wrap 成大 u32**、debug 才 panic；L13 一律带诊断 panic。**硬化只落在 L13 一枝**——回灌是单向的 |
| 14 | 命名空间键进值层 | 无（键 = 源码名） | `XCell::Decl{name}` 直接持限定键并原样给 pretty（syntax.rs:18-20,264）；`val_cache_key_t` 用 `XCell::Sum{name}` 拼缓存键（typeclass.rs:866-877）；`v_to_ref_val` 把 bump 值解码成参考域 `CVal`（typeclass.rs:898） | E2 | 命名空间**确实侵入了值表示**（以字符串键形式，不是新变体）：值层缓存键、pretty 输出、跨域解码都带前缀。对内核而言"名字"重新变成语义的一部分 |

## 4 抽样深挖

### 4.1 `force.rs` 的 25%：不是"换了一套"，是"少了一半 + 多加了一层"

L07 `force.rs`（832 行）按函数切：

| 区段 | 行 | 作用 | L13 有对应物？ |
|---|---:|---|---|
| vapp1 | 29-131（103） | 应用 | 有，但重写（46.4%） |
| `vapp_ok` + `project` | 132-171（40） | η 可应用性守卫 / 投影 | `project` 1.00；`vapp_ok` **改名搬家**为 L13 `unify.rs:190 is_appliable`（同一判据，按 L13 新变体集调整：`Call` 可应用、`Nat/Lit/Sum/SumCase` 不可）→ E1 |
| `val_mentions_lvl` | 172-281（110） | σ 的 occurs | **无** |
| `force` | 282-533（252） | 主循环 | 有，拆成 `force`(110 行 memo 壳) + `force_inner`(376 行臂集) |
| `frcs` | 535-766（232） | σ 推开 | **无** |
| `frcs_env` | 767-802（36） | σ 进闭包 env | **无** |
| `force_arg` | 803-832（30） | 逐层解 VSub | **无** |

⇒ σ/VSub 族 408 行 = **49%**，L13 一行都没有（L13 无 `subst.rs`，根注释 L13:171-175 自认）。L13 `force.rs` 反向多出 ≈320 行 memo/taint/统计（202-523）。真配对 `force↔force_inner` 33.6% 里丢掉的分，主要来自签名（10 参 → 7 参）与 `Prim`/`Match` 臂的消失，而不是"骨架换了"。**判 E3（缺 σ 族）+ E4（memo 层）+ E2（骨架按新值表示改写）**。

### 4.2 燃料：确定性预算 → 墙钟看门狗（E2）

```rust
// L07 machine.rs:620-627
self.fuel.set(unify_fuel_budget());
if self.unify(bump, &decls, cxt.lvl, t, t_prime) { Ok(()) } else {
    let fuel_note = if self.fuel.get() == 0 { " (fuel exhausted)" } else { "" };
```
```rust
// L13 machine.rs:1569-1571
self.constraints.clear();
let ok = self.unify(bump, cxt, cxt.lvl, t, t_prime, 100, &mut trait_err);
```

L07 的燃料是**跨 force/unify 的共享池**（`Fuel = Cell<u32>`，prim.rs:62），轮界充值、可被 `TYPORT_UNIFY_FUEL` 覆盖（prim.rs:68-75）——预算耗尽是一个**确定性**降级点，还会写进错误文案。L13 孪生把池整个删了：force 零预算，unify 只带一个随对透传的 `u32`，顶层入口写死 100（machine.rs:1570），SumCase 内层写死 100（unify.rs:1221）。终止性改由 `eval_budget::tick`（eval.rs:288、quote.rs:624）这个**墙钟**看门狗 + `NAT_CHAIN_LIMIT` 常量门（prim.rs:770）承担。
这不是"等价改写"：`(fuel exhausted)` 这条文案在 L13 孪生不存在（E2 的可观察证据之一），而墙钟中止点随机器/负载漂移，同一输入在同一台机器上两次 kick 也可能停在不同的 decl [推断]。**"共有部分的差异"在这里变成了"共有部分的语义前提不同"**——L07 的教科书式确定性预算，在 L13 生产层被换成了工程式超时。

### 4.3 卡住 Match 的应用：pending 链 vs 逐分支 splice（E2，两版作者互相否定）

```rust
// L07 syntax.rs:244-249 / force.rs:60-69（每次应用 O(1)）
Match { scrutinee: V, env: Env<'a>, cases: &'a [(PatternDetail, &'a Tm<'a>)],
        pending: Option<&'a PendingCons<'a>> },
let node = bump.alloc(PendingCons { arg: (a, i), next: *pending });
```
```rust
// L13 force.rs:177-185（每次应用：每分支 alloc 一个 App + 内嵌一次 quote）
.map(|(p, b)| ((*p).clone(), &*bump.alloc(Tm::App(*b, u_tm, i))))
```

两侧都声称自己"照参考版的 Match 臂"：L07 force.rs:63-64 明说"项层 splice 会把实参自由变量引到错误上下文"所以才用 pending；L13 force.rs:158 与 syntax.rs:291-292 明说"参考版 L13 同款"就是 splice。**这两句话不可能同时成立于"同一份实现"**——它们各自对本层参考版为真，对本层孪生互为反例。可观察后果：L13 每次向卡住 match 传参要付 O(分支数) 的 bump 分配 + 一次 `quote_iter`（且 `Vec::new()`×2），L07 是 O(1) 头插；在 HDL 负载（大量卡住 match + 逐个传参）上这是量级差 [推断]。语义是否真等价，读码无法判定 [未核实]。

### 4.4 本角度撞见但**不判**的三处交界（移交）

| 撞见的现象 | 锚点 | 为什么移交 |
|---|---|---|
| 结构相等整族从 `struct_eq.rs` 挪进 unify 快路径 | L07 有 `bump_spine_iter/struct_eq.rs`（428 行，`EQ_BUDGET=20_000` @ struct_eq.rs:21）；L13 无此文件（L13 根注释 172-173 自认） | 是"结构比较"的口径变化，归 02-unify |
| `v_to_ref_val` 把 bump 值解码成参考域 `CVal` 喂共享 `Synth` | L13 typeclass.rs:898；L13 根注释 68-70 | 值表示 ↔ 参考域的双向桥，归 03-cxt-refine / 02-unify |
| `PatternDetail::Con` 首字段从名字变 index | L13 根注释 bump_spine_iter.rs:24-26；具体在 pattern_match | 归 04-match |

## 5 本角度评级

**一脉相承 = 中。** 骨架是同一份（arena + 打包 tag 逐字相同、迭代内核 eval 86% / quote 78% / rename 76% / env 98%，quote memo 与 `MATCH_CMP_BUDGET=64` 两侧同口径），但**值表示是按各自参考版重造的**（tag 7 有 3 个变体互不相通、`U` 带不带层级、`Match` 带不带 pending），且两个"决定结果"的机制在 L13 侧整块不存在或被换掉（σ 精化 + 确定性燃料）。⇒ 共有的是**配方**，不是**实现**。

Top-3 差异（本角度）：

1. **确定性燃料池整体消失**：L07 `Fuel=Cell<u32>` 共享池 + `burn` 遍布 force/unify（prim.rs:62、force.rs:301/314/339/358/380/411/458/470、machine.rs:197/620）→ L13 孪生 force 零预算、unify 每对 `fuel:u32` 写死 100（machine.rs:1570、unify.rs:1221）+ 墙钟 `eval_budget`（eval.rs:288）——**E2**。
2. **σ/VSub 精化载体整块缺席**：L07 `XCell::VSub`（syntax.rs:255）+ `frcs/frcs_env/force_arg/val_mentions_lvl` 408 行（force.rs:172-281,535-832）+ `subst.rs` → L13 无任何对应物，环守卫改由 rename 失败兜底（rename.rs:251）——**E3**（连带让 `force.rs` 保留率跌到 25%）。
3. **卡住 Match 的应用机制分叉**：pending cons 链 O(1)（L07 syntax.rs:265-270、force.rs:60-69）vs 逐分支 `Tm::App` splice O(分支数)（L13 force.rs:157-191），且两侧注释互相指认对方"错/不符参考版"——**E2**，是"共有部分已不是同一份"的最直接文本证据。

## 6 给 Lead 的提醒（超出本角度）

1. **MAP §6.3 的"孪生层差异没有任何门禁会报警"对 L13 说过头了。** 封印只封了 `tests/l13_fast_parity.rs`（`#![cfg(feature="l13-twin")]`，L13:1）；`tests/twin_engine_tests.rs` **没有 gate**，仍逐条比对 twin↔reference 的 (severity, message, start, end) 诊断（tests/twin_engine_tests.rs:248、862、914）。而且 L13 孪生是 **LSP 的默认引擎**（src/lib.rs:297-302 未设 `TYPORT_LSP_ENGINE` 即 Twin）——它是活的生产路径，不是冻结标本。**只有 L07 孪生是真冻结**（`l07-twin` 门 + 仅 bench bin 消费）。这对"共有部分"的判定很关键：L13 侧的分叉有门禁兜底，L07 侧的分叉无人管。
2. **L13 孪生的内核正确性风险面已经不在 NbE 本身，而在 memo**：`FORCE_MEMO`/`FORCE_PRIM_MEMO`+`taint` 是 L07 完全没有的一层（force.rs:553-569 作者自记两条走过的弯路），而它只在 LSP 级测试里被间接覆盖。若 Lead 要排"最可能出隐蔽错误的模块"，我建议排 force memo 而不是 eval/quote。
3. **回灌是单向的，别按"成对提交"假设两边同步**：`lvl2ix` 硬化只在 L13 落地（syntax.rs:179），L07 孪生仍是裸减法（quote.rs:277、462）。反例也存在：L07 的 `globals_src` 基准负载在 L13 孪生丢了（L07 bench_src.rs:38），而 L13 的 `val_mentions_lvl` 等价物彻底没有。**同路径文件里"谁抄谁"要逐函数查**。
4. **别直接采信 `fn-matrix.tsv` 的低分行**：`quote_iter` 0.005、`machine.rs::unify` 0.012、`infer_decl` 0.001 都是同名不同物的误配（本体被拆成 `quote_go`/`unify_catch` 等）。我这边的真配对是 quote 77.9%、force↔force_inner 33.6%、eval 86.0%、vapp1 46.4%。
