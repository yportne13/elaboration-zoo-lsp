# 04 · 模式匹配编译与覆盖判定（L07 ⟷ L13）

## 1 范围与方法

- 角度：`match` 的**编译形态**、**覆盖/可达判定**、**诊断面**、**燃料预算**、`shape.rs` 的形状认回。
- 覆盖文件：`pattern_match.rs`（L07 850 行 / 4,972 tok · L13 819 行 / 5,305 tok）、`shape.rs`（120/689 · 146/943）、孪生 `bump_spine_iter/compiler.rs`（676/4,434 · 916/5,679）；旁证 `mod.rs` 的 `MATCH_CMP_BUDGET`/`UNIFY_FUEL`、L13 独有 `eval_budget.rs`（144 行）、`canonical.rs`。
- 方法：grep 建符号表（两侧同名函数 12 个）→ 逐函数读 + `git log -S` 定年代 → 用 Lead 的 `fn-matrix.tsv`（body_sim）交叉验证；行号均在本轮 HEAD `911628b3` 核过。**未构建、未跑二进制**（禁止 cargo），动态结论一律标 [推断]。
- **前提更正**：`PM_FUEL` 在本轮代码里不存在（两章 `grep -i pm_fuel` = 0）。真实的预算是 `MATCH_CMP_BUDGET=64` + `UNIFY_FUEL=4096`，**两侧都有**（见 §4.3）。

## 2 模块对位表

| 文件 | L07 tok/行 | L13 tok/行 | 保留率(文字/归一) | 判读 |
|---|---:|---:|---:|---|
| `pattern_match.rs` | 4,972 / 850 | 5,305 / 819 | **22% / 48%** | **同骨架重写**：算法段逐段对应，载体（σ→update_cxt、String→SmolStr、Val→Rc<Val>）全换，故逐行 diff 为 701 增 / 732 删 |
| `shape.rs` | 689 / 120 | 943 / 146 | 76% / 86% | **继承+适配**：同一显示启发式整体平移（body_sim：from_val .80 / shapes_for .79 / match_to_decl .71 / peel .48） |
| 孪生 `bump_spine_iter/compiler.rs` | 4,434 / 676 | 5,679 / 916 | 28% / 55% | **同骨架重写**，且是"参考版的翻译"（L13 文件头自述「参考版 pattern_match.rs 的逐臂下钻移植」，compiler.rs:1-4） |
| `eval_budget.rs` | —（无） | 6,985 B / 144 | — | **E4 单边新增**，职责与 match 判定无关（§4.3） |

函数级 body_sim（与 `tmp/fn-matrix.tsv` 同口径，供对照）：`covers` .54/.58、`is_catch_all` .63/.58、`compile` .32/.28、`probe_accessible` .22/.28、`unify_indices` .26/.11、**`eval_aux` .009（9 行 vs 68 行）**。
⇒ 保留率低不是"各写各的"：**被保留下来的正是判定助手（covers / is_catch_all / shape）**，被重写的正是与载体耦合的部分（探测、分派、诊断）。

## 3 逐机制差异表（核心）

| 机制 | L07 实现（锚点） | L13 实现（锚点） | 档 | 可观察后果 / 风险 |
|---|---|---|---|---|
| 编译形态 | 逐臂下钻，保用户顺序、首匹配（pattern_match.rs:29, 191-283） | 同（:273-287, 475-477；注释"L07 口径，2026-09-18 自决策树矩阵重写"） | E1 | 无（同一算法）。史实：L07 在 `c6b8ee2e`(2026-08-29) 已是逐臂；L09–L13 才于 2026-09-18/19 从决策树迁来（L13 `448775c2`）⇒ **L07 是源，L13 是移植** |
| 覆盖前置循环 | 遍历构造子，可达且无臂覆盖 → 报缺（:179-190；`covers`:828-833） | 同循环、同 `covers` 判据（:515-533；:801-809） | E1 | 无 |
| U2「穷尽 match 跳过探测」 | `fully_covered` 短路（:169-190，`a78daec7` 2026-11-10） | 同（:509-533，注释明写「port L07 a78daec7」；`55f2d42e` 同日） | E1 | **有对应物**。但两侧**孪生都没有 U2**（L07 twin compiler.rs:148-155 / L13 twin compiler.rs:555-567，均无条件逐 ctor 探测） |
| 可达性探测 | `probe_accessible` 返回 bool；Absurd→不可达，Undecided/Fuel→**可达**（:340-418，:402-411） | 返回 `Walk`；Fuel→Matched、Absurd→Unreachable、Undecided→**Undecided**（:129-219，:203-214） | **E2** | 见 §4.1：非穷尽 match 在 L13 可被静默接受 |
| 探测上下文 | 用**超上下文的 scratch 层级** `Lvl(lvl.0+scratch)`，塞进 solvable（:385-389） | 把 fresh rigid **绑进 probe_cxt**（:189-192；注释：update_cxt 的 lvl2ix 超层会 panic） | E2 | 载体约束的直接产物；探测期 cxt 更长、可解集口径不同 ⇒ 同一方程可能得出不同结论 [推断] |
| 构造子类型获取 | 手工拼 decl 键 `Sum.Ctor`（:360, :554） | `infer_expr(Raw::Obj(..))` 交命名空间（:163-167）；孪生另有 decl 直查快路（compiler.rs:338-353） | E1/E2 | 名字世界化；同名 case 不再靠后缀回退 |
| 无参 Sum 短路 | 无 | `:139-149` 独有：params 空 ⇒ 直接 Matched | E4 | 探测次数大降；对无参枚举结论与 L07 的"空参数表 zip 恒真"一致 [推断] |
| 索引方程 | `unify(..., Some(&mut SpecSolve))`（:426-467），每方程 `reset_unify_kind`+`reset_match_cmp_budget`（:448-451） | `unify_pm`（:224-251），同两个 reset（:244-245） | E1 | 预算纪律**逐点相同** |
| 形状不合约 | 当 `IndexUnify::Msg` → 上层按**可达**且报错（:410, :437-443） | 直接 `UnifyKind::Absurd` → **不可达**（:234-239） | E2 | 内部不变量破坏时 L07 报错、L13 静默丢臂（仅在畸形输入可见） |
| 头部精化 | walk_con 末尾把被匹配变量写进 σ：`Val::SumCase{typ,case_name,datas}` + occurs 守卫（:728-745） | **无此步**；精化由 `check_pm_final` → `update_cxt` 臂上下文承担（:583-591） | **E2/E3** | 语义断点，与 03 号角度（σ vs update_cxt）同源 |
| 臂级诊断 | `errors: Vec<String>` → 单个 `Error(text, first_span)`（:325-330）；文案"分支不可达：…被前面的通配臂遮蔽 / …与被匹配类型不相容 / 无法判定：…"（:203 / :255 / :268） | `Vec<Warning>`（:31-53，"unreachable pattern: …"），调用方在 **scrutinee span** 转成一条 Err（elaboration.rs:1174-1177），其余 Error 进 `accumulated_errors`（:1184-1190） | **E2** | 同一程序：L07 一条诊断、指向**模式**；L13 多条诊断、指向**被匹配表达式**，文案中英不同 |
| 覆盖缺失文案 | 顶层"match 不完整：缺少构造子 X"（:187）；嵌套"match 不完整：模式位置 … 缺少构造子 …"（:317-321） | 顶层"non-exhaustive pattern: … not covered"（:527-531，形态为「构造子 + 999 通配」）；嵌套**逐字同 L07**（:666-670） | E2（顶层）/ E1（嵌套） | 999 通配是 L10–L12 遗留的产出形态 |
| 不可达臂的等级 | 硬错误（:199-205） | Warning，但调用方立即转 Err（elaboration.rs:1174-1177） | E1 | 等级已对齐（`9a389dd8` 2026-09-20「与 L09–L13 拉齐」）；差异只剩文案/span |
| 编译产物 | `Con(name, subs)`/`Any(span)`/`Bind(name)`（:746 / :486 / :528） | `Con(idx,name,subs,qual)`/`Any(var,param,icit)`（:468 / :300） | E2 | 决定运行时分派方式（§4.2） |
| 运行时分派 | 逐臂线性、**按构造子名**，含 `in_type` 校验与"非该类型构造子→当变量模式"兜底（:766-824） | 两趟：先 **by-index** Con 臂，再 Any/Bind 兜底；原生 `Val::Nat` 直接分派（:690-751） | **E2** | 见 §4.2；L13 的"Con 优先"与 L07"严格首匹配"不同，靠遮蔽报错兜住 |
| 燃料（参考版） | `MATCH_CMP_BUDGET=64`（mod.rs:801）、`UNIFY_FUEL=4096`（:774）、`TYPORT_UNIFY_FUEL` 环境覆盖（:776-787） | `MATCH_CMP_BUDGET=64`（mod.rs:1475）、`UNIFY_FUEL=4096`（:1468）、**无**环境覆盖 | E1 + E3(尾项) | 预算同值同点；L07 有基准放大逃生门，L13 无 |
| 时间/内存护栏 | **无**（`ElabTimeout`、`deadline`、`Instant` 在 src 中 0 命中） | `eval_budget.rs`：`ElabTimeout` / `NAT_CHAIN_LIMIT=2^22`，checkpoint 在 eval 主循环（mod.rs:3446-3448） | **E4** | 不同职责（§4.3），**不是** MATCH_CMP_BUDGET 的替代 |
| 孪生侧燃料 | 显式 `mach.fuel.set(unify_fuel_budget())` + "fuel 耗尽按可达处理" + "(fuel exhausted)" 尾注（compiler.rs:133, 348-354, 391-401） | 全文件 **0 处** fuel 引用；`unify_indices` 直接返回 bool（compiler.rs:234-257） | **E2/E3** | §4.3；封印孪生后无门禁 |
| 孪生覆盖检查 | 线性 `covers` | `CtorIndex`（≥16 ctor 才建表，compiler.rs:816-905）+ `case_spans_memo`（:71, :99-111） | E4 | 等价性论证写在注释里；窄表零分配 |

**Q4 · shape.rs 成对提交核对**（`6f7e245e` L07 / `c824c43a` L13，均 2026-11-23，提交信息逐字相同）：两侧都是**纯新增**（L07 +120 行 shape.rs、L13 +147 行），函数名与结构一一对应，**是真对齐、不是同名提交**。但 L13 侧有 3 处必须改写，其中 1 处是**判据分叉**：①`peel` 多剥 `Val::Call`（shape.rs:90-92；L13 的 def 体包成 Call，不剥则值来源形状永远登记不上）；②新增 `pats_eq` 忽略 binder 名（:60-70；L13 的 `PatternDetail::Any` 带 fresh 名 `_l0`，`PartialEq` 会认不回）；③`match_to_decl` **丢弃 env_len 比较**（:134-139 只比 pats），而 L07 保留 `s.env_len == shape.env_len`（shape.rs:111）。⇒ 成对提交 = 人工按需移植；shape 层确属"一脉相承"，但分叉根源是 PatternDetail/Val 表示差异（E2 外溢到显示层）。这是**显示层**，不进语义/性能路径（两侧注释同款，L07:14 / L13:17）。

## 4 抽样深挖

### 4.1 Undecided 的覆盖义务：两侧方向相反（E2）

```
// L07 pattern_match.rs:402-411 —— 只有 Absurd 判不可达
// P3：只有**结构矛盾**才判不可达；"无法判定"与 fuel 耗尽按可达处理（保守地要求覆盖）
Err(IndexUnify::Kind(k)) => k != super::UnifyKind::Absurd,
Err(IndexUnify::Msg(_))  => true,
```

```
// L13 pattern_match.rs:203-214 —— 预算档按可达，语义档"判不出"独立成第三态
// 只有预算耗尽…才按可达处理（避免深负载下非穷尽 match 被静默接受）
Err(UnifyKind::Fuel)      => Walk::Matched,
Err(UnifyKind::Absurd)    => Walk::Unreachable,
Err(UnifyKind::Undecided) => Walk::Undecided,   // 覆盖检查里 != Matched ⇒ 不要求覆盖（:653-659）
```

**为什么是 E2 而不是 E1**：两版都做值级探测（先例化构造子 Π 链、再逐槽跑索引方程），但**对同一探测结果的处理方向相反**。L07 把"判不出"归入可达 ⇒ 覆盖检查要求该构造子被覆盖（也可能在臂上直接报"无法判定"硬错误）；L13 把它归入"不计覆盖义务" ⇒ 同一份"卡住索引方程"的程序，L07 拒绝、L13 接受。这并非笔误，而是 L13 明确选择的产品口径（注释自述"与 L12 的 σ 路线不同，记录为载体约束下的偏差"，:207-210）：`update_cxt` 下臂上下文可能解出探测期解不出的方程。**代价**：L13 侧"静默接受非穷尽 match"的风险在 L07 侧不存在；反向，L07 会在合法程序上误报"无法判定"。

### 4.2 编译产物与运行时分派：by-name → by-index（E2）

```
// L07 pattern_match.rs:796-821（eval_aux_arm）：按名字 + in_type
let Val::Sum(_,_,ctor_names) = typ.as_ref() else { return None };
let in_type = ctor_names.iter().any(|c| c.data == name.data);
if in_type && case_name.data == name.data { /* zip datas 下钻 */ }
else if !in_type { Some(env.prepend(head.clone())) }   // 非该类型构造子 → 当变量模式
```

```
// L13 pattern_match.rs:690-705 / 725
Val::SumCase { is_trait: _, typ: _, index, datas } => (*index, datas.clone()),
Val::Nat(k) if *k == 0 => (0, Rc::new(vec![])),          // 原生 Nat 的 O(1) 分派
PatternDetail::Con(constr_, _, item_pats, _) if *constr_ == index => { … }
```

| 维度 | L07 | L13 | 后果 |
|---|---|---|---|
| 分派键 | 构造子**名**（`case_name == name`） | 构造子**下标**（`index`） | 跨枚举同形不再混淆；但也丢了 `in_type` 这道校验 |
| 头形态 | 只有 `Val::SumCase` | `SumCase` **或** `Val::Nat(k)`（succ 字段合成为 `Nat(k-1)`） | 大字面量 match 从 O(链) 变 O(1)；观测面/性能差异 |
| 臂序 | 严格首匹配（单趟） | 两趟（Con 优先，Any/Bind 兜底） | 依赖编译期"通配臂之后一律报不可达"保证等价；该检查若被绕过（如孪生只发 Warning 而调用方未转 Err）语义会漂 |
| 兜底 | `!in_type` ⇒ 当变量模式（宽松兼容） | 无对应分支 | 畸形/手工构造模式上可观察 [推断] |

顺带定位 Q5 的"卡住值能否再应用"：**两侧都能**，但机制不同。L07 在 `force` 的 `Val::Match` 臂里：scrutinee 被 force 成 `SumCase` 且成功 `burn(unify_fuel)` 才重选分支，选中后补 `pending` 实参（mod.rs:1008-1030）；L13 在 `Frame::Match` 里对 `SumCase`/`Nat` 直接调 `eval_aux`，**不烧 fuel**，未命中则重新包回卡住 Match（mod.rs:3681-3722）。⇒ `SumCase.typ` 在 L13 **不参与分派**（只在打印/quote 用），L07 用它做 `in_type` + 名字比对；"再应用"语义两侧都在，但触发条件与计费不同。`canonical.rs`（typeclass 实例搜索 IDDFS，:9-31）与 `termination`（引用于 mod.rs:428、孪生 machine.rs:3764）都**不进** `pattern_match`（grep 0 命中）⇒ 它们不改变 match 的编译输入。

### 4.3 三层"燃料"：哪层是同一件事，哪层不是（答 Q3）

| 层 | L07 | L13 | 判定 |
|---|---|---|---|
| 卡住 match 比较次数 | `MATCH_CMP_BUDGET=64`（mod.rs:801）：顶层入口重置，`(Match,Match)` 慢路径计数 | `=64`（mod.rs:1475），同文档、同口径 | **E1 同一职责**（真·一脉相承） |
| 共享递归 fuel | `UNIFY_FUEL=4096` + `TYPORT_UNIFY_FUEL` 覆盖（mod.rs:774-787） | `=4096`，无环境覆盖（:1468） | E1（尾项 E3） |
| 时间/内存护栏 | 无 | `eval_budget.rs`：`ElabTimeout`（墙钟 deadline，`panic_any` 由 LSP/CLI 边界 `catch_unwind`）、`NAT_CHAIN_LIMIT`（原生 Nat 链展开分配上限） | **E4 不同职责** |

```
// L07 bump_spine_iter/compiler.rs:348-354（孪生）—— fuel 耗尽 ≠ 结构冲突 ⇒ 按可达
// fuel 耗尽的失败是预算问题而非结构冲突：按可达处理（保守地要求覆盖）
Self::unify_indices(mach, bump, cxt, lvl, &mut spec, head_sum, ret_sum, ctor).is_ok()
    || mach.fuel.get() == 0
// L13 bump_spine_iter/compiler.rs:234-257（孪生）—— 无 fuel 概念，直接 bool
) -> bool { … if mach.unify_pm(bump, cxt, *a, b.val, &span).is_err() { return false } … }
```

为什么 `eval_budget` **不是** `MATCH_CMP_BUDGET` 的 L13 版本：前者拦的是"无终止求值"（零参 def 自旋、`nat_mul 100000 100000` 的 10^10 次分配），checkpoint 在 **eval 主循环**（mod.rs:3446-3448），后果是**中止整次运行**（超时诊断或孪生回落参考版）；后者只影响**一次合一判定**，后果是"判不出"。两者既不同层也不同后果。**真正的 E2/E3 在孪生**：L13 孪生 match 编译器把 `Fuel` 与 `Absurd` 一起当"不可达"（返回 false ⇒ 丢臂），L07 孪生按可达处理（⇒ 报"不完整"或"不可达"）——**同一深负载输入下两侧诊断相反，且封印孪生后无任何门禁会报警**。

## 5 本角度评级

**评级：中（骨架同源，判定与诊断面已分叉）**——"逐臂下钻 + 两段式嵌套覆盖 + 值级可达探测 + U2 跳过 + MATCH_CMP_BUDGET=64"这一整套设计与纪律在 L13 是**逐段对应**的（多处注释直接写「L07 同款」「port L07 a78daec7」），但精化载体（σ→update_cxt）、编译产物（name→index）、诊断通道（String→Warning+span）三处改动，使 22% 逐字保留率背后的"语义等价"不再可推。

Top-3 差异：
1. **Undecided 的覆盖义务反向**（E2）：L07 按可达要求覆盖（pattern_match.rs:402-411）／L13 不计义务（:203-214, :653-659）⇒ 卡住索引方程的同一程序，L07 报错、L13 静默接受。
2. **诊断面整体重写**（E2）：L07 单条中文 Error + 首条模式 span（:325-330）；L13 `Warning` 英文文案 + 999 通配形态 + 错误落在 scrutinee span（elaboration.rs:1174-1177），其余错误转多条诊断（:1184-1190）。
3. **孪生侧燃料机制缺失**（E2/E3）：L07 孪生有 fuel 判定与 "(fuel exhausted)" 尾注（compiler.rs:348-401），L13 孪生 0 处 fuel、`Fuel≡Absurd≡不可达`（:234-257）——封印后无人报警。

**最可能在真实程序上暴露差异的 2 个场景**：
- ① **GADT/索引卡住的 match**（`Vec[A] (succ n)` 上缺 `nil`、`Eq (add x zero) (add y zero)` 这类递归相等）：直接命中 Top-1，L13 比 L07 更"宽容"。
- ② **宽枚举（≥16 构造子）+ 大量臂**：L13 走 `CtorIndex`/`covered()` 与 U2 短路，L07 孪生仍是 O(n³) 名扫描且无 U2 ⇒ 诊断**条数/顺序**与耗时都会分叉（两侧参考版则一致）。

## 6 给 Lead 的提醒（超出本角度）

1. **`PM_FUEL` 在 HEAD 上不存在**（两章 `grep -i pm_fuel` 均 0）。凡"L07 有 PM_FUEL / L13 用 eval_budget 对应"的叙述都要改口径：真实对位是 `MATCH_CMP_BUDGET+UNIFY_FUEL`（两侧同名同值，E1）与 `eval_budget`（E4 新职责）。
2. **`check::<CANONICAL>` 与臂体硬编码不一致**：L13 顶层合一走 `unify`/`unify_catch` 二选一（elaboration.rs:1207-1224；`const CANONICAL` 见 :997/:1042/:1236），而 `pattern_match` 的臂体检查写死 `infer.check::<false>`（pattern_match.rs:617）⇒ **臂体永远走非 canonical 路径**。跨 02/03 角度值得核：同一表达式在臂内/臂外可能得到不同合一入口与错误文案 [推断]。
3. **`fn-matrix` 的两处要按实读**：`pattern_match.rs:eval_aux` body_sim 0.009 是**真实重写**（by-name→by-index，§4.2），不是"同名误配"；两侧 `Val::SumCase` 字段结构不同（L07 3 字段含 `case_name`，L13 4 字段含 `index`/`is_trait`），凡引用"SumCase 同源"的表述都要按此更正。
4. **L07 内部就不一致**：参考版有 U2（`fully_covered`）而 L07 孪生没有；故"孪生=参考版的镜子"在 match 编译层不成立——若 07 号角度要论证"封印孪生导致差异无门禁"，这是又一处可在 L07 单侧复现的样本。
