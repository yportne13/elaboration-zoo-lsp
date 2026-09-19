# L11：宏（macro_rules）与 decl 表世界

本层在 L10 的全部语言面（trait/typeclass、接收者方法调用、`outParam`）之上加
`macro_rules` 声明级/表达式级宏与可变全局 builtin，并把全局名字世界从 L09/L10
的"`Infer.global` 大下标哨兵"切换到**名字键 decl 表**（`Val::Decl` 全局头；
`1919810` 哨兵在本层的同源位置不复存在，属架构演进而非缺口）。参考版是
L13 引擎的早期形态：`Arc` 持久化（`type Rc<T> = std::sync::Arc<T>`，
mod.rs:20）+ decl 表贯穿；快版孪生 `bump_spine_iter.rs`（L10 冠军配方移植，
commit `5cae365`）。

本 README 主线是 2026-09-18 前后的匹配编译器三连改造（参考版 + 孪生同步
落地，L11 是五层中的第一个落地层）：决策树矩阵 → **逐臂下钻**（`6ae12a6`）、
覆盖探测从推断级改**值级结构探测**（`f5952cf`）、评审修复轮恢复**嵌套覆盖
检查**（`f774703`），见 §2。诊断收窄的算法级出处登记在
`docs/l09l13-match-compiler-analysis-2026-09-17.md`。

---

## 1. 语言特性

### 1.1 宏：解析期展开的 macro_rules

宏在 **parser 内**处理：`macro_rules <name>` 在声明点把规则表登记进
`MacroState`（三元组：解析错误累积 + 宏表 + `MacroExpansionInfo` 表，
parser/mod.rs:134），调用点由 `p_raw` 沿途展开（parser/mod.rs:1310）——
展开发生在造 Raw 之前，类型检查器看不到宏的存在。机制分解：

- **匹配器**（`MacroMatcher`，parser/macros.rs:10-27）：普通 token 匹配、
  元变量捕获（片段 `Ident` / `Raw`（`$x: raw` 吃任意 raw） / `Param`）、
  `Many0`/`Many1`/`Optional` 重复、序列；
- **转写器**（`MacroTranscriber`）：Basic / Sequence / Group / BuiltIn——
  BuiltIn 即无文本定义的内建 `stringify`（`MacroRule` 的
  `def_*_offset` 全 None，parser/macros.rs:348-358）；
- **展开 = 直接 token 拼接**（`splice_transcriber`，`be8ec25`，实测
  -15~-18% fast_run）：不再经过「序列化成文本 → 重词法」往返；
  `splice_push`（parser/mod.rs:224-237）按构造复刻整串重词法的两个归一化
  行为（相邻 EndLine 折叠、丢 Eof），保证 token 流与旧路径逐 token 一致；
- **LSP 记录**：每个展开点记 `MacroExpansionInfo`（调用点 span、展开文本
  `expanded_text`、`name_token_is_macro` 消歧、宏定义位置
  `def_start/end_offset + def_path_id`，parser/mod.rs:9-29）——goto-definition
  的数据源；
- **深度守卫 `MAX_MACRO_EXPANSION_DEPTH = 256`**（`f51a0e4`，
  parser/mod.rs:140）：自递归宏（`macro_rules m { () => { m } }` +
  `def x = m`）展开后再次命中同名宏，不加限制会无限递归直至栈溢出（LSP
  可在任意用户源码上触发）。thread_local 计数 + RAII `MacroDepthGuard`
  （parser/mod.rs:142-169），超限推 IError
  `macro expansion too deep (limit 256)` 并停止展开——用解析错误替代崩溃；
- `#[macro_export]` 属性在声明点解析（parser/mod.rs:2038-2041）。

两个已验证的使用形态（l11bench `macro` 负载的构成）：声明级宏
（`make_bool` 展开成整个 enum 声明）与表达式级宏（`def c{i} = addtwo
c{i-1}`，每层一次 `$x: raw` 捕获 + 转写）。

其它语法面：隐式实参逗号合写 `f[A, B]`（本章形态，已回移植 L06-L10，
`e2d04bb`）；后缀单实参括号组消歧 `f a (b) ≡ f a b`（`0958e2e`）。

### 1.2 decl 表世界（名字键全局）

顶层 def/enum/构造子/内建全部登记在 `Cxt.decl`：
`type Decl = HashMap<String, (Span, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>`
（mod.rs:22）。项层引用是 `Tm::Decl(name)`，eval 的 Decl 臂查表取登记值，
未登记卡 `Val::Decl(name, [])`（mod.rs:844）——递归自引用就是
`fake_bind` 插进去的存根。要点与取舍：

- **递归 def 与重定义**：检查前 `fake_bind`（cxt.rs:392-408）把名字占成
  Decl 存根，撞名（含内建）报 `redefine {name}`；检查后 `decl()`
  （cxt.rs:438-454）静默覆盖为真值（其撞名检查被注释）——与 L07/L13
  一致：redefine 检查只罩 def/enum 名，构造子裸名跨 enum 重复仍按最后
  注册解析。
- **`Cxt.decl` 按 Rc 共享**（`53e8adb`）：此前按值持有 HashMap，
  `bind`/`define`/`new_binder`/`subst_cxt` 每次构造 Cxt 都克隆整表——
  探针实测 `struct` 负载 k=11 单 run 约 7 万次整表克隆、1.04 亿次条目
  拷贝（键是 String，每次克隆一次堆分配）。改 `Rc<Decl>` 后引用计数递增
  O(1)、插入走 `Rc::make_mut`，写时复制语义不变：`struct` 2952→846 ms、
  `macro` 2696→842 ms（3.2–3.5×）。插入路径的整表克隆残留（O(n²)）与
  String 键未动，见 `docs/perf-l08l13-followup-2026-09-17.md` §3.4。
- **builtin 是 5 个带类型的 `Tm::Prim(typ, PrimFunc)`**：`string_concat` /
  `string_to_global_type` / `create_global` / `change_mutable` /
  `get_global`（cxt.rs:28-92，注册在 `Cxt::new` 的 decl 表里）；可变全局
  走 `Infer.mutable_map`（每轮清空）。 PrimFunc 是
  `Rc<dyn Fn>`（mod.rs:64）——孪生侧不能在 bump 里携带闭包，见 §3。
- **精化交互**：`subst_cxt`（cxt.rs:456-483）只包 env 槽与 src_names 的
  类型包，lvl/locals/pruning/**decl**/namespace 不动（旧 `update_cxt` 也
  从不改写 decl 表）；`val_mentions_lvl` 对 Flex 的 spine 与 Decl 头都不
  扫（mod.rs:420-422）——全局声明头不可能被模式精化解掉，spine 是作用域
  事实。
- **Match 分支体的往返**：quote/rename/unify 的 Match 臂在 **declb 存根
  表**（全表条目换成 `Val::Decl` 存根的重建表）下重求值分支体，避免递归
  调用在往返中被重展开。参考版的同类重建 2026-09-17 已提到分支循环外
  （`53e8adb`，实测无差别——命中路径的 decl 数只有十位量级，作一致性
  清理）；孪生侧的 declb 缓存见 §3。
- **Def 臂的 pretty 残留**：L10 已把 `DeclTm::Def` 的 eager nf+pretty
  两字段整体删除（L10 README §5），本层只做了 body 侧——`body_pretty`
  置空（elaboration.rs:421），`typ_pretty` 仍每 def 做一次 nf + pretty
  （elaboration.rs:420）。无消费方（`run` 只取 `DeclTm::Println`），大值
  负载上是参考版侧的固定开销（占比未核实）。
- trait 面与 L10 同构：本层有自己的 `typeclass.rs`，参考版与孪生**共用
  同一 `Synth`**；def 体检查完统一 `solve_multi_trait`
  （elaboration.rs:372）。trait 未解 meta 的诊断比 L10 更细
  （`cannot infer typeclass` / `no (matching) instance` + available
  instances 列表，elaboration.rs:375-418）。

## 2. 匹配编译器：决策树 → 逐臂下钻

### 2.1 动机与移植（`6ae12a6`，五层第一个落地）

L09–L13 参考版与孪生都用**决策树矩阵**编译 match，`docs/bench-matrix-
2026-09-17.md` 的 match 行显示孪生反而比参考版慢（L11 首测 0.3×）。
诊断（`docs/l09l13-match-compiler-analysis-2026-09-17.md` §1）把耗时全部
定位到**编译期**（L11 孪生，match k=9）：elab 2.35 ms / quote 0.00 ms，
def 内 check 占 100%，check 内 compile 占 100%，其中决策树访问 360 个
节点（每 def ≈30 次，L07 逐臂只走 2 条臂）、`filter_accessible_constrs`
占 elab 34%（逐 (构造子 × 臂) 重复探测 + 逐节点上下文克隆）。只做常数
优化（记忆化）最多整层 ~1.25×，与换算法的 ~20× 不是一个量级，遂按 L07
口径整体重写：

- 参考版 `pattern_match.rs`：删 `compile_aux`/`fill_context`/`next_hole`/
  `MatchContext`/`MatchArm`/`PatConstructor`，改逐臂 `compile`（每臂一次
  `check_pm_final` + `subst_cxt` + 期望类型重锚 + 体检查）+ `walk_pat`
  （L07 `walk_con` 口径的槽位纪律）；
- 孪生 `bump_spine_iter.rs` 同款重写；净减 ~690 行；
- 实测（l11bench 同窗口交错取 min，k=11）：参考版 basic 1.250→0.542 ms
  （2.2–2.3×）；孪生 fast_ss 1.524→0.180 ms（8.5×）、fast_run
  1.575→0.228 ms（6.9×）。

**订正**：移植当时同窗口 A/B 报过"孪生/参考 → ~3×"，那是该窗口参考版被
测偏慢（basic 0.542 vs 矩阵复测 0.230）所致；以 09-18 矩阵口径为准，
match 上孪生/参考是**持平到略优**（`fast_run` 1.02× / `fast_ss` 1.31×），
与 L07/L08 的 3× 领先尚有差距，但不再落后（
`docs/bench-matrix-2026-09-18.md` §0）。

### 2.2 覆盖探测：推断级 → 值级结构探测（`f5952cf`）

逐臂重写后，`filter_accessible_constrs` 成了 match 编译的唯一热点。旧实现
是**推断级**探测：每个构造子拼一个带洞的 Raw，逐层 `infer_expr` + quote +
`bind_name`（孪生还 clone_cxt），整体套 `run_pure_probe`（meta 表快照/
回滚）大包装。新 `probe_accessible` 是**值级**的（L07 口径）：

- 参考版：decl 表裸名取构造子类型值（`DeclEntry.vty`），Π 链上枚举隐式
  参数用头部 Sum 的 Impl 实参实例化、其余绑定器用 scratch 层 fresh rigid
  （不进 cxt），返回 Sum 与头部 Sum 参数逐槽 `unify_pm`（以
  `SpecSolve { acc }` 作种子，头部一侧在前）；只快照/回滚 meta 表；
- 孪生：`decls` 取 `DeclEntry.vty`、`env_ext` + eval 走 Π 链、`unify_pm`
  同点充值 `refuel()`；
- `elaboration.rs` 的 `SpecSolve`/`unify_pm` 提为 pub(crate)——探测复用
  同一套特化方程，判定与臂内走查同源。

实测（k=11 match）：孪生 fast_ss 0.255→0.041 ms（6.2×，与 L07/L08 同负载
0.047/0.048 同档）、fast_run 0.295→0.083 ms（3.6×）、参考版 0.238→0.198 ms
（1.2×——旧探测只占其编译期小头）。判定与旧探测逐例一致（Bool 缺臂、
GADT `Vec[T] l` 只写 nil/cons 分别报 cons/nil、`Vec[T] (succ L)` 上 nil 与
`Vec[T] zero` 上 cons 均 absurd 不报）；孪生顺带修一例旧漏报（GADT 只写
nil 应报 cons，旧孪生漏报）。

### 2.3 诊断语义：两条收窄保留、嵌套覆盖恢复（`f774703`）

逐臂下钻的初始口径相对决策树有三处诊断收窄（登记于
`docs/l09l13-match-compiler-analysis-2026-09-17.md`）：①覆盖检查只做顶层
（`Unmatched(Con(ctor, [Any; 999], Expl))` 形态不变，嵌套路径的缺失不报）；
②遮蔽检查只认通配臂（通配臂之后的臂报 `Unreachable`；非通配的联合遮蔽如
`zero, succ, x` 里的 `x` 不再报）；③特化方程失败的臂静默跳过（不进
`pats`、不告警——与决策叶子上 `check_pm_final` 失败即 `Ok(false)` 的口径
一致）。

其中**嵌套覆盖缺失**（如 `nil` + `cons(h, nil)` 缺 `cons(h, cons(..))`）
被 2026-09-18 评审定为 P0——修复前静默接受、运行期在尾部为 cons 的值上
卡住——已按 L07 口径恢复（`f774703`，L10 同轮）：

- **两段式记账**：走查只记节点（`PendingNode`：路径 / 头部 Sum / 槽位
  实例化 ret）；臂特化方程成功后先逐节点把槽位方程经 `unify_pm` 解入 σ
  （L11 的臂特化走 raw 侧 meta 间接，走查槽位不在其解里，必须由本方程把
  索引精化落到槽位上），再以**终态 σ** 快照结算嵌套记账——字段 Sum 置于
  σ 之下探测才能看到索引精化；荒谬臂清账不产生覆盖义务。平面模式零成本；
- **判定与文案**：覆盖集 = 已走查臂的 `PatternDetail` 沿路径的结构贡献
  （`PosCover`/`cover_at`/`fmt_path`，mod.rs:142-171，参考版与孪生共用
  同一实现，两版 Debug 逐字节一致）；缺覆盖报
  `match 不完整：模式位置 {path} 缺少构造子 {ctor}`（`Warning::Nested`）；
- **保留的两条收窄**：②遮蔽只认通配臂、③特化失败静默跳过仍是现状。若
  后续要恢复路径感知的遮蔽诊断，需另建 usefulness 分析（决策树本就免费
  提供该分析）。

同轮其余修复：SumCase 合一先比 Sum 头名字（unify 与 unify_pm 双侧，跨
enum 重名构造子直接失败）；构造子良构性检查 `check_ctor_wf`（`ret` 不是
本 enum / 参数位特化在注册期拒绝，重绑定参数惯用法放行）；unreachable
降级（参考 4 处 + 孪生 2 处 + check_universe）；臂序无关性以
`parity_stale_solvable_order_independent` 双臂序钉钉住。

## 3. 性能孪生（`bump_spine_iter.rs`）

L10 冠军配方（bump arena + 打包值 + 迭代内核 + quote 记忆化 + O(1) 名字
解析 + `Tycker` 稳态复用）的移植（孪生模块头注释 1-66 行是权威清单）。
L11 的增量与落地项：

- **decl 表贯穿**：没有 global 表与哨兵；`Decls =
  FxHashMap<SmolStr, DeclEntry>`（bump_spine_iter.rs:635），`Cxt::decls`
  是 `Rc<Decls>` 写时复制——插入经 `Rc::make_mut`（表独占时原地 O(1)，
  bump_spine_iter.rs:4505-4511），与参考版逐 cxt 克隆语义一致；
  `DeclEntry` 只存参考版五元组中的三字段（tm/val/vty，bump_spine_iter.rs:623-631）；
  eval/force/v_app/quote/unify/rename/Compiler 全部带 `decl: &Decls` 参数
  （参考版同款）。**两版都是"整表 Rc 共享 + 写时复制"形态**——L07 那种
  "参考版逐条 Rc vs 快版平铺覆盖"的分层在本层不存在，`53e8adb` 之后两侧
  同构；
- **declb 存根表缓存**：Match 分支体重求值用的 `declb_of`（全表条目换
  `Decl` 存根）按 Rc 分配地址做 TLS 指针键缓存 `DECLB_CACHE`
  （`b1a5eb5`）——每轮首建后 O(1)，清除与 `clear_round`/`bump.reset`
  同界（缓存条目只含当轮 bump 句柄，跨轮即失效）；
- **builtin 的 `PrimId` 枚举**：快版用枚举替代参考版 `Rc<dyn Fn>`
  （bump 内不能携带闭包），5 个 builtin 逐句移植 cxt.rs 实现；卡住 Prim
  的 unify 与携带的 typ 合一（不再是 L10 的 `(LiteralType, Prim) => Ok`
  宽放）；
- **unify 臂序**：U/Pi/Rigid/Decl-Decl 同名/Flex/Flex/Lam/η/Flex 求解/
  LiteralType/Prim 带类型/Sum/SumCase/Match/Obj；SumCase/SumCase **先比
  Sum 头名字**再比 typ+datas（L09 参考版口径，与 L07+ 的 datas-only
  不同）；flex_flex 单方向尝试无快照回滚；Match/Match 分支体在 declb
  存根表下重求值；
- **精化燃料池 PM_FUEL**（`dbe79cf`）：thread_local、4096；三处燃烧
  （frcs 的 lookup 命中 / Match 重选 / spine 链 rigid 头命中）、五处入口
  充值；耗尽按有界降级（lookup 命中返回裸 rigid、Match 不重选）；
  `pm_fuel_exhausted` 供探测侧区分"结构冲突"与"预算耗尽"
  （bump_spine_iter.rs:1020-1049，后者按可达处理）；
- **parser 侧**：宏表 Rc 化（展开快照 clone O(1)）、span_map 线性扫 →
  `partition_point` 二分、declb 缓存（三者均 `b1a5eb5`）；宏直接 token
  拼接（`be8ec25`）；
- **匹配编译器**：§2 全套（逐臂下钻 + 值级探测 + `PendingNode` 两段式
  嵌套覆盖 + `fast_substv_reclaimed_across_rounds` 的 σ 跨轮回收）。

### 双 oracle

`cargo test --test l11_fast_parity`：`#[path]` 独立 crate（只编
list/bimap/parser_lib/L11），参考版 `run` vs 孪生 `run_fast`，判据
**Ok 输出逐字节一致 / Err 判定 + 归一化正文一致**。`norm_err` 除剥
Debug-Span 的 `@ N,M` 与 `start_offset/end_offset/path_id` 数字外，还剥
**meta 编号 `?N`**（双实现的 meta 分配序列不同，文档化偏差；
tests/l11_fast_parity.rs:48-50——L10 无此条）。覆盖面：L10 层语义回归、
宏与可变全局（`parity_macros_and_globals`、自递归宏深度上限
`probe_macro_self_recursion_depth_limit`）、trait 全家与错误文案、深负载
（natadd/strchain/match/struct/macro 生成器，节点数互检）、稳态复用、
评审钉（嵌套覆盖正负例 / 索引精化无假阳性 / 臂序无关 /
`parity_spine_escape_juxtaposed_paren` / σ 跨轮回收）。

### 基准

```text
cargo run --release --bin l11bench -- --workload all --max-k 11
```

**口径先于数字**：L11 参考版 `mod.rs` 无 `bench_check_nf`（bench 口径
缺口，登记于 `docs/review-continuity/a7-r1.md` §4），故 `basic` 行为
**全流程 `run`**（含 preprocess + parse）；`fast_run` = 快版全流程
`run_fast` 与之同轴；`fast`/`fast_ss`/`fast_memo` = 孪生 `Tycker` 的
bench 口径（解析在计时外）。**`fast_run` 才是与 `basic` 可比的全流程
口径**；跨层比较时用 `fast_ss` 会高估孪生优势。

负载族：`natadd`（枚举 Nat 加法链）/ `strchain`（L06）/ `match`（L07）/
`enum`（L07 GADT）† / `struct`（L08）/ `macro`（**L11 特色**：固定声明级
宏段 + 2^(k+1) 层表达式级宏展开 def 链）。无 `church`（L11 参考版即判型
失败，终裁 2026-09-11，非孪生单侧缺陷）与 `gadt`（快版已知缺陷区）。

实测（`docs/bench-matrix-2026-09-18.md`，隔离进程，`--rounds 3`，每格
min，k=11）：

| 负载 | basic (ms) | fast_ss (ms) | fast (ms) | fast_run (ms) | basic/孪生 |
|---|---|---|---|---|---|
| natadd | 1.871 | 0.917 | 0.964 | 0.764 | 2.4× |
| strchain | 992.910 | 3.344 | 2.979 | 7.913 | 125.5× |
| match | 0.230 | 0.175 | 0.179 | 0.226 | 1.0× |
| enum | — † | — | — | — | — |
| struct | 834.577 | 4.225 | 4.248 | 11.072 | 75.4× |
| macro | 897.324 | 3.826 | 3.685 | 10.166 | 88.3× |

相对 09-12 存档的净效果（basic 列）：match 1.098→0.230（0.209×）、
struct 3001.0→834.6（0.278×）、macro 2873.9→897.3（0.312×）、strchain
1762.6→992.9（0.563×）、natadd 2.032→1.871（0.921×）——match/struct/macro
的台阶来自匹配编译器 + decl 表 Rc 化；`macro` 负载另有孪生侧宏拼接与
declb 缓存的份额。

## 4. 已知分歧 / 刻意取舍（跨层连贯性评审登记）

- **SumCase 显示格式分层（comma + 头类型参数族）**：本章（及 L12/L13）的
  构造子值显示为 `{头}[{隐式实参}]::{分支}({显式实参 逗号连接})`，如
  `Point[Nat]::Point.mk(4, 6)`、`Vec[Bool]::cons(1, Bool::false, …)`——
  L09 起的血统格式，被本章内置测试（`mod.rs` test0/test2/test7/test8/
  test_trait、bits_adder）与 L13 `legacy_tests.rs:604/:716` 字面锁定；
  与 L08 的空格 + `[名]` 隐式格式**分层**，不得互贴（a4-r2 曾把 L08 格式
  误移植 L09-L12，终门禁回滚；`sum_head_name` 的非 Sum 头 panic 降级
  保留）。
- **快版孪生 `unify_sp_lockstep` 的实参位相等免比**：tag 7 与 Obj 头链
  不免比（字面量与卡住投影交回完整分派），由 (Obj, Obj) 合同臂接管判定。
- **参考版 `no_metas` 为 quote 版**（已解 meta quote 后续查、无 visited
  set，mod.rs:98-117）：L13 的值图遍历 + 指针去重（`71e11ae`，
  L13 mod.rs:519-565）未下沉；触发类（模块/bundle 链巨型解图）为
  L13-only，本层无已知触发例。
- **无 K 公理层面的安全保护**：精化出现在其它假设里的变量，教学取舍
  （同 L07/L10）。
- **参考版 Def 臂的 `typ_pretty` 固定开销**：见 §1.2 末条（body 侧已置
  空，type 侧每 def 一次 nf+pretty 保留，无消费方；占比未核实）。

### 与参考版的孪生偏差（文档化，parity 闸门覆盖）

- 错误消息 span 全零 + meta 编号序列不同：快版错误里内嵌 Debug-Val/Tm 的
  名字 Span 全零（参考版携带源码偏移），meta 编号 `?N` 序列不同——套件
  比对前按 §3 双 oracle 的 `norm_err` 归一化，不影响 Ok 输出（逐字节）
  与 Err 判定（一致）。

## 5. 已知限制（诚实清单）

- **enum 负载不可测（既有 parity 缺口）**：孪生 check+nf 失败（矩阵 †
  注），与本轮改动无关（改动前二进制同样失败）。
- **参考版无 bench 口径**：`bench_check_nf` 缺失使 basic 只能取全流程
  `run`（§3 基准口径），历史对照需认准 `fast_run` 列。
- **宏深度守卫是解析错误而非循环检测**：256 层上限截断的是"合法深嵌套"
  与"自递归失控"两类（合法宏/块嵌套深度远小于此值，parser/mod.rs:136-139
  注释）；不做宏图灵完备性判定。
- **匹配编译器诊断弱于决策树**（§2.3 保留的两条收窄）。

## 6. 测试

- `cargo test --lib L11_macro`：**29 个**（`mod.rs` 19 +
  `parser/mod.rs` 9 + `parser/lex.rs` 1）。`mod.rs` 内含 L10 血统的
  test 系列（test0/test2/test4-test11、test_trait、test_index、
  bits_adder 全加器）与宏用例（module/Expr 展开）；嵌套覆盖与构造子
  良构性评审钉 7 个（`test_nested_coverage_*` / `test_ctor_wf_*` /
  `test_stale_solvable_order_independent`）。
- `cargo test --test l11_fast_parity`：**48 个** = 套件自有 19 + `#[path]`
  引入 `mod.rs`（含 parser 子模块）带入的 29 个单测。判据见 §3 双 oracle。
- 基准正确性闸门：l11bench 的快版 memo/非 memo 节点数一致 + 两版全流程
  Ok 输出逐字节一致（Err 判定一致即通过）。

（历史注：`6ae12a6` 落地时的验收口径是 l11_fast_parity 37 / lib 22；
`f774703` 评审修复轮加钉后为 48/29，即当前数。）

## 7. 参考资料

- [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) 07
  （unification 骨架，inherit 自 L09/L10 重写）
- [KonjacSource/dpm-nbe](https://github.com/KonjacSource/dpm-nbe)
  （explicit substitutions + forcing：精化载体机制蓝本）
- 本仓库 `src/L07_sum_type/README.md`（逐臂下钻与显式替换的原始设计）、
  `src/L10_typeclass/README.md`（trait 面、值级探测与两段式嵌套覆盖的
  同款机制）、`docs/l09l13-match-compiler-analysis-2026-09-17.md`
  （决策树诊断与收窄登记）、`docs/bench-matrix-2026-09-18.md`（基准口径
  与全表）、`docs/review-continuity/a4-r1.md`/`a5-r1.md`/`a7-r1.md`
  （跨章连贯性登记）
