# LSP × 性能孪生接线：架构决策（2026-09-09）

> 前提结论（bench 已证）：孪生在真实 HDL prelude 上一次性 1.83s vs 参考版 3.29s
> （1.8×）。接线的目标就是让交互路径也吃到这个倍数。

## 0. 一页纸结论

**观察面与跨请求数据面不是两个独立任务，而是一个契约问题**：参考版三张观察表
存"live `Val` 句柄 + 查询期 quote"，这要求快照可持久——正是 bump arena 给不了的。
破法是**把观察表的存储形态从 `Val` 换成 push 期 quote 出的 owned `Rc<CTm>`
（+ binder names + spans）**：

- 孪生侧：push 时 `quote(V → ref Tm)` 即逃逸 bump，类型通常很小、成本可控
  （参考版生产路径本就在每个 def 处 eager 算 `vtyp_pretty`，是同类先例）；
- 消费侧：`hover_at`/`completion_at` 不再对 live Val quote，改对存的 `CTm`
  直接 `pretty_tm`——quote 从"每查询一次"变"每 push 一次"，需要在阶段 0 实测
  HDL 负载的 push 密度/类型规模，若个别大类型拖垮，再上"按 decl 惰性补表"
  或"查询触发孪生重放"兜底（孪生快，这是接线后才存在的免费选项）；
- 跨请求数据面随之降维：LSP 持久层只需持有 **owned 快照**（strings/CTm/spans）
  + 参考域全局 decl 表；"跨代 bump 快照"从必答题变成优化题。

## 1. 两侧现状（代码坐标）

### 参考版（LSP 生产路径）
- 消费主循环 `src/lib.rs`：`hover_table: DashMap<String, Infer>`（URI→整份
  Infer 快照，:221）；didChange = `local_cxt = cxt.clone()` 剔旧符号（:1604）
  → `local_infer = infer.clone()`（:1630）→ 逐 decl `infer()` → 无错则
  `cxt.decl = local_cxt.decl.clone()` Arc 写回（:1680）。
- 观察面 `elaboration.rs`：hover/completion/inlay 共 **27 push 点**
  （:188/:742/:905/:1153/:1467/:2126-2455/:2577/:2627/:2839/:2982/:3001/:3035
  等）；`accumulated_errors`（:775-778，match 分支诊断）；
  `defer_println + println_jobs` 两阶段（:1195-1196，消费于 lib.rs:1811）。
- `Cxt::decl` 条目 = **7 元组** `(span, t, vt, a, va, prim, typ_pretty)`
  （cxt.rs:955-969）。
- hover 消费两路径（lib.rs:346-367）：Path1 def 直接读 `DeclTm::typ_pretty`
  （owned String）；Path2 表达式 `hover_entry_at` 返回 `(span, def_span,
  HoverCxt, &Val)`，**查询期** `x.quote(&hcxt.decl, hcxt.lvl, val)`。

### 孪生（bump_spine_iter.rs）
- `Tycker { bump, machine }`（:11384）；入口 `run_decls_bounded` 第一件事
  `bump.reset()`（:11413）——一次性口径，跨请求复用值 = 悬垂。
- `DeclEntry<'a>` = Copy 四字段 `tm/val/vty/prim`（:558），刻意丢
  Span/typ_pretty。
- 观察面：0 处。`defer_println` 不移植（:8029 注释：立即 nf+pretty，
  run() 口径本就等价）；`accumulated_errors` 需核实是否有等价排水。
- 已有桥：`v_to_ref_val(spine, defs, v) -> Rc<CVal>`（:9339）——但只覆盖
  trait 求解的固定形态（闭包/Pi 等 unreachable），**不能**当观察面通用解码器；
  通用逃逸口是孪生自己的 `quote`（bench nf 已用）。

## 2. 分阶段计划

### 阶段 0：消费侧契约改造（先只动参考版，行为不变）
把三张表的元素类型从 `(Span, Span, HoverCxt, Rc<Val>)` 改为
`(t_span, def_span, names: Vec<SmolStr>, ty: Rc<CTm>)`——push 期
quote+存 owned；`hover_at` Path2 改 `pretty_tm(0, &names, &ty)`。
**验收**：`tests/` 下 LSP 8 件套（hover/completion/namespace/impl_goto/
macro_goto/hdl_check_locations/println_two_phase/large_did_open）全绿；
HDL 负载 didChange 计时对比改造前（盯 eager-quote 回归）。
产出：owned 化契约 + push 密度/类型规模实测数——决定要不要兜底。

### 阶段 1：孪生观察面 + 登记面（本文档主体动机）
- `DeclEntry` 补 `span: Span<SmolStr>` + `typ_pretty: String`（owned，
  与 bump 无关，不破坏 Copy？——会，二字段进 `Decls` 的另一张并表或
  DeclEntry 弃 Copy 改 `Clone`；性能影响在 bench 上量）。
- `Tycker` 挂三张 owned 表（阶段 0 同契约），逐 push 点移植 27 处，
  错误消息形态与参考版逐字节对齐（parity 口径）。
- 两阶段 println：孪生维持立即口径，`println_jobs` 仅参考版；LSP 接线时
  按引擎分派（或孪生提供 jobs 兼容层——阶段 3 再定）。
- 验收：`l13_fast_parity` 绿 + 新孪生观察面对同一源 dump 与参考版逐条一致。

### 阶段 2：prelude 加载
`prime_round` 扩展为可装载 24 文件 prelude（bench 已有手工拼装先例
l13bench::parse_prelude，抽成复用 API）；宏表/PreludePool 口径对齐。

### 阶段 3：跨请求数据面（降维后的选择题，实测定夺）
- 3a **全量重推**：didChange 只重推该文件（全局 decl 表参考域常驻，
  孪生每轮读它进 bump；新 decl 结果 quote 回参考域合并）。击键成本 =
  单文件推 + 全局 seed，需要测 seed 开销。
- 3b 逐 decl 克隆模型移植：孪生支持"上下文快照→推一个 decl→合并"——
  要求 bump 跨代，最后手段。
- 默认先 3a：简单、无悬垂风险，且孪生本身 1.8×。

### 阶段 4：双引擎并行与灰度
LSP 加引擎开关（先 env/config），孪生模式与参考版模式跑同一测试套件 +
真实 HDL 工程对比（击键延迟 P50/P99、内存）；达标后默认切孪生。

## 3. 已知风险
1. eager-quote 成本：943-decl HDL 全量重推时 27×N 处 push 的 quote 开销
   → 阶段 0 实测；兜底见 §0。
2. `DeclEntry` 弃 Copy 的热路径回归 → 并表方案对照 bench 定量后再选。
3. 观察面消息若含 `?N` meta 编号，跨引擎不逐字节一致（已知偏差 3），
   parity 比对需归一化——消费侧契约里存的是 quote 后 Tm，渲染归 pretty，
   不受影响。
4. LSP 8 测试驱动参考版：阶段 0 每步都以它们为回归闸，改契约不分叉。


---

## 4. 进展日志

### 2026-09-09（阶段 0 完成 + 阶段 1 大部）

**提交链**：`fba6638`（阶段0 hover owned 化）→ `f9070e6`（契约收敛
`(t_span, def_span, String)`）→ `c63c6be`（孪生三表+push_hover 骨架）→
`dc49f52`+`bbefc1b`（DeclEntry 回填 span/typ_pretty + Var→global 首站点）→
`e2564c1`（binder span 16 点穿线 + local/def-site/let/qualified/field 五组）→
`128d552`（completion 4 站点）。

**孪生观察面站点状态（对参考版 21 站点，2026-09-09 晚更新）**：
| 组 | 状态 |
|---|---|
| Var 解析五支（global/import/prefix/local/suffix-fallback） | ✅ 五支全（suffix-fallback 带 decl span + cached 串） |
| check-Lam binder（742）/ let（2627）/ def 名（1153） | ✅ 三点 |
| Obj qualified 三连（2317/2330/2339） | ✅（cached push，键=整 Raw span 对齐参考版 t_span） |
| 字段投影 struct/SumCase（2422/2455） | ✅ 但 **def_span 降级为字段 token**——孪生 Sum/SumCase 值不持字段 binder span，待评估补 |
| qualified 中间段 push_qualified_hover（2126） | ✅（逐段 cached push） |
| tuple-mk 元素（2577） | ✅（is_tuple_mk_head/tuple_n_arity 移植，`af8bdd9`；**实测互检待阶段 2**——TupleN.mk 来自 prelude） |
| ns-method/trait 方法（2817/2955） | ✅ 两点（`fc297f8`：trait 定义解析成功 push(方法 token→trait 声明名 span, 实例化调用类型)；ns 命中 push(Type.method 登记 span)） |
| PM 构造子 pattern token（pattern_match 907） | ✅（Con==Con arm 构造路径；无参→Tree::leaf、参数化→Pi；`9a6faff`） |
| enum 构造子定义处（use==def==声明 token） | ✅（constrs 从 decl 表回填声明 span；prime 渲染差属偏差 4） |
| impl header（1462/1482） | ✅（trait 名 token→声明、实现方法名→trait 方法声明名；`32a5635`） |
| completion（2431/2446/2466/3001/3035） | struct/SumCase 4 点 ✅；trait 未命中方法名收集 ✅（`fc297f8`；ns 失败传播支同参考版不收） |
| inlay（def 1157 / let 2601） | ✅ 两点（def peel_pi_collect 收 telescope names；偏移-标签集互检过） |

**性能事实（prelude-hdl 943 decls，release）**：
- 观察面接线前：fast 2204ms / fast_ss 1865ms。
- 阶段 1 全接通后：fast ~2644ms / fast_ss ~2222ms（**+20%**）。
- 归因：与参考版 eager 化同比例（参考版 prelude-core 亦 +11%，且其 push 期
  同样只渲染不 lazy）——是 **push 期渲染契约的对称成本**，非孪生退化；对
  参考版（~3.2s）领先维持 ~1.2-1.3×。
- 微优化候选（统一做，不分引擎）：local 使用处渲染 memo by (lvl,V)；
  trait 方法调用渲染 memo by (method, 类型头)；PM 探针内 constr_pi 复用
  （参考版已部分做）；qualified 三连可 spread cached。

**回归闸（每提交必绿）**：`l13_fast_parity` 382、`observation_tests` 9 例
（global/local/field/completion/inlay/impl-header/trait-dispatch/PM/全表
双引擎互检）、`debug_test` 15、LSP 守卫 12 套、bench 各 workload nf 一致。

### 下一步（阶段 1 已 wire-complete，转入收尾与接线主体）
1. **阶段 2：prelude 加载**——孪生 `prime_round` 扩为装载 24 prelude 文件
   （PreludePool/宏表口径），这是 tuple-mk/真实 HDL 观察面实测互检的前提。
2. **阶段 3a：全量重推数据面**——LSP didChange 走孪生全量推该文件（全局
   decl 参考域常驻 + 每轮 seed 进 bump），实测 seed 开销；owned 快照下
   跨代 bump 快照已非必需。
3. **值层增强**：XCell::Sum params/SumCase datas 带上字段 binder 源码 Span
   （解字段投影 def_span 降级）——独立子工程，评估后做。
4. tuple-mk 实测互检：随阶段 2 一并补（当前以参考版 debug_test 两枚 tuple
   用例 + parity 背书）。
5. 双引擎 LSP 灰度（阶段 4）：lib.rs 加引擎开关，8 测试套件跑孪生模式。


### 2026-09-09 续（三路评审 + 修复轮）

阶段 2 提交后按性能 / 正确性 / 代码风格三个维度并行评审，修复全部落地
（提交 `7c69eff` + 本轮）：

**正确性（3 修 + 1 对齐）**：
1. **VconnT `field`/`ctor_name` 补 tag 守卫（P1）**：`v_xcell_of` 是裸
   打包字解引用，tag 检查是前置守卫（`lit_of`/`project` 同款惯例）——
   参考版的 `match Val::SumCase` 是天然安全匹配，移植时漏了。恶意/畸形
   实参下是野指针读；好输入不触发（09-hierarchy 过了）。
2. **check 路径 Let binder hover 补 push（P1）**：参考版 742 在 **check
   的 Let 臂**（推断路径孪生已有 8223 同款）——检查路径的 let（HDL 模块
   体常见）此前丢条目。全表 fixture 加 `let m = succ(n)` 锁住。
3. **后缀回退臂仍读登记期缓存串（P2）**：与本轮主修同缺陷类的漏网点。
   改实时渲染（ref 2220）。
4. **参考版加载器补清 inlay 表（P2）**：参考侧只清 hover/completion，
   prelude 一旦未来产出 inlay 会按裸 offset 键泄漏进每个 backend clone；
   孪生三表全清。取参考侧对齐（行为今日等价——prelude 无 inlay）。
5. `run_decls_with_prelude` 签名收敛为 `&PreludeParse`，`failed` 非 None
   快速失败（parse 截断静默重放会以难诊断的 infer Err 爆在下游）。

**性能（1 主修 + 实测）**：
- **prelude 装载段关观察面 push（`Machine.observe` 总闸）**：装载段全部
  hover/inlay/completion push 与 decl_reg 的 typ_pretty 渲染在本轮末
  `clear_observation_tables` 里丢弃——参考版 LSP 只在进程启动装一次
  prelude，孪生每 kick 重放不应为被删的表条目付费。实测（release，
  observation 套件 4 次 prelude 重放）：**9.75s → 9.23s**，HDL 级重放
  省约 440ms/kick（≈ 阶段 1 接线的 +20% 渲染税全额回收）。gate 默认
  `true`——bench/run 口径维持与参考版的对称渲染成本，bench 数字可比。
- 未采纳（登记备查）：`types_names_list` O(lvl)→O(1)（bind 期缓存，
  留作"渲染 memo by (lvl,V)"候选的先导）；prelude 段 per-file force
  memo clear 去留（孪生 memo 不持 Rc，纯速度实验，语义中性）。

**代码风格（文档同步）**：
- 模块头"不移植"清单拆分为**已移植（阶段 1-2）**与仍不移植两部分；
  PrimId 文档"故不在枚举内"陈旧句删除；**偏差 4 标记已修复**（历史描述
  与现行为相反会误导下一棒），新增偏差 5 扩展（PM 重复）与偏差 6
  （零 span 条目）。
- `parse_prelude_files` 注释如实标注与加载器的差异（失败即止 vs 跳过
  继续）；测试 `run_prelude_both` 加 files/include_hdl 一致性守卫；
  mod.rs 测试本地 PRELUDE_FILES 标注"故意子集"防误"修复"。
- `tests/l13_into_probe.rs`（前会话临时探针）按仓库惯例收编入库。

**回归（评审修复后复测）**：lib 659、`l13_fast_parity` 385、observation
12、LSP 守卫 12 套全绿。注意：lib 全量与 release bench **并行**跑出现过
一次偶发异常退出（资源竞争），串行复跑均绿——回归闸请串行执行。

**bench 基线（本轮，release，prelude-hdl 943 decls，nf=219 两版一致）**：
basic 3946ms / fast 2746ms（min）。fast 较阶段 1 的 ~2644ms +4%：
使用处实时渲染的对称成本（参考版同款语义），observe 门控只作用于
`run_decls_with_prelude` 的 prelude 段（LSP 路径），不影响 bench 口径。

### 2026-09-09 续（阶段 2 完成：prelude 装载 + 真实互检）

**提交链**：`0b466a4`（prelude 表库化：`PRELUDE_CORE`/`PRELUDE_HDL`/
`PRELUDE_SHOW` + `parse_prelude_files`，参考加载器/l13bench/孪生三方同源）
→ 孪生侧（VconnT prim 移植 + `run_decls_with_prelude` 整轮入口）→
`0eb625b`（阶段 2 验收测试 + 三处引擎修复）。

**孪生新增**：
- `PrimId::VconnT`：参考版 `vconn_builtin` 逐句移植（subSignal 端口方向
  判定 + `vconnEmit` 发射），`register_vconn_builtin` 在 prelude 末尾注册
  （签名引用 prelude 的 ModuleTree/Expr，时机镜像参考版）。
- `Tycker::run_decls_with_prelude(prelude_decls, file_ends, nat_after,
  user_ast)`：本轮 = prime_round → 逐 decl 重放 prelude（nat 边界 + 每文件
  边界清 force memo）→ vconnT 注册 → **短名别名 or_insert**（参考版尾部
  逐句：ns 方法键排除、全键排序 first-wins）→ HdlLoopIdx 复位 → 清观察表
  → 用户 decls（与 `run_decls_bounded` 共用 `step_round_decl`）。每 kick
  重放整个 prelude，是阶段 3a seed 开销的基线。
- `insert_prelude_aliases` / `clear_observation_tables`。

**真实互检结果（12 例 observation_tests，全部逐字节/按已登记工件口径过）**：
- `prelude_tuple_mk_element_hover_matches_reference`：阶段 1 遗留的
  tuple-mk 实测互检完成——元素 token（`true`→Boolean、`zero`→Nat）双版
  一致，顺带验证别名解析。
- `prelude_full_observation_tables_match_reference`：Option/match/PM/
  字段投影/tuple 字面全表互检（三类已登记工件放行：参考 start=0 畸变、
  孪生零 span 条目、投影 def_span 降级）。
- `hdl_example_parity_with_full_prelude`：全量 prelude +
  examples/hdl/09-hierarchy **端到端**输出逐字节一致——vconnT 路径由
  `sum := u.sum` 展开实测，println 走 moduleTreeVL 全模块渲染。

**互检揪出的三个真分叉（已修）**：
1. **全局名使用处 hover 用登记期缓存串**：泛型 struct 参数的宇宙 meta
   在登记后才被构造子 check 解出，缓存串把 `?N` 带进使用处悬浮
   （`Tuple2` 使用处 `[A: ?264]` vs 参考 `[A: Type 0]`）。修复：
   `push_hover_cached` 改实时渲染（同参考版）；`typ_pretty` 保留给 LSP
   def-site 悬浮（参考版 Path1 直读）。
2. **no_metas 已解 meta 按 cxt.lvl quote 下溢**（debug panic，
   09-hierarchy 实测）：解出时上下文可比当前深。修复：`NM_QUOTE_LVL =
   u32::MAX/2`（参考版 `val_no_metas` 的 NM_QUOTE_LVL 同款，结果只扫
   Meta 节点、下标无所谓）。
3. **check 的 Lam 臂多余的 binder 定义处 push**：接线旧文档把参考版
   742 归因为 Lam 臂（实为 **let** 臂），def 参数折叠成 λ 会经过，推出
   参考版没有的条目。修复：删该 push，局部变量 hover 仍由使用处 Var 臂
   推（binder span 经 Names.by_lvl 携带，不回退）。

另：`unify_iter` 入口的 `debug_assert!(stack.is_empty())` 与 Call/Call
spine 快路径的嵌套调用（"首个对作入口、其余预载子栈"）矛盾，HDL 负载
实测踩中，已移除断言并注明合法形态。

**新偏差（已登记，不修）**：
- 偏差 5 扩展：PM 构造子 pattern token 处孪生可能推**同串重复**条目
  （PM 臂 + Var 臂各一），set 级互检不可见、对 LSP 取值无影响。
- 孪生零 span 条目：tuple 字段访问 `p._2` 反糖出的合成构造子 Var 无源码
  span，`.name` 后缀回退 push 的 t_span=0（参考版同场景推声明 span）。

**回归闸（本轮实测）**：lib 659、`l13_fast_parity` 385、observation 12、
LSP 守卫 12 套全绿；bench prelude-hdl parity 待本轮 bench 复跑确认。

### 2026-09-09 续（阶段 1 剩余站点的真实探查）

用一个临时对照 probe（同 fixture 跑孪生+参考版、打印两张 hover 全表）
拿到**实测**差异，确认阶段 1 未接站点的具体形态（fixture 含
`match t { case leaf => ..; case node(x) => x }`）：

- **PM 构造子 pattern token（ref pattern_match 907）——孪生未接**：
  参考版对 `case leaf` 的 leaf token 渲染 `Tree::leaf`（构造子标识），
  孪生这一带只有**退化 `@0..0` 零 span 条目**、值错渲染成类型 `Tree`。
  → 需在孪生 check_pm 决策树构造处补 `push_hover(整 case token span →
  构造子 decl span, constr_pi/SumCase 值)`，Lam 型构造子要取 Pi 签名而非
  quote 值（否则渲染成不可读 lambda，参考版同此处理）。
- **enum 构造子定义处（ref 1496/1280 族）**：参考版对 `node(x: Tree)` 定义
  token 渲染 `(x': Tree) → Tree`（binder 带 fresh 后缀 `x'`，即偏差 4 一族
  的显示差），孪生缺对应 def-site 条目。
- `x @30..31` 孪生出现**两条重复**（偏差 5：构造子体 datas 复用 infer 路径）。

结论：阶段 1 剩余四组（PM 构造子 / enum 构造子定义处 / impl header /
trait 方法与 trait completion）+ tuple-mk，均已定位到**具体点位与值形态**，
非泛泛"待接"。其中 PM 那组价值最高（HDL match 密集）且要先解构造子
pattern 在孪生决策树里的 span 来源（`constr_name`/`constr_` 目前是
`SmolStr` 非 `Span`）。

> 更正：本轮此前一段"孪生 10 条 / 参考版 14 条"的差异描述是在未拿到工具
> 输出时的臆测，已作废；以上为 `--nocapture` 实测两表 diff 的重述。

### 2026-09-10（阶段 3a 接线落地 + seed 成本实测）

**提交链**：`0259015`（Engine 开关 + ObserveSnapshot 契约）→ `c987621`
（阶段 3a 孪生观察面接线）。**阶段 3a 已接线，但实测不是净收益——需要
池化/常驻 prelude 才能兑现速度。**

**接线内容**：
- `Backend` 增 `Engine { Reference, Twin }`（`TYPORT_LSP_ENGINE=twin`
  切换，默认 `Reference`；`Backend::new_with_engine` 供测试显式选）。
- Twin 模式下 `load_prelude_impl` 顺带 parse 一次 24 文件 prelude
  （`PRELUDE_CORE`+`PRELUDE_HDL`+`PRELUDE_SHOW`，与参考加载器同序）。
- `elaborate`（LSP 的 `process_file` 路径）在参考版分析之外，把 prelude +
  该文件经 `Tycker::run_decls_with_prelude` 重放，把三张 owned 表存
  `twin_tables[uri]`（阶段 0 契约：`ObserveSnapshot`）。
- 消费端按引擎分派：`hover_at` / `goto_definition_at` / `cross_file_references`
  / `completion_at` / `inlay_hint_at` 命中孪生快照即用，未命中或该轮孪生
  报错则回落参考版 `Infer` 表。**孪生是加速器，出错降级而非替换**——诊断、
  全局 decl 表、跨文件符号合并、两阶段 println 仍在参考版。
- `inlay_hint` 主体提到泛型 `inlay_hint_at`（与 hover/completion 同款可测）。

**观测（`tests/twin_engine_tests.rs`，4 例全绿）**：tuple 元素 hover /
局部变量 hover / 成员补全 / inlay，双引擎逐字节一致。参考版 LSP 守卫
7 套默认引擎全绿；`TYPORT_LSP_ENGINE=twin` 下同样 7 套全绿（降级路径
保证行为等价）。

**seed 成本实测（release，09-hierarchy，`tests/twin_engine_bench.rs`，
`--ignored`）**：
| 引擎 | ms/kick（5 次取最小） |
|---|---|
| Reference（缓存 prelude） | **328.5** |
| Twin（每 kick 重放 prelude） | **3285.5** |

即**当前 3a 每次击键慢约 10×**：孪生把 943-decl prelude 整轮重放
（`run_decls_with_prelude` 体内 `bump.reset()` + `prime_round`）的
~2.9s 全额计入每次 kick，而参考版的 prelude 是进程级缓存、kick 只
重新 elaborate 改动文件。这与 bench 的 1.8× 优势不矛盾——bench 比的是
**一次性全量**，交互路径扣掉这个一次性成本才能兑现。

**结论 / 下一步（关键）**：3a 的"全量重推"口径在交互路径上被 seed 成本
压垮，必须让 prelude 常驻（`PreludePool` 池化移植 = 文档阶段 3b 的
"bump 跨代"），或退一步只在 3a 里 seed 参考域全局 decl 表（把参考版
`cxt.decl` 的条目一次性解码进孪生 bump，避免逐 decl 重推 prelude）。
在 seed 成本降下来之前，**默认引擎保持 `Reference`，不要切默认**。
`Backend` 为 `Send + Sync`（LSP 多线程握手需要），而 `Bump`/`Tycker`
是 `!Sync`，常驻孪生态只能挂线程局部（主循环单线程）——这既是 3b 的
约束也是其不进入 `Backend` 字段的原因。

**价值前提修正（本轮实测后必须澄清）**：bench 的 1.8× 是**一次性全量**
（prelude+user 一起 elaborate）的口径，而 LSP 交互路径里参考版的 prelude
已经是**进程级缓存**（`clone_prelude_state`），kick 只重新 elaborate 改动
文件。也就是说：**孪生省下的 prelude 装载时间，恰好是参考版缓存已经省掉的
那部分**——3a 若不池化，不但吃不到 1.8×，还要每 kick 倒贴一次 prelude。

**seed vs 用户段拆分（release，`split_seed_vs_user_cost` 手动测量）**：
- 孪生 prelude-only 重放：**2780.7 ms**
- 孪生 prelude + 09-hierarchy：**2839.5 ms** ⇒ **用户文件仅 ~58.8 ms**

对照参考版整 kick 328.5ms（其 prelude 已缓存，328ms 基本就是"单文件
elaborate + Infer/Cxt 深克隆"）。**孪生的单文件 elaborate 工作 ~59ms，
比参考版整 kick 快 ~5.5×**——这印证了 3b 的兑现路径：把 prelude 常驻后，
kick 只需 59ms 级即可完成观察面刷新，远优于参考版 328ms。

因此下一步（阶段 3b）优先级很高：**常驻/池化孪生 prelude**（`PreludePool`
池化移植；`Bump` `!Sync` → 线程局部挂主循环），随后实测"常驻态下 09
及更大 HDL 的双引擎 kick 对照"再谈默认切换。单看 bench 的 1.8× 不足以
推断 LSP 收益——真正的杠杆是这 5.5× 的单文件差值。
