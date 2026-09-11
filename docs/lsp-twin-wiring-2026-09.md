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

### 2026-09-10 续（阶段 3b 落地：常驻 prelude + 剩余阻塞点定位）

**提交链**：`cb0a3b4`（孪生侧 `prime_resident`/`observe_user` 检查点 + 跨
kick 等价性测试）→ `5000d31`（LSP 侧线程局部常驻接入）。

**孪生侧**：`Tycker` 增 `resident` 检查点——`prime_resident` 一次装载
prelude 并固化稳态（cxt + defs 长度 + metas/tstate/mutable/symbol_table/
import_map/trait_method_cache/指针导入表），`observe_user` 多次复用，每
kick 只付用户段。正确性：快照句柄钉在常驻 bump 上（检查点存活期间 bump
绝不 reset，所有 reset 路径清 resident）；每 kick 从检查点恢复 per-run
状态。bump 用户段增长超 512MB 时下个 kick 重新 prime（bump 不支持截断，
用周期性重放换内存上界）。验收
`resident_checkpoint_matches_fresh_replay_across_kicks`：prime 一次跑
三个不同源（全局使用/tuple/真实 HDL 09-hierarchy），hover 全表（含重复）
与每源全新 `run_decls_with_prelude` 逐字节一致。

**LSP 侧**：`twin_observe` 走线程局部 `TWIN_RESIDENT`（`Bump` `!Sync` 且
分析主循环单线程；按 `include_hdl` 分池），首 kick prime、后续 kick 复用。
新增 LSP 级测试 `twin_resident_reuse_across_kicks_is_consistent`（顺序
两 kick 与各自全新 Backend 一致）。`twin_engine_tests` 6 例、孪生模式
hover/completion/cross_file 守卫全绿。

**实测（09-hierarchy，release，min/5）**：

| 阶段 | 参考版 | 孪生 | 说明 |
|---|---|---|---|
| 3a（每 kick 重放 prelude） | 328ms | **3285ms** | seed 税压垮 |
| 3b（常驻检查点） | 325ms | **399ms** | seed 税清零，但孪生仍**加性** |

拆解参考版 kick（临时打点）：`cxt.clone` ~0.2µs、`infer.clone` ~0.7ms、
**`infer_loop` ~280ms**（单文件 elaboration 就是全部成本）。孪生用户段
~60-80ms。**即孪生单文件 elaboration 比参考版快 ~4×**，但当前 twin 模式
为诊断/跨文件状态跑完整参考版流水线，再叠加孪生观察段，故 399 ≈ 325 + 74。

**剩余阻塞点（下一步的唯一问题）**：要让孪生成为净收益，必须让孪生在
twin 模式下**接管诊断 + 跨文件数据面**，从而省掉参考版那 280ms 的单文件
elaboration（kick 可望落到 ~80ms 级）。这需要：
1. 孪生产诊断：当前 `run_decls_with_prelude` 遇错即 `?` 早退（不累积），
   且错误 span 全零（已知偏差 3）——要补**错误累积**与**源码 span 保真**，
   否则诊断定位错乱、UX 退化。
2. 跨文件符号合并 / namespace 登记 / goto 跨文件：孪生需给出等价的数据面
   （参考版 `file_symbols`/`file_namespace_regs` 那套）。
这是独立子工程。在完成前，**twin 模式保持 opt-in、默认 `Reference`**：
3b 已把孪生从"慢 10×"降到"慢 ~23%"，且观察面正确性已验证，但还不能默认。
单看 bench 的 1.8× 与 3b 的 5.5× 都不足以推断 LSP 收益——**收益取决于
孪生接管诊断**这一尚未完成的前提。

### 2026-09-10 续（阶段 4 落地：孪生接管单文件诊断——**净收益 3.4×**）

**提交链**：`cfcb503`（错误 span 保真 + 逐 decl 累积）→ `0a2cb3d`（用户声明
导出为参考域 Decl 行）→ `f4d5da8`（孪生接管单文件诊断+观察）→ `2ce437c`
（多文件放开 + 未解析名安全阀）。

**诊断面（孪生自产，`cfcb503`）**：
- `unify_catch` 补 span 形参，从 check/infer_expr/unify_pm 各调用点传入源码
  span（此前 `empty_span`，"can't unify"系列定位全零）。
- `observe_user` 逐 decl 累积错误不早退（参考版 `elaborate` 的 `err_collect`
  同口径：失败 decl 保留旧 cxt 继续）。
- println 记 span（`DeclOut::Println` 补 Span）；HDL 自检行记 (decl 下标, 行)。
- 验收 `twin_user_errors_match_reference_diagnostics`：7 例错误语料
  (span, msg) 多重集与参考版一致。
- `fake_bind` 的 redefine 错误补 span（实测 `def ok` 撞 prelude 名时暴露
  与参考版 4..6 vs 0..0 的分叉）。

**数据面（`0a2cb3d`）**：孪生 `DeclEntry` 补 `ty`（类型**项**，参考版行 .3）
——此前"无读取点省略"，导出层一来成必需（`pretty_sum_definition` 靠它渲染
构造子签名并判定尾随 `→ ret` 省略）。`observe_user` 末尾把本轮新增的用户
声明（对 prelude 基线 diff）导出成 `ExportedDecl` 七元组。验收
`twin_exported_decls_render_sum_members_like_reference`：enum/struct 成员
列表经导出表与参考版逐字节一致。

**接管（`f4d5da8`）**：`twin_elaborate` 在 `elaborate` 入口——孪生可拥有时
（Twin 引擎 + 无 import + 无 package）自产诊断、存观察快照、把导出声明并回
参考域 `cxt.decl`（Defs 另建 `DeclTm::Def` 供 Path1），**跳过参考版逐 decl
infer 循环**（那 ~280ms/kick 的成本主体）。有 ERROR 时保留旧符号（同参考版）。

**多文件放开（`2ce437c`）**：gate 去掉"仅一个用户文件"限制；安全阀——孪生
报 `error name not in scope: X` 且全局表确实定义 X 时判定视图不足，回落
参考版，不误报。

**实测（09-hierarchy，release；同 Backend 先 warm-up 再测稳态）**：

| 阶段 | 参考版 | 孪生 | 相对 |
|---|---|---|---|
| 3a 每 kick 重放 prelude | 328ms | 3285ms | 慢 10× |
| 3b 常驻检查点（仍加性） | 325ms | 399ms | 慢 23% |
| **4 接管诊断（稳态）** | **359ms** | **102ms** | **快 3.5×** |

启动成本单列：孪生首个 kick 需 prime（~3.3s）——已提前到 `load_prelude`
（启动期），故首 kick 也降到 121ms；参考版启动亦要装载 prelude（~1-3s）。
注：早期"min of 5 fresh Backend"口径被**线程局部常驻复用**掩盖了 prime
成本（首次 prime 后 5 次都命中常驻），故 `bench_kick_cost_by_engine` 改为
单 Backend + 显式 warm-up 分解，prime 成本不再被 min 吃掉。

**验收**：`twin_engine_tests` 10 例（错误诊断逐条互检含 println、跨文件回落、
未导入跨文件符号回落、同文件多 kick 常驻复用、多文件独立拥有、真实 HDL）；
参考版与孪生两模式 11 套 LSP 守卫全绿；`l13_fast_parity` 388、observation 15、
debug_test 15 全绿。

**剩余边界（不阻塞 HDL 目标）**：有 import 的文件（`import mylib._`）与
声明 package 的文件仍走参考版——它们的跨文件符号需要把别的文件喂进孪生的
bump，属另一子工程。HDL 工作负载不用 import（全靠 prelude 短名别名），故
目标已达成。

### 2026-09-10 续（全 HDL 语料验收：修挂死 + 诊断正确性闸）

全语料互检（`examples/hdl/` 23 例，双双装载完整 HDL prelude）暴露两个孪生
核心问题，均已处理：

**1. 挂死：`no_metas` 的 quote 版在模块链上死循环（已修）**
症状 `01-basics.typort` 的 `module { let x = a + b; y := x }` 永久挂起
（Phase B 的 `create` 体在 `no_metas` 处）。定位：内核调用计数器
（force/eval/quote/unify 均不增）+ 原子步骤标记，锁定 `no_metas`。根因：
孪生 `no_metas` 是**未修版**——对已解 meta 的解做 quote 再查，而
module/bundle 链上的解**自引用**（解里又嵌同一个 meta），quote 展开即无限。
参考版 mod.rs 早已改为**值图遍历 + 访问集**（注释记录该 quote 版曾占某
HDL 例 65% 采样）。已按参考版移植 `tm_no_metas`/`val_no_metas`/
`env_no_metas`：值身份去重破环；`Tm` 指针与值打包字用两套访问集（不同
地址空间，混用会误判同号）。回归 `expr_let_in_module_body_terminates`。

**2. 伪错误：可达性记录顺序错了（已修）**
`13-adder-tree.typort`：孪生把参考版接受的分支判成 unreachable → 该 decl
失败 → 递归 def 未登记 → 连锁 "not in scope" 伪错误，而参考版干净通过。
根因：孪生 `compile_aux` 在 `check_pm_final` **成功之后**才 `reachable.insert`，
而参考版（pattern_match.rs:361）是**到达叶即先记可达**——决策树按构造子
分支走查时，本分支不适用的臂 check_pm_final 会失败，孪生便漏记可达，遍历
结束即误报 unreachable。已按参考版改序；`checked_ret` 同步由"体 Raw"改为
"臂下标"（参考版 `entry.idx` 同款，避免两个同体臂互相顶替）。修后全语料
23 例中 **22 例由孪生拥有**（此前更少）。

**3. 漏报：模块 close-check 未跑全（已加闸）**
同语料暴露：`13-adder-tree` 孪生 **checks=0** 而参考版报 8 条
HDL001/HDL002 警告——该文件的模块树在孪生侧构建不全，close-check 走不到
报告点。`18-utils` 另有 trait 求解分叉（孪生报错，被错误闸挡下）。
**2026-09-11 精确化**（临时插桩 `TDBG_UNIFY`/`TDBG_FLEX`/`TDBG_SOLVE`，已全部
移除）：旧的"flex-flex 带 spine 合一"定位不够准——实际失败链是

```
unify_catch(LetNamed[?m₁[r],?m₁[r]] vs LetNamed[?m₂[r],?m₂[r]])
→ Sum/Sum 臂逐参数 → 参数对 Flex(?m[r]) vs …
→ solve_flex_side_bump(m=33949, args=[Rigid(Lvl(0))], rhs=TimeoutHandle[tm,3])
→ solve_bump 成功（?m33949[rigid] := TimeoutHandle）
→ solve_multi_trait_ref(33949) 解 LetNamed trait 时报错并向外传播
→ flexside fail → 候选全败 → 用户可见 "solve trait failed: LetNamed[...]"
```

即 `solve_bump` 本身不失败，失败在其后**同一步内**的 `solve_multi_trait_ref`：
刚解出的 trait meta 触发对 `LetNamed` 的再求解。参考版同点位
（`unification.rs::solve_flex_side`：`solve` 后 `?` 传播 `solve_multi_trait`
结果）代码形状一致，故差异在**求解簿记/状态**，不在分支本身。

**2026-09-11 再进一步**（双引擎日志，插桩已移除）：把失败那一步的 trait meta
候选打出来，两版差异是"该步要解的 trait meta 集合不同"：

- 孪生：`solve_multi_trait_ref(m=33949)` 的候选 = `[33950]`，即**同一步内新
  产生的 trait meta 33950（trait 名 LetNamed）** 落在 `mv >= m` 扫描范围内，
  被求解 → 其候选实例化又和目标的 flex 参数对比 → 递归求解失败 → 错误外传。
- 参考版：对应调用形如 `solve_multi_trait(m=34237)`、随后 `m=34238` 且
  `metas_len=34238`（m 已等于 meta 表长度）——索引越界即 `continue`，没有可解
  候选，直接 Ok；整轮 `solve_multi_trait` 全程 `ok=true`。
- 佐证：同一步孪生 `trait_metas` 长度 6962，参考版同阶段 6942——**孪生多注册
  约 20 条 trait meta**。两版 `fresh_meta` 的注册条件逐句一致（先试实例合成，
  trait Sum 才 `new_meta + trait_metas.push`），故多出来的来自孪生在某些路径上
  多走了一次 `fresh_meta`（或某处 rollback 只回滚 `metas` 未回滚
  `trait_metas`——Nat 默认化回滚点是两版共有的，已核查非此因）。

结论不变但点位更窄：**修点是让孪生在该步的 trait meta 集合/求解顺序与参考版
一致**（或让 `solve_multi_trait_ref` 对"同一步新产生、正被外层求解的 meta"
不再递归触发）。需要两版同步 trace（给 `fresh_meta` 记逻辑 id）才能安全定位，
属 unify 核心子工程。

**2026-09-11 注册序列 diff（最终收窄，插桩已移除）**：给两版 `fresh_meta` 的
trait 注册点各打一行 `[REG] idx trait名`，同一输入跑完做序列 diff（按 trait 名，
忽略跨引擎索引差异）：

- 孪生 **6988** 条、参考版 **6942** 条；diff 结果**没有任何 delete，只有
  insert**——孪生的注册序列是参考版的**超集**：顺序一致，在 18-utils 用户文件
  段额外插入 46 条（名字集中在 `Cons` / `Data` / `Add` / `LetNamed`，其中
  **5 条 `LetNamed`**，正是后来递归失败的那个）。
- 机制（**已由下一步的 outcome 直方图修正，见下**）：`fresh_meta` 第一步是
  "先试实例合成"——合成成功即直接返回、**不登记**；失败才登记 trait meta。
- 下一步（可落地）：取首个额外注册（用户段起点，trait 名 `Cons`/`Data`）时
  `fresh_meta` 的 goal 值，直接对比孪生 `solve_trait_ref` 与参考版
  `solve_trait` 在该 goal 上的实例匹配走向（谁被选/为何推迟），这是有界调试，
  不再需要全序列对照。

**2026-09-11 outcome 直方图（再收窄，插桩已移除）**：给两版 `fresh_meta` 记
每次调用的结局（`synth` = 合成成功直接返回 / `reg` = 退化为登记）与 trait 名，
按 (结局, 名) 计数后 diff：

| trait | twin reg | ref reg | twin synth | ref synth |
|---|---|---|---|---|
| Data | 341 | 312 | 0 | 0 |
| Cons | 21 | 15 | 0 | 0 |
| LetNamed | 13 | 7 | 0 | 0 |
| Add | 6560 | 6555 | 0 | 0 |
| Into | 5 | 5 | **111** | **82** |

**修正了上一条的机制推断**：对 `Data`/`Cons`/`LetNamed`/`Add`，**两版都不合成**
（synth=0），所以多出来的 46 条注册**不是**"孪生合成失败退回登记"，而是
**孪生在这些 trait 上多调用了 `fresh_meta`**（多出的调用每次都会登记）。唯一
会走合成路径的是 `Into`，且孪生也更高（111 vs 82）。即根因更上游：**孪生某条
elaboration 路径比参考版多展开了隐参/洞**，从而多发 `fresh_meta`；`LetNamed`
那 6 条额外登记里就有后来递归失败的一条。

修点：对齐孪生那段多展开的 elaboration 路径（而非合成判定、更非簿记）。下一
步可用"按 `fresh_meta` 调用点给调用方打 tag"定位多出的 46 次来自哪个路径
（Phase A/B、ns 方法缓存探测、trait 候选 elaborat​ion 等），这是收敛的单点调试。




**任何孪生诊断都不可无验证地当权威**：`twin_elaborate` 现有两道闸——
(1) 遇任何 ERROR/parse 错误整体回落参考版；(2) **声明了模块的文件若
check 警告为空则回落**（干净的模块文件会多付一次参考版代价，方向安全）。
无错且非空警告的文件仍由孪生拥有、保留加速。原多文件未解析名安全阀被
(1) 涵盖，已删。

**全语料验收** `twin_matches_reference_on_all_hdl_examples`：23 例诊断逐条
一致（严重度/文案/range），且参考版能解析的每个用户文件标识符位置孪生都能
解析（无缺失 hover）。渲染文本/def_span 在宏生成的方法/限定访问路径上仍有
已登记偏差（见下），由 curated 守卫套件严格把关。

**代价（错误态）**：出错文件每 kick 白跑一次孪生（~100ms）再回落参考版
（~334ms）——即打字期（常态性临时错误）比纯参考版慢 ~30%。换取的是诊断
永远正确。若后续修掉 pattern 编译器的 false-unreachable（`13-adder-tree`
根因），此闸可放宽为"仅未解析名类错误回落"，该损失随之消失。孪生自产
诊断的逐条互检仍在 lib 层保留（`twin_user_errors_match_reference_diagnostics`），
以便修好后可验证地放开。

**新登记偏差（记录，暂不修）**：
- **ns-method 调用点的 hover 集合分叉**（19-stream 的 `outs.at(0, si)`，
  逐条 dump 实测）：参考版在该方法 token 上只有**一条实例化后**的条目
  （`(n: Nat, default: Stream[UInt[8]]) → Stream[UInt[8]]`），泛型签名挂在
  整个 `outs.at` 的宽 span（2273..2280）上；孪生在方法 token 上有
  **两条实例化（正确）+ 两条泛型签名**（`Vec.get` 的声明 π，含 `this`）。
  泛型条目经 ns_method 分派的 `push_hover(r.1)` 产生——即孪生对
  `App(Var(TypeHead.at), receiver)` 推的 `r.1` 是**未实例化**的声明 π
  （接收者未被 v_app 消费），而参考版同点位推的是实例化结果；且孪生缺
  参考版挂在宽 span 上的那条。`min_by_key` 平局取先时泛型条目可能压过
  实例化条目 → popup 文案错。根因在 ns-method 分派/实例化层，非 hover
  渲染层。
- 宏限定成员访问（如 `basicDecls.create[8].tree`）：孪生渲染 `create` 的
  签名，参考版渲染投影后的 `ModuleTree`（偏差 4 家族，与上一条同源）。
- 宏内 module-local 信号的 def_span 退化为使用处 token（只影响 goto，不影响
  popup 文案）——值层缺 binder span，偏差 6 家族。

**内存实测（决定默认的关键，2026-09-10）**：同一 09-hierarchy，进程 RSS
（`GetProcessMemoryInfo`）：

| | prelude 装载后 | 一次 kick 后 |
|---|---|---|
| 参考版 | 201 MB | **203 MB** |
| 孪生 | 203 MB（含 parse；prime 在首次 kick） | **1835 MB** |

孪生常驻 bump 的 prime 成本 ≈ 2.15GB `allocated_bytes`（RSS 1.8GB），
存量来自 **bump arena 不回收 prelude 装载期的中间值**；参考版的 Rc 图会
释放不可达节点故仅 200MB。**即：孪生以 ~9× 内存（+1.6GB）换 3.4× CPU。**
此后每 kick 的用户段增量落在既有 chunk 余量内（实测 0 增长），故不是
逐 kick 泄漏，而是一次性的常驻高水位。

**默认切换结论（当时）**：**暂不默认开启**。+1.6GB 常驻对编辑器 LSP 是硬伤
（`resident_memory_growth_per_kick` 记录了该测量）。twin 模式保持
`TYPORT_LSP_ENGINE=twin` opt-in，供 HDL 专用/内存充裕场景使用。要默认
开启需先降内存，方向：装载后 arena 压实、分段 arena（prelude 段与用户段
分离，用户段可 reset）、或对 prelude 只保留可导出视图而非全部中间值。

### 2026-09-10 续（arena 压实落地：内存 1835MB → 429MB，峰值 730MB）

**提交**：`L13_namespace/bump_spine_iter/compact.rs` 新增常驻态深拷器 +
`compact_state` 就地压实，`prime_resident` 在每个 prelude 文件边界与收尾
各压一次。

**原理**：bump arena 不回收，prime 期间产生的**不可达中间值**是内存主体。
可达根只有 decl 表（`Resident.cxt`）、meta（含 `MetaSnap` 快照）、会话
全局、`defs`、`spine.stack`、两张指针导入表。实测**可达仅 ~53MB**，其余
~1.4GB 是垃圾。深拷器按旧指针/旧打包字 memo 遍历值图（DAG 无环，memo 防
共享子树重复拷）：

- 打包值 `V`：tag 0/3/6 立即数、tag 2 spine 下标、tag 5 meta 下标原样保留
  （下标因**保序拷贝** `spine.stack`/`defs` 而仍有效）；tag 1/4/7 指针深拷
  并按旧打包字 remap。
- 需拷的 bump 类型：`Tm`/`XCell`/`CloCell`/`PiCell`/`EnvCons`/`TCons`/
  `LCons`/`PrCons`/`NsCons`/`SumParamV`/`SumDataV`/`SumParamT`/`SumDataT`/
  `DeclEntry`+`Decls`/`Names`/`MetaSnap`/`Cxt`/`str`（按指针 intern 保共享）。
- **无需拷**：`TraitState`/`Synth`（引用域 `Rc<Val>` 与 owned `Raw`，与 bump
  无关，跨 bump 交换原样存活）、`symbol_table`/`import_map`、
  `trait_method_cache`、`Rc<String>` 渲染串、观察三表。
- 每文件边界压实使 arena **只承载可达状态**，峰值不随装载累积；容量按上一次
  压实实测的 live ×2 提示，避开 bumpalo 倍增过冲。

**实测（09-hierarchy，release，Windows 工作集/峰值）**：

| | 参考版 | 孪生（压实前） | 孪生（压实后） |
|---|---|---|---|
| prelude 装载 | 5630ms / 196MB / peak 211MB | 2759ms | **4046ms / 392MB / peak 730MB** |
| 一次 kick | 369ms / 199MB | 98ms / 1835MB / peak 1847MB | **98ms / 429MB / peak 730MB** |

即：稳态 **1835→429MB（4.3×）**、峰值 **1847→730MB（2.5×）**，CPU 优势
（3.8×）不变，且启动（4.0s）仍快于参考版（5.6s）。常驻 bump 本身仅
**60MB 容量 / 53MB 已用**；剩余工作集主要是参考版 prelude 缓存（~200MB，
Path1/回落仍需）+ 压实换 bump 的分配器余量。

**正确性闸**：压实后的常驻态被全部孪生测试覆盖——`twin_engine_tests`
11 例（含 23 例 HDL 语料诊断逐条一致）、`resident_checkpoint_matches_fresh_
replay_across_kicks`（压实态 vs 全新重放逐字节一致）、两模式 11 套 LSP 守卫、
`l13_fast_parity` 389、observation 16、debug_test 15 全绿。`TYPORT_TWIN_NO_
COMPACT` 可关压实（对照测量用）。

**默认切换建议（更新）**：内存已从 9× 降到 ~2.2×（429 vs 199MB），启动
更快，CPU 3.8×——**已具备默认开启的条件**，建议在真实多文件 HDL 工程上
量一轮 P50/P99 与长时内存曲线后即可考虑切默认；跨文件工程仍回落参考版
（正确但无加速）。

---

## 2026-09-11（回归体检发现并行测试 UAF：已定位并修复）

`cargo test` 默认并行口径在 8-12 线程下稳定 `0xC0000005`（4 线程/串行全绿），
此前 §2026-09-09 记的"偶发资源竞争"实为**孪生内部悬垂 meta 快照**：

- 故障恒为 `HashMap<SmolStr, DeclEntry>::get`，map 指针为 Windows 堆释放填充
  `0xFEEEFEEE`；行号级栈为 `prime_resident:12398 → … →
  solve_multi_trait_ref:6197 → solve_trait_ref → eval → eval_iter:2261`。
- 根因：`solve_multi_trait_ref` 从 `self.metas[idx]` 的 `Rc<MetaSnap>` 里用裸
  指针借出 meta 创建处 `&Cxt`，再调 `&mut self` 的 `solve_trait_ref`；候选实例
  的嵌套 unify 会把该槽位替换成 `Solved`，丢掉快照最后一个 `Rc` 并释放它 ——
  仍被使用的 `meta_cxt`（其 `cxt.decls`）随即悬垂。参考版同点位是
  `arc_cxt.as_ref().clone()` 先克隆 `Arc` 保命，孪生移植时缺了这一步。
- 修复：同点位克隆 `Rc<MetaSnap>` 作保命引用（语义与参考版一致，只防提前
  释放）。修复后 12 线程 16/16 绿、完整 `cargo test` 默认并行全绿。

已排除的其它嫌疑（均带 A/B）：prelude 池交接（`TYPORT_NO_PRELUDE_POOL=1`
关池后同点崩溃，开关生效经 -j4 套件 31s→9m42s 验证）、arena 压实
（`TYPORT_TWIN_NO_COMPACT=1` 同点崩溃）、内存耗尽、栈溢出。完整证据链见
`docs/l13-parallel-test-uaf-2026-09.md`。**回归闸恢复默认并行即可。**

---

## 2026-09-11（wasm 后端接入孪生 + 状态栏切换）

**背景**：孪生此前只在 CLI 后端可用——`TYPORT_LSP_ENGINE` 只由
`extension.desktop.ts` 的 CLI 分支注入，wasm 分支（`extension.ts`）从不给
进程传 env；且模块线性内存上限 ~1 GiB，容不下压实前的 1.8 GB。压实落地后
峰值 730 MB，上限才有谈的余地。

**接线**：

- **env 注入**：wasm 进程创建时经 `ProcessOptions.env` 传
  `TYPORT_LSP_ENGINE=twin`（`@vscode/wasm-wasi` 的 `Environment` 支持该
  字段，WASI guest 由 `Engine::from_env` 读取）。这与 CLI 分支的 env 注入
  是同一个内核入口，不新增引擎分派代码。
- **内存上限**：`extension.ts` 的 memory descriptor `16000` → `32768` 页
  （~976 MiB → 2 GiB），`package.json` 构建脚本 `--max-memory=1048576000`
  → `2147483648`。两者必须同步：wasm32-wasip1-threads 模块导入的 shared
  memory 边界由 linker 决定，descriptor 必须匹配，否则实例化失败。2 GiB
  对 730 MB 峰值留约 2.7× 余量。
- **状态栏切换**：新增 `client/src/serverActions.ts`，桌面两个后端都提供
  引擎组（`Reference` / `Twin (performance)`）与后端组（`WASM` / `CLI`）；
  引擎切换写 `typort-hdl.cli-server.engine` 后就地重启（两个后端都读它），
  后端切换因激活期语义需重载窗口。web 宿主（不能 spawn CLI）固定
  reference，不显示切换项。
- 顺带修掉重复注册：`extension.desktop.ts` 原先在分支前注册
  `showServerActions`，wasm 分支的 `activateWasm` 又注册同名命令。

**验证边界**：本地完成 TS `tsc -b` + esbuild 打包、以及
`cargo rustc --target wasm32-wasip1-threads` 带新 `--max-memory` 的链接，
确认 wasm-ld 接受 2 GiB；**未在 VS Code 运行时里真机点过**——env 注入与
2 GiB 上界在 wasm-wasi 宿主下的实际行为（含孪生常驻态是否稳定）仍待一轮
真机验证。


