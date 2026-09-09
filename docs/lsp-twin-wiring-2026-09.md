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
| tuple-mk 元素（2577） | ❌ |
| ns-method/trait 方法（2839/2982） | ns 支理论等价免接；trait-definition 支 ❌（需 trait_definition 方法名 span 穿线） |
| PM 构造子 pattern token（pattern_match 907） | ✅（Con==Con arm 构造路径；无参→Tree::leaf、参数化→Pi；`9a6faff`） |
| enum 构造子定义处（use==def==声明 token） | ✅（constrs 从 decl 表回填声明 span；prime 渲染差属偏差 4） |
| impl header（1462/1482） | ❌ |
| completion（2431/2446/2466/3001/3035） | struct/SumCase 命中与未命中 4 点 ✅；trait 方法候选（3001/3035）❌ |
| inlay（def 1157 / let 2601） | ✅ 两点（def peel_pi_collect 收 telescope names；偏移-标签集互检过） |

**性能事实（prelude-hdl 943 decls，release）**：
- 观察面接线前：fast 2204ms / fast_ss 1865ms。
- 接线后（五组 hover + completion）：fast ~2455ms / fast_ss ~2067ms，**+11%**。
- 归因：与参考版 eager 化同比例（参考版 prelude-core 亦 +11%）——是
  **push 期渲染契约的对称成本**，非孪生退化；对参考版领先维持 ~1.3×。
- 微优化候选（统一做，不分引擎）：local 使用处渲染 memo by (lvl,V)、
  Names 已并 (V,Span) 二表。

**回归闸（每提交必绿）**：`l13_fast_parity` 377、`observation_tests` 4 例
（global/local/field/completion 双引擎集合级互检）、`debug_test` 15、
LSP 守卫 12 套、bench 各 workload nf 一致。

### 下一步（顺序建议）
1. let-inlay + def-inlay（先 let，简单）。
2. PM 构造子 pattern hover + enum case 列表（905/pattern_match 907）。
3. trait-definition 方法 hover（2982）+ trait 方法 completion（3001/3035）。
4. push_qualified_hover + tuple-mk + suffix-fallback + impl header。
5. 字段 binder span 评估：XCell::Sum 的 params 带上 Span（值构造面改动）。
6. 阶段 2（prelude 加载）与阶段 3a（全量重推 seed 成本实测）并行启动。


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
