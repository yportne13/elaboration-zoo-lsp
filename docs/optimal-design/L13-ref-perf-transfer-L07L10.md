# L13 参考版性能优化 → L07–L10 参考版的移植可行性

> 角色：metrics/analysis（L07 分析员复用）。时点 2026-11-09；对象：`master` 工作树（只读静态核对，
> **未跑 cargo/bench**，行号用 `[IO.File]::ReadAllLines` 口径，1-based）。
> 证据分级：`[码]` 源码核对 / `[文档]` 仓库既有文档 / `[历史实测]` 仓库既有实验数字（注明出处）/
> `[推断]` 未实测。目标读者：想给 L07–L10 参考版做"简单、可被其他章节参考"的优化。

## 0. 结论（TL;DR）

1. **真正属于"L13 参考版"且可小改移植的只有 3 项**：L08 的 `simpl_decl` 缓存（照 L13 `DECLB_CACHE`）、
   L10 的 trait `head_index`、L10 `force` 的 `Rc::ptr_eq` 无变化短路（详见 §2）。
2. **不建议移植**：`FORCE_MEMO`（L13 的收益前提是 prelude 级共享值图，L07–L10 没有；σ/VSub/探针回滚
   还需要额外守卫）、`scan_def_replay`（HDL 专有）、`typ_pretty`（LSP hover 专有）、
   `Span<()>`/decl 7 元组 COW（L13 自己的 893ns/entry 形态，L07/L08 已是 2 字段 7ns/entry）。
3. **三处“候选误归因/已具备”**：`force` 的 Sum-WHNF 叶子在 L07–L10 本来就是叶子（无需移植）；`quote/rename`
   迭代化是 L07 的成果而非 L13 参考版（L13 参考版本身是递归）；`mimalloc` 已在全部 bench bin 挂载。
   特别问三答见 §4：Sum-WHNF 对所有层安全（已等价）；`Span<()>` 不能直接抄进 L07/L08 decl 表；
   `FORCE_MEMO` 确实会被 σ/VSub 的键语义卡住（§4.3）。

## 1. 候选逐项判定

| 候选 | L13 参考版锚点与证据 | L07/L08（decl 表 + σ） | L09/L10（global 哨兵，无 decl 表） | 判决 |
|---|---|---|---|---|
| **FORCE_MEMO** | `mod.rs:163`（TLS `FxHashMap<usize,(Rc<Val>,Rc<Val>,ver,epoch)>`）、`:194` cap 1<<20、`:2662-2709` 只对 `SumCase/Call/Obj` 入口 memo、taint `:2687-2690`、纯 prim 白名单 `:155-160`；README §3.3：prelude force **636M 次 / 188k 节点（~3400× 冗余）**，HDL prelude **11.0s→1.8s** `[文档]` | `force(Val)→Val` 按值（L07 `mod.rs:790`、L08 `:643`），无 `Rc` 身份可做键；即使改成 `&Rc<Val>`，σ 链/回滚与 `meta_restore` 会破坏“同输入同输出”前提 | L09 同样按值（`mod.rs:555`）；L10 是 `&Rc<Val>`（`:591`，结构上最接近），但同样有 σ/VSub + 探针回滚 | **不推荐**（风险>>收益；L10 若做须先 EXP-4 证明命中率） |
| **decl 表 COW / `&mut Cxt` 就地插入** | `cxt.rs:1303-1310` `decl(&mut self,…)+Rc::make_mut`，7 元组见 `mod.rs:432`（含 `Span<()>`+`typ_pretty`），条目 ~893ns（`cxt.rs:1235` 注释）；与 `scan_def_replay` memo 合修实测 struct **87.9×**、strchain **244×**（`bench-matrix-2026-09-20.md:374,422`）`[历史实测]` | **同款"先 clone 再 make_mut"仍在**：L07 `cxt.rs:258-262`、L08 `cxt.rs:195-197`；但条目仅 `{ty,val}`（L07 `:67-71`/L08 `:23-27`）、≈7ns/entry（`bench-matrix…:386-387`），且 L07/L08 已是同负载最快层（122/134ms，`bench-matrix…:428`）——09-20 轮刻意未动；改成 `&mut Cxt` 会破 L07 的“全程持久派生、无 &mut 改写点”纪律（`cxt.rs:79-83`）并波及 check 调用面 | 无 decl 表；`global_names` 已 append-only `FxHashMap<String,(Lvl,Rc<VTy>)>` + `shadow_local`（L09 `mod.rs:456/482`，L10 `:465/493,515-547`，“返回 Cxt 克隆是 O(1)”注释 `:526`），2026-09-20 已落地 | **小收益/中等成本，不建议本轮移植**（除非 L07/L08 要跑百级 def 语料） |
| **`typ_pretty` def-site 缓存** | decl 第 7 槽（`cxt.rs:1293,1303`），消费方只有 LSP hover（README `:300-304`：“hover 必须显示预计算串”）`[文档]` | 无 LSP/观察面，无消费者 | 同 | **别抄**（纯税） |
| **FxHashMap / SmolStr** | L13 用 `rustc-hash` 于 Decl/`FORCE_MEMO`/`no_metas` seen-set；isolated 贡献 **~1%（噪声边缘）**（`l13-perf-review-4.md:908-911`）`[历史实测]` | decl 表与 src_names 键已是 `SmolStr`，但 map 仍 std `HashMap`（L07 `cxt.rs:34`、`src_names` 键是 `String` `:84`；L08 `:21,35`） | `global_names` 已是 `FxHashMap`（L09 `mod.rs:456`、L10 `:465`）；`global`/`class_instances`/`assertion_table` 仍 std（L10 `typeclass.rs:148-150`） | **顺手可做、不值得单列任务** |
| **`head_index`（L10 trait）** | `typeclass.rs:96-98`（`HashMap<(trait,head),Vec<usize>>`）、`head_key :119-125`、`GENERIC_SELF_HEAD :131`、登记 `:155-190`、`can_satisfy :192-240`；孪生 README `:322` 同机制 `[码]` | 无 trait（L10 才加） | **L10 参考版 + 孪生共用同一 `Synth`**（孪生 `bump_spine_iter/typeclass.rs:14-19` 直接 `use …::{Assertion, Synth, Typ}`）→ 改一处两引擎同受益、无 parity 分歧；当前 `Synth` 只按 trait 分桶（`class_instances: HashMap<String,Vec<Instance>>` `:148`），`new_subgoal` 每个子目标**克隆整条实例 Vec** 并按线性下标试（`:287-308`、`:270-280`） | **Top（L10 唯一明确机会）**，但收益占比需实测（见 §2.1） |
| **`scan_def_replay` memo** | `mod.rs:3152`（def 体内 HDL 语句重放探测）；与 decl 就地写合修是 L13 struct/strchain 87–244× 的另一半（`bench-matrix…:374,422`） | 无 HDL/无 def replay | 同 | **只在 L13 有意义** |
| **`force` 把 `Val::Sum` 当 WHNF 叶子** | `mod.rs:2887-2897`：Sum 已 WHNF，参数由消费方按需 force；修前 examples/10-bundle 有 **29M/33M 次 force 落在 Sum**（`:2893-2894`）；孪生 `force.rs:651` 同口径 `[码]` | **本来就是叶子**：L07 `force` 无 Sum 臂，默认 `t => t`（`mod.rs:896`）；L08 同形态（默认臂 `:723`） | L09 只有 Flex/VSub 两臂（`mod.rs:555-568`，`:567 _ => t`）；L10 同（`:591-611`，`:610 _ => t.clone()`） | **已具备、无需移植**；勿反过来加“强制子值”臂 |
| **`Span<()>` decl 表设计** | `Decl` 7 元组：`(Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>, Option<PrimFunc>, String)`（`mod.rs:432`），名字在 map 键、span 只留位置（`DeclSpan` `:441`；`src_names` `cxt.rs:330` 同款） | `DeclEntry` 只有 `{ty,val}`，**没有 span/名字槽可缩**；`Span<String>` 遍布 `Tm/Val`（L07 `mod.rs:70-89`）与 `Cxt.bind`（`cxt.rs:290`）——要改是语法层全量重构 | 同（`Span<String>` 遍布，L10 `mod.rs`/`typeclass.rs:11,13,15`） | **不可直接抄**（详见 §4.2） |
| **quote/rename 迭代化 / 记忆化** | L13 参考版 quote 递归（`mod.rs:3613,3627`），rename 递归（`unification.rs:370`）；quote memo 仅孪生（`bump_spine_iter/machine.rs:1366`） | **L07 才是迭代化来源**：`quote_deep`（`mod.rs:1467`）、`rename_deep`（`unification.rs:377`）、`val_mentions_lvl`/`struct_eq` 任务栈（L07 README §6/§7.6）；L08 无 `quote_deep/rename_deep`（`mod.rs:1264` quote） | L09/L10 quote 均递归（L09 `:899`、L10 `:987`），无迭代化 | **误归因**：这不是 L13→L07 的转移；反向 L07→L08/L09/L10 是**健壮性**（P11 深值），非性能，且行数大 |
| **`simpl_decl` 缓存** | **L13 参考版有** `DECLB_CACHE`（`mod.rs:1249-1260,1268-1310`，单槽按 decl 指针键，轮界清） | L07 已有按 `Decls.ver` 的 per-Infer 缓存（`mod.rs:605,657,1915`）；**L08 无缓存**，每次重建（`mod.rs:1324,1447`、`unification.rs:387,891`） | L09/L10 无 simpl 机制（Match 分支体走中性 global 克隆，L09 README §6.2） | **Top2：L07/L13 的缓存形态 → L08**（若 L09/L10 将来引入 struct_eq 再议） |
| **`struct_eq` 快路径** | L13 无（其值层比较走 unify/Call 快路径） | L07/L08 有（L07 `struct_eq.rs`；L08 `unification.rs:865,876` 调用） | **L09/L10 明确没有**（L09 孪生头 `bump_spine_iter.rs:82-83`、L10 孪生头 `:111` 均写“无 struct_eq 快路径/分节”） | 这是 **L07/L08→L09/L10** 的机会，不属于 L13 转移；~300–400 行 + 孪生镜像，收益 `[推断]` 中低 |

## 2. 简单可抄 Top 3（都 ≤~60 行、不改公开 API）

> 与并行清单 `L13-ref-perf-inventory.md` 的对账（目标层修正，避免把 L07–L10 没有的节点/设施算进来）：
> ①清单 #7「unify Call 无-Flex 预检」不适用于本报告目标——`Val::Call` 只在 **L12/L13** 存在
> （grep：L12 12 处、L13 46 处，L07–L10 为 0）；②#8「trait_wrap 惰性 meta 快照」的 `ns_entries`
> 是 L13 namespace 专有（L10–L12 为 0），**该具体快路径抄不到 L10**；L10 的同类热成本是
> `trait_definition.clone()`（`elaboration.rs:1011-1012`，源码自带 TODO），属 L10 自有候选；
> ③#10「no_metas visited-set」符号只出现在 **L11–L13**（L07–L10 grep 为 0），目标应改 L11–L13；
> ④#6/#9 与本报告 Top2/Top1 一致；#1 对 L07/L08 是同模式但成本 M（见 §1 行）；#4/#15/#16/#17 同意“别抄/仅 L13”。

### 2.1 【Top1】L10 trait `head_index`（移植 L13 `typeclass.rs:96-240`）

- **改动**：`src/L10_typeclass/typeclass.rs` 单文件（参考版 + 孪生共用）。①`Synth` 增 `head_index:
  HashMap<(String,String),Vec<usize>>`；②注册处（`impl_trait_for` `:168-173` 旁）按“第一个非 out 参数”的
  `Typ` 头建桶，`Typ::Construct(span,..)`/`Typ::Val(span)` 取 `span.data`，`Var/Flex` 落 `"*"` 通配桶
  （L13 `head_key :119-125` 的 `Val` 版要改写成 `Typ` 版 ~10 行）；③`new_subgoal`（`:287-308`）把
  “克隆整条 `class_instances[..]`”改为“克隆候选**下标** + 通配桶 + 未索引回退”，`GeneratorNode`
  （`:90-95`）的 `instances: Vec<Instance>` 改 `indices: Vec<usize>`，`try_resolve` 处按 `&instances[idx]`
  取值（约 +15/−10 行）。
- **为什么简单/安全**：纯索引，不改求解语义；L10 两引擎共用同一 `Synth`（孪生 `bump_spine_iter/typeclass.rs:14`），
  **无 parity 分歧面**；L10 无 L13 的 checkpoint 撤销帧（`Synth` 每次 `clean()` 只清搜索栈/答案表，
  `typeclass.rs:175-180`），因此也不需要移植 `StateUndo`。
- **预期收益**：直接命中两个成本——`new_subgoal` 的整表 `Instance` 克隆（`:299`）与线性试实例（`:270-280`）；
  L10 `traitchain` 是全场最大参考版热点（D4 §3：basic **23,791ms** vs 孪生 39.4ms）`[实测]`，但其差距主因
  是引擎侧 `close` 死重（D4 §4：basic 5.3GB/1.22 亿分配，孪生侧 `close_tm_reduced` 仅落孪生；L10 README §6.0），
  **head_index 只吃实例扫描/克隆那一段，占比待 EXP-4 A/B** `[推断]`。**建议先测再决定是否保留**。

### 2.2 【Top2】L08 `simpl_decl` 缓存（照 L13 `DECLB_CACHE` 或 L07 `simpl_cache`）

- **改动**：`src/L08_product_type/mod.rs`/`cxt.rs`（参考版；孪生已有等价物，但 L08 孪生是独立实现，需同步）。
  照 L13 单槽 `(Rc::as_ptr(decl), Rc<Decls>)`（`mod.rs:1249-1310`）或 L07 的 `Infer.simpl_cache`
  version 键（L07 `mod.rs:605,1915`，需给 `Decls` 加 `ver` 或直接用 `Rc::as_ptr`）。把
  `mod.rs:1324,1447`、`unification.rs:387,891` 四处 `simpl_decl(decl)` 换成 `simpl_decl_cached(...)`。
- **为什么简单/安全**：纯缓存，`simpl` 幂等、同 decl 实例同内容（L07 `cxt.rs:26-29` 已有论证）；~25–40 行；
  不碰 σ/名字世界/API。
- **预期收益**：消除“每次卡住 Match 消费（quote/rename/unify）都 O(#decl) 重建简化表”的常数；L08 bench
  match 0.148ms 规模小，收益在**深证明/多 def 源码**上放大（L07 的性能评审 P1-2 即因此落地）`[推断]`；
  可用 L08 现有 eq/GADT 测试的耗时（debug）做前后对照。

### 2.3 【Top3】L10 `force(Obj)` 无变化短路（照 L13 `mod.rs:2744-2748`）

- **改动**：`src/L10_typeclass/mod.rs:607-609` 的 `Val::Obj` 臂：`let xf = self.force(x); if
  Rc::ptr_eq(&xf, x) { t.clone() } else { Val::Obj(xf, a.clone(), b.clone()).into() }`（~6 行）。
- **为什么简单/安全**：L10 `force` 已收 `&Rc<Val>`（`:591`），`Rc::ptr_eq` 短路在 L13 有同款先例；
  不改变结果，只省一次 `Val::Obj` 重建 + span/spine clone；L07/L08 因 `force(Val)` 按值不适用（它们
  没有 `&Rc` 身份，别硬改签名）。
- **预期收益**：投影/struct 负载每次 force 都重建 Obj（L10 struct 孪生 4.403ms，参考版口径未输出）；
  allocation 级收益 `[推断]` 小但确定；可作“零风险顺手项”。

## 3. 只在 L13 有意义 / 别抄

1. **`FORCE_MEMO`**：收益前提是 L13 prelude 的**共享大值图**（636M force/188k 节点）；L07–L10 无 prelude、
   值图小，命中率远低；且要重写 keepalive/taint/version/epoch 并额外接 σ/meta-rollback/fuel 守卫（§4.3）。
   对教学层它是“高风险低收益”的典型，D5 的“单引擎统一 memo 接口”结论也不在此处落地。
2. **`scan_def_replay` memo**：L13 HDL/def replay 专有（`mod.rs:3152`）；L07–L10 没有 replay 消费者，
   照抄只是死代码 + 新不变量。
3. **`typ_pretty` def-site 缓存**：唯一消费方是 LSP hover（L13 README `:300-304`）；L07–L10 无观察面，
   缓存串只会增加 decl 条目内存（L13 的 893ns/entry 里就有它的一份税）。

## 4. 特别回答

### 4.1 `force` 的 Sum-WHNF 叶子快路径对所有层都安全吗？

- **L07–L10 早已是“叶子”**（L07 `mod.rs:896`、L08 `:723`、L09 `:567`、L10 `:610` 的默认臂），所以这条
  “移植”实际是 **no-op**；真正要做的是**不要**在它们身上新增 L13 修前的“eager 递归 force Sum 子值”臂。
- 语义上安全：`force` 只需给出 WHNF；Sum 是构造子头，参数值/类型是构造子实参，**任何需要规范参数的
  消费点自己 force**（L13 `:2887-2896` 的理由：修前 examples/10-bundle 29M/33M 次 force 落在 Sum，
  且结果几乎恒为 `t.clone()`）；L07–L10 的消费点本来就是按需口径（unify 入口 force、project、quote 逐层）。
  若某层曾依赖“force(Sum) 顺带 force 参数”的隐含不变量，需先审计 call site——本轮 grep 未发现。

### 4.2 `Span<()>` 改法在 L07/L08 的 decl 表里能直接抄吗？

- **不能**。L13 的 `Span<()>` 是其 decl 7 元组 + `src_names: BiMap<SmolStr,Lvl,(Span<()>,Rc<VTy>)>`
  （`mod.rs:432,441`；`cxt.rs:330`）的一部分：**名字在 map 键（SmolStr）、span 只留位置**，供 hover 显示。
  L07/L08 的 `DeclEntry` 只有 `{ty, val}`（L07 `cxt.rs:67-71`、L08 `cxt.rs:23-27`）——**没有 span/名字槽可缩**；
  名字在 `HashMap<SmolStr, Rc<DeclEntry>>` 键里，`src_names` 是 `String` 键（L07 `cxt.rs:84`、L08 `cxt.rs:35`）。
- 要吃到 `Span<()>` 的收益，得把 `Tm/Val` 全体系的 `Span<String>`（L07 `mod.rs:70-89` 等）改成
  `Span<()>`+SmolStr——语法层全量重构 + pretty/错误路径 + 双引擎 parity，**收益却接近零**（L07/L08
  entry 已 ~7ns/entry，L13 的 893ns 是高载荷 7 元组 + typ_pretty + 先 clone 再 make_mut 的合计）。
  低风险子集可考虑：`src_names` 键 `String`→`SmolStr`（L07 `cxt.rs:84`），但 L07/L08 热点不在名字表，优先级低。

### 4.3 `FORCE_MEMO` 移植到 L07 是否会被 σ/VSub 的键语义卡住？

**会，且不止一处**：

1. **没有键**：L07/L08/L09 的 `force` 收 `Val` 按值（L07 `mod.rs:790`、L08 `:643`、L09 `:555`），L13 的 `Rc::as_ptr(t)` 键（`:2674`）无处可取；改 `&Rc<Val>` 是签名级改动（全 call site + 测试）。
2. **VSub 语义**：`force(VSub(v,σ))` 结果依赖 σ 链内容与“哪些解已 extend”；σ 在臂边界整体回滚、方程间持续 extend——按输入地址缓存必须把 σ 身份/epoch 并进键，或只缓存“无 VSub 的值”（命中率再降）。
3. **meta 回滚**：L13 的 taint 只防走查途中 consult **未解** meta；L07 的 `probe_accessible` 会 `meta_snapshot/meta_restore`（`pattern_match.rs:355,401`）把**已解** meta 回滚，同一输入 Rc 的已缓存结果会过期——L13 无此失效面。
4. **fuel 依赖**：L07 force 在展开点烧 fuel，耗尽返回**裸 rigid**（`mod.rs:919-921`）；同输入在不同 fuel 余量下结果不同，L13 memo 未把 fuel 进键——移植须再加 fuel 守卫或“仅 fuel>阈值入表”。
5. **结构性最优候选只有 L10**（`force(&Rc<Val>)`，`:591`），但仍有 2–4 的守卫成本；且无 prelude 级共享图，预期命中率远低于 3400×。**无 EXP-4 命中率数据前不要做**；若做，先做“只缓存 `SumCase`、无 VSub、taint 含 meta 版本、per-Infer 清空”的最小版，并用 L09/L10 parity 门禁。

## 5. 验证与风险控制（若采纳 Top 项）

1. **门禁**：每项先跑 `cargo test --lib L0X -- --test-threads=1` + `cargo test --test l0X_fast_parity`
   （L08/L10 参考版与孪生行为逐字节/判定一致）。**A/B 口径**复用 D4/EXP-4：单二进制、独立进程、
   ≥3 轮 min、配对交错；L10 traitchain basic 单次 ~24s，只适合两臂各 1 次 + 小规模 k；报“绝对 ms+分配数”。
2. **预期落空信号**：head_index 若只减少候选扫描而 `new_subgoal` 的 clone/close 仍在，L10 traitchain
   不会明显下降 ⇒ 应转去回灌孪生的 `close_tm_reduced`（L10 README §6.0；D4 §4 有 5.3GB→30.6MB 证据），
   那才是 604× 的主因。**不做**：不改 `force` 签名（波及 L07/L08/L09 全部 call site 与 parity）；
   不为 FxHash/mimalloc 单开任务（前者 ~1%，后者已挂载）；不在教学层引入 L13 的 7 元组 decl/typ_pretty/scan_def_replay。

**给 Lead 的一句话**：可转移的只有“L10 head_index + L08 simpl 缓存 + L10 force 短路”三个小件；
L13 的旗舰 FORCE_MEMO 与 decl 7 元组优化依赖 prelude/LSP 负载与更新式世界，L07–L10 不满足前提，别抄。
