# 02 · 合一（unify）与结构相等（struct_eq）· L07 ⟷ L13

> 角度：unify 的对外契约 + struct_eq 的去向。HEAD `911628b3`，全部锚点本轮重核；未构建、未运行二进制。
> 引用 Lead 的 `fn-matrix.tsv`（函数体 5-token 相似度）与 `tmp/l07l13_similarity2.tsv`（文件级 shingle），
> 但行号以我自己读到的为准（矩阵行号去注释后整体偏移 ~7–10 行）。

## 1 范围与方法

读透（非抽样）：`L07_sum_type/unification.rs`(1187 行)、`L13_namespace/unification.rs`(1279)、
`L07_sum_type/struct_eq.rs`(346)、`bump_spine_iter/struct_eq.rs`(399)、`L13_namespace/struct_refine_probe.rs`(260 行, test-only)；
孪生 `bump_spine_iter/unify.rs`(912 vs 1292) 按 Match/Match、快路径、memo 三处抽查。
方法：先 grep 建 `fn`/`Val`/`UnifyError` 符号表，再按「入口契约 / 结构快路径 / 预算 / 加固项」四条逐一对照；
单边文件（struct_eq）不在 Lead 的 tsv 口径内，只有字节与行数。

**先纠一处底稿**：MAP §2 写"L09 起删 struct_eq"——**过期**。L09/L10/L11/L12 至今都有 `struct_eq.rs`（含孪生），
L12 仍在调用（`L12_canonical/mod.rs:38`、`unification.rs:1253-1264`）；**L13 才是第一个没有它的层**。

## 2 模块对位表

| 文件 | L07 tok/行 | L13 tok/行 | 保留率(文字/归一) | 判读 |
|---|---:|---:|---|---|
| `unification.rs` | 9,605 / 1187 | 10,641 / 1279 | 36% / 56%（jac 20%/36%） | **继承骨架 + 头部重写**：11 个算法函数 0.6–0.9，入口/int/solve 全改 |
| `bump_spine_iter/unify.rs` | 6,366 / 912 | 9,138 / 1292 | 54% / 70%（jac 29%/42%） | **扩张**：同一工作站迭代器，新增 Call/Nat/trait 三类任务 |
| `struct_eq.rs` | 16,125 B / 346 行 | — | — / — | **E3 整模块缺失**（L13 首个没有它的层） |
| `bump_spine_iter/struct_eq.rs` | 17,005 B / 399 行 | — | — / — | **E3 整模块缺失**（孪生侧同删） |
| `struct_refine_probe.rs` | — | 10,688 B / 260 行 | — / — | **E4 单边新增**，且是 `#[cfg(test)]`（见 §4.1），不是 struct_eq 的替代品 |

函数级底稿（`fn-matrix.tsv`，unification.rs 22 个同名函数，我按代码复核过配对）：
`intersect_go` 0.89、`invert` 0.88、`prune_vflex_go` 0.79、`intersect` 0.78、`unify_no_arm` 0.77、
`prune_ty` 0.76、`is_canonical_head` 0.79、`rename_sp` 0.69、`flex_flex` 0.61、`unify_sp` 0.57、`solve_with_pren` 0.52；
而 `unify` 0.35、`rename` 0.01、`solve` 0.05、`lift/skip` 0.00–0.03。
⇒ 分化轴很清楚：**"求解方向的可逆性计算"是同源，"入口 + 求解 + renaming"是重写**。

## 3 逐机制差异表

| 机制 | L07 实现（锚点） | L13 实现（锚点） | E 档 | 可观察后果 / 风险 |
|---|---|---|---|---|
| unify 入口签名 | `unify(&mut self, decl:&Decls, l, cxt, t:Val, u:Val, spec:Option<&mut SpecSolve>) -> Result<(),UnifyError>` `unification.rs:894-902` | `unify(&mut self, l, cxt:&Cxt, t:&Rc<Val>, u:&Rc<Val>, fuel:u32) -> Result<(),UnifyError>` `unification.rs:1055` | **E2** | 值按引用 + 显式 `fuel` 递归参数；能力集不同（L07 可带精化 σ，L13 不可） |
| 值表示 | `Val` 枚举按值，仅槽位 `Rc`；有 `VSub(Rc<Val>,Rc<Subst>)` `mod.rs:301-337` | `Val` 全 `Rc`；有 `Call(SmolStr,List,..)`、`Nat(u64)`、`U(u32)`，**无 VSub** `mod.rs:906-941` | E2 | L07 的显式替换在 L13 不存在（σ 族整体删除，见 03 号文） |
| 错误类型 | 单元结构体 `pub(crate) struct UnifyError;` `mod.rs:615` | 枚举 `{Basic, Stuck, Trait(String)}` `mod.rs:1371-1375` | **E2** | L13 能表达"暂时解不出（可挂账）"与"trait 无解"，L07 一律失败 |
| 产物：解 vs 约束 | 只写 `meta`（`overwrite_meta` `unification.rs:734`）；精化解写 `SpecSolve::acc` `unification.rs:995-997` | 写 `meta` **+** `meta_contrains:Vec<(Rc<Val>,Rc<Val>)>` `mod.rs:1479` + `trait_metas` `mod.rs:1480`；Stuck 时挂账 `unification.rs:1046-1049` | **E4** | L13 有"延迟约束"这一层，失败不再是终局（`canonical.rs:142` 清账） |
| fuel | 池 `unify_fuel`（4096，可被 `TYPORT_UNIFY_FUEL` 覆盖 `mod.rs:779-787`），入口内联烧 `unification.rs:905-918` | 池 `unify_fuel`（4096，**无环境覆盖** `mod.rs:1468,2319-2321`）+ 独立 `fuel:u32` 递归参数（护 Decl 展开重试 `mod.rs:1464-1467`） | E2 | L13 少一个基准放大阀门（smalltt 级负载需改常量重编）[推断：L13 无对应基准] |
| 卡住 match 预算 | `MATCH_CMP_BUDGET=64`，**结构快路径先试、慢路径才计数**；耗尽记 `Undecided` `mod.rs:789-800`/`unification.rs:1158-1166` | 同 64、同"每顶层入口一份"；但**无快路径，一律计数**；耗尽记 **`Fuel`** `mod.rs:2337-2348`/`unification.rs:1250-1261` | **E2** | 同一方程两侧分档不同 ⇒ 覆盖探测兜底不同（Fuel 按"可达"处理，Undecided 不） |
| 结构相等快路径 | `struct_eq::{val_eq,env_eq,tm_eq}`，`EQ_BUDGET=20_000`，同址短路 `struct_eq.rs:36-53`；调用点 `unification.rs:1143-1154` | **无**（`L13_namespace` 全域 grep `val_eq|EQ_BUDGET|struct_eq` 只剩注释） | **E3** | 见 §4.2：自比较从 O(结构) 退化到 64 次分支重求值后判"不可信" |
| occurs check | 浅 `val_mentions_lvl` + **传递 `occurs_transitive`**（`mod.rs:442-452`，用在刚性解臂 `unification.rs:987-994,1009-1016`） | 只有浅式（注释自承 "solve 无跨 meta occurs check" `mod.rs:1467`） | **E3** | 两跳环 `x:=a, a:=succ x` 在 L13 只靠 fuel 兜底 → 可能烧穿池后误报 can't unify |
| 宽松 String 臂 | `loose_string`（`unification.rs:872-892`），P8 收窄为"未登记名仅空 spine 放行"，两条臂 `:1067-1072` | 无此臂；`(LiteralType, Decl(n,[]))` 落 `(_,Val::Decl(..))` 臂 `unification.rs:1158-1175` → quote→eval 自旋至 `fuel==0` 记 `Fuel` | **E3** | [推断] L13 里"动态类型逃逸"不可用，且坏形态是**烧光 fuel 再失败**（成本 + 分档都比 L07 差）——未跑二进制验证 |
| 字面量相等臂 | `:1062`（条件 `a.data==b.data`） | `:1213`（同形） | E1 | **血缘是 L13→L07**：L07 自注"L13 `unification.rs:1135` 同款…L09–L12 仍未补" `unification.rs:1058-1061`；git `c6c0e892`(2026-11-16) 只改 L07/L08，L13 早已有 |
| rename / renaming | 递归 + 手工栈帧：`rename`(28 行)`unification.rs:344-369`、`rename_arm`:552、`FrameKind`:383、`REN_DEPTH`:345 | 单函数 120 行迭代化，无 `rename_arm`/`Frame`/`REN_DEPTH`（矩阵 0.012） | E2 | 同一份 renaming 语义两套实现；L07 侧多一个全局深度计（调试面） |
| 头部短路 | 无 Call 概念 | `(Call,Call)` 同名先比 spine（无 Flex 免快照，有 Flex 三重快照回滚）`unification.rs:1077-1104`；孪生同位 `bump_spine_iter/unify.rs:663-700` | **E4** | 定理证明型负载的热路径；**部分**替代了 struct_eq 的角色（只对 Call 头有效） |
| 求解失败回退 | `solve` 4 行直调 `invert`→`solve_with_pren` `unification.rs:697-700` | `invert` 返回 Stuck 时走"不可逆 spine 常数解"回退 `unification.rs:562-613` | E4 | L13 能解 L07 解不出的 meta（也带来 clamp π 链等新 panic 面，见 §4.3） |
| Decl 展开重试 | 无（不匹配即落到 solve/unify_no_arm） | `(Decl(..),_)`/`(_,Decl(..))` 臂 quote→eval 重试 + `is_prim_application` 叶子识别 `unification.rs:1129-1176` | E4 | L13 多一层展开循环（fuel 护），L07 直接失败 |
| memo（仅孪生） | `conv.memo` 对已比 pair `bump_spine_iter/unify.rs:343-358,451` | 同有 `conv.memo` `bump_spine_iter/unify.rs:650-652`，**并多**位相等短路 `:647,655` | E1/E4 | 参考版两侧都无 memo；孪生层自带，故"孪生≠参考"不是 L13 特有 |

## 4 抽样深挖

### 4.1 struct_eq 去哪了：不是并入、不是替代，是**整模块没搬**

三份代码证据合起来是决定性的：

1. **L13 顶层根本没有这个 mod**：`L13_namespace/mod.rs` 全文 grep `struct_eq` 为 0 命中；
   而 `L07_sum_type/mod.rs:94 mod struct_eq;`、`L12_canonical/mod.rs:38 mod struct_eq;` 都在。
2. **调用点也没了**：L07/L12 的 Match/Match 臂都以 `struct_eq::val_eq(s1,s2) && env_eq(...)` 开头
   （`L07 unification.rs:1143-1144` / `L12 unification.rs:1253-1254`）；L13 该臂 `unification.rs:1250` 第一行直接是预算。
3. **作者自己写了删除理由**（L13 侧唯一提到它的地方）：
   `unification.rs:1251-1254` "…L13 无 σ 结构快路径，慢路径一律计数"；孪生侧 `bump_spine_iter.rs:171-173`
   "本层没有…`struct_eq`（无该分节；结构比较由 unify 的快路径承担）"。
   后半句对孪生**不准确**：孪生只有"位相等（同 arena 索引）"`bump_spine_iter/unify.rs:647` + `conv.memo`
   `:650`，那是**指针/记忆化**，不是结构比较——同一 decl 展开两份不同 Rc/loc 时二者都命不中。[未核实：是否有意省略]

至于 `struct_refine_probe.rs`：它是 `#[cfg(test)] mod`（`mod.rs:418-419`），文件头自称
"L13 中 `pattern_match.rs` 的 `compile_aux` 存在一个根本性缺陷…"（`struct_refine_probe.rs:1-11`），
内容全是 `assert_passes!`/`assert_expected_fail!` 宏 + `#[test]`（`:41-78,253`）。
**它是"GADT 索引精化缺陷"的探针测试套件，与"结构相等"只共享 struct 这个英文词**，
把它当 struct_eq 的替代品会把"机制被删"误读成"机制被换"。

### 4.2 Match/Match：快路径 vs 预算优先（E2，可观察）

```rust
// L07 src/L07_sum_type/unification.rs:1136-1163
(Val::Match(s1, env1, cases1, pending1), Val::Match(s2, env2, cases2, pending2)) => {
    if super::struct_eq::val_eq(s1, s2) && super::struct_eq::env_eq(env1, env2)
        && /* 分支体、pending 逐对 struct_eq */ { return Ok(()); }
    if !self.burn_match_cmp_budget() { self.note_unify_kind(Undecided); return Err(UnifyError); }
```
```rust
// L13 src/L13_namespace/unification.rs:1250-1262
(Val::Match(s1, env1, cases1), Val::Match(s2, env2, cases2)) => {
    if !self.burn_match_cmp_budget() { self.note_unify_kind(UnifyKind::Fuel); return Err(UnifyError::Basic); }
    self.unify(l, cxt, s1, s2, fuel)?;   // 之后逐分支 eval(simpl_decl) 再 unify
```
L07 注释说明了快路径存在的**唯一理由**："逐分支重求值会把分支体再展开一层卡住 match（fresh rigid 层级随深度递增，永不收敛）"
（`unification.rs:1137-1142`）。L13 删掉它以后，这个发散只由 64 次预算截断 —— 判定从
"结构相同 ⇒ 相等（Ok）"变成"重求值 64 次 ⇒ 判不出（Err+Fuel）"。**这不是纯度差异，是成功率差异**：
凡是"同一递归函数在方程两侧各展开一份相同卡住 match"的等式，L07 能证，L13 只能报不可信。
为什么仍判 E2 而非 E3：L13 的"结论"在保守方向上仍是安全的（失败≠误判相等），且它用 Call 快路径 `:1077` 覆盖了另一大类自比较。

### 4.3 契约表：6 个关键函数的签名对照

| 函数 | L07 | L13 | 差 |
|---|---|---|---|
| `unify` | `:894` `Val`/`spec` | `:1055` `&Rc<Val>`/`fuel` | E2 |
| `solve` | `:697` 4 行直转 | `:553` 56 行（Stuck 回退 + π 链 clamp + `occ:Some(m)`） | E2/E4 |
| `solve_with_pren` | `:702` `rhs:Val` | `:616` `rhs:&Rc<Val>`，`MetaEntry::Unsolved` 从 1 字段变 4 字段（`mod.rs:113` vs `:475`） | E1+E4 |
| `invert` | `:135`（0.88） | `:184` `pub` | E1 |
| `unify_no_arm` | `:1244` | `:1355` | **E1（注释几乎逐字同）** |
| `loose_string` | `:872` | 无 | E3 |
| `rename_arm` | `:552` | 无（`:396` 单函数迭代化） | E2 |

## 5 本角度评级

**评级：中。** 合一**算法内核**（prune/invert/intersect/flex_flex/unify_sp/unify_no_arm，0.6–0.9）确实是同一份代码；
但**入口契约**（签名/错误/产物/fuel）、**卡住 match 的整块机制**（struct_eq 快路径）与 **2026-11 加固的 3 项**都不同源，
"共有"只到函数级，不到机制级。

Top-3 差异：

1. **struct_eq 在 L13 整模块消失**（E3）：L07 `struct_eq.rs:36-53` + 调用 `unification.rs:1143-1154` ↔ L13 `mod.rs` 无、`unification.rs:1250-1261` 只剩预算。
2. **unify 契约重写**（E2）：L07 `unification.rs:894-902`（按值 Val + `spec` + 单元错误）↔ L13 `:1055`（`&Rc<Val>` + `fuel` + `UnifyError::{Basic,Stuck,Trait}` + `meta_contrains` 挂账）。
3. **加固项跨层不对等**（E3×2 / E2×1）：`TYPORT_UNIFY_FUEL` 覆盖（L07 `mod.rs:779-787` ↔ L13 `mod.rs:1468` 无）、`occurs_transitive`（L07 `mod.rs:452` ↔ L13 无）、Match 预算分档（L07 `Undecided` `unification.rs:1164` ↔ L13 `Fuel` `:1259`）。

## 6 给 Lead 的提醒

1. **MAP §2 需改**："L09 起删 struct_eq" 是旧文档的过期结论。事实是 L09–L12 都保留（`L12_canonical/mod.rs:38`、`unification.rs:1253-1264` 在用），**L13 才是删除点**；且 Lead 的 tsv/fn-matrix 都覆盖不到单边文件，这类"消失的模块"只能靠 mod 声明 + 调用点对查。
2. **回灌方向要反过来记**：literal equality 臂是 L13→L07（L07 自注 `unification.rs:1058-1061`，git `c6c0e892` 只改 L07/L08）。所以"L07 加固回灌 L13"这条叙述不能一概而论，**逐条都要查方向**。
3. **L13 内部有一处文档/代码不一致**：`mod.rs:1474` 说 match 预算耗尽记 `Undecided`，代码 `unification.rs:1259` 记 `Fuel`（并自注"L13 偏差（相对 L12）"）。这会改变覆盖探测的兜底档，若 07 号文按文档断言会出错。
4. **孪生 doc 不准确**：`bump_spine_iter.rs:172` 声称"结构比较由 unify 的快路径承担"，实际孪生只有位相等 + memo。孪生两侧都被封印（`7a68abc7`/`80f7cbc1`），这类表述漂移没有门禁会报。
5. 行为核验资源：`target/release/l13bench.exe`(2026-11-24) 与 `l07bench.exe`(2026-11-23) 都在，但 CLI 口径我没核实，未运行——若 07 号文需要，可直接用它们验 §4.2 的成功率差异。
