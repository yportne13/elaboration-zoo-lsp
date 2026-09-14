# L07 重构设计：从"事实表"到"显式替换"（dpm-nbe 对齐）

参照实现：`F:\projects\hermes\dpm-nbe`（KonjacSource/dpm-nbe，Haskell，
基于 elaboration-zoo + Kovács cctt 的 explicit substitutions & forcing，
特化合一来自 Norell 论文 / Cockx《Pattern Matching Without K》）。

## 1. 旧架构（pm_defs 事实表）与其结构性弱点

旧 L07 的精化机制（`Infer` 上的全局可变状态）：

- `pm_defs: Vec<(Lvl, Val)>`——特化方程的解，`pm_def(x)` **线性反序扫描**取最新；
- `pm_solvable: Vec<Lvl>`——"哪些 rigid 可解"的旁路通道，unify 里两个
  特判臂查询它；臂边界 / 探测边界用 `pm_mark` / `pm_restore` 截断回滚；
- `force(Rigid(x, []))` 查表展开——任何值里的 `Rigid(x)` 在**读点**都能
  看到 x 的解（全局查找表语义）。

弱点：

1. `pm_def` 是 O(n) 线性扫，位于 force 热路径；
2. "可解性"是全局可变通道（unify 与模式编译器耦合在 Infer 状态上），
   合一器本身不返回"解出了什么"——解散落在事实表里，驱动方无法组合；
3. 解与解之间没有组合结构：`n := plus m zero` 之后 `m := zero`，依赖的
   正确性完全压在"force 全局查表"这一条通道上；没有 dpm-nbe 的
   **替换组合**（剩余方程/活值置于解之下，读取时逐层推开）的显式纪律；
4. 回滚靠长度截断，快照点必须手工配对。

## 2. dpm-nbe 的三个核心机制与 L07 落点

| dpm-nbe | L07 v2 落点 |
|---|---|
| `VSub v σ` / `NSub n σ`：值携带显式替换；force（`frc`/`frcS`）把 σ 推进值结构，顺带触发 β / match / 归约 | `Val::VSub(Box<Val>, Rc<Sub>)`；`Infer::force` 的 VSub 臂（frcs） |
| `subst s2 s1`：替换组合，内层条目的值置于外层之下（读取时逐层推开）；解不改写既有值，只包裹 | `Sub::compose`（Rc 共享，O(|σ|)）；"后解的包外层" |
| `unify1` 返回 `USucc Lvl Sub | UAbs | UIDK`：特化解是**返回值**；驱动方把解应用到剩余方程（`subst ɑ vs`）与上下文（`subst sub ctx`） | `UnifyRes { Succ(Rc<Sub>), Absurd, Stuck }`；模式编译器线程 σ，消费点 wrap |

## 3. 数据结构

```rust
/// 模式特化的解：层级 → 值 的有限映射。仅由模式编译器构建。
pub(crate) struct Sub {
    map: FxHashMap<u32, Val>,   // 键 = 被解 rigid 的层级
}

/// 显式替换下的值。不变式：force 之后顶层不会是 VSub。
enum Val { ..., VSub(Box<Val>, Rc<Sub>) }
```

- `Sub::lookup(x)`：`map.get(x).cloned().unwrap_or(vvar(x))`；
- `Sub::extend(x, v)`（旧 `pm_solve` + push）：新单解叠加到 σ 上——
  **σ 的既有条目值包裹 `VSub(·, {x↦v})`，新键覆盖旧键**（右偏 union，
  对齐旧 `pm_def` 的 `rev().find` 取最新语义）；
- 浅 occurs 守卫（`val_mentions_lvl`）保留：解 `x := v` 要求 v 浅层
  结构不提及 x（闭包内部不探查，环由 force 的 fuel 兜底——与旧一致）。

## 4. force / frcs（对齐 dpm-nbe 的 frc / frcS）

```
force(v):
  VSub(v, σ)  => frcs(σ, v)                    -- 烧 1 fuel（防闭环）
  Rigid(x,[]) => Rigid(x,[])                   -- pm_defs 查表臂【删除】
  Flex/Match/Decl/Prim/Obj 臂                  -- 全部保持不变

frcs(σ, v):                                    -- 把 σ 推进 v 的结构
  VSub(v', σ') => frcs(compose(σ, σ'), v')     -- frcS sb (VSub v sb') = frcS (subst sb sb') v
  Rigid(x, sp) => v_app(force(σ.lookup(x)), wrap_sp(σ, sp) 按应用序)
                 -- dpm-nbe: napp (lookupSub sb v) (frcS sb sp)
                 -- lookup 命中 Lam ⇒ β；Flex/Rigid/Decl/Match ⇒ spine/pending
  Flex/Decl/Prim => force(同型值, wrap_sp(σ, sp))   -- 包裹后交回 force 走既有臂
  Obj            => force(Obj(frcs σ o, wrap_sp(σ, sp)))
  Lam/Pi       => 同型值，闭包 env 逐槽包 VSub(·, σ)（惰性，不重求值）
  Match(s, env, cases, pending)
               => force(Match(frcs σ s, env 逐槽包裹, cases, pending 包裹))
                 -- scrutinee 单独推进：重选分支需要解出的构造子值
  Sum/SumCase  => params/typ/datas 逐槽包裹
  U/Literal*   => 原样
```

### 槽位纪律（实现中发现的关键约束，评审与孪生版移植必读）

**σ 对 spine / 参数槽只"包裹"，绝不"推进物化"。** 旧 force 从不触碰
spine 槽（槽位引用是作用域事实）；若 frcs 把 σ 推进槽位（递归解析），
槽位会物化成精化后的构造子值，破坏后续 `solve` 的 invert
（`?m x y := Bool` 需要槽位仍是 bare rigid 才可逆）。复现：`def f(lhs
rhs carrier: Bool): Product[Bool][Bool] = match lhs { case true => match
rhs {...} }`——内层臂的 `?2` spine 槽被物化后误报 can't unify。
force_arg（invert 视角）同理，且必须**逐层解包** VSub（嵌套 match 的
上下文被外层臂与内层臂各 subst_cxt 一次，单层解包会漏）。

不变式与守护：

- `compose(σ_outer, σ_inner)`：内层先应用；键冲突**外层（新）覆盖**；
- v_app 的 VSub 臂：先 force 再分发（`eval(App)` 等不经 force 的调用点
  会把 VSub 头送进 v_app）；
- frcs 烧 fuel：浅 occurs 不探查闭包，闭包内的解环（`x := λ…x…`）在
  closure_apply 后的读点闭环——与旧设计的 fuel 兜底语义一致。

## 5. 特化合一器（unification.rs）

```rust
enum UnifyRes { Succ(Rc<Sub>), Absurd, Stuck }

unify_spec(l, t, u) -> UnifyRes:        -- 特化模式（对应 dpm-nbe unify1）
  force 两侧（VSub 推开后判定）
  (Rigid x, Rigid y) 同名       => Succ(空)
  (Rigid x, v) / (v, Rigid x)   => x ∈ 可解集 且 v 非 Flex 且 occurs 过
                                   => Succ({x ↦ v})；occurs 失败 => Absurd
                                   -- （对齐旧 pm_solve false => Err）
  (SumCase 同构造子)            => 逐字段 unify_spec（构造子注入性，
                                   对齐 dpm-nbe VSucc/VSucc → unify1 m n）
  (Sum 同名)                    => 逐参数 unify_spec（索引等式）
  (U,U)/(LitType,LitType)/(字面量同值) => Succ(空)
  其它                          => 常规 unify（meta 求解、η、宽松臂全保留）
                                   成功 => Succ(空)；失败 => Stuck
                                   -- Stuck 与 Absurd 都映射为旧"失败"路径
                                   --   （臂报错不可达），仅区分文档语义
```

`unify` 本体的两个 `pm_solvable_contains` 特判臂**删除**——可解性不再
是 Infer 全局通道，特化只走 `unify_spec`。

## 6. 模式编译器（pattern_match.rs）

`Compiler` 持有 `sub: Rc<Sub>` 与 `solvable: Vec<Lvl>`（本地字段，不再
挂在 Infer 上）。核心纪律——**所有"解前构建、解后消费"的值，消费点
用当前 σ 包裹**（`&wrap(sub, v)`，O(1) Rc）：

| 消费点 | wrap |
|---|---|
| unify_spec / unify 的方程两侧 | 入口 wrap |
| 构造子 telescope 下钻（`force(ty)`、closure_apply 的隐参 impl_vals） | wrap |
| 头部精化的读取（head_val、head_sum） | wrap |
| 期望类型（臂检查前） | wrap（旧的 quote→eval 重锚保持不变） |
| 分支体检查上下文 | `subst_cxt(cxt_arm, σ)`：env 槽与 src_names 类型逐槽包裹，lvl/locals/pruning/decl 不动（对齐 dpm-nbe `subst sub ctx`，lvl 不缩小——槽位布局 = 运行时布局，永不漂移） |

其余流程不变：

- 逐臂下钻、每绑定器一槽、bind/eval_aux/bind_count 三方同序同数；
- 头部精化（无条件）：`σ.extend(x, ctor_val)`，守卫同旧（bare rigid、
  可解、未精化即 `σ.lookup(x)` 仍是 vvar、occurs 过则跳过不阻断）；
- 覆盖探测：局部 σ（Rc clone）+ 局部 solvable + meta 快照回滚；
- 臂边界：`self.sub = snap`（O(1) Rc 赋值，替代 pm_mark/pm_restore）；
- 通配臂之后的臂跳过（首匹配语义）。

嵌套 match 自然消解：外层臂体检查期间编译嵌套 match，其入口上下文的
env 槽已带 VSub；方程两侧在 unify_spec 入口被 force 推开——已被外层
解出的变量不再以 bare rigid 出现，天然不可再解。`bind_slots` 解包 VSub
取 raw 层级作可解基线（多余的"已解"层级无害：方程里不会出现其 bare
形态）。

## 7. 行为保持承诺（验收口径）

1. 全部测试逐字节一致：39 内部 + l07_blackbox(48) + v2(51) + v3(85) +
   l07_fast_parity(57)——参考版 `run` 的可观测输出（含错误文案）不变；
2. 槽位布局不变（subst_cxt 不增删槽），运行时 eval_aux / Match 捕获
   env / splice 语义不动；
3. meta 求解器（invert/prune/rename/solve/intersect）、fuel、
   struct_eq 快路径、quote→eval 期望类型重锚全部保留；
4. 已知限制 #1（外层 meta 越界 rename）、#3（无 K 保护）、#4（probe
   与臂内方程判定主体）照旧——本次只动精化的**载体**，不动这些
   语义取舍。

## 9. 实现口径注记（首轮评审后补记，移植 L08–L13 前必读）

1. **特化合一的形状**：§5 的 `UnifyRes { Succ, Absurd, Stuck }` /
   `unify_spec` 独立入口是设计初稿；**实现**是 `unify(…,
   Option<&mut SpecSolve>)` 穿参 + `spec.acc` 就地累积（无独立返回
   类型）。语义等价、且不必触碰 elaboration-zoo meta 求解器的每个递归
   臂——后续层移植按**实现**形状走，不要按本稿 §5 的形状。
2. **`(LiteralIntro, LiteralIntro)` 臂不存在**：参考版 unify 无此臂，
   两字面量值合一走 `_ => Err`（孪生版头注释有同款记录）。§5 的
   "字面量同值 => Succ(空)"按实现删除。
3. **命名**：替换类型实名 `Subst`（`Sub` 已被 `std::ops::Sub` 占用）。
4. **σ 表示定稿（性能评审后）**：持久化单链（链头 = 最新），extend
   O(1) cons、lookup 沿链首个命中 + **条件包裹**（解值浅结构——含闭包
   env 槽——不引用任何已解层级时原样返回，零分配零 fuel；引用才包
   `VSub(·, σ)`）。初版 FxHashMap 写时整表重建 + 逐条深拷贝包裹是
   O(n³/6) 分配，深嵌套模式 2.5×@depth40 回归，已废弃。孪生移植直接
   采用链表 + 条件包裹终态。
5. **frcs 对"已解 rigid + 非空 spine"做解析应用**（v_app 带
   v_applicable 守卫）——旧 pm_defs 版在此卡住。这是相对旧版的**有意
   行为差异**（更完备，对齐 dpm-nbe napp），`tests.rs` 的
   `test_fn_typed_index_slot_applied_after_refine` 钉死，各层移植必须
   复刻。

## 10. 预期收益

1. force 热路径的 rigid 解查找 O(n) → O(1)（HashMap）；
2. 解是合一器的**返回值**，可解性不再经 Infer 全局可变通道——
   unify 与模式编译解耦，回滚 = Rc 指针赋值；
3. 替换组合显式化：多方程场景（add_assoc 族）的传播路径从
   "force 全局查表"单通道变为"σ 链逐层推开"，与 dpm-nbe/cctt 的
   理论构造同名同构，为 L08–L13 的同款重构提供模板。
