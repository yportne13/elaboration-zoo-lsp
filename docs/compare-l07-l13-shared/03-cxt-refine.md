# 03 · 上下文 cxt.rs 与精化载体（σ vs update_cxt）

## 1 范围与方法

- 对比 `src/L07_sum_type/{cxt,elaboration,pattern_match,syntax}.rs` ⟷ `src/L13_namespace/` 同名文件，外加孪生侧
  `L07 bump_spine_iter/{subst,machine,compiler,force}.rs` ⟷ `L13 bump_spine_iter/machine.rs`。
- 只读代码 + `git log -S` + `git merge-base --is-ancestor`（HEAD `911628b3`，master）；未构建、未跑测试 ⇒ 行为结论标 [推断]。
- 保留率/函数体相似度取自 MAP.md §1 与 `docs/compare-l07-l13-shared/fn-matrix.tsv`（Lead 口径），本文只做性质判读。

## 2 模块对位表

| 文件 | L07 tok/行 | L13 tok/行 | 保留率(文字/归一) | 判读(继承/重写/扩张) |
|---|---:|---:|---|---|
| cxt.rs | 3,022 / 504 | 12,318 / 1,435 | **19% / 48%** | **重写**：`Cxt` 字段、名字表、精化载体全换；同角色骨架仍在（`names` 0.93、`new_binder` 0.54、`bind` 0.47） |
| elaboration.rs | 7,217 / 902 | 32,711 / 4,033 | 42% / 75% | **扩张为主 + 骨架继承**：归一保留 75%（`insert_until_name` 1.00、`check_ctor_wf` 0.72、`insert_t` 0.59、`insert_until_go` 0.48，而 `check` 0.18 / `infer_expr` 0.18 / `insert_go` 0.13），增量是 namespace/typeclass/hover/终止性（E4） |
| pattern_match.rs | 4,972 / 700 | 5,305 / 683 | 22% / 48% | **重写交接契约**：走查骨架同血统（`compile` 0.32），臂上下文交接从 σ 改成"返回精化 Cxt" |
| syntax.rs（Locals） | 229 / 35 | 720 / 120 | 38% / 60% | **继承 + 一侧扩张**：`Locals` 定义同构，L13 多 `update_by_cxt/update_at`（σ 侧不需要） |
| 孪生 subst.rs | 20,896 B | **无** | — | **E3 缺失**：L13 两侧都没有 σ 设施（`bump_spine_iter.rs:171-172` 自述） |
| 孪生 machine.rs 精化段 | `subst_cxt` | `update_cxt_impl+refresh` | — | **E2 机制漂移**，与参考版同向 |

**行内构成**（说明"变大"不等于"改掉"）：L13 cxt.rs 1,435 行里只有 ~490 行是与 L07 同角色的 `Cxt` 定义 + 两个 impl（324–339、964–1435，其中 1102–1163 的 nat/vconn 注册也是 L13 新增），
其余是搬进来的 builtin 归约体：nat primop 40–302、`check_comb_cycles` 438–706、global/文件族 707–942、
`HoverCxt` 303–322 —— 这些在 L07 住在 `mod.rs`（`Infer::prim_reduce`，mod.rs:1227）。

## 3 逐机制差异表（核心）

| 机制 | L07 实现(锚点) | L13 实现(锚点) | E 档 | 可观察后果 / 风险 |
|---|---|---|---|---|
| 精化载体本体 | σ 显式替换 `Rc<Subst>`：`Val::VSub`（mod.rs:336）、`wrap_sub`（mod.rs:574）、`frcs`（mod.rs:1092） | 改写 env 槽 + quote/eval 重锚：`update_cxt`（cxt.rs:1327）、`fresh_val`（cxt.rs:1319）、`refresh`（cxt.rs:1372） | **E2** | 同一 GADT 方程两条路径；L07 值层携带 σ、读点 `force` 推开；L13 就地换槽、读点必须重算 |
| 臂上下文交接 | `cxt_arm.subst_cxt(&self.sub)`（pattern_match.rs:227），返回 `Walk::Matched(detail, cxt)` 的 cxt 未精化 | `check_pm_final` 直接返回精化 Cxt（elaboration.rs:679、687；pattern_match.rs:583-591） | **E2** | L13 的 `Compiler::compile` 把精化"藏"在返回值里；L07 把它作为 `self.sub` 状态机显式快照/回滚（pattern_match.rs:206、280） |
| 特化方程求解 | `unify(..., Some(&mut SpecSolve))` 解入 `spec.acc`（pattern_match.rs:452-460、unification.rs:934） | `unify_pm` 六条臂全部 `cxt.update_cxt(...)`（elaboration.rs:795/813/815/826/843/855） | **E2** | 解的"方向/优先级"写在两套代码里：L13 多了 already-refined 递归与覆盖语义（elaboration.rs:817-827 自述 F5 约束丢失未修） |
| 探针期精化 | 探针把解累进 σ（`probe_accessible` 传 `&self.sub`，pattern_match.rs:181） | 探针精化**丢弃**（pattern_match.rs:222-223 自述"精化出的上下文弃掉即回滚"） | **E2** | L13 臂上下文里的索引解必须在 `check_pm` 期被**重算一次**；重算路径不同即可能"探针判可达、臂内解不出" |
| 嵌套位置覆盖 | 记账带 `sub/solvable/lvl` 快照（pattern_match.rs:92-97、213-220） | 记账带 `arm_cxt: Cxt` 快照（pattern_match.rs:603-608、85-89） | E1 等价改写 | 均满足"延迟探测在臂实例化下跑"，机制换了容器 |
| 变量读点类型 | 直接返回名字表里的类型，σ 在 `force` 读点展开（elaboration.rs:566-574） | `is_refined()` 时逐次 `quote+eval` 重算类型（elaboration.rs:3003-3018、cxt.rs:1403） | **E2** | L13 需要"补偿读点"，L07 零成本；L13 若有路径绕过该分支就会拿到旧 rigid 类型 |
| 名字表 | `NameState{map,trail}` + `name_mark` 惰性回滚，`Rc<RefCell<…>>`（cxt.rs:106-142、328-344） | `src_names: Rc<BiMap<名, Lvl, (Span,VTy)>>` + 每次 `Rc::make_mut` 克隆插入（cxt.rs:330、1209-1210、1276-1277） | **E2/E3** | L07 侧 O(1) 轨迹（2026-11-10 `d411debe`）；L13 仍是"整表深拷"，深作用域 O(n²)。语义等价 [推断] |
| 名字表反向索引 | 无（σ 不需要） | `get_by_key2_mut(&Lvl)`（cxt.rs:1391）供 `refresh` 同步类型 | **E4** | 反向索引是 update_cxt 的**结构后果**：载体选了 env 重写，就必须有 Lvl→名 的反查 |
| Locals 链 | `Rc` 链（syntax.rs:16-20），2026-11-10 `65d4512a` **借自 L13 参考版** | `Rc` 链 + `update_by_cxt/update_at`（syntax.rs:12-14、16-70） | E1（定义）+ E4（方法） | 两侧定义同构；L13 的更新方法 L07 用不上（`subst_cxt` 明说 lvl/locals/pruning 不动，cxt.rs:446-447） |
| Locals 精化写入 | 不写（cxt.rs:472-474 原样 clone） | 精化时把 `Bind` 改写成 `Define(…, Tm::U)`（syntax.rs:57-63） | **E2 风险** | 见 §4-C：`close_ty` 会把该 binder 封成 `Let x := U`，与 `subst_cxt` 的 `Pi` 不同 |
| decl 表 COW | `decl_insert_mut` 就地写 + `ver` 代数（cxt.rs:365-369、40） | `fake_bind`/`decl` 就地写（cxt.rs:1240、1303），无 ver | E1 | 两侧同款优化；L07 注释自承"这是 L13 参考版 `fake_bind`/`decl` 就地写模式在 L07 的对应物"（cxt.rs:361） |
| builtin 注册 | `add_builtin` 建 Π 链 + η 壳 + `PrimFunc` 转发 `prim_reduce(名)`（cxt.rs:278-311） | `add_builtin(infer, 名, Rc<Tm>, PrimFunc)` 直接挂函数指针（cxt.rs:1094-1100） | E1（同角色）+ 签名不同 | L07 多一层"按名再分发"；注册集合 L13 更大（nat/vconn/comb-cycle，E4） |
| 预算 | `UNIFY_FUEL=4096` + `TYPORT_UNIFY_FUEL` 环境覆盖（mod.rs:774-785）；`MATCH_CMP_BUDGET=64`（mod.rs:801） | 同常量、同每方程重置（mod.rs:1468/2319、pattern_match.rs:245），**无环境变量覆盖** | E1 / 小 E3 | 预算语义两侧一致；L07 的 11 月调参旋钮未回灌 |
| 声明入口 | `infer`/`infer_owned`（elaboration.rs:233、242），`check(&Cxt,Raw,Val)`（:81） | `infer`/`infer_in_place`/`infer_after_prefix{,_mut}`（:1368/1383/1401/1410），`check::<CANONICAL>`（:1042） | E1 + E4 | 骨架同名同序；L13 的 `const CANONICAL`、prefix 变体是新增层 |
| 错误面 | `compile` 返回 `Result<(), Error>`，非穷尽 = **error**（pattern_match.rs:139、186-188） | 返回 `Result<Vec<Warning>, Vec<Error>>`，非穷尽 = **Warning**（pattern_match.rs:488、527） | **E2** | 同一个不完整 match，两版诊断等级不同；跨版本文本断言不可平移 |
| 命名空间上下文 | 无 | `namespace/namespace_prefix/namespaces` 三字段（cxt.rs:332-334）+ `clone_without_src_names`（:1180） | E4 | 撑大 cxt.rs 的第二个来源；不属于"共有部分差异" |

## 4 抽样深挖

### A. 臂上下文交接：同一行注释位置，两种契约（E2）

L07 `pattern_match.rs:224-227`：

```rust
// 上下文先置于精化之下（dpm-nbe `subst sub ctx`）：env 槽
// 与名字表类型包 VSub，lvl/locals/pruning 不动——
let cxt_arm = cxt_arm.subst_cxt(&self.sub);
```

L13 `pattern_match.rs:589-591`：

```rust
// L13 的 check_pm_final 返回**精化后的 Cxt**（update_cxt 血统，
// 不是 σ）——直接当臂上下文用。
Ok((_, cxt)) => cxt,
```

两侧的 `cxt_arm` 是同一个语义对象（"解出本臂索引方程之后的上下文"），但**来源相反**：L07 是"把解施加到
未精化的 cxt 上"（值层包裹、布局不动，cxt.rs:445-479），L13 是"特化器边解边改 cxt 再把它还回来"。
锚点：L13 的 `compile` 里根本不存在 σ 变量，`self` 只有 `warnings/pats/ret_type/errors/nested_checks/pending_pos/cur_path`
（pattern_match.rs:56-79）——L07 同结构体里有 `sub: Rc<Subst>` 与 `solvable`（pattern_match.rs:46-58，`sub` 在 :53、`solvable` 在 :57）。
**为什么算 E2 而不是 E1**：L07 的 `self.solvable`（可解层级集）在 L13 没有对应物，其职责被"env 槽是否已是自身 rigid"
（elaboration.rs:806-812、836-838）取代 —— 判据从"层级集合"变成"槽值形态"，两者在嵌套/Λ 下钻场景不等价 [推断]。

### B. 名字表：轨迹回滚 vs 整表克隆（E2 机制 / E3 优化未回灌）

L07 `cxt.rs:99-104`（注释自述落地理由）：

```rust
/// 新实现改为"单张表 + 撤销轨迹 + 按 mark 惰性回退"：`bind`/`define` 只做
/// 一次哈希插入 + 追加一条 (名字, 旧值) 轨迹，O(1)
```

L13 `cxt.rs:1209-1210`：

```rust
let mut src_names = self.src_names.clone();
Rc::make_mut(&mut src_names).insert(x.data.clone(), (self.lvl, (x.to_span(), a)));
```

这正是 L07 注释里批判的"强计数恒为 2 ⇒ make_mut 深拷整表"那一版（cxt.rs:95-97）。**为什么算 E2/E3**：语义上
"每上下文看到创建时快照"两者都成立（fn-matrix：`bind` 0.47、`define` 0.46 —— 只在名字表这一段分叉，其余逐字同），
可观察差异只有深作用域成本；但它是**方向性证据**：L07 的 11 月加固（`d411debe` "name_map+trail for src_names"，
git blame cxt.rs:92-96 全为该提交）没有回灌 L13，而 L13 的 `Locals` Rc 化反倒回灌了 L07（`65d4512a` 提交信息
"Rc-backed Locals chain (borrowed from L13 reference)"）。**一脉相承是双向的、且不对称**。

### C. `update_by_cxt` 的 `Tm::U` 占位（E2 风险，[未核实]）

L13 `syntax.rs:53-63`：`Bind` 槽被精化后改写成 `Define`，但项位置写的是

```rust
//infer.quote(decl, lvl, v),
infer.quote(decl, lvl, &Val::U(0).into()),
```

被注释掉的 `v` 才是精化值，实际写入的是"宇宙 U"。该 `Locals` 会流进 `close_ty`（syntax.rs:72-79）→
`fresh_meta`（mod.rs:2719-2734），即 **精化上下文里新建的 meta 闭类型**：L13 会把它封成 `Tm::Let(x,ty,U,b)`
（eval 后 x:=U），L07 因为 `subst_cxt` 不动 locals 仍封成 `Tm::Pi`（syntax.rs:24-34）。
**为什么列 E2 而不下结论**：触发需要"臂上下文已 update_prune 精化 + 体内新建隐式 meta"，我没有构建权限，
无法确认是否有测试覆盖，也无法确认 `pruning` 长度与少一个 Π 的望远镜是否仍对齐 ⇒ 记为可复核的风险点，
建议 Lead 交给 07-evidence 用现成二进制或测试点名验证。该行 git blame 指向 `f1392ad4`（2026-05-11 建层），
即**不是 11 月加固引入的，是 L13 的五月祖传代码**。

## 5 本角度评级

**断（就"精化载体"这一层）；总评：共有骨架"中"，语义核心"断"。**

一句话理由：`update_cxt` 是仓库里**只有 L13 目录有**的机制（参考版 cxt.rs:1327 + 孪生 machine.rs:2766，其余 12 层全无），
L07–L12 六层全部是 `subst_cxt`（各层 cxt.rs:453 同行号）——这不是"L13 多走了一步"，而是 L07 侧 2026-09-15
（`ad08c633`）单方面换掉载体、L13 没跟；σ 那条线（连同孪生）在 L07 侧此后还有 8 次 cxt.rs 提交（09-19 至 11-11），L13 侧一次都没接。

Top-3 差异：

1. **E2** 臂上下文交接契约：`cxt_arm.subst_cxt(&self.sub)`（L07 pattern_match.rs:227）vs `check_pm_final` 返回精化 Cxt（L13 pattern_match.rs:591 / elaboration.rs:679-688）。
2. **E2** 精化载体：`Val::VSub`+`frcs`（L07 mod.rs:336/1092、cxt.rs:453）vs `update_cxt`+`refresh`（L13 cxt.rs:1327/1372）；孪生同向（L07 subst.rs vs L13 machine.rs:2780）。
3. **E3/E2** 名字表：`NameState` trail 回滚（L07 cxt.rs:106-142）vs `Rc<BiMap>` 克隆插入（L13 cxt.rs:330、1209）——语义应等价，性能与后续演进已分叉。

## 6 给 Lead 的提醒（超出本角度，但会误导结论）

1. **σ 曾经移植进 L13 孪生并留在侧枝**：`8c53542f` + `a2989b81`（2026-09-21，"孪生精化移植显式替换 σ"）
   只在分支 `perf/l13-twin-sigma`，`git merge-base --is-ancestor` 对 HEAD 为 **false**。
   ⇒ "载体统一"被尝试过一次并被弃用，不是没人想到。若 Lead 要谈"为什么没统一"，这是唯一的第一手证据。
   （注：`rebase/l13-on-l12`(2026-11-18)、`review/l13-shared-perfect`(2026-10-01) 两个分支上的 L13 cxt.rs 仍是
   `update_cxt=1 / subst_cxt=0`，即重定基也没换载体。）
2. **`check_pm_final` 吞咽最后一次特化方程失败**：`self.unify_pm(&cxt, &ori, &tmv, t_span).unwrap_or(cxt)`
   （L13 elaboration.rs:687）——失败时静默保留未精化 cxt，臂仍被当作可达去检查体。L07 侧同位置是
   `Walk::Unreachable` 报错（pattern_match.rs:247-256）。属 04-match 角度，但会影响"两版对同一程序给不同诊断"的证据采集。
3. **非穷尽 match 的等级差**：L07 报 error（pattern_match.rs:186-188），L13 报 `Warning::Unmatched`（pattern_match.rs:527-531）。
   07-evidence 若做跨版本输出比对，必须按"error vs warning 分流"归一，否则会误判为回归。
4. `elaboration.rs` 的 L13 增量不全是新功能：`check_pm/infer_expr_pm/unify_pm/check_pm_final` 是从 L07 的
   `pattern_match.rs` **搬家**过去的（L07 全在 pattern_match.rs，L13 在 elaboration.rs:679-942），
   比对时按"文件"看会把这一大块算成 L13 新增，按"函数"看（fn-matrix）才不会误判。
