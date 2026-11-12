# L10 参考版为什么更快：机制归因与反向继承清单（2026-11-13）

> 问题（用户）：「L10 有一些更快的地方，详细分析原因」。
> 背景数据（同机、同文件、min-of-rounds `basic`，ms）：
> - 严格同文件 common（6 文件，L07 风格代码）：L07 66.6 / L08 68.4 / **L09-new 67.06** /
>   **L10 41.5**（L10 = 0.62× L07 = 0.62× L09-new）；
> - L09 自有的 Eq 证明阶梯（801 decls）：**L09-new 2.99 ms vs L10 1030–1075 ms
>   （L10 慢 345×）**；
> - 合成族（各层生成器，非逐字节同源）：natadd k=11 L10 1.82 vs L09-new 3.36；
>   match L10 ≈0.086 vs L09-new 0.103+；church/universe 基本持平。
>
> 结论先行：**L10 的「快」不是某个单点优化，而是参考引擎的世代差——L10 在
> `f72ece66` 被整体重写成 `Rc` 句柄风（`Env/Spine = List<Rc<Val>>`，
> `force/eval/quote/v_app/closure_apply/unify_catch` 全部 `&Rc`/`Rc` 进出），
> L11/L12 继承同族；L07/L08/L09 是「拥有式 Val」族。任务清单里那串单点 commit
> 绝大多数 L09-new 已逐字对位，或只落在孪生，或 L09 无宿主。**
> 因此：**不能把 L10 的「快」便宜地搬给 L09**（本质是表示层+全调用面重写）；
> **值得搬的是反向的 L09→L10**（L10 在全局引用/隐式 meta 密集负载上仍慢 6–345×，
> 那正是 L09 已治好而 L10 欠的债）。

## 0. 一句话答案

| 问题 | 答案 | 置信度 |
|---|---|---|
| L10 快在哪 | 参考引擎**整体 Rc 句柄化**（`f72ece66`）：值/项/环境/spine/meta 解都用 `Rc` 句柄按引用进出；具体收益集中在 ①**增长大值上的递归 match 抽取**：L07/L08/L09 的 `rc_take` 在共享时整棵深拷 O(值大小)（`add` 链每 stage ≈O(i²)），L10 的 `Rc<Val>` 抽取 O(1)；②**共享子项/δ 展开**：Rc 共享避免重复 quote/重建。L11/L12 同族 | 高 |
| 任务清单里的 U2/值级探测/逐臂下钻/显式替换/FxHashMap 等是原因吗 | **不是**：L09-new 全部已有（commit 逐字对位）；`fresh_meta` 快路径/`lams_from_ty`/`force-Obj` 早退/`solve_multi_trait worklist` 只落 L10 孪生；`18a8fd7b`（Def 去 eager nf）在 L09 无宿主（`DeclTm::Def` 是空结构） | 高（排除性） |
| L10 为什么在 Eq 阶梯/strchain/struct 反而慢 | L10 参考版**仍保留旧载体**：顶层定义压进 `Cxt`（env/lvl/locals/pruning 随 D 长），`fresh_meta` 的 `close_ty(cxt.locals)` 链长 O(D) ⇒ 每次 implicit meta O(D²)。这是 L10 的债，与「L10 快」无关；L09 已载体切换治好 | 高 |
| 要不要把 L10 的 Rc 重写搬给 L09 | **不要整机搬**：表示层+全调用面 1000+ 行、与 L09 的 partial-Rc 路线冲突；可做**低成本局部项**（`rc_take` 独占 move、`Span<String>` → `Rc`/`SmolStr`），预期只改善值增长类负载，需验收 | 中高 |

## 1. 机制在位矩阵（L10-ref vs L09-new-ref）

图例：✅ 两边都有；❌ L10 有 L09 无（=L10 独有）；⚠️ L09 有 L10 无（L09 独有）；➖ 与本对比无关（孪生/特性面）。

| # | 机制 | L10-ref 锚点 | L09-new 锚点 | 判定 |
|---|---|---|---|---|
| 1 | **值/项全 Rc 句柄**：`Env=List<Rc<Val>>`、`Spine=List<(Rc<Val>,Icit)>`、`eval(&Rc<Tm>)->Rc<Val>`、`force(&Rc<Val>)->Rc<Val>`、`quote(&Rc<Val>)->Rc<Tm>`、`MetaEntry::Solved(Rc<Val>,Rc<VTy>)` | `src/L10_typeclass/mod.rs:154-158,166-195,590,854,986`；整机 commit `f72ece66` | 按值同族：`Env=List<Val>`、`Spine=List<(Val,Icit)>`（`src/L09_mltt/mod.rs:170-171`）、`force(Val)->Val`、`eval(Tm)->Val`、`quote(Val)->Tm`；仅局部 Rc（`33a08764`/`85b9c87e`/`866f23e5`/`04e222e8`） | **❌ L10 独有（第一主因）** |
| 2 | `Tm` 全递归子项 `Rc`（Obj/App/AppPruning/Let 等） | `L10 mod.rs:57-79` | 仍 Box（Lam/Pi 已 Rc） | ❌ 同属世代差，单独收益有限 |
| 3 | 匹配编译器 U2「穷尽 match 跳过覆盖探测」 | `9b37c278` | **已有** `828df98d`（逐字对位） | ✅ 无差 |
| 4 | 值级可达性探测 `probe_accessible` | `e2560a47` | **已有** | ✅ 无差 |
| 5 | 逐臂下钻（决策树→逐臂） | `4e97743c` | **已有** `09b9ee8d` | ✅ 无差 |
| 6 | 显式替换 `Subst/VSub/frcs` | `ad412abd` | **已有** `ccfcb87c` | ✅ 无差 |
| 7 | `fresh_meta` 闭类型值中性化简 | `f2e28d50` **只改孪生**；参考版同旧形态 | 参考版同形态；且 L09-new 载体切换后 `locals` 短 ⇒ 更便宜 | ➖ 非 L10 优势 |
| 8 | `lams_from_ty` 死值 eval 消除 | `7c9d921e` 只孪生 | — | ➖ 无关 |
| 9 | Def 臂移除 eager nf+pretty | `18a8fd7b`（L10 自己的历史浪费） | L09 `DeclTm::Def` 空结构，本就零工作 | ✅ 无差 |
| 10 | FxHashMap 化 | `f32734c6`（含 trait 表） | **已有** `0bf8118f`/`866f23e5` | ✅ 无差（除 L09 无 trait 面） |
| 11 | force 的 Obj 臂 ptr_eq 早退 | `35a3734c` 只孪生；L10-ref Obj 臂仍重建 | L09-ref force 无 Obj 臂（`t => t`），本来就便宜 | ➖ 反向（L10 可捡的便宜） |
| 12 | `solve_multi_trait_ref` worklist | `3eb13bbc` 孪生+typeclass | L09 无 typeclass 面 | ➖ 无关 |
| 13 | universe / `check_universe` | 同血统 | 同血统；实测 universe k=10 = 2.4/2.4ms | ✅ 无差 |
| 14 | `struct_eq` 快路径 / `quote_deep`/`rename_deep` / 4 字段 `Val::Match`+pending | L10-ref **无**（3 字段 Match、无 struct_eq 引用） | **L09 独有**（11-11 回灌） | ⚠️ 反向收益项 |
| 15 | 顶层定义**不进** Cxt（载体切换） | L10 **仍进**（`define_global` env/lvl/locals/pruning） | **L09 独有**（`568c65c5`） | ⚠️ **反向大项**：L10 的 strchain/struct/Eq 慢 6–345× 病灶 |

## 2. 表示层细节：为什么这能解释观测倍率

| 点 | L10-ref | L09-new-ref | 后果 |
|---|---|---|---|
| `Env`/`Spine` | `List<Rc<Val>>` / `List<(Rc<Val>,Icit)>` | `List<Val>` / `List<(Val,Icit)>` | env 槽/实参按句柄传播；force/quote/unify 中间值共享，零枚举复制 |
| 求值入口 | 单入口 `eval(env,&Rc<Tm>)->Rc<Val>` | 双入口 `eval(env,Tm)->Val` + `eval_ref(&Tm)->Val` | L09 借用遍历避免深拷，但 λ/let/β 的结果值仍按枚举复制流出 |
| `force` | `&Rc<Val> -> Rc<Val>` | `Val -> Val`（浅拷贝枚举） | 转换检查每步常数 |
| `quote` | `&Rc<Val> -> Rc<Tm>` | `Val -> Tm`（深链走帧式） | 末值 quote/unify 内 quote |
| `v_app`/`closure_apply`/`unify_catch` | 全 `Rc<Val>` | 全 `Val` 按值 | β/应用热路径 |
| `MetaEntry::Solved` | `(Rc<Val>, Rc<VTy>)` | `(Val, VTy)` | meta 解链 |
| `Tm` 递归子项 | 全 `Rc` | Lam/Pi 是 Rc，其余 Box | L09 Def 臂 `t_tm.clone()` 深拷体项送 eval；L10 传 `&t_tm` 零克隆 |

**形态指纹**（代码审计 + 实测交叉，详见附录实验）：L10 赢的格子 = 「检查/转换阶段值流量大、
全局引用稀疏」（common ladder 0.62×、natadd ~0.54×、match 执行期、church 持平）；
L10 输的格子 = 「顶层声明多 ⇒ 旧载体/长 locals 发作」（strchain 6.1× 慢、struct 27× 慢、
Eq 阶梯 345× 慢）。这正是「表示层 Rc（赢）+ 旧载体（输）」两类机制叠加的指纹，
而不是某个编译器优化。

**跨层旁证**：`docs/bench-crosslayer-ref-2026-11-12.md` 的 common 排名
L10 38.6 → L12 42.0 → L11 47.8 → L13 57.8 → L07 62.3 → L08 63.8 → **L09(old) 106.2**
（L11/L12 的 `basic` 还含 parse+pretty+stdout 仍快过 L07）——L11/L12 参考版与 L10 是
同一 `Env=List<Rc<Val>>` 世代，L10 是该族最低层；世代边界正好落在 L09→L10 之间，
与 67→41.5 ms 的台阶重合。

### 2.4 同文件跨引擎实验：L10 的优势是**形状依赖**的，不是普遍的

实测（`target/perf09/l10exp/`，`realbench --only basic`，min-of-3；L10 引擎未改动）：

| 形状（同文件四引擎） | L09-new | L10 | L10/L09 | 读法 |
|---|---:|---:|---:|---|
| common ladder_l07_large（798 decls，大量 ctor + eval 应用 + 逐 stage 增长的 Nat 累积） | 64.0 ms | **38.1 ms** | **0.60×** | L10 唯一的大幅胜项（ladder small/medium/large 比值恒定 0.62–0.67×） |
| `unfold_probe` 16/18/20（`a_i = a_{i-1} (a_{i-1} x)` 指数 δ 展开/共享子项） | 7.4–121 ms | 3.3–54.8 ms | **0.38–0.45×** | 第二大胜项：Rc 句柄共享/避免重复 quote |
| plain_defs_1600（纯小 def） | 1.21 ms | 5.85 ms | 4.8× 慢 | L10 旧载体 O(D) 全局引用惩罚 |
| old_global_1600 / ctor_refs_1600 | 2.42 / 2.40 ms | 14.7 / 14.9 ms | 6.1× / 6.2× 慢 | 同上，且随引用距离放大（200→1600：1.03→6.09×） |
| proofs_400 / L09 Eq 阶梯 801 decls | 2.92 / 2.99 ms | 1959 / 1080 ms | **671× / 362× 慢** | L10 `fresh_meta` 的 `close_ty(locals)` 链长 O(D) ⇒ O(D²) |
| let_chain_800 / meta_implicit_200 / proj_chain_200 | 7.6 / 1.6 / 8.5 ms | 3435 / 523 / 1255 ms | 452× / 331× / 148× 慢 | 同上（长 locals / 隐式 meta / 投影） |
| match_dense_200（8 臂穷尽 match） | 3.99 ms | 10.19 ms | 2.55× 慢 | 匹配编译器已对齐（§1 #3–#5），差异来自载体常数 |

**结论**：L10 的「快」只在那类**每次声明的值与项流量大、而全局引用/隐式 meta 相对稀疏**
的形状上成立（common ladder、δ 展开共享）；一旦「声明数多且小」「全局引用远」「隐式 meta 多」
「locals 长」，L10 的旧载体惩罚（O(D)/O(D²)）就反超——这正是 L09-new 已治好而 L10 欠的债。
`L10` 还是唯一**随声明数超线性**的引擎（plain_defs 200→1600 步进 2.8–3.9×，≈1.7–2.0 次幂；
proofs 100→400 ≈2.9 次幂），L07/L08/L09-new 全部线性。

### 2.5 ladder 优势的判别实验：锁定「增长 Nat 值上的递归 match/add 链」

为进一步定位 common ladder 的 1.67×，用 ladder 的 5 个受控变体跑四引擎
（`target/perf09/l10exp/corpus2/`，同文件，basic min，ms）：

| 变体（每 stage 3 decl） | L07 | L09-new | L10 | L10/L07 |
|---|---:|---:|---:|---:|
| ladder_orig_798（原 common ladder） | 65.48 | 63.78 | **39.14** | **0.60×（快 1.67×）** |
| ladder_noadd_798（e + acc=eval，total=zero） | 3.58 | 3.71 | 9.47 | 2.65×（慢） |
| ladder_plain_798（每 stage 三个 zero def） | 0.52 | 0.58 | 1.48 | 2.83×（慢） |
| ladder_natchain_798（只有增长 Nat 链：add/succ，无 Expr/eval） | 22.60 | 22.62 | **14.21** | **0.63×（快 1.59×）** |
| ladder_succ_798（e/acc + total=succ total 构造器套链） | 3.71 | 4.00 | 9.74 | 2.63×（慢） |

差值分解：`add` 递归链组件 L10 快 **2.09×**，`e/acc` 声明组件 L10 慢 **2.65×**，净 1.67× 快。
**L10 的优势只属于「增长 Nat 值上的递归 `match`/`add` 链」**：删掉累积链、换成纯声明或
`succ` 套链后 L10 立刻反成 2.6–2.8× 慢；去掉 Expr/eval 只留 Nat 链仍复现 1.59× 快
（所以不是 Expr/ctor/match-on-Expr 的功劳）。

再做「值不增长」判别（表 F，`total{i} = add total{i-1} zero`，值恒为常数节点但每 stage
仍做递归遍历；以及 `add zero total{i-1}` 无遍历对照）：

| 变体 | L07 | L09-new | L10 | L10/L07 |
|---|---:|---:|---:|---:|
| `ladder_nogrow_798`（递归 add 遍历，值不增长） | 4.46 | 7.81 | 11.09 | **2.49× 更慢** |
| `ladder_nogrow_succ_798`（无遍历对照） | 3.94 | 4.19 | 10.46 | **2.66× 更慢** |
| 参照 orig（值每 stage 增长） | 65.48 | 63.78 | **39.14** | **0.60× 更快** |

**结论：优势只在值随 stage 增长时出现**（去增长后 L10 反而 2.5–2.7× 慢）。

**机制闭环（已交叉核实）**：L07/L08/L09 的 match 字段抽取走
`rc_take = Rc::try_unwrap(v).unwrap_or_else(|v| (*v).clone())`
（`L07 mod.rs:543`、`L08 mod.rs:553`、`L09 mod.rs:580`）——共享的大值
（`total{i-1}`，O(i) 大小的共享 Nat 值）在 `add` 的递归 match 里被逐层抽取时
**整棵深拷 O(值大小)**，每 stage 累计 ≈O(i²)，各层都付这笔钱。**L10 参考版
`rc_take` 出现 0 次**：`Rc<Val>` 句柄化后抽取直接传句柄 O(1)
（`src/L10_typeclass/**` grep 无 `rc_take`）。因此 `add` 链组件 L10 快 2.09×；
值不增长 → 深拷为零 → 优势消失。

**净值公式**：`ladder 上 L10 1.68× = 增长大值路径「O(1) 句柄抽取 vs rc_take 深拷」
的 2.09× 收益 − e/acc 声明组件 2.65× 的每声明 Rc 税`。ladder 由前者主导（净赢），
受控语料（plain/old_global/let/meta/proj）由后者主导（净输）——两套数据与
「L10 唯一独有差异 = 全 Rc 句柄化」自洽。δ-unfold/shared-subterm 的 0.38–0.45×
同源：Rc 句柄共享避免重复 quote/重建。

**可选的 L09 低成本改进（未做，供排期）**：L09 若要部分吃到这笔收益，可设法把
match 抽取的 `rc_take` 深拷路径降常——
①`Val::SumCase.datas: Rc<Vec<(.., Rc<Val>, ..)>>` 在 `Rc` 独占时（`try_unwrap` 成功）
直接 move 字段、避免深拷；
②把 `Val` 内频繁克隆的 `Span<String>` 换成 `Rc<Span<String>>`/`SmolStr`，让「每次 Val
复制一次 String 分配」降为 Rc 递增；
③彻底方案仍是 L10 的整机 `Rc<Val>`（成本高，不推荐）。
前两条属后续实验项（需 parity/黑盒/基准 A/B 验收）。




## 3. 被点名单点的逐条裁决（排除性证据）

- **U2 / 值级探测 / 逐臂下钻 / 显式替换 / FxHashMap**：L09-new 全部在位且与 L10 逐字对位
  （commit 对位见 §1 #3–#6、#10），不是差异来源。
- **`f2e28d50`（fresh_meta 闭类型值中性化简）**：只改 L10 孪生；参考版没有；且 L10-ref
  自身 `fresh_meta` 仍 `eval([], close_ty(locals, quote(...)))`，因旧载体 locals 长而 O(D²)
  ——这是 L10 的病灶，不是 L09 缺的优化。
- **`7c9d921e`（lams_from_ty）/`35a3734c`（force-Obj ptr_eq）/`3eb13bbc`（solve_multi_trait
  worklist）**：只落孪生（`bump_spine_iter*`），参考版无差。
- **`18a8fd7b`（Def 臂去 eager nf+pretty）**：修的是 L10 自己的历史浪费（church 199→6.8ms）；
  L09 的 `DeclTm::Def` 是空结构、Def 臂无 nf/pretty ⇒ 无差。
- **universe/meta**：`check_universe` 同血统、universe 负载实测持平。
- **bench 口径同工**：两边都是「逐 Decl `infer`（parse 在计时外）+ 末 def 值 `quote(Lvl(0))`
  + `tm_size_ref`」；realbench 计时前有 `nf_parity` gate（ref nf == twin nf），
  **不存在「少做工作」的假快**。L09 只是多一句 `meta_refuel()`（fuel 纪律）。

## 4. 反向：L10 欠的债（不该把 L10 当模板全抄）

| L09 已有、L10 缺 | L10 的代价 | 证据 |
|---|---|---|
| 顶层声明不进 Cxt（载体切换 `568c65c5`） | 全局引用 O(D) env 扫描 + `fresh_meta` O(D²) ⇒ strchain 6.1×、struct 27×、Eq 阶梯 345× 慢 | L09 自有 Eq 阶梯 2.99 ms vs L10 1030 ms |
| `close_meta_ty` 式 fresh_meta 快路径（L06 有 84× 先例） | 同上的 O(D²) 主项之一 | `src/L06_string/mod.rs:174-203` |
| `force` 无 Obj 重建（L09 `t => t`） | L10-ref 每步重建 Obj 值 | `L10 mod.rs:604-606` |
| `struct_eq` Match 快路径 + 4 字段 Match/pending | L10-ref `unify(Match,Match)` 走中性重求值、无 pending splice | L10-ref 3 字段 `Val::Match` |
| `quote/rename` 深链帧式化 | L10-ref quote/rename 递归（深值/大值风险） | `L10 mod.rs:986` |

## 5. 结论与后续（含 L10–L12 重定基排期）

1. **L10 快的本质是世代差**：`f72ece66` 的整体 Rc 句柄化。L09 只做了局部 Rc 回灌，
   要补齐等于重写表示层+全部调用面（1000+ 行），**不建议为常数收益反向移植**。
2. **L09 的量级问题已由载体切换解决**（common 67.06 ≈ L07/L08；Eq 阶梯 2.99ms）。
   L10 在 common 上仍比 L09-new 快（41.5 vs 67.06），差额可拆成「增长大值 `rc_take`
   深拷 → L10 O(1) 句柄」收益（2.09×）与「每声明 Rc 税」（2.65×）的净和；这是 L09
   未继承的「后世优化」，属于链上另一类不对称。若追求层间一致，正确方向仍是
   **把 L09 的改进顺链下传**。
3. **L09 可选的低成本增值（不阻塞主链）**：只把 match 抽取路径的 `rc_take` 深拷降常
   （独占 `Rc<Vec>` 时 move 字段；`Span<String>` → `Rc`/`SmolStr`），不需要整机
   `Rc<Val>` 重写，预期只改善值增长类负载（ladder/natadd）；需 parity/黑盒/基准验收。
4. **L10–L12 重定基排期**（已获用户批准，分阶段，不阻塞本轮 L09 提交）：
   - **P0（L10，先做，1 个 session）**：把 L09 现有成果继承到 L10 参考版：
     ①顶层声明移出 Cxt（载体切换，复用 `568c65c5` 的 `Tm::Global` 三态编码方案）；
     ②`close_meta_ty` fresh_meta 快路径；③`force`-Obj 早退；
     ④`struct_eq`/pending/深链帧式化（11-11 已回灌 L09 的机制，照搬对位）；
     ⑤重定义检查（**已在本轮 L10 落地**，参考版+孪生+lib 测试）；验收：`l10_fast_parity`
     全绿 + 跨层同文件基准（L10 的 strchain/struct/Eq 阶梯从 6–345× 落后回到 L09-old 量级）。
   - **P1（L11/L12，各 1 个 session）**：同剧本逐层继承（L11/L12 已是 Rc 世代，
     重点在载体切换 + 匹配/meta 路径的 L09 回灌项 + 各自真实语料验收）。
   - **P2（可选）**：若要让 L09 也吃到整机 Rc 世代红利，另立「L09 值/项全 Rc 化」实验
     分支（高成本高风控，需 parity/黑盒/validate 全量重跑；不建议与本链清理同轮做）。
5. **本轮 L10 的最小继承**：重定义检查（与 L09 同口径）已落地并配 lib 测试；
   其余 P0 项在下一轮按上述排期执行。

## 6. 证据与复现

| 证据 | 位置 |
|---|---|
| 代码机制审计（本报告 §1/§2 的来源） | `.deltawork/perf09/l10-faster-code.md` |
| 同文件四引擎形状实验 | `.deltawork/perf09/l10-faster-experiments.md`；`target/perf09/l10exp/` |
| L09/L10 跨层基线数字 | `docs/bench-crosslayer-ref-2026-11-12.md`；`target/perf09/baseline/ab_recheck2/ab_recheck.md` |
| L09 侧改造记录 | `docs/l09-carrier-switch-2026-11-12.md`、`docs/l09-perf-gap-2026-11-12.md` |
| 关键 commit | L10 `f72ece66`（Rc 句柄化）、`866f23e5`（全局名搬 Infer）、`9b37c278`/`4e97743c`/`ad412abd`/`f32734c6`；L09 `568c65c5`（载体切换）、`04e222e8`（G3+redefine） |
| 交叉文档 | `docs/bench-matrix-2026-09-20.md`（附录 A/C：L10 载荷 Rc 比 L09 轻 3×；L09/L10 残余 D^1.93 来自按值 Env）、`docs/optimal-design/L13-ref-perf-transfer-L07L10.md` |

> 方法：只读代码审计 + 同文件跨引擎计时；bench 前有 nf_parity gate。本轮同时把
> 「重定义检查」从 L09 继承到 L10（参考版+孪生+lib 测试），见 commit；其余 P0 继承项
> 按 §5 排期。
