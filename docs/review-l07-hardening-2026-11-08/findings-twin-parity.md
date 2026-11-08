# L07 孪生/parity + L08 迁移 review（reviewer-twin-parity）

> 对象：`master` HEAD `008f42ed`（基线 `641c52fe`），分支 `fix/l07-match-unify` 的 20 个 commit。
> 范围：孪生 `src/L07_sum_type/bump_spine_iter/`（`a70b5aaa`/`0f8acc52`/`1e1562e4`/`a1f1bf36`/`503c3187`/`3221433e` 的孪生侧）、`tests/l07_fast_parity.rs`、L08 迁移三 commit（`efbc9fa9`/`3c6b656b`/`d06d4c56`）与 `src/L08_product_type/**`、`tests/l08_*`。
> 方法：只读（`git show/diff`、read/grep）。**未运行 cargo**；所有「判定」结论均为代码路径推理 + 与 commit 内自述实测数字对照，实测复跑项集中列在末节交 Lead。
> 标注：已证实 = file:line/diff/可复核推理；疑似/未验证 = 路径已读到但反例未构造或未实测。

## 结论

1. **孪生侧两处「镜像」的遍历面是忠实的，但 `MATCH_CMP_BUDGET` 与参考版不是逐点同构**（参考版 = 递归**深度** 40、进出恢复、快路径前检查；孪生 = 单次 `unify_iter` 内 Match/Match 臂**命中总次数** 64、局部变量、不恢复、快路径后计数）。可构造**双向**判定漂移输入（§Q2），现有 parity 负载完全未覆盖。→ S2
2. **三个新 parity 用例只有 1 个在「修复前」真会红**：`parity_struct_eq_match_pending`（基线 ref=Ok / twin=Err，真差分钉 ✅）；`parity_occurs_transitive_chain` 只在「参考已修、孪生未修」的不对称窗口才红（基线两侧都接受、parity 绿）；`parity_stuck_match_equation_bounded` **不会红**——修复前两侧都 Err，只是慢（256 s + 26.3 s ≈ 4.7 分钟），且该用例**没有耗时断言**，`MATCH_CMP_BUDGET` 退化只会让 suite 变慢。→ S4
3. **L08 迁移只落在参考版**：`src/L08_product_type/bump_spine_iter/` 全目录无 `occurs_transitive` / `MATCH_CMP*`（只有 P9 的两处文案镜像）。c1 类输入在 L08 上已经是 **ref=Err / twin=Ok 的判定分裂**、c2 在孪生侧无预算；`l08_fast_parity` 93 绿**不能**证明 L08 双 oracle 一致。→ S2
4. **L08 的 P9 迁移不完整**：L07 的 P9 提交还顺带修了 `no named implicit arg {:?}` 的 Span Debug 泄漏（参考版 + 孪生各一处），L08 只迁了 pattern 文案两处，两处 Span 泄漏仍在（`src/L08_product_type/elaboration.rs:63`、`bump_spine_iter/machine.rs:812-815`）。→ S3
5. **PR/L07-RISKS 的「孪生只镜像 P2/P1/P9；P3/quote/pretty/Error span 未镜像，parity 只比 Ok 字节/Err 判定，故不受影响」不精确**：未镜像清单漏了 P5（跨 meta 环守卫→force/燃料剖面）与 P8（宽松合一收窄=接受集变更），二者是语义面；P3 的未镜像也不只是文案——参考版 `probe_accessible` 现在把 Undecided 当**可达**（要求覆盖），孪生仍是旧的「仅 fuel==0 算可达」，存在 Ok/Err 翻转路径；且 L08 的 parity oracle **比较 Err 正文**（`norm_err`），该括号句只对 L07 成立。→ S4
6. 其余：L07 孪生 `occurs_transitive`（V/SubstV 形态）与参考版**逐臂等价**（§Q1）；L08 的 P1/P2 参考版补丁与 L07 参考版**逐点同形**（值 40、2048 均一致）；L08 README 测试计数/已知偏差未随迁移更新（lib 49→60、parity 77→93），PR 的全库 987 也已陈旧（Lead 实测 990）。→ S4

## 逐项结论

### Q1 孪生 `occurs_transitive` 与参考版语义是否逐点一致 —— ✅（结构面一致，仅遍历序/预算序不同）

对照 `git show a474bf98`（参考 `src/L07_sum_type/mod.rs:335-385` + `unification.rs:972-1005`）与 `git show 0f8acc52`（孪生 `bump_spine_iter/subst.rs:304-420` + `unify.rs:514-525/540-548`）：

| 参考版臂 | 孪生标签臂 | 一致性 |
|---|---|---|
| `Rigid(y,sp)`：先 `y==target`，再 `lookup_hit(y)` 跟随，再扫 sp | tag 0 裸 rigid：`visit_rigid`（target→解值压栈）；tag 2 刚头：`visit_rigid` + `collect_args` 全部压栈 | ✅（顺序：参考先解后 args；孪生 LIFO 先 args 后解，仅序差） |
| `Flex/Decl/Prim(_,sp)`：只扫 spine | tag 2 非 rigid/Obj 头：只扫 args；裸 tag 5/7 忽略 | ✅（`XCell::VSub` 头不可达：`force.rs:683` 明示「VSub 值从不进 spine 的函数侧」，`vapp1` 的 VSub 头会 force 再分派） |
| `Obj(o,_,sp)`：o + sp | tag 7 `Obj` 压 `val`；tag 2 Obj 头压 `val` + args | ✅ |
| `Lam(_,_,cl)`：闭包 env | tag 1：`push_env`（binds + flat 区，与 `env_nth` 同槽序） | ✅ |
| `Pi(_,_,a,cl)`：dom + env | tag 4：dom + push_env | ✅ |
| `Sum`：params val+ty | tag 7 Sum：val+ty | ✅ |
| `SumCase`：typ + datas | typ + datas | ✅ |
| `Match`：scrutinee + env + pending | 同三件 | ✅ |
| `VSub(inner,s2)`：**切到内层 σ** 扫 inner | `XCell::VSub{val,sub:s2}` 压 `(val, s2)` | ✅ |
| `U/LiteralType/LiteralIntro`：false | tag 3/6 忽略；`XCell::Lit` 忽略 | ✅ |

其余核对点：
- **预算 2048 与参考版同值**（`mod.rs:336` vs `subst.rs:315`），耗尽都按「未出现」；都是**每次顶层调用**一份，都跟随 n 跳解链（`x:=a, a:=b, b:=succ x` 也会命中）。
- **调用条件逐点一致**：`acc` 非空 + `mentions_level(u, acc)` 前置筛选 + `occurs_transitive(u, target, acc)`；target 同为被解 rigid 的 level；`SubstV::lookup_hit` 的「引用已解层级则包 VSub」与参考 `Subst::lookup_hit` 同构，故 `go(VSub)` 的 σ 切换语义等价。
- **隐藏差异（不影响判定，只影响预算命中序）**：孪生用显式栈 + 每节点 `sub.has` 再 `lookup_hit`（双扫，微性能）；参考是左→右 DFS 短路、孪生是 LIFO，**共享 2048 预算下的「先扫到谁」不同** ⇒ 只可能在 >~2048 节点的病态值上出现检测差异（构造门槛远高于 c1，不列入发现表）。
- **误拒合法精化**：两版扫描面逐臂相同（VSub/闭包体/σ 映射值同样不扫），误报面一致；孪生 `mentions_level` 对 VSub 保守返回 true 只增大前置筛选命中率，不改变判定。✅
- 唯一未覆盖点与参考版相同：**pattern 头部精化写入点仍是浅 occurs**（见 F10，三实现共享，不是孪生分歧）。

### Q2 孪生 `MATCH_CMP_BUDGET` 与参考版常量/计数/重置 —— ❌ 不同构（可构造双向判定漂移）

事实对照：

| 维度 | 参考版 | 孪生版 |
|---|---|---|
| 常量 | `MATCH_CMP_DEPTH: u32 = 40`（`src/L07_sum_type/mod.rs:632`；L08 `mod.rs:547` 同值） | `MATCH_CMP_BUDGET: u32 = 64`（`bump_spine_iter/unify.rs:36`） |
| 维度 | **递归深度**（进入 Match/Match 臂 +1、退出恢复） | **单次 `unify_iter` 调用的臂命中总次数**（局部变量 `unify.rs:349-350`，只在 `:936-941` 递减，**从不恢复/重置**） |
| 位置 | 臂**入口**、结构快路径**之前**（`unification.rs:1121-1131`） | 结构快路径**之后**（`unify.rs:936-941`） |
| 作用域 | 每次 `unify` 调用内按路径计深度；兄弟比较各自从父深度重新计 | 一次方程（`unify_iter` 每次方程调用一次，`machine.rs:595`）内**全部兄弟比较累加** |

**判定漂移是双向的（构造思路，均未实测）**：

- **孪生 Err / 参考 Ok（兄弟多）**：一个 equation 内 >64 次**兄弟** Match/Match 命中、但嵌套只 1–2 层。
  构造：`def h(n, a1..a70)` 的 `match n` 有 2 臂（体都是 `zero`）；`def g(n)=match n{...}`；
  `def f(x,y, e: Eq[Nat] (h x (g a1)…(g a70)) (h y (g b1)…(g b70))) = match e { case refl(v) => v }`。
  第二个索引方程比较 `h x …` vs `h y …` → 外层 1 次命中 + 70 个 pending 对各自 `g ai` vs `g bi` 又是卡住 match ⇒ 孪生 71 > 64 在 65 个 pair 处返回 false；参考每个 pair 深度仅 2 ≤ 40 ⇒ Ok。
- **参考 Err / 孪生 Ok（深而合法）**：41–64 层**合法**嵌套卡住 match、最终收敛。
  构造：`def q(x1..x50)` 体为 50 层嵌套 `match xk { case zero => (下一层) case succ(n) => zero }`；由 `Eq[Nat] (q x1..x50) (q y1..y50)` 的索引方程触发比较。每层慢路径命中 +1，第 50 层收敛 ⇒ 孪生 50 ≤ 64 Ok；参考在深度 40 处 `Undecided` + Err（"无法判定"）。**这同时暴露参考版 40 的取值论证不成立**——「超过该深度说明双方分支体在递归上互不相同」对合法非递归嵌套 match 是假的（见 F4）。
- 另外：孪生把**快速路径命中的 Match/Match 不计入**（参考在快路径前检查，fast 命中在 depth=39→40 时会被判超限），也是一个方向上的细微差异。

结论：README §10「机制对齐/逐点同构」与 `L07-RISKS.md` §0.1 `P2′ ✅ 孪生版已跟修` 的表述掩盖了「代理维度不同、常量不同」这一事实；这不是纯粹的性能调节——它改变**接受集**（可构造输入），应作为已知偏差登记并加 parity 钉，或把两侧统一成同一维度（孪生给 `UItem` 带深度或按路径恢复计数）。

### Q3 parity 测试 oracle 设计 —— ⚠️ 差分 oracle 有效但能力边界大，且三新钉里两枚不守其名的性质

Harness（`tests/l07_fast_parity.rs:13-65`）：`run_basic` / `run_fast` 各在 256 MB 栈线程里跑，`assert_parity`：
- `Ok/Ok` → **输出字节逐字相等**（`assert_eq!(b,f)`）；
- `Err/Err` → **直接通过，不比任何内容**（不比文案、不比类别、不比 span、不比错误位置/条数）；
- 混合 → panic "判定不一致"。

**能发现**：接受集翻转（Ok vs Err）、`println` 输出差异（含输出顺序，因为比的是整串字节）、panic/abort（线程 join 会炸）。
**不能发现**（构造性反例）：
1. **两侧都错、错法相同**：基线（`641c52fe`）P1 的循环解在两个实现里都被接受；若当时把 c1 加进 parity，会 Ok/Ok 全绿——差分 oracle 对"共同 bug"零能力。P15（`0c73b65d`）能被 parity 抓到，只因孪生那侧恰好正确。
2. **Err/Err 但原因/分档/定位不同**：P3 已把参考版 c2 改成「无法判定」、孪生仍「分支不可达」——两边 Err，parity 绿，但语义（矛盾 vs 不知道）已分裂。任何"参考在第 A 个方程拒绝、孪生在 B 处拒绝"的输入同样全绿。
3. **内部多重解赋值顺序/σ 形态差异**（如 `x:=y` vs `y:=x`、`x:=a,a:=succ x` 的书写序）只要最终输出相同就不可见；只有它改变后续 fuel/判定时才间接可见。
4. **性能**：无任何超时/计时断言。`parity_stuck_match_equation_bounded` 的 docstring 写「任一侧丢失比较预算都会退化成分钟级」，但**退化后的判定仍是 Err ⇒ 用例仍绿**（只让 suite 慢 ~26 s / ~4.7 min）。孪生侧没有 lib 级计时钉（参考版有 `tests.rs:225-228` 的 `<30s`，孪生/`entry.rs` 无）；即 `MATCH_CMP_BUDGET` 目前**没有任何会红的回归钉**。
5. **文案/span**：L07 harness 明确不比（`l07_fast_parity.rs:5-6` 文档化偏差），故 P9/P10 的孪生差异不可见。

**稳定性**：三个新用例无计时断言 ⇒ 无因负载抖动而偶发红；c2 单测 ~0.3 s、256 MB 栈 ×2 线程/用例，在 64 位机上并行可接受；唯一"不稳定"是**若预算退化/死循环，cargo test 无 per-test timeout，suite 会挂住而不是失败**（建议 CI 加超时或给 parity 钉加计时断言）。

**三个新用例在修复前是否真会红**（详见 Q4）：`parity_stuck_match_equation_bounded` ❌ 不会红；`parity_occurs_transitive_chain` ⚠️ 只在不对称窗口红；`parity_struct_eq_match_pending` ✅ 会红。

### Q4 三个新 parity 测试的修复前行为（代码路径推理） —— ⚠️/❌

- **`parity_stuck_match_equation_bounded`（`1e1562e4`）— 不会红**。
  修复前：参考版无预算（256 197 ms，fuel 耗尽 → `Err`「分支不可达」），孪生无预算（26.3 s，fuel 耗尽 → `false` → `Err`）。`assert_parity` 见 Err/Err → 通过，约 4.7 分钟。用例只在「一侧判定翻转」时才红；两侧预算同时丢失/移除时全绿。PR 表 commit 地图第 6 行写的「修复前 run=Ok/fast=Err」与 `1e1562e4` 自己的提交信息（「断言两侧判定一致（**均为 Err**），实测新增用例 0.29 s」）矛盾——该括号描述属于 `0c73b65d` 的 `parity_struct_eq_match_pending`。→ F1/F2。
- **`parity_occurs_transitive_chain`（`a1f1bf36`）— 只在不对称窗口红**。
  基线（`a474bf98` 之前）两版都只有浅 occurs ⇒ 两侧都接受、Ok 输出也一致 ⇒ parity 绿（P1 在基线上是"共同 bug"，差分不可见）。只有在 `a474bf98..0f8acc52` 之间（参考已拒、孪生未修）才是 ref=Err / twin=Ok ⇒ 红。所以这枚钉实际守的是「孪生跟修不漂移」，**P1 本身的绝对钉只有 lib 侧 `test_occurs_check_transitive_chain`（且只跑参考版）**；若将来孪生的 `occurs_transitive` 过度拒绝，只有被既有 parity 正向负载碰到才会红（当前无该正向用例的镜像，属单向守卫）。
- **`parity_struct_eq_match_pending`（`0c73b65d`）— 会红 ✅**。
  基线：参考版 `struct_eq` 漏比 pending 值 ⇒ `refl f : Eq (Nat->Nat) f g` 被接受（Ok）；孪生一直正确 ⇒ Err。`assert_parity` 混合 → panic。这是三枚里唯一真正的"修复前差分钉"。

### Q5 L08 三项迁移忠实度 + L08 孪生现状 —— ⚠️（参考版忠实；孪生侧缺失；P9 不完整）

先回答结构问题：**`src/L08_product_type/bump_spine_iter/` 存在**（15 个文件，含 compiler/unify/subst/force/struct_eq…），`tests/l08_fast_parity.rs:22-48` 就是 `L08::run` ↔ `bump_spine_iter::run_fast` 的双 oracle。L08 的 oracle 比 L07 **更强**：`Err/Err` 要比较 `norm_err`（去掉 `@ start,end` 偏移）后的**错误正文**（`l08_fast_parity.rs:50-107`）。

- **P9 `Pattern::pretty`（`efbc9fa9`）**：L08 `parser/syntax.rs:29-53` 与 L07 `parser/syntax.rs` 的 `pretty` **逐字节同款**（`Con` 递归成 `name(sub, ...)`、`Any`→`_`、忽略 icit），两处文案点位（参考 `pattern_match.rs:159/208` + 孪生 `compiler.rs:163/222`）与 L07 同构 ⇒ 渲染一致 ✅。**但 P9 迁移不完整**：L07 的 `503c3187` 还修改了 `no named implicit arg {:?}` 的 Span Debug 泄漏（L07 `elaboration.rs:64` + 孪生 `machine.rs:828` 已改），L08 两引擎仍是 `{:?}`（`L08 elaboration.rs:63`、`bump_spine_iter/machine.rs:812-815`）⇒ 用户可见 `no named implicit arg foo @ 12,15` 形态，L07/L08 诊断口径分裂。→ F6
- **P2 `MATCH_CMP_DEPTH = 40`（`3c6b656b`）**：L08 与 **L07 参考版**同值同语义（`L08 mod.rs:547`；`unification.rs:858-919` 的 saved/restore 闭包形状与 L07 `1121-1185` 逐点同形，唯一差别是没有 `UnifyKind` 记录）⇒ 对 L07 **参考版**是忠实迁移。它与 L07 **孪生**的 64 次计数不同——不是 L08 的错，而是两个"孪生预算"设计本来就不同（L08 孪生干脆没有预算）。→ F3/F5
- **P1 `occurs_transitive`（`d06d4c56`）**：L08 `mod.rs:325-400` 与 L07 参考版 `occurs_transitive` **逐字节同款**（2048 预算、VSub 内层跟随、`mentions_any_solved` 前置筛选），两个 rigid 解臂的接入条件/位置也与 L07 `unification.rs:972-1005` 一致（`L08 unification.rs:690-735`）。L08 `Val` 变体集与 L07 相同（`L08 mod.rs:188-224`，14 个变体；积类型不新增值形态——README §9 明确"脱糖为 `{Name}.mk` 单构造子 enum"）⇒ 无漏臂/无语义变化 ✅。
- **遗漏/新变化**：
  1. **L08 孪生未镜像 P1/P2**（`bump_spine_iter/unify.rs:504-545` 仍只有 `val_mentions_lvl` 浅守卫，全目录 grep 无 `occurs_transitive`/`MATCH_CMP*`）⇒ c1：L08 参考 Err / 孪生仍 Ok（判定分裂）；c2：参考 639 ms Err / 孪生无预算（分钟级）。`l08_fast_parity` 未加这两类输入 ⇒ 93 绿不构成双 oracle 一致性证明。→ F5
  2. L08 `probe_accessible` 仍是旧口径（`pattern_match.rs:339-341`、孪生 `compiler.rs:355-357` `is_ok() || fuel_exhausted`）——因为 L08 没有迁 P3，所以**参考版与自己的孪生一致**，不构成新分歧；但这也意味着将来只迁 P3 参考版会立刻打红 L08 parity（它比正文）。
  3. P9 的 span Debug 泄漏（上文）。
  4. L08 `Error` 仍是单字段、无 span 填充（文档已声明）；P11 深值未迁（`quote`/`pretty` 共享代码，L08 的 pretty 是 L08 自己的模块副本，未做 1024 截断——不在本 PR 范围，但属于"L08 尚未迁移"清单）。

### Q6 「孪生只镜像 P2/P1/P9…parity 不受影响」是否精确 —— ❌ 不精确

逐条核：
1. **"只镜像了 P2/P1/P9"**：对 L07 孪生漏掉 P5、P8（清单外），也是仅参考版的**语义**修改：
   - P8 `999d617f`：`loose_string` 增加 `sp_is_empty`，未登记名 + 非空 spine 由「静默放行」变 `Undecided` Err（`unification.rs:1048-1058`；孪生仍是 `unify.rs:833-842` 的 `None => continue`）⇒ 接受集收窄，属语义面。
   - P5 `30547abf`：`force` 增 `meta_expanding` 跨 meta 环守卫（`mod.rs` 的 `Infer` 字段 + force 臂），环从「烧光 fuel」变「深度 2 确定性返回 Flex」；孪生 `force.rs:301/313` 仍靠 fuel 兜底 ⇒ **同一输入两侧剩余 fuel 不同**，后续判定/探针分档可能不同（燃料剖面差异）。
   - P10 解析 span（`26108306`）：文案逐字节不变，属纯诊断；孪生用旧 `parser`（commit 明说），无影响。
2. **"P3 三档…未镜像（parity 只比判定不比文案，故不受影响）"**：**P3 不止文案**。参考版 `probe_accessible` 改为「只有 `Absurd` 判不可达，`Undecided`/`Fuel` 按可达处理（保守要求覆盖）」（`pattern_match.rs:387-396`）；孪生探针仍是「`is_ok() || fuel==0`」（`bump_spine_iter/compiler.rs:349-357`）。当某构造子的特化方程以 **Undecided（且未耗尽 fuel）** 失败时：参考版要求该构造子被覆盖（未覆盖 ⇒ `"match 不完整"` Err），孪生判不可达（不要求覆盖 ⇒ 可能 Ok）。触发面是 `691623f8` 归为 Undecided 的 rename/invert/prune/solve 失败（README 自认 invert 失败可由用户程序触发）⇒ **存在 Ok/Err 翻转路径**，只是当前 parity 负载没有探到。（构造思路：索引族 match 的某个构造子方程需要 invert 一个 Decl 头 spine 而失败、且该构造子无臂覆盖。）
3. **"quote/pretty 未镜像"**：确实无影响——L07 孪生与参考版**共用** `super::pretty::pretty_tm`（`bump_spine_iter/entry.rs:10/290`、`machine.rs:14/635`），P11 的 1024 截断对两版同时生效；孪生 `quote_iter` 本就是迭代实现，参考版 `quote_deep` 只是补上参考版的短板 ⇒ 不改变任何字节。
4. **"Error span 未镜像"**：L07 parity 不比 Err 内容 ⇒ 无影响；但这是 L07 的 oracle 性质，**不能推广到 L08**：L08 harness 比较 `norm_err` 后的 Err 正文，未来把 P3/P10 式分档只迁参考版会直接打红 L08 parity。
5. **L08 侧**：PR §4 的这句话在 L07 上下文成立性已打折；§2.5/§7 对 L08 写「已完成 P9/P2/P1 迁移」必须限定为**参考版**，孪生镜像未做（PR §2.5 末尾确实提到"以及 L08 孪生版镜像"未迁，但 §4/§7.4 的乐观表述与 README §6/§10 的"逐点同构"容易让读者以为双引擎已同步）。

## 发现表

| ID | severity | 标题 | 证据 | 影响 | 建议 | 置信度 |
|---|---|---|---|---|---|---|
| F1 | S4 | `parity_stuck_match_equation_bounded` 无耗时断言，不守"bounded" | `tests/l07_fast_parity.rs:49-65,562-592`（Err/Err 直接通过）；参考版 lib 钉有 `dt<30s`（`src/L07_sum_type/tests.rs:225-228`），孪生无任何计时钉 | 孪生 `MATCH_CMP_BUDGET` 被移除/失效时判定仍 Err ⇒ parity 绿（26.3 s），预算退化静默；若退化为死循环，cargo test 无 per-test timeout 会挂住 | 给该 parity 用例加 `dt < 10s` 断言（reference+twin 各自计时），或给孪生加 lib 级 bounded 测试 | 已证实（代码） |
| F2 | S4 | PR commit 地图第 6 行描述错误 | `docs/compare-l07-vs-dpm/PR-l07-hardening.md:22`「修复前 run=Ok/fast=Err」vs `git show 1e1562e4` 提交信息「两侧判定一致（均为 Err）」；该括号描述实属 `0c73b65d` 的用例 | Review 会误以为 P2 有差分强度；掩盖"双侧预算同时丢失则无钉"的事实 | 改为「修复前两侧均 Err、仅慢；差分钉守的是判定不翻转；时序另由 lib 钉守」 | 已证实 |
| F3 | S2 | 孪生 `MATCH_CMP_BUDGET=64`（总次数）与参考 `MATCH_CMP_DEPTH=40`（递归深度）语义不等价 | `bump_spine_iter/unify.rs:36,349-350,936-941`（局部计数、不恢复、快路径后）vs `src/L07_sum_type/mod.rs:632` + `unification.rs:1121-1131,1184`（深度、进出恢复、快路径前） | **双向**判定漂移可构造：>64 兄弟卡住 match 对 → 孪生 Err/参考 Ok；41–64 层合法嵌套 → 参考 Err/孪生 Ok。parity 未覆盖；README §10「逐点同构」/`L07-RISKS` P2′ 未记录 | 二选一：统一维度（孪生按路径恢复计数/给 UItem 带深度）或登记为已知偏差 + 把两个构造方向的用例加入 parity（注意参考侧 40 会假拒，见 F4） | 高（路径/常量已核对；构造未实测） |
| F4 | S2 | 参考版 `MATCH_CMP_DEPTH=40` 会假拒 ≥41 层**合法**嵌套卡住 match | `mod.rs:632` 常量注释的论证「超过该深度说明双方分支体在递归上互不相同」不成立：合法非递归嵌套 match 可达任意深度；`unification.rs:1126-1129` 超限即 `Undecided`+Err | 参考版对病态但合法的深嵌套依赖匹配报「无法判定」而拒绝（接受集误收窄）；与孪生 64 次数窗口叠加产生判定分裂 | 实测 45–50 层嵌套 def 确认；如成立，考虑改「总工作项预算」或提高上限并注明这是启发式 | 中（推理强，未构造/未实测） |
| F5 | S2 | L08 迁移只落参考版：L08 孪生无 `occurs_transitive`、无 `MATCH_CMP*` | `src/L08_product_type/bump_spine_iter/unify.rs:504-545` 仅 `val_mentions_lvl` 浅守卫；全目录 grep 无 `occurs_transitive`/`MATCH_CMP_BUDGET`；`tests/l08_fast_parity.rs` 无 c1/c2 类输入；`d06d4c56` 自述"孪生版暂未镜像" | c1（两跳环）在 L08：参考 Err / 孪生 Ok（判定分裂已存在）；c2：参考 639 ms / 孪生无预算（分钟级）。`l08_fast_parity` 93 绿不能证明双 oracle 一致 | 按 L07 模板镜像两个 commit（P1 125 行 /保险 P2 同形 ~10 行），或在 L08 README §6/§10 明确登记为已知偏差并把 c1/c2 加进 L08 blackbox 基准（孪生计时单独看） | 高（代码核对；c1 孪生行为同构推理强，未实测） |
| F6 | S3 | L08 的 P9 迁移不完整：`no named implicit arg {:?}` 的 Span Debug 泄漏仍在两引擎 | `src/L08_product_type/elaboration.rs:63`、`bump_spine_iter/machine.rs:812-815`；L07 同码位已修（`elaboration.rs:64` / `machine.rs:828`；`503c3187` 提交信息"顺带修 no named implicit arg 的 Span Debug 泄漏"） | L08 诊断仍显示 `foo @ 12,15` 字节偏移，与 L07 诊断口径分裂；LSP 接入后用户可见 | 改 `format!("no named implicit arg {}", name.data)`（参考版）/ `{name}`（孪生），与 L07 同款 | 已证实（file:line） |
| F7 | S4 | 「未镜像清单 + parity 不受影响」不精确 | PR §4（`PR-l07-hardening.md:83-84`）、`L07-RISKS.md:46-53`「仅 P3 未跟修」；对照 `999d617f`（P8，接受集）、`30547abf`（P5，force/fuel）、`pattern_match.rs:387-396` vs `bump_spine_iter/compiler.rs:349-357`（P3 探针可达性）、`l08_fast_parity.rs:86-107`（L08 比 Err 正文） | 后续若沿用"parity 是唯二守卫"的判断，P3 探针分档/P8/P5 的语义漂移不会被发现；L08 parity 的更强断言未在文档中体现 | 改写为：「诊断类未镜像（quote/pretty/span/文案）不影响 L07 parity；语义类 P5/P8 与 P3 的探针分档未镜像，现有 parity 负载未覆盖；L08 parity 还比 Err 正文」；`L07-RISKS` §0.1 补 P5/P8/P10/P11 行的"孪生未镜像"标记 | 已证实 |
| F8 | S3 | 疑似：P8 未镜像留下验收分歧路径 | 参考 `unification.rs:1048-1058`+`loose_string`（未登记名+非空 spine ⇒ Undecided Err）vs 孪生 `unify.rs:833-842`（`None => continue` 放行） | 若存在可达的「未登记名 + 非空 spine 卡住 Decl/Prim 与 String 比较」输入：参考 Err / 孪生 Ok | 参考侧 P8 自称"当前源码路径不可触达（推断）"；建议把该不变量写成注释/测试，或把 loose 臂分档也镜像 | 低（分歧已证实，可达性未证实） |
| F9 | S4 | 文档漂移：L08 README 计数/已知偏差未更新；PR 全库 987 陈旧 | `src/L08_product_type/README.md:266-284`（lib 49 / parity 77 等）vs 实测/PR：lib 60 / parity 93；§6「已知偏差」`225-228` 未登记孪生未镜像 P1/P2 与 P9 缺口；PR §5「987 passed」vs Lead 实测 990 | 移植者按 README 得到错误面；"L08 已完成迁移"印象偏差 | 更新 L08 README §8 计数、§6 已知偏差（P1/P2 孪生未镜像、P9 span 泄漏、P3/P10/P11 未迁）；PR 计数改 990（或去掉精确数） | 已证实（计数由 Lead 实测 + 本次 grep 交叉） |
| F10 | S1（疑似） | P1 的传递 occurs 未覆盖 pattern 头部精化写入点，链式环仍可能被写入（三实现共享） | 参考 `pattern_match.rs:722-725`、孪生 `compiler.rs:669-671`、L08 `pattern_match.rs:662-665` 仍是 `val_mentions_lvl(&ctor_val, x)` 浅守卫；`val_mentions_lvl`（`mod.rs:1786-1827`）不跟随 σ，且 frcs 对 Sum 槽"只包裹不物化"（`force.rs:542-557`），故 ctor_val 内的 **VSub(bare y)** 不会展开出 `Rigid x`——若 `σ(y) ∋ x`，可写入 `x := ctor(…y…)` 形成链式循环 σ，与 c1 同类 | 若可构造：P1 类健全性残留（不是孪生分歧，参考/孪生/L08 同病）；`test_occurs_check_keeps_legit_refinement` 不覆盖 | 实测构造：嵌套依赖模式 + 外层索引方程先解 `y := …x…`、再对 x 做头部精化；若成立，把 `occurs_transitive` 也用于此写入点（前置 `mentions_level` 同样适用） | 低（路径已读通，反例未构造） |

## 未能验证 / 建议 Lead 实测

1. **F3 的两个构造输入**（最高优先，能直接判定"孪生预算是否只是近似"）：
   - A：70 个 pending 实参各为卡住 `g ai`/`g bi` 的 `h x …` vs `h y …` 索引方程（预期 ref=Ok / twin=Err）；
   - B：50 层合法嵌套卡住 match 的 `q x1..x50` vs `q y1..y50`（预期 ref=Err「无法判定」/ twin=Ok）。
   两枚都能同时验证 F4（参考版假拒）。
2. **F5 的 L08 c1 实测**：把 `parity_occurs_transitive_chain` 的源码喂给 `L08_product_type::run` 与 `L08_product_type::bump_spine_iter::run_fast`，确认 ref=Err / twin=Ok；c2 只测孪生计时（预期分钟级，加超时）。若成立，`l08_fast_parity` 的"93 绿"结论需在 PR 里限定。
3. **F6 可达性**：`def f {x : Nat} : Nat = x` + `f {y = zero}` 类输入确认 L08 报错文本含 `@ start,end`（L07 应不含）。
4. **F8 可达性**：构造「未登记名 + 非空 spine」类型值（候选路径：`simpl_decl` 表下的分支体重求值 + 类型层递归 def / `string_to_global_type` 产物被间接应用）；未构造成功则按"不可达（推断）"处理。
5. **F10 可达性**：嵌套依赖模式下 `head_sum` 参数经 σ 指向被精化变量、而 `val_mentions_lvl` 因 VSub 包裹看不穿的输入；失败即记为"未证实"。
6. **未覆盖的评审面（我未读全）**：`tests/l07_blackbox_v3.rs` 新增时间防护用例是否可覆盖孪生（它们只跑参考版）；`bench`/`twin_engine_bench` 是否受影响（P2 后 twins 的 c2 计时）；L07 README §10「已知偏差」是否应新增"预算代理维度不同"一条（我建议加）。
