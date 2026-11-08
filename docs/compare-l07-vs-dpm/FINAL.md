# L07 ↔ dpm-nbe-rs 实现差异总报告

> 对比对象
> - **L07**：`F:\projects\hermes\elaboration-zoo-lsp`，层目录 `src/L07_sum_type/`（HEAD `641c52fe`）。和类型 + 依赖模式匹配的教学层，骨架源自 András Kovács 的 elaboration-zoo 07（完整元变量求解器）。
> - **dpm**：`F:\projects\Rust\dpm-nbe-rs`（HEAD `db226de`）。U/Nat/Id/Π 的极简演算，λ 上带 `refl`/`(!)` 模式，是 `KonjacSource/dpm-nbe`（Haskell）的**逐行移植**，核心零依赖。
> ⚠ **2026-10-30 实测补正**：三侧（L07 / dpm-nbe-rs / Haskell 原版）已跑同一组程序，修正了本报告两条【推断】（自指索引、卡住索引方程），详见 [`EXPERIMENTS.md`](EXPERIMENTS.md)。后文与之冲突处以实测为准。
>
> - 分维度详证：[`01-subst-force.md`](01-subst-force.md)（替换与 force）、[`02-pattern-unify.md`](02-pattern-unify.md)（模式编译与特化合一）、[`03-value-quote.md`](03-value-quote.md)（值/quote/conv）、[`04-surface-meta.md`](04-surface-meta.md)（语言表面/元变量/工程面）。
> 文中 `文件:行号` 以各自仓库根为基准；`L07/` 简写 `src/L07_sum_type/`，`dpm/` 简写 `F:\projects\Rust\dpm-nbe-rs/src/`。
> 证据分级：【实测】= 本轮跑过二进制/测试；【读码】= 读代码确认；【推断】= 由代码推出未执行。

---

## 0. TL;DR（八条）

1. **两者是"堂兄弟"而非"两代"**：L07 用 elaboration-zoo 的骨架（Tensor/Pi/Sum/元变量），把 dpm-nbe 的**显式替换 + forcing** 当作精化载体搬了进来（`docs/l07-dpm-refactor-design.md`）；dpm-nbe-rs 则把同一套 Haskell 机制逐行移植到 Rust。所以"替换/force"这一层已高度同构，差异集中在**另外四层**。
2. **机械骨架七条重合**：NbE + 闭包共享 + 显式替换延迟值 + 读点 force 展开 + 特化解即替换（不改写上下文）+ 上下文 lvl 不缩 + 一阶合一/构造子注入。
3. **真正的分水岭是元变量**：L07 `unification.rs` 1141 行（其中 ≈674 行纯 meta：invert/prune/rename/solve/intersect/flex-flex），dpm 整个合一器约 105 行、9 个情形——**≈10.9×**。dpm 能这么小，是因为它的语言里**没有可解未知**（λ 不可推断、`refl` 不可推断、参数全显式、无洞）。
4. **L07 每一条"额外纪律"都能追溯到 meta**：槽位只包裹不物化（为了 `invert` 可逆，L07/`mod.rs:721-784`）、条件包裹（`mod.rs:260-273`）、共享 fuel 池（`mod.rs:479`）、σ 的可见性边界（decl 表/meta 解不扫 σ，L07/README §1.3）。dpm 没有 meta，所以这些约束在它那里**既不需要也不存在**——这不是 dpm 偷懒，是架构差异。
5. **判定的"档位"不同**：dpm 三值 `Succ{Abs}{Idk}`（`dpm/elab.rs:26-33`）能区分"矛盾（可写 `(!)`）"与"不知道"；L07 二值 `Result<(), UnifyError>`，把 fuel 耗尽也折叠成失败，只能靠文案尾注 `(fuel exhausted)` 区分（L07/`pattern_match.rs:382-392`）。**L07 可能把"算不完"误判成"不相容"（假 absurd，README §7.2 自认）**，dpm 不会。实测代价比文档描述严重：一个只有 4 个 `def` 的卡住索引程序，L07 **256 s** 后报"分支不可达"，Haskell 原版与 dpm 都在 ~10 ms 内报 `not sure`（EXPERIMENTS F2）。
6. **接受集最大单点差异是 occurs check**：dpm 完全没有（`NOTES.md:283-285`，`elab.rs:82-93` 直接 `insert_sub`），【实测】接受自指解 `x := suc x` 并输出 `λ x refl . zero`；L07 有两处**不同强度**的浅 occurs（方程侧硬 Err → 臂不可达 `unification.rs:908-910`；头精化侧软跳过 `pattern_match.rs:662-665`），但【实测】**不传递**：经模式槽中转过两跳的环仍被接受，把索引顺序对调才拒绝（EXPERIMENTS F1）。
7. **卡住项表示相反**：L07 把 `match` 做成一等值 `Val::Match`（捕获 env + pending，force 时重选分支，`mod.rs:609-628`）；dpm 把卡住的模式匹配折进 `Ne::Lam` + spine（`stuck_lam`，`eval.rs:267-269`），靠 `napp` 重跑 `match_`。这条差异向后传导出 quote（dpm 必须"饱和欠应用 λ"=偏离 3；L07 必须"分支体在简化 decl 表下重求值"）、打印、深值安全等全部差异。
8. **语言表面是"范围差"不是"进度差"**：dpm 无 enum/GADT/隐式参数/洞/投影/递归定义，全部有 `NOTES.md:3-7,281-313` 的"faithful 移植 + 刻意最小化"依据，**没有一处 TODO 承诺补上**。可比性只在"依赖模式匹配精化"这一件事上；把它当"实现质量差距"会误判整份结论。

---

## 1. 两项目定位

| 维度 | L07 | dpm-nbe-rs |
|---|---|---|
| 目标 | 教学层：和类型 + 依赖模式匹配 + 全套元变量/LSP 底座 | 理论最小核：`refl` 精化索引时显式替换/forcing 的必要性 |
| 语言 | `def`/`enum`（隐式方括号参数、GADT 返回类型、索引、投影、洞、限定构造子、15 个 builtin） | 单表达式：`U`/`Π`/`λ p* . t`/`let`/`Id`/`Nat`，模式只有 var/`refl`/`(!)` |
| 骨架 | elaboration-zoo 07（meta、pruning、invert、rename） | dpm-nbe(Haskell) 逐行移植（无 meta） |
| 精化载体 | 显式替换 `Subst`（2026-09 重构，蓝本 = dpm-nbe） | 显式替换 `Sub`（层序列，Rust 化修复） |
| 验收 | 自家双实现 parity（`run` vs `run_fast` 逐字节 Ok / 判定一致 Err） | 与 Haskell 原版 golden 逐字节 + 13 条 `_DEVIATION` 台账 |
| IDE | 本层未接入项目 LSP（仅 `src/lib.rs:52` 导出） | 独立 LSP crate + wasm web IDE |

**共同祖源一句话**：L07 的 `force/frcs + Val::VSub` 与 dpm 的 `frc/frcS + Val::Sub` 是同一个构造（Kovács cctt 的 explicit substitutions & forcing），只是 L07 把它嫁接到带 meta 的 elaboration-zoo 骨架上，因此必须额外维护"槽位可逆性"。

---

## 2. 规模（实测口径）

| 组件 | L07 | 备注 |
|---|---|---|
| `mod.rs`（Val/Subst/force/eval/quote/meta 表/run） | 1478 | 含 DEMO、bench 钩子 |
| `unification.rs` | 1141 | 实现部分 1-1117，测试 1118+ |
| `pattern_match.rs` | 642 | Compiler + 覆盖探测 + eval_aux |
| `elaboration.rs` | 701 | check/infer/def/enum |
| `cxt.rs` / `struct_eq.rs` / `pretty.rs` / `syntax.rs` | 305 / 342 / 266 / 19 | |
| `parser/`（lex+mod+syntax） | 843 | |
| **参考版核心小计（除 tests.rs）** | **≈4987（+parser 843）** | |
| `tests.rs` | 1406 | 48 个 `#[test]` |
| 性能孪生 `bump_spine_iter/` | **7611** | 另一套 arena + 迭代内核实现 |
| 黑盒/parity 测试 | 49 + 53 + 47 + 23 个 `#[test]` | `tests/l07_blackbox{,_v2,_v3}.rs`、`l07_fast_parity.rs` |
| **dpm `src/` 全部** | **3408** | 含内联单测、`lib.rs`(514)、`main.rs`(81) |
| 其中 `elab.rs`（含合一 `elab.rs:24-124`） | 501（合一 ≈105） | |
| `eval.rs` / `parse.rs` / `syntax.rs` / `context.rs` / `subst.rs` / `pretty.rs` | 676 / 698 / 406 / 224 / 85 / 223 | |
| dpm LSP crate `lsp/src/` | 1725 | 独立 crate |

**不要直接比 4987 vs 3408**：L07 侧不含 parser，dpm 侧含 parser/pretty/main 与内联单测。可比的三个切片：
- **合一层**：1141 vs ≈105 → **≈10.9×**（差异就是 meta）；
- **模式编译**：642 vs `check_pm` ≈99 行 → **≈6.5×**（但语义域不同：通用 enum 索引 vs 内建 `Id` 一条方程）；
- **求值/force/quote**：L07 `mod.rs` 中相关段 + `struct_eq`/pretty ≈ 2100 行 vs dpm `eval.rs`+pretty ≈899 行 → ≈2.3×（差异是 Sum/SumCase/Match 三个值构造与 simpl_decl 重求值）。

【数据口径】行数为 2026-10-30 `Get-Content | Measure-Object -Line` 实测；`04-surface-meta.md` 表内的 6011/2433 与 674 行 meta 明细是**按 `#[cfg(test)]` 前区间估算**，与实测总行数有 ±10% 出入，本报告一律以实测值为准，674 仅作量级参考。

---

## 3. 同源骨架（七条重合）

| # | 机制 | L07 | dpm |
|---|---|---|---|
| 1 | NbE：值域独立于语法，闭包 = (env, Tm) 共享 | `Val`/`Closure`（`mod.rs:175-220`） | `Val`/`Ne`/`Closure`（`syntax.rs:213-310,346-358`） |
| 2 | 显式替换是值的一种，force 消去 | `Val::VSub`（`mod.rs:219`） | `Val::Sub`/`Ne::Sub`（`syntax.rs:298,349`） |
| 3 | 读点展开：`force(vsub)` → 把 σ 推进结构 | `frcs`（`mod.rs:678-787`） | `frc_s`/`frc_ne_s`（`eval.rs:109-161`） |
| 4 | 特化解 = 替换；**不改写上下文** | `Subst` + `subst_cxt`（`cxt.rs:333-352`） | `Sub` + `subst_ctx`（`context.rs:174-186`） |
| 5 | 解后**层级不缩**（槽位布局 = 运行时布局） | `lvl` 不动（`cxt.rs:333-352`） | `lvl` 不动（`context.rs:176` 注释明写） |
| 6 | 一阶合一 + 构造子注入 | `unify` Sum/SumCase 臂（`unification.rs:983-1031`） | `unify1` Refl/Zero/Succ 臂（`elab.rs:96-106`） |
| 7 | with-K、无 K 保护、教学取舍 | README §7.3 | `NOTES.md` 首段 |

> **对任务简报的更正（由 02 维度查证）**：不要写"dpm 在 `subst_ctx` 里把 lvl 缩小"。`g.pred()` 只是 `insert_sub` 造出的 `Sub` 的 dom（`subst.rs:45-49`）与 `unify_s` 内部穿参的层级，`check_pm` 直接丢弃 `Succ.lvl`（`elab.rs:222`），`ctx.lvl` 全程不变。两侧都无 de Bruijn 错位。

---

## 4. 五组结构性差异

### 4.1 替换与 force：纪律差，不是机制差

- **数据结构**：L07 = 无 dom/cod 的持久化单链 `SubEntry{lvl,val,next}`（`mod.rs:236-361`），写 O(1) cons、读沿链扫描、**条件包裹**（解值不引用已解层级则原样返回，零分配零 fuel，`mod.rs:260-273`）；dpm = 带 dom/cod 的**层序列** `Sub{dom,cod,layers}`（`syntax.rs:241-258`），`subst_sub` 只拼层列表（O(1)），lookup 时"最旧命中层胜 + 新层逐个 subst 它的值"（`subst.rs:26-37`）。
  → 这是同一个 laziness 问题（Haskell 的 `IM.map` 惰性）的两种 Rust 解：dpm 用**层拼接**消除 2^n、L07 用**条件包裹**消除 O(n³/6) 分配（design doc §9.4）。两者在真实路径上等价。
- **frcs 的推进入口**：L07 入口不烧 fuel、逐臂包裹，**spine/Sum/SumCase 槽只包裹不物化**（`mod.rs:721-784`）；dpm `frc_s` 直接重建结构并**把 spine 实参全部推进**（`frc_sp_s`，`eval.rs:157,168-171`）。
  → 根因是 L07 的 `invert/prune` 需要**可逆 spine**（槽位必须保持 bare rigid 才能倒推 `?m` 的参数）；design doc 明确警告"移植必读：槽位只包裹"。**因此 dpm 不能当 L07 `force` 的逐行参考实现。**
- **发散防护**：L07 全局 `UNIFY_FUEL=4096` + `burn`（force 展开/合一同池，`mod.rs:479`），耗尽**有界降级**（可能翻转判定）；dpm `Res.progressed` + `frc_res`（`eval.rs:98-106`），只防自旋、不改变判定，无预算。
- **occurs**：L07 有浅 occurs（闭包体不探查，环交 fuel 兜底）；dpm 无（`NOTES.md:283-285`）。

### 4.2 模式编译与特化合一：接口同向，判定分档

| | L07 | dpm |
|---|---|---|
| 驱动 | `Compiler`（`sub: Rc<Subst>`, `solvable: Vec<Lvl>`, 覆盖记账）`pattern_match.rs:46-71` | `check_pm` 纯递归 + `Ctx`（`elab.rs:196-274`） |
| 解的载体 | `SpecSolve{solvable, acc}` 就地累积（`unification.rs:42-45,901-928`） | `unify1` 返回 `Succ{lvl,sub}`，`unify_s` 应用到剩余方程（`elab.rs:53-61`） |
| 可解性 | 显式白名单 + 未精化检查 + 非 Flex | 形态判定 `as_var`（**任意** bare var） |
| 结果 | 二值 + fuel 尾注 | 三值 Succ/Abs/Idk |
| 覆盖性 | 顶层逐构造子探测 + 嵌套延迟探测 + `PosCover`（`pattern_match.rs:140-149,228-261,276-348`） | 无（`refl` 的合法性即覆盖判定） |
| 上下文 | `subst_cxt` 只包裹 env 槽与类型表 | `subst_ctx` 全量重建 types/env |

三处实质结论：
1. 共同片段上**可解集几乎重合**（L07 基线 `bind_slots` = 全部真槽；dpm `Ne::Var` 也只能是槽），不存在"dpm 过度求解"的笼统结论；L07 只额外排除**瞬态层级**（η 下钻 `l+1`、探测 scratch）与 Flex。
2. **dpm 的 `unify_s` 多方程路径在 checker 里是死代码**（`check_pm` 每次只送 1 条方程），不要与 L07 的 `unify_indices`（每臂 N 条）直接对位。
3. L07 的"历史 bug 按构造排除"（add_assoc 族）来自"不改写槽位 + 不回滚值"；dpm 从原版继承同一设计，所以它本来就没有那类 bug。

### 4.3 卡住项与 quote：`Val::Match` vs `Ne::Lam`

- L07 把 `match` 做成一等值：捕获 env + 分支体 Tm + pending 实参，`force` 时重选 scrutinee、在**值层**补 pending（`mod.rs:609-628`），quote 时在 `simpl_decl` 下用 fresh rigid 重求值分支体（`mod.rs:1275-1302`）。**多 scrutinee、嵌套 match、splice 语义**都由它承载。
- dpm 没有 case 树：卡住的模式 λ = `Ne::Lam(ps, arity, cl, spine)`，重新来参数就重跑 `match_`（`eval.rs:233-263`，NOTES 偏离 2 明说会重算已匹配 binder）。因此 quote 必须**饱和欠应用 λ**（NOTES 偏离 3，`eval.rs:456-488`），否则会丢实参。
- 转换判定：L07 有 `struct_eq` 纯结构快路径（不 force、预算 20000、同址短路、迭代化，`struct_eq.rs`）+ η 臂（`unification.rs:947-962`）；dpm `conv` 递归 force、无 η、无预算（NOTES 偏离 13 修了 `plus` 中性不自反）。
- 后果：L07 的 `quote`/`pretty` 仍是深值递归路径（README §7.6 诚实清单），dpm 靠 `MAX_DEPTH=512` + 64 MiB 栈。

### 4.4 语言表面：声明层 vs 单表达式

| 能力 | L07 | dpm |
|---|---|---|
| 用户数据类型/GADT 返回/索引 | ✅ `enum` + `-> ret` | ❌（唯一索引类型是内建 `Id`） |
| 隐式参数 + 自动插入、命名隐式实参 | ✅ | ❌ |
| 洞 / 元变量 / 推断 | ✅ | ❌（λ 与 `refl` 均不可推断） |
| 递归定义 / 顶层声明 | ✅（decl 表 + 自引用占位） | ❌（程序 = 单表达式，递归只在 `plus` 原语里） |
| 构造子模式 / 嵌套模式 | ✅ `Pattern::Con` 树 | ❌（`Pn` 只有 var/refl/abs） |
| 荒谬模式 | ❌ 语法，但"零臂 match"等价 | ✅ `(!)` + `Tm::Bot`（NOTES 偏离 7） |
| `.field` 投影 / 限定构造子 / builtin（字符串、可变全局、文件 IO） | ✅ | ❌ |
| 打印产物可读回 | ❌（打印 `Enum::case`、读入 `Enum.case`） | ✅（`succ` 同义词 + 名字带 `'`，偏离 12） |

**判断**：这是 `NOTES.md` 明示的**范围选择**；dpm 的 `Val` 变体数并不少，是因为它把 `Ne` 单列一层，变体数不能当能力指标。

### 4.5 工程面：诊断与 API 是真正的不对称

| | L07 | dpm |
|---|---|---|
| 错误类型 | `Error(String)`，**无位置**（`mod.rs:445`） | `Error{msg,pos}` + `render`（行列 + 源码行 + caret，160/64 字符截断，`context.rs:50-96`） |
| 解析错误 | 折叠为 `"parse error"`（`parser/mod.rs:125-128`） | 最远失败位置 + caret |
| 防爆栈 | 大栈线程（64/256 MB） | 解析器内 `MAX_DEPTH=512` 共享预算 + 64 MiB 线程 |
| LSP | 本层未接入（项目 LSP 服务 L13） | 独立 crate，25 集成测试，wasm web IDE |
| 验收 oracle | 自家 `run` vs `run_fast`（Ok 逐字节 / Err 只判定） | Haskell 原版 golden（`tests/golden.rs`，7 测试 116 检查，跨进程） |
| 依赖 | crate 16 项（层内直接用 `smol_str`/`bumpalo`） | 核心 0，LSP 仅 `serde_json` |
| 性能口径 | 专用 `l07bench`（7 workload，min-of-rounds，孪生加速比 15×/27×/18×/3×/5×） | 无 bench，只有"复杂度不退化"断言（trans n=1..30 < 10s） |

---

## 5. 可观测差异矩阵（谁接受/谁拒绝）

| # | 情形 | L07 | dpm | 证据 |
|---|---|---|---|---|
| 1 | 自指索引 `Id Nat (suc x) x` 上的 `refl` | **接受**（浅 occurs 不传递，环经模式槽中转而漏过）【实测】 | **接受**，输出 `λ x refl . zero`，函数永不可应用【实测】 | `unification.rs:908-910`；`elab.rs:82-93`；EXPERIMENTS F1 |
| 2 | 荒谬消去 `Id Nat (suc zero) zero -> A` | 接受（零臂 match）【读码+回归钉】 | 接受（`λ A (!)`，打印 `⊥`）【实测】 | `l07_blackbox_v3`；`elab.rs:241-266` |
| 3 | 卡住索引方程（两个递归 def 的卡住 match）上写 `refl` | **先跑 256.2 s，再误报「分支不可达」（假不可达）**【实测】 | 拒绝：`I am not sure if there should be a pattern 'refl'...`，5 ms【实测】 | `unification.rs:1034-1085`；`elab.rs:111,235-239`；EXPERIMENTS F2/F3 |
| 4 | `zero = zero` 上写 `(!)` | 拒绝（分支不可达） | 拒绝：`It should not be '(!)' ... try 'refl'` | `elab.rs:228-234` |
| 5 | 递归定义 + 归纳证明（`add_comm`/`add_assoc`） | 接受 | **语法上写不出** | L07 README §8；`NOTES.md:281-313` |
| 6 | 省略 λ 参数类型 / 用洞 `_` | 接受（fresh meta） | 拒绝（`Can't infer type for lambda expression`） | `elaboration.rs:555-567`；`elab.rs:330` |
| 7 | 重定义同名 `def` | 报 `redefine {name}` | 不适用（`let` 遮蔽合法） | `elaboration.rs:213-215` |
| 8 | 同一类型错误的呈现 | `can't unify Nat == Bool`（无位置） | `<stdin>:1:17:` + 源码行 + caret | `mod.rs:1317-1333`；`context.rs:50-70` |
| 9 | 深层模式负载 | fuel 耗尽可能假 absurd（有界降级，带尾注） | 无此失效模式（可能栈溢出/超时） | L07 README §7.2；`NOTES.md:210-231` |
| 10 | 10^5 层深值 | occurs/struct_eq/rename 迭代化可跑；quote/pretty 仍递归 | 依赖 MAX_DEPTH + 大栈，未迭代化 | L07 README §7.6 |
| 11 | 打印 λ `λ f x . f x` | 打印 `f => x => f x`【实测】 | 打印 `λ f x . f x`【实测】；**Haskell 原版 nf 发散**（15 s 超时）【实测】 | EXPERIMENTS F4/F5 |
| 12 | 自指索引变体（索引对调，单步成环） | **拒绝**（8 ms）——证明浅 occurs 只挡单步环 | 未测（无 occurs，会接受） | EXPERIMENTS F1 |
| 13 | 非递归 / 可归约的卡住 match（隔离用例） | 接受（13 ms / 8 ms）——只有「递归 def × 刚性 scrutinee」才爆炸 | 未测 | EXPERIMENTS F3 |

**读法**：第 1 + 12 行说明 L07 的 occurs 是**逐方程、不传递**的——同一意图只把索引顺序对调，判定就从接受翻成拒绝；第 3 + 13 行说明它在卡住索引方程上既非"接受"也非"干净拒绝"，而是**先用 4 分钟再误报矛盾**。**同一维度上两侧不是简单的强弱关系**，必须按"接受集 / 诊断分档 / 表达力 / 鲁棒性"四个坐标分开陈述。

---

## 6. 复杂度与性能

- **算法级**：无差异——两侧都是 NbE + 一阶合一 + 构造子注入 + 显式替换，模式精化都是 specialization by unification。
- **成本位置不同**：
  - L07 用 **fuel 预算**换确定性（深模式可判、但可能翻转判定），成本在**写/包裹/组合**（perf 文档：读路径零命中；深嵌套 81% 分配在 `Subst::compose` 的逐条 cons）。显式替换重构后 match 密集负载回归 1.18–1.35×，**比值不随规模漂移**（判定为常数因子）。
  - dpm 用 **progressed 单调性**换"不改变判定"，成本在 **lookup 的按需 subst** 与 force 的 spine 推进；NOTES 偏离 4 记录分层替换把 `trans` 族从 2^n 降到二次（trans60 16 ms）。
- **规模**：合一层 10.9×、模式编译 6.5×、求值/quote 2.3×——差距几乎全部由"meta + Sum/GADT"两项解释，与模式匹配算法本身无关。

---

## 7. 证据与验证状态

| 事项 | 状态 |
|---|---|
| L07 单元测试 | 【实测】`cargo test --lib L07_sum_type` → **54 passed / 0 failed**（含 tests.rs 48 + mod/unification/孪生 entry 等 6），2026-10-30 |
| dpm 二进制行为 | 【实测】当前源码 `cargo build --release` 后跑 `dpm-nbe nf`：自指索引接受、`(!)` 接受并打印 `⊥`、卡住 plus 方程报 not sure、`zero=zero` 写 `(!)` 报 try refl（注意：仓库自带旧二进制会把 `Nat` 报成未绑定变量，必须重编译） |
| 两侧行数/测试数 | 【实测】`Get-Content` 计行、`Select-String '#\[test\]'` 计数 |
| L07 侧行为（occurs / 卡住索引方程 / 打印） | 【实测】临时 `examples/l07_probe.rs` + debug/release 二进制按文件跑（90 s/120 s/300 s 硬超时），测完已删除；结果见 [EXPERIMENTS.md](EXPERIMENTS.md) |
| Haskell 原版行为 | 【实测】GHC 9.10.2 + `Text.Megaparsec` 桩 + 手写 AST（绕过 Parse.hs）：infer 全部通过、nf 全部发散（偏离 1 实证） |
| L07 是否接入项目 LSP | 【推断】按类型名 grep `L07_sum_type` 仅出现在 `src/lib.rs:52` 与 `src/bin/l07*.rs`；未通读 `config.rs`/`ls.rs` |
| `674 行 meta` 明细 | 【估算】按函数行区间加总，±10% |
| 两侧 pretty 的逐字节可对齐性 | 【实测】不可对齐：同一 λ L07 出 `f => x => f x`、dpm 出 `λ f x . f x`、Haskell 原版打不出（EXPERIMENTS F5） |

**已更正的错误口径（相对最初的假设）**：
1. ~~"dpm `subst_ctx` 成功时 lvl=g-1 缩小"~~ → `ctx.lvl` 全程不变（见 §3 更正）。
2. ~~"dpm 合一只需处理闭值方程"~~ → dpm 方程同样是开值（含 `Ne::Var`），区别是 **metavariable-free**（只需解、不需回滚/回写），不是 closed。
3. ~~"L07 的 force 查表 Rust 版是 HashMap O(1)"~~ → 设计稿 §10 的旧表述；**实现是持久化单链沿链扫描**（§9.4 定稿），引用设计稿必须回代码核实。

---

## 8. 结论

**一句话**：两者是同一套理论（explicit substitutions + forcing + specialization by unification）的两个投影——L07 是"带元变量与声明层的完整 elaboration-zoo"，dpm 是"metavariable-free 的最小核"。因此：

1. **比机制**：重合度极高；分歧全在"有没有 meta"与"模式匹配放语法层还是值层"两处根结点上。
2. **比完备性**：L07 表达力严格更宽（GADT/隐式/洞/递归定义/η），但判定**不再纯语义**（fuel 可翻转——实测一个只有 4 个 def 的卡住索引程序要 **256 s** 才误报"不可达"）；dpm 在它自己的语言内判定更精细（Succ/Abs/Idk），但缺 occurs 使其接受集**更宽**。**两边都有 occurs 缺口，只是位置不同**：dpm 完全没有；L07 有浅检查但不传递（实测同一程序只换索引顺序就反转判定）。
3. **比工程**：dpm 的诊断/API/LSP 更完整（位置、caret、有界解析、独立 LSP crate、零依赖）；L07 的规模/性能工程更强（bench、双实现 parity、arena 孪生 15–27× 加速）。
4. **双向借鉴**：
   - **dpm → L07**：显式替换 + forcing 已吸收（本次重构）；**三值判定（Idk）**值得借——它能消除"fuel 耗尽 → 假 absurd"的语义污染；**错误携带位置 + 有界解析**是做 LSP 前的必补（README §7.6b 已列 quote/pretty 深路径待迭代化）。
   - **L07 → dpm**：**不要**搬 `Val::Match`/meta（dpm 的核心资产正是"值域小心、模式只在语法"）；但 **occurs check** 是 dpm 的真实缺陷（`insert_sub` 违反自己标注的类型不变量），补一条浅检查即可，成本极低。
   - **不要把 dpm 当 L07 `frcs` 的逐行参考**（会重新引入误报 can't unify）；也**不要**把 L07 的 `subst_cxt` 搬进 dpm（会破坏"上下文收缩"这条 dpm 的替代不变量）。

---

## 附录：四份分维度详证 + 一份实测

1. [`01-subst-force.md`](01-subst-force.md) — D1–D12 + S1–S5：替换表示/组合/查找、force 入口纪律、槽位不物化、fuel vs progressed、occurs、应用序/β、复杂度实测。
2. [`02-pattern-unify.md`](02-pattern-unify.md) — D1–D12 + A–E：接口形状、可解集、注入性与索引方程、上下文/lvl、覆盖性、occurs、三值判定、卡住 match、模式组形态、期望类型重锚、编译期成本。
3. [`03-value-quote.md`](03-value-quote.md) — D1–D10：值域分层、卡住 eliminator、quote 饱和、simpl_decl、struct_eq vs conv、η、fuel、打印、深值。
4. [`04-surface-meta.md`](04-surface-meta.md) — D1–D14 + 5.1 能力矩阵：语言表面、声明层、元变量机器规模、诊断/解析/运行契约、测试与验收口径、依赖与体量、IDE 面。
5. [`EXPERIMENTS.md`](EXPERIMENTS.md) — 三侧实测：方法（含 Haskell 无 megaparsec 时的桩方案）、5+3 用例、判定/耗时表、F1–F5、对四份文档的修订清单、复现步骤。
6. [`HASKELL-DIVERGENCE.md`](HASKELL-DIVERGENCE.md) — Haskell 原版"打印/比较 λ 就发散"的根因（`frc`/`napp` 自旋）、影响面、最小补丁与验证。
7. [`ISSUE-haskell-frc-lambda.md`](ISSUE-haskell-frc-lambda.md) — 可直接提交给 `KonjacSource/dpm-nbe` 的 issue 草稿（英文，含 4 个复现与 patch）。
8. [`L07-RISKS.md`](L07-RISKS.md) — L07 潜在问题清单 P1–P14（健全性/性能/工程/文档四级 + 修复顺序）。
