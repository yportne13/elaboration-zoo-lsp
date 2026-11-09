# L07–L13 横切分析：双引擎 / 防护 / 性能 / 工程性 / 重构建议

> 作者：横切分析员。口径：工作树 HEAD `8443586e`（2026-11-08）。**未运行任何 cargo/bench**（FACTS §1），
> 性能数字全部引自 `docs/bench-matrix-2026-09-20.md` 并标注时效。标记：`[码]` 静态读码/grep 实测，
> `[文档]` 引文档，`[推断]` 我的判断。
>
> **先纠一处 FACTS 错误（已报 Lead）**：FACTS §2「合计」列对 L07/L08/L13 **重复计入测试文件**
> （1893+1617+13498=17,008 行），故 143,814 是虚数。七层真实合计 = 参考侧 64,119 + 孪生 62,687
> = **126,806 行** `[码]`（`src/L07*…L13*` 下 `.rs`，PowerShell 行计数）；任务书里的"约 12 万行"
> 才是对的。另，`src/` 全域 362 个 `.rs` / 230,273 行（含 L01–L13、LSP、bins）。

---

## 1. 双引擎矩阵

### 1.1 规模与形态

| 层 | 参考版 LOC | 其中测试 | 生产 LOC | 孪生 LOC | 参考版形态 | 孪生形态 | parity 套件（静态） |
|---|---:|---:|---:|---:|---|---|---:|
| L07 | 6,212 | 1,893 | 4,319 | 7,848 | 平铺 11 文件 + `parser/`(3) | **子目录 13 文件** | 27 |
| L08 | 5,333 | 1,617 | 3,716 | 7,593 | 同 L07 | 子目录 13 文件 | 35 |
| L09 | 4,940 | 0 | 4,940 | 6,726 | 平铺 10 文件 + `parser/`(3) | 子目录 14 文件 | 29 |
| L10 | 6,245 | 0 | 6,245 | 8,375 | 平铺 + `typeclass.rs` | 子目录 13 文件 | 21 |
| L11 | 9,174 | 0 | 9,174 | 7,873 | 平铺 + `parser/`(4) | **单文件 7,873 行** | 19 |
| L12 | 9,398 | 0 | 9,398 | 7,864 | 平铺 + `canonical.rs` | **单文件 7,864 行** | 15 |
| L13 | 22,817 | 13,498 | 9,319 | 16,408 | 26 文件 + 17 个 `*_tests/probe` | 子目录 15 文件（含 `compact`/`observe`） | 15（多源循环） |

`[码]`（LOC 见 FACTS §2 并按上述口径纠偏；形态/local line 数为本次实测）。读法：**参考版 LOC 与孪生 LOC
不是"同一算法的两倍成本"**,后者是第二套值表示/求值器/合一器（FACTS §8）；L13 参考版看似 22.8k，
生产代码只有 9.3k，其余 13.5k 是测试/探针——L13 的"生产层"属性首先体现在**测试体量**上。

### 1.2 共享模块：所谓"共用"是层内共用，不是跨层共用

- **层内**：孪生与参考版共用 parser / pretty / preprocess / Synth。`[码]` L13 孪生模块头直言
  "与参考版共用 parser / pretty / preprocess / Synth，Ok 输出逐字节一致"
  （`src/L13_namespace/bump_spine_iter.rs:69`）；L09/L10/L11/L12 孪生同样 `use crate::Lxx::parser` +
  `use crate::Lxx::pretty`（`L09/bump_spine_iter.rs:108-110`、`L11/bump_spine_iter.rs:136-138`）。
  ⇒ **parity 无法守护 parser/pretty 漂移**（a7-r1 §2.6 已把这条列为 P3 风险）。
- **跨层**：**零 crate 级共享**。`[码]` 七个层目录各带一份 `parser/`（939/972/1,186/1,366/3,217/3,398/6,850
  行，合计 **17,928 行**）与一份 `pretty.rs`（10 个 pretty 文件）；`typeclass.rs` 有 4 份（L10–L13，
  `Synth` 命中 16/16/14/36）、`canonical.rs` 2 份（L12/L13）。MD5 比对：`pretty.rs`/`unification.rs`/
  `cxt.rs`/`mod.rs`/`pattern_match.rs` **七层两两全不同**；相同的只有 `syntax.rs` 的 **L07≡L08**、
  **L12≡L13** 两对。⇒ 任务书说的"L10/L11/L12/L13 的 Synth 共用"应更正为**语义同源、代码各自一份**。
- 消费方向是单向的：项目 LSP/format/docgen **只挂 L13**（`src/format/mod.rs:17`、`src/doc/collect.rs:24-28`、
  `src/lib.rs:1509/2830`）。L07–L12 没有外部消费者——双引擎只服务层内 oracle 与 bench。

### 1.3 只在单侧的机制

| 只在参考版 | 锚点 | 只在孪生版 | 锚点 |
|---|---|---|---|
| L12 `iddfs`/`canonical` 搜索（Err 重试闭包专用） | `src/L12_canonical/canonical.rs`（`fn iddfs` 1 处）；FACTS §4 | L13 `prime_resident`/常驻 prelude 检查点/`compact` 压实/`observe` 总闸 | `src/L13_namespace/bump_spine_iter.rs:80/163/179/187` |
| L13 `PreludePool`、`FUNC_PROF`、retry 闭包、Tm/Val 迭代 Drop | `src/L13_namespace/mod.rs`（FORCE_MEMO 相关 40 处）；wip §三：238 | L09–L12 的 `PM_FUEL` thread_local 燃料池（σ 移植补入） | `L09/bump_spine_iter/force.rs:104`、`L10:157`、`L11:166`、`L12:166` |
| L07 `quote_deep`（P11 深值迭代化） | `src/L07_sum_type/mod.rs:1467` | 各层消融开关 `L0x_NO_CONV_MEMO`/`NO_NAME_MAP`/`TYPORT_TWIN_NO_COMPACT` | `L07/bump_spine_iter.rs:12` 附近；`L13/bump_spine_iter.rs` 头部 |
| L13 `FORCE_MEMO`（两版都有，参考 mod.rs 与孪生 force/entry/prim/quote 均命中） | `L13/force.rs`、`L13/entry.rs` | — | — |

### 1.4 parity 判据差异（这是横切里最容易被忽略的不对称）

| 层 | Ok 判据 | Err 判据 | 归一化 | 锚点 |
|---|---|---|---|---|
| L07 | 逐字节 | **仅判定（Ok/Err）一致，不比正文** | — | `tests/l07_fast_parity.rs:5-6` |
| L08 | 逐字节 | **正文逐字节**（最强） | 剥 `@ N` span | `tests/l08_fast_parity.rs:5-7/60` |
| L09 | 逐字节 | 正文 | 剥 span | `tests/l09_fast_parity.rs:53-60` |
| L10 | 逐字节 | 正文 | 剥 span | `tests/l10_fast_parity.rs:48-50` |
| L11 | 逐字节 | 正文 | 剥 span + **`?N`** | `tests/l11_fast_parity.rs:50-51` |
| L12 | 逐字节 | 正文 | 剥 span + `?N` | `tests/l12_fast_parity.rs:133-136` |
| L13 | 逐字节 | 正文 | 剥 span + `?N` | `tests/l13_fast_parity.rs:67-70` |

**剔除/缺口族**：L11/L12 孪生 `gadt` 是"快版编译 walk 缺陷区"、bench 禁用（`tests/l11_fast_parity.rs:474-476`）；
`L10 enum` 孪生发散、`L11/L12 enum` 孪生 check+nf 失败、`L12 traitchain` 孪生 parity 失败（bench §4:261-264）；
L13 有 4 个既有 parity 失败（`test14`/`test_prove_term_pure`/`test_stuck_match_application_does_not_panic`/
`resident_compaction_*`，wip:174-184），另有"单行 enum 两版同错"的假阴性（FACTS §4）。
`[推断]` 判据强弱顺序是 L08 > L09/L10 > L11/L12/L13 > L07 —— 而 L07 恰是加固最厚的层，这使"最严的
语义加固"落在"最弱的 oracle"后面，是本仓最值得修的一处工程倒置。

**套件规模与实际执行量**（FACTS §3，静态 `#[test]`，未执行）：L07 27 / L08 35 / L09 29 / L10 21 /
L11 19 / L12 15 / L13 15 是**套件自有**数量；因 `#[path]` 把本层 `mod.rs` 编入，实跑数要加 lib 测试
（L07 97、L08 95（11-08 后）、L10 42、L11 37、L12 36/15 口径不一）。这带来两个后果：
①**测试重复执行**（同一断言在 lib 与 parity 各跑一遍，L13 13.5k 行 legacy 测试尤甚）；
②**parity 覆盖面被高估**——套件自有用例才是真正的"双引擎互检"，其余是"同引擎自检跑两遍"。

### 1.5 已知分叉家族汇总

| 家族 | 归属 | 性质 | 锚点 |
|---|---|---|---|
| 精化载体：σ（`VSub`/`frcs`/`SpecSolve`）vs `update_cxt`+`refresh` | L07–L12 已迁（`VSub` 命中 148/95/86/76/81/71，L13 仅 5 处且为注释）；L13 仍旧路（`update_cxt` 29/`refresh` 20） | **刻意分叉**（L13 五轮失败后回退） | explicit-subst-status §1/§4；FACTS §8 |
| 名字世界：`Infer.global` 大下标哨兵 vs decl 表 | L09/L10（`Infer.global` 5/6 处）；L07/L08/L11/L12/L13 用 `Val::Decl`（25/21/22/24/55） | 刻意分叉（时代架构） | FACTS §4；a7-r1 §5 |
| 原生 Nat / Call / OpCall / prim 入 decl 表 | **只有 L13**（`Val::Nat` 75 处、`Val::Call`、`force` 的 Decl 臂） | L13 生产增量，刻意 | `L13/bump_spine_iter.rs` 头部 |
| fuel 矩阵 | L07/L08 `UNIFY_FUEL`+`MATCH_CMP_BUDGET`；L09–L12 孪生 `PM_FUEL`；L13 `UNIFY_FUEL`+内层 fuel=100 | **部分刻意、部分是缺口**（见 §2） | 各层 mod.rs / twin force.rs |
| 深值处理 | L07 参考 `quote_deep`；L13 迭代 Drop+pretty 截断；L08–L12 无 | 加固不对称 | `L07/mod.rs:1467`；wip §三:238 |
| 探测隔离（`filter_accessible_constrs`） | L09/L10 克隆 Infer；L11/L12 参考版 **丢失隔离**（perf commit 165313d）；L13 窄快照；各层孪生 `run_pure_probe` 完整 | **L11/L12 是缺陷**（a7-r1 §2.1 P1） | `L11/pattern_match.rs:174-178`、`L12:176-180`、`L13:270-334` |
| 判定分档（`UnifyKind` 三档 vs bool） | L07 参考有、孪生无；L08–L13 无 | 缺陷窗口：同一程序 ref 报"无法判定"、twin 报"分支不可达" | L07-RISKS §0.1:56-60 |

---

## 2. 防护 / 健壮性矩阵

### 2.1 逐层取值

| 机制 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---|---|---|---|---|---|---|
| `UNIFY_FUEL` | 4096 `mod.rs:627`+`prim.rs:36` | 4096 `mod.rs:542` | 4096 `mod.rs:476` | 4096 `mod.rs:450` | 4096 `mod.rs:486` | 4096 `mod.rs:605` | 4096 `mod.rs:1419`（孪生无同名常量 `[推断]` 局部 fuel） |
| `PM_FUEL`（thread_local） | 无（0 命中） | 无 | 4096 `twin/force.rs:104` | 4096 `twin/force.rs:157` | 4096 `twin/force.rs:166` | 4096 `twin/force.rs:166` | 无 |
| `MATCH_CMP_BUDGET` | **64** `mod.rs:641`+`twin/unify.rs:40` | **64** `mod.rs:547`+`twin/unify.rs:37` | **缺** | **缺** | **缺** | **缺** | **缺** |
| unify 迭代内核燃料 | 有（参数化） | 有 | **无**（`twin/unify.rs:350` "无燃料（参考版无 fuel）"） | **无**（`twin.rs:61` 同） | **无** | **无** | 内层 fuel=100（`twin/unify.rs:477`） |
| 深值迭代化 | 参考 `quote_deep`；孪生 `quote_iter`（`twin/quote.rs:79`） | 无 | 无 | 无 | 无 | 无 | 迭代 Drop + pretty 定深截断（wip §三） |
| fuel 耗尽行为 | 参考→`Undecided`（三档）；孪生→"分支不可达" | 参考同上；孪生已镜像 P1/P2 但无三档 | PM_FUEL 耗尽→lookup 命中降级为裸 rigid（`twin/unify.rs:413`） | 同 L09 | 同 L09 | 同 L09 | FRCS/FORCE_MEMO 有 `fuel0>0` 守卫（wip:274-276）；深链 12k 层→爆栈 |
| Stacked Borrows UB | 未登记 | 未登记 | 未登记 | 同族 | 同族（twin 2159/2425/2541/2564/3959） | 同族（2210/2476/2592/2615/4035） | 同族 |
| `panic!` 静态数（含测试） | 17 | 21 | 27 | 19 | 31 | 31 | **253** |
| `Too much effort`（effort panic） | 0 | 0 | 0 | 1 | 1 | 1 | 1 |
| 跨轮回收 | σ 链 Rc，bump reset 不跑 Drop（有界泄漏，`L07/twin.rs:21-24`） | 同 | 同 | 同 | 同 | 同 | `compact` 压实（twin 专属）；参考版 `FORCE_MEMO` 1<<20 强持 |

`[码]` 静态 grep 实测（禁止 cargo，运行期未验证）。**结论：七层的燃料"都有 4096"，但语义完全不同**——
L07/L08 是"每顶层合一入口一份"的调用级预算（并带 `MATCH_CMP_BUDGET` 次数预算），L09–L12 是精化展开
的 thread_local 池（unify 主循环本身无燃料），L13 是参考版单常量 + 孪生内层 100。把 4096 当成
"七层同等防护"是错误读法。

### 2.2 2026-11 L07 加固 P1–P11 的层间分布（核心问题）

| 项（L07-RISKS 编号） | L07 | L08 | L09 | L10–L12 | L13 | 缺失的实际风险 |
|---|---|---|---|---|---|---|
| **P1** occurs 传递 | ✅ 参考+孪生（VSub 臂有 R2 已知限制） | ✅ 参考+孪生（11-08 镜像） | ❌ 试过→**回滚**（硬搬会把"接受"变"拒绝"） | ❌ 未评估 | ❌ 未评估 | 两跳环被接受 ⇒ **接受循环解**（健全性） |
| **P2** 卡住 match 比较预算 | ✅ 64 次总次数 | ✅ 64 | ❌（实测 **直接接受** c2，语义半径不同） | ❌ 无 `MATCH_CMP_BUDGET` | ❌ 无 | 无预算时 c2 在 L07 需 **256 s** 并报假不可达；L10–L13 `[推断]` 同类输入可能极慢或误判 |
| **P3** fuel 三档判定（`UnifyKind`） | ✅ 参考；**孪生未迁** | ❌ | ❌ | ❌ | ❌ | 耗尽被报"分支不可达"⇒ 合法程序被拒；ref/twin 判定分裂窗口 |
| **P5** 跨 meta 环守卫 | ✅ 参考（`meta_expanding` 有界化）；孪生未迁 | ❌ | ❌ | ❌ | ❌ | 间接环靠 fuel 兜底 → L13 实测 12k meta 解链爆栈（wip §二） |
| **P8** 宽松合一收窄 | ✅ 参考；孪生未迁 | ❌ | ❌ | ❌ | ❌ | 未登记 `Decl/Prim` 头可静默判等（字符串逃逸舱口） |
| **P9** 诊断 Debug 泄漏 | ✅ 参考+孪生 | ✅（11-08 补 span 泄漏） | ❌ | ❌ | ❌（但 L13 自带 span 载体） | LSP 用户可见 `Con("refl" @ 166,170,…)` |
| **P10** `Error` 带 span | ✅ 载体+解析/模式 span | ❌（单字段） | 未核实 | 未核实 | ✅ 已有 `Error(span, vec)`（`src/lib.rs:1988`） | 诊断无位置；LSP 无法出 `Diagnostic.range` |
| **P11** 深 quote/pretty | ✅ 部分（Sum/SumCase/Obj 迭代，Lam/Pi/Match 仍递归、Drop 递归未解） | ❌ | ❌ | ❌ | ✅ 迭代 Drop+截断 | 10 万层深值爆栈（L07 旧口径 0xC00000FD） |
| **P15** `struct_eq` 漏比 Match pending | ✅ | 未核实 | **不适用**（无 pending） | 未核实（L11/L12 有 Match pending） | 未核实 | 可证 `False`（S1 健全性） |

`[文档]` 分布依据：`docs/compare-l07-vs-dpm/PR-l07-hardening.md` §2/§2.5/§7、`L07-RISKS.md` §0.1:36-60、
`L07-RISKS.md` §0 编号表。**判断**：加固不是"七层共享的通用硬化"，而是**L07/L08 专属的语义收紧**；
跨层推广已由作者实测否决到 L09 为止（PR §2.5:63-69：L09 上 c1 栈溢出、c2 直接接受，硬搬模板是
"语义变更而非修复"）。⇒ 正确的期望不是"回灌"，而是让 L09–L13 自带的最小防护（PM_FUEL/UNIFY_FUEL）
**耗尽时降级为可诊断错误而非错误判定**——这一条七层都没完全做到。

### 2.3 时代缺口 vs 当前缺陷（别把"没做"都算成 bug）

| 归类 | 项 | 依据 |
|---|---|---|
| **刻意的时代缺口**（不该按 L07 口径"补"） | L09 无 decl 表/builtin 五件套/可变全局/`Match` pending/`struct_eq`/fuel；L09–L12 无 `Val::Decl` 精化可见性；L10–L12 的 `unify_pm` 无 `solvable` 白名单 | L09 README（FINAL §2.3:69-71）；explicit-subst-status §3 P2:100-106 |
| **当前缺陷**（跨层同族、应修） | L11/L12 参考版探测隔离丢失（fresh meta 泄漏 + 探测期求解持久化）；L07/L08 孪生未迁 P3/P5/P8/P10/P11；L10–L13 无 `MATCH_CMP_BUDGET`；PM_FUEL 耗尽静默降级；parity `?N` 归一化掩盖编号漂移 | a7-r1 §2.1/§2.3；L07-RISKS §0.1；§2.1 本表 |
| **未评估**（不能预设） | L10–L13 的 P1/P2/P3/P5/P8/P15 同构性；L09–L12 的 `Error` span 形态；L13 孪生未镜像 GADT 精化（仅补丁系列内） | PR §2.5:55-69；wip §5:159-172 |

`[推断]` 三者混谈是当前文档体系最大的认知风险：各层 README 的"已知偏差"是作者诚实清单
（FACTS §7.5），但**没有一张表区分"我们决定不做"与"我们还没做"**，导致读者（和下一次评审）反复重开
同一批问题。建议 FINAL 里沿用上面这张三分类表。

---

## 3. 性能横切

### 3.1 四种口径的定义与不可比性

`[文档]` bench §4:256-260：`basic` = 参考版；`fast_ss` = 孪生稳态（排除建表，**解析在计时外**）；
`fast` = 孪生一次性；`fast_run` = 孪生**全流程**（仅 L11/L12 有）。
五个陷阱：

1. **L11/L12 参考版没有 `bench_check_nf`**（a7-r1 §3.2/转交 A5-3），故其 `basic` 行是**含
   preprocess+parse** 的全流程 `run`，与 L09/L10 的节点数口径不同轴 → l11bench/l12bench 另加
   `fast_run` 行才可比（bench 表 L11/L12 的 `basic/孪生` 用 `fast_run` 算，§4 注）。
2. **`fast_ss` 不含解析**：孪生列天生抹掉 parser 成本；跨层比 `fast_ss` 时 parser 规模差
   （L07 parser 939 行 vs L13 6,850 行）被隐藏。
3. **参考版地板差异**：L09 引擎本身慢（同负载 `strchain` 2,669 ms vs L07 122 ms，`struct` 4,269 vs
   L08 134），所以 L09 的 match 倍率 0.10× 主要是**地板高**，不是孪生 match 特别快（孪生 0.055 ms 与
   L10/L07 的 0.049/0.053 同档）。
4. **大值负载倍率不可跨层**：FACTS §5 已注明——`strchain` 倍率 L07 23× / L09 867× / L13 519×，差异
   来自参考版地板（122 ms vs 2,669/4,537 ms），不是孪生差异（孪生全在 3–14 ms）。**只读绝对时间或同层倍率**。
5. **窗口漂移**：09-20 对未改动层 L02–L06 的 32 格落在 0.943–1.008×（中位 0.983×，bench §1:63-66），
   改动层 <±10% 的格全部在噪声内；唯一超噪声的是 L12 match 6.56×（真回归，见下）。

### 3.2 match 主线：绝对时间 vs 倍率

| 层 | basic (ms) | fast_ss (ms) | 孪生/参考 | 备注（时效） |
|---|---:|---:|---:|---|
| L07 | 0.145 | 0.049 | 0.34× | 逐臂+σ；**09-20 后 11 月加固已改参考版路径** |
| L08 | 0.144 | 0.052 | 0.36× | 同 L07 |
| L09 | 0.557 | 0.055 | 0.10× | 参考版地板慢，倍率最大 |
| L10 | 0.171 | 0.053 | 0.31× | — |
| L11 | 0.202 | 0.044 | 0.47× | `fast_run` 0.094 |
| L12 | **1.431** | 0.195 | 0.22× | **含 09-20 时点 `eprintln!("DBG nc")`；HEAD 已删，清后 0.196 ms（bench 附录 §B:409-410）** |
| L13 | 0.215 | 0.172 | 0.80× | 孪生领先最小（1.25×）；生产引擎地板 |

`[码]` 复核：`grep "DBG nc"` **0 命中**（HEAD），故 1.431 这一行**不可再引用**。两种读法：
①**倍率**只说明同层两引擎差距——L09 10× 最大、L13 1.25× 最小；②**绝对值**说明"谁的 match 快"，
只有 L07/L08/L10/L11（0.14–0.20 ms）可直接横比，L09（0.557，地板）与 L13（0.215，生产引擎含
更多机制）需注明不同轴。**性能主线的结论是：孪生 match 在 7 层全部领先（1.25–10×），
参考版之间的 match 差异主要来自引擎地板而非匹配算法**。

### 3.3 特色负载与 09-20 之后的时效性

- 负载族：L07/L08 `{church,strchain,global,match,enum,struct}`；L09 `{+struct,universe}`；L10 `{+universe,
  traitchain}`；L11/L12 `{natadd,strchain,match,enum,struct,macro|traitchain}`（church/gadt 被排除，
  a7-r1 §4-A5）；L13 `{+gadt,moduletree,prelude-core(-show/-hdl),examples-hdl}`（唯一有真实 prelude 负载的层）。
- **时效性四条**：①2026-11 L07/L08 加固轮改了 L07 参考版判定路径与常量（L07 lib 66→70、parity 92→97，
  PR §5/§9），L07/L08 的 09-20 数字应视为**下限**而非现状；②L13 σ 实验**未落地**（master 无补丁，
  `git apply --check` 存档于 wip），L13 数字仍是旧机制；③L12 eprintln 已删、附录 §B 的 0.196 才是现状；
  ④L05 chain 属边缘可测（09-18 超时、09-20 147 s 贴 180 s 上限），跨层引用 L05 数字有系统性风险。

---

## 4. 工程性

| 维度 | 事实 | 锚点 |
|---|---|---|
| 重复代码规模 | 孪生 62,687 行 ≈ 七层代码的 49.4%，是**第二实现**而非复制；真正可去重的是跨层 copies：parser 7 套 17,928 行 + pretty 7 份 + typeclass 4 份 + canonical 2 份 ⇒ `[推断]` 去重上限约 **2.2–2.6 万行** | §1.1/§1.2；MD5 实测 |
| `.bak` 残留 | **17 文件 / 12,464 行**（L11 14 个 8,520 行、L12 3 个 3,944 行），未被 git 跟踪（.gitignore）、不参与构建但占盘/误导读者 | `[码]`；FACTS §7.6 |
| 调试/探针残留 | L13 `eprintln!` 66 / `println!` 345（含测试），并自带 `debug_test.rs`、`struct_refine_probe.rs`、`FUNC_PROF`——属**有意的诊断设施**（FACTS §7.7），不是死码；L12 参考版 `eprintln!` 6 处（09-20 的 `DBG nc` 已删，`[码]` 0 命中） | `[码]`；bench 附录 §D:445-448 |
| 单文件巨兽 | L11/L12 孪生各 **7,873 / 7,864 行单文件**；L13 参考版 `mod.rs` **7,628 行** + 13.5k 行测试 | `[码]`（`wc`）；FACTS §2 |
| 文档/代码同步 | 7 层 README **2,608 行**（564/351/340/314/294/353/392），`docs/` 下另有 100+ 份设计/轮次报告；已证过期：L13 README 称 lib 341 vs 静态 612（FACTS §7.1）、L09–L12 lib 计数口径（§7.2）、L08 README 266-284（PR §9 F9）、`L07-RISKS §0.1` 自相矛盾（review F5） | `[文档]`/`[码]` |
| 测试重复执行 | parity 用 `#[path]` 把本层 `mod.rs` 编入 → lib 测试再跑一遍：L07 parity 97 = 27 自有 + 70 引入（PR §5）、L10 42 = 21+21（FACTS §3 注）；L13 13.5k 行 legacy 测试在 lib 与 parity 各跑一次 | `[文档]` |
| 磁盘/构建成本 | 七层两引擎 + 17 份 .bak + target 二进制；环境硬约束"F 盘 <1GB 禁 cargo"直接把可复现性锁在文档里 | FACTS §1 |

---

## 5. 统一 / 重构建议（判断优先）

1. **抽公共 crate，但要分两步（高收益/中成本）**：先把 `pretty.rs` + `syntax.rs` 抽出去（纯数据/纯函数、
   无引擎耦合，约 3–4 千行，7 份副本；L12≡L13、L07≡L08 的 syntax 已逐字节同源，先例现成），
   再考虑 parser。**不建议**抽 unify/force：参考版 Rc 树与孪生打包 V 是两套值表示（FACTS §8），
   抽象层会把热路径 box 化，等于用性能换整洁，方向错。parser 留后：L11/L13 的 token 表/宏语法已分叉。
2. **不要统一的东西（刻意差异，改即回归）**：SumCase 显示格式分层（L08 空格 vs L09–L13 comma+血统，
   FINAL §2.3）、fuel 矩阵（三族语义不同，见 §2.1）、L13 的 `update_cxt`/`Val::Nat`/`Call`/`OpCall`
   （生产层增量）、L09/L10 的大下标哨兵（教学层的时代架构，改造=重写）。
3. **L13 σ 迁移：建议停**（收益/成本已明显为负）。证据链：五轮 + 5-agent 评审后 `l13_fast_parity` 仍有
   4 个既有失败、孪生镜像未做（唯一已知 REF/TWIN 语义分歧，wip §5:159-172）、纯 elaboration 仍 ~28×
   （22.4→637 ms，wip §三:64-71）、12k meta 解链爆栈、`FRCS_MEMO` 长跑 13 GB（wip:266-268）。
   若将来重启，先行项应是**meta 解链环检测 + compiler 分支缓存**（wip 接续清单 #3/#4），
   而不是继续搬机制。
4. **L09–L13 回灌 L07 加固：只做诊断子集，不做语义子集**。可低成本做：P9（`Pattern::pretty` 文案，
   零语义风险，L07 已有模板）、P10（span 载体；L13 已有）。**不要**硬搬 P1/P2/P3/P5/P8：PR §2.5 已实测
   L09 上 c1 栈溢出、c2 由"接受"变"拒绝"，属语义变更；L10–L13 未评估，需逐层做 L09 那样的实测再定。
   若只允许一件事：给 L09–L13 加**"燃料/预算耗尽 ⇒ 可诊断错误"**的统一口径（现在 PM_FUEL 耗尽静默降级
   为裸 rigid，`twin/unify.rs:413`，这是比缺预算更危险的行为）。
5. **补 L09–L13 的 parity 判据**：把 L08 的"Err 正文归一化后逐字节"推广到 L09–L13（现在 L11–L13 靠
   `?N` 归一化掩盖了 a7-r1 §2.1 那类探测泄漏），并给 L11/L12 参考版恢复探测隔离（窄快照，
   `L13/pattern_match.rs:270-334` 可下沉）。这是**低成本、高确定性收益**的一项。
6. **双引擎长期策略：保留，但把它当"第二实现 oracle"而非"优化开关"**。价值已用实验钉死：match 1.25–10×、
   大值负载 3–800×（FACTS §5）；成本是维护面积 ×2、17 个 .bak、以及 parity 归一化带来的盲区。
   可持续的形态是：参考版 = 教学 + oracle + 生产回退面（L13 的 twin 回退机制已在 `eval_budget.rs` 里
   真实存在），孪生 = 性能交付面；**不再新增第三引擎**，并把"两侧必须同构的机制清单"（fuel 口径、
   探测隔离、判定分档）写进 CONVENTIONS 类文档，避免再出现"参考版修了孪生没修"（P3/P5/P8/P9/P10/P11）。
7. **立即可做的工程清理**（半天级）：删 17 个 `.bak`（12,464 行）；L13/L09–L12 README 数字对账；
   L11/L12 孪生 7.8k 行单文件按 L07 模板拆分（纯编译期收益，`[推断]` 不影响性能）；
   把双引擎代码共享的"同构机制清单"从各层 README 提到一处。

---

## 6. 给 Lead 的一句话结论

**双引擎是资产（1.25–10× match 加速 + 独立 oracle），但加固与 oracle 强度按层反向漂移：先抽 pretty/syntax、停 L13 σ、只回灌诊断类加固。**
