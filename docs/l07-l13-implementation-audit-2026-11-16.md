# L07–L13 章节实现差异审计与实验报告（2026-11-16）

> 仓库：F:/projects/hermes/elaboration-zoo-lsp ｜ HEAD 57a11c28（2026-11-15 23:52 +0800，master，工作树仅 .audit/、.deltawork/ 未跟踪）
> 环境：Windows 10 19045 / AMD Ryzen 5 5600 (6C/12T) / 31.9 GB / rustc 1.98.1 / release / mimalloc
> 配套证据：.audit/（机制矩阵、git 时间线、性能/正确性原始日志与各工作流底稿）、docs/compare-l07-l13/DELTA.md（2026-11-08 旧审计）
> 口径：行数 = src/LXX/**/*.rs 物理行；机制计数 = 剔除整行注释后的代码命中；测试数 = 静态 #[test] 计数；性能 = 同机串行、进程隔离、多 pass 中位数（原始日志见 .audit/raw-perf/）

---

**目录**：0 结论速览 ｜ 1 方法与边界 ｜ 2 七层当前形态 ｜ 3 git 编年史 ｜ 4 相邻层差异（pairwise） ｜ 5 跨层机制断点总账 ｜ 6 实验一：跨层正确性矩阵 ｜ 7 实验二：现有套件现状 ｜ 8 实验三：跨层性能 ｜ 9 实验四：分配/内存 ｜ 10 影响归因 ｜ 11 建议 ｜ 附录 A 复现 ｜ 附录 B 证据索引

---

## 0. 结论速览

**用一句话回答“为什么会乱”**：这条链在 2026-09 之前确实是 copy-forward 的；之后 L13 产品化独立演进、L07/L08 被重写成“新参考系”、L09→L10 与 L10→L11 两次换名字世界、L13 又整体换掉精化载体——同时 2026-11 的**优化传播方向反转**（VSpan 从 L09 回灌 L07/L08、carrier switch 从 L09 回灌 L10、L07 加固回灌 L08/L09），于是“章更后 = 实现更新”不再成立。

**核心事实（HEAD 57a11c28 实测）**：

| # | 结论 | 关键证据 |
|---|---|---|
| 1 | 全史 **1756** 提交；2026-09 后触层 **430**、多层 **60**（前向 6 / 反向回灌 4 / 全链同步 9 / 配对层 19 / 其他 15 / 纯文档 7）。优化传播在 11-10 之后反转 | §3；.audit/history.md |
| 2 | **七层不是一条链，而是三条血统 + 产品层**：L07/L08（decl 表 + σ）、L09/L10（Infer.global 哨兵，11 月回灌载体切换）、L11/L12（decl 表 + 宏/canonical，未跟进 11 月加固）、L13（产品层：update_cxt + 原生 Nat + 命名空间/HDL） | §5.1 机制矩阵；.audit/deltas.md |
| 3 | **优化/守卫分布跨层错位**：VSpan 只在 L07/L08/L09（35/35/34，L10+ 0）；MATCH_CMP_BUDGET 只在 L07–L09；meta_expanding/quote_deep/rename_deep/MAX_DEPTH 只在 L07–L09 参考版；PM_FUEL 只在 L09–L12 孪生；eval_budget/termination 只在 L13 | §5.1；.audit/mechanism-matrix-code.tsv |
| 4 | **精化载体在 L12→L13 换路线**：σ（Subst/VSub/frcs/SpecSolve）在 L07–L12（L13=0），L13 两版回到 update_cxt+refresh（cxt.rs:1327），孪生删 subst.rs；这是最大的单点语义断代（L13 σ 五轮移植失败，master 有意不含） | §5.2、§3.4；docs/wip/ |
| 5 | **性能曲线不再按章节单调**（同文件 common 6 文件，HEAD）：参考版 L07 53.0 / L08 53.2 / L09 52.5 / **L10 31.9（最快）** / L11 57.2* / L12 47.7* / **L13 65.9（最慢）** ms；7 层孪生全部 16.9–19.0 ms（极差 ≤12%）——**跨层差异几乎只在参考版，且拐点对应 commit 而非章节号** | §8.1；.audit/perf.md |
| 6 | **正确性上抓到 2 类真问题 + 1 类跨层全错**：① L11/L12 把不同实参的卡住 prim 等式判等（假阳性/不健全）；② L12 拒绝 enum 索引投影 `t.len`（L07–L11/L13 都接受；已用 realbench 最小化）；③ 同实参 prim 等式：L07/L08 误拒、L09–L12 **panic**（`Option::unwrap`），只有 L13 正确 | §6.2–6.4；.audit/raw-correctness/probe-matrix.tsv |
| 7 | **现有套件全绿（1140 passed / 0 failed / 6 ignored）但它们覆盖不到上面的问题**：L09–L12 没有跨层语义回归、没有 tests.rs/黑盒；parity 只保证“同层两版一致”，两版同错会全绿（如 L12 索引投影：l12_fast_parity 50 个用例全过） | §7；.audit/raw-correctness/suite-summary.csv |
| 8 | **11-15 的修复有效但不完整**：struct 模式糖已补到 L08–L10（L08–L13 全部接受 weak03/weak05，ill-typed 正确拒绝），gadt 跨层 84、backport3_pretty 48+76 全绿；但 L11/L12 的守卫/载体债、L10–L13 的深值/环守卫缺失、L13 与 L12 的精化路线分叉仍未处理 | §6.3、§7；.audit/correctness.md |

**一句话结论**：这不是“七级台阶”，而是“三条架构底座 + 两条回灌支流 + 一个产品层跃变”的缝合体；真正需要优先处理的是 **卡住 prim 的四态判定（健全性/panic）**、**L12 索引投影回归**，以及**把 L11/L12 重定基到 L10 或明确登记为遗留分支**；性能上则应把跨层门禁改成同文件口径（孪生轴已收敛，参考版拐点由载体 commit 决定）。


---

## 1. 这份报告要回答什么、怎么回答

用户观察：项目原本“每章 = 上一章 copy + 新特性”，但中途的优化尝试与 bug 修复使现状混乱。本报告只做三件事：

1. **把“当前七层的实现差异”摊开**：不是逐层介绍功能，而是相邻层的增量差异（新增/删除/换载体/回退/守卫丢失/测试断崖），以及跨层机制矩阵（同一机制在各层以什么形态存在）。
2. **用 git 记录还原“怎么变成这样的”**：2026-09 至 11 的 430 条触层提交里，60 条跨多层的提交分类为：前向增补、**反向回灌**、配对层修复、全链同步；并定位每个断点的最早引入提交。
3. **用实验量化差异的后果**：跨层同程序行为矩阵（正确性）、现有 parity/黑盒套件在 HEAD 的真实通过情况、跨层同文件性能（性能）、参考版 vs 孪生（架构对比）。

方法/数据源：

| 证据 | 内容 | 位置 |
|---|---|---|
| 机制矩阵 | 30 个机制 × 7 层（参考版/孪生分开）代码命中 | .audit/mechanism-matrix-code.tsv（本报告 §5 表） |
| 文件/行数矩阵 | 每层每个 .rs 的路径 + 物理行 | .audit/layer-files.tsv、.audit/layer-cats.tsv |
| git 时间线 | 2026-09-01 后触及 L07–L13 的 430 条提交（hash/date/subject/层集合） | .audit/commits-touching-layers.tsv |
| 机制进出追踪 | 22 个符号 × 7 层的 git log -S 首末提交 | .audit/history-evidence-mechanisms.tsv |
| 静态逐对审计 | 6 对相邻层的 churn/文件增删/README 声称核对/断点 | .audit/deltas.md |
| 正确性实验 | 39 程序 × 7 层 = 273 单元行为矩阵 + 11 套件实测 | .audit/correctness.md、.audit/raw-correctness/ |
| 性能实验 | 跨层同文件/微基准/旧二进制对照/内存 | .audit/perf.md、.audit/raw-perf/ |

**本报告没有做什么（避免误用）**：

- 不评审 L07 相对 L06 的增量（任务范围是 L07~L13）；不评审 LSP/HDL 产品路径的行为（正确性实验用各层 run，L13 不走 prelude/LSP）；
- 性能只测了同文件 corpus + micro 生成器 + 旧二进制量级对照，无 LSP 端到端、无并发/多文件、无峰值 RSS（分配字节 ≠ RSS）；
- 正确性语料 39 个程序是“单文件 + 无 prelude”的极简面，不覆盖 HDL/大语料/多文件；panic/超时只在探针进程内观测（栈溢出仍是进程级）；
- 本文所有行号/机制计数为 HEAD 工作树实测；git 历史中的提交计数/日期以 .audit/history.md 的 git 校验为准；两处“计数口径”差异已随文标注（机制计数 vs 字面量计数；物理行 vs 非空行）。

**先给结论**（证据在后续各节）：

- 这条链**不是“七级台阶”**，而是**多条血统 + 五次再定基/回灌**缝合出来的：L07/L08（decl 表 + σ + Nov 加固）、L09/L10（Infer.global 哨兵再定基，Nov 后又反向回灌 L07/L08 的载体切换/优化）、L11/L12（decl 表 + 宏/canonical，未跟进 Nov 的加固与载体切换）、L13（产品层，update_cxt 精化路线 + 原生 Nat + 命名空间/HDL）。
- 2026-11-10 之后，**优化传播方向反转**：VSpan（L09 的优化）被回灌到 L07/L08（437136b0），载体切换从 L09 回灌到 L10（7a2ebc41），L07 的 P1–P11 加固回灌 L08/L09（602c4188/b453a065/4a819fa6）——结果**“更早的章”拥有“更晚的章”没有的机制**：L07/L08/L09 有 VSpan、深值迭代、MATCH_CMP_BUDGET、P5 环守卫；L10–L12 全都没有。
- **守卫/健壮性只在部分层**：MATCH_CMP_BUDGET 只在 L07/L08/L09；PM_FUEL 只在 L09–L12 孪生；eval_budget/termination 只在 L13。同一程序在不同层的“预算/崩溃行为”不同。
- **精化载体在 L12→L13 换路线**：L07–L12 是 σ 显式替换（Subst/VSub/frcs/SpecSolve），L13 两版回到 update_cxt+refresh；这是全链最大的单点语义断代（L13 README 自认重，且 L13 孪生删掉 subst.rs）。
- **测试链断在 L09**：L07/L08 的 tests.rs（2354/2756 行）+ 三套黑盒（49/53/47 例）在 L09 起消失；L09–L12 只剩 lXX_fast_parity（层内双引擎互检，不验跨层语义）；L13 虽回填 613 个 #[test]，但 legacy_tests 仅回收 L10–L12 的少量用例，L07/L08 用例族基本未回收。
- **实验后果**：正确性上出现“后层拒绝前层接受”的真回归（GADT 跨字段精化 L11/L12 误拒、L09/L10 假 Ok）、以及“同名程序在不同层的重定义/解析/预算行为不同”；性能上 **twin（bump arena）比参考版快 1–2 个数量级**，而参考版之间的差距主要由“顶层声明载体”决定（L10 载体切换后 common 41.0→32.1 ms；L07/L08/L09 因 VSpan 降到 ~50 ms 同水位；L11/L12 未切换，decl-heavy 负载落后 6–8×）。

---

## 2. 七层当前形态（HEAD 实测）

### 2.1 规模（物理行，.audit/layer-cats.tsv）

| 层 | 章节主题（README） | 参考版 | parser | 孪生 | 层内测试 | 合计 | 测试数(#[test]) |
|---|---|---:|---:|---:|---:|---:|---:|
| L07 | 和类型 + 依赖模式匹配（2026-08 重写版） | 6539 / 8 文件 | 1041 / 3 | 9293 / 16 | 2354 / 1 | 19227 / 28 | 70 |
| L08 | 积类型（struct/new 语法糖） | 6601 / 8 | 1110 / 3 | 8981 / 16 | 2756 / 1 | 19448 / 28 | 81 |
| L09 | MLTT 宇宙层（再定基） | 6066 / 8 | 1315 / 3 | 7777 / 15 | 0 | 15158 / 26 | 17 |
| L10 | trait/typeclass | 5904 / 8 | 1501 / 3 | 9568 / 15 | 0 | 16973 / 26 | 26 |
| L11 | 宏 macro_rules + decl 表世界 | 7126 / 8 | 3408 / 4 | 9018 / 15 | 0 | 19552 / 27 | 33 |
| L12 | canonical + Val 级 trait 求解 | 7024 / 9 | 3609 / 4 | 9016 / 14 | 0 | 19649 / 27 | 35 |
| L13 | 命名空间 + 产品层（LSP/HDL/prelude） | 17751 / 10 | 7240 / 5 | 19117 / 19 | 15317 / 25 | 59425 / 59 | 613 |

读法：每层是“参考版（可读性优先，Rc/Box 树 + 递归）+ 孪生 bump arena（性能优先）”两套引擎；twin 恒占 45–50% 行数。L13 的 40% 行数是测试文件（25 个 *_tests/probe 文件）。

### 2.2 语言面（README 声称，逐层增量）

| 层 | 新增语言面 | 备注 |
|---|---|---|
| L07 | enum/GADT、依赖 match、Eq/证明、implicit | 2026-08 从零重写，不是 L06 的 copy |
| L08 | struct/new/投影、多段投影链、struct 模式糖（11-15 才补到 L08–L10） | 核心机零新变体（语法糖） |
| L09 | Type N 分层宇宙、check_universe/check_ctor_wf；去掉 L06–L08 的可变全局/file IO，builtin 只剩 string_concat | 设计性再定基 |
| L10 | trait/impl/outParam/接收者方法、Synth 求解 | 纯增量章（唯一符合 copy-forward 的边界） |
| L11 | macro_rules（解析期展开）、可变全局 builtin 回归、名字世界回 decl 表 | parser 膨胀 +1914 行 |
| L12 | Val 级 trait 求解、Val::Call 内联、canonical iddfs/search、SmolStr | canonical 仅参考版 |
| L13 | package/import/全限定 decl 键、原生 Nat、prim 挂 decl 表、class 两阶段、Call/OpCall、termination/eval_budget、HDL/derive/prelude/LSP 观察面 | 产品层 |

---

## 3. 这条链是怎么“搞乱”的：git 编年史

### 3.1 阶段划分（全史 1756 提交；2026-09-01 后 902 条，其中触层 430、多层 60）

| # | 阶段 | 日期区间 | 提交数 | 代表 commit | 性质 / 后果 |
|---|---|---|---:|---|---|
| P0 | 建层期 | 2025-03-24…2026-05-11 | 208 | L07 d4130900(2025-04-09)、L08 6d106bb7(05-01)、L09 cd41c476(05-08)、L10 83d5e275(05-11)、L11 ab123b49(2025-11-27)、L12 8f3cae69(2026-03-18)、L13 f1392ad4(2026-05-11) | “每章=上一章 copy+新特性”的黄金期；但层与层定基相差 6 个月~1 年，各层起点已不同代 |
| P0b | L13 产品化 + L07/L08 重写 | 2026-05-12…2026-09-02 | 654 | f02d9757(08-21 原生 u64 Nat)、e0e16a11(08-23 PreludePool)、c6b8ee2e(08-29 **L07 重写**)、8988f7ca(09-04 **L08 重写**) | L13 独占 57% 触层提交（LSP/HDL/prelude）；L07/L08 换代为 dpm-nbe 架构，成为后来 11 月“反向回灌”的上游 |
| P1a | 跨层继承审计 + 全链性能同步 | 2026-09-03…09-12 | 243 | 8eff89cf(09-11 R1 6-agent 继承审计)、cac125af(R2)、7f88a556(R3+P13)、70009023/4fa054ae(09-08 全链同步)、fd54399a(env_collect O(d)→O(d)) | 当时链仍可对位：同一改动能无冲突落到 5–7 层（全链同步 9 条） |
| P1b | Rc/pretty 性能轮 | 2026-09-13…09-14 | 38 | 5fc88c84(P1 L07–L09 SumCase/Sum→Rc<Val>)、8101e8c0(P2 L09/L10)、78145fff(P3 L11/L12)、42dcce76(L07/L08) | 4 条核心提交同一时刻 12:26；L07–L09 值表示开始追平 L10 |
| P2a | 精化载体切换：σ 显式替换 | 2026-09-15（单日 24 条） | 24 | ad08c633(L07 06:26)→8931d78a(L08)→ad412abd(L10)→ccfcb87c(L09)→21299758(L11)→58073dd5(L12 14:20) | **同日 8 小时铺到 L07–L12 六层；L13 缺席** → 精化载体永久分叉 |
| P2b | L13 σ 五轮移植失败 | 2026-09-15…09-17（09-23 归档） | 12 | 0adeb57c、49e515c0、4f266a5e、0ad32cd9、ff7cedb7、7c22c0be | 裸语言 65 例 diff=0，但 prelude 21s、深 meta 解链栈溢、GADT 覆盖误报 → master 有意不含补丁（docs/wip/） |
| P2c | 匹配编译器：决策树→逐臂 | 2026-09-18…09-19 | 29 | 4e97743c(L10)、6ae12a63(L11)、45330e64(L12)、448775c2(L13)、09b9ee8d(L09)、c63d2f1d(09-20) | 五层 = **L09–L13**；L07/L08 未参与（本来就是逐臂） |
| P2d | 名字世界/全局名搬迁 | 2026-09-20 | 17 | 866f23e5(L09/L10 全局名搬 Infer + Locals/close_ty Rc 化，strchain 42×/16×)、9a389dd8(不可达臂口径拉齐 L07/L08)、e36b76b2(L08–L13 README) | L09/L10 以 Infer.global 为顶层值家；L07/L08 走 decl 表；两套名字世界并存 |
| P3 | 收尾/归档/模块拆分 | 2026-09-21…10-06 | 168 | c199d210/c29b2a72 等(09-23 **单文件拆目录模块**，全层)、7c22c0be(归档 round3 补丁)、86195126(L13 评审) | 09-23 拆分改变了文件谱系（后续 diff 需按目录对位） |
| P4 | C2 尾任务寄存器化（全链） | 2026-10-07…10-31 | 177 | f627746e=1719292d(10-07 **L02–L13 同款**，12 文件)、10-08 合并冲突 b2c91afb/4057ee87、23f74901(Nat 字面量深度护栏) | 全仓最“全链”的一次同步；L13 仍需 10-08 merge 解冲突（看门狗 × C2） |
| P5 | L07 加固 P1–P11 + 端口回灌 | 2026-11-01…11-10 | 126 | 008f42ed/39538256(11-02 merge L07 加固 20 commits)、c63a6b32(11-08 review 修复轮)、11-10 单日 **88 条** port 批 | P1–P11 只落 L07；L08 仅迁 P9/P2/P1；11-10 把 L07 的 name_map/trail/FxHashMap/in-place decl 回灌 L08/L11/L12；L09/L10 只拿到少量 |
| P6 | carrier switch / VSpan / struct 糖 / 精化 fallback | 2026-11-11…11-15（HEAD） | 60 | 0b03e44a(11-11 L07 Rc 值层)、9da8298a(Tm Rc 负结果回滚)、b453a065(11-12 L09 回灌 P1–P11/struct_eq/quote_deep)、0df5bcbe+437136b0+568c65c5(11-13)、53309604+7a2ebc41(11-14 L10 carrier)、7900b6d5/21bda052/f8a90cc7/b0694c96/57a11c28(11-15) | **L09/L10 是主战场（16/7 条）**；VSpan 只到 L09→L07/L08，L10+ 空；11-15 集中修输出面与精化 fallback |

> 阶段计数自洽：208+654+243+38+24+12+29+17+168+177+126+60 = 1756。

### 3.2 60 条多层提交的方向：优化传播在 2026-11 反转

| 类别 | 条数 | 代表 commit | 后果 |
|---|---:|---|---|
| 纯文档 | 7 | e36b76b2(09-20 L08–L13 README)、7b1268d4、85003c9e、ffe38310 | 只改“声称”，README 与实现的时间差拉大 |
| 全链同步（≥5 层） | 9 | 1719292d/f627746e(10-07 C2)、8eff89cf(09-11 R1)、70009023(09-08)、4fa054ae、fd54399a、79a8bfab | **链仍连续的证据**：同一改动无冲突落到 5–7 层（主要发生在 2026-09/10） |
| 反向回灌（late→early） | 4 | 437136b0(L09 VSpan→L07/L08)、9a389dd8(L09–L13 口径→L07/L08)、35a3734c(L13 口径→L07/L08/L10–L12)、e2d04bb1(L11 隐式逗号→L06–L10) | 早期层开始接收后期层的语义/表示；“每章=上层+特性”不再成立 |
| 正向增补（early→late） | 6 | 85b9c87e(L07 Rc<Tm>→L08/L09)、8a53662e(L07/L08 Entry.hk→L10–L12)、370fb3f4(L07 decl 表 Rc→L08)、57a11c28(L08 walk_con→L09–L12) | 2026-09 后 L07/L08 成为“上游” |
| 配对层（恰好 2 层） | 19 | L07/L08 4 条、L09/L10 6 条、L11/L12 9 条 | 实际工作单元是**配对**：L07/L08、L09/L10、L11/L12 各自成对演进；跨对只在 09-10 出现 2 条 |
| 其他 3–4 层/跨对 | 15 | 5fc88c84(L07–L09 Rc)、b7b4225a(L08,L10)、fd25b740(L07,L09)、dbe79cf2(L10–L12 PM_FUEL)、b510a8c0(L07–L10 bench fuel) | “同一优化的不同完成度裁剪版”，最容易产生半移植 |

**方向判读**：2026-09 是“L07/L08 重写 → 正向移植到 L09–L12”；2026-11-10 之后是“L07/L08/L09/L10 互相回灌 + L11/L12 被落下”，同时 L13 一直独立演进（567 条提交、占全史 32%）。

### 3.3 机制首次/末次落地（git log -S 摘要；完整表见 .audit/history-evidence-mechanisms.tsv）

| 机制 | 各层首次引入 | 断点 |
|---|---|---|
| VSpan（Val 名字 span 句柄） | L09 0df5bcbe(11-13 19:36) → L07/L08 437136b0(同日) | L10–L13 从未引入；到齐时间差 0 天，跨层永断 |
| σ 显式替换（Subst/VSub/frcs/SpecSolve） | L07 ad08c633、L08 8931d78a、L10 ad412abd、L09 ccfcb87c、L11 21299758、L12 58073dd5 —— **全部 2026-09-15 06:26→14:20** | L13 从未有（五轮移植失败）；L07–L12 内部 VSub 计数 139/128/85/65/71/62 递减 |
| update_cxt（旧精化载体） | L09 2025-10-12、L10 2025-10-26、L11 2025-11-27、L12 2026-03-18、L13 2026-05-11 | L07/L08 于 2026-08-29/09-04 重写后**没有**该机制；L09–L12 保留旧载体注释/残迹；L13 活代码 |
| 1919810 哨兵 / Infer.global | L09/L10 2025-05 起；L11/L12 于 2026-09-11 d82006a5 基本清除 | L07/L08 重写后 0；L09/L10 26/26；L11/L12 1/1；L13 0 |
| Val::Decl | L07 c6b8ee2e(08-29)、L08 8988f7ca(09-04)；L11 2026-01-11、L12 2026-03-18、L13 2026-05-11 | **L10 = 0**（唯一没有该变体的层），L11/L12 24/28，L13 61 |
| MATCH_CMP_BUDGET | L07 40845701(10-31) → L08 c63a6b32(11-08) → L09 b453a065(11-12) | L10–L13 从未有 |
| PM_FUEL | L09 ccfcb87c、L10–L12 dbe79cf2（均 09-15） | L07/L08、L13 从未有（它们不走 σ 精化循环） |
| UNIFY_FUEL | L07 08-29 → L08 09-04 → L10–L13 8eff89cf 09-11 → L09 ccfcb87c 09-15 | 全层都有，但**到齐顺序与链序无关**（L10–L13 比 L09 早 4 天） |
| Val::Nat / PreludePool | 仅 L13：f02d9757(08-21)、e0e16a11(08-23) | 产品层专属，未回灌 |
| 隐式参数打印 [] | L07/L08/L13 一直 []；L09–L12 用 {} 直到 11-15 f8a90cc7/b0694c96 | 输出面漂移跨 2026-09~11 整个期间 |

### 3.4 撤销 / 负结果 / 未合并分支（与本链有关的）

- **N1 Tm 整枚举 Box→Rc 回滚**（9da8298a，11-11）：natadd −22.8%/church −41.1%，但 strchain k10 +24%、k11 +27% → 整 commit 回退；11-13 04e222e8 继承的是 L08 的“Lam 体/Pi 域 Rc”局部表示，不是同一改动。
- **N2 L13 σ 显式替换五轮移植失败**（docs/wip/，09-15~09-17，09-23 归档）：裸语言 65 例 diff=0，但 prelude 21s、深 meta 解链栈溢、GADT 覆盖误报 non-exhaustive → **master 有意不含补丁**；L13 因此永久保留旧精化载体。
- **N3 L13 求值器优化多为负结果**（docs/l13-perf-review-4.md）：eval 记忆化、Sum 臂记忆化（命中率 3.7%）、Nat prim 层等实现后整体撤销；L13 性能主要靠 LSP 表总闸/池化等工程项。
- **未合并分支**：perf/l13-twin-sigma（3 ahead：L13 孪生 σ 局部成功，未合入）、task/l13-backport3（8 ahead：含 2026-08-14 就已修过的隐式 [] 打印，11-15 才在 master 重做）、task/l13-bugs2（5 ahead：lvl2ix 下溢等修复延迟 6 周才落地）、analysis/l04-l07-perf（3 ahead）。
- **仓库卫生**：旧审计基线 8443586e **不在 master 上**（不被任何分支包含；master 有同内容孪生 5be479cd）；master 存在重复 merge（008f42ed 与 39538256）与孤儿同内容提交（c63a6b32 vs 6bd1926e）；本地 3 套 remote（origin/https-origin/ssh-origin）分支名重复。


---

## 4. 相邻层实现差异（pairwise delta，摘要）

完整逐对审计（README 声称核对、文件级/符号级差异、断点清单、工程残留）见 .audit/deltas.md；此处只给“每对到底改了什么、链是否连续”。

### 4.1 六对增量一张表（churn 来自 git diff --no-index -M --numstat，见 .audit/deltas-data/）

| 对 | 净行(churn) | 文件增删 | 真增量（标题内） | 偷带/回退（标题外，重点） | 链是否连续 |
|---|---:|---|---|---|---|
| L07→L08 | −25 | 0/0 | struct/new/多段投影链、类型级 .mk 剥链、参考版 unify 补 (Obj,Obj) 臂、struct 模式糖（11-15 补） | **反向动作**：L08 参考版 2026-11-12 以 L07 HEAD 整层重建（602c4188），把 P1–P11 加固/深值轮带入；L08 不再是 L07 的纯 copy，而是“L07 最新版 + 积类型” | 连续（但方向由纯前向变为前向+回灌） |
| L08→L09 | −4219 | −4/+1（twin/debug.rs） | MLTT 宇宙层（Type N、check_universe、check_ctor_wf） | **再定基**：删 tests.rs(2756)/struct_eq.rs(373)/twin/struct_eq.rs(297)/twin/prim.rs(381)；名字世界换 Infer.global+1919810 哨兵；builtin 15→1（去掉可变全局/file IO）；11-12 又把 P11 等加固补回参考版（b453a065） | **不连续**（设计性换基 + 测试断崖） |
| L09→L10 | +1742 | +2/−2 | trait/impl/outParam/接收者方法 + Synth 求解；参考版全面 Rc<Val> | 删 L09 的 struct_eq.rs/twin/debug.rs；**MATCH_CMP_BUDGET、P5 meta_expanding、quote_deep/rename_deep、VSpan、MAX_DEPTH 全部未移植**；11-14 只补了载体切换（7a2ebc41）与 close_meta_ty，没补守卫 | 功能连续、**机制断代** |
| L10→L11 | +2525 | +1/0 | macro_rules（解析期展开，parser/macros.rs 358 行）+ 可变全局 builtin 回归 + 名字世界回 decl 表（Val::Decl）+ Arc 化 | 名字世界第三次换基（哨兵→decl 表）；parser 同时塞入错误恢复/手写优先级/SPINE_ESCAPE/Verilog 兼容 token（+1914 行）；**struct 模式糖 L11 本来就有，反而 L08–L10 是 11-15 才补回** | **不连续**（第二次换基） |
| L11→L12 | +163 | +1/−1（twin/typeclass.rs） | Val 级 trait 求解（去 Typ 桥）、Val::Call 内联节点、canonical iddfs/search（仅参考版）、SmolStr | 孪生删 typeclass.rs（求解器并入 machine.rs，L13 又拆出 1030 行）；canonical 只有参考版；嵌套覆盖/精化行为在 L11/L12 间有细节漂移（11-15 用 walk_con fallback 部分修补） | 基本连续（共 26 个 rs 只有 1 个未变） |
| L12→L13 | +39807 | +33/−1（twin/subst.rs） | 命名空间（package/import/全限定 decl 键/五级解析）、原生 Nat、prim 挂 decl 表、class 两阶段、Call/OpCall、termination/eval_budget、HDL/derive/prelude/LSP 观察面 | **σ→update_cxt 换路线（两版）**、孪生删 subst.rs、VSpan/struct_eq/MATCH_CMP_BUDGET 全无、canonical 仅参考版、+25 个测试文件“一次性回填” | **不连续**（最大断点：机制/测试/产品面全分叉） |

### 4.2 每对“标题以外”最重的 2–3 条

| 对 | 标题说的是 | 标题没说的 |
|---|---|---|
| L07→L08 | 积类型 | ① L08 参考版 11-12 被 L07 HEAD 整体覆盖重建，导致“后章依赖前章的最新修复”这种逆时序；② L08 孪生没有同步这轮加固（606 行对位差异），两版健壮性不同步。 |
| L08→L09 | MLTT 宇宙层 | ① 删 tests.rs(2018–2756 行) 后 L09–L12 再无等价层内单测；② builtin 体系从 15 个收缩到 string_concat 一个（可变全局/文件 IO 消失，L11 才回来）；③ 名字身份从“名字键”改为“大下标哨兵”，构造子解析绕道 infer_expr(Var)。 |
| L09→L10 | trait/typeclass | ① 参考版全签名 Rc<Val> 重构，改动量大于 trait 本身（Rc<Val> 12→81）；② 删 struct_eq 与 MATCH_CMP_BUDGET 后，卡住 match 的相等性比较既无快路径也无总预算；③ 孪生 machine.rs +2120/−534 里相当一部分是 typeclass 求解。 |
| L10→L11 | 宏 | ① 名字世界第二次换基（哨兵→decl 表），同名重定义/构造子解析语义随之改变；② parser +1914 行中宏只是小头，大头是错误恢复/手写优先级/括号摊平/Verilog 兼容；③ 孪生 machine.rs −1462，求解器改用共享 typeclass 模块。 |
| L11→L12 | canonical | ① canonical 只在参考版，孪生无 iddfs/retry；② twin/typeclass.rs 模块消失（L13 又回来）；③ 参考版 cxt.rs 618→464，孪生侧 decl 载体/Rc 共享继续调整。 |
| L12→L13 | 命名空间/产品化 | ① 精化载体整体回退到 update_cxt+refresh（两版），σ 只在 L07–L12 存活；② 24 个测试文件 +15k 行一次性回填，但 L07/L08 的用例族未回收；③ 同一层内参考版（eval_budget/canonical）与孪生版（compact/observe/termination/prim）各有一批对方没有的机制。 |


---

## 5. 跨层机制断点总账

### 5.1 机制 × 层矩阵（参考版代码命中；孪生版在括号内）

| 机制（代码命中；括号内为孪生） | L07 | L08 | L09 | L10 | L11 | L12 | L13 | 读法 |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| VSpan（Val 名字 span 句柄） | 35 | 35 | 34 | 0 | 0 | 0 | 0 | 11-13 由 L09 回灌 L07/L08；L10+ 从未有 |
| Rc<Val>（整机共享值） | 11 | 11 | 12 | 81 | 105 | 123 | 258 | L10 起整体 Rc 化；L13 最重 |
| Val::Decl（名字键 decl 表） | 30 | 30 | 0 | 0 | 19 | 23 | 40 | L09/L10 撤表，L11 回来，L13 全限定 |
| 1919810 哨兵 / Infer.global | 0 | 0 | 14/9 | 14/9 | 0 | 0 | 0 | 只 L09/L10；（孪生 1/7 同） |
| struct Subst（σ 载体） | 1 | 1 | 1 | 1 | 1 | 1 | 0 | L07–L12 有，L13 无 |
| VSub | 41 | 41 | 24 | 16 | 16 | 14 | 0 | 同上，L09 起逐层递减 |
| frcs | 10 | 10 | 10 | 10 | 10 | 11 | 0 | 同上 |
| SpecSolve | 9 | 9 | 14 | 9 | 10 | 8 | 0 | 同上 |
| update_cxt（旧精化载体） | 0 | 0 | 0 | 0 | 0 | 0 | 7 | 只 L13（孪生 9）；与 σ 互斥 |
| struct_eq（结构相等快路径） | 18 | 18 | 8 | 0 | 0 | 0 | 0 | L09 只剩参考版；L10+ 无模块 |
| MATCH_CMP_BUDGET=64 | 3 | 3 | 3 | 0 | 0 | 0 | 0 | 只 L07–L09 参考版（L07/L08 孪生 2） |
| meta_expanding（P5 跨 meta 环守卫） | 6 | 6 | 6 | 0 | 0 | 0 | 0 | 只 L07–L09 参考版 |
| quote_deep / rename_deep | 4/4 | 4/4 | 4/4 | 0 | 0 | 0 | 0 | 深值迭代化只 L07–L09 参考版 |
| MAX_DEPTH（pretty 定深） | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 同上 |
| PM_FUEL（精化展开燃料） | 0 | 0 | (4) | (5) | (4) | (4) | 0 | 只 L09–L12 **孪生**；L07/L08/L13 无 |
| PendingNode（两段式模式方程） | 0 | 0 | 0 | 0 | 4 | 0 | 0 | 只 L11；11-15 fallback 用别名覆盖其他层 |
| Val::Call | 0 | 0 | 0 | 0 | 0 | 13 | 33 | L12 引入，L13 扩到 OpCall |
| Val::Nat(u64) 原生 Nat | 0 | 0 | 0 | 0 | 0 | 0 | 64 | 只 L13 |
| eval_budget | 0 | 0 | 0 | 0 | 0 | 0 | 30 | 只 L13 参考版（孪生 8） |
| termination 检查 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | 只 L13（两版） |
| canonical iddfs | 0 | 0 | 0 | 0 | 0 | 2 | 2 | L12+ 参考版 |
| redefine 检查 | 2 | 2 | 2 | 8 | 1 | 1 | 1 | 所有参考版都有；L09/L10 于 2026-11-13 继承 |
| 层内测试文件（tests.rs 等） | 1 | 1 | 0 | 0 | 0 | 0 | 25 | 测试链断在 L09 |


### 5.2 断点总表（按严重度）

| 严重度 | 断点 | 证据/锚点 | 后果 |
|---|---|---|---|
| P0 语义 | 精化载体 L07–L12 = σ（Subst/VSub/frcs/SpecSolve）→ L13 = update_cxt 返回精化后 Cxt；孪生 subst.rs 被删 | L12 mod.rs:306、cxt.rs:418 vs L13 cxt.rs:1327、pattern_match.rs:534；机制矩阵 σ 14→0 | L13 的 GADT/依赖匹配精化路线与 L07–L12 不同；同一精化程序在 L12/L13 走不同代码路径，ref/twin 的旧载体 CoW 成本也不同 |
| P0 语义 | 名字世界三段：decl 表（L07/L08）→ Infer.global+1919810 哨兵（L09/L10）→ decl 表（L11/L12）→ 全限定键（L13） | L09 mod.rs:636；L11 mod.rs:22；L13 mod.rs:432 | 同名重定义、构造子解析、名字遮蔽/歧义行为逐段不同；跨层对照程序必须限定在公共语法子集 |
| P1 守卫 | MATCH_CMP_BUDGET=64 只在 L07/L08（+L09 参考版 11-12 回灌）；L10+ 双版 0 | L07 mod.rs:641、L08 mod.rs:554、L09 mod.rs:608 | 卡住 match 的相等性比较在 L10+ 没有总预算，最坏情况靠 UNIFY_FUEL/超时兜底 |
| P1 守卫 | P5 meta_expanding 环守卫、quote_deep/rename_deep、MAX_DEPTH 只在 L07–L09 参考版 | L07/L08/L09 mod.rs/pretty.rs 锚点见 .audit/mechanism-matrix-code.tsv | 深值/跨 meta 环在 L10–L13 可能退化为递归栈溢出或长栈；L09 孪生本身也没移植（单层内两版不一致） |
| P1 守卫 | PM_FUEL 只在 L09–L12 孪生；L13 改成 eval_budget/termination | L09–L12 twin/force.rs 等；L13 eval_budget.rs:72/77、twin/termination.rs | 防护口径四代并存：L07/L08 调用级预算、L09–L12 孪生 thread_local 燃料、L13 协作式看门狗 + 终止检查 |
| P2 优化不回灌 | VSpan 只在 L07/L08/L09 参考版；L10+ 0 | L09 mod.rs:190；437136b0 | L10–L13 的 Val 名字 span 仍按 String 克隆；L13 的 Rc<Val> 258 处放大拷贝面（但 L13 是新产品层，不排除有意取舍） |
| P2 优化不回灌 | struct_eq 模块只在 L07（373 行）/L08（188）/L09（373，11-12 补）；L10+ 无 | 文件谱系 .audit/layer-files.tsv；L10 README 自述“无该分节” | 结构相等回落到 unify 常规路径；卡住 match 深比较没有 EqTask 迭代实现 |
| P2 优化不回灌 | L11/L12 未做“顶层声明移出 Cxt”的载体切换（L09 568c65c5、L10 7a2ebc41 已做） | .audit/vspan 文档 + 本报告§8 实测：L10 common 31.9ms，L11 57.2/L12 47.7（全流程口径） | L11/L12 参考版在 decl 多（ladder_large 798 decls）负载上落后 L10 1.5–1.9×；twin 因 bump arena 不受影响（~17ms 全层同水位） |
| P3 测试丢失 | L09 删 tests.rs(2756)、twin/prim.rs(381)、twin/struct_eq.rs(297)；L10 删 struct_eq.rs、twin/debug.rs；L12 删 twin/typeclass.rs | 层路径 git history 为空=从未移植；.audit/deltas.md §7 | L09–L12 只有 lXX_fast_parity（层内双引擎一致），没有任何跨层语义回归；11-15 才新增 tests/gadt_refine_cross_layer_tests.rs 一个跨层钉子 |
| P3 测试丢失 | 黑盒套件止于 L08（l07_blackbox×3、l08_blackbox×2），L09–L12 无黑盒 | tests/ 清单 | L09–L12 的语言面/错误信息/深值行为没有黑盒级守卫 |
| P4 文档失真 | L09 README 锚点漂移 14/34 行（elaboration.rs:246/567→260/601）；L10 README 50–90 行（mod.rs:448→498、elaboration.rs:624-633→692-701、:1003→1093）；L13 README 123–181 行（mod.rs:309→432、:724-733→905）且最后更新 2026-09-20 | .audit/deltas.md §0.8/§7 | 文档不能直接引用行号；README 的性能数字普遍过期 |
| P4 工程残留 | L13 eprintln 66 / println 280 / #[ignore] 4 / FIXME 10 / TODO 23；L09 twin/debug.rs 只活一层；.bak 文件被 .gitignore 隐藏（L11 13 个 + L12 4 个） | .audit/deltas.md §7；FACTS.md §7.9 | 产品层日志噪声与维护成本；.bak 可能在不知情时被误用 |


---

## 6. 实验一：同一程序在 L07–L13 上的行为矩阵（正确性）

### 6.1 实验方法

- 语料：39 个小程序 × 7 层 = 273 个单元（v1 34 + v2 定向追加 5：显式 `refl` 两版复现 prim 分裂、`macro_stringify`/`trait_outparam` 语料修正、L12 隐式打印单点探针）。程序覆盖 CORE(11)/STRUCT(6)/UNIVERSE(3)/TRAIT(4)/MACRO(4)/SEMANTIC(5)/L13 面(1)。
- 被测对象：各层**参考版** `run(input, 0)`（LSP 产品路径不在此实验内）；每次调用在 256MB 栈线程里，`catch_unwind` 捕 panic，`recv_timeout` 防挂（20s）。
- 判定：Ok 记去空白文本 hash；Err 记粗类别；Panic/Timeout 单列。矩阵原始数据 `.audit/raw-correctness/probe-matrix.tsv`（273 行，v2 终版）、语料 `.audit/raw-correctness/probe-programs.tsv`、运行日志 `probe-run2.log`。v2 对 prim 分裂用“显式 `refl` 构造子两种写法”复测，分布与 v1 完全一致（排除写法因素）。
- **重要分层契约**（否则会把特性门误读成 bug）：L07/L08 的 parse 失败返回 Err；L09–L13 的恢复式 parser 把解析错误 `println!` 到 stdout、继续检查已解析前缀、最终 **Ok**（L13 部分路径 eprintln）。因此“该层不支持某语法”在 L09–L13 可能显示为 Ok+部分输出（见 F5）。
- 另用 `realbench --validate` / `l13bench --file --with-prelude none` 对最小复现做跨层复核（可直接重跑）。

### 6.2 主结果：有跨层分歧的程序（其余程序见附录 B 全矩阵）

表注：单元格 = 该层结果；`O:xxxxxx` = Ok 且文本 hash 前 6 位（同 hash 即逐字节同输出）；`E` = Err；`P` = Panic；`—` = 特性门（min_layer 之前）。

| 程序（组） | L07 | L08 | L09 | L10 | L11 | L12 | L13 | 判读 |
|---|---|---|---|---|---|---|---|---|
| core_nat_add（CORE） | O:87d4ef | O:87d4ef | O:87d4ef | O:87d4ef | O:87d4ef | **O:f248ae** | O:f248ae | 显示契约分层：L12 起 Nat 十进制打印（`4` vs succ 链） |
| core_gadt_head（CORE） | O:953c1d | O:953c1d | O:953c1d | O:953c1d | O:953c1d | **O:fc6647** | O:fc6647 | 同上（`0` vs `Nat::zero`） |
| core_vec_len_proj（CORE） | O:87d4ef | O:87d4ef | O:87d4ef | O:87d4ef | O:87d4ef | **E** | O:f248ae | **L12 真回归**：enum 索引参数投影 `t.len` 在 L12 被拒（最小复现见 §6.4） |
| core_implicit_print（CORE） | O:6a52ba | O:6a52ba | O:fdd391 | O:fdd391 | O:6f5361 | **E** | O:3de25e | 显示分层（空格 vs 逗号 vs 头隐式实参）+ L12 Err（v2 未最小化：单点 nil/cons/标注探针在 L12 均 Ok，可能同 R2 根因或独立） |
| core_stuck_prim（CORE） | O:595e9d | O:595e9d | O:820d38 | O:820d38 | O:820d38 | O:820d38 | O:20b6ad | 卡住 prim 的打印/载体分层（L07/L08 vs L09–L12 vs L13） |
| core_ctor_eta（CORE） | O:7ab47b | O:7ab47b | O:7ab47b | O:7ab47b | O:7ab47b | **O:d42b98** | O:d42b98 | L12 起 η 显示 `x => x + 1`（L07–L11 `x => Nat::succ(x)`） |
| core_stuck_match（CORE） | O:ca6f72 | O:ca6f72 | O:464752 | O:464752 | O:464752 | O:ea8b14 | O:ea8b14 | 卡住 match 渲染分层：`(unsolved match n)` → L12 起 `f(n)` |
| struct_proj_new（STRUCT） | — | O:893500 | O:49e283 | O:49e283 | O:49e283 | O:3320af | O:3320af | struct 投影/打印分层（L09–L11 与 L12+ 十进制） |
| struct_weak03（STRUCT） | — | O:fae565 | O:eca8d4 | O:eca8d4 | O:eca8d4 | O:4c6a68 | O:4c6a68 | 均给出**具体值**（非卡住）：`Fin::fzero([Nat::zero])` / `(Nat::zero)` / `(0)` 分层 |
| struct_weak05（STRUCT） | — | O:953c1d | O:953c1d | O:953c1d | O:953c1d | O:fc6647 | O:fc6647 | 全 Ok（11-15 fallback 生效），输出分层同 Nat 打印 |
| macro_decl_level（MACRO） | E | E | **O:8e1fd4** | **O:8e1fd4** | O:3ab631 | O:3ab631 | O:3ab631 | L09/L10 的 Ok 是“恢复式 parser 吃掉宏 + 部分输出”的伪 Ok（特性门，不是支持宏） |
| prim_identity_bad（SEMANTIC） | E | E | E | E | **O:30406e** | **O:30406e** | E | **L11/L12 假阳性（不健全）**：不同实参的卡住 prim 被 Eq 判等；其余层正确拒绝 |
| prim_identity_ctrl（SEMANTIC） | **E** | **E** | **P** | **P** | **P** | **P** | O:30406e | **同一程序跨层四态**：L07/L08 误拒（假阴性，根因是 unify 缺 literal 臂，见 F1 注）；L09–L12 `Option::unwrap None` **panic**；只有 L13 正确 |
| redefine_ctor（SEMANTIC） | E | E | E | E | E | E | **O:fc6647** | L13 允许 `def succ : Nat` 撞构造子裸名（命名空间语义：构造子只登记限定名，见 §6.5），L07–L12 拒绝 |
| l13_package（L13 面） | E | E | O:8441e1 | O:8441e1 | O:8441e1 | O:be9d18 | O:cca2b9 | L09–L12 的 Ok 同样是解析错误被吃掉后的伪 Ok；特性门不可用 Ok/Err 判 |

其余程序（core_poly_id、core_illtyped_app、core_missing_case、core_unreachable_arm、struct_simple、struct_weak02_err、struct_weak04_err、univ_levels、univ_illtyped、univ_struct_high、trait_tostring、trait_blanket、trait_no_instance、macro_module、macro_depth_guard、match_cmp_stuck、redefine_def）在 ≥min_layer 上判定一致（Ok 同输出或 Err），无跨层分歧。

**v2 语料修正后的补充**：`macro_stringify` 在补 Nat 定义后 L11–L13 一致 Ok（此前 L11/L12 的 Err 是语料缺 `succ` 定义）；`trait_outparam` 在补 `def outParam` 存根后 L10–L13 Ok（L10/L11 succ 链、L12/L13 十进制）——两处均为探针语料缺陷，已从风险清单剔除。

### 6.3 关键发现

**F1（最严重，健全性/稳定性）：卡住 prim 的相等判定在四段血统里四态**
- `prim_identity_bad`（不同实参的 `string_concat`，语义上**不应**可证）：L11/L12 返回 Ok（假阳性、不健全）；L07/L08/L09/L10/L13 拒绝。
- `prim_identity_ctrl`（相同实参，语义上**应该**可证）：只有 L13 Ok；L07/L08 Err（假阴性）；L09–L12 **panic**（`Option::unwrap()` on `None`，锚点：src/L09_mltt/mod.rs:1185、src/L10_typeclass/mod.rs:1012、src/L11_macro/cxt.rs:100、src/L12_canonical/cxt.rs:85；v2 用显式 `refl` 两种构造子写法复测，分布完全一致）。
- **注：L07/L08 的假阴根因不是 prim 表示**。L07/L08 在 2026-11-10（`0971ad2e`/`77be5d06`）已迁到与 L13 同构的“decl 表条目挂 `Option<PrimFunc>`”模型，prim 相等按 `Val::Decl(name, spine)` 比较；失败来自 **unify 缺少 `(LiteralIntro, LiteralIntro)` 相等臂**——`Eq[String] "ab" "ab"` 同样被拒，而变量实参的 `Eq[String] (string_concat x y) (string_concat x y)` 通过（实测 `.audit/primprobe2/`、`.audit/primprobe3/`）。L13 在 `unification.rs:1135` 有该臂，所以通过。。
- 根因：各层 prim 载体不同——L07/L08 是 decl 表 `Val::Decl(name, spine)`（实参保留，unification.rs:1068 同名比 spine）；L09/L10 是单元 `Val::Prim`（无实参，且无 `(Prim,Prim)` 臂）；L11/L12 是 `Val::Prim(typ, PrimFunc)`（无应用实参，且 unification.rs:715-716/766-767 用 `(_,Prim(b,_)) => unify(t,b)` 把任意两 prim 判等）；L13 是 decl 表 + `PrimFunc(&[args])`（实参保留）。
- 影响：这不是“特性门”，是同一合法程序在不同层被接受/拒绝/崩溃；LSP 产品层 L13 自身正确，但任何以 L09–L12 为参考 oracle 的跨层测试都会误判。

> **2026-11-16 修复（L07/L08）**：参考版与孪生版已补 `(LiteralIntro, LiteralIntro)` 合一臂（`src/L07_sum_type/unification.rs`、`src/L07_sum_type/bump_spine_iter/unify.rs` 及 L08 同两处），并新增 2 个单测 + parity 语料；验证结果：`prim_identity_ctrl` 在 L07/L08 从 Err 变 **PASS**，`prim_identity_bad` 仍正确拒绝，L07 lib 72 / L08 lib 83 / l07 parity 99 / l08 parity 118 全绿。L09–L12 的 prim 载体迁移与 literal 臂已于同日第二轮完成（L09/L10 改为“名字+实参 spine”，L11/L12 改为 args 版 PrimFunc+spine），并顺带修复 L12 孪生 force 的一个既有潜在 bug，详见**附录 C**。

**F2（真回归）：L12 拒绝 enum 索引参数投影**
- 最小复现（独立复核，非仅 probe）：
  `enum Vec2(len: Nat) { nil2 -> Vec2 zero  cons2[l: Nat](x: Nat, xs: Vec2 l) -> Vec2 (succ l) }` + `def t2 = cons2 two (cons2 two nil2)` + `println t2.len`
  → `realbench --validate`：L07/L08/L09/L10/L11 **PASS**，L12 **SKIP(ref_run_err: can't unify expected (x: ?5) → ?6 x, find: Nat)**，L13 PASS；去掉隐式参数同样复现；纯隐式 enum 无索引投影不复现。
- 因此触发条件 = **enum 索引参数投影（`t.len`）**，与 L11 的 SPINE_ESCAPE/隐式参数无关；是 L11→L12 边界的真回归（L12 的 elaboration 侧待定位，列入风险清单）。

**F3（11-15 修复有效）：struct 模式糖与跨字段精化**
- `Name { .. }` 模式糖：L07 无 struct（特性门）；L08–L13 全部 Ok；ill-typed weak02/weak04 全层正确拒绝；weak03/weak05 输出具体值（`Fin::fzero(...)` / `Nat::zero` / `0`），无假 Ok。与 `tests/gadt_refine_cross_layer_tests.rs` 声称一致。
- 断点在 L08 rebase（602c4188）/L09、L10 再定基时丢糖，2026-11-15 的 7900b6d5/21bda052 补回；L11/L12/L13 本来就有。

**F4：redefine 检查其实全链都在，但 L13 的“裸名构造子”语义不同**
- `redefine_def`：L07–L13 全 Err（正确）。`redefine_ctor`（`def succ : Nat` 撞构造子裸名）：L07–L12 Err，L13 Ok——因为 L13 构造子只登记限定名 `Nat.succ`，裸名不占用（cxt.rs:1243 fake_bind 与之配合）；这是 L13 命名空间的**有意语义**，需在跨层对照中当 feature gate，而不是回归。
- 文档漂移：L09/L10 的 `bump_spine_iter.rs:45/66` 仍写“参考版无 redefine 检查”，是 2026-11-13 之前的旧状态。

**F5：恢复式 parser 的伪 Ok 是跨层对照的陷阱**
- 同一“L13 才支持”的程序（l13_package、macro_decl_level）在 L09–L12 返回 Ok + 部分输出（如 `?1`/Nat succ 串），而不是 Err；若跨层测试只比较 Ok/Err，会把“不支持”误判成“支持但输出不同”。任何跨层 harness 必须按层区分 parse 错误契约（§6.1）。

**F6：显示/诊断分层（不是正确性 bug，但会让“逐字节一致”类断言误报）**
- 构造子打印：L07/L08 空格分隔；L09–L11 逗号 + `Typ::case`；L11 起带隐式头 `List[A]::nil`；L12 起 Nat 十进制、η 显示、卡住 match 显示 `f(n)`；L13 同 L12。
- 隐式参数 `[]` 已在 HEAD 统一（2026-11-15 修复），7 层都打印 `[A]`。

**F7：预算/守卫缺失目前只在静态层面**
- `match_cmp_stuck` 在 7 层都是 Err、无 Timeout（该形态未触发 L10+ 缺 `MATCH_CMP_BUDGET` 的无界路径）；`meta_expanding` 环守卫缺失（L10–L13）与 `quote_deep`/`rename_deep` 缺失只能登记为**尾部风险**，未构造出可复现的挂死/栈溢出负载。

**F8：探针语料两处修正（v2 已修正并重跑，结论已更新）**
- `macro_stringify` 补 Nat 定义后 L11–L13 一致 Ok；`trait_outparam` 补 `def outParam` 存根后 L10–L13 Ok（两者此前 Err 是语料缺陷，不是实现分歧）。

### 6.4 正确性风险清单（按严重度）

| 严重度 | 风险 | 层/锚点 | 建议 |
|---|---|---|---|
| P0 | 卡住 prim 相等判定四态：L11/L12 假阳性、L07/L08 假阴性（根因是缺 literal 臂，prim 表示正确）、L09–L12 在相同实参时 panic | 见 F1；probe prim_identity_*；L07 实测 `.audit/primprobe*` | **2026-11-16 已全部落地**：L07/L08 补 literal 臂；L09/L10 改为“名字+实参 spine”；L11/L12 改为 args 版 PrimFunc+spine 并删除假阳臂；panic 点随 env-slot 模型移除。见附录 C |
| P0 | L12 拒绝 enum 索引投影 `t.len`（L07–L11/L13 接受） | F2；realbench 复核 | 定位 L12 elaboration 的索引投影路径；在 `tests/l12_fast_parity.rs` 之外加跨层回归 |
| P1 | L10–L13 缺 `MATCH_CMP_BUDGET`/`meta_expanding`/深值迭代；L07–L12 缺 eval 看门狗 | §5.1 矩阵 | 要么回灌守卫，要么在 README 写明“不设防”并给测试上限 |
| P1 | L13 与 L12 的精化载体分叉（σ vs update_cxt）导致的 GADT 行为差异未系统对照 | §5.1；gadt 测试 84 passed 只覆盖已钉形态 | 建立“L12/L13 精化行为差异”语料；L13 的 struct_refine_probe 已知弱点保持单独跟踪 |
| P2 | L09–L12 的 parse 错误契约（println + partial Ok）使黑盒/跨层测试易误判 | F5 | 跨层 harness 按层归一化；或给 L09–L13 的 run 加“strict parse”测试入口 |
| P2 | 输出/诊断分层（构造子格式、Nat 十进制、卡住 match 渲染、twin span 全零） | F6 | 跨层断言只比语义类别，不比逐字节；逐字节只在同层 ref/twin（且归一化 span/meta 编号） |

### 6.5 补充：为什么 L13 的 redefine_ctor 是“有意语义”而不是 bug（静态证据）

L13 的构造子只登记全限定名（`Enum.case`），不设裸名别名（elaboration.rs enum 臂；README §1.1），因此 `def succ : Nat` 不撞任何已登记裸名；L07–L12 的构造子按裸名登记（L09/L10 走 `Cxt::define` env 槽），所以撞名。两者都与各自名字世界自洽。跨层对照程序若依赖“构造子裸名”，应视为 L13 的 feature gate。


---

## 7. 实验二：现有测试/parity 套件在 HEAD 的真实状态

实验 B：在 HEAD 上真实执行现有测试套件（cargo test --release，`--test-threads=1`，逐套件日志 `.audit/raw-correctness/suite-*.log`、汇总 `suite-summary.csv`）。

### 7.1 通过情况（HEAD 实测）

| 套件 | 通过/失败 | 说明 |
|---|---|---|
| tests/gadt_refine_cross_layer_tests | **84 / 0** | 2026-11-15 新增的跨层 GADT 精化钉子；含 L09/L10/L11 的 `#[path]` 内嵌单测，故 84 > 文件内 8 个显式用例。**全绿**：11-15 的 walk_con fallback 修复了 weak03/weak05 的跨层分歧 |
| tests/l07_fast_parity | **97 / 0** | 层内参考版↔孪生 |
| tests/l09_fast_parity | **46 / 0** | 层内 |
| tests/l10_fast_parity | **47 / 0** | 层内 |
| tests/l11_fast_parity | **52 / 0** | 层内 |
| tests/l12_fast_parity | **50 / 0** | 层内 |
| tests/l13_fast_parity | **630 / 0（6 ignored）** | 层内 + L13 层内 unit tests；耗时 213.6s |
| tests/backport3_pretty_l0910 / backport3_pretty_tests | **48 / 0、76 / 0** | 2026-11-15 隐式打印修复的专用回归套件 |
| tests/known_bug_pins / p0_known_bug_pins | **8 / 0、2 / 0** | L13 产品路径已知 bug 钉子 |
| **合计（11 套件）** | **1140 passed / 0 failed / 6 ignored** | 全部跑完、无未跑套件；bench 未计入 |

静态用例数（`#[test]` 计数，供对照）：gadt 8 个显式 + 内嵌、l07 27、l09 29、l10 21、l11 19、l12 15、l13 15、backport3_pretty_l0910 5、backport3_pretty_tests 8。

### 7.2 这张表说明了什么

1. **层内 parity 全绿 ≠ 正确性**：parity 的判据是“同层参考版与孪生版 Ok 输出逐字节一致 / Err 判定一致”。它无法发现两版**同错**的问题——例如 L11/L12 的 prim 相等判定假阳性（参考版和孪生版走同构的 `(_, Prim(b,_)) => unify(t,b)` 臂），parity 自然全绿；L12 的索引投影回归也只在**跨层**对照（L11 Ok / L12 Err）时才暴露。
2. **bench 自带闸门反而抓到了 parity 缺口**：性能实验的 165 次 bench 进程里有 **12 次 exit=101**，全部是 bench 内建的正确性闸门 panic——L10 `enum`（`l10bench.rs:289` nf 节点数 ref=28/twin=6）、L11 `enum`（`l11bench.rs:314` 两版全流程输出不一致）、L12 `enum` + `traitchain`（`l12bench.rs:272` fast check+nf 未通过）。这些缺口在 `lXX_fast_parity` 里没有对应用例（语料未触达），说明 **parity 套件的语料覆盖也是断的**。
3. **测试密度与层序倒挂**：L07/L08 各 70/81 个层内测试 + 3/2 套黑盒；L09–L12 只有 17/26/33/35 个内联测试，没有 tests.rs、没有黑盒；L13 有 613 个测试但主要是产品面（namespace/hover/completion/HDL），L07/L08 的语义用例族只回收了个位数。**越靠后的“中间章”测试越薄**。
4. **11-15 的两个修复有专用回归**：gadt 跨层 84、backport3_pretty 系列（48+76 全绿），说明最近的“补链”动作开始补测试；但 L09–L12 仍缺“上一层 tests.rs 迁移”这类系统性回填。

### 7.3 建议的门禁改造

- 把 `tests/audit_crosslayer_probe.rs`（本报告实验 A）保留为常驻跨层门禁：对每个程序，后层必须与“语义基线层”判定一致（feature gate 白名单显式登记）；
- 每层至少恢复 `.audit` 里被删的 tests.rs 用例族（或迁移到 `tests/lXX_semantics.rs`）；
- parity 判据升级：除 Ok 输出/Err 判定外，增加“深值/环/超时”三类鲁棒性 smoke（可用 L07 的 P1–P11 用例族做模板），否则两版同错永远绿灯。


---

## 8. 实验三：跨层性能（同文件 / 微基准 / 参考版 vs 孪生）

实验 C：在当前 HEAD 重测 L07–L13 的性能。原始日志 `.audit/raw-perf/`（351 个进程日志 + 索引 + 汇总 tsv），方法见 `.audit/raw-perf/PREP.md`：单进程串行、每配置 3 pass（bench 内部 rounds=3 取 min/median）、跨 pass 取 median-of-medians、层序奇偶反转。**污染声明**：02:27 起 correctness-lab 的 cargo 编译/测试与 memmin/l13min 重叠；memmin 是确定性分配计数不受影响，l13min 只取 ref/twin 比值；old 阶段因预 P0 的 L10 traitchain >240s 被中止（保留 p1 全部+p2 部分）。

### 8.1 主表：strict 同文件跨层（tools/bench_corpus/common，6 文件；ms）

这是唯一“同文件同语义”的跨层口径（各层 micro 生成器不同，不能直接横比）。basic = 参考版；L11/L12 的 basic 是**全流程**口径（含 preprocess+parse+pretty+println），其余层 parse 在计时外。

| 口径 | L07 | L08 | L09 | L10 | L11* | L12* | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 参考版 TOTAL（basic） | 53.05 | 53.21 | 52.47 | **31.92** | 57.20 | 47.75 | **65.90** |
| 相对 L07 | 1.00× | 1.00× | 0.99× | **0.60×** | 1.08× | 0.90× | **1.24×** |
| ladder_large（798 decls）basic | 51.49 | 49.67 | 48.83 | **29.97** | 52.59 | 44.23 | **60.46** |
| 孪生 TOTAL（fast_ss） | 18.20 | **16.99** | 18.63 | 17.49 | 17.28 | **16.88** | 19.03 |
| 孪生 ladder_large | 17.12 | **16.27** | 18.42 | 18.37 | 17.85 | 17.51 | **16.86** |

**结论 1：参考版不再随章节单调**。L10（trait 章）在同文件上最快（31.9 ms，0.60× L07），L13（产品层）最慢（65.9 ms），L07/L08/L09 三个“早期章”在 VSpan+载体切换后收敛到 52–53 ms。
**结论 2：孪生版跨层几乎收敛**。7 层孪生 TOTAL 16.9–19.0 ms（极差 ≤12%），798-decl 单文件 16.3–18.4 ms——bump arena + 迭代内核把“章节差异/载体差异”基本抹平。**跨层性能差异主要来自参考版引擎**。

### 8.2 载体切换/优化回灌的量化效果（与旧文档同机对照）

| 变化 | 前 | 后 | 效果 | 证据 |
|---|---:|---:|---|---|
| L09 载体切换（568c65c5） | common 113.5 ms（11-12） | 52.5 ms（本次） | **−54%**；11-12 时 L09 是最慢层（1.69× L07），现在与 L07/L08 同水位 | docs/bench-crosslayer-ref-2026-11-12 §2 vs 本表 |
| L10 载体切换（7a2ebc41） | common 41.7/41.0 ms（11-12/11-13） | 31.9 ms | **−22~−24%**；Eq 阶梯单文件 1078.9→2.1 ms（L10 文档） | docs/l10-carrier-switch-2026-11-14 |
| L07/L08 继承 VSpan（437136b0） | common 69.0/69.0 ms（11-12） | 53.0/53.2 ms | **−23%**；与 11-13 VSpan 文档的 −26%/−21% 同量级 | docs/bench-crosslayer-vspan-2026-11-13 |
| L11/L12 未做载体切换 | — | — | microbasic 强制 basic（k=11）的 D 轴：strchain 27.6*/28.0* vs L09/L10 8.8/7.6；struct 40.7*/31.9* vs 11.3/8.2；universe 18.8*/19.5* vs 4.4/4.9 | .audit/raw-perf/summary-microbasic.tsv |

**结论 3**：2026-11 的三次回灌（L09 carrier、L10 carrier、VSpan→L07/L08）都有明确收益；但收益只落在被回灌的层，**L11/L12 的参考版没有拿到任何一项**——它们的 decl-heavy 参考版比 L09/L10 慢 1.5–3×（同文件 TOTAL 47.7*/57.2* vs 31.9；microbasic D 轴 27.6*/28.0* vs 7.6–8.8）。L11/L12 的孪生版不受影响（同文件 16.9–17.3 ms）。

### 8.3 微基准（各层自家生成器；只用于层内 ref/twin 与形态，不跨层横比）

- 孪生 fast_ss（k=11，ms）：church L07–L12 0.257–0.272 / L13 0.488；strchain L07 7.58 / L08–L12 3.50–4.46 / L13 9.83；struct L08–L12 4.22–5.08 / L13 12.11；universe L09–L12 1.87–2.14 / L13 4.30；match L07–L12 ~0.05 / L13 0.165；**traitchain L10 631.8** / L11 64.9 / L13 76.4；enum（k=9）L07 0.071 / L08 0.082 / L09 0.120 / L13 0.285。
- **twin 不是恒快**：L10 的 traitchain 孪生 631.8 ms vs 参考版 113.5 ms（k=11，twin 慢 5.6×，且随 k 超线性：k=9 40 ms → k=10 152 ms → k=11 632 ms）。这与 L10 参考版 2026-09 修复的 `close_tm_reduced`（fresh_meta 的 O(n²) close）同族，但孪生侧未同步修复；是“孪生总更快”结论的直接反例，也让 perf-lab 在 12/165 个 bench 进程里触发内建闸门 panic（L10/L11/L12 enum、L12 traitchain）。
- L13 孪生在 match（3.3×）、enum（4.0×）、struct（2.7×）、macro（2.6×）、strchain（2.7×）上明显慢于 L11/L12，但 natadd 最快；与 L13 孪生分配次数（church 5,583 vs L07 241）同向。

### 8.4 旧二进制对照（L10/L11/L12 2026-09-18 vs HEAD，量级参考，非受控 A/B）

- L10 `l10bench_old`：universe basic 1309.49 → 5.86 ms（**223.6×**）、match 0.308 → 0.094 ms（3.28×）、church 2.692 → 1.417 ms（1.90×）、twin church 0.509 → 0.280 ms（1.82×）——载体切换的 9 月→11 月总效果。
- 旧 L10 traitchain 单配置 >240 s（预 P0 的 O(D²/³) 灾难，本次被中止）；当前 HEAD 的 L10 孪生仍 631.8 ms（§8.3 反例）。
- L11/L12 的 old 对照（p1 完成、p2 部分）显示：9 月→11 月的回灌（name_map/trail、decl Rc、缓存容量归还等）在 micro 层有 1.1–2× 的局部收益；因非受控且 n=1–2，报告只作方向参考（raw: `.audit/raw-perf/summary-old.tsv`）。

### 8.5 怎么读这些数字（避免三类误读）

1. **不要跨层比 basic 绝对值**：L11/L12 的 basic 含 parse+pretty+println，L07–L10/L13 不含；同文件表已用 * 标注。若只看“谁快”的结论，用孪生轴（严格同口径）或同文件 basic 的 L07–L10/L13 子集。
2. **不要用各层 micro 生成器横比**：church/strchain/struct 的源在各层 `bench_src` 里是“同族不同文”，k 与节点数约定也不同；micro 只回答“同层 ref vs twin”和“形态/规模趋势”。
3. **不要把“章更后”当“实现更新”**：本章 §3 的编年史显示优化传播是网状的；性能曲线上的拐点对应的是 commit（VSpan/carrier switch），不是章节序号。

### 8.6 性能侧的断点与影响（对应 §5.2 / §10）

| 断点 | 性能后果 | 证据 |
|---|---|---|
| L11/L12 未做 carrier switch | 参考版 D 轴落后 L09/L10 1.5–3×；同文件 TOTAL 47.7*/57.2* vs 31.9 | §8.1/§8.2；docs/l09-carrier-switch、docs/l10-carrier-switch |
| VSpan 未回灌 L10–L13 | L10–L12 参考版名字 span 仍 String 克隆；L13 的 Rc<Val> 放大拷贝面（但 L13 有产品层其他成本，无法单因子分离） | §5.1；VSpan 文档 −23~−26% 仅在 L07/L08 可观测 |
| PM_FUEL 只在 L09–L12 孪生 | 孪生精化展开有界，参考版无；对性能影响未测（只在极端精化负载上体现） | §5.1 |
| L10 孪生 traitchain 超线性 | trait 负载上 twin 反而 5.6× 慢于参考版；修 close/COW 家族可解 | §8.3 |
| L13 产品层重（State 变大、prelude/prelude 相关机制） | 同文件 ref 65.9 ms / twin 19.0 ms 全场最慢；micro 小负载 2.6–4× | §8.1/§8.3；l06l13mem sizes（Tycker 2536 vs L07 512；Machine 1568 vs 488） |


---

## 9. 实验四：内存与工程健康度（可选）

实验 D（轻量）：分配/内存口径。工具 `target/release/l06l13mem.exe`（确定性 `GlobalAlloc` 计数，不受 CPU 竞争影响）；原始日志 `.audit/raw-perf/logs/memmin-*.log`、`--sizes` 输出。

### 9.1 分配次数/字节（twins；church & strchain k=11，one-shot）

| 指标 | L07 | L09 | L10 | L11 | L13 |
|---|---:|---:|---:|---:|---:|
| church fast one-shot allocs | 241 | 93 | 94 | 120 | **5,583** |
| church fast bytes | 1.59 MiB | 1.58 | 1.58 | 1.58 | 1.57 |
| church basic（参考版）allocs | 44,300 | 44,763 | 49,129 | 54,192 | 67,905 |
| strchain fast one-shot allocs | 45,092 | **50** | **50** | 8,228 | 94,989 |
| strchain fast bytes | 18.52 MiB | 16.08 | 16.08 | 16.17 | 24.80 |
| strchain basic allocs | 176,452 | 237,594 | 225,319 | **393,405** | 422,074 |
| strchain basic bytes | 42.54 MiB | 44.64 | 44.93 | **67.72** | 62.71 |

读法：
1. **孪生版分配趋同**：church 各层 1.66 MB 完全一致；strchain 除 L13（25.3 MB）外 16.9–19.4 MB；L09/L10 的 strchain allocs 只有 50 次（arena 一次性 4 chunk），L07 45k 次是因为其孪生 bench 口径不同（每轮重建）——这些是 harness/arena 策略差异，不是语义。
2. **参考版载体差异可见**：同一 strchain，L07 basic 176k allocs/42.5 MiB → L11 **393k allocs/67.7 MiB**（+2.23× allocs / +1.59× bytes）、L13 422k/62.7 MiB。L11/L12 的 decl 表在 Cxt 里做写时复制（`Rc::make_mut`）是主要来源；这与 §8 的 D 轴参考版性能差一致。
3. **L13 产品层更大**：strchain 孪生 parse 分配 49,215 次/23.6 MB（其他层 94k/16.3 MB，字节反更多是因为 L13 的 AST/prelude 表结构）；L13 的 `Tycker` 2536 B / `Machine` 1568 B，是 L07（512/488）的 3–5 倍，`MetaEntry` 40 B vs 24 B；`DeclEntryF` 在 L09+ 变成扁平 `&[V]`（无条目结构体），L13 用 7 元组 decl 条目。
4. **twin 与 ref 的分配比**：church basic/fast 字节比 1.80–3.51×；strchain 2.65–4.21×；allocs 比 12–5,000×（L09 strchain：237,594 vs 50，因为 twin 的 arena 一次性分配）。**性能对比必须同轴**（§8.5）。

### 9.2 内存/状态结构（`--sizes`，字节）

| 结构 | L06 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Tm | 48 | 56 | 56 | 56 | 56 | 56 | 56 | 56 |
| V（打包值） | 8 | 8 | 8 | 8 | 8 | 8 | 8 | 8 |
| EnvCons | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 |
| CloCell / PiCell | 48/56 同左 | → | → | → | → | → | → | → |
| MetaEntry | 24 | 24 | 24 | 24 | 24 | 24 | 24 | **40** |
| Machine | 536 | 488 | 536 | 512 | 752 | 720 | 736 | **1568** |
| Tycker | 560 | 512 | 560 | 536 | 776 | 744 | 760 | **2536** |

结论：**孪生版的“值单元大小”七层一致（V=8B、Tm=56B、EnvCons=16B）**，说明 bump arena 表示已收敛；差异在“引擎状态对象”（Machine/Tycker：L10 起变大，L13 最大 3–5×）与“条目结构”（L13 MetaEntry 40B、decl 七元组）。参考版的内存差异则由 §9.1 的分配次数体现（载体/值表示），不是单值大小。

### 9.3 局限

- 只测了 church/strchain 两个负载的分配；struct/trait/macro 的分配特征未测（时间让路给正确性实验）。
- `l06l13mem` 的“basic”列是各层参考版口径，但 L11/L12 的 basic 与 bench 口径不同（全流程），因此只作“同层 ref/twin 比值”读。
- 峰值 RSS 未测（需要 mem-profile feature 重建，且 Windows 口径与分配计数不可直接换算）；分配字节数 ≠ 峰值内存。


---

## 10. 影响归因：哪类差异造成什么后果

把“实现差异”按影响归类，而不是按章节归类：

| # | 差异类别 | 代表机制（锚点/证据） | 正确性影响 | 性能影响 | 证据 |
|---|---|---|---|---|---|
| A1 | **精化载体路线分叉**：L07–L12 用 σ 显式替换，L13 用 update_cxt+refresh（孪生删 subst.rs） | Subst/VSub/frcs/SpecSolve（L07–L12，L13=0）；update_cxt 只在 L13 活代码（cxt.rs:1327） | 同一 GADT/依赖匹配程序在 L12 与 L13 走不同精化路径；L13 的已知精化弱点（docs/pattern-match-refinement-analysis.md）与 L07–L12 不同；L13 README 自认 refresh 更重 | L13 嵌套 match 深负载的精化传播比 σ 路线重；σ 路线在 L07–L12 的读点推开（frcs）设计更省，但只在 L07–L12 参考版生效 | §2 表、§5.1、.audit/deltas.md §6；L13 README §6.8 |
| A2 | **名字世界三段切换**：decl 表（L07/L08/L11/L12）→ Infer.global+1919810 哨兵（L09/L10）→ 全限定键（L13） | Val::Decl 30/30/0/0/19/23/40；哨兵 0/0/14/14/0/0/0；Infer.global 0/0/9/9/0/0/0 | 同名重定义、构造子解析（裸名 vs 限定名）、名字遮蔽/歧义行为逐段不同；L10 是唯一没有 Val::Decl 的后层（跨层对照程序可能表现不同）；redefine 检查虽各层都有，但“检查什么名字”随名字世界而变 | 载体直接决定参考版性能：顶层声明压进 Cxt 时全局引用 O(D)、fresh_meta O(D²)（11-12 切换前实测 L09 strchain 61.7ms vs L07 7.8ms；L10 载体切换后 common 41.0→32.1ms、Eq 阶梯 1078.9→2.1ms）；L11/L12 未切换，decl-heavy 负载落后 L10 1.5–1.9×（同文件 TOTAL 57.2/47.7* vs 31.9） | §3、§5.1、§8；docs/l09-carrier-switch-2026-11-12.md、docs/l10-carrier-switch-2026-11-14.md |
| A3 | **单侧优化/回灌**：VSpan 只到 L07/L08/L09；Rc<Val> 从 L10 起整机；Rc<Tm> 局部只在 L08+/L09 | VSpan 35/35/34/0/0/0/0；Rc<Val> 11/11/12/81/105/123/258 | 表示层优化原则上不改判定；但 Rc 共享改变 clone 语义边界（是否有别名副作用由代码审计保证，跨层无等价性测试） | VSpan 让 L07/L08 同文件 −25%（69.0→51.1ms，11-13 实测）；Rc<Val> 让 L10 在 common 上快 1.65×（31.9 vs 52.5）；L11/L12 两头都缺 → 参考版最慢组 | §5.1、§8；docs/bench-crosslayer-vspan-2026-11-13.md |
| A4 | **守卫/预算覆盖差**：MATCH_CMP_BUDGET、P5 meta_expanding、quote_deep/rename_deep、MAX_DEPTH 只在 L07–L09 参考版；PM_FUEL 只在 L09–L12 孪生；eval_budget/termination 只在 L13 | 矩阵 §5.1；L10 的 unify(Match,Match) 无预算（unification.rs:691-751） | L10–L13 的“卡住 match 相等比较”没有总预算、跨 meta 环没有守卫 → 合法但极端的程序可能长时间挂起或栈溢出（本报告只对 match_cmp_stuck 做了探针；P5 未构造）；L07–L12 没有 eval 看门狗，循环求值只能靠人工中断 | 守卫本身有成本（L08 加固后 match −3~11%），但缺失时的最坏情况是时间无界；这类差异在基准负载上通常不可见，属于“尾部风险差异” | §5.1、§6.2；BACKPORT-2026-11-11 §2 |
| A5 | **测试链断在 L09**：L07/L08 tests.rs+黑盒，L09–L12 只有层内 parity，L13 一次性回填 | 层内 #[test] 70/81/17/26/33/35/613；tests/ 黑盒止于 L08 | 这是“为什么同一 bug 能潜伏到 11-15”的直接原因：L09–L12 没有跨层语义回归，parity 只保证“同层两版一致”，两版同错（如单行 enum 假阴性）会全绿；11-15 才补 gadt 跨层钉子 | 无直接性能影响；但意味着任何优化回灌都缺少“语义不变”自动门禁 | §7；L13 README §6.2/§7；旧 DELTA §2.3 |
| A6 | **参考版 ↔ 孪生不对称**：twin-only（PM_FUEL L09–L12、compact/observe/termination L13）vs ref-only（VSpan/struct_eq/deep quote L07–L09、eval_budget/canonical L13） | §5.1 矩阵；L10 traitchain 孪生 631.8ms vs 参考版 113.5ms（k=11，twin 反而慢 5.6×，超线性） | parity 判据只比 Ok 输出/Err 判定 → 鲁棒性（深值/环/超时）与诊断差异不可见；bench 自带闸门已暴露 L10/L11/L12 enum 与 L12 traitchain 的 twin 分叉（12/165 进程 exit=101） | 同文件 basic/fast_ss 比 1.8–3.5×；micro 各负载 1.0–6.8×；twin 不是恒快（L10 traitchain 反例），说明“bump arena 万能”不成立 | §8；.audit/raw-perf/summary-micro.tsv |
| A7 | **输出/诊断漂移**：隐式打印 [] 到 11-15 才统一；SumCase 显示格式 L08 空格 vs L09+ 逗号分层；twin 错误 span 全零；parse 错误契约 L07/L08 Err vs L09+ println+Ok(前缀) | §6.2–§6.5；f8a90cc7/b0694c96；L08 README §A4-R2 | 输出面差异会让“Ok 逐字节一致”类测试误报/漏报；parse 错误契约差异会让跨层 harness 把特性门误判成回归 | 无 | §6、§7 |
| A8 | **文档/工程卫生**：README 锚点漂移 14–181 行；旧审计基线 8443586e 不在 master；重复 merge/孤儿提交；3 套 remote；.bak 17 个；L13 eprintln 66/println 280 | §3.4、§5.2、.audit/deltas.md §7 | 引用文档行号会指错；新人/agent 会基于过期 README 做出错误判断 | 文档中的性能数字普遍过期（09-20/11-12 基线），直接用会得到错误结论 | §3.4、§5.2 |


---

## 11. 建议（若要收拾这条链）

### 11.1 正确性优先（小改动、高收益）

1. **统一卡住 prim 的相等语义**（真实健全性分裂，最小可复现）：L09/L10 的单元 `Val::Prim` 无 `(Prim,Prim)` 臂 → 相同实参的卡住 prim 等式也 Err，且 env-slot prim 体会 `unwrap` panic；L11/L12 用 `(_,Prim(b,_)) | (Prim(a,_),_) => unify(...)` 把任意两个卡住 prim 判等（假阳性）。L07/L08/L13 的 decl 表 prim 保留实参、按 spine 比较是正确的；L07/L08 的 ctrl 失败是**另一件事**——unify 缺 `(LiteralIntro,LiteralIntro)` 臂（L13 unification.rs:1135 有），补上即可。**2026-11-16 已按此执行**：L07/L08 补 literal 臂；L09/L10 改成“名字+实参 spine”（等价于 L07 的 args 保持模型，无需 decl 表）；L11/L12 改成 args 版 PrimFunc+spine 并删除假阳臂；新增 `tests/prim_identity_cross_layer.rs` 常驻门禁（5 程序 × 7 层）。详见附录 C。
2. **收口 L11/L12 的跨字段精化**：11-15 的 walk_con fallback 已把 weak03/weak05 拉回与 L08/L13 一致（实验结果为准）；若仍有误拒，优先移植 L13 的 `already_refined` 传播/9-29 精化重做，而不是再加一层 fallback。
3. **明确精化载体路线**：L13 产品层保留 `update_cxt` 是已定的产品决策（σ 五轮失败），但应停止在文档/模块头里声称“继承 L05–L12 全部机制”；在 L13 与 L12 之间建立“精化行为差异”对照表（哪些程序在 L12/L13 结果不同），并把 L13 的精化弱点文档化。
4. **补齐或登记守卫**：MATCH_CMP_BUDGET / P5 / 深值迭代在 L10–L13 缺失。若判定“这些层不会触发卡住比较/深值”，请在每层 README 写明理由；否则把 L07 的实现回灌（L09 已证明可适配），并加 deep-value/cyclic-meta 回归钉子。
5. **L10 孪生 traitchain 超线性（631.8ms @k11，参考版 113.5ms）**：这是 twin 侧的 O(n²) 回归（与 L10 参考版 close_tm_reduced 修复同族），应单独立项定位；否则“孪生更快”的基准结论在 trait 负载上反例成立。

### 11.2 结构优先（决定这条链还要不要维护）

6. **先定“这条链到底是什么”**：当前事实是“三条血统（L07/L08、L09/L10、L11/L12）+ L13 产品层”。若目标是教学章节，最省力的修复是**把 L11/L12 重定基到 L10**（L10 已有 carrier switch + Rc<Val>，L11/L12 在此之上加宏/canonical，改动量可控）；然后一次性把 L07→L10 的加固/守卫/VSpan 对齐。若目标是“保留每层独立可运行”，则应把“层间差异矩阵 + 每层已知偏离”作为正式产物维护，而不是继续假装 copy-forward。
7. **停止对 L13 的 copy-forward 期待**：L13 是产品层（LSP/HDL/prelude），与 L07–L12 的“章节”定位不同；L13 与 L12 的差异分析应按“产品化增量 + 两条机制分叉”来写，而不是按“章节增量”。
8. **性能门禁改成同文件口径**：各层自家 micro 生成器不同，跨层数字不可直接比。用 `tools/bench_corpus/common/`（6 文件，含 798-decl 阶梯）作为跨层性能主表；micro 只用于层内 ref/twin。把本次 §8 的表作为基线（HEAD 2026-11-16）。

### 11.3 工程与测试（防止再次失控）

9. **测试门禁**：保留 `tests/audit_crosslayer_probe.rs`（39 程序 × 7 层），把它作为跨层语义门禁；再加一条“后层必须接受前层语料”的 corpus 回归（允许显式 feature gate 白名单）。L09–L12 至少恢复被删的 tests.rs 用例族（或迁移到 tests/）。
10. **文档自动化**：每层 README 增加固定小节“相对上一章：新增/删除/弱化/守卫变化”；测试数、行数、性能数字改为脚本生成，禁止手写；锚点行号禁止写死（或 CI 检查漂移）。
11. **仓库卫生**：清理 .bak（L11 13 个 + L12 4 个）、根目录 prof/dhat/flamegraph 残留、L13 调试打印与 #[ignore]；统一 3 套 remote；修掉重复 merge/孤儿提交（008f42ed/39538256、c63a6b32/6bd1926e）；旧审计文档以 master 的 5be479cd 对齐而不是 8443586e。
12. **长期方向**：16 万行 × 双引擎的复制维护成本已经出现“单侧修复、另一侧漂移”的系统性问题（本报告 A4/A5/A6）。若要长期维护这个 zoo，应抽公共 crate（parser/pretty/preprocess/Synth/bench harness）+ 每层 feature 化，把“层差异”变成配置而不是复制。


---

## 附录 A. 复现命令

```powershell
# 0) 构建（HEAD）
cargo build --release --bins

# 1) git 编年史/机制追踪（只读）
git rev-list --count HEAD
git log --since=2026-09-01 --date=short --pretty=format:'@@%h|%ad|%s' --name-only -- src/L07_sum_type src/L08_product_type src/L09_mltt src/L10_typeclass src/L11_macro src/L12_canonical src/L13_namespace
git log -S'VSpan' --format='%h|%ad|%s' --date=short -- src/L09_mltt
# 本报告底稿：& .audit/build-matrix.ps1 ; & .audit/build-timeline.ps1 ; & .audit/build-code-matrix.ps1

# 2) 正确性实验 A：39 程序 × 7 层（tests/audit_crosslayer_probe.rs 由 correctness-lab 新增）
cargo test --release --test audit_crosslayer_probe -- --nocapture --test-threads=1
#    产出 .audit/raw-correctness/probe-matrix.tsv / probe-programs.tsv

# 3) 正确性实验 B：现有套件（HEAD 全绿）
pwsh -NoProfile -File .audit/raw-correctness/run-suites.ps1

# 4) L12 索引投影最小复现（跨层对照；文件在 .audit/tmpcorpus*/）
target/release/realbench.exe --layer L11 --corpus .audit\tmpcorpus --validate   # PASS
target/release/realbench.exe --layer L12 --corpus .audit\tmpcorpus --validate   # SKIP: ref_run_err (can't unify ... find: Nat)
target/release/l13bench.exe --file .audit\tmpcorpus\d_idxproj.typort --with-prelude none --rounds 1

# 5) 性能实验 C：strict 同文件跨层
target/release/realbench.exe --layer L07 --corpus tools\bench_corpus\common --rounds 3 --only basic,fast_ss   # L07..L12
target/release/l13bench.exe --file tools\bench_corpus\common\ladder_l07_large.typort --with-prelude none --rounds 3
# micro: target/release/lXXbench.exe --workload <church|stratchain|match|enum|struct|universe> --max-k 11 --rounds 3
# 完整驱动：.audit/raw-perf/run-perf.ps1（micro/samefile/microbasic/old/memmin/l13min）

# 6) 内存/分配：target/release/l06l13mem.exe --sizes ; --chapter L11 --workload church,strchain --k 11 --rounds 1
```


## 附录 B. 证据文件索引

| 路径 | 内容 |
|---|---|
| docs/l07-l13-implementation-audit-2026-11-16.md | 本报告（正式交付） |
| .audit/mechanism-matrix-code.tsv | 30 机制 × 7 层代码命中（参考版/孪生分开，剔注释） |
| .audit/layer-files.tsv、.audit/layer-cats.tsv | 文件/行数/分类（ref/parser/twin/test） |
| .audit/commits-touching-layers.tsv | 2026-09 后 430 条触层提交（层集合/文件数） |
| .audit/history.md、.audit/history-evidence-mechanisms.tsv | git 编年史（阶段/方向/机制首末/负结果/分支） |
| .audit/deltas.md、.audit/deltas-data/*.numstat.tsv | 6 对相邻层的静态差异审计（396 行） |
| .audit/correctness.md | 正确性实验全文（方法/静态机制/矩阵/风险） |
| .audit/raw-correctness/probe-programs.tsv、probe-matrix.tsv | 39 程序原文与 273 单元结果（v2 终版） |
| .audit/raw-correctness/suite-summary.csv、suite-*.log | 11 个套件逐套件实测结果（1140 passed / 0 failed / 6 ignored） |
| .audit/perf.md、.audit/raw-perf/ | 性能实验全文 + 351 个进程日志/索引/汇总 |
| .audit/raw-perf/_perf-part1..3.md | 性能报告分部草稿（含 micro/microbasic/old/mem 原始表） |
| tests/audit_crosslayer_probe.rs | 本报告实验 A 的常驻 harness（新增；建议保留为跨层门禁） |
| docs/compare-l07-l13/DELTA.md | 旧审计（2026-11-08 时点；基线 8443586e 是 master 之外的孤儿提交，master 内同内容为 5be479cd） |
| docs/bench-crosslayer-ref-2026-11-12.md、docs/bench-crosslayer-vspan-2026-11-13.md、docs/l09-carrier-switch-2026-11-12.md、docs/l10-carrier-switch-2026-11-14.md | 本报告 §8 对照的历史基准/载体文档 |

---

## 附录 C. 2026-11-16 prim 载体迁移记录（L09–L12，改造后状态）

> 正文 §6/§6.4/§11.1 记录的是当天上午的审计结论（当时 L09–L12 仍是 L06 式 env 槽 prim）。同日第二轮已完成迁移并验证；本附录是正文的后续状态，引用正文结论时以本附录为准。

### C.1 改造内容

| 层 | 参考版 | 孪生版 |
|---|---|---|
| L09/L10 | `Tm::Prim(SmolStr)` / `Val::Prim(SmolStr, Spine)`；builtin 注册值 = 单个中性 Prim 头（**不再构造 λ 链、不再读 env 槽**）；eval 产中性头、`v_app` 收 spine、`force` 先 force 实参再调本层 `prim_reduce(name, args)`；quote/rename/struct_eq/pretty/frcs/`mentions_level`/unify 全部改为“名字+实参 spine”；新增/收窄 `(LiteralIntro,LiteralIntro)` 自反臂 | `XCell::Prim(&str)` / `CTm::Prim(&str)` 携带名字；新增 `HK_PRIM` 链头种类与 `prim_head_name`，`bump_spine_iter/prim.rs` 提供 string_concat 归约；machine 的 builtin 初始化改为单 Prim 头；force/quote/rename/unify/spine/subst/debug 同步；v_app 对 Prim 头压栈而不再 panic |
| L11/L12 | `PrimFunc` 改为 args 版 `Rc<dyn Fn(&Infer,&Decl,&[Rc<Val>]) -> Option<Rc<Val>> + Send+Sync>`（去掉 `&Env`、返回 Option）；`Val::Prim(typ, PrimFunc, Spine)`；builtin 注册值 = 中性 Prim 头；cxt.rs 的 prim 函数由 `env.iter().nth(k).unwrap()` 改为 `args.get(k)`；**删除** unify 的“任意 Prim 判等 / 按携带 typ 剥离”假阳臂，改为同身份（同名或同 `Rc`）+ 逐 spine；补 literal 自反臂 | `XCell::Prim { typ, pid }` 保留 `PrimId` 身份但改为中性头 + spine；“任意 Prim 判等/typ 剥离”臂删除；v_app 压栈不再 panic；`prim_exec(pid, args)` 由 eval 的 env 版分支改成 args 版；quote/rename/unify/frcs/mentions 同步 |

公共：四层 ref+twin 均加 `(LiteralIntro, LiteralIntro)` 自反臂（L13 `unification.rs:1135` 同款）；新增 `tests/prim_identity_cross_layer.rs`（5 程序 × 7 层，参考版）作为常驻门禁；各层 `tests/lXX_fast_parity.rs` 增加 prim 钉子（literal 自反、prim 正控 Ok、prim 负例 Err、部分应用 no-panic）。

### C.2 顺带修复的既有 bug（L12 孪生）

`src/L12_canonical/bump_spine_iter/force.rs` 的未解 flex 链臂原为 `MetaEntry::Unsolved(v, _, _) => return *v`——把 `MetaEntry` 里存的**闭类型**当值返回（`?m x` 被 force 成其 Π 型），导致 `prim_identity_ctrl` 在 L12 twin Err。该行在 HEAD 即存在（修复前 `git show HEAD:src/L12_canonical/bump_spine_iter/force.rs` 可核），属既有潜在 bug，只是此前被 unify 的 Prim typ 剥离假阳臂掩盖。修复为 `Unsolved(_, _, _) => return v`（与 L11 孪生同款），`l12_fast_parity` 由 53 passed/2 ignored 变为 **55 passed / 0 failed / 0 ignored**。

### C.3 改造后门禁矩阵（HEAD + 本轮改动，实测）

| 门禁 | 结果 |
|---|---|
| `cargo test --release --test l07_fast_parity` | 99 passed / 0 failed / 0 ignored |
| `l08_fast_parity` | 118 / 0 / 0 |
| `l09_fast_parity` | 47 / 0 / 0 |
| `l10_fast_parity` | 48 / 0 / 0 |
| `l11_fast_parity` | 56 / 0 / 0 |
| `l12_fast_parity` | 55 / 0 / 0 |
| `l13_fast_parity` | 630 / 0 / 6 ignored（L13 未改） |
| `l07_blackbox` / `l08_blackbox` / `l09_blackbox` | 48+1 ignored / 57+1 ignored / 82，全部 0 failed |
| `tests/prim_identity_cross_layer` | 77 passed / 0 failed（5 程序 × 7 层 ref 语义） |
| `tests/audit_crosslayer_probe` | 273 单元矩阵：`prim_identity_bad`/`bad_rfl` 7 层全 Err；`prim_identity_ctrl`/`ctrl_rfl` 7 层全 Ok；`core_stuck_prim` 不再 panic |
| `realbench --layer L07..L12 --corpus .audit/primprobe4 --validate` | 六层全部 pass=1 skip=1（ctrl PASS / bad SKIP） |
| `cargo build --release --bins` | Finished，0 error |

### C.4 行为面变化与口径

1. **有意变化**：L09–L12 的部分应用 builtin 显示从 `y => Prim Func`（实参丢失）变为实际调用形态（`string_concat <实参>`）；`primprobe4`/`core_stuck_prim` 的 hash 因此变化，受影响的 L09 golden 与 L09 blackbox 期望已同步更新。
2. **诊断差异保留**：ref/twin 在 prim 负例上的 Err 文案顺序（find/expected）与零宽空格等仍按各自 pretty 血统，判定一致；parity 判据仍为“Ok 逐字节 / Err 判定一致”。
3. **未扩展**：L12 twin 仍只注册 5 个 builtin（ref 6 个，`change_mutable_default` 为既有分叉）；本次未补，不影响 prim 语义门禁。
4. **性能影响未测**：本次只做语义/载体改造，未重跑 §8 的性能矩阵；按设计，L09–L12 参考版在 prim 热路径上省掉了 env 槽读取与 λ 链求值，预期不劣于旧实现，但需后续基准确认。


