# L07–L13 实现差异与优劣：七层 elaboration zoo 的横向解剖

> 对象：工作树 HEAD `8443586e`（master，2026-11-08）。范围：`src/L07_sum_type` … `src/L13_namespace`
> 七层"独立完整实现"（每层含参考版 + bump 孪生版两套引擎）。
> 方法：只读静态分析（源码 + 文档 + git 历史）；**未运行任何 cargo/bench**（F 盘剩余空间不足 1 GB，
> 构建会写数 GB；这是本仓长期存在的环境约束）。性能数字均转引 `docs/bench-matrix-2026-09-20.md`
> 等文档并逐条标注时效：**09-20 之后 L07/L08 有 11-08 加固、L09/L10 有 866f23e5 性能修复、L12 删了
> 一个 eprintln 回归、L13 σ 迁移实验未落地**——所有 09-20 数字只代表当时状态。
> 分报告：`L07.md`–`L13.md`（逐层）、`CROSS.md`（横切）、`FACTS.md`（可核对事实底稿）、`VERIFY.md`（对抗核查）。
> 标注：`[码]` 源码核对 / `[文档]` 文档陈述 / `[推断]` 本文判断。

---

## 0. 摘要（TL;DR）

1. **这不是"同一编译器逐层加功能"，而是七台独立实现的编译器。** 七层合计 **163,638 物理行**
   （参考版生产 71.8k + 参考版测试 19.6k + 孪生 72.2k；不含测试的"两套完整实现"≈14.4 万行）。
   层间共享只有源码拷贝，**没有 crate 级复用**：parser 7 套（≈19.2k 物理行）、pretty 7 份、
   typeclass 4 份（L10–L13）、canonical 2 份。`[码]`（`FACTS.md §2`、`CROSS.md §1.2`）

2. **L07 是真正的分水岭与事实上的"语义参考实现"。** 它把旧 L07/L07a 的"事实表/上下文改写"精化
   改成 σ 显式替换 + 单一 unifier + 逐臂下钻，之后 L08 直接以它为蓝本，L09–L12 后来也移植了它的
   σ 精化与逐臂匹配（L09 内核本身是另一次"再定基"）；2026-11 的 P1–P11 加固的**参考版**全量
   也只落在 L07（孪生仅 P1/P2/P9）。
   **理解本仓语言语义，先读 L07。** `[文档]` L07.md、`docs/l07-dpm-refactor-design.md`

3. **L08 是"零核心机增量"的加糖层**：struct/new/投影链全在 parser 脱糖，核心机只加 1 条类型级剥链
   + 1 条 `(Obj,Obj)` 合一臂。它是全仓概念税最低的一层，也是 L07 加固的现成回灌试验田；
   但只迁了 P1/P2/P9，**P3 三档判定未迁 ⇒ L07 说"无法判定"、L08 仍说"分支不可达"** 的层间语义分叉。`[码]` L08.md §1/§3

4. **L09 是一次"再定基"而非继承**：按 MLTT 教学章重写内核，丢掉 decl 表/builtin/可变全局/
   Match pending/struct_eq/通用 fuel（时代缺口），改用 `Infer.global` 大下标哨兵 + 分层宇宙。
   它是最小、最好读的 MLTT 切片，也是 **L09/L10 名字世界成为支线**的起点：L11 立即切回 decl 表。`[文档]` L09.md §1/§2

5. **L10 用最小内核改动落地 trait/typeclass**（trait=is_trait enum，`Synth` 表驱动 Prolog，
   Val↔Typ 桥），教学价值高；但求解器 toy 化：多解取 HashMap 迭代序（非确定）、`effort>1000` 是
   panic 不是诊断、`close` 的 O(n²) 内存修复**只落孪生、参考版仍全量 close_ty**。`[码]` L10.md §1/§4/§6

6. **L11 是"decl 表回归 + 宏"的混合层，也是 L13 引擎的原型**：macro_rules 在 parser 内展开
   （类型检查器无感知，LSP 靠 `MacroExpansionInfo` 补偿）、5 个 builtin、`Rc<Decl>` COW。
   **L11/L12 的参考版都没有 `bench_check_nf`** ⇒ basic=全流程 run，只有 fast_run 同轴；
   L11 误用 fast_ss 会把孪生优势高估 2.2–2.8×（L12 同理，且其 basic 删 eprintln 后 ≈0.196 ms）。
   `[码]` L11.md §1/§6、L12.md §6

7. **L12 是 σ 路线最完整的参考样本，但增量面大面积未接线**：Val 级 trait 求解已生效；
   `Val::Call` 全仓无产生点；canonical/`iddfs` 唯一入口在 Err 重试闭包、而仓内 LSP 只接 L13 ⇒
   **不可达**；hover/completion 表只写不读。parity 15 例不是"整体降级"，而是
   **"共享内核可信、增量面零保证"**——8 个特性测试源全部被剔除。`[码]` L12.md §1.1/§4.1

8. **L13 是唯一生产层，也是唯一"两引擎都留在旧精化载体"的层**：L07–L12 已迁 σ，L13 参考版
   与孪生仍是 `update_cxt`/`refresh` 血统（孪生侧是 `update_cxt_impl` 镜像，非 σ）。σ 迁移五轮
   + 5-agent 评审后**回退**：纯 elaboration
   ~28×、12k 层 meta 解链爆栈、`FRCS_MEMO` 长跑 13 GB、GADT 覆盖回归（round5 补丁里参考版修了、
   孪生未镜像——**master 两版均未打补丁，HEAD 上不存在该分歧**）。`[文档/码]` L13.md、`docs/wip/README.md`、`docs/explicit-subst-refactor-status.md §4`

9. **双引擎（参考版 + 孪生）= 本仓最大的资产，也是最大的工程负担**：match 全层孪生领先
   1.25–10×；大值负载修复前 23–867×（09-20 主表）、修复后约 2–40×（L11 除外）；代价是 ~7.2 万行第二实现、parity 归一化造成的盲区、
   以及 **"加固最厚的 L07 的 parity 判据反而最弱（Err 只比判定不比正文）"** 的倒置。
   生产接线是 L13 双引擎混合：LSP 默认孪生，带 import/package 的文件回落参考版，
   `typort check` 走参考版。`[码]` CROSS.md §1.4、`src/lib.rs:258-330`

10. **最该做的五件事**（按性价比）：① 删除/归档 17 个 `.bak`（≈12,858 物理行）；② 给 L07 parity 补
    Err 正文比对、给 L11/L12 恢复探测隔离；③ 把"预算/燃料耗尽 ⇒ 可诊断错误"统一到 L09–L13
    （当前 PM_FUEL 耗尽在 L09–L12 静默降级为裸 rigid）；④ 只回灌诊断类加固（P9/P10）而非语义类
    （P1/P2/P3/P5/P8 已在 L09 实测会改变判定）；⑤ **停止 L13 σ 迁移**，先做 meta 环检测与
    compiler 分支缓存等前置项。`[码/文档]` CROSS.md §5

---

## 1. 方法与口径

- **对象**：每层的参考版（Rc/Box 树 + 递归，可读性优先、承担 oracle 角色）与 `bump_spine_iter*`
  孪生版（bump arena + 打包值 tag + 显式工作栈迭代内核，性能优先）。七层都是完整实现（各自带
  parser/pretty/elaboration/unify/force/eval），不是库的分层组合 `[码]`。
- **LOC 口径**：物理行（`[IO.File]::ReadAllLines().Count`，含空行/注释）。另有一种"非空行"
  口径会低 12–20%（`Measure-Object -Line`）；分析员报告中出现的 126.8k / 143.8k 等数字是不同
  口径/范围，勿与本节表格混用（`FACTS.md §2` 有专条说明）。
- **测试数**：静态 `grep '^\s*#\[test\]'`，**未执行**（环境禁构建）。`#[path]` 会把本层 lib 测试
  再编入 parity 目标跑一遍，所以 README 的"parity 数"通常是"套件自有 + 带入 lib"——这是重复执行，
  不是重复覆盖（`FACTS.md §3`）。
- **性能口径**：`basic`=参考版；`fast_ss`=孪生稳态（解析在计时外）；`fast`=孪生一次性；
  `fast_run`=孪生全流程（仅 L11/L12 有）。**basic 与 fast_ss 不同轴**，唯一同轴的是 `fast_run`
  （L11/L12）。跨层比倍率会被参考版地板差异放大（如 L09 的 0.10× 主要来自地板高）`[文档]` CROSS.md §3。
- **时效**：性能一律引 2026-09-20 矩阵并标注；代码/测试/机制状态以 HEAD `8443586e` 为准。

---

## 2. 总览矩阵

| 层 | 定位 | 语言特性增量（相对前层） | 参考版生产 LOC | 孪生 LOC | 精化载体 | 匹配编译 | 名字世界 | 主要防护 | 生产用途 |
|---|---|---|---:|---:|---|---|---|---|---|
| **L07** | 理论正向重写（蓝本） | enum/GADT/依赖 match/投影/限定构造子；String/decl/builtin/IO/可变全局继承 L06 | 7215 | 9051 | **σ 显式替换**（定稿） | 逐臂下钻（原生） | decl 表（`Val::Decl`） | UNIFY_FUEL 4096 + MATCH_CMP_BUDGET 64 + P1–P11 | 语义参考/oracle |
| **L08** | 加糖层 | struct/new/投影链（parser 脱糖）；核心机 0 新变体 | 6117 | 8733 | σ（已迁） | 逐臂 | decl 表（`Rc<DeclEntry>` COW） | 同 L07 但只迁 P1/P2/P9；**缺 P3** | 教学/回灌试验田 |
| **L09** | 再定基（MLTT） | `Type N` 分层宇宙、枚举/模式重写；**丢** decl 表/builtin/可变全局/Match pending/struct_eq/通用 fuel | 5598 | 7749 | σ（已迁） | 逐臂（09b9ee8 重写） | **`Infer.global` 哨兵**（无 decl 表） | 单烧点 UNIFY_FUEL 4096 | 教学/parity 参照 |
| **L10** | L09 + trait | trait/impl、接收者方法脱糖、outParam、实例表 Prolog | 7115 | 9541 | σ（已迁） | 逐臂（4e97743） | 哨兵（沿用 L09） | UNIFY_FUEL 4096 + 孪生 PM_FUEL | 类型类教学样板 |
| **L11** | decl 表回归 + 宏 | macro_rules（parser 内展开）、5 builtin、可变全局、`Cxt.decl` 名字键回归 | 10344 | 9018 | σ（已迁） | 逐臂（五层首个，6ae12a6） | **decl 表（名字键）** | UNIFY_FUEL + 孪生 PM_FUEL | L13 引擎原型 |
| **L12** | σ + Val 级求解 + canonical | trait 求解 Val 级重写、Call 节点（无产生点）、canonical/iddfs（未接线）、SmolStr、观察面雏形 | 10442 | 9016 | **σ（最完整参考）** | 逐臂（45330e6） | decl 表（`Rc<Decl>` COW） | UNIFY_FUEL + 孪生 PM_FUEL | σ/沙盒参照 |
| **L13** | 生产层 | namespace/package/import、原生 Nat、class 两阶段+BindingName、def replay、LSP 观察面、HDL prelude | 24946 | 19111 | **`update_cxt`/`refresh`**（σ 迁移失败回退；两版同用） | 逐臂（448775c） | decl 表七元组 + 全限定键 | UNIFY_FUEL + 内层 fuel；**无 MATCH_CMP_BUDGET/P1–P11** | **产品**（LSP/HDL） |

> 规模合计与口径见 `FACTS.md §2`（七层 163,638 物理行）。表中"参考版生产"不含测试文件
> （L07/L08/L13 的测试文件另计：2354/2018/15270 行）。
> 测试静态盘点：lib `#[test]`（参考侧/孪生侧）L07 69/1、L08 60/0、L09 10/0、L10 25/0、
> L11 33/0、L12 35/0、L13 587/25；集成套件：L07 blackbox 49/53/47 + parity 27；L08 58/53 + parity 35；
> L09–L13 parity 29/21/19/15/15；L13 另有约 11–12 套 LSP/namespace/hover/completion 守卫（口径见 FACTS §3）。`[码]`（未执行）

---

## 3. 逐层剖面与评估

### 3.1 L07_sum_type：σ + 逐臂匹配的"定稿蓝本"

**实现 DNA**：把依赖模式匹配的理论构造（specialization by unification）直接映射到 NbE 值表示：
模式变量一律刚性、特化解走显式替换链（`Subst` 持久单链 + `Val::VSub` 包裹 + `force` 的 `frcs`
读点在消费点推进解）、可解性经 `SpecSolve{acc}` 显式穿参（不再有全局旁路）；覆盖性/可达性/精化
由同一套特化方程给出；卡住的 match 是**一等中性值**（可被应用时把实参 splice 进各分支）。
`[文档/码]` L07.md §1–§3、`src/L07_sum_type/README.md`

**为什么它重要**：旧实现"改写 env 槽 + 刷新上下文"造成的 add_assoc 一族 bug 在本架构下**按构造
排除**，不是逐案修补；这正是 L08–L12 全部照搬它的原因。2026-11 加固轮又补上 P1（occurs 传递）、
P2（卡住 match 比较预算 `MATCH_CMP_BUDGET=64`）、P3（三档判定 `Absurd`/`Undecided`/`Fuel`）、
P5（跨 meta 环守卫）、P8（宽松合一收窄）、P9（诊断 pretty）、P10（Error span）、P11（深 quote/pretty
迭代化）等，使它成为**语义上最可信的一层**。`[文档]` `docs/compare-l07-vs-dpm/PR-l07-hardening.md`

**优点**：① bug 族按构造排除、机制单一可移植（σ 已落到 L08–L12）；② 双防护（fuel + 次数预算）
+ 三档判定，边界行为可诊断；③ 测试最厚（lib 70、黑盒 49/53/47、parity 97、v3 117）且深值栈安全轮
做了真正的工作栈化；④ match/大值负载性能不弱（match 0.145/0.049 ms，strchain 23.5×，09-20 口径）。
**缺点/风险**：① **with-K 定位**：不做 without-K 检查，精化可被用在其它假设上，是"教学检查器不是
证明助手"；② **σ 可见性边界**：meta 解（Tm 层）与 decl 表条目不在 σ 包裹范围，某些精化读点不可见
（已知取舍，孪生需对齐）；③ `occurs_transitive` 对嵌套 `VSub` 有已知盲区（R2）；④ 64 次预算/
fuel 4096 都是启发式上限，极深负载可能把合法程序判"无法判定"；⑤ 参考版为性能评审改造成"第二实现"
（undo-log、InlineStack、decl Rc 化），可读性被稀释；⑥ **P3 三档只在参考版，孪生仍报旧口径** ⇒
引擎间判定分裂窗口。`[文档]` L07.md §7、`L07-RISKS.md`

**一句话**：最值得作为"这个语言是什么"的参考实现；不要当证明助手或产品。

### 3.2 L08_product_type：概念税最低的加糖层

**实现 DNA**：核心机**零新增 Tm/Val 变体**——`struct` 在 parser 内脱糖成单构造子 enum
（构造子名 `{Name}.mk`），字段访问复用 L07 投影；`new` 脱糖成限定构造子 + 显式应用；投影链
`p.a.x` 在 parser fold 成嵌套 `Raw::Obj`。推理增量精确到两处：类型级 `.mk` 剥链（接收者只有类型
时按 `.mk` 剥构造子 Pi 链，前字段以**卡住投影值**精确实例化，从而支持依赖字段/Sigma）与
`(Obj,Obj)` 合同合一臂（修 L07 潜伏缺臂）；另加显示去重。`[码]` L08.md §1–§3

**与 L07 的真实关系**：机制上"L07@2026-09 全量继承 + 积类型糖"，**规模上不是**——L07 的 11-08
加固净增约 +900 行，L08 只承接了 P1/P2/P9，所以 HEAD 的 L08 生产 LOC（6117）反而小于 L07（7215）。
L08 还反过来暴露/修复了 L07 的若干潜伏 bug（η 层级 `lvl2ix` 越界、Obj 缺臂、投影遮蔽、孪生
MatchStruct 屏障越界 panic），是 L07 的"对抗测试放大器"。`[码]` L08.md §1/§8

**优点**：① 加糖教学教科书：机制增量可一眼审计；② 双引擎收益实在（struct 32×、strchain 38×，
09-20 口径）；③ 继承黑盒基线 58+53 原样全绿，证明加糖未破语义；④ 唯一已部分回灌 11-08 加固的层，
是"回灌试验田"；⑤ decl 条目 Rc 化把 struct basic 从 1728.7 ms 降到 135.2 ms（语义等价 + parity oracle）。
**缺点/风险**：① **P3 未迁=层间语义分叉**（L07"无法判定" vs L08"分支不可达"）；② `Error(String)`
无 span（P10）、无 `UnifyKind` ⇒ 诊断最弱；③ 语言面浅（struct 不能被 Con 模式解构、无元组 struct、
字段按行分隔、裸 spine 实参不接 `new`）；④ `contains(".mk")` 字符串 gate 把正确性押在"用户不能声明
带点 case 名"上 `[推断]`；⑤ 双引擎维护面积 ~2×。`[文档]` L08.md §7

**一句话**：L07 的"加糖教学版 + 回灌试验田"；生产不合格。

### 3.3 L09_mltt：再定基层（分层宇宙 + 层级化全局表）

**实现 DNA**：按 MLTT 教学章重写内核，**不是继承 L08**。名字世界换成三件套：
`src_names`（局部）+ `Infer.global_names`（顶层名，append-only、不随 Cxt 克隆）+ 
`Infer.global: HashMap<Lvl, VTy>`（值表，键=登记序号）；项层引用是 `Tm::Var(Ix(global_idx + 1919810))`
的大下标哨兵（`>=` 边界必须正确，曾出 off-by-one 修复）。递归 def = `fake_bind` 占名 + global 表
自指占位 + 检查后覆盖。新增 `Type N` 分层宇宙、enum `universe_lvl` max、`check_ctor_wf`（拒绝
phantom 构造子/参数位特化）。`[码]` L09.md §2/§3

**时代缺口（相对 L06–L08，刻意不补）**：无 decl 表、无 builtin 注册表/可变全局/文件 IO、无
`pm_defs`/Match pending splice（`v_app` 对卡住 match **panic**）、无 `struct_eq`、无通用 unify/force fuel
（唯一烧点是 frcs lookup）、无 `redefine` 检查。这些都由 A4 跨章评审登记为"再定基的时代缺口"。`[文档]` L09.md §1

**优点**：① 全仓最好读的 MLTT 切片（最小内核 + 分层宇宙 + 合类型/match + Eq 编码）；② σ 迁移完成度好，
是"旧 update_cxt 世界 → σ"最干净的样本；③ 语义边界诚实（panic/无 Match 重选/fuel 适用面均文档化 +
两版同崩 + parity 一致）；④ 宇宙与构造子良构检查比 L07/L08 更完整；⑤ 孪生 match 全仓领先最大
（0.10×，但主要是参考版地板高）。
**缺点/风险**：① 时代缺口是结构性的，合法源码可触发 `v_app` panic；② 名字世界双表 + 遮蔽特例 +
哨兵常数 1919810 渗透全层（源码命中约 36 处）；③ 09-20 矩阵主表的 L09 参考版数字（strchain 2669 ms 等）是**D² 修复前**——同文档 §B 修复后
strchain 2669→62.9（42.5×）、struct 4269→184（23.2×）、universe 3192→4.81（664×），HEAD 含
`866f23e5`；但 match 的 0.557 ms 未被 §B 复测；④ L07 加固未回灌；⑤ 测试薄（lib 10、parity 29）。
`[码]` L09.md §6/§7

**一句话**：分层宇宙与和类型的最小教学切片、σ 迁移的干净中间站；不能当生产基线。

### 3.4 L10_typeclass：L09 + trait 的最小样板

**实现 DNA**：trait 声明脱糖为 `is_trait` 的 enum（构造子=实例），`impl` 把方法登记进 `Synth` 的
实例表；期望类型是 trait Sum 时 `fresh_meta` 放待解 meta，体检查完后 `solve_multi_trait` →
`solve_trait`（Val 世界与 `Typ` 世界的桥：`force_deep().to_typ()`）→ Prolog 求解 → 实例名经
`infer_expr` 回 Val 世界。`x.foo y` 由 `trait_wrap` 脱糖：扫全部 trait 方法表，对每个候选构造断言
试解，命中后拼 Let 包裹的实例参数应用。实例匹配是**单向一阶** `match_typ`（pattern 侧 `Typ::Var`
才可绑，修正旧双向绑定的假匹配）；`outParam` 用布尔掩码、求解时 out 位填 `Typ::Any` 通配。
`[码]` L10.md §1–§3

**优点**：① trait 机制用最小内核改动落地（`is_trait` enum 复用 enum 全链），新增代码估计仅
700–900 行 `[推断]`；② Val/Typ 分层方向正确（一阶可 Hash 的 `Typ` 才能当 Prolog 表键，assertion
table 兼答案缓存）；③ 单向一阶匹配是与 L12/L13 `val_match` 同族的正确结论；④ golden 钉住了脱糖
文本与 outParam 链。
**缺点/风险**：① 求解器 toy 化：`trait_wrap` 每次调用整克隆 `trait_definition`（源码 TODO 自证）、
`new_subgoal` 每子目标克隆实例表、`synth` 前置 `clean()`；② **多解取 HashMap 迭代序第一个**
（源码 TODO 自认）⇒ 非确定性，parity 测不出；③ `effort>1000` 是 **panic** 不是诊断；④
**依赖表恒空**（无超类约束），Prolog 的 multi-goal 机械基本闲置；⑤ §6.0 的 O(n²) `close` 修复
**只在孪生**，参考版仍全量 `close_ty`、根因（ImplDecl 参数泄漏进 decl 级 cxt）两版都在；⑥ 继承
L09 时代缺口、L07 加固未回灌；⑦ parity 不剥 `?N`（把 meta 分配序变契约，等价重构即红）。
`[码]` L10.md §4/§6/§7

**一句话**：类型类求解与 NbE 内核分层设计的对照样板；不要当性能基线或产品层。

### 3.5 L11_macro：decl 表回归 + 宏（L13 引擎原型）

**实现 DNA**：在 L10 全部语言面之上加 `macro_rules`（parser 内匹配 + 转写，**类型检查器无感知**；
展开点记 `MacroExpansionInfo` 供 LSP goto、`MAX_MACRO_EXPANSION_DEPTH=256` 防自递归爆栈）、
5 个带类型 builtin（`Rc<dyn Fn>`，孪生用 `PrimId` 枚举）、可变全局；同时把名字世界从 L09/L10 的
哨兵换成**名字键 decl 表**（`Cxt.decl: Rc<Decl>` 写时复制、`Tm::Decl` 项层引用、`Val::Decl` 卡住头）——
哨兵 1919810 在本层同源位置消失。`[码]` L11.md §1–§3

**为什么换回 decl 表** `[推断，证据：L12/L13 不再回退]`：① 宏产生的是声明级/表达式级语法，名字键与
parser/AST 天然一致；② LSP 跨文件 goto 需要名字而非 elaborator 内部序号；③ 为 L12/L13 生产化铺路。
L11 因此是 **L13 引擎的早期形态**（参考版即 `Arc` 持久化 + decl 表贯穿）。

**优点**：① decl 表世界与 L13 同构，迁移/对照成本低；② 宏自包含（parser 内展开，类型检查器零改动；
直接 token 拼接使 fast_run −15~−18%）；③ `Cxt.decl` COW 把每次 Cxt 构造的整表克隆降为 O(1)
（struct 2952→846 ms、macro 2696→842 ms）；④ 五层中第一个落地逐臂重写（6ae12a6），并恢复嵌套覆盖；
⑤ trait 错误文案比 L10 细。
**缺点/风险**：① **L11/L12 参考版都没有 `bench_check_nf`** ⇒ basic 含解析，跨层参考版数字不可比（结构性性能口径缺口）；② 无 blackbox/golden/LSP 测试；③ 孪生模块头仍写 `update_cxt`/`refresh` 等
σ 迁移前文字（doc 腐化）；④ 参考版 `DeclTm::Def` 的 `typ_pretty` 每 def nf+pretty 但无消费方；
decl 插入仍先 clone 再 make_mut（O(n²) 残留）+ String 键；⑤ `get_global` 缺名 unwrap panic、
`Too much effort` panic；⑥ 宏无卫生性/gensym、错误定位锚在调用点。
`[码]` L11.md §5–§7

**一句话**：L13 引擎的宏+decl 表原型；语义基线佳、可教学/迁移参照，性能口径与工程性未达标。

### 3.6 L12_canonical：σ + Val 级求解的"最完整参考样本"

**实现 DNA**：相对 L11 无新语法面，增量全是机制/观察面：① trait 求解 **Val 级重写**（断言/实例
参数直接是 `Vec<Rc<Val>>`，`val_match` 直接结构匹配，去掉 L10/L11 的有损 Val↔Typ 桥；单向匹配
修正保留）；② `Tm::Call`/`Val::Call` 内联节点（7 个模块加臂）；③ `canonical.rs` 的 `iddfs`/`search`
（LSP quickfix 的"再试一次"）；④ 全面 SmolStr 化；⑤ hover/completion 表雏形。
`[码]` L12.md §1

**三件增量的真实可观察面（重要）**：
- Val 级求解**已生效**（实例匹配更精确、个别错误文案变化）；
- **`Val::Call` 全仓无产生点**（只有消费式重建）；`Tm::Call` 唯一"无中生有"是 quote 对卡住 match
  的 `origin` 包装 ⇒ README 的 HDL regNext 动机在本层**未接线**；
- **canonical/iddfs 不可达**：唯一调用点是 `Error` 携带的重试闭包，而仓内 LSP 只接 L13（`lib.rs`
  全是 `L13_namespace::`），没有任何二进制/测试调用它；`canonical.rs` 零测试 ⇒ 按可观察行为算
  **"未接线的设计资产（行为上等同死代码）"**。hover/completion 也只有写入、无读者。
`[码]` L12.md §1.1

**优点**：① 语义增量密度最高（Val 求解 + σ + 宏 + Call 骨架；namespace 表承自 L11、本层只做 SmolStr 化），是 L13 前最接近产品
语义的层；② σ 路线在本层最完整（条件包裹/compose/两档 force/燃料降级/臂序无关都有代码与注释），
是读 dpm-nbe 对齐实现的现成样本；③ match 在 HEAD（删 eprintln 后）basic ≈0.196 ms（1.431→0.196，7.3×）；同轴比较应看孪生
`fast_run`（09-20 旧值 0.319），按旧值推算参考版反而更快——孪生侧未复测，不能据此宣称"孪生领先"；
④ 回归钉质量高（嵌套覆盖两段式、构造子 WF、臂序无关、σ 跨轮回收）；⑤ 孪生大值负载 47–85×。
**缺点/风险**：① **死面**：canonical/`Val::Call`/观察面都"只建不用"，维护/文档成本换不到可观察
行为，且 canonical 无测试；② **双引擎可信度在增量面为零**：parity 剔除 mod.rs 全部 8 个特性测试源，
孪生又结构性无 Call/canonical ⇒ "15 例"不是均匀降级而是"共享内核高、增量面零"；③ 文档漂移最重
（孪生头写 update_cxt、README 说无燃料池、README 测试数 17 vs 静态 35（lib）/21（parity）、单文件形态已拆 13 子模块）；
④ 参考版深负载慢（strchain 645/struct 522 ms，是 L07 的 4–5×）；⑤ panic 面（Too much effort/
`get_global` unwrap）；⑥ 无 LSP 接线。`[码]` L12.md §4.1/§7

**一句话**：σ 与 Val 级 trait 求解的最完整参考样本、L13 的机制沙盒；不能当产品层或验收基线。

### 3.7 L13_namespace：生产层（LSP/HDL）与未完成的 σ 迁移

**实现 DNA**：相对 L12 的核心增量：① **全限定 decl 键命名空间**（构造子只登记 `Enum.case`、
五级 Var 解析链 local→decl→import_map→namespace_prefix→`.name` 后缀回退；package/import 不改
decl 表、别名挂 `Infer.import_map`）；② **原生 Nat**（`Val::Nat(u64)` + `quote_nat` 展开 + nat 内建
下沉，保留旧定义可归约性）；③ `Call`/`OpCall` 内联节点、prim 挂 decl 表（取消 `Tm/Val::Prim`）、
def replay（无参 def 含全局副作用时重放）、class 两阶段 + BindingName 隐参；④ 生产工程：
LSP 三张观察面（push 期渲染、owned 快照）、`FORCE_MEMO`（keepalive/taint/version，prelude 装载
force 636M→188k 节点、11.0s→1.8s）、`PreludeSlot/PreludePool`、常驻 prelude 检查点 + `compact`
压实、双引擎接线。`[码]` L13.md §1/§3

**复杂度构成**（关键判断，`[推断]`，非空行口径估算）：≈ 语言内核 7–8k 行 : 宿主工程 9k+ 行。
LSP 观察面/池化/双引擎/并行测试不变量才是 L13 的主要复杂度来源；语言理论不是。L13 参考版
24.9k 生产行**之外**另有 15.3k 行测试/探针（物理行口径；README 旧数字 22.8k/13.5k 是非空行口径）。

**σ 迁移五轮失败复盘**（本仓最重要的负结果）：
- 主阻塞是**纯 elaboration ~28×**（prelude-core basic 22.4 ms → 637 ms，关闭 LSP 表后），
  来源是编译器分支循环内的 quote/探测（`DIAG10`：quote 最外层 79% 来自 compiler）；
- **规模放大**：12,287 层 meta 解链（`succ(?m₁):=?m₁:=succ(?m₂)…`）逐层 force，默认测试栈必溢出；
- **观察面耦合**：每个变量引用类型都带 VSub 包裹，渲染要 quote+frcs 重建（prelude 期 LSP 表
  占 ~11 s；该总闸补丁 `lsp_collect` 21.1→9.3 s 随回退撤下，master 无此改动）；
- **补丁系列内的正确性回归**：round5 补丁里参考版已修 GADT 覆盖（逐列 σ 随臂下传 + 探测点
  `wrap_sub`）、孪生未镜像 ⇒ 若将来应用补丁，这是唯一已知 REF/TWIN 分歧；**master 两版均未打补丁，
  HEAD 上不存在该分歧**；
- `FRCS_MEMO` 长跑 13 GB；4 个既有 parity 失败；五轮 + 5-agent 评审后**回退**。
`[文档]` `docs/wip/README.md`、`docs/explicit-subst-refactor-status.md §4`、L13.md §σ

**精化载体现状**：参考版 `update_cxt`/`refresh`（`cxt.rs:1327`、`elaboration.rs:793-853` 八处真实
调用点）；孪生同样走 `update_cxt_impl`/`refresh` 镜像（`bump_spine_iter/machine.rs:1214/2324/2766-2806`，
零 `SubstV`/`frcs` 命中）。即**两引擎都留在旧载体**，L13 是七层里唯一整体未迁 σ 的层；跨层对照时
"L12 的 σ"不能与"L13（任一引擎）"直接对齐。`[码]` L13.md §2.3/§4、本轮 grep 复核。
> 注：`docs/l09l13-match-compiler-analysis-2026-09-17.md:41-42` 写"孪生侧仍是 σ（SubstV）"，那是对
> 当时迁移上下文的过时描述，与 HEAD 代码不符——本报告以代码为准。

**生产接线**：LSP 默认 **L13 孪生**（`Engine::lsp_default`）；带 `import`/`package` 的文件自动回落
参考版（孪生的 replay 只看到 prelude+当前文件）；`typort check` 走参考版专属管线。稳态 HDL 负载
kick 359→102 ms（~3.5×）；常驻孪生 prelude ~429 MB 稳态/730 MB 峰值 vs 参考版 ~200 MB
（~2.2× 内存换 CPU）。`[码]` `src/lib.rs:258-330`、CROSS.md §4

**优点**：① 唯一生产可用层（LSP/HDL/Verilog 生成全部压在这里）；② 性能工程最扎实（force memo、
prelude 池化、常驻检查点、compact 压实、push 期渲染契约）；③ 命名空间/原生 Nat/class 两阶段等
语言面领先；④ 测试体量最大（静态 lib 612 + 约 11–12 套 LSP 守卫 + parity 15）；⑤ 已知缺陷文档化最全。
**缺点/风险**：① **精化载体未统一** + σ 迁移负结果 + 孪生镜像未做 ⇒ 两引擎语义分歧；② 规模与
耦合：语言核心与宿主工程混在一层（观察面 push 进 elaboration、池化不变量跨模块）；③ L07 加固
P1–P11 零回灌（`occurs_transitive`/`MATCH_CMP_BUDGET`/`UnifyKind`/span 修复 0 命中）；
④ 已知缺陷面：单行 enum 假阴性（两版同错；`[文档]` 未复现）、GADT 组合覆盖缺口、文件 IO panic 无锁、并行测试 UAF、
18-utils flex-flex 求解分叉、Stacked Borrows UB 未清；⑤ `update_cxt`/`refresh` 全槽重求值的
性能成本未量化；⑥ 文档行号/计数大量漂移。
`[码]` L13.md §6

**一句话**：产品层；当产品养，不要当"语言语义参考书"读。

---

## 4. 横向深对比

### 4.1 谱系：三种"重写"，两种"增量"，一种"生产化"

| 类型 | 层 | 对前一层的关系 | 判断 |
|---|---|---|---|
| 理论正向重写 | L07 | 合并旧 L07/L07a，机制按 dpm-nbe 重做 | **全仓最有价值的设计资产**；成为 L08–L12 蓝本 |
| 零核心机加糖 | L08 | L07@2026-09 + struct 糖 | 教学最好、加固缺口最大（P3 分叉） |
| 再定基 | L09 | 按 MLTT 章重写，**丢** L06–L08 设施 | 制造了 L09/L10 的哨兵支线；被 L11 抛弃 |
| 增量扩展 | L10 | L09 + trait | trait 机制最小样板；求解器 toy 化 |
| 换世界 + 增糖 | L11 | L10 + 宏 + **切回 decl 表** | L13 引擎原型；名字世界选型在此收敛 |
| 机制/观察面预演 | L12 | L11 + Val 求解 + Call/canonical/观察面雏形 | 增量面大量未接线；σ 最完整样本 |
| 生产化 | L13 | L11/L12 世界 + namespace/Nat/LSP/HDL | 唯一产品层；未完成 σ 统一 |

**判断**：层间"重写 vs 继承"的决定并非都出于理论——L09 的再定基让后续两层付出名字世界迁移成本，
L11 又切回 decl 表；**L09/L10 是演进支线而非主线**。真正的复用主线是 L07→L08 的机制、L11→L12→L13
的 decl 表世界。`[码]` L09.md §8、L11.md §8、L12.md §8、CROSS.md §1

### 4.2 精化载体的三次换代（本仓最核心的技术叙事）

| 代 | 载体 | 层 | 状态 | 关键证据 |
|---|---|---|---|---|
| 0 | `pm_defs` 事实表 / `update_cxt` 改写 env 槽 + refresh | 旧 L07/L08、L09–L12 移植前、**L13（两版）现状** | L13 两版仍在用 | `L13 cxt.rs:1327`/`elaboration.rs:793-853`；孪生 `machine.rs:2766-2806`（`update_cxt_impl`） |
| 1 | σ 显式替换（Subst/VSub/frcs/SpecSolve） | L07 定稿 → L08–L12 移植 | ✅ 已落地 | `docs/explicit-subst-refactor-status.md §1`；grep：L07–L12 `VSub` 148/95/86/76/81/71（**参考版+孪生两版合计行数**），且 `update_cxt` 只剩注释 |
| 2 | σ 迁 L13 | L13 | ❌ 五轮回退 | `docs/wip/README.md`；详见 §3.7 |

**σ 的真正收益**：不是"更少的代码"（L13 移植后纯 elaboration 反而 ~28×），而是**按构造消除
"改写上下文 + 刷新" bug 族**（已捕获旧上下文的值过期、槽位错位、meta 与模式变量纠缠）。
L07/L08 的 add_assoc 一族是真 bug 修复；L09–L12 的移植因此首先是修复、其次才是统一。
**σ 的真正代价**：解只在消费点可见（必须显式 `wrap_sub`），任何"解前构建、解后消费"的缓存放进
错层就会丢精化（L13 的 GADT 覆盖回归正是此坑）；且对规模/观察面敏感（L13 prelude 放大器）。
**判断**：σ 对"语言核心 + 中等规模"是正确的；L13 卡在工程规模与宿主耦合，**继续搬机制不是出路**——
应先做 meta 解链环检测、compiler 分支缓存、观察面总闸这些前置项（`docs/wip/README.md` 接续清单）。`[文档/码]`

### 4.3 匹配编译器：决策树 → 逐臂，一笔收益巨大的全仓统一

- **史实**：L07/L08 一开始就是逐臂；L09–L13 原为决策树矩阵，2026-09-18/19 全部改成逐臂
  （L10–L13 为 09-18；L09 `09b9ee8` 为 09-19；参考版+孪生同步）。
- **收益**：受控实验（同一源文本喂 L07 与 L09 参考版）：臂数扫描 10×→**2363×**；列数/通配扫描
  9×→**14822×**；理论机制是决策树对通配臂的分支重数积（`Π βᵢ = 2^m`）。同负载实测 match：
  L09 3.8×/9.5×、L10 3.0×/5.1×、L11 2.2×/8.5×、L12 4.8×/8.9×、L13 1.44×/3.9×。
  `[文档]` `docs/pmab-per-arm-vs-decision-tree.md`、`docs/l09l13-match-compiler-analysis-2026-09-17.md`
- **代价**：诊断收窄三处（决策树的 `Unmatched` 路径感知填充退化为"构造子+999 通配"；遮蔽只认
  通配臂；特化失败臂静默跳过）。L10–L13 同款；嵌套覆盖已以"两段式"恢复，但**路径感知遮蔽/usefulness
  分析没有替代品**。
- **判断**：这是全仓最正确的性能投资之一（20× 量级、五个层、算法级），但诊断能力是永久性让步；
  若要恢复，需要另建 usefulness 分析，不能指望"换回决策树"（决策树的运行期收益在本仓从未兑现：
  树被丢弃、仍线性首匹配）。`[码]` 同上 + CROSS.md §1.4

### 4.4 名字世界的三条路线

| 路线 | 层 | 机制 | 优点 | 缺点 | 结局 |
|---|---|---|---|---|---|
| decl 表（名字键） | L06–L08、L11–L13 | `Cxt.decl: HashMap<Name, Entry>`；`Tm/Val::Decl` | 名字即键、宏/AST/LSP 友好、有 `redefine` | Cxt 克隆/插入成本（COW 化后可控） | **主线**：L11–L13 沿用并强化到 namespace |
| `Infer.global` 哨兵 | L09/L10 | `Tm::Var(Ix(global_idx+1919810))` + `HashMap<Lvl, VTy>` + `src_names/global_names` | 项层 Var 直达值表、eval 一次查表、无 decl 展开算子 | 无名字键（宏/重定义/跨文件无处挂）、魔法常数 1919810 渗透全层（源码约 36 处）、双表遮蔽特例 | **支线**：L11 切回 decl 表，L12/L13 不再回退 |
| 全限定键 + namespace | L13 | 构造子 `Enum.case`、package/import、五级解析链、import_map 挂 Infer | 跨文件/包语义、LSP goto 可追溯 | 名字解析复杂、别名/遮蔽规则多、文档漂移重 | 生产选型；但只此一层 |

**判断**：L09 的哨兵设计在教学上成立、在工程上失败（L11 的反手是证据）；L13 的 namespace 是
L11 decl 表的自然延伸，不是新世界。`[码]` L09.md §2、L11.md §8、L13.md §1.1

### 4.5 trait/typeclass 的三代实现

| 代 | 层 | 实现 | 状态/评价 |
|---|---|---|---|
| A | L10 | `Typ` 世界表驱动 Prolog（`Synth`）+ `Val↔Typ` 桥 `to_typ` | 正确但 toy：多解不确定、effort panic、有损桥；教学最好 |
| B | L11 | 继承 A（同一份 `Synth`，Decl 表世界） | 错误文案更细；仍是 toy |
| C | L12 | Val 级 `val_match`/`vals_eq_ground`，去掉 Typ 桥 | 匹配更精确；孪生经 `v_to_ref_val` 桥复用；**L13 未沿用** |
| D | L13 | 自写 typeclass.rs（参考 + 孪生各一份），原生 Nat/class 两阶段 | 生产语义最全；放弃统一，维护面积 +1 |

**关键澄清**：所谓"Synth 共用"是**层内**（参考版与孪生共用同一份代码，L10/L11；L12 孪生经桥复用），
**不是跨层**——跨层是 4 份源码（L10–L13 各一份，MD5 不同）。`[码]` CROSS.md §1.2、L10.md §4、L12.md §4
**风险**：多解取 HashMap 序（L10/L11 的 `trait_wrap`）、`effort>1000` panic、L12 的 canonical
探测无测试、L13 的 trait 求解与原生 Nat 交互有已知 bug（`docs/l13-typeclass-instance-nat-param-bug.md`）。
**判断**：trait 系统的语义价值高（方法分派/实例合成/outParam），但实现质量仍是"研究原型"，
不能按生产类型类（Lean/Agda/Rust）的完备性/确定性要求它。`[码]`

### 4.6 双引擎：资产还是债务？

**收益**（用受控/矩阵数据说话）：
- match：七层孪生/参考 = 0.10–0.80×（领先 1.25–10×）；大值负载（strchain/global/struct）孪生
  普遍 3–20 ms vs 参考 19–887 ms ⇒ 同层约 2–40×（修复后口径；09-20 主表的 23–867× 是修复前，
  L09/L10/L13 的 Rc 化修复会显著缩小倍率）；
- 独立 oracle：Ok 输出逐字节一致 + Err 判定一致（L08 还比正文），能在参考版/孪生结构不同的情况下
  抓实现漂移；
- 生产：L13 孪生默认 + 参考回落，稳态 3.5× + 内存 2.2× 的明确工程取舍。

**成本**：
- **第二实现 72.2k 行**（≈全层代码 44%），机制改动必须双写；parity 判据反而**倒置**：
  加固最厚的 L07 的 Err 只比判定（`l07_fast_parity.rs:5-6`），加固较少的 L08 反而比正文；
  L11–L13 靠剥 `?N` 掩盖 meta 编号漂移；
- **已知分叉/缺口**：L11/L12 孪生 gadt 缺陷区、L10/L11/L12 enum 孪生发散/traitchain parity 失败、
  L13 4 个既有 parity 失败 + 单行 enum 两版同错（假阴性）；
- **加固双写滞后**：P3/P5/P8/P10/P11 大量只在参考版；L13 孪生未镜像 GADT 精化（仅 round5 补丁系列内；master 未打补丁）。

**判断**：保留，但把它当"第二实现 oracle + 性能交付面"，不是"优化开关"；不再新增第三引擎；
把"两侧必须同构的机制清单"（fuel 口径、探测隔离、判定分档、精化载体）固化下来。`[码]` CROSS.md §5

### 4.7 防护/健壮性：同名常量，不同语义

| 机制 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---|---|---|---|---|---|---|
| `UNIFY_FUEL` | 4096 | 4096 | 4096 | 4096 | 4096 | 4096 | 4096 |
| `MATCH_CMP_BUDGET` | **64** | **64** | 缺 | 缺 | 缺 | 缺 | 缺 |
| `PM_FUEL`（孪生） | 无 | 无 | 4096 | 4096 | 4096 | 4096 | 无（内层 fuel=100） |
| unify 主循环燃料 | 有（参数化） | 有 | **无** | **无** | **无** | **无** | 内层 100 |
| 深值迭代化 | quote/pretty 部分 | 无 | 无 | 无 | 无 | 无 | 迭代 Drop + pretty 截断 |
| 燃料耗尽行为 | 参考=三档；孪生=旧口径 | 旧口径 | PM_FUEL 耗尽→裸 rigid | 同 L09 | 同 L09 | 同 L09 | FRCS/FORCE_MEMO 有守卫 |

**关键判断**：七层"都有 4096"是假象——L07/L08 是调用级预算 + 次数预算，L09–L12 是精化展开的
thread_local 池（unify 主循环本身无燃料），L13 是单常量 + 内层 100。**最危险的缺口**是
L09–L12 的 PM_FUEL 耗尽**静默降级为裸 rigid**（`twin/unify.rs:413`）：把"算不出来"伪装成"没解"，
比缺预算本身更难诊断。**P1–P11 分布**：参考版全量只有 L07（P11 部分）；L07 孪生只迁 P1/P2/P9；L08 参考版迁 P1/P2/P9；L09–L13 零回灌（L13 自带
span 载体但与 P10 不同源）。三个分类必须分清：**刻意的时代缺口**（L09 无 decl 表等）、
**当前缺陷**（L11/L12 探测隔离丢失、缺 MATCH_CMP_BUDGET、PM_FUEL 静默降级）、**未评估**（L10–L13
的 P1/P2/P3/P5/P8/P15 同构性）。`[码]` CROSS.md §2、L07.md §7、L09.md §3

### 4.8 性能：数字必须带口径和时效

**match 主线**（k=11，09-20 矩阵；单位 ms）：

| 层 | basic | fast_ss | 同轴孪生/参考 | 备注 |
|---|---:|---:|---:|---|
| L07 | 0.145 | 0.049 | 0.34× | σ+逐臂；11-08 加固后参考版路径有变 |
| L08 | 0.144 | 0.052 | 0.36× | 同 L07 |
| L09 | 0.557 | 0.055 | 0.10× | **参考版地板高**（且 09-20 早于 D² 修复） |
| L10 | 0.171 | 0.053 | 0.31× | 修复前 |
| L11 | 0.202 | 0.044 | 0.47×（fast_run 0.094） | basic 含 parse，只有 fast_run 同轴 |
| L12 | **1.431** | 0.195 | 0.22×（旧 basic）→HEAD basic≈0.196 | 1.431 含 eprintln 回归；删后 basic 0.196，与 fast_run 0.319（旧值，同轴）比参考反而更快，孪生未复测 |
| L13 | 0.215 | 0.172 | 0.80× | 生产引擎，孪生领先最小（1.25×） |

**读法**：① 倍率只说明同层两引擎差距；② 绝对时间才说明"谁的 match 快"，但 L09（参考地板）、
L13（生产语义多）与 L07/L08/L10 不同轴；③ **09-20 后时效**：同一文档 §B 已给出**修复后**复测——
L12 match 1.431→0.196、L13 strchain 4537→18.6/struct 7490→85.2、L09 strchain 2669→62.9/
struct 4269→184/universe 3192→4.81、L10 strchain 917→55.9/struct 981→170（`866f23e5` 等已进 HEAD）；
L07/L08 的 11-08 加固又改了参考版路径 ⇒ 现状 match/大值仍需一次全量复测。
**大值负载**：孪生把"树+递归 vs bump+迭代"的表示差放大；**修复后**参考版大值负载约 19–184 ms
（L13 18.6/85.2、L09 62.9/184、L10 55.9/170、L07 strchain 122.7/global 133.8、
L08 strchain 123.6/struct 134.2），孪生仍普遍 3–20 ms ⇒ 同层倍率仍大，但已从"千倍"回落到约 2–40×；
**L11 是例外**（未进 §B：strchain 707.6 / struct 887.5 ms）。
跨层比倍率会被参考版地板放大（L09 的 867× 是修复前数字）。**真实负载**只有 L13 有
（prelude-core/prelude-hdl/examples-hdl）：production 路径的收益由 LSP 双引擎给出（kick ~3.5×），
而不是 bench 合成负载；prelude-hdl 参考版 3073 ms vs 孪生 fast_ss 1332 ms（09-20 口径，2.3×）。
**判断**：性能是本仓做得最透的维度（四口径、矩阵、隔离进程、交错 A/B、受控实验），也是文档最易
误读的维度；任何"哪层快"的结论不写口径就是错的。`[文档]` CROSS.md §3、各层 §6

### 4.9 诊断、显示与错误契约

- **显示格式分层**：L08 的 struct 打印是"空格 + `[名]` 隐式"本地形态；L09–L13 是"comma + 头类型
  参数"血统（`Point[Nat]::Point.mk(4, 6)`），两族**不得互贴**（A4-R3 终裁，贴反曾导致 L12 内置断言
  失败并回滚）。`[文档]` `docs/archive/review-continuity/FINAL.md §2.3`
- **错误载体分层**（本轮 grep 核实）：L07 `Error(String, Option<Span>)` + 三档 `UnifyKind`；L08
  仍是 `Error(String)` 单字段（**无 span**）；L09–L11 是 `Error(Span<String>)`（有 span、无重试）；
  L12/L13 是 `Error(Span<String>, Vec<RetryClosure>)`（span + 错误重试闭包，L13 的 retry 面更完整）。
  parity 归一化剥 span 正是为了掩盖 L08 与其余层的差异——**代价是错误定位永远不被比对**。`[码]` L08.md §3、L12.md §3
- **诊断能力退化**：决策树→逐臂的三处收窄是永久让步；L07 还有 with-K 无检查、σ 可见性边界等
  已文档化限制。**判断**：诊断是七层里最不统一、最容易被 parity 归一化掩盖的面；P9/P10 是低成本
  可回灌项，P3 的层间分叉应先统一口径。`[码/文档]`

### 4.10 工程性与文档：16 万行代码配 4.3 MB 文档的代价

- **重复**：可去重上限约 2.4–2.8 万行（parser 7 套 19.2k 物理行 + pretty 7 份 + typeclass 4 份 + canonical 2 份）；
  但 unify/force 不可抽象（Rc 树 vs bump 打包值是两套值表示，抽象会热路径 box 化）。`[推断]` CROSS.md §4/§5
- **文档**：7 层 README 共 3,012 物理行 + `docs/` 232 份 md / 4.55 MB（含本目录 11 份；剔除后 221 份 / 4.33 MB）；**已证过期点**：L13 lib 341 vs
  静态 612、L09–L12 lib 计数、L07/L08 README 行号/基准、L12 单文件形态、L11 测试数、各层孪生模块头
  `update_cxt` 段、`docs/l09l13-match-compiler-analysis-2026-09-17.md:41-42` 的 L13 孪生 σ 描述
  （实际两版 update_cxt）。文档不是没有价值——它记录了所有负结果和刻意取舍——但**读者必须把 README 当
  "设计意图"而不是"现状"**。
- **卫生**：17 个 `.bak`（≈12,858 物理行、541 KB，多数与 HEAD 不同）；L13 参考版有大量有意诊断探针
  （`debug_test.rs`/`struct_refine_probe.rs`/`FUNC_PROF`，不是死码）；测试通过 `#[path]` 重复执行
  （L13 约 1.5 万行测试文件在 lib 与 parity 各跑一次，`legacy_tests.rs` 单文件 5,420 行）。
- **可复现性**：环境把"能否 cargo build"变成稀缺资源（F 盘 <1 GB），所有门禁只能静态/文档化——
  这是下一次评审最大的现实风险。`[码]` CROSS.md §4

---

## 5. 评分汇总与"用哪个"决策

### 5.1 七层评估卡（1–5，取自各层分析员报告；L07 以 L07.md 原表为准）

| 维度 | L07 | L08 | L09 | L10 | L11 | L12 | L13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 教学清晰度 | 4 | 5 | 5 | 5 | 4 | 4 | 2 |
| 语义健全性 | 3 | 3 | 3 | 3 | 4 | 3.5 | 3 |
| 参考版性能 | 4 | 4 | 2 | 2.5 | 2 | 2 | 3 |
| 孪生性能 | 5 | 5 | 5 | 5 | 5 | 5 | 5 |
| 可维护性 | 3 | 3 | 3 | 3 | 3 | 2 | 2 |
| 测试强度 | 5 | 4 | 3 | 3.5 | 3 | 3 | 4 |
| 生产就绪度 | 2 | 2 | 1 | 2 | 2 | 1.5 | **4** |

> 注 1：语义健全性给 L07 5 分是相对本仓其它层；with-K 定位意味着它仍不是证明助手。
> 注 2：参考版性能分按 09-20 主表/分析员口径给出；同文档 §B 的修复后复测（L09/L10/L13 大值负载
> 2–664× 提速）会显著抬高 L09/L10/L13 的参考版性能分；L11 除外（未进 §B，仍 708/887 ms）。
> 注 3：各分析员的 LOC/测试数若与 `FACTS.md §2` 不一致，以 FACTS 的物理行口径为准。

### 5.2 决策树

| 你的目的 | 选层 | 理由 |
|---|---|---|
| 理解"这个语言的语义应该是什么" | **L07** | 理论正向、机制单一、加固最厚、测试最厚 |
| 教学/讲"语法糖怎么加" | **L08** | 核心机零新变体，机制增量可一眼审计 |
| 讲 MLTT 最小内核/分层宇宙 | **L09** | 最小、最好读；但别拿它当"完整语言" |
| 讲类型类怎么接进 NbE | **L10** | trait=enum + 独立 Synth，最小可行样板 |
| 讲宏/decl 表/生产引擎的祖先 | **L11** | L13 引擎原型 + parser 内宏展开 |
| 研究 σ 显式替换/作用域精化 | **L12** | σ 最完整参考；canonical/Call 是负结果样本 |
| 做产品/LSP/HDL/Verilog | **L13** | 唯一生产层；接受其复杂度和未统一 σ |
| 性能基线/回归对照 | 各层孪生 | 但必须用同轴口径（fast_run vs basic；不要拿基本跨层比） |
| 证明/定理 | **都不要** | with-K 无检查，教学检查器不是证明助手 |

### 5.3 一句话总结各层

- **L07**：σ+逐臂依赖匹配的定稿蓝本，教学/移植一流，非证明助手、非生产层。
- **L08**：零核心机增量的加糖教学层 + L07 加固回灌试验田；生产不合格。
- **L09**：分层宇宙与和类型的最小教学切片、σ 迁移的干净中间站；双表名字世界与时代缺口决定它不能当基线。
- **L10**：L09+trait 的最小样板，Synth 共用但 toy 化、close 修复只落孪生，适合作教学对照。
- **L11**：L13 引擎的宏+decl 表原型，语义基线佳、性能口径与工程性未达标。
- **L12**：σ+Val 级求解最完整参考样本，但 canonical/Call/观察面未接线、增量面无双引擎保证。
- **L13**：产品层，复杂度的主体是宿主工程而非语言理论；σ 迁移负结果是全仓最重要的技术债。

---

## 6. 建议（按优先级）

### P0 · 立即（半天级，无风险）
1. **删/归档 17 个 `.bak`**（≈12,858 物理行）：它们不参与构建、与 HEAD 多数不同，只误导读者与占盘。
2. **文档对账**：统一 LOC 口径（本报告 `FACTS.md §2`）、修 L13 lib 341→612、L09–L12 测试计数、
   L11/L12 孪生"单文件"叙述、各孪生模块头 σ 段；给每层 README 顶部加"本文档时点/行号可能漂移"。
3. **恢复 L07 parity 的 Err 正文比对**（照 L08 模板）：当前只能抓 Ok 漂移，抓不到错误文案分叉。

### P1 · 短期（正确性/可观测性，中等风险）
4. **恢复 L11/L12 参考版探测隔离**（a7-r1 §2.1 P1；窄快照，L13 的实现可下沉）：当前 fresh meta 可能
   泄漏 + 探测期求解持久化，parity 的 `?N` 归一化正好掩盖它。
5. **统一"预算/燃料耗尽 ⇒ 可诊断错误"口径**（至少 L09–L13）：PM_FUEL 耗尽静默返回裸 rigid
   （`twin/unify.rs:413`）应改为 `Undecided`/可诊断边界；L09–L13 缺 `MATCH_CMP_BUDGET`，至少给
   卡住 match 比较一个次数上限（L13 有 12k meta 链爆栈前科）。
6. **只回灌诊断类加固**（P9/P10）到 L09–L13；**不要**硬搬语义类 P1/P2/P3/P5/P8——PR §2.5 已实测
   L09 上会"接受→拒绝"与栈溢出，属语义变更而非修复；L10–L13 需逐层做 L09 式实测再定。

### P2 · 中期（结构，高成本/高收益）
7. **抽公共 crate（分两步）**：先 `pretty` + `syntax`（纯数据/纯函数、7 份副本、L12≡L13 与 L07≡L08
   已有同源先例），再评估 parser；**不要**抽 unify/force（两套值表示，抽象=热路径 box 化）。
8. **L13 σ 迁移：停止**。重启前置项 = meta 解链环检测 + compiler 分支缓存 + 观察面总闸；
   在孪生镜像完成前，不要宣布"σ 已统一"。
9. **双引擎治理**：把"两侧必须同构的机制清单"（精化载体、fuel 口径、探测隔离、判定分档、span 载体）
   写成一份跨层契约；新增机制先写进契约再写代码。
10. **L11/L12 的"死面"决策**：canonical/iddfs、`Val::Call`、hover/completion 要么接线并补测试，
    要么删除并在 README 标"未接线设计资产"——不要维持"代码在、无人用、无测试"的第三态。

### 不建议做
- 把 L09/L10 的哨兵世界改回 decl 表（改造=重写，且 L11 已给出正确路线）。
- 把 L09–L13 统一成 L07 的语义细节（显示格式、fuel 矩阵、L13 的 update_cxt 是刻意差异，改即回归）。
- 用 L09–L13 的参考版当性能基线（地板不同、口径不同、且 L09/L10 的 09-20 数字已过期）。

---

## 7. 附录

### A. 证据与数据来源
- 逐层：`L07.md`–`L13.md`（本目录，含 path:line 锚点与各层文档不一致清单）
- 横切：`CROSS.md`（双引擎/防护/性能/工程性矩阵，含 parity 判据 7 层对照、P1–P11 分布表）
- 事实底稿：`FACTS.md`（LOC/测试/性能/时效/文档不一致，Lead 维护）
- 对抗核查：`VERIFY.md`（共核 27 条：错误 4 / 可疑 6 / 未核实 3 / 通过 14；本报告已按核查逐条修订：
  GADT 补丁态、L07 评分、P1–P11 分布、大值倍率、parser/README/1919810 计数、L12 测试数与 namespace 来源、
  09b9ee8 日期等）
- 关键历史文档：`docs/l07-dpm-refactor-design.md`、`docs/explicit-subst-refactor-status.md`、
  `docs/wip/README.md`（L13 σ 五轮失败）、`docs/l08-l13-refactor-plan.md`、
  `docs/l09l13-match-compiler-analysis-2026-09-17.md`、`docs/pmab-per-arm-vs-decision-tree.md`、
  `docs/bench-matrix-2026-09-20.md`、`docs/archive/review-continuity/FINAL.md`、`docs/compare-l07-vs-dpm/`（加固轮）
- 代码事实：`src/L07_sum_type` … `src/L13_namespace`、`src/lib.rs`（LSP 双引擎接线）、
  `Cargo.toml`（bin/target 布局）、`tests/l0*_fast_parity.rs`（parity 判据）

### B. 未核实/需实测项（诚实清单）
1. **执行数**：所有测试数均为静态 grep，**未运行**；README 的"以 Lead 实跑为准"依然成立。
2. **HEAD 性能**：09-20 矩阵后被 L07/L08 加固、L09/L10/L13 的 Rc 化修复、L12 eprintln 删除、
   L13 σ 实验（未落地）改变；同文档 §B 已实测修复后部分格子，但当前没有一次 HEAD 全量矩阵。
3. **L13 的 `update_cxt`/`refresh` 性能成本**未量化；σ 迁移若重启，前置收益需重新测量。
4. **L11/L12 探测隔离缺失**的影响面（哪些输入会真实触发 fresh meta 泄漏）未做对抗语料。
5. **L10–L13 的 P1/P2/P3/P5/P8/P15 同构性**未逐层实测（L09 已实测不可硬搬）。
6. **L09 的 match 绝对时间**：866f23e5 修复后 L09 非 match 负载已按矩阵 §B 更新（strchain 62.9 ms 等），
   但 match 的 0.557 ms/0.10× 未被 §B 复测，仍按修复前口径引用。
7. **对抗核查的边界**：`VERIFY.md` 只读抽查 27 条（4 错/6 可疑/3 未核实/14 通过），不是全量复算；
   核查期间 FINAL 仍在修订，其行号基于 2026-11-08 23:34 快照（607 行），文字锚点仍适用。

### C. 复现命令（本次均未执行，因 F 盘空间约束）
```bash
# 逐层门禁（示例）
cargo test --lib L07_sum_type
cargo test --test l07_blackbox && cargo test --test l07_blackbox_v2 && cargo test --test l07_blackbox_v3
cargo test --test l07_fast_parity
# 全层 parity（串行，大栈线程；L13 建议 --test-threads=1）
for t in 07 08 09 10 11 12 13; do cargo test --test l${t}_fast_parity; done
# 基准（参数示例）
cargo run --release --bin l07bench -- --workload all --max-k 11 --rounds 3
cargo run --release --bin l13bench -- --workload all
# LSP 双引擎开关
$env:TYPORT_LSP_ENGINE="reference"   # 默认 twin
```
