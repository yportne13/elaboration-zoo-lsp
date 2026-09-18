# D6 测试质量与文档准确性 — L07–L12 只读评审

## 1. 结论（verdict）

- **P0: 0  P1: 0  P2: 5  P3: 2  needs-verify: 3**
- 无 P0/P1：parity 套件本身是绿的、归一化方案不掩盖已知分歧、`#[ignore]`
  全部有原因记录、L07 的显式替换机制层单测真实存在且断言扎实。问题集中在
  **测试防护的层间不均衡**（L11/L12 特征路径被系统性剔除且无跟踪案、L09–L12
  无黑盒契约）与**移植后文档未随代码更新**（L09/L10/L11 README 与 L11/L12
  孪生模块头仍描述已删除的旧机制）。

### 覆盖范围与方法

- 通读：`docs/review-l07l12/BRIEF.md`、`docs/l07-dpm-refactor-design.md`、
  `docs/l08-l13-refactor-plan.md`、`docs/explicit-subst-refactor-status.md`；
  六层 `src/LXX/README.md` 全文；`tests/l07_fast_parity.rs`、
  `tests/l12_fast_parity.rs` 全文，其余 parity/blackbox 按头部 oracle、
  测试名与敏感用例采样。
- 机械比对：`#[test]`/`assert`/`norm_err`/`probe_`/`gadt_src`/`pm_defs`
  等逐文件 `grep -c` 横扫六层；git 只读命令核对 9 个重构/修复提交的
  `--stat`、`tests/` 是否被动过、v3 套件历史各时点的用例数
  （`git show <c>:file | grep -c "#\[test\]"`）。
- 代码抽查：L07 `Subst`/`SpecSolve`/`Val::VSub` 定义（mod.rs:147/200/182）、
  L09–L12 `unify_pm` 新形态（elaboration.rs）、`PM_FUEL`/`unify_fuel`
  在参考版与孪生版的存在性、孪生模块头注释。
- 未运行 cargo（按 BRIEF 硬约束）；所有计数均为静态计数。

### 逐层测试覆盖矩阵（A1：敏感路径 × 层）

| 敏感路径 | L07 | L08 | L09 | L10 | L11 | L12 |
|---|---|---|---|---|---|---|
| 归一化方案是否可能掩盖真实分歧 | 否¹ | 否 | 否 | 否 | 否 | 否（但见 P2-2/P2-5） |
| 深层嵌套 match（≥3 层） | ✓ bits_adder 4 层 / dependent_match | ✓（继承） | ✓ dependent_match | ✗（≤2 层） | ✗（match_src 为单层普通 match） | ✗（同 L11） |
| 多模式变量依赖解 / Eq 索引推理 | ✓ add_comm/add_assoc 全家 | ✓ | ✓ eq_reasoning/eq_proofs | 部分（stuck_projection_contract 单例） | 弱 | ✗（无 Eq/索引族源） |
| Absurd/Stuck 分支（不可达/不完整/零臂） | ✓ error_cases + v3 | ✓ | ✓ error_cases | ✗（仅 trait_errors） | ✗ | ✗ |
| fuel 耗尽（有界降级/假 absurd） | 仅参考版 tests.rs d=400² | ✗ | ✗ | ✗ | ✗ | ✗（孪生 PM_FUEL 降级路径零覆盖） |
| 宏展开产物进入 match（L11 特征） | — | — | — | — | **✗**（宏用例仅 stringify/展开成 enum） | — |
| trait 求解 × 精化交互（L10 特征） | — | — | — | 弱（无 GADT match + trait 接收者组合源） | 部分（probe_solve_multi_trait） | 部分（probe_solve_multi_trait_recoverable_parity） |
| 决策树编译（L09–L12 共有） | — | — | ✓ | ✓（继承用例） | 弱（仅普通 match 链） | 弱（仅普通 match 链） |
| record/sigma（L08 特征） | — | ✓ product_* 9 项 | ✓ struct heritage ×2 | ✓ l08_heritage | 弱 | 弱（struct_src 浅投影链） |
| canonical 求解（L12 特征） | — | — | — | — | — | ✗（iddfs 仅参考版 Err 重试路径；孪生刻意不移植——已登记） |
| 稳态复用 / packed 对齐钉子 | ✓ / —³ | ✓ / ✓ | ✓ / —³ | ✓ / ✓ | ✓ / ✓ | ✓ / ✓ |
| 探针 probe_* 系列（A2 η/A4 u64/A5 trait/A6 prune/A8 宏递归） | ✗ | ✗ | A6 同型⁴ | A6 同型⁴ | ✓ 全系 | ✓ 全系 |

> ¹ 各层 norm_err 只剥"已文档化偏差"（span 数字 / `?N`），其余正文逐字节比对，
> 不构成掩盖；例外是 L07——Err 正文完全不比（见 P2-5）。
> ² `src/L07_sum_type/tests.rs:1484`（`test_deep_pattern_fuel_budget_regression`，
> 只跑参考版 `run`）；六层 parity 语料中无用例真正触发 fuel 耗尽。
> ³ L07/L09 parity 无 `packed_cells_align_at_least_8`；对齐由源内 `const _` 断言兜底。
> ⁴ L09 `parity_nonlinear_pruning_rev_mask`、L10 `parity_prune_ty_rev_multilevel_nonlinear`
> 覆盖了 A6 同型场景，但未用统一 probe 命名，A2/A5 在这两层无用例。

**矩阵缺口结论**：防护强度从 L07→L12 单调递减。L07 最厚（机制单测 + 三卷
黑盒 + 深 GADT parity）；L11/L12 最薄——**两层都把"快版编译 walk 缺陷区"
（GADT 单臂 head / 依赖索引族）从 parity 整体剔除**，而这一族恰是显式替换
σ 传播最敏感的路径（详见 P2-2）。

## 2. 发现列表

### [P2] L09–L12 无 blackbox 契约套件，L09/L10/L11 模块内置测试零断言——移植层对外行为无跨重构 oracle（影响面：L09/L10/L11/L12）

- 位置：`tests/`（无 `l09_blackbox*`…`l12_blackbox*` 任何文件）；
  `src/L09_mltt/mod.rs:1023/1211`（test2/test1）、
  `src/L10_typeclass/mod.rs:1130–1863`（9 个 `test*`，grep `assert` 仅命中
  非测试代码的 `debug_assert`）、`src/L11_macro/mod.rs:1191–2337`（12 个
  `test*`，0 断言）；`docs/l08-l13-refactor-plan.md` §3。
- 证据：L09–L11 的 mod.rs `test*` 形如 `let result = run(input, 0).unwrap();
  println!("{result}")`（如 `src/L10_typeclass/mod.rs:1130` 起的 test_trait
  全文无断言；对照 `src/L12_canonical/mod.rs:1612–2160` 有约 20 处
  `assert!(result.contains(...))`）。计划文档 §3 验收口径列
  `cargo test --test l{XX}_blackbox*`，这四层没有该目标，口径落空。
- 机制/影响：五个移植提交（`ccfcb87/ad412ab/2129975/58073dd` 等）参考版与
  孪生版**同批**修改，parity 只能保证"两版互相一致"；若两版被同等地改坏
  （尤其 L09–L11 的 println 冒烟"单测"只检 Err 不检输出内容），没有任何
  自动化 oracle 能发现对外行为漂移。目前唯一兜底是
  `docs/explicit-subst-refactor-status.md` §2 声称的"移植前后基线逐字节
  0 diff"——那是一次性手工验证，没有沉淀为回归物。
- 处置建议：为 L09–L12 各补一卷最小 blackbox（可从 parity 源中挑 10–15 个
  锁 `run` 的 Ok 输出片段 + 错误子串）；把 L09–L11 mod.rs `test*` 补上
  `contains` 断言（L12 已是现成样板）。

### [P2] L11/L12 parity 系统性剔除 GADT/依赖索引族，"另案跟踪"的快版缺陷区无跟踪案（影响面：L11/L12）

- 位置：`tests/l11_fast_parity.rs:475–477`（"enum GADT 单臂 head 用例与
  已剔除的 test_index 同族——快版编译 walk 缺陷区，另案跟踪；gadt_src
  生成器保留供 bench 单独使用"）；`tests/l12_fast_parity.rs:9–13`（头部：
  "mod.rs 全部 8 个测试源、trait/impl 实例合成演示源与 get_global 缺名
  panic 用例……在快版上分叉或发散，整体剔除"）、`:146–149`（"依赖无注解
  def 的 Hole 推导——快版 check_universe 对该形态与参考版分叉"）；
  `src/L11_macro/bump_spine_iter.rs:8456`、`src/L12_canonical/bump_spine_iter.rs:8567`
  （`gadt_src` 定义存在、parity 未用）。
- 证据：`grep -rn "另案" docs/` 只命中 `docs/explicit-subst-refactor-status.md`
  对 L13 的记载；status doc §3 的 P2 登记清单（无 solvable 白名单、occurs
  扫描面等）**不含**上述任何一条分歧族；§2 验收表也没有 L12 行（连验收
  数字都没记）。另注：L12 头注释写"mod.rs 全部 8 个测试源"，实际 mod.rs
  有 9 个 `#[test]`，口径亦未对齐。
- 机制/影响：被剔除的恰是显式替换最敏感的路径（GADT 索引精化、单臂
  可达性、`?N` 洞与宇宙判定）。L12 的 `deep_workloads_parity` 用
  natadd/match_src/struct_src 全是普通 enum 单层 match——`58073dd` 给
  L12 mod.rs 增加的 446 行 σ 机制，其特征行为在 parity 上覆盖为零；
  快版在这些缺陷区内的回归（含 panic vs Err 判定翻转）不会被发现。
  "缺陷另案跟踪"的说法在仓库里找不到"案"。
- 处置建议：在 `docs/explicit-subst-refactor-status.md` §3（或新建
  known-divergences 文档）逐条登记 L11/L12 剔除族（触发源、两版实际
  行为、裁定依据）；至少把"判定一致（Ok/Err 同型）"级别的弱 parity
  加回剔除族，而不是整族消失。

### [P2] design doc §9.5 要求"各层移植必须复刻"的钉子用例未复刻；L07 README/孪生头注释宣称的"l07_fast_parity 逐字节保证"不实（影响面：全部六层）

- 位置：`docs/l07-dpm-refactor-design.md:180–184`（§9.5："`tests.rs` 的
  `test_fn_typed_index_slot_applied_after_refine` 钉死，各层移植必须复刻"）；
  `src/L07_sum_type/tests.rs:1454`（唯一载体，只跑参考版）；
  `src/L07_sum_type/README.md:391–393` 与 `src/L07_sum_type/bump_spine_iter.rs:23`
  （"……钉死，l07_fast_parity 逐字节保证"）。
- 证据：`grep -rn "Foo g\|refl_e\|slot_applied" tests/ src/L08* … src/L12*`
  零命中——该用例源不在 l07_fast_parity，也不在任何其他层的 tests.rs /
  parity。L08 README（`src/L08_product_type/README.md:318–320`）已诚实
  承认"本层测试集无 L07 那条钉死用例的同构物，故 l08_fast_parity 保持
  全绿"，与 design doc 的"必须复刻"直接矛盾且无裁定；L09–L12 README
  对此只字未提。
- 机制/影响：这是本轮重构相对旧版**唯一登记在案的有意行为差异**（frcs 对
  "已解 rigid + 非空 spine"做解析应用）。参考版 L07 有单测；孪生 L07 与
  L08–L12 的参考/孪生共四类宿主上该路径完全没有自动化测试。孪生版若在
  移植中丢失"v_app 带 v_applicable 守卫"的解析应用分支，现网测试全绿。
- 处置建议：把该源加入 l07_fast_parity（即兑现 README 的既有宣称），
  并按 design doc §9.5 复刻到 L08–L12 各自 tests.rs（或至少 parity）。

### [P2] 移植后层文档未随代码更新：L09/L10/L11 README 与 L11/L12 孪生模块头仍描述已删除机制、否认已存在的燃料池（影响面：L09/L10/L11/L12）

- 位置与证据（均已对照 HEAD 代码逐条核实）：
  - **L09 README**（`src/L09_mltt/README.md:24–47`，最后更新 2026-09-11
    `295ea69`，早于移植 `ccfcb87`）："无 L07/L08 的 unify/force fuel——
    不适用……加 fuel 属不可触发的死护栏"。现状：`src/L09_mltt/mod.rs:412/416`
    已有 `unify_fuel`/`UNIFY_FUEL`，孪生 `bump_spine_iter.rs:576–581` 已有
    `PM_FUEL`（均本轮移植引入）。同节 `:9/:31–32` "无 pm 机制故无宿主 /
    L09 无 pm_defs（grep 0 命中）"的前提也被本轮推翻（L09 现有
    `unify_pm`+`Subst` 显式替换形态）。
  - **L10 README**（`src/L10_typeclass/README.md:68–70`）："孪生
    bump_spine_iter 无燃料池……frcs 的 lookup 命中不做有界降级"——
    `dbe79cf` 已补齐（`src/L10_typeclass/bump_spine_iter.rs:937–947`；
    同文件 `:2637–2638` 深处注释已改，README 未改）。
  - **L11 README**（`src/L11_macro/README.md:27`）："无 unify/force fuel：
    参考版与快版一致无燃料"——两层皆错：`src/L11_macro/mod.rs:449–465`
    有 `UNIFY_FUEL`（`2129975` 引入），孪生 `bump_spine_iter.rs:963–973`
    有 `PM_FUEL`（`dbe79cf`）；该条引用的"快版头注释"本身已订正，README 没订正。
  - **L11 孪生模块头**（`src/L11_macro/bump_spine_iter.rs:40–47`）：
    "模式特化不走 pm_defs：参考版走 check_pm/unify_pm + `Cxt::update_cxt`/
    `refresh`——把精化等式直接改写进环境……快版镜像为 lvl_types 表 +
    双轨迹撤销"以及 "**unify 无燃料**、无 pm 臂、无 (Obj,Obj)/宽松臂"。
    参考版 `update_cxt`/`refresh` 已删净（grep 0 命中定义），快版已换
    `SubstV`——**同文件 `:285` 自称"替代旧的 update_cxt/refresh"**，
    头注释与自身实现矛盾。
  - **L12 孪生模块头**（`src/L12_canonical/bump_spine_iter.rs:62–66`）：
    同款 update_cxt/refresh bullet 未更新（燃料断言已在 `:2825–2840`
    订正，这条漏了；`:375` 同样自称"替代旧的 update_cxt/refresh"）。
- 说明：L12 README"快版 unify 无 Decl 头展开燃料臂"经核仍属实
  （`:2832–2839` 孪生确无该展开臂），**不**在此列；L10 孪生模块头
  （`:49`）已被移植提交更新为"模式特化 = 显式替换（SubstV/VSub/frcs）"，
  是四层里唯一改了头的。
- 机制/影响：README 是 BRIEF 指定的"机制表述权威口径"，L09 的 README 现在
  描述一个不存在的架构（"无 pm 机制、无 fuel"），L11 README 直接断言与
  代码相反的事实。后续移植（如 L13 重试）或评审若以这些 README 为依据会
  得出错误结论。
- 处置建议：一次文档收口提交：L09 README 时代缺口第 2 条改写为"移植后
  已带 unify_fuel/PM_FUEL，原'不适用'论证仅对移植前架构成立"；L10/L11
  README 燃料 bullet、L11/L12 孪生头的 pm/fuel bullet 按各自 `:2637`/
  `:2825` 的订正文案同步。

### [P2] L07 parity 的 Err oracle 弱于其余五层：Err 只判 Ok/Err 同型，不比正文——与 BRIEF 宣称判据不符（影响面：L07）

- 位置：`tests/l07_fast_parity.rs:49–64`（oracle 的
  `(Err(_), Err(_)) => {}` 臂）。
- 证据：BRIEF §0 宣称判据为"Err 文案里 Span 偏移与 `?N` meta 编号比对前
  归一化"；L08–L12 均实现为归一化后 `assert_eq!` 正文
  （`tests/l08_fast_parity.rs:96`、`l09:119`、`l10:114`、`l11:127`、
  `l12:129`），唯独蓝本层 L07 不比。另外归一化口径本身跨层不齐：
  `?N` 剥离仅 L11/L12 有（L08/L09/L10 的 norm_err 无 `'?'` 分支，
  grep `"b'?'"` 计 0）；`start_offset/end_offset/path_id` 剥离 L08 也没有
  （grep `start_offset` 计 0，L09–L12 均有）。
- 机制/影响：快版把 A 类错误报成 B 类（如"分支不可达"vs"can't unify"，
  除已知 span/fuel 尾注差异之外的新漂移）在 L07 不会被发现。L07 是其余
  五层的移植蓝本，它的 Err 一致性恰恰是最该钉死的。L08 缺 `start_offset`
  剥离属反向问题（过严、潜在假红——现绿说明未触发，记为脆弱性）。
- 处置建议：把 L12 的 `norm_err`（覆盖最全）下沉复用到 L07 parity，
  并统一六层归一化口径（`?N` + span 数字 + Debug-Span 偏移三件套）。

### [P3] 文档测试计数多处失真，同文档内部自相矛盾（影响面：L07/L08/文档）

- 位置与证据（静态计数，未跑 cargo）：
  - `src/L07_sum_type/README.md:328`"--lib 44 个测试"：实际 45
    （tests.rs 41 + parser/mod.rs 3 + lex.rs 1；status doc 亦记 45）。
  - `src/L07_sum_type/README.md:355`：l07_blackbox_v3 "86 个（85 可跑 +
    1 个 --ignored）"：实际 47 个（46+1）；历史各时点 41/46/47
    （`git show 7545ff0/17dbeba/7cfbb8e:tests/l07_blackbox_v3.rs`），
    从未有过 85。同文件同段 v1=49、v2=53 与实际一致，说明"例"的口径
    就是 `#[test]` 数。
  - `docs/l07-dpm-refactor-design.md:153–154`（§7 验收口径"39 内部 +
    …v3(85) + l07_fast_parity(57)"）：实际 45 / 47 / 18。
  - `src/L08_product_type/README.md:236–239`"l08_fast_parity 77（28 个
    parity 用例）" vs 同文件 `:321–322`"l08_fast_parity 80 全绿"：
    同文档 77/80 矛盾；静态口径 31 own + 49 lib = 80。
  - `docs/explicit-subst-refactor-status.md` §2 表（`:51–57`）：L07 行
    "48/51/91 黑盒"（v3 实为 47）；**缺 L12 行**（L12 已移植完成却无
    验收数字）；L09 "31 parity"、L10 "32"、L11 "37" 与静态口径
    （26+6=32 / 18+13=31 / 15+16=31）对不上——计入 needs-verify NV-1。
- 机制/影响：测试清点是回归防护的账本；虚高一倍的计数（v3 85 vs 47）
  会让人高估防护面。不影响运行行为，故 P3。
- 处置建议：文档收口时以 `cargo test` 实测数为准统一改一遍，并注明
  "parity 目标含 #[path] 引入的 lib 用例"的计数口径（L08 README :236
  已有正确示范）。

### [P3] 顶层 README 仅给 L07 标注显式替换机制，L08–L12 同批移植未提及（影响面：顶层文档）

- 位置：`README.md:137`、`README.zh.md:108`（L07 行有"精化为显式替换、
  对齐 dpm-nbe"）；`:138–142`/`:109–113` 的 L08–L12 行无此标注。
- 证据：`cc8ab08` 只改了 L07 行与灵感来源段。
- 机制/影响：读者从顶层架构表会以为显式替换只存在于 L07；L08–L12 的
  精化载体实际已同批更换。属表述完整性问题。
- 处置建议：L08–L12 行补一句"精化为显式替换（同 L07 蓝本）"，或指向
  `docs/explicit-subst-refactor-status.md`。

## 3. needs-verify 清单（验证方法）

1. **status doc §2 的 L09/L10/L11 parity 计数（31/32/37）口径**
   静态计数无法复现（可能含 lib-in-module 用例、或按子用例计）。
   验证：`CARGO_TARGET_DIR=<独立目录> cargo test --test l09_fast_parity -- --list | grep -c ": test"`（及 l10/l11/l12），对照 "31/32/37/?"。
2. **L07 补 Err 正文归一化比对后是否暴露新分歧**
   L07 孪生 Err 文案从未被逐字节比过（仅 span/fuel 尾注属已登记差异）。
   验证：临时把 `tests/l07_fast_parity.rs` 的 oracle 换成 L12 式
   `norm_err` + `assert_eq!` 跑全量；若出现正文分歧逐条裁定是登记偏差
   还是裂缝。
3. **L12 被剔除的 mod.rs 测试源在快版上的实际行为未逐条登记**
   头注释只给了"分叉或发散"的四类归因。验证：对
   `src/L12_canonical/mod.rs` 9 个 `test*` 源逐个以 `run` 与 `run_fast`
   对照，把 Ok/Err 判定、Err 归一化正文、是否 panic/发散记入分歧台账
   （与 P2-2 的登记建议合并执行）。

## 4. 设计决定讨论（不属 bug，只记录）

- **"删除清单"的字面 vs 实现**：`docs/l08-l13-refactor-plan.md` §2.1 写
  "删除 `unify_pm`/`update_cxt`/`refresh`/`Infer.global`（或等价物）"。
  实测：`update_cxt`/`refresh` 六层确已删净；`unify_pm` 在 L09–L12
  （参考 + 孪生）**名字保留但机制已换**（现为显式替换的宿主，见
  `src/L10_typeclass/elaboration.rs:121` 起的注释与实现）；
  `Infer.global` 在 L09/L10 保留（`mod.rs:408/418`），承载的是全局名表
  （非精化职责），符合计划但书"承载非精化职责，拆分之"。status doc §3
  已按"机制删除、名字保留"的口径自洽登记。建议计划文档补一行注记即可。
- **L09–L12 孪生 `unify_pm` 无 solvable 白名单**（任意裸 rigid 可解）与
  L07 bind-slot 白名单的有意分歧：status doc §3 已登记为 P2 不修，D6
  无新证据推翻。
- **L12 孪生不移植 canonical/iddfs**：README 登记为"Err 重试路径专属，
  不影响判定与 Ok 输出"；代价是 iddfs 的成功路径在孪生侧无等价物可测
  （参考版侧由 mod.rs `test*` 覆盖，尚有断言）。属登记过的取舍。
- **归一化口径跨层漂移**（`?N` 只有 L11/L12 剥、`start_offset` L08 不剥）
  是测试代码层面的口径不齐，不是行为分歧；若未来 L08–L10 出现两版 meta
  编号不同的 Err，会表现为测试假红而非假绿，方向安全。
- **`#[ignore]` 卫生良好**：全部 7 处（l07_blackbox 1、l07_blackbox_v2 2、
  l07_blackbox_v3 1、l08_blackbox 1、l08_blackbox_v2 2）均为深度/格式
  探针，注释写明用途、复跑方式（`-- --ignored --nocapture`）与风险
  （如"超过阈值会栈溢出终止测试进程"）。无 `#[cfg(disabled)]`、无注释掉
  的测试。无发现。
- **blackbox 断言质量总体扎实**：抽查 L07/L08 三卷，断言为具体输出片段
  的 `contains` 与错误子串匹配，未发现恒真断言；Err 边界（不完整 match、
  不可达臂、重定义、截断不 panic、Display 一致性）均有覆盖；"只测 happy
  path"的套件不存在。a5eb72b 对 `tests/l07_blackbox.rs` 的 7 行改动是
  头注释契约更正（match 行位置的措辞），属合理契约更新。
- **旧评审 `docs/review-l01l12/` 过时段落清单**（按 BRIEF 要求只列不改）：
  - `a3-r1.md:73/187`：以 `update_cxt` 为 L09 链上环节的描述——该机制已
    删除；`:251`"L07 README §1–§10 与代码机制（pm_defs/force 两条读点…）
    一致"——README 已重写、pm_defs 已删。
  - `ROUND2.md:80`：`lvl2ix`/rename/quote/Raw::Var/`update_cxt` 边界
    同口径——update_cxt 不复存在。
  - `FINAL.md` §3.1：L10/L11/L12 孪生 unify 重借的行号
    （`:3729/:2385/:2436` 等）——三个文件被移植大幅重写
    （+1262/+1018/+915 行），行号全部漂移，所指代码是否仍在需 D2 复核。
  - `FINAL.md` §3.4"L10 参考版缺 L08/L13 的 unify/force fuel 护栏"——
    移植后 L10 参考版已有 `unify_fuel`，该残余已消解。
  - `FINAL.md` §3.4"L12 快版 v_to_ref_val 链头 unreachable!(:5771)"——
    行号漂移（现文件 >8600 行），需重新定位。
  - `FINAL.md` §3.2 的假匹配修复及其回归
    （`synth_rigid_generic_not_falsely_matched`）仍然有效，不算过时。

---

verdict：P0:0 P1:0 P2:5 P3:2 needs-verify:3
