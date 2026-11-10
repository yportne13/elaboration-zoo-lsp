# L09/L10 参考版借 L07 新优化 · 审计与落地报告

> 角色：audit/impl（analyst-l10）。工作树 `C:\ezl-wt-l09l10`，分支 `feat/l09l10-audit`。
> 构建目录 `CARGO_TARGET_DIR=C:\ezl-target-all-l09l10`（F: 不构建；可执行文件/临时 raw 均在 C:
> 的 `C:\ezl-target-all-l09l10\{release,baseline-bin,bench-raw}`）。
> 基线：`feat/all-layers-hardening` @ **`deef97f7`**（含 Lead 的 L08 merge 修复 `07f737d6`）。
> 标注：`[码]` 源码锚点 / `[实测]` 本轮门禁或 A/B / `[历史实测]` 既有文档 / `[推断]`。

## 0. 基线与前置修复

- 原始基线 `1a1cab3b` **不编译**：merge 把 remote 旧 L08 `match_cmp_depth` 守卫 auto-merge 进了
  本地 budget 版 `src/L08_product_type/unification.rs`，而 `mod.rs` 侧已被 2026-11-08 review 轮
  改为 `match_cmp_budget` ⇒ E0425/E0609（仅 L08，L09/L10 自身无错）。
- 处置：Lead 在 `feat/all-layers-hardening` 打 `07f737d6`（删 depth 残余，与本审计的诊断一致），
  本 branch 已 fast-forward 到 `deef97f7`。**本 worktree 未保留任何 L08 改动**（临时未提交补丁
  已 `git checkout --` 丢弃）。
- 基线可编译性复核：`cargo build --release --bin l09bench --bin l10bench` EXIT=0 `[实测]`。

## 1. 轴 A：FxHashMap 覆盖（L09/L10 参考版）

### 1.1 清单（全部 std HashMap/HashSet 逐处核对，含顺序依赖判定）

| # | 层 | 位置 | 容器 | 使用方式（是否迭代/顺序依赖） | 处置 |
|---|---|---|---|---|---|
| A1 | L09 | `mod.rs:445` `Infer.global: HashMap<Lvl, VTy>` | std HashMap | `insert`（elaboration.rs:400/404/507/510）、`len`（:393/503 定 global_idx）、`get`（mod.rs:761 eval Var）。**无迭代** | 换 FxHashMap（commit 1） |
| A2 | L09 | `unification.rs:29` `PartialRenaming.ren` | std HashMap | `lift`/`skip` 每 prune 步整表 `clone`（:33/:49）、`invert_go` insert/remove/contains（:71-77）、`prune_vflex_go` get（:190）。**无迭代** | 换 FxHashMap（commit 1） |
| A3 | L09 | `unification.rs:64` invert 的 `HashSet<u32>` | std HashSet | `contains/insert/is_empty`（:71-72/:99）。**无迭代** | 换 FxHashSet（commit 1） |
| A4 | L09 | `pattern_match.rs:331` `reported` | std HashSet | 仅 `insert` 去重（:349） | 换 FxHashSet（commit 1） |
| A5 | L10 | `mod.rs:455` `Infer.global` | std HashMap | 同 A1（elaboration.rs:354/361/371/479/483/486；mod.rs:861 get） | 换 FxHashMap（commit 3） |
| A6 | L10 | `mod.rs:468` `trait_out_param` | std HashMap | `get`（elaboration.rs:574；unification.rs:476）、`insert`（:633）。**无迭代** | 换 FxHashMap（commit 3） |
| A7 | L10 | `mod.rs:467` `trait_definition` | std HashMap | `insert`（elaboration.rs:632）；`trait_wrap` **每方法调用整表 clone 后 `.iter()`** 找同名方法（:1011-1018）⇒ 迭代序决定多候选 trait 的 "first wins" | 换 FxHashMap（commit 3；顺序语义见 §1.2） |
| A8 | L10 | `typeclass.rs:148` `Synth.class_instances` | std HashMap | `new_trait/impl_trait_for` entry/insert（:164-172）、`new_subgoal` `get(...).unwrap().clone()`（:299，每子目标 clone 实例 Vec）。**无迭代** | 换 FxHashMap（commit 3） |
| A9 | L10 | `typeclass.rs:150` `Synth.assertion_table` | std HashMap | `insert`（:289）、`get_mut`（:341）、`clear`（:178）；**兼答案缓存**，无迭代 | 换 FxHashMap（commit 3） |
| A10 | L10 | `typeclass.rs:357` `Subst = HashMap<u32, Typ>` | std HashMap | match_typ 的 `insert/get`（:362/:405/:408）、apply_subst_*（:360-387） | 换 FxHashMap（commit 3） |
| A11 | L10 | `unification.rs:27/62` `PartialRenaming.ren` + `HashSet` | std | 与 A2/A3 同构（lift/skip/invert/prune_vflex） | 换 FxHashMap/FxHashSet（commit 3） |
| A12 | L10 | `pattern_match.rs:321` `reported` | std HashSet | 仅 `insert`（:339）；原文件里 `BTreeSet/HashMap` import 本就未使用，随手移除 | 换 FxHashSet（commit 3） |
| A13 | L10 孪生 | `bump_spine_iter/typeclass.rs:242/244` `TraitState.definition/out_param` | std HashMap | 与 A6/A7 同构；孪生 `machine.rs:2306` 有同款 `.definition.iter()`（trait_wrap 歧义顺序） | 与 A7 同步换 Fx（commit 3，保 ref/twin 同序） |

**已在使用 Fx / 无需改**：`Infer.global_names`（L09 mod.rs:456 / L10 mod.rs:465）、`src/bimap.rs` 双向表
（`:1,18-19` 已 FxHashMap）、孪生 by_name/by_lvl/quote_memo 等。
**N/A**：L09 `elaboration.rs:352` 的 `.collect::<HashMap>` 在**注释块**内（旧决策树残留），编译不生效。

### 1.2 `trait_definition` 的顺序语义（唯一有迭代的表）

`trait_wrap` 把"所有含同名方法的 trait"逐候选 `collect` 后取 `first()`，多解时选择取决于迭代顺序
[码 elaboration.rs:1011-1018、1079-1083；孪生 machine.rs:2306]。std HashMap 的迭代序由每进程随机
种子决定 ⇒ **该选择现状本就不可复现**。换成 FxHashMap 后变为确定性顺序（同一插入序列/容量下），
即"随机 → 可复现"，语义仍是"按表序取首个"，不引入新选择规则。收益：CI/parity/A-B 可复现；代价：
若某歧义程序的既有行为恰被某次随机序"选中"，理论上可能翻转（本仓 suite 无这类歧义负例，见 §4）。
因此该表单独归入 commit 3 并在本报告登记，便于必要时单独回退。

## 2. 轴 B：`src_names` / `global_names` / BiMap 还有没有深拷贝

- **BiMap 已是 FxHashMap**（`src/bimap.rs`），无 SipHash 税。
- 参考版名字表实际是两张：`Cxt.src_names: BiMap<String, Lvl, Rc<VTy>>` 只装**局部**条目
  （`Cxt::new` 的 2 个 builtin + 当前 def 内 binder/let）[码 L09 cxt.rs:30,99；L10 cxt.rs:22-29]；
  顶层 def/enum/构造子真名在 `Infer.global_names`：**append-only、随 Infer 存续、不随 Cxt 克隆**
  [码 L09 mod.rs:456-465；L10 mod.rs:456-465 注释]。2026-09-20 的 O(D²) 修复已把旧"顶层名累积进
  Cxt.src_names"的根因消除（同款见 `docs/bench-matrix-2026-09-20.md` §B）。
- 仍存在整表拷贝：`Cxt::bind`/`new_binder`/`define` 各一次 `src_names.clone()` [码 L09 cxt.rs:116,143；
  L10 cxt.rs:112-150]，`subst_cxt` 每臂重建 BiMap [码 L09 cxt.rs:169-174]。表规模 = O(局部绑定数)
  （个位数~几十），**不是 O(D)**；`Infer` 本身不再被 clone（旧"三处 self.clone() 整个 Infer"已删，
  见 L09 mod.rs:463 / L10 mod.rs:475 注释）；`global_names` 无 clone 点（grep `.global_names.clone` 0）。
- **L07 `NameState`/trail 结论：不适用（根因不在）**。L07 的改动（`src/L07_sum_type/cxt.rs:76-137`，
  `Rc<RefCell<NameState{map,trail}>>` + `name_mark` 惰性 `unwind`）解决的是"名字表含顶层 decl、且
  `Rc::make_mut` 强计数恒 2 ⇒ 每次 bind 深拷整表 O(D²)"（同文件 :79-88 注释）。L09/L10 既无该合成表
  （拆分后局部表小），也没有 `Rc::make_mut`（grep 0 命中）。套 trail 只会把**小表**的 O(B) clone 换成
  `RefCell`+mark 机制：复杂度上升、收益≈0 ⇒ 不改。
- 孪生 `name_map`+`name_trail`（`src/L07_sum_type/bump_spine_iter/machine.rs:139-141`）是孪生侧影子
  索引；L09/L10 孪生已有 `by_name/by_lvl`（`bump_spine_iter/machine.rs:43-46` / `546-549`）且
  `subst_cxt` 同步维护 ⇒ N/A。

## 3. 轴 C：L07 其它优化在 L09/L10 的适用性

| L07 优化（锚点） | L09/L10 现状 | 结论 |
|---|---|---|
| **Locals 脊 Rc**（`src/L07_sum_type/syntax.rs:12-18`，commit `65d4512a`） | 已采用：`Rc<Locals>` [码 L09 syntax.rs:21-26；L10 syntax.rs:19-24] | **已有，N/A** |
| **decl 表 COW**（`Rc<Decls>` + `make_mut` 强计数 1 就地写；`src/L07_sum_type/cxt.rs:339-346`、`elaboration.rs:200-230`） | L09/L10 **无 decl 表**（sentinel global 世界）；`global_names` 是 Infer 内 append-only 普通表，无 clone、无 make_mut | **N/A（root cause 不存在）** |
| **NameState + trail**（`cxt.rs:76-137,374-448`） | 见 §2 | **不适用**（收益≈0、复杂度↑） |
| **孪生 name_map + trail**（`machine.rs:139-141`） | 孪生已有 by_name/by_lvl | **已有，N/A** |
| **U2：穷尽 match 跳过覆盖探测**（commit `a78daec7`，`src/L07_sum_type/pattern_match.rs` 覆盖循环） | L09/L10 `compile()` 对每个构造子无条件 `probe_accessible`（每探测一次 meta 快照 + 索引特化方程），结果仅用于"缺构造子"告警 [码 L09 pattern_match.rs:213-226；L10 :212-225] | **✅ 已落地**（commits 2/4）：判据 `fully_covered` 与循环体同源（同一个 `covers`），全部覆盖时循环不可能产告警 ⇒ 判定逐值等价 |
| **U1：probe 借用 decl 表**（`a78daec7`） | L09/L10 probe 直接查 `src_names/global_names`，无 decl 表、无整表 clone | **N/A（无对应浪费）** |
| 三档 UnifyKind / occurs 传递 / MATCH_CMP 分档（L07 hardening） | 属正确性/诊断层，非"新优化"；L09–L13 未回灌（已登记 FACTS/CONVENTIONS） | 不属本任务；动诊断语义，需另立任务 |

## 4. 落地项（4 个 commit，均基于 `deef97f7`）

| # | commit | 内容 | 文件/LOC |
|---|---|---|---|
| 1 | **`0bf8118f`** | perf(l09): FxHashMap for Infer.global / PartialRenaming / coverage dedupe set | 3 files, +7/−8 |
| 2 | **`828df98d`** | perf(l09): skip coverage probes for exhaustive matches (port L07 `a78daec7` U2) | 1 file, +24/−12 |
| 3 | **`f32734c6`** | perf(l10): FxHashMap for global/trait tables + Synth maps + PartialRenaming（含孪生 TraitState 同步） | 5 files, +14/−16 |
| 4 | **`9b37c278`** | perf(l10): skip coverage probes for exhaustive matches (port L07 `a78daec7` U2) | 1 file, +24/−12 |

## 5. 门禁（全部 EXIT=0）

| 命令 | 结果 | 备注 |
|---|---|---|
| `cargo build --release --bin l09bench --bin l10bench` | OK（deef97f7 基线重建） | — |
| `cargo test --release --lib L09_mltt` | **10 passed / 0 failed** | commit 1+2 后 |
| `cargo test --release --test l09_fast_parity` | **39 passed / 0 failed** | 同上 |
| `cargo test --release --lib L10_typeclass` | **25 passed / 0 failed** | commit 3+4 后 |
| `cargo test --release --test l10_fast_parity` | **46 passed / 0 failed** | 同上 |
| blackbox | **N/A** | `tests/` 下无 `l09_blackbox*`/`l10_blackbox*`（已验证；L09/L10 无该套件） |

判据覆盖：L09/L10 的 parity 是"Ok 逐字节 / Err 判定 + span 归一化"双引擎对撞；L09 39 例含
enum/match/struct/投影/宇宙/深负载/σ 跨轮回收；L10 46 例含 trait 全家 + golden trait tostring/say +
outParam 链 + 深负载 + 嵌套覆盖正负例。上述两轮全绿 ⇒ FxHashMap（含 `trait_definition` 顺序变化）
与 U2 均未改变可观察行为 `[实测]`。

## 6. A/B 性能（2026-11-10 05:55–05:57 安静窗口，已测）

- 窗口确认：测前/测后 `Get-Process cargo,rustc,rustc_driver` 均为 **0**（Lead 协调暂停 l08/l12 线）。
- 基线二进制：`C:\ezl-target-all-l09l10\baseline-bin\{l09bench,l10bench}.exe`（`deef97f7` 构建）；
  新二进制：`...\release\`（4 commits 合并后构建）。raw：`C:\ezl-target-all-l09l10\bench-raw\final-ab{,2}\`。
- 协议：每个负载每 rep = base→new 相邻各 1 次进程；综合轮 3 rep + 复核轮 5 rep；每次 `--rounds 5`；
  表内取各侧 **min of reps**（min 与 median 同向才采信；跨 session 不比较绝对值）。
- 结果（ms，min；ratio=new/base，<1 为变快）：

| 负载 | k | 实现列 | base | new | ratio |
|---|---:|---|---:|---:|---:|
| L09 match | 9 | basic | 0.127 | 0.116 | **0.913** |
| L09 match | 10 | basic | 0.136 | 0.126 | **0.926** |
| L09 match | 11 | basic | 0.151 | 0.139 | **0.921** |
| L09 match | 11 | fast_ss | 0.054 | 0.054 | 1.000 |
| L09 enum | 9 | basic | 0.742 | 0.715 | 0.964 |
| L09 church | 11 | basic | 3.524 | 3.594 | 1.020（噪声带） |
| L09 church | 11 | fast_ss | 0.259 | 0.256 | 0.988 |
| L10 match | 9 / 10 / 11 | basic | 0.079 / 0.087 / 0.101 | 0.077 / 0.086 / 0.092 | 0.975 / 0.989 / **0.911** |
| L10 match | 11 | fast_ss | 0.054 | 0.054 | 1.000 |
| L10 church | 11 | basic | 1.225 | 1.292 | 1.055（噪声带；k9/k10 = 0.96/1.01） |
| L10 traitchain | 9 | fast_ss | 38.285 | 39.489 | 1.031（复核轮；综合轮 1.044） |
| L10 traitchain | 9 | fast | 42.020 | 39.936 | 0.950（同负载两列方向相反 ⇒ 噪声） |

- 解读：
  1. **L09 参考版 match 编译期 −7%~−9%**（k=9/10/11 三档一致；min 与 median 同向）——与 U2 机制预期
     一致（每 ctor 的 meta 快照 + 索引特化方程探测被整轮跳过）；L10 match 在 k=11 亦测得 **−8.9%**
     （k=9/10 仅 −1%~−3%，负载小、探测本身更便宜）。
  2. **孪生列不变**（fast/fast_ss 基本 1.000 ± 2%）：两层 U2 只改参考版 `compile()`；Fx 虽含 L10 共享
     `typeclass.rs`，但 traitchain 两列方向相反（+3.1%/−5.0%）= 机器噪声带，无稳定变化。
  3. 其余负载在噪声带（L09 enum −3.6% 可算轻微正收益；church ±2%~5% 混合）。
  4. **归因限制**：A/B 对比的是"4 commits 合并后 vs 基线"，**未逐 commit 分离**（逐 commit 重建 4 次
     release 会超出窗口）。match 的 −8% 主要归因 U2（L07 同 commit 自测 −10.7%@k13 `[历史实测]`），
     Fx 贡献预计在噪声内 `[推断]`；若要严格归因需在安静窗口重建 c1/c2 中间二进制。
  5. 跨 session 漂移个案：L10 match k11 basic 在综合轮/复核轮的 base 分别为 0.092/0.101（9% 漂移），
     故只用**同 session 交错比值**判读。
- 作废数据留档：05:31 争用窗口 smoke（L10 match k=9 basic 0.154ms、traitchain fast_ss 80.9ms，比基线
  慢 ~2×）——同期 12+ rustc 打满 CPU，不用于结论。

## 7. 结论

1. **落地 4 项**（FxHashMap ×2 层、U2 覆盖探测跳过 ×2 层），全部通过各自 lib + parity 门禁；
   判定：低风险、可合并候选。commit 1/2/3/4 = `0bf8118f`/`828df98d`/`f32734c6`/`9b37c278`。
   **A/B（安静窗口，§6）**：L09 match 编译期 **−7%~−9%**（k=9/10/11 一致）、L10 match k=11 **−8.9%**；
   孪生列不变、其余负载在噪声带；收益主要来自 U2（覆盖探测跳过），Fx 贡献在噪声内 `[推断]`。
2. **N/A 三项**（有据）：L07 `Locals Rc` 已采用；`decl 表 COW` 因无 decl 表不适用；
   `NameState/trail` 因 global_names 设计已消除根因、且会引入不必要的共享可变结构 ⇒ 不改。
   `U1（probe 借用 decl 表）` 亦 N/A。
3. **明确未做**：L07 hardening 的正确性/诊断类改动（三档 `UnifyKind`、occurs 传递、MATCH_CMP 分档）
   不在"性能优化"范围，且会改诊断语义，需另立任务；L09/L10 的 `src_names` 残余 O(B²/def) 登记为
   已知小项（B≤几十，见 §2）。
4. **已补**：A/B 数字见 §6（05:55–05:57 安静窗口，0 竞争进程）。报告与 4 个 commit 目前均为**未合并**
   状态，工作树干净。
5. 环境/复现：Windows、Rust 1.98.1、`CARGO_TARGET_DIR=C:\ezl-target-all-l09l10`；
   复现命令即 §5 各行 + §6 的 bench 行；F: 未构建。
