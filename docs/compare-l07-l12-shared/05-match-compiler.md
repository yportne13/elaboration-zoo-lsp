# 05 · 模式匹配编译（pattern_match.rs / shape.rs / 孪生 compiler.rs）

> 角度：模式匹配编译。对象 = L07_sum_type ⟷ L12_canonical，HEAD 8f4287ae。
> **锚点简写**：`R:x:NN` = `src/L07_sum_type/x:NN`；`C:x:NN` = `src/L12_canonical/x:NN`。
> 三文件行数：pattern_match.rs 850/850、shape.rs 120/120、bump_spine_iter/compiler.rs 676/679。

## 0 结论摘要

本角度**没有找到语义面的 E3**。三文件里 `pattern_match.rs` 自 L07 起六层逐字节相同（SHA256 `5C5988A982…`，35328 B），
`shape.rs` 是 2026-11-23 从 L07 移植回 L12 的新文件、119/120 行同，孪生 `compiler.rs` 的 44+/41- 全部是 **L08 一次成型**
（L08 版 28442 B 与 L12 逐字节同），L09–L12 原样继承。所以「L12 的匹配行为差异」不来自编译器→引擎的**接口**
（ref 侧 11 个方法签名全同），只来自两处孪生侧实现搬家 + 一处 L12 单边新增的值形态边界。

## 1 三文件分级总表

| 文件 | tok | 逐字节? | 实质差异 | 档 | 首次出现层 | 归因 |
|---|---:|:--:|---|---|---|---|
| `pattern_match.rs` | 4927→4927 | **是**（35328 B 全同） | 无 | **E0** | — | 六层冻结 |
| `shape.rs` | 689→692 (+3) | 否（119/120 行同） | 1 行 `Val::U`→`Val::U(_)` | **E1** | **L12**（11-23 `2ad6b1b4`） | L07→L12 移植 |
| `bump_spine_iter/compiler.rs` | 4367→4419 (+52) | 否 | 接口 5 条 + 注释改写 | **E1 / E3-继承** | **L08**（28442 B 即 L12 版） | L08 换掉，L09–L12 继承 |

哈希实测（本机核）：`compiler.rs` L07 `0564542306` ≠ L08 = L09 = L10 = L11 = L12 `CA0984B6DC`；`shape.rs` L07 `22F773D227`（4231 B）→ L08 `9EACF42F2B`（仅删行尾空行）→ L09 = L10 = L11 = L12 `A397E53F1A`（4234 B）。
⇒ 按 MAP §10 A.5：**compiler.rs 的差异是 E3-继承，不是「L12 重写」**；shape.rs 则是少数几条 **11-23 反方向（L07→L12）** 的流动。

## 2 (a) `pattern_match.rs` 逐字节相同 ⇒ 差异只可能来自它调用的 API

### 2.1 参考版（ref）侧：接口**零**变化

pattern_match.rs 只经由 `Infer` / `Cxt` 两个对象触碰引擎。逐一核签名（两版全同）：

| 调用点（C:pattern_match.rs） | 方法 | L07 定义 | L12 定义 | 签名同? |
|---|---|---|---|:--:|
| :150 / :153 | `Infer::eval` / `force` | R:mod.rs:1523 / :964 | C:mod.rs:1535 / :969 | 是 |
| :152 / :367 / :368 / :416 | `meta_refuel` / `meta_snapshot` / `meta_restore` | R:mod.rs:892 / :872 / :879 | C:mod.rs:897 / :877 / :884 | 是 |
| :241 | `Infer::check` | 孪生 `R:machine.rs:836` | C:machine.rs:853 | 是 |
| :390 | `closure_apply` | R:mod.rs:1457 | C:mod.rs:1469 | 是 |
| :448 / :451 / :463 | `reset_unify_kind` / `reset_match_cmp_budget` / `unify_kind` | R:mod.rs:921 / :904 / :934 | C:mod.rs:926 / :909 / :939 | 是 |
| :452 | `Infer::unify` 6 参 `-> Result<(), UnifyError>` | R:unification.rs:894 | C:unification.rs:989 | **逐字同** |
| :164 | `Cxt::bind_slots(&self) -> Vec<Lvl>` | R:cxt.rs:487 | C:cxt.rs:487 | **逐字同** |
| :227 | `Cxt::subst_cxt(&self, &Rc<Subst>)` | R:cxt.rs:453 | C:cxt.rs:453 | **逐字同** |

⇒ **接口面在 L07↔L12 之间是冻结的**：`cxt.rs` 的 27 token 差全是 `Val::U`→`Val::U(0)` / `Tm::U(0)` 常量（R:cxt.rs:200-267 / C:cxt.rs:200-267 全为 0），
`Infer::unify` 只少一行 `prof::bump`（R:unification.rs:903 / C:unification.rs:997 起无）。
**所以 L12 匹配语义的差异不可能从接口来解释**——这是本轮最强的一条否定性证据。

### 2.2 孪生（twin）侧：6 条接口变化（5 条接口 + 1 条值表示），全在 **L08** 定型

| # | L07 | L12 | 语义后果 | 档 |
|---|---|---|---|---|
| 1 | `Machine::subst_cxt(&mut self, bump, sub, cxt)` R:machine.rs:664 | 自由函数 `subst_cxt(bump, defs: &[V], sub, cxt)` C:machine.rs:2510 | 不再需要 `&mut self`；**失去 defs 平坦区**（见 §10 第 1 条） | **E3-继承** |
| 2 | `Machine::unify_spec(6 参) -> bool` R:machine.rs:568 | `unify_with(6 参) -> bool` C:machine.rs:663 | 纯改名；**新增入口 `work.clear()/stack.clear()`**（C:machine.rs:692-693，L07 无）→ 早退残留不再跨调用泄漏（稳健性 +） | E1 |
| 3 | `mach.fuel.get() == 0` R:compiler.rs:393 | `mach.fuel_exhausted()` C:compiler.rs:395 | 等价（C:machine.rs:218-220 即 `fuel.get()==0`）；但 C:compiler.rs:357 仍留旧写法 → 同文件两种拼法 | E1 |
| 4 | 无 | `wrap_names` / `restore_names` C:machine.rs:231 / :250，调用 C:compiler.rs:194 / :212 | name_map 影子同步 + 显式撤销；**L07 无此概念**（L07 在 subst_cxt 里整表包） | **E2** |
| 5 | name_map **全量**包裹 + 轨迹回滚 R:machine.rs:724-743（`mark = name_trail.len()` :741） | 只包 `cxt.types` 链上 `source == true` 的节点，且**仅当 tag 变化才写**（C:machine.rs:237-244） | 包裹面**收窄**：非 source 节点 / 不在 types 链上的 name_map 条目，臂内不再被包 σ [推断] | **E2** |
| 6 | `Val::U`（unit）R:bump_spine_iter/syntax.rs:28 | `Val::U(u32)`（层级入打包字）C:bump_spine_iter/syntax.rs:27 | 只影响 `shape.rs:78`；层号恒 0（§4） | E1 |

## 3 (b) 覆盖义务方向：Undecided/Fuel 是否一律按「可覆盖」

| 面 | L07 | L12 | 判定 |
|---|---|---|---|
| `Walk::Undecided` 存在 | R:pattern_match.rs:100-106（注释：**不产生覆盖义务**） | C:pattern_match.rs:100-106 | **逐字节同** |
| 探测成功判据 | R:pattern_match.rs:409 `k != UnifyKind::Absurd`（注释 R:402-404：Undecided/Fuel **按可达处理，保守要求覆盖**） | C:pattern_match.rs:409 | **同** |
| Undecided 文案 | R:pattern_match.rs:257-271 | C:pattern_match.rs:257-271 | **同** |
| `UnifyKind` 三档 | R:mod.rs:628（Absurd/Undecided/Fuel） | C:mod.rs:589 | 同 |
| 档位打点 | R:unification.rs 共 20 处（19 Undecided + 1 Fuel:915） | C:unification.rs 共 20 处（19 + 1 Fuel:1009） | 结构同，行号随增量平移 |

⇒ **(b) 的答案：L12 没有改口径**（不是 L13 那种改法）。承载口径的 `pattern_match.rs` 一个字节都没动，`UnifyKind` 的枚举与打点数也一致。
**但要记一条与层无关的分歧**：孪生 `compiler.rs` 的 `Walk` 无 `Undecided` 变体（R:compiler.rs:62 / C:compiler.rs:62 同），
探测判据是 `.is_ok() || mach.fuel.get() == 0`（R:compiler.rs:352-354 / C:compiler.rs:355-357）——**只有 fuel 耗尽被保守处理，卡住等式（Undecided）被当不可达**，
即孪生侧「算不出来」可豁免覆盖义务。这是 **ref↔twin 分歧**，两版同款，**不算 L07→L12 差异**；且孪生不在产品路径
（`src/lib.rs:52` / `:67` 均 `#[cfg_attr(not(test), allow(dead_code))]`，`Cargo.toml:196 l12-twin` 默认关），可观察面仅限 parity 测试。

## 4 (c) `shape.rs` 在 L12 是否真对齐（+3 token 是什么）

| 问题 | 事实 | 锚点 |
|---|---|---|
| 归属 | 新文件，120 行一次性加入；L07 `6f7e245e`（+120）与 L09–L12 `2ad6b1b4`（四层各 +120）同日 | `git show --stat 6f7e245e` / `2ad6b1b4` |
| 是否对齐 | **是**：两版 119/120 行同；L12 版 = L09 版逐字节（SHA `A397E53F1A`）= 移植件原样 | 哈希实测 |
| +3 token | 唯一差异：R:shape.rs:78 `Val::U` → C:shape.rs:78 `Val::U(_)`；`(`+`_`+`)` 恰为 3 token | :78 双锚 |
| 是否等价 | 该行只问「剥 Π 后是不是宇宙」，`matches!` 忽略载荷；L12 全层构造的 U 层号恒 0（R:cxt.rs:200-267 / C:cxt.rs:200-267 全 `Tm::U(0)`），非零层号只经 formation 的 `max(a,b)` 合成，对 L07 可写的程序不可能出现 ⇒ 判定相同 | **E1** |
| 接线 | 逻辑同、**消费点不同**：L07 在 R:observe.rs:60 / :77（observe.rs 在 L12 不存在）；L12 在 C:elaboration.rs:240 `render_by_shape` / :334 登记；登记条件同为 `if self.lsp_collect`（R:elaboration.rs:287 / C:elaboration.rs:331） | 两版都在用 |
| 可见性 | R:mod.rs:102 `mod shape` / C:mod.rs:44 `pub mod shape`；无跨 crate 消费者（grep `L12_canonical::` 无 shape 引用）→ 无后果 | E1 |

## 5 (d) 孪生 `compiler.rs` +52 token 落在哪些分支

| 增量 | 落点 | 性质 |
|---|---|---|
| **`wrap_sub` 14→16（+2）** | L07 **一次 hoist** 于 R:compiler.rs:555；L12 拆进 3 个 `match sub` 臂：C:compiler.rs:559（None）/ :567（Any）/ :609（Con） | **E1 代码搬移**：`self.sub` 在 `match` 前未被改写，包裹值相同；仅把分配推迟到实际用到的臂 |
| **`VSub` 3→4（+1）** | **四条全在注释里**：R:compiler.rs:140 / :191 / :656；C:compiler.rs:140 / :189 / **196** / :658 | **零机制增量**（MAP §3 的该机制计数在此处是注释计数） |
| 接口搬家 | C:compiler.rs:191 `subst_cxt(bump, &mach.defs, &self.sub, &cxt_arm)` + C:compiler.rs:194 / :212 `wrap_names` / `restore_names` | **E3 / E2**（§2.2 第 1/4/5 条） |
| 借用拆分 | R:compiler.rs:670 一行 → C:compiler.rs:671-673 `let wrapped = …; SubstV::extend(…, wrapped)` | E1（等价，借检友好） |
| 改名 / 访问器 | `unify_spec`→`unify_with`（R:390 / C:392）、`fuel.get()==0`→`fuel_exhausted()`（R:393 / C:395）、`format!("…{}",x)`→`format!("…{x}")` | E1 |
| 其余 ~30 行 | 注释改写，含模块头「2026-09-19 拆分」→「2026-09-23 拆分」（R:compiler.rs:4 / C:compiler.rs:5） | 无（不改语义，但说明 L12 孪生来自更晚的拆分快照） |

⇒ **+52 token 里没有一条语义增量**；真正的 E3 不在 token 数里，而在 `machine.rs` 把 `subst_cxt` 从「写 defs 平坦区」改成「调 `frcs_env` 走 binder 链」。

## 6 (e) 诊断面：措辞 / span / 等级

| 面 | L07 | L12 | 档 |
|---|---|---|---|
| 载体 | `Error(pub String, pub Option<Span<()>>)` R:mod.rs:670 | `C:mod.rs:631` 逐字同 | E0 |
| 聚合 | 全部 `self.errors: Vec<String>`，末尾一次 `Err(Error(join, first_span))`（R/C:pattern_match.rs:325-330） | 同 | E0 |
| **ref span** | 有：`first_span`（R:pattern_match.rs:73 / :199 / :251 / :265）附首条模式错误（:329） | 同 | E0 |
| **twin span** | **无**：`Err(Error::new(self.errors.join("\n")))` R:compiler.rs:277 | C:compiler.rs:279 同 | 两版同款（非层差） |
| 措辞 | 「match 不完整：缺少构造子 {c}」（R/C:187）、「分支不可达：模式 {} 被前面的通配臂遮蔽」（R:165 / C:163）、「构造子 {} 与被匹配类型不相容（分支不可达）{fuel_note}」（R:compiler.rs:399 / C:compiler.rs:401）、「无法判定：… 索引方程无法判定」（R/C:268-271） | **逐字同** | E0 |
| 等级 | 全部 error，无 warning / severity 通道（两版 mod.rs `grep -i warning` = 0） | 同 | E0 |
| 测试钉 | 19 个匹配类测试（`*match*` / `*cover*` / `*absurd*` / `*stale*` / `*undecid*`）全在 | 19 个全保留 + **新增 1 个** `test_absurd_nested_pattern_not_missing_coverage` | E4（无丢失） |

⇒ 诊断面**是同一套**（文案、等级、聚合方式、span 有无——ref 有 twin 无——两版一致）。唯一层间差只是孪生拿不到 span，而这在 L07 亦然。

## 7 已确认等价（不该算差异的清单）

| 项 | 双锚 | 档 |
|---|---|---|
| `PatternDetail` / `PosCover` / `cover_at`（嵌套覆盖判据，ref↔twin 共用） | R:mod.rs:161 / :180 / :188 与 C:mod.rs:112 / :131 / :139 逐字同 | E0 |
| `frcs_env` 实现（两侧都显式「不进 defs 平坦区」） | R:force.rs:764-790 / C:force.rs:712-733 | E0 |
| `bind_slots(defs, &cxt) -> Vec<u32>` | R:machine.rs:1801 / C:machine.rs:2484 | E0 |
| `wrap_sub` / `SubstV::extend` 签名 | R:subst.rs:426 / :123 / C:subst.rs:380 / :128 | E0 |
| `name_mark` / `unwind_names` | R:machine.rs:326 / :331 / C:machine.rs:372 / :377 | E0 |
| `MATCH_CMP_BUDGET = 64` + 每方程 reset | R:mod.rs:801 / C:mod.rs:755；reset 于 R/C:pattern_match.rs:448-451 | E0 |
| `Val::Match` 四字段形态（shape.rs 依赖） | R:mod.rs:332 / C:mod.rs:283 | E0 |
| `unify_fuel_budget()` 与逐探测独立充值 | R:prim.rs:68 / C:prim.rs:68；R/C:pattern_match.rs:364-367 | E0 |

## 8 (E4) L12 单边新增与共有代码的边界

- `Val::Call` / `Tm::Call`（L12 独有值形态，C:mod.rs:104 / :284）。
- **构造点极少**：`Tm::Call` 只在重命名里生成（C:unification.rs:644），`elaboration.rs` 与孪生侧 grep 构造 = 0；
  `lookup_function_by_cases` 标 `#[allow(dead_code)]`「当前仅保留 API」（C:mod.rs:2561-2562）⇒ Call 显示外衣**已无生产者**。
- **与共有代码的接口不匹配 [推断]**：`force` 对 Call 是**重包不剥**（C:mod.rs:1012-1015），而
  `pattern_match.rs:153-156`（scrutinee 类型必须是 `Val::Sum`，否则报「match 的对象必须是和类型（enum）」）与
  `shape.rs:56-72 peel`（只领会 `Pi` / `Lam`）都**没有 Call 分支**，两处文件逐字节等于 L07 版。
  若 Call 外衣经 meta 解（`rename` → `eval`，C:mod.rs:1620-1622）回流到这两个入口，L12 会分别误报和丢失形状认回；L07 无此值形态故无此风险。
  **未观察到实例，标 [推断]；需要运行证据才能升级为 E2。**

## 一脉相承评级

**强（本角度）**：模式匹配编译器的主体（`pattern_match.rs` 4927 token）自 L07 起六层逐字节未改，形状认回件 119/120 行同、诊断文案与等级同一套、
19 个回归钉一个不丢；孪生 44 行差异全部是 L08 一次成型、L09–L12 原样继承，其中有确凿的 E3（臂上下文平坦区）与 E2（name_map 包裹面收窄），
但**都是 L08 的账，L12 只是继承人**，且后果限于性能与 [推断] 的边角类型显示，不动匹配语义。

## Top-3 差异

1. **E3-继承**：孪生臂上下文失去 defs 平坦区——L07 在 `subst_cxt` 里把包裹槽追加成 defs 尾部新平坦区（R:machine.rs:695-705，R:README.md:637-640「已落地 2026-09-19」，臂内 `env_nth` O(1)）；L12 改用 `frcs_env`（C:machine.rs:2533 → C:force.rs:712-714 自注「整体退化为 binder 链」），自 **L08** 起即如此（L08 machine.rs:1901），L12 原样继承。可观察 = 臂体 env 访问 O(depth) 与每臂 n 个 `EnvCons` 分配（性能，非语义）。
2. **E2-继承**：name_map 的 σ 包裹面收窄——L07 包裹**整张** name_map 并压轨迹、以 `mark = name_trail.len()` 供臂边界回滚（R:machine.rs:724-743）；L12 只包 `cxt.types` 链上 `source` 节点且仅 tag 变化才写（C:machine.rs:237-244），撤销另走 `wrap_names` / `restore_names`（C:machine.rs:231 / :250，C:compiler.rs:194 / :212）。后果 [推断]：不在 types 链上的 name_map 条目在臂内看到的是未包 σ 的旧类型。
3. **E4→潜在 E2（[推断]）**：`Val::Call` 与共有模式匹配/形状代码无接口——Call 是 L12 单边值形态（C:mod.rs:284），force 重包不剥（C:mod.rs:1012-1015），而两处共有代码无 Call 分支（R/C:pattern_match.rs:153-156、R/C:shape.rs:56-72，逐字节同）。
