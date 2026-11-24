# 02 σ 显式替换载体 / VSpan / force —— L07 ⟷ L12「共有部分」差异

> 范围：孪生 `bump_spine_iter/{subst,syntax,force,entry}.rs` + 顶层 `syntax.rs`；只读，HEAD `8f4287ae`；下文
> `L07 …:N` / `L12 …:N` 均指孪生目录内文件。归因口径 = `MAP.md`（含 §10 附录 A）：**先判「是不是 L08 一次成型、
> L09–L12 原样继承」，再判「L12 本章增量」**。本册复验的继承硬事实（内容哈希）：孪生 `subst.rs` L08 = L09 =
> **L12**（`30554B7C…`）、孪生 `syntax.rs` L09 = **L12**（`319A996B…`）、孪生 `force.rs` L08→L12 **只多一个
> `force_deep`**、孪生 `entry.rs` L08→L12 **只改 crate 路径与 `U` 层级字段**；顶层 `syntax.rs` diff 退出码 0（E0）。

## 0 结论摘要

σ 的语义机器在 L12 逐点对位、完整可用。`subst.rs` 少的 444 token **没有一条是机制缺失**：3 条是 L07 在
`fb89bb00`（2026-09-19，即拆分那次提交）一并加入的加固/缓存，1 条是该提交带的回归测试，1 条是文档。
4 条 E3 **全部不是 L12 造成**——是 L08 分叉时丢的、L09–L12 逐字继承；**无 E2**（每条机制差都有方向：L12 更旧→E3、
更新→E4）；L12 自己只做加法（层级 `U(u32)`、`force_deep`、typeclass 侧 `vspan()` 桥）。

## 1 σ 载体：仍然完整可用（回答 (a)）

机械计数（VSub 129 vs 139、`wrap_sub` 66 vs 67、`SpecSolve` 32 vs 36）的**差额可逐项归因到文档与行宽**，
不是机制减少：

| 机制 | L07 | L12 | L07 锚点 | L12 锚点 | 判档 |
|---|---:|---:|---|---|---|
| `SubstV` 持久单链（extend/compose/has） | 有 | 有 | subst.rs:28 | subst.rs:27 | E1（同构） |
| `SUBSTV_ALIVE` / `VSUB_REGS` σ 跨轮回收 | 各 1 | 各 1 | subst.rs:45/69 | subst.rs:44/68 | E0 |
| `lookup_hit`（读点查 σ + 条件包裹） | 1 | 1 | subst.rs:94 | subst.rs:93 | E1（仅换行） |
| `wrap_sub` 读点包裹 | 67 | 66 | subst.rs:426 | subst.rs:380 | E1 |
| `SpecSolve` 穿参状态 | 36 | 32 | subst.rs:446 | subst.rs:400 | E1 |
| `XCell::VSub{val,sub}` | 4 | 4 | syntax.rs:255 | syntax.rs:259 | E0 |
| `subst_cxt`（σ 进上下文） | 12 | **13** | machine.rs 3 处 | machine.rs 5 处 | E1（L12 多 2 处调用） |
| `frcs` σ 推进结构（force.rs 内） | 17 | 16 | force.rs:545 | force.rs:505 | E1 |

**计数差去哪了**（逐文件复算，与 MAP §3 的 139/129、67/66、36/32 完全吻合）：主体在**模块根文档** `bump_spine_iter.rs`——
L07 的导览逐条点名 `SubstV`/`frcs`/`InlineStack`/`SpecSolve`（L07 `:83-92`、导出表 `:149-155`），L12 对应段落仍是
**`pm_defs` 时代的旧文案**（`L12 bump_spine_iter.rs:44-47` 还写"模式特化事实表 `pm_defs`/`pm_solvable`/`pm_mark`"，而实际
代码是 `SubstV` + `XCell::VSub` + `frcs`）；VSub 6→0、frcs 7→1、SpecSolve 5→2 全落在这一处（**E3-文档**：不影响行为，
但会误导读者）。其余是真实代码位差：force.rs 的 VSub 20→17（§4.2）、machine 4→3、subst 9→8，compiler.rs 3→4 抵消
⇒ **σ 载体没有被削减；被削减的是 L07 的加固件（§2）与文档。**

## 2 subst.rs 的 -444 token 逐项（"少的是什么"）

L07 444 行 / L12 379 行，差 65 行全是四个整块：

| 缺失项 | L07 锚点 | L12 | 性质 | 判档 |
|---|---|---|---|---|
| `InlineStack<T,const N>`（热路径零分配小栈） | subst.rs:159-202 | 无 | 只服务于 `mentions_level`/`val_mentions_lvl`/孪生 `struct_eq` | E3-继承 |
| `mentions_level` 迭代化 | subst.rs:208（工作栈 :223） | subst.rs:169 **递归** | 见 §2.1 | E3-继承 |
| `SIMPL_CACHE` 旁路缓存 + `simpl_cache_invalidate` | subst.rs:471、:476 | 无 | `simpl_decl` 由返回 `Rc` 变**返回 owned**（:480 → :409） | E3-继承 |
| 缓存失效钩子（decl 写点 / 轮界） | machine.rs:200、:1781 | 无 | 随上一行消失 | E3-继承 |

**2.1 递归 vs 迭代：语义等价、鲁棒性落后。** L12 的 `mentions_level` 与 L07 **遍历面完全相同**（Rigid 裸头、spine 头 +
`collect_args`、闭包 env 链 + 平坦区倒序、Pi 的 dom/env、Sum/SumCase 槽、Match 的 scrutinee/env/pending、`VSub` 保守
记为引用），存在性判定对顺序不敏感 ⇒ 等价。但 L07 于 2026-09-18 改显式工作栈的理由写在 L07 subst.rs:210-213：`eval`
可不烧 fuel 地构造 `succ^N zero` 深值、按值深度递归会在万级深度爆栈；L12 退回递归 ⇒ **E3**。同一形态在
`val_mentions_lvl` 重演（L07 force.rs:172/187 迭代 → L12 force.rs:138 递归）。`occurs_transitive` **不受影响**（两版都是
工作表迭代：L07 subst.rs:304/VSub 臂 :390 ↔ L12 :255/:341）。

**2.2 旁路缓存消失的后果[推断，无 bench]**：quote/rename/unify 的 Match 臂每遇一个卡住 match 就整表重建 `simpl_decl`，调用点
两侧一一对应（L07 quote.rs:349、rename.rs:523、unify.rs:965 ↔ L12 quote.rs:343、rename.rs:505、unify.rs:407）；L07 按 decl 表地址
命中（subst.rs:483-489），L12 每次 `O(表)` 次 `String` 克隆。注意**L12 参考版有缓存**（`simpl_decl_cached` 按 `Decls::ver`，
`mod.rs:2173`）——落后的只是孪生。

## 3 VSpan：真在用，且被新代码扩展（回答 (b)）

| 事实 | L07 | L12 | 判读 |
|---|---:|---:|---|
| `VSpan` 类型 token（`-CaseSensitive`） | **37**（mod 30/unif 6/pm 1） | **38**（同 + `typeclass.rs:5` 注释） | 与 MAP §3 一致，**共享文件逐点相同** E0/E1 |
| `vspan()` 构造调用 | 32（elab 2 / mod 16 / pm 1 / tests 7 / unif 6） | **39** | +7 全在孪生 `typeclass.rs:40/65/67/73/81/85/89` → **E4** |
| `Val` 的 VSpan 槽位 | Obj/Lam/Pi/LiteralIntro/Sum/SumCase 全带（`mod.rs:258-277`） | 同 | E1 |
| `tmspan` 桥（VSpan → `Span<String>`） | 32 处（elab 2 / mod 17 / pm 2 / unif 12） | **32 处，同分布** | E1 |
| 观察面 run | `observe.rs`（仅 L07，296 行） | `run_with_observe` + `hover_table`（`mod.rs:2194`/`:722`/`:2220`） | E1（移植，非拷贝） |

⇒ **"抄了 VSpan 但没接进观察面"不成立**：VSpan 是 `Val` 的结构字段，读点（quote/rename/unify/pretty）一律经 `tmspan` 落到
`Span<String>`；L12 还新付了 7 个 `vspan()` 给 trait 求解器的 V→Val 桥（孪生 `typeclass.rs:65-89`）。**唯一的结构性说明**：
L12 章不是 LSP 引擎——`src/lib.rs:274`/`:361` 显示 LSP 默认跑 **L13** 孪生（`L13_namespace::bump_spine_iter::Tycker`）⇒
"VSpan 的最终消费者不在 L12 内"是**章节分工**、不是漂移。孪生侧无 VSpan（用 `&'a str` 名字），两版一致。

## 4 force.rs：卡住 match 的 pending 机制——**不是**同一套（回答 (c)）

顶层强制循环（`force`/`frcs`/`frcs_env`/`force_arg`）架构逐点相同，差异集中在 `vapp1` 与 `val_mentions_lvl`；
L08→L12 的 diff 只多一个 `force_deep`，**+173 token 全部来自它**。

| 函数 | L07 | L12 | 判档 |
|---|---|---|---|
| `vapp1` | force.rs:29 | force.rs:26 | E1 |
| ├ 卡住 match 吸收实参 | **`PendingCons` 头插 O(1)**（:60-70，节点 :68） | `Vec` 整段重拷 + `alloc_slice`（:55-64） | **E3-继承** |
| ├ β 直接用调用方 work/vals | :41-46 | :41-46 | E1 |
| └ `VSub` 头推开后再分发 | :79-115：force 后若 **tag 1（闭包）** 用**私有草稿栈** work2/vals2/icits2 走 `eval_iter`（:81/:92/:95），否则 :110 递归 | :74-79：**直接递归 `vapp1`** | **E3-继承（潜在正确性）** |
| `val_mentions_lvl` | :172 迭代（`InlineStack` :187） | :138 **递归** | E3-继承 |
| `force` 主循环 | :282 | :244 | E1 |
| └ 分支选中后应用 pending | :513 `pending_to_vec(*pending)` | :474 `for &(u,i) in *pending` | E1（载体不同、序相同） |
| `frcs` / └ Match 臂重建 pending | :545 / :630-666（链→Vec→`reverse`→正向 cons） | :505 / :585-611（`map(wrap_sub)`→`alloc_slice`） | E1 |
| `frcs_env` | :767（`env: &Env`，私有） | :715（`env: Env`，`pub(super)`） | E1（`Env` 是 Copy） |
| `force_arg` | :803 | :746 | E1 |
| `force_deep` | **无** | :778 | **E4** |

**4.1 `pending` 不是同一套机制**：L07 用 cons 链（`syntax.rs:248` 字段、`:265` 节点；头 = 最新、尾部共享），
逐应用 O(1)；L12 是旧切片版（`syntax.rs:252` = `&'a [(V,Icit)]`），每次 `vapp1` 整段重拷（force.rs:56-58）⇒
累积 k 个实参 **O(k²) 拷贝 + O(k²) bump 内存**。随之消失的还有 `pending_len`/`pending_to_vec`/`pending_struct_eq`
（`syntax.rs:273/283/296`），L12 的 unify 改用 `pd1.len()` + 逐对（`L12 unify.rs:423/446`）。

**4.2 VSub→闭包 β 守卫关乎正确性而非性能**：L07 force.rs:82-91 写明失败模式——`frcs` 可把 VSub 头推成闭包，而进
`eval_iter` 会 `clear()` **调用方的 work/vals**（`L12 eval.rs:182-184` 实测存在该 clear），于是 `W::Apply`/`ChainWrap`/
`AppPrunOne` 带在飞的外层任务被静默截断。L12 的 `vapp1` 在 :74-79 直接递归回 `vapp1`、闭包臂（:41-46）用的仍是调用方栈
⇒ **同一路径在 L12 仍敞着**。可达性取决于"VSub 经 force 变闭包"是否真出现 → [未核实]，无测试覆盖。

## 5 entry.rs：预算没丢，丢的是回归钉（回答 (d)）

| 项 | L07 | L12 | 判档 |
|---|---|---|---|
| 文件行数 | 387 | 342 | — |
| `deep_value_tests`（10 万层深值迭代回归钉） | entry.rs:364 起整块 | **整块删除** | **E3-继承** |
| `EQ_BUDGET` 在 entry.rs 的出现 | 1（**只是被删测试里的一行注释**，:411） | 0 | **不是差异** |
| `EQ_BUDGET` 全层总数 | 7 | **7**（`struct_eq.rs` ref 2 + twin 4 + tests 1） | E0 |
| `export` 的 U 分支 | entry.rs:78 `CTm::U` | entry.rs:78 `CTm::U(*lvl)` | **E4-上游** |
| `NO_NAME_MAP` 消融开关位置 | machine.rs:2002-2006 | entry.rs:245-249（machine.rs:18 引用） | E1（搬家） |

⇒ **"预算去哪了"：没去哪。** entry.rs 的 `EQ_BUDGET` 从来只是被删那个测试里的一行注释；预算本体在 `struct_eq` 里两侧都是
`20_000`、计数 7→7。真正的损失是**测试本身**：L12 既退回递归扫描（§2.1）、又删掉"10 万层不爆栈"的钉，**证据链在 L12 断了**。
L08→L12 的 entry.rs diff 只有 crate 路径与 `U` 层级 ⇒ 这一删是 **L08 干的**。

## 6 孪生 syntax.rs：值表示的两处改形（回答 (e)）

顶层 `syntax.rs` 逐字节同（E0）⇒ 参考版 `Val`/`Locals`/`close_ty` 形状不变。**孪生 `V`（打包 u64）改了两处、
方向相反**：

| 形状 | L07 | L12 | 影响 | 判档 |
|---|---|---|---|---|
| tag 3 宇宙 | `U` 立即数 `V(3)`（syntax.rs:28/:136） | `U(u32)`、`lvl<<3\|3`、新增 `v_u_of`（:27/:135/:148） | **L12 有层级、L07 无**；`Type 0`/`Type 1` 在 L07 孪生不可区分 | **E4-上游** |
| `Match.pending` | cons 链 `Option<&PendingCons>`（:248） | `&'a [(V,Icit)]`（:252） | §4.1 的 O(k²) | **E3-继承** |
| 其余 tag / `XCell` / `PrCons` / `LCons` / `v_*` | — | 逐点同（差异仅注释与 `use` 排序） | — | E0/E1 |

`U(u32)` **不是** L12 本章增量：L08 的 entry.rs 仍是 `Tm::U`，**L09 起才带层级**（哈希：孪生 syntax L09 = L12）
⇒ "L09 引入、L10–L12 逐字继承"的 E4-上游；对 L07 而言是"L07 孪生没有宇宙层级"。参考版同理（L07 `mod.rs` 的
`Val::U` 无字段 → L12 `U(u32)`，`L12 mod.rs:84`）。

## 7 已确认等价清单（不必再查）

| 项 | 锚点 | 判档 |
|---|---|---|
| 顶层 `syntax.rs` | L07 / L12 同内容 | E0 |
| `SUBSTV_ALIVE`/`VSUB_REGS`/`wrap_sub`/`lookup_hit`/`SubstV` | L07 subst.rs:45/69/426/94/28 ↔ L12 :44/68/380/93/27 | E1 |
| `occurs_transitive`（工作表迭代，VSub 保守为引用） | L07 subst.rs:304/390 ↔ L12 :255/341 | E1 |
| `frcs` 槽位纪律（spine、Sum/SumCase 只包裹不物化）；`force_arg` 逐层解包 VSub、不推开、不重选 Match | L07 force.rs:497-505/:803 ↔ L12 :457-464/:746 | E1 |
| `frcs` Match 臂语义（scrutinee 单独推进 + pending 逐个包裹 + 交回 force） | L07 force.rs:620-667 ↔ L12 :575-615 | E1 |
| VSpan 与 `tmspan` 桥；`EQ_BUDGET`=20_000 | §3；`struct_eq.rs:21` ↔ `:17` | E1 / E0 |
| 孪生封印（`SEALED`） | L07 `bump_spine_iter.rs:1-9`（11-22）↔ L12 `:1-5`（11-23） | E1 |

## 8 E4 单边新增（不计入"共有部分差异"，列出以免误算）

| 项 | 锚点 | 说明 |
|---|---|---|
| 孪生 `force_deep` | L12 force.rs:778（参考版 `mod.rs:825`） | 本章 trait 求解边界；L12 force.rs `+173` token 的全部来源 |
| 宇宙层级 `U(u32)`/`v_u(lvl)`/`v_u_of`；typeclass 的 `vspan()` 桥 7 处 | L12 syntax.rs:27/135/148、`mod.rs:84`；孪生 `typeclass.rs:40/65/67/73/81/85/89` | 层级 L09 引入（非本章）；vspan 桥属章主题 |
| `DeclEntry` 兼容别名、`struct_src`/`natadd_src` | L12 `bump_spine_iter.rs:126/138` | 基准面 |

## 9 归因与影响面

1. 本册 4 条 E3 **全部首次出现在 L08**（L08 = L09 = L12 哈希相同；与附录 A.3 一致）；**L12 的 11-17 重建只贡献
   §8 的加法**（force.rs 加 `force_deep`；entry.rs 仅改 crate 路径）。
2. 后果被**封印**限制：两侧孪生都 `SEALED`、`l07-twin`/`l12-twin` 默认关，LSP 默认引擎是 L13 孪生（`lib.rs:274`/`:361`）
   ⇒ 这些 E3 在默认构建/默认 LSP 路径下**不出现**，只在显式开孪生或跑基准时出现；而 `lNN_fast_parity` 是它们唯一的门禁，
   该门禁默认关闭（MAP §6.2）。**对照**：L12 的参考版在这三处都比孪生新（`val_mentions_lvl` 迭代 + `InlineStack`
   `mod.rs:2069`、`simpl_decl_cached` `mod.rs:2173`、`force_deep` `mod.rs:825`）⇒ **孪生落后于同层参考版**，这是 L08 分叉
   的直接后果，不是 L12 的退化。

## 一脉相承评级

**中偏强**（参考版这一面 **强**、孪生这一面 **中**）：σ 载体与 force 架构在 L12 逐点对位、完整可用，
顶层 `syntax.rs` 逐字节同；但孪生侧因 L08 一次分叉丢了 L07 的 4 项加固（深值迭代 + `InlineStack`、
`simpl_decl` 旁路缓存、`pending` cons 链、`vapp1` 的 VSub→闭包 β 守卫），L09–L12 逐字继承而 L12 未补。

## Top-3 差异

1. **E3-继承**：`vapp1` 缺 L07 的 VSub→闭包 β 守卫——L12 force.rs:74-79 直接递归回用调用方栈，而 `eval_iter`
   会 clear 外层任务（L12 eval.rs:182）；L07 用私有草稿栈规避（L07 force.rs:81-107）。
2. **E3-继承**：深值扫描退回递归（L12 subst.rs:169 / force.rs:138 ↔ L07 subst.rs:208 + `InlineStack`:159 /
   force.rs:172），且唯一回归钉 `deep_value_tests` 在 L12 被删（L07 entry.rs:364 ↔ L12 无）。
3. **E3-继承**：卡住 match 的 `pending` 由 L07 cons 链（L07 syntax.rs:248/265，O(1) 头插）退回切片（L12
   syntax.rs:252，`vapp1` 每次整段重拷 force.rs:56-58）⇒ 逐应用 O(k²)；同一分叉带走 `simpl_decl` 旁路缓存
   （L07 subst.rs:471/480 ↔ L12 subst.rs:409）。
