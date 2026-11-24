# 03 · 合一 / 结构相等（`L07_sum_type` ⟷ `L12_canonical`）

> 视角：合一（`unification.rs` / `bump_spine_iter/unify.rs`）与结构相等（`struct_eq.rs` / `bump_spine_iter/struct_eq.rs`）。只读分析，HEAD `8f4287ae`。
> 数字来源：标 **MAP** 的取自 `docs/compare-l07-l12-shared/MAP.md` §1/§10；标 **自算** 的是本轮 6-token shingle 复算（同 §7 口径，tokenizer 与 Lead 有 ±2% 差）；
> 标 **numstat** 的是 `git diff --no-index --numstat` 的增删行数（硬事实，不依赖 tokenizer）。

## 0 一句话结论

**参考版同源、孪生侧落后一代。** 顶层 `struct_eq.rs` 就是 L07 的文件加 2 个 hunk（宇宙层级载荷）；合一内核 21 个函数 keep07=**1.000**、其中 18 个 keep12 也 =1.000（双向逐 token 相同），
其余差异（含 L08 新增的 `(Obj,Obj)` 合一臂）全部可归因到「L08 Obj 合同 / L09 宇宙层级 / L10 trait 求解 / L12 Call」。真正的落后只有一处：**孪生 `struct_eq` 在 L08 被换成递归版，L07 的堆上工作栈没跟过来**（E3）。

## 1 覆盖清单与归因

| 文件 | tok07→12（MAP） | keep07 | keep12 | numstat（hunk） | 差异首次出现层 | 判级 |
|---|---:|---:|---:|---|---|---|
| `unification.rs`（ref） | 9507→10507 (+1000) | 0.987 | 0.919 | 136/19（20） | L08/L09/L10 混合；**L11→L12 仅 22/2** | E1 主体 + E4 |
| `struct_eq.rs`（ref） | 2759→2791 (+32) | 0.989 | **1.000** | **11/2（2）** | L08→L09（+32 tok） | **E1** |
| `bump_spine_iter/unify.rs` | 6303→6672 (+369) | 0.920 | 0.905 | 216/169（64） | **L07→L08 = 211/167**；L08→L09 = 6/3；**L09→L12 = 0** | E1/E2 继承 |
| `bump_spine_iter/struct_eq.rs` | 3166→2459 (−707) | **0.527** | 0.741 | 198/327（23） | **L07→L08 一次成型**；L08→L09 = 4/3；**L09→L12 = 0** | **E3 + E1** |

归因口径按 MAP §10 A.5：`L09_mltt` 与 `L12_canonical` 的孪生 `unify.rs`、`struct_eq.rs` 二者 `git diff` **均为 0 行**——L12 没碰它们，是 L08/L09 的原件。
（`bump_spine_iter/prim.rs` 同理：L09→L12 = 0 行，`UNIFY_FUEL` 因此在两版落在同一行 `:64`。）

## 2 (b) 顶层 `struct_eq.rs`：不是「独立重写刚好重合」，是拷贝 + 2 个 hunk

| 证据 | 数值 |
|---|---|
| `git diff --no-index` | **2 个 hunk，+11 / −2 行** |
| L07 与 L08 的 sha256（前 16 位） | 同 `32E04D4DAF80365D`（16125 B） |
| L09 / L10 / L11 / L12 的 sha256 | 全同 `E8AF8F4FD65B6E23`（16411 B） |
| 差异内容 | 只有 `Val::U` / `Tm::U` 的载荷穿线 |

逐 hunk（两版都给）：

| hunk | L07 | L12 |
|---|---|---|
| 值层 | `src/L07_sum_type/struct_eq.rs:127` 「`(Val::U, Val::U)` 与 `(Val::LiteralType, …)` 同臂空转」 | `src/L12_canonical/struct_eq.rs:127-132` `(Val::U(x), Val::U(y)) => { if x != y { return false; } }` + 独立 `LiteralType` 臂 |
| 项层 | `…:253` `(Tm::U, Tm::U) => {}` | `…:258-262` 同款 |

⇒ **E1**（等价改写的最小形式：只加了一条更严的判定）。MAP 的 +32 token 可全额对上这 2 个 hunk（自算 +35，差值是 `if` 块边界 token）。
反证「独立重写」：`Val::VSub` 的 `Rc::ptr_eq` 同址短路（`:82-88`）、`EqTask` 五个变体名（`:55-62`）、`Closure` 的「env 先 / 体后」注释（`:374-377`）都不可能在独立重写下逐字复现。

**一处需要校正的读法**：MAP §10 A.3 的 `struct_eq.rs` 行若读成「L07..L12 逐字节同」是错的——逐字节同只成立于 **L07↔L08** 与 **L09↔L12** 两段，**L07 vs L12 差这 2 个 hunk**（即 §1 表里那 +32 token）。这不影响 A.3「冻结起点 = L09」的结论。

## 3 (c) 顶层与孪生在 L12 内部互相同源吗？——不同源

| 对比 | keep | 依据 |
|---|---:|---|
| L07 ref → L07 twin | **0.44**（自算）/ 0.71（自算，标识符归一化）/ 0.689（MAP A.4） | 同层不同物：ref 用 `Rc<Val>` 模式匹配 + `InlineStack`；twin 用 tag 整数 + bump 扁平 `V` |
| **L12 ref → L12 twin** | **0.27** | 比 L07 同层还低 |
| L07 twin → L08 twin | 0.528（MAP A.4） | L08 把孪生换了一支 |
| **L08 twin → L12 twin** | **0.997**（MAP A.4）；numstat **4/3 行** | L12 孪生 = L08 孪生原件 + 宇宙载荷 |

决定性论证不是相似度而是**机器是否存在**：`seq_run` / `seq_step_t` / `SEqTask` 在 L07 孪生 `struct_eq.rs` 命中 **51 行**（57 次），在 L12 孪生命中 **0** 行（`InlineStack` 4→0）；
L08 孪生同样 0 次（`struct_val_eq_go` 命中 14）。若 L12 的孪生是由 L12 的顶层（迭代版）翻译的，它必然带 `SEqTask`——它没有。
⇒ 按 MAP §10 A.5 写：**孪生 `struct_eq` 自 L08 起就是另一支实现，L09–L12 原样继承**，不是「L12 重写」。

## 4 (a) 孪生 `struct_eq.rs` 被改写成什么

| 项 | L07（`src/L07_sum_type/bump_spine_iter/struct_eq.rs`，427 行） | L12（`src/L12_canonical/bump_spine_iter/struct_eq.rs`，298 行） |
|---|---|---|
| 三个入口 | `struct_tm_eq:46` / `struct_val_eq:61` / `struct_env_eq:65` | 同名同序 `:42` / `:46` / `:50` |
| **遍历机制** | `enum SEqTask:70` + `seq_step_t:79` + `seq_run:190`，`InlineStack<SEqTask,16>` **堆上工作栈** | `struct_tm_eq_go:71` / `struct_val_eq_go:142` / `struct_spine_eq_go:54` / `struct_env_eq_go:251`，**全部原生递归** |
| 预算常量 | `EQ_BUDGET: usize = 20_000`（`:21`） | `EQ_BUDGET: usize = 20_000`（`:17`）——**同值** |
| 预算构造点 | 2 处（T-only 入口 `:50`、`seq_run` `:191`） | 3 处（三个公开入口各一份 `:43`/`:47`/`:51`） |
| 燃烧面 | T/V 任务各烧 1；Env/Spine 展开不烧（`:364-366`） | 同（`_go` 入口各烧 1；`struct_spine_eq_go`/`struct_env_eq_go` 入口不烧） |
| pending 表示 | `Option<&PendingCons>` 链；`pending_len`/`pending_struct_eq` 在 `syntax.rs:273/296` | 切片 `&[(V,Icit)]`，`pd.len()` + 内联 zip（`:240-243`） |
| token（自算） | 3401 | 2673（−728） |
| token 账 | `seq_step_t` 1108 + `seq_run` 1811 = **2919** | `struct_*_go` 合计 **2341**（198+893+1027+223） |

**L07 的 Match/Match 结构快路径还在**：`XCell::Match{..}` 臂两侧都逐项比 scrutinee / env / cases 长度 / pattern / 分支体 / pending 长度+icit+值（L07 `:318-358`，L12 `:219-244`）。
我逐臂对过：Tm 16 臂、`V` 的 tag 14 路、`XCell` 8 支，**缺 0 项**。差异只有三处：

1. `(Tm::U,Tm::U)=>true`（L07 `:110`）→ `(Tm::U(x),Tm::U(y))=>x==y`（L12 `:84`）；`(3,3)|(6,6)=>{}`（`:218`）→ `(3,3)=>v_u_of(x)==v_u_of(y)` + `(6,6)=>true`（`:149-150`）——**L09 的宇宙层级载荷（E4-继承）**。
2. Sum/SumCase 里 icit 检查与子项比较由「先全查 icit 再压子项」（L07 `:136-147`）改为「逐对交错」（L12 `:102-110`）——布尔结果相同（失败都短路到 false），只有失败路径的预算消耗略不同，**E1**。
3. **遍历机制**：工作栈 → 递归（下条）。

### 可观察后果（E3 的判据）

- L07 自己写下了判据：`src/L07_sum_type/bump_spine_iter/struct_eq.rs:47-49` 与顶层 `struct_eq.rs:10-12`——「递归版在预算（20k 层）烧尽**之前**就会先在 ~万级深度爆栈（常规栈 1–8 MB）」。
- L07 有回归钉 `src/L07_sum_type/bump_spine_iter/entry.rs:363-417`：`succ` 链 **100_000 层**，在默认 ~2 MB 测试栈上断言 `struct_val_eq(2_000 层)=true`（`:414`）、`struct_val_eq(100_000 层)=false`（预算耗尽的有界降级，`:415`），**全程不爆栈**。
- L12 孪生 `entry.rs` 里 `struct_val_eq` 命中 **0** 次、`#[test]` 命中 **0** 次——这条钉子没有对位。

⇒ 同一组输入在 L12 孪生上会在 ~万级深度栈溢出（Rust 栈溢出 = abort，不可捕获）。**谓词语义没变、健壮性倒退**，故整条记 **E3**（不是 E1）。
影响面必须写清，否则会高估：① `Cargo.toml:196` 只有空的 `l12-twin = []`，无 default feature，`tests/l12_fast_parity.rs` 首行 `#![cfg(feature = "l12-twin")]` 默认不跑；② LSP 默认引擎是 `L13_namespace::bump_spine_iter`（`src/lib.rs:361`），L12 孪生只被 bench 用。
所以这是**无门禁的潜在爆栈**（bench/实验路径），不是现网回归。

**`EQ_BUDGET` 6→10 的落点（预算更严还是更松）**：常量值不变（20_000），每次顶层调用仍只有**一份**预算，燃烧面逐项相同（T 任务 1 / V 任务 1 / Env·Spine 展开 0）。
6→10 只是「构造点 2→3」的计数后果：L07 把三个入口汇到 `seq_run`（1 处）+ T-only 入口（1 处），L12 三个入口各构造一份。**既没更严也没更松。**

## 5 (d) 合一内核逐函数真配对

口径：按 `fn` 名字从两版 `unification.rs` 切函数体算 6-token shingle。已核**同名同物**：都在同一个 `impl Infer` 内、同一调用链、签名同形（`machine::unify` 是孪生侧另一物，**未**混入本表）。

| 函数 | L07 行 | L12 行 | tok07→12 | keep07 | keep12 | 判 |
|---|---:|---:|---|---:|---:|---|
| `invert_go` | 104 | 105 | 317→317 | **1.000** | 1.000 | E0 |
| `invert` | 135 | 136 | 130→134 | **1.000** | 0.968 | E1（只多 `pub(crate)`） |
| `intersect_go` | 819 | 914 | 264→264 | **1.000** | 1.000 | E0 |
| `intersect` | 845 | 940 | 155→155 | **1.000** | 1.000 | E0 |
| `prune_vflex_go` | 242 | 243 | 375→375 | **1.000** | 1.000 | E0 |
| `prune_vflex` | 285 | 286 | 278→278 | **1.000** | 1.000 | E0 |
| `prune_meta` | 213 | 214 | 230→230 | **1.000** | 1.000 | E0 |
| `unify_no_arm` | 1244 | 1361 | 69→69 | **1.000** | 1.000 | E0 |
| `solve` / `solve_with_pren` | 697/702 | 706/711 | 72 / 227 同 | **1.000** | 1.000 | E0 |
| `loose_string` | 872 | 967 | 134→134 | **1.000** | 1.000 | E0 |
| `frame_new` / `frame_assemble` | 407/472 | 408/473 | 479 / 391 同 | **1.000** | 1.000 | E0 |
| `lams_go`/`drop`/`lift`/`skip`/`unlift`/`lift_in_place` | 672/353/73/78/85/67 | 681/354/74/79/86/68 | 全同 | **1.000** | 1.000 | E0 |
| `prune_ty` / `rename` | 195/344 | 196/345 | +4 | **1.000** | 0.962 / 0.981 | E1（`pub(crate)`） |
| `unify_sp` | 739 | 830 | 246→222 | 0.884 | 0.974 | E3（少 `prof::bump`，见 §7） |
| `flex_flex` | 770 | 860 | 327→349 | 0.931 | 0.866 | E4（`cxt` 参数 + `solve_multi_trait`） |
| `rename_arm` | 552 | 553 | 1109→1229 | 0.985 | 0.889 | E4（`Val::Call` 臂 `:638-645`） |
| `unify` | 894 | 989 | 2909→3124 | 0.974 | 0.915 | E1 + E4（见 §7） |
| `is_canonical_head` | 1253 | 1370 | 72→75 | 0.922 | 0.908 | E1（`Val::U(_)`） |

孪生侧同样做了一遍（求解内核在 `bump_spine_iter/rename.rs`；该文件 L09 起冻结，且下面这 4 个求解函数在 L07→L08 也没动过，故与 L07 逐 token 相同）：

| 孪生函数 | 位置（L07 → L12） | tok | keep07/keep12 | 判 |
|---|---|---|---:|---|
| `invert_bump` | `rename.rs:103` → `:100` | 390 | 1.000 / 1.000 | E0 |
| `prune_meta_bump` | `rename.rs:750` → `:661` | 403 | 1.000 / 1.000 | E0 |
| `solve_bump` | `rename.rs:215` → `:212` | 203 | 1.000 / 1.000 | E0 |
| `solve_with_pren_bump` | `rename.rs:162` → `:159` | 337 | 1.000 / 1.000 | E0 |
| `unify_sp_lockstep` | `unify.rs:252` → `:238` | 376 | 1.000 / 1.000 | E0 |
| `flex_flex_bump` | `unify.rs:185` → `:170` | 468→464 | 0.988 / 1.000 | E1 |
| `intersect_bump` | `unify.rs:110` → `:101` | 482→451 | 0.921 / 0.988 | E2/E4（Obj 合同臂配套，见 §7-2） |
| `unify_iter` | `unify.rs:324` → `:306` | 4757→5176 | 0.893 / 0.824 | E1 + E4 |

## 6 (e) 预算 / 燃料：同值、同点、同燃烧面

| 常量 | L07 | L12 | 值 | 判 |
|---|---|---|---|---|
| `UNIFY_FUEL`（ref） | `src/L07_sum_type/mod.rs:774` | `src/L12_canonical/mod.rs:728` | **4096 / 4096** | 同值同点 |
| `TYPORT_UNIFY_FUEL`（env 覆盖） | `mod.rs:779-785` | `mod.rs:733-739` | 缺省回落 `UNIFY_FUEL`，两侧同字符串 | 同值同点 |
| `UNIFY_FUEL`（twin） | `bump_spine_iter/prim.rs:64` | `bump_spine_iter/prim.rs:64` | **4096 / 4096**（行号也同，因 L09→L12 零改） | 同值同点 |
| `MATCH_CMP_BUDGET`（ref） | `mod.rs:801` = 64 | `mod.rs:755` = 64 | 64 / 64 | 同值同点 |
| `MATCH_CMP_BUDGET`（twin） | `bump_spine_iter/unify.rs:40` = 64 | `…/unify.rs:37` = 64 | 64 / 64 | 同值同点 |
| `EQ_BUDGET`（ref / twin） | `struct_eq.rs:36` / `bump_spine_iter/struct_eq.rs:21` | `struct_eq.rs:36` / `…:17` | 20_000 ×4 | 同值 |
| 计数点（twin Match） | 每顶层 `unify_iter` 一份 `:354`，**快路径后**递减 `:954-957` | 同 `:338` / `:1032-1035` | — | 同点 |
| ref `unify` 递归燃料 | `unification.rs:905-918` | `:999-1012` | 每递归 1 | 同点 |

⇒ `UNIFY_FUEL` 11/11、`TYPORT_UNIFY_FUEL` 4/4、`MATCH_CMP_BUDGET` 11/11 的**位置集合也一一对应**（L07 `mod.rs` 因内联 `prof` 模组整体下移 ~46 行，其后偏移恒定）。

## 7 其它差异（含两处必须写清的「不是 E3」）

| # | 项 | 锚点 | 判 |
|---|---|---|---|
| 1 | L07 的负载画像探针在 L12 完全缺失：`prof::bump(UNIFY_SP)` / `prof::bump(UNIFY)`，模组本身是 L07 `mod.rs:33` 的内联 `pub mod prof`（2026-11-21 `287e78ae` 单边新增） | `src/L07_sum_type/unification.rs:748` / `:903`；L12 `prof::` 命中 **0** | **E3**（零语义影响，只少画像口径） |
| 2 | 孪生 `(Obj, Obj)` 合同臂 + `intersect_bump` 的 Obj 头免比放宽（L07 对 Obj 头「恒败」，L12 走专臂比接收者+实参） | L12 `unification.rs:1186-1194`、`unify.rs:677-712`、`unify.rs:262`；L07 计数 **0**（L08 起才有） | **E2/E4-继承**：不是落后，是 L08 的能力增量；可观察后果是 Obj 头实参的 flex-flex 交叉在 L07 恒败、L12 可解 |
| 3 | `Val::Call` 三处：`rename_arm` 臂、`unify` 的透明穿透 ×2 | `L12:638-645`、`:1307-1313`；L07/L11 均 0 | **E4**（L12 本章增量） |
| 4 | `solve_trait` / `solve_multi_trait`（L10 起有；L12 改为 **Val 级求解** + Flex 实参推迟） | L12 `:751` / `:780`；L07 无 | E4（L10 引入 / L12 改机制） |
| 5 | `Val::U(x)` / `Tm::U(x)` 全域载荷（struct_eq / unify / rename / is_canonical_head 同步收紧） | L12 `unification.rs:1034`、`struct_eq.rs:127/258`；L07 单元 | E4（L09 引入），对判等是**严格细化** |
| 6 | 孪生 `UItem` 屏障重构：`MatchPrecheck`+`MatchBranch{p1,p2}`+`MatchPending` → `MatchStruct`+`MatchPattern`+`MatchIcit` | L07 `unify.rs:71/87/93` → L12 `unify.rs:78/88/90`；L09→L12 零改 | E1（比较序与失败路径副作用时序逐项相同） |
| 7 | **过期注释（不要当 E3）**：L12 `unification.rs:1159-1162` 注释自称「L09–L12 仍未补 literal 相等臂」，但 `:1163` **已经有该臂** | L07 同款注释 `:1058-1061` + 同款臂 `:1062` | **注释过期、代码已补**。方向：L07/L08 先在 `c6c0e892`（11-16 19:29）补，L09–L12 同日 `26c53eb7`（23:39）跟进，六层臂文逐字相同 ⇒ **不是 L12 落后** |
| 8 | 孪生 `pending_struct_eq`（`syntax.rs:296` 每次比较建两个 `Vec`）被内联成切片 zip | L12 `unify.rs:1026` | E1（且 L12 更省：零分配） |
| 9 | 孪生 `entry.rs` 少了 `deep_value_iterative_under_default_stack` 回归钉 | L07 `entry.rs:363-417`；L12 无 | E3（见 §4） |

## 8 已确认等价清单（不必再查）

- 顶层 `struct_eq.rs`：`tm_eq` / `val_eq` / `env_eq` / `eq_run` + `EqTask` 五变体 + `Closure` 序 + `Match` 的 **pending 值比较**（S1 不健全性修复，`L07:202-208` 与 `L12:202-208` 逐字同）。
- 顶层合一内核 18 个函数 keep07=keep12=1.000，另 3 个（`invert`/`prune_ty`/`rename`）只差 `pub(crate)` 前缀（§5 表）。
- `unify_no_arm` / `is_canonical_head` 判定集合同（后者只差 `Val::U(_)` 模式）。
- 孪生求解内核 5 个函数 keep=1.000（§5 第二表）；`pr_slots` / `spend` 70 / 32 tok 两侧 1.000。
- 五个预算常量全部同值同点（§6）。
- `pending` 的四字段（scrutinee / env / cases / pending）在两侧 struct_eq 快路径里**都**被比较——L07 的 S1 修复没有在孪生侧丢失。

## 一脉相承评级

**强**（参考版）/ **中**（孪生侧）。理由：参考版结构相等只差宇宙载荷、合一内核逐 token 同源，属最强一档继承；孪生 `struct_eq` 虽在 L08 换成递归版并丢了 L07 09-18 的工作栈加固（E3，无门禁），但它在 bench 路径、不是 LSP 默认引擎，不足以把整个角度压到「中偏强」以下。

## Top-3 差异

1. **E3** · 孪生 `struct_eq` 的遍历机器被换掉：L07 的 `SEqTask`+`seq_run` 堆上工作栈（`src/L07_sum_type/bump_spine_iter/struct_eq.rs:70-190`）→ L12 的原生递归 `struct_*_go`（`src/L12_canonical/bump_spine_iter/struct_eq.rs:54/71/142/251`）。`EQ_BUDGET` 同为 20_000、燃烧面同，但深值（`succ^N`，N ≫ 10⁴）在 L12 会栈溢出，而 L07 有 `entry.rs:363-417` 的 10 万层回归钉兜住。
2. **E3** · L07 2026-11-21 的 `prof` 探针在 L12 无对位（`src/L07_sum_type/unification.rs:748`/`:903`；L12 `prof::` 命中 0，模组本身在 L07 `mod.rs:33`）。零语义影响，但 L07 的 unify/force/eval/quote 负载画像在 L12 上无法复现。
3. **E4** · L12 单边增量（不算差异，但必须扣除）：`Val::Call` 三处（`src/L12_canonical/unification.rs:638-645`、`:1307-1313`）、`solve_trait` 改为 Val 级（`:751-830`）、`Val::U(x)` 全域载荷（`:1034`、`struct_eq.rs:127/258`，源自 L09）。扣除后 L07→L12 的 `unification.rs` 差异只剩 L08 的 `(Obj,Obj)` 臂与 L10 的 trait 骨架。
