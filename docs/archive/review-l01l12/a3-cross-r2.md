# A3 Cross-Audit Round2 — A4 切片（L08_product_type / L10_typeclass）

> 只读审计，**未改对方任何文件**。审计对象为 worktree 当前状态（A4 本轮并发编辑，
> 本报告基于最终读到的一致快照；若 A4 继续改动，请以 orchestrator 冻结版本复核）。
> 结论：0 个 P0/P1/P2；3 个 P3/needs-verify 记录。

## 1. 结论（verdict）

- P0: 0  P1: 0  P2: 0  P3: 2（+1 needs-verify）

## 2. 发现列表

### [P3] L10 `val_to_typ` 的两处 doc 注释与已修代码不符
- 位置：`src/L10_typeclass/bump_spine_iter.rs:24-25`（模块头）与
  `src/L10_typeclass/bump_spine_iter.rs:5436-5437`（`val_to_typ` doc）
- 证据：两处均写 "字面量/Prim 分支**参考版是 `todo!()`**——同款不可达即崩"。
  但 A4 本轮已把参考版 `Val::to_typ` 的 `LiteralType/LiteralIntro/Prim` 从 `todo!()`
  改为 `None`（`src/L10_typeclass/typeclass.rs:33-35`），快版 `val_to_typ` 对
  tag 6 / XCell 非 Sum 走 `_ => None`（`bump_spine_iter.rs:5484/5486`）——参考版与快版
  现为**同返 None**（`has no object` Err），不再是"两版同崩"。
- 机制/影响：纯文档漂移，会误导后续维护者以为两版在字面量接收者上仍会 panic。
- 处置：**仅报告（转交 A4）**：更新这两处注释为"参考版返回 None，与快版一致"。

### [P3] L08 README 双 oracle 计数漂移（A4 新增对齐测试未计入）
- 位置：`src/L08_product_type/README.md:232`（§8）与 `:128`（§6 双 oracle）
- 证据：静态计数 `rg -c '#\[test\]' tests/l08_fast_parity.rs` = **29**
  （28 parity + A4 本轮新增的 `packed_cells_align_at_least_8`，见
  `tests/l10_fast_parity.rs` 同款 / L08 对应测试），lib `#[test]` = **49**
  （tests.rs 45 + parser/mod.rs 3 + parser/lex.rs 1；`README.md` 里的 2 个 `#[test]`
  提及不算）。故 `cargo test --test l08_fast_parity` 应约 **78**；README §8 写
  "**77**（28 个 parity…；49 个 lib）"，§6 写 "（74 例）"，两处都与静态计数不符。
- 机制/影响：文档计数漂移，非行为问题。
- 处置：**仅报告（转交 A4）**：以静态 `#[test]` 计数核准（78 / 注明含 1 个非 parity 的
  对齐断言测试）。

### [needs-verify] L10 A6 探针的触发强度
- 位置：`tests/l10_fast_parity.rs:637-654`（`parity_prune_ty_rev_multilevel_nonlinear`）
- 证据：源为 `def mul : Nat -> Nat -> Nat = a => b => N => s => z => a _ (b _ s) z` +
  `def four = mul two two`，注释称其为 L08 `bb_unannotated_lambda_arg_ok` 的 L10 对应、
  会产出"混合非线性掩码"。该源中 `mul` 类型全注解、实参 `two` 为闭项，**未显式构造
  `m a a b c` 式重复实参的非线性 spine**；`a _`/`b _ s` 的洞是否产生非线性剪枝无法静态确证。
- 影响：若该源不经过 `prune_meta(non-linear)`，则 A6 修复（参考版 `prune_ty` 反转）
  未被此探针钉住，存在覆盖缺口（代码修复本身经交叉阅读正确，见 §3）。
- 处置：**仅报告 / needs-verify（转交 A4）**：建议采用 L05/L07 的确定性触发源
  `nonlinear_asymmetric_mask_pairs_inner_first`（`m : (A)(B)(C)(D) -> D -> D = _` +
  `the (Eq (m a a b c) (λd.d)) refl`），与本轮 A3 在 `tests/l09_fast_parity.rs` 新增的
  `parity_nonlinear_pruning_rev_mask` 同款；由 orchestrator 运行裁决后回填。

## 3. 交叉核对：确认无误的项（逐条给证据）

1. **A1 XCell/CloCell 对齐（L08/L10）**：`#[repr(align(8))]` 已加在
   `L08 bump:275 (XCell) / :400 (CloCell)`、`L10 bump:292 (XCell) / :433 (CloCell)`；
   四项编译期断言 `XCell/CloCell/PiCell/EnvCons`（`L08 bump:421-426`、`L10 bump:454-459`）。
   `PiCell` 含 `dom: V`(u64)、`EnvCons` 含 `val: V`，天然 ≥8，仅断言不加 repr——与
   A3 对 L07/L09 的处置一致。`v_clo_of/v_pi_of/v_xcell_of` 的 `// SAFETY:` 注释均点明
   对齐依赖（`L08 bump:222-226/233-236/249-253`、`L10 bump:234-237/245-248/261-265`）。
   运行时证据测试 `packed_cells_align_at_least_8`（`tests/l10_fast_parity.rs:612-626`）。
   **未见反例。**
2. **L10 `prune_ty` 掩码反转（A6）**：`unification.rs:99-139` 现收 `&[Option<Icit>]` +
   `rev.split_first()`，`prune_ty` 先 `rev.reverse()`（:127-128），与快版
   `prune_ty_bump` 的 `mask_inner_first.iter().rev()`（`bump_spine_iter.rs` 同款）及
   L05–L08 一致；两处 `//TODO:revPruning` 已删（`unification.rs:146/411`）。
   方向与 A3 对 L09 的修复相同，实现正确。
3. **L10 全局哨兵（A7）**：参考版 `mod.rs:176 x.0 >= 1919810`、
   `unification.rs:258 x.0 < 1919810`；快版全部 6 处 `>=`
   （`bump:1383/1538` quote、`2815/2860` rename、`4516` lvl2ix、`4772` Raw::Var）；
   eval `>=`（`bump:933/1043`）。与 "全局 iff `level >= 1919810`" 口径统一，
   0 号全局自引用不再下溢。新增钉子 `parity_global_sentinel_self_ref`
   （`tests/l10_fast_parity.rs:665-669`）断言 `recursive_0\n`。
4. **L10 `intersect_go`（A3 同款）**：`unification.rs:555-562` 长度失配已为
   `_ => None`（两处），与快版 `intersect_bump` 的 false 及 L05–L09 一致。
5. **L10 `to_typ` todo! 修复**：`typeclass.rs:33-35` 三臂改 `None`。调用方均能优雅处理：
   `elaboration.rs:462 .ok_or_else(|| ... "Not a type")?`、`:468-471` 显式 None→Err、
   `:913-920` `else` 分支→`has no object` Err；`unification.rs` 的
   `.flat_map(|...| self.force(tm).to_typ())` 天然过滤 None。与快版
   `val_to_typ`（tag 6→`_=>None`、tag 7 非 Sum→`_=>None`）判定一致，**修复正确**。
6. **"L10 `Val::Flex` 等于一切" needs-verify**：复核 `unification.rs:606-637`，
   Flex 臂为标准的 `intersect`/`flex_flex`/`solve`，**无 accept-all**；`Typ::Any` 的
   `(Any,_)|(_,Any)=>true` 在 `typeclass.rs:396` 属求解器设计（可选标记）。真正的
   无 occurs-check 假匹配在 `typeclass.rs:371-399` `Synth::unify`，A4 已加
   `#[ignore]` 探针 `probe_synth_false_match_rigid_generic`（`tests/l10_fast_parity.rs:686-710+`）
   并写明裁决流程，处置合规范（ROUND2 §B2）。
7. **A4 删除的 import 无未使用误判**：`L10 unification.rs` 删掉 `pretty::pretty_tm`
   后，其余 `pretty_tm` 出现均在 `/* ... */` 块注释内（`:588/589/690/691/704/705`），
   不构成使用；`colored::Colorize` 的使用全在注释内。**不会编译失败。**

## 4. 需要 orchestrator 处置

- 以上 3 条转交 A4（2×P3 + 1 needs-verify）；均不涉及 A3 文件。
- 建议 orchestrator 运行 A4 的 `#[ignore]` 假匹配探针与 A3/A4 的 A6 parity 探针后回填结论。
