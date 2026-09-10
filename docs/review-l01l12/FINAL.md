# L01–L12 多轮评审 · 最终汇总报告

- 评审对象：`src/L01_nbe` … `src/L12_canonical`（及对应 `tests/l0*`、`l1*`）
- 工作树：`F:/projects/hermes/elaboration-zoo-lsp-review`，分支 `review/l01l12-perfect`
  （基于 master `0a2cb3d`；主线 `F:/projects/hermes/elaboration-zoo-lsp` 未被触碰）
- 方法：5 个子 agent × 3 轮（审计+修复 → 集中编译/测试 → 轮转交叉审计 → 最终验证），
  所有编译与测试由 orchestrator 集中执行（避免并发踩 target）。
- 产出：49 个文件改动（+1323 / −196），21 份过程报告见 `docs/review-l01l12/a*-r*.md`。

## 1. 门禁结果

| 门禁 | 基线（master@0a2cb3d） | 最终 |
|---|---|---|
| `cargo check --lib` | 通过 | 通过 |
| `cargo check --all-targets` | — | **0 error** |
| L02–L12 集成测试（23 target / ~1600 用例） | 全绿 | **全绿**（无新增失败） |
| 新增回归探针 | — | 10 个（对齐/η/u64/宏递归/trait/哨兵/prune/假匹配） |
| `cargo test --lib` | 约 3min 后在 L13 legacy 段 `STATUS_ACCESS_VIOLATION` | 未改（L13，不在本次范围） |

## 2. 已修复（按价值排序）

### 2.1 真实内存安全 / wasm 目标 UB（P0）
- **packed-word tag 解码在 32 位目标对齐不足**：`XCell`/`CloCell` 在 64 位天然 8 对齐，
  但 wasm32 上 `&str`/指针仅 4 对齐，而解码用 `v.0 & !7` → 清掉 bit2、解引用错位指针。
  `Cargo.toml` 明确为 wasm 目标构建 LSP 二进制，故属真实 UB。
  修复：L02–L12 的 `XCell`/`CloCell` 加 `#[repr(align(8))]`，并对所有 `ptr|tag` 编码类型
  加 `const _: () = assert!(align_of::<T>() >= 8)`（L01 为 2 位 tag，断言 ≥4）。
  64 位布局逐字节不变。
- **L01 `bench_cek_deep` 早退分支**漏 `mem::forget(check)`：百万层 Box 树递归 Drop 爆栈
  （`--only <未选中深段变体>` 可触发）。

### 2.2 用户可达 panic → 可恢复 Err（P1）
- `L10/L11 Val::to_typ` 的 `LiteralType/LiteralIntro/Prim => todo!()`：`"s".foo` 直接崩溃；
  改为 `None`（与快版 `val_to_typ` 口径一致）。
- `L09 pretty::go_app_pruning` 的 `todo!()`：`println (_.foo)` 崩溃；移植 L06 实现。
- `L11/L12` 超大整数字面量 `parse::<u64>().unwrap()`：>u64::MAX 崩溃；改为推 IError + Hole。
- `L11` trait 求解 `solve_multi_trait(...).unwrap()`（参考版+快版）改可恢复 Err。
- `L09/L10/L11/L12` `intersect_go` 长度失配 `unreachable!()` → `None`（与快版及 L05–L08 一致）。

### 2.3 语义 / parity 裂缝（P1–P2）
- **L09/L10 全局哨兵 off-by-one**：`global_idx=0` 的层级恰为 `1919810`，边界写 `>` 导致
  `def f : String = f` 下溢崩溃；统一为 `>= GLOBAL_BASE`（参考版+快版共 8+6 处）。
- **L11/L12 η 臂缺 applicability 守卫**：`get_global` 取 decl 值（可为 λ）时
  `LiteralType ≡ λ` 落 η 臂 panic；移植 L06 `v_applicable`/`vapp_ok`（参考+快版同步）。
- **L09–L12 `prune_ty` 未反转 pruning 掩码**：与 L05–L08 及快版 `prune_ty_bump`
  （`mask_inner_first.iter().rev()`）口径相反，多层非线性掩码下 parity 分叉；已统一。
- **L11/L12 自递归宏无展开深度上限**（P0）：`macro_rules m { () => { m } } def x = m`
  无界递归栈溢出；加 `thread_local` + RAII `MacroDepthGuard`（上限 256），超限给解析错误。
- **L10 快版 `unify_catch` expected/find 标签反向**（既有诊断 parity 裂缝）：对齐参考版。

### 2.4 质量 / 文档
未使用导入/死代码清理、packed-word 解引用 SAFETY 注释补齐（L01–L12）、
过期 `//TODO:revPruning` / `Machine` 误拷注释删除、README 测试计数校准、
失效测试引用订正。

## 3. 残余问题（诚实记录，未修）

### 3.1 [P0] 快版整机重借的 Stacked Borrows 别名 UB
- 位置：`L10 bump_spine_iter.rs:3729/3739/3741-3753`（回调 `:2232/:2347/:2370`）、
  `L11 :2385/:2501/:2524`（句柄 `:3946`）、`L12 :2436/:2552/:2575`（句柄 `:4022`）。
- 机制：`unify` 取 `let mach_ptr = self` 后解构字段 `&mut`，`unify_iter` 在字段借用存活时
  `unsafe { (&mut *mach_ptr).solve_multi_trait_ref(..) }` 重建整机 `&mut` 并写 `metas`——
  严格 SB 下先前字段借用被 invalidate，属 use-after-invalidate。
- 三个 agent 独立复核结论一致（A3/A4/A5 均同意刻画成立）。
- 未修原因：修复需把 `solve_multi_trait_ref`/`solve_trait_ref` 改成接收不相交字段的自由函数，
  属高风险重构，且本环境无 Miri 无法验证；盲改可能引入真实错误。
- 建议：单独立项 + CI 跑 Miri（`MIRIFLAGS=-Zmiri-strict-provenance cargo miri test`）。

### 3.2 [P1→已修复] L10/L11 `Synth` 假匹配（错误结果）
- 位置（修复前）：`L10 typeclass.rs:377-380`（`:378` 自述省略 occurs check），
  接收者路径 `elaboration.rs:828`；L11 同码 `typeclass.rs:370`。
- 复现：`impl[T] Say for List[T]` + `def f[T](x: T): String = x.say` + `f two`
  → 旧实现输出 `"list"`（泛型 `T` 被误配到 `List[T]` 实例；正确行为是"无实例"错误）。
- **已修复**：`try_resolve` 的双向 `unify` 改为单向 `match_typ(goal, pattern)`
  （只允许实例侧 `Typ::Var` 绑定，目标侧 rigid 拒绝构造子；`Any` 通配语义不变），
  对齐 L12/L13 的 `val_match`。参考版与快版共用同一 `Synth`，一处修复两版同判。
  回归测试：`tests/l10_fast_parity.rs`、`tests/l11_fast_parity.rs` 的
  `synth_rigid_generic_not_falsely_matched`。实测泛型目标现报无实例 Err，
  与 L13 行为一致。

### 3.3 [P0/P1] L13 共享文件中的同族缺陷（本次范围外，已定位）
- 宏展开无深度上限：`src/L13_namespace/parser/mod.rs:1267/1603/3151`（同构副本）。
- `XCell` 无 `#[repr(align(8))]`：`src/L13_namespace/bump_spine_iter.rs:541`（wasm UB）。
- `intersect_go unreachable!()`、`prune_ty` 未反转、哨兵边界等与 L09–L12 同族
  （`L13_namespace/unification.rs` 等）。
- 由于本次任务限定 L01–L12 且 L13 为共享文件，未改；建议按同款补丁跟进。

### 3.4 needs-verify（已刻画，未改）
- L09 不支持"卡住 match 再被应用"（`v_app` panic；已在 `L09/mod.rs` 模块头正式记为限制）。
- L09 `check_universe` 把 meta 解成 `U(0)`（`elaboration.rs:135`，上游 TODO）。
- L12 canonical IDDFS `basic_target_limit < target_limit` 跳过偶数预算，
  完备性存疑（`canonical.rs:19-24`）。
- L12 `vals_eq_ground` 把 `Val::Flex` 视为等于一切、`Match` 分支忽略 case 表
  （`typeclass.rs:130/197/227-231`）。
- L12 快版 `v_to_ref_val` 链头 `unreachable!`（`bump_spine_iter.rs:5771`）。
- L10 参考版缺 L08/L13 的 unify/force fuel 护栏；`pretty` 越界/SumCase panic；
  `elaboration.rs:287` unwrap；`typeclass.rs:42` flat_map 静默丢参。
- L09/L10/L11/L12 若干 P3 文档行号漂移与 README 计数（见各 `a*-r3.md`）。

## 4. 收敛判定（诚实版）

- A1（L01–L03）、A2（L04–L06）、A3（L07/L09）：**收敛**，自审与交叉均 0 个 P0/P1/P2。
- A4（L08/L10）、A5（L11/L12）：**条件收敛**——所有可安全修复项清零，但明确记录
  §3.1 SB P0 与 §3.2 假匹配 P1 为需独立立项的深水区残余。
- 因此，严格意义上"所有 agent 都认为代码完美"**未达成**：仍存在 1 个 SB 别名 UB
  （L10–L13 共有，见 §3.1）与若干已文档化的 needs-verify/跨层共享副本问题；
  L10/L11 的假匹配 P1 已在后续移植中修复（见 §3.2）。
  这些均**不适合在没有 Miri 与专项验证的条件下盲改**——盲改一个正在工作的
  依赖类型语言实现的风险高于保留有据可查的已知项。

## 5. 如何查看

- 改动：`cd F:/projects/hermes/elaboration-zoo-lsp-review && git diff`
- 报告：`docs/review-l01l12/`（`BRIEF.md`、`ROUND2.md`、`a1..a5-r1/r2/r3.md`、`a*-cross-r2.md`）
- 复跑门禁：`CARGO_TARGET_DIR=F:/projects/hermes/elaboration-zoo-lsp/target cargo test --test l10_fast_parity -- --ignored`（假匹配探针）
- 改动尚未提交（按约定不擅自 commit）；如需保留请提交 `review/l01l12-perfect` 分支。
