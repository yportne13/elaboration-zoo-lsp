# L08-RC：L08 reference 值层 Rc 化（Val Rc）+ Tm Rc 评估

> 分支 `feat/l08-val-rc`（worktree `C:\ezl-wt-l08rc2`）· 基线 master `a770d9ef` · **未 push**
> 构建：`CARGO_TARGET_DIR=C:\ezl-target-l08rc2` · 时点 2026-11-11 01:20–02:20
> 模板：L09 `33a08764`（Val 负载 Rc，不动 eval/force 签名）；L10 Tm 表示（Tm Rc 参考）
> 范围：只动 `src/L08_product_type/` 参考版（5 个 .rs）；**未动其它层、未动 L08 twin**。

## 0. 结论（TL;DR）

- **Val Rc 已完成并落地**：commit **`c8f26323`**（5 文件 +132/−115）。
  `Obj/Pi/Match/VSub` 负载 `Box→Rc`；`Sum` params/cases、`SumCase.datas` 载荷 `Rc<Vec<..>>`；
  `Match` 的 cases 与 **L08 特有 pending** 均 `Rc<Vec<..>>`。eval/force/v_app 签名与求值形状不变。
- **门禁全绿**：`cargo check --all-targets` 0 error；L08 lib **60**（release + debug）；
  blackbox **57+1 ignored**；blackbox_v2 **51+2**；parity **95**；L07 对照 lib **70** / parity **97**。
- **性能（同窗口交错 A/B，7 对/格，min-of-3 rounds）**：
  **struct k10 7.571→5.838 ms（0.77×）、k13 64.20→50.19（0.78×）；natadd k13 25.29→19.55（0.77×）；
  match k10 0.097→0.084（0.87×）**；church/strchain/global 中性（±5% 窗口噪声内）。
- **Tm Rc：已评估、未落地**——受阻于 twin 的类型依赖（见 §4）：L08 twin 的
  `bump_spine_iter/entry.rs:14` 直接 `use crate::L08_product_type::Tm as CTm`，`export()` 用参考
  `Tm` 构造导出树；改 Tm 表示必须改 twin，而本任务约束「不要动 twin」。**建议另开任务**（估 1–1.5h）。

## 1. Val Rc 变更清单（commit `c8f26323`）

| 文件 | diff | 内容 |
|---|---:|---|
| `mod.rs` | +? / −?（主改动，183 行 diff） | `Val` 枚举负载：`Obj(Rc<Val>)`、`Pi(.., Rc<VTy>, ..)`、`VSub(Rc<Val>, ..)`、`Match(Rc<Val>, Env, Rc<Vec<(PatternDetail,Tm)>>, Rc<Vec<(Val,Icit)>>)`、`Sum(.., Rc<Vec<params>>, Rc<Vec<Span>>)`、`SumCase{datas: Rc<Vec<..>>}`；`force/frcs/eval/quote/subst/env 包裹/mentions/val_eq 等构造与解构点适配（`Rc::new` / `(*x).clone()` / `.iter()`） |
| `unification.rs` | +18/−18 | rename/invert/prune/unify 各臂：`(*a).clone()`、`Rc::new`、`Rc<Vec>` 解构；`Tm` 侧构造保持不变 |
| `elaboration.rs` | +9/−9 | `Val::Pi` 构造与 `*a` move-out 改 clone；`Val::Obj`/sumcase 构造 |
| `pattern_match.rs` | +3/−3 | `SumCase.datas` Rc、`Val::Sum` cases 解引用、`dom` clone |
| `cxt.rs` | +2/−2 | `subst_cxt` 的 `VSub` 包裹、`bind_slots` 的 VSub 解包（`&**inner`） |
| **合计** | **+132/−115** | 语义不变（纯表示/克隆成本变化） |

### 设计要点与 L08 特有决策
- **pending 也 Rc**：L08 的 `Val::Match` 有第 4 字段 `pending: Vec<(Val,Icit)>`（L09/L10 无）。
  为保证 `Val::Match` clone 全 O(1)，改成 `Rc<Vec<(Val,Icit)>>`；唯一的 push 点
  （`v_app` 的 Match 臂）用 copy-on-write：`let mut pending = (*pending).clone(); push; Rc::new(..)`。
  stuck-match 的应用次数平时很小/为空，实测无回归（match/struct 反而变快）。
- **Sum/SumCase 载荷 rc**：L08 的 `Sum` 条目已是 `Rc<Val>/Rc<VTy>`，但外层 `Vec` 还是内联；
  改成 `Rc<Vec<..>>` 后 `Val::Sum`/`Val::SumCase` 的 clone 不再分配/克隆 Vec。
- **不动签名**：`eval/force/frcs/v_app/quote/rename` 仍按值收 `Val`、按值返回；只把字段表示换成 Rc，
  所有站点以 `(*x).clone()`（O(1) 计增）替代 move-out。

## 2. 门禁（全绿，release 除注明外）

| 套件 | 结果 |
|---|---|
| `cargo check --release --all-targets` | ✅ 0 error（仅既有 warnings） |
| `cargo test --release --lib L08_product_type` | ✅ **60 passed** |
| `cargo test --lib L08_product_type`（debug） | ✅ 60 passed |
| `cargo test --release --test l08_blackbox` | ✅ 57 passed / 0 failed / 1 ignored |
| `cargo test --release --test l08_blackbox_v2` | ✅ 51 passed / 2 ignored |
| `cargo test --release --test l08_fast_parity` | ✅ **95 passed** |
| L07 对照：`--lib L07_sum_type` / `--test l07_fast_parity` | ✅ 70 / 97 passed |
| 全量 lib（所有层，最后跑） | ✅ **994 passed / 0 failed / 6 ignored**（92.3 s；见 `full-lib.txt`） |

原始日志：`C:\ezl-src-bench-l08rc2\{valrc-gates,valrc-debug-lib,full-lib}.txt`。

## 3. 性能（`l08bench --only basic --rounds 3`，同窗口 7 对反向交错、每侧取 min/median）

### 3.1 k=10（重点 natadd/church/struct/match）

| workload | baseline min (ms) | Val Rc min (ms) | ratio(min) | ratio(median) |
|---|---:|---:|---:|---:|
| **struct** | 7.571 | **5.838** | **0.771** | 0.792 |
| **natadd** | 2.047 | **1.563** | **0.764** | 1.063\* |
| **match** | 0.097 | **0.084** | **0.866** | 0.876 |
| church | 0.710 | 0.735 | 1.035 | 1.033\* |

### 3.2 k=13

| workload | baseline min (ms) | Val Rc min (ms) | ratio(min) | ratio(median) |
|---|---:|---:|---:|---:|
| **struct** | 64.204 | **50.189** | **0.782** | 0.802 |
| **natadd** | 25.294 | **19.549** | **0.773** | 0.747 |
| church | 7.057 | 7.782 | 1.103\* | 0.902\* |
| strchain | 52.641 | 51.739 | 0.983 | 1.001 |
| global | 58.793 | 58.478 | 0.995 | 0.981 |

\* 小负载/窗口噪声格：natadd k10 与 church 的 median 与 min 方向不一致（绝对值 <1ms 或 ±5% 内），
以 min 与 k13 同向数据为准；结论取「struct/natadd/match 显著变快，church/strchain/global 中性」。

口径与局限：共享机器（其他 agent 同时构建/bench），绝对值有 ±10–30% 窗口漂移；因此用**同窗口
7 对反向交错**的 min/min 比值为准（与 L09 `33a08764` 的 A/B 方法一致：natadd −24%、match −15%、
church −7%、strchain −2.5%）。本层 struct 是 L08 特色负载（大量 `Val::Obj` 投影 + SumCase 值），
收益最大（−21~23%），符合"产品投影路径 clone 最重"的预期。

## 4. Tm Rc：已试做评估，未落地（受阻于 twin 依赖）

**计划**（照 L10 表示）：`Tm::Obj(Rc<Tm>)`、`App(Rc,Rc)`、`AppPruning(Rc)`、
`Let(.., Rc<Ty>, Rc<Tm>, Rc<Tm>)`、`Sum(Span, Vec<(Span,Rc<Tm>,Rc<Ty>,Icit)>, Vec<Span>)`、
`SumCase{typ: Rc<Tm>, datas: Vec<(Span,Rc<Tm>,Icit)>}`、`Match(Rc<Tm>, Vec<(PatternDetail,Rc<Tm>)>)`。
（L08 的 `Lam`/`Pi` 已是 Rc，无需改。）

**为何没做**：只改枚举后 `cargo check --lib` 立刻出现 **59 个错误**，其中 8 个在
`src/L08_product_type/bump_spine_iter/entry.rs`（twin）——该文件:
```rust
use crate::L08_product_type::Tm as CTm;   // entry.rs:14
pub(super) fn export(t: &Tm<'_>) -> CTm   // entry.rs:26：把 bump 项导出成参考 Tm（供 pretty/节点数互检）
```
即 **L08 twin 直接以参考版 `Tm` 为导出类型**（`export` 里 `CTm::App(Box::new(..))` 等 ~25 处构造）。
要改参考 `Tm` 表示，必须同步改 twin 的 `export`/`tm_size`；这与任务约束「**不要动其它层/twin**」冲突。

**成本估计（若允许动 twin）**：
- 参考侧机械适配 ~51 处：`mod.rs` ~25（eval/quote/rename/shift_tm/tm_size/val_mentions 等）、
  `elaboration.rs` 14、`unification.rs` 12、`pretty.rs`/`struct_eq.rs`/`cxt.rs`/`syntax.rs` 若干，
  全部为 `Box::new→Rc::new`、`(*x)` 解引用、`.iter().cloned()`；
- twin 侧 `entry.rs` `export()` 的 ~25 处 `CTm::..` 构造同步改（纯类型适配，无语义）；
- 门禁同本次 + `cargo check --all-targets`；预计 **1–1.5 小时**（含编译与 A/B）。
- 风险：中等偏低（与 Val Rc 同类机械改动），但会**触到 twin**，需 Lead 明确放宽约束后再做。
- 另注：Tm Rc 对性能的增益预期小于 Val Rc（clone 点集中在 elaborate 期 Tm 传递，但本层 nf/quote
  路径以 Val 为主；L10 的 Tm Rc 是其强类型/宏路径需要）。若要做，建议与「`Decls::ver`+simpl 缓存回移」
  一起评估，而非单独追求。

## 5. 风险与注意事项

1. **语义**：纯表示替换；所有 clone 语义等价（Rc 共享不可变），无求值顺序/短路变化。
   唯一需留意的是 `Rc<Vec<..>>` 载荷的**不可变共享**：L08 这些 Vec 构造后从不就地改（pending 例外，
   已用 COW），因此安全。
2. **pending COW**：`v_app` 每次给卡住 match 追加实参时克隆一次 pending Vec（元素是 `(Val,Icit)`，
   Val 现在 clone O(1)）；实测 match/struct 无回归。若未来 pending 变长明显，可改 `Rc::make_mut`。
3. **twin 未动**：L08 twin 的 `Val`/`Tm` 表示完全不变，parity 95 与 bench 节点断言照常通过
   （参考版输出与 twin 逐字节一致是本次最强的语义证据）。
4. **L07 未动**：L07 对照 lib/parity 全绿（共享 lib 编译单元，但代码未改）。
5. **窗口噪声**：见 §3；如需发表级数字，可在安静窗口用保存的
   `l08bench-baseline.exe` / `l08bench-valrc.exe` 重跑 7–9 对反向交错。

## 6. 复现

```powershell
cd C:\ezl-wt-l08rc2
$env:CARGO_TARGET_DIR='C:\ezl-target-l08rc2'
cargo check --release --all-targets
cargo build --release --bin l08bench
cargo test --release --lib L08_product_type
cargo test --release --test l08_blackbox
cargo test --release --test l08_blackbox_v2
cargo test --release --test l08_fast_parity
cargo test --release --lib L07_sum_type
cargo test --release --test l07_fast_parity
cargo test --lib L08_product_type          # debug
cargo test --release --lib                 # 全量
# A/B（安静窗口）
C:\ezl-src-bench-l08rc2\l08bench-baseline.exe --workload struct --max-k 13 --rounds 3 --only basic
C:\ezl-src-bench-l08rc2\l08bench-valrc.exe    --workload struct --max-k 13 --rounds 3 --only basic
```

产物：`C:\ezl-src-bench-l08rc2\`（`l08bench-baseline.exe`、`l08bench-valrc.exe`、`ab-*`/`c-*` 原始
A/B 日志、`*-gates.txt`/`valrc-debug-lib.txt`/`full-lib.txt` 门禁日志）。

## 7. 交付状态

- 分支 `feat/l08-val-rc`：`a770d9ef` + **1 commit `c8f26323`**（Val Rc）；工作树干净；未 push。
- Tm Rc：**未落地**（原因见 §4，等待 Lead 决定是否允许动 twin 后另开任务）。
