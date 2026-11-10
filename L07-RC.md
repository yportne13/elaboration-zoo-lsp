# L07 reference：Val 层 Rc 化（L09 `33a08764` 模板）

> worktree `C:\ezl-wt-l07rc2`，分支 `feat/l07-val-rc`（从 master `a770d9ef` 拉出）；
> `CARGO_TARGET_DIR=C:\ezl-target-l07rc2`；未 push、未动其它层/twin、未改 reference 语义。
> 任务：把 L09 已完成的 Rc 值表示模板（`33a08764`）拿到 L07 reference；Tm Rc 视风险/时间。

## 0. 结论

1. **Val Rc 已落地**（commit **`0b03e44a`**，6 文件 **+121/−113**）：`Obj/Pi/VSub` 的 `Box` 改 `Rc`，
   `Sum` 的参数/构造子名表与 `SumCase.datas`、`Match.cases` 改 `Rc<Vec<…>>`，`Match` 的 scrutinee
   改 `Rc<Val>`；`Val` clone 从"整树深拷 + 每个 payload Vec 重新分配（逐元素 String clone）"
   变成 O(1) 指针递增。**不改 Tm / eval / force / v_app 的签名与形状**，语义不变。
2. **A/B（同批交错，base=`a770d9ef` vs own，`--only basic --rounds 3`，min/median）**：
   **natadd k10 1.144→0.934ms（0.816×，−18.4%）**、**match k13 0.097→0.084ms（0.866×，−13.4%）**、
   strchain k10 0.982×、church k10 1.007×（噪声）。load 11%→13%；无 >5% 回落。
   （L09 同模板实测 natadd −24.4% / match −14.7% / church −7% / strchain −2.5%，L07 形似。）
3. **门禁全绿**：L07 lib **70**；blackbox **48+1 / 51+2 / 116+1**；`l07_fast_parity` **97**；
   L08 对照 lib **60** + `l08_fast_parity` **95**；L07 **debug lib 70**；全量
   `cargo test --release --lib` **994 passed / 0 failed / 6 ignored**；`cargo check --all-targets` **0 error**。
4. **Tm Rc 未做**（按 Lead 口径"风险大就只留 Val Rc"）。L07 `Tm` 仍是 `Lam/Pi: Rc` 之外，
   `Obj/App/AppPruning/Let/Sum/SumCase/Match` 用 `Box`/内联 `Vec`（见 §5 清单）。评估与计划见 §5；
   预计 1.5–2h（构造/匹配面巨大且波及 eval/force/quote/rename/pretty/unify/struct_eq），
   建议单独任务 + parity/deep 门禁兜底。
5. 说明：更早的 **L08 twin PrimFunc 第二半**在本 worktree 之外进行，补丁曾编译/门禁在跑，
   但原工作树 `C:\ezl-wt-twinprim` 已被回收，**未产生 commit**；如需继续，按 `TWIN-PRIMFUNC.md` §8
   在新 worktree 重放（L07 版补丁可作模板）。

## 1. 模板映射（L09 `33a08764` → L07）

| L09 模板 | L07 落地 |
|---|---|
| `Obj(Rc<Val>, …)` | `Obj(Rc<Val>, Span<String>, Spine)` |
| `Pi(…, Rc<VTy>, …)` | `Pi(…, Rc<VTy>, Closure)`（`VTy = Val`） |
| `Match(Rc<Val>, Env, Rc<Vec<(PatternDetail,Tm)>>)` | `Match(Rc<Val>, Env, Rc<Vec<(PatternDetail,Tm)>>, Vec<(Val,Icit)>)`（L07 多 pending 字段） |
| `VSub(Rc<Val>, Rc<Subst>)` | 同（L07 已有 `Subst` 持久链） |
| `Sum(…, Rc<Vec<params>>, Rc<Vec<cases>>)` | `Sum(Span<String>, Rc<Vec<(Span<String>, Rc<Val>, Rc<VTy>, Icit)>>, Rc<Vec<Span<String>>>)` |
| `SumCase { datas: Rc<Vec<…>> }` | 同 |
| 构造/拆箱点：`Rc::new` / `rc_take` / `(*x).clone()` | 同；`frcs` 臂用 `(*x).clone()`（Rc clone 廉价）；`wrap_sub`/`frcs_env` 的 VSub 包裹改 `Rc::new` |

L07 原已有 `rc_take`（元素级 `Rc<Val>` 复用助手），本轮未新增语义助手。

## 2. 改动文件（`0b03e44a`）

| 文件 | 改动 |
|---|---|
| `mod.rs`（+~142） | `Val` enum 字段改 Rc；`force` 的 `Obj/Pi/Sum/SumCase/Match/VSub` 臂、`frcs`/`frcs_env`、`wrap_sub`、`eval` 的 `Tm::Obj/Pi/Sum/SumCase/Match` 构造、`quote`/`quote_arm`/`quote_deep` 的拆箱（`(*x).clone()`、`Rc::new(...)`）、`rc_take` 适配 |
| `unification.rs` | `rename` 的 `Pi`/`Match`/`Sum`/`SumCase` 拆箱；rename 深链收集器 `pending` 用 `(*x).clone()`；cfg(test) 深链用例构造改 Rc |
| `elaboration.rs` | `Val::Pi` 构造 `Rc::new`；`fresh_meta`/`quote` 的 `(*a).clone()`；`absurd`/type-annotation 臂 |
| `pattern_match.rs` | `SumCase.datas` 构造 `Rc::new`；`sum_cases()` 用 `as_ref().clone()`；`Pi.dom` 拆箱 |
| `cxt.rs` | `subst_cxt` 的名字表包装 `Val::VSub(Rc::new(...))` |
| `tests.rs` | 测试构造点（VSub/Sum/SumCase 深链 fixture）同步改 Rc |

`Tm` 零改动 → `l07_fast_parity`（ref↔twin 逐字节/判定）保持 97/97。

## 3. 门禁

| 套件 | 结果 |
|---|---|
| `cargo test --release --lib L07_sum_type` | ✅ 70 passed |
| `cargo test --lib L07_sum_type`（debug，验断言/布局） | ✅ 70 passed |
| `l07_blackbox` / `_v2` / `_v3` | ✅ 48+1 / 51+2 / 116+1 |
| `l07_fast_parity` | ✅ **97 passed** |
| L08 对照 `--lib L08_product_type` / `l08_fast_parity` | ✅ 60 / 95 passed |
| `cargo test --release --lib`（全量） | ✅ **994 passed, 0 failed, 6 ignored**（137.9s） |
| `cargo check --all-targets` | ✅ 0 error（仅既有 warning） |

## 4. A/B（l07bench，同批交错 base/own 各 3 次，`--only basic --rounds 3`，min|median）

| 负载 | base (ms) | own (ms) | ratio | 判读 |
|---|---:|---:|---:|---|
| **natadd k10** | 1.144 \| 1.156 | **0.934 \| 0.943** | **0.816×（−18.4%）** | 显著 |
| church k10 | 0.434 \| 0.437 | 0.437 \| 0.444 | 1.007× | 噪声（L09 模板是 −7%，L07 church 负载更小） |
| strchain k10 | 1.692 \| 1.749 | 1.661 \| 1.669 | 0.982× | 持平/略好 |
| **match k13** | 0.097 \| 0.107 | **0.084 \| 0.084** | **0.866×（−13.4%）** | 显著 |

- 口径：独立进程、同窗口 base/own 交替；`load` 采样 11%→13%（共享机）；
  min 与 median 同向，无长尾假象；无 >5% 回落项。

## 5. Tm Rc：剩余清单与计划（未做）

L07 `Tm`（`mod.rs:65-94`）现状：`Lam(…, Rc<Tm>)`、`Pi(…, Rc<Ty>, Rc<Ty>)` 已是 Rc；**其余**：

```
Obj(Box<Tm>, Span<String>)
App(Box<Tm>, Box<Tm>, Icit)
AppPruning(Box<Tm>, Pruning)
Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>)
Sum(Span<String>, Vec<(Span<String>, Tm, Ty, Icit)>, Vec<Span<String>>)
SumCase { typ: Box<Tm>, case_name, datas: Vec<(Span<String>, Tm, Icit)> }
Match(Box<Tm>, Vec<(PatternDetail, Tm)>)
```

对应 L10 模板：`Tm` 全 `Rc` + `eval(&Rc<Tm>)`。波及：`eval/force/v_app/quote/quote_deep/rename/
pretty/struct_eq/unify/elaboration/pattern_match/tests`（构造点与模式匹配数百处），以及
`Tm` 的 `Clone`/移动语义（`quote_deep` 的 move 纪律、`simpl_decl` 缓存）。预计 1.5–2h；
建议独立任务，先做 `Obj/App/AppPruning/Let` 小步（与 Val 同型、风险低），再做 `Sum/SumCase/Match`
（带 payload Vec → `Rc<Vec>`），每步跑 L07 lib/blackbox/parity + L08 对照，最后 A/B。

## 6. 复现

```powershell
git switch feat/l07-val-rc          # worktree C:\ezl-wt-l07rc2
$env:CARGO_TARGET_DIR='C:\ezl-target-l07rc2'
$env:RUST_MIN_STACK='67108864'
cargo test --release --lib L07_sum_type
cargo test --release --test l07_blackbox --test l07_blackbox_v2 --test l07_blackbox_v3
cargo test --release --test l07_fast_parity
cargo test --lib L07_sum_type
cargo test --release --lib
cargo check --all-targets
cargo build --release --bin l07bench
# A/B：base = a770d9ef 构建；own = 本分支；--only basic --rounds 3
#   --workload natadd --max-k 10 / church 10 / strchain 10 / match 13
```

## 7. 交付

- 分支 `feat/l07-val-rc`：**`0b03e44a`**（Val Rc）+ 本报告 commit；**未 push**；工作树干净（scratch 已清）。
- 其它层 / twin / 主工作树：未改；未动 `Cargo.toml`/构建配置。
