# Phase A/B/C 实测记录：为什么 smalltt 的机制在本仓库需要"先换表示"

> 2026-11-20，分支 `exp/l07-phase-a-unfold`（从 master 04d0a005 拉出，**未合入**）。
> 目标：按 `docs/smalltt-opt-techniques-analysis-2026-11-20.md` §5 的顺序，一步步实现并测量：
> A 值表示（VUnfold/quote 三档）→ B 有界近似转换（ConvState）→ C meta 解报价/eta-short。
> 结论：**这三步在本仓库当前的值表示上都无法单独拿到收益**，每步都实测了原因。
> 代码全部回退（实验分支只保留本文与 `tools/l07opt/` 的可复用 A/B 工具），master 未动。

## 0. 结果汇总

| 步骤 | 改动 | 门禁 | 性能（同机，30 档合计） | 判定 |
|---|---|---|---|---|
| A-1 | `quote_none`（smalltt `quote UnfoldNone`）：无注解 let / binder 类型不展开 | 全绿 | pairTest20 -2%（仅一处） | 收益可忽略 |
| A-2 | 顶层 def 值登记为**折叠头**（glued eval 的 VUnfold 对应物） | **失败**（lib 2/parity 5） | — | 语义不成立（见 §1.2） |
| B | 两段式转换：先 `force_metas` 近似（只展开 meta、Decl 保持折叠头）失败回退 | 全绿 | **stlc -37%**（0.63×） | 净负 |
| B' | 近似前加闸门（只在同折叠头/带 spine 形态尝试） | 全绿 | 合计 1.00×（忠实地退化为旧行为） | 闸门命中率 2–18%，且几乎都失败 |
| C-1 | eta-short meta 解（smalltt `etaContract`） | **失败**（blackbox v3 3 条） | -1~4% | 语义不成立（见 §3.1） |
| C-2 | `fresh_meta` 的类型 quote 改 `quote_none` | 全绿 | **-2~9%**（stlc80 7.40→7.77 s） | 净负 |

一句话：**本仓库参考版的 `force` 是"全展开"语义，任何"保留折叠头"的局部改动要么语义破裂、
要么因为双次展开而更慢**；要拿 smalltt 的收益必须先换值表示（VUnfold + G + ConvState 一起），
这不是分步可增量的大改，估算 2–3 周、且要让孪生版同步。

## 1. 步骤 A：值表示（VUnfold / force 三档 / quote 三档）

### 1.1 做了什么

- `UnfoldMode { All, Metas, None }` + `force_impl`/`force_metas`：`Metas` 档对
  `Decl/Prim/Obj` 直接返回折叠头（对应 smalltt `force`，Evaluation.hs:100-111）。
- `quote_none`：对应 smalltt `quote UnfoldNone`（Evaluation.hs:157-193），
  保存类型/项时不再展开已解 meta 与顶层 def。
- 落点：无注解 let 的推断类型（Elaboration.hs:289 同款）、binder 类型、`fresh_meta` 的闭合类型。

### 1.2 关键失败：本仓库的 def 值本来就是"已展开 + 折叠占位"两套形态

把顶层 def 的值改成折叠头（`Decl(自身名, [])`）会**与递归自引用占位撞车**：
L07 用同一个 `Decl(name, [])` 既表示"递归中的占位"（`fake_bind`，force 拒绝展开）
又表示"正常的全局引用"。实测 lib 2 条（`test_decl_table_and_globals`、`test_file_io_builtins`）、
parity 5 条失败——所有全局调用都变成"卡住"。smalltt 能这么做，是因为它有**独立的
`UnfoldHead` 表示**（`CoreTypes.hs:78-101`）+ 展开体字段，与"未求解占位"天然可区分。

=> 结论：A 步不是"加一个 quote 档位"，而是**Val 表示重构**（引入折叠头专用的值变体，
并把 decl 表存成"头 + 惰性体"）。这是 B/C 的前置条件，单独做没有收益（`quote_none` 实测仅 pairTest20 -2%）。

## 2. 步骤 B：有界近似转换（ConvState = Rigid）

### 2.1 做了什么

- `unify_impl(mode)`：`Metas` 模式下同 `Decl` 头先比 spine（对应 `Unification.hs:355-361`），
  且不解 meta（对应 `guardCS`）；`unify_catch` 先跑近似、失败用 `meta_snapshot` 回滚再跑全展开。
- 消融开关 `L07_NO_APPROX`（默认开启，用于 A/B）。

### 2.2 实测

| 用例 | base | 近似（无闸门） | 近似（有闸门） |
|---|---:|---:|---:|
| stlc 80 | 7.40 s | **11.71 s（0.63×）** | 7.38 s（1.00×） |
| stlcs 96 | 710.7 ms | 1.04 s（0.68×） | 721 ms（0.99×） |
| pairtest 20 | 5.38 s | 5.37 s | 5.34 s |
| treeconv 18 | 568.7 ms | 562 ms | 557 ms |
| natconv 100k | 168.5 ms | 173 ms | 174 ms |
| **30 档合计** | **37.69 s** | **51.84 s（0.73×）** | **37.73 s（1.00×）** |

### 2.3 为什么

- 本仓库 `force` 是**全展开**：一旦要比较，两侧本来就会展开成 WHNF；先做一次
  "只展开 meta"的近似，绝大多数情况**仍然失败**（因为折叠头几乎不出现——见 §1.2），
  于是付两次展开代价。
- 加了闸门后：stlc80 命中 12 960/70 402（18%）、其中成功 960（7.4%）；treeconv18 命中 36/250、成功 1。
  成功的一次也只是省掉一次展开，量级不足以抵消判据本身的浅层 force 开销。
- smalltt 的近似转换之所以赚，是因为**顶层头本来就折叠**（VUnfold），近似命中率高；
  本仓库值的形态决定了近似很难命中。

## 3. 步骤 C：meta 解报价 / eta-short / occurs

### 3.1 eta-short：语义不成立

实现（剥公共尾部 eta 实参，`Unification.hs:259-298` 同构）后 blackbox v3 有 3 条失败：
`redex_regression_extra_domain`、`redex_regression_eq_swapped_args`、`redex_family_full_parity_scan`
（双实现全文不一致）。原因：L07 的 `rename` 对解出的项有**作用域/剪枝纪律**（assembly 顺序、
`prune_vflex` 的 Tm 重建），简单剥 spine 尾部会改变解的形状，破坏既有钉死的等价性。
性能侧即使不看语义也只 -1~4%（stlc80 7.295 vs 7.376 s）。

### 3.2 `fresh_meta` 改 `quote_none`：净负

`fresh_meta` 的闭合类型改成不展开后，stlc80 7.40→**7.77 s（-5%）**、stlcs192 1.43→1.59 s（-11%）、
vectest960 357→372 ms（-4%）。原因：meta 类型后续会被 force 做 unify/quote，
存储时省下的展开会在**更热的读取点**重复付出（且 close_ty 后重复 quote）。

### 3.3 occurs cache（smalltt `approxOccursInSolution`）：未单独实现

本仓库的 occurs 检查（`val_mentions_lvl` / `occurs_transitive`）已经是迭代栈 + 早退，
且 pairTest 的指数**不在 occurs**（探针实测：pairTest20 `unify=43`、`solve=21`、
**`rename=16 777 060`**）——加 cache 不会碰这个指数。

## 4. pairTest 的真实成因（探针，已在本次实验中确认）

`dup x_{i-1}` 的隐式 meta 与 `x` 的类型合一 → `force` 把 `Pair` 展开成 Pi →
`solve` 的 `rename` 逐个**内联已解 meta**（每层复制 2 份）→ 2^k：

| 层数 | unify | solve | **rename** | eval | 时间 |
|---|---:|---:|---:|---:|---:|
| 10 | 33 | 11 | 16 298 | 17 149 | 3.0 ms |
| 15 | 38 | 16 | 524 167 | 525 738 | 92 ms |
| 20 | 43 | 21 | **16 777 060** | 16 779 576 | 3.08 s |

smalltt 阻断这条链靠的是 **`rigidQuote` 输出 `Meta/Meta` 引用而不是内联解值**
（`Unification.hs:82-127`）——但那需要解本身是"小项"，而小项又需要 VUnfold 值表示（§1.2）。
本次尝试过 `rename` 的 dom=0 快路径 + `solve` 的 closed 快路径，均无效：
`rename` 入口的 `force` 已把 meta 展开，快路径根本看不到折叠头。

## 5. 建议

1. **不要分步做 A/B/C**：A 的"折叠头"必须先与 B/C 同批落地（Val 变体 + decl 表存"头+惰性体"），
   否则每一步都是净负或语义破裂——本次已逐一验证。
2. 若要做，按**一次性表示重构**推进：Val 增折叠头变体（与递归占位区分）、decl 表惰性体、
   force 三档、quote 三档、ConvState、rigidQuote —— 与孪生版同步，预计 2–3 周 + 全量门禁回归。
3. 在此之前，L07 参考版的性能改进应继续只做"不改变值表示"的局部优化（如你们 11-18 已做的分配器/
   迭代 quote 类实验），并接受与 smalltt 的 5–47× 差距来源是表示层。

## 6. 复现

```powershell
# 基线（master 构建）：
git worktree add C:ezl-base master
cd C:ezl-base; cargo build --release --bin smallttbench --bin l07bench
# 当前分支：
cargo build --release --bin smallttbench --bin l07bench
# A/B：
powershell -File toolsl07optun_ab_cases.ps1 -Exe <base>smallttbench.exe -Tag base -OutDir targetl07opt
powershell -File toolsl07optun_ab_cases.ps1 -Exe targeteleasesmallttbench.exe -Tag new -OutDir targetl07opt
python toolsl07optsummarize_ab.py --dir targetl07opt
```

原始数据：`F:\projects\hermes\_ref\l07opt\ab\`（base/new 的 elab/nf/alloc/synth 日志）、
`F:\projects\hermes\_ref\l07opt\gates_*.log`（门禁输出）。
