# L07 fast twin：L13 式 PrimFunc-on-decl（L08 待续）

> worktree `C:\ezl-wt-twinprim`，分支 `feat/twin-primfunc`（从 `6e4a94bd` 拉出）；
> `CARGO_TARGET_DIR=C:\ezl-target-twinprim`；未 push、未动主工作树、未改 reference 语义。
> 背景：此前 `0971ad2e` 已把 L07/L08 **reference** 改为 L13 式 PrimFunc（prim 挂 decl 条目、
> `Val::Decl`+spine 应用），但 fast twin 仍走 `Tm::Prim`/`XCell::Prim` 特例。本轮把 **L07 twin**
> 改成同形态；L08 twin 未动（计划见 §6）。

## 0. 结论

1. **L07 fast twin 已落地**（commit `77be5d06`，6 文件 **+266/−38**）：builtin 注册不再构造
   `Tm::Prim`；decl 条目带 `prim`/`prim_names`；`eval(Tm::Decl)` 对 builtin 返回中性
   `Decl(自身名)`；`force` 在 Decl 链头按 spine 调 `prim_reduce`；为 partial builtin 的 quote
   增加了与 reference 同形的 **η 展开**（`shift_tm_bump` + `prim_eta_quote` + 链装配用的
   `QJob::QNoEta`）。
2. **门禁全绿**：L07 lib 70 / blackbox 48+1、51+2、116+1 / parity **97**；L08 lib 60 /
   blackbox 57+1、51+2 / parity **95**（L08 未改，作为回归对照）；`twin_engine_tests` **28**；
   `cargo check --all-targets` exit 0。
3. **性能（同批交错 A/B，base=6e4a94bd vs own，`--only fast,fast_ss --rounds 3 --max-k 9`）**：
   L07 fast_ss 全项 **0.93–0.99×**（strchain −5%、global −6.7%、natadd −5.4%、church −1.3%，
   **无回归**）；L08（未改的对照）1.00–1.02×，符合预期。load ≈5%。
4. **Prim 形态**：生产路径**不再构造** `Tm::Prim`/`XCell::Prim`；变体与 quote/rename/export/unify/
   struct_eq 的 Prim 分支作为**只读兼容**保留（正常运行不可达），未做删除式大改以控制风险
   （见 §4）。`force` 残留的 `HK_PRIM` 分派与 `eval(Tm::Prim)` 臂同样是 legacy 只读路径。
5. **未做**：L08 twin 的同一移植（机械同构，预计 1–1.5h，风险与 L07 相同：η/parity）；没有改
   `L08_product_type/bump_spine_iter/**`。

## 1. 设计映射（reference → twin）

| reference（`mod.rs`/`cxt.rs`） | twin 对应 |
|---|---|
| `DeclEntry { ty, val, prim: Option<PrimFunc>, eta, prim_names }` | `DeclEntryF { ty: V, val: V, prim: Option<&'static str>, prim_names: Option<&'static [&'static str]> }`（arena 版不存闭包：builtin 集合固定，`prim` 用静态名字，force 直接 `prim_reduce(name, args)`） |
| `add_builtin`：值 = `Val::Decl(自身名, [])` 中性占位；prim 闭包挂条目；`eta` 仅供显示 | builtin 注册：`val = v_xcell(XCell::Decl(name))`（同款中性占位）；`prim: Some(name)`；`prim_names` 由静态表 `prim_names_static(name)` 给出（与类型 Π 链同名同序） |
| `eval(Tm::Decl)`：prim 条目 → 中性 `Val::Decl`（不展开 λ） | `eval.rs` `W::Tm(Tm::Decl)`：`Some(e) if e.prim.is_some()` → `v_xcell(XCell::Decl(*name))`；否则取 `e.val` |
| `force(Val::Decl)`：prim → force 实参逆序、调 prim 闭包；未命中保持卡住；否则 unfold | `force.rs`：`HK_DECL` 链头 prim 分支（collect_args → 逐个 force → `prim_reduce`，Some 继续，None 返回卡住）；`XCell::Decl` 裸头 prim 分支只烧 1 fuel 后卡住 |
| `quote(Val::Decl+prim_names)`：应用不足时 η 展开 `λ 剩余. (Decl 已有实参…)` | `quote.rs`：`prim_eta_quote`（tag2 spine / tag7 裸 Decl；`have<arity` 时按应用序引已提供实参 → `shift_tm_bump` 平移 → 补 `App Var` → 包 `Lam`），链装配函数部分用 `QJob::QNoEta` 禁止 η（reference `quote_sp` 的结构性 App 拼接不 η 中间部分） |

## 2. 改动文件（`77be5d06`，+266/−38）

| 文件 | 改动 |
|---|---|
| `prim.rs`（+34/−0） | `DeclEntryF` 增 `prim`/`prim_names`；新增 `prim_names_static` 静态参数名表 |
| `machine.rs`（±52） | builtin 注册删 λ 链 → 中性 `Decl` 头 + `prim`/`prim_names`；4 处 `DeclEntryF` 构造补 `prim: None, prim_names: None` |
| `eval.rs`（±6） | `Tm::Decl` prim → 中性 Decl 头（不展开）；`Tm::Prim` 臂保留为 legacy |
| `force.rs`（+30） | `HK_DECL` 增 prim 归约分支；`XCell::Decl` 裸头 prim → 烧 1 fuel 保持卡住 |
| `quote.rs`（+180） | `shift_tm_bump`（arena 版 shift，Sum/SumCase/Match 递归重建）；`prim_eta_quote`；`quote_arg`（私有 scratch 递归）；`QJob::QNoEta` + 3 处链装配 push 改用 |
| `subst.rs`（±2） | `simpl_decl` 的 `DeclEntryF` 拷贝保留 `prim`/`prim_names`（**必须**：否则卡住 match 分支体里的 builtin 会丢 prim） |

## 3. η 展开：为什么必须做（两轮 parity 抓出的真实差异）

L07 twin 改完后 parity 先是 96/97，失败项依次暴露：
1. `def v : String = get_global "missing"`：参考版 `get_global missing`，twin 首版印成
   `(x => get_global x) missing`（把链装配中的**函数部分**也 η 了）。
2. `s => string_concat s !`：参考版保持 `string_concat s !`，twin 印成
   `s => (y => string_concat s y) !`（同样是对中间 partial 值 η）。
解法：η 只对**整值**（spine 链 / 裸 Decl）做；`QJob::QNoEta` 专门用于三处「链装配的函数部分」
引读（right-chain base、二元 fallback 的 fval、ChainRun 的 fi）。最终 parity 97/97。
（这两次失败也说明：η 的边界不是可选装饰，直接影响 parity 逐字节判据。）

## 4. Prim 兼容面（只读、正常不可达，未删）

保留以控制改动半径与避免大范围 rename/quote/export 重写：
- `Tm::Prim` / `XCell::Prim` 枚举变体与 `HK_PRIM`：builtin 注册已不再构造，正常程序不可达；
- `eval(Tm::Prim)`、`force` 的 `HK_PRIM`/`XCell::Prim`、`quote.rs`/`rename.rs` 的 Prim 转换、
  `entry.rs` `J::Do(Tm::Prim)`/`CTm::Prim`、`unify/struct_eq` 的 Prim 臂：legacy 只读；
- 删除这些路径（真正的"去掉特例"）建议放到 L08 一起做一轮，且以 parity 为门禁；
  本轮以"禁止新构造 + 读路径保留"完成目标的可运行部分。

## 5. 门禁（`C:\ezl-target-twinprim`，release；L06/L08 深负载用 `RUST_MIN_STACK=67108864`）

| 套件 | 结果 |
|---|---|
| L07 `--lib L07_sum_type` | ✅ **70 passed** |
| L07 `l07_blackbox` / `_v2` / `_v3` | ✅ 48+1 / 51+2 / 116+1 |
| L07 `l07_fast_parity`（ref↔twin 逐字节/判定） | ✅ **97 passed** |
| L08 `--lib L08_product_type`（对照） | ✅ 60 passed |
| L08 `l08_blackbox` / `_v2` / `l08_fast_parity`（对照） | ✅ 57+1 / 51+2 / 95 passed |
| `twin_engine_tests` | ✅ **28 passed**（85s） |
| `cargo check --all-targets` | ✅ exit 0（1m17s） |

## 6. Bench A/B（同批交错：base/own 各 3 次、k=9、rounds=3，取 min；load≈5%）

| bench/workload | fast_ss base→own (ms) | ratio | fast base→own (ms) | ratio |
|---|---|---:|---|---:|
| L07 church | 0.075→0.074 | 0.987× | 0.075→0.073 | 0.973× |
| L07 strchain | 1.129→1.072 | **0.950×** | 1.143→1.074 | 0.940× |
| L07 global | 1.773→1.655 | **0.933×** | 1.759→1.671 | 0.950× |
| L07 natadd | 0.221→0.209 | 0.946× | 0.227→0.212 | 0.934× |
| L08 church（对照） | 0.072→0.072 | 1.000× | 0.073→0.073 | 1.000× |
| L08 strchain（对照） | 0.598→0.587 | 0.982× | 0.593→0.592 | 0.998× |
| L08 global（对照） | 1.319→1.339 | 1.015× | 1.322→1.335 | 1.010× |
| L08 natadd（对照） | 0.204→0.204 | 1.000× | 0.213→0.214 | 1.005× |

判读：L07 twin 小项全面持平或略好（无 >5% 回归；无需解释项）；L08 未改，比值在噪声内，
证明本轮只影响 L07 twin。**注意**：绝对 ms 是 k=9/本窗口口径，不与历史矩阵直接比。

## 7. 风险

1. **η 边界**：只对整值 η，链装配函数部分不 η；若未来新增 quote 消费点（例如新 eliminator）
   把 partial builtin 放在链装配位置，需按 reference `quote_sp` 的结构语义复核。
2. **只读 Prim 面**：仍存在 `Tm::Prim`/`XCell::Prim` 的转换代码（不可达）；未删是为控制
   rename/quote/export/unify 的改动面。建议 L08 同批删除并让 parity 兜底。
3. **内存**：`DeclEntryF` 从 2 个 `V`（16B）增至 4 字段（`prim` 16B + `prim_names` 16B，共 48B）；
   decl 条目通常数十~数千，影响可忽略；`Copy` 仍成立。
4. **fuel 剖面**：prim 归约仍按"每次 force 调用烧 1"（与原 `HK_PRIM`/`XCell::Prim`、reference
   一致）；若将来改"只成功才烧"会动 parity/性能口径。
5. `simpl_decl` 拷贝 prim 已显式保留（§2），删除 `prim` 传递会让卡住 match 分支体丢 builtin 归约
   ——任何后续重构须保留该字段。

## 8. L08 移植计划（未做，估计 1–1.5h）

L08 twin（`src/L08_product_type/bump_spine_iter/**`）与 L07 twin 同构（同一套 syntax/eval/force/
prim/quote/machine/subst 分节）；步骤：
1. 同 §2 六文件机械移植（`DeclEntryF` +2 字段、声明处构造补 None、builtin 注册中性头+prim、
   eval Decl prim、force Decl prim 两分支、quote η + QNoEta、simpl_decl 保留字段）；
2. 门禁：L08 lib 60 / blackbox 57+1、51+2 / parity 95 + L07 全套（防跨层回归）；
3. A/B：l08bench fast_ss/fast（church/strchain/global/natadd），预期 L08 twin 也小项持平或略好；
4. 风险与 L07 相同（η/parity/只读 Prim 面），可复用本报告 §3 的两条失败-修复经验。

## 9. 复现

```powershell
git switch feat/twin-primfunc          # worktree C:\ezl-wt-twinprim
$env:CARGO_TARGET_DIR='C:\ezl-target-twinprim'
$env:RUST_MIN_STACK='67108864'
cargo check --all-targets
cargo test --release --lib L07_sum_type
cargo test --release --test l07_blackbox --test l07_blackbox_v2 --test l07_blackbox_v3
cargo test --release --test l07_fast_parity
cargo test --release --test twin_engine_tests
cargo build --release --bin l07bench --bin l08bench
# A/B：base = 6e4a94bd 构建；own = 本分支；--only fast,fast_ss --rounds 3 --max-k 9
```

## 10. 交付/工作树

- 分支 `feat/twin-primfunc`：`77be5d06`（L07 twin）+ 本报告 commit；未 push；工作树除 scratch 外干净。
- 主工作树/其它层/reference：未改。
