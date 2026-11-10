# L12 reference `strchain`/`macro` 性能剖析（2026-11-11）

> 工作树：`C:\ezl-wt-l12prof`，分支 `feat/l12-profile`，基线 master `4357fb07`（已含
> L12 硬化 3 commit + merge）。构建：`CARGO_TARGET_DIR=C:\ezl-target-l12prof`（**F: 未构建**）；
> **未 push**。标记：`[实测]` 本次命令输出；`[码]` 源码核对；`[推断]` 判断。
> 状态：1 个 commit（修复）+ 本分析；次候选（typ_pretty）实测无收益未落地。

## 0. 一页结论

| 问题 | 结论 |
|---|---|
| 最终矩阵 L12 `strchain k10` 146.9→145.2ms、`macro` 148.4→149.7ms 为什么"没有收益"？ | **不是 L12 不吃 decl COW/Fx/name_map，而是 L12 的 LSP 观察表（hover/completion）在顺序 def 路径上钉住了 decl 表的 `Rc`**，使已移植的 `fake_bind_mut`/`decl_mut` 的 `Rc::make_mut` 退化为**每个顶层 def 深拷整张 decl 表**（O(D²)）。同一矩阵里 L11 已带此闸（`collect_observations`），L12 漏了；L07 没有观察表所以其 COW 移植不需要处理。 |
| 修复 | `Infer.collect_observations`（默认 true）+ `set_collect_observations`；6 处 hover/completion push 加闸；`run`/`run_with_prelude`（L12 仅有的非 LSP 全流程入口）关闭收集。commit **`aa60c424`**。 |
| 收益 `[实测]`（l12bench `--only basic`，k10，同窗口 min） | **strchain 144.0 → 25.2–30.9 ms（约 4.7–5.7×）**；**macro 148.1 → 28.0–30.2 ms（约 4.9–5.3×）**。放大：strchain **k13 77.8 s（修复前同机测量）→ 0.323 s**。 |
| 修复后与邻居对比 `[实测]` | L12 已与 **L11 sibling 持平**：strchain k10 30.9 vs 31.2 ms、macro 30.2 vs 28.3 ms。剩余与孪生的差距（strchain k10 ref 25–31ms vs twin `fast_ss` 1.52ms / `fast_run` 3.67ms）是**引擎级**（树/Rc 递归 vs arena/迭代），不是 COW 回归。 |
| 旧记录订正 | 上一轮 "strchain k13 −17.8%" 的两次比较侧**都处于 hover-pinned 状态**（深拷照旧），该数字应视为噪声/不可复现；真正的收益在去掉 pinning 后才显现（k13 78s→0.32s）。 |
| 次候选 | 去掉 Def 臂每 def 一次的 `nf+pretty`（`typ_pretty`，无消费方）：A/B ratio(min) 0.94–1.06（符号混合）⇒ **无收益，不落地**（strchain 的声明类型是 `String`，nf/pretty 本身很便宜）。 |

## 1. 背景与复现

- `docs/optimal-design/PERF-FINAL-2026-11-10.md:41-42`：L12 strchain k10 146.858→145.208 ms
  （0.989×）、macro k10 148.425→149.739（1.009×），而同批 L11 strchain k10 163.7→11.5 ms
  （14.2×）、L08 strchain 123.9→8.0 ms（15.4×）。
- 本机复现（master `4357fb07`，`l12bench --workload strchain/macro --max-k 10 --rounds 3
  --only basic`，load 4%）`[实测]`：
  strchain k9 38.5 / k10 **144.0** ms；macro k9 39.8 / k10 **148.1** ms；natadd k10 0.81 ms。
- 结论：与矩阵一致，确实"没有硬化收益"，且 k9→k10 放大约 3.7×（超线性，提示仍有 O(D²) 项）。

## 2. 根因定位

### 2.1 排除项

- **不是 parse/println**：临时插桩（已 revert）显示 `run` 内 `preprocess+parse` 仅
  **2.1–5.4 ms**（k10，2k defs），infer 循环占大头。
- **不是字符串本身**：`string_concat` 的 O(n²) 字节量在同负载的孪生侧也存在
  （twin `fast_ss` strchain k10 1.52 ms，k13 3.84 ms @k11），远小于参考版差距。
- **不是三件硬化没生效**：`[码]` master 的 `run` 已走 `infer_owned`，`fake_bind_mut`/
  `decl_mut` 就位。问题在于它们**在运行期没能拿到唯一 `Rc`**。

### 2.2 根因链 `[码]` + `[实测]`

1. `elaboration.rs` 的 `infer_expr(Raw::Var)` 在命中局部名/全局 decl 时 push
   `hover_table`，条目第三元是 `cxt.clone_without_src_names()` 即 **Cxt 克隆**；
   每个 `def` 的体至少 2 个 Var（`string_concat` + `s{i-1}`）⇒ 每次批量产生 Cxt 克隆。
2. 这些 `Cxt` 存活在 `Infer.hover_table` 里直到 run 结束，**把 `Rc<Decl>` 强计数钉在 >1**。
3. 于是 `infer_owned` 里的 `cxt.fake_bind_mut(...)` / `cxt.decl_mut(...)`
   调 `Rc::make_mut` 时看到共享 ⇒ **每个顶层 def 深拷贝整张 decl 表**（D 增长时 O(D²)）；
   这正是三件硬化想消除的放大器，只是换了个持有者。
4. 为什么 L11 没事：L11 的硬化 port 已加 `collect_observations` 闸（`L11_macro/mod.rs`
   字段注释明写"hover 条目会 clone Cxt 从而钉住 decl 表的 Rc"），`run` 里
   `set_collect_observations(false)`。L12 的硬化 port 只搬了 COW，**漏搬了该闸**。
   L07 没有 hover 表，故其 COW 移植天然不需要。
5. 插桩验证（临时，已 revert）`[实测]`：加闸后 `hover=0`、`decl_deep_copies=0`；
   修复前每次 Def 的 `make_mut` 都命中共享（即每次深拷，指针见 §4 的 A/B）。

### 2.3 与"旧 k13 −17.8%"的关系（订正）

上一轮 `ALL-LAYERS-HARDENING-2026-11-10.md` 的 L12 strchain k13 −17.8% 是在
**移植前/移植后两侧都 hover-pinned** 的窗口测的（两边深拷行为相同）；该差异应视为
噪声（k13 单发 60–90 s，当时 n=1/2、load 波动大）。真正的修复效果在加闸后才是
O(D²)→O(D) 的质变，见 §4.2。

## 3. 修复（commit `aa60c424`，2 文件 +32/−6）

- `Infer` 新增 `collect_observations: bool`（**默认 `true`**，直接驱动 `Infer`/`Cxt`
  API 的调用方行为不变）与 `pub fn set_collect_observations(&mut self, on: bool)`。
- 6 处 push 全部加闸：`elaboration.rs` 的 Let/check 两处（`:304`、`:1096`）、Var 两处
  （局部名 `:887`、全局 decl `:892`）、completion 两处（`:950` 与 `:1195` 的 trait 候选
  计算也一并跳过——它们只为填 completion 表）。
- `run` 与 `run_with_prelude`（L12 仅有的两个非 LSP 全流程入口；L12 无 LSP 装配）
  在 `Infer::new()` 后调用 `set_collect_observations(false)`。
- 语义：L12 全仓无 `hover_table`/`completion_table` 读点（LSP 只接 L13），
  parity 判据是 `run` 的 Ok 输出/Err 判定，不涉及观察表 ⇒ 门禁不变（§5）。
  若将来 L12 接入 LSP：用 `set_collect_observations(true)` 显式打开，或改造成
  "仅用户文件/按请求"（L13 `lsp_collect` 的形态）。

## 4. A/B 与扩展性（`[实测]`）

### 4.1 k10 A/B（同窗口，`--only basic`；修复前/后各 3 轮；min/median）

| 负载 | 修复前 min/med | 修复后 min/med | ratio(min) |
|---|---:|---:|---:|
| strchain k10 | 144.0 / 144.4 ms | **25.2 / 39.7 ms**（另一窗口 30.9 / 39.2） | ≈0.17–0.21（4.7–5.7×） |
| macro k10 | 148.1 / 149.2 ms | **28.0 / 29.8 ms**（另一窗口 30.2 / 38.9） | ≈0.19–0.20（4.9–5.3×） |
| natadd k10 | 0.81 / 0.84 ms | 0.80 / 0.87 ms | 1.0（不受影响，无 decl 表规模） |

> median 偏高是共享机 load 尖峰（测量窗口 load 4–18%，个别轮 40%+）；min 口径与
> 修复前同窗口对比。**修复后 L12 与 L11 sibling 持平**（同窗口交错：strchain k10
> L11 31.2 / L12 30.9 ms；macro k10 L11 28.3 / L12 30.2 ms）。

### 4.2 修复后扩展性（k9→k13，min）

| 负载 | k9 | k10 | k11 | k12 | k13 |
|---|---:|---:|---:|---:|---:|
| strchain basic | 10.5 ms | 34.0 ms | 69.8 ms | 157.8 ms | **322.7 ms** |
| macro basic | 12.7 ms | 34.1 ms | 76.3 ms | 160.8 ms | **334.3 ms** |

- 修复前同机 k13（上一轮，pre-gate）= **77.8 s**（n=2 min）⇒ 修复后 **0.323 s**，
  约 **240×**；k10–k13 的每翻倍增长 2.0–3.2×（字符串字节 O(n²) + 每 def 常数），
  不再有 8–70× 的深拷放大。
- 与孪生对照（同窗口）：strchain k10 `fast_ss` 1.52 ms / `fast_run` 3.67 ms；
  macro `fast_ss` 2.00 / `fast_run` 5.48 ms。参考版剩余 ~7–17× 差距是引擎级的
  （Rc 树 + 递归 quote/eval vs bump + 迭代内核），非本轮可低风险消除。

## 5. 门禁

| 命令 | 结果 |
|---|---|
| `cargo check --all-targets` | **EXIT=0，0 error** |
| `cargo test --release --lib L12_canonical` | **35 passed / 0 failed**（同基线计数） |
| `cargo test --release --test l12_fast_parity` | **50 passed / 0 failed**（Ok 逐字节 / Err 判定） |
| `cargo test --release --lib`（全量） | **994 passed / 0 failed / 6 ignored**（66.4 s；含 L07–L13 全部层与 L11/L13 套件 ⇒ L11/L13 未受影响） |
| L11/L13 影响 | **无代码依赖**：`git grep L12_canonical src/L11_macro src/L13_namespace` 仅 L13 README 一处文档提及；本 commit 仅改 2 个 L12 文件，全量 lib 测试覆盖。 |

### 5.1 全量 lib 结果

`cargo test --release --lib`：**994 passed / 0 failed / 6 ignored**（`gate-lib-full.txt`），
其中包含 L07–L13 各层单测与 L11/L13 相关套件；总耗时 66.4 s。四条门禁合计 648 s
（`gates.txt`）。

## 6. 为什么这解释了矩阵的"无收益"

矩阵的 before/after 两侧都在 **hover-pinned** 状态：before（master 之前）已含 L12
硬化 3 commit 但未加闸，after（4357fb07）同样未加闸 ⇒ 两侧每 def 仍深拷整表，
`146.9→145.2` 只剩噪声。加闸后 strchain k10 145→25–31 ms、macro 148→28–30 ms；
k 越大差距越大（k13 78s→0.32s）。**建议矩阵在含本 commit 的 master 上重跑 L12
strchain/macro 两格**，并把旧的 "k13 −17.8%" 记录替换为本结果。

## 7. 未做/限制

- 未做更激进优化：**Decl 条目瘦身**（5 元组 → `{ty, val}`）会动 `Decl` 类型/API，
  不属于低风险项；**参考版平铺 decl 表**（`Rc<RefCell<..>>`）会失持久快照语义。
- `typ_pretty` 的 `nf+pretty` 已实测无收益（§0 次候选），未落地。
- 参考版 vs 孪生的引擎级差距（arena/迭代）不在本任务范围。
- 未改动 L07/L11/L13/主工作树；未 push；工作树在交付时保持干净（临时插桩已 revert）。
- 未做 LSP 侧验证（L12 无 LSP 装配；`run` 的观察表本就无消费者）。

## 8. 复现

```powershell
cd C:\ezl-wt-l12prof
$env:CARGO_TARGET_DIR='C:\ezl-target-l12prof'
cargo build --release --bin l12bench
C:\ezl-target-l12prof\release\l12bench.exe --workload strchain --max-k 10 --rounds 3 --only basic
C:\ezl-target-l12prof\release\l12bench.exe --workload macro    --max-k 10 --rounds 3 --only basic
C:\ezl-target-l12prof\release\l12bench.exe --workload strchain --max-k 13 --rounds 2 --only basic
# 门禁
cargo check --all-targets
cargo test --release --lib L12_canonical
cargo test --release --test l12_fast_parity
cargo test --release --lib
```

原始输出：`C:\ezl-target-l12prof\{rep-*.txt, fix-*.txt, final-*.txt, scale-*.txt, gate-*.txt}`
与 A/B 脚本 `C:\ezl-target-l12prof\{cmp-l11l12.ps1, ab\typ-ab.ps1}`。
