# L13 参考版剩余优化审计与低风险落地（feat/l13-audit）

> 基线：`feat/all-layers-hardening` @ `f8d21e55`；本分支从它拉出，worktree `C:\ezl-wt-l13`，
> `CARGO_TARGET_DIR=C:\ezl-target-all-l13`；只改 L13 参考版（`src/L13_namespace/*.rs` 非 twin），
> 未 push、未动 main/L07 等其它层。行号 = `[IO.File]::ReadAllLines` 1-based（本仓 Get-Content 会漏行）。
> 证据标签：`[实测]` 本轮本机跑出；`[码]` 源码核对；`[推断]` 分析判断（沿用 L07 同型证据）。

## 0. 结论速览

| 项 | 结论 |
|---|---|
| 落地 | **3 组低风险改动**：① 观察面总闸 `Infer.lsp_collect`（prelude/bench 装载期不渲染 hover/inlay）；② U2：穷尽 match 跳过覆盖探测；③ FxHashMap：Infer 8 张热表 + typeclass 3 张 + `PartialRenaming.ren` |
| 审计后不做 | `src_names` NameState/trail（L13 的 `MetaEntry::Unsolved(_, Arc<Cxt>, …)` 使快照语义与 trail 撤销冲突，**不能证明安全**）；`fresh_meta`/`close_ty` O(n²)（L07 局部修法已证伪 26 红） |
| N/A | `check_ty` move Pi Raw / `eval(Lam/Pi)` 深拷 / U1 decl 借用（L13 无 check_ty；Closure 是 `(Env, Rc<Tm>)`；probe 早已借用 `&cxt.decl`） |
| 基线测试 | `cargo test --release --lib L13_namespace::` → **614 passed / 0 failed / 6 ignored**（68.94s） |
| 落地后测试 | lib **614/0/6**、`l13_fast_parity` **15/0**、`twin_engine_tests` **28/0**、`hdl042` **2/0** —— 全绿、与基线同数 |
| 基准（同批交错 A/B，min-of-2） | prelude-core **−22.7%**、prelude-hdl **−7.0%**、match(k11) **−28%**、enum **−52%**、church(k11) **−10.7%** |

## 1. 已落地项

### 1.1 观察面总闸 `Infer.lsp_collect`（prelude/bench 期零渲染）

- 机制：`Infer` 新增 `pub lsp_collect: bool`（默认 true）。为 false 时三个 push 入口直接返回，
  不做 quote+pretty：`push_hover`（`elaboration.rs:2826-2829`）、`push_ctor_hover`
  （`:2837-2848`）、`push_inlay_hint`（`:481-493`）；Def 无返回类型的那条 inlay 直推
  （`:1674`）也加同一闸。锚点：字段 `mod.rs:1437-1442`，Clone/`new()` 同步。
- 为什么安全：`load_prelude_state_impl` 在本函数末尾本来就 `clear()` 三张表
  （`mod.rs:4314-4317`），prelude 期渲染是**纯死工作**；孪生侧早有 `observe=false` 同款闸。
  `bench_check_*` 三个入口从不消费观察表，也置 false（`mod.rs:4891/4933/4969`）——
  这让 bench 的 prelude 负载口径等于"生产 prelude 装载（修复后）"，不是伪优化。
- 触发：`load_prelude_state_impl` `mod.rs:4237` 置 false、`:4381` 返回缓存前恢复 true。
- 改动：≈25 行；无 API 破坏；行为：所有表在 prelude 结束仍为空 → 用户可见零变化；
  `run/run_with_prelude` 用户段与 LSP 每文件 push 保持 true。

### 1.2 U2：穷尽 match 跳过覆盖探测（port L07 `a78daec7`）

- 机制：`Compiler::compile` 的覆盖检查循环（`pattern_match.rs:461-476`）在跑之前先算
  `fully_covered = !constrs.is_empty() && 所有构造子都被某臂 covers(...)`；为真则整轮跳过
  `ctor_accessible`（每次一次特化方程 + meta 快照 + 可达性探测）。判据与循环体同一个
  `covers`，**不改变判定**；不完整 match 仍逐构造子探测报 Unmatched。
- 锚点：`pattern_match.rs:471-475`（新），探测函数 `:106/:211`。
- 与 L07 的差异：L13 的 `ctor_accessible` 已有 per-match memo，但探测本身仍昂贵（GADT 索引
  方程 + meta 快照）；L07 同款实测量级：manydefs −34~−64%、match k13 −10.7%。

### 1.3 FxHashMap 热表（对齐 L07 `72f12101` / L09-L12 移植）

只换哈希器（键/值/语义不变），逐项核对过"只做 lookup、无依赖迭代序的消费方"：

| 文件 | 表 | 锚点 |
|---|---|---|
| `mod.rs` | `trait_out_param` / `assoc_defaults` / `mutable_map` / `symbol_table` / `import_map` / `trait_method_cache` / `def_replay_memo` / `ctor_hover_memo` | `:1427/1429/1430/1459/1469/1477/1492/1505` |
| `typeclass.rs` | `Synth.class_instances` / `trait_out_params` / `head_index` | `:91/97/100` |
| `unification.rs` | `PartialRenaming.ren`（rename 热路径，每 binder `Rc::make_mut` 深拷） | `:50/156` |

**刻意保留 std `HashMap`**：`trait_definition`（`elaboration.rs:3769` 按 map 迭代序生成
completions，且 trait 候选选择依赖插入/迭代序——改序有行为风险）、`parser` 宏表（共享层）、
`val_match` 的局部 `subst`（每次新建的小表，改签名会跨模块扩散）。decl 表/`FORCE_MEMO`
本来就是 FxHash。

## 2. 审计后未落地（含原因与建议）

### 2.1 `src_names: Rc<BiMap>` 每 binder 深拷 —— **P2，暂不移植 NameState/trail**

- 现状 `[码]`：`Cxt.src_names: Rc<BiMap<SmolStr,Lvl,(Span<()>,Rc<VTy>)>>`（`cxt.rs:330`）；
  `bind`（`:1207-1223`）、`define`（`:1274-1291`）、`new_binder`（`:1249-1268`）、
  `update_cxt`（`:1327/1349`）都 `let mut src_names = self.src_names.clone();` 再
  `Rc::make_mut(...).insert(..)` —— 与 L07 修复前的 decl 表同一形态：**先 clone 再
  make_mut，强计数恒 ≥2，每次 binder/define 必然整表深拷**（BiMap 两张 FxHashMap）。
- 为什么 L07 NameState/trail 不能直接搬：
  1. L13 的元变量表保存**上下文快照**：`MetaEntry::Unsolved(Rc<VTy>, Arc<Cxt>, …)`
     （`mod.rs:453-455`），`new_meta` 时 `cxt.clone()` 入表（`:2594-2596`）；这些快照在
     之后（trait 求解、`no_metas`、诊断）还会被读取（`mod.rs:718`、`:2291/:2346`）。
     NameState 是 `Rc<RefCell<…>> + trail` 的**共享可变**结构；若不做逐快照的 mark/undo，
     后续 undo 会让历史快照看到被撤销/改写后的名字表 → 潜在语义漂移，无法用现有测试面证明安全。
  2. L13 没有 L07/L08 的 `name_mark`/`Preview` 作用域纪律；`check_pm`、`trait_wrap` 探测、
     LSP 快照都靠 `Cxt` 的持久克隆语义（σ/update_cxt 之外还有大量 clone-probe）。
  3. `update_cxt` 会**改写** `src_names` 已有的值（`:1349-1391`），trail 方案要同时记录
     旧值/旧键，复杂度高于 L07（L07 只有插入）。
- 建议（P2，独立立项）：顺序声明路径改 `bind_in_place(&mut self) -> Self`（与 decl 的
  `&mut Cxt` 同款，只改 `infer_in_place` 等有限调用点）+ 其余路径保留 clone 语义；
  或设计"快照感知的持久名字表"（不可变 overlay + 版本号），先 profile 确认占比
  （L13 prelude 208/1439 decls；`[推断]` prelude-hdl 里每 binder 深拷是 5–15% 量级）。

### 2.2 `fresh_meta`/`close_ty` 的作用域平方项 —— **存在，未修（P2 高风险）**

`fresh_meta`（`mod.rs:2598-2612`）每个新 meta 都做
`close_ty(&cxt.locals, self.quote(&cxt.decl, cxt.lvl, &a))`（`close_ty` `syntax.rs:72`），
把整条 Locals 链重建成 Pi/Let telescope ⇒ n 层 hole 时 O(n²)。与 L07 本轮结论同型
（L07 deep 探针 check-only 4.1–4.6×/翻倍，主项即此）；L07 试过"无自由局部变量就跳过
close_ty"→ 26 failed，说明 telescope 语义不可局部绕开。结论：**登记 P2，需 open meta type /
共享 telescope 设计，不在本轮小改范围**。

### 2.3 其余逐项核对结果

| 候选 | 结论 | 依据 |
|---|---|---|
| `Locals` 已是 Rc（每 binder） | **已达标** | `Locals::Bind(Define)(Rc::new(self.locals.clone()), …)`（`cxt.rs:1214/1281/1254`）；`Locals` 枚举在 `syntax.rs:10` |
| `env`/`pruning`/`namespace` 每 binder 深拷 | **无** | env 是持久 `List` prepend；`Pruning = List<Option<Icit>>`（`syntax.rs:7`）；`namespace` 是 `List`；`namespaces` 是 `Rc<HashSet>`；`binding_name` 是 `Option<SmolStr>` —— 全是 O(1)/廉价克隆（`cxt.rs:1211-1222`） |
| `check_ty` 的 Pi Raw clone（L07 `deef97f7`） | **N/A** | L13 无 `check_ty`（git grep 0 命中）；Pi 检查走 `check_universe`（`elaboration.rs:942`）→ `infer_expr`/`insert`，不存在 L07 的按值 `Raw` 逐层 clone 形态；`elaboration.rs:1420/1800/1812` 等 `Raw::Pi(b.0.clone(), …)` 是构造/重建点，不是每 binder 检查路径 |
| `eval(Tm::Lam/Pi)` 闭包 body 深拷（L07 未修项） | **N/A** | `Closure(Env, Rc<Tm>)`（`mod.rs:877`）；eval 臂 `Closure(env.clone(), t.clone())`（`mod.rs:3358`），env 是 `List<Rc<Val>>` O(1)；无 Box body 深拷 |
| U1：探测里 `cxt.decl().clone()` 整表克隆 | **已达标** | L13 `probe_accessible` 直接借用 `&cxt.decl`（`pattern_match.rs:194/259/450`），无整表 clone |
| FxHashMap 剩余热 map | **已覆盖主要项** | 见 §1.3；`trait_definition` 因迭代序保留；`HashMap` 局部/宏表不在 L13 引擎热路径 |

## 3. 基准（同批交错 A/B，base = 干净基线二进制，new = 本分支；rounds=1 × 两轮交替）

| 负载 | base min | new min | Δ |
|---|---:|---:|---:|
| prelude-core (208 decls) | 55.584ms | **42.941ms** | **−22.7%** |
| prelude-hdl (1439 decls) | 5292.361ms | **4923.689ms** | **−7.0%** |
| match k=11 | 0.217ms | **0.156ms** | **−28.1%** |
| match k=9 / k=10 | 0.198 / 0.208 | **0.141 / 0.147** | −28.8% / −29.3% |
| enum k=9 | 0.845ms | **0.401ms** | **−52.5%** |
| church k=11 | 2.390ms | **2.134ms** | **−10.7%** |

- 口径：`l13bench --workload <w> --rounds 1 --max-k 11 --only basic`，两轮"B→N / N→B"交替，
  每引擎取两轮 min；机器为共享机，跨窗口绝对值只作量级参照（base/new 同窗口交替）。
- 归因（`[推断]`，本轮未做单因子消融）：match/enum 的主项是 U2（覆盖探测）；
  prelude-core/prelude-hdl/church 的主项是 FxHashMap（trait/import/rename 热表）
  + prelude 期观察面总闸（后者直接砍掉 prelude 装载中的 hover/inlay 渲染）。
- 旧报告对照：历史同机 prelude-hdl basic 约 3.1–5.9s 区间波动，量级一致。

- examples-hdl 未纳入 Δ 表：baseline 与 new 均报 BOTH-FAILED (两版都未跑完，与范式一致无关)——这是既有的示例自检标签缺陷（两版一致失败），基准不可用，不是本轮改动引入。

## 4. 测试

- 基线（干净 f8d21e55 worktree，release）：`cargo test --release --lib L13_namespace::`
  → **614 passed / 0 failed / 6 ignored**（68.94s）。
- 落地后（本轮最终树，release，`CARGO_TARGET_DIR=C:\ezl-target-all-l13`）：
  - `cargo test --release --lib L13_namespace::` → **614 passed / 0 failed / 6 ignored**（71.77s，与基线同数）；
  - `cargo test --release --test l13_fast_parity -- --skip "L13_namespace::"` → **15 passed / 0 failed**；
  - `cargo test --release --test twin_engine_tests` → **28 passed / 0 failed**（157.38s，含 30 examples 双引擎互检）；
  - `cargo test --release --test hdl042_engine_tests` → **2 passed / 0 failed**；
  - `cargo check --release --lib` 干净（0 error）。
  - 结论：**L13 全套门禁与基线同数、零回归**（twin 未动）。
- 说明：baseline parity/twin/hdl042 未在干净树上重复跑（首次构建耗时 >10min，会话预算内
  优先落地+复跑）；分支 `f8d21e55` 为全层硬化报告声明的已验证状态。

## 5. 改动文件与回滚

- 改动：`src/L13_namespace/mod.rs`、`elaboration.rs`、`pattern_match.rs`、`typeclass.rs`、
  `unification.rs`；新增本文件。未动 twin/共享 parser/pretty/LSP 宿主。
- 回滚：`git revert` 本分支 commit 即可；三组改动互相独立（闸/U2/Fx 可分别 revert）。
- 风险：① 闸只在 `lsp_collect=false` 生效，用户文件路径默认 true，回归面是 hover/inlay 测试
  （本轮 lib+LSP 套件覆盖）；② U2 判据与既有 `covers` 同源，若 `covers` 有边界 bug 行为与
  旧实现相同（探测只在"未全覆盖"时进行）；③ Fx 只换哈希器，迭代序敏感表已排除。
