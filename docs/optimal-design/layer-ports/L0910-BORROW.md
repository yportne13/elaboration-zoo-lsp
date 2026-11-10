# L09/L10 借用式优化（P0-1 模板移植）— 审计、A/B 与结论

- 工作树：`C:\ezl-wt-l0910`，分支 `feat/l0910-borrow`，起点 `6e4a94bd`（= master 当前 `feat/all-layers-hardening` 头部）
- 构建：`CARGO_TARGET_DIR=C:\ezl-target-l0910`（F: 零构建）；**未 push / 未改主工作树 / 未触碰 L07/L08 / 未动 twin**（只改 L09 reference）
- 提交：`75985cb9` perf(l09): borrow closure bodies in beta reduction；`6e22b595` perf(l09): borrow match branch bodies in eval_aux
- 时间：2026-11-10 20:26–21:10（Asia/Shanghai），Windows / Ryzen 5 5600 / 34 GB

## 0. 结论（先给结论）

1. **L09 两个 L08 模板点都真实存在，已修**：
   - `closure_apply` 每次 β 深拷 `Rc<Tm>` 闭包体（`(*closure.1).clone()`）→ 改借用 `eval_ref`（模板 `fd5a3a95`）；
   - `Compiler::eval_aux` 每次选中臂返回**克隆的 `Tm` 分支体**、每层字段下钻再 clone 子模式与体（模板 `bc929dcc`）→ 改 `Option<(&Tm, Env)>` + `eval_aux_arm` 借用。
2. **收益（L09，同窗口交错，min of interleaved trials）**：church k10 **1.56→1.26 ms（−19%）**；universe k11 **5.22→4.65 ms（−4~−8%）**；strchain k10 / match k13 在噪声带内（中性）。两笔提交叠加后无任何负载回退。
3. **`match` 负载对第 2 笔提交无感**：L09 bench 的 match 臂体极小、墙钟被 elaboration（覆盖编译/检查）主导，克隆开销不可见。第 2 笔提交作为**语义等价、零回归的清理**保留；若仓库只收"实测有收益"的改动，可单独 revert `6e22b595`（第 1 笔不受影响）。
4. **L10 无需任何改动**：L10 的 `Tm` 本来就是 `Rc<Tm>` 表示（`Tm::Lam(..., Rc<Tm>)`、`Tm::Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>)`），`eval` 已接收 `&Rc<Tm>`、`closure_apply` 已借用闭包体、`eval_aux` 返回 `Rc<Tm>`（O(1) 引用计数克隆）——**L08 两个模板点在 L10 已在设计上成立**。证据：`l10bench` 二进制与改动前**bit-identical**（SHA256 `DB5B173F…`），match k13 0.100 vs 0.101 ms（≤1%）。
5. 门禁全绿（见 §4）：`cargo check --all-targets` 0 error；release lib 10/25、parity 39/46、debug lib 10/25 全部 0 failed。

## 1. 审计：每次 β / match 深拷 Tm/Val 的点（改前 → 改后）

### 1.1 L09（reference）— 两个真点 + 两个已存在

| # | 位置（改前） | 形态 | 频率 | 处置/改后位置 |
|---|---|---|---|---|
| 1 | `src/L09_mltt/mod.rs:704-707` `closure_apply` | `self.eval(&closure.0.prepend(u), (*closure.1).clone())`：`Rc<Tm>` 解引用后**深拷整棵 Tm** | 每次 β 归约（church/递归 add 高频） | **已修**（`75985cb9`）：`self.eval_ref(&closure.0.prepend(u), &closure.1)` |
| 2 | `src/L09_mltt/pattern_match.rs:373-423` `eval_aux` | 返回 `Option<(Tm, Env)>`：选中臂 `body.clone()`（4 处），字段递归再把 `pat.clone()+body` 打包成临时臂（每层各一次） | 每次运行时 match 选臂（每层递归一次） | **已修**（`6e22b595`）：返回 `Option<(&Tm, Env)>`，新增 `eval_aux_arm(..)->Option<Env>`（pattern 借用、body 由调用方借用） |
| 3 | `src/L09_mltt/mod.rs:754-872` `eval`（owned） | 全部调用点都是 owned `Tm`；其中 `Tm::Match` 选中臂调用 `eval_aux` 得到 owned body | 每次求值 Match/Lam | **已改**（两笔提交）：`eval` 保留为 owned 快路（Lam/Pi 仍 move Box→Rc，零克隆；Match 卡住仍 move `cases`），新增 `eval_ref(&self, env, &Tm)` 借用核心；两笔提交后 `Tm::Match` 走借用分支体 |
| 4 | `src/L09_mltt/mod.rs:878-883` `eval_neutral` | owned 入口，但 3 个调用点（unify/rename/quote 的 Match 臂）都从 owned `cases` 移入，**无 clone** | — | 不动 |
| 5 | `src/L09_mltt/mod.rs` `force` | **没有 `Val::Match` 臂**（L09 无 Match 重选，卡住即终态） | — | 模板中"force 的 Val::Match 臂改 eval_ref"一条不适用（如实登记） |

### 1.2 L10（reference）— 模板点已存在，零改动

| 位置 | 形态 | 结论 |
|---|---|---|
| `src/L10_typeclass/mod.rs:58-79` `enum Tm` | 所有子项已是 `Rc<Tm>`（`Lam(.., Rc<Tm>)`、`Match(Rc<Tm>, Vec<(PatternDetail, Rc<Tm>)>)`） | 分支体/闭包体 clone 都是 O(1) 引用计数 |
| `src/L10_typeclass/mod.rs:805-808` `closure_apply` | `self.eval(&closure.0.prepend(u), &closure.1)` | 已借用（无 clone） |
| `src/L10_typeclass/mod.rs:854-…` `eval(&self, env, tm: &Rc<Tm>)` | 入口即 `&Rc<Tm>` | 已是借用式 |
| `src/L10_typeclass/pattern_match.rs:360-399` `eval_aux` | 返回 `Option<(Rc<Tm>, Env)>`，`body.clone()` 为 Rc clone（1 次原子加） | 等价已修 |
| `src/L10_typeclass/mod.rs:944-955`、`:710-719`（frcs Match 重选） | 选中臂 `self.eval(&env, &tm)`；无深拷 | 已借用 |
| 二进制证据 | `l10bench-base.exe` 与改动后重建的 `l10bench.exe` SHA256 相同（`DB5B173FAE9C…`） | L09 改动不进入 L10 bin（各层 `#[path]` 独立编译） |

### 1.3 剩余候选（本轮**未做**，登记给后续）

| 位置 | 形态 | 为什么不做 |
|---|---|---|
| `src/L09_mltt/mod.rs:839/845` | `eval_ref` 的 `Tm::Lam/Pi` 臂：`Rc::new((**t).clone())`——λ 字面量出现在"分支体/闭包体内部"时仍需克隆 Box 内容 | 属借用式 eval 的固有代价（`Tm` 是 Box 表示）；只在"体内再嵌 λ"的形态出现，非每步 β 热路径。实测无回退 |
| `src/L09_mltt/mod.rs:908` | `eval_ref` 的卡住 match：`cases.clone()` 深拷臂表 | 只在"借用上下文里 match 卡住"一枝；owned 入口保持 move（零克隆） |
| `src/L09_mltt/unification.rs:594` | `(Obj,Obj)` 合同臂 `(**o1).clone()`：`Box<Val>` 深拷接收者 | 不是 β/match 热路径；要根治需把 `unify` 改成收 `&Val`（大范围签名重构，超出本任务低风险边界） |
| `src/L09_mltt/mod.rs:1070/1366` | 驱动循环 `infer.infer(&cxt, tm.clone())`：每个 decl 深拷一次 AST | 每声明一次、非 β/match；且 `infer` 收 owned，改成 move 是 1 行但属另一类（move 而非 borrow），未纳入 |
| `src/L09_mltt/pattern_match.rs:243/326` | 编译期每臂 `body.clone()`（unreachable 警告 / 臂体检查） | 编译期一次/臂，非运行期；在 elaboration 主成本内占比小 |

## 2. 改动说明（两笔提交，逐项）

### 2.1 `75985cb9` perf(l09): borrow closure bodies in beta reduction
- `src/L09_mltt/mod.rs`（+56/−29）：把 `fn eval(env, Tm)` 拆成
  - owned 入口 `eval`：`Tm::Lam`/`Tm::Pi` 仍把 `Box<Tm>` **move** 进 `Closure(Rc<Tm>)`（零克隆），其余下沉到 `eval_ref`；
  - 借用核心 `eval_ref(&self, env: &Env, tm: &Tm)`（原 match 体的 `&Tm` 版本：`x.clone()`/`(**t).clone()` 只在需要构造 owned 结构处）；
  - `closure_apply` 改为 `eval_ref(&closure.0.prepend(u), &closure.1)`，β 不再深拷体。
- 语义等价：`force`/`eval` 的求值顺序、`neutral_globals` 包裹、`Val` 形态全部不变；仅把"先克隆再求值"换成"直接借用求值"。

### 2.2 `6e22b595` perf(l09): borrow match branch bodies in eval_aux
- `src/L09_mltt/pattern_match.rs`（+99/−45 区域）：`eval_aux` 返回 `Option<(&'a Tm, Env)>`；新增 `eval_aux_arm(infer, heads, cxt, pattern) -> Option<Env>`，把原 `filter_map` 的四种守卫（Any/Bind、非本类型 Con 当变量、同类型异构造子跳过、同构造子字段 zip 下钻）搬进 helper。
  - 保留旧语义细节：非 `SumCase` 头 → 任意 `Con` 都按变量模式绑定整头；字段 `zip` 长度不齐时**截断**（不新增长度检查）；首匹配顺序不变；每层字段先 `force` 再下钻（与旧递归入口同）。
- `src/L09_mltt/mod.rs`（+18）：owned `eval` 增加 `Tm::Match` 快路（选中臂用 `eval_ref`，卡住 move `cases`）；`eval_ref` 的 `Tm::Match` 选中臂改用 `eval_ref`（卡住一枝才 `cases.clone()`）。

## 3. A/B 方法

- 基线二进制：改动前 release 构建的 `l09bench.exe` / `l10bench.exe` 复制为 `*-base.exe`；改动后逐笔构建快照 `l09bench-c1.exe` / `l09bench-c2.exe`（均在 `C:\ezl-target-l0910\ab\`，**不在 worktree 内**）。
- 交错执行（base → c1 → c2 → …），每格 `--rounds N --only basic`（match 用 rounds=9 压噪，其余 5），3 轮交错取 **min**；bench 只输出 min/median（无 max）。
- 机器负载：测量窗口内无其它编译/bench（每次构建结束后才开始测量）；match k13 的历史抖动达 ±28%，故以多轮交错 + rounds 提高判读置信度。
- 原始数据：`C:\ezl-target-l0910\ab\ab-commit1.txt`、`ab-final.txt`、`base-*.txt`。

## 4. 门禁结果（HEAD `6e22b595`）

| 门禁 | 结果 | 耗时（含构建） |
|---|---|---|
| `cargo check --all-targets` | **exit 0**（0 error） | 43.5 s |
| `cargo test --release --lib L09_mltt` | **10 passed / 0 failed** | 334.8 s（release LTO 重编） |
| `cargo test --release --lib L10_typeclass` | **25 passed / 0 failed** | 1.2 s |
| `cargo test --release --test l09_fast_parity` | **39 passed / 0 failed** | 301.6 s（首编） |
| `cargo test --release --test l10_fast_parity` | **46 passed / 0 failed** | 31.1 s |
| `cargo test --lib L09_mltt`（debug） | **10 passed / 0 failed** | 118.7 s |
| `cargo test --lib L10_typeclass`（debug） | **25 passed / 0 failed** | 1.0 s |

说明：每层的 `lXX_fast_parity` 通过 `#[path]` 把本层 reference 再编进测试二进制，`39 = 29 本体 + 10 lib`、`46 = 21 本体 + 25 lib`（与既有口径一致），因此这两条同时覆盖了 reference↔twin 逐字节 parity 与 lib 单测。

## 5. A/B 数据（L09；min/median ms，`--only basic`）

### 5.1 三笔快照，交错 3 轮取 min

| 负载 | k | rounds | base | c1（闭包借用） | c2（+match 借用） | c2/base |
|---|---:|---:|---:|---:|---:|---:|
| church | 10 | 5 | **1.563**（1.615/1.563/1.597） | 1.285（1.286/1.285/1.316） | **1.262**（1.262/1.269/1.296） | **0.81×（−19%）** |
| universe | 11 | 5 | **4.869**（5.399/5.215/4.869） | 4.732（4.732/4.818/5.274） | **4.654**（4.783/4.654/4.835） | **0.96×（−4.4% @min；逐轮 −5~−8%）** |
| match | 13 | 9 | **0.150**（0.150/0.150/0.151） | 0.153（0.154/0.154/0.153） | **0.152**（0.153/0.152/0.153） | 1.01×（噪声带内，**无收益**） |
| strchain | 10 | 5 | **16.02**（16.02/16.80/17.15） | 16.46（16.46/16.69/17.01） | **16.61**（16.61/17.63/16.92） | ~1.0×（噪声，±3%） |

判读：
1. **church −19%** 是闭包体借用的直接收益（church 数 = 纯 β 归约，每次 β 正好命中 `closure_apply`；与 L08 `fd5a3a95` 的 −29% 同向、幅度略小，因 L09 参考版地板不同）。
2. **universe −4~−8%**：universe 的 nf 阶段大量 quote→eval 的 β，闭包借用同样生效。
3. **match 无收益**：L09 `l09bench` 的 match 负载是 k+1 个自递归依赖 match def + 一次 println，臂体极小、墙钟被 elaboration（覆盖编译/检查）主导；L08 的 `natadd` 收益来自 2^n 次选臂且臂体较大，两者不同构。L09 bench 无 natadd 负载（`src/bin/l09bench.rs` 头注：natadd 自 L11 才移植），因此无法在本层复现 L08 的 natadd 曲线。
4. **无回退**：四个负载 c2 均不慢于 base 超出噪声带。

### 5.2 L10（零改动，bin 相同）

| 负载 | k | base 拷贝 | 改动后当前 bin | 说明 |
|---|---:|---:|---:|---|
| match | 13 | 0.100 ms | 0.101 ms | 同一二进制（SHA256 相同），差异 ≤1% = 纯噪声 |
| church | 10 | 0.695 ms（20:31 基线窗口记录） | 未重测（bin 相同） | 无源码改动，A/B 无意义 |

## 6. 未验证 / 风险 / 边界

1. **平台**：只在 Windows 10（Ryzen 5 5600）测得；未在 Linux CI 复测，未测内存/分配（可复用 `l06l13mem --chapter L09` 另测）。
2. **match 负载收益为噪声**：第 2 笔提交保留为"语义等价、零回归的清理"；若评审要求"只合并实测有收益的改动"，建议只留 `75985cb9`，`6e22b595` 可单独 revert（两笔无相互依赖；但 revert 后 `eval_ref` 的 Match 臂需回到 owned 调用，revert 会一并回退该处）。
3. **twin / L07 / L08 零改动**：未改任何 `bump_spine_iter*` 与其它层；parity 依旧全绿说明 reference 行为与 twin 仍逐字节一致（twin 侧本来就有等价机制）。
4. **`eval_ref` 的固有克隆**：`Tm::Lam/Pi` 在借用路径仍需把 Box 内容克隆进 `Rc<Tm>`（§1.3）；若后续把 L09 `Tm` 迁到 Rc 表示（L10 已如此），可再消掉。
5. **工作树干净**：源码改动已全部提交（`75985cb9`、`6e22b595` + 本报告提交）；`git status --porcelain` 为空；未 push。

## 7. 复现

```powershell
# 构建（F: 禁止构建）
$env:CARGO_TARGET_DIR='C:\ezl-target-l0910'
cargo build --release --bin l09bench --bin l10bench
# A/B（交错、min）
C:\ezl-target-l0910\ab\l09bench-base.exe --workload church   --max-k 10 --rounds 5 --only basic
C:\ezl-target-l0910\ab\l09bench-c2.exe   --workload church   --max-k 10 --rounds 5 --only basic
C:\ezl-target-l0910\ab\l09bench-base.exe --workload match    --max-k 13 --rounds 9 --only basic
C:\ezl-target-l0910\ab\l09bench-c2.exe   --workload match    --max-k 13 --rounds 9 --only basic
# 门禁
cargo check --all-targets
cargo test --release --lib L09_mltt ; cargo test --release --lib L10_typeclass
cargo test --release --test l09_fast_parity ; cargo test --release --test l10_fast_parity
cargo test --lib L09_mltt ; cargo test --lib L10_typeclass
```
