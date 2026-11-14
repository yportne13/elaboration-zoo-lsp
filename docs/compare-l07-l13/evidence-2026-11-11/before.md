# L08/L09 参考版相对 L07 的弱化：可复现证据与性能基线（before）

> 证据采集日期：2026-11-11 23:52 – 2026-11-12 00:35（Asia/Shanghai）
> 采集者：独立证据 agent（worktree `F:/projects/hermes/ezl-gap-evidence`，分支 `evidence/l07-gaps`）
> 主树：`F:/projects/hermes/elaboration-zoo-lsp`（只读，未改 tracked 文件）
> 结论口径：**“实测崩溃/超时”与“静态缺失（源码/编译期）”严格分栏**；未实测的行为不写成实测。

---

## 0. 结论摘要

| # | 缺口 | 分类 | L07 | L08 | L09 |
|---|---|---|---|---|---|
| P11 | 深值 occurs / quote / struct_eq 非迭代 | **实测崩溃** | 1 MB 栈通过（occurs + quote，quote 深度 100001） | 1 MB 栈栈溢出（occurs / quote / struct_eq 三项，exit `-1073741571`） | 1 MB 栈栈溢出（occurs / quote 两项） |
| P5 | 跨 meta 环 force 无环守卫 | **实测 / 静态** | 环守卫命中：fuel 64→62，展开栈清空，43 µs | 无守卫，靠 fuel 烧尽：64→0，102 µs（有界但非环守卫） | force 无 fuel/守卫：1 MB 栈**实测栈溢出** |
| P3 | 三档诊断 `UnifyKind` | **静态缺失 + 编译失败** | 有 `Absurd/Undecided/Fuel` 三档 API（源码 59 处引用） | 无该类型/方法，移植测试 `cargo test` exit 101 | 无该类型/方法，移植测试 `cargo test` exit 101 |
| L09 | 卡住 match 被应用（pending/splice） | **实测 panic** | 通过（值层 pending 应用） | 不适用（L08 已有 pending 字段） | 直接移植 L07 用例**不触发**；改用 outer-binder 变体后 `v_app` panic（mod.rs:731），exit 101 |
| P8 | 宽松 string 合一未检查 spine | **实测行为差异** | 非空 spine → Err + Undecided | 非空 spine → **Ok（静默判等）** | 无 `Val::Decl`；另有 `LiteralType/Prim` 无条件放行（静态） |
| S1 | struct_eq 比较 match pending | **无差异** | 拒绝（can't unify） | 拒绝（can't unify，已比较 pending） | 无 `struct_eq` 模块（静态缺失） |

性能侧（同一合成负载、参考版 `--only basic`）：L09 的 `struct` 负载在 k=13 为 **5452 ms**，L08 为 **76.2 ms**（约 71.6×）；church/enum 也在 1.4–4.1× 区间，match 基本持平。详见 §2。

---

## 1. 方法与版本

### 1.1 版本与环境

| 项 | 值 |
|---|---|
| 主树 HEAD | `0464150c0dd2b018c590ee085543af69d188fe06`（`docs(bench): L07-L13 参考版跨层对比…`，2026-11-11 20:50:16 +08:00） |
| worktree HEAD | 同上 `0464150c0dd2b018c590ee085543af69d188fe06`，分支 `evidence/l07-gaps` |
| 最后一次改动 L07/L08/L09 源码的提交 | `d0fc0935`（2026-11-11 02:18:42 +08:00，`merge: L08 value-layer Rc`） |
| 基准二进制构建时间 | 2026-11-11 05:31:54–05:31:56（晚于最后一次源码提交、早于 docs-only HEAD；按任务约定直接使用，未重编译） |
| 工具链 | cargo 1.98.1 (`797e8a9bc` 2026-08-05) / rustc 1.98.1 (`48a229cea` 2026-09-01) |
| 宿主 | DESKTOP-QRAP4BP，Windows，时区 +08:00 |
| 测试 profile | `[profile.test] opt-level = 2`（debug 构建 + 优化） |

基准二进制（绝对路径 / SHA-256）：

| 二进制 | 大小 | mtime (+08:00) | SHA-256 |
|---|---:|---|---|
| `F:/projects/hermes/elaboration-zoo-lsp/target/release/l07bench.exe` | 1,842,688 | 2026-11-11T05:31:56.211 | `E2C2BC77B18FEB8785D007FC2C35144BE12636D9DE2D1A41AD19DD1CF65EC1F6` |
| `F:/projects/hermes/elaboration-zoo-lsp/target/release/l08bench.exe` | 1,808,896 | 2026-11-11T05:31:55.211 | `A494A29D3AA9849B5C7FA31FE8E672D818E5F4EA5788841CD19287C37CA04A72` |
| `F:/projects/hermes/elaboration-zoo-lsp/target/release/l09bench.exe` | 1,706,496 | 2026-11-11T05:31:54.862 | `546BC79365692935B04CA073FA73EAFBB91D97BD881FA86A92B527C344E5A744` |

> 说明：主树 `git status` 有其它工作流产生的未提交改动，但上述二进制在新于所有 L07–L09 源码提交的时间点构建，且 HEAD 只新增 docs/bench corpus；因此可按“HEAD 构建”使用。

### 1.2 基准命令（逐条原样执行，未重编译）

```powershell
cd F:/projects/hermes/elaboration-zoo-lsp

target/release/l07bench.exe --only basic --workload church   --max-k 13 --rounds 5
target/release/l07bench.exe --only basic --workload match    --max-k 13 --rounds 5
target/release/l07bench.exe --only basic --workload enum     --max-k 13 --rounds 5
target/release/l07bench.exe --only basic --workload strchain --max-k 11 --rounds 3

target/release/l08bench.exe --only basic --workload church   --max-k 13 --rounds 5
target/release/l08bench.exe --only basic --workload match    --max-k 13 --rounds 5
target/release/l08bench.exe --only basic --workload enum     --max-k 13 --rounds 5
target/release/l08bench.exe --only basic --workload struct   --max-k 13 --rounds 5

target/release/l09bench.exe --only basic --workload church   --max-k 13 --rounds 5
target/release/l09bench.exe --only basic --workload match    --max-k 13 --rounds 5
target/release/l09bench.exe --only basic --workload enum     --max-k 13 --rounds 5
target/release/l09bench.exe --only basic --workload struct   --max-k 13 --rounds 5
target/release/l09bench.exe --only basic --workload universe --max-k 13 --rounds 5
```

每条命令的 wall time / exit code / host / 时间戳都记录在原始文件首行（格式：`# cmd: … # wall: …s exit: 0 # host: … <ISO8601>`）。

### 1.3 行为探针命令（worktree 内，debug 构建）

```powershell
cd F:/projects/hermes/ezl-gap-evidence
cargo test --lib --no-run
# 得到 target/debug/deps/elaboration_zoo_lsp-647b90ef7f32ef90.exe

$exe = "target/debug/deps/elaboration_zoo_lsp-647b90ef7f32ef90.exe"
& $exe 'L07_sum_type::gap_evidence::zz_gap_p11_occurs_deep_1mb' --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_stuck_match_under_binder' --exact --nocapture
# …每个探针单独一条命令；栈溢出用例必须单独跑
```

探针代码（全部未提交，仅本 worktree）：

- `src/L07_sum_type/gap_evidence.rs`（新增，`mod.rs` 加 `#[cfg(test)] mod gap_evidence;`）
- `src/L08_product_type/tests.rs` 末尾追加（前缀 `zz_gap_`）
- `src/L09_mltt/gap_tests.rs`（新增，`mod.rs` 加 `#[cfg(test)] mod gap_tests;`）

> 前一 agent 留下的 `tests/gap_behavior.rs` 因 `#[path]` 直编层源码时 `crate::bimap` 无法解析而**从未编译成功**（exit 101，见 `raw-gap-behavior-SUPERSEDED-compile-failure.txt`），本报告未采用其任何输出；该文件已删除。

---

## 2. 性能基线

口径：`basic` 列 = 参考版；每个 k 取 5 轮中的 **min / median（ms）**（strchain 按任务要求 3 轮）；`n=2^k`。加粗不适用，全部为原始数值。

| 负载 | k | n | L07 (min / median) | L08 (min / median) | L09 (min / median) |
|---|---:|---:|---:|---:|---:|
| church | 9 | 1024 | 0.691 / 0.769 | 0.454 / 0.471 | 1.105 / 1.242 |
| church | 10 | 2048 | 1.234 / 1.398 | 0.911 / 1.250 | 2.034 / 2.282 |
| church | 11 | 4096 | 2.423 / 2.825 | 1.824 / 2.103 | 4.234 / 4.788 |
| church | 12 | 8192 | 5.492 / 6.179 | 6.728 / 8.064 | 9.860 / 11.069 |
| church | 13 | 16384 | 10.883 / 13.417 | 13.208 / 14.697 | 13.963 / 15.251 |
| match | 9 | 1024 | 0.095 / 0.150 | 0.079 / 0.143 | 0.147 / 0.149 |
| match | 10 | 2048 | 0.096 / 0.190 | 0.134 / 0.136 | 0.106 / 0.169 |
| match | 11 | 4096 | 0.102 / 0.108 | 0.144 / 0.148 | 0.110 / 0.111 |
| match | 12 | 8192 | 0.112 / 0.193 | 0.145 / 0.158 | 0.121 / 0.122 |
| match | 13 | 16384 | 0.208 / 0.210 | 0.102 / 0.108 | 0.128 / 0.129 |
| enum | 9 | 1024 | 0.168 / 0.175 | 0.259 / 0.281 | 0.689 / 0.701 |
| struct | 9 | 1024 | — | 2.993 / 3.547 | 15.171 / 17.345 |
| struct | 10 | 2048 | — | 7.057 / 7.570 | 56.780 / 58.763 |
| struct | 11 | 4096 | — | 13.777 / 16.576 | 252.618 / 266.095 |
| struct | 12 | 8192 | — | 30.119 / 36.993 | 1256.201 / 1613.687 |
| struct | 13 | 16384 | — | 76.152 / 77.839 | 5452.051 / 5690.779 |
| strchain | 9 | 1024 | 1.879 / 2.096 | — | — |
| strchain | 10 | 2048 | 5.125 / 6.816 | — | — |
| strchain | 11 | 4096 | 15.358 / 15.911 | — | — |
| universe | 9 | 1024 | — | — | 2.236 / 2.767 |
| universe | 10 | 2048 | — | — | 3.340 / 4.083 |
| universe | 11 | 4096 | — | — | 8.691 / 10.043 |
| universe | 12 | 8192 | — | — | 13.563 / 14.839 |
| universe | 13 | 16384 | — | — | 24.155 / 27.106 |

“—” = 该层 bench 未提供/本任务未跑该负载（**不是 0，也不是同功能对照缺失的结论**）；L07 无 struct/universe 负载，L08/L09 未跑 strchain。

### 2.1 读数

- **church**：k=13 时 L07 10.883 / L08 13.208 / L09 13.963 ms（min），L08/L09 相对 L07 约 1.21× / 1.28×；k=9–11 时 L08 反而略快于 L07，交叉点在 k=12。
- **match**：三层都 ≤ 0.21 ms，L09 与 L07 基本持平（0.128 vs 0.208 @k=13），不是弱化点。
- **enum**：L08 0.259、L09 0.689 vs L07 0.168 ms（k=9），L09 约 4.1×。
- **struct**（L08 新增产品类型负载）：k=13 时 L08 76.152 ms、L09 5452.051 ms，**约 71.6×**（median 73.1×）；k=9 时 5.07×。L09 每加一档 k 约 ×3.7–5.0（15.17 → 56.78 → 252.6 → 1256 → 5452），L08 约 ×2.2–2.5/档。
- **strchain / universe**：各自只有一层有负载，仅作该层绝对基线（strchain k=11 15.358 ms；universe k=13 24.155 ms）。

> 注意：三层功能集不同（L08 + 产品类型、L09 + 宇宙），这些数字是“各层参考版在同一合成负载上的绝对耗时”，不能解释为纯实现效率差异；但 struct 上 71.6× 的差距远超功能增量可解释范围，与 §3 的递归/机制缺口方向一致。

### 2.2 原始文件（主树 `.deltawork/evidence/`）

```
before-bench-l07bench-church.txt     before-bench-l08bench-church.txt     before-bench-l09bench-church.txt
before-bench-l07bench-match.txt      before-bench-l08bench-match.txt      before-bench-l09bench-match.txt
before-bench-l07bench-enum.txt       before-bench-l08bench-enum.txt       before-bench-l09bench-enum.txt
before-bench-l07bench-strchain.txt   before-bench-l08bench-struct.txt     before-bench-l09bench-struct.txt
                                                                          before-bench-l09bench-universe.txt
```

---

## 3. 逐项弱化证据

> 分类约定：
> - **实测崩溃**：进程异常终止，记录退出码与 stderr；
> - **实测超时/发散**：线程/进程在限定时间内不返回；
> - **实测行为差异**：正常退出但判定结果与 L07 相反；
> - **静态缺失**：源码中不存在该机制，或用例移植时编译失败（记录 rustc 错误）。
>
> 栈溢出退出码统一为 `-1073741571`（有符号十进制）= `0xC00000FD`（`STATUS_STACK_OVERFLOW`），stderr 含 `thread '<unknown>' (pid) has overflowed its stack`。

### 3.1 P11：深值 occurs / quote / struct_eq 仍是递归（L08/L09 实测崩溃）

**探针**：把 L07 `tests.rs:1913 deep_value_iterative_under_default_stack` 的 helper（`nat_sum` / `succ_of` / `chain`）原样适配到 L08/L09，构造 **100,000 层** `Nat.succ` 链，在 **1 MB 显式栈线程**（`std::thread::Builder::new().stack_size(1<<20)`）内执行；Rc 深链与返回的 Tm 用 `ManuallyDrop` 泄漏（测试基建，避免 Drop 递归污染结论）。每个用例单独进程运行。

命令示例：

```powershell
$exe = "F:/projects/hermes/ezl-gap-evidence/target/debug/deps/elaboration_zoo_lsp-647b90ef7f32ef90.exe"
& $exe 'L08_product_type::tests::zz_gap_p11_quote_deep_1mb' --exact --nocapture
```

| 用例 | L07 | L08 | L09 |
|---|---|---|---|
| occurs（100k 链，`val_mentions_lvl`） | ✅ exit 0，0.22 s | ❌ exit `-1073741571` | ❌ exit `-1073741571` |
| quote（100k 链，`Infer::quote`） | ✅ exit 0，depth=100001，0.18 s | ❌ exit `-1073741571` | ❌ exit `-1073741571` |
| struct_eq（100k 同构链，`struct_eq::val_eq`） | ✅ 迭代化（源码 + L07 既有测试覆盖；本次未单独跑 100k） | ❌ exit `-1073741571` | 无该模块（静态） |

L07 实测输出（`raw-gap-l07-p11-occurs.txt` / `raw-gap-l07-p11-quote.txt`）：

```
[L07 zz_gap_p11_occurs] 100k 不含 Lvl(1)=true; 50k 含 Rigid(7)=true; 50k 不含 Lvl(1)=true
test result: ok. 1 passed; 0 failed; ... finished in 0.22s

[L07 zz_gap_p11_quote] quote 100k 深度 = 100001（期望 100001）
test result: ok. 1 passed; 0 failed; ... finished in 0.18s
```

L08/L09 实测输出（`raw-gap-l08-p11-*.txt`、`raw-gap-l09-p11-*.txt`）：

```
running 1 test

thread '<unknown>' (74884) has overflowed its stack
# exit: -1073741571
```

（occurs / quote / struct_eq 三份 L08 日志与两份 L09 日志内容同型，仅 PID 不同。）

**静态依据**：

- L07：`val_mentions_lvl` 与 `struct_eq::val_eq` 已迭代化（L07 README §7.6；`src/L07_sum_type/mod.rs`、`struct_eq.rs`）；`quote` 走迭代实现。
- L08：`val_mentions_lvl` 递归（`src/L08_product_type/mod.rs:1459-1491`，`Val::SumCase` 臂直接自调用）；`quote` 递归（`mod.rs:1317-1318`，各 `Val` 臂内 `self.quote`）；`struct_eq::val_eq_go` 递归且预算 20,000（`struct_eq.rs:12-24, 111-179`）。
- L09：`val_mentions_lvl` 递归（`src/L09_mltt/mod.rs:357-384`）；`quote` 递归（`mod.rs:942-944` 起，各臂 `self.quote`）；无 `struct_eq` 模块（目录内无该文件）。

**结论**：P11 在 L08/L09 未迁移，**1 MB 栈下 10 万层深值直接崩溃**；L07 同规模通过。这是本次证据中最硬的崩溃类弱化。

### 3.2 P5：跨 meta 环 force 无环守卫（L08 烧尽 fuel，L09 实测崩溃）

**探针**：移植 L07 `tests.rs:2301 cross_meta_cycle_force_is_bounded`：`m1 := ?m2`、`m2 := ?m1`，`unify_fuel=64`，`force(Flex m1)`；L08/L09 侧用 `std::thread` + `recv_timeout(5s)` 观察，并回传剩余 fuel / 耗时。

命令示例：

```powershell
& $exe 'L08_product_type::tests::zz_gap_p5_cross_meta_cycle' --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_p5_cross_meta_cycle' --exact --nocapture   # 单独跑
```

实测：

| 层 | 结果 | 输出 |
|---|---|---|
| L07 | ✅ 环守卫命中 | `out=Flex(MetaVar(0), []) fuel_left=62 expanding_left=0 elapsed_us=43` |
| L08 | ⚠️ 有界但靠 fuel 烧尽 | `完成 out=Flex(MetaVar(0), []) fuel_left=0 elapsed_us=102` |
| L09 | ❌ 栈溢出 | `thread '<unknown>' (75032) has overflowed its stack`，exit `-1073741571` |

**静态依据**：

- L07：`src/L07_sum_type/mod.rs:618-624, 802-817` 有 `unify_kind` Cell 与 `meta_expanding: RefCell<Vec<MetaVar>>` 展开栈，force 展开前检查重复 meta；返回时弹栈。
- L08：`mod.rs:650-660` 只有 `MetaEntry::Solved(t_solved, _) if burn(&self.unify_fuel)`，无 `meta_expanding`；fuel 耗尽即把值当未解返回——旧“靠耗尽兜底”行为。
- L09：`mod.rs:554-560` `force` 对 `MetaEntry::Solved` **直接** `self.force(self.v_app_sp(...))`，既无环守卫也无 fuel（`unify_fuel` 只用于 `frcs` 精化传播，见 `mod.rs:468-471`）。

**结论**：L08 的差异是“机制降级”（结果正确但烧光预算，可能让后续合一误判 Fuel 失败）；L09 是**实测无限递归 → 栈溢出**。任务要求的“recv_timeout 超时”在 L09 上表现为进程先崩溃（栈溢出不可捕获），已如实记录。

### 3.3 P3：三档诊断（L08/L09 静态缺失，移植用例编译失败）

**静态事实**：

```
Select-String -Path src/<layer>/*.rs -Pattern 'UnifyKind|unify_kind|meta_expanding'
L07_sum_type:  59 处（含 pub(crate) enum UnifyKind { Absurd, Undecided, Fuel }）
L08_product_type: 0 处
L09_mltt:         0 处
```

原始：`raw-gap-p3-static.txt`。L07 定义在 `src/L07_sum_type/mod.rs:511-526`，API 在 `747-761`，调用点遍布 `unification.rs` / `pattern_match.rs`。

**编译失败证据**（临时探针，捕获后已删除）：

L08（`raw-gap-p3-l08-compile.txt`，exit 101）：

```
error[E0432]: unresolved import `elaboration_zoo_lsp::L08_product_type::UnifyKind`
  |  no `UnifyKind` in `L08_product_type`
error[E0599]: no method named `reset_unify_kind` found for struct `elaboration_zoo_lsp::L08_product_type::Infer`
error[E0599]: no method named `unify_kind` found for struct `elaboration_zoo_lsp::L08_product_type::Infer`
error: could not compile `elaboration-zoo-lsp` (test "gap_p3_l08") due to 4 previous errors
```

（另有一条 `E0603: struct Cxt is private`，是探针构造 `Cxt` 的附带错误，不影响“无 UnifyKind”的结论。）

L09（`raw-gap-p3-l09-compile.txt`，exit 101）：

```
error[E0425]: cannot find type `UnifyKind` in this scope
 --> src\L09_mltt\gap_p3_probe.rs:8:13
  |
8 |     let _k: UnifyKind = infer.unify_kind();
  |             ^^^^^^^^^ not found in this scope
  |
help: consider importing this enum
  |
2 + use crate::L07_sum_type::UnifyKind;
error[E0599]: no method named `reset_unify_kind` found for struct `L09_mltt::Infer`
error[E0599]: no method named `unify_kind` found for struct `L09_mltt::Infer`
error: could not compile `elaboration-zoo-lsp` (lib test) due to 3 previous errors
```

**后果**：L07 的 `test_unify_kind_separates_absurd_from_undecided`（`tests.rs:282`）以及“预算耗尽 ≠ 结构矛盾”的诊断分档无法移植；L08 源码注释自认“未迁 P3 三档，失败仍按旧口径报‘分支不可达’”（`src/L08_product_type/mod.rs:551-554`）。L09 同样没有该机制。

### 3.4 L09：卡住 match 被应用（直接移植不触发；outer-binder 变体实测 panic）

**探针 A（直接移植 L07 `test_stuck_match_splice`，`tests.rs:983`）**：

```
enum Nat { zero  succ(x: Nat) }
def f(n: Nat): Nat -> Nat =
    match n { case zero => succ  case succ(k) => succ }
println f
println (f zero)
println ((f zero) zero)
```

实测 **exit 0**，没有 panic（`raw-gap-l09-stuck-match.txt`）：

```
> Nat
> f
[L09 zz_gap_stuck_match_splice] OK out="n => (unsolved match n)\nx => Nat::succ(x)\nNat::succ(Nat::zero)\n"
test result: ok. 1 passed; 0 failed; ...
```

原因：该程序里 `f zero` 的 scrutinee 立刻是构造子，match 直接选中分支归约，没有出现“中性 scrutinee 的卡住 Match 再被应用”；`println f` 只把 match 留在 λ 体内打印（`n => (unsolved match n)`）。**因此“直接移植 L07 用例”并不能复现 L09 的 v_app 崩溃，这是一个重要的阴性结果**。

**探针 B（L07 `test_stuck_match_applied_with_outer_binder`，`tests.rs:1009` 的适配，trigger）**：

```
def pick(n: Nat): Nat -> Nat =
    match n { case zero => k => k  case succ(k) => k => succ k }
def test(m: Nat, j: Nat): Nat = (pick m) j
println test
```

实测 **exit 101**，panic（`raw-gap-l09-stuck-match-binder.txt`）：

```
thread '<unnamed>' (73580) panicked at src\L09_mltt\mod.rs:731:18:
impossible apply
  Match(Rigid(Lvl(7), []), [Rigid(Lvl(7), []), Lam("x" @ 30,31, Expl, Closure(.., ...)), ...])
to
  Rigid(Lvl(8), [])
test result: FAILED. 0 passed; 1 failed; ...
```

**对照**：本次实测 L07 两个原用例均 exit 0（`raw-gap-l07-stuck-match-splice.txt`、`raw-gap-l07-stuck-match-binder.txt`）——值层 `Val::Match` 携带 `pending`，应用实参累积、分支选中后应用。L08 也有 `pending` 字段（`mod.rs:217-226`）与 `v_app` 的 Match 臂，同类用例预期通过（未单独跑 L08 此项）。

**静态依据**：L09 `Val::Match(Rc<Val>, Env, Rc<Vec<(PatternDetail, Tm)>>)`（`mod.rs:192`）无 `pending` 字段；`v_app`（`mod.rs:715-731`）只有 `VSub/Lam/Flex/Rigid/Obj` 五臂，其余 `panic!("impossible apply") `；模块头自述“L07 起以值层 splice 实现该特性，L09 是时代缺口”（`mod.rs:3-10`）。

### 3.5 P8：宽松 string 合一未检查 spine（L08 实测静默判等）

**探针**：移植 L07 `tests.rs:2325 loose_string_requires_empty_spine` 的等价值构造：

1. `Val::Decl("Missing", [])` vs `Val::LiteralType`（空 spine，应放行）；
2. `Val::Decl("Missing", [Val::U])` vs `Val::LiteralType`（非空 spine，L07 应 Err + Undecided）。

实测（`raw-gap-l07-p8.txt` / `raw-gap-l08-p8.txt`）：

```
[L07 zz_gap_p8] bare_ok=true applied_err=true kind_undecided=true
[L08 zz_gap_p8] bare_ok=true applied_ok=true（L07: applied_err=true）
```

**L08 把“未知函数被应用”误当成 String 的动态类型并静默判等**；L07 将其记为 `Undecided` 并失败。

**静态依据**：

- L07 `src/L07_sum_type/unification.rs:867-884`：`loose_string(..., sp_is_empty: bool, ...)`，未登记名且 `!sp_is_empty` 时 `note_unify_kind(Undecided)` + `Err`。
- L08 `src/L08_product_type/unification.rs:592-606`：`loose_string(decl, l, cxt, n, spec)` **不接收 spine**，未登记名一律 `Ok(())`；调用臂 `(LiteralType, Decl(n, _)) | (Decl(n, _), LiteralType)`（`780-790`）把 `_` 丢弃。

### 3.6 struct_eq pending 比较（L08 与 L07 一致；L09 静态缺失）

**探针**：L07 `tests.rs:144 test_struct_eq_compares_match_pending_values` 的程序级适配（`bad : Eq[Nat -> Nat] f g = refl f`，其中 f/g 的卡住 match pending 不同）。

实测（L07 对照 `raw-gap-l07-struct-eq-pending.txt`：exit 0，断言通过；L08 `raw-gap-l08-struct-eq-pending.txt`）：

```
[L08 zz_gap_struct_eq_pending] REJECTED err="can't unify Eq[...] == Eq[...]"
```

**结论：本项没有行为差异**——L08 已在 `struct_eq.rs:164-175` 的 `Val::Match` 臂比较 `pending` 值，正确拒绝；与 L07 一致。此前“L08 struct_eq 只比长度”的假设不成立，本报告如实否定。

真正的 struct_eq 弱化在**实现方式**：L08 仍递归（§3.1 实测 100k 链栈溢出），L07 已迭代化。L09 则**没有 struct_eq 模块/val_eq API**（目录无文件，静态缺失），其“卡住 match 相等”只能走 unify 慢路径。

### 3.7 附带静态观察（未做行为探针，仅记录）

- L09 `unification.rs:662-664`：`(LiteralType, Prim) => Ok(())`、`(Prim, LiteralType) => Ok(())` 无条件放行；L07 已把“卡住内建不带实参”修成按 spine 比较 / Undecided（L07 `test_stuck_prim_not_unconditionally_equal`，`tests.rs:1040`）。L09 的 `Val::Prim` 无 spine（`mod.rs:181`），结构上无法区分 `x ++ y` 与 `x ++ z`。**静态推断：同类静默判等在 L09 仍可能存在**，未做端到端复现。
- L08 `force` 的 fuel 是全局 `Cell`，环展开烧尽后会影响同一编译单元后续合一（L07 用 `UnifyKind::Fuel` 把这种“预算失败”与“结构矛盾”分开；L08 未迁）。

---

## 4. 复现说明

### 4.1 环境准备

```powershell
cd F:/projects/hermes/ezl-gap-evidence
git rev-parse HEAD          # 期望 0464150c0dd2b018c590ee085543af69d188fe06
cargo test --lib --no-run   # 首次约 3m20s；增量约 30–50s
```

产物：`target/debug/deps/elaboration_zoo_lsp-647b90ef7f32ef90.exe`（hash 随源码/feature 可能变化，以 `--no-run` 输出为准）。

### 4.2 行为探针（逐条单独运行）

```powershell
$exe = "target/debug/deps/elaboration_zoo_lsp-647b90ef7f32ef90.exe"

# 会通过的对照项
& $exe 'L07_sum_type::gap_evidence::zz_gap_p11_occurs_deep_1mb' --exact --nocapture
& $exe 'L07_sum_type::gap_evidence::zz_gap_p11_quote_deep_1mb'  --exact --nocapture
& $exe 'L07_sum_type::gap_evidence::zz_gap_p5_cross_meta_cycle' --exact --nocapture
& $exe 'L07_sum_type::gap_evidence::zz_gap_p8_loose_string'     --exact --nocapture

# 行为差异 / panic 项（正常进程退出）
& $exe 'L08_product_type::tests::zz_gap_p5_cross_meta_cycle'          --exact --nocapture
& $exe 'L08_product_type::tests::zz_gap_p8_loose_string'              --exact --nocapture
& $exe 'L08_product_type::tests::zz_gap_struct_eq_pending_program'    --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_stuck_match_splice'               --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_stuck_match_under_binder'         --exact --nocapture  # 期望 exit 101 + panic

# 栈溢出项：必须单独跑（abort 整个测试进程）
& $exe 'L08_product_type::tests::zz_gap_p11_occurs_deep_1mb'   --exact --nocapture
& $exe 'L08_product_type::tests::zz_gap_p11_quote_deep_1mb'    --exact --nocapture
& $exe 'L08_product_type::tests::zz_gap_p11_struct_eq_deep_1mb' --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_p11_occurs_deep_1mb'       --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_p11_quote_deep_1mb'        --exact --nocapture
& $exe 'L09_mltt::gap_tests::zz_gap_p5_cross_meta_cycle'       --exact --nocapture
```

期望：前 9 条 exit 0/0/0/0、0/0/0、0、101；后 6 条 exit `-1073741571`。Windows 上若弹出 WER，可忽略/关闭；退出码按 `$LASTEXITCODE` 记录。

### 4.3 基准复现

直接按 §1.2 命令运行主树 release 二进制即可；每条的原始输出已带 command/wall/exit/host 头，便于比对。注意 `l09bench --workload struct --max-k 13 --rounds 5` 单次约 **56.5 s**（k=13 单轮约 5.45 s × 5 轮 + 预热）。

### 4.4 临时改动与清理

本 worktree 当前未提交改动（用于取证，**不要提交**）：

```
M src/L07_sum_type/mod.rs          # + #[cfg(test)] mod gap_evidence;
M src/L08_product_type/tests.rs    # 末尾追加 zz_gap_* 探针
M src/L09_mltt/mod.rs              # + #[cfg(test)] mod gap_tests;
?? src/L07_sum_type/gap_evidence.rs
?? src/L09_mltt/gap_tests.rs
```

清理（保留证据文件即可）：

```powershell
cd F:/projects/hermes/ezl-gap-evidence
git checkout -- src/L07_sum_type/mod.rs src/L08_product_type/tests.rs src/L09_mltt/mod.rs
Remove-Item src/L07_sum_type/gap_evidence.rs, src/L09_mltt/gap_tests.rs
```

P3 编译探针是临时文件，捕获错误后已删除（`tests/gap_p3_l08.rs`、`src/L09_mltt/gap_p3_probe.rs`）；其完整 rustc 输出保存在 `raw-gap-p3-l08-compile.txt` / `raw-gap-p3-l09-compile.txt`。

### 4.5 证据文件索引（主树 `.deltawork/evidence/`）

| 文件 | 内容 |
|---|---|
| `before-bench-l07bench-*.txt` (4) | L07 church/match/enum/strchain 原始输出 |
| `before-bench-l08bench-*.txt` (4) | L08 church/match/enum/struct 原始输出 |
| `before-bench-l09bench-*.txt` (5) | L09 church/match/enum/struct/universe 原始输出 |
| `raw-gap-l07-p11-occurs.txt` / `raw-gap-l07-p11-quote.txt` | L07 P11 对照（exit 0） |
| `raw-gap-l07-p5.txt` / `raw-gap-l07-p8.txt` | L07 P5/P8 对照 |
| `raw-gap-l08-p11-occurs.txt` / `-quote.txt` / `-struct-eq.txt` | L08 P11 栈溢出（exit -1073741571） |
| `raw-gap-l09-p11-occurs.txt` / `-quote.txt` | L09 P11 栈溢出 |
| `raw-gap-l08-p5.txt` / `raw-gap-l08-p8.txt` | L08 P5 烧尽 fuel / P8 静默判等 |
| `raw-gap-l09-p5.txt` | L09 P5 栈溢出 |
| `raw-gap-l09-stuck-match.txt` | 直接移植不触发（exit 0，阴性结果） |
| `raw-gap-l09-stuck-match-binder.txt` | outer-binder 变体 panic（exit 101） |
| `raw-gap-l07-stuck-match-splice.txt` / `raw-gap-l07-stuck-match-binder.txt` | L07 两个 stuck-match 原用例（exit 0 对照） |
| `raw-gap-l07-struct-eq-pending.txt` | L07 struct_eq pending 原用例（exit 0 对照） |
| `raw-gap-l08-struct-eq-pending.txt` | L08 struct_eq pending 拒绝（与 L07 一致） |
| `raw-gap-p3-static.txt` | L07 59 处 vs L08/L09 0 处 |
| `raw-gap-p3-l08-compile.txt` / `raw-gap-p3-l09-compile.txt` | P3 移植编译失败完整输出（exit 101） |
| `raw-gap-behavior-SUPERSEDED-compile-failure.txt` | 前一 agent 失败探针（从未编译成功，未采用） |
