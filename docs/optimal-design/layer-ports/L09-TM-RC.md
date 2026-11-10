# L09 Tm Box→Rc：**负结果**（strchain 硬回归，已回退）

- 工作树：`C:\ezl-wt-l09rc2`，分支 `feat/l09-tm-rc`，起点 `a770d9ef`（master：已含上轮 Val Rc `33a08764`）
- **最终状态：`a770d9ef` + 本报告提交；Tm Rc 代码全部回退**（`54406e56` 已 `git reset` 丢弃，未 push；twin export 的 7 行机械适配随之一并撤销）。保留 master 已合并的 **Val Rc**。
- 构建/实验：`CARGO_TARGET_DIR=C:\ezl-target-l09rc2`；Windows / Ryzen 5 5600 / 34 GB；未改主工作树、未改其它层。
- 时间：2026-11-11 01:20–02:45（Asia/Shanghai）

## 0. 结论（先给结论）

1. **Tm Box→Rc 收益真实**：quiet 窗口交错 3 轮 min，`natadd k10` **1.961 → 1.513 ms（−22.8%）**、`church k10` **1.232 → 0.726 ms（−41.1%）**、`match k13` 中性；L09/L10 的 natadd 差距 2.72× → 1.50×。
2. **但 strchain 出现随规模放大的硬回归**（安静窗口、8 轮 × 4 trial 复现，非 load/rebuild）：
   | 负载 | k=9 | k=10 | k=11 |
   |---|---:|---:|---:|
   | base（a770d9ef，Val Rc） | 4.69–4.96 ms | 16.39–17.13 ms | 66.86–69.96 ms |
   | Tm Rc | 5.53–5.65 ms（**+16%**） | 20.22–22.60 ms（**+24%**） | 86.99–88.69 ms（**+27%**） |
   | 比值 | ~1.16× | ~1.24× | ~1.27× |
   ⇒ 回归随问题规模增长（绝对增量 k9≈0.8ms、k10≈4ms、k11≈19ms，近似随总时间同阶放大），**远超 5% 阈值**。
3. **按 Lead 裁决规则：回退整个 Tm Rc commit**（`54406e56` 不在分支历史中），不带着回归合入。Val Rc（上轮已并入 master）不受影响、继续有效。
4. **没有可行的局部修复**（见 §3）：Tm 是单一枚举，无法只为 strchain 保留 Box 热路径；Env/Spine Rc 的另一尝试也是负收益（见 §3.3）。若未来重启 Tm Rc，需先做 alloc/cache 级剖析并把 strchain 一类"长字符串/大工作集"负载纳入门禁。
5. 回退后状态 = 上一轮已验证的 master 点（`a770d9ef`）：门禁复跑全绿（§4）。

## 1. 回归复现（排除 load / rebuild / 单次抖动）

- 方法：同一 target 目录、同一工具链；base 二进制 = `a770d9ef` 构建的 `l09bench-base.exe`（上轮末 Val Rc 状态），当前 = Tm Rc 构建的 `l09bench-Tm.exe`；**同窗口交错**、每格 `--rounds 8 --only basic`、每个 k 4 个交错 trial；测量前确认无其它编译进程（`Get-Process cargo|rustc` = 0~3，均为本会话残留 shell）。
- 原始数据：`C:\ezl-target-l09rc2\ab\strchain-repro.txt`（k9/k10/k11 全量交错）、`ab-Tm2.txt`（k10 首轮清晰窗口）。
- 结论：**k10 稳定 +24%（4/4 trial 一致），k9 +16%、k11 +27%**；church/natadd 同窗口仍显著变快 ⇒ 不是机器负载或构建抖动，且不是"整体变慢"（说明与负载形状相关）。

## 2. 定位：Tm Rc 改了什么、strchain 走了哪条路

`strchain` 的 basic 口径 = 重复调用 `L09_mltt::bench_check_nf(&decls)`（`src/bin/l09bench.rs:277-279`），每次 = 逐 decl `infer.infer`（elaborate：`check_universe` → `fake_bind` → `check` → `eval` → `define_global`）+ 末值 `quote`/`tm_size_ref`。`pattern_match`（无 match）、`eval_neutral`（无卡住 match/rename 分支）、`twin export`（只在跨实现互检时）**都不在 basic 路径上**。

Tm Rc commit 对该路径的全部改动都是**表示层**：

| 改动 | 对 strchain 的运行期影响 |
|---|---|
| `Tm` 子项 `Box<Tm>` → `Rc<Tm>`、`Sum/SumCase/Match` 负载元素 `Rc` | 构造点 `Box::new`→`Rc::new`：分配次数不变，每节点多 16B Rc 头（strong/weak 计数）；`Tm::clone()` 变便宜 |
| `eval`/`eval_ref` 的 Lam/Pi 闭包体改为共享 `Rc<Tm>`（不再 `Rc::new((**t).clone())`） | 更快（少一次深拷），不是变慢来源 |
| `eval_neutral` 收 `&Tm`；`pattern_match.pats/eval_aux` 收 `Rc<Tm>` | **strchain 不执行** |
| twin `export` 机械适配 | **basic 不经过**（仅 parity/互检） |
| `Value`/`Env`/`Spine` | **未改**（Env/Spine Rc 尝试已回退，见 §3.3） |

**没有发现任何新增的 O(n) / O(n²) 工作或"每 def 一次 O(i) 拷贝"**：strchain 的 O(n²) 成本来自"每 def 的值是长度 ≈i 的字符串、eval 时 clone 一次 + concat 复制一次"，这条路径（`eval_ref` 的 Var→global `v.clone()` → Prim `format!`）在 Tm Rc 前后**逐行相同**。

因此回归最可能来自**内存足迹/局部性** [推断，未做 alloc 计数与采样剖析——本机无 perf/alloc 采样设施]：Tm 节点全部 +16B Rc 头，且 `Rc<Tm>` 让项树与 `Closure` 共享、生存期变长；strchain 在大工作集（每 def 保存长字符串值 + 逐 def 的项树）下对 cache/allocator 更敏感，于是表现为"随规模放大的均匀倍率"。这也解释了为什么小工作集的 natadd/church（β 密集、节点小、克隆收益大）显著变快，而 strchain 变慢。

## 3. 尝试过的修复与其它负结果

### 3.1 局部修复（不可行）
- 想给 strchain 热路径保留 owned/Box 形态：`Tm` 是单一枚举，`eval`/`quote`/`elab` 全层统一消费，无法对单负载双表示（除非加第二套类型，等于不做）。
- 想只回退"变慢的改动"：逐项审查后，strchain 路径上**没有单独的"变慢改动"**可摘（Rc 头/共享生存期是表示本身的属性）。
- 因此没有"修复后 <5%"的候选。

### 3.2 收益/代价对比
- 收益：natadd −22.8%、church −41.1%（这两项是任务目标负载）；
- 代价：strchain +24%（k10）/ +27%（k11）——strchain 是 L06 血统的参考版超线性负载（README 明示"参考版超线性"，生产层不用），但它是**现有 bench 门禁负载之一**，硬回归不能带病合入。
- 结论：按"仍 >5% 回归即回退"的裁决，回退。

### 3.3 Env/Spine → `Rc<Val>`（本轮更早的负结果，已回退）
在 Val 仍按值传递、`eval/force` 仍 owned 的前提下单独做 Env/Spine Rc：编译通过、`check --all-targets` 0，但 **natadd +3.4%、church +14%（且抖动大）**。机制：`env.prepend(x)` 需 `Rc::new(x)`，每次入栈多一次堆分配 + 引用计数；L10 能受益是因为 Val 本来即 `Rc<Val>`。**结论：Env/Spine Rc 必须与"Val 全 Rc 签名（`&Rc<Val>` 传递）"同批做才有意义**；单独做是负优化，未提交。

## 4. 门禁（回退后最终状态 = `a770d9ef` + 本报告）

| 门禁 | 结果 | 耗时 |
|---|---|---|
| `cargo check --all-targets` | **exit 0（0 error）** | 14.6 s |
| `cargo test --release --lib L09_mltt` | **10 passed / 0 failed** | 294.3 s（release LTO 重编，含外部负载） |
| `cargo test --release --test l09_fast_parity` | **39 passed / 0 failed** | 390.0 s（首编） |
| `cargo test --release --lib`（全量） | **994 passed / 0 failed / 6 ignored** | 65.5 s |

（本状态与此前 a770d9ef 的验收一致；L10 未改动，其 lib 25 / parity 46 在上一轮同 commit 已验证。）

## 5. 建议（后续）

1. **Tm Rc 若要重启**：先加 alloc/`l06l13mem --chapter L09` 计数与分阶段计时（本次缺 profiling 设施，只能推断）；并把 strchain/长字符串类负载列为必测回归项。
2. 若目标只是继续收窄 natadd：优先"局部借用"（quote/rename/elab 中仍存在的 Tm 克隆点）而不是整体表示迁移；或按 L10 形态**整批**做 Val 全 Rc 签名（`&Rc<Val>`/`Rc<Val>` 传递 + `Env/Spine` Rc）——但需单独立项评估 strchain 类负载。
3. twin：本轮 Tm Rc 的 export 适配随回退一起撤销；最终分支 twin 零改动。

## 6. 复现

```powershell
$env:CARGO_TARGET_DIR='C:\ezl-target-l09rc2'
# 被回退的 Tm Rc 版本二进制仍留档（不参与最终分支）：
#   C:\ezl-target-l09rc2\ab\l09bench-Tm.exe（Tm Rc 状态）
#   C:\ezl-target-l09rc2\ab\l09bench-base.exe（a770d9ef 状态 = 最终）
C:\ezl-target-l09rc2\ab\l09bench-base.exe --workload strchain --max-k 10 --rounds 8 --only basic
C:\ezl-target-l09rc2\ab\l09bench-Tm.exe   --workload strchain --max-k 10 --rounds 8 --only basic
# 交错重复 4 trial；k=9/10/11 同法（原始记录 ab\strchain-repro.txt）
cargo check --all-targets
cargo test --release --lib L09_mltt ; cargo test --release --test l09_fast_parity ; cargo test --release --lib
```
