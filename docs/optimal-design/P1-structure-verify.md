# P1 结构变更独立验证报告（verifier: analyst-l10 / P1-structure-verifier）

> 验证对象：分支 `p0-p1-baseline-cleanup`（工作树 HEAD `8443586e`，**无新提交**，共享工作树）
> 上 analyst-l12 的 P1 结构改动：删除 `src/bench_head/`、把 `src/bench_pre/` 移到
> `tools/bench_snapshots/L07_pre/`、更新 `src/bin/{l07alloc,l07whoalloc,pmabbench}.rs` 的 `#[path]`。
> 验证方式：**只读**（不改代码、不 git 写、不跑 bench，仅编译/仓内命令 + bin smoke）。
> 构建目录：`CARGO_TARGET_DIR=C:\ezl-target`。时间：2026-11-09 09:02–09:11（本机 5600 6C/12T）。
> 标注：`[实测]` 本次命令/输出；`[码]` 源码/仓库状态；`[推断]` 推断。

## 0. 结论（先给判定）

**PASS（结构改动可验收），附 2 条语义/文档 caveat，无需改代码。**

- 目录搬运完整、无内容污染：15/15 快照文件内容与 `HEAD:src/bench_pre` **逐字节相同**（SHA/`git hash-object` 对比），
  迁移后 3 个 bin 从新路径编译通过；`src/bench_head`、`src/bench_pre` 在磁盘上均不存在。
- 全仓无功能性遗留引用：`bench_head`/`bench_pre` 仅剩注释、历史文档与 `tools/metrics.py` 的**刻意**归档探测表。
- `cargo check --all-targets` **exit 0 / 0 error**；三个受影响 bin 的 release 构建 + smoke（`--help` + 小负载）全部通过。
- **Caveat 1**：`src/bench_head/` 实际**不是"HEAD 快照"**，而是 2026-09 时代的冻结快照（见 §3）——删除它
  在 git 历史中可恢复，但 `l07alloc` 的 `head` 列自此**退化为 `cur` 的重复**（已实测 head≡cur）。
- **Caveat 2**：首次 `cargo check --all-targets` 曾命中 35 个 error，为 l12 收尾窗口内的**中间态**（`#[path]`
  二次包含尝试）；当前稳定态已 0 error，且 l12 已于 09:14 宣布编辑完结（其后仅一处注释收尾，09:15 复核仍绿，见 §5.3）。
  建议 Lead 在合并前再跑一次全量门禁留档。

## 1. 环境、方法与证据链

| 项 | 值 |
|---|---|
| 分支 / HEAD | `p0-p1-baseline-cleanup` / `8443586e`（`git log -1`；工作树 dirty，未提交）|
| 构建 target | `C:\ezl-target`（不写 F:；F: 剩余空间限制）|
| 角色边界 | 只读验证：未改 Rust/文档（本报告除外）、未 `git add/commit`、未跑 bench、未写 lock |
| 关键命令 | `git status/diff/ls-tree/hash-object`、`cargo check --all-targets`、`cargo build --release --bin …`、3 bin `--help`+小负载 |
| 二进制 | 新构建 09:08；`l07alloc/l07whoalloc/pmabbench` release 构建 **28.34s** `[实测]` |

## 2. 检查项与结果（Lead 的 5 条 + 附加项）

| # | 检查项 | 结果 | 证据 |
|---|---|---|---|
| C1 | `src/bench_head` 不存在、`tools/bench_snapshots/L07_pre/L07_sum_type/mod.rs` 存在、`src/bench_pre` 不存在 | ✅ | `Test-Path` 三查：False/True/False；`src/` 下无任何 `bench*` 目录 |
| C2 | 全仓 grep 无遗留引用（Rust/Cargo/脚本） | ✅（注释/历史文档除外，符合约定）| 见 §4 残留清单：仅 `src/bin/*.rs` 注释、快照 README、历史 docs、`tools/metrics.py`（设计上探测归档目录）|
| C3 | `cargo check --all-targets` 0 error | ✅ | 最终稳定态 exit 0，`Finished dev … in 0.80s`；(bin `l07alloc`) 与 (bin `l07alloc` test) 的 warning 均在本次 re-check 中重新出现 ⇒ 目标确实被重新检查 |
| C4 | 受影响 bin smoke | ✅ | `l07alloc --help` exit0；`--sweeps flat` 小负载 exit0；`pmabbench --help` exit0、`--impls l07,l07pre --sweep flat --sizes 4,8` exit0（新路径 L07_pre 可运行）；`l07whoalloc` 默认构建按设计提示"需要 --features sampler"（exit1），`--features sampler` check 通过 |
| C5 | git diff 只含预期文件（无 `src/lib.rs`/`tests/`/L13 源码改动）| ✅ | 非 docs 变更 = 15 staged rename + 13 staged delete + 8 modified（`Cargo.toml`、`ci.yml`、3 bins、3 层 README）+ 7 untracked（P0 他人文件）；无 `src/lib.rs`、无 tracked `tests/`、无 `src/L13_*` 改动 |
| C6 | 删除后编译中确实不再引用 bench_head | ✅ | `grep -r bench_head src tests Cargo.toml tools`：仅 2 处注释（`src/L13_namespace/mod.rs:3835` 为 HEAD 既有注释；`src/bin/l07alloc.rs:95`/`l07whoalloc.rs:42` 为 P1 说明）+ `tools/metrics.py` 归档探测 |
| C7 | 快照内容完整性（附加）| ✅ | 15 个文件中 14 个 `.rs`/README 与 `HEAD:src/bench_pre/**` **hash 完全相同**；仅 `tools/bench_snapshots/L07_pre/README.md` 被有意改写（+说明与再生成步骤）|
| C8 | 快照不参与 lib 构建（附加）| ✅ | `src/lib.rs` 无 bench 引用；`Cargo.toml` 对 `pmabbench/l07alloc/l07whoalloc` 均 `test = false`（`Cargo.toml:105-117`），快照 `tests.rs` 不会被当作 crate 测试 |

## 3. 关键发现：`bench_head` 的真实身份（Caveat 1）

`git log` 与内容对比显示：`src/bench_head/` 是 **2026-09 时代的冻结快照**（最后改动 `bbb673fd` 2026-09-29
"chore: 依赖/死代码/测试卫生清理"；更早 `370fb3f4`），**不是"HEAD 快照"** `[码]`：

- 旧 bin 注释自证其身份：`#[path = "../bench_head/mod.rs"] mod L07_head; --- 已提交的 HEAD（ea01207）`，
  即 σ 重构后（`ad08c63`）某一时点的 L07 拷贝，用于把"重构本身"与"工作区在飞的修复轮"分开。
- 与当前 L07 的漂移量（HEAD blob 对比）`[码]`：`mod.rs` +753/−135、`unification.rs` +572/−129、
  `struct_eq.rs` +335/−149、`pattern_match.rs` +302/−101；`bump_spine_iter.rs` 为 7,616 行单文件
  （当前是 145 行 shim + `bump_spine_iter/` 目录）⇒ 它是重构前/拆分前的旧形态，**并非**当前源码的冗余拷贝。
- 删除的"无损性"：内容仍可从 git 历史恢复（`git show 8443586e:src/bench_head/...`），且 l12 已在
  `l07alloc.rs:95-99`、`l07whoalloc.rs:42-46`、快照根 README 中记录"head 改为别名当前 L07"的决策 `[码]`。

**后果（需登记进 P1 决策记录）**：`l07alloc --hist` / `l07whoalloc --imp head` 的 "head" 列自 P1 起
≡ "cur"（同一模块实例），不再提供"冻结对照"。实测确认：`l07alloc --sweeps flat` 输出
`pre.run/head.run/cur.run = 9630/2354/2354、17637/4209/4209、49970/9838/9838`，**head 与 cur 逐值相同**
`[实测]`。若仍需要"重构本身 vs 工作区"的对照，应改用 `git archive ea01207/b9d54fe` 另建快照并按
快照 README 的再生成步骤（含 `crate::L07_sum_type → crate::L07_pre` 的 sed 修正）加入 `tools/bench_snapshots/`。

## 4. 遗留引用/残留清单（C2 明细，全部非阻塞）

| 位置 | 内容 | 判定 |
|---|---|---|
| `src/bin/l07alloc.rs:4,95-99`；`src/bin/l07whoalloc.rs:42-46`；`src/bin/pmabbench.rs:10` | P1 迁移说明/旧路径历史叙述（注释）| ✅ 允许（说明文字）|
| `tools/bench_snapshots/L07_pre/README.md` | 已改写为新位置 + head 别名说明 + 再生成步骤 | ✅ 有意更新 |
| `tools/bench_snapshots/L07_pre/L07_sum_type/README.md` | 快照自带历史 README，保留 1 处 `src/bench_pre` 表述 | ✅ 历史文档（快照内容"仅移动未改"，符合 l12 声明）|
| `docs/perf-ab-l07l12-2026-09-16.md:104` | 正文仍写"`git archive` 抽到 `src/bench_pre/L07_sum_type/`" | ⚠️ 历史文档可保留，但建议改为新路径或加"（已迁 `tools/bench_snapshots/`）"（行号经 l12 核对为 :104，本报告初稿误记 :101）|
| `tools/metrics.py`（untracked，P0 工具）| 含 `ARCHIVE_DIRS=("bench_head","bench_pre")` 与"moved 候选路径"探测表 | ✅ 设计需要（度量工具判断归档是否移出 `src/`）|
| `src/L13_namespace/mod.rs:3835` | `bench_head 输出——均即时 pretty_tm` 注释 | ✅ HEAD 既有注释，与 P1 无关 |

未发现任何 `#[path]`/`mod`/`Cargo.toml`/CI 对 `src/bench_head`、`src/bench_pre` 的功能性引用。

## 5. 编译门禁与 smoke（C3/C4 细节）

### 5.1 首次 check 的 35 error：中间态，非最终缺陷（Caveat 2）

- 首跑 `cargo check --all-targets`（约 09:03，l12 收尾窗口内）exit 101：**仅** `(bin "l07alloc")` 与
  `(bin "l07alloc" test)` 失败，35 errors；错误形态 = `E0432 unresolved import super::pretty/empty_span`、
  `E0603 module pretty is private / TokenKind is private`、`E0423 private fields`、`E0308 mismatched types`，
  全部指向 `src/bin/../L07_sum_type/**`，且诊断名出现 `L07_head::bump_spine_iter`。
- 该形态与 l12 源码注释自述的失败模式**完全一致**：`l07alloc.rs:98-99` 写"不能用 `#[path]` 二次包含同一份
  源码——L07 源码内部硬编码 `crate::L07_sum_type::...`，二次实例化会漂到兄弟模块实例（E0432/可见性错误）"
  ⇒ `[推断]` 首跑命中的是 l12"先试 `#[path]` 别名、后改 `use` 别名"的中间态（共享工作树并发写窗口）。
- 稳定态复跑（同命令，09:07）**exit 0、0 error**，且日志中重新出现 `(bin "l07alloc")`、`(bin "l07alloc" test)`
  的 warning ⇒ 这两个目标确实被重新检查并通过。
- **建议**：共享工作树的 P1 验证必须在 l12 明确"写完"之后做最终门禁；建议 Lead 在合并前重跑
  `CARGO_TARGET_DIR=C:\ezl-target cargo check --all-targets` 一次留档。

### 5.2 最终门禁与 smoke 结果

| 命令 | 结果 |
|---|---|
| `cargo check --all-targets`（稳定态）| **exit 0 / 0 error**；0.80s（增量）|
| `cargo check --bin l07alloc` / `--bin l07whoalloc` | exit 0 |
| `cargo check --features sampler --bin l07whoalloc` | exit 0（sampler 特性路径也编译）|
| `cargo build --release --bin l07alloc --bin l07whoalloc --bin pmabbench` | **exit 0**，28.34s |
| `l07alloc.exe --help` / `--sweeps flat` | exit 0 / exit 0（head≡cur 已核）|
| `l07whoalloc.exe --help` | exit 1 + 提示"需要 --features sampler"（**设计行为**，非缺陷；按 Lead 授权以特性 check 代替）|
| `pmabbench.exe --help` / `--impls l07,l07pre --sweep flat --sizes 4,8 --rounds 1` | exit 0 / exit 0（**新路径 L07_pre 运行通过**，`l07pre/l07=1.53/1.73`）|

### 5.3 l12 收尾改动后的复核（09:15，增量）

l12 于本验证之后只做了一处**注释**收尾（`src/bin/l07alloc.rs` 的 `L07_head` 注释补"**head 列自 P1 起不再独立**：
head.run 恒等于 cur.run，`--hist` 的 head/pre 净增桶即 cur/pre；需要历史对照按快照 README 再生成"，
`git diff` 已核仅注释/说明行，无逻辑变更；其余 43 项非 docs 变更集合与 §6 一致）。复核：
`cargo check --bin l07alloc` **exit 0**（0.3s，缓存命中；l12 自验 1.1s 同结论）`[实测]`。
⇒ 收尾改动不影响 PASS 判定；全量 `cargo check --all-targets` 由 Lead 在合并前最终留档。

## 6. 范围核对（C5 明细）与未验证项

- 非 docs 变更：`R`×15（bench_pre→tools 快照，含根 README）、`D`×13（bench_head 全部文件；其中 5 个因
  git 相似度被索引配对为 `bench_head→tools` 的 rename，**内容 hash 已证为 bench_pre 内容，无污染**）、
  `M`×8（`Cargo.toml` 仅注释、`ci.yml` 加 P0 gate step、3 bins、`src/L09_mltt`/`L10_typeclass`/`L11_macro`
  三个 README 少量行）、`??`×7（他人 P0 工具：`tools/metrics.py`、`gate_p0.sh`、`gate_lean_oracle.sh`、
  `run_engine_parity.sh`、`tests/engine_parity_report.rs` 等）。
- `Cargo.toml` 的 P1 相关 diff 仅 1 行注释（pmabbench 快照路径说明），**无 target/dependency 变化**；
  `ci.yml` 的 15 行是 P0 gate/Lean oracle optional step，**不属 P1 结构改动**（留给 Lead/P0 负责人确认）。
- `src/lib.rs`、tracked `tests/`、`src/L13_*` 源码：**零改动** ✅；`.bak` 文件当前 `src/` 下 0 个（若属 P0 指标
  假设之一已满足，但非 P1 动作）。
- **未验证（明确声明）**：未跑任何测试套件（`cargo test`）与 bench；`cargo test --release --test
  engine_parity_report -- --ignored` 按 Lead 指示由他人负责；未验证 `--profile release-profiling` 的
  l07whoalloc 实跑（仅 `--features sampler` check）。

## 7. 给 Lead / l12 的处置建议

1. **接受 P1 结构改动**（编译/路径/内容三面全绿）。无需代码修正；本 verifier 未做任何源码/文档编辑。
2. **补一条决策记录**（P1 报告或 commit message）："删除的 `src/bench_head` 是 2026-09-29 前的冻结快照
   （约 `ea01207` 时代），非当前 HEAD 拷贝；`l07alloc/l07whoalloc` 的 head 列自 P1 起 ≡ cur；原 head↔pre
   A/B 能力改用 git 历史/新建快照恢复。"——避免后续把"head 列"误读为独立对照。
   *（已落地：l12 已在 `l07alloc.rs` 注释与 P1 报告 §2.2/§6 登记该界定与 §3 实测数字。）*
3. **低优先**：把 `docs/perf-ab-l07l12-2026-09-16.md` 的 `src/bench_pre/L07_sum_type/` 更新为新路径（或加迁移备注）。
4. **门禁**：l12 正式收尾后由 Lead 复跑一次 `cargo check --all-targets`（共享工作树的中间态风险见 §5.1）。
5. 若需要，我可再跑一次"重建快照 `git archive ea01207 → tools/bench_snapshots/L07_head/`"的可行性验证
   （需 Lead 批准写 `tools/` 与追加 bin 的 `#[path]`，本次未做）。

## 8. 复现命令附录

```powershell
# 结构
Test-Path src/bench_head; Test-Path src/bench_pre; Test-Path tools/bench_snapshots/L07_pre/L07_sum_type/mod.rs
git ls-tree -r --name-only HEAD src/bench_pre   # 15
git ls-tree -r --name-only HEAD src/bench_head  # 13
# 内容完整性（逐文件比 HEAD:bench_pre 的 blob hash）
git hash-object tools/bench_snapshots/L07_pre/L07_sum_type/<f> ; git rev-parse HEAD:src/bench_pre/L07_sum_type/<f>
# 引用
git grep -n "bench_head\|bench_pre\|bench_snapshots" -- src tests Cargo.toml .github tools
# 门禁（稳定窗口）
$env:CARGO_TARGET_DIR='C:\ezl-target'; cargo check --all-targets; $LASTEXITCODE  # 0
cargo build --release --bin l07alloc --bin l07whoalloc --bin pmabbench       # 28.34s
C:\ezl-target\release\pmabbench.exe --impls l07,l07pre --sweep flat --sizes 4,8 --rounds 1
C:\ezl-target\release\l07alloc.exe --sweeps flat      # head.run == cur.run
```
