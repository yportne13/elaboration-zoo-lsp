# P1 基线清理报告：bench 快照整理（bench_head 删除 / bench_pre 迁 tools/）

> 执行：bench 快照整理（原 branch-archaeologist → 本任务角色）。分支 `p0-p1-baseline-cleanup`
> @ `8443586e`，**共享工作树**；按要求 **未 git commit / 未 push**；构建统一
> `CARGO_TARGET_DIR=C:\ezl-target`（F: 盘未写 target）。证据标记：`[码]`=仓库对象核对、
> `[实测]`=本任务命令输出、`[推断]`=判断。

## 0. 一页结论

| 项 | 结果 |
|---|---|
| 删除 `src/bench_head/` | 13 文件，index 中 13×`D`（`git rm -r`） |
| `src/bench_pre/` → `tools/bench_snapshots/L07_pre/` | 15 文件全迁；内容保持（14/15 与 HEAD blob 逐字节同，README 为唯一有意修改） |
| 删除 17 个 `.bak` | 完成，`Get-ChildItem src -Recurse -Filter *.bak` 计数 17→0 |
| 引用修复 | `l07alloc.rs` / `l07whoalloc.rs` / `pmabbench.rs` + `Cargo.toml` 注释 + 迁移目录 README |
| **独立验证**（verifier: analyst-l10） | **PASS**（`docs/optimal-design/P1-structure-verify.md`）：结构/内容/编译/三 bin smoke 全绿；附 2 条语义 caveat（head 列退化为 cur、首跑中间态） |
| `cargo check --all-targets` | **EXIT=0，0 error**（修复后增量 6.61s；首跑含错误 68.3s，见 §2.1） |
| `cargo check --features sampler --bin l07whoalloc` | **EXIT=0**（32s，验证 sampler 门下的别名/路径） |
| 测试/bench | **未跑**（任务只要求 check；且需 Lead 授权 bench 时段） |
| 遗留 | 4 项（§4）：head 列语义、旧路径文档、快照内冻结 README、改动尚未提交 |

## 1. 目录移动与删除（实际 git 状态）

```text
# 1) 建立父目录后整目录 git mv（落到 L07_pre/ 子目录，见 §1.1 的路径一致性说明）
New-Item -ItemType Directory tools/bench_snapshots
git mv src/bench_pre tools/bench_snapshots/L07_pre
# 2) 删除冗余冻结副本
git rm -r --quiet src/bench_head
# 3) 删除未跟踪 .bak（.gitignore 已忽略）
Get-ChildItem src -Recurse -Filter *.bak | Remove-Item -Force
```

`[码]` index/工作区最终状态（`git status --porcelain` 过滤本任务路径）：

- `D` × 13：`src/bench_head/{README.md,bump_spine_iter.rs,cxt.rs,elaboration.rs,mod.rs,parser/{lex,mod,syntax}.rs,pattern_match.rs,pretty.rs,struct_eq.rs,syntax.rs,unification.rs}`；
- `R`/`RM` × 15：`src/bench_pre/**` → `tools/bench_snapshots/L07_pre/**`（**RM 1 个 = 顶层 README，其余 14 个内容不动**）；
- 未暂存编辑 ×5：3 个 bin、`Cargo.toml`、迁移后的顶层 README；
- `git diff --cached --stat` 对本任务路径：**28 files changed, 13,645 deletions**（13 D + 15 R 的汇总口径）。

**内容完整性校验** `[码]`：对 `HEAD:src/bench_pre` 的 15 个 blob 逐一比对新位置文件的
`git hash-object` —— **14 个逐字节相同**，唯一差异是顶层 `README.md`（有意更新路径与说明）。
另：index 里 5 个文件被 git 相似度配对成 `bench_head → tools/...` 的 rename（索引呈现层），
verifier 已用 blob hash 证明内容均来自 bench_pre、**无污染**。
`.bak` 删除明细：`src/L11_macro/**` 14 个 + `src/L12_canonical/**` 3 个 = 17 个。

### 1.1 目标布局与指令字面路径的偏差（已按后者收敛）

任务 step 1 写 `git mv src/bench_pre tools/bench_snapshots`，step 2 给出的引用路径却是
`tools/bench_snapshots/L07_pre/L07_sum_type/mod.rs`（背景同句也写"移到 tools/bench_snapshots/L07_pre/"）。
两者不能同时字面成立。本任务按 **step 2 的显式路径 + 背景意图**落地为
`tools/bench_snapshots/L07_pre/{README.md, L07_sum_type/...}`（一次 `git mv` 到 `L07_pre` 子目录，
等价且无临时中间态）。`[推断]` 这符合 Lead 想保留 "L07_pre" 命名的意图；若坚持 step 1 字面布局，
改动仅需挪一层目录 + 改三条 `#[path]`，可在复核时 5 分钟内调整。

## 2. 引用修复明细

| # | 文件:行 | 修复前 | 修复后 |
|---:|---|---|---|
| 1 | `src/bin/l07alloc.rs:92` | `#[path = "../bench_pre/L07_sum_type/mod.rs"] mod L07_pre;` | `#[path = "../../tools/bench_snapshots/L07_pre/L07_sum_type/mod.rs"]` |
| 2 | `src/bin/l07alloc.rs:95-98` | `#[path = "../bench_head/mod.rs"] mod L07_head;` | `use crate::L07_sum_type as L07_head;`（+ P1 说明注释） |
| 3 | `src/bin/l07whoalloc.rs:42-44` | `#[cfg(feature="sampler")] #[path = "../bench_head/mod.rs"] mod L07_head;` | `#[cfg(feature="sampler")] pub(crate) use crate::L07_sum_type as L07_head;` |
| 4 | `src/bin/l07whoalloc.rs:50` | `#[path = "../bench_pre/L07_sum_type/mod.rs"]` | `#[path = "../../tools/bench_snapshots/L07_pre/L07_sum_type/mod.rs"]` |
| 5 | `src/bin/pmabbench.rs:47` | `#[path = "../bench_pre/L07_sum_type/mod.rs"]` | `#[path = "../../tools/bench_snapshots/L07_pre/L07_sum_type/mod.rs"]` |
| 6 | `Cargo.toml:99-101` | 注释 "（L07 + bench_pre/L07 + L09）" | "（L07 + tools/bench_snapshots/L07_pre + L09；快照自 P1 清理起移出 src/）" |
| 7 | `tools/bench_snapshots/L07_pre/README.md` | 旧 `src/bench_pre` 路径、"只被 pmabbench 引用" | 新路径（L07_pre）、3 个引用 bin、P1 迁移/bench_head 删除说明；**快照内容（`L07_sum_type/` 内）一字未改** |

同时更新了 `l07alloc.rs:3-4` 与 `pmabbench.rs:8-11` 的文件头路径描述、`l07whoalloc.rs:147`
的符号前缀注释（`L07_head` → 实际符号落在 `L07_sum_type`）。

### 2.1 为什么没有按建议二次 `#[path]`：首跑失败的证据

按 Lead 建议先实现为 `#[path = "../L07_sum_type/mod.rs"] mod L07_head;`，`cargo check --all-targets`
**失败（EXIT=101，68.3s）**：36 条 `error` 行 / l07alloc 目标 35 个错误，码型分布 `[实测]`：

| 错误码 | 次数 | 代表位置 |
|---|---:|---|
| `E0603` enum import `TokenKind` is private | 13 | `bump_spine_iter` 各子模块宏展开点 |
| `E0308` mismatched types | 13 | 同上（兄弟模块实例的不同类型） |
| `E0432` unresolved import `super::empty_span` / `super::pretty` | 3+2 | `L07_head::bump_spine_iter/{compiler,entry,machine}.rs` |
| `E0423` 私有字段 tuple struct | 2 | `L07_head::...entry.rs`（`Ix`/`MetaVar` 来自兄弟实例） |

根因 `[码]`：当前 L07 源码**不是可重命名自包含模块**——`src/L07_sum_type/mod.rs:195` 起宏体硬编码
`$crate::L07_sum_type::parser::TokenKind`，`bump_spine_iter.rs:117-119` 亦硬编码
`use crate::L07_sum_type::{parser, pretty, ...}`；大量项是 `pub(super)`/私有。二次实例化后
`crate::L07_sum_type` 指向兄弟实例、`super::pretty` 在该实例下不存在 ⇒ 可见性/类型全断。
**改法**：模块别名（`use ... as L07_head`），不产生第二实例；call site 不变
（l07alloc `L07_head::run` 1 处、whoalloc `--imp head` 1 处），完全符合"模块别名可保留/改名并改代码引用"的授权。

### 2.2 "语义等价"的偏差（必须上报）

`[码]` `src/bench_head/` **不是当前 HEAD 的 L07 副本**，甚至不对应可达历史中任何 L07 版本：

- 文件集：bench_head 13 文件 vs 当前 `src/L07_sum_type` 27 文件（无 `tests.rs` 2,354 行、无
  `bump_spine_iter/` 子模块 17 文件）；
- `git diff --no-index --stat src/bench_head src/L07_sum_type`：**27 files, 13,912 insertions(+), 8,293 deletions(−)**；
- blob 检索：遍历触及 `src/L07_sum_type` 的 **86 个提交**，没有任何提交的 `L07_sum_type/mod.rs`
  blob 等于 `bench_head/mod.rs` 的 blob（`b906d97e…`），也与 bin 注释所称的 `ea01207` 不一致；
- 最后修改是 `bbb673fd`（2026-09-29，"依赖/死代码/测试卫生清理"，给 bench_head/bench_pre README 加冻结注记）。

⇒ 重定向后 `l07alloc`/`l07whoalloc` 的 `head` 列**恒等于 `cur`**（工作树干净时），不再提供历史对照。
这不影响编译与工具可用性（pre/cur 对照仍在），但**丢掉了"重构前 vs 已提交 HEAD"的基线价值**。
verifier 独立实测确认（`l07alloc --sweeps flat`，`pre.run/head.run/cur.run`）：
**9630/2354/2354、17637/4209/4209、49970/9838/9838**——head 与 cur 逐值相同 `[实测 by verifier]`；
并核实 bench_head 是 σ 重构后某时点、**拆分前**的旧形态（`bump_spine_iter.rs` 7,616 行单文件，
当前是 145 行 shim + `bump_spine_iter/` 17 文件目录）。
若仍需该对照：用 `git archive <目标commit> src/L07_sum_type` 重新生成一份冻结快照（放入
`tools/bench_snapshots/` 新目录），否则建议下次删掉 `head` 列/`--imp head`（P2 决策）。

## 3. 构建验证 `[实测]`

环境：cargo 1.98.1；`CARGO_TARGET_DIR=C:\ezl-target`（C: 余量 302 GB；F: 未写 target）。

| 命令 | 结果 |
|---|---|
| `cargo check --all-targets`（第 1 次，二次 `#[path]` 方案） | EXIT=101，35 个错误（§2.1），68.3s |
| `cargo check --all-targets`（别名方案，增量） | **EXIT=0**，`Finished dev profile [unoptimized + debuginfo] target(s) in 6.61s`，**0 error** |
| `cargo check --features sampler --bin l07whoalloc` | **EXIT=0**，32s（cfg(sampler) 分支下别名 + 新路径均验证） |
| `cargo build --release --bin l07alloc --bin l07whoalloc --bin pmabbench`（独立验证） | **EXIT=0**，28.34s `[实测 by verifier]` |
| bin smoke（独立验证） | `l07alloc --help`/`--sweeps flat` exit0（head≡cur）；`pmabbench --impls l07,l07pre --sweep flat --sizes 4,8` exit0（新路径可运行）；`l07whoalloc --help` 无 sampler 时 exit1 并提示"需要 --features sampler"（设计行为） |

独立验证 `[实测 by verifier]`：analyst-l10 的 `docs/optimal-design/P1-structure-verify.md` 判定
**PASS**（C1–C8：结构/内容 hash/无功能性遗留引用/编译/3 bin smoke/范围核对全绿）；其首跑
35 error 与本文 §2.1 记录的中间态一致（共享工作树并发窗口），稳定态 0 error。

告警：`--all-targets` 日志 2,360 行 `^warning:` 级（既有 dead_code/私有性/`non_snake_case` 模块名
与快照自身冻结内容的 unused 告警为主）。**改动点未新增告警类别**：日志中与本任务相关命中仅为
原有的 `mod L07_pre` 非 snake_case 与 snapshot 冻结告警；新别名行无 unused/dead_code 告警。
未运行任何 test/bench（本任务只要求 check；另注意 `l07alloc`/`l07whoalloc`/`pmabbench` 在
`Cargo.toml` 中 `test = false`，语义 smoke 应跑 `cargo run --release --bin l07alloc -- --sweeps flat`，
建议在 Lead 授权的 bench 时段执行）。

**范围确认** `[码]`：未修改 `src/lib.rs`、`tests/`、`docs/review-*`；`git status` 中出现的
`docs/review-* → docs/archive/*` 重命名是共享工作树上其他 agent 的改动，本任务未触碰。

## 4. 残留与后续

1. **`head` 列语义**（§2.2）：现为 `cur` 别名。P2 需二选一：删列/删 `--imp head`（更简洁），
   或从 `ea01207` 等目标 commit 重新冻结一份 snapshot（恢复对照能力）。本任务不擅自扩权。
2. **旧路径文档未改**（超出本任务授权，且多数在 docs/ 他人范围内）：`docs/perf-l07-2026-09-17.md:8/46/48-49/282-283`、
   `docs/perf-ab-l07l12-2026-09-16.md:104`（verifier 报告标 :101，实测 grep 命中 :104，同一段）、`docs/perf-l01-optimization-2026-10-06.md:31`、
   `docs/perf-l02-optimization-2026-10-06.md:274`、`docs/test-catalog.md:400`、`docs/archive/review-*/**`（历史，
   建议不改）、`src/L13_namespace/mod.rs:3835` 注释（源码，未动）。建议 P2 统一替换为
   `tools/bench_snapshots/L07_pre` 或标注"已删（P1）"。
3. **快照内冻结 README**：`tools/bench_snapshots/L07_pre/L07_sum_type/README.md:4` 仍提 `src/bench_head/`
   ——属冻结内容（历史描述），保留；顶层 README 已加说明，避免误改。
4. **未提交**：全部改动在 index/worktree（staged：13 D + 15 R/RM；unstaged：5 处编辑），按指令
   **未 commit/push**，待 Lead 统一提交（本分支可能与其他 P0/P1 改动一起收口）。
5. D6 已登记的 worktree 失效注册（`target/bbwt`）等不属本任务，未处理。

## 5. 可复现命令记录

```powershell
# 预检
git status --porcelain; git branch --show-current   # p0-p1-baseline-cleanup / 8443586e
# 移动/删除
New-Item -ItemType Directory tools/bench_snapshots
git mv src/bench_pre tools/bench_snapshots/L07_pre
git rm -r --quiet src/bench_head
Get-ChildItem src -Recurse -Filter *.bak | Remove-Item -Force
# 校验内容完整性（14/15 blob 相同）
git ls-tree -r HEAD src/bench_pre   # 与 tools/bench_snapshots/L07_pre 逐文件 git hash-object 比对
# 构建（C: target，禁止 F: 构建）
$env:CARGO_TARGET_DIR='C:\ezl-target'; cargo check --all-targets               # EXIT=0
cargo check --features sampler --bin l07whoalloc                              # EXIT=0
```

## 6. 一句话结论

`bench_head` 是 2026-09-29 前冻结的旧形态残片（约 `ea01207` 时代、拆分前，非当前 HEAD 拷贝），
删除不损失可复现性（git 历史可恢复）；`bench_pre` 15 文件完整迁入 `tools/bench_snapshots/L07_pre/`
保住 l07pre 实验；3 个 bin 引用与 Cargo 注释已修，**check 0 error + 独立验证 PASS**；
唯一语义代价是 l07alloc/whoalloc 的 `head` 列自 P1 起 ≡ cur（head↔pre A/B 能力需按快照 README
重建 headline 快照恢复），需 P2 决策删列或重冻基线。

> **决策记录（供 commit message 引用）**：删除的 `src/bench_head` 是 2026-09-29 前的冻结快照
> （约 `ea01207` 时代，σ 重构后/孪生拆分前的旧形态），**不是当前 HEAD 的 L07 拷贝**；
> `l07alloc`/`l07whoalloc` 的 `head` 列自 P1 起恒等于 `cur`；原 head↔pre A/B 能力改用
> git 历史 + 按 `tools/bench_snapshots/L07_pre/README.md` 再生成快照恢复。
