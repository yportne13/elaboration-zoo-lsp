# P1 文档归档报告（docs/review-* → docs/archive/）

> 分支 `p0-p1-baseline-cleanup`（共享工作树，**未 commit/push**）· 时点 2026-11-09
> 角色：docs 归档与链接修复 · 只改 `.md`（含 `README*.md`），**未改任何 `.rs`/`Cargo.toml`/CI**
> 验证口径：只读静态检查（`git status`/`grep`），未运行 cargo。

## 1. 目标与完成状态

| 任务项 | 状态 | 证据 |
|---|---|---|
| 7 个 `docs/review-*` 目录 `git mv` → `docs/archive/review-*` | ✅ 7 目录 / **105 文件** | `git status --porcelain` 中 `R`/`RM` 项；`docs/archive/README.md` §目录清单 |
| 新建 `docs/archive/README.md`（归档规则 + 目录清单 + 迁移记录） | ✅ | 新文件 |
| 修复仓库内旧路径引用（重点 `docs/**`、`docs/optimal-design/`、`docs/compare-l07-l13/`、`README*.md`） | ✅ **47 文件 / 103 处** | §3 统计、§4 验证 |
| 检查 `docs/archive/` 内是否还有指向旧位置的路径 | ✅ 已统一改为 `docs/archive/...`；内部相对 sibling 链接保持原样（整树移动后仍成立） | §4 |
| 本报告 | ✅ | 本文件 |

## 2. 移动清单

| 原路径 | 新路径 | 文件数 |
|---|---|---:|
| `docs/review-2026-10-11/` | `docs/archive/review-2026-10-11/` | 11 |
| `docs/review-cont/` | `docs/archive/review-cont/` | 18 |
| `docs/review-continuity/` | `docs/archive/review-continuity/` | 16 |
| `docs/review-l01l12/` | `docs/archive/review-l01l12/` | 23 |
| `docs/review-l07-hardening-2026-11-08/` | `docs/archive/review-l07-hardening-2026-11-08/` | 4 |
| `docs/review-l07l12/` | `docs/archive/review-l07l12/` | 11 |
| `docs/review-l13/` | `docs/archive/review-l13/` | 22 |
| **合计** | | **105** |

- 使用 `git mv`（目录级），git 可识别为 rename，历史可追溯；`docs/archive/` 先建后迁。
- 归档规则写入 `docs/archive/README.md`：只读历史评审、不再更新；新评审写到
  `docs/optimal-design/` 或仓库级当前评审目录；该轮结束后再整体迁入 archive。
- ⚠️ 共享工作树中另有并行 P1 任务（`src/bench_head`+`src/bench_pre` → `tools/bench_snapshots/`、
  删 `.bak`、合并 bin、改 `Cargo.toml`/`.github/workflows/ci.yml`）在同一工作树进行；
  `git status` 里非 `.md` 的改动**不是本任务产生的**（见 §5）。

## 3. 引用修复统计

方法：`grep -rn "docs/review-" --include=*.md` 的全仓等价扫描（正则枚举 7 个具体目录名，
并加 `(?![a-z0-9])` 防止 `review-cont` 误匹配 `review-continuity`），对命中文件做
**机械字符串替换**（只动路径，不动任何叙述文字）：

- 绝对路径：`docs/review-<name>` → `docs/archive/review-<name>`；
- 相对路径：`../review-<name>` → `../archive/review-<name>`（仅限 `docs/archive/` 之外；
  archive 内部的 `../review-<name>` 指向 sibling，整树移动后仍成立，**不改写**）；
- 模板/通配写法（如 `rNN-*.md`、`a<N>-r<R>.md`）保留原样，只修前缀。

| 区域 | 文件数 | 替换处数 | 说明 |
|---|---:|---:|---|
| `docs/archive/review-*/**`（归档内部交叉引用/自引用） | 33 | 83 绝对 | 按任务第 4 项统一改指新位置；sibling 相对链接未动 |
| `docs/**` 其他（不含 archive） | 11 | 14 绝对 | `compare-l07-l13/{FINAL,L09,L13}.md`、`compare-l07-vs-dpm/{L07-RISKS,PR-l07-hardening}.md`、`optimal-design/{D7-architecture,FINAL-OPTIMAL-DESIGN}.md`、`l13-parallel-test-uaf-2026-09.md`、`perf-ab-l07l12-2026-09-16.md`、`perf-l01/01-hotpath.md`、`perf-l01-optimization-2026-10-06.md` |
| `src/**/README.md` | 3 | 5 绝对 | `L09_mltt` 2、`L10_typeclass` 1、`L11_macro` 2（按任务"可编辑 README*.md"授权；未动任何 `.rs`） |
| 相对路径 `../review-*`（archive 外） | 1 | 1 相对 | `docs/compare-l07-vs-dpm/L07-RISKS.md`：`../review-l07-hardening-…` → `../archive/review-l07-hardening-…` |
| **合计（本人写入）** | **47** | **103**（102 绝对 + 1 相对） | |

另：`tools/bench_snapshots/L07_pre/README.md`（由并行 P1 任务从 `src/bench_pre/` 迁出）中的
1 处旧引用已由该任务自行改为 `docs/archive/review-l07l12`——本任务未重复触碰 `tools/`。

## 4. 验证（移动+修复后）

1. **旧绝对路径 = 0**：全仓 `*.md`（排除 `target/`、`.git/`、`.workbuddy/`、`node_modules/`）
   中 `docs/review-<7 目录名>` **0 命中**（唯一的 1 处历史遗留已由 tools README 的并行修改消除）。
2. **旧相对路径 = 0**：archive 之外 `../review-<7 名>` **0 命中**；archive 内部无 `../review-*`
   （迁移前也不存在）。
3. **新链接可解析**：抽取 `docs/archive/review-<7>/xxx.md` 形式的**具体**链接 72 条逐一
   `Test-Path`，71 条存在；唯一"缺失"是归档文档里的模板写法 `review-cont/a1-r1..r3.md`
   （省略号缩写，非链接，属原文风格）。9 条 `a<N>-…`/`rNN-*.md` 通配同理不计。
4. **无误改写**：无 `docs/archive/docs/archive`、`archive/archive` 类双前缀；`review-cont`
   与 `review-continuity` 未被互相误改；`docs/review-2026-09-29.md`（是**文件**、不在本次
   7 个目录内）保持原样。
5. **移动本身**：`docs/archive/` 下 7 目录文件数 11/18/16/23/4/11/22 = 105，与原目录一致。

复核命令（供 Lead 一键验证）：

```powershell
git status --porcelain | Select-String '^R'                  # rename 清单（7 目录 105 文件）
grep -rn "docs/review-" --include=*.md . | grep -v -e /target/ -e P1-docs-archive-report -e docs/archive/README.md
                                                            # 应为 0（.workbuddy 除外）
grep -r "docs/archive/review-" --include=*.md docs | wc -l  # 新路径命中（说明文字会额外计入）
```

> 说明：本报告与 `docs/archive/README.md` 为描述迁移过程，**故意保留**了 `docs/review-` 字样
> （非链接、非引用），严格 grep 校验时请排除这两个文件；其余文档命中数应为 0。

## 5. 未修复项与原因（需要 Lead 决策）

| 位置 | 处数 | 原因 / 建议 |
|---|---:|---|
| `.workbuddy/memory/2026-09-16.md` | 2 | 非 `docs/`，agent 工具记忆目录，按约束未动；如需要一行修 |
| `tools/../review-1011/gen_r02.py`、`lean/Typort/Engine/Budget.lean`、`src/lib.rs`、`src/pmab_gen.rs`、`src/bin/{cli,l11bench,l12bench}.rs`、`src/L07_sum_type/mod.rs`、`src/L12_canonical/mod.rs`、`src/L13_namespace/mod.rs` | 各 1（注释/脚本内路径） | **非 `.md`**（源码/工具注释），按"不碰 src/tests/tools"保留；建议后续由 P1 代码清理统一改注释 |
| `docs/archive/review-l13/a7-probe.py` | 3 | `docs/` 下**非 `.md`**（归档探针脚本的 usage docstring），按 `--include=*.md` 范围外未改；如需改仅 3 行 |
| `target/**` 下同名 md | 多处 | 构建产物/实验副本，忽略 |
| 非路径简写（如 `FINAL(review-continuity) §4`、`review-continuity:60`） | 若干 | 是"复核锚点标签"而非路径，保持原语义不改 |

## 6. 共享工作树注意事项

- 本工作树同时有并行 P1 任务在改：`Cargo.toml`、`.github/workflows/ci.yml`、
  `src/bin/{l07alloc,l07whoalloc,pmabbench}.rs`、`src/bench_head` 删除、`src/bench_pre`→
  `tools/bench_snapshots/` 迁移、`.bak` 删除。这些**不是**本任务改动；合并/复核时请按
  `git status --short` 的路径区分（本任务只有 `.md` 改动 + 7 个目录 rename）。
- `docs/optimal-design/` 与 `docs/compare-l07-l13/` 目前是**未跟踪目录**，本任务对其中的
  `D7-architecture.md`、`FINAL-OPTIMAL-DESIGN.md`、`FINAL.md`、`L09.md`、`L13.md`
  做了链接修复——这些修改不会出现在 `git diff`，但已在工作区生效；若对应负责人随后
  整篇重写，需要重跑一次 `grep -rn "docs/review-" --include=*.md`。
- 本任务未 commit/push；rename 与文档修改均待 Lead 统一提交。

## 7. 交付物清单

1. `docs/archive/`（7 个目录 105 文件，`git mv` 自 `docs/review-*`）；
2. `docs/archive/README.md`（归档规则/清单/迁移记录）；
3. 本报告 `docs/optimal-design/P1-docs-archive-report.md`；
4. 47 个 `.md` 的 103 处路径修复（含 5 个未跟踪文档与 3 个 `src/**/README.md`）。
