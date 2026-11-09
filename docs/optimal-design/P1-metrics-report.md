# P1 度量工具与基线报告（`tools/metrics.py`）

> 角色：metrics。时点 2026-11-09（基线采集 `2026-11-09T01:19Z` 前后）。
> 快照：**分支 `p0-p1-baseline-cleanup` HEAD `163eb5f2`**（P1 清理提交，2026-11-09 09:17 CST）。
> P1 前对照：`8443586e`（master / P1 前 HEAD）。基线文件：`docs/metrics/baseline-2026-11-09.{json,md}`。
> 约束遵守：只写 `tools/metrics.py` 与 `docs/metrics/`、本报告；**未运行 cargo/bench**；未提交、
> 未 git add。工具 v1.0.0，仅 Python 标准库，已在 **Python 3.6.9（WSL `python3`）与 3.10.4（Windows）** 实跑。

## 0. TL;DR

1. **一个命令复现全仓数字**：`python tools/metrics.py --json OUT.json --md OUT.md`（工作树）
   或 `--git-ref HEAD --compare-ref 8443586e`（可复现快照 + P1 前后对比）。
   `docs/metrics/baseline-2026-11-09.md` 就是该命令生成的（274 行，含口径、逐层表、风险、
   环境开关、Jaccard、P1 对比、CI 门禁说明）；JSON 263 KB 为机器可读版。
2. **P1 前基线（`8443586e`）**：`src/` 362 文件 / 230,242 非空行 / 244,151 物理行；其中层内
   **284 文件 / 185,432 非空行**（参考 82,946 + 孪生 85,411 + 测试 17,075）、bin 7,186、
   glue 12,290、归档 **25,334**（bench_head 12,606 + bench_pre 12,728）。
3. **P1 后基线（`163eb5f2` = 当前 HEAD）**：`src/` **337 文件 / 204,908 非空行 / 217,512 物理行**；
   层内 **185,432 非空行不变**（`compare.layer_only_invariant = true`）；归档从 `src/` 消失，
   其中 **13 个 `.rs` / 12,728 行**移入 `tools/bench_snapshots/L07_pre/`（`src/bench_head` 12 文件
   / 12,606 行按 P1 提交说明删除——它是 2026-09-29 的过期冻结副本、非 HEAD 拷贝），
   **17 个 `.bak` / 12,464 行删除**（P1 提交信息，git 不跟踪故本工具不可重测）。
4. **`--check` 已实现并对接 gate**：`tools/gate_p0.sh` 的 `--help` 探测实测会选中
   `python3 tools/metrics.py --check`（dry-run 输出 `[metrics] DRY-RUN: python3 tools/metrics.py --check`）。
   退出码策略（首轮选择）：**默认 WARN 但 exit 0（advisory，不阻塞 CI）**；`--strict` 时任一 WARN
   exit 1。基线缺失自动回退内置阈值并标注 `baseline=builtin`。校验矩阵见 §5。
5. **与 D3 对账**：层内全部数字（284/185,432/82,946/85,411/17,075、逐层表、L13 24,248/13,304、
   unsafe 317=91+226、prints 663、L13 `.unwrap()` 238 / `.expect(` 197、归档 25,334、bin 7,186、
   glue 12,290、`tests/` 34,963/63 文件/1,363 `#[test]`）**逐项吻合**；不一致集中在 5 项
   （`[[bin]]` 19 vs 22、`test=false` 20 vs 19、`#[path]` 118 vs 208、`src/` `#[test]` 1,114 vs 1,071、
   env 33/28 vs 32/46、Jaccard 抽样值、L13 `panic!` 276 vs 253），逐条归因见 §4。

## 1. 工具接口与口径

### 1.1 CLI

| 参数 | 语义 |
|---|---|
| `--json PATH` / `--md PATH` | 输出机器可读 / Markdown 报告（`-` = stdout）；JSON 排序稳定 |
| `--git-ref REF` | 主快照取 git ref（`git archive` 导出到临时目录扫描；不读工作树） |
| `--compare-current` | 与 `--git-ref` 组合：主快照=ref，另扫工作树做对比 |
| `--compare-ref REF` | 主快照=工作树或 `--git-ref`，对照快照=该 ref（P1 前后对比用） |
| `--test-rule {plural,any}` | 层内测试文件判定：`plural`（默认）= `tests.rs`/`*_tests.rs`（与 D3 一致）；`any` = basename 含 `test` |
| `--check` / `--check-budgets` | CI 度量门禁（见 §5）；后者是旧 gate 的兼容别名 |
| `--strict` | `--check` 下 WARN 时 exit 1（默认 advisory exit 0） |
| `--baseline-json PATH` | `--check` 基线；缺省 `docs/metrics/baseline-2026-11-09.json`，再缺省内置常量 |
| `--deterministic` | 省略时间戳/git 字段，CI 可 `diff` 两次输出 |
| `--no-git` | 跳过 git 子进程（无 git 环境 / 纯静态） |

### 1.2 口径（报告与 JSON 都带 `definitions` 字段）

- **物理行** = `text.splitlines()` 长度；**非空行** = `strip()` 非空（两者都输出，禁止混用）。
- **分类**（`file → kind`）：`ref` = 层目录内非孪生非测试；`twin` = 路径/components 含
  `bump_spine_iter*`；`test` = 层内测试文件（按 `--test-rule`）；`bin` = `src/bin/**`；
  `glue` = `src/` 其余 `.rs`（`src/*.rs`、`src/doc`、`src/format`、`src/sim` 等）；
  `archive` = `src/bench_head|bench_pre`（P1 后为 0）；另单列 `tests/` 目录与 `.bak`。
- **测试规则为什么默认 `plural`**：D3 的 L13“参考生产 24,248 / 测试 13,304”只有把
  `debug_test.rs`（414 非空行）计入参考版才能复现；本工具默认与 D3 对齐，`--test-rule any`
  可切换为“basename 含 test”。两个口径的差 = L13 414 行（见 §4）。
- **`#[cfg(test)]` 生产区近似**：定位文件中**首个** `#[cfg(test)]` 行，其前计入生产区、其后计入测试区；
  文件级测试文件（`*_tests.rs`）整文件计测试区。对“测试模块在文件尾部”的仓内惯例精确，对交错用例保守。
- **计数语义**：`unsafe`（词出现/`unsafe {` 块）、`panic!(...)`/`.unwrap()`/`.expect(`/`todo!`/
  `unreachable!`/print 宏均为**出现次数**（同一行多次也计）；`env::var("…")` 与
  `env::var_os("…")` 去重成名字清单；`#[path]` 计出现次数；`[[bin]]` 等从 `Cargo.toml` 文本解析
  （行锚定 `^[[bin]]`，避免注释误计）。
- **Jaccard**：同一机制文件族（`mod.rs` 取父目录名，否则 basename）跨层两份文件的行集合，
  行 = `strip()` 后长度 ≥4 的非空行；报告只列**跨层**、非 `/test` 键的对，供“copy-forward”证据。
  `pairs_ge_90/95` = Jaccard ≥0.90/0.95 的跨层对数；`max_jaccard` 为最大值。
- **快照可复现**：`--git-ref` 通过 `git archive <ref>` + 标准库 `tarfile` 导出到临时目录后扫描，
  不受工作树未提交编辑影响；`--deterministic` 下同一 ref 两次输出应逐字节一致（除 git 字段）。

## 2. 基线：HEAD `163eb5f2`（P1 后，稳定快照）

### 2.1 总量（`src/`，不含 `.bak`；`--git-ref HEAD`）

| 分区 | 文件数 | 物理行 | 非空行 |
|---|---:|---:|---:|
| 参考版（层内，非孪生非测试） | 132 | 88,992 | **82,946** |
| 孪生（`bump_spine_iter*`） | 127 | 88,568 | **85,411** |
| 层内测试文件 | 25 | 18,917 | **17,075** |
| `src/bin` | 21 | 7,872 | 7,186 |
| glue | 32 | 13,171 | 12,290 |
| 归档（`src/bench_head|bench_pre`） | 0 | 0 | 0 |
| **`src/` 合计** | **337** | **217,512** | **204,908** |
| `.bak`（单列） | 0 | 0 | 0 |
| `tests/`（不计入 src） | 63 | 39,058 | 34,963（`#[test]` 1,363 / `#[ignore]` 11） |

层内小计：**284 文件 / 185,432 非空行**（= 132+127+25 文件；与 D3 逐项一致）。
逐层表（ref / twin / test 非空行）：L01 5,619/472/0；L02 1,139/1,628/0；L03 1,568/2,523/0；
L04 1,830/2,800/0；L05 2,182/3,526/0；L06 2,720/4,644/0；L07 6,835/8,758/2,048；
L08 5,760/8,441/1,723；L09 5,230/7,474/0；L10 6,566/9,224/0；L11 9,539/8,713/0；
L12 9,710/8,715/0；L13 **24,248 / 18,493 / 13,304**（L13 拆分为 D3 同口径）。

### 2.2 风险/质量指标（层内 ref+twin+test，除非注明）

`unsafe` 词出现 **317**（ref 91 / twin 226；L13 46+48、L01 30 为大头）；`unsafe {` 块 312；
`panic!(` **487**（L13 253）；`.unwrap()` **732**；`.expect(` **739**；`todo!` 16；`unreachable!` 97；
print 宏 **663**（L13 345、L12 95、L11 65、L10 62、L09 41、L07/L08 各 7）。
`src/` 全量（含 bin/glue）：unsafe 364、panic 498、unwrap 914、expect 761、print 876、`#[path]` 103。
“生产区”近似（`#[cfg(test)]` 之前）：panic 367、prints 739、unwrap 794、expect 650。

### 2.3 环境开关与构建

- `env::var` distinct：**`src/` 全量 68**；**层内 32**（46 次出现）；总出现 91。
  高频：`L06_NO_CONV_MEMO`×8、`L11_LOOPCAP`×4、`L06_NO_NAME_MAP`×3、`TYPORT_KICK_PROBE`×3、
  `L13BENCH_NOBSERVE`×2、`TYPORT_PROFILE`×2、`L13SAMPLE`/`L10SAMPLE`×2；另有
  `L02L05MEM_TRACE`/`L06L13MEM_*`/`L13_TW_*`/`TYPORT_TWIN_*`/`ZZ_TRACE` 等（全清单见 JSON `env.names`）。
- `Cargo.toml`：`[[bin]]` **22**、`[[test]]` 0、`test = false` **19**、`[features]` 1。
- `#[path]`：**`src/bin` 103 次 + `tests/` 105 次 = 208**（src 其余分类为 0）。
- 归档迁移证据：`tools/bench_snapshots/L07_pre/` 13 个 `.rs` / 12,728 非空行（= P1 前 `bench_pre` 量；
  与 D3 的 bench_pre 12,728 逐位一致）；P1 前 `src/bench_head` 12,606 行按提交说明删除（过期副本）。

## 3. P1 清理前后（`8443586e` → `8443586e`…`163eb5f2`）

基线命令：`python tools/metrics.py --git-ref HEAD --compare-ref 8443586e --json … --md …`
（两侧均为 git 快照，可复现；与工作树未提交编辑解耦）。

| 指标 | P1 前 `8443586e` | P1 后 `163eb5f2`(HEAD) | 变化 |
|---|---:|---:|---:|
| `src/` 文件数 | 362 | 337 | **−25** |
| `src/` 非空行 | 230,242 | 204,908 | **−25,334（−11.0%）** |
| `src/` 物理行 | 244,151 | 217,512 | −26,639 |
| 　层内（ref+twin+test）非空行 | 185,432 | 185,432 | **0（不变量）** |
| 　归档非空行 | 25,334 | 0 | −25,334 |
| 　`bin` / `glue` 非空行 | 7,186 / 12,290 | 7,186 / 12,290 | 0 / 0 |
| `src/` 全量 `unsafe` | 394 | 364 | −30（仅归档贡献） |
| `src/` 全量 `panic!` / `unwrap()` / `expect(` | 538 / 972 / 857 | 498 / 914 / 761 | −40 / −58 / −96 |
| `src/` 全量 print 宏 | 888 | 876 | −12 |
| `src/` 全量 `#[path]` | 103 | 103 | 0 |
| `.bak` 文件 / 非空行 | 0（git 不跟踪） | 0 | 需用 D3 历史值：17 / 12,464 |
| `src/bench_head|bench_pre` 存在 | True / True | False / False | P1 已处置 |

**判读**：P1 的收益全部在“仓库物理体积/`src/` 全量口径”上（−25,334 行 = −11.0%），**层内代码、
风险计数 317/487/732/739/663 不变**；连同 `.bak` 的 12,464 行，P1 合计从源码树移出/删除
**37,798 非空行**（与 D3 建议值一致）。实现细节（P1 提交 `163eb5f2` 信息）：`bench_head` 是
2026-09-29 的过期冻结副本（非 HEAD 拷贝），删除；`bench_pre` 的 15 文件 `git mv` 到
`tools/bench_snapshots/L07_pre`（14/15 与旧备份逐字节相同，仅顶层 README 更新），并改
`l07alloc`/`l07whoalloc`/`pmabbench` 的 `#[path]`；`.bak` 17 个删除。**建议另行更新 D3/FACTS
引用“19 bench bin”（P1 尚未合并 bin，仍 22 个 [[bin]]）**。

## 4. 与 D3 报告数字对账

| # | 指标 | D3 | 本工具 | 差异与归因 |
|---|---|---|---:|---|
| 1 | 层内文件 / 非空行 | 284 / 185,432 | 284 / 185,432 | ✅ 完全一致（含逐层表全部 13 行） |
| 2 | ref / twin / test | 82,946 / 85,411 / 17,075 | 同 | ✅ 一致（`--test-rule plural`） |
| 3 | L13 ref / test 拆分 | 24,248 / 13,304 | 同 | ✅ 一致（`debug_test.rs` 414 行归 ref；`--test-rule any` 可将 414 行移入 test） |
| 4 | bin / glue | 7,186 / 12,290 | 7,186 / 12,290 | ✅ 一致（P1 前 HEAD；P1 后未提交编辑另计） |
| 5 | `unsafe` | 317（ref 91 / twin 226） | 317（91 / 226） | ✅ 一致 |
| 6 | print 宏 | 663 | 663 | ✅ 一致 |
| 7 | L13 `.unwrap()` / `.expect(` | 238 / 197 | 238 / 197 | ✅ 一致 |
| 8 | 归档合计 | 25,334（12,606+12,728） | 25,334（P1 前快照） | ✅ 一致；P1 后 bench_pre 12,728 移入 `tools/bench_snapshots`，bench_head 12,606 删除 |
| 9 | `tests/` | 34,963 / 63 文件 / `#[test]` 1,363 / `#[ignore]` 17（含 src） | 34,963 / 63 / 1,363；ignore = 11(tests)+6(src) = 17 | ✅ 一致（工作树含未跟踪新测试文件时为 64/1,364，git-ref 快照不含） |
| 10 | `[[bin]]` | **19** | **22** | ⚠️ D3 的 19 = **bench bins**（22 总数 − main/typort/l13lspsample）；工具报全量。建议 D3 改写“19 bench bins / 22 总” |
| 11 | `test = false` | **20** | **19** | ⚠️ D3 把 Cargo.toml:19 注释里的 “`test = false` drops them” 计入；工具用行锚定正则，19 才是真实数 |
| 12 | `#[path]` | **118** | **208**（103 `src/bin` + 105 `tests/`） | ⚠️ 无法复现 D3 的 118；工具给出完整分解。可能 D3 只统计了部分文件或旧时点；**建议以工具二值为准并请 Lead 复核** |
| 13 | `src/` `#[test]` | **1,114** | **1,071**（层 1,045 + glue 26） | ⚠️ 差 −43；最可能：D3 grep 时把 L11/L12 的 `.bak`（12.4k 行整文件副本，含 `tests.rs` 拷贝）计入。`.bak` 已被 P1 删除，无法复测；建议 D3 标注口径 |
| 14 | env distinct / `std::env::var` | 33 / 28（层内） | 32 / 46（层内 `env::var` 出现；`std::env::var` 47） | ⚠️ 口径不同（工具按 `env::var(_os)` 全出现计数、名字去重）；清单在 JSON 可逐条对 |
| 15 | L13 `panic!` | **276** | **253** | ⚠️ 差 −23，未解释；同表中 `unwrap()`/`expect(` 精确一致，故排除整体口径差；建议 Lead 复核 D3 采样时点/正则 |
| 16 | Jaccard 抽样（D3 §3 表） | pretty 86.4、elaboration 82.1、pattern_match 80.5、parser 73.2、typeclass 89.7、unif 71.2/81.9、lex 85.0 | 83.2、74.3、74.7、59.2、87.0、60.7/74.3、84.5 | ⚠️ 本工具按标准 Jaccard（stripped 非空行、去 <4 字符）系统性地低；尝试 min-length 1→40 与含空行变体均无法复现 D3 值 ⇒ D3 的实现口径未公开。趋势一致（lex/macros 100%、typeclass≈87%、pretty≈83%、elaboration≈74%、parser≈59%），但**具体数字建议改用本工具输出** |
| 17 | `.bak` | 12,464 / 17 | 0（不可测） | ⚠️ `.bak` 在 HEAD 未跟踪、P1 前已被清除；工具只能引用 D3/提交信息历史值（P1 提交注明 12,464 非空行） |
| 18 | FACTS §2 LOC | “生产 LOC” 4,319(L07)/3,716(L08)/… | L07 ref 6,835 / L08 5,760（与 D3 一致） | ✅ 工具独立确认 FACTS 口径系统性偏低（应为非空行口径 + 排除测试文件后重算） |

**结论**：D3 的**核心规模/风险数字全部可复现**（284/185,432/82,946/85,411/17,075、317、663、归档 25,334），
分歧集中在**计数口径与文档期时点**（bin 定义、注释误计、`#[path]`、`#[test]`/`.bak`、env 口径、Jaccard 算法）。
建议：D3/FINAL/D1 中凡引用上述指标处改为“由 `tools/metrics.py` 生成（附 JSON 路径）”，
并在 D3 更新 §2.1 的 `[[bin]]`/`test=false`/`#[path]` 三项与 §3 的 Jaccard 表。

## 5. CI 门禁 `--check`（Lead P0-2 接口）

### 5.1 语义与退出码

- `tools/gate_p0.sh` 第 90–100 行按 `--help` 探测：实测（`bash tools/gate_p0.sh --dry-run`）
  输出 `==> [metrics] DRY-RUN: python3 tools/metrics.py --check`，即**接口已对齐**；
  gate 对 metrics 只认 exit code（非 0 = FAIL，但 SKIP 不算失败）。
- **退出码选择（首轮 advisory）**：`--check` 默认打印 `PASS/WARN` 后 **exit 0**；
  `--strict` 才在任一 WARN 时 exit 1。理由：①基线刚建立且 P1 刚提交（HEAD 在任务期间从
  `8443586e`→`377b1af1`→`163eb5f2`），工作树持续有并行编辑；②gate 的 SKIP 容错口径要求
  “未就绪不阻塞主分支”，advisory 与之一致；③避免因 D3 口径未对账的项（见 §4）先红。
  **P1 稳定/基线冻结后建议**把 gate 改为 `python3 tools/metrics.py --check --strict`
  （gate 本身无需改代码，仅一行参数）。
- 基线来源优先级：`docs/metrics/baseline-2026-11-09.json` 的 `check_baseline` →
  （缺失时）脚本内置 `BUILTIN_CHECK_BASELINE`（与本次基线同步，输出标注 `baseline=builtin`）。

### 5.2 检查项与阈值

| 检查项 | 阈值 | 基线值 |
|---|---|---:|
| `src/` 非空行 | ≤ 基线 ×1.005（+0.5%） | 204,908 |
| 层内非空行 | ≤ 基线 ×1.005 | 185,432 |
| `unsafe`（层内） | 不得高于基线 | 317 |
| `panic!` / `.unwrap()` / `.expect(` / print 宏（层内） | 各自不得高于基线 | 487 / 732 / 739 / 663 |
| 归档非空行 / `.bak` 文件数 | 必须为 0（防重新归档） | 0 / 0 |
| 跨层复制（Jaccard ≥90% / ≥95% 对数） | 不得高于基线 | 24 / 10 |
| INFO（不判失败） | 最大 Jaccard / env distinct / `[[bin]]` / `test=false` | 1.0 / 68 / 22 / 19 |

### 5.3 验证矩阵（已执行，均为静态；无 cargo）

| 场景 | 命令 | 结果 |
|---|---|---|
| 正常 | `python tools/metrics.py --check` | `RESULT: PASS - 11/11 checks within baseline`，exit 0 |
| 基线缺失回退 | `--check --baseline-json /nonexistent` | 标注 `baseline=builtin`，按内置阈值判定（不崩） |
| WARN 路径 | 用临时基线把 unsafe 改 100 等（`$TEMP/tight_baseline.json`） | `RESULT: WARN - 3/11`，默认 exit 0 |
| strict 路径 | 同上 + `--strict` | `RESULT: WARN - 3/11 (mode=strict)`，exit 1 |
| gate 探测 | `bash tools/gate_p0.sh --dry-run` | 选中 `--check`（不再 SKIP） |
| 跨平台 | WSL `python3` 3.6.9 / Windows `python` 3.10.4 | `--help`、`--check` 均正常（脚本无 3.7+ 语法/API） |

## 6. 局限与维护

1. **快照时点**：基线 = `163eb5f2`（P1 提交）。HEAD 在任务期间被并行推进，故本报告一律用
   `--git-ref HEAD` + `--compare-ref 8443586e` 的**提交快照**，不含工作树未提交编辑；
   刷新基线：`python tools/metrics.py --git-ref HEAD --compare-ref 8443586e --json … --md …`。
2. **不可测项**：`.bak`（HEAD 未跟踪，已由 P1 删除）只能用 D3/提交信息历史值；
   `.gitignore` 内其它未跟踪文件同理（工作树扫描与 git-ref 扫描会差这些文件：当前 `tests/` 的
   64/1,364 就是多了一个未跟踪 P0 测试文件）。
3. **粗粒度**：计数为文本正则出现次数（注释里的 `panic!` 等也计）；`unsafe` 词与块分别统计；
   `#[cfg(test)]` 生产区为近似；Jaccard 去短行阈值会改变绝对值（敏感性：min-length 4→20 可让
   elaboration 74.3%→68.9%）；`#[path]`/env 的口径见 §1.2。**跨报告比较必须同口径**。
4. **check 的边界**：只做静态度量门禁，不替代 `cargo test`/parity/Lean oracle（那是 gate 的
   另外两件）；`+0.5%` 容忍意味着少量新增行不告警；`--check` 不校验 D3 文档数字本身。
5. **维护动作**：D3/FINAL 引用数字改为工具输出；P1 完成后把 `gate_p0.sh` 的 metrics 步骤切
   `--strict`；每次阶段收口重跑基线并更新 `check_baseline`（内置常量随之同步）。

## 7. 复现

```bash
# 当前工作树度量
python tools/metrics.py --json /tmp/m-worktree.json --md /tmp/m-worktree.md
# P1 后基线（HEAD 提交快照）+ 与 P1 前 8443586e 对照
python tools/metrics.py --git-ref HEAD --compare-ref 8443586e \
  --json docs/metrics/baseline-2026-11-09.json \
  --md   docs/metrics/baseline-2026-11-09.md
# CI 门禁
python tools/metrics.py --check            # advisory: WARN + exit 0
python tools/metrics.py --check --strict   # blocking: WARN + exit 1
```

产出文件：`tools/metrics.py`（1,630 行）、`docs/metrics/baseline-2026-11-09.json`（263 KB）、
`docs/metrics/baseline-2026-11-09.md`（274 行，本报告数字的来源）。
