# P0 CI/Gate 报告（P0-2：gate_p0.sh + gate_lean_oracle.sh + ci.yml 接线）

> 分支 `p0-p1-baseline-cleanup`（共享工作树，**未 commit / 未 push**，改动仅工作区）。
> 执行者：P0-2（analyst-l09）。时间：2026-11-09 08:58–09:08。约束：只写脚本/CI/本报告，不碰 Rust 源码、未跑 cargo。
> 交付：`tools/gate_p0.sh`、`tools/gate_lean_oracle.sh`、`.github/workflows/ci.yml`（+15 行）、本文件。

## 1. 摘要

| 文件 | 状态 | 说明 |
|---|---|---|
| `tools/gate_p0.sh` | 新增 | P0 门禁聚合：metrics `--check` + engine parity + Lean oracle（预构建二进制）；SKIP 不算失败 |
| `tools/gate_lean_oracle.sh` | 新增 | Lean 工具链探测 → `lake build` → `LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity`；无工具链明确 SKIP(exit 0) |
| `.github/workflows/ci.yml` | 修改 +15 行 | `test` job 末尾新增 2 个 step（P0 gate、Lean oracle optional），其他 job 未动 |
| `docs/optimal-design/P0-ci-report.md` | 新增 | 本报告（设计、optional 理由、转必需路线、未验证项） |

一句话：**门禁先以"可容忍未就绪子件"的形态接入 CI**——P0-1 的 `metrics.py` / `run_engine_parity.sh` 落地过程中不会把 CI 打红，落地后同一 step 自动从 SKIP 转 PASS/FAIL；Lean oracle 以 `continue-on-error` 保持 optional。

## 2. `tools/gate_p0.sh` 设计

### 2.1 三件套与判定

| # | 步骤 | 命令 | 执行条件 | 判定 |
|---|---|---|---|---|
| 1 | metrics | `python3 tools/metrics.py <check-flag>` | `tools/metrics.py` 存在且找到 `--check`/`--check-budgets` | exit 0 → PASS；非 0 → FAIL；无检查子命令 → SKIP |
| 2 | parity | `bash tools/run_engine_parity.sh` | 文件存在 | exit 0 → PASS；非 0 → FAIL |
| 3 | lean_oracle | `env LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity` | `lean/.lake/build/bin/engine-oracle{,.exe}` 存在且 PATH 有 cargo | exit 0 → PASS；非 0 → FAIL |

- 退出码：**0 = 全 PASS 或 SKIP；1 = 任一 FAIL**。SKIP 明确不算失败（`set -u`，不 `set -e`，手工累计 `fail`）。
- 每步打印 `[PASS] / [SKIP] / [FAIL]` 前缀，便于 CI 日志 grep；完整输出落 `$CARGO_TARGET_DIR/gate_p0_logs/<step>.log`（默认 `./target/gate_p0_logs`，CI 上随现有 cargo 缓存一起）。
- `CARGO_TARGET_DIR` 原样透传（与 `tools/gate_l13.sh` 同款约定）。
- `--dry-run`：只打印将执行的命令、不跑子进程（本地/CI 排障）；`--help` 打印头部注释；未知参数 exit 2。

### 2.2 metrics 接口自适应（重要，当前存在接口差）

Lead 口径是 `python3 tools/metrics.py --check`；但 P0-1 当前落地的 `metrics.py`（09:02 版，42.6 KB）**尚未实现任何检查子命令**（argparse 仅 `--root/--json/--md/--deterministic/--no-git`；docstring 提到 `--check-budgets` 但未实现）。
为避免门禁因接口迭代先红，`gate_p0.sh` 按 `--help` 探测实际 flag：

1. 有 `--check` → 用它（Lead 口径，优先）；
2. 只有 `--check-budgets` → 用它并打印兼容提示；
3. 两者都无 → SKIP + 提示"接口未定稿"，**不阻塞**。

**建议（给 Lead/P0-1）**：`metrics.py` 定稿时统一提供 `--check`（或把 `--check-budgets` 固化为正式名），gate 侧无需再改；若两版接口同时存在，gate 会优先 `--check`。

### 2.3 为什么 Lean 步骤只探测预构建二进制、不自己 build

`gate_p0.sh` 是**快速门禁**，不应在每次 CI 里做 Lean 构建（lake 全量构建 ~2 GB 缓存、分钟级）。构建+测试的完整路径放在 `gate_lean_oracle.sh`（见 §3）。`lean/.lake/` 已写进 `.gitignore`（见该文件 `lean/.lake/` 条目）⇒ **CI checkout 上恒无 oracle 二进制，本步在 CI 常态 SKIP**，这是预期行为；本地/专用 job 先构建后才会真跑。

## 3. `tools/gate_lean_oracle.sh` 设计

1. **工具链探测**（按序）：`command -v lean` → `$HOME/.elan/bin/lean` → `$HOME/.elan/bin/lake`；命中 `.elan` 时把 `$HOME/.elan/bin` 前置到 PATH。
2. **无工具链**：打印 SKIP + 安装提示（elan 一行安装 / winget / 官方 get_started 链接），**exit 0**。
   - 新增逃生门：`GATE_LEAN_ORACLE_REQUIRED=1` 时改为 **exit 1**（供"转必需"阶段使用，见 §4）。
3. **有工具链**：先 `cd lean && lake build && lake build engine-oracle`（第二段是产出 oracle 可执行文件的必要 target；日志 `gate_lean_oracle_logs/lean_build.log`）。
4. 回仓库根：`LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity`（oracle 路径由测试自身按 `CARGO_MANIFEST_DIR/lean/.lake/build/bin/engine-oracle{,.exe}` 探测，平台名都覆盖；不依赖 `LEAN_ORACLE_BIN`）。
5. `--dry-run` 同上只打印命令；无 `lake`/`cargo` 但探测到工具链时明确 FAIL（工具链残缺）。
6. 判定：构建或测试任一失败 → exit 1；PASS/SKIP → exit 0。

## 4. `.github/workflows/ci.yml` 变更

### 4.1 变更内容（仅 `test` job，末尾两 step）

```yaml
      # P0 gate（2026-11-09 baseline-cleanup）：仓库度量 --check + 引擎 parity 聚合。
      # 子件未就绪时（tools/metrics.py / tools/run_engine_parity.sh 尚未合入）
      # tools/gate_p0.sh 打印 [SKIP] 且不计失败，所以本 step 可以先于 P0-1 落地；
      # 两脚本一旦就绪，同一 step 自动从 SKIP 转为 PASS/FAIL。
      - name: Run P0 gate (metrics + parity)
        run: bash tools/gate_p0.sh

      # Lean oracle 差分：第三方语义裁判（4 例 curated 语料）。CI 目前未 provision
      # Lean 4 工具链与 ~2GB lake 缓存 ⇒ tools/gate_lean_oracle.sh 明确 SKIP（exit 0）。
      # 先以 continue-on-error 保持 optional、不阻塞发布；工具链纳入 CI 后删除该行
      # 即转必需（判据与步骤见 docs/optimal-design/P0-ci-report.md §4）。
      - name: Lean oracle (optional)
        run: bash tools/gate_lean_oracle.sh
        continue-on-error: true
```

位置：`test` job 现有最后一步 `Check every example and test target builds` 之后；`test-full` / `dependencies` / 三个 build / `release` job **未改**。
`git diff` 记录：`.github/workflows/ci.yml | 15 +++++++++++++++`（纯插入，无删除/重排）。

### 4.2 为什么 Lean oracle 先 optional（continue-on-error）

1. **CI 未 provision Lean 4 工具链**（elan + lake 构建缓存 ~2 GB）；现在改成必需会让所有 push 变红。
2. oracle 是**第三方语义裁判**、价值高但**样本小**（4 例 curated 语料：occurs-transitive / stuck-match-bounded / empty-type-zero-arm / struct-eq-pending）；D2/EXP-7 已记录其局限，暂不宜作为发布阻塞项。
3. 先用 `continue-on-error` 让 step **在 CI 上真实执行一次**（验证脚本/路径/缓存行为），失败只标 warning、不影响 job 结论——比"不接线"多拿到真实执行证据。

### 4.3 如何转必需（checklist）

1. 在 `test` job 增加 toolchain 步骤（时序可缓存在 `~/.elan`）：
   `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y`；
   `echo "$HOME/.elan/bin" >> "$GITHUB_PATH"`；缓存 `lean/.lake`（key 含 `lean/lake-manifest.json` 哈希）。
2. 删除 `test` job 里 `Lean oracle (optional)` step 的 `continue-on-error: true`。
3. 给该 step 加 `timeout-minutes: 30`（lake 全量重建 + 4 例差分；本机实测 oracle 测试 1.0 s，构建是大头）。
4. 把 gate 内的 SKIP 收紧为失败：`GATE_LEAN_ORACLE_REQUIRED=1 bash tools/gate_lean_oracle.sh`
   （可选：给 `gate_p0.sh` 加同类 strict 开关；当前未加，保持主分支容忍面）。
5. 验收：连续 3 个 push 的 CI 中该 step 为绿色 PASS（不是 SKIP）且耗时稳定；失败时能定位到 `lake_build.log`/`lean_oracle.log`。

## 5. 验证记录（本机，**无 GHA 环境**）

| 验证项 | 命令 | 结果 |
|---|---|---|
| bash 语法 | `bash -n tools/gate_p0.sh`、`bash -n tools/gate_lean_oracle.sh` | 均 exit 0（bash 4.4.20） |
| gate_p0 干跑 | `bash tools/gate_p0.sh --dry-run` | exit 0；输出 metrics/parity/lean 三步判定（当前 metrics=SKIP、parity=DRY-RUN、lean=DRY-RUN） |
| gate_lean_oracle 干跑 | `bash tools/gate_lean_oracle.sh --dry-run` | exit 0；正确打印 lake build + cargo test 两条命令 |
| `--help` / 错误参数 | `--help` / `--bogus` | help 正常；未知参数 exit 2 |
| YAML 合法性 | `python -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml'))"` | 通过；`jobs` = test/test-full/dependencies/build-vscode/build-cli/build-cli-macos/release；`test.steps` 末尾两项为新增 step；`continue-on-error: true` 解析正确 |
| diff 范围 | `git diff --stat -- .github/workflows/ci.yml` | `1 file changed, 15 insertions(+)`，其他 job 无改动 |
| 未执行 | `cargo` / GHA / actionlint | 按约束未跑 cargo、无 GHA 环境、未安装 actionlint |

**当前依赖状态（写入本报告时，09:04–09:05）**：
- `tools/metrics.py` 已由 P0-1 落盘（42.6 KB，09:02），**尚无 `--check`/`--check-budgets` 实现** → gate 自适应为 SKIP + 提示（§2.2）；
- `tools/run_engine_parity.sh` 已落盘（09:03，`set -euo pipefail`，跑 `cargo test --release --test engine_parity_report -- --ignored`）；对应 `tests/engine_parity_report.rs`（30 KB）同时存在；
- `lean/.lake/build/bin/engine-oracle.exe` 本地存在（11-08 21:20 构建）但 `lean/.lake/` 被 `.gitignore` 忽略 ⇒ CI 上必然 SKIP。

## 6. 未验证项与风险（诚实清单）

1. **GHA 真跑未验证**：本机无 GitHub Actions；ubuntu-latest 的 bash 5.x / python3 / 缓存行为与 WSL bash 4.4.20 不完全等价。首次 push 后需看一次真实日志（重点：`Run P0 gate` 的 SKIP 语义与 `Lean oracle (optional)` 是否显示 warning 而不影响 job）。
2. **actionlint / YAML schema** 未跑（只做了 `yaml.safe_load` 语法级校验）。
3. **metrics.py 接口可能再变**：若 P0-1 定稿的检查命令既非 `--check` 也非 `--check-budgets`，gate 会 SKIP 而非 FAIL（容忍设计）；需 Lead 在 P0-1 收口时对齐接口（§2.2 建议）。
4. **parity 脚本的运行成本**：`run_engine_parity.sh` 会 `cargo test --release --test engine_parity_report -- --ignored`（默认全量示例，可能分钟级）；`test` job 已有 60 min 超时，暂未给该 step 单独限时。若首次 CI 太慢，可用 `ENGINE_PARITY_ONLY`/`ENGINE_PARITY_MAX_FILES` 收敛 smoke 口径（脚本原生支持）。
5. **Lean step 在 CI 恒 SKIP**（`lean/.lake` 未提交）：这是预期，不要误读为"oracle 已在 CI 验证"；真跑只有 `gate_lean_oracle.sh` 在 provision 工具链后才发生。
6. **共享工作树并发**：本轮期间其他成员在改 `Cargo.toml`、归档 `docs/review-*` 等；本任务只碰 4 个约定文件，`git status` 里其余改动均非本任务（未 commit/push）。
7. **step 级超时/重试**未加（可选后续项）；`continue-on-error` 只影响该 step 的结论，不影响后续 `dependencies/release` job 的 needs 关系（它们 needs `test` job，job 级结论仍为成功——符合"先不阻塞"意图）。

## 7. 复现命令

```bash
# 本地（任意平台，bash）：
bash tools/gate_p0.sh --dry-run
bash tools/gate_lean_oracle.sh --dry-run

# CI 等价（自行 provision 环境后）：
bash tools/gate_p0.sh
bash tools/gate_lean_oracle.sh

# YAML 校验：
python -c "import yaml; d=yaml.safe_load(open('.github/workflows/ci.yml')); print(list(d['jobs']['test']['steps'][-2:]))"
```

## 8. 给 Lead 的一句话结论

**P0 门禁已接线且"未就绪不阻塞"：`gate_p0.sh` 自适应 metrics 接口、缺件 SKIP，`gate_lean_oracle.sh` 无工具链明确 SKIP(exit 0)，CI 两 step 仅插入 `test` job；唯一待协调项是 metrics.py 的检查子命令名（现无 `--check`），定稿后同一 step 自动转 PASS/FAIL。**
