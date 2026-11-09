#!/usr/bin/env bash
# tools/gate_p0.sh — P0 提交前门禁：仓库度量 --check + 引擎 parity + Lean oracle 差分。
#
# 用法：
#   bash tools/gate_p0.sh
#   bash tools/gate_p0.sh --dry-run                # 只打印将执行的命令，不跑任何子进程（本地校验/CI 排障用）
#   CARGO_TARGET_DIR=/path/to/target bash tools/gate_p0.sh   # 原样透传给 cargo（日志落在 $CARGO_TARGET_DIR/gate_p0_logs）
#
# 三件套（Lead 2026-11-09 P0 任务口径）：
#   1) metrics : `python3 tools/metrics.py --check`（仓库度量一致性；P0-1 并行落地）
#   2) parity  : `bash tools/run_engine_parity.sh`（双引擎 parity 聚合；若存在）
#   3) oracle  : `LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity`
#                （仅当 lean/.lake/build/bin/engine-oracle{,.exe} 已构建时执行）
#
# 退出码语义：0 = 全部 PASS 或 SKIP；1 = 任一 FAIL。**SKIP 不算失败**
#   （未就绪的子件不得阻塞主分支；一旦对应文件/二进制落地，本脚本自动从 SKIP 转 PASS/FAIL）。
#
# 依赖未就绪时的行为（刻意设计，避免 gate 先于 P0-1 合入而红）：
#   - tools/metrics.py 不存在           → SKIP + 提示（P0-1 合入后自动生效）
#   - tools/run_engine_parity.sh 不存在 → SKIP + 提示
#   - Lean oracle 二进制不存在          → SKIP + 提示（CI 上 `lean/.lake` 未提交，常态即 SKIP；
#                                          需要真跑时用 `bash tools/gate_lean_oracle.sh` 走工具链构建）
set -u

cd "$(dirname "$0")/.." || { echo "[FAIL] cannot cd to repo root"; exit 1; }

DRY_RUN=0
for arg in "$@"; do
    case "$arg" in
        --dry-run) DRY_RUN=1 ;;
        -h|--help)
            sed -n '2,32p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "[FAIL] unknown argument: $arg (only --dry-run / --help)" >&2
            exit 2
            ;;
    esac
done

LOGDIR="${CARGO_TARGET_DIR:-$PWD/target}/gate_p0_logs"
[ "$DRY_RUN" = "1" ] || mkdir -p "$LOGDIR" || { echo "[FAIL] cannot create $LOGDIR"; exit 1; }

fail=0
t_all=$SECONDS

echo "== gate_p0: repo=$PWD"
echo "== gate_p0: target dir logs=$LOGDIR dry_run=$DRY_RUN"

# run_step <name> <cmd...>
run_step() {
    local name="$1"
    shift
    local t0=$SECONDS
    local log="$LOGDIR/$name.log"
    if [ "$DRY_RUN" = "1" ]; then
        echo "==> [$name] DRY-RUN: $*"
        echo "    [SKIP: dry-run]"
        return 0
    fi
    echo "==> [$name] $*"
    if "$@" >"$log" 2>&1; then
        tail -n 3 "$log" | sed 's/^/    /'
        echo "    [PASS: $((SECONDS - t0))s, log: $log]"
    else
        local rc=$?
        echo "    [FAIL: rc=$rc, $((SECONDS - t0))s — 完整输出: $log]"
        tail -n 20 "$log" | sed 's/^/    /'
        fail=1
    fi
}

# ---------------------------------------------------------------- 1) metrics
# 接口自适应：Lead 口径是 `--check`；P0-1 的 metrics.py 可能先落地为 `--check-budgets`
# 或尚未提供检查子命令。这里按 --help 探测实际支持的 flag，避免 gate 因接口迭代先红。
if [ -f tools/metrics.py ]; then
    PY=""
    if command -v python3 >/dev/null 2>&1; then
        PY=python3
    elif command -v python >/dev/null 2>&1; then
        PY=python
    else
        echo "==> [metrics] [FAIL] tools/metrics.py 存在但找不到 python3/python"
        fail=1
    fi
    if [ -n "$PY" ]; then
        METRICS_FLAG=""
        METRICS_HELP="$("$PY" tools/metrics.py --help 2>/dev/null || true)"
        if printf '%s\n' "$METRICS_HELP" | grep -Eq -- '--check([^-A-Za-z0-9_]|$)'; then
            METRICS_FLAG=--check
        elif printf '%s\n' "$METRICS_HELP" | grep -q -- '--check-budgets'; then
            METRICS_FLAG=--check-budgets
            echo "==> [metrics] 注：metrics.py 暂无 --check，使用兼容 flag --check-budgets（P0-1 定稿后建议统一）"
        fi
        if [ -z "$METRICS_FLAG" ]; then
            echo "==> [metrics] [SKIP] tools/metrics.py 存在但尚无 --check/--check-budgets 检查子命令（P0-1 接口未定稿）"
            echo "    自检：$PY tools/metrics.py --help；定稿后本步自动生效"
        else
            run_step metrics "$PY" tools/metrics.py "$METRICS_FLAG"
        fi
    fi
else
    echo "==> [metrics] [SKIP] tools/metrics.py 未就绪（P0-1 并行落地中）；合入后本步自动生效"
fi

# ---------------------------------------------------------------- 2) parity
if [ -f tools/run_engine_parity.sh ]; then
    run_step parity bash tools/run_engine_parity.sh
else
    echo "==> [parity] [SKIP] tools/run_engine_parity.sh 未就绪；合入后本步自动生效"
fi

# ---------------------------------------------------------------- 3) lean oracle
ORACLE_BIN=""
for cand in lean/.lake/build/bin/engine-oracle lean/.lake/build/bin/engine-oracle.exe; do
    if [ -f "$cand" ]; then
        ORACLE_BIN="$cand"
        break
    fi
done

if [ -n "$ORACLE_BIN" ]; then
    echo "==> [lean_oracle] oracle 二进制: $ORACLE_BIN"
    if [ "$DRY_RUN" = "1" ]; then
        # dry-run 只打印命令：本机 PATH 里没有 cargo 也不算失败（CI 上必有）。
        run_step lean_oracle env LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity
    elif ! command -v cargo >/dev/null 2>&1; then
        echo "==> [lean_oracle] [FAIL] oracle 二进制存在（$ORACLE_BIN）但 PATH 中无 cargo"
        fail=1
    else
        run_step lean_oracle env LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity
    fi
else
    echo "==> [lean_oracle] [SKIP] 未找到 lean/.lake/build/bin/engine-oracle{,.exe}"
    echo "    需要真跑：bash tools/gate_lean_oracle.sh（有 Lean 工具链时自动 lake build engine-oracle）"
fi

# ---------------------------------------------------------------- summary
echo "== gate_p0: total $((SECONDS - t_all))s, fail=$fail"
if [ "$fail" -eq 0 ]; then
    echo "== gate_p0: PASS（skips 允许，不计失败）"
else
    echo "== gate_p0: FAIL（见上方 FAIL 行与日志）"
fi
exit "$fail"
