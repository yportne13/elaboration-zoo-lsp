#!/usr/bin/env bash
# tools/gate_lean_oracle.sh — Lean oracle 差分门禁（渐进式：无工具链时明确 SKIP，不阻塞）。
#
# 行为：
#   1) 检测 Lean 工具链：`lean --version` 可用，或 `~/.elan`（含 bin/lean 或 bin/lake）；
#      找不到 → 打印 SKIP + 安装提示，**exit 0**（CI 上该 step 是 optional/continue-on-error）。
#   2) 有工具链 → `cd lean && lake build && lake build engine-oracle`；
#   3) 回仓库根 → `LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity`。
#
# 用法：
#   bash tools/gate_lean_oracle.sh
#   bash tools/gate_lean_oracle.sh --dry-run     # 只打印将执行的命令，不真正构建/测试
#   CARGO_TARGET_DIR=/path/to/target bash tools/gate_lean_oracle.sh   # 透传给 cargo
#
# 退出码：0 = PASS 或 SKIP；1 = 构建/测试 FAIL；2 = 参数错误。
#
# 为什么默认 SKIP 不算失败：Lean 4 工具链（elan/lake）与 ~2 GB 构建缓存尚未纳入 CI
#   provision；oracle 是**第三方语义裁判**，价值高但样本小（4 例 curated 语料），
#   暂不作为阻塞门禁。转必需的方法见 docs/optimal-design/P0-ci-report.md §4。
set -u

cd "$(dirname "$0")/.." || { echo "[FAIL] cannot cd to repo root"; exit 1; }

DRY_RUN=0
for arg in "$@"; do
    case "$arg" in
        --dry-run) DRY_RUN=1 ;;
        -h|--help)
            sed -n '2,26p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "[FAIL] unknown argument: $arg (only --dry-run / --help)" >&2
            exit 2
            ;;
    esac
done

LOGDIR="${CARGO_TARGET_DIR:-$PWD/target}/gate_lean_oracle_logs"
[ "$DRY_RUN" = "1" ] || mkdir -p "$LOGDIR" || { echo "[FAIL] cannot create $LOGDIR"; exit 1; }

echo "== gate_lean_oracle: repo=$PWD dry_run=$DRY_RUN"

# ---------------------------------------------------------------- 工具链探测
# 先看 PATH；再补 ~/.elan/bin（elan 默认安装位置，CI/新环境常见未 export）。
if command -v lean >/dev/null 2>&1; then
    LEAN_FOUND=1
    LEAN_WHY="lean on PATH: $(command -v lean)"
elif [ -x "${HOME:-/nonexistent}/.elan/bin/lean" ]; then
    LEAN_FOUND=1
    LEAN_WHY="~/.elan/bin/lean"
    export PATH="${HOME}/.elan/bin:$PATH"
elif [ -x "${HOME:-/nonexistent}/.elan/bin/lake" ]; then
    LEAN_FOUND=1
    LEAN_WHY="~/.elan/bin/lake"
    export PATH="${HOME}/.elan/bin:$PATH"
else
    LEAN_FOUND=0
    LEAN_WHY=""
fi

if [ "$LEAN_FOUND" -eq 0 ]; then
    if [ "${GATE_LEAN_ORACLE_REQUIRED:-0}" = "1" ]; then
        echo "== gate_lean_oracle: [FAIL] GATE_LEAN_ORACLE_REQUIRED=1 但未检测到 Lean 工具链（lean --version / ~/.elan）"
        echo "   安装后重跑，或去掉 REQUIRED 以恢复可选口径；见 docs/optimal-design/P0-ci-report.md §4。"
        exit 1
    fi
    echo "== gate_lean_oracle: [SKIP] 未检测到 Lean 工具链（lean --version 与 ~/.elan 均不可用）"
    echo "   安装（Linux/macOS，二选一）："
    echo "     curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"
    echo "     export PATH=\"\$HOME/.elan/bin:\$PATH\""
    echo "   Windows：winget install Lean.Lean 或 https://leanprover-community.github.io/get_started.html"
    echo "   SKIP 不计失败（CI 上该 step 为 continue-on-error；成熟后转必需，见 P0-ci-report.md §4）。"
    exit 0
fi

echo "== gate_lean_oracle: toolchain = $LEAN_WHY"
if command -v lean >/dev/null 2>&1; then
    LEAN_VER="$(lean --version 2>/dev/null | head -1 || true)"
    echo "   ${LEAN_VER:-(lean --version 无输出)}"
fi

if [ "$DRY_RUN" = "1" ]; then
    # dry-run 不检查 lake/cargo 是否就位（本地排障/Windows 交叉验证用），只打印将执行的命令。
    echo "==> [lean_build] DRY-RUN: (cd lean && lake build && lake build engine-oracle)"
    echo "==> [lean_oracle] DRY-RUN: env LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity"
    echo "== gate_lean_oracle: DRY-RUN done（未执行任何构建/测试）"
    exit 0
fi

for need in lake cargo; do
    if ! command -v "$need" >/dev/null 2>&1; then
        echo "== gate_lean_oracle: [FAIL] 工具链存在但 PATH 中无 $need"
        exit 1
    fi
done

# ---------------------------------------------------------------- lake build
echo "==> [lean_build] cd lean && lake build && lake build engine-oracle"
if ( cd lean && lake build && lake build engine-oracle ) >"$LOGDIR/lean_build.log" 2>&1; then
    tail -n 3 "$LOGDIR/lean_build.log" | sed 's/^/    /'
    echo "    [PASS: log: $LOGDIR/lean_build.log]"
else
    rc=$?
    echo "    [FAIL: rc=$rc — 完整输出: $LOGDIR/lean_build.log]"
    tail -n 20 "$LOGDIR/lean_build.log" | sed 's/^/    /'
    echo "== gate_lean_oracle: FAIL (lake build)"
    exit 1
fi

# oracle 二进制名随平台（Linux 无后缀 / Windows .exe）；测试侧两者都探测。
if [ -f lean/.lake/build/bin/engine-oracle ]; then
    echo "== gate_lean_oracle: oracle bin = lean/.lake/build/bin/engine-oracle"
elif [ -f lean/.lake/build/bin/engine-oracle.exe ]; then
    echo "== gate_lean_oracle: oracle bin = lean/.lake/build/bin/engine-oracle.exe"
else
    echo "== gate_lean_oracle: [FAIL] lake build 成功但找不到 engine-oracle 可执行文件"
    exit 1
fi

# ---------------------------------------------------------------- cargo test
echo "==> [lean_oracle] env LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity"
if env LEAN_ORACLE=1 cargo test --release --test lean_oracle_parity >"$LOGDIR/lean_oracle.log" 2>&1; then
    grep -E "^test result|^running" "$LOGDIR/lean_oracle.log" | tail -n 2 | sed 's/^/    /'
    echo "    [PASS: log: $LOGDIR/lean_oracle.log]"
else
    rc=$?
    echo "    [FAIL: rc=$rc — 完整输出: $LOGDIR/lean_oracle.log]"
    tail -n 30 "$LOGDIR/lean_oracle.log" | sed 's/^/    /'
    echo "== gate_lean_oracle: FAIL (lean_oracle_parity)"
    exit 1
fi

echo "== gate_lean_oracle: PASS"
exit 0
