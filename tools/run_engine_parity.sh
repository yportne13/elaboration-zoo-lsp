#!/usr/bin/env bash
# P0-1: run the reference-vs-twin engine parity report.
#
# Usage:
#   bash tools/run_engine_parity.sh
#   ENGINE_PARITY_ONLY=examples/hdl bash tools/run_engine_parity.sh   # smoke
#   ENGINE_PARITY_MAX_FILES=3 bash tools/run_engine_parity.sh
#   ENGINE_PARITY_MODES=core bash tools/run_engine_parity.sh
#
# Build output MUST NOT land on F: (repo disk has <1 GB free).  The script
# defaults CARGO_TARGET_DIR to C:/ezl-target on Windows (Git Bash / MSYS) and to
# ./target on other platforms.  Report files are written next to the target dir:
#   $CARGO_TARGET_DIR/engine-parity-report.{json,md}
set -euo pipefail

cd "$(dirname "$0")/.."

if [ -z "${CARGO_TARGET_DIR:-}" ]; then
    case "$(uname -s)" in
        MINGW*|MSYS*|CYGWIN*) CARGO_TARGET_DIR="C:/ezl-target" ;;
        *) CARGO_TARGET_DIR="target" ;;
    esac
    export CARGO_TARGET_DIR
fi

# Keep the report next to the build artifacts unless explicitly overridden.
export ENGINE_PARITY_OUT="${ENGINE_PARITY_OUT:-$CARGO_TARGET_DIR}"

# Two modes:
#   * default (no env)                 -> FULL corpus (P0 baseline; ~1-3 min locally)
#   * GATE_P0_MAX_FILES=<n> (CI smoke) -> first n files only, bounded CI cost
# ENGINE_PARITY_MAX_FILES / ENGINE_PARITY_ONLY / ENGINE_PARITY_MODES still work
# as explicit overrides.
if [ -n "${GATE_P0_MAX_FILES:-}" ] && [ -z "${ENGINE_PARITY_MAX_FILES:-}" ]; then
    export ENGINE_PARITY_MAX_FILES="$GATE_P0_MAX_FILES"
fi

echo "== engine parity report (P0-1)"
echo "   repo:            $(pwd)"
echo "   CARGO_TARGET_DIR: $CARGO_TARGET_DIR"
echo "   report dir:       $ENGINE_PARITY_OUT"
[ -n "${ENGINE_PARITY_ONLY:-}" ] && echo "   filter:           ENGINE_PARITY_ONLY=$ENGINE_PARITY_ONLY"
[ -n "${ENGINE_PARITY_MAX_FILES:-}" ] && echo "   max files:        $ENGINE_PARITY_MAX_FILES"

start=$(date +%s)
cargo test --release --test engine_parity_report -- --ignored --nocapture
end=$(date +%s)

echo
echo "== done in $((end - start))s"
echo "   report: $ENGINE_PARITY_OUT/engine-parity-report.json"
echo "   report: $ENGINE_PARITY_OUT/engine-parity-report.md"
