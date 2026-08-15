#!/bin/bash
# Memory sweep: measure peak working set of `typort check` across recent commits.
# Usage: bash tools/memory_sweep.sh
set -u
cd "$(dirname "$0")/.." || exit 1
LOG="$PWD/memory_sweep.log"
FILES="tests/trait_system_tests.typort examples/theorem_proving.typort examples/typeclass_complex.typort examples/alu.typort"

echo "=== memory sweep started $(date) ===" > "$LOG"

run_one() {
    local ref="$1"
    echo ">>> $ref" >> "$LOG"
    git checkout -q "$ref" 2>>"$LOG" || { echo "CHECKOUT FAILED: $ref" >> "$LOG"; return; }
    git log -1 --format='%h %ci %s' "$ref" >> "$LOG"
    cargo build --release --bin typort 2>&1 | tail -2 >> "$LOG"
    powershell -File tools/measure_peak.ps1 "target/release/typort.exe" check $FILES >> "$LOG"
    echo "" >> "$LOG"
}

run_one HEAD
for c in c81bec9 b775cb0 b3e3ee4 6697c06 ee8dbf6 f1ad00d eca3a45; do
    run_one "$c"
done
git checkout -q master
echo "=== memory sweep finished $(date) ===" >> "$LOG"
