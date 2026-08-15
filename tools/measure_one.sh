#!/bin/bash
# Measure one commit: stable 4-file workload peak WS + trait_system_tests panic probe.
# Usage: bash tools/measure_one.sh <ref>
set -u
cd "$(dirname "$0")/.." || exit 1
REF="$1"
git checkout -q "$REF" || { echo "CHECKOUT FAILED: $REF"; exit 1; }
git log -1 --format='%h %ci %s' "$REF"
cargo build --release --bin typort 2>&1 | tail -1
powershell -File tools/measure_peak.ps1 "target/release/typort.exe" check examples/theorem_proving.typort examples/typeclass_complex.typort examples/alu.typort examples/hdl_ops.typort
./target/release/typort.exe check tests/trait_system_tests.typort >/dev/null 2>err_tst.txt
echo "TST_STABLE exit=$? panic=$(grep -c panicked err_tst.txt)"
