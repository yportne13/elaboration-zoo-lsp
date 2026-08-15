#!/bin/bash
# Measure a list of commits: 2-file stable workload peak + trait_system_tests probe.
# Usage: bash tools/measure_range.sh <ref1> <ref2> ...
set -u
cd "$(dirname "$0")/.." || exit 1
for REF in "$@"; do
    echo ">>> $REF"
    git checkout -q "$REF" || { echo "CHECKOUT FAILED: $REF"; continue; }
    git log -1 --format='%h %ci %s' "$REF"
    cargo build --release --bin typort 2>&1 | tail -1
    powershell -File tools/measure_peak.ps1 "target/release/typort.exe" check examples/theorem_proving.typort examples/typeclass_complex.typort
    ./target/release/typort.exe check examples/theorem_proving.typort >/dev/null 2>err_probe.txt
    echo "PROBE_STABLE exit=$? panic=$(grep -c panicked err_probe.txt)"
    ./target/release/typort.exe check tests/trait_system_tests.typort >/dev/null 2>err_probe2.txt
    echo "PROBE_TST exit=$? panic=$(grep -c panicked err_probe2.txt)"
    echo ""
done
git checkout -q master
