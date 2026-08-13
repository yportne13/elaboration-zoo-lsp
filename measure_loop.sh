#!/usr/bin/env bash
# Measure --release `typort check` wall time for each examples/hdl/*.typort.
# Runs each file N times, reports the minimum "change" time plus wall time.
# Usage: bash measure_loop.sh [runs] [glob]
set -u
cd "$(dirname "$0")"
RUNS="${1:-3}"
GLOB="${2:-examples/hdl/*.typort}"
BIN=./target/release/typort.exe
[ -x "$BIN" ] || BIN=./target/release/typort

printf "%-28s %8s %8s %8s\n" "file" "min_s" "med_s" "wall_min_s"
for f in $GLOB; do
    [ -f "$f" ] || continue
    declare -a times=()
    wallbest=9999
    for i in $(seq 1 "$RUNS"); do
        t0=$(date +%s.%N)
        out=$("$BIN" check "$f" 2>&1)
        rc=$?
        t1=$(date +%s.%N)
        wall=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.3f", b-a}')
        chg=$(echo "$out" | grep -oE "change [0-9.]+$" | tail -1 | awk '{print $2}')
        if [ -z "$chg" ]; then
            chg="ERR($rc)"
            times+=("9999")
        else
            times+=("$chg")
        fi
        wallbest=$(awk -v w="$wall" -v b="$wallbest" 'BEGIN{print (w<b)?w:b}')
    done
    sorted=$(printf '%s\n' "${times[@]}" | sort -n)
    minv=$(echo "$sorted" | head -1)
    medv=$(echo "$sorted" | sed -n "$(( (RUNS+1)/2 ))p")
    printf "%-28s %8s %8s %8s\n" "$(basename "$f")" "$minv" "$medv" "$wallbest"
done
