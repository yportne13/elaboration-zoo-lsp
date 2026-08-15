#!/usr/bin/env bash
# Automated bisect driver for the l13 perf regression (01-basics / 02-arithmetic).
# `git bisect run` invokes this with cwd = the worktree root where bisect started,
# so this script must NOT cd anywhere else.
set -e

build() {
    cargo build --release --bin typort >/dev/null 2>&1
}

measure() {
    local f="$1" best=999 t
    for i in 1 2 3; do
        t=$(./target/release/typort.exe check "$f" 2>&1 | grep -oP 'change \K[0-9.]+' | tail -1)
        [ -n "$t" ] && best=$(echo "$t $best" | awk '{print ($1<$2)?$1:$2}')
    done
    echo "$best"
}

if ! build; then
    echo "BUILD FAILED"
    exit 125
fi

b1=$(measure examples/hdl/01-basics.typort)
b2=$(measure examples/hdl/02-arithmetic.typort)
echo "01-basics=$b1 02-arithmetic=$b2"

# Classify by geometric mean. perf1-era baselines: 0.080 / 0.347; master: 0.253 / 1.052.
# Midpoint of the two states (log scale): gm_mid = sqrt(0.14 * 0.60) ~= 0.29.
# awk does sqrt; no bc dependency.
read gm mid <<EOF
$(awk -v a="$b1" -v b="$b2" 'BEGIN { printf "%.4f %.4f", sqrt(a*b), sqrt(0.14*0.60) }')
EOF
echo "gm=$gm mid=$mid"
if [ "$(awk -v g="$gm" -v m="$mid" 'BEGIN { print (g < m) ? "1" : "0" }')" = "1" ]; then
    echo "GOOD"
    exit 0
else
    echo "BAD"
    exit 1
fi
