#!/usr/bin/env bash
# L02 deterministic memory baseline via `l02l05mem --chapter L02`.
#
# This is NOT a timing run: it counts allocations / bytes (the counter is exact
# and should be bit-identical between runs), so it does NOT take the bench lock.
# Do not run it while a teammate is timing on cpu7 if it needs a big compile --
# the binary is prebuilt here, and the run itself is short.
#
# Semantics (see src/bin/l02l05mem.rs header):
#   fast(one-shot)  = full per-round footprint (arena chunks + Machine buffers + scratch)
#   fast_ss growth  = first round with a reused Tycker -- steady-state resident lower bound
#   fast_ss churn   = per-round NEW allocations after Bump::reset (true churn)
#   basic           = Box/Rc reference impl per-node counts
#
# Usage:
#   tools/perf-l02/run_mem.sh                       # church,conv,conv_dup,dup,dup_deep @ k=11
#   WORKLOADS=church,dup K=13 ROUNDS=3 tools/perf-l02/run_mem.sh
#   REPEAT=2 tools/perf-l02/run_mem.sh              # two runs for determinism proof
set -euo pipefail

cd "$(dirname "$0")/../.."
ROOT="$PWD"
BIN="${BIN:-$ROOT/target/release/l02l05mem}"
RAW_DIR="${RAW_DIR:-$ROOT/docs/perf-l02/raw}"
CHAPTER="${CHAPTER:-L02}"
WORKLOADS="${WORKLOADS:-church,conv,conv_dup,dup,dup_deep}"
K="${K:-11}"
ROUNDS="${ROUNDS:-3}"
REPEAT="${REPEAT:-1}"
NO_BASIC="${NO_BASIC:-0}"

[[ -x "$BIN" ]] || { echo "ERROR: $BIN missing -- run: cargo build --release --bin l02l05mem" >&2; exit 1; }
mkdir -p "$RAW_DIR"
TS="$(date +%Y%m%d-%H%M%S)"
TAG="${CHAPTER}_mem_k${K}_w$(echo "$WORKLOADS" | tr ',' '-')"
OUT="$RAW_DIR/${TS}_${TAG}.txt"

ARGS=(--chapter "$CHAPTER" --workload "$WORKLOADS" --k "$K" --rounds "$ROUNDS")
(( NO_BASIC )) && ARGS+=(--no-basic)

{
  echo "timestamp_utc: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "binary: $BIN"
  echo "binary_sha256: $(sha256sum "$BIN" | cut -d' ' -f1)"
  echo "cmd: $BIN ${ARGS[*]}"
  echo "repeat: $REPEAT"
  echo
} > "$OUT"

i=1
while (( i <= REPEAT )); do
  echo "########## run $i/$REPEAT ##########"
  "$BIN" "${ARGS[@]}"
  i=$((i + 1))
done | tee -a "$OUT"

echo
echo "raw: $OUT"
