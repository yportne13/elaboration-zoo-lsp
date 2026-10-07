#!/usr/bin/env bash
# exp-mem-run.sh -- task-8 deterministic allocation evidence for the built-in
# L02 ablation switches, via `l02l05mem` (counting global allocator).
#
# Counts are exact and bit-reproducible, so this is the only zero-noise metric on
# this box (no PMU: perf_event_open is EACCES).  It is NOT a timing run, but it
# takes the same bench lock anyway: it is a single-thread CPU load and would
# otherwise perturb a teammate's timing window on cpu7.
#
# For each env setting x workload x k it runs `l02l05mem --chapter L02
# --workload W --k K --rounds R --no-basic` REPEAT times and stores every run in
# one file, then verifies the repeats are textually identical (determinism
# proof).  `--no-basic` skips the Box/Rc reference impl (not needed here).
#
# Env settings default to the ablation matrix plus two semantics probes:
#   -                 default
#   L02_NO_BITEQ=1    bit-equality fast path + inline chain pruning OFF
#   L02_NO_CONV_MEMO=1 conv worksheet equality memo OFF
#   L02_NO_BITEQ=0    MUST behave exactly like default  (is_ok_and(v != "0"))
#   L02_NO_BITEQ=     empty value MUST behave like =1  (present and != "0")
#
# Usage:
#   docs/perf-l02/raw/exp-mem-run.sh --tag ablate --workloads conv,conv_dup --ks 13,15
#   docs/perf-l02/raw/exp-mem-run.sh --tag ablate --envs '-,L02_NO_BITEQ=1' --rounds 3
set -euo pipefail

cd "$(dirname "$0")/../../.."
ROOT="$PWD"
BIN="${BIN:-$ROOT/target/release/l02l05mem}"
LOCK="$ROOT/docs/perf-l02/.benchlock"
RAW_DIR="${RAW_DIR:-$ROOT/docs/perf-l02/raw}"

TAG="mem"
WORKLOADS="conv,conv_dup"
KS="13,15"
ENVS=("-" "L02_NO_BITEQ=1" "L02_NO_CONV_MEMO=1" "L02_NO_BITEQ=0" "L02_NO_BITEQ=")
ROUNDS=3
REPEAT=2
CPU=7
DRYRUN=0
WAIT_S=10
MAX_WAIT=1800

usage() { sed -n '2,26p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tag)        TAG="$2"; shift 2 ;;
    --workloads)  WORKLOADS="$2"; shift 2 ;;
    --ks)         KS="$2"; shift 2 ;;
    --envs)       IFS=',' read -r -a ENVS <<<"$2"; shift 2 ;;
    --rounds)     ROUNDS="$2"; shift 2 ;;
    --repeat)     REPEAT="$2"; shift 2 ;;
    --cpu)        CPU="$2"; shift 2 ;;
    --dry-run)    DRYRUN=1; shift ;;
    --help|-h)    usage 0 ;;
    *) echo "unknown arg: $1" >&2; usage 2 ;;
  esac
done
mkdir -p "$RAW_DIR"
TS="$(date +%Y%m%d-%H%M%S)"
PREFIX="exp-${TS}_${TAG}"

envlabel() {
  local s="$1"
  if [[ "$s" == "-" ]]; then echo default
  elif [[ "$s" == *= ]]; then echo "${s%=}-empty"
  else echo "$s"; fi
}

if (( DRYRUN )); then
  for w in ${WORKLOADS//,/ }; do
    for k in ${KS//,/ }; do
      for e in "${ENVS[@]}"; do
        extra=""; [[ "$e" != "-" ]] && extra="$e "
        for r in $(seq 1 "$REPEAT"); do
          printf 'taskset -c %s env %s%s --chapter L02 --workload %s --k %s --rounds %s --no-basic\n' \
            "$CPU" "$extra" "$BIN" "$w" "$k" "$ROUNDS"
        done
      done
    done
  done
  exit 0
fi

[[ -x "$BIN" ]] || { echo "ERROR: $BIN missing -- cargo build --release --bin l02l05mem" >&2; exit 1; }

# ------------------------------------------------------------- exclusive lock
holder_alive() {
  local pid="$1"
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  [[ -d "/proc/$pid" ]] || return 1
  tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null \
    | grep -qE 'l02bench|l02l05mem|run_bench|exp-ab|exp-mem|bench|python|cargo|rustc|bash|dash|busybox|sh' || return 1
  return 0
}
acquired=0; waited=0
while (( waited <= MAX_WAIT )); do
  if mkdir "$LOCK" 2>/dev/null; then acquired=1; echo "$$" > "$LOCK/pid"; break; fi
  holder="$(cat "$LOCK/pid" 2>/dev/null || echo unknown)"
  if ! holder_alive "$holder"; then
    echo "benchlock stale (pid=$holder gone); taking over" >&2
    rm -f "$LOCK/pid"; rmdir "$LOCK" 2>/dev/null || true
    waited=$((waited + 1)); continue
  fi
  echo "benchlock held by live pid=$holder; sleeping ${WAIT_S}s (waited ${waited}s)" >&2
  sleep "$WAIT_S"; waited=$((waited + WAIT_S))
done
(( acquired )) || { echo "ERROR: could not acquire $LOCK within ${MAX_WAIT}s" >&2; exit 1; }
release() { rm -f "$LOCK/pid"; rmdir "$LOCK" 2>/dev/null || true; }
trap release EXIT INT TERM

FILES=()
for w in ${WORKLOADS//,/ }; do
  for k in ${KS//,/ }; do
    for e in "${ENVS[@]}"; do
      lbl="$(envlabel "$e")"
      out="$RAW_DIR/${PREFIX}_${lbl}_${w}_k${k}.txt"
      {
        echo "# env_spec: $e"
        echo "# cmd: taskset -c $CPU $BIN --chapter L02 --workload $w --k $k --rounds $ROUNDS --no-basic"
        echo "# binary_sha256: $(sha256sum "$BIN" | cut -d' ' -f1)"
      } > "$out"
      extra=(); [[ "$e" != "-" ]] && extra=("$e")
      for r in $(seq 1 "$REPEAT"); do
        echo "## run $r" >> "$out"
        set +e
        taskset -c "$CPU" env ${extra[@]+"${extra[@]}"} "$BIN" \
          --chapter L02 --workload "$w" --k "$k" --rounds "$ROUNDS" --no-basic >>"$out" 2>&1
        rc=$?
        set -e
        (( rc == 0 )) || echo "## run $r FAILED rc=$rc" >> "$out"
      done
      FILES+=("$out")
      echo "done: $(basename "$out")"
    done
  done
done

echo
echo "--- determinism check (repeat runs within each file must be identical) ---"
python3 - "${FILES[@]}" <<'PY'
import sys
bad = 0
for path in sys.argv[1:]:
    blocks, cur = [], None
    for line in open(path):
        if line.startswith("## run "):
            cur = []
            blocks.append(cur)
            continue
        if cur is not None:
            cur.append(line)
    if len(blocks) < 2:
        print(f"  {path}: only {len(blocks)} run block(s)")
        continue
    same = all(b == blocks[0] for b in blocks[1:])
    if not same:
        bad += 1
    print(f"  {'IDENTICAL' if same else 'DIFFERS  '} x{len(blocks)}  {path}")
print(f"determinism: {'ALL IDENTICAL' if bad == 0 else str(bad) + ' FILE(S) DIFFER'}")
sys.exit(1 if bad else 0)
PY
echo
echo "prefix: $PREFIX"
