#!/usr/bin/env bash
# L02 (`l02bench`) reproducible wall-clock timing harness for this
# aarch64 / big.LITTLE Termux box.
#
# Why this exists: no perf/valgrind/hyperfine, a `walt` governor whose actual
# frequency swings 0.79-2.25 GHz, and a benchmark whose default mode times all
# four implementations in ONE process (memory footprint evicts `fast_ss`'s big
# bump pool -> large-k mins are inflated).  This harness enforces the protocol
# that made L01 numbers reproducible on the same box (docs/perf-l01/00-baseline.md):
#   * pin every timing command to ONE fixed big core (default cpu7) via taskset;
#   * **`--only <one impl>` is mandatory** -- one implementation per process,
#     so the readme's full-run footprint contamination cannot happen.  The name
#     is validated against l02bench's four valid impls (basic / fast / fast_ss /
#     fast_memo) and a comma list is rejected;
#   * whole-process repetitions (default N=7) -- each rep is a fresh process, so
#     every (workload,k,impl) cell gets N independent per-process minima;
#   * aggregate = **median of the per-rep minima** (`med_of_min`).  `min` is an
#     extreme statistic that jumps ~20% when `walt` happens to be in a fast gear;
#     the median is the comparable quantity;
#   * exclusive timing via the shared lock dir docs/perf-l02/.benchlock
#     (mkdir = acquire, rm pid + rmdir = release, sleep 10 + retry otherwise;
#     stale locks from killed holders are taken over automatically);
#   * keep-alive spinner on the pinned core (default ON, SCHED_IDLE) so the
#     `walt` governor sits at a steady gear instead of 787 MHz idle;
#   * raw stdout of every rep kept under docs/perf-l02/raw/ with a timestamp,
#     plus an environment fingerprint (`*_env.txt`).
#
# Units: `l02bench` measures `Instant::elapsed().as_micros()` and prints
# `min/1000 . min%1000 ms` -- i.e. the printed number is **milliseconds with
# microsecond precision** (the literal `ms` suffix is in the stdout).  The
# parser (`parse_bench.py`) also accepts a `µs`/`us` suffix and converts to ms,
# so the harness stays correct either way.
#
# Usage:
#   tools/perf-l02/run_bench.sh --only fast --workload church --max-k 15
#   tools/perf-l02/run_bench.sh --only fast_ss -w conv_dup -k 15 -N 7 -r 5
#   tools/perf-l02/run_bench.sh --only basic -w church -k 13 --tag basic_church
#   tools/perf-l02/run_bench.sh --only fast -w church -k 13 -N 42 --tag nullab
#   tools/perf-l02/run_bench.sh --only fast,fast_ss --interleave -w church -N 21
#   tools/perf-l02/run_bench.sh --only fast --bin target/release/l02bench-exp ...
#   tools/perf-l02/run_bench.sh --no-keepalive ...   # reproduce opportunistic mins
#
# Exit status: 0 if at least one rep succeeded, 1 otherwise.
set -euo pipefail

cd "$(dirname "$0")/../.."
ROOT="$PWD"
BIN="${BIN:-$ROOT/target/release/l02bench}"
LOCK="$ROOT/docs/perf-l02/.benchlock"
RAW_DIR="${RAW_DIR:-$ROOT/docs/perf-l02/raw}"

MAX_K=15
ROUNDS=5
REPS=7
ONLY=""
WORKLOAD=church
CPU=7
STACK_MB=128
TAG=""
KS=""
WAIT_S=10
# l02-exp may hold the lock for a shadow release build plus its A/B reps;
# waiting must outlast that.  1800s covers the worst case observed in L01.
MAX_WAIT=1800
# Keep-alive protocol (default ON): a SCHED_IDLE (fallback: nice 19) spinner
# pinned to the same core for the whole locked window.  Without it `walt` leaves
# cpu7 at 787 MHz and a short rep catches an arbitrary governor gear.
KEEPALIVE=1
# Interleaved A/B (default OFF): `--only a,b --interleave` alternates the two
# impls process-by-process (ABBA) inside one locked window.
INTERLEAVE=0

usage() { sed -n '2,45p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --max-k|-k)      MAX_K="$2"; shift 2 ;;
    --rounds|-r)     ROUNDS="$2"; shift 2 ;;
    --reps|-N)       REPS="$2"; shift 2 ;;
    --only)          ONLY="$2"; shift 2 ;;
    --workload|-w)   WORKLOAD="$2"; shift 2 ;;
    --cpu)           CPU="$2"; shift 2 ;;
    --stack-mb)      STACK_MB="$2"; shift 2 ;;
    --ks)            KS="$2"; shift 2 ;;     # display filter, e.g. 11,13,15
    --tag)           TAG="$2"; shift 2 ;;
    --raw-dir)       RAW_DIR="$2"; shift 2 ;;
    --bin)           BIN="$2"; shift 2 ;;
    --interleave)    INTERLEAVE=1; shift ;;
    --no-keepalive)  KEEPALIVE=0; shift ;;
    --keepalive)     KEEPALIVE=1; shift ;;
    --help|-h)       usage 0 ;;
    *) echo "unknown arg: $1" >&2; usage 2 ;;
  esac
done

# ------------------------------------------------------- mandatory isolation
# The readme's own measurement-methodology section says cross-impl numbers from
# a single full run are contaminated; enforce one impl per *process* here.
# `--interleave --only a,b` is the ONE sanctioned exception: each process still
# runs a single impl, but the harness alternates A/B process-by-process
# (ABBA order) inside one locked window.  That is the only way to compare two
# impls on this box, because the clock gear drifts in ~20% blocks across a batch
# (see docs/perf-l02/00-baseline.md §3): a blocked A-then-B run carries a ~19%
# false-positive floor even with 21 reps/side.
[[ -n "$ONLY" ]] || { echo "ERROR: --only <impl> is mandatory (one impl per process; see readme 测量方法论)" >&2; exit 2; }
IFS=',' read -r -a ONLY_LIST <<< "$ONLY"
for _i in "${!ONLY_LIST[@]}"; do
  ONLY_LIST[_i]="${ONLY_LIST[_i]// /}"
  case "${ONLY_LIST[_i]}" in
    basic|fast|fast_ss|fast_memo) ;;
    *) echo "ERROR: unknown impl '${ONLY_LIST[_i]}' (valid: basic, fast, fast_ss, fast_memo)" >&2; exit 2 ;;
  esac
done
if (( INTERLEAVE )); then
  (( ${#ONLY_LIST[@]} >= 2 )) || { echo "ERROR: --interleave needs --only a,b (>=2 impls)" >&2; exit 2; }
else
  (( ${#ONLY_LIST[@]} == 1 )) || { echo "ERROR: --only takes exactly one impl; got '$ONLY' (use --interleave for an A/B, or separate invocations releasing the lock between them)" >&2; exit 2; }
fi
case "$WORKLOAD" in
  church|conv|conv_dup|dup|dup_deep) ;;
  *) echo "ERROR: unknown workload '$WORKLOAD'" >&2; exit 2 ;;
esac

[[ -x "$BIN" ]] || { echo "ERROR: $BIN missing -- run: cargo build --release --bin l02bench" >&2; exit 1; }
command -v taskset >/dev/null || { echo "ERROR: taskset not found" >&2; exit 1; }
mkdir -p "$RAW_DIR"

TS="$(date +%Y%m%d-%H%M%S)"
[[ -n "$TAG" ]] || TAG="${WORKLOAD}_${ONLY}_k${MAX_K}"
BASE="$RAW_DIR/${TS}_${TAG}"
ENV_FILE="${BASE}_env.txt"
LOG="${BASE}.log"

# ---------------------------------------------------------------- environment
cpu_line() { # $1 = cpu id, $2 = sysfs attr
  local p="/sys/devices/system/cpu/cpu$1/cpufreq/$2"
  [[ -r "$p" ]] && cat "$p" || echo "n/a"
}

{
  echo "timestamp_utc: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "kernel: $(uname -srmo)"
  echo "cpu_model: $(grep -m1 -iE 'model name|Hardware' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//' || echo unknown)"
  echo "cores_online: $(nproc)"
  for c in 0 4 7; do
    echo "cpu$c: max=$(cpu_line "$c" cpuinfo_max_freq)kHz cur=$(cpu_line "$c" scaling_cur_freq)kHz governor=$(cpu_line "$c" scaling_governor)"
  done
  echo "pinned_cpu: $CPU"
  echo "cpus_allowed: $(grep -m1 Cpus_allowed_list /proc/self/status | cut -f2)"
  echo "cgroup_cpu_max: $(cat /sys/fs/cgroup/cpu.max 2>/dev/null || echo n/a)"
  echo "loadavg_at_start: $(cat /proc/loadavg)"
  echo "binary: $BIN"
  echo "binary_size: $(stat -c %s "$BIN" 2>/dev/null || echo n/a)"
  echo "binary_mtime: $(stat -c %y "$BIN" 2>/dev/null || echo n/a)"
  echo "binary_sha256: $(sha256sum "$BIN" | cut -d' ' -f1)"
  echo "rustc: $(rustc --version 2>/dev/null || echo unknown)"
  echo "cargo_profile_release: $(sed -n '/\[profile.release\]/,/^\[/p' Cargo.toml | tr '\n' ' ' | sed 's/  */ /g')"
  echo "allocator: mimalloc (src/bin/l02bench.rs #[global_allocator])"
  echo "stack_mb: $STACK_MB (L02_STACK_MB env on the big-stack thread)"
  echo "isolation: --only $ONLY (one impl per process, mandatory)"
  echo "cmd: taskset -c $CPU env L02_STACK_MB=$STACK_MB $BIN --max-k $MAX_K --rounds $ROUNDS --only $ONLY --workload $WORKLOAD"
} | tee "$ENV_FILE"
echo

# ------------------------------------------------------------- exclusive lock
# Stale-lock self-healing: a killed/suspended holder leaves the dir behind (and
# the pid file makes a bare rmdir fail), which would wedge the whole team -- the
# lock is a cross-agent convention, not an OS lock.  If the holder pid is gone
# take the lock over; only a live holder is waited for.
holder_alive() {
  local pid="$1"
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  [[ -d "/proc/$pid" ]] || return 1
  tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null \
    | grep -qE 'l02bench|l02l05mem|run_bench|bench|python|cargo|rustc|bash|dash|busybox|sh' || return 1
  return 0
}
acquired=0
waited=0
while (( waited <= MAX_WAIT )); do
  if mkdir "$LOCK" 2>/dev/null; then
    acquired=1
    echo "$$" > "$LOCK/pid"
    break
  fi
  holder="$(cat "$LOCK/pid" 2>/dev/null || echo unknown)"
  if ! holder_alive "$holder"; then
    echo "benchlock stale (pid=$holder gone); taking over" >&2
    rm -f "$LOCK/pid"
    rmdir "$LOCK" 2>/dev/null || true
    waited=$((waited + 1))   # guard against a tight retry loop
    continue
  fi
  echo "benchlock held by live pid=$holder; sleeping ${WAIT_S}s (waited ${waited}s)" >&2
  sleep "$WAIT_S"
  waited=$((waited + WAIT_S))
done
if (( acquired == 0 )); then
  echo "ERROR: could not acquire $LOCK within ${MAX_WAIT}s" >&2
  exit 1
fi
# The pid file makes a bare `rmdir` fail, so release must remove it first --
# otherwise every abnormal exit would leak the lock.
SPIN_PID=""
release() {
  if [[ -n "$SPIN_PID" ]]; then
    kill "$SPIN_PID" 2>/dev/null || true
    SPIN_PID=""
  fi
  rm -f "$LOCK/pid"
  rmdir "$LOCK" 2>/dev/null || true
}
trap release EXIT INT TERM

if (( KEEPALIVE )); then
  if command -v chrt >/dev/null 2>&1; then
    chrt -i 0 taskset -c "$CPU" sh -c 'while :; do :; done' &
    KEEPALIVE_MODE="sched_idle"
  else
    nice -n 19 taskset -c "$CPU" sh -c 'while :; do :; done' &
    KEEPALIVE_MODE="nice19"
  fi
  SPIN_PID=$!
  sleep 1   # let the governor reach its sustained gear before the first rep
  echo "keepalive: $KEEPALIVE_MODE spinner pid=$SPIN_PID on cpu$CPU; cpu$CPU freq=$(cpu_line "$CPU" scaling_cur_freq)kHz"
else
  KEEPALIVE_MODE="off"
  echo "keepalive: off (opportunistic governor gear)"
fi
echo "keepalive_mode: $KEEPALIVE_MODE" >> "$ENV_FILE"

# ---------------------------------------------------------------- rep N times
# In interleave mode `--reps N` means N reps PER SIDE; the two impls alternate
# process-by-process in ABBA order so a drifting clock gear hits both arms
# equally (a blocked A-then-B run carries a ~19% false-positive floor here).
run_one() { # $1 = impl, $2 = stdout path
  taskset -c "$CPU" env "L02_STACK_MB=$STACK_MB" "$BIN" \
    --max-k "$MAX_K" --rounds "$ROUNDS" --workload "$WORKLOAD" --only "$1" >"$2" 2>&1
}

declare -A ARM_FILES=()
rep_files=()
ok_reps=0
if (( INTERLEAVE == 0 )); then
  for i in $(seq 1 "$REPS"); do
    out="${BASE}_rep${i}.txt"
    echo "--- rep $i/$REPS -> $out" | tee -a "$LOG"
    set +e; run_one "${ONLY_LIST[0]}" "$out"; rc=$?; set -e
    if (( rc == 0 )); then
      rep_files+=("$out"); ok_reps=$((ok_reps + 1))
    else
      echo "  rep $i FAILED rc=$rc (see $out)" | tee -a "$LOG"
      tail -5 "$out" | sed 's/^/    /' >&2 || true
    fi
  done
else
  for i in $(seq 1 "$REPS"); do
    if (( i % 2 == 1 )); then
      order=("${ONLY_LIST[@]}")
    else
      order=(); for ((j=${#ONLY_LIST[@]}-1; j>=0; j--)); do order+=("${ONLY_LIST[j]}"); done
    fi
    for impl in "${order[@]}"; do
      out="${BASE}_${impl}_rep${i}.txt"
      echo "--- rep $i/$REPS $impl -> $out" | tee -a "$LOG"
      set +e; run_one "$impl" "$out"; rc=$?; set -e
      if (( rc == 0 )); then
        ARM_FILES[$impl]+=" $out"; rep_files+=("$out"); ok_reps=$((ok_reps + 1))
      else
        echo "  rep $i $impl FAILED rc=$rc (see $out)" | tee -a "$LOG"
        tail -5 "$out" | sed 's/^/    /' >&2 || true
      fi
    done
  done
fi
echo "reps_ok: $ok_reps/$(( INTERLEAVE ? REPS * ${#ONLY_LIST[@]} : REPS ))" | tee -a "$LOG"

if (( ok_reps == 0 )); then
  echo "ERROR: all reps failed" >&2
  exit 1
fi
if (( INTERLEAVE )); then
  for impl in "${ONLY_LIST[@]}"; do
    [[ -n "${ARM_FILES[$impl]:-}" ]] || { echo "ERROR: no successful reps for $impl" >&2; exit 1; }
  done
fi

# ------------------------------------------------------------------ aggregate
AGG="${BASE}_agg.tsv"
python3 "$ROOT/tools/perf-l02/parse_bench.py" --tsv "${rep_files[@]}" > "$AGG"
echo

if [[ -n "$KS" ]]; then
  python3 - "$AGG" "$KS" <<'PY'
import sys
agg, ks = sys.argv[1], {int(x) for x in sys.argv[2].split(",")}
lines = open(agg).read().splitlines()
print(lines[0])
for ln in lines[1:]:
    f = ln.split("\t")
    if len(f) > 1 and int(f[1]) in ks:
        print(ln)
PY
else
  cat "$AGG"
fi

echo
python3 "$ROOT/tools/perf-l02/parse_bench.py" "${rep_files[@]}"

if (( INTERLEAVE )); then
  echo
  for impl in "${ONLY_LIST[@]}"; do
    read -r -a _ff <<< "${ARM_FILES[$impl]}"
    python3 "$ROOT/tools/perf-l02/parse_bench.py" --tsv "${_ff[@]}" > "${BASE}_${impl}_agg.tsv"
  done
  echo "=== interleaved A/B (ABBA, $REPS reps/side) ==="
  for impl in "${ONLY_LIST[@]}"; do
    read -r -a _ff <<< "${ARM_FILES[$impl]}"
    if [[ "$impl" == "${ONLY_LIST[0]}" ]]; then A_FILES=("${_ff[@]}"); else B_FILES=("${_ff[@]}"); fi
  done
  AGG_ARGS=(--a "${A_FILES[@]}" --b "${B_FILES[@]}" --impl-a "${ONLY_LIST[0]}" --impl-b "${ONLY_LIST[1]}")
  [[ -n "$KS" ]] && AGG_ARGS+=(--ks "$KS")
  python3 "$ROOT/tools/perf-l02/ab_report.py" "${AGG_ARGS[@]}"
fi

echo
echo "raw: $ENV_FILE"
echo "agg: $AGG"
