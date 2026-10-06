#!/usr/bin/env bash
# L01 NBE reproducible timing harness for this aarch64 / big.LITTLE box.
#
# Why this exists: this machine has no perf/valgrind/hyperfine, a `walt`
# governor whose actual frequency swings roughly 0.8-2.2 GHz, and no cgroup CPU
# quota -- wall-clock numbers from a single `l01bench` run are not a baseline.
# Protocol enforced here:
#   * every timing command pins to ONE fixed big core (default cpu7) via taskset;
#   * min-of-N whole-process repetitions (default N=7) -- not min-of-rounds
#     inside one process;
#   * exclusive timing via the shared lock dir docs/perf-l01/.benchlock
#     (mkdir = acquire, rm pid + rmdir = release, sleep 10 + retry otherwise;
#     stale locks from killed holders are taken over automatically);
#   * keep-alive spinner on the pinned core (default ON, SCHED_IDLE) so the
#     `walt` governor sits at a steady gear instead of 787 MHz idle -- this is
#     what makes min-of-N reproducible (see docs/perf-l01/00-baseline.md);
#   * raw stdout of every rep is kept under docs/perf-l01/raw/ with a timestamp.
#
# Usage:
#   tools/perf-l01/run_bench.sh --max-church 8000 --only bump_spine_iter,bump_spine
#   tools/perf-l01/run_bench.sh -w guest --reps 3 --rounds 5
#   tools/perf-l01/run_bench.sh -w dup --only bump_spine_iter,bump_spine_memo
#   tools/perf-l01/run_bench.sh --no-keepalive ...   # reproduce opportunistic mins
#
# Exit status: 0 if at least one rep succeeded, 1 otherwise.
set -euo pipefail

cd "$(dirname "$0")/../.."
ROOT="$PWD"
BIN="$ROOT/target/release/l01bench"
LOCK="$ROOT/docs/perf-l01/.benchlock"
RAW_DIR="${RAW_DIR:-$ROOT/docs/perf-l01/raw}"

MAX_CHURCH=8000
ROUNDS=3
REPS=7
ONLY=""
WORKLOAD=church
CPU=7
STACK_MB=128
TAG=""
SIZES=""
WAIT_S=10
# exp-ab may hold the lock for a full shadow build (~6 min, fresh deps + LTO)
# plus its A/B reps; waiting must outlast that, and a timed-out exit would just
# hand the lock back to nobody.  1800s covers the worst case observed.
MAX_WAIT=1800
# Keep-alive protocol (default ON): a SCHED_IDLE (fallback: nice 19) spinner is
# pinned to the same core for the whole locked window.  Without it `walt` leaves
# cpu7 at 787 MHz and a short bench rep catches an arbitrary governor gear; the
# same config then swings ~20% between batches.  Under the spinner the core sits
# at a steady 2246 MHz and batch-to-batch spread drops to ~1-8%, at the cost of
# ~18% slower absolute times (documented in docs/perf-l01/00-baseline.md).
# Disable with --no-keepalive only when reproducing the old opportunistic mins.
KEEPALIVE=1

usage() { sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --max-church|-n) MAX_CHURCH="$2"; shift 2 ;;
    --rounds|-r)     ROUNDS="$2"; shift 2 ;;
    --reps|-N)       REPS="$2"; shift 2 ;;
    --only)          ONLY="$2"; shift 2 ;;
    --workload|-w)   WORKLOAD="$2"; shift 2 ;;
    --cpu)           CPU="$2"; shift 2 ;;
    --stack-mb)      STACK_MB="$2"; shift 2 ;;
    --sizes)         SIZES="$2"; shift 2 ;;   # display filter, e.g. 4000,8000
    --tag)           TAG="$2"; shift 2 ;;
    --raw-dir)       RAW_DIR="$2"; shift 2 ;;
    --no-keepalive)  KEEPALIVE=0; shift ;;
    --keepalive)     KEEPALIVE=1; shift ;;
    --help|-h)       usage 0 ;;
    *) echo "unknown arg: $1" >&2; usage 2 ;;
  esac
done

[[ -x "$BIN" ]] || { echo "ERROR: $BIN missing -- run: cargo build --release --bin l01bench" >&2; exit 1; }
command -v taskset >/dev/null || { echo "ERROR: taskset not found" >&2; exit 1; }
mkdir -p "$RAW_DIR"

TS="$(date +%Y%m%d-%H%M%S)"
[[ -n "$TAG" ]] || TAG="${WORKLOAD}_n${MAX_CHURCH}"
BASE="$RAW_DIR/${TS}_${TAG}"
ENV_FILE="${BASE}_env.txt"

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
  echo "binary_sha256: $(sha256sum "$BIN" | cut -d' ' -f1)"
  echo "rustc: $(rustc --version 2>/dev/null || echo unknown)"
  echo "cargo_profile_release: $(sed -n '/\[profile.release\]/,/^\[/p' Cargo.toml | tr '\n' ' ' | sed 's/  */ /g')"
  echo "allocator: mimalloc (src/bin/l01bench.rs #[global_allocator])"
  echo "stack_mb: $STACK_MB (L01_STACK_MB env on the big-stack thread)"
  echo "cmd: taskset -c $CPU env L01_STACK_MB=$STACK_MB $BIN --max-church $MAX_CHURCH --rounds $ROUNDS${ONLY:+ --only $ONLY} --workload $WORKLOAD"
} | tee "$ENV_FILE"
echo

# ------------------------------------------------------------- exclusive lock
# Stale-lock self-healing: a killed/suspended holder leaves the dir behind (and
# the pid file makes a bare rmdir fail), which would wedge the whole team -- the
# lock is a cross-agent convention, not an OS lock.  If the holder pid is gone
# (or /proc/<pid> is not a shell/l01bench process) take the lock over; only a
# live holder is waited for.
holder_alive() {
  local pid="$1"
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  [[ -d "/proc/$pid" ]] || return 1
  # Any live bench/harness interpreter counts as a real holder; an unrelated
  # recycled pid (daemon etc.) is treated as stale.  Erring toward "live" is
  # safer: MAX_WAIT bounds the wait, stealing would corrupt someone's timing.
  tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null \
    | grep -qE 'l01bench|run_bench|bench|python|cargo|rustc|bash|dash|busybox|sh' || return 1
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
CMD=(taskset -c "$CPU" env "L01_STACK_MB=$STACK_MB" "$BIN"
     --max-church "$MAX_CHURCH" --rounds "$ROUNDS" --workload "$WORKLOAD")
[[ -n "$ONLY" ]] && CMD+=(--only "$ONLY")

rep_files=()
ok_reps=0
for i in $(seq 1 "$REPS"); do
  out="${BASE}_rep${i}.txt"
  echo "--- rep $i/$REPS -> $out" | tee -a "$BASE.log"
  set +e
  "${CMD[@]}" >"$out" 2>&1
  rc=$?
  set -e
  if (( rc == 0 )); then
    rep_files+=("$out"); ok_reps=$((ok_reps + 1))
  else
    echo "  rep $i FAILED rc=$rc (see $out)" | tee -a "$BASE.log"
    tail -5 "$out" | sed 's/^/    /' >&2 || true
  fi
done
echo "reps_ok: $ok_reps/$REPS" | tee -a "$BASE.log"

if (( ok_reps == 0 )); then
  echo "ERROR: all reps failed" >&2
  exit 1
fi

# ------------------------------------------------------------------ aggregate
AGG="${BASE}_agg.tsv"
python3 "$ROOT/tools/perf-l01/parse_bench.py" --tsv "${rep_files[@]}" > "$AGG"
echo

if [[ -n "$SIZES" ]]; then
  python3 - "$AGG" "$SIZES" <<'PY'
import sys
agg, sizes = sys.argv[1], {int(x) for x in sys.argv[2].split(",")}
lines = open(agg).read().splitlines()
print(lines[0])
for ln in lines[1:]:
    f = ln.split("\t")
    if int(f[1]) in sizes:
        print(ln)
PY
else
  cat "$AGG"
fi

echo
python3 "$ROOT/tools/perf-l01/parse_bench.py" "${rep_files[@]}"
echo
echo "raw: $ENV_FILE"
echo "agg: $AGG"
