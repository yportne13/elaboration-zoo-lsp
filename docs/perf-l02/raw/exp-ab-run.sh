#!/usr/bin/env bash
# exp-ab-run.sh -- task-8 interleaved A/B + same-batch null control driver.
#
# WHY THIS EXISTS: tools/perf-l02/run_bench.sh runs ONE configuration per
# invocation (21 reps of A, then 21 reps of B in a second invocation).  On this
# box that "blocked A-then-B" shape carries a ~19% false-positive floor (walt
# gear autocorrelation, measured in task-6); only a same-batch interleave with a
# same-batch null control is usable.  This driver therefore takes the bench lock
# ONCE and inside that window runs, per segment, strictly interleaved
# A1 B1 A2 B2 ... reps of a fresh l02bench process.
#
# Segments (see docs/perf-l02/raw/exp-8-plan.md):
#   nullA : side nA1 vs nA2, BOTH with env A / bin A -> this batch's noise floor
#   ab    : side A   vs B,   env A vs env B, bin A vs bin B -> the experiment
#   nullB : side nB1 vs nB2, BOTH with env B / bin B -> floor in the B setting
# The pair's two sides run adjacent in time and their order alternates by pair
# parity (--order-fixed disables), so first-position and slow-drift effects are
# baked into the null floors as well and the comparison stays apples-to-apples.
# Cross-binary A/B (task-9): --bin-a/--bin-b point the two sides at different
# l02bench builds (nullA then measures the A binary's own floor, nullB the B's).
#
# Lock protocol: identical to run_bench.sh (mkdir acquire + pid file, stale-pid
# takeover, release = rm -f pid then rmdir).  keep-alive spinner on the pinned
# core, SCHED_IDLE via chrt (nice -n 19 fallback).
#
# Usage:
#   docs/perf-l02/raw/exp-ab-run.sh --tag conv_biteq -w conv \
#       --env-a - --env-b L02_NO_BITEQ=1 --reps 21
#   docs/perf-l02/raw/exp-ab-run.sh --tag conv_dup_memo -w conv_dup \
#       --env-a - --env-b L02_NO_CONV_MEMO=1 --segs nullA,ab,nullB
#   docs/perf-l02/raw/exp-ab-run.sh --tag c1_church -w church --env-a - --env-b - \
#       --bin-a /tmp/l02-exp/l02bench-base --bin-b /tmp/l02-exp/l02bench-c1 --reps 42
#   docs/perf-l02/raw/exp-ab-run.sh ... --dry-run    # print commands, no lock/run
#
# Other knobs: --rounds-b N (per-arm --rounds), --max-k, --only, --cpu, --stack-mb.
# env spec syntax: "-" (unset) or "NAME=VALUE" (exactly one var, like run_bench).
set -euo pipefail

cd "$(dirname "$0")/../../.."
ROOT="$PWD"
BIN="${BIN:-$ROOT/target/release/l02bench}"
BIN_A="$BIN"
BIN_B="$BIN"
LOCK="$ROOT/docs/perf-l02/.benchlock"
RAW_DIR="${RAW_DIR:-$ROOT/docs/perf-l02/raw}"

TAG=""
WORKLOAD="conv"
MAX_K=15
ROUNDS=5
ROUNDS_B=""
REPS=21
ONLY=fast
ENV_A="-"
ENV_B="L02_NO_BITEQ=1"
SEGS="nullA,ab,nullB"
CPU=7
STACK_MB=128
DRYRUN=0
ORDER_ALT=1
WAIT_S=10
MAX_WAIT=1800

usage() { sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

while [[ $# -gt 0 ]]; do
  case "$1" in
    --tag)        TAG="$2"; shift 2 ;;
    --workload|-w) WORKLOAD="$2"; shift 2 ;;
    --max-k|-k)   MAX_K="$2"; shift 2 ;;
    --rounds|-r)  ROUNDS="$2"; shift 2 ;;
    --rounds-b)   ROUNDS_B="$2"; shift 2 ;;
    --reps|-N)    REPS="$2"; shift 2 ;;
    --only)       ONLY="$2"; shift 2 ;;
    --env-a)      ENV_A="$2"; shift 2 ;;
    --env-b)      ENV_B="$2"; shift 2 ;;
    --bin-a)      BIN_A="$2"; shift 2 ;;
    --bin-b)      BIN_B="$2"; shift 2 ;;
    --segs)       SEGS="$2"; shift 2 ;;
    --cpu)        CPU="$2"; shift 2 ;;
    --stack-mb)   STACK_MB="$2"; shift 2 ;;
    --order-fixed) ORDER_ALT=0; shift ;;
    --dry-run)    DRYRUN=1; shift ;;
    --help|-h)    usage 0 ;;
    *) echo "unknown arg: $1" >&2; usage 2 ;;
  esac
done
[[ -n "$ROUNDS_B" ]] || ROUNDS_B="$ROUNDS"

[[ -n "$TAG" ]] || { echo "ERROR: --tag is required (raw file prefix)" >&2; exit 2; }
case "$WORKLOAD" in church|conv|conv_dup|dup|dup_deep) ;; *) echo "ERROR: bad workload $WORKLOAD" >&2; exit 2 ;; esac
case "$ONLY" in basic|fast|fast_ss|fast_memo) ;; *) echo "ERROR: bad --only $ONLY" >&2; exit 2 ;; esac
for s in ${SEGS//,/ }; do
  case "$s" in nullA|ab|nullB) ;; *) echo "ERROR: bad segment '$s' (nullA|ab|nullB)" >&2; exit 2 ;; esac
done
for spec in "$ENV_A" "$ENV_B"; do
  [[ "$spec" == "-" || "$spec" =~ ^[A-Za-z_][A-Za-z0-9_]*=.*$ ]] \
    || { echo "ERROR: env spec must be '-' or NAME=VALUE (got '$spec')" >&2; exit 2; }
done
mkdir -p "$RAW_DIR"

TS="$(date +%Y%m%d-%H%M%S)"
PREFIX="exp-${TS}_${TAG}"
SPEC_FILE="$RAW_DIR/${PREFIX}_spec.txt"

# ---------------------------------------------------------------- segment map
declare -A ARM_ENV=()
seg_arms() {
  case "$1" in
    nullA) echo "nA1 nA2" ;;
    ab)    echo "A B" ;;
    nullB) echo "nB1 nB2" ;;
  esac
}
for s in ${SEGS//,/ }; do
  read -r a1 a2 <<<"$(seg_arms "$s")"
  case "$s" in
    nullA) ARM_ENV[$a1]="$ENV_A"; ARM_ENV[$a2]="$ENV_A" ;;
    ab)    ARM_ENV[$a1]="$ENV_A"; ARM_ENV[$a2]="$ENV_B" ;;
    nullB) ARM_ENV[$a1]="$ENV_B"; ARM_ENV[$a2]="$ENV_B" ;;
  esac
done

# Per-arm in-process round count.  Route (c) for the walt gear problem: a
# bigger --rounds makes each rep's reported min cross gear boundaries; arms
# carrying env B use --rounds-b (default = --rounds).
arm_rounds() {
  case "$1" in
    B|nB1|nB2) echo "$ROUNDS_B" ;;
    *)         echo "$ROUNDS" ;;
  esac
}
# Per-arm binary (cross-binary A/B: shadow A' vs patched C1/C2); arms carrying
# env B also carry BIN_B.
arm_bin() {
  case "$1" in
    B|nB1|nB2) echo "$BIN_B" ;;
    *)         echo "$BIN_A" ;;
  esac
}
ORDER_STR=$([[ $ORDER_ALT == 1 ]] && echo alternate || echo fixed)

echo "tag:        $TAG"
echo "binary A:   $BIN_A"
echo "binary B:   $BIN_B"
echo "workload:   $WORKLOAD  max_k=$MAX_K rounds=$ROUNDS (b-side=$ROUNDS_B) reps/side=$REPS only=$ONLY order=$ORDER_STR"
echo "segments:   $SEGS"
for s in ${SEGS//,/ }; do
  read -r a1 a2 <<<"$(seg_arms "$s")"
  echo "  $s: $a1(env=${ARM_ENV[$a1]} rounds=$(arm_rounds "$a1") bin=$(basename "$(arm_bin "$a1")")) vs $a2(env=${ARM_ENV[$a2]} rounds=$(arm_rounds "$a2") bin=$(basename "$(arm_bin "$a2")"))"
done
echo "prefix:     $PREFIX"

# ---------------------------------------------------------------- dry run
if (( DRYRUN )); then
  echo
  echo "--- dry run: commands that WOULD run inside one locked window ---"
  for s in ${SEGS//,/ }; do
    read -r a1 a2 <<<"$(seg_arms "$s")"
    for i in $(seq 1 "$REPS"); do
      if (( ORDER_ALT )) && (( i % 2 == 0 )); then order=("$a2" "$a1"); else order=("$a1" "$a2"); fi
      for arm in "${order[@]}"; do
        spec="${ARM_ENV[$arm]}"
        envpart=""; [[ "$spec" != "-" ]] && envpart="$spec "
        printf 'taskset -c %s env L02_STACK_MB=%s %s%s --max-k %s --rounds %s --workload %s --only %s > %s\n' \
          "$CPU" "$STACK_MB" "$envpart" "$(arm_bin "$arm")" "$MAX_K" "$(arm_rounds "$arm")" \
          "$WORKLOAD" "$ONLY" "$RAW_DIR/${PREFIX}_${arm}_rep${i}.txt"
      done
    done
  done
  exit 0
fi

for b in "$BIN_A" "$BIN_B"; do
  [[ -x "$b" ]] || { echo "ERROR: $b missing -- cargo build --release --bin l02bench" >&2; exit 1; }
done
command -v taskset >/dev/null || { echo "ERROR: taskset not found" >&2; exit 1; }

# ------------------------------------------------------------- env fingerprint
{
  echo "timestamp_utc: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "kernel: $(uname -srmo)"
  echo "cores_online: $(nproc)"
  for c in 0 4 7; do
    p="/sys/devices/system/cpu/cpu$c/cpufreq"; 
    echo "cpu$c: max=$(cat $p/cpuinfo_max_freq 2>/dev/null || echo n/a)kHz cur=$(cat $p/scaling_cur_freq 2>/dev/null || echo n/a) governor=$(cat $p/scaling_governor 2>/dev/null || echo n/a)"
  done
  echo "pinned_cpu: $CPU  stack_mb: $STACK_MB  keepalive: sched_idle"
  echo "binary_a: $BIN_A"
  echo "binary_a_sha256: $(sha256sum "$BIN_A" | cut -d' ' -f1)"
  echo "binary_b: $BIN_B"
  echo "binary_b_sha256: $(sha256sum "$BIN_B" | cut -d' ' -f1)"
  echo "binary_mtime: $(stat -c %y "$BIN_A")"
  echo "rustc: $(rustc --version 2>/dev/null || echo unknown)"
  echo "workload: $WORKLOAD  max_k: $MAX_K  rounds: $ROUNDS (b-side: $ROUNDS_B)  only: $ONLY  reps_per_side: $REPS  order: $ORDER_STR"
  echo "segments: $SEGS"
  for s in ${SEGS//,/ }; do
    read -r a1 a2 <<<"$(seg_arms "$s")"
    echo "  $s: $a1 env=${ARM_ENV[$a1]} | $a2 env=${ARM_ENV[$a2]}"
  done
} | tee "$RAW_DIR/${PREFIX}_env.txt"
echo

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
  if mkdir "$LOCK" 2>/dev/null; then
    acquired=1; echo "$$" > "$LOCK/pid"; break
  fi
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

SPIN_PID=""
release() {
  if [[ -n "$SPIN_PID" ]]; then kill "$SPIN_PID" 2>/dev/null || true; SPIN_PID=""; fi
  rm -f "$LOCK/pid"; rmdir "$LOCK" 2>/dev/null || true
}
trap release EXIT INT TERM

if command -v chrt >/dev/null 2>&1; then
  chrt -i 0 taskset -c "$CPU" sh -c 'while :; do :; done' &
  KA_MODE="sched_idle"
else
  nice -n 19 taskset -c "$CPU" sh -c 'while :; do :; done' &
  KA_MODE="nice19"
fi
SPIN_PID=$!
sleep 1
echo "keepalive: $KA_MODE spinner pid=$SPIN_PID on cpu$CPU"

# ------------------------------------------------ spec file (written BEFORE the
# rep loop so a killed/interrupted run is still analyzable)
{
  echo "tag=$TAG"
  echo "timestamp_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "prefix=$PREFIX"
  echo "binary=$BIN"
  echo "binary_sha256=$(sha256sum "$BIN" | cut -d' ' -f1)"
  echo "bin_a=$BIN_A"
  echo "bin_a_sha256=$(sha256sum "$BIN_A" | cut -d' ' -f1)"
  echo "bin_b=$BIN_B"
  echo "bin_b_sha256=$(sha256sum "$BIN_B" | cut -d' ' -f1)"
  echo "workload=$WORKLOAD"
  echo "max_k=$MAX_K"
  echo "rounds=$ROUNDS"
  echo "rounds_b=$ROUNDS_B"
  echo "rounds_a=$ROUNDS"
  echo "order=$ORDER_STR"
  echo "freqs=${PREFIX}_freqs.tsv"
  echo "reps=$REPS"
  echo "only=$ONLY"
  echo "cpu=$CPU"
  echo "stack_mb=$STACK_MB"
  echo "keepalive=$KA_MODE"
  for arm in "${!ARM_ENV[@]}"; do echo "arm=$arm env=${ARM_ENV[$arm]} rounds=$(arm_rounds "$arm")"; done
  for s in ${SEGS//,/ }; do
    read -r a1 a2 <<<"$(seg_arms "$s")"
    kind=exp; [[ "$s" == null* ]] && kind=null
    echo "segment=$s $kind $a1 $a2"
  done
} > "$SPEC_FILE"
echo "spec:       $SPEC_FILE"

# ------------------------------------------------------------------- rep loop
LOG="$RAW_DIR/${PREFIX}.log"
: > "$LOG"
FREQ_FILE="$RAW_DIR/${PREFIX}_freqs.tsv"
printf 'segment\tarm\trep\torder\tfreq_before_kHz\tfreq_after_kHz\n' > "$FREQ_FILE"
freq_khz() { cat "/sys/devices/system/cpu/cpu$CPU/cpufreq/scaling_cur_freq" 2>/dev/null || echo n/a; }
run_rep() { # $1=env spec $2=out $3=bin $4=rounds $5=seg $6=arm $7=rep $8=order
  local spec="$1" out="$2" bin="$3" rnds="$4" seg="$5" arm="$6" rep="$7" ord="$8" rc=0 fb="" fa=""
  local -a extra=()
  [[ "$spec" != "-" ]] && extra=("$spec")
  fb="$(freq_khz)"
  set +e
  taskset -c "$CPU" env "L02_STACK_MB=$STACK_MB" ${extra[@]+"${extra[@]}"} "$bin" \
    --max-k "$MAX_K" --rounds "$rnds" --workload "$WORKLOAD" --only "$ONLY" >"$out" 2>&1
  rc=$?
  set -e
  fa="$(freq_khz)"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$seg" "$arm" "$rep" "$ord" "$fb" "$fa" >>"$FREQ_FILE"
  return "$rc"
}

for s in ${SEGS//,/ }; do
  read -r a1 a2 <<<"$(seg_arms "$s")"
  ok1=0; ok2=0
  echo "--- segment $s: $a1 vs $a2" | tee -a "$LOG"
  for i in $(seq 1 "$REPS"); do
    # alternate which side runs first on even pairs (order effect cancels)
    if (( ORDER_ALT )) && (( i % 2 == 0 )); then order=("$a2" "$a1"); ord="s2first"; else order=("$a1" "$a2"); ord="s1first"; fi
    for arm in "${order[@]}"; do
      if run_rep "${ARM_ENV[$arm]}" "$RAW_DIR/${PREFIX}_${arm}_rep${i}.txt" "$(arm_bin "$arm")" "$(arm_rounds "$arm")" "$s" "$arm" "$i" "$ord"; then
        if [[ "$arm" == "$a1" ]]; then ok1=$((ok1+1)); else ok2=$((ok2+1)); fi
      else
        echo "  $s $arm rep $i FAILED" | tee -a "$LOG"
      fi
    done
  done
  echo "  reps_ok: $a1=$ok1/$REPS $a2=$ok2/$REPS" | tee -a "$LOG"
done

echo
echo "raw prefix: $PREFIX"
echo "spec:       $SPEC_FILE"
echo "analyze:    python3 docs/perf-l02/raw/exp-ab-analyze.py $SPEC_FILE"
