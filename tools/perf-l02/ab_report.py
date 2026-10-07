#!/usr/bin/env python3
"""Paired report for an interleaved A/B produced by run_bench.sh --interleave.

Each arm is a set of `l02bench` rep files (one process per rep, single impl per
process).  Because the harness alternates A/B in ABBA order inside one locked
window, rep i of arm A and rep i of arm B share the same clock-gear state, so
the per-rep ratio is the drift-cancelling statistic -- not the difference of two
block medians (which carries a ~19% false-positive floor on this box; see
docs/perf-l02/00-baseline.md §3).

Reported per (workload, k):
  medA, medB      median of the per-rep minima (same estimator as the baseline)
  ratio           medA / medB
  diff%           |medA - medB| / min
  pair_med        median of per-rep A_i / B_i
  pair_iqr%       (p75 - p25) / median of the per-rep ratios, in %
  wins            #reps with A_i < B_i  /  #reps with A_i > B_i  (ties omitted)
  halves          median ratio of the first half of the paired ratios vs second
                  half -- a sign of drift leaking through the pairing

Usage:
    ab_report.py --a a_rep1.txt a_rep2.txt ... --b b_rep1.txt ... \
                 --impl-a fast_ss --impl-b fast [--ks 13,15]
"""

import argparse
import importlib.util
import os
import re
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("parse_bench", os.path.join(HERE, "parse_bench.py"))
pb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pb)

REP_RE = re.compile(r"_rep(\d+)\.txt$")


def by_rep(files):
    """{rep_index: {(workload,k): min_ms}}"""
    out = {}
    for f in files:
        m = REP_RE.search(os.path.basename(f))
        rep = int(m.group(1)) if m else 0
        d = out.setdefault(rep, {})
        for (wl, k, _impl), (mn, _med) in pb.parse_file(f).items():
            d[(wl, k)] = mn
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", nargs="+", required=True)
    ap.add_argument("--b", nargs="+", required=True)
    ap.add_argument("--impl-a", default="A")
    ap.add_argument("--impl-b", default="B")
    ap.add_argument("--ks", default="")
    args = ap.parse_args()

    A, B = by_rep(args.a), by_rep(args.b)
    ks = {int(x) for x in args.ks.split(",") if x} if args.ks else None
    keys = sorted({k for r in (A, B) for d in r.values() for k in d}, key=lambda k: (k[0], k[1]))

    hdr = (f"{'workload':<10}{'k':>3} {'A':<9}{'B':<9}{'n':>4}"
           f"{'medA':>10}{'medB':>10}{'ratio':>8}{'diff%':>8}"
           f"{'pair_med':>10}{'pair_iqr%':>10}{'wins':>11}{'halves':>9}")
    print(hdr)
    print("-" * len(hdr))
    for key in keys:
        wl, k = key
        if ks is not None and k not in ks:
            continue
        pairs = [(A[r][key], B[r][key]) for r in sorted(A) if key in A[r] and key in B[r]]
        if len(pairs) < 2:
            continue
        aa = [x for x, _ in pairs]
        bb = [y for _, y in pairs]
        ma, mb = statistics.median(aa), statistics.median(bb)
        ratio = ma / mb
        diff = abs(ma - mb) / min(ma, mb) * 100.0
        ratios = sorted(x / y for x, y in pairs)
        pr = statistics.median(ratios)
        q1 = ratios[len(ratios) // 4]
        q3 = ratios[(3 * len(ratios)) // 4]
        iqr = (q3 - q1) / pr * 100.0
        wins_a = sum(1 for x, y in pairs if x < y)
        wins_b = sum(1 for x, y in pairs if x > y)
        h = len(ratios) // 2
        halves = statistics.median(ratios[:h]) / statistics.median(ratios[h:]) if h else float("nan")
        print(f"{wl:<10}{k:>3} {args.impl_a:<9}{args.impl_b:<9}{len(pairs):>4}"
              f"{ma:>10.4f}{mb:>10.4f}{ratio:>8.3f}{diff:>8.2f}"
              f"{pr:>10.3f}{iqr:>10.2f}{f'{wins_a}/{wins_b}':>11}{halves:>9.3f}")
    print()
    print("ratio = medA/medB (>1 => A slower); pair_med = median per-rep A_i/B_i")
    print("wins = #reps A<B / #reps A>B; halves = median ratio first half / second half")
    return 0


if __name__ == "__main__":
    sys.exit(main())
