#!/usr/bin/env python3
"""Null A/B (false-positive floor) from l02bench raw rep files.

Takes one or more glob patterns that all point at the SAME binary + SAME
configuration (`--only <impl> --workload <w> --max-k <k>`), concatenates the
per-rep minima in (batch, rep) order, and splits them by rep parity into two
groups of equal size (21 reps/side when 42 reps were measured).  The two groups
have identical ground truth, so any measured difference is pure noise -- this is
the false-positive floor an A/B experiment must beat.

Also reports an i.i.d. bootstrap of the same statistic over random balanced
splits (p50/p95/max of |median(A) - median(B)| / min), which answers "how many
reps/side would be needed" more cheaply than measuring many batches.

Usage:
    tools/perf-l02/null_ab.py 'docs/perf-l02/raw/*nullab*_rep*.txt'
"""

import argparse
import glob
import importlib.util
import os
import random
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("parse_bench", os.path.join(HERE, "parse_bench.py"))
pb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pb)

REP_RE = __import__("re").compile(r"_rep(\d+)\.txt$")


def ordered_series(files):
    """key -> list of per-rep minima ordered by (batch, rep)."""
    per_key = {}
    entries = []
    for f in files:
        base = os.path.basename(f)
        m = REP_RE.search(base)
        batch = base[: m.start()] if m else base
        rep = int(m.group(1)) if m else 0
        entries.append((batch, rep, f))
    entries.sort(key=lambda e: (e[0], e[1]))
    for _b, _r, f in entries:
        for key, (mn, _med) in pb.parse_file(f).items():
            per_key.setdefault(key, []).append(mn)
    return per_key


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("patterns", nargs="+", help="glob(s) for raw rep files (quote them)")
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=12345)
    args = ap.parse_args()

    files = sorted({f for pat in args.patterns for f in glob.glob(pat)})
    if not files:
        print("no files matched", file=sys.stderr)
        return 1

    series = ordered_series(files)
    rng = random.Random(args.seed)
    hdr = (f"{'workload':<10}{'k':>3} {'impl':<10}{'n_side':>7}"
           f"{'medA':>10}{'medB':>10}{'diff%':>9}{'blk1st':>10}{'blk2nd':>10}{'blkdiff%':>10}"
           f"{'boot_p50':>10}{'boot_p95':>10}{'boot_max':>10}")
    print(hdr)
    print("-" * len(hdr))
    for key in sorted(series):
        vals = series[key]
        wl, k, impl = key
        n = len(vals)
        if n < 4:
            continue
        a = vals[0::2]
        b = vals[1::2]
        ma, mb = statistics.median(a), statistics.median(b)
        diff = abs(ma - mb) / min(ma, mb) * 100.0
        half = n // 2
        lo_all = min(vals)
        # "blocked" comparison: all reps of arm A measured first, then all of B
        # (the shape a naive two-invocation A/B takes on this box).
        blk_a, blk_b = vals[:half], vals[half:]
        mba, mbb = statistics.median(blk_a), statistics.median(blk_b)
        blk_diff = abs(mba - mbb) / min(mba, mbb) * 100.0
        # index-based bootstrap (values can repeat, so sample indices not values)
        idx = list(range(n))
        sims = []
        for _ in range(args.iters):
            a_idx = set(rng.sample(idx, half))
            aa = [vals[i] for i in range(n) if i in a_idx]
            bb = [vals[i] for i in range(n) if i not in a_idx]
            sims.append(abs(statistics.median(aa) - statistics.median(bb)) / lo_all * 100.0)
        sims.sort()
        p50 = sims[len(sims) // 2]
        p95 = sims[min(len(sims) - 1, int(0.95 * len(sims)))]
        pmax = sims[-1]
        print(f"{wl:<10}{k:>3} {impl:<10}{half:>7}{ma:>10.4f}{mb:>10.4f}{diff:>9.2f}"
              f"{mba:>10.4f}{mbb:>10.4f}{blk_diff:>10.2f}"
              f"{p50:>10.2f}{p95:>10.2f}{pmax:>10.2f}")
    print()
    print("diff%     = |median(odd reps) - median(even reps)| / min  (interleaved-like split)")
    print("blkdiff%  = |median(first half) - median(second half)| / min  (blocked A-then-B hazard)")
    print("boot_p95  = 95th percentile of diff% over random balanced splits")
    return 0


if __name__ == "__main__":
    sys.exit(main())
