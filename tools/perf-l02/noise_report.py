#!/usr/bin/env python3
"""Quantify wall-clock timing noise from l02bench raw rep files.

Reads `*_repN.txt` files produced by tools/perf-l02/run_bench.sh (one file per
whole-process repetition, all with the same `--only <impl>` isolation) and
reports, per (workload, k, impl):

  * cross-batch spread of **both** estimators over the per-rep minima:
    min-of-N and median-of-N (`med_of_min`).  The team compares on
    `med_of_min`, so its cross-batch spread is the number that matters;
  * pooled single-rep coefficient of variation (CV = sd/mean);
  * within-batch half-split paired difference (first half vs second half of the
    reps), for both estimators -- this mimics the residual error of an
    *interleaved* A/B comparison run inside one batch;
  * i.i.d. bootstrap CV of min-of-k / median-of-k (k = reps per batch): an
    optimistic lower bound, because it ignores the batch-correlated governor
    drift that the cross-batch columns expose.

Usage:
    tools/perf-l02/noise_report.py 'docs/perf-l02/raw/*_rep*.txt' [--reps 7]
"""

import argparse
import glob
import importlib.util
import os
import random
import re
import statistics
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("parse_bench", os.path.join(HERE, "parse_bench.py"))
pb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pb)

REP_RE = re.compile(r"_rep(\d+)\.txt$")


def batch_of(path):
    base = os.path.basename(path)
    m = REP_RE.search(base)
    return (base[: m.start()] if m else base, int(m.group(1)))


def spread_pct(vals):
    lo, hi = min(vals), max(vals)
    return (hi - lo) / lo * 100.0 if lo > 0 else float("nan")


def boot_cv(pooled, k, stat, iters=4000, seed=12345):
    if len(pooled) < 2:
        return float("nan")
    rng = random.Random(seed)
    vals = [stat(rng.choices(pooled, k=k)) for _ in range(iters)]
    return statistics.pstdev(vals) / statistics.mean(vals) * 100.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pattern", help="glob for raw rep files (quote it)")
    ap.add_argument("--reps", type=int, default=None, help="reps per batch (for bootstrap)")
    ap.add_argument("--ks", default="", help="optional comma list to filter k")
    args = ap.parse_args()

    files = sorted(glob.glob(args.pattern))
    if not files:
        print(f"no files match {args.pattern}", file=sys.stderr)
        return 1
    ks = {int(x) for x in args.ks.split(",") if x} if args.ks else None

    per_batch = defaultdict(lambda: defaultdict(dict))  # key -> batch -> rep -> min
    for f in files:
        b, rep = batch_of(f)
        for key, (mn, _med) in pb.parse_file(f).items():
            per_batch[key][b][rep] = mn

    rows = []
    for key, batches in per_batch.items():
        wl, k, impl = key
        if ks is not None and k not in ks:
            continue
        bvals = [list(v.values()) for v in batches.values()]
        bmins = [min(v) for v in bvals]
        bmeds = [statistics.median(v) for v in bvals]
        pooled = [x for v in bvals for x in v]
        nreps = args.reps or max(len(v) for v in bvals)
        cross_min = spread_pct(bmins)
        cross_med = spread_pct(bmeds)
        cv = statistics.pstdev(pooled) / statistics.mean(pooled) * 100.0
        pmin, pmed = [], []
        for v in bvals:
            reps = sorted(v)
            if len(reps) < 2:
                continue
            h = len(reps) // 2
            a, b = reps[:h], reps[h:]
            pmin.append(abs(min(a) - min(b)) / min(min(a), min(b)) * 100.0)
            pmed.append(abs(statistics.median(a) - statistics.median(b))
                        / min(statistics.median(a), statistics.median(b)) * 100.0)
        rows.append(
            (
                wl, k, impl, len(bvals), nreps,
                min(bmins), max(bmins), cross_min, cross_med, cv,
                statistics.median(pmin) if pmin else float("nan"),
                max(pmin) if pmin else float("nan"),
                statistics.median(pmed) if pmed else float("nan"),
                max(pmed) if pmed else float("nan"),
                boot_cv(pooled, nreps, min), boot_cv(pooled, nreps, statistics.median),
            )
        )

    rows.sort(key=lambda r: (r[0], r[1], r[2]))
    hdr = (
        f"{'workload':<10}{'k':>3} {'impl':<10}{'batches':>8}{'reps':>5}"
        f"{'bmin_cross%':>12}{'bmed_cross%':>12}{'repCV%':>8}"
        f"{'pair_min%':>10}{'pair_minmax%':>13}{'pair_med%':>10}{'pair_medmax%':>13}"
        f"{'boot_minCV%':>12}{'boot_medCV%':>12}"
    )
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        print(
            f"{r[0]:<10}{r[1]:>3} {r[2]:<10}{r[3]:>8}{r[4]:>5}"
            f"{r[7]:>12.2f}{r[8]:>12.2f}{r[9]:>8.2f}"
            f"{r[10]:>10.2f}{r[11]:>13.2f}{r[12]:>10.2f}{r[13]:>13.2f}"
            f"{r[14]:>12.2f}{r[15]:>12.2f}"
        )

    if rows:
        print()
        print(f"cross-batch spread of min-of-N      : median {statistics.median(r[7] for r in rows):.2f}%  "
              f"max {max(r[7] for r in rows):.2f}%")
        print(f"cross-batch spread of median-of-N   : median {statistics.median(r[8] for r in rows):.2f}%  "
              f"max {max(r[8] for r in rows):.2f}%")
        print(f"single-rep CV                       : median {statistics.median(r[9] for r in rows):.2f}%  "
              f"max {max(r[9] for r in rows):.2f}%")
        print(f"within-batch half-split, min-of-half: median {statistics.median(r[10] for r in rows):.2f}%  "
              f"max {max(r[11] for r in rows):.2f}%")
        print(f"within-batch half-split, med-of-half: median {statistics.median(r[12] for r in rows):.2f}%  "
              f"max {max(r[13] for r in rows):.2f}%")
        print(f"bootstrap CV of min-of-N (iid)      : median {statistics.median(r[14] for r in rows):.2f}%  "
              f"max {max(r[14] for r in rows):.2f}%")
        print(f"bootstrap CV of median-of-N (iid)   : median {statistics.median(r[15] for r in rows):.2f}%  "
              f"max {max(r[15] for r in rows):.2f}%")
    return 0


if __name__ == "__main__":
    sys.exit(main())
