#!/usr/bin/env python3
"""Quantify timing noise from l01bench raw rep files.

Reads `*_repN.txt` files produced by tools/perf-l01/run_bench.sh (one file per
whole-process repetition) and reports, per (workload, size, variant):

  * per-batch min-of-reps and the cross-batch spread of that estimator
    (`min-of-N` is what the team compares on, so *its* reproducibility is the
    number that matters -- not the scatter of a single rep);
  * pooled single-rep coefficient of variation (CV = sd/mean);
  * within-batch half-split paired difference: min of the first half of the
    reps vs the second half, which mimics the residual error of an *interleaved*
    A/B comparison run inside one batch;
  * i.i.d. bootstrap CV of min-of-k (k = reps per batch): an optimistic lower
    bound, because it ignores the batch-correlated governor drift that the
    cross-batch column exposes.

Usage:
    tools/perf-l01/noise_report.py 'docs/perf-l01/raw/*_rep*.txt' [--reps 7]
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


def bootstrap_min_cv(pooled, k, iters=4000, seed=12345):
    if len(pooled) < 2:
        return float("nan")
    rng = random.Random(seed)
    mins = [min(rng.choices(pooled, k=k)) for _ in range(iters)]
    return statistics.pstdev(mins) / statistics.mean(mins) * 100.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pattern", help="glob for raw rep files (quote it)")
    ap.add_argument("--reps", type=int, default=None, help="reps per batch (for bootstrap)")
    ap.add_argument("--sizes", default="", help="optional comma list to filter sizes")
    args = ap.parse_args()

    files = sorted(glob.glob(args.pattern))
    if not files:
        print(f"no files match {args.pattern}", file=sys.stderr)
        return 1
    sizes = {int(x) for x in args.sizes.split(",") if x} if args.sizes else None

    per_batch = defaultdict(lambda: defaultdict(dict))  # key -> batch -> rep -> min
    for f in files:
        b, rep = batch_of(f)
        for key, (mn, _med) in pb.parse_file(f).items():
            per_batch[key][b][rep] = mn

    rows = []
    for key, batches in per_batch.items():
        wl, size, variant = key
        if sizes is not None and (size not in sizes):
            continue
        bmins = [min(v.values()) for v in batches.values()]
        pooled = [x for v in batches.values() for x in v.values()]
        nreps = args.reps or max(len(v) for v in batches.values())
        cross = (max(bmins) - min(bmins)) / min(bmins) * 100.0
        cv = statistics.pstdev(pooled) / statistics.mean(pooled) * 100.0
        paired = []
        for v in batches.values():
            reps = sorted(v)
            if len(reps) < 2:
                continue
            h = len(reps) // 2
            a = min(v[r] for r in reps[:h])
            b = min(v[r] for r in reps[h:])
            paired.append(abs(a - b) / min(a, b) * 100.0)
        rows.append(
            (
                wl, size, variant, len(batches), nreps,
                min(bmins), max(bmins), cross, cv,
                statistics.median(paired) if paired else float("nan"),
                max(paired) if paired else float("nan"),
                bootstrap_min_cv(pooled, nreps),
            )
        )

    rows.sort(key=lambda r: (r[0], r[1] or 0, r[2]))
    hdr = (
        f"{'workload':<14}{'n':>7} {'variant':<22}{'batches':>8}{'reps':>5}"
        f"{'batchmin':>10}{'batchmax':>10}{'cross%':>8}{'repCV%':>8}"
        f"{'pair_med%':>10}{'pair_max%':>10}{'boot_minCV%':>12}"
    )
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        print(
            f"{r[0]:<14}{r[1]:>7} {r[2]:<22}{r[3]:>8}{r[4]:>5}"
            f"{r[5]:>10.4f}{r[6]:>10.4f}{r[7]:>8.2f}{r[8]:>8.2f}"
            f"{r[9]:>10.2f}{r[10]:>10.2f}{r[11]:>12.2f}"
        )

    if rows:
        print()
        print(f"cross-batch spread of min-of-N : median {statistics.median(r[7] for r in rows):.2f}%  "
              f"max {max(r[7] for r in rows):.2f}%")
        print(f"single-rep CV                  : median {statistics.median(r[8] for r in rows):.2f}%  "
              f"max {max(r[8] for r in rows):.2f}%")
        print(f"within-batch half-split paired : median {statistics.median(r[9] for r in rows):.2f}%  "
              f"max {max(r[10] for r in rows):.2f}%")
        print(f"bootstrap CV of min-of-N (iid) : median {statistics.median(r[11] for r in rows):.2f}%  "
              f"max {max(r[11] for r in rows):.2f}%")
    return 0


if __name__ == "__main__":
    sys.exit(main())
