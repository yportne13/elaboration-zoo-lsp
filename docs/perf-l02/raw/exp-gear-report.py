#!/usr/bin/env python3
"""Gear-stratification report for exp-ab-run.sh batches (walt OPP toggling).

Reads the `<prefix>_freqs.tsv` sidecar written by exp-ab-run.sh (one row per
l02bench process: segment, arm, rep, within-pair order, scaling_cur_freq before
and after) and answers, per (segment, workload, k, impl):

  * the frequency value histogram per arm (are there two OPP clusters?);
  * cross-peak pairs: |paired relative diff| > 5%  (the knife-edge pairs);
  * gear-stable pairs: all four freq readings of the pair (before/after x both
    arms) equal -> the pair very likely did not straddle a gear change;
  * the paired median and its bootstrap p95 on the FULL set vs on the
    gear-stable subset.

This is the diagnostic behind "how much resolution can a 1-6% A/B get on this
box", used to validate route (c) (larger --rounds makes the per-rep minimum
cross gear boundaries) before running task-9's C1/C2.

Usage:
    python3 docs/perf-l02/raw/exp-gear-report.py docs/perf-l02/raw/exp-*_spec.txt \
        [--ks 13,15] [--iters 4000] [--cross 5]
"""

import argparse
import collections
import glob as globmod
import importlib.util
import os
import random
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "an", os.path.join(HERE, "exp-ab-analyze.py"))
an = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(an)

SIDE_A_ARMS = ("A", "nA1", "nA2")


def read_freqs(path):
    """(segment, arm, rep) -> (order, freq_before, freq_after)."""
    out = {}
    if not path or not os.path.isfile(path):
        return out
    with open(path) as fh:
        for line in fh:
            f = line.rstrip("\n").split("\t")
            if len(f) < 6 or f[0] == "segment":
                continue
            out[(f[0], f[1], int(f[2]))] = (f[3], f[4], f[5])
    return out


def diffs_of(v1, v2):
    return [(b - a) / a * 100.0 for a, b in zip(v1, v2) if a > 0]


def boot95(vals, iters, rng):
    """bootstrap p95 of |median| over resampled pair indices (paired stat)."""
    n = len(vals)
    if n < 4:
        return float("nan")
    sims = []
    for _ in range(iters):
        s = [vals[rng.randrange(n)] for _ in range(n)]
        sims.append(abs(statistics.median(s)))
    sims.sort()
    return sims[min(len(sims) - 1, int(0.95 * len(sims)))]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("specs", nargs="+")
    ap.add_argument("--ks", default="")
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--cross", type=float, default=5.0)
    ap.add_argument("--seed", type=int, default=12345)
    args = ap.parse_args()
    ks = {int(x) for x in args.ks.split(",") if x.strip()} or None

    files = sorted({f for pat in args.specs for f in globmod.glob(pat)})
    for path in files:
        spec = an.read_spec(path)
        prefix = spec.get("prefix") or os.path.basename(path).replace("_spec.txt", "")
        repdir = os.path.dirname(os.path.abspath(path))
        freqs = read_freqs(os.path.join(repdir, spec.get("freqs", "")))
        print(f"== {spec.get('tag','?')}  workload={spec.get('workload')} "
              f"rounds_a={spec.get('rounds_a')} rounds_b={spec.get('rounds_b')} "
              f"order={spec.get('order')} ==")
        if not freqs:
            print("   (no freqs sidecar -- run predates freq sampling)")
            print()
            continue
        nreps = int(spec.get("reps", "0") or 0)
        for seg in spec["segments"]:
            s1, s2 = seg["sides"]
            cnt = {s1: collections.Counter(), s2: collections.Counter()}
            for i in range(1, nreps + 1):
                for s in (s1, s2):
                    r = freqs.get((seg["name"], s, i))
                    if r:
                        cnt[s][r[1]] += 1
            r1 = spec.get("rounds_a") if s1 in SIDE_A_ARMS else spec.get("rounds_b")
            r2 = spec.get("rounds_a") if s2 in SIDE_A_ARMS else spec.get("rounds_b")
            print(f"   segment {seg['name']} [{seg['kind']}]: "
                  f"{s1}(rounds={r1}) freqs={dict(cnt[s1])} | "
                  f"{s2}(rounds={r2}) freqs={dict(cnt[s2])}")
            d1 = an.series_by_key(an.rep_files(os.path.join(repdir, prefix), s1))
            d2 = an.series_by_key(an.rep_files(os.path.join(repdir, prefix), s2))
            keys = sorted((set(d1) & set(d2)), key=lambda k: (k[0], k[1], k[2]))
            if ks:
                keys = [k for k in keys if k[1] in ks]
            rng = random.Random(args.seed)
            print(f"     {'workload':<10}{'k':>3} {'n':>4}{'stableall4':>11}"
                  f"{'cross':>7}{'pair_full%':>12}{'p95_full':>9}"
                  f"{'pair_stbl%':>12}{'p95_stbl':>9}")
            for key in keys:
                v1, v2 = d1[key], d2[key]
                ds = diffs_of(v1, v2)
                idxs = []
                for idx in range(min(len(v1), len(v2))):
                    a = freqs.get((seg["name"], s1, idx + 1))
                    b = freqs.get((seg["name"], s2, idx + 1))
                    if a and b and len({a[1], a[2], b[1], b[2]}) == 1:
                        idxs.append(idx)
                stbl = [ds[i] for i in idxs if i < len(ds)]
                cross = sum(1 for d in ds if abs(d) > args.cross)
                print(f"     {key[0]:<10}{key[1]:>3} {len(ds):>4}{len(stbl):>11}"
                      f"{cross:>7}{statistics.median(ds):>12.3f}"
                      f"{boot95(ds, args.iters, rng):>9.3f}"
                      f"{(statistics.median(stbl) if stbl else float('nan')):>12.3f}"
                      f"{boot95(stbl, args.iters, rng):>9.3f}")
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
