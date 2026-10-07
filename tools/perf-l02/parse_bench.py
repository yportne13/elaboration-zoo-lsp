#!/usr/bin/env python3
"""Aggregate `l02bench` stdout across whole-process repetitions.

`l02bench` prints one line per k:

    k=11  n=4096   fast=  0.210ms /  0.230

where the first number is the min over `--rounds` inner rounds and the second
is the inner median.  The numeric value is milliseconds (the binary measures
`as_micros()` and prints `min/1000 . min%1000`), but this parser also accepts a
`us`/`µs` suffix and converts to ms so it stays correct if the unit ever changes.

A single process invocation is one "rep"; the honest protocol on this box is to
run the whole benchmark N times with `--only <one impl>` and keep, per
(workload, k, impl), the **median of the per-rep minima** (`med_of_min`) plus
the spread of those minima (the only observable noise bound -- no perf/valgrind
here, see docs/perf-l02/00-baseline.md).

Usage:
    parse_bench.py [--tsv] [--min-reps K] rep1.txt rep2.txt ...

Output: one aggregated row per (workload, k, impl):
    workload  k  impl  reps  min_ms  med_of_min  max_ms  spread_pct  med_of_med
where min_ms/med_ms/max_ms are over the per-rep minima and
spread_pct = (max_ms - min_ms) / min_ms * 100.
"""

import argparse
import re
import statistics
import sys

SECTION_RE = re.compile(r"^==\s*workload:\s*(\S+)\s*==")
K_RE = re.compile(r"^k=(\d+)\s+n=(\d+)\b")
# `<impl>=  <num><unit><star>/ <num>`; the star marks the fastest impl on the line.
IMPL_RE = re.compile(
    r"([A-Za-z_][A-Za-z0-9_]*)=\s*(\d+(?:\.\d+)?)\s*(ms|\u00b5s|us|\u03bcs)\s*(\*?)\s*/\s*(\d+(?:\.\d+)?)"
)


def to_ms(value: float, unit: str) -> float:
    return value / 1000.0 if unit in ("us", "\u00b5s", "\u03bcs") else value


def parse_file(path):
    """Return {(workload, k, impl): (min_ms, med_ms)} for one rep."""
    out = {}
    workload = None
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.strip()
            m = SECTION_RE.match(line)
            if m:
                workload = m.group(1)
                continue
            if workload is None:
                continue
            if not K_RE.match(line):
                continue
            for name, vmin, unit, _star, vmed in IMPL_RE.findall(line):
                out[(workload, int(K_RE.match(line).group(1)), name)] = (
                    to_ms(float(vmin), unit),
                    to_ms(float(vmed), unit),
                )
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--tsv", action="store_true", help="tab-separated output")
    ap.add_argument("--min-reps", type=int, default=1,
                    help="only report keys observed in at least K reps")
    args = ap.parse_args()

    reps = [parse_file(p) for p in args.files]
    keys = sorted({k for r in reps for k in r}, key=lambda k: (k[0], k[1], k[2]))
    rows = []
    for key in keys:
        mins = [r[key][0] for r in reps if key in r]
        meds = [r[key][1] for r in reps if key in r]
        if len(mins) < args.min_reps:
            continue
        lo, hi = min(mins), max(mins)
        med = statistics.median(mins)
        spread = (hi - lo) / lo * 100.0 if lo > 0 else float("nan")
        med_of_med = statistics.median(meds) if meds else float("nan")
        rows.append((key[0], key[1], key[2], len(mins), lo, med, hi, spread, med_of_med))

    if args.tsv:
        print("workload\tk\timpl\treps\tmin_ms\tmed_of_min\tmax_ms\tspread_pct\tmed_of_med")
        for r in rows:
            print(f"{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{r[4]:.4f}\t{r[5]:.4f}\t"
                  f"{r[6]:.4f}\t{r[7]:.2f}\t{r[8]:.4f}")
        return 0

    cur = None
    for wl, k, name, nreps, lo, med, hi, spread, med_of_med in rows:
        head = (wl, k)
        if head != cur:
            cur = head
            n = 1 << (k + 1)
            print(f"\n== {wl} k={k} n={n} (reps={nreps}) ==")
            print(f"  {'impl':<12}{'min_ms':>10}{'med_of_min':>13}{'max_min':>10}{'spread%':>9}")
        print(f"  {name:<12}{lo:>10.4f}{med:>13.4f}{hi:>10.4f}{spread:>9.2f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
