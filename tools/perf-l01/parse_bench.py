#!/usr/bin/env python3
"""Aggregate `l01bench` stdout across whole-process repetitions.

`l01bench` prints, per variant per size, the *min* and *median* of `--rounds`
inner rounds (ms).  A single process invocation is one "rep"; the honest
min-of-N protocol for this machine is to run the whole benchmark N times and
keep, per (workload, size, variant), the min across the per-rep minima -- plus
the spread of those per-rep minima, which is the only observable noise bound
(no perf/valgrind on this box, see docs/perf-l01/00-baseline.md).

Usage:
    parse_bench.py [--tsv] [--min-reps K] rep1.txt rep2.txt ...

Output: one aggregated row per (workload, size, variant):
    workload  size  variant  reps  min_ms  med_ms  max_ms  spread_pct  med_of_med
where min_ms/med_ms/max_ms are over the per-rep minima and
spread_pct = (max_ms - min_ms) / min_ms * 100.
"""

import argparse
import re
import statistics
import sys

SECTION_RE = re.compile(r"^==\s*(.+?)\s*==")


def section_key(label: str):
    """Map a bench section header to (workload, size)."""
    m = re.search(r"church_pair\((\d+)\)", label)
    if m:
        return "church", int(m.group(1))
    m = re.search(r"dup_pair\((\d+)\)", label)
    if m:
        return "dup_pair", int(m.group(1))
    m = re.search(r"dup_deep\((\d+)\)", label)
    if m:
        return "dup_deep", int(m.group(1))
    m = re.match(r"guest/(\S+)", label)
    if m:
        return "guest/" + m.group(1), None  # size comes from the column header
    return None


def parse_file(path):
    """Return {(workload, size, variant): (min_ms, med_ms)} for one rep."""
    out = {}
    workload = size = None
    guest_sizes = []
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            m = SECTION_RE.match(line.strip())
            if m:
                key = section_key(m.group(1))
                workload, size = key if key else (None, None)
                guest_sizes = []
                continue
            if workload is None:
                continue
            body = line.strip()
            if not body or body.startswith("("):
                continue
            body = body.rstrip("*").strip()
            toks = body.split()
            if len(toks) < 2:
                continue
            if toks[0] == "variant":
                # guest column header: variant n=50 n=100 ...
                guest_sizes = [int(t.split("=")[1]) for t in toks[1:] if "=" in t]
                continue
            try:
                nums = [float(t) for t in toks[1:]]
            except ValueError:
                continue  # prose / divider lines
            name = toks[0]
            if len(nums) == 2:
                out[(workload, size, name)] = (nums[0], nums[1])
            elif guest_sizes and len(nums) == len(guest_sizes):
                for sz, v in zip(guest_sizes, nums):
                    out[(workload, sz, name)] = (v, float("nan"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--tsv", action="store_true", help="tab-separated output")
    ap.add_argument(
        "--min-reps",
        type=int,
        default=1,
        help="only report keys observed in at least K reps",
    )
    args = ap.parse_args()

    reps = [parse_file(p) for p in args.files]
    keys = sorted({k for r in reps for k in r}, key=lambda k: (k[0], k[1] or 0, k[2]))
    rows = []
    for key in keys:
        mins = [r[key][0] for r in reps if key in r]
        meds = [r[key][1] for r in reps if key in r and r[key][1] == r[key][1]]
        if len(mins) < args.min_reps:
            continue
        lo, hi = min(mins), max(mins)
        med = statistics.median(mins)
        spread = (hi - lo) / lo * 100.0 if lo > 0 else float("nan")
        med_of_med = statistics.median(meds) if meds else float("nan")
        rows.append((key[0], key[1], key[2], len(mins), lo, med, hi, spread, med_of_med))

    if args.tsv:
        print("workload\tsize\tvariant\treps\tmin_ms\tmed_ms\tmax_ms\tspread_pct\tmed_of_med")
        for r in rows:
            print(
                f"{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{r[4]:.4f}\t{r[5]:.4f}\t"
                f"{r[6]:.4f}\t{r[7]:.2f}\t{r[8]:.4f}"
            )
        return 0

    cur = None
    for wl, size, name, nreps, lo, med, hi, spread, med_of_med in rows:
        head = (wl, size)
        if head != cur:
            cur = head
            print(f"\n== {wl} n={size} (reps={nreps}) ==")
            print(f"  {'variant':<26}{'min_ms':>10}{'med_of_min':>12}{'max_min':>10}{'spread%':>9}")
        print(f"  {name:<26}{lo:>10.4f}{med:>12.4f}{hi:>10.4f}{spread:>9.2f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
