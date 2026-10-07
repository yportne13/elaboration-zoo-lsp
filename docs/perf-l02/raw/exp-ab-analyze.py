#!/usr/bin/env python3
"""Analyze same-batch interleaved A/B (+ null control) raw reps from exp-ab-run.sh.

Input: one or more `exp-*_spec.txt` files written by exp-ab-run.sh.  Each spec
points at arm raw files `<prefix>_<arm>_rep<N>.txt`, each of which is one
l02bench process run; per (workload, k, impl) l02bench reports the min over its
inner `--rounds` rounds.

Statistics per cell (21 pairs by default, arms interleaved A1 B1 A2 B2 ...):
  * unpaired  : (median(B) - median(A)) / median(A) * 100
  * paired    : median_i (B_i - A_i) / A_i * 100, with a paired bootstrap CI
  * null floor: for `null` segments (both sides identical config) the same two
    statistics are bootstrapped (4000 resamples) and the p95 of |stat| is the
    batch's false-positive floor.
Verdict (pre-registered in exp-8-plan.md): |observed| <= floor p95 -> NOT
DECIDED; otherwise DECIDED with sign.  PRIMARY is the paired statistic against
the paired null floor, because the arms are interleaved and adjacent in time and
pairing removes the slow walt gear drift; the unpaired statistic is reported for
continuity with tools/perf-l02/null_ab.py but its floor on a drifting batch is
~16-19% (measured on the existing 42-rep nullab batch), so it is NOT gating.

Usage:
    python3 docs/perf-l02/raw/exp-ab-analyze.py docs/perf-l02/raw/exp-*_spec.txt \
        [--ks 13,15] [--iters 4000] [--dump] [--tsv]
    python3 docs/perf-l02/raw/exp-ab-analyze.py --selftest
"""

import argparse
import glob as globmod
import importlib.util
import os
import random
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
_spec = importlib.util.spec_from_file_location(
    "parse_bench", os.path.join(_REPO, "tools", "perf-l02", "parse_bench.py"))
pb = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pb)


# --------------------------------------------------------------------- spec io
def read_spec(path):
    spec = {"arms": {}, "segments": []}
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or "=" not in line:
                continue
            key, val = line.split("=", 1)
            if key == "arm":
                name, _, env = val.partition(" ")
                spec["arms"][name] = env[len("env="):] if env.startswith("env=") else env
            elif key == "segment":
                parts = val.split()
                spec["segments"].append(
                    {"name": parts[0], "kind": parts[1], "sides": parts[2:4]})
            else:
                spec[key] = val
    return spec


def rep_files(prefix, arm):
    pat = f"{prefix}_{arm}_rep*.txt"
    out = []
    for f in globmod.glob(pat):
        base = os.path.basename(f)
        try:
            n = int(base.rsplit("_rep", 1)[1].split(".")[0])
        except (IndexError, ValueError):
            continue
        out.append((n, f))
    out.sort()
    return [f for _n, f in out]


def series_by_key(files):
    """[(workload,k,impl)] -> list of per-rep minima, in rep order."""
    per_key = {}
    for f in files:
        for key, (mn, _med) in pb.parse_file(f).items():
            per_key.setdefault(key, []).append(mn)
    return per_key


# ------------------------------------------------------------------- statistics
def _stat(v1, v2, paired):
    m1, m2 = statistics.median(v1), statistics.median(v2)
    if paired:
        ds = [(b - a) / a * 100.0 for a, b in zip(v1, v2) if a > 0]
        return statistics.median(ds) if ds else float("nan")
    return (m2 - m1) / m1 * 100.0 if m1 > 0 else float("nan")


def boot_dist(v1, v2, iters, rng, paired):
    n1, n2 = len(v1), len(v2)
    out = []
    if paired:
        n = min(n1, n2)
        for _ in range(iters):
            idx = [rng.randrange(n) for _ in range(n)]
            out.append(_stat([v1[i] for i in idx], [v2[i] for i in idx], True))
    else:
        for _ in range(iters):
            a = [v1[rng.randrange(n1)] for _ in range(n1)]
            b = [v2[rng.randrange(n2)] for _ in range(n2)]
            out.append(_stat(a, b, False))
    return out


def pct(sorted_vals, q):
    if not sorted_vals:
        return float("nan")
    i = min(len(sorted_vals) - 1, int(q * len(sorted_vals)))
    return sorted_vals[i]


def cell_report(v1, v2, iters, rng):
    unpaired = _stat(v1, v2, False)
    paired = _stat(v1, v2, True)
    ud = sorted(abs(x) for x in boot_dist(v1, v2, iters, rng, False))
    pd = sorted(abs(x) for x in boot_dist(v1, v2, iters, rng, True))
    uci = sorted(boot_dist(v1, v2, iters, rng, False))
    pci = sorted(boot_dist(v1, v2, iters, rng, True))
    return {
        "n1": len(v1), "n2": len(v2),
        "med1": statistics.median(v1), "med2": statistics.median(v2),
        "unpaired": unpaired, "paired": paired,
        "u_ci": (pct(uci, 0.025), pct(uci, 0.975)),
        "p_ci": (pct(pci, 0.025), pct(pci, 0.975)),
        "u_p50": pct(ud, 0.50), "u_p95": pct(ud, 0.95), "u_max": ud[-1] if ud else float("nan"),
        "p_p50": pct(pd, 0.50), "p_p95": pct(pd, 0.95), "p_max": pd[-1] if pd else float("nan"),
    }


def analyze_spec(path, ks=None, iters=4000, seed=12345):
    spec = read_spec(path)
    prefix = spec.get("prefix") or os.path.basename(path).replace("_spec.txt", "")
    repdir = os.path.dirname(os.path.abspath(path))
    prefix_path = os.path.join(repdir, prefix)
    result = {"spec": spec, "path": path, "prefix": prefix, "segments": []}
    for seg in spec["segments"]:
        s1, s2 = seg["sides"]
        f1, f2 = rep_files(prefix_path, s1), rep_files(prefix_path, s2)
        if not f1 or not f2:
            print(f"WARN {prefix}: segment {seg['name']} missing reps "
                  f"({s1}={len(f1)}, {s2}={len(f2)})", file=sys.stderr)
            continue
        rng = random.Random(seed)
        d1, d2 = series_by_key(f1), series_by_key(f2)
        cells = {}
        for key in sorted(set(d1) & set(d2)):
            if ks and key[1] not in ks:
                continue
            cells[key] = cell_report(d1[key], d2[key], iters, rng)
        result["segments"].append({"seg": seg, "cells": cells,
                                   "raw": {k: (d1[k], d2[k]) for k in cells}})
    return result


def decide(analysis, iters, seed, min_floor=0.5):
    """Return list of per-cell verdict rows, floors taken from null segments.

    Effective floor = max(same-batch null p95, min_floor) as mandated by the
    Lead's rule |ratio-1| > max(floor, 0.5%)."""
    rows = []
    for segres in analysis["segments"]:
        seg = segres["seg"]
        if seg["kind"] != "exp":
            continue
        nulls = [s for s in analysis["segments"] if s["seg"]["kind"] == "null"]
        if not nulls:
            print(f"WARN {analysis['prefix']}: no null segment; cannot decide",
                  file=sys.stderr)
        for key, st in sorted(segres["cells"].items()):
            raw_u = max([n["cells"][key]["u_p95"] for n in nulls if key in n["cells"]],
                        default=float("nan"))
            raw_p = max([n["cells"][key]["p_p95"] for n in nulls if key in n["cells"]],
                        default=float("nan"))
            fu = max(raw_u, min_floor) if raw_u == raw_u else float("nan")
            fp = max(raw_p, min_floor) if raw_p == raw_p else float("nan")
            dec_u = abs(st["unpaired"]) > fu if fu == fu else None
            dec_p = abs(st["paired"]) > fp if fp == fp else None
            # PRIMARY = paired statistic vs paired null floor: the arms are
            # interleaved and adjacent in time, so pairing removes the slow walt
            # gear drift that inflates the unpaired floor to ~16-19% on a
            # drifting batch (validated on the existing 42-rep nullab batch).
            if dec_p is None:
                overall = "无空对照"
            elif dec_p and dec_u:
                overall = "判定(配对+非配对)"
            elif dec_p:
                overall = "判定(配对);非配对未过(地板受档位漂移抬高)"
            elif dec_u:
                overall = "未判定(配对);非配对超地板(查配对分布)"
            else:
                overall = "未判定"
            rows.append({
                "workload": key[0], "k": key[1], "impl": key[2],
                "unpaired": st["unpaired"], "paired": st["paired"],
                "u_ci": st["u_ci"], "p_ci": st["p_ci"],
                "floor_u": fu, "floor_p": fp,
                "raw_floor_u": raw_u, "raw_floor_p": raw_p,
                "dec_u": dec_u, "dec_p": dec_p, "verdict": overall,
                "med1": st["med1"], "med2": st["med2"], "n": st["n1"],
            })
    return rows


def report(analysis, rows, dump=False):
    spec = analysis["spec"]
    print(f"== {spec.get('tag','?')}  ({os.path.basename(analysis['path'])}) ==")
    print(f"   workload={spec.get('workload')} max_k={spec.get('max_k')} "
          f"rounds={spec.get('rounds')} reps/side={spec.get('reps')} "
          f"only={spec.get('only')} sha256={str(spec.get('binary_sha256'))[:12]}")
    for segres in analysis["segments"]:
        seg = segres["seg"]
        def _bin(side):
            b = spec.get("bin_a" if side in ("A", "nA1", "nA2") else "bin_b")
            return f" bin={os.path.basename(b)}" if b else ""
        print(f"   segment {seg['name']} [{seg['kind']}]: "
              f"{seg['sides'][0]}(env={analysis['spec']['arms'].get(seg['sides'][0],'?')}"
              f"{_bin(seg['sides'][0])}) "
              f"vs {seg['sides'][1]}(env={analysis['spec']['arms'].get(seg['sides'][1],'?')}"
              f"{_bin(seg['sides'][1])})")
        print(f"     {'workload':<10}{'k':>3} {'impl':<6}{'n':>4}"
              f"{'med1':>10}{'med2':>10}{'unpaired%':>11}{'paired%':>10}"
              f"{'u_boot95':>11}{'p_boot95':>11}")
        for key, st in sorted(segres["cells"].items()):
            print(f"     {key[0]:<10}{key[1]:>3} {key[2]:<6}{st['n1']:>4}"
                  f"{st['med1']:>10.4f}{st['med2']:>10.4f}{st['unpaired']:>11.3f}"
                  f"{st['paired']:>10.3f}{st['u_p95']:>12.3f}{st['p_p95']:>12.3f}")
        if dump:
            for key, (v1, v2) in sorted(segres["raw"].items()):
                print(f"     raw {key}: {seg['sides'][0]}={['%.4f' % x for x in v1]}")
                print(f"     raw {key}: {seg['sides'][1]}={['%.4f' % x for x in v2]}")
    if rows:
        print("   --- verdict (exp segment vs same-batch null floors) ---")
        print(f"     {'workload':<10}{'k':>3} {'unpaired%':>10}{'u_ci95':>18}"
              f"{'floor_u':>9}{'paired%':>10}{'p_ci95':>18}{'floor_p':>9}  verdict")
        for r in rows:
            print(f"     {r['workload']:<10}{r['k']:>3} {r['unpaired']:>10.3f}"
                  f"  [{r['u_ci'][0]:>6.2f},{r['u_ci'][1]:>6.2f}] {r['floor_u']:>9.3f}"
                  f" {r['paired']:>9.3f}  [{r['p_ci'][0]:>6.2f},{r['p_ci'][1]:>6.2f}]"
                  f" {r['floor_p']:>9.3f}  {r['verdict']}")
    print()


def selftest():
    rng = random.Random(7)
    n = 21
    base = [6.3 * (1 + rng.gauss(0, 0.01)) for _ in range(n)]
    # null: two draws of the same truth -> must NOT be decided
    a = [x * (1 + rng.gauss(0, 0.006)) for x in base]
    b = [x * (1 + rng.gauss(0, 0.006)) for x in base]
    st = cell_report(a, b, 4000, rng)
    ok_null = abs(st["unpaired"]) <= st["u_p95"] and abs(st["paired"]) <= st["p_p95"]
    # effect: 30% slower B -> must be decided
    b2 = [x * 1.30 * (1 + rng.gauss(0, 0.006)) for x in base]
    st2 = cell_report(a, b2, 4000, rng)
    ok_eff = abs(st2["unpaired"]) > st["u_p95"] and abs(st2["paired"]) > st["p_p95"]
    print(f"selftest null : unpaired={st['unpaired']:+.3f}% floor95={st['u_p95']:.3f}% "
          f"paired={st['paired']:+.3f}% floor95={st['p_p95']:.3f}% -> {'OK' if ok_null else 'FAIL'}")
    print(f"selftest +30% : unpaired={st2['unpaired']:+.3f}% floor95={st['u_p95']:.3f}% "
          f"paired={st2['paired']:+.3f}% floor95={st['p_p95']:.3f}% -> {'OK' if ok_eff else 'FAIL'}")
    return 0 if (ok_null and ok_eff) else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("specs", nargs="*", help="exp-*_spec.txt files (or globs)")
    ap.add_argument("--ks", default="", help="comma list of k to report, e.g. 13,15")
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--min-floor", type=float, default=0.5,
                    help="Lead's rule floor: effective = max(null p95, this) in %%")
    ap.add_argument("--dump", action="store_true", help="print raw per-rep series")
    ap.add_argument("--tsv", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()

    files = sorted({f for pat in args.specs for f in globmod.glob(pat)})
    if not files:
        print("no spec files matched", file=sys.stderr)
        return 1
    ks = {int(x) for x in args.ks.split(",") if x.strip()} or None
    all_rows = []
    for f in files:
        ana = analyze_spec(f, ks=ks, iters=args.iters, seed=args.seed)
        rows = decide(ana, args.iters, args.seed, min_floor=args.min_floor)
        report(ana, rows, dump=args.dump)
        all_rows.extend(rows)
    if args.tsv:
        print("workload\tk\timpl\tn\tmed1\tmed2\tunpaired_pct\tpaired_pct\t"
              "null_p95_u\teff_floor_u\tnull_p95_p\teff_floor_p\tverdict")
        for r in all_rows:
            print(f"{r['workload']}\t{r['k']}\t{r['impl']}\t{r['n']}\t{r['med1']:.4f}\t"
                  f"{r['med2']:.4f}\t{r['unpaired']:.3f}\t{r['paired']:.3f}\t"
                  f"{r['raw_floor_u']:.3f}\t{r['floor_u']:.3f}\t"
                  f"{r['raw_floor_p']:.3f}\t{r['floor_p']:.3f}\t{r['verdict']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
