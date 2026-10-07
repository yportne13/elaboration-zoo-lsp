#!/usr/bin/env python3
"""l02-verify: independent re-analysis of exp-ab-run.sh raw reps.

Written from scratch for task-10 adversarial verification. Does NOT import or
call exp-ab-analyze.py / parse_bench.py. Only the raw rep text files and spec
files are consumed.

Per (workload, k, impl) cell:
  * value = first number on the l02bench line = min over --rounds inner rounds
    (same observable the original pipeline uses; the star and the second
    number are ignored).
  * paired  : md = median_i (B_i - A_i)/A_i * 100 over index-matched pairs.
  * bootstrap p95 of |md| (resample pairs with replacement).
  * sign-flip permutation test on the paired relative diffs (independent of the
    bootstrap; valid under the exchangeability of pair signs).
  * unpaired: (median(B)-median(A))/median(A)*100 + its bootstrap p95.

Usage:
  verify_analyze.py --spec SPEC [--cells church:13,conv:13] [--iters 4000]
                    [--signflip 20000] [--dump]
"""
import argparse
import glob
import os
import random
import re
import statistics
import sys

NUM = r"(\d+(?:\.\d+)?)"
LINE_RE = re.compile(r"^k=(\d+)\s+n=(\d+)\b")
VAL_RE = re.compile(r"fast=\s*" + NUM + r"\s*(ms|us|\u00b5s|\u03bcs)?\s*\*?\s*/\s*" + NUM)


def parse_rep(path):
    """{(workload,k): {impl: min_ms}} for one process rep."""
    out = {}
    wl = None
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            line = line.rstrip("\n")
            m = re.match(r"^==\s*workload:\s*(\S+)\s*==", line)
            if m:
                wl = m.group(1)
                continue
            mk = LINE_RE.match(line)
            if wl is None or not mk:
                continue
            k = int(mk.group(1))
            vals = {}
            for name, v, unit, _vmed in re.findall(
                    r"([A-Za-z_][A-Za-z0-9_]*)=\s*" + NUM +
                    r"\s*(ms|us|\u00b5s|\u03bcs)?\s*\*?\s*/\s*" + NUM, line):
                vals[name] = float(v) / 1000.0 if unit in ("us", "\u00b5s", "\u03bcs") else float(v)
            out[(wl, k)] = vals
    return out


def discover_keys(prefix, arm):
    files = sorted(glob.glob(prefix + "_" + arm + "_rep*.txt"))
    if not files:
        return set()
    return set(parse_rep(files[0]).keys())


def rep_series(prefix, arm, keys):
    files = sorted(
        ((int(re.search(r"_rep(\d+)\.txt$", f).group(1)), f)
         for f in glob.glob(prefix + "_" + arm + "_rep*.txt")),
        key=lambda t: t[0])
    per = {key: [] for key in keys}
    used = []
    for n, f in files:
        used.append((n, f))
        d = parse_rep(f)
        for key in keys:
            if key in d:
                per[key].append(d[key]["fast"])
    return per, used


def paired(v1, v2):
    return [(b - a) / a * 100.0 for a, b in zip(v1, v2) if a > 0]


def unpaired(v1, v2):
    m1, m2 = statistics.median(v1), statistics.median(v2)
    return (m2 - m1) / m1 * 100.0


def boot_paired(d, iters, rng):
    n = len(d)
    return [statistics.median([d[rng.randrange(n)] for _ in range(n)]) for _ in range(iters)]


def boot_unpaired(v1, v2, iters, rng):
    n1, n2 = len(v1), len(v2)
    out = []
    for _ in range(iters):
        a = [v1[rng.randrange(n1)] for _ in range(n1)]
        b = [v2[rng.randrange(n2)] for _ in range(n2)]
        out.append(unpaired(a, b))
    return out


def pctl(xs, q):
    s = sorted(xs)
    idx = min(len(s) - 1, int(q * len(s)))
    return s[idx]


def signflip_p(d, iters, rng):
    obs = abs(statistics.median(d))
    n = len(d)
    hits = 0
    for _ in range(iters):
        v = [x if rng.random() < 0.5 else -x for x in d]
        if abs(statistics.median(v)) >= obs:
            hits += 1
    return hits / iters


def analyze_segment(prefix, sides, key, iters, sf, rng):
    v1, _ = rep_series(prefix, sides[0], [key])
    v2, _ = rep_series(prefix, sides[1], [key])
    a, b = v1[key], v2[key]
    d = paired(a, b)
    bp = sorted(abs(x) for x in boot_paired(d, iters, rng))
    return {
        "n": min(len(a), len(b)), "med1": statistics.median(a), "med2": statistics.median(b),
        "md": statistics.median(d) if d else float("nan"),
        "p95": pctl(bp, 0.95), "pmax": bp[-1] if bp else float("nan"),
        "unp": unpaired(a, b),
        "unp_p95": pctl(sorted(abs(x) for x in boot_unpaired(a, b, iters, rng)), 0.95),
        "signflip": signflip_p(d, sf, rng) if d else float("nan"),
        "a": a, "b": b,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", required=True)
    ap.add_argument("--cells", default="",
                    help="comma list workload:k, e.g. church:13,conv:15 (default all)")
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--signflip", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=20261007)
    ap.add_argument("--dump", action="store_true")
    args = ap.parse_args()

    spec = {}
    segs = []
    with open(args.spec) as fh:
        for line in fh:
            line = line.strip()
            if "=" not in line:
                continue
            k, v = line.split("=", 1)
            if k == "segment":
                p = v.split()
                segs.append((p[0], p[1], p[2], p[3]))
            else:
                spec[k] = v
    prefix = os.path.join(os.path.dirname(os.path.abspath(args.spec)), spec["prefix"])
    print(f"# spec={os.path.basename(args.spec)} prefix={spec['prefix']}")
    print(f"# bin_a={os.path.basename(spec.get('bin_a',''))} sha={spec.get('bin_a_sha256','')[:12]} "
          f"bin_b={os.path.basename(spec.get('bin_b',''))} sha={spec.get('bin_b_sha256','')[:12]}")
    print(f"# order={spec.get('order')} reps={spec.get('reps')} rounds={spec.get('rounds')} "
          f"only={spec.get('only')}")

    want = set()
    for c in args.cells.split(","):
        c = c.strip()
        if c:
            w, k = c.split(":")
            want.add((w, int(k)))

    hdr = (f"{'seg':<6}{'workload':<9}{'k':>3}{'n':>4}{'med1':>9}{'med2':>9}"
           f"{'paired%':>10}{'p95':>8}{'unp%':>9}{'unp95':>8}{'signflip_p':>12}")
    print(hdr)
    exp_rows, null_rows = [], []
    for name, kind, s1, s2 in segs:
        keys = set()
        for arm in (s1, s2):
            keys |= discover_keys(prefix, arm)
        for key in sorted(keys):
            if want and key not in want:
                continue
            r = analyze_segment(prefix, (s1, s2), key, args.iters, args.signflip,
                                random.Random(args.seed + key[1] * 97 + (0 if key[0] == "church" else 1)))
            print(f"{name:<6}{key[0]:<9}{key[1]:>3}{r['n']:>4}{r['med1']:>9.4f}{r['med2']:>9.4f}"
                  f"{r['md']:>10.3f}{r['p95']:>8.3f}{r['unp']:>9.3f}{r['unp_p95']:>8.3f}"
                  f"{r['signflip']:>12.5f}")
            (exp_rows if kind == "exp" else null_rows).append((name, key, r))
            if args.dump:
                print(f"   {s1}: {['%.4f' % x for x in r['a']]}")
                print(f"   {s2}: {['%.4f' % x for x in r['b']]}")
    print()
    print("== verdict (paired md vs max(null p95, 0.5)) ==")
    for name, key, r in exp_rows:
        fl = max([n[2]["p95"] for n in null_rows if n[1] == key] + [float("nan")])
        fl_raw = fl
        fl_eff = max(fl, 0.5) if fl == fl else float("nan")
        md = r["md"]
        verdict = "未判定" if abs(md) <= fl_eff else f"判定({'+' if md > 0 else '-'})"
        print(f"{key[0]:<9}k={key[1]:<3} md={md:+8.3f}%  p95_floor={fl_raw:.3f}  "
              f"eff={fl_eff:.3f}  signflip_p={r['signflip']:.4f}  -> {verdict}")
    print("== null segment paired stats (floors) ==")
    for name, key, r in null_rows:
        print(f"{name:<6}{key[0]:<9}k={key[1]:<3} md={r['md']:+8.3f}%  p95={r['p95']:.3f}  "
              f"max={r['pmax']:.3f}  unp={r['unp']:+.3f}% unp95={r['unp_p95']:.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
