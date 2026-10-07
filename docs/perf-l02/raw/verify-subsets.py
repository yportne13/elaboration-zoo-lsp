#!/usr/bin/env python3
"""Independent freq-aware subset analysis for the C2 batch (task-10 verify).

Splits the `ab` segment pairs by frequency platform / order / time half and
recomputes the paired median relative difference + sign-flip p, and the same
for the nullB segment (which sits on the same low-frequency platform as `ab`).
"""
import glob
import os
import random
import re
import statistics
import sys

sys.path.insert(0, "/tmp/l02-verify")
from verify_analyze import parse_rep, paired, discover_keys  # noqa: E402


def load(spec_path):
    spec, segs = {}, []
    with open(spec_path) as fh:
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
    prefix = os.path.join(os.path.dirname(os.path.abspath(spec_path)), spec["prefix"])
    return spec, segs, prefix


def arm_vals(prefix, arm, key):
    files = sorted(((int(re.search(r"_rep(\d+)\.txt$", f).group(1)), f)
                    for f in glob.glob(f"{prefix}_{arm}_rep*.txt")), key=lambda t: t[0])
    out = []
    for n, f in files:
        d = parse_rep(f)
        out.append((n, d.get(key, {}).get("fast")))
    return out


def freq_map(prefix):
    """(seg,arm,rep) -> (fb, fa)"""
    fm = {}
    path = glob.glob(prefix + "_freqs.tsv")
    if not path:
        return fm
    with open(path[0]) as fh:
        next(fh)
        for line in fh:
            p = line.rstrip("\n").split("\t")
            if len(p) >= 6:
                fm[(p[0], p[1], int(p[2]))] = (int(p[4]), int(p[5]))
    return fm


def substat(a, b, seed=7, iters=4000):
    d = paired(a, b)
    if not d:
        return None
    rng = random.Random(seed)
    n = len(d)
    boot = sorted(abs(statistics.median([d[rng.randrange(n)] for _ in range(n)]))
                  for _ in range(iters))
    p95 = boot[min(len(boot) - 1, int(0.95 * len(boot)))]
    obs = abs(statistics.median(d))
    hits = sum(1 for _ in range(8000)
               if abs(statistics.median([x if rng.random() < .5 else -x for x in d])) >= obs)
    return dict(n=n, md=statistics.median(d), p95=p95, sfp=hits / 8000,
                med1=statistics.median(a), med2=statistics.median(b))


def main():
    spec_path = sys.argv[1]
    key = (sys.argv[2], int(sys.argv[3]))
    spec, segs, prefix = load(spec_path)
    fm = freq_map(prefix)
    A = dict(arm_vals(prefix, "A", key))
    B = dict(arm_vals(prefix, "B", key))
    nA1 = dict(arm_vals(prefix, "nA1", key))
    nA2 = dict(arm_vals(prefix, "nA2", key))
    nB1 = dict(arm_vals(prefix, "nB1", key))
    nB2 = dict(arm_vals(prefix, "nB2", key))
    reps = sorted(set(A) & set(B))

    def pair_ok(i, arms, want):
        for arm in arms:
            f = fm.get(("ab", arm, i))
            if f is None or f[0] != want or f[1] != want:
                return False
        return True

    def show(label, idx):
        a = [A[i] for i in idx if A.get(i) is not None]
        b = [B[i] for i in idx if B.get(i) is not None]
        r = substat(a, b)
        if r:
            print(f"{label:<42} n={r['n']:>3}  med {r['med1']:.4f}->{r['med2']:.4f}  "
                  f"md={r['md']:+7.3f}%  boot95={r['p95']:.3f}  signflip_p={r['sfp']:.4f}")
        else:
            print(f"{label:<42} n=0")

    print(f"# {os.path.basename(spec_path)} {key}")
    # frequency distribution in ab
    from collections import Counter
    for arm in ("A", "B"):
        c = Counter(fm.get(("ab", arm, i)) for i in reps)
        print(f"# freq(ab,{arm}) {dict(c)}")
    print(f"# freq(nullA,nA1) {dict(Counter(fm.get(('nullA','nA1',i)) for i in sorted(nA1)))}")
    print(f"# freq(nullB,nB1) {dict(Counter(fm.get(('nullB','nB1',i)) for i in sorted(nB1)))}")
    show("ALL ab pairs", reps)
    for plat in (921600, 787200, 1766400, 2361600):
        idx = [i for i in reps if pair_ok(i, ("A", "B"), plat)]
        if idx:
            show(f"same-platform {plat} (all 4 reads)", idx)
    show("odd pairs (A first)", [i for i in reps if i % 2 == 1])
    show("even pairs (B first)", [i for i in reps if i % 2 == 0])
    half = len(reps) // 2
    show(f"first half reps <= {reps[half-1]}", reps[:half])
    show(f"second half reps >= {reps[half]}", reps[half:])
    # quartiles by rep index
    q = len(reps) // 4
    for j in range(4):
        idx = reps[j * q:(j + 1) * q] if j < 3 else reps[3 * q:]
        show(f"quartile {j+1} ({idx[0]}..{idx[-1]})", idx)
    print()
    # nullB same-platform floor
    for plat in (921600, 787200, 1766400):
        i1 = [i for i in sorted(set(nB1) & set(nB2))
              if fm.get(("nullB", "nB1", i)) == (plat, plat)
              and fm.get(("nullB", "nB2", i)) == (plat, plat)]
        if i1:
            r = substat([nB1[i] for i in i1], [nB2[i] for i in i1])
            print(f"nullB same-platform {plat:<8} n={r['n']:>3} md={r['md']:+7.3f}% "
                  f"boot95={r['p95']:.3f} signflip_p={r['sfp']:.4f}")
    for lbl, d1, d2 in (("nullA", nA1, nA2), ("nullB", nB1, nB2)):
        common = sorted(set(d1) & set(d2))
        r = substat([d1[i] for i in common], [d2[i] for i in common])
        print(f"{lbl} all n={r['n']:>3} md={r['md']:+7.3f}% boot95={r['p95']:.3f} "
              f"signflip_p={r['sfp']:.4f}")


if __name__ == "__main__":
    main()
