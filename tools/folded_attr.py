#!/usr/bin/env python3
"""Aggregate a sampler time-weighted folded file by function (inclusive + leaf).

Usage: python tools/folded_attr.py <time.folded>
"""
import collections
import re
import sys


def short(s: str) -> str:
    s = re.sub(r"^elaboration_zoo_lsp::L13_namespace::bump_spine_iter::", "", s)
    s = re.sub(r"^elaboration_zoo_lsp::", "", s)
    return s[:96]


def main() -> None:
    path = sys.argv[1] if len(sys.argv) > 1 else "target/bench_out/lspsample.folded.time.folded"
    inc: collections.Counter = collections.Counter()
    leaf: collections.Counter = collections.Counter()
    total = 0
    for line in open(path, encoding="utf-8", errors="replace"):
        line = line.rstrip("\n")
        if not line:
            continue
        stack, _, w = line.rpartition(" ")
        try:
            w = int(w)
        except ValueError:
            continue
        frames = [f for f in stack.split(";") if f]
        total += w
        for f in set(frames):
            inc[f] += w
        if frames:
            leaf[frames[-1]] += w
    if not total:
        print("no weighted stacks")
        return
    print(f"total {total / 1e9:.3f}s over {sum(1 for _ in open(path, encoding='utf-8', errors='replace'))} stacks")
    print("== inclusive top 16 ==")
    for f, w in inc.most_common(16):
        print(f"  {w / 1e9:7.3f}s {100 * w / total:5.1f}%  {short(f)}")
    print("== leaf top 12 ==")
    for f, w in leaf.most_common(12):
        print(f"  {w / 1e9:7.3f}s {100 * w / total:5.1f}%  {short(f)}")


if __name__ == "__main__":
    main()
