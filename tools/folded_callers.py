#!/usr/bin/env python3
"""For each occurrence of a target function in a folded stack, attribute the
weight to its IMMEDIATE CALLER (the frame just below it, i.e. closer to root).

Usage: python tools/folded_callers.py <time.folded> <substring-of-target>
"""
import collections
import re
import sys


def short(s: str) -> str:
    s = re.sub(r"^elaboration_zoo_lsp::L13_namespace::bump_spine_iter::", "", s)
    s = re.sub(r"^elaboration_zoo_lsp::L13_namespace::", "", s)
    s = re.sub(r"^elaboration_zoo_lsp::", "", s)
    return s[:88]


def main() -> None:
    path = sys.argv[1]
    target = sys.argv[2]
    callers: collections.Counter = collections.Counter()
    occurrences: collections.Counter = collections.Counter()
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
        for i, f in enumerate(frames):
            if target in f:
                occurrences[f] += w
                caller = frames[i - 1] if i > 0 else "<root>"
                callers[short(caller)] += w
    print(f"total {total / 1e9:.3f}s")
    print(f"== frames matching '{target}' (inclusive weight) ==")
    for f, w in occurrences.most_common(6):
        print(f"  {w / 1e9:7.3f}s {100 * w / total:5.1f}%  {short(f)}")
    print(f"== immediate callers of '{target}' ==")
    for f, w in callers.most_common(14):
        print(f"  {w / 1e9:7.3f}s {100 * w / total:5.1f}%  {f}")


if __name__ == "__main__":
    main()
