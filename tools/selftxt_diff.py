#!/usr/bin/env python3
"""Diff two sampler self.txt reports side by side (tick counts + ns/tick).

Usage: python tools/selftxt_diff.py <a.self.txt> <b.self.txt>
"""
import re
import sys

ROW = re.compile(r"\s*(\d+)\s+([\d.]+)\s+(\d+)\s+(\d+)\s+(\S+)\s*$")


def load(p: str):
    d = {}
    for line in open(p, encoding="utf-8", errors="replace"):
        m = ROW.match(line)
        if m:
            d[m.group(5)] = (int(m.group(3)), int(m.group(1)))
    return d


def short(s: str) -> str:
    return s.replace("src\\L13_namespace\\bump_spine_iter\\", "").replace("src\\L13_namespace\\", "")


def main() -> None:
    a = load(sys.argv[1])
    b = load(sys.argv[2])
    print(f"{'site':<44}{'a ticks':>12}{'b ticks':>12}{'a/b':>7}   a ns   b ns")
    for k in sorted(set(a) | set(b), key=lambda k: -max(a.get(k, (0, 0))[0], b.get(k, (0, 0))[0])):
        ta, na = a.get(k, (0, 0))
        tb, nb = b.get(k, (0, 0))
        r = f"{ta / tb:.2f}" if tb else "-"
        print(f"{short(k):<44}{ta:>12}{tb:>12}{r:>7}  {na:>6} {nb:>7}")


if __name__ == "__main__":
    main()
