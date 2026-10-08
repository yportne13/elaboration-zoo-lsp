#!/usr/bin/env python3
"""Per-file and per-area documentation coverage for the builtin prelude.

Reads the JSON produced by `typort doc --format json` and reports how many
top-level items carry a doc comment, per prelude file and per area.

Usage
-----
    # 1. generate the JSON (the binary bakes the prelude in, so rebuild first)
    typort doc target/prelude_scratch/doc_measure.typort \
        --out target/doc_json --format json --min-coverage 0

    # 2. report (accepts either the doc.json path or the output directory)
    python tools/prelude_doc_cov.py target/doc_json/doc.json
    python tools/prelude_doc_cov.py target/doc_json
    python tools/prelude_doc_cov.py target/doc_json --nested
    python tools/prelude_doc_cov.py target/doc_json --fail-under 60   # gate usage

Options
-------
    --nested            also count member-level items: methods, enum cases,
                        record fields, variants and constructors. Without it
                        only the 370-ish top-level items per file are counted,
                        which is the number the prelude doc work is measured in.
    --fail-under PCT    exit 1 when the TOTAL percentage is below PCT, so the
                        script can be used as a documentation gate.
    --quiet             print only the summary + TOTAL lines.

Why a separate source file per item matters
-------------------------------------------
`typort doc` reports `docs: null` for an undocumented item; the `source.uri` is
`builtin:///<file>.typort`, so grouping by its basename gives the per-file view.
Areas follow the prelude load groups: every `hdl-*.typort` is "hdl",
`show.typort` is "show", and everything else (the op/eq/nat/... data files) is
"core+data".
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from collections import defaultdict

# Member-level collections the doc model may attach to a top-level item.
# "members" is the key `typort doc` actually emits today (trait methods, enum
# cases, record fields, ...); the rest are kept for forward compatibility.
# NOTE: round 1 listed only the speculative names and missed "members", so
# --nested silently counted nothing. Keep "members" first.
NESTED_KEYS = ("members", "methods", "cases", "variants", "fields", "constructors")


def parse_args(argv):
    p = argparse.ArgumentParser(
        description="Per-file doc coverage for the builtin prelude (typort doc JSON).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("doc_json", help="path to doc.json, or the directory containing it")
    p.add_argument("--nested", action="store_true",
                   help="also count methods / enum cases / record fields")
    p.add_argument("--fail-under", type=float, default=None, metavar="PCT",
                   help="exit 1 if the TOTAL percentage is below PCT")
    p.add_argument("--quiet", action="store_true",
                   help="print only the summary and TOTAL lines")
    return p.parse_args(argv)


def resolve_json_path(arg: str) -> str:
    """Accept either doc.json itself or the directory that holds it."""
    if os.path.isdir(arg):
        cand = os.path.join(arg, "doc.json")
        if not os.path.isfile(cand):
            raise SystemExit("no doc.json inside directory: %s" % arg)
        return cand
    if not os.path.isfile(arg):
        raise SystemExit("no such file: %s" % arg)
    return arg


def area_of(uri: str) -> str:
    name = uri.rsplit("/", 1)[-1]
    if "hdl-" in name:
        return "hdl"
    if name == "show.typort":
        return "show"
    return "core+data"


def main(argv) -> int:
    args = parse_args(argv)
    path = resolve_json_path(args.doc_json)
    with open(path, encoding="utf-8") as fh:
        doc = json.load(fh)

    items = doc.get("items") or []
    warnings = doc.get("warnings") or []

    # per-file [documented, total]
    by_file = defaultdict(lambda: [0, 0])
    # per-area [documented, total]
    by_area = defaultdict(lambda: [0, 0])

    for it in items:
        uri = ((it.get("source") or {}).get("uri")) or "<none>"
        base = uri.rsplit("/", 1)[-1]
        entries = [it]
        if args.nested:
            for key in NESTED_KEYS:
                for member in it.get(key) or []:
                    entries.append(member)
        for e in entries:
            by_file[base][1] += 1
            by_area[area_of(uri)][1] += 1
            if e.get("docs"):
                by_file[base][0] += 1
                by_area[area_of(uri)][0] += 1

    if not args.quiet:
        print("source: %s" % path)
        print("summary: documented=%s  items=%s  warnings=%s"
              % (doc.get("documented"), len(items), len(warnings)))
        for w in warnings:
            print("  warning: %s" % w)
        scope = "items + members" if args.nested else "top-level items"
        print("scope: %s" % scope)

    def pct(d, t):
        return (100.0 * d / t) if t else 0.0

    if not args.quiet:
        print("")
        print("%-41s %5s %5s %7s" % ("prelude file", "doc", "tot", "pct"))
        print("-" * 62)
    for base in sorted(by_file, key=lambda b: (pct(*by_file[b]), b)):
        d, t = by_file[base]
        if not args.quiet:
            print("%-41s %5d %5d %6.1f%%" % (base, d, t, pct(d, t)))

    if not args.quiet:
        print("")
        print("%-41s %5s %5s %7s" % ("area", "doc", "tot", "pct"))
        print("-" * 62)
    for area in sorted(by_area):
        d, t = by_area[area]
        if not args.quiet:
            print("%-41s %5d %5d %6.1f%%" % (area, d, t, pct(d, t)))

    d = sum(v[0] for v in by_file.values())
    t = sum(v[1] for v in by_file.values())
    total_pct = pct(d, t)
    print("")
    print("%-41s %5d %5d %6.1f%%" % ("TOTAL", d, t, total_pct))
    print("documented=%d  items=%d  pct=%.1f%%" % (d, t, total_pct))

    if args.fail_under is not None and total_pct < args.fail_under:
        print("FAIL: %.1f%% is below --fail-under %.1f%%" % (total_pct, args.fail_under),
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
