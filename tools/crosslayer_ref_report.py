#!/usr/bin/env python3
"""tools/crosslayer_ref_report.py - summarize L07-L13 reference-engine benchmark logs.

Reads the raw logs written by tools/run_crosslayer_ref.ps1:
    target/bench_real/ref_<TAG>/pass<N>_{common,synth,real}_*.txt
and emits a markdown summary (stdout), also saved next to the logs.

Protocol recap: each pass runs the whole matrix serially with process isolation;
the harness already reports min-of-rounds. This script takes min across passes
per file/workload, and also reports pass-to-pass spread.

Usage:
    python tools/crosslayer_ref_report.py [out_dir]
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "target" / "bench_real" / "ref_2026-11-12"
LAYERS = [f"L{n:02d}" for n in range(7, 14)]

# ---- previous run (docs/bench-crosslayer-ref-2026-11-11.md, min-of-rounds, ms) ----
OLD_COMMON = {
    "ex_block_comments.typort": [0.021, 0.019, 0.018, 0.016, 0.031, 0.028, 0.021],
    "ex_even_odd.typort": [0.044, 0.042, 0.037, 0.031, 0.059, 0.058, 0.051],
    "ex_line_comments.typort": [0.016, 0.015, 0.012, 0.010, 0.023, 0.023, 0.022],
    "ladder_l07_small.typort": [0.412, 0.406, 0.523, 0.279, 0.563, 0.510, 0.497],
    "ladder_l07_medium.typort": [4.240, 4.255, 7.063, 2.794, 4.069, 3.636, 4.272],
    "ladder_l07_large.typort": [64.062, 65.635, 107.595, 39.618, 49.962, 45.285, 59.311],
}
OLD_COMMON_TOTAL = [68.795, 70.372, 115.248, 42.748, 54.707, 49.540, 64.174]
OLD_SYNTH = {
    "match": [0.097, 0.090, 0.112, 0.089, 0.174, 0.291, 0.156],
    "church": [1.609, 1.476, 2.403, 1.416, 1.447, 1.451, 2.145],
    "natadd": [3.754, 3.016, 4.339, 1.937, 1.727, 1.546, 2.564],
    "strchain": [8.857, 9.640, 65.604, 60.543, 52.365, 52.777, 18.426],
    "enum": [0.179, 0.167, 0.658, None, None, None, 0.413],
    "struct": [None, 5.634, 52.719, 44.923, 20.431, 20.767, 19.703],
    "universe": [None, None, 2.506, 2.381, 22.396, 23.902, 3.351],
    "macro": [None, None, None, None, 18.011, 21.921, 17.704],
}
SYNTH_ORDER = ["match", "church", "natadd", "strchain", "enum", "struct", "universe", "macro"]
SYNTH_K = {"match": 11, "church": 11, "natadd": 11, "strchain": 11, "enum": 9,
           "struct": 10, "universe": 10, "macro": 10}

L13_BASIC_RE = re.compile(r"^\s+basic\s+([0-9.]+)ms\*")
L13_FILE_RE = re.compile(r"^-- (\S+\.typort) \(\d+ decls\)")
L13_REAL_RE = re.compile(r"^-- (\S+) \(\d+ decls\)")


def parse_realbench_cases(path):
    """{file: basic_min_us} from CASE lines (field index 5)."""
    res = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("CASE,"):
            f = line.split(",")
            if len(f) >= 6:
                res[f[2]] = int(f[5])
    return res


def parse_realbench_total(path):
    """basic min-of-round-sums us (TOTAL for parse-out layers, TOTAL4 for L11/L12)."""
    total = None
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith("TOTAL,") or line.startswith("TOTAL4,"):
            f = line.split(",")
            total = int(f[5])
    return total


def parse_l13_basic(path):
    """{header_key: basic_min_ms} for a l13bench log (file / workload / k blocks)."""
    res = {}
    cur = None
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = L13_FILE_RE.match(line) or L13_REAL_RE.match(line)
        if m:
            cur = m.group(1)
            continue
        h = re.match(r"^-- (\S+) k=(\d+) \(", line)
        if h:
            cur = (h.group(1), int(h.group(2)))
            continue
        b = L13_BASIC_RE.match(line)
        if b and cur is not None:
            res[cur] = float(b.group(1))
    return res


def parse_name(p, prefix):
    m = re.match(prefix, p.name)
    return int(m.group(1)) if m else None


def md_table(headers, rows):
    out = ["| " + " | ".join(headers) + " |", "|" + "|".join(["---:"] * len(headers)) + "|"]
    for r in rows:
        out.append("| " + " | ".join(str(x) for x in r) + " |")
    return "\n".join(out)


def main():
    if not OUT_DIR.exists():
        sys.exit(f"missing {OUT_DIR}")

    out = [f"# L07-L13 reference benchmark summary ({OUT_DIR.name})", ""]
    common_files = list(OLD_COMMON.keys())

    # ---------------- collect common ----------------
    cells = {f: {L: [] for L in LAYERS} for f in common_files}   # list of per-pass us
    pass_layer_sum = defaultdict(list)                            # (pass, layer) -> us
    l13_pass_files = defaultdict(dict)                            # pass -> {file: us}
    total_check = defaultdict(list)                               # layer -> TOTAL us per pass
    for path in sorted(OUT_DIR.glob("pass*_common_*.txt")):
        m = re.match(r"pass(\d+)_common_(L\d+)\.txt", path.name)
        if m:
            pr, layer = int(m.group(1)), m.group(2)
            cases = parse_realbench_cases(path)
            for f, v in cases.items():
                if f in cells:
                    cells[f][layer].append(v)
            pass_layer_sum[(pr, layer)].append(sum(cases.values()))
            t = parse_realbench_total(path)
            if t:
                total_check[layer].append(t)
            continue
        m = re.match(r"pass(\d+)_common_L13_(.+)\.txt", path.name)
        if m:
            pr = int(m.group(1))
            for f, v in parse_l13_basic(path).items():
                if f in cells:
                    us = round(v * 1000)
                    cells[f]["L13"].append(us)
                    l13_pass_files[pr][f] = us

    for _, files in l13_pass_files.items():
        pass_layer_sum[("l13", "L13")].append(sum(files.values()))

    missing = [(f, L) for f in common_files for L in LAYERS if not cells[f][L]]
    if missing:
        sys.exit(f"missing common cells: {missing}")
    common_min = {f: {L: min(cells[f][L]) for L in LAYERS} for f in cells}
    layer_total_ms = {L: sum(common_min[f][L] for f in common_files) / 1000.0 for L in LAYERS}
    layer_pass_sums = {L: [] for L in LAYERS}
    for (pr, layer), vals in pass_layer_sum.items():
        layer_pass_sums[layer].extend(vals)

    out.append("## A. strict same files (6 files, reference `basic`, min across passes)")
    out.append("")
    rows = []
    for f in common_files:
        rows.append([f] + [f"{common_min[f][L] / 1000.0:.3f}" for L in LAYERS])
    total_row = []
    for L in LAYERS:
        spread = ""
        if layer_pass_sums[L]:
            spread = f" ({max(layer_pass_sums[L]) / min(layer_pass_sums[L]) - 1:+.1%})"
        total_row.append(f"{layer_total_ms[L]:.3f}{spread}")
    rows.append(["**total**"] + total_row)
    rows.append(["**relative to L07**"] + [f"{layer_total_ms[L] / layer_total_ms['L07']:.2f}x" for L in LAYERS])
    rows.append(["**11-11 total**"] + [f"{v:.3f}" for v in OLD_COMMON_TOTAL])
    rows.append(["**new / 11-11**"] + [f"{layer_total_ms[L] / OLD_COMMON_TOTAL[i]:.2f}x" for i, L in enumerate(LAYERS)])
    out.append(md_table(["file", *LAYERS], rows))
    out.append("")
    out.append("total pass-to-pass spread in parentheses; per-file values are min across passes.")
    out.append("")

    # ---------------- collect synth ----------------
    synth_cells = {(w, L): [] for w in SYNTH_ORDER for L in LAYERS}
    for path in sorted(OUT_DIR.glob("pass*_synth_*.txt")):
        m = re.match(r"pass(\d+)_synth_(L\d+)_(\w+)_k\d+\.txt", path.name)
        if not m:
            continue
        layer, w = m.group(2), m.group(3)
        if w not in SYNTH_ORDER:
            continue
        if layer == "L13":
            entries = parse_l13_basic(path)  # {(workload, k): ms}
            if entries:
                kmax = max(k for (_, k) in entries)
                synth_cells[(w, layer)].append(round(entries[(w, kmax)] * 1000))
        else:
            best_k, val = None, None
            for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
                mm = re.match(r"k=(\d+)\s+.*basic=\s*([0-9.]+)ms\*", line)
                if mm:
                    k = int(mm.group(1))
                    if best_k is None or k > best_k:
                        best_k, val = k, round(float(mm.group(2)) * 1000)
            if val is not None:
                synth_cells[(w, layer)].append(val)

    missing = [k for k, v in synth_cells.items() if not v and OLD_SYNTH[k[0]][LAYERS.index(k[1])] is not None]
    if missing:
        sys.exit(f"missing synth cells: {missing}")
    synth_min = {key: (min(v) if v else None) for key, v in synth_cells.items()}

    out.append("## B. same-family synthetic workloads (largest k, reference `basic`)")
    out.append("")
    rows = []
    for w in SYNTH_ORDER:
        rows.append([f"{w} k={SYNTH_K[w]}"] + ["-" if synth_min[(w, L)] is None else f"{synth_min[(w, L)] / 1000.0:.3f}" for L in LAYERS])
    out.append(md_table(["workload", *LAYERS], rows))
    out.append("")
    out.append("L11/L12 `basic` = reference full `run` (parse+pretty+stdout); others = parse-out `bench_check_nf`.")
    out.append("")

    out.append("### B2. new / 11-11 ratio")
    out.append("")
    rows = []
    for w in SYNTH_ORDER:
        vals = []
        for i, L in enumerate(LAYERS):
            new, old = synth_min[(w, L)], OLD_SYNTH[w][i]
            vals.append("-" if (new is None or old is None) else f"{new / 1000.0 / old:.2f}x")
        rows.append([f"{w} k={SYNTH_K[w]}", *vals])
    out.append(md_table(["workload", *LAYERS], rows))
    out.append("")

    out.append("### B3. pass-to-pass spread (max/min - 1 per measured cell)")
    out.append("")
    spreads = []
    for (w, L), v in synth_cells.items():
        if len(v) >= 2 and min(v) > 0:
            spreads.append((w, L, max(v) / min(v) - 1))
    spreads.sort(key=lambda x: -x[2])
    if spreads:
        med = sorted(s for _, _, s in spreads)[len(spreads) // 2]
        out.append(f"cells measured: {len(spreads)}; median spread {med:.1%}; "
                   f"max spread {spreads[0][2]:.1%} ({spreads[0][0]} {spreads[0][1]})")
        out.append("worst 6: " + ", ".join(f"{w} {L}: {s:.1%}" for w, L, s in spreads[:6]))
    out.append("")

    # ---------------- real appendix ----------------
    out.append("## C. appendix: each layer's own real corpus (reference `basic`, per-layer only)")
    out.append("")
    OLD_REAL_TOTAL = {"L07": 76.551, "L08": 28.973, "L09": 1792.452,
                      "L10": 16.987, "L11": 19.144, "L12": 39.771}
    rows = []
    for L in LAYERS:
        if L == "L13":
            continue
        totals, case_sums = [], []
        for path in sorted(OUT_DIR.glob(f"pass*_real_{L}.txt")):
            t = parse_realbench_total(path)
            if t is not None:
                totals.append(t)
            case_sums.append(sum(parse_realbench_cases(path).values()))
        if totals:
            mn = min(totals) / 1000.0
            old = OLD_REAL_TOTAL[L]
            rows.append([L, f"{len(totals)}", f"{mn:.1f}", f"{max(totals) / 1000.0:.1f}",
                         f"{old:.1f}", f"{mn / old:.2f}x"])
    out.append(md_table(["layer", "passes", "TOTAL min ms", "TOTAL max ms",
                         "11-11 basic ms", "new / 11-11"], rows))
    out.append("")
    OLD_L13_REAL = {"prelude-core": 45.772, "prelude-hdl": 4796.355}
    l13_rows = []
    for w in ["prelude-core", "prelude-hdl", "examples-hdl"]:
        vals = []
        for path in sorted(OUT_DIR.glob(f"pass*_real_L13_{w}.txt")):
            d = parse_l13_basic(path)
            for key, v in d.items():
                if w == "examples-hdl" and key.startswith("examples-hdl"):
                    vals.append(v)
                elif key == w:
                    vals.append(v)
        if vals:
            old = OLD_L13_REAL.get(w)
            detail = f"{min(vals):.1f}-{max(vals):.1f}" if w == "examples-hdl" else f"{min(vals):.1f}"
            l13_rows.append([w, f"{len(vals)} samples", detail,
                             f"{old:.1f}" if old else "-",
                             f"{min(vals) / old:.2f}x" if old else "-"])
    if l13_rows:
        out.append("L13 real workloads (reference `basic`, ms):")
        out.append("")
        out.append(md_table(["workload", "samples", "new min/max", "11-11 basic", "new / 11-11"], l13_rows))
        out.append("")
        out.append("examples-hdl = 6 blocks (214-226 decls); BOTH-FAILED failure-path timing, range shown.")
        out.append("")

    text = "\n".join(out)
    dest = OUT_DIR / "summary.md"
    dest.write_text(text + "\n", encoding="utf-8")
    print(text)
    print(f"\n[written] {dest}")


if __name__ == "__main__":
    main()
