#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""smallttbench 日志 → Markdown 汇总。

输入：tools/smalltt_bench.ps1 产出的 <profile>_<layer>.csv（CASE/SKIP 行）。
输出：按 profile 分组的 Markdown：
  1) 各层主口径表（elab 用例取 ref/ref_nf 中"主"轴；nf 用例取 ref_nf/twin_nf）
  2) SKIP/失败表
用法：
  python tools/smalltt_bench_report.py --dir target/smalltt_bench/final
"""
import argparse
import collections
import os
import re
import sys

NF_CASES = {"forcetree", "nftree"}
AXES = ["ref", "ref_nf", "twin", "twin_nf"]


def parse_dir(d):
    rows = {}   # (profile, layer, case, size) -> dict
    skips = []  # (profile, layer, case, size, reason)
    pat = re.compile(r"^(default|fuel|stlc)_(?:[a-z0-9]+_)?(L\d\d)\.csv$")
    for name in sorted(os.listdir(d)):
        m = pat.match(name)
        if not m:
            continue
        profile, layer = m.group(1), m.group(2)
        with open(os.path.join(d, name), "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                line = line.strip()
                if line.startswith("CASE,"):
                    p = line.split(",")
                    if len(p) < 17:
                        continue
                    _, lay, case, size = p[0], p[1], p[2], p[3]
                    try:
                        vals = [int(x) for x in p[6:14]]
                        ok = (int(p[14]), int(p[15]))
                        nodes = int(p[16])
                    except ValueError:
                        continue
                    rows[(profile, lay, case, size)] = {
                        "ref": vals[0], "ref_med": vals[1],
                        "ref_nf": vals[2], "ref_nf_med": vals[3],
                        "twin": vals[4], "twin_med": vals[5],
                        "twin_nf": vals[6], "twin_nf_med": vals[7],
                        "ok": ok, "nodes": nodes,
                    }
                elif line.startswith("SKIP,"):
                    p = line.split(",")
                    if len(p) >= 5:
                        skips.append((profile, p[1], p[2], p[3], p[4]))
    return rows, skips


def ms(us):
    return "-" if not us else "%.3f" % (us / 1000.0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    rows, skips = parse_dir(a.dir)
    out = []
    out.append("# smalltt 迁移基准汇总（自动生成）\n")
    out.append("单位 ms；每格 = 该口径 min-of-rounds。\n")
    profiles = ["default", "fuel", "stlc"]
    for prof in profiles:
        keys = [k for k in rows if k[0] == prof]
        if not keys:
            continue
        out.append("\n## profile: %s\n" % prof)
        cases = sorted({k[2] for k in keys})
        for case in cases:
            sizes = sorted({k[3] for k in keys if k[2] == case}, key=lambda s: (len(s), s))
            layers = sorted({k[1] for k in keys if k[2] == case})
            nf = case in NF_CASES
            out.append("\n### %s（%s 口径）\n" % (case, "nf" if nf else "elab"))
            hdr = "| size | " + " | ".join(layers) + " | 说明 |"
            sep = "|---|" + "---|" * len(layers) + "---|"
            out.append(hdr)
            out.append(sep)
            for size in sizes:
                cells = []
                note = ""
                for lay in layers:
                    r = rows.get((prof, lay, case, size))
                    if r is None:
                        cells.append("-")
                        continue
                    if nf:
                        cells.append("%s / %s" % (ms(r["ref_nf"]), ms(r["twin_nf"])))
                    else:
                        cells.append("%s / %s" % (ms(r["ref"]), ms(r["twin"])))
                    if r["nodes"]:
                        note = "nf_nodes=%d" % r["nodes"]
                out.append("| %s | %s | %s |" % (size, " | ".join(cells), note))
            out.append("\n（每格 = 参考版 / 孪生版；nf 用例取 ref_nf / twin_nf）")
    if skips:
        out.append("\n## SKIP / 失败\n")
        out.append("| profile | layer | case | size | reason |")
        out.append("|---|---|---|---|---|")
        # 去重：同一 case/size 在 fuel profile 成功则不列（默认 profile 的 SKIP 是有意义的上限）
        for s in sorted(set(skips)):
            out.append("| %s | %s | %s | %s | %s |" % s)
    text = "\n".join(out) + "\n"
    if a.out:
        with open(a.out, "w", encoding="utf-8") as f:
            f.write(text)
        print("written " + a.out)
    else:
        print(text)


if __name__ == "__main__":
    main()
