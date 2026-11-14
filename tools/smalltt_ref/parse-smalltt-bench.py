#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""解析 smalltt REPL 基准日志。

识别行：
  <name> elaborated in 0.1234567s     -> elab（[elabtime] 的 def；或文件整载 "path elaborated in"）
  <name> normalized in 0.1234567s     -> nf  （[nftime]）
  <path> parsed in 0.1234567s         -> parse
  total load time: 0.1234567s         -> total
同 name 在多次 :r 中出现时取 min。输出 JSON：file -> {elab,nf,parse,total}。
用法：python parse-smalltt-bench.py --dir <log dir> --out <parsed.json>
"""
import argparse, collections, glob, json, os, re

PAT_ELAB = re.compile(r"^(.*?) elaborated in ([0-9.]+)s\s*$")
PAT_NF = re.compile(r"^(.*?) normalized in ([0-9.]+)s\s*$")
PAT_PARSE = re.compile(r"^(.*?) parsed in ([0-9.]+)s\s*$")
PAT_TOTAL = re.compile(r"^total load time: ([0-9.]+)s\s*$")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    result = {}
    for path in sorted(glob.glob(os.path.join(a.dir, "*.log"))):
        f = os.path.basename(path)[:-4]
        d = result.setdefault(f, {"elab": collections.defaultdict(list),
                                  "nf": collections.defaultdict(list),
                                  "parse": collections.defaultdict(list),
                                  "total": []})
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.rstrip("\r\n")
                m = PAT_ELAB.match(line)
                if m:
                    d["elab"][m.group(1).strip()].append(float(m.group(2)))
                    continue
                m = PAT_NF.match(line)
                if m:
                    d["nf"][m.group(1).strip()].append(float(m.group(2)))
                    continue
                m = PAT_PARSE.match(line)
                if m:
                    d["parse"][m.group(1).strip()].append(float(m.group(2)))
                    continue
                m = PAT_TOTAL.match(line)
                if m:
                    d["total"].append(float(m.group(1)))
    out = {}
    for f, d in result.items():
        out[f] = {
            "elab": {k: {"min": min(v), "rounds": v} for k, v in d["elab"].items() if v},
            "nf": {k: {"min": min(v), "rounds": v} for k, v in d["nf"].items() if v},
            "parse": {k: {"min": min(v), "rounds": v} for k, v in d["parse"].items() if v},
            "total": {"min": min(d["total"]) if d["total"] else None, "rounds": d["total"]},
        }
    text = json.dumps(out, ensure_ascii=False, indent=1)
    if a.out:
        with open(a.out, "w", encoding="utf-8") as fh:
            fh.write(text)
        print("written " + a.out)
    else:
        print(text)


if __name__ == "__main__":
    main()
