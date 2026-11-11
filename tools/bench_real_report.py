#!/usr/bin/env python3
"""汇总 L07–L13 真实语料基准日志 -> Markdown 表格（供报告粘贴）。

输入（默认 target/bench_real/）：
  realbench_L07..L12.txt          # tools/run_realistic_bench.ps1 输出
  synthetic_*.txt                 # tools/run_synthetic_anchor.ps1 输出
  l13_workload_*.txt              # tools/run_l13_real.ps1 输出
  l13_file_core.txt / l13_file_hdl.txt
  l13_typort_check.txt
  lsp_kick.txt                    # 可选：twin_engine_bench 输出
用法：
  python tools/bench_real_report.py [--out-dir target/bench_real]
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

RE_SUMMARY = re.compile(r"^SUMMARY,(L\d\d),pass=(\d+),skip=(\d+)", re.M)
RE_TOTAL = re.compile(r"^TOTAL4?,(L\d\d),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+)", re.M)
RE_CASE = re.compile(
    r"^CASE,(L\d\d),([^,]+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+)"
)
RE_WORKLOAD = re.compile(r"^== workload: (.+) ==", re.M)
RE_LABEL = re.compile(r"^-- (.+?) \((\d+) decls\)")
RE_ROW = re.compile(r"^\s+(basic|fast_ss|fast_run|fast)\s+([\d.]+)ms\*?\s+med\s+([\d.]+)ms")
RE_FILE = re.compile(r"^### (.+)$")
RE_CHECK = re.compile(r"^CHECK,(.+?),([\d.]+)ms,exit=(\d+)")
RE_BENCH = re.compile(
    r"\[BENCH(-ERR)?\] (\w+): .*?steady-state min=([\d.]+) avg=([\d.]+) ms/kick"
)
RE_EX_TOTAL = re.compile(r"\[BENCH-EX\] TOTAL ref=(\d+) ms twin=(\d+) ms \(([\d.]+)x\)")
RE_EX_FILE = re.compile(
    r"\[BENCH-EX\] (\S+\.typort)\s+Reference: first=\s*([\d.]+) min=\s*([\d.]+) ms \| "
    r"Twin: first=\s*([\d.]+) min=\s*([\d.]+) ms \| x([\d.]+)"
)
RE_K = re.compile(r"^k=(\d+)\s+n=(\d+)\s+(.*)$")
RE_PAIR = re.compile(r"(\w+)=\s*([\d.]+)ms")


def read_text_auto(path: Path) -> str:
    """读日志：兼容 UTF-8(含 BOM) 与 Windows PowerShell Tee-Object 的 UTF-16LE BOM。"""
    b = path.read_bytes()
    if b[:2] == b"\xff\xfe":
        return b[2:].decode("utf-16-le", errors="replace")
    if b[:2] == b"\xfe\xff":
        return b[2:].decode("utf-16-be", errors="replace")
    if b[:3] == b"\xef\xbb\xbf":
        return b[3:].decode("utf-8", errors="replace")
    return b.decode("utf-8", errors="replace")


def fmt_ms(us: int) -> str:
    return f"{us / 1000.0:.3f}"


def ratio(a, b) -> str:
    try:
        if not b or a is None:
            return "—"
        r = a / b
        if r == 0:
            return "0"
        if r < 0.01:
            return f"{r:.3f}×"
        if r >= 100:
            return f"{r:.0f}×"
        return f"{r:.2f}×"
    except TypeError:
        return "—"


def parse_realbench(path: Path) -> dict | None:
    text = read_text_auto(path)
    m = RE_SUMMARY.search(text)
    t = RE_TOTAL.search(text)
    if not (m and t):
        return None
    layer = m.group(1)
    n, rounds, repeat, basic, fast_run, fast, fast_ss = (int(x) for x in t.groups()[1:])
    cases = []
    for line in text.splitlines():
        cm = RE_CASE.match(line)
        if cm:
            cases.append(
                {
                    "file": cm.group(2),
                    "decls": int(cm.group(4)),
                    "basic": int(cm.group(5)),
                    "fast_run": int(cm.group(7)),
                    "fast": int(cm.group(9)),
                    "fast_ss": int(cm.group(11)),
                }
            )
    return {
        "layer": layer,
        "pass": int(m.group(2)),
        "skip": int(m.group(3)),
        "n": n,
        "rounds": rounds,
        "repeat": repeat,
        "basic": basic,
        "fast_run": fast_run,
        "fast": fast,
        "fast_ss": fast_ss,
        "cases": cases,
    }


def category(name: str) -> str:
    if name.startswith("ladder_"):
        return "ladder"
    if name.startswith(("proj_", "hw_")):
        return "handwritten"
    return "extracted"


def parse_synthetic(path: Path) -> dict | None:
    text = read_text_auto(path)
    wm = RE_WORKLOAD.search(text)
    name = wm.group(1) if wm else path.stem
    best = None
    for line in text.splitlines():
        m = RE_K.match(line)
        if not m:
            continue
        k = int(m.group(1))
        pairs = {mm.group(1): float(mm.group(2)) for mm in RE_PAIR.finditer(m.group(3))}
        if best is None or k > best["k"]:
            best = {"k": k, **pairs}
    if not best:
        return None
    return {"name": name, "file": path.stem, **best}


def parse_l13_workload(path: Path) -> list[dict]:
    rows: list[dict] = []
    workload = ""
    cur = None
    for line in read_text_auto(path).splitlines():
        m = RE_WORKLOAD.match(line)
        if m:
            workload = m.group(1)
            cur = None
            continue
        m = RE_LABEL.match(line)
        if m:
            cur = {
                "workload": workload,
                "label": m.group(1),
                "decls": int(m.group(2)),
                "basic": None,
                "fast": None,
                "fast_ss": None,
            }
            rows.append(cur)
            continue
        m = RE_ROW.match(line)
        if m and cur is not None:
            cur[m.group(1)] = float(m.group(2))
    return [r for r in rows if r.get("basic") or r.get("fast") or r.get("fast_ss")]


def parse_l13_files(path: Path) -> list[dict]:
    rows: list[dict] = []
    cur = None
    for line in read_text_auto(path).splitlines():
        m = RE_FILE.match(line)
        if m:
            cur = {
                "file": m.group(1),
                "decls": 0,
                "verdict": "",
                "basic": None,
                "fast": None,
                "fast_ss": None,
            }
            rows.append(cur)
            continue
        m = RE_LABEL.match(line)
        if m and cur is not None:
            cur["decls"] = int(m.group(2))
            cur["verdict"] = line.split(")", 1)[-1].strip()[:40]
            continue
        m = RE_ROW.match(line)
        if m and cur is not None:
            cur[m.group(1)] = float(m.group(2))
    return [r for r in rows if r.get("basic") or r.get("fast")]


def parse_check(path: Path) -> list[dict]:
    rows = []
    for line in read_text_auto(path).splitlines():
        m = RE_CHECK.match(line)
        if m:
            rows.append({"file": m.group(1), "ms": float(m.group(2)), "exit": m.group(3)})
    return rows


def parse_lsp(path: Path) -> dict:
    kicks: list[dict] = []
    ex_files: list[dict] = []
    ex_total = None
    for line in read_text_auto(path).splitlines():
        m = RE_BENCH.search(line)
        if m:
            kicks.append(
                {
                    "scenario": "error-state kick" if m.group(1) else "clean kick",
                    "engine": m.group(2),
                    "min": float(m.group(3)),
                    "avg": float(m.group(4)),
                }
            )
            continue
        m = RE_EX_TOTAL.search(line)
        if m:
            ex_total = {"ref": float(m.group(1)), "twin": float(m.group(2)), "ratio": m.group(3)}
            continue
        m = RE_EX_FILE.search(line)
        if m:
            ex_files.append(
                {
                    "file": m.group(1),
                    "ref": float(m.group(3)),
                    "twin": float(m.group(5)),
                    "ratio": float(m.group(6)),
                }
            )
    return {"kicks": kicks, "ex_total": ex_total, "ex_files": ex_files}


def main() -> int:
    import sys

    # Windows 控制台默认 GBK，表格里有 µ/× 等字符，强制 stdout 走 UTF-8。
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="target/bench_real")
    args = ap.parse_args()
    d = Path(args.out_dir)
    out: list[str] = []

    # 1) L07–L12 真实语料：整目录 + 分来源
    rows = [r for p in sorted(d.glob("realbench_L*.txt")) if (r := parse_realbench(p))]
    out.append("## L07–L12 真实语料（整目录一遍的总时间，min of rounds）\n")
    out.append(
        "| 层 | PASS/SKIP | 用例数 | basic (ms) | fast_run (ms) | fast (ms) | fast_ss (ms) | fast/basic | fast_ss/basic |"
    )
    out.append("|---|---|---|---:|---:|---:|---:|---:|---:|")
    for r in rows:
        out.append(
            f"| {r['layer']} | {r['pass']}/{r['skip']} | {r['n']} | {fmt_ms(r['basic'])} | "
            f"{fmt_ms(r['fast_run'])} | {fmt_ms(r['fast'])} | {fmt_ms(r['fast_ss'])} | "
            f"{ratio(r['fast'], r['basic'])} | {ratio(r['fast_ss'], r['basic'])} |"
        )
    out.append("")

    # 1b) 分来源（extracted / handwritten / ladder）
    out.append("## L07–L12 真实语料分来源（basic 合计，µs；阶梯单列）\n")
    out.append("| 层 | extracted basic | handwritten basic | ladder basic | 不含 ladder basic | 阶梯占比 |")
    out.append("|---|---:|---:|---:|---:|---:|")
    for r in rows:
        agg: dict[str, int] = {}
        for c in r["cases"]:
            agg[category(c["file"])] = agg.get(category(c["file"]), 0) + c["basic"]
        no_ladder = r["basic"] - agg.get("ladder", 0)
        share = (agg.get("ladder", 0) / r["basic"]) if r["basic"] else 0
        out.append(
            f"| {r['layer']} | {agg.get('extracted', 0)} | {agg.get('handwritten', 0)} | "
            f"{agg.get('ladder', 0)} | {no_ladder} | {share:.0%} |"
        )
    out.append("")

    # 2) 合成锚点
    syn = [s for p in sorted(d.glob("synthetic_*.txt")) if (s := parse_synthetic(p))]
    if syn:
        out.append("## 合成负载锚点（同 HEAD 二进制；取该文件最大 k 的一行，min）\n")
        out.append("| 文件 | workload | k | basic (ms) | fast_run (ms) | fast (ms) | fast_ss (ms) | fast_ss/basic |")
        out.append("|---|---|---:|---:|---:|---:|---:|---:|")
        for s in syn:
            out.append(
                f"| {s['file']} | {s['name']} | {s['k']} | {s.get('basic', '—')} | "
                f"{s.get('fast_run', '—')} | {s.get('fast', '—')} | {s.get('fast_ss', '—')} | "
                f"{ratio(s.get('fast_ss'), s.get('basic'))} |"
            )
        out.append("")

    # 3) L13 全量 workload
    for p in sorted(d.glob("l13_workload_*.txt")):
        wr = parse_l13_workload(p)
        if not wr:
            continue
        out.append(f"## L13 真实负载：{p.stem.replace('l13_workload_', '')}\n")
        out.append("| 负载 | decls | basic (ms) | fast (ms) | fast_ss (ms) | fast/basic | fast_ss/basic |")
        out.append("|---|---:|---:|---:|---:|---:|---:|")
        for r in wr:
            b, f, s = r.get("basic"), r.get("fast"), r.get("fast_ss")
            out.append(
                f"| {r.get('label', r['workload'])} | {r['decls']} | "
                f"{b if b is not None else '—'} | {f if f is not None else '—'} | "
                f"{s if s is not None else '—'} | {ratio(f, b)} | {ratio(s, b)} |"
            )
        out.append("")

    # 4) L13 逐文件 sweep
    for name in ("l13_file_core.txt", "l13_file_hdl.txt"):
        p = d / name
        if not p.exists():
            continue
        fr = parse_l13_files(p)
        if not fr:
            continue
        out.append(f"## L13 逐文件 sweep：{name.replace('l13_file_', '').replace('.txt', '')}\n")
        out.append("| 文件 | decls | 判定 | basic (ms) | fast (ms) | fast_ss (ms) | fast/basic |")
        out.append("|---|---:|---|---:|---:|---:|---:|")
        for r in fr:
            b, f, s = r.get("basic"), r.get("fast"), r.get("fast_ss")
            out.append(
                f"| {r['file']} | {r['decls']} | {r['verdict']} | "
                f"{b if b is not None else '—'} | {f if f is not None else '—'} | "
                f"{s if s is not None else '—'} | {ratio(f, b)} |"
            )
        out.append("")

    # 5) CLI 墙钟
    p = d / "l13_typort_check.txt"
    if p.exists():
        cr = parse_check(p)
        if cr:
            out.append("## L13 `typort check` 墙钟（单次，含 prelude 装载）\n")
            out.append("| 文件 | 墙钟 (ms) | exit |")
            out.append("|---|---:|---:|")
            for r in cr:
                out.append(f"| {r['file']} | {r['ms']} | {r['exit']} |")
            out.append("")

    # 6) LSP kick
    p = d / "lsp_kick.txt"
    if p.exists():
        lr = parse_lsp(p)
        if lr["kicks"]:
            out.append("## L13 LSP per-kick（twin_engine_bench，真实 HDL 文件，稳态 min/avg）\n")
            out.append("| 场景 | 引擎 | min (ms/kick) | avg (ms/kick) |")
            out.append("|---|---|---:|---:|")
            for r in lr["kicks"]:
                out.append(f"| {r['scenario']} | {r['engine']} | {r['min']} | {r['avg']} |")
            out.append("")
        if lr["ex_total"]:
            t = lr["ex_total"]
            out.append("## L13 LSP 逐文件 sweep（32 个真实 HDL/示例文件，稳态 min）\n")
            out.append(
                f"**TOTAL**: ref = {t['ref']:.0f} ms, twin = {t['twin']:.0f} ms, "
                f"twin/ref = {1 / float(t['ratio']):.2f}×（快 {t['ratio']}×）\n"
            )
            out.append("| 文件 | ref min (ms) | twin min (ms) | 加速比 |")
            out.append("|---|---:|---:|---:|")
            for r in sorted(lr["ex_files"], key=lambda x: x["ratio"]):
                out.append(f"| {r['file']} | {r['ref']} | {r['twin']} | {r['ratio']}× |")
            out.append("")

    md = "\n".join(out)
    (d / "summary.md").write_text(md, encoding="utf-8")
    print(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
