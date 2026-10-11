#!/usr/bin/env python3
"""Experiment driver for the 2026-10-11 review rounds.

Scans a round directory for `*.typort` probe files, runs each through
`typort check` (release binary), and classifies the outcome against the
`// expect:` directive in the file header.

Header directives (must appear as `//`-comment lines before any code):
  // probe: <one-line description of what is being tested>
  // expect: ok                      -> no ERROR diagnostics
  // expect: error /REGEX/           -> stderr matches REGEX (Python syntax)
  // expect: error SUBSTR            -> stderr contains SUBSTR
  // expect: stdout /REGEX/          -> stdout matches
  // expect: stdout SUBSTR           -> stdout contains SUBSTR
  // expect: crash                   -> nonzero exit or panic message
  // expect: timeout                 -> run hits the wall-clock limit (bug signal)
  // expect-not: SUBSTR              -> negated secondary check on the whole output
  // mode: emit [-- extra args]      -> run `typort emit` instead of `check`
  // args: <extra CLI args>          -> appended to the command line

Output: <round_dir>/RESULTS.md with one row per experiment plus details
of every non-PASS case.  Exit code counts failures (0 = all as expected).
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

DEFAULT_BIN = Path(__file__).resolve().parents[2] / "target" / "release" / "typort.exe"


def parse_header(text: str) -> dict:
    """Extract header directives from leading // comment lines."""
    hdr = {"probe": "", "expect": None, "expect_not": None, "mode": "check", "args": []}
    for line in text.splitlines():
        s = line.strip()
        if not s.startswith("//"):
            break
        body = s[2:].strip()
        m = re.match(r"(probe|expect-not|expect|mode|args)\s*:\s*(.*)", body)
        if not m:
            continue
        key, val = m.group(1), m.group(2).strip()
        if key == "args":
            hdr["args"] = val.split()
        else:
            hdr[key] = val
    return hdr


def classify(expect: str | None, stdout: str, stderr: str, code: int, timed_out: bool, emit: bool = False) -> tuple[str, str]:
    """Return (verdict, note). verdict in PASS/FAIL/TIMEOUT/NOEXPECT."""
    if expect is None:
        return ("NOEXPECT", "no // expect: header")
    if timed_out:
        return ("TIMEOUT", "hit wall-clock limit") if expect == "timeout" else (
            "FAIL", "unexpected wall-clock timeout")
    if expect == "timeout":
        return ("FAIL", "expected a timeout but it finished")
    if expect == "crash":
        panicked = "panicked" in stderr or "RUST_BACKTRACE" in stderr
        if code != 0 or panicked:
            return ("PASS", f"exit={code}, panic={panicked}")
        return ("FAIL", "expected crash but exited cleanly")
    if expect == "ok":
        if code == 0 and "error:" not in stderr and "panicked" not in stderr:
            return ("PASS", "")
        # surface the offending diagnostic line
        lines = [l for l in stderr.splitlines() if "error:" in l or "panicked" in l]
        return ("FAIL", " | ".join(lines[:2]) or f"exit={code}")
    kind, _, pat = expect.partition(" ")
    if kind == "stdout" and emit:
        # `typort emit` writes the Verilog to fd 1; match the raw stdout.
        if "error:" in stderr or "panicked" in stderr:
            return ("FAIL", "expected Verilog but errors present")
        blob = stdout
    elif kind == "stdout":
        # A program-output expectation means println notes -- and a program
        # with errors cannot have produced them.  Matching the raw combined
        # transcript let rendered line numbers ("3 | ...") and error text
        # ("unreachable pattern: 3") satisfy /3/, masking real failures
        # (found while adjudicating round 4; rounds 2/3 verdicts re-derived).
        if "error:" in stderr or "panicked" in stderr:
            return ("FAIL", "expected program output but errors present")
        notes = "\n".join(l for l in (stdout + "\n" + stderr).splitlines()
                          if l.startswith("note:"))
        blob = notes
    elif kind == "warn":
        # match rendered warning lines only (e.g. the TY001 defaulting notice)
        blob = "\n".join(l for l in (stdout + "\n" + stderr).splitlines()
                         if "warning" in l)
    else:
        blob = stderr
    if pat.startswith("/") and pat.endswith("/") and len(pat) > 2:
        hit = re.search(pat[1:-1], blob) is not None
    else:
        hit = pat in blob
    return ("PASS" if hit else "FAIL", "" if hit else f"no match for {expect!r} (exit={code})")


def run_one(bin_path: Path, file: Path, wall_s: int) -> tuple[str, str, str, int, bool, float]:
    hdr = parse_header(file.read_text(encoding="utf-8", errors="replace"))
    cmd = [str(bin_path)]
    if hdr["mode"].startswith("emit"):
        cmd.append("emit")
        extra = hdr["mode"][4:].strip()
        if extra.startswith("--"):
            cmd += extra.split()[1:]
    else:
        cmd.append(hdr["mode"] if hdr["mode"] in ("check", "build", "test", "doc") else "check")
    cmd += hdr["args"]
    cmd.append(str(file))
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=wall_s)
        out, err, code, to = p.stdout, p.stderr, p.returncode, False
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        err = (e.stderr or b"").decode("utf-8", "replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        code, to = -1, True
    return out, err, code, to, time.monotonic() - t0, hdr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("round_dir", type=Path)
    ap.add_argument("--bin", type=Path, default=DEFAULT_BIN)
    ap.add_argument("--wall", type=int, default=30, help="per-experiment wall-clock seconds")
    args = ap.parse_args()

    files = sorted(args.round_dir.glob("*.typort"))
    if not files:
        print(f"no probes in {args.round_dir}", file=sys.stderr)
        return 2

    rows, details = [], []
    counts = {"PASS": 0, "FAIL": 0, "TIMEOUT": 0, "NOEXPECT": 0}
    for f in files:
        out, err, code, to, dt, hdr = run_one(args.bin, f, args.wall)
        verdict, note = classify(hdr["expect"], out, err, code, to, emit=hdr["mode"].startswith("emit"))
        if hdr["expect_not"]:
            blob = out + err
            if hdr["expect_not"] in blob:
                verdict, note = "FAIL", f"output contains forbidden {hdr['expect_not']!r}"
        counts[verdict] += 1
        rows.append((f.stem, verdict, f"{dt:.2f}s", hdr["probe"], note))
        if verdict != "PASS":
            details.append((f.stem, verdict, note, out, err))

    lines = [f"# {args.round_dir.name} — 实验结果", "",
             f"- probes: {len(files)}  PASS: {counts['PASS']}  FAIL: {counts['FAIL']}  "
             f"TIMEOUT: {counts['TIMEOUT']}  NOEXPECT: {counts['NOEXPECT']}", "",
             "| id | verdict | time | probe | note |", "|---|---|---|---|---|"]
    for rid, v, t, probe, note in rows:
        lines.append(f"| {rid} | {v} | {t} | {probe} | {note} |")
    if details:
        lines += ["", "## 非 PASS 详情", ""]
        for rid, v, note, out, err in details:
            lines += [f"### {rid} — {v}", f"`{note}`", "", "```text",
                      "--- stdout ---", out.strip()[:2000],
                      "--- stderr ---", err.strip()[:2000], "```", ""]
    (args.round_dir / "RESULTS.md").write_text("\n".join(lines), encoding="utf-8")
    print(f"{args.round_dir.name}: {len(files)} probes -> "
          f"PASS {counts['PASS']} FAIL {counts['FAIL']} "
          f"TIMEOUT {counts['TIMEOUT']} NOEXPECT {counts['NOEXPECT']}")
    return counts["FAIL"] + counts["NOEXPECT"]


if __name__ == "__main__":
    sys.exit(main())
