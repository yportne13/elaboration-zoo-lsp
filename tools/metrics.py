#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""tools/metrics.py -- repository-wide static metrics for the Elaboration Zoo.

Purpose
-------
One command that reproduces every size / risk / structure number quoted in the
optimal-design reports (D1-D7, FINAL) and the following cleanup phases (P1).
It is intentionally dependency-free (Python standard library only), runs on
Linux CI and Windows, and never builds, tests or modifies Rust sources.

What it measures
----------------
* Physical lines and non-empty lines for every ``*.rs`` file under ``src/``,
  classified into: per-layer reference side, per-layer twin (``bump_spine_iter*``)
  side, per-layer test files, ``src/bin``, glue (``src/`` non-layer, non-bin
  files), archive (``src/bench_head`` / ``src/bench_pre``) and ``.bak`` files.
* Risk counters: ``unsafe`` (word + block), ``panic!`` / ``unwrap()`` /
  ``expect(`` / ``todo!`` / ``unreachable!``, print macros
  (``println!``/``eprintln!``/``dbg!``) both raw and "production region"
  (approximation: everything from the first ``#[cfg(test)]`` to EOF is treated
  as test-only).
* Environment switches: distinct ``env::var("...")`` names with occurrences and
  files, plus ``#[path]`` attribute count, ``[[bin]]`` / ``[[test]]`` /
  ``test=false`` / ``[features]`` counts from ``Cargo.toml``.
* Artifacts: presence of ``src/bench_head``, ``src/bench_pre``, ``.bak`` files
  (with line counts), and whether the archive directories were already moved
  out of ``src/`` (checked in a few conventional locations).
* Cross-layer family lines + line-set Jaccard samples (optional evidence for
  "13 layers copy-forward").  Jaccard uses non-empty stripped lines of length
  >= 4 so trivial braces do not dominate.
* P1 projection: baseline minus ``bench_head`` + ``bench_pre`` + ``.bak``.
  This is a *projection from the same scan*, not a second checkout; run the
  tool again after the cleanup and diff the JSON to verify it.

Outputs
-------
``--json PATH`` writes a machine-readable report (schema is stable and sorted;
with ``--deterministic`` the timestamp is omitted so CI can ``diff`` it).
``--md PATH`` writes a human report; the baseline document in ``docs/metrics/``
is generated this way.

Usage
-----
::

    python tools/metrics.py --json docs/metrics/baseline-YYYY-MM-DD.json \
                            --md   docs/metrics/baseline-YYYY-MM-DD.md
    # CI regression check (non-zero exit if a budget in --budget-json fails)
    python tools/metrics.py --json /tmp/m.json --check-budgets
    python tools/metrics.py --root /path/to/repo --deterministic --json -

Notes
-----
* Line counts are *physical* (``splitlines``) and *non-empty*
  (``line.strip() != ""``).  Report both; never mix them.
* ``tests/`` is reported as a single aggregate group.  It is not part of the
  ``src/`` totals; the same is true for ``.bak`` files (reported separately).
* The ``#[cfg(test)]`` split is an approximation: it is exact for the common
  "test module at the bottom of the file" convention and conservative for
  files whose tests are interleaved (they are counted as production).
"""

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict

TOOL_VERSION = "1.0.0"
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Directories never scanned (build outputs, VCS, tooling caches).
SKIP_DIRS = {
    ".git", "target", ".lake", "node_modules", "__pycache__", ".commandcode",
    ".idea", ".vscode", "dist", "build", ".cargo",
}

LAYER_RE = re.compile(r"^L\d{2}_[A-Za-z0-9_]+$")
BIN_DIR = "bin"
ARCHIVE_DIRS = ("bench_head", "bench_pre")

RX = {
    "unsafe_word": re.compile(r"\bunsafe\b"),
    "unsafe_block": re.compile(r"\bunsafe\s*\{"),
    "panic_macro": re.compile(r"\bpanic!\s*\("),
    "unwrap": re.compile(r"\.unwrap\(\)"),
    "expect": re.compile(r"\.expect\("),
    "todo": re.compile(r"\btodo!\s*\("),
    "unreachable": re.compile(r"\bunreachable!\s*\("),
    "print_macro": re.compile(r"\b(?:println|eprintln|dbg)!\s*\("),
    "env_var": re.compile(r"env::var(?:_os)?\s*\(\s*\"([^\"]+)\"\s*\)"),
    "path_attr": re.compile(r"#\[path\s*="),
    "test_attr": re.compile(r"^\s*#\[test\]"),
    "ignore_attr": re.compile(r"^\s*#\[ignore"),
    "cfg_test": re.compile(r"^\s*#\[cfg\(test\)\]"),
}

# Counter keys that we aggregate everywhere.
COUNTER_KEYS = (
    "unsafe_word", "unsafe_block", "panic_macro", "unwrap", "expect",
    "todo", "unreachable", "print_macro", "path_attr",
)
# Counters we also evaluate on the "production region" (before #[cfg(test)]).
PROD_COUNTER_KEYS = ("panic_macro", "unwrap", "expect", "todo",
                     "unreachable", "print_macro", "unsafe_word")

# Families used for the copy-forward / Jaccard section.  Added dynamically too.
DEFAULT_FAMILIES = (
    "parser", "pretty", "unification", "typeclass", "canonical", "struct_eq",
    "cxt", "elaboration", "force", "eval", "rename", "subst", "unify",
    "machine", "syntax", "lex", "macros", "pattern_match", "mod",
)


def rel_posix(path, root):
    """Return path relative to root using forward slashes."""
    return os.path.relpath(path, root).replace(os.sep, "/")


def iter_files(root, predicate):
    """Yield absolute paths under root satisfying predicate(rel_posix_path)."""
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS)
        for name in sorted(filenames):
            full = os.path.join(dirpath, name)
            rel = rel_posix(full, root)
            if predicate(rel):
                yield full, rel


def read_lines(path):
    """Read a file as text and return (physical_lines, non_empty_lines, lines)."""
    with open(path, "rb") as fh:
        raw = fh.read()
    text = raw.decode("utf-8", errors="replace")
    lines = text.splitlines()
    nonempty = sum(1 for line in lines if line.strip())
    return len(lines), nonempty, lines


def worse_line(a, b):
    """Merge two 'worst line' records (max count) for top-N reporting."""
    if b is None:
        return a
    if a is None:
        return b
    return a if a[1] >= b[1] else b


def count_line(line, counters, prod, prod_counters, env_seen):
    """Count one line into counters / env map."""
    for key in COUNTER_KEYS:
        hits = len(RX[key].findall(line))
        if hits:
            counters[key] += hits
            if prod and key in PROD_COUNTER_KEYS:
                prod_counters[key] += hits
    for name in RX["env_var"].findall(line):
        env_seen[name] += 1


def scan_rs_file(path, rel):
    """Scan one .rs file; return a record dict."""
    physical, nonempty, lines = read_lines(path)
    counters = {key: 0 for key in COUNTER_KEYS}
    prod_counters = {key: 0 for key in PROD_COUNTER_KEYS}
    env_seen = defaultdict(int)
    test_attr = ignore_attr = 0
    cfg_test_line = None
    for idx, line in enumerate(lines):
        if cfg_test_line is None and RX["cfg_test"].search(line):
            cfg_test_line = idx
        if RX["test_attr"].search(line):
            test_attr += 1
        if RX["ignore_attr"].search(line):
            ignore_attr += 1
    prod_end = cfg_test_line if cfg_test_line is not None else len(lines)
    for idx, line in enumerate(lines):
        count_line(line, counters, idx < prod_end, prod_counters, env_seen)
    return {
        "path": rel,
        "physical": physical,
        "nonempty": nonempty,
        "counters": counters,
        "prod_counters": prod_counters,
        "env": dict(sorted(env_seen.items())),
        "test_attrs": test_attr,
        "ignore_attrs": ignore_attr,
    }


def is_test_basename(base, test_rule="plural"):
    """Is this .rs basename a layer test file?

    * ``plural`` (default, matches the D3/FACTS convention): ``tests.rs`` or
      ``*_tests.rs``.  Singular ``*_test.rs`` (e.g. L13 ``debug_test.rs``) is
      treated as production, which is what the historical reports did.
    * ``any``: any basename containing ``test`` (broader; counts debug_test.rs
      as test code).
    """
    low = base.lower()
    if test_rule == "any":
        return "test" in low
    return low == "tests.rs" or low.endswith("_tests.rs")


def classify(rel, test_rule="plural"):
    """Classify a repository-relative forward-slash path.

    Returns a dict {kind, layer, side, group} or None for files we do not count
    in the source metrics (non-.rs under src etc.).
    """
    parts = rel.split("/")
    if parts[0] == "src":
        if len(parts) == 1:
            return None
        if parts[-1].endswith(".rs"):
            base = parts[-1]
            if len(parts) >= 2 and parts[1] == BIN_DIR:
                return {"kind": "bin", "layer": None, "side": None, "group": "src/bin"}
            if len(parts) >= 2 and parts[1] in ARCHIVE_DIRS:
                return {"kind": "archive", "layer": None, "side": None,
                        "group": "src/" + parts[1]}
            if len(parts) >= 2 and LAYER_RE.match(parts[1]):
                layer = parts[1]
                twin = any(p.startswith("bump_spine_iter") for p in parts[2:])
                if is_test_basename(base, test_rule):
                    return {"kind": "test", "layer": layer, "side": None,
                            "group": layer}
                return {"kind": "ref" if not twin else "twin", "layer": layer,
                        "side": "twin" if twin else "ref", "group": layer}
            # glue: any other .rs under src (src/*.rs, src/doc/*.rs, ...)
            if len(parts) >= 3:
                return {"kind": "glue", "layer": None, "side": None,
                        "group": "src/" + parts[1]}
            return {"kind": "glue", "layer": None, "side": None,
                    "group": "src/top"}
        return None  # .typort, .md, ... under src
    if parts[0] == "tests" and parts[-1].endswith(".rs"):
        return {"kind": "tests_dir", "layer": None, "side": None, "group": "tests"}
    return None


def empty_agg():
    return {"files": 0, "physical": 0, "nonempty": 0,
            "counters": {key: 0 for key in COUNTER_KEYS},
            "prod_counters": {key: 0 for key in PROD_COUNTER_KEYS},
            "test_attrs": 0, "ignore_attrs": 0}


def add_record(agg, rec):
    agg["files"] += 1
    agg["physical"] += rec["physical"]
    agg["nonempty"] += rec["nonempty"]
    for key in COUNTER_KEYS:
        agg["counters"][key] += rec["counters"][key]
    for key in PROD_COUNTER_KEYS:
        agg["prod_counters"][key] += rec["prod_counters"][key]
    agg["test_attrs"] += rec["test_attrs"]
    agg["ignore_attrs"] += rec["ignore_attrs"]


def merge_agg(dst, src):
    dst["files"] += src["files"]
    dst["physical"] += src["physical"]
    dst["nonempty"] += src["nonempty"]
    for key in COUNTER_KEYS:
        dst["counters"][key] += src["counters"][key]
    for key in PROD_COUNTER_KEYS:
        dst["prod_counters"][key] += src["prod_counters"][key]
    dst["test_attrs"] += src["test_attrs"]
    dst["ignore_attrs"] += src["ignore_attrs"]


def family_of(rel):
    """Family key for a .rs file: mod.rs -> directory name, else basename."""
    base = rel.rsplit("/", 1)[-1]
    stem = base[:-3] if base.endswith(".rs") else base
    if stem == "mod" or stem.startswith("mod_"):
        parent = rel.rsplit("/", 2)
        if len(parent) >= 2:
            return parent[-2]
        return stem
    return stem


def jaccard(a, b):
    if not a or not b:
        return None
    inter = len(a & b)
    union = len(a | b)
    return (inter / union) if union else None


def git_info(root):
    """Best-effort branch / HEAD info; never fails the run."""
    info = {"branch": None, "head": None, "dirty": None}
    for key, args in (
        ("branch", ["git", "rev-parse", "--abbrev-ref", "HEAD"]),
        ("head", ["git", "rev-parse", "--short", "HEAD"]),
    ):
        try:
            out = subprocess.run(args, cwd=root, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE,
                                 universal_newlines=True, timeout=10)
            if out.returncode == 0:
                info[key] = out.stdout.strip()
        except (OSError, subprocess.SubprocessError):
            pass
    try:
        out = subprocess.run(["git", "status", "--porcelain"], cwd=root,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             universal_newlines=True, timeout=15)
        if out.returncode == 0:
            info["dirty"] = bool(out.stdout.strip())
    except (OSError, subprocess.SubprocessError):
        pass
    return info


def parse_cargo(root):
    """Structural facts from Cargo.toml (text parse; tomllib is 3.11+ only)."""
    path = os.path.join(root, "Cargo.toml")
    facts = {
        "bin_targets": 0, "test_targets": 0, "test_false": 0,
        "features_sections": 0, "bin_names": [],
        "path_attrs_in_cargo": 0,
    }
    if not os.path.isfile(path):
        return facts
    with open(path, "rb") as fh:
        text = fh.read().decode("utf-8", errors="replace")
    lines = text.splitlines()
    facts["bin_targets"] = len(re.findall(r"(?m)^\[\[bin\]\]", text))
    facts["test_targets"] = len(re.findall(r"(?m)^\[\[test\]\]", text))
    facts["test_false"] = len(re.findall(r"(?m)^\s*test\s*=\s*false", text))
    facts["features_sections"] = len(re.findall(r"(?m)^\[features\]", text))
    facts["path_attrs_in_cargo"] = text.count("#[path")
    in_bin = False
    for line in lines:
        stripped = line.strip()
        if stripped == "[[bin]]":
            in_bin = True
            continue
        if in_bin and stripped.startswith("["):
            in_bin = False
        if in_bin:
            m = re.match(r'name\s*=\s*"([^"]+)"', stripped)
            if m:
                facts["bin_names"].append(m.group(1))
    return facts


def find_moved_archive(root):
    """Where did bench_head/bench_pre go, if they are no longer under src/?"""
    candidates = [
        "tools/bench_snapshots", "tools/bench_snapshots/bench_head",
        "tools/bench_snapshots/bench_pre", "tools/bench_snapshots/L07_pre",
        "tools/bench_snapshots/L07_head", "tools/bench_head", "tools/bench_pre",
        "tools/experiments/bench_head", "tools/experiments/bench_pre",
        "experiments/bench_head", "experiments/bench_pre", "bench/bench_head",
        "bench/bench_pre", "oracle/bench_head", "oracle/bench_pre",
        "src/bench_head", "src/bench_pre",
    ]
    found = {}
    for rel in candidates:
        full = os.path.join(root, rel.replace("/", os.sep))
        if os.path.isdir(full):
            found[rel] = True
    return found


def scan_relocated_archive(root):
    """Size summary of archived bench snapshots moved out of src/ by P1.

    P1 moved the frozen L07 snapshot engines to ``tools/bench_snapshots/``
    (they are no longer part of the product tree, but keeping their size gives
    the P1 report a verifiable "moved, not silently deleted" number).
    """
    summary = {"paths": [], "files": 0, "physical": 0, "nonempty": 0}
    for rel_root in ("tools/bench_snapshots", "experiments/bench_snapshots",
                     "bench/bench_snapshots"):
        base = os.path.join(root, rel_root.replace("/", os.sep))
        if not os.path.isdir(base):
            continue
        summary["paths"].append(rel_root)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS)
            for name in sorted(filenames):
                if not name.endswith(".rs"):
                    continue
                full = os.path.join(dirpath, name)
                try:
                    physical, nonempty, _ = read_lines(full)
                except OSError:
                    continue
                summary["files"] += 1
                summary["physical"] += physical
                summary["nonempty"] += nonempty
    return summary


def scan_bak(root):
    """Scan *.bak files anywhere under src/ (archive copies of Rust files)."""
    records = []
    total = {"files": 0, "physical": 0, "nonempty": 0, "by_layer": defaultdict(
        lambda: {"files": 0, "physical": 0, "nonempty": 0})}
    src = os.path.join(root, "src")
    if not os.path.isdir(src):
        return total, records
    for dirpath, dirnames, filenames in os.walk(src):
        dirnames[:] = sorted(d for d in dirnames if d not in SKIP_DIRS)
        for name in sorted(filenames):
            if not name.endswith(".bak"):
                continue
            full = os.path.join(dirpath, name)
            rel = rel_posix(full, root)
            try:
                physical, nonempty, _ = read_lines(full)
            except OSError:
                continue
            parts = rel.split("/")
            layer = parts[1] if len(parts) >= 3 and LAYER_RE.match(parts[1]) else None
            rec = {"path": rel, "physical": physical, "nonempty": nonempty,
                   "layer": layer}
            records.append(rec)
            total["files"] += 1
            total["physical"] += physical
            total["nonempty"] += nonempty
            if layer:
                total["by_layer"][layer]["files"] += 1
                total["by_layer"][layer]["physical"] += physical
                total["by_layer"][layer]["nonempty"] += nonempty
    total["by_layer"] = {k: dict(v) for k, v in sorted(total["by_layer"].items())}
    return total, records


def build_report(root, test_rule="plural"):
    report = {
        "tool": "tools/metrics.py",
        "tool_version": TOOL_VERSION,
        "generated_at": None,
        "test_rule": test_rule,
        "git": git_info(root),
        "root": os.path.basename(os.path.normpath(root)),
        "definitions": {
            "physical_lines": "text.splitlines() length",
            "nonempty_lines": "lines whose .strip() is non-empty",
            "twin": "path component starting with 'bump_spine_iter'",
            "test_file": "layer .rs whose basename contains 'test'",
            "glue": "src/**/*.rs outside layers, src/bin and bench_head/bench_pre",
            "archive": "src/bench_head + src/bench_pre (frozen L07 copies)",
            "prod_region": "lines before the first '#[cfg(test)]'; approximate",
            "jaccard": "stripped non-empty line sets, lines < 4 chars ignored",
        },
        "totals": {},           # src aggregates by kind
        "layers": {},           # per-layer: ref / twin / test
        "risk": {},             # risk counters, layer-only + src-wide + tops
        "env": {},              # distinct env switches
        "cargo": {},
        "artifacts": {},
        "families": {},         # family line totals + Jaccard pairs
        "tests_dir": {},
        "p1_projection": {},
        "errors": [],
    }

    file_records = []
    for full, rel in iter_files(root, lambda r: r.startswith("src/")
                                and r.endswith(".rs")):
        try:
            rec = scan_rs_file(full, rel)
        except OSError as exc:  # pragma: no cover - defensive
            report["errors"].append({"path": rel, "error": str(exc)})
            continue
        cls = classify(rel, test_rule)
        rec.update(cls or {"kind": "other", "layer": None, "side": None,
                           "group": "src/other"})
        file_records.append(rec)

    # ---------- aggregates ----------
    def new_group():
        return empty_agg()

    groups = defaultdict(new_group)
    layers = defaultdict(lambda: {"ref": new_group(), "twin": new_group(),
                                  "test": new_group(), "total": new_group()})
    for rec in file_records:
        kind = rec["kind"]
        add_record(groups[kind], rec)
        if kind in ("ref", "twin", "test") and rec["layer"]:
            add_record(layers[rec["layer"]][kind], rec)
            add_record(layers[rec["layer"]]["total"], rec)
        if kind == "glue":
            sub = rec["group"]
            groups["glue_by_group"].setdefault(sub, new_group())
            add_record(groups["glue_by_group"][sub], rec)

    # Drop the accidental no-op above if Python warns; groups[kind] is a dict.
    def group_short(rec):
        return {
            "files": rec["files"], "physical": rec["physical"],
            "nonempty": rec["nonempty"],
            "test_attrs": rec["test_attrs"], "ignore_attrs": rec["ignore_attrs"],
            "counters": dict(rec["counters"]),
            "prod_counters": dict(rec["prod_counters"]),
        }

    totals = {}
    for kind in ("ref", "twin", "test", "bin", "glue", "archive"):
        totals[kind] = group_short(groups.get(kind, empty_agg()))
    archive_by_group = {}
    for rec in file_records:
        if rec["kind"] == "archive":
            agg = archive_by_group.setdefault(rec["group"], empty_agg())
            add_record(agg, rec)
    totals["archive_by_group"] = {k: group_short(v)
                                  for k, v in sorted(archive_by_group.items())}
    totals["src_no_bak"] = {"files": sum(t["files"] for t in totals.values()
                                        if isinstance(t, dict) and "files" in t),
                            "physical": sum(t["physical"] for t in totals.values()
                                            if isinstance(t, dict) and "files" in t),
                            "nonempty": sum(t["nonempty"] for t in totals.values()
                                            if isinstance(t, dict) and "files" in t)}
    # src-wide counters (sum over ref/twin/test/bin/glue/archive)
    src_counters = {key: 0 for key in COUNTER_KEYS}
    src_prod = {key: 0 for key in PROD_COUNTER_KEYS}
    src_env = defaultdict(int)
    for kind in ("ref", "twin", "test", "bin", "glue", "archive"):
        for key in COUNTER_KEYS:
            src_counters[key] += totals[kind]["counters"].get(key, 0)
        for key in PROD_COUNTER_KEYS:
            src_prod[key] += totals[kind]["prod_counters"].get(key, 0)
    for rec in file_records:
        for name, n in rec["env"].items():
            src_env[name] += n

    report["totals"] = {
        "by_kind": totals,
        "src_counters": src_counters,
        "src_prod_counters": src_prod,
        "layer_only_counts": {
            "files": totals["ref"]["files"] + totals["twin"]["files"]
                     + totals["test"]["files"],
            "nonempty": totals["ref"]["nonempty"] + totals["twin"]["nonempty"]
                        + totals["test"]["nonempty"],
            "counters": {key: sum(totals[k]["counters"].get(key, 0)
                                  for k in ("ref", "twin", "test"))
                         for key in COUNTER_KEYS},
        },
    }

    # per-layer table (stable order L01..L13)
    layer_rows = {}
    for layer in sorted(layers):
        row = {}
        for side in ("ref", "twin", "test", "total"):
            agg = layers[layer][side]
            row[side] = {"files": agg["files"], "physical": agg["physical"],
                         "nonempty": agg["nonempty"],
                         "test_attrs": agg["test_attrs"],
                         "ignore_attrs": agg["ignore_attrs"],
                         "unsafe": agg["counters"]["unsafe_word"],
                         "panic": agg["counters"]["panic_macro"],
                         "prints": agg["counters"]["print_macro"]}
        row["nonempty_ref_prod"] = row["ref"]["nonempty"]
        layer_rows[layer] = row
    report["layers"] = layer_rows

    # ---------- risk ----------
    top_defs = (
        ("unsafe", "unsafe_word"), ("panic", "panic_macro"),
        ("unwrap", "unwrap"), ("expect", "expect"),
        ("prints", "print_macro"), ("todo", "todo"),
        ("unreachable", "unreachable"), ("path_attr", "path_attr"),
    )
    risk = {"tops": {}, "layer_only": {}, "src_wide": {}}
    for name, key in top_defs:
        rows = sorted(
            ({"path": rec["path"], "count": rec["counters"][key]}
             for rec in file_records if rec["counters"][key] > 0),
            key=lambda r: (-r["count"], r["path"]),
        )
        risk["tops"][name] = rows[:15]
    risk["layer_only"] = report["totals"]["layer_only_counts"]["counters"]
    risk["src_wide"] = src_counters

    def dir_key(rel):
        parts = rel.split("/")
        if len(parts) >= 4 and parts[0] == "src" and LAYER_RE.match(parts[1]) \
                and parts[2].startswith("bump_spine_iter"):
            return "/".join(parts[:3])
        return "/".join(parts[:2]) if len(parts) >= 2 else rel

    by_dir = defaultdict(lambda: defaultdict(int))
    for rec in file_records:
        dk = dir_key(rec["path"])
        for key in ("unsafe_word", "panic_macro", "print_macro",
                    "unwrap", "expect"):
            by_dir[dk][key] += rec["counters"][key]
    risk["tops_by_dir"] = {
        key: sorted(({"dir": d, "count": c[key]} for d, c in by_dir.items()
                     if c[key] > 0), key=lambda r: (-r["count"], r["dir"]))[:12]
        for key in ("unsafe_word", "panic_macro", "print_macro", "unwrap", "expect")
    }
    risk["layer_only"]["files"] = report["totals"]["layer_only_counts"]["files"]
    risk["layer_only"]["nonempty"] = report["totals"]["layer_only_counts"]["nonempty"]
    report["risk"] = risk

    # per-layer risk rows
    layer_risk = {}
    for layer, row in layer_rows.items():
        layer_risk[layer] = {
            "unsafe_ref": row["ref"]["unsafe"],
            "unsafe_twin": row["twin"]["unsafe"],
            "panic": row["ref"]["panic"] + row["twin"]["panic"] + row["test"]["panic"],
            "prints": row["ref"]["prints"] + row["twin"]["prints"] + row["test"]["prints"],
        }
    report["layers_risk"] = layer_risk

    # env switches
    env_files = defaultdict(list)
    for rec in file_records:
        for name in rec["env"]:
            env_files[name].append(rec["path"])
    layer_env = defaultdict(int)
    layer_env_files = defaultdict(list)
    for rec in file_records:
        if rec["kind"] in ("ref", "twin", "test"):
            for name, count in rec["env"].items():
                layer_env[name] += count
                layer_env_files[name].append(rec["path"])
    report["env"] = {
        "distinct": len(src_env),
        "total_occurrences": sum(src_env.values()),
        "names": [
            {"name": name, "count": count,
             "files": sorted(env_files[name])[:6],
             "file_count": len(set(env_files[name]))}
            for name, count in sorted(src_env.items(), key=lambda kv: (-kv[1], kv[0]))
        ],
        "layer_only_distinct": len(layer_env),
        "layer_only_occurrences": sum(layer_env.values()),
        "layer_only_names": [
            {"name": name, "count": count,
             "files": sorted(set(layer_env_files[name]))[:4]}
            for name, count in sorted(layer_env.items(), key=lambda kv: (-kv[1], kv[0]))
        ],
    }

    # ---------- cargo / artifacts ----------
    report["cargo"] = parse_cargo(root)
    moved = find_moved_archive(root)
    bak, bak_records = scan_bak(root)
    report["artifacts"] = {
        "src_bench_head_exists": os.path.isdir(os.path.join(root, "src", "bench_head")),
        "src_bench_pre_exists": os.path.isdir(os.path.join(root, "src", "bench_pre")),
        "moved_archive_locations": sorted(moved),
        "archive_present_in_src": any(
            k in ("src/bench_head", "src/bench_pre") for k in moved),
        "relocated_archive": scan_relocated_archive(root),
        "bak_exists": bak["files"] > 0,
        "bak": bak,
        "bak_files": bak_records,
        "path_attr_total": src_counters["path_attr"],
    }

    # ---------- tests/ aggregate (not part of src totals) ----------
    tests_agg = empty_agg()
    for full, rel in iter_files(root, lambda r: r.startswith("tests/")
                                and r.endswith(".rs")):
        try:
            rec = scan_rs_file(full, rel)
        except OSError as exc:  # pragma: no cover
            report["errors"].append({"path": rel, "error": str(exc)})
            continue
        add_record(tests_agg, rec)
    report["tests_dir"] = {
        "files": tests_agg["files"], "physical": tests_agg["physical"],
        "nonempty": tests_agg["nonempty"],
        "test_attrs": tests_agg["test_attrs"],
        "ignore_attrs": tests_agg["ignore_attrs"],
        "path_attr": tests_agg["counters"]["path_attr"],
    }

    # ---------- families + Jaccard ----------
    family_sets = defaultdict(lambda: defaultdict(set))
    family_files = defaultdict(lambda: defaultdict(list))
    family_lines = defaultdict(lambda: defaultdict(int))
    for full, rel in iter_files(root, lambda r: r.startswith("src/")
                                and r.endswith(".rs")):
        cls = classify(rel, test_rule)
        if not cls or cls["kind"] not in ("ref", "twin", "test"):
            continue
        try:
            _, nonempty, lines = read_lines(full)
        except OSError:
            continue
        fam = family_of(rel)
        if cls["kind"] == "test":
            layer_key = cls["layer"] + "/test"
        else:
            layer_key = cls["layer"] + "/" + cls["side"]
        s = {line.strip() for line in lines if len(line.strip()) >= 4}
        family_sets[fam][layer_key] |= s
        family_files[fam][layer_key].append(rel)
        family_lines[fam][layer_key] += nonempty
    families_out = {}
    all_pairs = []
    for fam in sorted(family_sets):
        keys = sorted(family_sets[fam])
        pairs = []
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                a, b = keys[i], keys[j]
                # Only keep cross-layer pairs (L07/ref vs L08/ref, ...), which
                # is the "copy-forward" question; same-layer /test pairs are
                # not comparable evidence.
                if a.split("/")[0] == b.split("/")[0]:
                    continue
                score = jaccard(family_sets[fam][a], family_sets[fam][b])
                if score is None:
                    continue
                pairs.append({
                    "a": a, "b": b, "jaccard": round(score, 4),
                    "a_files": family_files[fam][a],
                    "b_files": family_files[fam][b],
                })
        pairs.sort(key=lambda p: (-p["jaccard"], p["a"], p["b"]))
        if pairs:
            all_pairs.extend({"family": fam, **{k: p[k]
                                                for k in ("a", "b", "jaccard")}}
                             for p in pairs)
            families_out[fam] = {
                "keys": keys,
                "line_totals": {key: family_lines[fam][key] for key in keys},
                "files": {key: sorted(paths)
                          for key, paths in sorted(family_files[fam].items())},
                "top_pairs": pairs[:8],
                "all_pairs": [{k: p[k] for k in ("a", "b", "jaccard")}
                              for p in pairs],
            }
    all_pairs.sort(key=lambda p: (-p["jaccard"], p["family"], p["a"], p["b"]))
    report["families"] = {"by_family": families_out, "top_pairs": all_pairs[:30]}

    # ---------- cross-layer duplication proxy (for --check) ----------
    dup_pairs = [p for p in all_pairs
                 if not p["a"].endswith("/test") and not p["b"].endswith("/test")]
    report["duplication"] = {
        "pairs_total": len(dup_pairs),
        "pairs_ge_90": sum(1 for p in dup_pairs if p["jaccard"] >= 0.90),
        "pairs_ge_95": sum(1 for p in dup_pairs if p["jaccard"] >= 0.95),
        "max_jaccard": round(max((p["jaccard"] for p in dup_pairs), default=0.0), 4),
        "note": "cross-layer non-test line-set Jaccard; grows when code is copied, "
                "not directly a violation unless the pair count increases",
    }

    # ---------- P1 projection ----------
    archive = totals["archive"]
    archive_counters = {key: archive["counters"].get(key, 0)
                        for key in COUNTER_KEYS}
    p1 = {
        "assumptions": ("bench_head+bench_pre moved out of src/ and all *.bak "
                        "deleted; nothing else changes"),
        "baseline_src_files": totals["src_no_bak"]["files"],
        "baseline_src_nonempty": totals["src_no_bak"]["nonempty"],
        "baseline_src_physical": totals["src_no_bak"]["physical"],
        "archive_files": archive["files"],
        "archive_nonempty": archive["nonempty"],
        "archive_physical": archive["physical"],
        "bak_files": bak["files"],
        "bak_nonempty": bak["nonempty"],
        "bak_physical": bak["physical"],
        "post_src_files": totals["src_no_bak"]["files"] - archive["files"],
        "post_src_nonempty": totals["src_no_bak"]["nonempty"] - archive["nonempty"],
        "post_src_physical": totals["src_no_bak"]["physical"] - archive["physical"],
        "removed_total_nonempty": archive["nonempty"] + bak["nonempty"],
        "removed_total_physical": archive["physical"] + bak["physical"],
        "src_wide_counters_before": dict(src_counters),
        "src_wide_counters_after": {
            key: src_counters[key] - archive_counters.get(key, 0)
            for key in COUNTER_KEYS},
        "layer_only_unchanged": True,
    }
    report["p1_projection"] = p1
    # Reference numbers from the 2026-11-09 D3 report.  ``.bak`` files were
    # untracked at HEAD and are not recoverable from git, so the tool can only
    # quote them; everything else is re-measured.
    report["p1_projection"]["d3_historical_reference"] = {
        "source": "docs/optimal-design/D3-elegance.md (2026-11-09)",
        "bak_files": 17,
        "bak_nonempty": 12464,
        "archive_nonempty": 25334,
        "total_removed_nonempty": 37798,
        "note": "参考值；本工具在 git-ref 快照上重测 archive，.bak 不可重测",
    }

    # ---------- check baseline (self-describing; consumed by ``--check``) ----------
    lo_counters = report["totals"]["layer_only_counts"]["counters"]
    archive = totals["archive"]
    report["check_baseline"] = {
        "src_nonempty": totals["src_no_bak"]["nonempty"],
        "layer_only_nonempty": report["totals"]["layer_only_counts"]["nonempty"],
        "unsafe": lo_counters["unsafe_word"],
        "panic_macro": lo_counters["panic_macro"],
        "unwrap": lo_counters["unwrap"],
        "expect": lo_counters["expect"],
        "print_macro": lo_counters["print_macro"],
        "archive_nonempty": archive["nonempty"],
        "bak_files": bak["files"],
        "pairs_ge_90": report["duplication"]["pairs_ge_90"],
        "pairs_ge_95": report["duplication"]["pairs_ge_95"],
        "max_jaccard": report["duplication"]["max_jaccard"],
        "env_distinct": report["env"]["distinct"],
        "bin_targets": report["cargo"]["bin_targets"],
        "test_false": report["cargo"]["test_false"],
    }
    return report


def export_git_tree(root, ref):
    """Materialize ``git archive <ref>`` into a temporary directory.

    Returns the temp directory path; caller is responsible for cleanup.
    Raises RuntimeError when git is unavailable or the ref is unknown.
    """
    import io
    import tarfile
    import tempfile

    try:
        proc = subprocess.run(
            ["git", "archive", "--format=tar", ref],
            cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise RuntimeError(f"git archive {ref!r} failed: {exc}") from exc
    if proc.returncode != 0:
        raise RuntimeError(
            f"git archive {ref!r} failed (exit {proc.returncode}): "
            f"{proc.stderr.decode('utf-8', 'replace').strip()[:500]}"
        )
    tmpdir = tempfile.mkdtemp(prefix="ezl-metrics-")
    with tarfile.open(fileobj=io.BytesIO(proc.stdout)) as tf:
        tf.extractall(tmpdir)
    return tmpdir


def _summary(report):
    """Subset of a report used for snapshot comparison."""
    t = report["totals"]["by_kind"]
    kinds = {}
    for kind in ("ref", "twin", "test", "bin", "glue", "archive"):
        kinds[kind] = {"files": t[kind]["files"],
                       "nonempty": t[kind]["nonempty"]}
    risk_lo = report["risk"]["layer_only"]
    risk_sw = report["risk"]["src_wide"]
    return {
        "src_files": t["src_no_bak"]["files"],
        "src_nonempty": t["src_no_bak"]["nonempty"],
        "src_physical": t["src_no_bak"]["physical"],
        "kinds": kinds,
        "layer_only": {"files": report["totals"]["layer_only_counts"]["files"],
                       "nonempty": report["totals"]["layer_only_counts"]["nonempty"],
                       "counters": {k: risk_lo.get(k, 0) for k in COUNTER_KEYS}},
        "src_wide": {k: risk_sw.get(k, 0) for k in COUNTER_KEYS},
        "env_distinct": report["env"]["distinct"],
        "env_layer_only_distinct": report["env"]["layer_only_distinct"],
        "cargo": {k: report["cargo"][k] for k in
                  ("bin_targets", "test_false", "test_targets",
                   "features_sections")},
        "artifacts": {
            "src_bench_head_exists": report["artifacts"]["src_bench_head_exists"],
            "src_bench_pre_exists": report["artifacts"]["src_bench_pre_exists"],
            "bak_files": report["artifacts"]["bak"]["files"],
            "bak_nonempty": report["artifacts"]["bak"]["nonempty"],
            "path_attr_total": report["artifacts"]["path_attr_total"],
        },
        "layers_nonempty": {layer: row["total"]["nonempty"]
                            for layer, row in report["layers"].items()},
    }


# --------------------------------------------------------------------------
# --check: repo metrics gate (used by tools/gate_p0.sh)
# --------------------------------------------------------------------------

# Fallback thresholds, copied from docs/metrics/baseline-2026-11-09.json's
# ``check_baseline`` block.  Used only when that JSON is missing (fresh clone /
# CI checkout without docs/metrics).  Keep in sync when the baseline is refreshed:
#   python tools/metrics.py --compare-ref HEAD \
#       --json docs/metrics/baseline-YYYY-MM-DD.json --md ...
BUILTIN_CHECK_BASELINE = {
    "src_nonempty": 204908,
    "layer_only_nonempty": 185432,
    "unsafe": 317,
    "panic_macro": 487,
    "unwrap": 732,
    "expect": 739,
    "print_macro": 663,
    "archive_nonempty": 0,
    "bak_files": 0,
    "pairs_ge_90": 24,
    "pairs_ge_95": 10,
    "max_jaccard": 1.0,
    "env_distinct": 68,
    "bin_targets": 22,
    "test_false": 19,
}

# Hard gate items: (key, label, mode, tolerance)
#   mode "abs" = current must be <= baseline
#   mode "pct" = current must be <= baseline * (1 + tolerance)
# Labels are ASCII only: Windows CI logs may run under a legacy code page.
CHECK_ITEMS = (
    ("src_nonempty", "`src/` nonempty lines (+0.5%)", "pct", 0.005),
    ("layer_only_nonempty", "layer nonempty lines (+0.5%)", "pct", 0.005),
    ("unsafe", "`unsafe` (layer-only)", "abs", 0.0),
    ("panic_macro", "`panic!(` (layer-only)", "abs", 0.0),
    ("unwrap", "`.unwrap()` (layer-only)", "abs", 0.0),
    ("expect", "`.expect(` (layer-only)", "abs", 0.0),
    ("print_macro", "print macros (layer-only)", "abs", 0.0),
    ("archive_nonempty", "archive nonempty lines (must be 0)", "abs", 0.0),
    ("bak_files", "`.bak` files (must be 0)", "abs", 0.0),
    ("pairs_ge_90", "cross-layer copies with Jaccard >=90%", "abs", 0.0),
    ("pairs_ge_95", "cross-layer copies with Jaccard >=95%", "abs", 0.0),
)
INFO_ITEMS = (
    ("max_jaccard", "max cross-layer Jaccard"),
    ("env_distinct", "distinct env switches"),
    ("bin_targets", "`[[bin]]` targets"),
    ("test_false", "`test = false` count"),
)

DEFAULT_BASELINE_JSON = "docs/metrics/baseline-2026-11-09.json"


def load_check_baseline(root, baseline_path=None):
    """Return (numbers, source_label).  Prefer the checked-in JSON baseline."""
    path = baseline_path or DEFAULT_BASELINE_JSON
    if not os.path.isabs(path):
        path = os.path.join(root, path)
    data = None
    if os.path.isfile(path):
        try:
            with open(path, "rb") as fh:
                data = json.loads(fh.read().decode("utf-8", "replace"))
        except (OSError, ValueError):
            data = None
    if isinstance(data, dict):
        cb = data.get("check_baseline")
        if isinstance(cb, dict):
            merged = dict(BUILTIN_CHECK_BASELINE)
            merged.update({k: v for k, v in cb.items()
                           if isinstance(v, (int, float))})
            try:
                label = rel_posix(path, root)
            except ValueError:  # different Windows drive / unrelated root
                label = path
            return merged, label
    return dict(BUILTIN_CHECK_BASELINE), "builtin"


def run_check(root, baseline_path=None, strict=False, test_rule="plural"):
    """Run the metrics gate; print PASS/WARN/INFO and return an exit code.

    Exit-code policy (documented in docs/optimal-design/P1-metrics-report.md):
    * default: WARN lines + ``RESULT: WARN`` + **exit 0** (advisory first round;
      the P0 gate only fails on non-zero, so this is non-blocking by design);
    * ``--strict``: any WARN makes the gate fail with exit 1.
    """
    baseline, source = load_check_baseline(root, baseline_path)
    report = build_report(root, test_rule=test_rule)
    cur = report["check_baseline"]

    print(f"metrics --check: root={root} baseline={source}")
    print(f"  mode={'strict' if strict else 'warn-only'}"
          f" ({'exit 1 on WARN' if strict else 'exit 0 even on WARN; use --strict to fail'})")
    warn = 0
    checks = 0
    for key, label, mode, tol in CHECK_ITEMS:
        base = baseline.get(key)
        now = cur.get(key)
        if base is None or now is None:
            print(f"  INFO  {key:<20} baseline/current missing — skipped")
            continue
        checks += 1
        if mode == "pct":
            limit = base * (1.0 + tol)
            ok = now <= limit
            shown = f"{fmt_int(now)} <= {fmt_int(int(limit))} (+{tol * 100:.1f}%)"
        else:
            limit = base
            ok = now <= limit
            shown = f"{fmt_int(now)} <= {fmt_int(int(limit))}"
        if ok:
            print(f"  PASS  {key:<20} {shown}  [{label}]")
        else:
            warn += 1
            delta = now - base
            print(f"  WARN  {key:<20} {shown}  (delta {delta:+d})  [{label}]")
    for key, label in INFO_ITEMS:
        now = cur.get(key)
        base = baseline.get(key)
        if now is not None:
            print(f"  INFO  {key:<20} {now} (baseline {base})  [{label}]")
    if warn:
        print(f"RESULT: WARN - {warn}/{checks} checks above baseline "
              f"(mode={'strict' if strict else 'warn-only'})")
        return 1 if strict else 0
    print(f"RESULT: PASS - {checks}/{checks} checks within baseline")
    return 0


def compare_snapshots(base, current):
    """Compare a baseline snapshot (usually ``--git-ref HEAD``) to the worktree.

    Used for the P1 comparison: baseline = pre-cleanup tree, current = working
    tree after (or while) moving ``bench_head``/``bench_pre`` and deleting
    ``.bak``.  Layer metrics are expected to be *invariant*; a difference there
    is reported as "other changes detected" (concurrent worktree edits).
    """
    b = _summary(base)
    c = _summary(current)
    deltas = {}
    for key in ("src_files", "src_nonempty", "src_physical"):
        deltas[key] = c[key] - b[key]
    deltas["kinds"] = {
        kind: {"files": c["kinds"][kind]["files"] - b["kinds"][kind]["files"],
               "nonempty": c["kinds"][kind]["nonempty"] - b["kinds"][kind]["nonempty"]}
        for kind in b["kinds"]
    }
    deltas["layer_only_files"] = c["layer_only"]["files"] - b["layer_only"]["files"]
    deltas["layer_only_nonempty"] = (c["layer_only"]["nonempty"]
                                     - b["layer_only"]["nonempty"])
    deltas["layer_counters"] = {
        k: c["layer_only"]["counters"][k] - b["layer_only"]["counters"][k]
        for k in COUNTER_KEYS}
    deltas["src_wide"] = {k: c["src_wide"][k] - b["src_wide"][k]
                          for k in COUNTER_KEYS}
    deltas["env_distinct"] = c["env_distinct"] - b["env_distinct"]
    deltas["env_layer_only_distinct"] = (c["env_layer_only_distinct"]
                                        - b["env_layer_only_distinct"])
    deltas["cargo"] = {k: c["cargo"][k] - b["cargo"][k] for k in b["cargo"]}
    changed_layers = {
        layer: c["layers_nonempty"].get(layer, 0) - b["layers_nonempty"].get(layer, 0)
        for layer in sorted(set(b["layers_nonempty"]) | set(c["layers_nonempty"]))
        if c["layers_nonempty"].get(layer, 0) != b["layers_nonempty"].get(layer, 0)
    }
    return {
        "baseline": b,
        "current": c,
        "delta": deltas,
        "layers_changed": changed_layers,
        "layer_only_invariant": not changed_layers,
        "note": ("baseline = git ref snapshot; current = working tree snapshot. "
                 "If the worktree is mid-cleanup (P1 in progress) numbers may be "
                 "partial; re-run after the cleanup lands."),
    }


# --------------------------------------------------------------------------
# Markdown rendering
# --------------------------------------------------------------------------

def fmt_int(n):
    return f"{n:,}"


def md_table(headers, rows):
    out = ["| " + " | ".join(headers) + " |",
           "|" + "|".join("---" for _ in headers) + "|"]
    for row in rows:
        out.append("| " + " | ".join(str(c) for c in row) + " |")
    return "\n".join(out)


def render_markdown(report, json_path=None):
    L = []
    add = L.append
    snap = report.get("snapshot") or {"mode": "worktree"}
    title = "# 仓库静态度量基线（`tools/metrics.py` 生成）"
    add(title)
    add("")
    mode = snap.get("mode", "worktree")
    mode_txt = (f"git ref `{snap.get('ref')}` 快照" if mode == "git-ref"
                else "工作树磁盘快照")
    add(f"> 快照：**{mode_txt}**；生成工具：`tools/metrics.py` v{report['tool_version']}"
        "（仅标准库）；"
        + (f"分支 `{(report['git'] or {}).get('branch')}` / HEAD "
           f"`{(report['git'] or {}).get('head')}`；" if report.get("git") else "")
        + "**只读静态扫描，未构建/未运行测试**。")
    add(">")
    add(f"> 口径：物理行 = `splitlines()` 长度；非空行 = `strip()` 非空；"
        f"孪生 = 路径含 `bump_spine_iter`；测试文件规则 = `{report.get('test_rule')}`"
        "（`plural` = `tests.rs`/`*_tests.rs`，与 D3 对齐；`any` = basename 含 test）；"
        "glue = `src/` 中除层/`src/bin`/归档外的 `.rs`；"
        "`#[cfg(test)]` 之后视为测试区（近似）。")
    add("")
    git = report.get("git") or {}
    if git:
        add(f"- git：branch=`{git.get('branch')}` head=`{git.get('head')}` "
            f"dirty=`{git.get('dirty')}`")
    add(f"- 生成时间：`{report.get('generated_at') or '（deterministic 模式省略）'}`")
    add("")

    # 1. totals
    add("## 1. 总量（`src/`，不含 `.bak`）")
    add("")
    bk = report["totals"]["by_kind"]
    rows = []
    for name, label in (("ref", "参考版（层，非孪生、非测试）"),
                        ("twin", "孪生（`bump_spine_iter*`）"),
                        ("test", "层内测试文件（按 test 规则）"),
                        ("bin", "`src/bin`"),
                        ("glue", "glue（`src/` 非层非 bin）"),
                        ("archive", "归档 `src/bench_head`+`bench_pre`")):
        t = bk[name]
        rows.append([label, fmt_int(t["files"]), fmt_int(t["physical"]),
                     fmt_int(t["nonempty"])])
    for grp, label in (("src/bench_head", "　其中 `bench_head`"),
                       ("src/bench_pre", "　其中 `bench_pre`")):
        g = (bk.get("archive_by_group") or {}).get(grp)
        if g:
            rows.append([label, fmt_int(g["files"]), fmt_int(g["physical"]),
                         fmt_int(g["nonempty"])])
    t = report["totals"]["by_kind"]["src_no_bak"]
    rows.append(["**`src/` 合计（不含 .bak）**", f"**{fmt_int(t['files'])}**",
                 f"**{fmt_int(t['physical'])}**", f"**{fmt_int(t['nonempty'])}**"])
    bak = report["artifacts"]["bak"]
    rows.append(["`.bak`（单独统计，不计入上表）", fmt_int(bak["files"]),
                 fmt_int(bak["physical"]), fmt_int(bak["nonempty"])])
    add(md_table(["分区", "文件数", "物理行", "非空行"], rows))
    add("")
    add(f"- 层内（ref+twin+test）合计：{fmt_int(report['totals']['layer_only_counts']['files'])} 文件 / "
        f"{fmt_int(report['totals']['layer_only_counts']['nonempty'])} 非空行。")
    add(f"- `tests/` 目录（不计入 `src/`）：{fmt_int(report['tests_dir']['files'])} 文件 / "
        f"{fmt_int(report['tests_dir']['nonempty'])} 非空行；"
        f"`#[test]`={fmt_int(report['tests_dir']['test_attrs'])}，"
        f"`#[ignore]`={fmt_int(report['tests_dir']['ignore_attrs'])}。")
    add("")

    # 2. per layer
    add("## 2. 每层规模（物理行 / 非空行）")
    add("")
    rows = []
    for layer, row in sorted(report["layers"].items()):
        rows.append([layer,
                     f"{fmt_int(row['ref']['physical'])} / {fmt_int(row['ref']['nonempty'])}",
                     f"{fmt_int(row['twin']['physical'])} / {fmt_int(row['twin']['nonempty'])}",
                     f"{fmt_int(row['test']['physical'])} / {fmt_int(row['test']['nonempty'])}",
                     f"{fmt_int(row['total']['physical'])} / {fmt_int(row['total']['nonempty'])}",
                     fmt_int(row['total']['files'])])
    add(md_table(["层", "参考版 物理/非空", "孪生 物理/非空", "测试文件 物理/非空",
                  "层合计 物理/非空", "文件"], rows))
    add("")
    add("> 注：`test` 列按 `--test-rule`（默认 `plural` = `tests.rs`/`*_tests.rs`，与 D3 口径一致）"
        "按文件名剔除；单数 `*_test.rs`（如 L13 `debug_test.rs`）计入参考版，"
        "与 D3 的 L13 24,248/13,304 拆分一致。")
    add("")

    # 3. risk
    add("## 3. 风险/质量指标")
    add("")
    lo = report["risk"]["layer_only"]
    sw = report["risk"]["src_wide"]
    rows = []
    for name, label in (("unsafe_word", "`unsafe`（词出现）"),
                        ("unsafe_block", "`unsafe {` 块"),
                        ("panic_macro", "`panic!(`"),
                        ("unwrap", "`.unwrap()`"),
                        ("expect", "`.expect(`"),
                        ("todo", "`todo!(`"),
                        ("unreachable", "`unreachable!(`"),
                        ("print_macro", "`println!/eprintln!/dbg!`"),
                        ("path_attr", "`#[path]`")):
        rows.append([label, fmt_int(lo.get(name, 0)), fmt_int(sw.get(name, 0))])
    add(md_table(["指标", "层内（ref+twin+test）", "`src/` 全量（含 bin/glue/归档）"], rows))
    add("")
    add("**每层风险面**（层内合计）")
    add("")
    rows = []
    for layer, r in sorted(report["layers_risk"].items()):
        rows.append([layer, fmt_int(r["unsafe_ref"]), fmt_int(r["unsafe_twin"]),
                     fmt_int(r["panic"]), fmt_int(r["prints"])])
    add(md_table(["层", "unsafe(ref)", "unsafe(twin)", "panic!", "prints"], rows))
    add("")
    add("**Top 文件**（`src/` 全量）")
    add("")
    for name in ("unsafe", "panic", "prints", "unwrap", "expect"):
        tops = report["risk"]["tops"].get(name) or []
        if not tops:
            continue
        add(f"- `{name}`：" + "；".join(
            f"`{r['path']}`={fmt_int(r['count'])}" for r in tops[:6]))
    add("")
    add("**`#[cfg(test)]` 之后的“生产区”近似**（仅 `src/` 全量中 print/panic 族）：")
    add("")
    prod = report["totals"]["src_prod_counters"]
    rows = [[f"`{k}`", fmt_int(prod.get(k, 0))] for k in
            ("panic_macro", "unwrap", "expect", "print_macro", "todo",
             "unreachable", "unsafe_word")]
    add(md_table(["指标", "生产区（近似）"], rows))
    add("")

    # 4. env switches
    add("## 4. 环境开关与构建结构")
    add("")
    env = report["env"]
    add(f"- distinct `env::var` 名字：**{fmt_int(env['distinct'])}**"
        f"（层内 distinct = {fmt_int(env['layer_only_distinct'])}；"
        f"总出现次数 = {fmt_int(env['total_occurrences'])}）")
    add("")
    rows = []
    for item in env["names"][:40]:
        rows.append([f"`{item['name']}`", fmt_int(item["count"]),
                     fmt_int(item["file_count"]),
                     "、".join(f"`{p}`" for p in item["files"][:3])])
    if rows:
        add(md_table(["开关名", "次数", "文件数", "示例文件"], rows))
        add("")
    cargo = report["cargo"]
    add(f"- Cargo.toml：`[[bin]]` **{cargo['bin_targets']}**、`[[test]]` "
        f"{cargo['test_targets']}、`test = false` **{cargo['test_false']}**、"
        f"`[features]` {cargo['features_sections']}、Cargo 内 `#[path]` "
        f"{cargo['path_attrs_in_cargo']}")
    add(f"- 源码中 `#[path]` 总次数：**{fmt_int(report['artifacts']['path_attr_total'])}**"
        f"（`src/` 全量；`tests/` 另计见 JSON）")
    add("")

    # 5. artifacts
    art = report["artifacts"]
    add("## 5. 归档 / 垃圾状态（P1 对象）")
    add("")
    add(f"- `src/bench_head` 存在：`{art['src_bench_head_exists']}`；"
        f"`src/bench_pre` 存在：`{art['src_bench_pre_exists']}`；"
        f"发现的归档位置：{art['moved_archive_locations'] or '（无）'}")
    rel = art.get("relocated_archive") or {}
    if rel.get("files"):
        add(f"- 已移出 `src/` 的归档快照（`{'`、`'.join(rel['paths'])}`）："
            f"{fmt_int(rel['files'])} 个 `.rs` / {fmt_int(rel['nonempty'])} 非空行"
            "（不计入上方 `src/` 指标；P1 的“移动而非删除”证据）")
    add(f"- `.bak`：{fmt_int(art['bak']['files'])} 文件 / "
        f"{fmt_int(art['bak']['nonempty'])} 非空行"
        + ("；按层：" + "、".join(f"`{k}`={fmt_int(v['files'])}"
                                for k, v in (art["bak"]["by_layer"] or {}).items())
           if art["bak"]["by_layer"] else "（基线快照中无 .bak；D3 历史实测 17 文件/12,464 行，"
           "已在 P1 清理中删除，git 不跟踪、不可重测）"))
    add("")
    if art["bak_files"]:
        rows = [[f"`{b['path']}`", fmt_int(b["nonempty"])] for b in art["bak_files"][:20]]
        add(md_table(["`.bak` 文件", "非空行"], rows))
        add("")

    # 6. families
    add("## 6. 机制文件族与跨层复制（抽样 Jaccard）")
    add("")
    fam = report["families"]
    if fam.get("top_pairs"):
        add("Top 同族行集合 Jaccard（去空行、去 <4 字符的短行）：")
        add("")
        rows = []
        for p in fam["top_pairs"][:20]:
            rows.append([f"`{p['family']}`", p["a"], p["b"],
                         f"{p['jaccard'] * 100:.1f}%"])
        add(md_table(["文件族", "A", "B", "Jaccard"], rows))
        add("")
    add(f"发现的文件族数：{len(fam.get('by_family', {}))}；"
        "逐族明细（含文件清单与族内 top 对）见 JSON。")
    add("")
    # Fixed sample pairs used by D3 for the copy-forward argument; looking them
    # up here makes the D3 number check a one-command operation.
    sample = [
        ("pretty", "L07_sum_type/ref", "L08_product_type/ref"),
        ("elaboration", "L07_sum_type/ref", "L08_product_type/ref"),
        ("pattern_match", "L07_sum_type/ref", "L08_product_type/ref"),
        ("parser", "L07_sum_type/ref", "L08_product_type/ref"),
        ("typeclass", "L10_typeclass/ref", "L11_macro/ref"),
        ("unification", "L10_typeclass/ref", "L11_macro/ref"),
        ("unification", "L11_macro/ref", "L12_canonical/ref"),
        ("lex", "L12_canonical/ref", "L13_namespace/ref"),
    ]
    rows = []
    for fam_name, a, b in sample:
        entry = fam.get("by_family", {}).get(fam_name)
        if not entry:
            continue
        hit = None
        for pair in entry.get("all_pairs", entry.get("top_pairs", [])):
            if {pair["a"], pair["b"]} == {a, b}:
                hit = pair
                break
        rows.append([f"`{fam_name}`", a, b,
                     f"{hit['jaccard'] * 100:.1f}%" if hit else "—"])
    if rows:
        add("D3 报告 §3 抽样对的对账值：")
        add("")
        add(md_table(["文件族", "A", "B", "Jaccard（本工具）"], rows))
        add("")

    # 7. P1 comparison
    cmp = report.get("compare")
    if cmp:
        add("## 7. P1 清理前后对比（实扫描：基线 vs 当前）")
        add("")
        b = cmp["baseline"]
        c = cmp["current"]
        bs = cmp.get("baseline_snapshot") or {}
        cs = cmp.get("current_snapshot") or {}
        b_label = (f"git ref `{bs.get('ref')}` 快照"
                   if bs.get("mode") == "git-ref" else "工作树快照")
        c_label = ("当前工作树磁盘状态" if cs.get("mode") == "worktree"
                   else f"git ref `{cs.get('ref')}` 快照")
        add(f"基线 = {b_label}；当前 = {c_label}。P1 清理 = 移出 "
            "`src/bench_head` + `src/bench_pre`、删除 `.bak`。"
            + ("两侧均为 git ref 快照（可复现、不受工作树未提交编辑影响）。"
               if bs.get("mode") == "git-ref" and cs.get("mode") == "git-ref"
               else "若采集时工作树仍在清理中，数字可能不完整，清理落地后重跑即可。"))
        add("")
        rows = [
            ["`src/` 文件数", fmt_int(b["src_files"]), fmt_int(c["src_files"]),
             f"{c['src_files'] - b['src_files']:+d}"],
            ["`src/` 非空行", fmt_int(b["src_nonempty"]), fmt_int(c["src_nonempty"]),
             f"{c['src_nonempty'] - b['src_nonempty']:+d}"],
            ["`src/` 物理行", fmt_int(b["src_physical"]), fmt_int(c["src_physical"]),
             f"{c['src_physical'] - b['src_physical']:+d}"],
        ]
        for kind in ("ref", "twin", "test", "bin", "glue", "archive"):
            rows.append([f"　`{kind}` 非空行",
                         fmt_int(b["kinds"][kind]["nonempty"]),
                         fmt_int(c["kinds"][kind]["nonempty"]),
                         f"{c['kinds'][kind]['nonempty'] - b['kinds'][kind]['nonempty']:+d}"])
        rows.append(["层内（ref+twin+test）非空行",
                     fmt_int(b["layer_only"]["nonempty"]),
                     fmt_int(c["layer_only"]["nonempty"]),
                     f"{c['layer_only']['nonempty'] - b['layer_only']['nonempty']:+d}"])
        rows.append(["层内文件数", fmt_int(b["layer_only"]["files"]),
                     fmt_int(c["layer_only"]["files"]),
                     f"{c['layer_only']['files'] - b['layer_only']['files']:+d}"])
        add(md_table(["指标", "基线", "当前", "变化"], rows))
        add("")
        add("层内不变量：" + ("✅ **层内指标完全不变**（P1 只动了归档/`.bak`）"
                              if cmp["layer_only_invariant"]
                              else "⚠️ **层内有差异**——工作树可能存在并发编辑："
                              + "、".join(f"`{k}` {v:+d} 行"
                                         for k, v in cmp["layers_changed"].items())))
        add("")
        rows = []
        for key in ("unsafe_word", "panic_macro", "unwrap", "expect",
                    "print_macro", "path_attr"):
            rows.append([f"`{key}`", fmt_int(b["src_wide"][key]),
                         fmt_int(c["src_wide"][key]),
                         f"{c['src_wide'][key] - b['src_wide'][key]:+d}"])
        add(md_table(["`src/` 全量风险计数", "基线", "当前", "变化"], rows))
        add("")
        rows = [
            ["环境开关 distinct（`src/` 全量）", b["env_distinct"],
             c["env_distinct"]],
            ["环境开关 distinct（层内）", b["env_layer_only_distinct"],
             c["env_layer_only_distinct"]],
            ["`[[bin]]`", b["cargo"]["bin_targets"], c["cargo"]["bin_targets"]],
            ["`test = false`", b["cargo"]["test_false"], c["cargo"]["test_false"]],
            ["`.bak` 文件数", b["artifacts"]["bak_files"],
             c["artifacts"]["bak_files"]],
            ["`src/bench_head` 存在", b["artifacts"]["src_bench_head_exists"],
             c["artifacts"]["src_bench_head_exists"]],
            ["`src/bench_pre` 存在", b["artifacts"]["src_bench_pre_exists"],
             c["artifacts"]["src_bench_pre_exists"]],
            ["`#[path]` 总次数（`src/`）", b["artifacts"]["path_attr_total"],
             c["artifacts"]["path_attr_total"]],
        ]
        add(md_table(["结构指标", "基线", "当前"], rows))
        add("")
    else:
        p1 = report["p1_projection"]
        add("## 7. P1 清理后对比（投影，非实测）")
        add("")
        add("假设：把 `src/bench_head` + `src/bench_pre` 移出 `src/`，删除全部 "
            "`*.bak`，其余不动。**P1 之后应重跑本脚本并以 JSON diff 验证**；"
            "本节数字来自同一次扫描的投影。")
        add("")
        rows = [
            ["`src/` 文件数", fmt_int(p1["baseline_src_files"]),
             fmt_int(p1["post_src_files"]),
             f"-{fmt_int(p1['archive_files'])}"],
            ["`src/` 非空行", fmt_int(p1["baseline_src_nonempty"]),
             fmt_int(p1["post_src_nonempty"]),
             f"-{fmt_int(p1['archive_nonempty'])}（-{p1['archive_nonempty'] / max(p1['baseline_src_nonempty'], 1) * 100:.1f}%）"],
            ["`src/` 物理行", fmt_int(p1["baseline_src_physical"]),
             fmt_int(p1["post_src_physical"]),
             f"-{fmt_int(p1['archive_physical'])}"],
            ["另删除 `.bak`（不在 `src/` 合计内）", fmt_int(p1["bak_nonempty"]),
             "0", f"-{fmt_int(p1['bak_nonempty'])}"],
            ["**合计移出/删除（非空行）**", "—", "—",
             f"**{fmt_int(p1['removed_total_nonempty'])}**"],
        ]
        add(md_table(["指标", "基线", "P1 后", "变化"], rows))
        add("")
        rows = []
        for key in ("unsafe_word", "panic_macro", "unwrap", "expect",
                    "print_macro", "path_attr"):
            rows.append([f"`{key}`", fmt_int(p1["src_wide_counters_before"][key]),
                         fmt_int(p1["src_wide_counters_after"][key])])
        add("`src/` 全量风险计数（归档移走后）：")
        add("")
        add(md_table(["指标", "基线", "P1 后"], rows))
        add("")
        ref = p1["d3_historical_reference"]
        add(f"> 参考（{ref['source']}，历史实测）：`.bak` = {ref['bak_files']} 文件 / "
            f"{fmt_int(ref['bak_nonempty'])} 非空行；归档 = "
            f"{fmt_int(ref['archive_nonempty'])} 非空行；合计 {fmt_int(ref['total_removed_nonempty'])}。"
            "`.bak` 在 HEAD 未跟踪、本工具无法重测，只作对账参考。")
        add("")
        add("> 注意：**层内（ref+twin+test）指标不因 P1 变化**（归档与 `.bak` 不计入层内）；"
            "P1 只改变 `src/` 全量口径与仓库物理体积。")
        add("")

    # 8. reproduce
    add("## 8. 复现")
    add("")
    add("```bash")
    add("# 当前工作树快照：")
    add("python tools/metrics.py --json /tmp/metrics-worktree.json")
    add("# P1 前基线（HEAD 快照）+ 与当前工作树的实扫描对比：")
    add("python tools/metrics.py --git-ref HEAD --compare-current \\")
    add("  --json docs/metrics/baseline-YYYY-MM-DD.json \\")
    add("  --md   docs/metrics/baseline-YYYY-MM-DD.md")
    add("# CI 可重复性（无时间戳，可 diff）：")
    add("python tools/metrics.py --deterministic --json /tmp/metrics.json")
    add("```")
    add("")
    if json_path:
        add(f"机器可读版：`{json_path}`")
        add("")
    add("## 9. CI 门禁（`--check`）")
    add("")
    add("`tools/gate_p0.sh` 调用 `python tools/metrics.py --check`（只看 exit code）。"
        "检查项与阈值（基线 = 本 JSON 的 `check_baseline`，缺失时用内置常量）：")
    add("")
    rows = [["`src/` 非空行", "≤ 基线 ×1.005（+0.5%）"],
            ["层内非空行", "≤ 基线 ×1.005"],
            ["`unsafe`（层内）", "不得高于基线"],
            ["`panic!` / `.unwrap()` / `.expect()` / print 宏（层内）", "不得高于基线"],
            ["归档非空行 / `.bak` 文件数", "必须为 0（不得重新引入）"],
            ["跨层复制（Jaccard ≥90% / ≥95% 的对数）", "不得高于基线"]]
    add(md_table(["检查项", "阈值"], rows))
    add("")
    add("**退出码策略（首轮选择）**：默认 `--check` 只打印 `WARN` 且 **exit 0**（不阻塞 CI，"
        "避免基线刚建立/清理进行中被误红）；加 `--strict` 才在 WARN 时 exit 1。"
        "P1 清理落地、基线稳定后建议把 `gate_p0.sh` 改为 `--check --strict`。"
        "基线缺失时自动退回内置阈值并在输出中标注 `baseline=builtin`。")
    add("")
    add("```bash")
    add("python tools/metrics.py --check            # WARN+exit0（默认，advisory）")
    add("python tools/metrics.py --check --strict   # WARN+exit1（阻断）")
    add("python tools/metrics.py --check --baseline-json path/to/baseline.json")
    add("```")
    add("")
    add("---")
    add("")
    add("*本文件由 `tools/metrics.py` 生成，请勿手工修改数字；"
        "口径说明见 `docs/optimal-design/P1-metrics-report.md`。*")
    return "\n".join(L) + "\n"


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Static repository metrics (stdlib only; read-only).",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--root", default=REPO_ROOT,
                        help="repository root (default: parent of tools/)")
    parser.add_argument("--json", default=None,
                        help="write JSON report to this path ('-' = stdout)")
    parser.add_argument("--md", default=None,
                        help="write Markdown report to this path ('-' = stdout)")
    parser.add_argument("--test-rule", choices=("plural", "any"), default="plural",
                        help="test file rule: plural=*/tests.rs (D3 convention), "
                             "any=basename contains 'test'")
    parser.add_argument("--git-ref", default=None,
                        help="measure a git ref snapshot (e.g. HEAD) instead of the "
                             "working tree; materialized via `git archive` in a temp dir")
    parser.add_argument("--compare-current", action="store_true",
                        help="with --git-ref: also scan the working tree and add a "
                             "baseline-vs-current comparison (P1 delta)")
    parser.add_argument("--compare-ref", default=None,
                        help="scan the working tree as primary and compare it against "
                             "this git ref (e.g. HEAD): P1 before/after delta")
    parser.add_argument("--check", action="store_true",
                        help="repo metrics gate: compare the working tree against the "
                             "checked-in baseline and print PASS/WARN; exit 0 unless "
                             "--strict")
    parser.add_argument("--check-budgets", action="store_true",
                        help=argparse.SUPPRESS)  # compatibility alias for older gates
    parser.add_argument("--strict", action="store_true",
                        help="with --check: exit 1 when any WARN is reported "
                             "(default is advisory: WARN + exit 0)")
    parser.add_argument("--baseline-json", default=None,
                        help=f"with --check: baseline JSON path "
                             f"(default: {DEFAULT_BASELINE_JSON}; falls back to builtin)")
    parser.add_argument("--deterministic", action="store_true",
                        help="omit timestamp / git fields for diffable output")
    parser.add_argument("--no-git", action="store_true",
                        help="skip git subprocess probing")
    args = parser.parse_args(argv)

    root = os.path.abspath(args.root)
    if not os.path.isdir(os.path.join(root, "src")):
        parser.error(f"{root} does not look like the repository root (no src/)")

    # --check: advisory metrics gate used by tools/gate_p0.sh.
    if args.check or args.check_budgets:
        return run_check(root, baseline_path=args.baseline_json,
                         strict=args.strict, test_rule=args.test_rule)

    import datetime
    timestamp = None
    if not args.deterministic:
        timestamp = datetime.datetime.now(
            datetime.timezone.utc).isoformat(timespec="seconds")
    repo_git = {} if args.no_git else git_info(root)

    tmpdir = None
    tmpdir2 = None
    try:
        if args.git_ref:
            try:
                tmpdir = export_git_tree(root, args.git_ref)
            except RuntimeError as exc:
                parser.error(str(exc))
            report = build_report(tmpdir, test_rule=args.test_rule)
            report["root"] = os.path.basename(os.path.normpath(root))
            report["git"] = repo_git
            report["snapshot"] = {"mode": "git-ref", "ref": args.git_ref,
                                  "test_rule": args.test_rule}
            if args.compare_current:
                current = build_report(root, test_rule=args.test_rule)
                current["git"] = repo_git
                current["snapshot"] = {"mode": "worktree",
                                       "test_rule": args.test_rule}
                report["compare"] = compare_snapshots(report, current)
                report["compare"]["baseline_snapshot"] = report["snapshot"]
                report["compare"]["current_snapshot"] = current["snapshot"]
            elif args.compare_ref:
                try:
                    tmpdir2 = export_git_tree(root, args.compare_ref)
                except RuntimeError as exc:
                    parser.error(str(exc))
                before = build_report(tmpdir2, test_rule=args.test_rule)
                before["root"] = os.path.basename(os.path.normpath(root))
                before["git"] = repo_git
                before["snapshot"] = {"mode": "git-ref",
                                      "ref": args.compare_ref,
                                      "test_rule": args.test_rule}
                report["compare"] = compare_snapshots(before, report)
                report["compare"]["baseline_snapshot"] = before["snapshot"]
                report["compare"]["current_snapshot"] = report["snapshot"]
        else:
            report = build_report(root, test_rule=args.test_rule)
            report["git"] = repo_git
            report["snapshot"] = {"mode": "worktree",
                                  "test_rule": args.test_rule}
            if args.compare_ref:
                try:
                    tmpdir = export_git_tree(root, args.compare_ref)
                except RuntimeError as exc:
                    parser.error(str(exc))
                baseline = build_report(tmpdir, test_rule=args.test_rule)
                baseline["root"] = os.path.basename(os.path.normpath(root))
                baseline["git"] = repo_git
                baseline["snapshot"] = {"mode": "git-ref",
                                        "ref": args.compare_ref,
                                        "test_rule": args.test_rule}
                report["compare"] = compare_snapshots(baseline, report)
                report["compare"]["baseline_snapshot"] = baseline["snapshot"]
                report["compare"]["current_snapshot"] = report["snapshot"]
    finally:
        import shutil
        for d in (tmpdir, tmpdir2):
            if d:
                shutil.rmtree(d, ignore_errors=True)

    report["generated_at"] = timestamp
    if args.no_git:
        report["git"] = {}

    # Stable JSON ordering.
    payload = json.dumps(report, sort_keys=True, ensure_ascii=False, indent=2)

    if args.json == "-":
        sys.stdout.write(payload + "\n")
    elif args.json:
        outdir = os.path.dirname(os.path.abspath(args.json))
        if outdir:
            os.makedirs(outdir, exist_ok=True)
        with open(args.json, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(payload + "\n")

    if args.md == "-":
        sys.stdout.write(render_markdown(report, args.json))
    elif args.md:
        outdir = os.path.dirname(os.path.abspath(args.md))
        if outdir:
            os.makedirs(outdir, exist_ok=True)
        with open(args.md, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(render_markdown(report, args.json))

    if not args.json and not args.md:
        # Human summary to stdout.
        t = report["totals"]["by_kind"]
        print(f"src files={t['src_no_bak']['files']} "
              f"nonempty={t['src_no_bak']['nonempty']} "
              f"physical={t['src_no_bak']['physical']} | "
              f"layers(ref+twin+test)={report['totals']['layer_only_counts']['files']} files | "
              f"env={report['env']['distinct']} | "
              f"unsafe={report['risk']['layer_only']['unsafe_word']} | "
              f"bak={report['artifacts']['bak']['files']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
