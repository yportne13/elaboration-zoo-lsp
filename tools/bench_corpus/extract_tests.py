#!/usr/bin/env python3
"""从仓库内 Rust 测试/基准源码与 README 代码块中抽取 Typort 源程序候选。

用途：给 L07-L13 的「真实语料性能基准」提供候选池（raw/）。候选未经语义
验证，必须再用 `realbench --validate`（或各层 `run`）过滤——测试文件里本来
就有大量故意写错的程序。

用法：
    python tools/bench_corpus/extract_tests.py [--out tools/bench_corpus/raw]
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# 每层的候选来源（相对仓库根）。README 只取 ``` / ```typort 代码块。
SOURCES: dict[str, list[str]] = {
    "L07": [
        "tests/l07_blackbox.rs",
        "tests/l07_blackbox_v2.rs",
        "tests/l07_blackbox_v3.rs",
        "tests/l07_fast_parity.rs",
        "src/L07_sum_type/tests.rs",
        "src/L07_sum_type/bump_spine_iter/bench_src.rs",
        "src/L07_sum_type/README.md",
    ],
    "L08": [
        "tests/l08_blackbox.rs",
        "tests/l08_blackbox_v2.rs",
        "tests/l08_fast_parity.rs",
        "src/L08_product_type/tests.rs",
        "src/L08_product_type/bump_spine_iter/bench_src.rs",
        "src/L08_product_type/README.md",
    ],
    "L09": [
        "tests/l09_fast_parity.rs",
        "src/L09_mltt/bump_spine_iter/bench_src.rs",
        "src/L09_mltt/README.md",
    ],
    "L10": [
        "tests/l10_fast_parity.rs",
        "src/L10_typeclass/bump_spine_iter/bench_src.rs",
        "src/L10_typeclass/README.md",
    ],
    "L11": [
        "tests/l11_fast_parity.rs",
        "src/L11_macro/bump_spine_iter/bench_src.rs",
        "src/L11_macro/README.md",
    ],
    "L12": [
        "tests/l12_fast_parity.rs",
        "src/L12_canonical/bump_spine_iter/bench_src.rs",
        "src/L12_canonical/README.md",
    ],
    "L13": [
        "tests/l13_fast_parity.rs",
        "tests/twin_engine_tests.rs",
        "src/L13_namespace/bump_spine_iter/bench_src.rs",
        "src/L13_namespace/README.md",
    ],
}

RAW_RE = re.compile(r'r(#*)"(.*?)"\1', re.S)
NORM_RE = re.compile(r'"((?:[^"\\\n]|\\.)*)"')
FENCE_RE = re.compile(r"```(?:typort|rust)?\n(.*?)```", re.S)
KEYWORDS = ("def ", "enum ", "struct ", "trait ", "impl ", "macro_rules", "package ", "import ")


def unescape_rust(s: str) -> str:
    out = []
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            n = s[i + 1]
            out.append({"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\", "0": "\0"}.get(n, n))
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def looks_like_typort(s: str) -> bool:
    if len(s) < 40:
        return False
    if not any(k in s for k in KEYWORDS):
        return False
    # 纯 Rust 片段常见标记，出现则大概率不是 Typort 源
    if any(k in s for k in ("fn main", "println!(", "assert_eq!(", "use std::", "-> Result<")):
        return False
    return True


def extract_rust(path: Path) -> list[tuple[str, int]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    found: list[tuple[str, int]] = []
    for m in RAW_RE.finditer(text):
        found.append((m.group(2), m.start()))
    for m in NORM_RE.finditer(text):
        raw = m.group(1)
        if "\\n" not in raw and len(raw) < 120:
            continue  # 单行短字符串几乎都是标识/错误文案，不是程序
        found.append((unescape_rust(raw), m.start()))
    return found


def extract_readme(path: Path) -> list[tuple[str, int]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    return [(m.group(1), m.start()) for m in FENCE_RE.finditer(text)]


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(ROOT / "tools" / "bench_corpus" / "raw"))
    args = ap.parse_args()
    out_root = Path(args.out)
    summary = {}
    for layer, rels in SOURCES.items():
        out_dir = out_root / layer
        out_dir.mkdir(parents=True, exist_ok=True)
        for old in out_dir.glob("case_*.typort"):
            old.unlink()
        seen: set[str] = set()
        manifest: list[dict] = []
        n = 0
        for rel in rels:
            path = ROOT / rel
            if not path.exists():
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            items = extract_readme(path) if path.suffix == ".md" else extract_rust(path)
            for src, offset in items:
                if not looks_like_typort(src):
                    continue
                key = re.sub(r"\s+", " ", src).strip()
                if key in seen:
                    continue
                seen.add(key)
                n += 1
                name = f"case_{n:03d}.typort"
                (out_dir / name).write_text(src if src.endswith("\n") else src + "\n", encoding="utf-8")
                manifest.append({"file": name, "source": rel, "line": line_of(text, offset), "bytes": len(src)})
        with (out_dir / "manifest.jsonl").open("w", encoding="utf-8") as fh:
            for row in manifest:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        summary[layer] = len(manifest)
        print(f"{layer}: {len(manifest)} candidates -> {out_dir}")
    print(json.dumps(summary, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
