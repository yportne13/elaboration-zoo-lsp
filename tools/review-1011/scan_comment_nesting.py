#!/usr/bin/env python3
"""Scan .typort sources for block comments whose OLD (non-nesting) and NEW
(nesting) preprocessings disagree -- i.e. a `/*` appearing inside a block
comment before its first `*/`. Those are the only inputs whose parse changes
with nested comment support."""
import sys
from pathlib import Path

roots = [Path("src/prelude"), Path("examples"), Path("tests"), Path("docs")]
hits = []
for root in roots:
    if not root.exists():
        continue
    for f in root.rglob("*.typort"):
        s = f.read_text(encoding="utf-8", errors="replace")
        i = 0
        n = len(s)
        while i < n:
            # skip strings (mirror preprocess rules)
            c = s[i]
            if c == '"':
                j = i + 1
                while j < n:
                    if s[j] == "\\":
                        j += 2
                    elif s[j] == '"':
                        break
                    else:
                        j += 1
                i = j + 1
                continue
            if c == "/" and i + 1 < n and s[i + 1] == "*":
                # scan old-style: first */ at depth 1; check for inner /*
                j = i + 2
                old_close = None
                inner_open = None
                while j < n - 1:
                    if s[j] == "*" and s[j + 1] == "/":
                        old_close = j
                        break
                    if s[j] == "/" and s[j + 1] == "*":
                        inner_open = j
                        # keep scanning to first */ (old semantics end)
                    j += 1
                if old_close is not None and inner_open is not None and inner_open < old_close:
                    line = s.count("\n", 0, i) + 1
                    hits.append((str(f), line, s[i:old_close + 2][:80]))
                i = (old_close if old_close is not None else n - 2) + 2
                continue
            i += 1

if hits:
    for f, line, frag in hits:
        print(f"{f}:{line}: {frag!r}")
    sys.exit(1)
print("no nesting-sensitive block comments found")
