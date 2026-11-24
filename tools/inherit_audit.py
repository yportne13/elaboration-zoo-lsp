#!/usr/bin/env python3
"""逐层继承审计 (inherit audit).

把上一章 (prev) 的每个 Rust 条目（fn/struct/enum/trait/impl/mod/const/type/union）
在被下一章 (next) 里"存活"的情况量化成 TSV 账本，供人工确认/登记偏差。

口径
----
* 条目范围用花括号配对求（字符串/注释先掩码），嵌套取最内层。
* 用 git diff --no-index -U0 的删除 hunk 归到 prev 侧最内层条目 => deleted 行数。
* status: identical(0 删除) / changed(有删除) / missing(文件或条目在 next 不存在)
* keep = 1 - deleted / item_lines

用法
----
python tools/inherit_audit.py --prev src/L07_sum_type --next src/L08_product_type --out docs/inheritance/L07-to-L08.tsv
"""
import argparse, os, re, subprocess

ITEM_RE = re.compile(
    r"^\s*(?:pub(?:\s*\([^)]*\))?\s+)?(?:(?:async|unsafe|const|extern|default)\s+)*"
    r"(fn|struct|enum|trait|impl|mod|const|static|type|union)\b(.*)$")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def mask(src):
    """把注释/字符串替换成空格，保留换行与长度（行号/列号不变）。"""
    out = list(src)
    i, n = 0, len(src)

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != chr(10):
                out[k] = " "

    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find(chr(10), i)
            j = n if j < 0 else j
            blank(i, j); i = j
        elif c == "/" and i + 1 < n and src[i + 1] == "*":
            j = src.find("*/", i + 2)
            j = n if j < 0 else j + 2
            blank(i, j); i = j
        elif c == "r" and i + 1 < n and src[i + 1] in '#"':
            j = i + 1
            while j < n and src[j] == "#":
                j += 1
            if j < n and src[j] == '"':
                hashes = src[i + 1:j]
                end = src.find('"' + hashes, j + 1)
                end = n if end < 0 else end + 1 + len(hashes)
                blank(i, end); i = end
            else:
                i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2; continue
                if src[j] == '"':
                    j += 1; break
                j += 1
            blank(i, j); i = j
        elif c == "'":
            if i + 2 < n and src[i + 2] == "'":
                blank(i, i + 3); i += 3
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


def scan_items(path):
    """-> [(kind, name, start, end, nlines)] 0-based, end 含。"""
    with open(path, encoding="utf-8", errors="replace") as f:
        src = f.read()
    m = mask(src).split(chr(10))
    items = []
    for ln, line in enumerate(m):
        mo = ITEM_RE.match(line)
        if not mo:
            continue
        kind, tail = mo.group(1), mo.group(2)
        ident = IDENT_RE.search(tail)
        if kind == "impl":
            hdr = (line[mo.start(1) + 4:] + " " + " ".join(
                x.strip() for x in m[ln + 1:ln + 4])).split("{")[0]
            name = " ".join(hdr.split())
        else:
            name = ident.group(0) if ident else "?"
        depth, seen_brace, end = 0, False, None
        for j in range(ln, len(m)):
            for ch in m[j]:
                if ch == "{":
                    depth += 1; seen_brace = True
                elif ch == "}":
                    depth -= 1
                    if seen_brace and depth == 0:
                        end = j; break
                elif ch == ";" and depth == 0 and not seen_brace:
                    end = j; break
            if end is not None:
                break
        if end is None:
            end = len(m) - 1
        items.append((kind, name, ln, end, end - ln + 1))
    return items


def deletions(prev, nxt):
    if not os.path.exists(nxt):
        return None
    pr = subprocess.run(["git", "diff", "--no-index", "-U0", "--", prev, nxt],
                        capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = []
    for line in pr.stdout.split(chr(10)):
        mo = re.match(r"^@@ -(\d+)(?:,(\d+))? \+\d+(?:,\d+)? @@", line)
        if mo:
            start = int(mo.group(1))
            cnt = 1 if mo.group(2) is None else int(mo.group(2))
            if cnt > 0:
                out.append((start, cnt))
    return out


def rel(base, p):
    return os.path.relpath(p, base).replace("\\", "/")


def audit(prev_dir, next_dir, out_path):
    rows = []
    for root, _, files in os.walk(prev_dir):
        for fn in sorted(files):
            if not fn.endswith(".rs"):
                continue
            p = os.path.join(root, fn)
            r = rel(prev_dir, p)
            n = os.path.join(next_dir, r)
            items = scan_items(p)
            dels = deletions(p, n)
            if dels is None:
                for kind, name, s, e, ln in items:
                    rows.append([r, kind, name, ln, ln, "missing-file", 0.0])
                continue
            if not items:
                continue
            per = [0] * len(items)
            for start, cnt in dels:
                for k in range(start, start + cnt):
                    best, bestlen = None, None
                    for idx, (kind, name, s, e, ln) in enumerate(items):
                        if s <= k - 1 <= e:
                            if bestlen is None or ln < bestlen:
                                best, bestlen = idx, ln
                    if best is not None:
                        per[best] += 1
            nkeys = set((k, nm) for k, nm, s, e, ln in scan_items(n))
            for idx, (kind, name, s, e, ln) in enumerate(items):
                if (kind, name) not in nkeys:
                    status, keep = "missing", 0.0
                elif per[idx] == 0:
                    status, keep = "identical", 1.0
                else:
                    status, keep = "changed", max(0.0, 1.0 - per[idx] / ln)
                rows.append([r, kind, name, ln, per[idx], status, round(keep, 4)])
    d = os.path.dirname(out_path)
    if d:
        os.makedirs(d, exist_ok=True)
    with open(out_path, "w", encoding="utf-8", newline=chr(10)) as f:
        f.write("file\tkind\titem\tprev_lines\tdeleted\tstatus\tkeep\n")
        for row in sorted(rows, key=lambda x: (-int(x[4]), x[0], x[2])):
            f.write("\t".join(str(x) for x in row) + chr(10))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prev", required=True)
    ap.add_argument("--next", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--top", type=int, default=15)
    a = ap.parse_args()
    rows = audit(a.prev, a.next, a.out)
    tot = len(rows)
    ident = sum(1 for r in rows if r[5] == "identical")
    changed = sum(1 for r in rows if r[5] == "changed")
    missing = sum(1 for r in rows if str(r[5]).startswith("missing"))
    plines = sum(int(r[3]) for r in rows)
    dlines = sum(int(r[4]) for r in rows)
    print(a.prev + " -> " + a.next)
    print("  items={} identical={} changed={} missing={}".format(tot, ident, changed, missing))
    print("  item_lines={} deleted={} line_keep={:.4f}".format(plines, dlines, 1 - dlines / max(1, plines)))
    print("  ledger: " + a.out)
    print("  top deleted:")
    for r in sorted(rows, key=lambda x: -int(x[4]))[:a.top]:
        if int(r[4]):
            print("    -{:<5} {}:{}  ({})".format(r[4], r[0], r[2], r[5]))


if __name__ == "__main__":
    main()
