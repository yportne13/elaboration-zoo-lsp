#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""smalltt 本机基准 vs 我们 smallttbench CSV 的同机对照表。

输入：
  --parsed   parse-smalltt-bench.py 产出的 parsed.json
  --our-dir  可多次指定；smallttbench 的 CASE,<layer>,<case>,<size>,... CSV 目录
             （例如 target/smalltt_bench/final 与 target/smalltt_bench/same_machine）
输出：Markdown 表（默认 stdout，可用 --out 写文件）。

约定：
- elab 族：我们取 bench_check（ref）/ bench_check（twin）的 min；
- nf 族：我们取 (ref_nf - ref_check) / (twin_nf - twin_check) 的 min，对齐 smalltt [nftime]；
- 全 0 的轴视为未测；同一配置跨目录取 min。
"""
import argparse, glob, json, os, sys

ELAB = [
    ('natconv', '1M', 'conv_eval', 'elab', 'convn1M'),
    ('natconv', '5M', 'conv_eval', 'elab', 'convn5M'),
    ('natconv', '10M', 'conv_eval', 'elab', 'convn10M'),
    ('treeconv', '15', 'conv_eval', 'elab', 'convt15'),
    ('treeconv', '18', 'conv_eval', 'elab', 'convt18'),
    ('treeconv', '19', 'conv_eval', 'elab', 'convt19'),
    ('treeconv', '20', 'conv_eval', 'elab', 'convt20'),
    ('treeconv', '21', 'conv_eval', 'elab', 'convt21'),
    ('treeconv', '22', 'conv_eval', 'elab', 'convt22'),
    ('treeconv', '23', 'conv_eval', 'elab', 'convt23'),
    ('treeconvm', '15', 'conv_eval', 'elab', 'convmt15'),
    ('treeconvm', '18', 'conv_eval', 'elab', 'convmt18'),
    ('treeconvm', '19', 'conv_eval', 'elab', 'convmt19'),
    ('treeconvm', '20', 'conv_eval', 'elab', 'convmt20'),
    ('vectest', '960', 'asymptotics', 'elab', 'vecTest'),
    ('stlc', '40', 'stlc5k', 'elab', 'bench/stlc5k.stt'),
    ('stlc', '80', 'stlc10k', 'elab', 'bench/stlc10k.stt'),
    ('stlcl', '40', 'stlc_lessimpl5k', 'elab', 'bench/stlc_lessimpl5k.stt'),
    ('stlcl', '80', 'stlc_lessimpl10k', 'elab', 'bench/stlc_lessimpl10k.stt'),
    ('stlcs', '96', 'stlc_small5k', 'elab', 'bench/stlc_small5k.stt'),
    ('stlcs', '192', 'stlc_small10k', 'elab', 'bench/stlc_small10k.stt'),
]
NF = [
    ('forcetree', '15', 'forcet15'), ('forcetree', '18', 'forcet18'),
    ('forcetree', '19', 'forcet19'), ('forcetree', '20', 'forcet20'),
    ('nftree', '15', 'nft15'), ('nftree', '18', 'nft18'),
    ('nftree', '19', 'nft19'), ('nftree', '20', 'nft20'),
]
LAYERS = ['L07', 'L08', 'L09', 'L10']


def merge_dir(d, rows):
    for path in glob.glob(os.path.join(d, '*.csv')):
        with open(path, encoding='utf-8', errors='replace') as f:
            for line in f:
                if not line.startswith('CASE,'):
                    continue
                p = line.strip().split(',')
                if len(p) < 17:
                    continue
                key = (p[1], p[2], p[3])
                v = [int(x) for x in p[6:14]]
                cur = rows.setdefault(key, {})
                for name, us in {'ref': v[0], 'ref_nf': v[2], 'twin': v[4], 'twin_nf': v[6]}.items():
                    if us > 0 and (name not in cur or us < cur[name]):
                        cur[name] = us


def best(rows, case, size, axis, nf):
    vals = {}
    for L in LAYERS:
        r = rows.get((L, case, size), {})
        if nf:
            tot, chk = r.get(axis + '_nf'), r.get(axis)
            if tot and chk is not None and tot > chk:
                vals[L] = tot - chk
        else:
            if r.get(axis):
                vals[L] = r[axis]
    if not vals:
        return None, None
    m = min(vals.values())
    return m, [k for k, v in vals.items() if v == m][0]


def fmt_smalltt(ms):
    if ms is None:
        return '—'
    return ('%.2f s' % (ms / 1000.0)) if ms >= 1000 else ('%.1f ms' % ms)


def fmt_us(us):
    if us is None:
        return '—'
    return ('%.2f s' % (us / 1e6)) if us >= 1e6 else ('%.1f ms' % (us / 1000.0))


def ratio(us, ms):
    if us is None or not ms:
        return '—'
    return '%.2f×' % ((us / 1000.0) / ms)


def main():
    try:
        sys.stdout.reconfigure(encoding='utf-8')
    except Exception:
        pass
    ap = argparse.ArgumentParser()
    ap.add_argument('--parsed', required=True)
    ap.add_argument('--our-dir', action='append', required=True)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    st = json.load(open(a.parsed, encoding='utf-8'))
    rows = {}
    for d in a.our_dir:
        merge_dir(d, rows)

    def stv(src, kind, name):
        v = st.get(src, {}).get(kind, {}).get(name)
        return v['min'] * 1000.0 if v else None

    md = []
    for title, items, is_nf in (
        ('A. conv_eval：elaborate 族（smalltt [elabtime] vs 我们 bench_check）', ELAB, False),
        ('B. conv_eval：nf 族（smalltt [nftime] vs 我们 nf-only = ref_nf - check）', NF, True),
    ):
        md += ['#### ' + title, '',
               '| 用例 | smalltt 本机 | 我们 ref 最好层 | ref/smalltt | 我们 twin 最好层 | twin/smalltt |',
               '|---|---:|---|---:|---|---:|']
        for item in items:
            if is_nf:
                case, size, name = item
                ms = stv('conv_eval', 'nf', name)
            else:
                case, size, src, kind, name = item
                ms = stv(src, kind, name)
            br, brL = best(rows, case, size, 'ref', is_nf)
            bt, btL = best(rows, case, size, 'twin', is_nf)
            ref_cell = fmt_us(br) if br is None else '%s (%s)' % (fmt_us(br), brL)
            twin_cell = fmt_us(bt) if bt is None else '%s (%s)' % (fmt_us(bt), btL)
            md.append('| %s %s | %s | %s | %s | %s | %s |' % (
                case, size, fmt_smalltt(ms), ref_cell, ratio(br, ms), twin_cell, ratio(bt, ms)))
        md.append('')
    text = '\n'.join(md)
    if a.out:
        open(a.out, 'w', encoding='utf-8').write(text + '\n')
        print('written ' + a.out)
    else:
        print(text)


if __name__ == '__main__':
    main()
