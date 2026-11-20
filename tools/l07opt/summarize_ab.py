#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""L07 参考版改进的 A/B 汇总：base（旧）vs new（当前分支）。

读取 tools/l07opt/run_ab_cases.ps1 产出：
  elab_<tag>.csv / nf_<tag>.csv / nfcheck_<tag>.csv / alloc_<tag>.csv / synth_<tag>.txt
输出 Markdown：base→new 加速、new/twin 比、分配计数、合成负载加速、可选 smalltt 对比。
"""
import argparse, json, os, re, sys

NF = {'forcetree', 'nftree'}
CASES = [('natconv', ['1k','10k','100k','1M']), ('treeconv', ['10','15','18','20']),
         ('treeconvm', ['10','15','18']), ('idtest', ['40']),
         ('pairtest', ['10','15','20']), ('vectest', ['240','960']),
         ('stlc', ['8','40','80']), ('stlcs', ['96','192']), ('stlcl', ['40','80']),
         ('forcetree', ['15','18','20']), ('nftree', ['15','18','20'])]
SMALLTT = {
    ('natconv','1M'): ('conv_eval','elab','convn1M'),
    ('treeconv','15'): ('conv_eval','elab','convt15'), ('treeconv','18'): ('conv_eval','elab','convt18'),
    ('treeconv','20'): ('conv_eval','elab','convt20'),
    ('treeconvm','15'): ('conv_eval','elab','convmt15'), ('treeconvm','18'): ('conv_eval','elab','convmt18'),
    ('forcetree','15'): ('conv_eval','nf','forcet15'), ('forcetree','18'): ('conv_eval','nf','forcet18'),
    ('forcetree','20'): ('conv_eval','nf','forcet20'),
    ('nftree','15'): ('conv_eval','nf','nft15'), ('nftree','18'): ('conv_eval','nf','nft18'),
    ('nftree','20'): ('conv_eval','nf','nft20'),
    ('vectest','960'): ('asymptotics','elab','vecTest'),
    ('stlc','40'): ('stlc5k','elab','bench/stlc5k.stt'), ('stlc','80'): ('stlc10k','elab','bench/stlc10k.stt'),
    ('stlcl','40'): ('stlc_lessimpl5k','elab','bench/stlc_lessimpl5k.stt'),
    ('stlcl','80'): ('stlc_lessimpl10k','elab','bench/stlc_lessimpl10k.stt'),
    ('stlcs','96'): ('stlc_small5k','elab','bench/stlc_small5k.stt'),
    ('stlcs','192'): ('stlc_small10k','elab','bench/stlc_small10k.stt'),
}

def load_dir(d, tag, rows):
    for fn in ('elab_%s.csv' % tag, 'nf_%s.csv' % tag, 'nfcheck_%s.csv' % tag):
        p = os.path.join(d, fn)
        if not os.path.exists(p):
            continue
        for line in open(p, encoding='utf-8', errors='replace'):
            if not line.startswith('CASE,'):
                continue
            c = line.strip().split(',')
            if len(c) < 17:
                continue
            cur = rows.setdefault((tag, c[2], c[3]), {})
            v = [int(x) for x in c[6:14]]
            for name, us in {'ref': v[0], 'rf': v[2], 'twin': v[4], 'tnf': v[6]}.items():
                if us > 0:
                    cur[name] = us

def metric(rows, tag, case, size):
    r = rows.get((tag, case, size), {})
    if case in NF:
        tot = r.get('rf') or r.get('tnf')
        chk = r.get('ref') or r.get('twin') or 0
        return (tot - chk) if (tot and chk and tot > chk) else tot
    return r.get('ref') or r.get('twin')

def twin_metric(rows, tag, case, size):
    r = rows.get((tag, case, size), {})
    if case in NF:
        tot = r.get('tnf'); chk = r.get('twin') or 0
        return (tot - chk) if (tot and chk and tot > chk) else tot
    return r.get('twin')

def fms(us):
    if us is None:
        return '—'
    return '%.2f s' % (us / 1e6) if us >= 1e6 else '%.1f ms' % (us / 1000.0)

def main():
    try:
        sys.stdout.reconfigure(encoding='utf-8')
    except Exception:
        pass
    ap = argparse.ArgumentParser()
    ap.add_argument('--dir', required=True)
    ap.add_argument('--base', default='base')
    ap.add_argument('--new', default='new')
    ap.add_argument('--smalltt-parsed', default=None)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    rows = {}
    for tag in (a.base, a.new):
        load_dir(a.dir, tag, rows)
    out = []
    if a.smalltt_parsed:
        parsed = json.load(open(a.smalltt_parsed, encoding='utf-8'))
        def stv(src, kind, name):
            v = parsed.get(src, {}).get(kind, {}).get(name)
            return v['min'] * 1e6 if v else None
        out += ['| 用例 | smalltt | base | new | base/smalltt | new/smalltt |',
                '|---|---:|---:|---:|---:|---:|']
        ts = tb = tn = 0.0
        for (case, size), (src, kind, name) in SMALLTT.items():
            sv = stv(src, kind, name); b = metric(rows, a.base, case, size); n = metric(rows, a.new, case, size)
            if not (sv and b and n):
                continue
            ts += sv; tb += b; tn += n
            out.append('| %s %s | %s | %s | %s | %.2f× | **%.2f×** |' % (
                case, size, fms(sv), fms(b), fms(n), b / sv, n / sv))
        out.append('| **合计** | **%s** | **%s** | **%s** | **%.2f×** | **%.2f×** |' % (
            fms(ts), fms(tb), fms(tn), tb / ts, tn / ts))
        out.append('')
    out += ['| 用例 | size | base | new | 加速 | new/twin |', '|---|---:|---:|---:|---:|---:|']
    sp = []
    sb = sn = 0.0
    for case, sizes in CASES:
        for size in sizes:
            b = metric(rows, a.base, case, size); n = metric(rows, a.new, case, size)
            t = twin_metric(rows, a.new, case, size)
            if not (b and n):
                continue
            sb += b; sn += n
            sp.append(b / n)
            out.append('| %s | %s | %s | %s | **%.2f×** | %s |' % (
                case, size, fms(b), fms(n), b / n, ('%.2f' % (n / t)) if t else '—'))
    if sb:
        out.append('| **合计** | | **%s** | **%s** | **%.2f×** | |' % (fms(sb), fms(sn), sb / sn))
        sp.sort()
        out.append('')
        out.append('加速分布：min %.2f× / median %.2f× / max %.2f×（%d 档）' % (
            sp[0], sp[len(sp)//2], sp[-1], len(sp)))
    # alloc
    al = []
    for tag in (a.base, a.new):
        p = os.path.join(a.dir, 'alloc_%s.csv' % tag)
        if not os.path.exists(p):
            continue
        for line in open(p, encoding='utf-8', errors='replace'):
            if line.startswith('ALLOC,'):
                c = line.strip().split(',')
                al.append((tag, c[2], c[3], int(c[4]), int(c[5])))
    if al:
        out += ['', '| 用例 | size | base 分配/字节 | new 分配/字节 | 字节比 |', '|---|---:|---:|---:|---:|']
        base_map = {(c, s): (n_, b_) for (t, c, s, n_, b_) in al if t == a.base}
        for (t, c, s, n_, b_) in al:
            if t != a.new:
                continue
            bk = base_map.get((c, s))
            if not bk:
                continue
            out.append('| %s | %s | %s / %.2f GB | %s / %.2f GB | %.2f× |' % (
                c, s, f'{bk[0]:,}', bk[1] / 1e9, f'{n_:,}', b_ / 1e9, b_ / bk[1]))
    # synthetic
    def synth(tag):
        p = os.path.join(a.dir, 'synth_%s.txt' % tag)
        res = {}
        if not os.path.exists(p):
            return res
        wl = None
        for line in open(p, encoding='utf-8', errors='replace'):
            s = line.strip().lstrip('\ufeff')
            m = re.match(r'== workload: (\w+) ==', s)
            if m:
                wl = m.group(1); continue
            m = re.match(r'k=(\d+)\s+n=(\d+).*?basic=\s*([0-9]+)\.([0-9]{3})ms', line)
            if m and wl:
                res[(wl, int(m.group(1)))] = int(m.group(3)) + int(m.group(4)) / 1000.0
        return res
    sb_, sn_ = synth(a.base), synth(a.new)
    items = []
    for wl in ['church', 'strchain', 'global', 'match', 'enum', 'natadd']:
        ks = [k for (w, k) in sb_ if w == wl and (w, k) in sn_]
        if not ks:
            continue
        k = max(ks)
        items.append('| %s | %d | %.3f | %.3f | **%.2f×** |' % (
            wl, k, sb_[(wl, k)], sn_[(wl, k)], sb_[(wl, k)] / sn_[(wl, k)]))
    if items:
        out += ['', '| 合成负载 | k | base (ms) | new (ms) | 加速 |', '|---|---:|---:|---:|---:|'] + items
    text = '\n'.join(out) + '\n'
    if a.out:
        open(a.out, 'w', encoding='utf-8').write(text)
        print('written ' + a.out)
    else:
        print(text)

if __name__ == '__main__':
    main()
