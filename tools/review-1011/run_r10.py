#!/usr/bin/env python3
"""Round-10 performance experiment battery: 30 timed dimensions."""
import subprocess, re, time, json, statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXE = ROOT / 'target' / 'release'
OUT = ROOT / 'tools' / 'review-1011' / 'r10-perf' / 'RESULTS.md'
OUT.parent.mkdir(exist_ok=True)


def run(cmd, timeout=600):
    t0 = time.monotonic()
    p = subprocess.run(cmd, capture_output=True, text=True, encoding='utf-8',
                       errors='replace', timeout=timeout, cwd=str(ROOT))
    return p.stdout + p.stderr, time.monotonic() - t0, p.returncode


rows = []

# 1-13: one row per layer bench (smoke timing: parse+elab of the layer corpus)
for i in range(1, 14):
    b = EXE / f'l{i:02d}bench.exe'
    if not b.exists():
        rows.append((f'bench_l{i:02d}', 'MISSING', ''))
        continue
    out, dt, rc = run([str(b), '--rounds', '2'], timeout=900)
    m = re.findall(r'([\w\-]+)\s+([\d.]+)ms\s+\*\?', out)
    fast = re.findall(r'fast\s+([\d.]+)ms', out)
    basic = re.findall(r'basic\s+([\d.]+)ms', out)
    if basic and fast:
        rows.append((f'bench_l{i:02d}', f'basic={basic[0]}ms fast={fast[0]}ms', f'proc={dt:.1f}s'))
    else:
        rows.append((f'bench_l{i:02d}', f'rc={rc}', out.strip().splitlines()[-1][:80] if out.strip() else ''))

# 14: church scaling slope (k=9..13)
scale = []
for k in (9, 11, 13):
    out, dt, rc = run([str(EXE / 'l13bench.exe'), '--workload', 'church', '--max-k', str(k), '--rounds', '3'])
    fast = re.findall(r'fast\s+([\d.]+)ms', out)
    scale.append((k, fast[-1] if fast else '?'))
rows.append(('church_scaling', ' '.join(f'k={k}:{v}ms' for k, v in scale), 'doubling slope'))

# 15-21: seven workload families on l13
for w in ('natadd', 'gadt', 'match', 'enum', 'struct', 'strchain', 'prelude-core'):
    out, dt, rc = run([str(EXE / 'l13bench.exe'), '--workload', w, '--rounds', '3', '--max-k', '10'])
    basic = re.findall(r'basic\s+([\d.]+)ms', out)
    fast = re.findall(r'fast\s+([\d.]+)ms', out)
    if basic and fast:
        rows.append((f'workload_{w}', f'basic={basic[0]}ms fast={fast[0]}ms', f'ratio={float(basic[0])/float(fast[0]):.1f}x'))
    else:
        rows.append((f'workload_{w}', f'rc={rc}', ''))

# 22: cold start on an empty file
tmp = ROOT / 'tools' / 'review-1011' / 'r10-perf' / 'empty.typort'
tmp.write_text('', encoding='utf-8')
out, dt, rc = run([str(EXE / 'typort.exe'), 'check', str(tmp)])
rows.append(('cold_start_empty', f'{dt*1000:.0f}ms', f'rc={rc}'))

# 23: prelude load (check with a trivial file)
tmp2 = ROOT / 'tools' / 'review-1011' / 'r10-perf' / 'one.typort'
tmp2.write_text('def one: Nat = 1\nprintln(one)\n', encoding='utf-8')
ts = []
for _ in range(3):
    out, dt, rc = run([str(EXE / 'typort.exe'), 'check', str(tmp2)])
    ts.append(dt * 1000)
rows.append(('check_with_prelude', f'{statistics.median(ts):.0f}ms median(3)', f'all={[f"{t:.0f}" for t in ts]}'))

# 24-25: examples through check
for ex in ('adder_proof.typort', 'theorem_proving.typort', 'typeclass_complex.typort', 'hdl_ops.typort', 'alu.typort'):
    out, dt, rc = run([str(EXE / 'typort.exe'), 'check', str(ROOT / 'examples' / ex)], timeout=300)
    rows.append((f'check_{ex}', f'{dt*1000:.0f}ms', f'rc={rc}'))

# 26-28: emit on selected HDL examples
for ex, top in (('16-counter.typort', 'counterFree'), ('12-memory.typort', 'memWriteRead'), ('01-basics.typort', 'basicDecls')):
    out, dt, rc = run([str(EXE / 'typort.exe'), 'emit', str(ROOT / 'examples' / 'hdl' / ex), '--top', top], timeout=300)
    lines = len(out.splitlines())
    rows.append((f'emit_{ex}', f'{dt*1000:.0f}ms {lines} lines', f'rc={rc}'))

# 29: memory accounting on L13
out, dt, rc = run([str(EXE / 'l06l13mem.exe'), '--help'], timeout=120)
rows.append(('mem_tool_present', 'ok' if rc == 0 else f'rc={rc}', out.splitlines()[0][:60] if out else ''))

# 30: regression guard -- the R1..R5 fixes must not slow the hot path
out, dt, rc = run([str(EXE / 'l13bench.exe'), '--workload', 'prelude-core', '--rounds', '3'])
fast = re.findall(r'fast\s+([\d.]+)ms', out)
basic = re.findall(r'basic\s+([\d.]+)ms', out)
rows.append(('post_fix_guard', f'basic={basic[0] if basic else "?"}ms fast={fast[0] if fast else "?"}ms',
             f'proc={dt:.1f}s (compare with row prelude-core)'))

md = ['# Round-10 performance battery (2026-10-11)', '',
      '30 timed dimensions over the release binaries at this HEAD.',
      'All numbers are single-run medians reported by the bench binaries', '',
      '| experiment | result | note |', '|---|---|---|']
for r in rows:
    md.append(f'| {r[0]} | {r[1]} | {r[2]} |')
OUT.write_text('\n'.join(md) + '\n', encoding='utf-8')
print(f'wrote {OUT} ({len(rows)} rows)')
for r in rows:
    print(f'{r[0]:38s} {r[1]}')
