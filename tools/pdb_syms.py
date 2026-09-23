#!/usr/bin/env python3
# pdb_syms.py — 离线重符号化 sampler folded/self 报告里的 0x 文件VA 帧（纯
# python，零依赖，读 PDB 的 publics 流，不依赖 dbghelp）。
#
# 背景：本机 dbghelp 拒绝加载 rust release exe 的 PDB（SymType 恒为
# EXPORT，进程内 backtrace::resolve 与 tools/symbolize_l13.ps1 两条路都
# 只给 __ImageBase —— perf-l13-round-2026-09-22 §3.6 的悬案，本脚本绕开
# 它：直接解析 MSF 700 超级块 → 流目录 → DBI.public_stream → S_PUB32
# 记录，建 RVA→函数名最近邻表）。
#
# 用法:
#   python tools/pdb_syms.py <exe> <pdb> <folded...>     # 就地重写
# 0x token 视为「文件 VA = PE 首选 ImageBase + RVA」；解不出（exports/
# CRT 外部帧）保留 0x token。
import struct
import sys


def read_msf_streams(pdb):
    d = open(pdb, 'rb').read()
    assert d[:4] == b'Micr' or d[:24].startswith(b'Microsoft C/C++ MSF'), "not an MSF pdb"
    bs = struct.unpack_from('<I', d, 0x20)[0]
    assert bs in (512, 1024, 2048, 4096), f"bad block size {bs}"
    ndirbytes = struct.unpack_from('<I', d, 0x2c)[0]
    blockmap_addr = struct.unpack_from('<I', d, 0x34)[0]
    ndirblocks = (ndirbytes + bs - 1) // bs
    bm = struct.unpack_from('<%dI' % ndirblocks, d, blockmap_addr * bs)
    dirdata = b''.join(d[b * bs:(b + 1) * bs] for b in bm)[:ndirbytes]
    nstreams = struct.unpack_from('<I', dirdata, 0)[0]
    sizes = struct.unpack_from('<%dI' % nstreams, dirdata, 4)
    offp = 4 + 4 * nstreams
    streams = []
    for s in range(nstreams):
        n = (sizes[s] + bs - 1) // bs
        blocks = struct.unpack_from('<%dI' % n, dirdata, offp)
        offp += 4 * n
        streams.append(b''.join(d[b * bs:(b + 1) * bs] for b in blocks)[:sizes[s]] if sizes[s] != 0xFFFFFFFF else b'')
    return streams


def pub_symbols(pdb_streams):
    """从 DBI 头 @20 指的符号记录流（本机 PDB 实测：S_PUB32 都在这里）抽
    [(sect, off, flags, name)]。"""
    dbi = pdb_streams[3]
    rec_idx = struct.unpack_from('<H', dbi, 20)[0]
    if rec_idx >= len(pdb_streams):
        return []
    pub = pdb_streams[rec_idx]
    return (try_parse_publics(pub[0:]) or try_parse_publics(pub[16:])
            or try_parse_publics(pub[12:]) or try_parse_publics(pub[8:]))


PROC_KINDS = {0x110F, 0x1110, 0x1146, 0x1147}  # S_LPROC32 / S_GPROC32 / *_ID


def try_parse_procs(recs):
    out, i, n = [], 0, len(recs)
    bad = 0
    while i + 4 <= n:
        reclen = struct.unpack_from('<H', recs, i)[0]
        if reclen < 2 or i + 2 + reclen > n:
            # 失步重同步：记录流中混入 C13/杂段时逐字节找下一个可解析记录
            i += 1
            bad += 1
            if bad > 5_000_000:
                break
            continue
        bad = 0
        kind = struct.unpack_from('<H', recs, i + 2)[0]
        if kind in PROC_KINDS:
            # G/LPROC32: pParent(4) pEnd(8) pNext(12) len(16) dbgStart(20)
            # dbgEnd(24) typeIndex(28) off(32) sect(36) flags u8(38) name(39)
            off = struct.unpack_from('<I', recs, i + 32)[0]
            sect = struct.unpack_from('<H', recs, i + 36)[0]
            name = recs[i + 39:i + 2 + reclen].split(b'\0')[0].decode('utf-8', 'replace')
            out.append((sect, off, 0, name))
        elif kind == 0x110E:
            flags, off = struct.unpack_from('<II', recs, i + 4)
            sect = struct.unpack_from('<H', recs, i + 12)[0]
            name = recs[i + 14:i + 2 + reclen].split(b'\0')[0].decode('utf-8', 'replace')
            out.append((sect, off, flags, name))
        i += 2 + reclen
        i += _pad4(i)
    return out


def all_functions(pdb_streams):
    """DBI 模块表逐流抽函数符号（LTO 内部化后 publics 不含内核函数，
    模块流的 S_L/GPROC32 才是全集）。"""
    dbi = pdb_streams[3]
    mod_list_size = struct.unpack_from('<I', dbi, 28)[0]
    hdr = 68  # DbiStreamHeader（llvm 布局，含 Flags/Machine/Padding）
    out, p, end = [], hdr, hdr + mod_list_size
    nstreams = len(pdb_streams)
    while p + 64 <= end and p < len(dbi):
        imod = struct.unpack_from('<H', dbi, p + 8)[0]
        line_size = struct.unpack_from('<I', dbi, p + 12)[0]
        # 64 字节定长 + 模块名 + 对象名（NUL 结尾，4 对齐）
        nm_end = dbi.find(b'\0', p + 64)
        obj_end = dbi.find(b'\0', nm_end + 1)
        p = (obj_end + 1 + 3) & ~3
        if imod >= nstreams or imod == 0xFFFF:
            continue
        ms = pdb_streams[imod]
        out += try_parse_procs(ms[:line_size] if line_size and line_size <= len(ms) else ms)
    return out


def try_parse_publics(recs):
    out, i, n = [], 0, len(recs)
    while i + 4 <= n:
        reclen = struct.unpack_from('<H', recs, i)[0]
        if reclen < 2 or i + 2 + reclen > n:
            break  # 尾部/错位——返回已解析的部分
        kind = struct.unpack_from('<H', recs, i + 2)[0]
        if kind == 0x110E:  # S_PUB32
            flags, off = struct.unpack_from('<II', recs, i + 4)
            sect = struct.unpack_from('<H', recs, i + 12)[0]
            name = recs[i + 14:i + 2 + reclen].split(b'\0')[0].decode('utf-8', 'replace')
            out.append((sect, off, flags, name))
        i += 2 + reclen
        i += _pad4(i)
    return out


def _pad4(x):
    return (4 - x % 4) % 4


def exe_sections_and_base(exe):
    d = open(exe, 'rb').read()
    pe = struct.unpack_from('<I', d, 0x3c)[0]
    optsize = struct.unpack_from('<H', d, pe + 20)[0]
    opt = pe + 24
    magic = struct.unpack_from('<H', d, opt)[0]
    imgbase = struct.unpack_from('<Q', d, opt + 24)[0] if magic == 0x20b else struct.unpack_from('<I', d, opt + 28)[0]
    nsec = struct.unpack_from('<H', d, pe + 6)[0]
    so = opt + optsize
    secs = []
    for i in range(nsec):
        o = so + 40 * i
        vaddr, vsize = struct.unpack_from('<II', d, o + 12)
        secs.append((vaddr, max(vsize, 1)))
    return imgbase, secs


def scan_stream_procs(s):
    """逐字节模式扫描：S_INLINESITE 的二进制内联注记让顺序 walk 失步，
    这里对每个位置做严格校验（kind + off/sect 合法 + 名字在 reclen 内
    NUL 结尾 + 可打印），命中即收集。"""
    out, n = [], len(s)
    kinds = PROC_KINDS | {0x110E}
    i = 0
    while i + 44 <= n:
        kind = struct.unpack_from('<H', s, i + 2)[0]
        if kind in kinds:
            reclen = struct.unpack_from('<H', s, i)[0]
            if kind == 0x110E:
                off = struct.unpack_from('<I', s, i + 8)[0]
                sect = struct.unpack_from('<H', s, i + 12)[0]
                nstart = i + 14
            else:
                off = struct.unpack_from('<I', s, i + 32)[0]
                sect = struct.unpack_from('<H', s, i + 36)[0]
                nstart = i + 39
            if 1 <= sect <= 8 and off < 0x400000:
                nul = s.find(b'\0', nstart, min(i + 2 + reclen, n))
                if 0 < nul - nstart < 2000:
                    nm = s[nstart:nul].decode('utf-8', 'replace')
                    if all(32 <= ord(c) < 127 for c in nm[:48]):
                        out.append((sect, off, 0, nm))
                        i = nul
                        continue
        i += 1
    return out


def scan_all_streams(pdb_streams):
    """逐流 + 起始偏移 {0,4,8} 暴力解析 proc/pub 记录，每流取最优。
    （DBI 模块表布局在 lld 生成的 PDB 里字段漂移不定，暴力扫描反而稳。）"""
    best = {}
    for i, s in enumerate(pdb_streams):
        if not s or len(s) < 64:
            continue
        recs = scan_stream_procs(s)
        if recs:
            best[i] = recs
    out = []
    for recs in best.values():
        out += recs
    return out


def main():
    exe, pdb, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    imgbase, secs = exe_sections_and_base(exe)
    streams = read_msf_streams(pdb)
    syms_raw = scan_all_streams(streams) or pub_symbols(streams)

    def sect_rva(sect, off):
        if 1 <= sect <= len(secs):
            return secs[sect - 1][0] + off
        return None

    table = []
    for sect, off, flags, name in syms_raw:
        rva = sect_rva(sect, off)
        if rva is not None:
            table.append((rva, name))
    table.sort()
    if not table:
        print("pdb_syms: publics 空 — PDB 无公开符号?", file=sys.stderr)
        sys.exit(1)
    rv = [t[0] for t in table]
    print(f"pdb_syms: {len(table)} publics, imagebase={imgbase:#x}")

    import bisect
    cache = {}

    def resolve(va):
        if va in cache:
            return cache[va]
        rva = va - imgbase
        i = bisect.bisect_right(rv, rva) - 1
        nm = None
        if i >= 0:
            base_rva, base_nm = table[i]
            if rva - base_rva < 0x100000:  # 限最近符号段内距离（防越节错配）
                nm = base_nm
        cache[va] = nm
        return nm

    for f in files:
        lines = open(f, encoding='utf-8', errors='replace').read().splitlines()
        out, ntok, nsym = [], 0, 0
        for line in lines:
            if line.startswith('#') or not line.strip():
                out.append(line)
                continue
            parts = line.split(' ', 1)
            if len(parts) < 2:
                out.append(line)
                continue
            frames = parts[0].split(';')
            for k, fr in enumerate(frames):
                if fr.startswith('0x'):
                    try:
                        va = int(fr, 16)
                    except ValueError:
                        continue
                    ntok += 1
                    nm = resolve(va)
                    if nm:
                        frames[k] = nm.replace(';', '_')
                        nsym += 1
            out.append(';'.join(frames) + ' ' + parts[1])
        open(f, 'w', encoding='utf-8').write('\n'.join(out) + '\n')
        print(f"  {f}: tokens={ntok} resolved={nsym}")


if __name__ == '__main__':
    main()
