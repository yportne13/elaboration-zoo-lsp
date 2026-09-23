#!/bin/bash
# attr_l13.sh — L13 孪生（bump_spine_iter）采样归因一条龙：跑采样 → 出 self% Top。
#
# 用法:
#   bash tools/attr_l13.sh <workload> [--max-k N] [--rounds N] [--only fast]
#                          [--out DIR] [--no-build] [--no-build-check]
# 例:
#   bash tools/attr_l13.sh prelude-hdl --rounds 3
#   bash tools/attr_l13.sh church --max-k 13 --rounds 5
#
# 做什么:
#   1) 用独立 CARGO_TARGET_DIR=target_opt_S6 构建 sampler 版 l13bench
#      （--features sampler；不碰根 target/）。
#   2) 在临时目录里以 L13SAMPLE=1 跑 l13bench（采样输出落在 <tmp>/target/
#      bench_out/，不写仓库根 target/）。
#   3) 打印三张 Top 表（self% / 时间加权链 / 频度×链）+ trait_wrap /
#      probe_accessible 两个归因焦点在时间加权口径里的份额。
#
# 口径说明（src/sampler.rs 头注释）:
#   *.self.txt / *.self.folded —— tick 间区间归因到最内层 tick 点（self%）。
#   *.time.folded              —— 两次栈捕获之间的墙钟记到捕获链（时间加权链）。
#   *.folded                   —— 旧口径：入口频度 × 调用链。
# 环境变量: L13SAMPLE_TICK=n（栈捕获节奏，默认 200）、L13SAMPLE_NOTS=1（关时间戳）。
set -u
cd "$(dirname "$0")/.." || exit 1
ROOT="$PWD"

WORKLOAD="${1:-prelude-hdl}"; shift || true
MAXK=""; ROUNDS="--rounds 5"; ONLY="--only fast"; OUTDIR=""; DO_BUILD=1; BUILD_CHECK=1
while [ $# -gt 0 ]; do
    case "$1" in
        --max-k) MAXK="--max-k $2"; shift 2;;
        --rounds) ROUNDS="--rounds $2"; shift 2;;
        --only) ONLY="--only $2"; shift 2;;
        --out) OUTDIR="$2"; shift 2;;
        --no-build) DO_BUILD=0; shift;;
        --no-build-check) BUILD_CHECK=0; shift;;
        *) echo "unknown arg: $1"; exit 1;;
    esac
done

EXE="target_opt_S6/l13bench.exe"
if [ "$DO_BUILD" = 1 ]; then
    echo ">> building sampler l13bench into target_opt_S6 (log: target_opt_S6/build_attr.log)"
    export CARGO_TARGET_DIR="$PWD/target_opt_S6"
    # 完整符号 PDB 三件套（缺一不可，2026-09-23 S6 实测）：
    #   /DEBUG:FULL —— 默认 /DEBUG 出的是 thin pdb（无用户函数名）；
    #   -C debuginfo=1 —— debuginfo=0 时对象里没有 CodeView，LTO 内部化的
    #                     内核函数在哪儿都不会再出现；
    #   rust-lld —— 本机 link.exe 的 pdb dbghelp 拒载（SymType 恒 EXPORT），
    #               lld 出的 pdb 由 tools/pdb_syms.py 直接解析，绕开 dbghelp。
    export RUSTFLAGS="-C linker=C:/Users/40668/.rustup/toolchains/1.98.1-x86_64-pc-windows-msvc/lib/rustlib/x86_64-pc-windows-msvc/bin/rust-lld.exe -C linker-flavor=lld-link -C link-arg=/DEBUG:FULL -C debuginfo=1"
    mkdir -p target_opt_S6
    cargo build --release --bin l13bench --features sampler > target_opt_S6/build_attr.log 2>&1
    rc=$?
    tail -3 target_opt_S6/build_attr.log
    [ $rc -ne 0 ] && { echo "BUILD FAILED (rc=$rc)"; exit $rc; }
elif [ ! -x "$EXE" ]; then
    echo "$EXE missing — drop --no-build or run: RUSTFLAGS='-C link-arg=/DEBUG:FULL' CARGO_TARGET_DIR=\$PWD/target_opt_S6 cargo build --release --bin l13bench --features sampler"
    exit 1
fi

# 采样构建自检：旧基线 release 构建没编 sampler（L13SAMPLE 是死开关），先验真。
if [ "$BUILD_CHECK" = 1 ]; then
    grep -aq L13SAMPLE "$EXE" || { echo "FATAL: $EXE 不含 sampler（L13SAMPLE 字符串缺失）"; exit 1; }
fi

RUNDIR="${OUTDIR:-$(mktemp -d)}"
mkdir -p "$RUNDIR"
echo ">> run dir: $RUNDIR"
echo ">> L13SAMPLE=1 L13SAMPLE_TICK=${L13SAMPLE_TICK:-200} $EXE --workload $WORKLOAD $MAXK $ROUNDS $ONLY"
cd "$RUNDIR" || exit 1
L13SAMPLE=1 "$ROOT/$EXE" --workload "$WORKLOAD" $MAXK $ROUNDS $ONLY
rc=$?
cd "$ROOT" || exit 1
[ $rc -ne 0 ] && { echo "RUN FAILED (rc=$rc)"; exit $rc; }

B="$RUNDIR/target/bench_out"
F="$B/l13_fast.folded"
for f in "$F" "$F.self.txt" "$F.time.folded"; do
    [ -f "$f" ] || { echo "missing: $f"; exit 1; }
done

# 离线重符号化：release exe 进程内 dbghelp 只给 __ImageBase（本机 PDB 加载
# 恒为 EXPORT——连最小 rustc 构建都如此，机器级问题），sampler 落 0x 文件VA，
# 这里用 pdb_syms.py 直接解析 /DEBUG:FULL PDB 的函数符号表换回函数名。
EXE_ABS="$(cd "$(dirname "$EXE")" && pwd)/$(basename "$EXE")"
PDB="${EXE_ABS%.exe}.pdb"
if [ -f "$PDB" ] && command -v python >/dev/null 2>&1; then
    python "$ROOT/tools/pdb_syms.py" "$EXE_ABS" "$PDB" "$F" "$F.time.folded" \
        || echo "(offline symbolize failed — 帧保留 0x token)"
else
    echo "(no full pdb or python — 帧保留 0x token; 用 RUSTFLAGS='-C link-arg=/DEBUG:FULL' 构建)"
fi

echo ""
echo "======== self% Top (tick 区间归因, src/sampler.rs) ========"
cat "$F.self.txt"

echo ""
echo "======== 时间加权链 Top 15 (两次捕获间墙钟 → 捕获链) ========"
echo "======== 频度×链 Top 15 (旧口径: 入口频度) ========"
echo "======== 归因焦点份额 (时间加权链口径, 链内任意帧命中) ========"
# 注意：符号化后的帧名可能含空格，权重一律取最后一个字段（rsplit 最后一个空格）。
python - "$F" <<'PYEOF'
import sys

def load(p):
    rows = []
    for line in open(p, encoding='utf-8', errors='replace'):
        line = line.rstrip('\n')
        if not line or line.startswith('#'):
            continue
        sp = line.rsplit(' ', 1)
        if len(sp) == 2:
            rows.append((sp[0], int(sp[1])))
    return rows

time_rows = load(sys.argv[1] + '.time.folded')
freq_rows = load(sys.argv[1])
tt = sum(w for _, w in time_rows) or 1
tf = sum(w for _, w in freq_rows) or 1

print('---- 时间加权链 Top 15 ----')
for chain, w in sorted(time_rows, key=lambda x: -x[1])[:15]:
    print(f'{w/1e6:10.1f}ms  {w/tt*100:6.2f}%  ...{chain[-190:]}')
print()
print('---- 频度×链 Top 15 ----')
for chain, w in sorted(freq_rows, key=lambda x: -x[1])[:15]:
    print(f'{w:10d}    {w/tf*100:6.2f}%  ...{chain[-190:]}')
print()
print('---- 归因焦点份额 (时间加权, 链内任意帧命中) ----')
for pat in ('trait_wrap', 'probe_accessible', 'solve_trait'):
    s = sum(w for chain, w in time_rows if pat in chain)
    print(f'{pat:20s} {s/1e6:8.1f} ms  {s/tt*100:5.2f}%')
PYEOF
echo ""
echo "artifacts in: $B"
