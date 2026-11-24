#!/usr/bin/env bash
# tools/gate_l13.sh — L13 提交前门禁三件套（lib + parity 本体 + 孪生 LSP 接线）。
#
# 用法：
#   bash tools/gate_l13.sh                                  # 快速口径（日常改 L13 后跑这个）
#   CARGO_TARGET_DIR="$PWD/target_gate" bash tools/gate_l13.sh  # CARGO_TARGET_DIR 原样透传给 cargo（日志也落在该目录下）
#   GATE_FULL=1 bash tools/gate_l13.sh                      # 全量口径（parity 不 skip）
#   GATE_NO_TWIN_LSP=1 bash tools/gate_l13.sh               # 跳过第三件（孪生 LSP 接线，约 80s）
#   bash tools/gate_l13.sh --release --quiet                # 其余位置参数原样追加到每次 cargo test
#                                                           #（常用 flag，如 --release 避开 dev-profile
#                                                           # fat-LTO 重链悬崖，见 docs §3.4）
#
# 第三件（2026-09-23 补）：`tests/twin_engine_tests.rs` —— 孪生 LSP 接线的
#   唯一执行渠道。此前它**不在门禁内**，只有手动全量 `cargo test` 才跑，于是
#   "孪生接管 / 回落类别 / 诊断与警告 parity" 这些最贴近用户的行为没有提交前
#   保障（它一跑 ~80s：每个 examples 文件新建两个 Backend 并各自 prime HDL
#   prelude）。急用时可用 GATE_NO_TWIN_LSP=1 跳过，但别在改动 LSP 接线时跳。
#
# 为什么 parity 件要 --skip "L13_namespace::"（skip 配方，无覆盖损失）：
#   tests/l13_fast_parity.rs 用
#   `#[path = "../src/L13_namespace/mod.rs"] mod L13_namespace;` 把整个 L13
#   以 cfg(test) 再编译进测试二进制，于是 lib 的 411 个测试在
#   该二进制里重复执行一遍：
#     l13_fast_parity   426 = 411 重复 + 15 本体
#   实测（round-2026-09-22，docs §3.4）重复执行占门禁墙钟 ~44%。
#   --skip "L13_namespace::" 滤掉的 411 个在第一件套 `--lib L13_namespace::`
#   里恰好跑过一次，所以只是去掉重复，不丢任何断言。
#   （原 l13_into_probe 件已于 5f6dc82 收编进 l13_fast_parity.rs 后删除，
#   其唯一探针断言 parity_into_add_nat_uint_field_projection 由 parity
#   套件覆盖，不再单列。）
#
# 什么时候该跑全量（GATE_FULL=1，即不 skip 的 parity）：
#   - 改了 parity 判据/归一化本身（tests/l13_fast_parity.rs）；
#   - 改了 L13 与 LSP/L02-L12 共享的底层（parser_lib、list、bimap 等
#     #[path] 链上的文件）后做整轮回归；
#   - 发布前收官。日常 lib-only 的 L13 改动用快速口径即可。
#
# 小写过滤器陷阱：`cargo test --lib l13`（小写）静默跑 0 个测试——测试
#   过滤器区分大小写，lib 测试路径全部形如 `L13_namespace::...`。手敲命令
#   务必写 `L13_namespace`；本脚本统一用大写，这也是 skip 过滤器能生效的原因。
#
# 注意：`--skip` 是 libtest（测试主程序）的参数而非 cargo 参数，必须放在
#   `--` 之后：`cargo test --test l13_fast_parity -- --skip "L13_namespace::"`。
#   直接写 `cargo test --test ... --skip ...` 会报 `unexpected argument`。
#   （skip 配方生效的前提是过滤器大小写一致，见下文小写过滤器陷阱。）
#
# 慢测试说明：`module_probe_tests::probe_timing`（3.9-5.3s，且向工作目录写
#   probe-out.txt）已按 docs §3.4 加 `#[ignore]`，不进任何口径；显式跑法：
#   cargo test --lib probe_timing -- --ignored --nocapture
set -u
cd "$(dirname "$0")/.." || exit 1

SKIP_ARGS=(--skip "L13_namespace::")
if [ "${GATE_FULL:-0}" = "1" ]; then
    SKIP_ARGS=()
    echo "== GATE_FULL=1: 全量口径（parity 不 skip）"
fi
EXTRA_ARGS=("$@")   # 透传给每次 cargo test 的附加 cargo 层 flag（如 --release --quiet，位于 `--` 之前）
if [ ${#EXTRA_ARGS[@]} -gt 0 ]; then
    echo "== 额外 cargo 参数: ${EXTRA_ARGS[*]}"
fi

LOGDIR="${CARGO_TARGET_DIR:-$PWD/target}"
LOGDIR="$LOGDIR/gate_l13_logs"
mkdir -p "$LOGDIR"

fail=0
t_all=$SECONDS

# 每套件例数下限（与 tools/gate_l13.ps1 的 -MinLib/-MinParity/-MinTwin/
# -MinHdl042 对齐）。被 feature 门关掉的套件会编译成**空 crate**，此时
# `test result: ok. 0 passed` 依旧 exit 0 —— 2026-11-24 孪生硬封印
# （Cargo.toml 的 l06-twin..l13-twin，默认全关）之后这一点尤其致命：
# l13_fast_parity 首行是 `#![cfg(feature = "l13-twin")]`，不带 feature 就是空跑。
MIN_LIB="${GATE_MIN_LIB:-500}"
MIN_PARITY="${GATE_MIN_PARITY:-15}"
MIN_TWIN="${GATE_MIN_TWIN:-27}"
MIN_HDL042="${GATE_MIN_HDL042:-2}"

run_suite() {
    local name="$1" min="$2" t0 line passed; shift 2
    t0=$SECONDS
    echo "==> [$name] $*"
    if "$@" >"$LOGDIR/$name.log" 2>&1; then
        line=$(grep "^test result" "$LOGDIR/$name.log" | head -1)
        echo "    $line"
        passed=$(printf '%s' "$line" | sed -n 's/.* \([0-9][0-9]*\) passed.*/\1/p')
        if [ -z "$passed" ]; then
            echo "    [$name FAILED — 日志里找不到 'test result' 行: $LOGDIR/$name.log]"
            fail=1
        elif [ "$passed" -lt "$min" ]; then
            echo "    [$name TOO FEW — $passed < $min（套件被 feature 门关成空 crate 了？）]"
            fail=1
        else
            echo "    [$name ok: $((SECONDS - t0))s]"
        fi
    else
        echo "    [$name FAILED — 完整输出: $LOGDIR/$name.log]"
        grep -E "^error|FAILED|panicked at" "$LOGDIR/$name.log" | head -20 | sed 's/^/    /'
        fail=1
    fi
}

run_suite lib        "$MIN_LIB"    cargo test --lib L13_namespace:: "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}"
# parity 必须显式带 --features l13-twin：该 target 首行是
# `#![cfg(feature = "l13-twin")]`，不带 feature 会编译成空 crate 而依旧
# "ok. 0 passed"（封印后曾长期"绿而空"）。
run_suite parity     "$MIN_PARITY"  cargo test --test l13_fast_parity --features l13-twin "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}" -- "${SKIP_ARGS[@]+"${SKIP_ARGS[@]}"}"
# 第三件不带 --skip：twin_engine_tests 没有 #[path] 再编译 L13，不存在重复面。
if [ "${GATE_NO_TWIN_LSP:-0}" = "1" ]; then
    echo "== GATE_NO_TWIN_LSP=1: 跳过 twin_lsp 件套（孪生 LSP 接线本次无保障）"
else
    run_suite twin_lsp   "$MIN_TWIN"   cargo test --test twin_engine_tests "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}"
fi
# 第四件（2026-09-30 评审补）：HDL042 的**双引擎**钉子。它必须放集成 target：
# `src/L13_namespace/**` 下的测试文件会被上面 parity 件的
# `#[path = "../src/L13_namespace/mod.rs"]` 二次编译，那里 `crate` 是测试二进制根，
# 没有 `Backend`/`Engine`/`client`（源码侧的参考版口径测试仍在 `--lib` 的
# `hdl_check_graph_tests.rs` 里跑）。放在这里是因为 auto-discovery 只保证全量
# `cargo test` 会跑到它，而本门禁只显式列件套。
run_suite hdl042     "$MIN_HDL042" cargo test --test hdl042_engine_tests "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}"

echo "== gate_l13: total $((SECONDS - t_all))s, fail=$fail, logs: $LOGDIR"
exit "$fail"
