#!/usr/bin/env bash
# tools/gate_l13.sh — L13 提交前快速门禁三件套（lib + parity 本体 + into_probe）。
#
# 用法：
#   bash tools/gate_l13.sh                                  # 快速口径（日常改 L13 后跑这个）
#   CARGO_TARGET_DIR="$PWD/target_gate" bash tools/gate_l13.sh  # CARGO_TARGET_DIR 原样透传给 cargo（日志也落在该目录下）
#   GATE_FULL=1 bash tools/gate_l13.sh                      # 全量口径（parity/into 不 skip）
#   bash tools/gate_l13.sh --release --quiet                # 其余位置参数原样追加到每次 cargo test
#                                                           #（常用 flag，如 --release 避开 dev-profile
#                                                           # fat-LTO 重链悬崖，见 docs §3.4）
#
# 为什么 parity/into 两件要 --skip "L13_namespace::"（skip 配方，无覆盖损失）：
#   tests/l13_fast_parity.rs 与 tests/l13_into_probe.rs 都用
#   `#[path = "../src/L13_namespace/mod.rs"] mod L13_namespace;` 把整个 L13
#   以 cfg(test) 再编译进各自的测试二进制，于是 lib 的 409 个测试在每个
#   二进制里各重复执行一遍：
#     l13_fast_parity   423 = 409 重复 + 14 本体
#     l13_into_probe    410 = 409 重复 +  1 本体
#   实测（round-2026-09-22，docs §3.4）重复执行占门禁墙钟 ~44%。
#   --skip "L13_namespace::" 滤掉的 409 个在第一件套 `--lib L13_namespace::`
#   里恰好跑过一次，所以只是去掉重复，不丢任何断言。
#
# 什么时候该跑全量（GATE_FULL=1，即不 skip 的 parity）：
#   - 改了 parity 判据/归一化本身（tests/l13_fast_parity.rs、l13_into_probe.rs）；
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
    echo "== GATE_FULL=1: 全量口径（parity/into 不 skip）"
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

run_suite() {
    local name="$1" t0; shift
    t0=$SECONDS
    echo "==> [$name] $*"
    if "$@" >"$LOGDIR/$name.log" 2>&1; then
        grep "^test result" "$LOGDIR/$name.log" | sed 's/^/    /'
        echo "    [$name ok: $((SECONDS - t0))s]"
    else
        echo "    [$name FAILED — 完整输出: $LOGDIR/$name.log]"
        grep -E "^error|FAILED|panicked at" "$LOGDIR/$name.log" | head -20 | sed 's/^/    /'
        fail=1
    fi
}

run_suite lib        cargo test --lib L13_namespace:: "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}"
run_suite parity     cargo test --test l13_fast_parity "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}" -- "${SKIP_ARGS[@]+"${SKIP_ARGS[@]}"}"
run_suite into_probe cargo test --test l13_into_probe "${EXTRA_ARGS[@]+"${EXTRA_ARGS[@]}"}" -- "${SKIP_ARGS[@]+"${SKIP_ARGS[@]}"}"

echo "== gate_l13: total $((SECONDS - t_all))s, fail=$fail, logs: $LOGDIR"
exit "$fail"
