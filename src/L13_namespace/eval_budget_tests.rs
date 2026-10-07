// ============================================================
// 求值预算（看门狗）测试
//
// 引擎没有终止性检查（docs/l13-quirks-analysis-2026-10.md §4）：被求值的
// 循环定义会让迭代 eval 静默自旋。eval_budget 在两版引擎的 eval 主循环
// 每 2^20 次迭代做 checkpoint，超 deadline panic_any(ElabTimeout)；这里钉：
// ①参考版/孪生的循环定义在预算内被中止（而非永久挂死）；②正常文件在
// 预算下不受影响；③作用域恢复（嵌套/退出后无残留 deadline）。
// 所有超时用例都先设预算再 catch_unwind——失败模式是断言失败而非挂死。
// ============================================================

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

/// 会挂死的输入：`bad` 自递归，`bad2` 触发对 `bad 5` 的求值（登记期整求）。
const LOOPING: &str = "def bad(x: Nat): Nat = bad x\ndef bad2: Nat = bad 5\n";

#[test]
fn reference_eval_budget_aborts_loop() {
    let t0 = std::time::Instant::now();
    let _g = eval_budget::scope(300);
    let r = catch_unwind(AssertUnwindSafe(|| run_with_prelude(LOOPING)));
    match r {
        Err(p) => assert!(
            eval_budget::is_timeout(p.as_ref()),
            "expected ElabTimeout payload"
        ),
        Ok(_) => panic!("expected budget timeout, but run completed"),
    }
    assert!(
        t0.elapsed().as_secs() < 10,
        "abort took far longer than the budget"
    );
}

#[test]
fn budget_does_not_fire_on_normal_file() {
    let _g = eval_budget::scope(60_000);
    let out = run_with_prelude("def x: Nat = succ zero\nprintln x").unwrap();
    assert!(out.contains("1"), "normal output missing: {}", out);
}

#[test]
fn twin_eval_budget_aborts_loop() {
    // 直连孪生 observe_user：core-only prelude prime 后注入循环 decl，
    // 预算内应得到 ElabTimeout 而非挂死（与 lib.rs twin_elaborate 的
    // catch 点同 payload）。
    let parsed = parse_prelude_files(PRELUDE_CORE);
    assert!(parsed.failed.is_none(), "core prelude parse failed");
    let mut t = bump_spine_iter::Tycker::new();
    t.prime_resident(&parsed)
        .expect("prime_resident failed");
    let (decls, errs) = match parser::parser_with_macros(&preprocess(LOOPING), 24, &Default::default())
    {
        Some((d, e, _, _)) => (d, e),
        None => panic!("parse failed"),
    };
    assert!(errs.is_empty(), "unexpected parse errors: {:?}", errs.len());
    let t0 = std::time::Instant::now();
    let _g = eval_budget::scope(300);
    let r = catch_unwind(AssertUnwindSafe(|| t.observe_user(&parsed, &decls)));
    match r {
        Err(p) => assert!(
            eval_budget::is_timeout(p.as_ref()),
            "expected ElabTimeout payload"
        ),
        Ok(_) => panic!("expected budget timeout, but observe completed"),
    }
    assert!(
        t0.elapsed().as_secs() < 10,
        "abort took far longer than the budget"
    );
}

#[test]
fn scope_restores_after_drop() {
    // 退出作用域后 deadline 恢复为 None（后续未设预算的求值不受限）；
    // 嵌套 scope 取较早者（内层先到期）。
    {
        let _outer = eval_budget::scope(60_000);
        {
            let _inner = eval_budget::scope(60_000);
        }
        // 内层退出后外层 deadline 仍在（对正常求值不触发即可）
        let out = run_with_prelude("def x: Nat = 1 + 2\nprintln x").unwrap();
        assert!(out.contains("3"));
    }
    // 外层也退出：正常路径再跑一遍（无预算路径不被污染）
    let out = run_with_prelude("def y: Nat = 2 + 2\nprintln y").unwrap();
    assert!(out.contains("4"));
}

/// 孪生大数显示的内存护栏钉（R4 孪生侧待接线，tests/bignum_display.rs
/// 文件头）：`println (nat_mul 100000 100000)` 的 k = 10^10，孪生显示位
/// `quote` 会把原生 Nat 展开成 10^10 节点 succ 链——**裸循环、链内无
/// checkpoint**，时间预算拦不住。
///
/// 2026-10-07 实锤：本测试（当时叫 …_pending_watchdog_catches）在 lib 套件
/// 里把进程提交量顶到 121.8 GB（Windows 事件 2004），系统级虚拟内存耗尽、
/// 主机非正常重启——**跑一次全量 lib 套件就复现一次**。
///
/// 现在第一道防线是 `eval_budget::guard_nat_chain`（超 `NAT_CHAIN_LIMIT`
/// 立即中止、不开始分配），时间预算只是第二道。故本钉改判：
/// 1. 中止 payload 必须是 `NatChainOverflow`（护栏），**不是** ElabTimeout；
/// 2. 预算故意给到 60s（宽到时间超时不可能解释这次中止）——证明护栏与
///    预算无关、无条件生效；
/// 3. 中止必须是即时的（远小于 10s），即真的没展开。
/// 孪生显示压缩（Machine::quote_dec 接线 + succ-折叠对齐）落地后，本钉
/// 应改判 observe 正常返回且 println note 为十进制。
#[test]
fn twin_big_nat_display_aborts_via_chain_guard() {
    let parsed = parse_prelude_files(PRELUDE_CORE);
    let mut t = bump_spine_iter::Tycker::new();
    t.prime_resident(&parsed).expect("prime_resident failed");
    let (decls, errs) = match parser::parser_with_macros(
        &preprocess("println (nat_mul 100000 100000)\n"),
        24,
        &Default::default(),
    ) {
        Some((d, e, _, _)) => (d, e),
        None => panic!("parse failed"),
    };
    assert!(errs.is_empty());
    let t0 = std::time::Instant::now();
    // 宽预算：时间维度不可能在这次中止里起作用（见 doc 注释第 2 点）
    let _g = eval_budget::scope(60_000);
    let r = catch_unwind(AssertUnwindSafe(|| t.observe_user(&parsed, &decls)));
    match r {
        Err(p) => {
            let ov = p
                .downcast_ref::<eval_budget::NatChainOverflow>()
                .expect("expected NatChainOverflow (memory guard), not a time-based abort");
            assert_eq!(ov.k, 100_000 * 100_000, "guard must see the real k");
            assert_eq!(ov.limit, eval_budget::NAT_CHAIN_LIMIT);
            assert!(
                eval_budget::is_timeout(p.as_ref()),
                "边界口径：与 ElabTimeout 同族（LSP 据此回落参考版）"
            );
        }
        Ok(res) => panic!(
            "expected NatChainOverflow (twin big-nat display still expands), got Ok={:?}",
            res.is_ok()
        ),
    }
    assert!(
        t0.elapsed().as_secs() < 10,
        "guard must abort immediately, not expand (elapsed {:?})",
        t0.elapsed()
    );
}

/// 护栏边界钉（无引擎、纯判定）：界内一律放行（正常规模 Nat 完全不受
/// 影响），超界立即抛 [`eval_budget::NatChainOverflow`] 且归属"主动中止"
/// 族——这是"内存安全不依赖调用方是否设了时间预算"的最小证据。
#[test]
fn nat_chain_guard_boundary() {
    // 界内（含恰好等于上限）：不得中止
    catch_unwind(|| eval_budget::guard_nat_chain(0)).expect("k=0 must pass");
    catch_unwind(|| eval_budget::guard_nat_chain(1_000_000)).expect("k=1e6 must pass");
    catch_unwind(|| eval_budget::guard_nat_chain(eval_budget::NAT_CHAIN_LIMIT))
        .expect("k=limit must pass");
    // 超界：立即抛，payload 精确
    let p = catch_unwind(|| eval_budget::guard_nat_chain(eval_budget::NAT_CHAIN_LIMIT + 1))
        .expect_err("k=limit+1 must abort before allocating");
    let ov = p
        .downcast_ref::<eval_budget::NatChainOverflow>()
        .expect("payload must be NatChainOverflow");
    assert_eq!(ov.k, eval_budget::NAT_CHAIN_LIMIT + 1);
    assert_eq!(ov.limit, eval_budget::NAT_CHAIN_LIMIT);
    assert!(
        eval_budget::is_timeout(p.as_ref()),
        "NatChainOverflow must be in the is_timeout family"
    );
}
