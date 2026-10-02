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
