// ============================================================
// Level A 终止性检查测试（docs/l13-quirks-analysis-2026-10.md §4.3 档 A）
//
// 判据：def 体检查通过后、wrap_match_in_call 前，每个自调用
// `f a1..an` 至少一个实参是「结构位置模式变量」——scrutinee 链（Var /
// `x.field`）下落到 def 参数的 match 的模式变量，链可经模式变量传递；实
// 参允许构造器包裹（ofNat b / negSucc a）。参数本身**不算**递减证据
// （`bad x` 拒）；零参 / 裸自引用拒；let 计算值与函数应用实参拒（nat_div/
// combReach/gcd 因此进引擎侧 allowlist）。
// 本文件钉住的已知放行（Level A 是止损守卫，不健全）：
// - ping-pong 换参 `weird b k`：k 是模式变量即放行；
// - 构造器包裹可增 `bad (succ k)`（eval_budget_tests 的 LOOPING 靠它
//   保留真循环供看门狗测试）；
// - 方法自递归经 `t.lenOf` Obj 派发，头不是 Decl-spine，不在判定内。
// 双引擎：负例参考 / 孪生各自断言文案；正例参考版断值 + 孪生对拍
// （cong_projection_tests 的 assert_twin_matches_reference 口径）。
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

fn assert_err_contains(input: &str, needle: &str) {
    match run_with_prelude(input) {
        Ok(output) => panic!("expected error containing '{}', got OK: {}", needle, output.trim()),
        Err(e) => {
            assert!(
                e.0.data.contains(needle),
                "expected error containing '{}', got: '{}'",
                needle,
                e.0.data
            );
        }
    }
}

fn assert_output(input: &str, expected: &[&str]) {
    let output = assert_ok(input);
    let lines: Vec<&str> = output
        .lines()
        .map(str::trim_end)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(lines, expected, "program output mismatch; raw: {:?}", output);
}

const TERM_MSG: &str = "cannot prove termination of recursive call to";

/// 在 512MB 栈的独立线程里跑测试体（孪生走图递归深度超出测试线程默认栈，
/// cong_projection_tests 同款）。
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    match std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .expect("spawn big-stack test thread")
        .join()
    {
        Ok(v) => v,
        Err(e) => std::panic::resume_unwind(e),
    }
}

/// 核心 prelude 文件序列（含 show——两版加载器恒排最后）。
fn core_files() -> Vec<(&'static str, &'static str)> {
    let mut v: Vec<(&'static str, &'static str)> = PRELUDE_CORE.to_vec();
    v.push(PRELUDE_SHOW);
    v
}

/// 孪生侧负例：run_decls_with_prelude 首错即返（step_round_decl 的 `?`），
/// 断言错误文案。
fn twin_err_contains(user_src: &str, needle: &str) {
    let user_src = user_src.to_string();
    let needle = needle.to_string();
    with_big_stack(move || {
        let files = core_files();
        let pre = parse_prelude_files(&files);
        assert_eq!(pre.failed, None, "prelude files must parse");
        let (user_decls, _errs, _exports, _expansions) = parser::parser_with_macros(
            &preprocess(&user_src),
            24,
            &pre.macros,
        )
        .expect("user parse");
        let mut t = bump_spine_iter::Tycker::new();
        match t.run_decls_with_prelude(&pre, &user_decls) {
            Ok(o) => panic!("twin expected error containing '{needle}', got OK: {o}"),
            Err(e) => assert!(
                e.0.data.contains(&needle),
                "twin expected error containing '{needle}', got: '{}'",
                e.0.data
            ),
        }
    });
}

/// 双引擎各跑一遍「core prelude + 用户源」，断言两版 Ok 且输出一致
/// （cong_projection_tests 同款收敛版）。
fn assert_twin_matches_reference(user_src: &str, path_id: u32) {
    let user_src = user_src.to_string();
    with_big_stack(move || {
        let files = core_files();
        let pre = parse_prelude_files(&files);
        assert_eq!(pre.failed, None, "prelude files must parse");
        let (user_decls, _errs, _exports, _expansions) = parser::parser_with_macros(
            &preprocess(&user_src),
            path_id,
            &pre.macros,
        )
        .expect("user parse");

        // twin
        let mut t = bump_spine_iter::Tycker::new();
        let t_out = t
            .run_decls_with_prelude(&pre, &user_decls)
            .expect("twin prelude round");

        // reference
        let (mut infer, mut rcxt, _macros) = clone_prelude_state(false).expect("reference prelude load");
        let mut r_out = String::new();
        for d in &user_decls {
            let (x, _, nc) = infer.infer(&rcxt, d.clone()).expect("ref user decl");
            rcxt = nc;
            if let DeclTm::Println(_, s, _) = x {
                r_out += &s;
                r_out += "\n";
            }
        }
        assert_eq!(t_out, r_out, "twin/reference output mismatch");
    });
}

// ── 负例：拒绝形态 ──

/// 实参是参数而非模式变量（无 match）：`bad x` 的 x 直接回传。
#[test]
fn rejects_direct_self_call_with_param_arg() {
    assert_err_contains("def bad(x: Nat): Nat = bad x", TERM_MSG);
}

/// 零参循环证明：`def p: Eq 1 2 = p`（R1 两行触发假定理的入口）。
#[test]
fn rejects_cyclic_proof() {
    assert_err_contains("def p: Eq 1 2 = p", TERM_MSG);
    twin_err_contains("def p: Eq 1 2 = p", TERM_MSG);
}

/// 计算值实参：`cs (nat_add k k)`——函数应用不是构造器应用。
#[test]
fn rejects_computed_argument() {
    assert_err_contains(
        "def cs(n: Nat): Nat = match n {\n    case zero => zero\n    case succ(k) => cs (nat_add k k)\n}",
        TERM_MSG,
    );
}

/// let 计算值实参（nat_div 的形状，mydiv 未进 allowlist ⇒ 拒）：
/// `match sub` 的 scrutinee 是 let 槽，链不下落到参数。
#[test]
fn rejects_let_computed_argument() {
    assert_err_contains(
        "def mydiv(x: Nat, y: Nat): Nat =\n    match x {\n        case zero => zero\n        case succ(_) =>\n            match y {\n                case zero => x\n                case succ(_) =>\n                    let sub = nat_sub x y;\n                    match sub {\n                        case zero => zero\n                        case succ(_) => mydiv sub y\n                    }\n            }\n    }",
        TERM_MSG,
    );
}

/// gcd 的形状（未进 allowlist 的同形定义 ⇒ 拒）：换参 `g2(b, a)` 实参全
/// 是参数、`g2(nat_sub(a, b), b)` 是计算值。
#[test]
fn rejects_gcd_shape_swap_and_sub() {
    assert_err_contains(
        "def g2(a: Nat, b: Nat): Nat =\n    match b {\n        case zero => a\n        case succ(_) =>\n            match nat_compare(a, b) {\n                case lt => g2(b, a)\n                case eq => a\n                case gt => g2(nat_sub(a, b), b)\n            }\n    }",
        TERM_MSG,
    );
}

/// 被拒 def 的下游引用走既有失败 decl 通道（A2 降级）：`bad2 = bad 5`
/// 不再挂死 / 不再产出循环值，run_with_prelude 首错即 bad 的终止性错误
/// （完整级联形态由 CLI 探针 target/quirks/termination/probe_hang_elab
/// 覆盖——observe 面逐 decl 收集，bad2 报 not-in-scope 降级文案）。
#[test]
fn rejected_def_downstream_is_normal_decl_error() {
    assert_err_contains(
        "def bad(x: Nat): Nat = bad x\ndef bad2: Nat = bad 5\n",
        TERM_MSG,
    );
    twin_err_contains(
        "def bad(x: Nat): Nat = bad x\ndef bad2: Nat = bad 5\n",
        TERM_MSG,
    );
}

/// 孪生侧直连拒绝（与 rejects_direct_self_call 对拍）。
#[test]
fn twin_rejects_direct_self_call() {
    twin_err_contains("def bad(x: Nat): Nat = bad x", TERM_MSG);
}

// ── 正例：接受形态 ──

/// 结构递归（k 是 match 参数 n 的模式变量）。
#[test]
fn accepts_structural_recursion() {
    assert_output(
        "def s(n: Nat): Nat = match n {\n    case zero => zero\n    case succ(k) => s k\n}\nprintln (s 3)",
        &["0"],
    );
    assert_twin_matches_reference(
        "def s(n: Nat): Nat = match n {\n    case zero => zero\n    case succ(k) => s k\n}\nprintln (s 3)",
        24,
    );
}

/// 嵌套 match 链（is_even 形状）：内层 match 的 scrutinee 是外层模式变
/// 量——链经模式变量传递后仍算下落到参数。
#[test]
fn accepts_nested_match_chain() {
    assert_output(
        "def ne(n: Nat): Nat = match n {\n    case zero => zero\n    case succ(m) =>\n        match m {\n            case zero => zero\n            case succ(k) => ne k\n        }\n}\nprintln (ne 5)",
        &["0"],
    );
}

/// ping-pong 换参（**实测归类：接受**）。`weird b k` 的 b 是参数不算，k
/// 是模式变量 ⇒ Level A「至少一个实参」放行——文档化的不健全点；实测
/// 该形态按 (a+b) 递减本身也终止（weird 3 5 = 2）。
#[test]
fn accepts_ping_pong_swap_documented_unsoundness() {
    assert_output(
        "def weird(a: Nat, b: Nat): Nat =\n    match a {\n        case zero => b\n        case succ(k) => weird b k\n    }\nprintln (weird 3 5)",
        &["2"],
    );
}

/// 构造器包裹的模式变量实参（int_mul 的形状）：`cm (ofNat a) y` 的首
/// 实参是 Int 构造器应用于模式变量 a。
#[test]
fn accepts_ctor_wrapped_pattern_args() {
    assert_output(
        "def cm(x: Int, y: Int): Int =\n    match x {\n        case ofNat(n) =>\n            match n {\n                case zero => ofNat zero\n                case succ(a) => int_add y (cm (ofNat a) y)\n            }\n        case negSucc(_) => ofNat zero\n    }\nprintln (nat_of_int (cm (ofNat 2) (ofNat 3)))",
        &["6"],
    );
    // prelude 的 int_add / int_mul 本体（ctor 包裹递归的招牌）在每次
    // run_with_prelude 装载期即被检查；这里端到端跑一个负×负乘法
    // （Nat 字面量不自动转 Int，须显式 ofNat）。
    assert_output(
        "println (nat_of_int (int_mul (int_neg (ofNat 2)) (int_neg (ofNat 3))))",
        &["6"],
    );
}

/// 方法自递归经 Obj 派发（`t.lenOf`）：头不是 Decl-spine，Level A 不判
/// 定——文档化的洞（守卫是止损而非健全性证明）。
#[test]
fn accepts_method_self_recursion_via_dispatch() {
    // 构造器名避开 prelude List 的 lnil/lcons（裸名解析会被其抢先）。
    assert_output(
        "enum Lst {\n    mnil\n    mcons(h: Nat, t: Lst)\n}\nimpl Lst {\n    def lenOf: Nat = match this {\n        case mnil => zero\n        case mcons(_, t) => succ (t.lenOf)\n    }\n}\ndef l2: Lst = mcons(1, mcons(2, mnil))\nprintln l2.lenOf",
        &["2"],
    );
}

/// allowlist 成员仍照常 elaboration + 求值：nat_div / nat_rem 的递归回退
/// 定义在 prelude 装载期受检（allowlist 放行），装载后由
/// register_nat_builtins 换成 primop，用户侧行为不变。
#[test]
fn allowlisted_nat_div_rem_elaborate_and_evaluate() {
    assert_output("println (nat_div 7 2)\nprintln (nat_rem 7 2)", &["3", "1"]);
}
