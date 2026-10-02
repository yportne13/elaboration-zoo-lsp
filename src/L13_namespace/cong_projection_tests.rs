// ============================================================
// cong 作用于字面 lambda：卡死投影重归约（挂起选择子）回归测试
//
// 根因（docs/l13-quirks-analysis-2026-10.md §1）：lambda 体的 trait 方法
// `+` 造出字典 meta（Self 仍 flex → 推迟），余定义域 `Eq (f ?x) (f ?y)`
// 求值期把 `Obj(?D, ".+")` 烘成永久卡死单元；字典 meta 后续落地后无入
// 重新投影。修复 = 双引擎把卡死 Obj 改成挂起选择子（twin force.rs 的
// 裸 Obj 臂 + HK_OBJ 链臂；参考版 mod.rs force 的 Obj 臂）+ 唯一候选
// trait goal 不再推迟（twin typeclass.rs / 参考 unification.rs solve_trait），
// 使 `cong (x => x + 0) rfl` 这类无刚性锚点的写法可检。
//
// 正例： refl 解包出值断言（参考版 run_with_prelude）+ 孪生/参考双引擎
// 输出一致性（run_decls_with_prelude 对拍）。负例：真正不等的形状必须
// 仍报 can't unify（calc_tests.rs:21 的 assert_err_contains 口径）。
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

/// 在 512MB 栈的独立线程里跑测试体（孪生走图递归深度超出测试线程默认栈，
/// observation_tests 同款）。
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

/// 核心 prelude 文件序列（含 show——参考版加载器恒排在最后）。
fn core_files() -> Vec<(&'static str, &'static str)> {
    let mut v: Vec<(&'static str, &'static str)> = PRELUDE_CORE.to_vec();
    v.push(PRELUDE_SHOW);
    v
}

/// 双引擎各跑一遍「core prelude + 用户源」，断言两版 Ok 且输出一致
/// （observation_tests::run_prelude_both 的收敛版：不取观察表）。
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
    })
}

// ── 正例：`cong (x => x + 0) rfl`—— rfl 无刚性锚点，字典 meta 靠唯一
// 候选落地 + 卡死投影重归约 ──

#[test]
fn cong_lambda_add_zero_refl_unwraps() {
    let output = assert_ok(r#"
def uses_cong_lambda(n: Nat): Eq (n + 0) (n + 0) =
    cong (x => x + 0) rfl
def r = uses_cong_lambda 5
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "5", "expected 5, got: {}", output);
}

// ── 正例：lambda 捕获外层变量 n ──

#[test]
fn cong_lambda_captured_var_refl_unwraps() {
    let output = assert_ok(r#"
def pq(n: Nat): Eq (n + n) (n + n) =
    cong (x => x + n) rfl
def r = pq 4
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "8", "expected 8, got: {}", output);
}

// ── 正例：期望侧非归约形状的 cong2（ps 探针形状）──
//
// 注：refl 解包出的**见证值**是 cong2 内部 `refl (f a b)` 的 `f a b`，
// 其中 b 是 e2（裸 rfl）索引 meta 的解——裸 rfl 索引 meta 与 find 侧
// 索引 meta 的解出现分叉（类型侧已正确钉到 k，见证侧取到 m/n），HEAD
// 上同值 4（cong2+裸 rfl 在修复前即可检，同款分叉），非本修复引入。
// 此处钉现状防漂移；类型本身 `Eq (2+3) (2+3)` 已正确检查。

#[test]
fn cong2_nat_add_e_rfl_nonreducing_expected() {
    let output = assert_ok(r#"
def ps(m: Nat, n: Nat, k: Nat, e: Eq m n): Eq (m + k) (n + k) =
    cong2 nat_add e rfl
def r = ps 2 2 3 (rfl)
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "4", "expected 4 (pre-existing bare-rfl witness split), got: {}", output);
}

// ── 正例：具类型证明变量（e-case，修复前即通过——防回归）──

#[test]
fn cong_lambda_typed_proof_var_still_ok() {
    let output = assert_ok(r#"
def pw(m: Nat, n: Nat, e: Eq m n): Eq (m + 0) (n + 0) =
    cong (x => x + 0) e
def r = pw 3 3 (rfl)
println (match r { case refl(a) => a })
"#);
    assert!(output.trim() == "3", "expected 3, got: {}", output);
}

// ── 负例：真正不等的形状必须仍失败（`x + 1` ≠ 恒等；字典落地后
// `nat_add ?x 1 → succ ?x` 与 `n` 失配）──

#[test]
fn cong_lambda_add_one_inequal_still_errs() {
    assert_err_contains(
        r#"
def bad(n: Nat): Eq n n =
    cong (x => x + 1) rfl
"#,
        "can't unify",
    );
}

// ── 负例（已知残留，非本修复范围）：pr 探针形状——期望侧 `Eq (m+0) (n+0)`
// 归约成 `Eq m n`，而 find 侧 `nat_add m ?v` 需要反向解出 rfl 的索引
// `?v := 0`（prim 反向求解，模式合一不做）。钉住现状防静默漂移；
// 修复路径见 docs/l13-quirks-analysis-2026-10.md §1（三方死锁的第三
// 方——本对拍只动了前两方）。
#[test]
fn cong2_reducing_expected_shape_residual_known_limitation() {
    assert_err_contains(
        r#"
def pr(m: Nat, n: Nat, e: Eq m n): Eq (m + 0) (n + 0) =
    cong2 nat_add e rfl
"#,
        "can't unify",
    );
}

// ── 双引擎对拍：正例形状孪生与参考版输出必须一致 ──

#[test]
fn cong_lambda_shapes_twin_matches_reference() {
    assert_twin_matches_reference(
        r#"
def uses_cong_lambda(n: Nat): Eq (n + 0) (n + 0) =
    cong (x => x + 0) rfl
def pq(n: Nat): Eq (n + n) (n + n) =
    cong (x => x + n) rfl
def a = uses_cong_lambda 5
def b = pq 4
println (match a { case refl(x) => x })
println (match b { case refl(x) => x })
"#,
        77,
    );
}
