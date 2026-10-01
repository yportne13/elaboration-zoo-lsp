//! spine 实参位单实参括号组的摊平回归套件（2026-10-01，Q1 错分组修复）。
//!
//! 背景：2026-09-19 的 SPINE_ESCAPE 哨兵只让 p_spine 结算**拆一层**标记，
//! 而 expr_bp 的后缀循环贪心折叠**任意多个**连续单实参括号组——于是
//! 「裸原子实参 + run ≥ 2 括号组」错分组：`add_assoc n (n * a) (n * k)`
//! 被读作 `add_assoc (n (n * a)) (n * k)`（首组胶连成对原子的应用，
//! 调用点报 can't unify）。修复（parser/mod.rs unescape_spine）把结算改
//! 为递归拆尽哨兵链：实参位括号组一律平级，部分应用的函数值实参须写
//! `f (g a b) c`。本套件从 elaboration 层钉住：
//!   1. 触发矩阵家族（`f n (x) (y)`、`f 0 (x) (y)`、`f n ((x => …)) (y)`、
//!      prelude `add_assoc n (n * a) (n * k)`）typecheck 且求值正确；
//!   2. 守护形状（run=1 `f n (x)`、头位 run、复杂实参在前、
//!      `cong succ (add_assoc n (n * k) k)`、`succ (x) + y`、
//!      `xs.map (f).length`、`f(a, b)` 逗号调用）不回归；
//!   3. 显式括号的部分应用实参仍是**单个**实参（语义决策的逃生门）；
//!   4. 参考版 ↔ 孪生版 parity（两实现共用 parser，回归即同坏；
//!      tests/implicit_comma_args.rs / l13_fast_parity.rs 同款线程壳）。
//!
//! 隐参同族问题（`f n [T]` 胶连成 `f (n[T])`）**不在本修复范围**：
//! `x [T]` 折叠是真实类型应用（`lnil[Nat]` / `List[Nat]` 惯用形），
//! 摊平它需要能区分「类型应用实参」与「平级隐参」，而空白不进词法，
//! 两者在 token 层不可区分——见 parser/mod.rs unescape_spine 文档。
//! parser 内联形状钉（spine_paren_shape 模块）另有
//! spine_impl_arg_type_application_stays_glued 钉住该现状。

#![allow(dead_code)]

#[path = "../src/list.rs"]
mod list;
#[path = "../src/bimap.rs"]
mod bimap;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L13_namespace/mod.rs"]
mod L13_namespace;

use L13_namespace::bump_spine_iter as fast;

/// 在大栈线程里跑带完整 prelude 的参考引擎（run_with_prelude）。
/// Error 可能携带非 Send 的重试闭包（L13 系）：子线程内先转归一化 String。
fn run_prelude(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L13_namespace::run_with_prelude(&input).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑参考版 `run`（无 prelude，parity 用）。
fn run_basic(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L13_namespace::run(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`（无 prelude，parity 用）。
fn run_fast(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// Err 文案归一化：剥掉 Span 偏移数字与 meta 编号 `?N`
/// （tests/l13_fast_parity.rs 同款，双实现 meta 分配序列不同）。
fn norm_err(e: &str) -> String {
    let mut out = String::with_capacity(e.len());
    let b = e.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'@' && i + 1 < b.len() && b[i + 1] == b' ' {
            let mut j = i + 2;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 2 {
                if j < b.len() && b[j] == b',' {
                    let mut k = j + 1;
                    while k < b.len() && b[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k > j + 1 {
                        j = k;
                    }
                }
                out.push_str("@ _");
                i = j;
                continue;
            }
        }
        if b[i] == b'?' && i + 1 < b.len() && b[i + 1].is_ascii_digit() {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                out.push_str("?_");
                i = j;
                continue;
            }
        }
        let rest = &e[i..];
        let mut matched = false;
        for key in ["start_offset: ", "end_offset: ", "path_id: "] {
            if rest.starts_with(key) {
                let mut j = i + key.len();
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
                if j > i + key.len() {
                    out.push('_');
                    i = j;
                    matched = true;
                    break;
                }
            }
        }
        if matched {
            continue;
        }
        let ch = e[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// 把 run 输出按行拆开（run_with_prelude 的 println 逐行 + 尾换行）。
fn lines(out: &str) -> Vec<&str> {
    out.lines().map(str::trim).filter(|l| !l.is_empty()).collect()
}

// ============================================================
// 1. 触发矩阵家族：修复后必须 typecheck 且求值正确
// ============================================================

/// 原始触发形状（分析 §2.2 / prelude nat.typort:96 注释绕开的写法）：
/// `add_assoc n (n * a) (n * k)` = add_assoc(2, 6, 8) : Eq 16 16，
/// match refl 取见证值 16。修复前被读作 `add_assoc (n (n * a)) (n * k)`，
/// `n (n * a)` 把 Nat 当函数应用，调用点 can't unify。
#[test]
fn add_assoc_bare_atom_paren_run_typechecks_and_evaluates() {
    let out = run_prelude(
        r#"
def n: Nat = 2
def a: Nat = 3
def k: Nat = 4
def w: Nat =
    match add_assoc n (n * a) (n * k) {
        case refl(z) => z
    }
println w
"#,
    )
    .expect("add_assoc n (n * a) (n * k) must elaborate after the fix");
    assert_eq!(lines(&out), vec!["16"]);
}

/// use4 混排矩阵（分析 §2.2）：字面量原子、函数值原子、lambda 组原子
/// 起头的 run ≥ 2 全部摊平。
#[test]
fn mixed_paren_runs_flatten_at_elaboration() {
    let out = run_prelude(
        r#"
def n: Nat = 2
def x: Nat = 5
def y: Nat = 7
def k: Nat = 4
def f4(p: Nat, q: Nat, r: Nat, s: Nat): Nat = ((p + q) + r) + s
def f5(p: Nat, g: Nat -> Nat, q: Nat): Nat = g (p + q)
println (f4 n (x) (y) k)
println (f4 0 (x) (y) k)
println (f5 n ((w => succ w)) (y))
"#,
    )
    .expect("mixed paren runs must elaborate after the fix");
    assert_eq!(lines(&out), vec!["18", "16", "10"]);
}

// ============================================================
// 2. 守护形状：2026-09-19 以来就正确的读法不许回归
// ============================================================

#[test]
fn guard_shapes_still_elaborate() {
    let out = run_prelude(
        r#"
def n: Nat = 2
def a: Nat = 3
def k: Nat = 4
def x: Nat = 5
def y: Nat = 7
def f3(p: Nat, q: Nat, r: Nat): Nat = (p + q) + r
println (f3 n (x) k)
println (f3 (n) (a) (k))
def w2: Nat =
    match add_assoc (n * a) n (n * k) {
        case refl(z) => z
    }
println w2
def p3: Eq (succ ((n + (n * k)) + k)) (succ (n + ((n * k) + k))) =
    cong succ (add_assoc n (n * k) k)
println (succ (x) + y)
println (nat_add(2, 3))
def lst: List[Nat] = lcons 1 (lcons 2 (lnil))
println (lst.map (w => w * 2)).length
println (lst.map (w => w * 2).length)
"#,
    )
    .expect("guard shapes must keep elaborating");
    assert_eq!(lines(&out), vec!["11", "9", "16", "13", "5", "2", "2"]);
}

// ============================================================
// 3. 语义决策逃生门：显式括号的部分应用实参仍是单个实参
// ============================================================

/// 摊平后要传「函数应用的值」必须显式括号（`f (g a b) c`）：
/// `(nat_add 2 3)` 整组是单个实参，不能被摊平成 `f nat_add 2 3 …`
/// （摊平会变四实参，f2 双参签名直接 can't unify）。
/// 注：不直接用裸部分应用 `nat_add 2` 作实参——具名参数 Pi
/// （`(y: Nat) → Nat`）与匿名 `Nat -> Nat` 的合一是引擎另一桩未修的
/// 刚性问题，与本修复无关，别把两件事钉在一起。
#[test]
fn explicit_paren_partial_application_stays_one_arg() {
    let out = run_prelude(
        r#"
def f2(v: Nat, w: Nat): Nat = v + w
println (f2 (nat_add 2 3) 4)
println (f2 2 3)
"#,
    )
    .expect("paren-wrapped application must stay one argument");
    assert_eq!(lines(&out), vec!["9", "5"]);
}

// ============================================================
// 4. 参考版 ↔ 孪生版 parity（共用 parser，Ok 逐字节 / Err 判定一致）
// ============================================================

const PARITY_SRC: &str = r#"
enum Nat {
    zero
    succ(n: Nat)
}
def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }
def two = succ (succ zero)
def f3(p: Nat, q: Nat, r: Nat): Nat = add (add p q) r
println (f3 two two two)
println (f3 two (two) (two))
println (f3 zero two two)
println (f3 zero (two) (two))
"#;

#[test]
fn flattened_run_matches_bare_juxtaposition_on_both_engines() {
    // 摊平读法正确性：`f3 two (two) (two)` 必须与无括号拼列 `f3 two two two`
    // 同值（修复前是 `f3 (two (two)) (two)`，Nat 当函数，Err）。
    let r = run_basic(PARITY_SRC).expect("reference engine must elaborate");
    let ls = lines(&r);
    assert_eq!(ls.len(), 4, "unexpected output: {r}");
    assert_eq!(ls[0], ls[1], "flattened run must equal bare juxtaposition");
    assert_eq!(ls[2], ls[3], "flattened run must equal bare juxtaposition");
    // parity：孪生快版 Ok 输出逐字节一致。
    let f = run_fast(PARITY_SRC).expect("twin engine must elaborate");
    assert_eq!(r, f, "parity mismatch");
}
