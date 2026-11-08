//! M3：Lean 可执行 oracle ↔ L07 参考引擎的差分测试（curated review 语料）。
//!
//! 默认 **跳过**（不要求 CI 有 Lean 工具链）；打开方式：
//!
//! ```powershell
//! $L = "$env:USERPROFILE\.lean4-toolchain\lean\lean-4.34.1-windows"
//! $env:PATH = "$L\bin;$env:PATH"
//! Set-Location lean; lake build engine-oracle
//! Set-Location ..
//! $env:LEAN_ORACLE = '1'
//! cargo test --test lean_oracle_parity
//! ```
//!
//! oracle 可执行文件默认取 `lean/.lake/build/bin/engine-oracle.exe`（可用
//! `LEAN_ORACLE_BIN` 覆盖）。每个语料在 Lean 侧的裁决依据见
//! `lean/Typort/Engine/Oracle.lean` 的模块注释（R2/R1/R3/P15 的机检定理）。
//!
//! 这与 `l07_fast_parity` 的区别：那里比的是「参考版 vs 性能孪生版」两个 Rust
//! 实现；这里是「Lean 形式化模型 vs Rust 参考引擎」，即 M3 的第三方语义裁判
//! 与漂移探针。

use std::process::Command;
use std::time::{Duration, Instant};

fn lean_oracle_enabled() -> bool {
    std::env::var("LEAN_ORACLE").as_deref() == Ok("1")
}

fn lean_oracle_bin() -> Option<std::path::PathBuf> {
    if let Ok(p) = std::env::var("LEAN_ORACLE_BIN") {
        return Some(std::path::PathBuf::from(p));
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for rel in [
        "lean/.lake/build/bin/engine-oracle.exe",
        "lean/.lake/build/bin/engine-oracle",
    ] {
        let p = root.join(rel);
        if p.exists() {
            return Some(p);
        }
    }
    None
}

/// 在大栈线程里跑参考引擎（依赖匹配的精化合一链远超默认 2 MB 栈）。
fn run_l07(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            elaboration_zoo_lsp::L07_sum_type::run(&input, 0)
                .map(|out| out)
                .map_err(|e| e.to_string())
        })
        .expect("spawn")
        .join()
        .expect("join")
}

fn oracle_verdict(exe: &std::path::Path, case: &str) -> String {
    let start = Instant::now();
    let out = Command::new(exe)
        .arg(case)
        .output()
        .unwrap_or_else(|e| panic!("无法运行 Lean oracle {exe:?}（{e}）；先 `lake build engine-oracle`"));
    let dt = start.elapsed();
    assert!(
        out.status.success(),
        "Lean oracle 对 {case} 退出码 {:?}；stderr={:?}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        dt < Duration::from_secs(30),
        "Lean oracle 对 {case} 耗时 {dt:?}（>30 s）"
    );
    String::from_utf8_lossy(&out.stdout).trim().to_owned()
}

/// 崩溃/超时之外的协议健壮性：未知语料必须 exit 2（避免"永远 ok"式空转）。
#[test]
fn lean_oracle_rejects_unknown_case() {
    if !lean_oracle_enabled() {
        eprintln!("LEAN_ORACLE!=1：跳过（需先 `lake build engine-oracle`）");
        return;
    }
    let exe = lean_oracle_bin().expect("找不到 engine-oracle；先 `lake build engine-oracle`");
    let out = Command::new(&exe)
        .arg("no-such-case")
        .output()
        .expect("run lean oracle");
    assert_eq!(out.status.code(), Some(2), "未知语料应 exit 2");
}

/// c1（review R2）/ c2（review R3）/ 空类型零臂（review R1）/ struct_eq pending（P15）
/// 四组语料：Lean oracle 与 Rust 参考引擎的接受/拒绝判定必须一致。
#[test]
fn lean_oracle_matches_reference_on_review_corpus() {
    if !lean_oracle_enabled() {
        eprintln!("LEAN_ORACLE!=1：跳过（需先 `lake build engine-oracle`）");
        return;
    }
    let exe = lean_oracle_bin().expect("找不到 engine-oracle；先 `lake build engine-oracle`");

    // c1：两跳环（`x := a`、`a := succ x`），occurrence 检查应拒绝。
    let occurs_transitive = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def bad(x: Nat, e: Eq[Nat] x (succ x)): Nat =
    match e {
        case refl(a) => zero
    }
"#;

    // c2：两个递归 def 的卡住索引方程，预算生效后按不可判定保守失败。
    let stuck_match_bounded = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def f(x: Nat, y: Nat, e: Eq[Nat] (add x zero) (add y zero)): Nat =
    match e {
        case refl(a) => a
    }
"#;

    // 空类型零臂 match：`T Bool`/`T String` 都不可达，零臂消去合法。
    let empty_type_zero_arm = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum T(A : U) {
    c -> T Nat
}

def f1(e: T Bool): Nat =
    match e { }

def f2(e: T String): Nat =
    match e { }

println "ok"
"#;

    // struct_eq 的 pending 值不同 ⇒ `refl` 不能证明 f = g。
    let struct_eq_pending = r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}

def pfun(n: Nat): Nat -> Nat =
    match n {
        case zero => k => k
        case succ(j) => k => k
    }

def f(x: Nat): Nat =
    match (pfun x zero) {
        case zero => zero
        case succ(m) => succ m
    }

def g(x: Nat): Nat =
    match (pfun x (succ zero)) {
        case zero => zero
        case succ(m) => succ m
    }

def bad : Eq[Nat -> Nat] f g =
    refl f
"#;

    let cases: &[(&str, &str)] = &[
        ("occurs-transitive", occurs_transitive),
        ("stuck-match-bounded", stuck_match_bounded),
        ("empty-type-zero-arm", empty_type_zero_arm),
        ("struct-eq-pending", struct_eq_pending),
    ];

    for (name, src) in cases {
        let lean = oracle_verdict(&exe, name);
        let start = Instant::now();
        let rust_ok = match run_l07(src) {
            Ok(_) => true,
            Err(_) => false,
        };
        let rust = if rust_ok { "ok" } else { "err" };
        let dt = start.elapsed();
        assert!(
            dt < Duration::from_secs(30),
            "Rust 参考引擎对 {name} 耗时 {dt:?}（>30 s）：预算/守卫可能失效"
        );
        assert_eq!(
            lean, rust,
            "语料 `{name}` 判定分裂：Lean oracle={lean}，Rust 参考引擎={rust}\n\
             （Lean 侧依据见 lean/Typort/Engine/Oracle.lean 模块注释）\n--- 源码 ---\n{src}"
        );
    }
}
