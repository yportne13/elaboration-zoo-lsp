//! L13 类型检查器基准：参考版（`Infer`/`Cxt`，生产路径）vs
//! `bump_spine_iter` 性能孪生的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs` / `src/bimap.rs` / `src/parser_lib*.rs`
//! 和 `src/L13_namespace/`（与 `tests/l13_fast_parity.rs` 同款）。
//!
//! 负载族（`--workload`）：
//! - `church` / `natadd` / `gadt` / `strchain` / `match` / `enum` / `struct`：
//!   孪生自带生成器（与 L02-L08 bench 同族）。
//! - `prelude-core`：核心 prelude 15 个文件（无 `show.typort`——它依赖
//!   `nat_to_dec` prim，本 bench 不注册 nat 内建，两版同缺）。
//! - `prelude-core-show`：再加 `show.typort`（预期两版同 Err，用于确认
//!   缺口一致而非分叉）。
//! - `prelude-hdl`：core + 全部 HDL prelude（预期孪生早 Err——无宏展开/
//!   class 语义面缺口，用于量化接线距离）。
//! - `examples-hdl`：core + `examples/hdl/*.typort`（真实用户负载）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l13bench [--max-k 13] [--rounds 5]
//!        [--only basic,fast,fast_ss]
//!        [--workload church|prelude-core|...|all]
//! ```

#![allow(dead_code)]

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../bimap.rs"]
mod bimap;

#[path = "../parser_lib.rs"]
mod parser_lib;
#[path = "../parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../L13_namespace/mod.rs"]
mod L13_namespace;

use clap::Parser;
use mimalloc::MiMalloc;
use std::collections::HashMap;
use std::time::Instant;

use L13_namespace::bump_spine_iter as fast;
use L13_namespace::parser::macros::MacroRule;
use L13_namespace::parser::syntax::Decl;
use L13_namespace::parser::parser_with_macros;

#[derive(Parser)]
#[command(
    name = "l13bench",
    about = "L13 类型检查器基准：参考版 vs bump_spine_iter 版（合成 + 真实 prelude 负载）"
)]
struct Cli {
    /// church 数 = 2^(k+1)，k 从 9 起翻倍到 max-k
    #[arg(long, default_value_t = 13)]
    max_k: u32,

    /// 每实现每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定实现（逗号分隔：basic,fast,fast_ss）
    #[arg(long)]
    only: Option<String>,

    /// 负载族（见文件头）
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L13_STACK_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(256);
    std::thread::Builder::new()
        .stack_size(stack_mb << 20)
        .spawn(move || run(cli))
        .unwrap()
        .join()
        .unwrap();
}

// ── prelude 源（与 mod.rs::load_prelude_state_impl 同列表）──

const CORE: &[(&str, &str)] = &[
    ("op", include_str!("../prelude/core/op.typort")),
    ("eq", include_str!("../prelude/core/eq.typort")),
    ("nat", include_str!("../prelude/core/nat.typort")),
    ("calc", include_str!("../prelude/core/calc.typort")),
    ("bool", include_str!("../prelude/core/bool.typort")),
    ("option", include_str!("../prelude/data/option.typort")),
    ("result", include_str!("../prelude/data/result.typort")),
    ("order", include_str!("../prelude/data/order.typort")),
    ("void", include_str!("../prelude/core/void.typort")),
    ("decidable", include_str!("../prelude/data/decidable.typort")),
    ("vec", include_str!("../prelude/data/vec.typort")),
    ("either", include_str!("../prelude/data/either.typort")),
    ("list", include_str!("../prelude/data/list.typort")),
    ("string", include_str!("../prelude/data/string.typort")),
    ("nonempty", include_str!("../prelude/data/nonempty.typort")),
];

const HDL: &[(&str, &str)] = &[
    ("hdl-core", include_str!("../prelude/hdl/hdl-core.typort")),
    ("hdl-check", include_str!("../prelude/hdl/hdl-check.typort")),
    ("hdl-types", include_str!("../prelude/hdl/hdl-types.typort")),
    ("hdl-ops", include_str!("../prelude/hdl/hdl-ops.typort")),
    ("hdl-clock", include_str!("../prelude/hdl/hdl-clock.typort")),
    ("hdl-bus", include_str!("../prelude/hdl/hdl-bus.typort")),
    ("hdl-signals", include_str!("../prelude/hdl/hdl-signals.typort")),
    ("hdl-utils", include_str!("../prelude/hdl/hdl-utils.typort")),
    ("hdl-stream", include_str!("../prelude/hdl/hdl-stream.typort")),
    ("hdl-crossclock", include_str!("../prelude/hdl/hdl-crossclock.typort")),
    ("hdl-bus-proto", include_str!("../prelude/hdl/hdl-bus-proto.typort")),
    ("hdl-misc-io", include_str!("../prelude/hdl/hdl-misc-io.typort")),
    ("hdl-misc", include_str!("../prelude/hdl/hdl-misc.typort")),
    ("hdl-macros", include_str!("../prelude/hdl/hdl-macros.typort")),
    ("hdl-verilog-compat", include_str!("../prelude/hdl/hdl-verilog-compat.typort")),
    ("hdl-verilog", include_str!("../prelude/hdl/hdl-verilog.typort")),
];

/// 按参考版 prelude 加载口径解析一串文件：逐文件 `parser_with_macros`，
/// 累积导出宏，拼成单一 decl 序列（`bench_check_nf` 需要 `&[Decl]`）。
/// 返回 (decls, 每文件 decl 数, 首个失败文件)。
fn parse_prelude(
    files: &[(&str, &str)],
) -> (Vec<Decl>, Vec<(String, usize)>, Option<String>, Vec<usize>) {
    let mut macros: HashMap<String, Vec<MacroRule>> = Default::default();
    let mut all: Vec<Decl> = Vec::new();
    let mut counts: Vec<(String, usize)> = Vec::new();
    let mut failed: Option<String> = None;
    let mut nat_after: Vec<usize> = Vec::new();
    for (i, (name, src)) in files.iter().enumerate() {
        let pre = L13_namespace::preprocess(src);
        match parser_with_macros(&pre, i as u32, &macros) {
            Some((decls, _errs, exports, _exp)) => {
                for (k, v) in exports {
                    macros.insert(k, v);
                }
                counts.push((name.to_string(), decls.len()));
                all.extend(decls);
                if *name == "nat" && !all.is_empty() {
                    nat_after.push(all.len() - 1);
                }
            }
            None => {
                failed = Some(name.to_string());
                break;
            }
        }
    }
    (all, counts, failed, nat_after)
}

/// 跑一个 decl 序列的两版口径，返回 (basic_nf, fast_nf, 两版是否一致)。
fn nf_parity(decls: &[Decl], nat_after: &[usize]) -> (u64, u64, bool) {
    let b = L13_namespace::bench_check_nf_bounded(decls, nat_after);
    let mut t = fast::Tycker::new();
    let f = t.bench_check_nf_bounded(decls, nat_after);
    (b, f, b == f && b != 0)
}

/// 诊断：逐 decl 喂孪生，报首个失败的 decl 序号与错误（twin 早退时定位用）。
fn diagnose_fast(label: &str, decls: &[Decl], nat_after: &[usize]) {
    if std::env::var_os("L13BENCH_DIAG").is_none() {
        return;
    }
    // 增量喂：每次多一个 decl，二分定位首个失败点
    let mut lo = 0usize;
    let mut hi = decls.len();
    let fails = |n: usize| -> bool {
        let mut t = fast::Tycker::new();
        let bounds: Vec<usize> = nat_after.iter().copied().filter(|&i| i < n).collect();
        t.run_decls_bounded(&decls[..n], &bounds).is_err()
    };
    if !fails(decls.len()) {
        println!("   [diag] {label}: twin 全部 {} decls 通过", decls.len());
        return;
    }
    while lo + 1 < hi {
        let mid = (lo + hi) / 2;
        if fails(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let mut t = fast::Tycker::new();
    let bounds: Vec<usize> = nat_after.iter().copied().filter(|&i| i < hi).collect();
    let err = t.run_decls_bounded(&decls[..hi], &bounds).err();
    let decl_name = decl_name_of(&decls[hi - 1]);
    println!(
        "   [diag] {label}: twin 首个失败在第 {hi}/{} 个 decl ({decl_name}): {:?}",
        decls.len(),
        err.map(|e| e.0.data)
    );
}

fn decl_name_of(d: &Decl) -> String {
    use L13_namespace::parser::syntax::Decl as D;
    match d {
        D::Def { name, .. } => format!("def {}", name.data),
        D::Enum { name, .. } => format!("enum {}", name.data),
        D::TraitDecl { name, .. } => format!("trait {}", name.data),
        D::ImplDecl { name, trait_name, .. } => {
            format!("impl {} for {}", trait_name.data, name)
        }
        D::Class { name, .. } => format!("class {}", name.data),
        D::Package { path } => format!(
            "package {}",
            path.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join(".")
        ),
        D::Import { .. } => "import".to_string(),
        D::Println(_) => "println".to_string(),
        D::Derive { .. } => "derive".to_string(),
    }
}

fn bench_one(label: &str, decls: &[Decl], nat_after: &[usize], cli: &Cli, want: &dyn Fn(&str) -> bool) {
    // 计时外：正确性互检
    let (b_nf, f_nf, ok) = nf_parity(decls, nat_after);
    diagnose_fast(label, decls, nat_after);
    let verdict = if ok {
        format!("nf={b_nf}")
    } else {
        format!("NF-DIVERGE basic={b_nf} fast={f_nf}")
    };
    println!("-- {label} ({} decls) {verdict}", decls.len());

    let mut ts_basic: Vec<u128> = Vec::new();
    let mut ts_fast: Vec<u128> = Vec::new();
    let mut ts_ss: Vec<u128> = Vec::new();
    let mut tycker_ss = if want("fast_ss") { Some(fast::Tycker::new()) } else { None };
    if let Some(t) = tycker_ss.as_mut() {
        t.bench_check_nf_bounded(decls, nat_after);
    }
    for _ in 0..cli.rounds {
        if let Some(t) = tycker_ss.as_mut() {
            let s = Instant::now();
            t.bench_check_nf_bounded(decls, nat_after);
            ts_ss.push(s.elapsed().as_micros());
        }
        if want("fast") {
            let s = Instant::now();
            let mut t = fast::Tycker::new();
            t.bench_check_nf_bounded(decls, nat_after);
            ts_fast.push(s.elapsed().as_micros());
        }
        if want("basic") {
            let s = Instant::now();
            L13_namespace::bench_check_nf_bounded(decls, nat_after);
            ts_basic.push(s.elapsed().as_micros());
        }
    }
    let mut rows: Vec<(&str, u128, u128)> = Vec::new();
    if want("basic") {
        rows.push(("basic", *ts_basic.iter().min().unwrap(), median(&mut ts_basic)));
    }
    if want("fast") {
        rows.push(("fast", *ts_fast.iter().min().unwrap(), median(&mut ts_fast)));
    }
    if want("fast_ss") {
        rows.push(("fast_ss", *ts_ss.iter().min().unwrap(), median(&mut ts_ss)));
    }
    let fastest = rows.iter().map(|r| r.1).min().unwrap_or(0);
    for (name, min, med) in &rows {
        let star = if *min == fastest { "*" } else { " " };
        print!(
            "   {name:<8}{:>8}.{:03}ms{star}  med {:>8}.{:03}ms\n",
            min / 1000,
            min % 1000,
            med / 1000,
            med % 1000
        );
    }
}

fn run(cli: Cli) {
    let want = |name: &str| {
        cli.only
            .as_deref()
            .map(|s| s.split(',').any(|x| x.trim() == name))
            .unwrap_or(true)
    };
    let workloads: Vec<&str> = match cli.workload.as_str() {
        "all" => vec![
            "church", "natadd", "gadt", "strchain", "match", "enum", "struct", "moduletree",
            "prelude-core", "prelude-core-show", "prelude-hdl", "examples-hdl",
        ],
        w => vec![w],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        match workload {
            "church" | "natadd" | "gadt" | "strchain" | "match" | "enum" | "struct" | "moduletree" => {
                let ks: Vec<u32> = if matches!(workload, "gadt" | "enum" | "moduletree") {
                    vec![9]
                } else {
                    (9..=cli.max_k).collect()
                };
                for k in ks {
                    let src = match workload {
                        "church" => fast::church_src(k),
                        "natadd" => fast::natadd_src(k),
                        "gadt" => fast::gadt_src(),
                        "strchain" => fast::strchain_src(k),
                        "match" => fast::match_src(k),
                        "struct" => fast::struct_src(k),
                        "moduletree" => fast::moduletree_src(),
                        _ => fast::enum_src(),
                    };
                    let Ok(decls) = fast::parse(&src, 0) else {
                        eprintln!("parse failed at k={k}");
                        continue;
                    };
                    bench_one(&format!("{workload} k={k}"), &decls, &[], &cli, &want);
                }
            }
            "prelude-core" | "prelude-core-show" | "prelude-hdl" => {
                let mut files: Vec<(&str, &str)> = CORE.to_vec();
                if workload != "prelude-core" {
                    files.push(("show", include_str!("../prelude/show.typort")));
                }
                if workload == "prelude-hdl" {
                    files.extend_from_slice(HDL);
                }
                let (decls, counts, failed, nat_after) = parse_prelude(&files);
                for (n, c) in &counts {
                    println!("   parsed {n}: {c} decls");
                }
                if let Some(f) = &failed {
                    println!("   PARSE-FAILED at {f}");
                }
                bench_one(workload, &decls, &nat_after, &cli, &want);
            }
            "examples-hdl" => {
                // 核心 prelude + 每个 example 单独一段（避免宏跨文件冲突）
                let (prelude_decls, _c, _f, core_nat) = parse_prelude(CORE);
                let mut examples: Vec<(String, String)> = Vec::new();
                for e in [
                    include_str!("../../examples/hdl/01-basics.typort"),
                    include_str!("../../examples/hdl/02-arithmetic.typort"),
                    include_str!("../../examples/hdl/05-bool.typort"),
                    include_str!("../../examples/hdl/07-registers.typort"),
                    include_str!("../../examples/hdl/09-hierarchy.typort"),
                    include_str!("../../examples/hdl/16-counter.typort"),
                ] {
                    examples.push((String::new(), e.to_string()));
                }
                for (i, (_n, src)) in examples.iter().enumerate() {
                    let mut decls = prelude_decls.clone();
                    let pre = L13_namespace::preprocess(src);
                    match parser_with_macros(&pre, 100 + i as u32, &Default::default()) {
                        Some((d, _e, _x, _p)) => decls.extend(d),
                        None => {
                            println!("   example {i} parse failed");
                            continue;
                        }
                    }
                    bench_one(&format!("examples-hdl[{i}]"), &decls, &core_nat, &cli, &want);
                }
            }
            other => eprintln!("unknown workload: {other}"),
        }
    }
}
