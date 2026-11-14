//! realbench —— L07–L12 **真实语料**性能基准（参考版 vs 孪生版）。
//!
//! 与 `l07bench`…`l12bench` 的区别：那六个 bin 量的是 k 翻倍的**合成生成器
//! 负载**（church/strchain/match/…），只覆盖单一语言特性；本 bin 量的是
//! `tools/bench_corpus/Lxx/` 下的**真实语料**——仓库测试/README 里抽取并
//! 经语义验证的程序，以及按真实领域手写的项目级程序（解释器、列表库、
//! trait 家族、宏 DSL……）。
//!
//! 口径（与既有 bench 对齐，见 docs/bench-matrix-2026-09-20.md）：
//! - 解析在计时外（L07–L10 的 basic/fast/fast_ss 三轴都是 parse-out 口径）；
//! - `basic` = 参考版 `bench_check_nf`（L07–L10）；L11/L12 参考版没有
//!   `bench_check_nf`，故 `basic` 是全流程 `run`（含 parse+pretty），
//!   另设同轴的 `fast_run`（孪生全流程）与 parse-out 的 `fast`/`fast_ss`；
//! - 每轮内 basic / twin 交替执行（轮级交错 + 奇偶轮换序），每配置取 min；
//! - 计时前先过**正确性闸门**：参考版全流程 `run` 必须 Ok，且参考版与孪生版
//!   的 nf 节点数一致（L07–L10）或全流程输出逐字节一致（L11/L12）——
//!   不通过的文件记为 SKIP，不进入计时。
//!
//! 用法：
//! ```text
//! cargo run --release --bin realbench -- --layer L07 --corpus tools/bench_corpus/L07 --rounds 5
//! cargo run --release --bin realbench -- --layer all --validate
//! ```
//! 输出为 CSV 行：`PASS/SKIP/SUMMARY/CASE/TOTAL,<layer>,…`，便于脚本汇总。

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

#[path = "../L07_sum_type/mod.rs"]
mod L07_sum_type;
#[path = "../L08_product_type/mod.rs"]
mod L08_product_type;
#[path = "../L09_mltt/mod.rs"]
mod L09_mltt;
#[path = "../L10_typeclass/mod.rs"]
mod L10_typeclass;
#[path = "../L11_macro/mod.rs"]
mod L11_macro;
#[path = "../L12_canonical/mod.rs"]
mod L12_canonical;

use clap::Parser;
use mimalloc::MiMalloc;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Parser)]
#[command(
    name = "realbench",
    about = "L07–L12 真实语料性能基准：参考版 vs 孪生版（tools/bench_corpus/）"
)]
struct Cli {
    /// 层：L07|L08|L09|L10|L11|L12|all
    #[arg(long, default_value = "all")]
    layer: String,

    /// 语料目录（默认 tools/bench_corpus/<layer>）
    #[arg(long)]
    corpus: Option<String>,

    /// 每配置计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 每轮把整个语料重复 N 遍（短语料稳定化；总耗时按 N 倍累计）
    #[arg(long, default_value_t = 1)]
    repeat: usize,

    /// 只跑指定口径（逗号分隔：basic,fast,fast_ss,fast_run）
    #[arg(long)]
    only: Option<String>,

    /// 只验证语料合法性（PASS/SKIP + SUMMARY），不计时
    #[arg(long)]
    validate: bool,
}

fn want(only: &Option<String>, name: &str) -> bool {
    only
        .as_deref()
        .map(|s| s.split(',').any(|x| x.trim() == name))
        .unwrap_or(true)
}

fn median(ts: &mut [u128]) -> u128 {
    if ts.is_empty() {
        return 0;
    }
    ts.sort_unstable();
    ts[ts.len() / 2]
}

/// 单个用例的各口径耗时样本（µs）。未跑的轴为空。
#[derive(Default)]
struct Times {
    basic: Vec<u128>,
    fast_run: Vec<u128>,
    fast: Vec<u128>,
    fast_ss: Vec<u128>,
}

struct Case<A> {
    file: String,
    bytes: usize,
    decls: usize,
    src: String,
    ast: A,
}

fn read_dir_typort(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("typort"))
                .collect()
        })
        .unwrap_or_default();
    v.sort();
    v
}

/// 读目录 + 解析 + 语义闸门。返回 (通过用例, PASS 数, SKIP 数)。
fn load_cases<A>(
    layer: &str,
    dir: &Path,
    validate: bool,
    parse: impl Fn(&str) -> Option<(A, usize)>,
    gate: impl Fn(&A, &str) -> Result<(), String>,
) -> (Vec<Case<A>>, usize, usize) {
    let mut cases = Vec::new();
    let mut pass = 0usize;
    let mut skip = 0usize;
    for path in read_dir_typort(dir) {
        let file = path
            .file_name()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| path.display().to_string());
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                println!("SKIP,{layer},{file},reason=read_err:{e}");
                skip += 1;
                continue;
            }
        };
        let parsed = std::panic::catch_unwind(AssertUnwindSafe(|| parse(&src)));
        let (ast, decls) = match parsed {
            Ok(Some(v)) => v,
            Ok(None) => {
                println!("SKIP,{layer},{file},reason=parse_fail");
                skip += 1;
                continue;
            }
            Err(_) => {
                println!("SKIP,{layer},{file},reason=parse_panic");
                skip += 1;
                continue;
            }
        };
        let gated = std::panic::catch_unwind(AssertUnwindSafe(|| gate(&ast, &src)));
        match gated {
            Ok(Ok(())) => {
                pass += 1;
                if validate {
                    println!("PASS,{layer},{file},bytes={},decls={decls}", src.len());
                }
                cases.push(Case {
                    file,
                    bytes: src.len(),
                    decls,
                    src,
                    ast,
                });
            }
            Ok(Err(reason)) => {
                println!("SKIP,{layer},{file},reason={reason}");
                skip += 1;
            }
            Err(_) => {
                println!("SKIP,{layer},{file},reason=gate_panic");
                skip += 1;
            }
        }
    }
    (cases, pass, skip)
}

/// parse-out 三轴（L07–L10）：basic=参考版 bench_check_nf，fast/fast_ss=孪生。
fn run_ast_layer<A>(
    layer: &str,
    cases: &[Case<A>],
    cli: &Cli,
    mut fast: impl FnMut(&A),
    mut fast_ss: impl FnMut(&A),
    mut basic: impl FnMut(&A),
) {
    let wb = want(&cli.only, "basic");
    let wf = want(&cli.only, "fast");
    let ws = want(&cli.only, "fast_ss");
    let n = cases.len();
    let mut per: Vec<Times> = (0..n).map(|_| Times::default()).collect();
    let mut totals: Vec<(u128, u128, u128)> = Vec::with_capacity(cli.rounds);
    for r in 0..cli.rounds {
        let mut tot = (0u128, 0u128, 0u128); // (fast, fast_ss, basic)
        for _ in 0..cli.repeat.max(1) {
            for (i, c) in cases.iter().enumerate() {
                let ast = &c.ast;
                let rev = r % 2 == 1;
                if !rev {
                    if wf {
                        let t = Instant::now();
                        fast(ast);
                        let d = t.elapsed().as_micros();
                        per[i].fast.push(d);
                        tot.0 += d;
                    }
                    if ws {
                        let t = Instant::now();
                        fast_ss(ast);
                        let d = t.elapsed().as_micros();
                        per[i].fast_ss.push(d);
                        tot.1 += d;
                    }
                    if wb {
                        let t = Instant::now();
                        basic(ast);
                        let d = t.elapsed().as_micros();
                        per[i].basic.push(d);
                        tot.2 += d;
                    }
                } else {
                    if wb {
                        let t = Instant::now();
                        basic(ast);
                        let d = t.elapsed().as_micros();
                        per[i].basic.push(d);
                        tot.2 += d;
                    }
                    if ws {
                        let t = Instant::now();
                        fast_ss(ast);
                        let d = t.elapsed().as_micros();
                        per[i].fast_ss.push(d);
                        tot.1 += d;
                    }
                    if wf {
                        let t = Instant::now();
                        fast(ast);
                        let d = t.elapsed().as_micros();
                        per[i].fast.push(d);
                        tot.0 += d;
                    }
                }
            }
        }
        totals.push(tot);
    }
    print_layer(layer, cases, &per, cli, &totals, false);
}

/// 全流程四轴（L11/L12）：basic=参考版 run，fast_run=孪生 run_fast，
/// fast/fast_ss=孪生 parse-out bench。
fn run_full_layer<A>(
    layer: &str,
    cases: &[Case<A>],
    cli: &Cli,
    mut basic_src: impl FnMut(&str),
    mut fast_run_src: impl FnMut(&str),
    mut fast: impl FnMut(&A),
    mut fast_ss: impl FnMut(&A),
) {
    let wb = want(&cli.only, "basic");
    let wfr = want(&cli.only, "fast_run");
    let wf = want(&cli.only, "fast");
    let ws = want(&cli.only, "fast_ss");
    let n = cases.len();
    let mut per: Vec<Times> = (0..n).map(|_| Times::default()).collect();
    // totals: (basic, fast_run, fast, fast_ss)
    let mut totals: Vec<(u128, u128, u128, u128)> = Vec::with_capacity(cli.rounds);
    for r in 0..cli.rounds {
        let mut tot = (0u128, 0u128, 0u128, 0u128);
        for _ in 0..cli.repeat.max(1) {
            for (i, c) in cases.iter().enumerate() {
                axes4(
                    c,
                    r % 2 == 1,
                    (wb, wfr, wf, ws),
                    &mut per[i],
                    &mut tot,
                    &mut basic_src,
                    &mut fast_run_src,
                    &mut fast,
                    &mut fast_ss,
                );
            }
        }
        totals.push(tot);
    }
    print_layer(layer, cases, &per, cli, &[], false);
    let mins = |idx: fn(&(u128, u128, u128, u128)) -> u128| -> u128 {
        totals.iter().map(idx).min().unwrap_or(0)
    };
    println!(
        "TOTAL4,{layer},{n},{rounds},{repeat},{basic},{fast_run},{fast},{fast_ss}",
        n = n,
        rounds = cli.rounds,
        repeat = cli.repeat,
        basic = mins(|t| t.0),
        fast_run = mins(|t| t.1),
        fast = mins(|t| t.2),
        fast_ss = mins(|t| t.3)
    );
}

/// 一轮内跑四个口径；`rev=true` 时反序（消窗口偏置）。`tot` 四元组：
/// (basic, fast_run, fast, fast_ss)。
#[allow(clippy::too_many_arguments)]
fn axes4<A>(
    c: &Case<A>,
    rev: bool,
    want: (bool, bool, bool, bool),
    per: &mut Times,
    tot: &mut (u128, u128, u128, u128),
    basic_src: &mut impl FnMut(&str),
    fast_run_src: &mut impl FnMut(&str),
    fast: &mut impl FnMut(&A),
    fast_ss: &mut impl FnMut(&A),
) {
    let (wb, wfr, wf, ws) = want;
    if !rev {
        if wb {
            let t = Instant::now();
            basic_src(&c.src);
            let d = t.elapsed().as_micros();
            per.basic.push(d);
            tot.0 += d;
        }
        if wfr {
            let t = Instant::now();
            fast_run_src(&c.src);
            let d = t.elapsed().as_micros();
            per.fast_run.push(d);
            tot.1 += d;
        }
        if wf {
            let t = Instant::now();
            fast(&c.ast);
            let d = t.elapsed().as_micros();
            per.fast.push(d);
            tot.2 += d;
        }
        if ws {
            let t = Instant::now();
            fast_ss(&c.ast);
            let d = t.elapsed().as_micros();
            per.fast_ss.push(d);
            tot.3 += d;
        }
    } else {
        // 反序：fast_ss → fast → fast_run → basic
        if ws {
            let t = Instant::now();
            fast_ss(&c.ast);
            let d = t.elapsed().as_micros();
            per.fast_ss.push(d);
            tot.3 += d;
        }
        if wf {
            let t = Instant::now();
            fast(&c.ast);
            let d = t.elapsed().as_micros();
            per.fast.push(d);
            tot.2 += d;
        }
        if wfr {
            let t = Instant::now();
            fast_run_src(&c.src);
            let d = t.elapsed().as_micros();
            per.fast_run.push(d);
            tot.1 += d;
        }
        if wb {
            let t = Instant::now();
            basic_src(&c.src);
            let d = t.elapsed().as_micros();
            per.basic.push(d);
            tot.0 += d;
        }
    }
}

fn print_layer<A>(
    layer: &str,
    cases: &[Case<A>],
    per: &[Times],
    cli: &Cli,
    totals: &[(u128, u128, u128)],
    _full: bool,
) {
    for (c, t) in cases.iter().zip(per.iter()) {
        let (bmin, bmed) = stat(&t.basic);
        let (frmin, frmed) = stat(&t.fast_run);
        let (fmin, fmed) = stat(&t.fast);
        let (smin, smed) = stat(&t.fast_ss);
        println!(
            "CASE,{layer},{file},{bytes},{decls},{bmin},{bmed},{frmin},{frmed},{fmin},{fmed},{smin},{smed}",
            file = c.file,
            bytes = c.bytes,
            decls = c.decls,
            bmin = bmin,
            bmed = bmed,
            frmin = frmin,
            frmed = frmed,
            fmin = fmin,
            fmed = fmed,
            smin = smin,
            smed = smed
        );
    }
    if !totals.is_empty() {
        let tmin = |idx: fn(&(u128, u128, u128)) -> u128| -> u128 {
            totals.iter().map(idx).min().unwrap_or(0)
        };
        println!(
            "TOTAL,{layer},{n},{rounds},{repeat},{basic},{fast_run},{fast},{fast_ss}",
            n = cases.len(),
            rounds = totals.len(),
            repeat = cli.repeat,
            basic = tmin(|t| t.2),
            fast_run = 0,
            fast = tmin(|t| t.0),
            fast_ss = tmin(|t| t.1)
        );
    }
}

fn stat(v: &[u128]) -> (u128, u128) {
    if v.is_empty() {
        return (0, 0);
    }
    let mn = *v.iter().min().unwrap();
    let mut s = v.to_vec();
    (mn, median(&mut s))
}

// ── 各层：解析 / 语义闸门 / 计时 ──────────────────────────────────────────

fn bench_l07(cli: &Cli, dir: &Path) {
    let (cases, pass, skip) = load_cases(
        "L07",
        dir,
        cli.validate,
        |src| {
            let pre = L07_sum_type::preprocess(src);
            let d = L07_sum_type::parser::parser(&pre, 0).ok()?;
            let n = d.len();
            Some((d, n))
        },
        |ast: &Vec<L07_sum_type::parser::syntax::Decl>, src| {
            L07_sum_type::run(src, 0).map_err(|e| format!("run_err:{e:?}"))?;
            let mut t = L07_sum_type::bump_spine_iter::Tycker::new();
            let f = t.bench_check_nf(ast);
            let b = L07_sum_type::bench_check_nf(ast);
            if f == 0 {
                return Err("twin_nf_fail".into());
            }
            if b == 0 {
                return Err("ref_nf_fail".into());
            }
            if b != f {
                return Err(format!("nf_parity ref={b} twin={f}"));
            }
            Ok(())
        },
    );
    println!("SUMMARY,L07,pass={pass},skip={skip}");
    if cli.validate || cases.is_empty() {
        return;
    }
    run_ast_layer(
        "L07",
        &cases,
        cli,
        |ast| {
            let mut t = L07_sum_type::bump_spine_iter::Tycker::new();
            assert!(t.bench_check_nf(ast) > 0);
        },
        {
            let mut t = L07_sum_type::bump_spine_iter::Tycker::new();
            move |ast| {
                assert!(t.bench_check_nf(ast) > 0);
            }
        },
        |ast| {
            assert!(L07_sum_type::bench_check_nf(ast) > 0);
        },
    );
}

fn bench_l08(cli: &Cli, dir: &Path) {
    let (cases, pass, skip) = load_cases(
        "L08",
        dir,
        cli.validate,
        |src| {
            let pre = L08_product_type::preprocess(src);
            let d = L08_product_type::parser::parser(&pre, 0).ok()?;
            let n = d.len();
            Some((d, n))
        },
        |ast: &Vec<L08_product_type::parser::syntax::Decl>, src| {
            L08_product_type::run(src, 0).map_err(|e| format!("run_err:{e:?}"))?;
            let mut t = L08_product_type::bump_spine_iter::Tycker::new();
            let f = t.bench_check_nf(ast);
            let b = L08_product_type::bench_check_nf(ast);
            if f == 0 {
                return Err("twin_nf_fail".into());
            }
            if b == 0 {
                return Err("ref_nf_fail".into());
            }
            if b != f {
                return Err(format!("nf_parity ref={b} twin={f}"));
            }
            Ok(())
        },
    );
    println!("SUMMARY,L08,pass={pass},skip={skip}");
    if cli.validate || cases.is_empty() {
        return;
    }
    run_ast_layer(
        "L08",
        &cases,
        cli,
        |ast| {
            let mut t = L08_product_type::bump_spine_iter::Tycker::new();
            assert!(t.bench_check_nf(ast) > 0);
        },
        {
            let mut t = L08_product_type::bump_spine_iter::Tycker::new();
            move |ast| {
                assert!(t.bench_check_nf(ast) > 0);
            }
        },
        |ast| {
            assert!(L08_product_type::bench_check_nf(ast) > 0);
        },
    );
}

fn bench_l09(cli: &Cli, dir: &Path) {
    let (cases, pass, skip) = load_cases(
        "L09",
        dir,
        cli.validate,
        |src| {
            let d = L09_mltt::bump_spine_iter::parse(src, 0).ok()?;
            let n = d.len();
            Some((d, n))
        },
        |ast, src| {
            L09_mltt::run(src, 0).map_err(|e| format!("run_err:{e:?}"))?;
            let mut t = L09_mltt::bump_spine_iter::Tycker::new();
            let f = t.bench_check_nf(ast);
            let b = L09_mltt::bench_check_nf(ast);
            if f == 0 {
                return Err("twin_nf_fail".into());
            }
            if b == 0 {
                return Err("ref_nf_fail".into());
            }
            if b != f {
                return Err(format!("nf_parity ref={b} twin={f}"));
            }
            Ok(())
        },
    );
    println!("SUMMARY,L09,pass={pass},skip={skip}");
    if cli.validate || cases.is_empty() {
        return;
    }
    run_ast_layer(
        "L09",
        &cases,
        cli,
        |ast| {
            let mut t = L09_mltt::bump_spine_iter::Tycker::new();
            assert!(t.bench_check_nf(ast) > 0);
        },
        {
            let mut t = L09_mltt::bump_spine_iter::Tycker::new();
            move |ast| {
                assert!(t.bench_check_nf(ast) > 0);
            }
        },
        |ast| {
            assert!(L09_mltt::bench_check_nf(ast) > 0);
        },
    );
}

fn bench_l10(cli: &Cli, dir: &Path) {
    let (cases, pass, skip) = load_cases(
        "L10",
        dir,
        cli.validate,
        |src| {
            let d = L10_typeclass::bump_spine_iter::parse(src, 0).ok()?;
            let n = d.len();
            Some((d, n))
        },
        |ast, src| {
            L10_typeclass::run(src, 0).map_err(|e| format!("run_err:{e:?}"))?;
            let mut t = L10_typeclass::bump_spine_iter::Tycker::new();
            let f = t.bench_check_nf(ast);
            let b = L10_typeclass::bench_check_nf(ast);
            if f == 0 {
                return Err("twin_nf_fail".into());
            }
            if b == 0 {
                return Err("ref_nf_fail".into());
            }
            if b != f {
                return Err(format!("nf_parity ref={b} twin={f}"));
            }
            Ok(())
        },
    );
    println!("SUMMARY,L10,pass={pass},skip={skip}");
    if cli.validate || cases.is_empty() {
        return;
    }
    run_ast_layer(
        "L10",
        &cases,
        cli,
        |ast| {
            let mut t = L10_typeclass::bump_spine_iter::Tycker::new();
            assert!(t.bench_check_nf(ast) > 0);
        },
        {
            let mut t = L10_typeclass::bump_spine_iter::Tycker::new();
            move |ast| {
                assert!(t.bench_check_nf(ast) > 0);
            }
        },
        |ast| {
            assert!(L10_typeclass::bench_check_nf(ast) > 0);
        },
    );
}

fn bench_l11(cli: &Cli, dir: &Path) {
    let (cases, pass, skip) = load_cases(
        "L11",
        dir,
        cli.validate,
        |src| {
            let d = L11_macro::bump_spine_iter::parse(src, 0).ok()?;
            let n = d.len();
            Some((d, n))
        },
        |ast, src| {
            let b = L11_macro::run(src, 0).map_err(|e| format!("ref_run_err:{e:?}"))?;
            let f = L11_macro::bump_spine_iter::run_fast(src, 0)
                .map_err(|e| format!("twin_run_err:{e:?}"))?;
            if b != f {
                return Err("run_output_parity".into());
            }
            let mut t = L11_macro::bump_spine_iter::Tycker::new();
            if t.bench_check_nf(ast) == 0 {
                return Err("twin_nf_fail".into());
            }
            Ok(())
        },
    );
    println!("SUMMARY,L11,pass={pass},skip={skip}");
    if cli.validate || cases.is_empty() {
        return;
    }
    run_full_layer(
        "L11",
        &cases,
        cli,
        |src| {
            assert!(L11_macro::run(src, 0).is_ok());
        },
        |src| {
            assert!(L11_macro::bump_spine_iter::run_fast(src, 0).is_ok());
        },
        |ast| {
            let mut t = L11_macro::bump_spine_iter::Tycker::new();
            assert!(t.bench_check_nf(ast) > 0);
        },
        {
            let mut t = L11_macro::bump_spine_iter::Tycker::new();
            move |ast| {
                assert!(t.bench_check_nf(ast) > 0);
            }
        },
    );
}

fn bench_l12(cli: &Cli, dir: &Path) {
    let (cases, pass, skip) = load_cases(
        "L12",
        dir,
        cli.validate,
        |src| {
            let d = L12_canonical::bump_spine_iter::parse(src, 0).ok()?;
            let n = d.len();
            Some((d, n))
        },
        |ast, src| {
            let b = L12_canonical::run(src, 0).map_err(|e| format!("ref_run_err:{e:?}"))?;
            let f = L12_canonical::bump_spine_iter::run_fast(src, 0)
                .map_err(|e| format!("twin_run_err:{e:?}"))?;
            if b != f {
                return Err("run_output_parity".into());
            }
            let mut t = L12_canonical::bump_spine_iter::Tycker::new();
            if t.bench_check_nf(ast) == 0 {
                return Err("twin_nf_fail".into());
            }
            Ok(())
        },
    );
    println!("SUMMARY,L12,pass={pass},skip={skip}");
    if cli.validate || cases.is_empty() {
        return;
    }
    run_full_layer(
        "L12",
        &cases,
        cli,
        |src| {
            assert!(L12_canonical::run(src, 0).is_ok());
        },
        |src| {
            assert!(L12_canonical::bump_spine_iter::run_fast(src, 0).is_ok());
        },
        |ast| {
            let mut t = L12_canonical::bump_spine_iter::Tycker::new();
            assert!(t.bench_check_nf(ast) > 0);
        },
        {
            let mut t = L12_canonical::bump_spine_iter::Tycker::new();
            move |ast| {
                assert!(t.bench_check_nf(ast) > 0);
            }
        },
    );
}

fn run(cli: Cli) {
    let layers: Vec<&str> = match cli.layer.as_str() {
        "all" => vec!["L07", "L08", "L09", "L10", "L11", "L12"],
        "L07" | "L08" | "L09" | "L10" | "L11" | "L12" => vec![cli.layer.as_str()],
        other => {
            eprintln!("unknown layer: {other} (expect L07..L12 or all)");
            std::process::exit(2);
        }
    };
    for layer in layers {
        let dir = cli
            .corpus
            .as_deref()
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(format!("tools/bench_corpus/{layer}")));
        if !dir.is_dir() {
            println!("MISSING,{layer},{}", dir.display());
            continue;
        }
        println!("== layer: {layer} (corpus: {}) ==", dir.display());
        match layer {
            "L07" => bench_l07(&cli, &dir),
            "L08" => bench_l08(&cli, &dir),
            "L09" => bench_l09(&cli, &dir),
            "L10" => bench_l10(&cli, &dir),
            "L11" => bench_l11(&cli, &dir),
            "L12" => bench_l12(&cli, &dir),
            _ => unreachable!(),
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("REALBENCH_STACK_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(512);
    std::thread::Builder::new()
        .stack_size(stack_mb << 20)
        .spawn(move || run(cli))
        .unwrap()
        .join()
        .unwrap();
}
