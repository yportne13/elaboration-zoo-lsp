//! smallttbench —— smalltt（András Kovács）公开基准用例的 typort 迁移驱动。
//!
//! 目的：把 smalltt 仓库 bench/ 下的性能用例（conv_eval / asymptotics / stlc）
//! 翻译成 L07–L10 各层可消化的 typort 源码，并在**同一台机器**上测各层
//! 参考版 / 孪生版的耗时，回答「smalltt 的性能用例能否迁移到 L07–L10」。
//!
//! 口径（对齐 realbench / l07bench 的历史约定）：
//! - 解析在计时外；每轮内 ref/twin × check/nf 交错，奇偶轮换序；每格取 min；
//! - ref   = 参考版 bench_check（只 elaborate，不 quote）；
//! - ref_nf = 参考版 bench_check_nf（elaborate 后 quote 最后一个 def 的 nf，
//!   对应 smalltt 的 [nftime] 用例；最后一个 def 的选取由用例生成器保证）；
//! - twin / twin_nf = bump_spine_iter::Tycker 的同口径版本；
//! - 语义闸门：ref bench_check 必须为 true（否则 SKIP 并打印原因，不渲染
//!   巨型错误项——这是不用 realbench run 闸门的理由：燃料耗尽时 run 的
//!   can't unify 报错会 pretty 出巨大的 numeral）。
//!
//! 用法：
//!   cargo run --release --bin smallttbench -- --layer L07 --case natconv --sizes 1k,10k
//!   cargo run --release --bin smallttbench -- --layer all --rounds 5
//!   cargo run --release --bin smallttbench -- --dump-dir target/smalltt_corpus

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

#[path = "smalltt_cases/mod.rs"]
mod cases;

use clap::Parser;
use mimalloc::MiMalloc;
use std::panic::AssertUnwindSafe;
use std::time::Instant;

#[derive(Parser)]
#[command(
    name = "smallttbench",
    about = "smalltt 基准用例在 L07–L10 上的迁移测量"
)]
struct Cli {
    /// 层：L07|L08|L09|L10|all
    #[arg(long, default_value = "all")]
    layer: String,

    /// 用例：all 或逗号分隔（natconv,treeconv,forcetree,nftree,idtest,pairtest,vectest,stlc,...）
    #[arg(long, default_value = "all")]
    case: String,

    /// 只跑指定 size 标签（逗号分隔；缺省=该用例声明的全部）
    #[arg(long)]
    sizes: Option<String>,

    /// 每配置计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定口径（逗号分隔：ref,ref_nf,twin,twin_nf）
    #[arg(long)]
    only: Option<String>,

    /// 只验证/打印（不写 CSV 计时结果）
    #[arg(long)]
    validate: bool,

    /// 把生成的 typort 源码落盘到该目录（便于复现/人工检查）
    #[arg(long)]
    dump_dir: Option<String>,
}

fn want(only: &Option<String>, name: &str) -> bool {
    only.as_deref()
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

#[derive(Default, Clone)]
struct Times {
    ref_: Vec<u128>,
    ref_nf: Vec<u128>,
    twin: Vec<u128>,
    twin_nf: Vec<u128>,
}

impl Times {
    fn stat(v: &[u128]) -> (u128, u128) {
        if v.is_empty() {
            return (0, 0);
        }
        let mn = *v.iter().min().unwrap();
        let mut s = v.to_vec();
        (mn, median(&mut s))
    }
}

/// 单用例测量：闭包给出四个口径。返回 (ref_ok, twin_ok, nodes)。
#[allow(clippy::too_many_arguments)]
fn measure<A>(
    case: &str,
    size: &str,
    bytes: usize,
    decls: usize,
    ast: &A,
    cli: &Cli,
    mut ref_check: impl FnMut(&A) -> bool,
    mut ref_nf: impl FnMut(&A) -> u64,
    mut twin_check: impl FnMut(&A) -> bool,
    mut twin_nf: impl FnMut(&A) -> u64,
    times: &mut Times,
) -> (bool, bool, u64) {
    let wr = want(&cli.only, "ref");
    let wrn = want(&cli.only, "ref_nf");
    let wt = want(&cli.only, "twin");
    let wtn = want(&cli.only, "twin_nf");
    let mut ref_ok = true;
    let mut twin_ok = true;
    let mut nodes = 0u64;
    for r in 0..cli.rounds.max(1) {
        let rev = r % 2 == 1;
        if !rev {
            if wr {
                let t = Instant::now();
                ref_ok = ref_check(ast) && ref_ok;
                times.ref_.push(t.elapsed().as_micros());
            }
            if wrn {
                let t = Instant::now();
                nodes = ref_nf(ast);
                times.ref_nf.push(t.elapsed().as_micros());
            }
            if wt {
                let t = Instant::now();
                twin_ok = twin_check(ast) && twin_ok;
                times.twin.push(t.elapsed().as_micros());
            }
            if wtn {
                let t = Instant::now();
                let _ = twin_nf(ast);
                times.twin_nf.push(t.elapsed().as_micros());
            }
        } else {
            if wtn {
                let t = Instant::now();
                let _ = twin_nf(ast);
                times.twin_nf.push(t.elapsed().as_micros());
            }
            if wt {
                let t = Instant::now();
                twin_ok = twin_check(ast) && twin_ok;
                times.twin.push(t.elapsed().as_micros());
            }
            if wrn {
                let t = Instant::now();
                nodes = ref_nf(ast);
                times.ref_nf.push(t.elapsed().as_micros());
            }
            if wr {
                let t = Instant::now();
                ref_ok = ref_check(ast) && ref_ok;
                times.ref_.push(t.elapsed().as_micros());
            }
        }
    }
    let _ = (case, size, bytes, decls);
    (ref_ok, twin_ok, nodes)
}

fn print_case(
    layer: &str,
    case: &str,
    size: &str,
    bytes: usize,
    decls: usize,
    t: &Times,
    ref_ok: bool,
    twin_ok: bool,
    nodes: u64,
) {
    let (rmin, rmed) = Times::stat(&t.ref_);
    let (rnmin, rnmed) = Times::stat(&t.ref_nf);
    let (tmin, tmed) = Times::stat(&t.twin);
    let (tnmin, tnmed) = Times::stat(&t.twin_nf);
    println!(
        "CASE,{layer},{case},{size},{bytes},{decls},{rmin},{rmed},{rnmin},{rnmed},{tmin},{tmed},{tnmin},{tnmed},{},{},{}",
        ref_ok as u8, twin_ok as u8, nodes
    );
}

// ── 各层驱动 ────────────────────────────────────────────────────────────────

fn bench_l07(cli: &Cli) {
    println!("== layer: L07 ==");
    for spec in cases::specs_for(cases::Family::L07) {
        if !cases::case_wanted(&cli.case, spec.name) {
            continue;
        }
        for size in cases::sizes_for(&cli.sizes, spec) {
            let Ok(src) = cases::source(cases::Family::L07, spec.name, size) else {
                println!("SKIP,L07,{},{size},reason=unsupported", spec.name);
                continue;
            };
            let Ok(pre) =
                std::panic::catch_unwind(AssertUnwindSafe(|| L07_sum_type::preprocess(&src)))
            else {
                println!("SKIP,L07,{},{size},reason=preprocess_panic", spec.name);
                continue;
            };
            let parsed = std::panic::catch_unwind(AssertUnwindSafe(|| {
                L07_sum_type::parser::parser(&pre, 0).ok()
            }));
            let Some(decls) = parsed.ok().flatten() else {
                println!("SKIP,L07,{},{size},reason=parse_fail", spec.name);
                continue;
            };
            let n = decls.len();
            if let Some(dir) = &cli.dump_dir {
                let _ = dump(dir, "L07", spec.name, size, &src);
            }
            if cli.validate {
                println!(
                    "PASS,L07,{},{size},bytes={},decls={}",
                    spec.name,
                    src.len(),
                    n
                );
                continue;
            }
            let mut t = Times::default();
            let gated = std::panic::catch_unwind(AssertUnwindSafe(|| {
                measure(
                    spec.name,
                    size,
                    src.len(),
                    n,
                    &decls,
                    cli,
                    |a| L07_sum_type::bench_check(a),
                    |a| L07_sum_type::bench_check_nf(a),
                    |a| {
                        let mut tt = L07_sum_type::bump_spine_iter::Tycker::new();
                        tt.bench_check(a)
                    },
                    |a| {
                        let mut tt = L07_sum_type::bump_spine_iter::Tycker::new();
                        tt.bench_check_nf(a)
                    },
                    &mut t,
                )
            }));
            match gated {
                Ok((ref_ok, twin_ok, nodes)) => {
                    if !ref_ok {
                        println!("SKIP,L07,{},{size},reason=ref_check_fail", spec.name);
                        continue;
                    }
                    print_case(
                        "L07",
                        spec.name,
                        size,
                        src.len(),
                        n,
                        &t,
                        ref_ok,
                        twin_ok,
                        nodes,
                    );
                }
                Err(_) => println!("SKIP,L07,{},{size},reason=panic", spec.name),
            }
        }
    }
}

fn bench_l08(cli: &Cli) {
    println!("== layer: L08 ==");
    for spec in cases::specs_for(cases::Family::L08) {
        if !cases::case_wanted(&cli.case, spec.name) {
            continue;
        }
        for size in cases::sizes_for(&cli.sizes, spec) {
            let Ok(src) = cases::source(cases::Family::L08, spec.name, size) else {
                println!("SKIP,L08,{},{size},reason=unsupported", spec.name);
                continue;
            };
            let Ok(pre) =
                std::panic::catch_unwind(AssertUnwindSafe(|| L08_product_type::preprocess(&src)))
            else {
                println!("SKIP,L08,{},{size},reason=preprocess_panic", spec.name);
                continue;
            };
            let parsed = std::panic::catch_unwind(AssertUnwindSafe(|| {
                L08_product_type::parser::parser(&pre, 0).ok()
            }));
            let Some(decls) = parsed.ok().flatten() else {
                println!("SKIP,L08,{},{size},reason=parse_fail", spec.name);
                continue;
            };
            let n = decls.len();
            if let Some(dir) = &cli.dump_dir {
                let _ = dump(dir, "L08", spec.name, size, &src);
            }
            if cli.validate {
                println!(
                    "PASS,L08,{},{size},bytes={},decls={}",
                    spec.name,
                    src.len(),
                    n
                );
                continue;
            }
            let mut t = Times::default();
            let gated = std::panic::catch_unwind(AssertUnwindSafe(|| {
                measure(
                    spec.name,
                    size,
                    src.len(),
                    n,
                    &decls,
                    cli,
                    |a| L08_product_type::bench_check(a),
                    |a| L08_product_type::bench_check_nf(a),
                    |a| {
                        let mut tt = L08_product_type::bump_spine_iter::Tycker::new();
                        tt.bench_check(a)
                    },
                    |a| {
                        let mut tt = L08_product_type::bump_spine_iter::Tycker::new();
                        tt.bench_check_nf(a)
                    },
                    &mut t,
                )
            }));
            match gated {
                Ok((ref_ok, twin_ok, nodes)) => {
                    if !ref_ok {
                        println!("SKIP,L08,{},{size},reason=ref_check_fail", spec.name);
                        continue;
                    }
                    print_case(
                        "L08",
                        spec.name,
                        size,
                        src.len(),
                        n,
                        &t,
                        ref_ok,
                        twin_ok,
                        nodes,
                    );
                }
                Err(_) => println!("SKIP,L08,{},{size},reason=panic", spec.name),
            }
        }
    }
}

fn bench_l09(cli: &Cli) {
    println!("== layer: L09 ==");
    for spec in cases::specs_for(cases::Family::L09) {
        if !cases::case_wanted(&cli.case, spec.name) {
            continue;
        }
        for size in cases::sizes_for(&cli.sizes, spec) {
            let Ok(src) = cases::source(cases::Family::L09, spec.name, size) else {
                println!("SKIP,L09,{},{size},reason=unsupported", spec.name);
                continue;
            };
            let parsed = std::panic::catch_unwind(AssertUnwindSafe(|| {
                L09_mltt::bump_spine_iter::parse(&src, 0).ok()
            }));
            let Some(decls) = parsed.ok().flatten() else {
                println!("SKIP,L09,{},{size},reason=parse_fail", spec.name);
                continue;
            };
            let n = decls.len();
            if let Some(dir) = &cli.dump_dir {
                let _ = dump(dir, "L09", spec.name, size, &src);
            }
            if cli.validate {
                println!(
                    "PASS,L09,{},{size},bytes={},decls={}",
                    spec.name,
                    src.len(),
                    n
                );
                continue;
            }
            let mut t = Times::default();
            let gated = std::panic::catch_unwind(AssertUnwindSafe(|| {
                measure(
                    spec.name,
                    size,
                    src.len(),
                    n,
                    &decls,
                    cli,
                    |a| L09_mltt::bench_check(a),
                    |a| L09_mltt::bench_check_nf(a),
                    |a| {
                        let mut tt = L09_mltt::bump_spine_iter::Tycker::new();
                        tt.bench_check(a)
                    },
                    |a| {
                        let mut tt = L09_mltt::bump_spine_iter::Tycker::new();
                        tt.bench_check_nf(a)
                    },
                    &mut t,
                )
            }));
            match gated {
                Ok((ref_ok, twin_ok, nodes)) => {
                    if !ref_ok {
                        println!("SKIP,L09,{},{size},reason=ref_check_fail", spec.name);
                        continue;
                    }
                    print_case(
                        "L09",
                        spec.name,
                        size,
                        src.len(),
                        n,
                        &t,
                        ref_ok,
                        twin_ok,
                        nodes,
                    );
                }
                Err(_) => println!("SKIP,L09,{},{size},reason=panic", spec.name),
            }
        }
    }
}

fn bench_l10(cli: &Cli) {
    println!("== layer: L10 ==");
    for spec in cases::specs_for(cases::Family::L10) {
        if !cases::case_wanted(&cli.case, spec.name) {
            continue;
        }
        for size in cases::sizes_for(&cli.sizes, spec) {
            let Ok(src) = cases::source(cases::Family::L10, spec.name, size) else {
                println!("SKIP,L10,{},{size},reason=unsupported", spec.name);
                continue;
            };
            let parsed = std::panic::catch_unwind(AssertUnwindSafe(|| {
                L10_typeclass::bump_spine_iter::parse(&src, 0).ok()
            }));
            let Some(decls) = parsed.ok().flatten() else {
                println!("SKIP,L10,{},{size},reason=parse_fail", spec.name);
                continue;
            };
            let n = decls.len();
            if let Some(dir) = &cli.dump_dir {
                let _ = dump(dir, "L10", spec.name, size, &src);
            }
            if cli.validate {
                println!(
                    "PASS,L10,{},{size},bytes={},decls={}",
                    spec.name,
                    src.len(),
                    n
                );
                continue;
            }
            let mut t = Times::default();
            let gated = std::panic::catch_unwind(AssertUnwindSafe(|| {
                measure(
                    spec.name,
                    size,
                    src.len(),
                    n,
                    &decls,
                    cli,
                    |a| L10_typeclass::bench_check(a),
                    |a| L10_typeclass::bench_check_nf(a),
                    |a| {
                        let mut tt = L10_typeclass::bump_spine_iter::Tycker::new();
                        tt.bench_check(a)
                    },
                    |a| {
                        let mut tt = L10_typeclass::bump_spine_iter::Tycker::new();
                        tt.bench_check_nf(a)
                    },
                    &mut t,
                )
            }));
            match gated {
                Ok((ref_ok, twin_ok, nodes)) => {
                    if !ref_ok {
                        println!("SKIP,L10,{},{size},reason=ref_check_fail", spec.name);
                        continue;
                    }
                    print_case(
                        "L10",
                        spec.name,
                        size,
                        src.len(),
                        n,
                        &t,
                        ref_ok,
                        twin_ok,
                        nodes,
                    );
                }
                Err(_) => println!("SKIP,L10,{},{size},reason=panic", spec.name),
            }
        }
    }
}

fn dump(dir: &str, layer: &str, case: &str, size: &str, src: &str) -> std::io::Result<()> {
    let p = std::path::Path::new(dir).join(layer);
    std::fs::create_dir_all(&p)?;
    std::fs::write(p.join(format!("{case}__{size}.typort")), src)
}

fn run(cli: Cli) {
    let layers: Vec<&str> = match cli.layer.as_str() {
        "all" => vec!["L07", "L08", "L09", "L10"],
        "L07" | "L08" | "L09" | "L10" => vec![cli.layer.as_str()],
        other => {
            eprintln!("unknown layer: {other} (expect L07..L10 or all)");
            std::process::exit(2);
        }
    };
    for layer in layers {
        match layer {
            "L07" => bench_l07(&cli),
            "L08" => bench_l08(&cli),
            "L09" => bench_l09(&cli),
            "L10" => bench_l10(&cli),
            _ => unreachable!(),
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("SMALLTTBENCH_STACK_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1024);
    std::thread::Builder::new()
        .stack_size(stack_mb << 20)
        .spawn(move || run(cli))
        .unwrap()
        .join()
        .unwrap();
}
