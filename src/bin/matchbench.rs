//! matchbench —— 多分支多层次 match 在 L07–L13 七章上的**耗时**基准。
//!
//! 为什么单独做一个 bin：现有 `realbench` 只覆盖 L07–L12，`l13bench` 只做
//! L13 的参考版 vs 孪生，`l06l13mem` 只量内存。本 bin 用**同一份源**喂全部
//! 七章，直接对照「同一负载在不同章节实现上的挂钟时间」。
//!
//! 用法：
//!   cargo run --release --bin matchbench -- --depth 4 --copies 4 --width 8
//!   cargo run --release --bin matchbench -- --chapter L13 --reps 3
//!   cargo run --release --bin matchbench -- --sweep
//!
//! 输出 CSV 行：`RESULT,<chapter>,<depth>,<copies>,<width>,<bytes>,<ms>,<ok>`

#![allow(dead_code)]

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
#[path = "../L13_namespace/mod.rs"]
mod L13_namespace;

#[path = "matchbench_src.rs"]
mod gen_src;

use clap::Parser;
use std::time::Instant;

/// 递归层数上限。级联每层都会在引擎里展开一次，太深会让参考版爆栈。
const MAX_DEPTH: u32 = 12;

#[derive(Parser)]
#[command(
    name = "matchbench",
    about = "多分支多层次 match：L07-L13 同源耗时对照"
)]
struct Cli {
    /// 章节（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    chapter: String,

    /// 单条级联的嵌套层数（1..=12）
    #[arg(long, default_value_t = 4)]
    depth: u32,

    /// 级联条数
    #[arg(long, default_value_t = 4)]
    copies: u32,

    /// 叶子 Wide 的构造子数
    #[arg(long, default_value_t = 8)]
    width: u32,

    /// 每档重复次数（取最小值，抑制抖动）
    #[arg(long, default_value_t = 3)]
    reps: usize,

    /// 跑 depth 1..=8 的完整扫描（覆盖 depth/copies/width 三个轴）
    #[arg(long)]
    sweep: bool,
}

/// 一个章节的跑法：返回 (是否成功, 毫秒)。
macro_rules! run_chapter {
    ($ch:ident, $src:expr, $reps:expr) => {{
        let mut best_ms = f64::INFINITY;
        let mut ok = false;
        for _ in 0..$reps {
            let t0 = Instant::now();
            ok = $ch::run(&$src, 0).is_ok();
            let ms = t0.elapsed().as_secs_f64() * 1000.0;
            if ms < best_ms {
                best_ms = ms;
            }
        }
        (ok, best_ms)
    }};
}

fn chapters(cli: &Cli) -> Vec<&'static str> {
    match cli.chapter.as_str() {
        "all" => vec!["L07", "L08", "L09", "L10", "L11", "L12", "L13"],
        "L07" => vec!["L07"],
        "L08" => vec!["L08"],
        "L09" => vec!["L09"],
        "L10" => vec!["L10"],
        "L11" => vec!["L11"],
        "L12" => vec!["L12"],
        "L13" => vec!["L13"],
        other => {
            eprintln!("unknown chapter: {other} (expect L07..L13 or all)");
            std::process::exit(2);
        }
    }
}

fn main() {
    let cli = Cli::parse();

    let mut cases: Vec<(u32, u32, u32)> = Vec::new();
    if cli.sweep {
        for depth in 1..=8u32 {
            for width in [2u32, 8, 32] {
                cases.push((depth, cli.copies, width));
            }
        }
    } else {
        if cli.depth < 1 || cli.depth > MAX_DEPTH {
            eprintln!("depth must be 1..={MAX_DEPTH}");
            std::process::exit(2);
        }
        cases.push((cli.depth, cli.copies, cli.width));
    }

    let chs = chapters(&cli);
    println!("# matchbench: chapters={chs:?} reps={}", cli.reps);

    for (depth, copies, width) in cases {
        let src = gen_src::match_cascade_src(depth, copies, width);
        for ch in &chs {
            let (ok, ms) = match *ch {
                "L07" => run_chapter!(L07_sum_type, src, cli.reps),
                "L08" => run_chapter!(L08_product_type, src, cli.reps),
                "L09" => run_chapter!(L09_mltt, src, cli.reps),
                "L10" => run_chapter!(L10_typeclass, src, cli.reps),
                "L11" => run_chapter!(L11_macro, src, cli.reps),
                "L12" => run_chapter!(L12_canonical, src, cli.reps),
                "L13" => run_chapter!(L13_namespace, src, cli.reps),
                _ => unreachable!(),
            };
            println!(
                "RESULT,{ch},{depth},{copies},{width},{},{ms:.3},{ok}",
                src.len()
            );
        }
    }
}
