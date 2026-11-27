//! workbench —— L07–L13 在**非 match 语料**上的同源耗时基准。
//!
//! 为什么单独做一个 bin：`matchbench` 只覆盖 match 负载，`l07bench`/`realbench`
//! 等都要 `--features twins`（孪生引擎当前不编译）。本 bin 只 `#[path]` 直编七章
//! 的参考版，用同一份源喂全部章节，直接对照挂钟时间。
//!
//! 用法：
//!   cargo run --release --bin workbench -- --workload all --k 10 --reps 3
//!   cargo run --release --bin workbench -- --chapter L13 --workload enum
//!
//! 输出 CSV 行：`RESULT,<workload>,<chapter>,<k>,<bytes>,<ms>,<ok>`

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

#[path = "../workbench_src.rs"]
mod gen_src;

use clap::Parser;
use std::time::Instant;

#[derive(Parser)]
#[command(name = "workbench", about = "非 match 语料：L07-L13 同源耗时对照")]
struct Cli {
    /// 章节（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    chapter: String,

    /// 负载：church | strchain | global | enum | natadd | all
    #[arg(long, default_value = "all")]
    workload: String,

    /// 规模（各负载的 k；enum 用固定源，忽略）
    #[arg(long, default_value_t = 10)]
    k: u32,

    /// 每档重复次数（取最小值）
    #[arg(long, default_value_t = 3)]
    reps: usize,

    /// 打印各章 Val/Tm 字节数
    #[arg(long)]
    layout: bool,
}

macro_rules! run_chapter {
    ($ch:ident, $src:expr, $reps:expr) => {{
        let mut best_ms = f64::INFINITY;
        let mut ok = false;
        for _ in 0..$reps {
            let t0 = Instant::now();
            ok = $ch::run(&$src, 0).is_ok();
            let ms = t0.elapsed().as_secs_f64() * 1000.0;
            if ms < best_ms { best_ms = ms; }
        }
        (ok, best_ms)
    }};
}

fn chapters(cli: &Cli) -> Vec<&'static str> {
    match cli.chapter.as_str() {
        "all" => vec!["L07", "L08", "L09", "L10", "L11", "L12", "L13"],
        "L07" => vec!["L07"], "L08" => vec!["L08"], "L09" => vec!["L09"],
        "L10" => vec!["L10"], "L11" => vec!["L11"], "L12" => vec!["L12"],
        "L13" => vec!["L13"],
        other => { eprintln!("unknown chapter: {other}"); std::process::exit(2); }
    }
}

fn main() {
    let cli = Cli::parse();
    let chs = chapters(&cli);
    println!("# workbench: chapters={chs:?} k={} reps={}", cli.k, cli.reps);

    if cli.layout {
        println!("LAYOUT,chapter,val_bytes,tm_bytes");
        for ch in &chs {
            let (v, t) = match *ch {
                "L07" => (std::mem::size_of::<L07_sum_type::Val>(), std::mem::size_of::<L07_sum_type::Tm>()),
                "L08" => (std::mem::size_of::<L08_product_type::Val>(), std::mem::size_of::<L08_product_type::Tm>()),
                "L09" => (std::mem::size_of::<L09_mltt::Val>(), std::mem::size_of::<L09_mltt::Tm>()),
                "L10" => (std::mem::size_of::<L10_typeclass::Val>(), std::mem::size_of::<L10_typeclass::Tm>()),
                "L11" => (std::mem::size_of::<L11_macro::Val>(), std::mem::size_of::<L11_macro::Tm>()),
                "L12" => (std::mem::size_of::<L12_canonical::Val>(), std::mem::size_of::<L12_canonical::Tm>()),
                "L13" => (std::mem::size_of::<L13_namespace::Val>(), std::mem::size_of::<L13_namespace::Tm>()),
                _ => unreachable!(),
            };
            println!("LAYOUT,{ch},{v},{t}");
        }
    }

    let workloads: Vec<&'static str> = match cli.workload.as_str() {
        "all" => vec!["church", "strchain", "global", "enum", "natadd"],
        "church" => vec!["church"],
        "strchain" => vec!["strchain"],
        "global" => vec!["global"],
        "enum" => vec!["enum"],
        "natadd" => vec!["natadd"],
        other => { eprintln!("unknown workload: {other}"); std::process::exit(2); }
    };

    for w in workloads {
        for ch in &chs {
            // globals 族的类型注解随层变化：L07/L08 只认 `U`，L09+ 只认 `Type 0`。
            // 同一族内各层用的源因此不同，但**每层各自与自己的改前基线比**，
            // 跨层绝对值不可直接横比（文档里按层标注）。
            let src = if w == "global" {
                let ty = if *ch == "L07" || *ch == "L08" { "U" } else { "Type 0" };
                gen_src::globals_src_with(cli.k, ty)
            } else {
                gen_src::make_src(w, cli.k)
            };
            // L13 参考版不支持 `change_mutable` 族（该 prim 只在 L13 孪生引擎与
            // L07–L12 参考版里实现），故 global 族跳过 L13——其耗时对 L13 无意义。
            if w == "global" && *ch == "L13" {
                println!("SKIP,{w},{ch},{}", cli.k);
                continue;
            }
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
            println!("RESULT,{w},{ch},{},{},{ms:.3},{ok}", cli.k, src.len());
        }
    }
}