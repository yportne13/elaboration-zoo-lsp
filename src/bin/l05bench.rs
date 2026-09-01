//! L05 类型检查器基准：参考版（Box/List）vs `bump_spine_iter` 移植版
//! （L04 冠军配方 + pruning 的 typed-meta/剪枝机制）的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/parser_lib.rs` 和
//! `src/L05_pruning/`（L05 的基准因此不关心其余各层的编译状态）。
//!
//! 负载族（`--workload`）：
//! - `church`：church 2^(k+1) 的 check + nf（L02/L03/L04 同款源）。
//! - `implicit`（L04 同款）：`id p_{i-1}` 链——插入 meta 类型恒 U，走
//!   `fresh_meta` 的 tag3/5 快捷（验证 typed-meta 不劣化 implicit 近线性）。
//! - `prune`：**L05 特色**——每层 `m_i : (A)(B) -> U -> U -> U = _` 的洞类型
//!   telescope + `m_i a a` 的非线性 spine（invert 掩码 + prune_ty 验证 + solve），
//!   类型闭型沿增长的 define 链构造（参考版逐层重 eval，快路径在此省掉）。
//! - `conv` / `conv_dup` / `chain` / `solve` / `dup` / `dup_deep`：同 L04。
//!
//! 实现行：`basic`（参考版）、`fast` / `fast_ss`（bump_spine_iter 一次性 /
//! 稳态）、`fast_memo`（quote 记忆化口径）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l05bench [--max-k 15] [--rounds 5] [--only basic,fast]
//!                                     [--workload church|implicit|prune|conv|conv_dup|chain|solve|dup|dup_deep|all]
//! ```

#![feature(pattern)]
#![allow(dead_code)]

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;

#[path = "../L05_pruning/mod.rs"]
mod L05_pruning;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L05_pruning::bump_spine_iter::{
    chain_src, church_src, conv_dup_src, conv_src, dup_deep_src, dup_src, implicit_src,
    prune_src, solve_src, Tycker,
};
use L05_pruning::parser::parser;

#[derive(Parser)]
#[command(
    name = "l05bench",
    about = "L05 类型检查器基准：pruning/非线性求解负载下参考版 vs bump_spine_iter 版"
)]
struct Cli {
    /// church 数 = 2^(k+1)，k 从 9 起翻倍到 max-k
    #[arg(long, default_value_t = 15)]
    max_k: u32,

    /// 每实现每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定实现（逗号分隔：basic,fast,fast_ss,fast_memo）
    #[arg(long)]
    only: Option<String>,

    /// 负载族：church（check+nf，默认）| implicit | prune | conv | conv_dup | chain | solve | dup | dup_deep | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L05_STACK_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(128);
    std::thread::Builder::new()
        .stack_size(stack_mb << 20)
        .spawn(move || run(cli))
        .unwrap()
        .join()
        .unwrap();
}

fn run(cli: Cli) {
    let want = |name: &str| {
        cli.only
            .as_deref()
            .map(|s| s.split(',').any(|x| x.trim() == name))
            .unwrap_or(true)
    };
    let workloads: &[&str] = match cli.workload.as_str() {
        "church" => &["church"],
        "implicit" => &["implicit"],
        "prune" => &["prune"],
        "conv" => &["conv"],
        "conv_dup" => &["conv_dup"],
        "chain" => &["chain"],
        "solve" => &["solve"],
        "dup" => &["dup"],
        "dup_deep" => &["dup_deep"],
        _ => &[
            "church",
            "implicit",
            "prune",
            "conv",
            "conv_dup",
            "chain",
            "solve",
            "dup",
            "dup_deep",
        ],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // implicit/prune/conv/conv_dup/chain/solve 只走 check（无 quote）；
        // church/dup/dup_deep 走 check + nf
        let nf_workload = matches!(*workload, "church" | "dup" | "dup_deep");
        for k in 9..=cli.max_k {
            let n = 1u64 << (k + 1);
            let src = match *workload {
                "church" => church_src(k),
                "implicit" => implicit_src(k),
                "prune" => prune_src(k),
                "conv" => conv_src(k),
                "conv_dup" => conv_dup_src(k),
                "chain" => chain_src(k),
                "solve" => solve_src(k),
                "dup" => dup_src(k),
                _ => dup_deep_src(k),
            };
            // 计时外：解析 + 正确性断言
            let Some(raw) = parser(&src, 0) else {
                eprintln!("parse failed at k={k}");
                continue;
            };
            let expect_nodes = match *workload {
                "church" => 2 * n + 4,
                "dup" => 4 * n + 12,
                "dup_deep" => 8 * n + 28,
                _ => 0,
            };
            if nf_workload {
                let mut t = Tycker::new();
                let nodes = t.bench_check_nf(&raw);
                assert_eq!(nodes, expect_nodes, "fast nf 节点数不符 k={k} ({workload})");
                let mut t2 = Tycker::new();
                assert!(t2.bench_check(&raw));
                if *workload != "church" {
                    let mut t3 = Tycker::new();
                    assert_eq!(
                        t3.bench_check_nf_memo(&raw),
                        expect_nodes,
                        "fast_memo nf 节点数不符 k={k} ({workload})"
                    );
                }
            } else {
                let mut t = Tycker::new();
                assert!(t.bench_check(&raw), "check-only 负载未通过 k={k}");
            };

            let mut rows: Vec<(&str, u128, u128)> = Vec::new();

            if want("fast_ss") {
                let mut ts = Vec::new();
                let mut tycker = Tycker::new();
                // 预热 1 次
                if nf_workload {
                    assert_eq!(tycker.bench_check_nf(&raw), expect_nodes);
                } else {
                    assert!(tycker.bench_check(&raw));
                }
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    if nf_workload {
                        tycker.bench_check_nf(&raw);
                    } else {
                        tycker.bench_check(&raw);
                    }
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast_ss", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            if want("fast") {
                let mut ts = Vec::new();
                for _ in 0..cli.rounds {
                    let mut tycker = Tycker::new(); // 一次性口径：每轮新建
                    let start = Instant::now();
                    if nf_workload {
                        tycker.bench_check_nf(&raw);
                    } else {
                        tycker.bench_check(&raw);
                    }
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            // quote 记忆化口径（dup 负载的主对比行；其余无 quote 不出赛）
            if want("fast_memo") && nf_workload {
                let mut ts = Vec::new();
                for _ in 0..cli.rounds {
                    let mut tycker = Tycker::new();
                    let start = Instant::now();
                    tycker.bench_check_nf_memo(&raw);
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast_memo", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            if want("basic") {
                let mut ts = Vec::new();
                // 预热 1 次（同时验证通过）
                L05_pruning::bench_check(&raw);
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    if nf_workload {
                        L05_pruning::bench_check_nf(&raw);
                    } else {
                        L05_pruning::bench_check(&raw);
                    }
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("basic", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            let fastest = rows.iter().map(|r| r.1).min().unwrap();
            print!("k={k:<3} n={n:<8}");
            for (name, min, med) in &rows {
                let star = if *min == fastest { "*" } else { " " };
                print!(
                    " {name}={:>6}.{:03}ms{:>1}/{:>6}.{:03}",
                    min / 1000,
                    min % 1000,
                    star,
                    med / 1000,
                    med % 1000
                );
            }
            println!();
        }
    }
}
