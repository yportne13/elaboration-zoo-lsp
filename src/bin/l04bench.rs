//! L04 类型检查器基准：参考版（Box/List）vs `bump_spine_iter` 移植版
//! （L03 冠军配方 + implicit args 的 icit 穿线与插入机制）的一次性 / 稳态
//! 两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/parser_lib.rs` 和
//! `src/L04_implicit/`（L04 的基准因此不关心其余各层的编译状态）。
//!
//! 负载族（`--workload`）：
//! - `church`：church 2^(k+1) 的 check + nf（L02/L03 同款源）。
//! - `implicit`：**L04 特色**——n = 2^(k+1) 条 let 链 `p_i = id p_{i-1}`
//!   （`id : {A : U} -> A -> A`）：每层触发一次隐式插入（`{A}` 补 meta）
//!   + 一次 `? := Nat` 求解——insert/insert_go/solve 与名字解析的主展示。
//! - `conv` / `conv_dup`：同 L03（转换检查 / 判等记忆化命中负载）。
//! - `chain`：名字解析负载（O(n²) vs 名字 map O(n)；大 k 段建议
//!   `--only fast`）。
//! - `solve`：`Eq _ p_k p_k = refl _ _` 的大解（rename 沿 church 链走）。
//! - `dup` / `dup_deep`：复制强制负载（quote 记忆化轴）。
//!
//! 实现行：`basic`（参考版）、`fast` / `fast_ss`（bump_spine_iter 一次性 /
//! 稳态）、`fast_memo`（quote 记忆化口径）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l04bench [--max-k 15] [--rounds 5] [--only basic,fast]
//!                                     [--workload church|implicit|conv|conv_dup|chain|solve|dup|dup_deep|all]
//! ```

#![feature(pattern)]
#![allow(dead_code)]

// 参考版（Box/List 递归）在大 k 段仍需要深栈，默认 128MB 留足余量。
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;

#[path = "../L04_implicit/mod.rs"]
mod L04_implicit;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L04_implicit::bump_spine_iter::{
    chain_src, church_src, conv_dup_src, conv_src, dup_deep_src, dup_src, implicit_src,
    solve_src, Tycker,
};
use L04_implicit::parser::parser;

#[derive(Parser)]
#[command(
    name = "l04bench",
    about = "L04 类型检查器基准：隐式插入/求解负载下参考版 vs bump_spine_iter 版"
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

    /// 负载族：church（check+nf，默认）| implicit | conv | conv_dup | chain | solve | dup | dup_deep | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L04_STACK_MB")
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
        "conv" => &["conv"],
        "conv_dup" => &["conv_dup"],
        "chain" => &["chain"],
        "solve" => &["solve"],
        "dup" => &["dup"],
        "dup_deep" => &["dup_deep"],
        _ => &[
            "church",
            "implicit",
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
        // conv/conv_dup/solve/implicit/chain 只走 check（无 quote）；
        // church/dup/dup_deep 走 check + nf
        let nf_workload = matches!(*workload, "church" | "dup" | "dup_deep");
        for k in 9..=cli.max_k {
            let n = 1u64 << (k + 1);
            let src = match *workload {
                "church" => church_src(k),
                "implicit" => implicit_src(k),
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
                L04_implicit::bench_check(&raw);
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    if nf_workload {
                        L04_implicit::bench_check_nf(&raw);
                    } else {
                        L04_implicit::bench_check(&raw);
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