//! L06 类型检查器基准：参考版（Box/List + decl 表 + builtin prim）vs
//! `bump_spine_iter` 移植版（L05 冠军配方 + string 层的 Literal/Decl/prim
//! 机制）的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/parser_lib.rs` 和
//! `src/L06_string/`（L06 的基准因此不关心其余各层的编译状态）。
//!
//! 负载族（`--workload`，全部为 L06 顶层 decl 语法——无尾表达式行、def
//! 无分号，parser 只取 decl 前缀）：
//! - `church`：church 2^(k+1) 的 check + nf（L02-L05 同款源；nf 节点数
//!   = 2n + 4）。
//! - `implicit`（L04 同款）：`id p_{i-1}` 链——插入 meta 类型恒 U，走
//!   `fresh_meta` 的 tag3/5 快捷。
//! - `prune`（L05 特色）：每层 `m_i : (A)(B) -> U -> U -> U = _` 的洞类型
//!   telescope + `m_i a a` 的非线性 spine（invert 掩码 + prune_ty 验证 +
//!   solve）。
//! - `solve`：`Eq _ p_k p_k = refl`——rename 沿 church 展开的整条 neutral
//!   链走。
//! - `strchain`（**L06 特色**）：每层 `string_concat s_{i-1} "x"`——define
//!   链 + decl 表增长 + 每层一次 builtin prim 触发（末值 = 长 n 的字面量，
//!   nf 节点数 = 1）。
//!
//! 实现行：`basic`（参考版）、`fast` / `fast_ss`（bump_spine_iter 一次性 /
//! 稳态）、`fast_memo`（quote 记忆化口径）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l06bench [--max-k 13] [--rounds 5] [--only basic,fast]
//!                                     [--workload church|implicit|prune|solve|strchain|all]
//! ```

#![feature(pattern)]
#![allow(dead_code)]

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;

#[path = "../L06_string/mod.rs"]
mod L06_string;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L06_string::bump_spine_iter::{
    church_src, implicit_src, prune_src, solve_src, strchain_src, Tycker,
};
use L06_string::parser::parser;

#[derive(Parser)]
#[command(
    name = "l06bench",
    about = "L06 类型检查器基准：string/decl 表/builtin prim 负载下参考版 vs bump_spine_iter 版"
)]
struct Cli {
    /// church 数 = 2^(k+1)，k 从 9 起翻倍到 max-k
    #[arg(long, default_value_t = 13)]
    max_k: u32,

    /// 每实现每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定实现（逗号分隔：basic,fast,fast_ss,fast_memo）
    #[arg(long)]
    only: Option<String>,

    /// 负载族：church（check+nf，默认）| implicit | prune | solve | strchain | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L06_STACK_MB")
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
        "solve" => &["solve"],
        "strchain" => &["strchain"],
        _ => &["church", "implicit", "prune", "solve", "strchain"],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // implicit/prune/solve 只走 check（无 quote）；church/strchain 走
        // check + nf。**implicit/prune 的参考版超线性**（L05 readme 同款：
        // 每 define 克隆 src_names + telescope 逐层重 eval，k=10 已 20s+），
        // 默认不排 basic（--only basic 可强制，自负超时）
        let nf_workload = matches!(*workload, "church" | "strchain");
        let basic_too_slow = matches!(*workload, "implicit" | "prune");
        for k in 9..=cli.max_k {
            let n = 1u64 << (k + 1);
            let src = match *workload {
                "church" => church_src(k),
                "implicit" => implicit_src(k),
                "prune" => prune_src(k),
                "solve" => solve_src(k),
                _ => strchain_src(k),
            };
            // 计时外：解析 + 正确性断言
            let Some(raw) = parser(&L06_string::preprocess(&src), 0) else {
                eprintln!("parse failed at k={k}");
                continue;
            };
            let expect_nodes = match *workload {
                "church" => 2 * n + 4,
                "strchain" => 1,
                _ => 0,
            };
            if nf_workload {
                let mut t = Tycker::new();
                let nodes = t.bench_check_nf(&raw);
                assert_eq!(nodes, expect_nodes, "fast nf 节点数不符 k={k} ({workload})");
                let mut t2 = Tycker::new();
                assert!(t2.bench_check(&raw));
                let mut t3 = Tycker::new();
                assert_eq!(
                    t3.bench_check_nf_memo(&raw),
                    expect_nodes,
                    "fast_memo nf 节点数不符 k={k} ({workload})"
                );
                // 参考版节点数同式（basic 的正确性即互检）
                assert_eq!(
                    L06_string::bench_check_nf(&raw),
                    expect_nodes,
                    "basic nf 节点数不符 k={k} ({workload})"
                );
            } else {
                let mut t = Tycker::new();
                assert!(t.bench_check(&raw), "check-only 负载未通过 k={k}");
                if !basic_too_slow {
                    assert!(
                        L06_string::bench_check(&raw),
                        "basic check-only 负载未通过 k={k}"
                    );
                }
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

            // quote 记忆化口径（有 quote 的负载才出赛）
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

            if want("basic") && !(basic_too_slow && cli.only.is_none()) {
                let mut ts = Vec::new();
                // 预热 1 次（同时验证通过）
                L06_string::bench_check(&raw);
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    if nf_workload {
                        L06_string::bench_check_nf(&raw);
                    } else {
                        L06_string::bench_check(&raw);
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
