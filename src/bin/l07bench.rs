//! L07 类型检查器基准：参考版（Box/Val + decl 表 + builtin prim + 依赖
//! 模式匹配）vs `bump_spine_iter` 移植版的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/parser_lib.rs` 和
//! `src/L07_sum_type/`。
//!
//! 负载族（`--workload`）：
//! - `church`：church 2^(k+1) 的 check + nf（nf 节点数 = 2n + 4，与 L06
//!   同式）。
//! - `strchain`（L06 特色）：每层 `string_concat s_{i-1} "x"`——decl 表
//!   增长 + 每层一次 builtin prim 触发；末值 = 长 n 的字面量（nf 节点
//!   数 = 1）。
//! - `global`（L06 特色）：每层 `change_mutable "k" (s => string_concat
//!   s "x")`——mutable_map 读写 + β 应用 + 重入 prim 触发；末值 = U
//!   （nf 节点数 = 1）。
//! - `match`（**L07 特色**）：k+1 个自递归依赖 match def + 一次
//!   println——编译期特化合一 + 运行时首匹配 + 卡住 match 协同。
//! - `enum`（**L07 特色**）：多 enum + Vec 风格 GADT + 投影 + 索引等式
//!   + 递归 length（固定源，check + nf）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l07bench [--max-k 13] [--rounds 5] [--only basic,fast]
//!                                     [--workload church|strchain|global|match|enum|all]
//! ```

#![feature(pattern)]
#![allow(dead_code)]

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;

#[path = "../L07_sum_type/mod.rs"]
mod L07_sum_type;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L07_sum_type::bump_spine_iter::{
    church_src, enum_src, globals_src, match_src, strchain_src, Tycker,
};
use L07_sum_type::parser::parser;

#[derive(Parser)]
#[command(
    name = "l07bench",
    about = "L07 类型检查器基准：sum-type/依赖模式匹配负载下参考版 vs bump_spine_iter 版"
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

    /// 负载族：church（check+nf，默认）| strchain | global | match | enum | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L07_STACK_MB")
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
        "strchain" => &["strchain"],
        "global" => &["global"],
        "match" => &["match"],
        "enum" => &["enum"],
        _ => &["church", "strchain", "global", "match", "enum"],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // church/strchain/global/match 走 check + nf；enum 是固定源（check+nf
        // 一次）。**strchain/global 的参考版超线性**（L06 readme 同款：每
        // define 克隆 src_names/decl 表 + prim 链求值），默认不排 basic
        let nf_workload = matches!(*workload, "church" | "strchain" | "global" | "match");
        let basic_too_slow = matches!(*workload, "strchain" | "global");
        // match/enum 的节点数无闭式——以「快版 == 参考版」互检代替硬编码
        let closed_form = matches!(*workload, "church" | "strchain" | "global");

        let ks: Vec<u32> = if *workload == "enum" {
            vec![9] // enum 负载与 k 无关，只跑一行
        } else {
            (9..=cli.max_k).collect()
        };

        for k in ks {
            let n = 1u64 << (k + 1);
            let src = match *workload {
                "church" => church_src(k),
                "strchain" => strchain_src(k),
                "global" => globals_src(k),
                "match" => match_src(k),
                _ => enum_src(),
            };
            // 计时外：解析 + 正确性断言
            let Ok(raw) = parser(&L07_sum_type::preprocess(&src), 0) else {
                eprintln!("parse failed at k={k}");
                continue;
            };
            let expect_nodes = match *workload {
                "church" => 2 * n + 4,
                "strchain" | "global" => 1,
                _ => 0,
            };
            let mut t0 = Tycker::new();
            let fast_nodes = t0.bench_check_nf(&raw);
            if closed_form {
                assert_eq!(fast_nodes, expect_nodes, "fast nf 节点数不符 k={k} ({workload})");
            }
            let mut t1 = Tycker::new();
            assert!(t1.bench_check(&raw), "fast check-only 未通过 k={k}");
            if !closed_form {
                // match/enum：快版 vs 参考版节点数互检
                assert_eq!(
                    fast_nodes,
                    L07_sum_type::bench_check_nf(&raw),
                    "match/enum 节点数双实现不一致 k={k}"
                );
            } else {
                assert_eq!(
                    L07_sum_type::bench_check_nf(&raw),
                    expect_nodes,
                    "basic nf 节点数不符 k={k} ({workload})"
                );
            }
            drop(t0);
            drop(t1);

            let mut rows: Vec<(&str, u128, u128)> = Vec::new();

            if want("fast_ss") {
                let mut ts = Vec::new();
                let mut tycker = Tycker::new();
                // 预热 1 次
                assert_eq!(tycker.bench_check_nf(&raw), fast_nodes);
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    tycker.bench_check_nf(&raw);
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast_ss", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            if want("fast") {
                let mut ts = Vec::new();
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    // 一次性口径：每轮新建（Tycker::new 的 bump 预分配计入
                    // 计时——参考版 Infer::new 的建表同样在 bench_check 内）
                    let mut tycker = Tycker::new();
                    tycker.bench_check_nf(&raw);
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            // quote 记忆化口径（有 quote 的负载才出赛）
            if want("fast_memo") && nf_workload {
                let mut ts = Vec::new();
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    let mut tycker = Tycker::new(); // 同 fast：新建计入计时
                    tycker.bench_check_nf_memo(&raw);
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast_memo", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            if want("basic") && !(basic_too_slow && cli.only.is_none()) {
                let mut ts = Vec::new();
                // 预热 1 次（同时验证通过）
                L07_sum_type::bench_check_nf(&raw);
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    L07_sum_type::bench_check_nf(&raw);
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
