//! L02 类型检查器基准：参考版（Box/List，L03 风格）vs `bump_spine_iter`
//! 移植版（L01 冠军配方）的一次性 / 稳态两种口径。
//!
//! 与 `typort`（语言服务器/编译器的总二进制）完全解耦：本 bin 不引用
//! `elaboration_zoo_lsp` 库，只通过 `#[path]` 直接编译 `src/list.rs`、
//! `src/parser_lib.rs` 和 `src/L02_tyck/`——L02 的基准因此不关心（也不被
//! 阻塞于）其余各层（L03…L13）的编译状态。
//!
//! 负载族（`--workload`）：
//! - `church`：church 2^(k+1)（k 次 ×2 翻倍的 let 链）的 check + nf
//!   （quote 强制整条 s-链，L01 church_pair 的 L02 对应物）。
//! - `conv`：同一 church 数之上的 `Eq Nat (add big zero) big = refl Nat big`
//!   ——check 内 beta-eta conv 强制两侧完整展开后结构比较。
//! - `conv_dup`：同一昂贵子对在类型多处重现——`Rel = \a b. (P : a -> U) ->
//!   P b -> P b -> P b`，`relRefl Nat p_k` 对 `Rel Nat (add p_k zero)` 的
//!   check 把 (p_k, add p_k zero) 这对比较 3 次（conv 判等记忆化的命中
//!   场景；`L02_NO_CONV_MEMO=1` 可消融）。
//! - `dup`：church 2^(k+1) 之上 `D p_k`（`D = \x f. f x x`），nf =
//!   `λf. f C C`——λ-binder 复制同一闭包值，quote 对它强制 **2 次**
//!   （L01 dup_pair 的 L02 对应物；call-by-need / quote 记忆化轴）。
//! - `dup_deep`：`D1 (D0 p_k)`，nf = `λf. f (λf'. f' C C) (λf'. f' C C)`
//!   ——C 被强制 **4 次**（复制层数翻倍，收益随层数指数增长）。
//!
//! 实现行：`basic`（参考版）、`fast` / `fast_ss`（bump_spine_iter 一次性 /
//! 稳态）、`fast_memo`（quote 记忆化口径；线性负载付哈希税，复制负载把
//! 2×/4× 重复强制塌缩回 1×；conv 无 quote 故不出赛）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l02bench [--max-k 15] [--rounds 5] [--only basic,fast]
//!                                     [--workload church|conv|conv_dup|dup|dup_deep|all]
//! ```

// parser_lib 的 `pmatch`/`is` 泛型约束 `Pattern` 是 nightly API（lib 同款
// feature；仓库依赖 nightly 工具链）。
#![feature(pattern)]
#![allow(dead_code)]

// 求值/quote/conv 全链路迭代化后深度无上限；参考版（Box/List 递归）在
// 大 k 段仍需要深栈，默认 128MB 留足余量（L01 l01bench 同款）。
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = MiMalloc;

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;

#[path = "../L02_tyck/mod.rs"]
mod L02_tyck;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L02_tyck::bump_spine_iter::{conv_dup_src, church_src, conv_src, dup_deep_src, dup_src, Tycker};
use L02_tyck::parser::parser;

#[derive(Parser)]
#[command(
    name = "l02bench",
    about = "L02 类型检查器基准：check(+nf) 负载下参考版 vs bump_spine_iter 版"
)]
struct Cli {
    /// church 数 = 2^(k+1)，k 从 9 起翻倍到 max-k
    #[arg(long, default_value_t = 15)]
    max_k: u32,

    /// 每实现每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定实现（逗号分隔：basic,fast,fast_ss）
    #[arg(long)]
    only: Option<String>,

    /// 负载族：church（check+nf，默认）| conv | conv_dup | dup | dup_deep | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L02_STACK_MB")
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
        "conv" => &["conv"],
        "conv_dup" => &["conv_dup"],
        "dup" => &["dup"],
        "dup_deep" => &["dup_deep"],
        _ => &["church", "conv", "conv_dup", "dup", "dup_deep"],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // conv/conv_dup 只走 check（无 quote）；church/dup/dup_deep 走 check + nf
        let nf_workload = matches!(*workload, "church" | "dup" | "dup_deep");
        for k in 9..=cli.max_k {
            let n = 1u64 << (k + 1);
            let src = match *workload {
                "church" => church_src(k),
                "conv" => conv_src(k),
                "conv_dup" => conv_dup_src(k),
                "dup" => dup_src(k),
                _ => dup_deep_src(k),
            };
            // 计时外：解析 + 正确性断言
            let Some(raw) = parser(&src, 0) else {
                eprintln!("parse failed at k={k}");
                continue;
            };
            // church：λ N s z. s^n z = 3 Lam + n App + (n+1) Var；
            // dup / dup_deep 的推导见 bump_spine_iter 的生成器注释
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
            } else {
                let mut t = Tycker::new();
                assert!(t.bench_check(&raw), "conv 负载未通过 k={k}");
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

            // quote 记忆化口径（dup 负载的主对比行；conv 无 quote 不出赛）
            if want("fast_memo") && nf_workload {
                // 计时外正确性：memo 口径节点数与普通口径一致（DAG 共享不改逐出现计数）
                let mut t = Tycker::new();
                assert_eq!(
                    t.bench_check_nf_memo(&raw),
                    expect_nodes,
                    "fast_memo nf 节点数不符 k={k} ({workload})"
                );
                let mut ts = Vec::new();
                for _ in 0..cli.rounds {
                    let mut tycker = Tycker::new(); // 一次性口径：每轮新建
                    let start = Instant::now();
                    tycker.bench_check_nf_memo(&raw);
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("fast_memo", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            if want("basic") {
                let mut ts = Vec::new();
                // 预热 1 次（同时验证通过）
                L02_tyck::bench_check(&raw);
                for _ in 0..cli.rounds {
                    let start = Instant::now();
                    if nf_workload {
                        L02_tyck::bench_check_nf(&raw);
                    } else {
                        L02_tyck::bench_check(&raw);
                    }
                    ts.push(start.elapsed().as_micros());
                }
                rows.push(("basic", *ts.iter().min().unwrap(), median(&mut ts)));
            }

            let fastest = rows.iter().map(|r| r.1).min().unwrap();
            print!("k={k:<3} n={n:<8}");
            for (name, min, med) in &rows {
                let star = if *min == fastest { "*" } else { " " };
                print!(" {name}={:>6}.{:03}ms{:>1}/{:>6}.{:03}", min / 1000, min % 1000, star, med / 1000, med % 1000);
            }
            println!();
        }
    }
}
