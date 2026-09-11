//! L09 类型检查器基准：参考版（`Type N` 分层宇宙 + global 表引擎）vs
//! `bump_spine_iter` 移植版的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/bimap.rs`、`src/parser_lib*.rs`
//! 和 `src/L09_mltt/`（与 `tests/l09_fast_parity.rs` 同款）。
//!
//! 负载族（`--workload`）——L08 全家桶去掉 `global`（L09 builtin 只剩
//! `string_concat`，无可变全局）+ L09 宇宙特色负载：
//! - `church`：church 2^(k+1) 的 check + nf（nf 节点数 = 2n + 4，与
//!   L06-L08 同式；`U` 已改为 `Type 0/1`，裸 `U` 在 L09 是普通变量名）。
//! - `strchain`（L06 特色）：每层 `string_concat s_{i-1} "x"`——每层一次
//!   builtin prim 触发；末值 = 长 n 的字面量（nf 节点数 = 1）。
//! - `match`（L07 特色）：k+1 个自递归依赖 match def + 一次 println。
//! - `enum`（L07 特色）：多 enum + Vec 风格 GADT + 投影 + 索引等式 +
//!   递归 length（固定源，check + nf 一次）。
//! - `struct`（L08 特色，L09 语义子集）：两层嵌套 struct + 2^(k+1) 层
//!   浅值投影 def 链（末值 = zero，nf 节点数 = 2）。
//! - `universe`（**L09 特色**）：固定宇宙塔（`Type 1 = Type 0`、
//!   `Type 2 = Type 1 -> Type 0`、高宇宙 enum `HighLvl`，与
//!   `tests/l09_fast_parity.rs::parity_universe_levels` 同款形态）+
//!   2^(k+1) 层 `def c{i} : Type 2 = Type 1 -> Type 0` def 链——每层
//!   一次 `check_universe` 的 Pi 规则判定 + global 登记；末值 nf 节点数
//!   无闭式，以「快版 == 参考版」互检代替硬编码。
//!
//! nf 节点数口径：check 全部 decl 后取**最后一个 def** 的登记值空层级
//! 引读并数节点（`Tycker::bench_check_nf`，quote 无记忆化）；`fast_memo`
//! 行为 quote 记忆化口径。match/enum/universe 无闭式——以双实现互检代替。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l09bench [--max-k 13] [--rounds 5]
//!                                     [--only basic,fast]
//!                                     [--workload church|strchain|match|enum|struct|universe|all]
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

#[path = "../L09_mltt/mod.rs"]
mod L09_mltt;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L09_mltt::bump_spine_iter::{
    church_src, enum_src, match_src, parse, strchain_src, struct_src, Tycker,
};

#[derive(Parser)]
#[command(
    name = "l09bench",
    about = "L09 类型检查器基准：MLTT 分层宇宙负载下参考版 vs bump_spine_iter 版"
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

    /// 负载族：church（check+nf，默认）| strchain | match | enum | struct | universe | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L09_STACK_MB")
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

/// universe 负载源（**L09 特色**，形态取自 tests/l09_fast_parity.rs 的
/// parity_universe_levels 已验证用例；方括号类型参数是隐式实参——显式
/// 方括号应用语法不存在，见 tests/l11_fast_parity.rs 的 icit 失配用例）。
fn universe_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n\
         def t0 : Type 1 = Type 0\n\n\
         def t1 : Type 2 = Type 1 -> Type 0\n\n\
         enum HighLvl[A] {\n    case1(a: A)\n    case2(a: t1)\n}\n\n\
         def hl : HighLvl[Nat] = case1 zero\n\n\
         def c0 : Type 2 = Type 1 -> Type 0\n",
    );
    for i in 1..n {
        s += &format!("def c{i} : Type 2 = Type 1 -> Type 0\n");
    }
    s
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
        "match" => &["match"],
        "enum" => &["enum"],
        "struct" => &["struct"],
        "universe" => &["universe"],
        _ => &["church", "strchain", "match", "enum", "struct", "universe"],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // church/strchain/match 走 check + nf；enum/universe 是固定源或
        // 轻末值（check+nf 一次）。**strchain/struct 的参考版超线性**
        // （L06 readme 同款），默认不排 basic
        let nf_workload = matches!(*workload, "church" | "strchain" | "match" | "universe");
        let basic_too_slow = matches!(*workload, "strchain" | "struct");
        // church/strchain/struct 的节点数有闭式（孪生生成器注释 +
        // tests/l09_fast_parity.rs 钉值）；match/enum/universe 以
        // 「快版 == 参考版」互检代替硬编码
        let closed_form = matches!(*workload, "church" | "strchain" | "struct");

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
                "match" => match_src(k),
                "struct" => struct_src(k),
                "universe" => universe_src(k),
                _ => enum_src(),
            };
            // 计时外：解析（共用参考版 parser，快版 `parse` 同时可见私有
            // parser 模块）+ 正确性断言
            let Ok(decls) = parse(&src, 0) else {
                eprintln!("parse failed at k={k}");
                continue;
            };
            let expect_nodes = match *workload {
                "church" => 2 * n + 4,
                "strchain" => 1,
                "struct" => 2, // 末值 zero：SumCase + typ 的 Sum 两节点
                _ => 0,
            };
            let mut t0 = Tycker::new();
            let fast_nodes = t0.bench_check_nf(&decls);
            if closed_form {
                assert_eq!(fast_nodes, expect_nodes, "fast nf 节点数不符 k={k} ({workload})");
            }
            let mut t1 = Tycker::new();
            assert!(t1.bench_check(&decls), "fast check-only 未通过 k={k}");
            if !closed_form {
                // match/enum/universe：快版 vs 参考版节点数互检
                assert_eq!(
                    fast_nodes,
                    L09_mltt::bench_check_nf(&decls),
                    "match/enum/universe 节点数双实现不一致 k={k}"
                );
            } else {
                assert_eq!(
                    L09_mltt::bench_check_nf(&decls),
                    expect_nodes,
                    "basic nf 节点数不符 k={k} ({workload})"
                );
            }
            drop(t0);
            drop(t1);

            let mut rows: Vec<(&str, u128, u128)> = Vec::new();

            // 轮级交错计时（l08bench 同款）：同一轮内依次跑各实现，消除
            // 时间窗相关的系统性偏置。min 统计量下去相关。
            let mut ts_ss: Vec<u128> = Vec::new();
            let mut ts_fast: Vec<u128> = Vec::new();
            let mut ts_memo: Vec<u128> = Vec::new();
            let mut ts_basic: Vec<u128> = Vec::new();
            let mut tycker_ss = if want("fast_ss") {
                Some(Tycker::new())
            } else {
                None
            };
            // 预热各 1 次（同时验证通过；不计入计时）
            if let Some(t) = tycker_ss.as_mut() {
                assert_eq!(t.bench_check_nf(&decls), fast_nodes);
            }
            if want("basic") {
                L09_mltt::bench_check_nf(&decls);
            }
            for _ in 0..cli.rounds {
                if let Some(t) = tycker_ss.as_mut() {
                    let start = Instant::now();
                    t.bench_check_nf(&decls);
                    ts_ss.push(start.elapsed().as_micros());
                }
                if want("fast") {
                    let start = Instant::now();
                    // 一次性口径：每轮新建（Tycker::new 的 bump 预分配计入
                    // 计时——参考版 Infer::new 的建表同样在 bench_check 内）
                    let mut tycker = Tycker::new();
                    tycker.bench_check_nf(&decls);
                    ts_fast.push(start.elapsed().as_micros());
                }
                // quote 记忆化口径（有 quote 的负载才出赛）
                if want("fast_memo") && nf_workload {
                    let start = Instant::now();
                    let mut tycker = Tycker::new(); // 同 fast：新建计入计时
                    tycker.bench_check_nf_memo(&decls);
                    ts_memo.push(start.elapsed().as_micros());
                }
                if want("basic") && !(basic_too_slow && cli.only.is_none()) {
                    let start = Instant::now();
                    L09_mltt::bench_check_nf(&decls);
                    ts_basic.push(start.elapsed().as_micros());
                }
            }
            if want("fast_ss") {
                rows.push((
                    "fast_ss",
                    ts_ss.iter().min().unwrap_or(&0).to_owned(),
                    median(&mut ts_ss),
                ));
            }
            if want("fast") {
                rows.push((
                    "fast",
                    ts_fast.iter().min().unwrap_or(&0).to_owned(),
                    median(&mut ts_fast),
                ));
            }
            if want("fast_memo") && nf_workload {
                rows.push((
                    "fast_memo",
                    ts_memo.iter().min().unwrap_or(&0).to_owned(),
                    median(&mut ts_memo),
                ));
            }
            if want("basic") && !(basic_too_slow && cli.only.is_none()) {
                rows.push((
                    "basic",
                    ts_basic.iter().min().unwrap_or(&0).to_owned(),
                    median(&mut ts_basic),
                ));
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
