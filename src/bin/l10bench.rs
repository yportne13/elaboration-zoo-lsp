//! L10 类型检查器基准：参考版（L09 全家桶 + trait/impl 实例合成）vs
//! `bump_spine_iter` 移植版的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/bimap.rs`、`src/parser_lib*.rs`
//! 和 `src/L10_typeclass/`（与 `tests/l10_fast_parity.rs` 同款）。
//!
//! 负载族（`--workload`）——L09 全家桶 + L10 trait 特色负载：
//! - `church`：church 2^(k+1) 的 check + nf（nf 节点数 = 2n + 4，与
//!   L06-L09 同式）。
//! - `strchain`（L06 特色）：每层 `string_concat s_{i-1} "x"`——每层一次
//!   builtin prim 触发；末值 = 长 n 的字面量（nf 节点数 = 1）。
//! - `match`（L07 特色）：k+1 个自递归依赖 match def + 一次 println。
//! - `enum`（L07 特色）：多 enum + Vec 风格 GADT + 投影 + 索引等式 +
//!   递归 length（固定源，check + nf 一次）。
//! - `struct`（L08 特色，L09 语义子集）：两层嵌套 struct + 2^(k+1) 层
//!   浅值投影 def 链（末值 = zero，nf 节点数 = 2）。
//! - `universe`（L09 特色）：固定宇宙塔 + 2^(k+1) 层 `Type N` Pi 判定
//!   def 链（每层一次 check_universe + global 登记；末值无闭式，双实现
//!   互检）。
//! - `traitchain`（**L10 特色**）：固定 trait/impl 段（`ToString` for
//!   `Bool` + 泛型约束参数 `t[T][s: ToString[T]]` + 毛毯实例
//!   `impl[T] Say for T`，与 tests/l10_fast_parity.rs 的
//!   parity_trait_full_demo 同款形态）+ 2^(k+1) 层
//!   `def c{i} : Nat = c{i-1}.say zero` 方法调用 def 链——每层一次实例
//!   合成（Synth → 单实例求解）+ 方法 β 应用；末值 = succ^n zero（节点
//!   数无闭式，以「快版 == 参考版」互检代替硬编码）。
//!
//! nf 节点数口径：check 全部 decl 后取**最后一个 def** 的登记值空层级
//! 引读并数节点（`Tycker::bench_check_nf`，quote 无记忆化）；`fast_memo`
//! 行为 quote 记忆化口径。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l10bench [--max-k 13] [--rounds 5]
//!                                    [--only basic,fast]
//!                                    [--workload church|strchain|match|enum|struct|universe|traitchain|all]
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

#[path = "../L10_typeclass/mod.rs"]
mod L10_typeclass;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L10_typeclass::bump_spine_iter::{
    church_src, enum_src, match_src, parse, strchain_src, struct_src, Tycker,
};

#[derive(Parser)]
#[command(
    name = "l10bench",
    about = "L10 类型检查器基准：trait/impl 实例合成负载下参考版 vs bump_spine_iter 版"
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

    /// 负载族：church（check+nf，默认）| strchain | match | enum | struct | universe | traitchain | all
    #[arg(long, default_value = "church")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L10_STACK_MB")
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

/// universe 负载源（L09 特色负载，形态取自 tests/l09_fast_parity.rs 的
/// parity_universe_levels 已验证用例；L10 = L09 + trait，语法面超集）。
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

/// traitchain 负载源（**L10 特色**，固定段与规模段均为
/// tests/l10_fast_parity.rs::parity_trait_full_demo 已验证形态）。
fn traitchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

trait Say {
    def say(x: Nat): Nat
}

impl[T] Say for T {
    def say(x: Nat): Nat = succ x
}

def t[T][s: ToString[T]](x: T): String =
    s.to_string x

println (t true)

def c0 : Nat = zero
"#,
    );
    for i in 1..n {
        s += &format!("def c{i} : Nat = c{}.say zero\n", i - 1);
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
        "traitchain" => &["traitchain"],
        _ => &[
            "church",
            "strchain",
            "match",
            "enum",
            "struct",
            "universe",
            "traitchain",
        ],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // church/strchain/match/universe/traitchain 走 check + nf；enum 是
        // 固定源（check+nf 一次）。**strchain/struct 的参考版超线性**
        // （L06 readme 同款），默认不排 basic
        let nf_workload =
            matches!(*workload, "church" | "strchain" | "match" | "universe" | "traitchain");
        let basic_too_slow = matches!(*workload, "strchain" | "struct");
        // church/strchain/struct 的节点数有闭式（孪生生成器注释 +
        // tests/l10_fast_parity.rs 钉值）；match/enum/universe/traitchain
        // 以「快版 == 参考版」互检代替硬编码
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
                "traitchain" => traitchain_src(k),
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
                // match/enum/universe/traitchain：快版 vs 参考版节点数互检
                assert_eq!(
                    fast_nodes,
                    L10_typeclass::bench_check_nf(&decls),
                    "match/enum/universe/traitchain 节点数双实现不一致 k={k}"
                );
            } else {
                assert_eq!(
                    L10_typeclass::bench_check_nf(&decls),
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
                L10_typeclass::bench_check_nf(&decls);
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
                    L10_typeclass::bench_check_nf(&decls);
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
