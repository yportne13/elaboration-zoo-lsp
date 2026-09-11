//! L12 类型检查器基准：参考版（L11 全家桶 + 全面 SmolStr 化 + canonical
//! 搜索）vs `bump_spine_iter` 移植版的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/bimap.rs`、`src/parser_lib*.rs`
//! 和 `src/L12_canonical/`（与 `tests/l12_fast_parity.rs` 同款）。
//!
//! 负载族（`--workload`）——L12 孪生自带的生成器家族（无 `church`/`gadt`。
//! 终裁 2026-09-11：`church_src` 负载在 L12 参考版即判型失败——orchestrator
//! 实测 `L12_canonical::run(church_src(9))` Err："can't unify expected:
//! N → N, find: N @ 113,123"（孪生 `bench_check_nf` 返回 false 与之同判，
//! 非孪生单侧缺陷），故本 bin 无此负载；「λ 体 + `Type N` 注解合法」的
//! 小样例形态见 tests/l12_fast_parity.rs:628（A5 r1 反例所指程序，非
//! church_src 本身）。`gadt` 处于快版已知缺陷区
//! （tests/l11_fast_parity.rs deep_workloads_parity 注释，L12 同源），
//! 不排入）：
//! - `natadd`：枚举 Nat 加法链（k+1 个 def，值 = 2^(k+1)）——递归
//!   match + 构造子链深负载。
//! - `strchain`（L06 特色）：每层 `string_concat s_{i-1} "x"`；末值 =
//!   长 n 的字面量（nf 节点数 = 1）。
//! - `match`（L07 特色）：k+1 个自递归依赖 match def + 一次 println。
//! - `enum`（L07 特色）：多 enum + Vec 风格 GADT + 投影 + 索引等式 +
//!   递归 length（固定源，check + nf 一次）。
//! - `struct`（L08 特色，L09 语义子集）：两层嵌套 struct + 2^(k+1) 层
//!   浅值投影 def 链（末值 = zero，nf 节点数 = 2）。
//! - `traitchain`（**L12 特色负载**）：毛毯实例 `impl[T] Say for T` +
//!   2^(k+1) 层 `def c{i} : Nat = c{i-1}.say zero` 方法调用 def 链——
//!   每层一次实例合成（L12 合成路径 = L10 链路 + SmolStr 表 +
//!   canonical 搜索的挂接点）。注：canonical/`iddfs`（canonical.rs）在
//!   参考版只在合成失败的 Err 重试闭包里调用（elaboration.rs:368 附近），
//!   快版孪生刻意不移植（`bump_spine_iter.rs` 模块头「canonical/iddfs
//!   不移植」），不存在 Ok 路径的 canonical 专属负载；末值 = succ^n
//!   zero（节点数无闭式，以快版 memo/非 memo 互检 + 两版全流程输出
//!   parity 代替硬编码）。
//!
//! 口径：L12 参考版 mod.rs 无 `bench_check_nf`（bench 口径缺口，见
//! docs/review-continuity/a7-r1.md §4），故 basic 行为全流程 `run`
//! （含 preprocess+parse），另设 `fast_run` 行 = 快版全流程 `run_fast`
//! 与之同轴对比；`fast`/`fast_ss`/`fast_memo` 行为孪生 `Tycker` 的
//! bench 口径（解析在计时外）。正确性闸门：快版 memo/非 memo 节点数
//! 一致 + 两版全流程 Ok 输出逐字节一致（Err 判定一致即通过）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l12bench [--max-k 13] [--rounds 5]
//!                                    [--only basic,fast]
//!                                    [--workload natadd|strchain|match|enum|struct|traitchain|all]
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

#[path = "../L12_canonical/mod.rs"]
mod L12_canonical;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

use L12_canonical::bump_spine_iter::{
    enum_src, match_src, natadd_src, parse, run_fast, strchain_src, struct_src, Tycker,
};

#[derive(Parser)]
#[command(
    name = "l12bench",
    about = "L12 类型检查器基准：canonical 层（trait 合成链）负载下参考版 vs bump_spine_iter 版"
)]
struct Cli {
    /// church 数 = 2^(k+1)，k 从 9 起翻倍到 max-k
    #[arg(long, default_value_t = 13)]
    max_k: u32,

    /// 每实现每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定实现（逗号分隔：basic,fast,fast_run,fast_ss,fast_memo）
    #[arg(long)]
    only: Option<String>,

    /// 负载族：natadd（check+nf，默认）| strchain | match | enum | struct | traitchain | all
    #[arg(long, default_value = "natadd")]
    workload: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L12_STACK_MB")
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

/// traitchain 负载源（**L12 特色负载**，形态与 l10bench 同族——
/// tests/l10_fast_parity.rs::parity_trait_full_demo 已验证的毛毯实例 +
/// 方法调用；L12 = L11 + canonical，语法面超集）。
fn traitchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        r#"enum Nat {
    zero
    succ(x: Nat)
}

trait Say {
    def say(x: Nat): Nat
}

impl[T] Say for T {
    def say(x: Nat): Nat = succ x
}

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
        "natadd" => &["natadd"],
        "strchain" => &["strchain"],
        "match" => &["match"],
        "enum" => &["enum"],
        "struct" => &["struct"],
        "traitchain" => &["traitchain"],
        // 无 church 负载：church_src 在 L12 参考版即判型失败（终裁
        // 2026-09-11，实测 Err @113,123；见文件头与 a7-r2 终裁节）
        _ => &["natadd", "strchain", "match", "enum", "struct", "traitchain"],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        // **strchain/struct/traitchain 的参考版超线性**（L06 readme 同款：
        // 每 define 克隆 src_names/decl 表），默认不排 basic
        let basic_too_slow = matches!(*workload, "strchain" | "struct" | "traitchain");
        // 闭式节点数（孪生生成器注释 + tests/l12_fast_parity.rs 同族钉
        // 值）：strchain = 1、struct = 2；其余以快版双口径互检代替硬编码
        let closed_form = matches!(*workload, "strchain" | "struct");

        let ks: Vec<u32> = if *workload == "enum" {
            vec![9] // enum 负载与 k 无关，只跑一行
        } else {
            (9..=cli.max_k).collect()
        };

        for k in ks {
            let n = 1u64 << (k + 1);
            let src = match *workload {
                "natadd" => natadd_src(k),
                "strchain" => strchain_src(k),
                "match" => match_src(k),
                "struct" => struct_src(k),
                "traitchain" => traitchain_src(k),
                _ => enum_src(),
            };
            // 计时外：解析 + 快版正确性闸门（check-only / memo 互检）
            let Ok(decls) = parse(&src, 0) else {
                eprintln!("parse failed at k={k}");
                continue;
            };
            let expect_nodes = match *workload {
                "strchain" => 1,
                "struct" => 2, // 末值 zero：SumCase + typ 的 Sum 两节点
                _ => 0,
            };
            let mut t0 = Tycker::new();
            let fast_nodes = t0.bench_check_nf(&decls);
            assert!(fast_nodes > 0, "fast check+nf 未通过 k={k} ({workload})");
            if closed_form {
                assert_eq!(fast_nodes, expect_nodes, "fast nf 节点数不符 k={k} ({workload})");
            }
            let mut t1 = Tycker::new();
            assert!(t1.bench_check(&decls), "fast check-only 未通过 k={k}");
            assert_eq!(
                t1.bench_check_nf_memo(&decls),
                fast_nodes,
                "memo 口径节点数漂移 k={k} ({workload})"
            );
            drop(t0);
            drop(t1);

            // 两版全流程输出 parity（计时外；basic 首跑兼作预热）。
            // 参考版无 bench 口径（见文件头），全流程 Ok 输出逐字节一致
            // 是本 bin 的双 oracle；Err 判定一致即通过（正常负载不应 Err）。
            let basic_out = if want("basic") {
                Some(L12_canonical::run(&src, 0))
            } else {
                None
            };
            let fast_out = run_fast(&src, 0);
            if let (Some(Ok(b)), Ok(f)) = (&basic_out, &fast_out) {
                assert_eq!(
                    b, f,
                    "两版全流程 Ok 输出不一致 k={k} ({workload})\n--- basic ---\n{b}--- fast ---\n{f}"
                );
            } else if basic_out.is_some()
                && basic_out.as_ref().unwrap().is_err() != fast_out.is_err()
            {
                panic!("两版 Ok/Err 判定不一致 k={k} ({workload})");
            }

            let mut rows: Vec<(&str, u128, u128)> = Vec::new();

            // 轮级交错计时（l08bench 同款）：同一轮内依次跑各实现，消除
            // 时间窗相关的系统性偏置。min 统计量下去相关。
            let mut ts_ss: Vec<u128> = Vec::new();
            let mut ts_fast: Vec<u128> = Vec::new();
            let mut ts_run: Vec<u128> = Vec::new();
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
            for _ in 0..cli.rounds {
                if let Some(t) = tycker_ss.as_mut() {
                    let start = Instant::now();
                    t.bench_check_nf(&decls);
                    ts_ss.push(start.elapsed().as_micros());
                }
                if want("fast") {
                    let start = Instant::now();
                    // 一次性口径：每轮新建（Tycker::new 的 bump 预分配计入
                    // 计时——解析在计时外）
                    let mut tycker = Tycker::new();
                    tycker.bench_check_nf(&decls);
                    ts_fast.push(start.elapsed().as_micros());
                }
                // 全流程口径（同 basic 轴：含 preprocess+parse+println）
                if want("fast_run") {
                    let start = Instant::now();
                    run_fast(&src, 0);
                    ts_run.push(start.elapsed().as_micros());
                }
                // quote 记忆化口径
                if want("fast_memo") {
                    let start = Instant::now();
                    let mut tycker = Tycker::new(); // 同 fast：新建计入计时
                    tycker.bench_check_nf_memo(&decls);
                    ts_memo.push(start.elapsed().as_micros());
                }
                if want("basic") && !(basic_too_slow && cli.only.is_none()) {
                    let start = Instant::now();
                    L12_canonical::run(&src, 0);
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
            if want("fast_run") {
                rows.push((
                    "fast_run",
                    ts_run.iter().min().unwrap_or(&0).to_owned(),
                    median(&mut ts_run),
                ));
            }
            if want("fast_memo") {
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
