//! 模式匹配编译策略受控实验：同一份源文本喂给多个**参考版**编译器，
//! 比较编译期代价随规模的走势。
//!
//! 与 `typort` 解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs`、`src/bimap.rs`、`src/parser_lib*.rs`、
//! `src/pmab_gen.rs`，以及被比较的层目录。当前可选实现：
//!
//! - `l07`    —— 当前 HEAD 的 L07（逐臂下钻 + 显式替换精化）；
//! - `l07pre` —— 重构前（`b9d54fe`）的 L07（逐臂下钻 + pm_defs 事实表），
//!               源码由 `git archive` 抽到 `src/bench_pre/L07_sum_type/`；
//! - `l09`    —— 当前 HEAD 的 L09（决策树矩阵）。
//!
//! 口径：
//! - 计时面 = `run(src, 0)` 全流程（preprocess + parse + 逐 decl 推导）。
//!   源里没有 `println`，所以不做 nf；随规模增长的是 match 编译。
//! - 每规模跑同枚举、无 match（或常量体）的对照源，报告**扣掉对照后的净值**。
//! - 每规模先跑一次验证 `run` 返回 Ok（不过就不报数，避免拿失败路径当时间）。
//! - `--rounds` 次取 min（默认 3）。
//! - 深嵌套模式负载递归很深，工作负载跑在 1 GB 栈线程上。
//! - stdout 被 L09 的 `run` 用来打印 decl 名，故本 bin 的结果走 stderr。

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

#[path = "../pmab_gen.rs"]
mod pmab_gen;

#[path = "../L07_sum_type/mod.rs"]
mod L07_sum_type;

#[path = "../L09_mltt/mod.rs"]
mod L09_mltt;

#[path = "../bench_pre/L07_sum_type/mod.rs"]
mod L07_pre;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

#[derive(Parser)]
#[command(
    name = "pmabbench",
    about = "模式匹配编译策略受控实验：同源喂多个参考版编译器，比编译期走势"
)]
struct Cli {
    /// 被比较的两个实现（逗号分隔）：l07 | l07pre | l09
    #[arg(long, default_value = "l07,l09")]
    impls: String,

    /// 扫描族：flat（臂数）| wild（列数/通配重数）| cart（完整交叉积）| deep（深嵌套模式）
    #[arg(long, default_value = "flat")]
    sweep: String,

    /// 规模列表（逗号分隔）
    #[arg(long, default_value = "4,8,16")]
    sizes: String,

    /// 每规模的计时轮数
    #[arg(long, default_value_t = 3)]
    rounds: usize,
}

type RunFn = Box<dyn Fn(&str) -> Result<(), String>>;

fn runner(name: &str) -> Option<RunFn> {
    match name {
        "l07" => Some(Box::new(|s| {
            L07_sum_type::run(s, 0).map(|_| ()).map_err(|e| format!("{e:?}"))
        })),
        "l07pre" => Some(Box::new(|s| {
            L07_pre::run(s, 0).map(|_| ()).map_err(|e| format!("{e:?}"))
        })),
        "l09" => Some(Box::new(|s| {
            L09_mltt::run(s, 0).map(|_| ()).map_err(|e| format!("{e:?}"))
        })),
        _ => None,
    }
}

fn time_it(f: &RunFn, src: &str, rounds: usize) -> Result<f64, String> {
    f(src)?;
    let mut best = f64::INFINITY;
    for _ in 0..rounds {
        let t = Instant::now();
        f(src)?;
        best = best.min(t.elapsed().as_secs_f64() * 1000.0);
    }
    Ok(best)
}

fn main() {
    let cli = Cli::parse();
    let names: Vec<String> = cli.impls.split(',').map(|x| x.trim().to_owned()).collect();
    assert_eq!(names.len(), 2, "--impls 需要恰好两个实现名");
    let sizes: Vec<usize> = cli
        .sizes
        .split(',')
        .filter_map(|x| x.trim().parse().ok())
        .collect();
    let sweep = cli.sweep.clone();
    let rounds = cli.rounds;

    // 深嵌套负载的走查递归很深（L07 tests 用 512 MB 栈），统一放大到 1 GB。
    std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || go(sweep, names, sizes, rounds))
        .unwrap()
        .join()
        .unwrap();
}

fn go(sweep: String, names: Vec<String>, sizes: Vec<usize>, rounds: usize) {
    let f0 = runner(&names[0]).unwrap_or_else(|| panic!("未知实现 {}", names[0]));
    let f1 = runner(&names[1]).unwrap_or_else(|| panic!("未知实现 {}", names[1]));
    eprintln!(
        "== sweep: {sweep} ==  impls: {} vs {}  (rounds={rounds}, 净 = 扣同枚举对照)",
        names[0], names[1]
    );
    eprintln!(
        "{:>6}{:>8}{:>16}{:>16}{:>10}",
        "size",
        "arms",
        format!("{}(ms)", names[0]),
        format!("{}(ms)", names[1]),
        format!("{}/{}", names[1], names[0])
    );
    for &sz in &sizes {
        let (src, ctrl, arms) = match sweep.as_str() {
            "wild" => (pmab_gen::wild_src(sz), pmab_gen::wild_ctrl(sz), sz + 1),
            "cart" => (pmab_gen::cart_src(sz), pmab_gen::wild_ctrl(sz), 1usize << sz),
            "deep" => (pmab_gen::deep_src(sz), pmab_gen::deep_ctrl(sz), 2),
            _ => (pmab_gen::flat_src(sz), pmab_gen::flat_ctrl(sz), sz + 1),
        };
        let (t0, c0) = (time_it(&f0, &src, rounds), time_it(&f0, &ctrl, rounds));
        let (t1, c1) = (time_it(&f1, &src, rounds), time_it(&f1, &ctrl, rounds));
        match (t0, c0, t1, c1) {
            (Ok(t0), Ok(c0), Ok(t1), Ok(c1)) => {
                let (n0, n1) = ((t0 - c0).max(0.0), (t1 - c1).max(0.0));
                let r = if n0 > 0.0 { format!("{:.2}", n1 / n0) } else { "—".into() };
                // raw0/raw1 = 含对照的总时长，net0/net1 = 扣对照后
                eprintln!(
                    "{:>6}{:>8}{:>16.3}{:>16.3}{:>10}   raw {:.3}/{:.3}  ctrl {:.3}/{:.3}",
                    sz, arms, n0, n1, r, t0, t1, c0, c1
                );
            }
            (e0, _, e1, _) => {
                if let Err(e) = e0 {
                    eprintln!("    [{} 拒绝] {}", names[0], e);
                }
                if let Err(e) = e1 {
                    eprintln!("    [{} 拒绝] {}", names[1], e);
                }
                eprintln!("{:>6}{:>8}   —— 未通过检查（该规模不可比）", sz, arms);
            }
        }
    }
}
