//! matchbench —— 多分支多层次 match 在 L07–L13 七章上的**耗时**基准。
//!
//! 为什么单独做一个 bin：现有 `realbench` 只覆盖 L07–L12，`l13bench` 只做
//! L13 的参考版 vs 孪生，`l06l13mem` 只量内存。本 bin 用**同一份源**喂全部
//! 七章，直接对照「同一负载在不同章节实现上的挂钟时间」。
//!
//! 用法：
//!   cargo run --release --bin matchbench -- --depth 4 --copies 4 --width 8
//!   cargo run --release --bin matchbench -- --chapter L13 --reps 3
//!   cargo run --release --bin matchbench -- --sweep
//!
//! 输出 CSV 行：`RESULT,<chapter>,<depth>,<copies>,<width>,<bytes>,<ms>,<ok>`

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

#[path = "matchbench_src.rs"]
mod gen_src;

use clap::Parser;
use std::time::Instant;

/// 递归层数上限。级联每层都会在引擎里展开一次，太深会让参考版爆栈。
const MAX_DEPTH: u32 = 12;

#[derive(Parser)]
#[command(
    name = "matchbench",
    about = "多分支多层次 match：L07-L13 同源耗时对照"
)]
struct Cli {
    /// 章节（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    chapter: String,

    /// 单条级联的嵌套层数（1..=12）
    #[arg(long, default_value_t = 4)]
    depth: u32,

    /// 级联条数
    #[arg(long, default_value_t = 4)]
    copies: u32,

    /// 叶子 Wide 的构造子数
    #[arg(long, default_value_t = 8)]
    width: u32,

    /// 每档重复次数（取最小值，抑制抖动）
    #[arg(long, default_value_t = 3)]
    reps: usize,

    /// 跑 depth 1..=8 的完整扫描（覆盖 depth/copies/width 三个轴）
    #[arg(long)]
    sweep: bool,

    /// 只扫宽度轴：width 固定取 1,2,4,8,16,32,64,128，depth 用 --depth
    #[arg(long)]
    width_sweep: bool,

    /// 宽度轴的最大值（与 --width-sweep 配合，默认 128）
    #[arg(long, default_value_t = 128)]
    max_width: u32,

    /// 打开各章的计数器探针（L07–L12 用 prof 模块，L13 用 FUNC_PROF），
    /// 每条 RESULT 行后追加一行 PROFILE：force/eval/quote/v_app/unify/check
    /// 的调用次数。探针本身有 ~1 atomic load / 次的成本，计时只作参考。
    #[arg(long)]
    prof: bool,

    /// 打印各章 Val / Tm 的字节大小（表示层对照）。
    #[arg(long)]
    layout: bool,

    /// 关掉 L13 的 `FORCE_MEMO`（消融对照：只对 L13 生效，其余章本来就没有）。
    #[arg(long)]
    no_memo: bool,
}

/// 一个章节的跑法：返回 (是否成功, 毫秒)。
macro_rules! run_chapter {
    ($ch:ident, $src:expr, $reps:expr) => {{
        let mut best_ms = f64::INFINITY;
        let mut ok = false;
        for _ in 0..$reps {
            let t0 = Instant::now();
            ok = $ch::run(&$src, 0).is_ok();
            let ms = t0.elapsed().as_secs_f64() * 1000.0;
            if ms < best_ms {
                best_ms = ms;
            }
        }
        (ok, best_ms)
    }};
}

fn chapters(cli: &Cli) -> Vec<&'static str> {
    match cli.chapter.as_str() {
        "all" => vec!["L07", "L08", "L09", "L10", "L11", "L12", "L13"],
        "L07" => vec!["L07"],
        "L08" => vec!["L08"],
        "L09" => vec!["L09"],
        "L10" => vec!["L10"],
        "L11" => vec!["L11"],
        "L12" => vec!["L12"],
        "L13" => vec!["L13"],
        other => {
            eprintln!("unknown chapter: {other} (expect L07..L13 or all)");
            std::process::exit(2);
        }
    }
}

/// 一章的能力：跑一次、开探针、读计数器、报类型大小。
///
/// 七章的探针口径不同（L07–L12 是 `prof` 模块的 relaxed 计数器，L13 是
/// `FUNC_PROF` 的「计数 + 独占耗时」二元组），这里用 trait 把差异封在
/// 每个章各自的标记类型里，bench 主体只面对统一接口。
trait ChapterProbe {
    /// 跑一次源，返回成功与否。
    fn run(src: &str) -> bool;
    /// 打开该章的计数器探针。
    fn enable_prof();
    /// 清零该章的计数器。
    fn reset_prof();
    /// `(名字, 累计次数)`；计数器在 `run` 期间累加。
    fn counters() -> Vec<(&'static str, u64)>;
    /// `(Val 字节数, Tm 字节数)`。
    fn sizes() -> (usize, usize);
}

/// 为 L07–L12（`prof` 模块计数器口径）生成标记类型 + trait 实现。
macro_rules! chapter_prof {
    ($marker:ident, $ch:ident, $($name:ident),* $(,)?) => {
        struct $marker;
        impl ChapterProbe for $marker {
            fn run(src: &str) -> bool { $ch::run(src, 0).is_ok() }
            fn enable_prof() { $ch::prof::enable(); }
            fn reset_prof() { $ch::prof::reset(); }
            fn counters() -> Vec<(&'static str, u64)> {
                let mut v = vec![$(( stringify!($name), $ch::prof::$name.load(std::sync::atomic::Ordering::Relaxed) )),*];
                v.extend($ch::phases::report());
                v
            }
            fn sizes() -> (usize, usize) {
                (std::mem::size_of::<$ch::Val>(), std::mem::size_of::<$ch::Tm>())
            }
        }
    };
}

chapter_prof!(ChL07, L07_sum_type, FORCE, EVAL, QUOTE, VAPP, UNIFY, MATCH_RUN, DECL_FORCE, VSPAN_ALLOC, EVAL_SUM, QUOTE_SUM);
chapter_prof!(ChL08, L08_product_type, FORCE, EVAL, QUOTE, VAPP, UNIFY, MATCH_RUN, DECL_FORCE);
chapter_prof!(ChL09, L09_mltt, FORCE, EVAL, QUOTE, VAPP, UNIFY, MATCH_RUN, DECL_FORCE);
chapter_prof!(ChL10, L10_typeclass, FORCE, EVAL, QUOTE, VAPP, UNIFY, MATCH_RUN, DECL_FORCE);
chapter_prof!(ChL11, L11_macro, FORCE, EVAL, QUOTE, VAPP, UNIFY, MATCH_RUN, DECL_FORCE);
chapter_prof!(ChL12, L12_canonical, FORCE, EVAL, QUOTE, VAPP, UNIFY, MATCH_RUN, DECL_FORCE);

/// L13 的探针是 `FUNC_PROF`：计数在 `.1`，独占耗时在 `.0`。
struct ChL13;
impl ChapterProbe for ChL13 {
    fn run(src: &str) -> bool { L13_namespace::run(src, 0).is_ok() }
    fn enable_prof() {
        L13_namespace::FUNC_PROF.enabled.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    /// `FUNC_PROF` 没有整表清零的公开入口：每档之间按「记基线、读增量」
    /// 处理（见 `main` 的 prof 路径）。
    fn reset_prof() {}
    fn counters() -> Vec<(&'static str, u64)> {
        use std::sync::atomic::Ordering::Relaxed;
        vec![
            ("FORCE", L13_namespace::FUNC_PROF.force.1.load(Relaxed)),
            ("EVAL", L13_namespace::FUNC_PROF.eval.1.load(Relaxed)),
            ("QUOTE", L13_namespace::FUNC_PROF.quote.1.load(Relaxed)),
            ("VAPP", L13_namespace::FUNC_PROF.v_app.1.load(Relaxed)),
            ("UNIFY", L13_namespace::FUNC_PROF.unify.1.load(Relaxed)),
            ("CHECK", L13_namespace::FUNC_PROF.check.1.load(Relaxed)),
            ("INFER_EXPR", L13_namespace::FUNC_PROF.infer_expr.1.load(Relaxed)),
            ("FORCE_HITS", L13_namespace::FUNC_PROF.force_hits.1.load(Relaxed)),
            ("FORCE_MISSES", L13_namespace::FUNC_PROF.force_misses.1.load(Relaxed)),
            ("FORCE_TAINTED", L13_namespace::FUNC_PROF.force_tainted.1.load(Relaxed)),
            ("COVER_NS", L13_namespace::phases::COVER_NS.load(Relaxed)),
            ("ARMS_NS", L13_namespace::phases::ARMS_NS.load(Relaxed)),
            ("WALK_NS", L13_namespace::phases::WALK_NS.load(Relaxed)),
            ("SUBCXT_NS", L13_namespace::phases::SUBCXT_NS.load(Relaxed)),
            ("REANCHOR_NS", L13_namespace::phases::REANCHOR_NS.load(Relaxed)),
            ("BODY_NS", L13_namespace::phases::BODY_NS.load(Relaxed)),
            ("NEST_NS", L13_namespace::phases::NEST_NS.load(Relaxed)),
            ("COVERS", L13_namespace::phases::COVERS.load(Relaxed)),
        ]
    }
    fn sizes() -> (usize, usize) {
        (std::mem::size_of::<L13_namespace::Val>(), std::mem::size_of::<L13_namespace::Tm>())
    }
}

/// 按章节名分派：`run` / 探针 / 计数 / 类型大小。
macro_rules! dispatch {
    ($ch:expr, $method:ident $(, $arg:expr)*) => {{
        match $ch {
            "L07" => ChL07::$method($($arg),*),
            "L08" => ChL08::$method($($arg),*),
            "L09" => ChL09::$method($($arg),*),
            "L10" => ChL10::$method($($arg),*),
            "L11" => ChL11::$method($($arg),*),
            "L12" => ChL12::$method($($arg),*),
            "L13" => ChL13::$method($($arg),*),
            _ => unreachable!(),
        }
    }};
}

fn main() {
    let cli = Cli::parse();

    let mut cases: Vec<(u32, u32, u32)> = Vec::new();
    if cli.width_sweep {
        // 宽度轴：1,2,4,8,...,max_width；depth 固定。
        let mut w = 1u32;
        while w <= cli.max_width {
            cases.push((cli.depth, cli.copies, w));
            w *= 2;
        }
    } else if cli.sweep {
        for depth in 1..=8u32 {
            for width in [2u32, 8, 32] {
                cases.push((depth, cli.copies, width));
            }
        }
    } else {
        if cli.depth < 1 || cli.depth > MAX_DEPTH {
            eprintln!("depth must be 1..={MAX_DEPTH}");
            std::process::exit(2);
        }
        cases.push((cli.depth, cli.copies, cli.width));
    }

    let chs = chapters(&cli);
    println!("# matchbench: chapters={chs:?} reps={}", cli.reps);

    if cli.no_memo {
        L13_namespace::FORCE_MEMO_DISABLED.store(true, std::sync::atomic::Ordering::Relaxed);
        println!("# L13 FORCE_MEMO disabled");
    }

    if cli.layout {
        println!("LAYOUT,chapter,val_bytes,tm_bytes");
        for ch in &chs {
            let (v, t) = dispatch!(*ch, sizes);
            println!("LAYOUT,{ch},{v},{t}");
        }
    }

    if cli.prof {
        for ch in &chs {
            dispatch!(*ch, enable_prof);
        }
    }

    for (depth, copies, width) in cases {
        let src = gen_src::match_cascade_src(depth, copies, width);
        for ch in &chs {
            // 每档取基线，run 之后读增量——`FUNC_PROF` 没有整表清零入口，
            // 差分让 L07–L13 走同一套读法。
            let base = if cli.prof { dispatch!(*ch, counters) } else { Vec::new() };
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
            println!(
                "RESULT,{ch},{depth},{copies},{width},{},{ms:.3},{ok}",
                src.len()
            );
            if cli.prof {
                let now = dispatch!(*ch, counters);
                let body = now
                    .iter()
                    .enumerate()
                    .map(|(i, (n, c))| {
                        let b = base.get(i).map(|(_, b)| *b).unwrap_or(0);
                        format!("{n}={}", c.saturating_sub(b))
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                println!("PROFILE,{ch},{depth},{copies},{width},{body}");
            }
        }
    }
}
