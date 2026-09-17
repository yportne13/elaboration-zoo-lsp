//! L07 显式替换重构的**分配计数**对照器（确定性、无计时噪声）。
//!
//! 同一个源文本喂给两个 L07 参考版实现（当前 HEAD 的 `L07_sum_type` 与
//! 重构前 `b9d54fe` 的 `src/bench_pre/L07_sum_type`），只比对：
//!
//! - `allocs` / `bytes`：进程级 `GlobalAlloc` 计数（alloc + realloc 记 1 次，
//!   bytes 记请求的 size）；
//! - `parse` 行：`preprocess + parser` 单独一次（两版解析器代码相同，用于
//!   把"解析/预处理"的固定分摊从推导增量里摘出去）；
//! - `run` 行：`run(src, 0)` 全流程（含上述解析 + 逐 decl 推导）。
//!
//! 计数是确定性的：同一二进制重复跑同一源，数字逐位相同，所以 delta 就是
//! 重构引入的分配量差，不需要 rounds/min 那套降噪。

#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::{AtomicU64, Ordering};

struct Counting;

static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);

/// 按请求大小分桶的分配直方图：size<256 逐字节精确成桶，≥256 按 64B 粗分。
/// 纯原子写，分配器内不做任何分配，避免重入。
const EXACT: usize = 256;
const NB: usize = EXACT + 64;
static SZ: [AtomicU64; NB] = [const { AtomicU64::new(0) }; NB];

#[inline]
fn bump_sz(size: usize) {
    let idx = if size < EXACT {
        size
    } else {
        EXACT + ((size - EXACT) / 64).min(63)
    };
    SZ[idx].fetch_add(1, Ordering::Relaxed);
}

fn hist_reset() {
    for b in SZ.iter() {
        b.store(0, Ordering::Relaxed);
    }
}

fn hist_snapshot() -> Vec<u64> {
    SZ.iter().map(|b| b.load(Ordering::Relaxed)).collect()
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(l.size() as u64, Ordering::Relaxed);
        bump_sz(l.size());
        unsafe { mimalloc::MiMalloc.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { mimalloc::MiMalloc.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(new as u64, Ordering::Relaxed);
        bump_sz(new);
        unsafe { mimalloc::MiMalloc.realloc(p, l, new) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(l.size() as u64, Ordering::Relaxed);
        bump_sz(l.size());
        unsafe { mimalloc::MiMalloc.alloc_zeroed(l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;
#[path = "../parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../pmab_gen.rs"]
mod pmab_gen;

#[path = "../L07_sum_type/mod.rs"]
mod L07_sum_type;

#[path = "../bench_pre/L07_sum_type/mod.rs"]
mod L07_pre;

/// 已提交的 HEAD（ea01207）——用来把"重构本身"与"工作区在飞的修复轮"分开。
#[path = "../bench_head/mod.rs"]
mod L07_head;

use clap::Parser;

#[derive(Parser)]
#[command(name = "l07alloc", about = "L07 分配计数对照：HEAD vs 重构前（确定性）")]
struct Cli {
    /// 只跑指定扫描（逗号分隔）：flat,wild,cart,deep
    #[arg(long, default_value = "flat,wild,cart,deep")]
    sweeps: String,

    /// 量对照源（同枚举、无 match）而不是负载源
    #[arg(long)]
    ctrl: bool,

    /// 每个扫描族的最大规模额外打印分配大小直方图（pre vs cur 的净增桶）
    #[arg(long)]
    hist: bool,
}

/// 分配大小直方图归因：size<256 逐字节精确，≥256 每 64B 一桶。
/// 返回 (桶标签下界, pre, cur)，只保留 cur > pre 的桶，按净增降序。
fn hist_delta(src: &str) -> Vec<(usize, u64, u64)> {
    hist_reset();
    let _ = L07_pre::run(src, 0);
    let h_pre = hist_snapshot();
    hist_reset();
    let _ = L07_sum_type::run(src, 0);
    let h_cur = hist_snapshot();
    let mut v: Vec<(usize, u64, u64)> = (0..NB)
        .map(|i| (if i < EXACT { i } else { EXACT + (i - EXACT) * 64 }, h_pre[i], h_cur[i]))
        .filter(|&(_, p, c)| c > p)
        .collect();
    v.sort_by_key(|&(_, p, c)| std::cmp::Reverse(c - p));
    v
}

fn measure(parse_only: bool, src: &str, which: char) -> (u64, u64) {
    let a0 = ALLOCS.load(Ordering::Relaxed);
    let b0 = BYTES.load(Ordering::Relaxed);
    let ok = match (which, parse_only) {
        ('p', true) => {
            let _ = L07_pre::parser::parser(&L07_pre::preprocess(src), 0);
            true
        }
        ('c', true) => {
            let _ = L07_sum_type::parser::parser(&L07_sum_type::preprocess(src), 0);
            true
        }
        ('p', false) => L07_pre::run(src, 0).is_ok(),
        ('h', false) => L07_head::run(src, 0).is_ok(),
        ('c', false) => L07_sum_type::run(src, 0).is_ok(),
        _ => unreachable!(),
    };
    let a1 = ALLOCS.load(Ordering::Relaxed);
    let b1 = BYTES.load(Ordering::Relaxed);
    if !ok {
        eprintln!("  [warn] impl {which} 未通过");
    }
    (a1 - a0, b1 - b0)
}

fn main() {
    let cli = Cli::parse();
    let sweeps: Vec<String> = cli.sweeps.split(',').map(|s| s.trim().to_owned()).collect();
    let (ctrl, hist) = (cli.ctrl, cli.hist);
    // 与 pmabbench 同款：深嵌套负载走查递归很深
    std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || go(&sweeps, ctrl, hist))
        .unwrap()
        .join()
        .unwrap();
}

fn go(sweeps: &[String], ctrl: bool, hist: bool) {
    println!(
        "{:>6}{:>6}{:>7}{:>10}{:>10}{:>10}{:>15}{:>15}",
        "sweep", "size", "arms", "pre.run", "head.run", "cur.run", "head/pre", "cur/pre"
    );
    for sweep in sweeps {
        let sweep = sweep.as_str();
        let sizes: Vec<usize> = match sweep {
            "wild" => vec![5, 7, 9, 11],
            "cart" => vec![4, 6, 8, 10],
            "deep" => vec![16, 32, 64, 128],
            _ => vec![5, 9, 17],
        };
        for &sz in &sizes {
            let src = if ctrl {
                match sweep {
                    "wild" => pmab_gen::wild_ctrl(sz),
                    "deep" => pmab_gen::deep_ctrl(sz),
                    _ => pmab_gen::flat_ctrl(sz),
                }
            } else {
                match sweep {
                    "wild" => pmab_gen::wild_src(sz),
                    "cart" => pmab_gen::cart_src(sz),
                    "deep" => pmab_gen::deep_src(sz),
                    _ => pmab_gen::flat_src(sz),
                }
            };
            let arms = if sweep == "cart" && !ctrl { 1usize << sz } else { sz + 1 };
            // 每侧先热身一次再计数（缓存/惰性初始化不计入）
            let _ = measure(false, &src, 'p');
            let _ = measure(false, &src, 'h');
            let _ = measure(false, &src, 'c');
            let (pp, _) = measure(true, &src, 'p');
            let (pc, _) = measure(true, &src, 'c');
            let (rp, _bu) = measure(false, &src, 'p');
            let (rh, _) = measure(false, &src, 'h');
            let (rc, _bc) = measure(false, &src, 'c');
            println!(
                "{sweep:>6}{sz:>6}{arms:>7}{rp:>10}{rh:>10}{rc:>10}{:>15.3}{:>15.3}",
                rh as f64 / rp as f64,
                rc as f64 / rp as f64,
            );
            let _ = (pp, pc);
            if hist && sz == *sizes.last().unwrap() {
                println!(
                    "       ^ 分配直方图净增（size_of::<Val>()={}, size_of::<Subst>()={}, size_of::<Tm>()={}, Rc 头=16B；SubEntry=Rc 分配 - 16）",
                    std::mem::size_of::<L07_sum_type::Val>(),
                    std::mem::size_of::<L07_sum_type::Subst>(),
                    std::mem::size_of::<L07_sum_type::Tm>(),
                );
                for (lo, p, c) in hist_delta(&src).iter().take(10) {
                    let label = if *lo < EXACT {
                        format!("size ={lo:<5}")
                    } else {
                        format!("size ≥{lo:<5}")
                    };
                    println!("         {label}  pre {p:>8}  cur {c:>8}  +{}", c - p);
                }
            }
        }
    }
}
