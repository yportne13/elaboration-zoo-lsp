//! L02–L05 性能版（`bump_spine_iter` 孪生）**内存占用**测量器（确定性分配
//! 计数口径，与 `l07alloc` 同族）。
//!
//! 测的不是墙钟时间，而是每个负载在每个实现口径下的**分配次数 / 分配字节 /
//! 大小直方图**。由此可推导：
//!
//! - **一次性口径（`fast`）**：每轮新建 `Tycker`，计数 = 该轮完整足迹
//!   （arena chunk 链 + Machine 常驻缓冲 + 逐调用草稿 + 解析外的全部）。
//! - **稳态口径（`fast_ss`）**：一个 `Tycker` 跨轮 `Bump::reset`：
//!   - 第 1 轮（`growth`）= arena chunk 链高水位 + Machine 缓冲高水位 +
//!     逐调用草稿高水位——**即稳态常驻内存的下界**（reset 不还 chunk、
//!     Vec clear 保容量）；
//!   - 后续轮（`churn`）= 每轮真正的新分配（arena 内 bump 推进不经过全局
//!     分配器，故只剩逐调用 Vec/HashMap 的分配与释放）。
//! - **参考版（`basic`）**：Box/Rc 版逐节点分配的计数（`mem::forget` 语义
//!   同 bench：只测一次，泄漏不管）。
//!
//! 直方图按请求大小分桶（<256B 逐字节，≥256B 每 64B），据此把 arena chunk
//! （≥1MB，bumpalo 的 chunk 分配）与小的逐调用分配分开。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l02l05mem [--chapter L02|L03|L04|L05|all]
//!                                  [--workload church|conv|...|all] [--k 11]
//!                                  [--rounds 3] [--hist]
//! ```

#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::{AtomicU64, Ordering};

struct Counting;

static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
/// ≥1MB 的分配（bumpalo 的 arena chunk 链是这类分配的唯一来源；Vec 扩容
/// 在该负载下到不了 1MB）。单独计数以便把 arena 与逐调用草稿分开。
static BIG_N: AtomicU64 = AtomicU64::new(0);
static BIG_B: AtomicU64 = AtomicU64::new(0);
/// 前 24 个 ≥1MB 分配的精确大小（bumpalo chunk 序列：1MB、2MB、4MB…翻倍）。
/// 超出 24 个的部分只进 BIG_N/BIG_B。
const BIGLIST: usize = 24;
static BIG_SIZES: [AtomicU64; BIGLIST] = [const { AtomicU64::new(0) }; BIGLIST];

/// 按请求大小分桶的分配直方图：size<256 逐字节精确成桶，≥256 按 64B 粗分。
/// 纯原子写，分配器内不做任何分配，避免重入。
const EXACT: usize = 256;
const NB: usize = EXACT + 64;
static SZ: [AtomicU64; NB] = [const { AtomicU64::new(0) }; NB];

#[inline]
fn bump_sz(size: usize) {
    if size >= (1 << 20) {
        BIG_N.fetch_add(1, Ordering::Relaxed);
        BIG_B.fetch_add(size as u64, Ordering::Relaxed);
        let i = BIG_N.load(Ordering::Relaxed) as usize - 1;
        if i < BIGLIST {
            BIG_SIZES[i].store(size as u64, Ordering::Relaxed);
        }
        trace_big(size);
    }
    let idx = if size < EXACT {
        size
    } else {
        EXACT + ((size - EXACT) / 64).min(63)
    };
    SZ[idx].fetch_add(1, Ordering::Relaxed);
}

/// `L02L05MEM_TRACE=1` 时打印每个 ≥1MB 分配的调用栈（归因 arena chunk 与
/// 其它大块，如 hashbrown 表/Vec 扩容）。分配器内打印有重入风险，但只有
/// ≥1MB 的分配会触发，而打印自身只做小分配，安全。
fn trace_big(size: usize) {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    if !*ON.get_or_init(|| std::env::var("L02L05MEM_TRACE").is_ok_and(|v| v != "0")) {
        return;
    }
    let bt = std::backtrace::Backtrace::capture();
    eprintln!("[big alloc] {size} B\n{bt}");
}

fn hist_reset() {
    for b in SZ.iter() {
        b.store(0, Ordering::Relaxed);
    }
    BIG_N.store(0, Ordering::Relaxed);
    BIG_B.store(0, Ordering::Relaxed);
    for b in BIG_SIZES.iter() {
        b.store(0, Ordering::Relaxed);
    }
}

fn hist_snapshot() -> Hist {
    Hist {
        sz: SZ.iter().map(|b| b.load(Ordering::Relaxed)).collect(),
        big_n: BIG_N.load(Ordering::Relaxed),
        big_b: BIG_B.load(Ordering::Relaxed),
        big_sizes: BIG_SIZES.iter().map(|b| b.load(Ordering::Relaxed)).collect(),
    }
}

/// 直方图快照（含 ≥1MB 大块计数与 chunk 尺寸序列）。
struct Hist {
    sz: Vec<u64>,
    big_n: u64,
    big_b: u64,
    big_sizes: Vec<u64>,
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
        bump_sz(new as usize);
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

#[path = "../L02_tyck/mod.rs"]
mod L02_tyck;
#[path = "../L03_holes/mod.rs"]
mod L03_holes;
#[path = "../L04_implicit/mod.rs"]
mod L04_implicit;
#[path = "../L05_pruning/mod.rs"]
mod L05_pruning;

use clap::Parser;
use mimalloc::MiMalloc;

#[derive(Parser)]
#[command(
    name = "l02l05mem",
    about = "L02–L05 性能版内存占用：分配计数/字节/直方图（确定性口径）"
)]
struct Cli {
    /// 章节（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    chapter: String,

    /// 负载族（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    workload: String,

    /// church 数 = 2^(k+1)（implicit/prune 默认 k=9，其余默认 11）
    #[arg(long)]
    k: Option<u32>,

    /// 稳态 churn 的测量轮数
    #[arg(long, default_value_t = 3)]
    rounds: usize,

    /// 打印各章数据结构尺寸（真实 pub(crate) 类型 + 私有类型的同构副本）
    #[arg(long)]
    sizes: bool,

    /// 跳过参考版（basic）测量——chain 族负载参考版是 O(n²)，大 k 段跑不动
    #[arg(long)]
    no_basic: bool,
}

// ---------------------------------------------------------------------------
// 每章负载表：(workload, 是否 check+nf)
// ---------------------------------------------------------------------------

fn cases_of(ch: &str) -> Vec<(&'static str, bool)> {
    match ch {
        "L02" => vec![
            ("church", true),
            ("conv", false),
            ("conv_dup", false),
            ("dup", true),
            ("dup_deep", true),
        ],
        "L03" => vec![
            ("church", true),
            ("conv", false),
            ("conv_dup", false),
            ("chain", false),
            ("solve", false),
            ("dup", true),
            ("dup_deep", true),
        ],
        "L04" => vec![
            ("church", true),
            ("implicit", false),
            ("conv", false),
            ("conv_dup", false),
            ("chain", false),
            ("solve", false),
            ("dup", true),
            ("dup_deep", true),
        ],
        "L05" => vec![
            ("church", true),
            ("implicit", false),
            ("conv", false),
            ("conv_dup", false),
            ("chain", false),
            ("solve", false),
            ("dup", true),
            ("dup_deep", true),
            ("prune", false),
        ],
        _ => unreachable!("unknown chapter {ch}"),
    }
}

const CHAPTERS: [&str; 4] = ["L02", "L03", "L04", "L05"];

fn default_k(w: &str) -> u32 {
    match w {
        // implicit/prune 是 O(n) let 链 × 每层求解，k=9 已与 bench 矩阵对齐
        "implicit" | "prune" => 9,
        _ => 11,
    }
}

// ---------------------------------------------------------------------------
// 计数助手
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Default)]
struct Count {
    allocs: u64,
    bytes: u64,
}

impl Count {
    fn sub(&self, base: Count) -> Count {
        Count {
            allocs: self.allocs - base.allocs,
            bytes: self.bytes - base.bytes,
        }
    }
}

fn snap() -> Count {
    Count {
        allocs: ALLOCS.load(Ordering::Relaxed),
        bytes: BYTES.load(Ordering::Relaxed),
    }
}

/// arena chunk 分配量（≥1MB 的分配；bumpalo chunk 分配是全局分配器唯一的
/// 大块来源）。返回 (次数, 字节)。
fn arena_bytes(h: &Hist) -> (u64, u64) {
    (h.big_n, h.big_b)
}

fn fmt_mb(b: u64) -> String {
    format!("{:.2}MB", b as f64 / 1048576.0)
}

fn fmt_count(a: u64, b: u64) -> String {
    format!("{:>9} allocs {:>10} B {:>9}", a, b, fmt_mb(b))
}

/// chunk 序列格式化（MB，去掉尾随 0）。
fn fmt_chunks(cs: &[u64]) -> String {
    let v: Vec<String> = cs
        .iter()
        .filter(|&&c| c > 0)
        .map(|&c| format!("{}", c as f64 / 1048576.0))
        .collect();
    format!("[{}]", v.join(","))
}

// ---------------------------------------------------------------------------
// 单格测量：返回 (解析, basic, fast 一次性, fast_ss 首轮, fast_ss churn/轮,
// fast_memo)
// ---------------------------------------------------------------------------

/// 各章只实现本层特色的负载生成器（L02 无 chain/solve/implicit/prune），
/// 按 (章, 负载) 显式分派。
fn src_of(ch: &str, w: &str, k: u32) -> String {
    match (ch, w) {
        ("L02", "church") => L02_tyck::bump_spine_iter::church_src(k),
        ("L02", "conv") => L02_tyck::bump_spine_iter::conv_src(k),
        ("L02", "conv_dup") => L02_tyck::bump_spine_iter::conv_dup_src(k),
        ("L02", "dup") => L02_tyck::bump_spine_iter::dup_src(k),
        ("L02", "dup_deep") => L02_tyck::bump_spine_iter::dup_deep_src(k),
        ("L03", "church") => L03_holes::bump_spine_iter::church_src(k),
        ("L03", "conv") => L03_holes::bump_spine_iter::conv_src(k),
        ("L03", "conv_dup") => L03_holes::bump_spine_iter::conv_dup_src(k),
        ("L03", "dup") => L03_holes::bump_spine_iter::dup_src(k),
        ("L03", "dup_deep") => L03_holes::bump_spine_iter::dup_deep_src(k),
        ("L03", "chain") => L03_holes::bump_spine_iter::chain_src(k),
        ("L03", "solve") => L03_holes::bump_spine_iter::solve_src(k),
        ("L04", "church") => L04_implicit::bump_spine_iter::church_src(k),
        ("L04", "conv") => L04_implicit::bump_spine_iter::conv_src(k),
        ("L04", "conv_dup") => L04_implicit::bump_spine_iter::conv_dup_src(k),
        ("L04", "dup") => L04_implicit::bump_spine_iter::dup_src(k),
        ("L04", "dup_deep") => L04_implicit::bump_spine_iter::dup_deep_src(k),
        ("L04", "chain") => L04_implicit::bump_spine_iter::chain_src(k),
        ("L04", "solve") => L04_implicit::bump_spine_iter::solve_src(k),
        ("L04", "implicit") => L04_implicit::bump_spine_iter::implicit_src(k),
        ("L05", "church") => L05_pruning::bump_spine_iter::church_src(k),
        ("L05", "conv") => L05_pruning::bump_spine_iter::conv_src(k),
        ("L05", "conv_dup") => L05_pruning::bump_spine_iter::conv_dup_src(k),
        ("L05", "dup") => L05_pruning::bump_spine_iter::dup_src(k),
        ("L05", "dup_deep") => L05_pruning::bump_spine_iter::dup_deep_src(k),
        ("L05", "chain") => L05_pruning::bump_spine_iter::chain_src(k),
        ("L05", "solve") => L05_pruning::bump_spine_iter::solve_src(k),
        ("L05", "implicit") => L05_pruning::bump_spine_iter::implicit_src(k),
        ("L05", "prune") => L05_pruning::bump_spine_iter::prune_src(k),
        _ => unreachable!("unknown (chapter, workload) = ({ch}, {w})"),
    }
}

struct Row {
    parse: Count,
    basic: Option<Count>,
    fast: Count,
    ss_growth: Count,
    ss_churn: Count,
    ss_churn_raw: Count,
    fast_memo: Option<Count>,
    arena_fast: (u64, u64),
    arena_ss: (u64, u64),
    arena_churn: (u64, u64),
    chunks_fast: Vec<u64>,
    chunks_ss: Vec<u64>,
    chunks_churn: Vec<u64>,
    hist_top: Vec<(usize, u64, u64)>, // (size_lo, allocs, bytes) 顶层小桶
}

macro_rules! measure_chapter {
    ($ch:ident, $src:expr, $nf:expr, $rounds:expr, $basic:expr) => {{
        use $ch::bump_spine_iter::Tycker;
        let src: String = $src;
        // 解析（计数，只报一次；解析对所有口径相同）
        hist_reset();
        let c0 = snap();
        let raw = $ch::parser::parser(&src, 0).expect("parse failed");
        let parse = snap().sub(c0);
        let _ = &raw;

        // basic（参考版）：计数一次（bench_check* 内部 mem::forget，泄漏
        // 不管——与 l02bench..l05bench 同口径）
        let basic = if $basic {
            let c0 = snap();
            if $nf {
                $ch::bench_check_nf(&raw);
            } else {
                $ch::bench_check(&raw);
            }
            Some(snap().sub(c0))
        } else {
            None
        };

        // fast（一次性）：每轮新建 Tycker（同 l02bench 的 `fast` 行）
        hist_reset();
        let c0 = snap();
        let mut t = Tycker::new();
        if $nf {
            t.bench_check_nf(&raw);
        } else {
            t.bench_check(&raw);
        }
        let fast = snap().sub(c0);
        let h_fast = hist_snapshot();
        drop(t);

        // fast_ss（稳态）：新建 + 首轮计数 + churn 轮计数。histogram 在首轮
        // 后立刻快照（增长期的 chunk 序列），churn 段单独一份。
        hist_reset();
        let c_new = snap();
        let mut t = Tycker::new();
        if $nf {
            t.bench_check_nf(&raw);
        } else {
            t.bench_check(&raw);
        }
        let ss_growth = snap().sub(c_new); // 含 Tycker::new：常驻缓冲 + arena 首轮
        let h_ss = hist_snapshot();
        hist_reset(); // churn 段单独计数（h_ss 已拷贝）
        let c1 = snap();
        for _ in 0..$rounds {
            if $nf {
                t.bench_check_nf(&raw);
            } else {
                t.bench_check(&raw);
            }
        }
        let ss_churn_raw = snap().sub(c1);
        let ss_churn = Count {
            allocs: ss_churn_raw.allocs / $rounds as u64,
            bytes: ss_churn_raw.bytes / $rounds as u64,
        };
        let h_churn = hist_snapshot();
        drop(t);

        // fast_memo（quote 记忆化口径；仅 nf 负载）
        let fast_memo = if $nf {
            let c0 = snap();
            let mut t = Tycker::new();
            t.bench_check_nf_memo(&raw);
            let c = snap().sub(c0);
            drop(t);
            Some(c)
        } else {
            None
        };

        // 小桶 Top-N（< 1MB），用于归因逐调用草稿
        let mut small: Vec<(usize, u64, u64)> = Vec::new();
        for (i, &c) in h_fast.sz.iter().enumerate() {
            let lo = if i < EXACT { i } else { EXACT + (i - EXACT) * 64 };
            if lo < (1 << 20) && c > 0 {
                small.push((lo, c, c * lo as u64));
            }
        }
        small.sort_by_key(|&(_, _, b)| std::cmp::Reverse(b));

        Row {
            parse,
            basic,
            fast,
            ss_growth,
            ss_churn,
            ss_churn_raw,
            fast_memo,
            arena_fast: arena_bytes(&h_fast),
            arena_ss: arena_bytes(&h_ss),
            arena_churn: arena_bytes(&h_churn),
            chunks_fast: h_fast.big_sizes.clone(),
            chunks_ss: h_ss.big_sizes.clone(),
            chunks_churn: h_churn.big_sizes.clone(),
            hist_top: small.into_iter().take(6).collect(),
        }
    }};
}

fn run_chapter(ch: &str, workloads: &[&str], k_override: Option<u32>, rounds: usize, basic: bool) {
    for &w in workloads {
        let nf = cases_of(ch)
            .iter()
            .find(|&&(n, _)| n == w)
            .map(|&(_, nf)| nf)
            .unwrap();
        let k = k_override.unwrap_or_else(|| default_k(w));
        let row = match ch {
            "L02" => measure_chapter!(L02_tyck, src_of(ch, w, k), nf, rounds, basic),
            "L03" => measure_chapter!(L03_holes, src_of(ch, w, k), nf, rounds, basic),
            "L04" => measure_chapter!(L04_implicit, src_of(ch, w, k), nf, rounds, basic),
            "L05" => measure_chapter!(L05_pruning, src_of(ch, w, k), nf, rounds, basic),
            _ => unreachable!(),
        };
        let n = 1u64 << (k + 1);
        println!("== {ch} {w} k={k} n={n} nf={nf} ==");
        println!("  parse         {}", fmt_count(row.parse.allocs, row.parse.bytes));
        if let Some(b) = row.basic {
            println!("  basic         {}", fmt_count(b.allocs, b.bytes));
        }
        println!(
            "  fast(one-shot){}  [arena {}× {} chunks {:?}]",
            fmt_count(row.fast.allocs, row.fast.bytes),
            row.arena_fast.0,
            fmt_mb(row.arena_fast.1),
            fmt_chunks(&row.chunks_fast)
        );
        let retained = row.chunks_ss.iter().copied().max().unwrap_or(0);
        println!(
            "  fast_ss growth{}  [arena {}× {} chunks {:?}] reset 后保留 {}",
            fmt_count(row.ss_growth.allocs, row.ss_growth.bytes),
            row.arena_ss.0,
            fmt_mb(row.arena_ss.1),
            fmt_chunks(&row.chunks_ss),
            fmt_mb(retained)
        );
        println!(
            "  fast_ss churn {} ({} 轮均值; 合计 {} allocs / {} B, 其中 arena {}× {})",
            fmt_count(row.ss_churn.allocs, row.ss_churn.bytes),
            rounds,
            row.ss_churn_raw.allocs,
            row.ss_churn_raw.bytes,
            row.arena_churn.0,
            fmt_mb(row.arena_churn.1)
        );
        if let Some(m) = row.fast_memo {
            println!("  fast_memo     {}", fmt_count(m.allocs, m.bytes));
        }
        if let (Some(b), Some(m)) = (row.basic, row.fast_memo) {
            println!(
                "  ratio basic/fast = {:.2}× bytes, {:.2}× allocs",
                b.bytes as f64 / row.fast.bytes as f64,
                b.allocs as f64 / row.fast.allocs as f64
            );
            let _ = m;
        } else if let Some(b) = row.basic {
            println!(
                "  ratio basic/fast = {:.2}× bytes, {:.2}× allocs",
                b.bytes as f64 / row.fast.bytes as f64,
                b.allocs as f64 / row.fast.allocs as f64
            );
        }
        println!("  small-alloc top (fast):");
        for (lo, c, b) in row.hist_top {
            println!("    size {lo:<6} {c:>8} allocs {:>10} B", b);
        }
    }
}

// ---------------------------------------------------------------------------
// 数据结构尺寸：pub(crate) 类型直接 size_of；私有类型用逐字段同构副本
// （副本法先用 L03/L04/L05 的 pub(crate) 类型交叉验证：副本尺寸 == 真实尺寸）
// ---------------------------------------------------------------------------

/// 章节私有 `Icit`（parser 的 Expl/Impl 二值枚举）的同构副本。
#[derive(Clone, Copy)]
enum IcitR {
    Expl,
    Impl,
}

// ---- L02 副本（bump_spine_iter.rs:59-175）----
enum Tm2<'a> {
    Var(u32),
    Lam(&'a str, &'a Tm2<'a>),
    App(&'a Tm2<'a>, &'a Tm2<'a>),
    U,
    Pi(&'a str, &'a Tm2<'a>, &'a Tm2<'a>),
    Let(&'a str, &'a Tm2<'a>, &'a Tm2<'a>, &'a Tm2<'a>),
}
#[repr(align(8))]
struct CloCell2<'a> {
    name: &'a str,
    env: Option<&'a EnvCons2<'a>>,
    body: &'a Tm2<'a>,
}
struct PiCell2<'a> {
    name: &'a str,
    dom: (u64,),
    env: Option<&'a EnvCons2<'a>>,
    body: &'a Tm2<'a>,
}
struct EnvCons2<'a> {
    val: (u64,),
    next: Option<&'a EnvCons2<'a>>,
}
struct Entry2 {
    f: (u64,),
    a: (u64,),
    len: u32,
    base: u32,
}
struct TCons2<'a> {
    name: &'a str,
    ty: (u64,),
    next: Option<&'a TCons2<'a>>,
}

// ---- L03 副本（+Meta/InsertedMeta/BdCons；Entry/TCons 无 icit/source）----
enum Tm3<'a> {
    Var(u32),
    Lam(&'a str, &'a Tm3<'a>),
    App(&'a Tm3<'a>, &'a Tm3<'a>),
    U,
    Pi(&'a str, &'a Tm3<'a>, &'a Tm3<'a>),
    Let(&'a str, &'a Tm3<'a>, &'a Tm3<'a>, &'a Tm3<'a>),
    Meta(u32),
    InsertedMeta(u32, Option<&'a BdCons3<'a>>),
}
struct BdCons3<'a> {
    bound: bool,
    next: Option<&'a BdCons3<'a>>,
}

// ---- L04 副本（+icit；TCons +source）----
enum Tm4<'a> {
    Var(u32),
    Lam(&'a str, IcitR, &'a Tm4<'a>),
    App(&'a Tm4<'a>, &'a Tm4<'a>, IcitR),
    U,
    Pi(&'a str, IcitR, &'a Tm4<'a>, &'a Tm4<'a>),
    Let(&'a str, &'a Tm4<'a>, &'a Tm4<'a>, &'a Tm4<'a>),
    Meta(u32),
    InsertedMeta(u32, Option<&'a BdCons4<'a>>),
}
struct BdCons4<'a> {
    bound: bool,
    next: Option<&'a BdCons4<'a>>,
}
struct Entry4 {
    f: (u64,),
    a: (u64,),
    icit: IcitR,
    len: u32,
    base: u32,
}
struct TCons4<'a> {
    name: &'a str,
    ty: (u64,),
    source: bool,
    next: Option<&'a TCons4<'a>>,
}
struct RenameScratch4<'a> {
    tasks: Vec<u8>,
    done: Vec<&'a u8>,
    done_icits: Vec<IcitR>,
    args: Vec<(u64, IcitR)>,
    popped: Vec<&'a u8>,
}
struct ConvScratch4 {
    memo: rustc_hash::FxHashSet<(u64, u64)>,
    scratch1: Vec<(u64, IcitR)>,
    scratch2: Vec<(u64, IcitR)>,
}

// ---- L05 副本（+AppPruning/PrCons/LCons）----
enum Tm5<'a> {
    Var(u32),
    Lam(&'a str, IcitR, &'a Tm5<'a>),
    App(&'a Tm5<'a>, &'a Tm5<'a>, IcitR),
    AppPruning(&'a Tm5<'a>, Option<&'a PrCons5<'a>>),
    U,
    Pi(&'a str, IcitR, &'a Tm5<'a>, &'a Tm5<'a>),
    Let(&'a str, &'a Tm5<'a>, &'a Tm5<'a>, &'a Tm5<'a>),
    Meta(u32),
}
struct PrCons5<'a> {
    slot: Option<IcitR>,
    none_run: u32,
    after_run: Option<&'a PrCons5<'a>>,
    next: Option<&'a PrCons5<'a>>,
}
struct LCons5<'a> {
    name: &'a str,
    a_t: &'a Tm5<'a>,
    t_t: Option<&'a Tm5<'a>>,
    next: Option<&'a LCons5<'a>>,
    prefix: Option<u32>,
}

macro_rules! sz {
    ($t:ty) => {
        std::mem::size_of::<$t>()
    };
}

fn print_sizes() {
    use L03_holes::bump_spine_iter as l3;
    use L04_implicit::bump_spine_iter as l4;
    use L05_pruning::bump_spine_iter as l5;

    println!("== replica cross-check (replica must equal real for pub(crate) types) ==");
    println!(
        "L03 Tm        real {:>3}  replica {:>3}   {}",
        sz!(l3::Tm<'static>),
        sz!(Tm3<'static>),
        if sz!(l3::Tm<'static>) == sz!(Tm3<'static>) { "OK" } else { "MISMATCH" }
    );
    println!(
        "L03 CloCell   real {:>3}  replica(n/a)      (L02 replica used)",
        sz!(l3::CloCell<'static>)
    );
    println!(
        "L04 Tm        real {:>3}  replica {:>3}   {}",
        sz!(l4::Tm<'static>),
        sz!(Tm4<'static>),
        if sz!(l4::Tm<'static>) == sz!(Tm4<'static>) { "OK" } else { "MISMATCH" }
    );
    println!(
        "L05 Tm        real {:>3}  replica {:>3}   {}",
        sz!(l5::Tm<'static>),
        sz!(Tm5<'static>),
        if sz!(l5::Tm<'static>) == sz!(Tm5<'static>) { "OK" } else { "MISMATCH" }
    );
    println!(
        "L05 PrCons    real {:>3}  replica {:>3}   {}",
        sz!(l5::PrCons<'static>),
        sz!(PrCons5<'static>),
        if sz!(l5::PrCons<'static>) == sz!(PrCons5<'static>) { "OK" } else { "MISMATCH" }
    );

    println!("\n== arena node sizes (bytes) ==");
    println!("L02 Tm={} CloCell={} PiCell={} EnvCons={} Entry={} TCons={}", sz!(Tm2<'static>), sz!(CloCell2<'static>), sz!(PiCell2<'static>), sz!(EnvCons2<'static>), sz!(Entry2), sz!(TCons2<'static>));
    println!(
        "L03 Tm={} BdCons={} CloCell={} PiCell={} EnvCons={} Entry={} TCons={}",
        sz!(Tm3<'static>),
        sz!(BdCons3<'static>),
        sz!(l3::CloCell<'static>),
        sz!(l3::PiCell<'static>),
        sz!(l3::EnvCons<'static>),
        sz!(Entry2),
        sz!(TCons2<'static>)
    );
    println!(
        "L04 Tm={} CloCell={} PiCell={} EnvCons={} Entry={} TCons={} RenameScratch={} ConvScratch={}",
        sz!(Tm4<'static>),
        sz!(l4::CloCell<'static>),
        sz!(l4::PiCell<'static>),
        sz!(l4::EnvCons<'static>),
        sz!(Entry4),
        sz!(TCons4<'static>),
        sz!(RenameScratch4<'static>),
        sz!(ConvScratch4)
    );
    println!(
        "L05 Tm={} PrCons={} LCons={} CloCell={} PiCell={} EnvCons={} Entry={} TCons={} RenameScratch={} ConvScratch={}",
        sz!(Tm5<'static>),
        sz!(PrCons5<'static>),
        sz!(LCons5<'static>),
        sz!(l5::CloCell<'static>),
        sz!(l5::PiCell<'static>),
        sz!(l5::EnvCons<'static>),
        sz!(Entry4),
        sz!(TCons4<'static>),
        sz!(RenameScratch4<'static>),
        sz!(ConvScratch4)
    );
    println!("\npacked value V = {} B (all chapters); RenBuf = Vec<u32> + Vec<u64> + u64", sz!(l5::V));
}

fn main() {
    let cli = Cli::parse();
    if cli.sizes {
        print_sizes();
        return;
    }
    let chapters: Vec<String> = if cli.chapter == "all" {
        CHAPTERS.iter().map(|s| s.to_string()).collect()
    } else {
        cli.chapter.split(',').map(|s| s.trim().to_string()).collect()
    };
    for ch in &chapters {
        assert!(CHAPTERS.contains(&ch.as_str()), "unknown chapter {ch}");
    }
    // 深嵌套负载（chain/solve/prune）走查递归很深——bench 同款大栈线程。
    std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || {
            for ch in &chapters {
                let all = cases_of(ch);
                let workloads: Vec<&str> = if cli.workload == "all" {
                    all.iter().map(|&(n, _)| n).collect()
                } else {
                    cli.workload
                        .split(',')
                        .map(|s| s.trim())
                        .filter(|w| all.iter().any(|&(n, _)| n == *w))
                        .collect()
                };
                run_chapter(ch, &workloads, cli.k, cli.rounds, !cli.no_basic);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
