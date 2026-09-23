//! L06–L13 性能版（`bump_spine_iter` 孪生）**内存占用**测量器（确定性分配
//! 计数口径，`l02l05mem` 的姊妹工具）。
//!
//! 与 `l02l05mem` 同族：`GlobalAlloc` 计数 + ≥1MB 大块尺寸序列 + 大小直方图，
//! 由此推导每轮 arena chunk 链、reset 后保留量、逐轮 churn 与结构尺寸。
//! 负载族与 k 对齐 `docs/bench-matrix-2026-09-20.md`（n = 2^(k+1)）。
//!
//! 章间 API 差异：
//! - L06  twin 收 `Raw`（`parser::parser`）；参考版 `bench_check(&Raw)`。
//! - L07–L10/L13  twin 收 `&[Decl]`（孪生自带 `parse`）；参考版
//!   `bench_check(&[Decl])`。
//! - L11/L12 参考版无 bench 口径，用全流程 `run(&src)` 对照孪生
//!   `run_fast(&src)`（与 l11/l12bench 的 parity 口径一致）。
//! - L13 另有 prelude 负载（`parse_prelude_files` +
//!   `bench_check_nf_bounded`，镜像 nat 内建注册边界）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l06l13mem [--chapter L06|...|L13|all]
//!                                  [--workload church|strchain|...|all] [--k 11]
//!                                  [--rounds 3] [--no-basic] [--sizes]
//! ```

#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

struct Counting;

static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
/// ≥1MB 的分配（bumpalo arena chunk 链是主要来源；Machine 大缓冲扩容次之）。
static BIG_N: AtomicU64 = AtomicU64::new(0);
static BIG_B: AtomicU64 = AtomicU64::new(0);
/// 前 24 个 ≥1MB 分配的精确大小（bumpalo chunk 序列：1MB、2MB、4MB…翻倍）。
const BIGLIST: usize = 24;
static BIG_SIZES: [AtomicU64; BIGLIST] = [const { AtomicU64::new(0) }; BIGLIST];

const EXACT: usize = 256;
const NB: usize = EXACT + 64;
static SZ: [AtomicU64; NB] = [const { AtomicU64::new(0) }; NB];

/// ≥1MB 分配之外，`L06L13MEM_TRACE_MIN=<bytes>` 可把调用栈追踪阈值降到任意值
/// （归因"每次调用分配 O(环境) 字节"这类中大块；`L06L13MEM_TRACE=1` 等价于
/// 阈值 1MB）。
///
/// **必须在 `main` 里由 `init_trace()` 设置**：分配器路径内不能读环境变量
/// （`std::env::var` 自身要分配 → 重入全局分配器 → 死锁）。默认 `usize::MAX`
/// = 关闭。
static TRACE_MIN: AtomicUsize = AtomicUsize::new(usize::MAX);
/// `L06L13MEM_TRACE_EXACT=<size>`：只追踪该精确大小的分配（归因特定桶）。
/// `usize::MAX` = 不过滤（同 `TRACE_MIN` 的哨兵；size 不可能是 MAX）。
///
/// 与 `TRACE_SKIP`/`TRACE_MAX` 一样，**也必须在 `init_trace()` 里读**——原先
/// 它们是在 `trace_big` 内用 `OnceLock` 惰性读环境变量的：第一次读发生在
/// **分配器路径内部**（`bump_sz` → `trace_big`），而 Windows 上
/// `std::env::var` 自己就要分配（`Vec<u16>` 键缓冲，键名 20-23 字符 ≈ 42-46B，
/// ≥ 低阈值 TRACE_MIN）→ 该分配重入 `bump_sz` → 再进 `trace_big` →
/// `OnceLock::get_or_init` 同线程重入自旋 ⇒ `L06L13MEM_TRACE_MIN<=46` 时
/// 死锁，size-32/40 口径的栈根本采不到。三处惰性读全部改为下面的原子量。
static TRACE_EXACT: AtomicUsize = AtomicUsize::new(usize::MAX);
/// `L06L13MEM_TRACE_SKIP=<n>`：跳过前 n 次匹配（越过 parse 段的同尺寸分配）。
static TRACE_SKIP: AtomicUsize = AtomicUsize::new(0);
/// `L06L13MEM_TRACE_MAX=<n>`：最多打印 n 条栈（默认 100）。
static TRACE_MAX: AtomicUsize = AtomicUsize::new(100);
/// 相位闸：`trace_arm()` 置 true 后才输出调用栈（测量循环在 parse 结束后
/// 置位，engine 段开始时再置位——把 parse 段噪声挡在栈外）。
static TRACE_ARM: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// 重入闸：`Backtrace::capture()` 自身要分配，低阈值下会经本分配器重新进入
/// `trace_big` 并死锁在 backtrace 库的内部锁上。线程内嵌套追踪直接抑制
/// （只采栈顶那一次）。
static IN_TRACE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn trace_arm() {
    TRACE_ARM.store(true, Ordering::Relaxed);
}

fn env_usize(key: &str) -> Option<usize> {
    std::env::var(key).ok().and_then(|v| v.parse::<usize>().ok())
}

fn init_trace() {
    // 先**读完**全部环境变量（此刻 `TRACE_MIN` 仍是 MAX，分配器路径完全不
    // 追踪），再一次性落原子量：这样 init_trace 里的分配（`env::var` 自己的
    // `Vec<u16>`/`String`）不可能走进 `trace_big` 的任何一条路径。
    let min = std::env::var("L06L13MEM_TRACE_MIN")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(if std::env::var("L06L13MEM_TRACE").is_ok_and(|v| v != "0") {
            1 << 20
        } else {
            usize::MAX
        });
    let exact = env_usize("L06L13MEM_TRACE_EXACT").filter(|&n| n > 0);
    let skip = env_usize("L06L13MEM_TRACE_SKIP");
    let max = env_usize("L06L13MEM_TRACE_MAX").filter(|&n| n > 0);

    TRACE_MIN.store(min, Ordering::Relaxed);
    // 下面三项原先在 `trace_big` 内惰性读（`OnceLock` + `env::var`），会在
    // 分配器路径里再分配而重入 → 低阈值下死锁；见 `TRACE_EXACT` 的注释。
    if let Some(n) = exact {
        TRACE_EXACT.store(n, Ordering::Relaxed);
    }
    if let Some(n) = skip {
        TRACE_SKIP.store(n, Ordering::Relaxed);
    }
    if let Some(n) = max {
        TRACE_MAX.store(n, Ordering::Relaxed);
    }
}

#[inline]
fn bump_sz(size: usize) {
    if size >= (1 << 20) {
        BIG_N.fetch_add(1, Ordering::Relaxed);
        BIG_B.fetch_add(size as u64, Ordering::Relaxed);
        let i = BIG_N.load(Ordering::Relaxed) as usize - 1;
        if i < BIGLIST {
            BIG_SIZES[i].store(size as u64, Ordering::Relaxed);
        }
    }
    if size >= TRACE_MIN.load(Ordering::Relaxed) {
        trace_big(size);
    }
    let idx = if size < EXACT {
        size
    } else {
        EXACT + ((size - EXACT) / 64).min(63)
    };
    SZ[idx].fetch_add(1, Ordering::Relaxed);
}

fn trace_big(size: usize) {
    // `L06L13MEM_TRACE_EXACT=<size>`：只追踪该精确大小的分配（归因特定桶）。
    // 原子量（`init_trace` 里读）：分配器路径内不得读环境变量，见常量注释。
    let exact = TRACE_EXACT.load(Ordering::Relaxed);
    if exact != usize::MAX && size != exact {
        return;
    }
    if !TRACE_ARM.load(Ordering::Relaxed) {
        return; // 相位闸未开：parse 段噪声不抽样
    }
    // **重入闸**：`Backtrace::capture()` 自身要分配，低阈值下会经本分配器
    // 重新进入本函数并死锁在 backtrace 库的内部锁上。嵌套追踪直接抑制
    // （只采栈顶那一次；`swap` 返回旧值，已在追踪中即为 true）。
    if IN_TRACE.swap(true, Ordering::Relaxed) {
        return;
    }
    let _guard = TraceGuard;
    // `L06L13MEM_TRACE_SKIP=<n>`：跳过前 n 次匹配（越过 parse 段的同尺寸分配）。
    let skip = TRACE_SKIP.load(Ordering::Relaxed);
    static N: AtomicUsize = AtomicUsize::new(0);
    let i = N.fetch_add(1, Ordering::Relaxed);
    if i < skip {
        return;
    }
    let cap: usize = TRACE_MAX.load(Ordering::Relaxed);
    if i - skip >= cap {
        return;
    }
    let bt = std::backtrace::Backtrace::capture();
    eprintln!("[big alloc] {size} B\n{bt}");
}

/// 重入闸的 RAII 复位（含 panic 路径）。
struct TraceGuard;

impl Drop for TraceGuard {
    fn drop(&mut self) {
        IN_TRACE.store(false, Ordering::Relaxed);
    }
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

#[path = "../bimap.rs"]
mod bimap;

#[path = "../parser_lib.rs"]
mod parser_lib;
#[path = "../parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../L06_string/mod.rs"]
mod L06_string;
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

use clap::Parser;
use mimalloc::MiMalloc;

#[derive(Parser)]
#[command(
    name = "l06l13mem",
    about = "L06–L13 性能版内存占用：分配计数/字节/直方图（确定性口径）"
)]
struct Cli {
    /// 章节（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    chapter: String,

    /// 负载族（逗号分隔或 all）
    #[arg(long, default_value = "all")]
    workload: String,

    /// church 数 = 2^(k+1)（enum/gadt/moduletree 固定源；traitchain 默认 9）
    #[arg(long)]
    k: Option<u32>,

    /// 稳态 churn 的测量轮数
    #[arg(long, default_value_t = 3)]
    rounds: usize,

    /// 跳过参考版（basic）测量——参考版超线性/无 bench 口径的负载跑不动
    #[arg(long)]
    no_basic: bool,

    /// 打印各章数据结构尺寸（pub(crate) 类型直接 size_of）
    #[arg(long)]
    sizes: bool,
}

// ---------------------------------------------------------------------------
// bench 本地生成器（从 l07/l09/l10/l11bench 逐字移植，保持负载同源）
// ---------------------------------------------------------------------------

fn natadd_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n\
         def add(x: Nat, y: Nat): Nat =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\n\n\
         def p0 : Nat = succ (succ zero)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

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

fn macro_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        r#"enum Nat {
    zero
    succ(x: Nat)
}

macro_rules make_bool {
    (yes) => {
        enum Yes { y }
    }
}

make_bool yes

def b = y

println b

macro_rules addtwo {
    ($x: raw) => { succ (succ $x) }
}

def c0 : Nat = zero
"#,
    );
    for i in 1..n {
        s += &format!("def c{i} : Nat = addtwo c{}\n", i - 1);
    }
    s
}

/// 诊断负载（不进正式表）：分离 traitchain O(n²) 的因子。
/// - `diag_chain`：标准 traitchain（n decl + n 方法调用，接收者 c{i-1}）。
/// - `diag_fixed`：n decl + n 方法调用，但接收者恒为 c0（接收者链不增长）。
/// - `diag_nest`：1 个 decl，体内 n 层嵌套方法调用（decl 表不增长）。
/// - `diag_plain`：n decl 普通 def 链（无方法调用），对照基线。
fn diag_src(kind: &str, k: u32) -> String {
    let n = 1u64 << (k + 1);
    let head = r#"enum Nat {
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
"#;
    match kind {
        "diag_chain" => {
            let mut s = String::from(head);
            for i in 1..n {
                s += &format!("def c{i} : Nat = c{}.say zero\n", i - 1);
            }
            s
        }
        "diag_fixed" => {
            let mut s = String::from(head);
            for i in 1..n {
                s += &format!("def c{i} : Nat = c0.say zero\n");
            }
            s
        }
        "diag_nest" => {
            let mut s = String::from(head);
            let mut body = String::from("zero");
            for _ in 0..n {
                body = format!("c0.say ({})", body);
            }
            s += &format!("def c : Nat = {}\n", body);
            s
        }
        "diag_plain" => {
            let mut s = String::from(head);
            for i in 1..n {
                s += &format!("def c{i} : Nat = c{}\n", i - 1);
            }
            s
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// 每章负载表：(workload, k, 是否 check+nf)
// ---------------------------------------------------------------------------

const CHAPTERS: [&str; 8] = ["L06", "L07", "L08", "L09", "L10", "L11", "L12", "L13"];
// 诊断章（不进 CHAPTERS 主表，仅 --chapter L10diag 可用）
const DIAG_CHAPTER: &str = "L10diag";

fn cases_of(ch: &str) -> Vec<(&'static str, u32, bool)> {
    match ch {
        // (workload, k, nf) —— k 对齐 bench-matrix-2026-09-20
        "L06" => vec![
            ("church", 11, true),
            ("implicit", 9, false),
            ("prune", 9, false),
            ("solve", 11, false),
            ("strchain", 11, true),
            ("global", 11, true),
        ],
        "L07" => vec![
            ("church", 11, true),
            ("strchain", 11, true),
            ("global", 11, true),
            ("match", 11, true),
            ("enum", 9, true),
        ],
        "L08" => vec![
            ("church", 11, true),
            ("strchain", 11, true),
            ("global", 11, true),
            ("match", 11, true),
            ("enum", 9, true),
            ("struct", 11, true),
        ],
        "L09" => vec![
            ("church", 11, true),
            ("strchain", 11, true),
            ("match", 11, true),
            ("enum", 9, true),
            ("struct", 11, true),
            ("universe", 11, true),
        ],
        "L10" => vec![
            ("church", 11, true),
            ("strchain", 11, true),
            ("match", 11, true),
            ("struct", 11, true),
            ("universe", 11, true),
            ("traitchain", 9, true),
        ],
        "L11" => vec![
            ("church", 11, true),
            ("natadd", 11, true),
            ("strchain", 11, true),
            ("match", 11, true),
            ("struct", 11, true),
            ("macro", 11, true),
            ("universe", 11, true),
            ("traitchain", 11, true),
        ],
        "L12" => vec![
            ("church", 11, true),
            ("natadd", 11, true),
            ("strchain", 11, true),
            ("match", 11, true),
            ("struct", 11, true),
            ("traitchain", 11, true),
            ("universe", 11, true),
            ("macro", 11, true),
        ],
        "L13" => vec![
            ("church", 11, true),
            ("natadd", 11, true),
            ("gadt", 9, true),
            ("strchain", 11, true),
            ("match", 11, true),
            ("enum", 9, true),
            ("struct", 11, true),
            ("moduletree", 9, true),
        ],
        // 诊断负载（L10 traitchain O(n²) 归因；k 与 traitchain 对齐）
        "L10diag" => vec![
            ("diag_chain", 9, true),
            ("diag_fixed", 9, true),
            ("diag_nest", 9, true),
            ("diag_plain", 9, true),
        ],
        _ => unreachable!("unknown chapter {ch}"),
    }
}

/// 生成负载源。孪生自带生成器优先；bench 本地移植的四个（natadd/universe/
/// traitchain/macro）按章分派。
fn src_of(ch: &str, w: &str, k: u32) -> String {
    match (ch, w) {
        ("L06", "church") => L06_string::bump_spine_iter::church_src(k),
        ("L06", "implicit") => L06_string::bump_spine_iter::implicit_src(k),
        ("L06", "prune") => L06_string::bump_spine_iter::prune_src(k),
        ("L06", "solve") => L06_string::bump_spine_iter::solve_src(k),
        ("L06", "strchain") => L06_string::bump_spine_iter::strchain_src(k),
        ("L06", "global") => L06_string::bump_spine_iter::globals_src(k),
        ("L07", "church") => L07_sum_type::bump_spine_iter::church_src(k),
        ("L07", "strchain") => L07_sum_type::bump_spine_iter::strchain_src(k),
        ("L07", "global") => L07_sum_type::bump_spine_iter::globals_src(k),
        ("L07", "match") => L07_sum_type::bump_spine_iter::match_src(k),
        ("L07", "enum") => L07_sum_type::bump_spine_iter::enum_src(),
        ("L08", "church") => L08_product_type::bump_spine_iter::church_src(k),
        ("L08", "strchain") => L08_product_type::bump_spine_iter::strchain_src(k),
        ("L08", "global") => L08_product_type::bump_spine_iter::globals_src(k),
        ("L08", "match") => L08_product_type::bump_spine_iter::match_src(k),
        ("L08", "enum") => L08_product_type::bump_spine_iter::enum_src(),
        ("L08", "struct") => L08_product_type::bump_spine_iter::struct_src(k),
        ("L09", "church") => L09_mltt::bump_spine_iter::church_src(k),
        ("L09", "strchain") => L09_mltt::bump_spine_iter::strchain_src(k),
        ("L09", "match") => L09_mltt::bump_spine_iter::match_src(k),
        ("L09", "enum") => L09_mltt::bump_spine_iter::enum_src(),
        ("L09", "struct") => L09_mltt::bump_spine_iter::struct_src(k),
        ("L09", "universe") => universe_src(k),
        ("L10", "church") => L10_typeclass::bump_spine_iter::church_src(k),
        ("L10", "strchain") => L10_typeclass::bump_spine_iter::strchain_src(k),
        ("L10", "match") => L10_typeclass::bump_spine_iter::match_src(k),
        ("L10", "struct") => L10_typeclass::bump_spine_iter::struct_src(k),
        ("L10", "universe") => universe_src(k),
        ("L10", "traitchain") => traitchain_src(k),
        ("L11", "church") => L11_macro::bump_spine_iter::church_src(k),
        ("L11", "natadd") => L11_macro::bump_spine_iter::natadd_src(k),
        ("L11", "strchain") => L11_macro::bump_spine_iter::strchain_src(k),
        ("L11", "match") => L11_macro::bump_spine_iter::match_src(k),
        ("L11", "struct") => L11_macro::bump_spine_iter::struct_src(k),
        ("L11", "macro") => macro_src(k),
        ("L11", "universe") => universe_src(k),
        ("L11", "traitchain") => traitchain_src(k),
        ("L12", "church") => L12_canonical::bump_spine_iter::church_src(k),
        ("L12", "natadd") => L12_canonical::bump_spine_iter::natadd_src(k),
        ("L12", "strchain") => L12_canonical::bump_spine_iter::strchain_src(k),
        ("L12", "match") => L12_canonical::bump_spine_iter::match_src(k),
        ("L12", "struct") => L12_canonical::bump_spine_iter::struct_src(k),
        ("L12", "traitchain") => traitchain_src(k),
        ("L12", "universe") => universe_src(k),
        ("L12", "macro") => macro_src(k),
        ("L13", "church") => L13_namespace::bump_spine_iter::church_src(k),
        ("L13", "natadd") => L13_namespace::bump_spine_iter::natadd_src(k),
        ("L13", "gadt") => L13_namespace::bump_spine_iter::gadt_src(),
        ("L13", "strchain") => L13_namespace::bump_spine_iter::strchain_src(k),
        ("L13", "match") => L13_namespace::bump_spine_iter::match_src(k),
        ("L13", "enum") => L13_namespace::bump_spine_iter::enum_src(),
        ("L13", "struct") => L13_namespace::bump_spine_iter::struct_src(k),
        ("L13", "moduletree") => L13_namespace::bump_spine_iter::moduletree_src(),
        ("L10", "diag_chain") => diag_src("diag_chain", k),
        ("L10", "diag_fixed") => diag_src("diag_fixed", k),
        ("L10", "diag_nest") => diag_src("diag_nest", k),
        ("L10", "diag_plain") => diag_src("diag_plain", k),
        // 诊断章名直接命中（run_chapter 传进来的 ch 是 "L10diag"）
        ("L10diag", "diag_chain") => diag_src("diag_chain", k),
        ("L10diag", "diag_fixed") => diag_src("diag_fixed", k),
        ("L10diag", "diag_nest") => diag_src("diag_nest", k),
        ("L10diag", "diag_plain") => diag_src("diag_plain", k),
        _ => unreachable!("unknown (chapter, workload) = ({ch}, {w})"),
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

struct Hist {
    sz: Vec<u64>,
    big_n: u64,
    big_b: u64,
    big_sizes: Vec<u64>,
}

fn hist_snapshot() -> Hist {
    Hist {
        sz: SZ.iter().map(|b| b.load(Ordering::Relaxed)).collect(),
        big_n: BIG_N.load(Ordering::Relaxed),
        big_b: BIG_B.load(Ordering::Relaxed),
        big_sizes: BIG_SIZES.iter().map(|b| b.load(Ordering::Relaxed)).collect(),
    }
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

fn arena_bytes(h: &Hist) -> (u64, u64) {
    (h.big_n, h.big_b)
}

fn fmt_mb(b: u64) -> String {
    format!("{:.2}MB", b as f64 / 1048576.0)
}

fn fmt_count(a: u64, b: u64) -> String {
    format!("{:>9} allocs {:>10} B {:>9}", a, b, fmt_mb(b))
}

fn fmt_chunks(cs: &[u64]) -> String {
    let v: Vec<String> = cs
        .iter()
        .filter(|&&c| c > 0)
        .map(|&c| format!("{}", c as f64 / 1048576.0))
        .collect();
    format!("[{}]", v.join(","))
}

// ---------------------------------------------------------------------------
// 单格测量
// ---------------------------------------------------------------------------

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
    hist_top: Vec<(usize, u64, u64)>,
}

/// L06（twin 收 `Raw`）。
macro_rules! measure_raw_chapter {
    ($ch:ident, $src:expr, $nf:expr, $rounds:expr, $basic:expr) => {{
        use $ch::bump_spine_iter::Tycker;
        let src: String = $src;
        hist_reset();
        let c0 = snap();
        let raw = $ch::parser::parser(&src, 0).expect("parse failed");
        let parse = snap().sub(c0);
        let _ = &raw;

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

        hist_reset();
        let c_new = snap();
        let mut t = Tycker::new();
        if $nf {
            t.bench_check_nf(&raw);
        } else {
            t.bench_check(&raw);
        }
        let ss_growth = snap().sub(c_new);
        let h_ss = hist_snapshot();
        hist_reset();
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
            hist_top: small.into_iter().take(6).collect(),
        }
    }};
}

/// L07–L10/L13（twin 收 `&[Decl]`，参考版有 bench_check 口径）。
macro_rules! measure_decl_chapter {
    ($ch:ident, $src:expr, $nf:expr, $rounds:expr, $basic:expr) => {{
        use $ch::bump_spine_iter::{parse, Tycker};
        let src: String = $src;
        hist_reset();
        let c0 = snap();
        let decls = parse(&src, 0).expect("parse failed");
        let parse = snap().sub(c0);
        let _ = &decls;

        let basic = if $basic {
            let c0 = snap();
            if $nf {
                $ch::bench_check_nf(&decls);
            } else {
                $ch::bench_check(&decls);
            }
            Some(snap().sub(c0))
        } else {
            None
        };

        hist_reset();
        let c0 = snap();
        let mut t = Tycker::new();
        trace_arm(); // 开栈抽样：parse 段已结束，此后全是 engine 分配
        if $nf {
            t.bench_check_nf(&decls);
        } else {
            t.bench_check(&decls);
        }
        let fast = snap().sub(c0);
        let h_fast = hist_snapshot();
        drop(t);
        crate::TRACE_ARM.store(false, std::sync::atomic::Ordering::Relaxed);

        hist_reset();
        let c_new = snap();
        let mut t = Tycker::new();
        if $nf {
            t.bench_check_nf(&decls);
        } else {
            t.bench_check(&decls);
        }
        let ss_growth = snap().sub(c_new);
        let h_ss = hist_snapshot();
        hist_reset();
        let c1 = snap();
        for _ in 0..$rounds {
            if $nf {
                t.bench_check_nf(&decls);
            } else {
                t.bench_check(&decls);
            }
        }
        let ss_churn_raw = snap().sub(c1);
        let ss_churn = Count {
            allocs: ss_churn_raw.allocs / $rounds as u64,
            bytes: ss_churn_raw.bytes / $rounds as u64,
        };
        let h_churn = hist_snapshot();
        drop(t);

        let fast_memo = if $nf {
            let c0 = snap();
            let mut t = Tycker::new();
            t.bench_check_nf_memo(&decls);
            let c = snap().sub(c0);
            drop(t);
            Some(c)
        } else {
            None
        };

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
            hist_top: small.into_iter().take(6).collect(),
        }
    }};
}

/// L11/L12（参考版无 bench 口径：全流程 `run` vs 孪生 `run_fast`）。
macro_rules! measure_run_chapter {
    ($ch:ident, $src:expr, $nf:expr, $rounds:expr, $basic:expr) => {{
        use $ch::bump_spine_iter::{parse, Tycker};
        let src: String = $src;
        hist_reset();
        let c0 = snap();
        let decls = parse(&src, 0).expect("parse failed");
        let parse = snap().sub(c0);
        let _ = &decls;

        let basic = if $basic {
            let c0 = snap();
            let _ = $ch::run(&src, 0);
            Some(snap().sub(c0))
        } else {
            None
        };

        hist_reset();
        let c0 = snap();
        let mut t = Tycker::new();
        trace_arm(); // 开栈抽样：parse 段已结束，此后全是 engine 分配
        if $nf {
            t.bench_check_nf(&decls);
        } else {
            t.bench_check(&decls);
        }
        let fast = snap().sub(c0);
        let h_fast = hist_snapshot();
        drop(t);
        crate::TRACE_ARM.store(false, std::sync::atomic::Ordering::Relaxed);

        hist_reset();
        let c_new = snap();
        let mut t = Tycker::new();
        if $nf {
            t.bench_check_nf(&decls);
        } else {
            t.bench_check(&decls);
        }
        let ss_growth = snap().sub(c_new);
        let h_ss = hist_snapshot();
        hist_reset();
        let c1 = snap();
        for _ in 0..$rounds {
            if $nf {
                t.bench_check_nf(&decls);
            } else {
                t.bench_check(&decls);
            }
        }
        let ss_churn_raw = snap().sub(c1);
        let ss_churn = Count {
            allocs: ss_churn_raw.allocs / $rounds as u64,
            bytes: ss_churn_raw.bytes / $rounds as u64,
        };
        let h_churn = hist_snapshot();
        drop(t);

        let fast_memo = if $nf {
            let c0 = snap();
            let mut t = Tycker::new();
            t.bench_check_nf_memo(&decls);
            let c = snap().sub(c0);
            drop(t);
            Some(c)
        } else {
            None
        };

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
            hist_top: small.into_iter().take(6).collect(),
        }
    }};
}

fn print_row(ch: &str, w: &str, k: u32, nf: bool, rounds: usize, row: Row) {
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
    if let Some(b) = row.basic {
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

fn run_chapter(ch: &str, workloads: &[&str], k_override: Option<u32>, rounds: usize, basic: bool) {
    for &w in workloads {
        let (_, dk, nf) = cases_of(ch).iter().find(|&&(n, _, _)| n == w).copied().unwrap();
        let k = k_override.unwrap_or(dk);
        let src = src_of(ch, w, k);
        let row = match ch {
            "L06" => measure_raw_chapter!(L06_string, src, nf, rounds, basic),
            "L07" => measure_decl_chapter!(L07_sum_type, src, nf, rounds, basic),
            "L08" => measure_decl_chapter!(L08_product_type, src, nf, rounds, basic),
            "L09" => measure_decl_chapter!(L09_mltt, src, nf, rounds, basic),
            "L10" => measure_decl_chapter!(L10_typeclass, src, nf, rounds, basic),
            "L11" => measure_run_chapter!(L11_macro, src, nf, rounds, basic),
            "L12" => measure_run_chapter!(L12_canonical, src, nf, rounds, basic),
            "L13" => measure_decl_chapter!(L13_namespace, src, nf, rounds, basic),
            _ => measure_decl_chapter!(L10_typeclass, src, nf, rounds, basic), // L10diag
        };
        print_row(ch, w, k, nf, rounds, row);
    }
}

// ---------------------------------------------------------------------------
// L13 prelude 负载（core 15 文件；prime + nat 注册边界）
// ---------------------------------------------------------------------------

const CORE: &[(&str, &str)] = &[
    ("op", include_str!("../prelude/core/op.typort")),
    ("eq", include_str!("../prelude/core/eq.typort")),
    ("nat", include_str!("../prelude/core/nat.typort")),
    ("calc", include_str!("../prelude/core/calc.typort")),
    ("bool", include_str!("../prelude/core/bool.typort")),
    ("option", include_str!("../prelude/data/option.typort")),
    ("result", include_str!("../prelude/data/result.typort")),
    ("order", include_str!("../prelude/data/order.typort")),
    ("void", include_str!("../prelude/core/void.typort")),
    ("decidable", include_str!("../prelude/data/decidable.typort")),
    ("vec", include_str!("../prelude/data/vec.typort")),
    ("either", include_str!("../prelude/data/either.typort")),
    ("list", include_str!("../prelude/data/list.typort")),
    ("string", include_str!("../prelude/data/string.typort")),
    ("nonempty", include_str!("../prelude/data/nonempty.typort")),
];

fn run_l13_prelude(rounds: usize, basic: bool) {
    use L13_namespace::bump_spine_iter::Tycker;
    hist_reset();
    let c0 = snap();
    let p = L13_namespace::parse_prelude_files(CORE);
    let parse = snap().sub(c0);
    println!(
        "== L13 prelude-core ({} files, {} decls, failed={:?}) ==",
        CORE.len(),
        p.decls.len(),
        p.failed
    );
    println!("  parse         {}", fmt_count(parse.allocs, parse.bytes));

    if basic {
        let c0 = snap();
        let n = L13_namespace::bench_check_nf_bounded(&p.decls, &p.nat_after);
        let b = snap().sub(c0);
        println!(
            "  basic         {} (nodes={n})",
            fmt_count(b.allocs, b.bytes)
        );
    }

    hist_reset();
    let c0 = snap();
    let mut t = Tycker::new();
    let n = t.bench_check_nf_bounded(&p.decls, &p.nat_after);
    let fast = snap().sub(c0);
    let h_fast = hist_snapshot();
    println!(
        "  fast(one-shot){}  [arena {}× {} chunks {:?}] (nodes={n})",
        fmt_count(fast.allocs, fast.bytes),
        h_fast.big_n,
        fmt_mb(h_fast.big_b),
        fmt_chunks(&h_fast.big_sizes)
    );

    // 观察面成本对照：L13BENCH_NOBSERVE=1 关掉 typ_pretty / hover / inlay 渲染
    // （bench 口径仅量化"孪生为 LSP 观察面额外付的内存"，与参考版无关）。
    if std::env::var_os("L13BENCH_NOBSERVE").is_some() {
        let c0 = snap();
        let mut t = Tycker::new();
        let n3 = t.bench_check_nf_bounded(&p.decls, &p.nat_after);
        let c = snap().sub(c0);
        println!(
            "  fast(no-obs)  {} (nodes={n3})",
            fmt_count(c.allocs, c.bytes)
        );
    }

    hist_reset();
    let c_new = snap();
    let mut t = Tycker::new();
    let n2 = t.bench_check_nf_bounded(&p.decls, &p.nat_after);
    let ss_growth = snap().sub(c_new);
    let h_ss = hist_snapshot();
    hist_reset();
    let c1 = snap();
    for _ in 0..rounds {
        t.bench_check_nf_bounded(&p.decls, &p.nat_after);
    }
    let ss_churn_raw = snap().sub(c1);
    let h_churn = hist_snapshot();
    let ss_churn = Count {
        allocs: ss_churn_raw.allocs / rounds as u64,
        bytes: ss_churn_raw.bytes / rounds as u64,
    };
    let retained = h_ss.big_sizes.iter().copied().max().unwrap_or(0);
    println!(
        "  fast_ss growth{}  [arena {}× {} chunks {:?}] reset 后保留 {} (nodes={n2})",
        fmt_count(ss_growth.allocs, ss_growth.bytes),
        h_ss.big_n,
        fmt_mb(h_ss.big_b),
        fmt_chunks(&h_ss.big_sizes),
        fmt_mb(retained)
    );
    println!(
        "  fast_ss churn {} ({} 轮均值; 合计 {} allocs / {} B, 其中 arena {}× {})",
        fmt_count(ss_churn.allocs, ss_churn.bytes),
        rounds,
        ss_churn_raw.allocs,
        ss_churn_raw.bytes,
        h_churn.big_n,
        fmt_mb(h_churn.big_b)
    );
}

// ---------------------------------------------------------------------------
// 结构尺寸
// ---------------------------------------------------------------------------

fn print_sizes() {
    use L06_string::bump_spine_iter as l6;
    use L07_sum_type::bump_spine_iter as l7;
    use L08_product_type::bump_spine_iter as l8;
    use L09_mltt::bump_spine_iter as l9;
    use L10_typeclass::bump_spine_iter as l10;
    use L11_macro::bump_spine_iter as l11;
    use L12_canonical::bump_spine_iter as l12;
    use L13_namespace::bump_spine_iter as l13;

    macro_rules! p {
        ($label:expr, $($t:ty),+) => {
            println!("{:<26} {}", $label, vec![$(format!("{}", std::mem::size_of::<$t>())),+].join(" / "))
        };
    }
    println!("(sizes in bytes; columns = L06 / L07 / L08 / L09 / L10 / L11 / L12 / L13)");
    p!("Tm", l6::Tm<'static>, l7::Tm<'static>, l8::Tm<'static>, l9::Tm<'static>, l10::Tm<'static>, l11::Tm<'static>, l12::Tm<'static>, l13::Tm<'static>);
    p!("V (packed)", l6::V, l7::V, l8::V, l9::V, l10::V, l11::V, l12::V, l13::V);
    p!("EnvCons", l6::EnvCons<'static>, l7::EnvCons<'static>, l8::EnvCons<'static>, l9::EnvCons<'static>, l10::EnvCons<'static>, l11::EnvCons<'static>, l12::EnvCons<'static>, l13::EnvCons<'static>);
    p!("CloCell", l6::CloCell<'static>, l7::CloCell<'static>, l8::CloCell<'static>, l9::CloCell<'static>, l10::CloCell<'static>, l11::CloCell<'static>, l12::CloCell<'static>, l13::CloCell<'static>);
    p!("PiCell", l6::PiCell<'static>, l7::PiCell<'static>, l8::PiCell<'static>, l9::PiCell<'static>, l10::PiCell<'static>, l11::PiCell<'static>, l12::PiCell<'static>, l13::PiCell<'static>);
    p!("MetaEntry", l6::MetaEntry, l7::MetaEntry, l8::MetaEntry, l9::MetaEntry, l10::MetaEntry, l11::MetaEntry, l12::MetaEntry, l13::MetaEntry);
    // L06–L08 的 decl 表条目叫 DeclEntryF（prim 侧）；L09/L10 起 globals 退化为
    // 扁平 &[V]（无 DeclEntryF）；L11–L13 叫 DeclEntry
    println!(
        "{:<26} L06={} L07={} L08={} (L09+ globals 为扁平 &[V]，无条目结构体)",
        "DeclEntryF",
        std::mem::size_of::<l6::DeclEntryF>(),
        std::mem::size_of::<l7::DeclEntryF>(),
        std::mem::size_of::<l8::DeclEntryF>(),
    );
    p!("DeclEntry", l11::DeclEntry, l12::DeclEntry, l13::DeclEntry);
    p!("Machine", l6::Machine, l7::Machine, l8::Machine, l9::Machine, l10::Machine, l11::Machine, l12::Machine, l13::Machine);
    p!("Tycker", l6::Tycker, l7::Tycker, l8::Tycker, l9::Tycker, l10::Tycker, l11::Tycker, l12::Tycker, l13::Tycker);
}

fn main() {
    let cli = Cli::parse();
    init_trace();
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
        assert!(
            CHAPTERS.contains(&ch.as_str()) || ch == DIAG_CHAPTER,
            "unknown chapter {ch}"
        );
    }
    // 深嵌套负载走查递归很深——bench 同款大栈线程。
    std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || {
            for ch in &chapters {
                if ch == "L13"
                    && (cli.workload == "all" || cli.workload.split(',').any(|x| x.trim() == "prelude"))
                {
                    run_l13_prelude(cli.rounds, !cli.no_basic);
                }
                let all = cases_of(ch);
                let workloads: Vec<&str> = if cli.workload == "all" {
                    all.iter().map(|&(n, _, _)| n).collect()
                } else {
                    cli.workload
                        .split(',')
                        .map(|s| s.trim())
                        .filter(|w| all.iter().any(|&(n, _, _)| n == *w))
                        .collect()
                };
                run_chapter(ch, &workloads, cli.k, cli.rounds, !cli.no_basic);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
