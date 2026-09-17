//! L07 分配归因：把**指定大小的分配**（默认 88 = `Box<Val>` / `Box<Tm>`）的
//! 调用栈抓下来，符号化后聚合。用来回答"多出来的那 N 次 88B 分配是谁做的"。
//!
//! 走 `sampler` 特性借它的 `backtrace` 依赖；抓栈用静态环形缓冲，分配器内
//! 零分配（`IN_HOOK` 线程标志防重入，`IDX` 原子下标，不 push Vec）。
//!
//! 符号化需要调试信息——release profile 里没有，必须走 release-profiling：
//!
//! ```text
//! cargo build --profile release-profiling --features sampler --bin l07whoalloc
//! ./target/release-profiling/l07whoalloc.exe --imp cur --size 88 --sweep flat --n 17 --ctrl
//! ```
//!
//! `--size` 对应关系：88 = `Box<Val>`/`Box<Tm>`，120 = `Rc<SubEntry>`（σ 链条目，
//! `SubEntry` 104B + Rc 头 16B），24 = `Rc<Subst>`（8 + 16）。
//!
//! 无 `sampler` 特性时本 bin 编译成空壳（`cargo build --release` 全 bin
//! 构建不会因缺 `backtrace` 而失败）。

#![allow(dead_code)]

#[cfg(not(feature = "sampler"))]
fn main() {
    eprintln!("l07whoalloc 需要 --features sampler（配合 --profile release-profiling 才有符号）");
    std::process::exit(1);
}

// 这些直接源文件 include 的模块必须挂在 **crate 根**：被 include 的源码里有
// `crate::list`、`$crate::L07_pre` 这类绝对路径。
#[cfg(feature = "sampler")]
#[path = "../list.rs"]
mod list;
#[cfg(feature = "sampler")]
#[path = "../parser_lib.rs"]
mod parser_lib;
#[cfg(feature = "sampler")]
#[path = "../parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[cfg(feature = "sampler")]
#[path = "../pmab_gen.rs"]
mod pmab_gen;
#[cfg(feature = "sampler")]
#[path = "../bench_head/mod.rs"]
mod L07_head;
#[cfg(feature = "sampler")]
#[path = "../L07_sum_type/mod.rs"]
mod L07_sum_type;
#[cfg(feature = "sampler")]
#[path = "../bench_pre/L07_sum_type/mod.rs"]
mod L07_pre;

#[cfg(feature = "sampler")]
mod imp {
    use std::alloc::{GlobalAlloc, Layout};
    use std::cell::Cell;
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    const NF: usize = 8;
    const NS: usize = 200_000;

    static RING: [[AtomicU64; NF]; NS] = [const { [const { AtomicU64::new(0) }; NF] }; NS];
    static IDX: AtomicUsize = AtomicUsize::new(0);
    static TARGET: AtomicUsize = AtomicUsize::new(88);
    static STRIDE: AtomicUsize = AtomicUsize::new(1);
    static SEEN: AtomicU64 = AtomicU64::new(0);

    thread_local! {
        static IN_HOOK: Cell<bool> = const { Cell::new(false) };
    }

    struct Counting;

    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, l: Layout) -> *mut u8 {
            hook(l.size());
            unsafe { mimalloc::MiMalloc.alloc(l) }
        }
        unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
            unsafe { mimalloc::MiMalloc.dealloc(p, l) }
        }
        unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
            hook(new);
            unsafe { mimalloc::MiMalloc.realloc(p, l, new) }
        }
        unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
            hook(l.size());
            unsafe { mimalloc::MiMalloc.alloc_zeroed(l) }
        }
    }

    #[global_allocator]
    static A: Counting = Counting;

    fn hook(size: usize) {
        if size != TARGET.load(Ordering::Relaxed) {
            return;
        }
        let n = SEEN.fetch_add(1, Ordering::Relaxed);
        if n % STRIDE.load(Ordering::Relaxed) as u64 != 0 {
            return;
        }
        IN_HOOK.with(|h| {
            if h.get() {
                return;
            }
            h.set(true);
            let i = IDX.fetch_add(1, Ordering::Relaxed);
            if i < NS {
                let mut k = 0usize;
                backtrace::trace(|f| {
                    if k < NF {
                        RING[i][k].store(f.ip() as u64, Ordering::Relaxed);
                        k += 1;
                        true
                    } else {
                        false
                    }
                });
            }
            h.set(false);
        });
    }

    use clap::Parser;

    #[derive(Parser)]
    #[command(name = "l07whoalloc", about = "抓取指定大小分配的调用栈并聚合")]
    struct Cli {
        /// cur = 工作区，head = 已提交 HEAD（ea01207），pre = 重构前（b9d54fe）
        #[arg(long, default_value = "cur")]
        imp: String,
        /// 目标分配大小（88 = Box<Val>/Box<Tm>，120 = Rc<SubEntry>，24 = Rc<Subst>）
        #[arg(long, default_value_t = 88)]
        size: usize,
        /// 抽样步长（每 N 次抓一次）
        #[arg(long, default_value_t = 1)]
        stride: usize,
        #[arg(long, default_value = "flat")]
        sweep: String,
        #[arg(long, default_value_t = 9)]
        n: usize,
        #[arg(long)]
        ctrl: bool,
    }

    /// 只留最后 3 段模块路径（丢掉 `l07whoalloc::L07_head` 前缀、泛型实参与
    /// `impl$N` 匿名块编号），便于聚合。
    fn shorten(name: &str) -> String {
        let name = match name.find("::{{") {
            Some(p) => &name[..p],
            None => name,
        };
        let segs: Vec<&str> = name
            .split("::")
            .filter(|s| !s.starts_with("impl$") && !s.starts_with("closure"))
            .collect();
        let start = segs.len().saturating_sub(3);
        segs[start..].join("::")
    }

    fn symbolize(ips: &[u64]) -> Vec<String> {
        ips.iter()
            .filter(|&&ip| ip != 0)
            .map(|&ip| {
                let mut name = String::new();
                backtrace::resolve(ip as *mut std::ffi::c_void, |sym| {
                    if let Some(n) = sym.name() {
                        name = n.to_string();
                    }
                });
                if name.is_empty() {
                    format!("0x{ip:x}")
                } else {
                    shorten(&name)
                }
            })
            .collect()
    }

    pub fn main_inner() {
        let cli = Cli::parse();
        TARGET.store(cli.size, Ordering::Relaxed);
        STRIDE.store(cli.stride.max(1), Ordering::Relaxed);
        let src = if cli.ctrl {
            match cli.sweep.as_str() {
                "wild" => crate::pmab_gen::wild_ctrl(cli.n),
                "deep" => crate::pmab_gen::deep_ctrl(cli.n),
                _ => crate::pmab_gen::flat_ctrl(cli.n),
            }
        } else {
            match cli.sweep.as_str() {
                "wild" => crate::pmab_gen::wild_src(cli.n),
                "cart" => crate::pmab_gen::cart_src(cli.n),
                "deep" => crate::pmab_gen::deep_src(cli.n),
                _ => crate::pmab_gen::flat_src(cli.n),
            }
        };
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || {
                let ok = match cli.imp.as_str() {
                    "pre" => crate::L07_pre::run(&src, 0).is_ok(),
                    "head" => crate::L07_head::run(&src, 0).is_ok(),
                    _ => crate::L07_sum_type::run(&src, 0).is_ok(),
                };
                assert!(ok, "run 未通过");
                let taken = IDX.load(Ordering::Relaxed).min(NS);
                let total = SEEN.load(Ordering::Relaxed);
                eprintln!(
                    "== impl={} size={} sweep={} n={} ctrl={} ==\n   size-{}-allocs={} sampled={}",
                    cli.imp, cli.size, cli.sweep, cli.n, cli.ctrl, cli.size, total, taken
                );
                // 帧 0/1 = hook + GlobalAlloc 包装，从帧 2 起是真调用点
                let mut agg: std::collections::HashMap<Vec<String>, u64> = Default::default();
                for i in 0..taken {
                    let ips: Vec<u64> =
                        (0..NF).map(|k| RING[i][k].load(Ordering::Relaxed)).collect();
                    let names = symbolize(&ips);
                    let key: Vec<String> = names.into_iter().skip(2).take(5).collect();
                    *agg.entry(key).or_default() += 1;
                }
                let mut v: Vec<_> = agg.into_iter().collect();
                v.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
                for (stack, c) in v.iter().take(12) {
                    eprintln!("  {:>7}  {}", c, stack.join("  <-  "));
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(feature = "sampler")]
fn main() {
    imp::main_inner()
}
