//! Tiny IP-capture sampling profiler. Lazy symbol resolution at the end.
//!
//! # 入口 tick 序列的区间归因（S6 2026-09-23 增强）
//!
//! 上一轮（docs/perf-l13-round-2026-09-22.md §3.6）指出：入口 tick 式采样给
//! 出的是「入口调用频度 × 调用链」而非墙钟 self%。本版在**不改 tick 调用点
//! 签名**（`crate::sampler::tick()`）的前提下补上 self% 口径：
//!
//! - `tick()` 标 `#[track_caller]`——`Location::caller()` 以近乎零成本
//!   （一个寄存器实参，指向静态 `Location`，其指针即调用点身份）拿到每个
//!   tick 的**调用点**（machine.rs 的 eval/unify/check/infer_expr 等行号）。
//! - active 期间每个 tick 取一次时间戳（x86_64 走 `_rdtsc`，enable 时对
//!   `Instant` 校准 ns/cycle；非 x86_64 回退 `Instant::now()`）。相邻两个
//!   tick 的时间差 = 前一个 tick 点到下一个 tick 点之间的独占区间，记到
//!   前一个 tick 点（"入口 tick 序列的区间归因"）。
//! - 栈捕获（每 `L13SAMPLE_TICK` 个 tick 一次，默认 200）同时记录捕获间隔，
//!   可输出**时间加权链**（每条链分到两次捕获之间的墙钟）。
//!
//! 输出四件套（`write_folded(path)` 被调用时**顺带**写出同目录兄弟文件，
//! 因此 `src/bin/l13bench.rs` 无需改动即可拿到全部口径）：
//! - `path`             —— 原有频度 × 链 folded（口径不变）。
//! - `path.self.folded` —— self% 口径：每行 `sampler_self;<file:line> <ns>`，
//!   权重 = 记到该 tick 点的独占纳秒。
//! - `path.time.folded` —— 时间加权链 folded：权重 = 两次捕获间隔的纳秒。
//! - `path.self.txt`    —— 人读报告（self Top 表 + tick 计数 + ns/tick）。
//!
//! 开销口径（采样构建且 active 时）：每 tick ≈ rdtsc + 少量比较（~15ns）；
//! 关闭路径从旧版的「每 tick 一把 mutex」改为一次 `AtomicBool` 读（~1ns）。
//! `L13SAMPLE_NOTS=1` 关掉时间戳记账回到纯频度模式（最低开销）；
//! `L13SAMPLE_TICK=n` 调栈捕获节奏（默认 200）。采样是**单线程**口径
//! （backtrace::trace 只采当前线程栈），TLS 记账与之一致。

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::panic::Location;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

#[derive(Clone)]
struct RawStack {
    ips: Vec<usize>,
}

/// One tick 调用点：`Location` 指针身份 + 累计的独占时间/次数。
struct Site {
    loc: usize,
    file: String,
    line: u32,
    /// 记到本 tick 点的独占时间（校准后的纳秒）。
    self_ns: u64,
    ticks: u64,
}

/// Per-thread 记账（采样口径本来就是单线程的：栈捕获只覆盖当前线程）。
struct Acc {
    /// 上一个 tick 的时间戳（cycle；0 = 尚无）。
    last_t: u64,
    /// 区间归属：上一个 tick 的 site 下标。
    prev_site: usize,
    sites: Vec<Site>,
    /// `Location::caller()` 指针 -> 下标的查找缓存（连续同点 tick 是快路径）。
    last_ptr: usize,
    last_idx: usize,
    /// 栈捕获节奏（legacy skip_counter 语义）。
    skip: u32,
    capture_every: u32,
    /// 上次栈捕获的时间戳（时间加权链用）。
    cap_last_t: u64,
    raw: Vec<RawStack>,
    /// 与 `raw` 平行：该捕获距上一次捕获的时间（cycle）。
    raw_dt: Vec<u64>,
    ns_per_cycle: f64,
    no_ts: bool,
}

impl Acc {
    fn new() -> Self {
        Acc {
            last_t: 0,
            prev_site: 0,
            sites: Vec::new(),
            last_ptr: 0,
            last_idx: 0,
            skip: 0,
            capture_every: 200,
            cap_last_t: 0,
            raw: Vec::new(),
            raw_dt: Vec::new(),
            ns_per_cycle: 0.0,
            no_ts: false,
        }
    }

    /// 只用指针身份查表（热路径零分配）；file/line 仅在**首次登记**时物化。
    fn site_of(&mut self, loc: usize, file: impl FnOnce() -> String, line: impl FnOnce() -> u32) -> usize {
        if loc == self.last_ptr {
            return self.last_idx;
        }
        if let Some(i) = self.sites.iter().position(|s| s.loc == loc) {
            self.last_ptr = loc;
            self.last_idx = i;
            return i;
        }
        self.sites.push(Site { loc, file: file(), line: line(), self_ns: 0, ticks: 0 });
        self.last_ptr = loc;
        self.last_idx = self.sites.len() - 1;
        self.last_idx
    }
}

thread_local! {
    static ACC: RefCell<Acc> = RefCell::new(Acc::new());
}

static ACTIVE: AtomicBool = AtomicBool::new(false);

// —— Windows release PDB 兜底（上一轮 §3.6：release exe 的 PDB 不被 std
// backtrace 解析，全部帧塌成 __ImageBase）——dbghelp 拿不到函数名时退回
// 「文件 VA 十六进制」帧（ip - 运行时模块基 + PE 头 ImageBase），这样的
// token 可以离线重符号化（tools/symbolize_l13.ps1，dbghelp + PDB）。
#[cfg(windows)]
static MODULE_BASE: OnceLock<usize> = OnceLock::new();

#[cfg(windows)]
fn runtime_module_base(ip: usize) -> Option<usize> {
    unsafe extern "system" {
        fn RtlPcToFileHeader(pc: *const std::ffi::c_void, base: *mut *mut std::ffi::c_void) -> *mut std::ffi::c_void;
    }
    let mut base: *mut std::ffi::c_void = std::ptr::null_mut();
    let r = unsafe { RtlPcToFileHeader(ip as *const _, &mut base) };
    if r.is_null() || base.is_null() {
        None
    } else {
        Some(base as usize)
    }
}

/// PE 头里的 ImageBase（文件口径首选基址）。
#[cfg(windows)]
fn pe_image_base(base: usize) -> Option<usize> {
    unsafe {
        let mz = *(base as *const u16);
        if mz != 0x5A4D {
            return None;
        }
        let e_lfanew = *((base + 0x3C) as *const u32) as usize;
        let pe = base + e_lfanew;
        if *(pe as *const u16) != 0x4550 {
            return None;
        }
        // OptionalHeader 紧跟 COFF 头（PE+0x18），PE32+ ImageBase 在 +0 处。
        Some(*((pe + 0x18) as *const u64) as usize)
    }
}

/// ip → 文件 VA（用于无符号帧的稳定 hex 兜底）；失败则退回原始 ip。
#[cfg(windows)]
fn ip_to_file_va(ip: usize) -> usize {
    let base = *MODULE_BASE.get_or_init(|| {
        runtime_module_base(ip).unwrap_or(0)
    });
    if base == 0 {
        return ip;
    }
    if let Some(img) = pe_image_base(base) {
        img.wrapping_add(ip.wrapping_sub(base))
    } else {
        ip
    }
}

#[cfg(not(windows))]
fn ip_to_file_va(ip: usize) -> usize {
    ip
}

fn frame_name_or_va(ip: usize, name: &str) -> String {
    // dbghelp 在 release exe 上常只给出段符号（__ImageBase）——按无符号处理，
    // 输出文件 VA，交给 tools/symbolize_l13.ps1 离线重符号化。
    if name.is_empty() || name == "__ImageBase" {
        format!("0x{:x}", ip_to_file_va(ip))
    } else {
        name.to_string()
    }
}

/// x86_64：rdtsc（enable 时对 Instant 校准）；其它平台回退 Instant（~30ns/次）。
#[cfg(target_arch = "x86_64")]
#[inline]
fn now_cycles() -> u64 {
    // _rdtsc 在所有 x86_64 基线可用；较新 std 里是安全内建，旧版是 unsafe——
    // 包 unsafe 块对两者都成立（新版仅会触发 unused_unsafe 提示，这里允许）。
    #[allow(unused_unsafe)]
    unsafe { std::arch::x86_64::_rdtsc() }
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn now_cycles() -> u64 {
    Instant::now().elapsed().as_nanos() as u64
}

#[cfg(target_arch = "x86_64")]
fn calibrate() -> f64 {
    let t0 = Instant::now();
    let c0 = now_cycles();
    let mut spin = 0u64;
    while t0.elapsed().as_nanos() < 200_000 {
        spin = spin.wrapping_add(1);
    }
    let dt_ns = t0.elapsed().as_nanos() as f64;
    let dc = (now_cycles().saturating_sub(c0)) as f64;
    let _ = spin;
    if dc > 0.0 { dt_ns / dc } else { 1.0 }
}

#[cfg(not(target_arch = "x86_64"))]
fn calibrate() -> f64 {
    1.0
}

#[inline]
fn to_ns(a: &Acc, cycles: u64) -> u64 {
    if a.ns_per_cycle > 0.0 {
        (cycles as f64 * a.ns_per_cycle) as u64
    } else {
        cycles
    }
}

pub fn enable() {
    let capture_every = std::env::var("L13SAMPLE_TICK")
        .ok()
        .and_then(|s| s.parse().ok())
        .filter(|&n: &u32| n > 0)
        .unwrap_or(200);
    let no_ts = std::env::var_os("L13SAMPLE_NOTS").is_some();
    let ns_per_cycle = if no_ts { 0.0 } else { calibrate() };
    ACC.with(|a| {
        let mut a = a.borrow_mut();
        *a = Acc::new();
        a.capture_every = capture_every;
        a.no_ts = no_ts;
        a.ns_per_cycle = ns_per_cycle;
    });
    ACTIVE.store(true, Ordering::Relaxed);
}

pub fn disable() {
    ACTIVE.store(false, Ordering::Relaxed);
}

pub fn has_active() -> bool {
    ACTIVE.load(Ordering::Relaxed)
}

/// 把最后一个 tick 到 now 的尾差记到 prev_site（write 时调用，段和 ≈ 墙钟）。
fn charge_tail(a: &mut Acc) {
    if a.no_ts || a.last_t == 0 {
        return;
    }
    let now = now_cycles();
    let dt = now.saturating_sub(a.last_t);
    a.last_t = now;
    let add = to_ns(a, dt);
    if let Some(s) = a.sites.get_mut(a.prev_site) {
        s.self_ns += add;
    }
}

#[track_caller]
#[inline(never)]
pub fn tick() {
    if !ACTIVE.load(Ordering::Relaxed) {
        return;
    }
    let loc = Location::caller();
    let loc_ptr = loc as *const Location as usize;
    let mut do_capture = false;
    ACC.with(|cell| {
        let mut a = cell.borrow_mut();
        let t = if a.no_ts { 0 } else { now_cycles() };
        let idx = a.site_of(loc_ptr, || loc.file().to_string(), || loc.line() as u32);
        a.sites[idx].ticks += 1;
        // 区间归因：上个 tick 到本 tick 的时间差记到上个 tick 点。
        if t != 0 && a.last_t != 0 {
            let dt = t.saturating_sub(a.last_t);
            let add = to_ns(&a, dt);
            let ps = a.prev_site; // RefMut 经 Deref 不做字段级 borrow 拆分，先出局部
            if let Some(s) = a.sites.get_mut(ps) {
                s.self_ns += add;
            }
        }
        if t != 0 {
            a.last_t = t;
        }
        a.prev_site = idx;
        a.skip += 1;
        if a.skip >= a.capture_every {
            a.skip = 0;
            do_capture = true;
        }
    });
    if do_capture {
        capture_raw();
    }
}

#[inline(never)]
fn capture_raw() {
    let mut ips = Vec::new();
    backtrace::trace(|frame| {
        ips.push(frame.ip() as usize);
        true
    });
    if ips.len() < 3 {
        return;
    }
    let trimmed: Vec<_> = ips.into_iter().skip(2).collect();
    if trimmed.is_empty() {
        return;
    }
    ACC.with(|cell| {
        let mut a = cell.borrow_mut();
        let t = if a.no_ts { 0 } else { now_cycles() };
        let dt = if t != 0 && a.cap_last_t != 0 { t.saturating_sub(a.cap_last_t) } else { 0 };
        if t != 0 {
            a.cap_last_t = t;
        }
        a.raw.push(RawStack { ips: trimmed });
        a.raw_dt.push(dt);
    });
}

/// 符号解析缓存（legacy 语义：进程级共享一张表）。
fn resolve_names(all_ips: &HashSet<usize>) -> HashMap<usize, String> {
    static CACHE: OnceLock<Mutex<HashMap<usize, String>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut out: HashMap<usize, String> = HashMap::new();
    let mut cache = cache.lock().unwrap();
    for &ip in all_ips {
        if let Some(n) = cache.get(&ip) {
            out.insert(ip, n.clone());
            continue;
        }
        let mut name = String::new();
        backtrace::resolve(ip as *mut std::ffi::c_void, |sym| {
            if let Some(n) = sym.name() {
                name = n.to_string();
            }
        });
        let resolved = frame_name_or_va(ip, &name);
        cache.insert(ip, resolved.clone());
        out.insert(ip, resolved);
    }
    out
}

fn collect_raw() -> (Vec<RawStack>, Vec<u64>, HashSet<usize>) {
    ACC.with(|cell| {
        let a = cell.borrow();
        let all_ips: HashSet<usize> = a.raw.iter().flat_map(|s| s.ips.iter().copied()).collect();
        (a.raw.clone(), a.raw_dt.clone(), all_ips)
    })
}

fn folded_from(raw: &[RawStack], names: &HashMap<usize, String>) -> HashMap<String, u64> {
    let mut folded: HashMap<String, u64> = HashMap::new();
    for stack in raw {
        let mut line = String::new();
        for &ip in stack.ips.iter().rev() {
            if let Some(name) = names.get(&ip) {
                line.push_str(name);
                line.push(';');
            }
        }
        *folded.entry(line).or_insert(0) += 1;
    }
    folded
}

pub fn write_folded(path: &str) -> std::io::Result<()> {
    // 顺带产出 self% / 时间加权链 / 人读报告（兄弟文件；l13bench 不用改）。
    let _ = write_self_folded(&format!("{path}.self.folded"));
    let _ = write_time_folded(&format!("{path}.time.folded"));
    let _ = write_self_report(&format!("{path}.self.txt"));

    let (raw, _dt, ips) = collect_raw();
    let names = resolve_names(&ips);
    let folded = folded_from(&raw, &names);
    let mut out = String::new();
    for (stack, count) in &folded {
        out.push_str(&format!("{} {}\n", stack, count));
    }
    std::fs::write(path, out)
}

fn ns_per_cycle_cached() -> f64 {
    ACC.with(|cell| cell.borrow().ns_per_cycle)
}

/// self% 口径 folded：每行 `sampler_self;<file:line> <self_ns>`。
/// （单帧"栈"——self 时间不挂调用链；链的归属看 `path` / `path.time.folded`。）
pub fn write_self_folded(path: &str) -> std::io::Result<()> {
    let rows: Vec<(String, u64)> = ACC.with(|cell| {
        let mut a = cell.borrow_mut();
        charge_tail(&mut a);
        let mut rows: Vec<(String, u64)> = a
            .sites
            .iter()
            .map(|s| (format!("sampler_self;{}:{}", s.file, s.line), s.self_ns))
            .collect();
        rows.sort_by(|x, y| y.1.cmp(&x.1));
        rows
    });
    let mut out = String::new();
    for (frame, ns) in rows {
        if ns > 0 {
            out.push_str(&format!("{} {}\n", frame, ns));
        }
    }
    std::fs::write(path, out)
}

/// 时间加权链 folded：权重 = 两次栈捕获之间的墙钟纳秒（≈ 每条链"开门"
/// 的那段真实时间；与频度 folded 相互校正"频度高 ≠ 时间多"）。
pub fn write_time_folded(path: &str) -> std::io::Result<()> {
    let f = ns_per_cycle_cached();
    let (raw, raw_dt, ips) = collect_raw();
    let names = resolve_names(&ips);
    let mut folded: HashMap<String, u64> = HashMap::new();
    for (stack, dt) in raw.iter().zip(raw_dt.iter()) {
        let mut line = String::new();
        for &ip in stack.ips.iter().rev() {
            if let Some(name) = names.get(&ip) {
                line.push_str(name);
                line.push(';');
            }
        }
        let ns = if f > 0.0 { (*dt as f64 * f) as u64 } else { *dt };
        *folded.entry(line).or_insert(0) += ns;
    }
    let mut out = String::new();
    for (stack, ns) in &folded {
        if *ns > 0 {
            out.push_str(&format!("{} {}\n", stack, ns));
        }
    }
    std::fs::write(path, out)
}

/// 人读报告：self% Top 表（含 tick 计数与 ns/tick 失真指示）。
pub fn write_self_report(path: &str) -> std::io::Result<()> {
    let (rows, total_ns, total_ticks, n_caps, unit): (Vec<(String, u64, u64)>, u64, u64, usize, &'static str) =
        ACC.with(|cell| {
            let mut a = cell.borrow_mut();
            charge_tail(&mut a);
            let total_ns: u64 = a.sites.iter().map(|s| s.self_ns).sum();
            let total_ticks: u64 = a.sites.iter().map(|s| s.ticks).sum();
            let mut rows: Vec<(String, u64, u64)> = a
                .sites
                .iter()
                .map(|s| (format!("{}:{}", s.file, s.line), s.self_ns, s.ticks))
                .collect();
            rows.sort_by(|x, y| y.1.cmp(&x.1));
            let unit = if a.ns_per_cycle > 0.0 { "ns (rdtsc calibrated)" } else { "ns (Instant)" };
            (rows, total_ns, total_ticks, a.raw.len(), unit)
        });
    let mut out = String::new();
    out.push_str(&format!(
        "# sampler self-time report: {} tick sites, {} captures, {} ticks, total attributed {} {}\n",
        rows.len(),
        n_caps,
        total_ticks,
        total_ns,
        unit
    ));
    out.push_str("# self_ns  self%  ticks  ns/tick  site\n");
    for (site, ns, ticks) in &rows {
        let pct = if total_ns > 0 { *ns as f64 * 100.0 / total_ns as f64 } else { 0.0 };
        let per = if *ticks > 0 { ns / ticks } else { 0 };
        out.push_str(&format!(
            "{:>12}  {:5.1}  {:>10}  {:>6}  {}\n",
            ns, pct, ticks, per, site
        ));
    }
    std::fs::write(path, out)
}
