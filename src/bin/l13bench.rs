//! L13 类型检查器基准：参考版（`Infer`/`Cxt`，生产路径）vs
//! `bump_spine_iter` 性能孪生的一次性 / 稳态两种口径。
//!
//! 与 `typort` 完全解耦：本 bin 不引用 `elaboration_zoo_lsp` 库，只通过
//! `#[path]` 直接编译 `src/list.rs` / `src/bimap.rs` / `src/parser_lib*.rs`
//! 和 `src/L13_namespace/`（与 `tests/l13_fast_parity.rs` 同款）。
//!
//! 负载族（`--workload`）：
//! - `church` / `natadd` / `gadt` / `strchain` / `match` / `enum` / `struct`：
//!   孪生自带生成器（与 L02-L08 bench 同族）。`church`（具体 Nat 上的高阶
//!   迭代倍增）与 `enum`（Vec GADT，元组式构造子应用）已改写成 L13 语言面
//!   合法形态——原 impredicative Church 编码与分离位置 `cons a b` 两版一致判型
//!   失败，非孪生分叉。
//! - `prelude-core`：核心 prelude 15 个文件（无 `show.typort`——它依赖
//!   `nat_to_dec` prim，本 bench 不注册 nat 内建，两版同缺）。
//! - `prelude-core-show`：再加 `show.typort`（预期两版同 Err，用于确认
//!   缺口一致而非分叉）。
//! - `prelude-hdl`：core + 全部 HDL prelude（预期孪生早 Err——无宏展开/
//!   class 语义面缺口，用于量化接线距离）。
//! - `examples-hdl`：core + `examples/hdl/*.typort`（真实用户负载）。
//!
//! 用法：
//! ```text
//! cargo run --release --bin l13bench [--max-k 13] [--rounds 5]
//!        [--only basic,fast,fast_ss]
//!        [--workload church|prelude-core|...|all]
//!        [--file <path.typort>]   # 跑任意源文件（忽略 --workload）；
//!                                 # 配 L13BENCH_DIAG=1 逐 decl 定位两版首个失败点
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

#[path = "../L13_namespace/mod.rs"]
mod L13_namespace;

use clap::Parser;
use mimalloc::MiMalloc;
use std::time::Instant;

#[cfg(feature = "sampler")]
#[path = "../sampler.rs"]
mod sampler;

use L13_namespace::bump_spine_iter as fast;
use L13_namespace::parser::parser_with_macros;
use L13_namespace::parser::syntax::Decl;

#[derive(Parser)]
#[command(
    name = "l13bench",
    about = "L13 类型检查器基准：参考版 vs bump_spine_iter 版（合成 + 真实 prelude 负载）"
)]
struct Cli {
    /// church 数 = 2^(k+1)，k 从 9 起翻倍到 max-k
    #[arg(long, default_value_t = 13)]
    max_k: u32,

    /// 每实现每规模的计时轮数
    #[arg(long, default_value_t = 5)]
    rounds: usize,

    /// 只跑指定实现（逗号分隔：basic,fast,fast_ss）
    #[arg(long)]
    only: Option<String>,

    /// 负载族（见文件头）
    #[arg(long, default_value = "church")]
    workload: String,

    /// 调试口：跑任意源文件（两版互检 + L13BENCH_DIAG=1 逐 decl 定位），忽略 --workload
    #[arg(long)]
    file: Option<String>,

    /// `--file` 配套：装载 prelude（none|core|hdl）。旧实现 --file 不带
    /// prelude 也不注册 nat 内建——依赖 prelude 的真实示例（adder_proof 等）
    /// 两版都在 decl 1 报 `name not in scope: Nat`，示例级互检不可用。
    #[arg(long, default_value = "none")]
    with_prelude: String,
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let cli = Cli::parse();
    let stack_mb: usize = std::env::var("L13_STACK_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(256);
    std::thread::Builder::new()
        .stack_size(stack_mb << 20)
        .spawn(move || run(cli))
        .unwrap()
        .join()
        .unwrap();
}

// ── prelude 源（与 mod.rs::load_prelude_state_impl 同列表）──

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

const HDL: &[(&str, &str)] = &[
    ("hdl-core", include_str!("../prelude/hdl/hdl-core.typort")),
    ("hdl-check", include_str!("../prelude/hdl/hdl-check.typort")),
    ("hdl-types", include_str!("../prelude/hdl/hdl-types.typort")),
    ("hdl-ops", include_str!("../prelude/hdl/hdl-ops.typort")),
    ("hdl-clock", include_str!("../prelude/hdl/hdl-clock.typort")),
    ("hdl-bus", include_str!("../prelude/hdl/hdl-bus.typort")),
    ("hdl-signals", include_str!("../prelude/hdl/hdl-signals.typort")),
    ("hdl-utils", include_str!("../prelude/hdl/hdl-utils.typort")),
    ("hdl-stream", include_str!("../prelude/hdl/hdl-stream.typort")),
    ("hdl-crossclock", include_str!("../prelude/hdl/hdl-crossclock.typort")),
    ("hdl-bus-proto", include_str!("../prelude/hdl/hdl-bus-proto.typort")),
    ("hdl-misc-io", include_str!("../prelude/hdl/hdl-misc-io.typort")),
    ("hdl-misc", include_str!("../prelude/hdl/hdl-misc.typort")),
    ("hdl-macros", include_str!("../prelude/hdl/hdl-macros.typort")),
    ("hdl-verilog-compat", include_str!("../prelude/hdl/hdl-verilog-compat.typort")),
    ("hdl-verilog", include_str!("../prelude/hdl/hdl-verilog.typort")),
];

/// 按参考版 prelude 加载口径解析一串文件（库化：[`L13_namespace::
/// parse_prelude_files`]，与参考加载器 / 孪生 prelude 轮三方同源）。
///
/// 返回整个 `PreludeParse`（而非只取四个字段）：`--file` 口径需要它的
/// `macros` 去解析用户文件，否则用到 prelude 宏的示例两版同错早退。
fn parse_prelude(files: &[(&str, &str)]) -> L13_namespace::PreludeParse {
    L13_namespace::parse_prelude_files(files)
}


/// universe 负载（自 l09/l10bench 移植）：固定宇宙塔 + 2^(k+1) 层
/// `Type N` Pi 判定 def 链（每层一次 check_universe + global 登记；
/// 末值无闭式，双实现互检）。
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

/// traitchain 负载（自 l10bench 移植，**L10 特色**）：固定段（ToString for
/// Bool + 泛型约束 t[T][s: ToString[T]] + 毛毯实例 impl[T] Say for T）+
/// 2^(k+1) 层 `def c{i} : Nat = c{i-1}.say zero` 方法调用 def 链——每层
/// 一次实例合成（Synth → 单实例求解）+ 方法 β 应用；末值 = succ^n zero
/// （节点数无闭式，双实现互检）。
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

/// macro 负载（自 l11bench 移植，**L11 特色**）：macro_rules 两段（枚举
/// 生成 make_bool + raw 片段插值 addtwo）+ 2^(k+1) 层
/// `def c{i} : Nat = addtwo c{i-1}` 宏展开 def 链（末值 = succ^n zero，
/// 节点数无闭式，双实现互检）。
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

/// 跑一个 decl 序列的两版口径，返回 (basic_nf, fast_nf, 两版是否一致)。
fn nf_parity(decls: &[Decl], nat_after: &[usize]) -> (u64, u64, bool) {
    let b = L13_namespace::bench_check_nf_bounded(decls, nat_after);
    let mut t = fast::Tycker::new();
    let f = t.bench_check_nf_bounded(decls, nat_after);
    (b, f, b == f && b != 0)
}

/// 诊断：逐 decl 喂孪生，报首个失败的 decl 序号与错误（twin 早退时定位用）。
fn diagnose_fast(label: &str, decls: &[Decl], nat_after: &[usize]) {
    if std::env::var_os("L13BENCH_DIAG").is_none() {
        return;
    }
    // 增量喂：每次多一个 decl，二分定位首个失败点
    let mut lo = 0usize;
    let mut hi = decls.len();
    let fails = |n: usize| -> bool {
        let mut t = fast::Tycker::new();
        let bounds: Vec<usize> = nat_after.iter().copied().filter(|&i| i < n).collect();
        t.run_decls_bounded(&decls[..n], &bounds).is_err()
    };
    if !fails(decls.len()) {
        println!("   [diag] {label}: twin 全部 {} decls 通过", decls.len());
        return;
    }
    while lo + 1 < hi {
        let mid = (lo + hi) / 2;
        if fails(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let mut t = fast::Tycker::new();
    let bounds: Vec<usize> = nat_after.iter().copied().filter(|&i| i < hi).collect();
    let err = t.run_decls_bounded(&decls[..hi], &bounds).err();
    let decl_name = decl_name_of(&decls[hi - 1]);
    println!(
        "   [diag] {label}: twin 首个失败在第 {hi}/{} 个 decl ({decl_name}): {:?}",
        decls.len(),
        err.map(|e| e.0.data)
    );
}

/// 诊断：逐 decl 喂参考版，报首个失败的 decl 序号与错误（--file 迭代时定位用）。
fn diagnose_basic(label: &str, decls: &[Decl], nat_after: &[usize]) {
    if std::env::var_os("L13BENCH_DIAG").is_none() {
        return;
    }
    let fails = |n: usize| -> bool {
        let bounds: Vec<usize> = nat_after.iter().copied().filter(|&i| i < n).collect();
        L13_namespace::bench_check_first_err_bounded(&decls[..n], &bounds).is_err()
    };
    if !fails(decls.len()) {
        println!("   [diag] {label}: basic 全部 {} decls 通过", decls.len());
        return;
    }
    let mut lo = 0usize;
    let mut hi = decls.len();
    while lo + 1 < hi {
        let mid = (lo + hi) / 2;
        if fails(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    let bounds: Vec<usize> = nat_after.iter().copied().filter(|&i| i < hi).collect();
    let err = L13_namespace::bench_check_first_err_bounded(&decls[..hi], &bounds).err();
    let decl_name = decl_name_of(&decls[hi - 1]);
    println!(
        "   [diag] {label}: basic 首个失败在第 {hi}/{} 个 decl ({decl_name}): {:?}",
        decls.len(),
        err.map(|e| e.0.data)
    );
}

fn decl_name_of(d: &Decl) -> String {
    use L13_namespace::parser::syntax::Decl as D;
    match d {
        D::Def { name, .. } => format!("def {}", name.data),
        D::Enum { name, .. } => format!("enum {}", name.data),
        D::TraitDecl { name, .. } => format!("trait {}", name.data),
        D::ImplDecl { name, trait_name, .. } => {
            format!("impl {} for {}", trait_name.data, name)
        }
        D::Class { name, .. } => format!("class {}", name.data),
        D::Package { path } => format!(
            "package {}",
            path.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join(".")
        ),
        D::Import { .. } => "import".to_string(),
        D::Println(_) => "println".to_string(),
        D::Derive { .. } => "derive".to_string(),
    }
}

fn bench_one(label: &str, decls: &[Decl], nat_after: &[usize], cli: &Cli, want: &dyn Fn(&str) -> bool) {
    // 计时外：正确性互检
    let (b_nf, f_nf, ok) = nf_parity(decls, nat_after);
    diagnose_fast(label, decls, nat_after);
    diagnose_basic(label, decls, nat_after);
    let verdict = if ok {
        format!("nf={b_nf}")
    } else {
        format!("NF-DIVERGE basic={b_nf} fast={f_nf}")
    };
    println!("-- {label} ({} decls) {verdict}", decls.len());
    // **尺寸不同 ≠ 语义不同**：`nf` 是 `tm_size` 的节点数，而 `tm_size` 会计入
    // pretty **不打印**的槽位（`Sum` 的参数类型槽、`Match` 的模式内部、
    // `AppPruning` 的掩码长度）。2026-09-23 adder_proof 实测 `NF-DIVERGE
    // basic=26307 fast=26357`，而两版 pretty 范式**逐字符相同**（516 字符）——
    // 该 DIVERGE 是度量粒度的假警报。所以尺寸不一致且两版都跑通时，自动补一次
    // pretty 对比把判定说清楚（只在分歧时付这一次额外 elaboration 的钱）。
    // `L13BENCH_NF_DUMP=1` 可强制在尺寸一致时也打印。
    let force_dump = std::env::var_os("L13BENCH_NF_DUMP").is_some();
    if force_dump || (!ok && b_nf != 0 && f_nf != 0) {
        let bp = L13_namespace::bench_check_nf_pretty_bounded(decls, nat_after);
        let mut t = fast::Tycker::new();
        let fp = t.bench_check_nf_pretty_bounded(decls, nat_after);
        match (bp, fp) {
            (Some(b), Some(f)) if b == f => println!(
                "   [NF] 两版 pretty 范式逐字符相同（{} 字符）⇒ 上面的尺寸差来自 \
                 tm_size 计入但不打印的槽位，**不是语义分歧**",
                b.len(),
            ),
            (Some(b), Some(f)) => {
                let bc: Vec<char> = b.chars().collect();
                let fc: Vec<char> = f.chars().collect();
                let i = bc
                    .iter()
                    .zip(fc.iter())
                    .position(|(x, y)| x != y)
                    .unwrap_or(bc.len().min(fc.len()));
                let lo = i.saturating_sub(60);
                println!(
                    "   [NF] **可见分歧**：pretty 串在第 {i} 个字符起不同（basic {} / fast {} 字符）",
                    bc.len(),
                    fc.len(),
                );
                println!(
                    "   [NF] basic …{}",
                    bc[lo..(i + 120).min(bc.len())].iter().collect::<String>()
                );
                println!(
                    "   [NF] fast  …{}",
                    fc[lo..(i + 120).min(fc.len())].iter().collect::<String>()
                );
            }
            (a, c) => println!("   [NF] basic_ok={} fast_ok={}", a.is_some(), c.is_some()),
        }
    }

    let mut ts_basic: Vec<u128> = Vec::new();
    let mut ts_fast: Vec<u128> = Vec::new();
    let mut ts_ss: Vec<u128> = Vec::new();
    let mut tycker_ss = if want("fast_ss") { Some(fast::Tycker::new()) } else { None };
    if let Some(t) = tycker_ss.as_mut() {
        t.bench_check_nf_bounded(decls, nat_after);
    }
    for _ in 0..cli.rounds {
        if let Some(t) = tycker_ss.as_mut() {
            let s = Instant::now();
            t.bench_check_nf_bounded(decls, nat_after);
            ts_ss.push(s.elapsed().as_micros());
        }
        if want("fast") {
            #[cfg(feature = "sampler")]
            if std::env::var_os("L13SAMPLE").is_some() {
                sampler::enable();
            }
            let s = Instant::now();
            let mut t = fast::Tycker::new();
            t.bench_check_nf_bounded(decls, nat_after);
            ts_fast.push(s.elapsed().as_micros());
            #[cfg(feature = "sampler")]
            if std::env::var_os("L13SAMPLE").is_some() {
                let _ = std::fs::create_dir_all("target/bench_out");
                sampler::write_folded("target/bench_out/l13_fast.folded").ok();
            }
        }
        if want("basic") {
            let s = Instant::now();
            L13_namespace::bench_check_nf_bounded(decls, nat_after);
            ts_basic.push(s.elapsed().as_micros());
        }
    }
    let mut rows: Vec<(&str, u128, u128)> = Vec::new();
    if want("basic") {
        rows.push(("basic", *ts_basic.iter().min().unwrap(), median(&mut ts_basic)));
    }
    if want("fast") {
        rows.push(("fast", *ts_fast.iter().min().unwrap(), median(&mut ts_fast)));
    }
    if want("fast_ss") {
        rows.push(("fast_ss", *ts_ss.iter().min().unwrap(), median(&mut ts_ss)));
    }
    let fastest = rows.iter().map(|r| r.1).min().unwrap_or(0);
    for (name, min, med) in &rows {
        let star = if *min == fastest { "*" } else { " " };
        print!(
            "   {name:<8}{:>8}.{:03}ms{star}  med {:>8}.{:03}ms\n",
            min / 1000,
            min % 1000,
            med / 1000,
            med % 1000
        );
    }
}

fn run(cli: Cli) {
    let want = |name: &str| {
        cli.only
            .as_deref()
            .map(|s| s.split(',').any(|x| x.trim() == name))
            .unwrap_or(true)
    };
    if let Some(path) = &cli.file {
        let src = std::fs::read_to_string(path).expect("--file: cannot read");
        let label = path.rsplit(['/', '\\']).next().unwrap_or(path).to_string();
        // 无 prelude 口径：没有可继承的宏表，按老路 parse。
        let Ok(bare_decls) = fast::parse(&src, 0) else {
            eprintln!("parse failed: {label}");
            return;
        };
        if cli.with_prelude == "none" {
            bench_one(&label, &bare_decls, &[], &cli, &want);
            return;
        }
        // 装载 prelude 后跑（--with-prelude core|hdl）：示例级两版互检
        let files: Vec<(&str, &str)> = match cli.with_prelude.as_str() {
            "core" => CORE.to_vec(),
            "hdl" => {
                let mut f = CORE.to_vec();
                f.extend_from_slice(HDL);
                f
            }
            other => {
                eprintln!("unknown --with-prelude: {other} (none|core|hdl)");
                return;
            }
        };
        let p = parse_prelude(&files);
        let (mut all, failed, nat_after) = (p.decls, p.failed, p.nat_after);
        if let Some(f) = &failed {
            eprintln!("prelude PARSE-FAILED at {f}");
            return;
        }
        // **用户文件必须带 prelude 累积的宏表解析**（2026-09-23 修）：旧实现用
        // `fast::parse(&src, 0)`（空宏表），凡用到 prelude 导出宏的示例——`calc`
        // (adder_proof)、`when`/`switch`/`module` (hdl_ops、09-hierarchy、23/25
        // 等)——两版都在**同一个文件声明**上以 `error name not in scope: <宏名>`
        // 早退，`bench_one` 只报 `NF-DIVERGE basic=0 fast=0`，示例级互检与性能
        // 都成了空转（30 个示例里只有 typeclass_complex 能测）。`PreludeParse`
        // 的 `macros` 字段本就为此准备（见 `parse_prelude_files` 的注释）。
        // path_id 取 prelude 文件数，与加载器的逐文件递增口径一致。
        let user_decls = match parser_with_macros(
            &L13_namespace::preprocess(&src),
            files.len() as u32,
            &p.macros,
        ) {
            Some((decls, _errs, _exports, _exp)) => decls,
            None => {
                eprintln!("parse failed: {label}");
                return;
            }
        };
        all.extend(user_decls);
        bench_one(&label, &all, &nat_after, &cli, &want);
        return;
    }
    let workloads: Vec<&str> = match cli.workload.as_str() {
        "all" => vec![
            "church", "natadd", "gadt", "strchain", "match", "enum", "struct", "moduletree",
            "wide_enum", "prelude-core", "prelude-core-show", "prelude-hdl", "examples-hdl",
        ],
        w => vec![w],
    };

    for workload in workloads {
        println!("== workload: {workload} ==");
        match workload {
            "church" | "natadd" | "gadt" | "strchain" | "match" | "enum" | "struct" | "moduletree"
            | "wide_enum" | "universe" | "traitchain" | "macro" => {
                let ks: Vec<u32> = if matches!(workload, "gadt" | "enum" | "moduletree") {
                    vec![9]
                } else if workload == "wide_enum" {
                    // 表宽轴 16/64/512/2048 臂；k>=13 单轮 >30s，勿入更大默认列
                    vec![4, 6, 9, 11]
                } else {
                    (9..=cli.max_k).collect()
                };
                for k in ks {
                    let src = match workload {
                        "church" => fast::church_src(k),
                        "natadd" => fast::natadd_src(k),
                        "gadt" => fast::gadt_src(),
                        "strchain" => fast::strchain_src(k),
                        "match" => fast::match_src(k),
                        "struct" => fast::struct_src(k),
                        "moduletree" => fast::moduletree_src(),
                        "wide_enum" => fast::wide_enum_src(k),
                        "universe" => universe_src(k),
                        "traitchain" => traitchain_src(k),
                        "macro" => macro_src(k),
                        _ => fast::enum_src(),
                    };
                    let Ok(decls) = fast::parse(&src, 0) else {
                        eprintln!("parse failed at k={k}");
                        continue;
                    };
                    bench_one(&format!("{workload} k={k}"), &decls, &[], &cli, &want);
                }
            }
            "prelude-core" | "prelude-core-show" | "prelude-hdl" => {
                let mut files: Vec<(&str, &str)> = CORE.to_vec();
                if workload != "prelude-core" {
                    files.push(("show", include_str!("../prelude/show.typort")));
                }
                if workload == "prelude-hdl" {
                    files.extend_from_slice(HDL);
                }
                let p = parse_prelude(&files);
                for (n, c) in &p.counts {
                    println!("   parsed {n}: {c} decls");
                }
                if let Some(f) = &p.failed {
                    println!("   PARSE-FAILED at {f}");
                }
                bench_one(workload, &p.decls, &p.nat_after, &cli, &want);
            }
            "examples-hdl" => {
                // 核心 prelude + 每个 example 单独一段（避免宏跨文件冲突）
                let core_p = parse_prelude(CORE);
                let (prelude_decls, core_nat) = (core_p.decls, core_p.nat_after);
                let mut examples: Vec<(String, String)> = Vec::new();
                for e in [
                    include_str!("../../examples/hdl/01-basics.typort"),
                    include_str!("../../examples/hdl/02-arithmetic.typort"),
                    include_str!("../../examples/hdl/05-bool.typort"),
                    include_str!("../../examples/hdl/07-registers.typort"),
                    include_str!("../../examples/hdl/09-hierarchy.typort"),
                    include_str!("../../examples/hdl/16-counter.typort"),
                ] {
                    examples.push((String::new(), e.to_string()));
                }
                for (i, (_n, src)) in examples.iter().enumerate() {
                    let mut decls = prelude_decls.clone();
                    let pre = L13_namespace::preprocess(src);
                    match parser_with_macros(&pre, 100 + i as u32, &Default::default()) {
                        Some((d, _e, _x, _p)) => decls.extend(d),
                        None => {
                            println!("   example {i} parse failed");
                            continue;
                        }
                    }
                    bench_one(&format!("examples-hdl[{i}]"), &decls, &core_nat, &cli, &want);
                }
            }
            other => eprintln!("unknown workload: {other}"),
        }
    }
}
