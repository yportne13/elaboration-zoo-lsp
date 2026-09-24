//! LSP-kick 采样归因口（需要 `--features sampler`）。
//!
//! 为什么单独一个 bin：`--features sampler` 在实践中是 **bin 级**的——包级开该
//! feature 时，十几个用 `#[path]` 直接编译 L13/L10 源码的 bin（`lXXbench` 等）
//! 因未包含 `sampler.rs` 而报 `cannot find sampler in crate`。本 bin 只依赖库
//! （`elaboration_zoo_lsp::{Backend, Engine, sampler}`），所以
//! `cargo build --release --features sampler --bin l13lspsample` 只编译它 + 库，
//! 绕开上述限制，从而能给 **LSP kick 口径**（`Backend::process_file`，含常驻
//! prelude、观察面、导出桥）打采样，而不只是 bench 口径。
//!
//! 用法：
//! ```text
//! cargo build --release --features sampler --bin l13lspsample
//! ./target/release/l13lspsample.exe [file] [twin|ref] [kicks]
//! # 输出 target/bench_out/lspsample.{folded,self.folded,time.folded,self.txt}
//! ```
//!
//! 注意 tick 点稀疏：孪生内核只有 5 个 tick 点（`bump_spine_iter/machine.rs`），
//! `compiler.rs` / `eval.rs` / `force.rs` 零 tick，未打点区间会被"上一个 tick 点"
//! 吸收（`docs/perf-l13-round-2026-09-23b.md` §3）。

#[cfg(feature = "sampler")]
fn main() {
    use elaboration_zoo_lsp::client::ClientLike;
    use elaboration_zoo_lsp::{sampler, Backend, Engine};
    use lsp_types::{MessageType, Url};
    use std::sync::Arc;
    use std::time::Instant;

    #[derive(Default)]
    struct Silent;
    impl ClientLike for Silent {
        fn publish_diagnostics(&self, _u: Url, _d: Vec<lsp_types::Diagnostic>, _v: Option<i32>) {}
        fn show_message(&self, _t: MessageType, _m: String) {}
        fn log_message(&self, _t: MessageType, _m: String) {}
    }

    let a: Vec<String> = std::env::args().collect();
    let file = a.get(1).cloned().unwrap_or_else(|| "examples/adder_proof.typort".into());
    let engine = match a.get(2).map(|s| s.as_str()) {
        Some("ref") | Some("reference") => Engine::Reference,
        _ => Engine::Twin,
    };
    let kicks: usize = a.get(3).and_then(|s| s.parse().ok()).unwrap_or(3);
    // 第 4 个参数：`core` = 只装 core prelude（`load_prelude_skip_hdl`）。
    // 对照用——同一份源码、同一引擎，唯一变量是常驻 arena / decl 表的规模。
    let core_only = matches!(a.get(4).map(|s| s.as_str()), Some("core"));
    let src = std::fs::read_to_string(&file).expect("read source");
    let b: Arc<Backend<Silent>> = Backend::new_with_engine(Silent, engine);
    if core_only {
        b.load_prelude_skip_hdl();
    } else {
        b.load_prelude();
    }
    let uri = Url::parse("file:///lspsample.typort").unwrap();
    // 预热：付常驻 prime 并让 arena 进入稳态（同 twin_engine_bench 的口径）。
    b.process_file(&uri, &src, Some(0));
    // 探测计数只看**采样窗口内**的增量（`probe_count` 从进程启动累计，含
    // prelude 与预热 kick——直接比总量会把 prelude 的工作算进来）。
    let probes0 = elaboration_zoo_lsp::L13_namespace::probe_count();
    sampler::enable();
    for k in 0..kicks {
        let t0 = Instant::now();
        b.process_file(&uri, &src, Some(k as i32 + 1));
        println!("[LSPSAMPLE] {engine:?} kick {k}: {:.0} ms", t0.elapsed().as_secs_f64() * 1e3);
    }
    sampler::disable();
    println!(
        "[LSPSAMPLE] probe_accessible calls in sampled window = {} ({} kicks, {:.1}/kick)",
        elaboration_zoo_lsp::L13_namespace::probe_count() - probes0,
        kicks,
        (elaboration_zoo_lsp::L13_namespace::probe_count() - probes0) as f64 / kicks as f64
    );
    let _ = std::fs::create_dir_all("target/bench_out");
    match sampler::write_folded("target/bench_out/lspsample.folded") {
        Ok(()) => println!(
            "[LSPSAMPLE] wrote target/bench_out/lspsample.{{folded,self.folded,time.folded,self.txt}}"
        ),
        Err(e) => println!("[LSPSAMPLE] write_folded failed: {e}"),
    }
}

#[cfg(not(feature = "sampler"))]
fn main() {
    eprintln!("l13lspsample 需要 --features sampler");
    eprintln!("  cargo build --release --features sampler --bin l13lspsample");
}
