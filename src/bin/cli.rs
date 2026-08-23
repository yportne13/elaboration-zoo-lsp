use std::error::Error;
use std::fs;
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use elaboration_zoo_lsp::Backend;
use elaboration_zoo_lsp::client::CliClient;
use elaboration_zoo_lsp::TextDocumentItem;
use lsp_types::Url;

#[cfg(feature = "mem-profile")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

// Small-node allocation churn dominates the evaluator's per-step cost;
// mimalloc beats the Windows default heap there (mem-profile builds keep
// dhat for heap profiling instead).
#[cfg(not(feature = "mem-profile"))]
#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Get Windows process memory counters via raw FFI (no crate dependency).
#[cfg(all(windows, feature = "mem-profile"))]
mod win_mem {
    #[repr(C)]
    pub struct ProcessMemoryCounters {
        pub cb: u32,
        pub PageFaultCount: u32,
        pub PeakWorkingSetSize: usize,
        pub WorkingSetSize: usize,
        pub QuotaPeakPagedPoolUsage: usize,
        pub QuotaPagedPoolUsage: usize,
        pub QuotaPeakNonPagedPoolUsage: usize,
        pub QuotaNonPagedPoolUsage: usize,
        pub PagefileUsage: usize,
        pub PeakPagefileUsage: usize,
    }

    unsafe extern "system" {
        fn GetCurrentProcess() -> isize;
        fn K32GetProcessMemoryInfo(
            hProcess: isize,
            ppsmemCounters: *mut ProcessMemoryCounters,
            cb: u32,
        ) -> i32;
    }

    pub fn get_memory_stats() -> (usize, usize, usize) {
        unsafe {
            let mut counters: ProcessMemoryCounters = std::mem::zeroed();
            counters.cb = std::mem::size_of::<ProcessMemoryCounters>() as u32;
            let h = GetCurrentProcess();
            let ret = K32GetProcessMemoryInfo(h, &mut counters, counters.cb);
            if ret != 0 {
                (counters.WorkingSetSize, counters.PeakWorkingSetSize, counters.PagefileUsage)
            } else {
                (0, 0, 0)
            }
        }
    }
}

/// Walk all process heaps via GetProcessHeaps + HeapWalk, return size-class histogram + total.
#[cfg(all(windows, feature = "mem-profile"))]
mod heap_walk {
    use std::collections::BTreeMap;

    #[repr(C)]
    struct ProcessHeapEntry {
        lpData: *mut u8,
        cbData: u32,
        cbOverhead: u8,
        iRegionIndex: u8,
        wFlags: u16,
        // union: Block { hMem, dwReserved }, Region { dwCommittedSize, dwUnCommittedSize, ... }
        // On x64 the Region sub-struct is 24 bytes (4+4+8+8) vs 16 bytes on x86,
        // so use 24 to be safe on both architectures.
        _union: [u8; 24],
    }

    const PROCESS_HEAP_ENTRY_BUSY: u16 = 0x0004;

    unsafe extern "system" {
        fn GetProcessHeaps(NumberOfHeaps: u32, ProcessHeaps: *mut isize) -> u32;
        fn GetProcessHeap() -> isize;
        fn HeapWalk(heap: isize, entry: *mut ProcessHeapEntry) -> i32;
        fn HeapLock(heap: isize) -> i32;
        fn HeapUnlock(heap: isize) -> i32;
    }

    pub fn heap_size_histogram() -> serde_json::Value {
        unsafe {
            let mut histogram: BTreeMap<String, (usize, usize)> = BTreeMap::new();
            let mut total_blocks: usize = 0;
            let mut total_bytes: usize = 0;

            // Get number of heaps
            let heap_count = GetProcessHeaps(0, std::ptr::null_mut());
            if heap_count == 0 {
                return serde_json::json!({"error": "GetProcessHeaps count failed"});
            }

            let mut heaps: Vec<isize> = vec![0; heap_count as usize];
            let actual = GetProcessHeaps(heap_count, heaps.as_mut_ptr());
            if actual == 0 {
                return serde_json::json!({"error": "GetProcessHeaps enumeration failed"});
            }
            heaps.truncate(actual as usize);

            for &heap in &heaps {
                if HeapLock(heap) == 0 {
                    continue;
                }
                let mut entry: ProcessHeapEntry = std::mem::zeroed();
                let mut sample_count = 0u32;
                while HeapWalk(heap, &mut entry) != 0 {
                    if entry.wFlags & PROCESS_HEAP_ENTRY_BUSY != 0 {
                        let sz = entry.cbData as usize;
                        total_blocks += 1;
                        total_bytes += sz;

                        // Sample first 16 bytes of blocks in 1025-2048 range
                        if sz >= 1025 && sz <= 2048 && sample_count < 5 {
                            sample_count += 1;
                            // let data = std::slice::from_raw_parts(entry.lpData, 16.min(sz));
                            // eprintln!("SAMPLE 1-2KB block sz={}: {:02x?}", sz, data);
                        }

                        let bucket = match sz {
                            0..=16 => "0-16",
                            17..=32 => "17-32",
                            33..=48 => "33-48",
                            49..=64 => "49-64",
                            65..=80 => "65-80",
                            81..=96 => "81-96",
                            97..=128 => "97-128",
                            129..=192 => "129-192",
                            193..=256 => "193-256",
                            257..=384 => "257-384",
                            385..=512 => "385-512",
                            513..=1024 => "513-1024",
                            1025..=2048 => "1025-2048",
                            2049..=4096 => "2049-4096",
                            4097..=8192 => "4097-8192",
                            8193..=16384 => "8193-16384",
                            16385..=32768 => "16385-32768",
                            32769..=65536 => "32769-65536",
                            65537..=131072 => "65537-131072",
                            131073..=262144 => "131073-262144",
                            262145..=524288 => "262145-524288",
                            _ => "524289+",
                        };

                        let e = histogram.entry(bucket.to_string()).or_insert((0, 0));
                        e.0 += 1;
                        e.1 += sz;
                    }
                }
                HeapUnlock(heap);
            }

            let mut buckets: Vec<serde_json::Value> = histogram.into_iter().map(|(range, (blocks, bytes))| {
                serde_json::json!({
                    "size_range": range,
                    "blocks": blocks,
                    "total_bytes": bytes,
                })
            }).collect();
            buckets.sort_by_key(|b| b["size_range"].as_str().unwrap().to_string());

            serde_json::json!({
                "total_blocks": total_blocks,
                "total_bytes": total_bytes,
                "histogram": buckets,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// CLI definition using clap
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(
    name = "typort",
    version,
    about = "TyportHDL type checker and language server",
    long_about = "TyportHDL is a dependently-typed hardware description language. \
                   This CLI provides type-checking, analysis, an LSP language server, \
                   and memory profiling tools."
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Type-check and analyze one or more TyportHDL source files.
    ///
    /// Each file is parsed, type-checked, and reported with diagnostic messages
    /// (errors, warnings, notes) printed to stderr with source-context snippets.
    #[command(visible_alias = "c")]
    Check {
        /// Source files to analyze (.typort)
        #[arg(required = true)]
        files: Vec<String>,

        /// Enable statistical CPU sampling profiler
        ///
        /// Records backtrace samples during type-checking and produces a
        /// flamegraph SVG. Requires building with `--features sampler`.
        #[arg(long, short)]
        sample: bool,

        /// Generate flamegraph SVG (implies --sample)
        ///
        /// Requires building with `--features sampler`.
        #[arg(long, short)]
        flamegraph: bool,
    },

    /// Start the LSP language server over stdio.
    ///
    /// Used by editor extensions (e.g. VS Code) to provide IDE features
    /// such as diagnostics, hover information, go-to-definition, and
    /// completion.
    #[command(visible_alias = "l")]
    Lsp,

    /// Elaborate HDL sources and emit generated Verilog.
    ///
    /// Compiles the given files, runs the Verilog generator on the requested
    /// top module (including all instantiated submodules), and writes the
    /// result to `<out>/<top>.v` or, without `--out`, to stdout.
    #[command(visible_alias = "e")]
    Emit {
        /// Source files to compile (.typort)
        #[arg(required = true)]
        files: Vec<String>,

        /// Top module instantiation: a module name, or name with create
        /// arguments such as 'adder[8]'
        #[arg(long, short)]
        top: String,

        /// Output directory (emits to stdout when omitted)
        #[arg(long, short)]
        out: Option<PathBuf>,

        /// Also emit <top>.manifest.json (ports/clock-domain/instance
        /// metadata consumed by tooling); requires --out
        #[arg(long, requires = "out")]
        manifest: bool,
    },

    /// Build a Typort.toml project: emit Verilog + manifest + filelist into
    /// the target directory.
    #[command(visible_alias = "b")]
    Build {
        /// Top module override ("top" or "adder[8]"); defaults to
        /// [project] top in Typort.toml
        #[arg(long, short)]
        top: Option<String>,
    },

    /// Build and smoke-test a Typort.toml project's simulation model
    /// (compile with the configured simulator, run one eval).
    #[command(visible_alias = "t")]
    Test {
        /// Top module override ("top" or "adder[8]"); defaults to
        /// [project] top in Typort.toml
        #[arg(long, short)]
        top: Option<String>,

        /// Override [test] trace (compile with VCD tracing)
        #[arg(long)]
        trace: bool,
    },

    /// Print memory statistics after loading the prelude.
    ///
    /// Outputs a JSON report with heap usage, allocation histograms,
    /// and per-file timing breakdowns. Requires building with
    /// `--features mem-profile`.
    #[command(visible_alias = "s")]
    Stats {
        /// Skip loading HDL prelude files
        #[arg(long, short)]
        no_hdl: bool,
    },
}

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    #[cfg(feature = "mem-profile")]
    let _profiler = dhat::Profiler::new_heap();

    let cli = Cli::parse();

    match cli.command {
        Commands::Lsp => {
            elaboration_zoo_lsp::run_lsp_server()?;
        }

        Commands::Check { files, sample, flamegraph } => {
            let do_sample = sample || flamegraph;
            run_check(files, do_sample)?;
        }

        Commands::Emit { files, top, out, manifest } => {
            run_emit(files, top, out, manifest)?;
        }

        Commands::Build { top } => {
            run_build(top)?;
        }

        Commands::Test { top, trace } => {
            run_test(top, trace)?;
        }

        Commands::Stats { no_hdl } => {
            run_stats(no_hdl)?;
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Subcommand implementations
// ---------------------------------------------------------------------------

fn run_emit(
    files: Vec<String>,
    top: String,
    out: Option<PathBuf>,
    manifest: bool,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let paths: Vec<PathBuf> = files.iter().map(PathBuf::from).collect();
    let sources = elaboration_zoo_lsp::emit::load_source_files(&paths)?;

    let result = elaboration_zoo_lsp::emit::emit_design(&sources, &top, manifest)?;
    match out {
        Some(dir) => {
            fs::create_dir_all(&dir)?;
            let name = elaboration_zoo_lsp::emit::top_module_name(&top)?;
            let path = dir.join(format!("{name}.v"));
            fs::write(&path, &result.verilog)?;
            eprintln!("Emitted {} ({} bytes)", path.display(), result.verilog.len());
            if let Some(manifest) = &result.manifest {
                let path = dir.join(format!("{name}.manifest.json"));
                fs::write(&path, manifest)?;
                eprintln!("Emitted {} ({} bytes)", path.display(), manifest.len());
            }
        }
        None => print!("{}", result.verilog),
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Project commands (Typort.toml)
// ---------------------------------------------------------------------------

/// Resolve (project config, top) for build/test; `--top` beats [project] top.
fn resolve_project(
    top_override: Option<String>,
) -> Result<(elaboration_zoo_lsp::config::ProjectConfig, String), Box<dyn Error + Sync + Send>> {
    let cwd = std::env::current_dir()?;
    let project = elaboration_zoo_lsp::config::Config::discover(&cwd)?;
    let top = top_override
        .or_else(|| project.config.project.top.clone())
        .ok_or_else(|| {
            format!(
                "no top module: set `top` under [project] in {} or pass --top",
                elaboration_zoo_lsp::config::CONFIG_FILE
            )
        })?;
    Ok((project, top))
}

fn run_build(top_override: Option<String>) -> Result<(), Box<dyn Error + Sync + Send>> {
    let (project, top) = resolve_project(top_override)?;
    let sources = elaboration_zoo_lsp::emit::load_source_files(&project.collect_sources()?)?;
    let target = project.target_dir();
    fs::create_dir_all(&target)?;

    let emitted = elaboration_zoo_lsp::emit::emit_design(&sources, &top, true)?;
    let top_name = elaboration_zoo_lsp::emit::top_module_name(&top)?;
    let verilog_path = target.join(format!("{top_name}.v"));
    fs::write(&verilog_path, &emitted.verilog)?;
    let manifest_path = target.join(format!("{top_name}.manifest.json"));
    fs::write(&manifest_path, emitted.manifest.as_deref().unwrap_or("{}"))?;
    // Filelist (verilator -f compatible): decouples downstream tools from
    // the layout of the target dir (veryl's build pattern).
    let filelist_path = target.join(format!("{}.f", project.config.project.name));
    fs::write(&filelist_path, format!("{top_name}.v\n"))?;

    println!(
        "built {} ({} bytes), manifest {}, filelist {}",
        verilog_path.display(),
        emitted.verilog.len(),
        manifest_path.display(),
        filelist_path.display(),
    );
    Ok(())
}

fn run_test(top_override: Option<String>, trace: bool) -> Result<(), Box<dyn Error + Sync + Send>> {
    use elaboration_zoo_lsp::sim::{Dut, SimConfig};

    let (project, top) = resolve_project(top_override)?;
    let sources = project.collect_sources()?;
    if project.config.test.simulator != "verilator" {
        return Err(format!(
            "unsupported simulator '{}' (only verilator)",
            project.config.test.simulator
        )
        .into());
    }
    let top_name = elaboration_zoo_lsp::emit::top_module_name(&top)?.to_string();
    let workdir = project.target_dir().join(format!("sim_{top_name}"));

    let cfg = SimConfig {
        top,
        sources,
        workdir,
        verilator_args: project.config.test.verilator.compile_args.clone(),
        trace: trace || project.config.test.trace,
    };
    let model = cfg.compile()?;

    // Smoke session: the model must spawn, settle one eval, and exit
    // cleanly. Behavioral testbenches live in cargo test (tests/sim_tests).
    let mut dut = Dut::spawn(&model)?;
    dut.eval()?;
    dut.finish()?;

    println!(
        "ok: {} model compiled and ran (smoke eval); binary {}{}",
        top_name,
        model.exe.display(),
        if cfg.trace { ", trace: wave.vcd in workdir" } else { "" }
    );
    Ok(())
}


fn run_check(files: Vec<String>, do_sample: bool) -> Result<(), Box<dyn Error + Sync + Send>> {
    #[cfg(feature = "sampler")]
    if do_sample {
        eprintln!("Sampling profiler enabled (backtrace)...");
        elaboration_zoo_lsp::sampler::enable();
    }
    #[cfg(not(feature = "sampler"))]
    if do_sample {
        eprintln!(
            "warning: --sample / --flamegraph requires building with --features sampler"
        );
        eprintln!("         cargo run --features sampler -- check <files>");
    }

    let cli_client = CliClient::new();
    let source_map = cli_client.source_map.clone();
    let backend = Backend::new(cli_client);

    // Load builtin prelude (core types, data structures, HDL primitives).
    backend.load_prelude();

    for filepath in &files {
        let path = PathBuf::from(filepath);
        let contents = fs::read_to_string(&path)?;
        let uri = Url::from_file_path(path.canonicalize()?).unwrap();

        eprintln!("Analyzing: {} ({} bytes)", uri.as_str(), contents.len());

        // Store source text so the CLI client can render diagnostics with source context.
        source_map.insert(uri.as_str().to_string(), contents.clone());

        // Run the analysis pipeline (parse + infer + diagnostics).
        backend.on_change::<false>(TextDocumentItem {
            uri: uri.clone(),
            text: &contents,
            version: None,
        });
    }

    #[cfg(feature = "sampler")]
    if do_sample {
        eprintln!("Writing folded stacks...");
        elaboration_zoo_lsp::sampler::write_folded("sampler.folded")
            .expect("write folded");
        eprintln!("Generating flamegraph SVG...");
        let folded = std::fs::read_to_string("sampler.folded")
            .expect("read folded");
        let lines: Vec<&str> = folded.lines().collect();
        let mut opts = inferno::flamegraph::Options::default();
        opts.title = "elaboration-zoo-lsp CPU flame graph (backtrace sampler)".to_string();
        let file = std::fs::File::create("flamegraph.svg")
            .expect("create svg");
        let mut writer = std::io::BufWriter::new(file);
        if inferno::flamegraph::from_lines(&mut opts, lines.into_iter(), &mut writer).is_ok() {
            // Keep sampler.folded for offline analysis when TYPORT_PROFILE is set.
            if std::env::var_os("TYPORT_PROFILE").is_none() {
                let _ = std::fs::remove_file("sampler.folded");
            }
            eprintln!("Flame graph written to flamegraph.svg");
        }
    }

    Ok(())
}

#[allow(unreachable_code)]
fn run_stats(no_hdl: bool) -> Result<(), Box<dyn Error + Sync + Send>> {
    #[cfg(feature = "mem-profile")]
    {
        let cli_client = CliClient::new();
        let backend = Backend::new(cli_client);

        // Load prelude (optional skip HDL for faster profiling).
        if no_hdl {
            backend.load_prelude_skip_hdl();
        } else {
            backend.load_prelude();
        }

        // Collect timings recorded during load_prelude.
        let timings_vec = backend.timings.lock().unwrap().clone();

        let infer_arc = backend.get_infer();
        let cxt_arc = backend.get_cxt();
        let infer_lock = infer_arc.lock().unwrap();
        let cxt_lock = cxt_arc.lock().unwrap();
        let stats = infer_lock.memory_stats_with_cxt(Some(&cxt_lock));
        drop(cxt_lock);
        drop(infer_lock);

        #[cfg(windows)]
        let (ws, peak_ws, pf) = win_mem::get_memory_stats();
        #[cfg(not(windows))]
        let (ws, peak_ws, pf) = (0, 0, 0);

        #[cfg(windows)]
        let heap_histogram = heap_walk::heap_size_histogram();
        #[cfg(not(windows))]
        let heap_histogram = serde_json::json!(null);

        // Aggregate timing totals.
        let total_parser: f64 = timings_vec.iter().map(|t| t.1).sum();
        let total_infer: f64 = timings_vec.iter().map(|t| t.2).sum();
        let total_change: f64 = timings_vec.iter().map(|t| t.3).sum();

        let result = serde_json::json!({
            "peak_working_set_bytes": peak_ws,
            "peak_working_set_mb": format!("{:.1}", peak_ws as f64 / 1_048_576.0),
            "working_set_bytes": ws,
            "working_set_mb": format!("{:.1}", ws as f64 / 1_048_576.0),
            "pagefile_usage_bytes": pf,
            "pagefile_usage_mb": format!("{:.1}", pf as f64 / 1_048_576.0),
            "heap_histogram": heap_histogram,
            "backend_stats": backend.backend_stats(),
            "infer_stats": stats,
            "timings": {
                "files": timings_vec.iter().map(|(uri, parser_s, infer_s, total_s)| {
                    serde_json::json!({
                        "uri": uri,
                        "parser_secs": format!("{:.4}", parser_s),
                        "infer_secs": format!("{:.4}", infer_s),
                        "total_secs": format!("{:.4}", total_s),
                    })
                }).collect::<Vec<_>>(),
                "total_parser_secs": format!("{:.4}", total_parser),
                "total_infer_secs": format!("{:.4}", total_infer),
                "total_secs": format!("{:.4}", total_change),
            },
        });

        println!("{}", serde_json::to_string_pretty(&result).unwrap());
    }

    #[cfg(not(feature = "mem-profile"))]
    {
        eprintln!("error: `typort stats` requires building with --features mem-profile");
        eprintln!("       cargo run --features mem-profile -- stats");
        std::process::exit(1);
    }

    Ok(())
}
