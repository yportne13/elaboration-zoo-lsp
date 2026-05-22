use std::error::Error;
use std::fs;
use std::path::PathBuf;

use elaboration_zoo_lsp::Backend;
use elaboration_zoo_lsp::client::CliClient;
use elaboration_zoo_lsp::TextDocumentItem;
use lsp_types::Url;

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

/// Get Windows process memory counters via raw FFI (no crate dependency).
#[cfg(windows)]
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

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();

    let args: Vec<String> = std::env::args().collect();

    // Check for subcommands.
    if args.len() >= 2 && args[1] == "lsp" {
        return elaboration_zoo_lsp::run_lsp_server();
    }

    if args.len() < 2 {
        eprintln!("Usage:");
        eprintln!("  typort <file.typort> [<file2.typort> ...]    Analyze files");
        eprintln!("  typort --stats                                Print memory stats after prelude");
        eprintln!("  typort lsp                                    Start the language server");
        std::process::exit(1);
    }

    // Create CLI client with source map for pretty-printed diagnostics.
    let cli_client = CliClient::new();
    let source_map = cli_client.source_map.clone();

    // Create backend with CLI client.
    let backend = Backend::new(cli_client);
    // Load builtin prelude (separated from Backend::new for LSP init timing).
    backend.load_prelude();

    if args[1] == "--stats" {
        // ─── Memory benchmark mode ───
        let infer_arc = backend.get_infer();
        let infer_lock = infer_arc.lock().unwrap();
        let stats = infer_lock.memory_stats();
        drop(infer_lock);

        #[cfg(windows)]
        let (ws, peak_ws, pf) = win_mem::get_memory_stats();
        #[cfg(not(windows))]
        let (ws, peak_ws, pf) = (0, 0, 0);

        let result = serde_json::json!({
            "peak_working_set_bytes": peak_ws,
            "peak_working_set_mb": format!("{:.1}", peak_ws as f64 / 1_048_576.0),
            "working_set_bytes": ws,
            "working_set_mb": format!("{:.1}", ws as f64 / 1_048_576.0),
            "pagefile_usage_bytes": pf,
            "pagefile_usage_mb": format!("{:.1}", pf as f64 / 1_048_576.0),
            "infer_stats": stats,
        });

        println!("{}", serde_json::to_string_pretty(&result).unwrap());
        return Ok(());
    }

    for filepath in &args[1..] {
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

    Ok(())
}
