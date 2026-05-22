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

/// Walk all process heaps via GetProcessHeaps + HeapWalk, return size-class histogram + total.
#[cfg(windows)]
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
        _union: [u8; 16],
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
        eprintln!("  typort --stats-no-hdl                         Print memory stats (skip hdl.typort)");
        eprintln!("  typort lsp                                    Start the language server");
        std::process::exit(1);
    }

    // Temporary: skip hdl for faster profiling
    let skip_hdl = args[1] == "--stats-no-hdl";
    let is_stats = args[1] == "--stats" || skip_hdl;

    // Create CLI client with source map for pretty-printed diagnostics.
    let cli_client = CliClient::new();
    let source_map = cli_client.source_map.clone();

    // Create backend with CLI client.
    let backend = Backend::new(cli_client);
    // Load builtin prelude (separated from Backend::new for LSP init timing).
    if skip_hdl {
        backend.load_prelude_skip_hdl();
    } else {
        backend.load_prelude();
    }

    if is_stats {
        // ─── Memory + timing benchmark mode ───
        // Collect timings recorded during load_prelude
        let timings_vec = backend.timings.lock().unwrap().clone();
        // lock released after clone

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

        // Aggregate timing totals
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
            "heap_histogram": heap_walk::heap_size_histogram(),
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
