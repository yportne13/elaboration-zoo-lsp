#![feature(pattern)]
#![feature(anonymous_pipe)] // std::io::pipe, used by the lsp_stdio chunked-roundtrip tests

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

mod parser_lib;
mod parser_lib_resilient;
mod list;
mod bimap;
pub mod ls;
pub mod client;
mod lsp_stdio;
mod L01_eval;
//mod L01a_fast;
mod L02_tyck;
mod L03_holes;
mod L04_implicit;
mod L05_pruning;
mod L06_string;
mod L07_sum_type;
mod L07a_depend_pm;
mod L08_product_type;
mod L09_mltt;
mod L10_typeclass;
mod L11_macro;
pub mod L12_canonical;
pub mod L13_namespace;

#[cfg(feature = "sampler")]
pub mod sampler;

use std::collections::{HashMap, HashSet};
use std::error::Error;

use client::{Client, ClientLike};
use dashmap::DashMap;
use log::debug;
use ls::LanguageServer;
use lsp_server::{ExtractError, Message, ProtocolError, Request, RequestId, Response};
use lsp_types::request::{CodeActionRequest, Completion, ExecuteCommand, GotoDefinition, HoverRequest, InlayHintRequest, References, Rename, SemanticTokensFullRequest, SemanticTokensRangeRequest};
use ropey::Rope;
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;
use serde_json::Value;
use lsp_types::notification::{DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, DidSaveTextDocument, Notification};
use lsp_types::{CancelParams, NumberOrString, *};
use crate::ls::Result;

use L13_namespace::pretty::pretty_tm;
use L13_namespace::parser::{parser, parser_with_macros, macros::MacroRule, MacroExpansionInfo};
use L13_namespace::parser::syntax::Decl;
use L13_namespace::{DeclTm, Infer, preprocess};
use L13_namespace::cxt::Cxt;

use std::sync::{Arc, Mutex, Condvar, mpsc};
use std::io::{self, BufRead, Write, stdin, stdout};
use std::thread;

// ---------------------------------------------------------------------------
// Fine-grained stage timing probe (perf diagnostics).
//
// Enabled by setting the environment variable TYPORT_PROFILE (any value).
// When enabled, `on_change` prints per-stage timings and the top-N slowest
// declarations to stderr; the existing `change/parser/infer` LOG lines are
// unchanged. When disabled, each `mark` costs one `Instant::now()` check
// that returns immediately, so normal output and tests are unaffected.
// ---------------------------------------------------------------------------
pub struct Prof {
    enabled: bool,
    stages: Vec<(String, f64)>,
    last: std::time::Instant,
    decls: Vec<(String, f64, u64, u64, u64, u64, u64)>,
}

impl Prof {
    pub fn new() -> Self {
        let enabled = std::env::var_os("TYPORT_PROFILE").is_some();
        if enabled {
            L13_namespace::FUNC_PROF
                .enabled
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
        Prof {
            enabled,
            stages: Vec::new(),
            last: std::time::Instant::now(),
            decls: Vec::new(),
        }
    }

    #[inline]
    pub fn mark(&mut self, name: &str) {
        if !self.enabled {
            return;
        }
        let now = std::time::Instant::now();
        let d = now.duration_since(self.last).as_secs_f64();
        self.last = now;
        self.stages.push((name.to_string(), d));
    }

    /// Record the elapsed time of one declaration's elaboration, plus the
    /// number of `force` / `eval` / `quote` / `unify` / `v_app` calls it made
    /// (hot-loop evidence).
    #[inline]
    pub fn decl(&mut self, label: String, secs: f64, force_calls: u64, eval_calls: u64, quote_calls: u64, unify_calls: u64, vapp_calls: u64) {
        if !self.enabled {
            return;
        }
        self.decls.push((label, secs, force_calls, eval_calls, quote_calls, unify_calls, vapp_calls));
    }

    pub fn report(&self, uri: &str, top_n: usize) {
        if !self.enabled {
            return;
        }
        eprintln!("[PROF] == {} ==", uri);
        for (name, d) in &self.stages {
            eprintln!("[PROF]   {:<26} {:>9.4} s", name, d);
        }
        let total: f64 = self.decls.iter().map(|(_, d, _, _, _, _, _)| d).sum();
        let mut sorted = self.decls.clone();
        sorted.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        eprintln!("[PROF]   {} decls, infer_loop total {:.4} s, top-{} slowest:", self.decls.len(), total, top_n);
        for (label, d, fc, ec, qc, uc, vc) in sorted.iter().take(top_n) {
            let pct = if total > 0.0 { 100.0 * d / total } else { 0.0 };
            eprintln!("[PROF]     {:>8.4} s ({:>5.1}%)  force{:>11} eval{:>9} quote{:>8} unify{:>7} vapp{:>8}  {}",
                d, pct, fc, ec, qc, uc, vc, label);
        }
        // Function-level breakdown (accumulated incl. nesting; read-and-reset).
        let fp = &L13_namespace::FUNC_PROF;
        eprintln!("[PROF]   -- function-level (accumulated, nesting included) --");
        let mut rows: Vec<(String, u64, u64)> = vec![
            ("check".into(), fp.check.0.swap(0, Ordering::Relaxed), fp.check.1.swap(0, Ordering::Relaxed)),
            ("infer_expr".into(), fp.infer_expr.0.swap(0, Ordering::Relaxed), fp.infer_expr.1.swap(0, Ordering::Relaxed)),
            ("check_universe".into(), fp.check_universe.0.swap(0, Ordering::Relaxed), fp.check_universe.1.swap(0, Ordering::Relaxed)),
            ("eval".into(), fp.eval.0.swap(0, Ordering::Relaxed), fp.eval.1.swap(0, Ordering::Relaxed)),
            ("force".into(), fp.force.0.swap(0, Ordering::Relaxed), fp.force.1.swap(0, Ordering::Relaxed)),
            ("v_app".into(), fp.v_app.0.swap(0, Ordering::Relaxed), fp.v_app.1.swap(0, Ordering::Relaxed)),
            ("quote".into(), fp.quote.0.swap(0, Ordering::Relaxed), fp.quote.1.swap(0, Ordering::Relaxed)),
            ("nf".into(), fp.nf.0.swap(0, Ordering::Relaxed), fp.nf.1.swap(0, Ordering::Relaxed)),
            ("unify".into(), fp.unify.0.swap(0, Ordering::Relaxed), fp.unify.1.swap(0, Ordering::Relaxed)),
            ("solve_multi_trait".into(), fp.solve_trait.0.swap(0, Ordering::Relaxed), fp.solve_trait.1.swap(0, Ordering::Relaxed)),
        ];
        rows.sort_by(|a, b| b.1.cmp(&a.1));
        for (name, ns, n) in rows {
            eprintln!("[PROF]     {:>8.4} s  {:>12} calls  {}", ns as f64 / 1e9, n, name);
        }
        // force() entry-value shape histogram.
        let shapes = ["Flex", "Rigid", "Decl", "Obj", "Lam", "Pi", "U", "LiteralType", "LiteralIntro", "Sum", "SumCase", "Match", "Call"];
        eprintln!("[PROF]   -- force() entry shapes --");
        for (i, name) in shapes.iter().enumerate() {
            let c = fp.force_shape[i].swap(0, Ordering::Relaxed);
            if c > 0 {
                eprintln!("[PROF]     {:>14} {:>12}", name, c);
            }
        }
    }
}

/// Short human-readable label for a declaration (used by the per-decl timing).
fn decl_label(t: &Decl) -> String {
    match t {
        Decl::Package { path } => format!(
            "package {}",
            path.iter().map(|p| p.data.as_str()).collect::<Vec<_>>().join(".")
        ),
        Decl::Import { prefix, names, wildcard } => {
            let names = if *wildcard {
                "*".to_string()
            } else {
                names.join(",")
            };
            format!("import {}.{{{}}}", prefix.join("."), names)
        }
        Decl::Def { name, .. } => format!("def {}", name.data),
        Decl::Println(e) => {
            let s: String = format!("{:?}", e).chars().take(60).collect();
            format!("println {}", s)
        }
        Decl::Enum { name, is_trait, .. } => format!(
            "{} {}",
            if *is_trait { "trait" } else { "enum" },
            name.data
        ),
        Decl::TraitDecl { name, .. } => format!("trait {}", name.data),
        Decl::ImplDecl { name, trait_name, .. } => {
            let n: String = format!("{:?}", name).chars().take(40).collect();
            format!("impl {} for {}", trait_name.data, n)
        }
        Decl::Derive { traits, decl } => {
            let t = traits.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join("+");
            format!("derive({}) {:.40}", t, decl_label(decl))
        }
        Decl::Class { name, .. } => format!("class {}", name.data),
    }
}

// 2. 定义传递给工作线程的任务包
struct AnalysisJob {
    uri: Url,
    text: String,
    version: Option<i32>,
}

// 3. 修改 Backend 结构
pub struct Backend<C: ClientLike + Send + Sync + 'static> {
    pub client: C,
    pub ast_map: DashMap<String, Vec<Decl>>,
    pub type_map: DashMap<String, Vec<DeclTm>>,
    pub document_map: DashMap<String, Rope>,
    pub document_id: DashMap<String, u32>,
    /// Full document text for incremental sync (maintained on the LSP server thread)
    pub document_buffers: Mutex<HashMap<String, String>>,
    pub hover_table: DashMap<String, Infer>,
    pub quickfix_map: DashMap<String, HashMap<String, Vec<Box<dyn Fn() -> Option<String> + Send + Sync>>>>,
    /// Exported macros accumulated across all files (keyed by macro name)
    pub exported_macros: DashMap<String, Vec<MacroRule>>,
    /// uri -> macro names the file exports, so `exported_macros` can be
    /// cleaned up when a file closes or fails to parse (G5/G8).
    pub file_macros: DashMap<String, HashSet<String>>,
    /// Macro expansion data collected during parsing (keyed by URI)
    pub macro_expansion_map: DashMap<String, Vec<MacroExpansionInfo>>,
    /// uri -> decl keys the file wrote into the global cxt (for incremental rebuild)
    pub file_symbols: DashMap<String, HashSet<String>>,
    /// uri -> inherent-impl namespace entries (type Arc ptr, type name) the file
    /// merged into the global cxt.namespace, for removal on close/edit.
    pub file_namespace_regs: DashMap<String, Vec<(usize, SmolStr)>>,
    /// uri -> namespaces the file imports (its dependencies)
    pub file_deps: DashMap<String, HashSet<String>>,
    /// uri -> the package namespaces the file declares (ALL `package` decls;
    /// a file may declare several, G3)
    pub file_namespaces: DashMap<String, HashSet<String>>,
    /// namespace -> files that provide it (declare `package ns`)
    pub ns_providers: DashMap<String, HashSet<String>>,
    /// namespace -> files that depend on it (import it)
    pub ns_dependents: DashMap<String, HashSet<String>>,
    // 状态标记和条件变量
    processing_uris: DashMap<String, bool>, // URI -> 正在被 worker 处理
    pending_uris: DashMap<String, bool>,     // URI -> 已排队等待处理（在 worker 启动前就标记）
    // 信号机制：mpsc 通道任务队列
    job_sender: mpsc::Sender<AnalysisJob>,
    // Worker 线程的接收端（在 spawn_worker 时取出使用）
    job_receiver: Mutex<Option<mpsc::Receiver<AnalysisJob>>>,
    // 处理完成的信号
    processed_signal: Arc<(Mutex<HashMap<String, bool>>, Condvar)>,
    /// Track cancelled request IDs from $/cancelRequest
    cancelled_requests: Mutex<HashSet<RequestId>>,

    infer: Arc<Mutex<Infer>>,
    cxt: Arc<Mutex<Cxt>>,

    /// Timing data: (uri, parser_secs, infer_secs, change_secs)
    pub timings: Mutex<Vec<(String, f64, f64, f64)>>,
}

impl<C: ClientLike + Send + Sync + 'static> Backend<C> {
    pub fn new(client: C) -> Arc<Self> {
        let ast_map = Default::default();
        let type_map = Default::default();
        let document_map = Default::default();
        let document_id = Default::default();
        let hover_table = Default::default();

        let processed_signal = Arc::new((Mutex::new(HashMap::new()), Condvar::new()));
        let infer = Infer::new();
        let cxt = Cxt::new(&infer);
        let timings = Mutex::new(Vec::new());

        let (tx, rx) = mpsc::channel::<AnalysisJob>();

        let ret = Arc::new(Backend {
            client,
            ast_map,
            type_map,
            document_map,
            document_id,
            document_buffers: Mutex::new(HashMap::new()),
            hover_table,
            quickfix_map: DashMap::new(),
            exported_macros: DashMap::new(),
            file_macros: DashMap::new(),
            macro_expansion_map: DashMap::new(),
            file_symbols: DashMap::new(),
            file_namespace_regs: DashMap::new(),
            file_deps: DashMap::new(),
            file_namespaces: DashMap::new(),
            ns_providers: DashMap::new(),
            ns_dependents: DashMap::new(),
            processing_uris: DashMap::new(),
            pending_uris: DashMap::new(),
            job_sender: tx,
            job_receiver: Mutex::new(Some(rx)),
            processed_signal,
            cancelled_requests: Mutex::new(HashSet::new()),
            infer: Arc::new(Mutex::new(infer)),
            cxt: Arc::new(Mutex::new(cxt)),
            timings,
        });
        ret
    }
}

impl<C: ClientLike + Send + Sync + 'static> Backend<C> {
    pub fn get_infer(&self) -> Arc<Mutex<Infer>> {
        self.infer.clone()
    }

    pub fn get_cxt(&self) -> Arc<Mutex<Cxt>> {
        self.cxt.clone()
    }

    /// All keys currently in the global cxt.decl (sorted), for tests/tools.
    pub fn global_decl_keys(&self) -> Vec<String> {
        let cxt = self.cxt.lock().unwrap();
        let mut keys: Vec<String> = cxt.decl.keys().map(|k| k.to_string()).collect();
        keys.sort();
        keys
    }

    pub fn backend_stats(&self) -> serde_json::Value {
        use serde_json::json;
        let doc_count = self.document_map.len();
        let doc_bytes: usize = self.document_map.iter().map(|e| e.value().len_bytes()).sum();
        let ast_count = self.ast_map.len();
        let ast_entries: usize = self.ast_map.iter().map(|e| e.value().len()).sum();
        let type_count = self.type_map.len();
        let type_entries: usize = self.type_map.iter().map(|e| e.value().len()).sum();
        let hover_count = self.hover_table.len();
        let mac_count = self.exported_macros.len();
        let mac_rules: usize = self.exported_macros.iter().map(|e| e.value().len()).sum();
        json!({
            "document_map": {
                "files": doc_count,
                "total_bytes": doc_bytes,
            },
            "ast_map": {
                "files": ast_count,
                "total_decls": ast_entries,
            },
            "type_map": {
                "files": type_count,
                "total_decls": type_entries,
            },
            "hover_table_map": {
                "files": hover_count,
            },
            "exported_macros": {
                "names": mac_count,
                "total_rules": mac_rules,
            },
        })
    }

    /// Look up the text content of a builtin:// URI from the document map.
    /// Prelude files are loaded into `document_map` during `load_prelude()`.
    pub fn get_builtin_content(&self, uri: &str) -> Option<String> {
        // Try the URI as-is first.
        if let Some(content) = self.document_map.get(uri).map(|rope| rope.to_string()) {
            return Some(content);
        }
        // VS Code normalizes builtin:/// → builtin:/ (empty authority → no //).
        // Normalize to match the keys in document_map.
        if uri.starts_with("builtin:/") && !uri.starts_with("builtin://") {
            let normalized = uri.replacen("builtin:/", "builtin:///", 1);
            if let Some(content) = self.document_map.get(&normalized).map(|rope| rope.to_string()) {
                return Some(content);
            }
        }
        None
    }

    /// 在 LSP init 握手完成后加载 prelude 文件。
    /// 这时 connection 已经建立，diagnostics 会正确发送给客户端。
    pub fn load_prelude(self: &Arc<Self>) {
        self.load_prelude_impl(false);
    }

    pub fn load_prelude_skip_hdl(self: &Arc<Self>) {
        self.load_prelude_impl(true);
    }

    fn load_prelude_impl(self: &Arc<Self>, skip_hdl: bool) {
        // Elaborate the builtin prelude once per process and clone the cached
        // infer/cxt/macro state into this Backend, instead of re-elaborating
        // ~24 files on every startup (LSP server, CLI check, tests).
        let (mut infer, mut cxt, global_macros) =
            match L13_namespace::clone_prelude_state(!skip_hdl) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("typort: prelude elaboration failed: {e:?}");
                    return;
                }
            };
        // Register the virtual builtin documents (same URIs/order as before)
        // so goto/hover across the prelude boundary and builtinContent
        // requests keep working.
        {
            let mut docs: Vec<(&'static str, &'static str)> = vec![
                ("builtin:///op.typort", include_str!("prelude/core/op.typort")),
                ("builtin:///eq.typort", include_str!("prelude/core/eq.typort")),
                ("builtin:///nat.typort", include_str!("prelude/core/nat.typort")),
                ("builtin:///calc.typort", include_str!("prelude/core/calc.typort")),
                ("builtin:///bool.typort", include_str!("prelude/core/bool.typort")),
                ("builtin:///option.typort", include_str!("prelude/data/option.typort")),
                ("builtin:///result.typort", include_str!("prelude/data/result.typort")),
                ("builtin:///order.typort", include_str!("prelude/data/order.typort")),
                ("builtin:///void.typort", include_str!("prelude/core/void.typort")),
                ("builtin:///decidable.typort", include_str!("prelude/data/decidable.typort")),
                ("builtin:///vec.typort", include_str!("prelude/data/vec.typort")),
                ("builtin:///either.typort", include_str!("prelude/data/either.typort")),
                ("builtin:///list.typort", include_str!("prelude/data/list.typort")),
                ("builtin:///string.typort", include_str!("prelude/data/string.typort")),
                ("builtin:///nonempty.typort", include_str!("prelude/data/nonempty.typort")),
            ];
            if !skip_hdl {
                docs.extend([
                    ("builtin:///hdl-core.typort", include_str!("prelude/hdl/hdl-core.typort")),
                    ("builtin:///hdl-check.typort", include_str!("prelude/hdl/hdl-check.typort")),
                    ("builtin:///hdl-types.typort", include_str!("prelude/hdl/hdl-types.typort")),
                    ("builtin:///hdl-ops.typort", include_str!("prelude/hdl/hdl-ops.typort")),
                    ("builtin:///hdl-clock.typort", include_str!("prelude/hdl/hdl-clock.typort")),
                    ("builtin:///hdl-bus.typort", include_str!("prelude/hdl/hdl-bus.typort")),
                    ("builtin:///hdl-signals.typort", include_str!("prelude/hdl/hdl-signals.typort")),
                    ("builtin:///hdl-utils.typort", include_str!("prelude/hdl/hdl-utils.typort")),
                    ("builtin:///hdl-stream.typort", include_str!("prelude/hdl/hdl-stream.typort")),
                    ("builtin:///hdl-crossclock.typort", include_str!("prelude/hdl/hdl-crossclock.typort")),
                    ("builtin:///hdl-bus-proto.typort", include_str!("prelude/hdl/hdl-bus-proto.typort")),
                    ("builtin:///hdl-misc-io.typort", include_str!("prelude/hdl/hdl-misc-io.typort")),
                    ("builtin:///hdl-misc.typort", include_str!("prelude/hdl/hdl-misc.typort")),
                    ("builtin:///hdl-macros.typort", include_str!("prelude/hdl/hdl-macros.typort")),
                    ("builtin:///hdl-verilog.typort", include_str!("prelude/hdl/hdl-verilog.typort")),
                ]);
            }
            docs.push(("builtin:///show.typort", include_str!("prelude/show.typort")));
            let mut next_id = self.document_id.len() as u32;
            for (uri, text) in docs {
                let key = uri.to_string();
                self.document_map.insert(key.clone(), Rope::from_str(text));
                if !self.document_id.contains_key(&key) {
                    self.document_id.insert(key, next_id);
                    next_id += 1;
                }
            }
        }
        // Merge prelude-exported macros into the global macro table.
        for (name, rules) in global_macros {
            self.exported_macros.insert(name, rules);
        }
        // Auto-import prelude: create short aliases for enum cases (e.g., Nat.zero → zero).
        // Namespace-registered instance methods (`TypeHead.method`, e.g. `Bool.mux`)
        // are excluded — methods are only reachable through `x.method` dispatch,
        // never by bare name, so they must not shadow constructor aliases.
        // Short-name collisions between constructors are resolved deterministically:
        // iterating in sorted full-key order makes the `or_insert` (first wins)
        // winner independent of HashMap iteration order.  Mirrors the test/cache
        // path in `L13_namespace::mod.rs::load_prelude_state`.
        {
            let ns_method_keys: std::collections::HashSet<SmolStr> = cxt.namespace.iter()
                .flat_map(|ns| ns.1.iter().map(move |m| SmolStr::new(format!("{}.{}", ns.2, m))))
                .collect();
            let mut aliases: Vec<(SmolStr, SmolStr, _)> = cxt.decl.iter()
                .filter(|(k, _)| k.contains('.') && !ns_method_keys.contains(*k))
                .map(|(k, v)| {
                    let short = SmolStr::new(k.split('.').last().unwrap());
                    (short, k.clone(), v.clone())
                })
                .collect();
            aliases.sort_by(|a, b| a.1.cmp(&b.1));
            let decl_map = Arc::make_mut(&mut cxt.decl);
            for (short, _full_key, v) in aliases {
                decl_map.entry(short).or_insert(v);
            }
        }
        // The cached state is never queried for hover/completion; drop the
        // accumulated tables and the mutable global map so per-file clones
        // stay cheap.
        infer.hover_table.clear();
        infer.hover_table.shrink_to_fit();
        infer.completion_table.clear();
        infer.completion_table.shrink_to_fit();
        infer.inlay_hint_table.clear();
        infer.inlay_hint_table.shrink_to_fit();
        infer.shrink();
        infer.mutable_map.write().unwrap().clear();
        *self.infer.lock().unwrap() = infer;
        *self.cxt.lock().unwrap() = cxt;
    }

    /// 启动工作线程处理分析任务。
    /// 必须在 `load_prelude` 之后调用，确保 prelude 已就绪。
    pub fn spawn_worker(self: &Arc<Self>) {
        let rx = self.job_receiver.lock().unwrap().take()
            .expect("spawn_worker() called more than once");
        let for_thread = self.clone();
        thread::spawn(move || {
            for_thread.worker_loop(rx);
        });
    }

    fn worker_loop(
        &self,
        rx: mpsc::Receiver<AnalysisJob>,
    ) {
        loop {
            // Block until at least one job is available
            let first_job = match rx.recv() {
                Ok(job) => job,
                Err(_) => break, // channel disconnected
            };

            // Drain all remaining queued jobs, keeping only the latest per URI.
            // If user types faster than we can analyze, intermediate versions
            // are skipped — only the most recent content of each file matters.
            let mut latest: HashMap<String, AnalysisJob> = HashMap::new();
            latest.insert(first_job.uri.to_string(), first_job);
            while let Ok(job) = rx.try_recv() {
                latest.insert(job.uri.to_string(), job);
            }

            for (_uri, job) in latest {
                let uri_str = job.uri.to_string();
                self.pending_uris.remove(&uri_str);
                {
                    let (lock, _) = &*self.processed_signal;
                    let mut processed = lock.lock().unwrap();
                    processed.remove(&uri_str);
                    drop(processed);
                }
                self.processing_uris.insert(uri_str.clone(), true);

                // 此时锁已释放，主线程可以放入新任务，我们在处理当前最新的任务
                self.client.log_message(MessageType::LOG, format!("Worker starting job for version {:?}", job.version));
                self.process_file(&job.uri, &job.text, job.version);

                self.processing_uris.remove(&uri_str);
                let (lock, cvar) = &*self.processed_signal;
                let mut processed = lock.lock().unwrap();
                processed.insert(uri_str, true);
                cvar.notify_all();
            }
        }
    }

    pub fn on_change<const MUT:bool>(&self, params: TextDocumentItem<'_>) {
        let start_all = std::time::Instant::now();
        let mut prof = Prof::new();
        self.client.log_message(MessageType::LOG, format!("change: {}", params.uri.as_str()));
        //dbg!(&params.version);
        let rope = ropey::Rope::from_str(params.text);
        self.document_map
            .insert(params.uri.to_string(), rope.clone());
        let now_id = self.document_id.get(params.uri.as_str())
            .map(|x| *x)
            .unwrap_or(self.document_id.len() as u32);
        self.document_id.insert(params.uri.to_string(), now_id);
        let start = std::time::Instant::now();
        // Collect all currently exported macros from the global table
        let global_macros: std::collections::HashMap<String, Vec<MacroRule>> = self.exported_macros.iter()
            .map(|entry| (entry.key().clone(), entry.value().clone()))
            .collect();
        if let Some((decls, parse_errs, new_exports, expansions)) = parser_with_macros(&preprocess(params.text), now_id, &global_macros) {
            prof.mark("parse+preprocess");
            self.client.log_message(MessageType::LOG, format!("parser {:?}", start.elapsed().as_secs_f32()));
            let parser_dur = start.elapsed().as_secs_f64();
            // Merge newly exported macros into the global table
            self.update_file_macros(params.uri.as_str(), &new_exports);
            // Store macro expansions for the "expand macro" feature
            self.macro_expansion_map.insert(params.uri.to_string(), expansions);
            let mut err_collect = vec![];
            // self.ast_map.insert(params.uri.to_string(), decls.clone());
            let mut i = self.infer.lock().unwrap();
            let mut c = self.cxt.lock().unwrap();
            let (mut ic, mut cc);
            let infer: &mut Infer;
            let cxt: &mut Cxt;
            if MUT {
                infer = &mut i;
                cxt = &mut c;
            } else {
                ic = i.clone();
                cc = c.clone();
                infer = &mut ic;
                cxt = &mut cc;
            };
            prof.mark("clone_infer_cxt");
            let mut terms = vec![];
            let start = std::time::Instant::now();
            for tm in decls {
                let decl_start = std::time::Instant::now();
                let f0 = L13_namespace::FUNC_PROF.force.1.load(Ordering::Relaxed);
                let e0 = L13_namespace::FUNC_PROF.eval.1.load(Ordering::Relaxed);
                let q0 = L13_namespace::FUNC_PROF.quote.1.load(Ordering::Relaxed);
                let u0 = L13_namespace::FUNC_PROF.unify.1.load(Ordering::Relaxed);
                let v0 = L13_namespace::FUNC_PROF.v_app.1.load(Ordering::Relaxed);
                match infer.infer(cxt, tm.clone()) {
                    Ok((x, _, new_cxt)) => {
                        if let DeclTm::Println(_, ref s, span) = x {
                            err_collect.push((
                                crate::L13_namespace::Error(span.map(|_| s.clone()), vec![]),
                                DiagnosticSeverity::INFORMATION
                            ))
                        }
                        terms.push(x);
                        *cxt = new_cxt;
                    },
                    Err(err) => {
                        err_collect.push((err, DiagnosticSeverity::ERROR));
	                }
	                }
		                // 取出模式匹配分支中累积的额外类型错误，每个变成独立诊断
		                for err in infer.accumulated_errors.drain(..) {
		                    err_collect.push((err, DiagnosticSeverity::ERROR));
		                }
		                let f1 = L13_namespace::FUNC_PROF.force.1.load(Ordering::Relaxed);
		                let e1 = L13_namespace::FUNC_PROF.eval.1.load(Ordering::Relaxed);
		                let q1 = L13_namespace::FUNC_PROF.quote.1.load(Ordering::Relaxed);
		                let u1 = L13_namespace::FUNC_PROF.unify.1.load(Ordering::Relaxed);
		                let v1 = L13_namespace::FUNC_PROF.v_app.1.load(Ordering::Relaxed);
		                prof.decl(decl_label(&tm), decl_start.elapsed().as_secs_f64(), f1 - f0, e1 - e0, q1 - q0, u1 - u0, v1 - v0);
	            }
	            prof.mark("infer_loop");
	            self.client.log_message(MessageType::LOG, format!("infer {:?}", start.elapsed().as_secs_f32()));
            let infer_dur = start.elapsed().as_secs_f64();
            // Record timing for benchmark
            self.timings.lock().unwrap().push((
                params.uri.to_string(),
                parser_dur,
                infer_dur,
                start_all.elapsed().as_secs_f64(),
            ));
            let is_builtin = params.uri.scheme() == "builtin";
            if !is_builtin {
                self.type_map.insert(params.uri.to_string(), terms);
            }
            if MUT {
                // Prelude load path: drop the per-file tables accumulated in
                // the global infer.  Hover/inlay/completion requests read the
                // per-file snapshots stored below, never the global state.
                infer.hover_table.clear();
                infer.hover_table.shrink_to_fit();
                infer.completion_table.clear();
                infer.completion_table.shrink_to_fit();
                infer.inlay_hint_table.clear();
                infer.inlay_hint_table.shrink_to_fit();
                infer.shrink();
            }
            infer.mutable_map.write().unwrap().clear();
            let mut diags = Vec::new();
            let mut quickfixes_for_uri = HashMap::new();

            // 生成诊断（原有的 err_collect + parse errors）
            for (e, severity) in err_collect.into_iter().chain(parse_errs.into_iter().map(|e| (e.to_err(), DiagnosticSeverity::ERROR))) {
                let start_position = offset_to_position(e.0.start_offset as usize, &rope).unwrap_or_default();
                let end_position = offset_to_position(e.0.end_offset as usize, &rope).unwrap_or_default();
                let mut diagnostic = Diagnostic::new_simple(
                    Range::new(start_position, end_position),
                    e.0.data.clone(),
                );
                diagnostic.severity = Some(severity);

                // 如果有 Quick Fix 修复函数
                if !e.1.is_empty() {
                    // 生成唯一 ID（可用原子计数器或 UUID）
                    static NEXT_ID: AtomicU64 = AtomicU64::new(1);
                    let id = NEXT_ID.fetch_add(1, Ordering::SeqCst).to_string();
                    diagnostic.data = Some(serde_json::Value::String(id.clone()));

                    let mut code_actions: Vec<Box<dyn Fn() -> Option<String> + Send + Sync>> = Vec::new();
                    for fix_fn in e.1.into_iter() {
                        let url = params.uri.clone();
                        code_actions.push(fix_fn);
                    }
                    if !code_actions.is_empty() {
                        quickfixes_for_uri.insert(id, code_actions);
                    }
                }
                diags.push(diagnostic);
            }
            prof.mark("diagnostics");

            // 发布诊断
            self.client.publish_diagnostics(params.uri.clone(), diags, params.version);
            // 存储 Quick Fix 映射（覆盖旧的）
            self.quickfix_map.insert(params.uri.to_string(), quickfixes_for_uri);
            if !is_builtin {
                if MUT {
                    self.hover_table.insert(params.uri.to_string(), infer.clone());
                } else {
                    // Store the elaborated snapshot by MOVING it (no deep clone
                    // of `meta`/trait tables); the local clone is replaced.
                    self.hover_table.insert(params.uri.to_string(), std::mem::replace(infer, Infer::new()));
                }
            }
            prof.mark("publish+snapshot");
        } else {
            // Parser returned None — file has syntax errors.
            // Clear any stale analysis results for this URI so the editor
            // doesn't show outdated hovers / type info from the last good parse.
            self.type_map.remove(params.uri.as_str());
            self.hover_table.remove(params.uri.as_str());
            self.quickfix_map.remove(params.uri.as_str());
            self.macro_expansion_map.remove(params.uri.as_str());
            self.remove_file_macros(params.uri.as_str());
            self.client
                .publish_diagnostics(params.uri.clone(), vec![Diagnostic::new_simple(
                    Range::new(
                        Position { line: 0, character: 0 },
                        Position { line: 0, character: 1 },
                    ), "parse error".to_owned())], params.version);
            self.timings.lock().unwrap().push((
                params.uri.to_string(),
                start_all.elapsed().as_secs_f64(),
                -1.0,
                start_all.elapsed().as_secs_f64(),
            ));
        }
        prof.report(params.uri.as_str(), 10);
        self.client.log_message(MessageType::LOG, format!("change {:?}", start_all.elapsed().as_secs_f32()));
    }

    // ── Cross-file dependency tracking (incremental rebuild) ────────────────

    /// Record `uri`'s freshly-parsed macro exports and rebuild `exported_macros`
    /// accounting for removed names: a macro name is dropped from the global
    /// table only when no other open file exports it (G5).
    fn update_file_macros(&self, uri: &str, new_exports: &HashMap<String, Vec<MacroRule>>) {
        let old: HashSet<String> = self.file_macros.get(uri)
            .map(|e| e.value().clone())
            .unwrap_or_default();
        let new: HashSet<String> = new_exports.keys().cloned().collect();
        // Insert/update this file's exports (last writer wins for name clashes).
        for (name, rules) in new_exports {
            self.exported_macros.insert(name.clone(), rules.clone());
        }
        // Drop names this file no longer exports, if no other file does.
        for name in old.difference(&new) {
            let others_export = self.file_macros.iter()
                .any(|e| e.key() != uri && e.value().contains(name));
            if !others_export {
                self.exported_macros.remove(name);
            }
        }
        if new.is_empty() {
            self.file_macros.remove(uri);
        } else {
            self.file_macros.insert(uri.to_string(), new);
        }
    }

    /// Remove a closed/failed file's macro exports from the global table
    /// (only the names no other open file exports).  Called on file close and
    /// on parse failure (G5/G8).
    fn remove_file_macros(&self, uri: &str) {
        if let Some((_, names)) = self.file_macros.remove(uri) {
            for name in names.iter() {
                let others_export = self.file_macros.iter()
                    .any(|e| e.value().contains(name));
                if !others_export {
                    self.exported_macros.remove(name);
                }
            }
        }
    }

    /// L2: completion items for `import <prefix>.<typed>` / `import <prefix>.{ <typed>`.
    /// Offers the first-level members of the namespace under `<prefix>` that
    /// start with the typed text.  Reads the global decl (works mid-edit even
    /// when the current file failed to parse).
    fn import_context_completions(&self, rope: &Rope, offset: usize, line: &str) -> Vec<CompletionItem> {
        let Some((prefix, typed)) = import_completion_prefix(line) else {
            return vec![];
        };
        let search = format!("{}.", prefix);
        let mut items = vec![];
        let cxt = self.cxt.lock().unwrap();
        for k in cxt.decl.keys() {
            let Some(rest) = k.strip_prefix(&search) else { continue };
            // Only first-level members (`Tree`, `foo` — not `Tree.mk`).
            if rest.contains('.') || !rest.starts_with(&typed) {
                continue;
            }
            let start = offset.checked_sub(typed.len()).unwrap_or(offset);
            let (Some(sp), Some(ep)) = (offset_to_position(start, rope), offset_to_position(offset, rope))
            else { continue };
            items.push(CompletionItem {
                label: rest.to_string(),
                insert_text: Some(rest.to_string()),
                text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                    range: Range::new(sp, ep),
                    new_text: rest.to_string(),
                })),
                kind: Some(CompletionItemKind::FIELD),
                detail: Some(format!("{}.{}", prefix, rest)),
                ..Default::default()
            });
        }
        items.sort_by(|a, b| a.label.cmp(&b.label));
        items
    }

    /// L4: cross-file references.  The cursor is on a definition; find every
    /// open file's use of that definition.  Def-span identity is compared by
    /// path_id + offsets (`Span<()>` PartialEq only compares the payload).
    fn cross_file_references(&self, uri: &Url, offset: usize) -> Option<Vec<Location>> {
        let uri = normalize_builtin_uri(uri);
        let semantic = self.hover_table.get(uri.as_str())?;
        let targets: Vec<(u32, u32, u32)> = semantic.hover_table.iter()
            .filter(|x| x.1.contains(offset))
            .map(|x| (x.1.path_id, x.1.start_offset, x.1.end_offset))
            .collect();
        if targets.is_empty() {
            return Some(vec![]);
        }
        let mut ret: Vec<Location> = Vec::new();
        for entry in self.hover_table.iter() {
            let file_uri = entry.key().clone();
            let f_rope = self.document_map.get(&file_uri)?.clone();
            for x in entry.value().hover_table.iter() {
                if targets.iter().any(|(pid, so, eo)| {
                    *pid == x.1.path_id && *so == x.1.start_offset && *eo == x.1.end_offset
                }) {
                    if let (Some(sp), Some(ep)) = (
                        offset_to_position(x.0.start_offset as usize, &f_rope),
                        offset_to_position(x.0.end_offset as usize, &f_rope),
                    ) {
                        if let Ok(u) = Url::parse(&file_uri) {
                            ret.push(Location::new(u, Range::new(sp, ep)));
                        }
                    }
                }
            }
        }
        Some(ret)
    }

    /// L3: rename the definition under the cursor (and every cross-file use)
    /// to `new_name`.  For a qualified use (`mylib.foo`) only the last segment
    /// is replaced (`mylib.<new>`); bare identifiers are replaced whole.
    fn rename_at(&self, uri: &Url, offset: usize, new_name: &str) -> Option<WorkspaceEdit> {
        let locations = self.cross_file_references(uri, offset)?;
        let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
        for loc in locations {
            let text = self.document_map.get(loc.uri.as_str())?;
            let start = position_to_offset(loc.range.start, &text)?;
            let end = position_to_offset(loc.range.end, &text)?;
            let span_text = text.byte_slice(start..end).to_string();
            let (edit_start, edit_end) = if let Some(dot) = span_text.rfind('.') {
                (start + dot + 1, end)
            } else {
                (start, end)
            };
            let te = TextEdit {
                range: Range::new(
                    offset_to_position(edit_start, &text)?,
                    offset_to_position(edit_end, &text)?,
                ),
                new_text: new_name.to_string(),
            };
            changes.entry(loc.uri.clone()).or_default().push(te);
        }
        Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        })
    }

    /// Recompute the dependency records for `uri` from its import/package decls.
    fn update_deps(&self, uri: &str, decls: &[Decl]) {
        // Clear stale records.
        if let Some(deps) = self.file_deps.get(uri) {
            for ns in deps.value().clone() {
                if let Some(mut d) = self.ns_dependents.get_mut(&ns) {
                    d.remove(uri);
                }
            }
        }
        self.file_deps.remove(uri);
        if let Some(nss) = self.file_namespaces.get(uri) {
            for ns in nss.value() {
                if let Some(mut p) = self.ns_providers.get_mut(ns) {
                    p.remove(uri);
                }
            }
        }
        self.file_namespaces.remove(uri);
        // Re-scan decls.
        let mut deps = HashSet::new();
        let mut namespaces: HashSet<String> = HashSet::new();
        for d in decls {
            match d {
                Decl::Import { prefix, .. } if !prefix.is_empty() => {
                    let ns_str = prefix.join(".");
                    deps.insert(ns_str.clone());
                    self.ns_dependents.entry(ns_str).or_default().insert(uri.to_string());
                }
                Decl::Package { path } => {
                    // G3: a file may declare several packages; record them all.
                    namespaces.insert(path.iter().map(|s| s.data.as_str()).collect::<Vec<_>>().join("."));
                }
                _ => {}
            }
        }
        if !namespaces.is_empty() {
            for ns in &namespaces {
                self.ns_providers.entry(ns.clone()).or_default().insert(uri.to_string());
            }
            self.file_namespaces.insert(uri.to_string(), namespaces);
        }
        if !deps.is_empty() {
            self.file_deps.insert(uri.to_string(), deps);
        }
    }

    /// Remove all dependency records involving `uri` (used on file close).
    fn clear_file_deps(&self, uri: &str) {
        if let Some(deps) = self.file_deps.get(uri) {
            for ns in deps.value().clone() {
                if let Some(mut d) = self.ns_dependents.get_mut(&ns) {
                    d.remove(uri);
                }
            }
        }
        self.file_deps.remove(uri);
        if let Some(nss) = self.file_namespaces.get(uri) {
            for ns in nss.value() {
                if let Some(mut p) = self.ns_providers.get_mut(ns) {
                    p.remove(uri);
                }
            }
        }
        self.file_namespaces.remove(uri);
    }

    /// True when namespace `ns` is a segment-boundary prefix of path `p`
    /// (`p == ns`, or `p` starts with `ns.`).  Used for G2: a provider's
    /// namespace covers every import path under it, so `package a.b` provides
    /// keys matched by `import a.b.C._` where `C` is a type in that package.
    fn ns_prefix_of(&self, ns: &str, p: &str) -> bool {
        p == ns || p.strip_prefix(ns).map_or(false, |rest| rest.starts_with('.'))
    }

    /// All dependents whose import path is under namespace `ns` (prefix match).
    fn dependents_under(&self, ns: &str) -> HashSet<String> {
        let mut out = HashSet::new();
        for e in self.ns_dependents.iter() {
            if self.ns_prefix_of(ns, e.key()) {
                out.extend(e.value().clone());
            }
        }
        out
    }

    /// All providers whose namespace is a prefix of import path `p`.
    fn providers_under(&self, p: &str) -> HashSet<String> {
        let mut out = HashSet::new();
        for e in self.ns_providers.iter() {
            if self.ns_prefix_of(e.key(), p) {
                out.extend(e.value().clone());
            }
        }
        out
    }

    /// DFS helper for `rebuild_set`: visit `f`, recursing into its namespace
    /// providers that are part of the rebuild set, then push `f`.
    fn visit_dep(&self, f: &str, set: &HashSet<String>, visited: &mut HashSet<String>, order: &mut Vec<String>) {
        if !visited.insert(f.to_string()) {
            return;
        }
        if let Some(deps) = self.file_deps.get(f) {
            for dep in deps.value().clone() {
                // G2: providers whose namespace is a prefix of the import path.
                let mut ps: Vec<String> = self.providers_under(&dep).into_iter().collect();
                ps.sort();
                for p in ps {
                    if set.contains(&p) {
                        self.visit_dep(&p, set, visited, order);
                    }
                }
            }
        }
        order.push(f.to_string());
    }

    /// Compute the set of files that must be rebuilt when `changed` changes:
    /// `changed` plus, transitively, every file that imports the namespaces
    /// provided by a file in the set.  Returned in topological order
    /// (dependencies before dependents).
    fn rebuild_set(&self, changed: &str) -> Vec<String> {
        let mut set: HashSet<String> = HashSet::new();
        let mut queue = vec![changed.to_string()];
        set.insert(changed.to_string());
        while let Some(f) = queue.pop() {
            if let Some(nss) = self.file_namespaces.get(&f) {
                for ns in nss.value().clone() {
                    // G2: dependents whose import path is under this namespace.
                    let deps: Vec<String> = self.dependents_under(&ns).into_iter().collect();
                    for d in deps {
                        if set.insert(d.clone()) {
                            queue.push(d);
                        }
                    }
                }
            }
        }
        let set_ref = set.clone();
        let mut order: Vec<String> = Vec::new();
        let mut visited: HashSet<String> = HashSet::new();
        let mut set_list: Vec<String> = set_ref.into_iter().collect();
        set_list.sort();
        for f in &set_list {
            self.visit_dep(f, &set_list.iter().cloned().collect(), &mut visited, &mut order);
        }
        order
    }

    /// Analyze a single file and publish its diagnostics.  The file's symbols
    /// are merged back into the *global* cxt.decl so other files can import
    /// them; on a type error the previous successful symbols are kept.
    fn elaborate(&self, uri: &Url, text: &str, version: Option<i32>) {
        let uri_str = uri.to_string();
        let rope = Rope::from_str(text);
        let global_macros: std::collections::HashMap<String, Vec<MacroRule>> = self.exported_macros.iter()
            .map(|entry| (entry.key().clone(), entry.value().clone()))
            .collect();
        let now_id = self.document_id.get(&uri_str).map(|x| *x).unwrap_or(0);
        if let Some((decls, parse_errs, new_exports, expansions)) = parser_with_macros(&preprocess(text), now_id, &global_macros) {
            self.update_file_macros(&uri_str, &new_exports);
            self.macro_expansion_map.insert(uri_str.clone(), expansions);
            let mut infer = self.infer.lock().unwrap();
            let mut cxt = self.cxt.lock().unwrap();
            // Local cxt = global copy minus this file's previous symbols.
            let mut local_cxt = cxt.clone();
            if let Some(keys) = self.file_symbols.get(&uri_str) {
                let m = Arc::make_mut(&mut local_cxt.decl);
                for k in keys.value().clone() {
                    m.remove(k.as_str());
                }
            }
            // Also drop this file's previous namespace entries from the local
            // cxt (I4): the global still has them; if left in the local clone,
            // the write-back merge would re-add them alongside the freshly
            // re-registered ones → duplicate entries → ambiguous `x.method`.
            if let Some(entry) = self.file_namespace_regs.get(&uri_str) {
                let removed: std::collections::HashSet<usize> = entry.value().iter().map(|(p, _)| *p).collect();
                let keep: Vec<_> = local_cxt.namespace.iter()
                    .filter(|e| !removed.contains(&(std::sync::Arc::as_ptr(&e.0) as usize)))
                    .cloned()
                    .collect();
                local_cxt.namespace = keep.iter().rev()
                    .fold(crate::list::List::new(), |l, e| l.prepend(e.clone()));
            }
            let before_keys: HashSet<SmolStr> = local_cxt.decl.keys().cloned().collect();
            let mut local_infer = infer.clone();
            // Phase 1 (fast): type-check without normalizing `println` args, so
            // tyck errors reach the client before the slow `nf` phase.
            local_infer.defer_println = true;
            // HDL self-check support: purge the previous pass's phase-2
            // leftovers — deferred-println normalization re-runs create-side
            // constructors after the mutable_map clear, re-appending check
            // lines that would otherwise land on this pass's first decl.
            let _ = L13_namespace::take_check_issues(&local_infer);

            fn decl_span(tm: &Decl) -> parser_lib::Span<()> {
                use crate::parser_lib::ToSpan;
                match tm {
                    Decl::Def { name, .. }
                    | Decl::Enum { name, .. }
                    | Decl::TraitDecl { name, .. }
                    | Decl::Class { name, .. } => name.to_span(),
                    _ => parser_lib::Span { data: (), start_offset: 0, end_offset: 0, path_id: 0 },
                }
            }
            fn check_issue_error(line: &str, tm: &Decl) -> L13_namespace::Error {
                L13_namespace::Error(
                    decl_span(tm).map(|_| L13_namespace::format_check_warning(line)),
                    vec![],
                )
            }

            let mut err_collect = vec![];
            let mut terms = vec![];
            for tm in decls {
                match local_infer.infer(&local_cxt, tm.clone()) {
                    Ok((x, _, new_cxt)) => {
                        terms.push(x);
                        local_cxt = new_cxt;
                    }
                    Err(err) => {
                        err_collect.push((err, DiagnosticSeverity::ERROR));
                    }
                }
                for err in local_infer.accumulated_errors.drain(..) {
                    err_collect.push((err, DiagnosticSeverity::ERROR));
                }
                // HDL self-check warnings: attributed to the decl currently
                // being checked (the module close-check runs during the
                // module class decl's elaboration; replays are deduped in
                // take_fresh_check_issues via the CheckIssuesSeen global).
                for line in L13_namespace::take_fresh_check_issues(&local_infer) {
                    err_collect.push((check_issue_error(&line, &tm), DiagnosticSeverity::WARNING));
                }
            }
            let after_keys: HashSet<SmolStr> = local_cxt.decl.keys().cloned().collect();
            let new_keys: HashSet<SmolStr> = after_keys.difference(&before_keys).cloned().collect();
            // Decision 1-a: on type error, keep the previous successful symbols.
            let has_error = err_collect.iter().any(|(_, sev)| *sev == DiagnosticSeverity::ERROR);
            if !has_error {
                // Publish the elaborated decl map by Arc hand-off: the map is
                // immutable from here on (all writes go through make_mut
                // copy-on-write), so a full-table deep clone is unnecessary.
                cxt.decl = local_cxt.decl.clone();
                if new_keys.is_empty() {
                    self.file_symbols.remove(&uri_str);
                } else {
                    self.file_symbols.insert(uri_str.clone(), new_keys.into_iter().map(|k| k.to_string()).collect());
                }
                // I4-cross-file: sync inherent-impl namespace entries into the
                // global cxt.namespace so files importing this file's package
                // can dispatch `x.method`.  This file's previous entries are
                // dropped first (edits may change the method set), then the
                // fresh ones are merged (dedup by type-value pointer) and
                // tracked for removal on close.
                let old: std::collections::HashSet<usize> = self.file_namespace_regs.get(&uri_str)
                    .map(|r| r.value().iter().map(|(p, _)| *p).collect())
                    .unwrap_or_default();
                let keep: Vec<_> = cxt.namespace.iter()
                    .filter(|e| !old.contains(&(std::sync::Arc::as_ptr(&e.0) as usize)))
                    .cloned()
                    .collect();
                cxt.namespace = keep.iter().rev()
                    .fold(crate::list::List::new(), |l, e| l.prepend(e.clone()));
                let mut regs: Vec<(usize, SmolStr)> = Vec::new();
                for entry in local_cxt.namespace.iter() {
                    let already = cxt.namespace.iter()
                        .any(|e| std::sync::Arc::ptr_eq(&e.0, &entry.0));
                    if !already {
                        cxt.namespace = cxt.namespace.prepend(entry.clone());
                        regs.push((std::sync::Arc::as_ptr(&entry.0) as usize, entry.2.clone()));
                    }
                }
                if regs.is_empty() {
                    self.file_namespace_regs.remove(&uri_str);
                } else {
                    self.file_namespace_regs.insert(uri_str.clone(), regs);
                }
            }
            let is_builtin = uri.scheme() == "builtin";
            if !is_builtin {
                self.type_map.insert(uri_str.clone(), terms);
            }
            local_infer.mutable_map.write().unwrap().clear();
            drop(infer);
            drop(cxt);
            let (mut diags, quickfixes_for_uri) = self.build_diags(&uri, &rope, err_collect, parse_errs);
            // Publish tyck errors first (fast path).
            self.client.publish_diagnostics(uri.clone(), diags.clone(), version);
            self.quickfix_map.insert(uri_str.clone(), quickfixes_for_uri);
            // Phase 2: normalize deferred `println`s, then re-publish with the
            // results still bundled alongside the current errors.
            if !local_infer.println_jobs.is_empty() {
                let start = std::time::Instant::now();
                let print_diags = self.println_info_diags(&local_infer, &rope);
                local_infer.println_jobs.clear();
                self.client.log_message(MessageType::LOG, format!("println nf {:?}", start.elapsed().as_secs_f32()));
                diags.extend(print_diags);
                self.client.publish_diagnostics(uri.clone(), diags, version);
            }
            // Store the elaborated snapshot for hover/inlay/completion requests
            // by MOVING it (no deep clone of `meta`/trait tables); the local
            // `local_infer` is replaced with a fresh instance.
            if !is_builtin {
                self.hover_table.insert(uri_str, std::mem::replace(&mut local_infer, Infer::new()));
            }
        } else {
            // Parse error: clear per-file analysis state, keep previous symbols.
            self.type_map.remove(uri.as_str());
            self.hover_table.remove(uri.as_str());
            self.quickfix_map.remove(uri.as_str());
            self.macro_expansion_map.remove(uri.as_str());
            self.remove_file_macros(&uri_str);
            self.client.publish_diagnostics(
                uri.clone(),
                vec![Diagnostic::new_simple(
                    Range::new(
                        Position { line: 0, character: 0 },
                        Position { line: 0, character: 1 },
                    ),
                    "parse error".to_owned(),
                )],
                version,
            );
        }
    }

    /// Convert collected errors into LSP diagnostics (and quick-fix mappings),
    /// without publishing — the caller publishes them (possibly more than once
    /// when deferred `println` results arrive in a second phase).
    fn build_diags(
        &self,
        uri: &Url,
        rope: &Rope,
        err_collect: Vec<(crate::L13_namespace::Error, DiagnosticSeverity)>,
        parse_errs: Vec<crate::L13_namespace::parser::IError>,
    ) -> (Vec<Diagnostic>, HashMap<String, Vec<Box<dyn Fn() -> Option<String> + Send + Sync>>>) {
        let mut diags = Vec::new();
        let mut quickfixes_for_uri = HashMap::new();
        for (e, severity) in err_collect.into_iter().chain(parse_errs.into_iter().map(|e| (e.to_err(), DiagnosticSeverity::ERROR))) {
            let start_position = offset_to_position(e.0.start_offset as usize, rope).unwrap_or_default();
            let end_position = offset_to_position(e.0.end_offset as usize, rope).unwrap_or_default();
            let mut diagnostic = Diagnostic::new_simple(
                Range::new(start_position, end_position),
                e.0.data.clone(),
            );
            diagnostic.severity = Some(severity);
            if !e.1.is_empty() {
                static NEXT_ID: AtomicU64 = AtomicU64::new(1);
                let id = NEXT_ID.fetch_add(1, Ordering::SeqCst).to_string();
                diagnostic.data = Some(serde_json::Value::String(id.clone()));
                let mut code_actions: Vec<Box<dyn Fn() -> Option<String> + Send + Sync>> = Vec::new();
                for fix_fn in e.1.into_iter() {
                    code_actions.push(fix_fn);
                }
                if !code_actions.is_empty() {
                    quickfixes_for_uri.insert(id, code_actions);
                }
            }
            diags.push(diagnostic);
        }
        (diags, quickfixes_for_uri)
    }

    /// Phase 2 of a file analysis: normalize deferred `println` terms and turn
    /// the results into INFORMATION diagnostics (mirroring the pre-existing
    /// inline behavior).
    fn println_info_diags(
        &self,
        infer: &crate::L13_namespace::Infer,
        rope: &Rope,
    ) -> Vec<Diagnostic> {
        let mut diags = Vec::new();
        for job in &infer.println_jobs {
            let s = pretty_tm(0, job.names.clone(), &infer.nf(&job.decl, &job.env, &job.tm));
            let start_position = offset_to_position(job.span.start_offset as usize, rope).unwrap_or_default();
            let end_position = offset_to_position(job.span.end_offset as usize, rope).unwrap_or_default();
            let mut diagnostic = Diagnostic::new_simple(
                Range::new(start_position, end_position),
                s.to_string(),
            );
            diagnostic.severity = Some(DiagnosticSeverity::INFORMATION);
            diags.push(diagnostic);
        }
        diags
    }

    /// Entry point for a changed file: update dependency records, compute the
    /// incremental rebuild set, and re-elaborate each affected file in order.
    pub fn process_file(&self, uri: &Url, text: &str, version: Option<i32>) {
        let start_all = std::time::Instant::now();
        self.client.log_message(MessageType::LOG, format!("change: {}", uri.as_str()));
        let uri_str = uri.to_string();
        self.document_map.insert(uri_str.clone(), Rope::from_str(text));
        let now_id = self.document_id.get(&uri_str)
            .map(|x| *x)
            .unwrap_or(self.document_id.len() as u32);
        self.document_id.insert(uri_str.clone(), now_id);
        let global_macros: std::collections::HashMap<String, Vec<MacroRule>> = self.exported_macros.iter()
            .map(|entry| (entry.key().clone(), entry.value().clone()))
            .collect();
        if let Some((decls, _, _, _)) = parser_with_macros(&preprocess(text), now_id, &global_macros) {
            self.update_deps(&uri_str, &decls);
        }
        let rebuild = self.rebuild_set(&uri_str);
        for f in &rebuild {
            let f_text = self.document_map.get(f).map(|r| r.to_string()).unwrap_or_default();
            if let Ok(f_url) = Url::parse(f) {
                let f_version = if f == &uri_str { version } else { None };
                self.elaborate(&f_url, &f_text, f_version);
            }
        }
        self.client.log_message(MessageType::LOG, format!("change {:?}", start_all.elapsed().as_secs_f32()));
    }

    /// Remove a closed file's symbols from the global cxt and rebuild its dependents.
    pub fn remove_file(&self, uri: &Url) {
        let uri_str = uri.to_string();
        let dependents: Vec<String> = {
            let mut deps = HashSet::new();
            if let Some(nss) = self.file_namespaces.get(&uri_str) {
                for ns in nss.value().clone() {
                    // G2: dependents whose import path is under this namespace.
                    deps.extend(self.dependents_under(&ns));
                }
            }
            deps.into_iter().collect()
        };
        {
            let mut infer = self.infer.lock().unwrap();
            let mut cxt = self.cxt.lock().unwrap();
            if let Some(keys) = self.file_symbols.get(&uri_str) {
                let m = Arc::make_mut(&mut cxt.decl);
                for k in keys.value().clone() {
                    m.remove(k.as_str());
                }
            }
            self.file_symbols.remove(&uri_str);
            // I4-cross-file: drop this file's merged namespace entries.
            if let Some((_, regs)) = self.file_namespace_regs.remove(&uri_str) {
                let removed: std::collections::HashSet<usize> = regs.iter().map(|(p, _)| *p).collect();
                let keep: Vec<_> = cxt.namespace.iter()
                    .filter(|e| !removed.contains(&(std::sync::Arc::as_ptr(&e.0) as usize)))
                    .cloned()
                    .collect();
                cxt.namespace = keep.iter().rev()
                    .fold(crate::list::List::new(), |l, e| l.prepend(e.clone()));
            }
            drop(infer);
            drop(cxt);
        }
        self.clear_file_deps(&uri_str);
        self.type_map.remove(uri.as_str());
        self.hover_table.remove(uri.as_str());
        self.quickfix_map.remove(uri.as_str());
        self.macro_expansion_map.remove(uri.as_str());
        self.remove_file_macros(&uri_str);
        for f in dependents {
            if let Some(text) = self.document_map.get(&f).map(|r| r.to_string()) {
                if let Ok(f_url) = Url::parse(&f) {
                    self.elaborate(&f_url, &text, None);
                }
            }
        }
    }

    /// Goto-definition for macro invocations. The cursor is matched against
    /// the use-site spans recorded during parsing (`macro_expansion_map`):
    /// first against the macro name token span, then against the full
    /// invocation span. The matched expansion carries the definition span and
    /// path_id of the rule that actually matched, so the target resolves
    /// across files (e.g. the prelude's `hdl-macros.typort`).
    ///
    /// Note: the full `goto_definition` path uses `goto_macro_definition_name`
    /// first and only falls back to this method (which also matches the whole
    /// invocation span) when the semantic hover table has nothing for the
    /// cursor position.
    pub fn goto_macro_definition(&self, uri: &Url, offset: usize) -> Option<GotoDefinitionResponse> {
        let uri_str = uri.as_str();
        let exp = self.macro_expansion_at(&uri_str, offset, false)?;
        self.macro_def_location(uri, &exp)
    }

    /// Name-token-only variant of `goto_macro_definition`: the cursor must be
    /// inside the macro NAME token of an invocation. `goto_definition` uses
    /// this before the semantic hover table, so a click on the `calc` keyword
    /// jumps to `macro_rules calc` while a click on an identifier inside the
    /// macro body resolves to that identifier's own definition.
    pub fn goto_macro_definition_name(&self, uri: &Url, offset: usize) -> Option<GotoDefinitionResponse> {
        let uri_str = uri.as_str();
        let exp = self.macro_expansion_at(&uri_str, offset, true)?;
        self.macro_def_location(uri, &exp)
    }

    /// The `MacroExpansionInfo` whose span covers `offset`, preferring the
    /// innermost (smallest) match. With `name_only`, only the macro name token
    /// span matches; otherwise the full invocation span is the fallback.
    fn macro_expansion_at(
        &self,
        uri_str: &str,
        offset: usize,
        name_only: bool,
    ) -> Option<MacroExpansionInfo> {
        let expansions = self.macro_expansion_map.get(uri_str)?;
        let name_match = || expansions.iter()
            // Only expansions whose recorded `name` is an actual macro name
            // token at the call site participate in the name-token match.
            // Fragment-driven expansions (Expr inside a module/when body) use
            // the first call-site token as `name`; for a plain body statement
            // (`sum := a +^ b`) that token is user code, and clicking it must
            // NOT jump to the fragment macro's definition.
            .filter(|e| e.name_token_is_macro)
            .filter(|e| offset >= e.start_offset as usize && offset < e.start_offset as usize + e.name.len())
            .min_by_key(|e| e.end_offset - e.start_offset)
            .cloned();
        if name_only {
            name_match()
        } else {
            name_match().or_else(|| expansions.iter()
                .filter(|e| offset >= e.start_offset as usize && offset < e.end_offset as usize)
                .min_by_key(|e| e.end_offset - e.start_offset)
                .cloned())
        }
    }

    /// Resolve a matched expansion's definition location (macro_rules name
    /// token + defining file) into an LSP Location. `None` for built-in macros
    /// such as `stringify`, which have no textual definition.
    fn macro_def_location(&self, uri: &Url, exp: &MacroExpansionInfo) -> Option<GotoDefinitionResponse> {
        let uri_str = uri.as_str();
        let (def_start, def_end, def_path_id) = (
            exp.def_start_offset?,
            exp.def_end_offset?,
            exp.def_path_id?,
        );
        let def_uri = self.document_id.iter()
            .find(|e| *e.value() == def_path_id)
            .map(|e| Url::parse(e.key()).ok())
            .flatten()
            .unwrap_or_else(|| uri.clone());
        let def_rope = if def_uri.as_str() == uri_str {
            self.document_map.get(uri_str)?.clone()
        } else {
            self.document_map.get(def_uri.as_str())?.clone()
        };
        let start_position = offset_to_position(def_start as usize, &def_rope)?;
        let end_position = offset_to_position(def_end as usize, &def_rope)?;
        Some(GotoDefinitionResponse::Scalar(Location::new(
            def_uri,
            Range::new(start_position, end_position),
        )))
    }

    /// Full goto-definition logic shared by the LSP `textDocument/definition`
    /// handler and tests. Resolution order:
    ///
    /// 1. A click on a macro invocation's NAME token resolves to the matching
    ///    `macro_rules` declaration (e.g. the `calc` keyword → the calc macro).
    /// 2. Semantic resolution from the hover table. The most specific entry
    ///    (smallest span containing the cursor) wins — macro expansion emits
    ///    whole-invocation-span entries for its literal tokens, which are
    ///    larger than the user's own tokens, so identifiers written inside a
    ///    macro body (variables, functions, types) resolve to their own
    ///    definitions, not to the macro's.
    /// 3. Fallback: a cursor anywhere else inside a macro invocation with no
    ///    semantic entry (e.g. a macro argument naming a declaration) resolves
    ///    to the macro definition via the full invocation span.
    pub fn goto_definition_at(&self, uri: &Url, offset: usize) -> Option<GotoDefinitionResponse> {
        // 1. Macro name token → macro definition.
        if let Some(def) = self.goto_macro_definition_name(uri, offset) {
            return Some(def);
        }
        // 2. Semantic resolution (most specific entry wins, like hover).
        let semantic = self.hover_table.get(uri.as_str())?;
        let file_id = self.document_id.get(uri.as_str())?;
        let interval = semantic.hover_table
            .iter()
            .filter(|x| x.0.path_id == *file_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
            .and_then(|x| {
                let def_span = &x.1;
                // Look up the source file URI for the definition span's path_id
                let def_uri = self.document_id.iter()
                    .find(|e| *e.value() == def_span.path_id)
                    .map(|e| Url::parse(e.key()).ok())
                    .flatten()
                    .unwrap_or_else(|| uri.clone());
                let def_rope = if def_uri == *uri {
                    self.document_map.get(uri.as_str())?.clone()
                } else {
                    self.document_map.get(def_uri.as_str())?.clone()
                };
                let start_position = offset_to_position(def_span.start_offset as usize, &def_rope)?;
                let end_position = offset_to_position(def_span.end_offset as usize, &def_rope)?;
                Some(GotoDefinitionResponse::Scalar(
                    Location::new(
                        def_uri,
                        Range::new(start_position, end_position),
                    )
                ))
            })
            .or({
                let rope = self.document_map.get(uri.as_str())?;
                let ret: Vec<Location> = semantic.hover_table
                    .iter()
                    .filter(|x| x.1.contains(offset))
                    .map(|x| x.0)
                    .flat_map(|x| Some(Location::new(
                        uri.clone(),
                        Range::new(
                            offset_to_position(x.start_offset as usize, &rope)?,
                            offset_to_position(x.end_offset as usize, &rope)?,
                        )
                    )))
                    .collect();
                if ret.is_empty() {
                    None
                } else {
                    Some(GotoDefinitionResponse::Array(ret))
                }
            });
        if interval.is_some() {
            return interval;
        }
        // 3. Full-invocation fallback → macro definition.
        self.goto_macro_definition(uri, offset)
    }

    /// Completion handler body, kept on the generic `Backend<C>` so the real
    /// request path is directly exercised by integration tests (the concrete
    /// `LanguageServer for Backend<Client>` impl forwards to it).
    pub fn completion_at(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let uri = normalize_builtin_uri(&uri);
        let uri_str = uri.to_string();

        // Wait for any pending/ongoing analysis of this file to complete,
        // so completion_table reflects the most recent edit.
        {
            let (lock, cvar) = &*self.processed_signal;
            let mut processed = lock.lock().unwrap();
            let start = std::time::Instant::now();
            let timeout = Duration::from_millis(1500);
            while start.elapsed() < timeout
                && (self.pending_uris.contains_key(&uri_str)
                    || self.processing_uris.contains_key(&uri_str))
            {
                if processed.contains_key(&uri_str) {
                    break;
                }
                processed = cvar.wait_timeout(processed, Duration::from_millis(50)).unwrap().0;
            }
            processed.remove(&uri_str);
        }

        self.client.log_message(MessageType::LOG, "on completion".to_string());
        let position = params.text_document_position.position;
        let completions = || -> Option<Vec<CompletionItem>> {
            let rope = self.document_map.get(&uri.to_string())?;
            // Position -> byte offset, UTF-16 aware (same as hover/definition).
            // The old `try_line_to_char + character` math mixed char and byte
            // offsets, which drifted whenever a non-ASCII character appeared
            // before the cursor.
            let offset = position_to_offset(position, &rope)?;
            // L2: import-context completion — `import mylib.<prefix>` /
            // `import mylib.{ <prefix>`.  Runs even when the file is mid-edit
            // (incomplete import → parse error → hover_table absent).
            let before = rope.byte_slice(0..offset).to_string();
            let line = before.rsplit('\n').next().unwrap_or("");
            let mut items = self.import_context_completions(&rope, offset, line);
            let mut seen: HashSet<String> = items.iter().map(|i| i.label.clone()).collect();
            // Member-access completions need a successful analysis.
            if let Some(infer) = self.hover_table.get(&uri.to_string()) {
                infer.completion_table
                    .iter()
                    // Member-access entries are keyed to the receiver's span:
                    // `x.<prefix>` for typed names, but only `x` for the empty
                    // `x.` state (the dangling dot is not part of the span).
                    // Match when the cursor is on that span (hover-style), or
                    // exactly at its end (cursor right after the typed member
                    // name), or one byte past it with a `.` in between (cursor
                    // right after the trigger dot).  The old `contains(offset -
                    // 2)` hack covered at most two of these cases and missed
                    // longer typed prefixes.
                    .filter(|(span, _)| {
                        let end = span.end_offset as usize;
                        span.contains(offset)
                            || offset == end
                            || (offset == end + 1
                                && rope.byte_slice(end..end + 1).chars().next() == Some('.'))
                    })
                    .filter_map(|(span, name)| {
                        if !seen.insert(name.to_string()) {
                            return None;
                        }
                        // Replace the typed member prefix (`x.<le>` -> `x.<length>`)
                        // instead of relying on client-side word replacement.
                        let prefix_start = member_prefix_start(&rope, offset).unwrap_or(offset);
                        let range = Range::new(
                            offset_to_position(prefix_start, &rope)?,
                            offset_to_position(offset, &rope)?,
                        );
                        Some(CompletionItem {
                            label: name.to_string(),
                            insert_text: Some(name.to_string()),
                            text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                                range,
                                new_text: name.to_string(),
                            })),
                            kind: Some(CompletionItemKind::VARIABLE),
                            detail: Some(name.to_string()),
                            ..Default::default()
                        })
                    })
                    .for_each(|i| items.push(i));
            }
            Some(items)
        }();
        Ok(completions.map(CompletionResponse::Array))
    }
}

impl LanguageServer for Backend<Client> {
    fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            server_info: None,
            offset_encoding: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::INCREMENTAL),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                            include_text: Some(true),
                        })),
                        ..Default::default()
                    },
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                inlay_hint_provider: Some(OneOf::Left(true)),
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(false),
                    trigger_characters: Some(vec![".".to_string()]),
                    work_done_progress_options: Default::default(),
                    all_commit_characters: None,
                    completion_item: None,
                }),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec!["typort.applyQuickFix".to_string()],
                    work_done_progress_options: Default::default(),
                }),

                workspace: Some(WorkspaceServerCapabilities {
                    workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                        supported: Some(true),
                        change_notifications: Some(OneOf::Left(true)),
                    }),
                    file_operations: None,
                }),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Left(true)),
                ..ServerCapabilities::default()
            },
        })
    }
    fn initialized(&self, _: InitializedParams) {
        debug!("initialized!");
    }

    fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    fn did_open(&self, params: DidOpenTextDocumentParams) {
        // Skip builtin:// prelude files — they are already loaded during load_prelude()
        if params.text_document.uri.scheme() == "builtin" {
            return;
        }
        // Store full text for incremental sync
        self.document_buffers.lock().unwrap().insert(
            params.text_document.uri.to_string(),
            params.text_document.text.to_string(),
        );
        let uri = params.text_document.uri.to_string();
        self.pending_uris.insert(uri.clone(), true);
        let job = AnalysisJob {
            uri: params.text_document.uri.clone(),
            text: params.text_document.text.to_string(),
            version: Some(params.text_document.version),
        };
        self.job_sender.send(job).ok();
    }

    fn did_change(&self, params: DidChangeTextDocumentParams) {
        // Skip builtin:// prelude files — they are read-only virtual documents
        if params.text_document.uri.scheme() == "builtin" {
            return;
        }
        // Apply incremental edits to the stored document buffer
        let full_text = {
            let mut buffers = self.document_buffers.lock().unwrap();
            if let Some(buffer) = buffers.get_mut(params.text_document.uri.as_str()) {
                for change in &params.content_changes {
                    if let Some(range) = change.range {
                        // Incremental edit: replace text at the specified range
                        let rope = Rope::from_str(buffer);
                        if let (Some(start), Some(end)) = (
                            position_to_offset(range.start, &rope),
                            position_to_offset(range.end, &rope),
                        ) {
                            let mut rope = rope;
                            // Convert byte offsets to char offsets for ropey operations
                            let start_char = rope.byte_to_char(start);
                            let end_char = rope.byte_to_char(end);
                            rope.remove(start_char..end_char);
                            rope.insert(start_char, &change.text);
                            *buffer = rope.to_string();
                        } else {
                            // Fallback: position conversion failed, replace whole text
                            *buffer = change.text.clone();
                        }
                    } else {
                        // No range = full text replacement
                        *buffer = change.text.clone();
                    }
                }
                buffer.clone()
            } else {
                // No existing buffer — fallback to first change's text
                params.content_changes[0].text.clone()
            }
        };
        let uri = params.text_document.uri.to_string();
        self.pending_uris.insert(uri.clone(), true);
        let job = AnalysisJob {
            uri: params.text_document.uri.clone(),
            text: full_text,
            version: Some(params.text_document.version),
        };
        self.job_sender.send(job).ok();
    }

    fn did_save(&self, params: DidSaveTextDocumentParams) {
        // Skip builtin:// prelude files — they are read-only virtual documents
        if params.text_document.uri.scheme() == "builtin" {
            return;
        }
        if let Some(text) = params.text {
            let uri = params.text_document.uri.to_string();
            self.pending_uris.insert(uri.clone(), true);
            let job = AnalysisJob {
                uri: params.text_document.uri.clone(),
                text,
                version: None,
            };
            self.job_sender.send(job).ok();
        }
        debug!("file saved!");
    }
    fn did_close(&self, params: DidCloseTextDocumentParams) {
        debug!("file closed!");
        let uri = params.text_document.uri;
        self.document_buffers.lock().unwrap().remove(uri.as_str());
        // Remove the file's symbols from the global cxt and rebuild dependents.
        if !self.file_symbols.contains_key(uri.as_str()) {
            return;
        }
        self.remove_file(&uri);
    }

    fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let hover = || -> Option<Hover> {
            let uri = params.text_document_position_params.text_document.uri;
            let uri = normalize_builtin_uri(&uri);
            let semantic = self.type_map.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let id = self.document_id.get(uri.as_str())?;
            let position = params.text_document_position_params.position;
            let offset = position_to_offset(position, &rope)?;
            semantic.iter()
                .flat_map(|x| match x {
                    DeclTm::Def { name, typ_pretty, body_pretty, .. } => Some((name, typ_pretty, body_pretty)),
                    _ => None
                })
                .find(|x| x.0.contains(offset))
                .and_then(|x| Some(Hover {
                    contents: HoverContents::Markup(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: format!("{}\n\n{}", x.1, x.2),
                    }),
                    range: Some(Range::new(
                        offset_to_position(x.0.start_offset as usize, &rope)?,
                        offset_to_position(x.0.end_offset as usize, &rope)?,
                    )),
                }))
                .or_else(|| {
                    self.hover_table
                        .get(uri.as_str())
                        .and_then(|x| x.hover_entry_at(*id, offset)
                            .map(|(span, _, hcxt, val)| (*span, pretty_tm(0, hcxt.names(), &x.quote(&hcxt.decl, hcxt.lvl, val))))
                        )
                        .and_then(|x| Some(Hover {
                            contents: HoverContents::Markup(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: x.1.to_string(),
                            }),
                            range: Some(Range::new(
                                offset_to_position(x.0.start_offset as usize, &rope)?,
                                offset_to_position(x.0.end_offset as usize, &rope)?,
                            )),
                        }))
                })
        };
         Ok(hover())
    }

    fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let uri = normalize_builtin_uri(&params.text_document.uri);
        let hints = || -> Option<Vec<InlayHint>> {
            let infer = self.hover_table.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let mut ret = Vec::new();
            for (offset, label) in &infer.inlay_hint_table {
                let position = offset_to_position(*offset as usize, &rope)?;
                ret.push(InlayHint {
                    position,
                    label: InlayHintLabel::String(label.clone()),
                    kind: Some(InlayHintKind::TYPE),
                    text_edits: None,
                    tooltip: None,
                    padding_left: Some(true),
                    padding_right: None,
                    data: None,
                });
            }
            Some(ret)
        }();
        Ok(hints)
    }

    fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let definition = || -> Option<GotoDefinitionResponse> {
            let uri = params.text_document_position_params.text_document.uri;
            let uri = normalize_builtin_uri(&uri);
            let rope = self.document_map.get(uri.as_str())?;
            let position = params.text_document_position_params.position;
            let offset = position_to_offset(position, &rope)?;
            self.goto_definition_at(&uri, offset)
        };
        Ok(definition())
    }

    fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let reference_list = || -> Option<Vec<Location>> {
            let uri = normalize_builtin_uri(&params.text_document_position.text_document.uri);
            let rope = self.document_map.get(uri.as_str())?;
            let offset = position_to_offset(params.text_document_position.position, &rope)?;
            self.cross_file_references(&uri, offset)
        }();
        Ok(reference_list)
    }

    fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let edit = || -> Option<WorkspaceEdit> {
            let uri = normalize_builtin_uri(&params.text_document_position.text_document.uri);
            let rope = self.document_map.get(uri.as_str())?;
            let offset = position_to_offset(params.text_document_position.position, &rope)?;
            self.rename_at(&uri, offset, &params.new_name)
        }();
        Ok(edit)
    }

    fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        self.completion_at(params)
    }

    fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        debug!("configuration changed!");
    }

    fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {
        debug!("workspace folders changed!");
    }

    fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        debug!("watched files have changed!");
    }

    fn execute_command(&self, params: ExecuteCommandParams) -> Result<Option<Value>> {
        if params.command == "typort.applyQuickFix" {
            let args = params.arguments;
            let uri: String = serde_json::from_value(args[0].clone()).unwrap();
            let id: String = serde_json::from_value(args[1].clone()).unwrap();

			let result_text = if let Some(map) = self.quickfix_map.get(&uri) {
				if let Some(code_actions) = map.get(&id) {
					code_actions.iter().flat_map(|x| {
						x()
					}).next()
						.unwrap_or("failed to find a solution".to_owned())
				} else {
					"failed to find a solution".to_owned()
				}
			} else {
				"failed to find a solution".to_owned()
			};

            self.client.show_message(MessageType::INFO, format!("find a possible solution: {}", result_text));
        }
        Ok(None)
    }

    fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = normalize_builtin_uri(&params.text_document.uri).to_string();
        if let Some(map) = self.quickfix_map.get(&uri) {
            let mut actions = Vec::new();
            for diagnostic in params.context.diagnostics {
                if let Some(data) = diagnostic.data {
                    if let Some(id) = data.as_str() {
                        if map.get(id).is_some() {
                            let command = Command {
                                title: "Canonical Quick Fix".to_string(),
                                command: "typort.applyQuickFix".to_string(),
                                arguments: Some(vec![
                                    serde_json::Value::String(uri.clone()),
                                    serde_json::Value::String(id.to_string()),
                                ]),
                            };
                            actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                                title: "Search solution".to_string(),
                                kind: Some(CodeActionKind::QUICKFIX),
                                command: Some(command),
                                edit: None,
                                ..Default::default()
                            }));
                        }
                    }
                }
            }
            if !actions.is_empty() {
                return Ok(Some(actions));
            }
        }
        Ok(None)
    }
}

impl Backend<Client> {
    pub fn init(&self) -> std::result::Result<serde_json::Value, ProtocolError> {
        let server_capabilities = serde_json::to_value(
            self.initialize(Default::default()).unwrap().capabilities
        ).unwrap();
        self.client.connection.initialize(server_capabilities)
    }
    pub fn main_loop(&self) -> std::result::Result<(), Box<dyn Error + Sync + Send>> {
        self.client.log_message(MessageType::INFO, "starting example main loop".to_string());
        for msg in self.client.connection.receiver.clone() {
            match msg {
                Message::Request(req) => {
                    if self.client.connection.handle_shutdown(&req)? {
                        return Ok(());
                    }
                    // Custom request: fetch prelude/builtin file content for virtual documents
                    if req.method == "typort-hdl/builtinContent" {
                        #[derive(Deserialize)]
                        struct BuiltinContentParams {
                            uri: String,
                        }
                        match serde_json::from_value::<BuiltinContentParams>(req.params) {
                            Ok(params) => {
                                let content = self.get_builtin_content(&params.uri);
                                let resp = Response { id: req.id, result: Some(serde_json::to_value(&content).unwrap()), error: None };
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                            Err(_) => {
                                let resp = Response::new_err(req.id, -32602, "Invalid params: expected { uri: string }".into());
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                        }
                        continue;
                    }
                    // Custom request: expand macro at cursor position
                    if req.method == "typort-hdl/expandMacro" {
                        #[derive(Deserialize)]
                        struct ExpandMacroParams {
                            uri: String,
                            position: lsp_types::Position,
                        }
                        #[derive(Serialize)]
                        struct ExpandMacroResult {
                            name: String,
                            range: lsp_types::Range,
                            expanded_text: String,
                        }
                        match serde_json::from_value::<ExpandMacroParams>(req.params) {
                            Ok(params) => {
                                // Normalize URI: parse into Url to handle builtin:/// vs builtin:/
                                // and ensure consistent casing on Windows.
                                let uri = Url::parse(&params.uri)
                                    .map(|u| normalize_builtin_uri(&u).to_string())
                                    .unwrap_or(params.uri);
                                self.client.log_message(MessageType::LOG,
                                    format!("expandMacro: uri={:?}, pos={}:{}",
                                        uri, params.position.line, params.position.character));
                                let has_expansions = self.macro_expansion_map.contains_key(&uri);
                                let has_doc = self.document_map.contains_key(&uri);
                                let expansions_count = self.macro_expansion_map.get(&uri).map(|e| e.len()).unwrap_or(0);
                                self.client.log_message(MessageType::LOG,
                                    format!("expandMacro: in map? {} ({} expansions), doc? {}",
                                        has_expansions, expansions_count, has_doc));
                                if !has_expansions {
                                    self.client.log_message(MessageType::LOG,
                                        format!("expandMacro: available uris in macro_expansion_map: {:?}",
                                            self.macro_expansion_map.iter().map(|e| e.key().clone()).collect::<Vec<_>>()));
                                }
                                let result = self.macro_expansion_map.get(&uri).and_then(|expansions| {
                                    let rope = self.document_map.get(&uri)?;
                                    let offset = position_to_offset(params.position, &rope)?;
                                    self.client.log_message(MessageType::LOG,
                                        format!("expandMacro: cursor byte offset={}", offset));
                                    let found = expansions.iter().find(|e| {
                                        offset >= e.start_offset as usize && offset < e.end_offset as usize
                                    });
                                    if found.is_none() {
                                        self.client.log_message(MessageType::LOG,
                                            format!("expandMacro: no match among {} expansions at offset {}",
                                                expansions.len(), offset));
                                        for (i, e) in expansions.iter().enumerate() {
                                            self.client.log_message(MessageType::LOG,
                                                format!("  expansion[{}]: name={:?} range={}-{}",
                                                    i, e.name, e.start_offset, e.end_offset));
                                        }
                                    }
                                    found.map(|e| {
                                        let start = offset_to_position(e.start_offset as usize, &rope)?;
                                        let end = offset_to_position(e.end_offset as usize, &rope)?;
                                        Some(ExpandMacroResult {
                                            name: e.name.clone(),
                                            range: lsp_types::Range::new(start, end),
                                            expanded_text: e.expanded_text.clone(),
                                        })
                                    }).flatten()
                                });
                                self.client.log_message(MessageType::LOG,
                                    format!("expandMacro: result={}", result.is_some()));
                                let resp = Response { id: req.id, result: Some(serde_json::to_value(&result).unwrap()), error: None };
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                            Err(_) => {
                                let resp = Response::new_err(req.id, -32602, "Invalid params: expected { uri: string, position: { line: u32, character: u32 } }".into());
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                        }
                        continue;
                    }
                    match cast::<GotoDefinition>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.goto_definition(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<HoverRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.hover(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<InlayHintRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.inlay_hint(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<Completion>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.completion(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            if !self.cancelled_requests.lock().unwrap().remove(&id) {
                                let resp = Response { id, result: Some(result), error: None };
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<References>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.references(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<SemanticTokensFullRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.semantic_tokens_full(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            if !self.cancelled_requests.lock().unwrap().remove(&id) {
                                let resp = Response { id, result: Some(result), error: None };
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<SemanticTokensRangeRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.semantic_tokens_range(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            if !self.cancelled_requests.lock().unwrap().remove(&id) {
                                let resp = Response { id, result: Some(result), error: None };
                                self.client.connection.sender.send(Message::Response(resp))?;
                            }
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<Rename>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.rename(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<CodeActionRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.code_action(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<ExecuteCommand>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.execute_command(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                }
                Message::Response(resp) => {
                }
                Message::Notification(not) => {
                    let is_cancel = not.method == "$/cancelRequest";
                    if is_cancel {
                        if let Ok(cancel) = serde_json::from_value::<CancelParams>(not.params) {
                            let rid = match cancel.id {
                                NumberOrString::Number(n) => RequestId::from(n as i32),
                                NumberOrString::String(s) => RequestId::from(s),
                            };
                            self.client.log_message(MessageType::LOG, format!("cancelled request {:?}", rid));
                            self.cancelled_requests.lock().unwrap().insert(rid);
                        }
                    } else {
                        match on::<DidOpenTextDocument>(not.clone()) {
                            Ok(params) => {
                                self.did_open(params);
                            },
                            Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                            Err(ExtractError::MethodMismatch(not)) => (),
                        }
                        match on::<DidChangeTextDocument>(not.clone()) {
                            Ok(params) => {
                                self.did_change(params);
                            },
                            Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                            Err(ExtractError::MethodMismatch(not)) =>(),
                        }
                        match on::<DidCloseTextDocument>(not.clone()) {
                            Ok(params) => {
                                self.did_close(params);
                            },
                            Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                            Err(ExtractError::MethodMismatch(not)) => (),
                        }
                        match on::<DidSaveTextDocument>(not) {
                            Ok(params) => {
                                self.did_save(params);
                            },
                            Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                            Err(ExtractError::MethodMismatch(not)) => (),
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[allow(unused)]
enum CustomNotification {}
impl Notification for CustomNotification {
    type Params = InlayHintParams;
    const METHOD: &'static str = "custom/notification";
}

/// Normalize a builtin:// URI for map lookups.
/// VS Code serializes builtin:/// → builtin:/ (empty authority → no //),
/// but our maps store keys with builtin:///.
fn normalize_builtin_uri(uri: &Url) -> Url {
    let s = uri.as_str();
    if s.starts_with("builtin:/") && !s.starts_with("builtin://") {
        if let Ok(normalized) = Url::parse(&s.replacen("builtin:/", "builtin:///", 1)) {
            return normalized;
        }
    }
    // VSCode may use memfs:// scheme for in-memory virtual files;
    // normalize to file:// to match keys in document_map / macro_expansion_map.
    if uri.scheme() == "memfs" {
        let mut u = uri.clone();
        let _ = u.set_scheme("file");
        return u;
    }
    uri.clone()
}

pub struct TextDocumentItem<'a> {
    pub uri: Url,
    pub text: &'a str,
    pub version: Option<i32>,
}

pub fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
    let line = rope.try_byte_to_line(offset).ok()?;
    let line_byte_start = rope.try_line_to_byte(line).ok()?;
    let line_text = rope.line(line);
    // Convert byte offset to UTF-16 code unit column position
    let mut column = 0u32;
    let mut byte_i = 0usize;
    for ch in line_text.chars() {
        if line_byte_start + byte_i >= offset {
            break;
        }
        column += ch.len_utf16() as u32;
        byte_i += ch.len_utf8();
    }
    Some(Position::new(line as u32, column))
}

pub fn position_to_offset(position: Position, rope: &Rope) -> Option<usize> {
    let line_byte_start = rope.try_line_to_byte(position.line as usize).ok()?;
    let line_text = rope.line(position.line as usize);
    // Convert UTF-16 code unit column to byte offset within line
    let mut col_byte_offset = 0usize;
    let mut utf16_count = 0u32;
    for ch in line_text.chars() {
        if utf16_count >= position.character {
            break;
        }
        col_byte_offset += ch.len_utf8();
        utf16_count += ch.len_utf16() as u32;
    }
    Some(line_byte_start + col_byte_offset)
}

/// Byte offset of the start of the member name being completed at `offset`:
/// one past the last `.` on the same line before the cursor.  The completion's
/// text edit replaces exactly the typed member prefix (`x.<le>` -> `x.<len>`).
/// Falls back to `offset` (pure insertion) when no dot precedes the cursor.
pub fn member_prefix_start(rope: &Rope, offset: usize) -> Option<usize> {
    let line = rope.try_byte_to_line(offset).ok()?;
    let line_byte_start = rope.try_line_to_byte(line).ok()?;
    let mut dot: Option<usize> = None;
    let mut byte_i = line_byte_start;
    for ch in rope.line(line).chars() {
        if byte_i >= offset {
            break;
        }
        if ch == '.' {
            dot = Some(byte_i);
        }
        byte_i += ch.len_utf8();
    }
    dot.map(|d| d + 1)
}

/// For a line like `import mylib.<typed>` or `import mylib.{ a, <typed>`,
/// return the namespace prefix and the typed member prefix.  None when the
/// cursor is not inside an import statement.
fn import_completion_prefix(line: &str) -> Option<(String, String)> {
    let rest = line.trim_start().strip_prefix("import")?.trim_start();
    if rest.is_empty() {
        return None;
    }
    let last_dot = rest.rfind('.');
    let last_brace = rest.rfind('{');
    let sep = match (last_dot, last_brace) {
        (Some(d), Some(b)) => d.max(b),
        (Some(d), None) => d,
        (None, Some(b)) => b,
        (None, None) => return None,
    };
    let prefix = rest[..sep]
        .trim_end_matches(|c| c == '{' || c == ' ' || c == '\t')
        .trim_end_matches('.');
    if prefix.is_empty() {
        return None;
    }
    let mut typed = rest[sep + 1..].trim_start();
    if let Some(c) = typed.rfind(',') {
        typed = typed[c + 1..].trim_start();
    }
    Some((prefix.to_string(), typed.to_string()))
}

pub fn cast<R>(req: Request) -> std::result::Result<(RequestId, R::Params), ExtractError<Request>>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

pub fn on<N>(not: lsp_server::Notification) -> std::result::Result<N::Params, ExtractError<lsp_server::Notification>>
where
    N: lsp_types::notification::Notification,
    N::Params: serde::de::DeserializeOwned,
{
    not.extract(N::METHOD)
}

use std::fs;

pub fn run_lsp_server() -> std::result::Result<(), Box<dyn Error + Sync + Send>> {
    // Note that we must have our logging only write out to stderr.
    eprintln!("starting generic LSP server");

    // This is a workaround for a deadlock issue in WASI libc.
    // See https://github.com/WebAssembly/wasi-libc/pull/491
    let _ = fs::metadata("/workspace");

    // Create the transport. Includes the stdio (stdin and stdout) versions.
    // Reads/writes are chunked to 64 KiB per call, so large JSON frames
    // (didOpen payloads, big publishDiagnostics) survive WASI runtimes with
    // per-call buffer limits; desktop behavior is unchanged.
    let (connection, io_threads) = lsp_stdio::stdio();

    // When the "stdio-monitor" feature is enabled, wrap the connection with
    // proxy threads that dump the full wire format (Content-Length + JSON body)
    // to stderr for debugging LSP protocol issues.
    #[cfg(not(feature = "stdio-monitor"))]
    let connection = connection;
    #[cfg(feature = "stdio-monitor")]
    let connection = create_monitored_connection(connection);

    // Run the server and wait for the two threads to end.
    let backend = Backend::new(Client { connection });
    let _initialization_params = match backend.init() {
        Ok(it) => it,
        Err(e) => {
            if e.channel_is_disconnected() {
                io_threads.join()?;
            }
            return Err(e.into());
        }
    };

    // 在 init 握手完成后加载 prelude，避免 diagnostics 发送在握手之前
    backend.load_prelude();
    // 然后启动工作线程处理用户文件
    backend.spawn_worker();

    let main_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        backend.main_loop()
    }));
    match main_result {
        Ok(result) => { result?; }
        Err(panic_err) => {
            let msg = if let Some(s) = panic_err.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_err.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown panic".to_string()
            };
            eprintln!("main loop panicked: {}", msg);
        }
    }
    io_threads.join()?;

    // Shut down gracefully.
    eprintln!("shutting down server");
    Ok(())
}

#[cfg(feature = "stdio-monitor")]
fn create_monitored_connection(connection: lsp_server::Connection) -> lsp_server::Connection {
    #[derive(serde::Serialize)]
    struct JsonRpcMsg {
        jsonrpc: &'static str,
        #[serde(flatten)]
        msg: lsp_server::Message,
    }
    let (monitored_tx, monitored_rx) = crossbeam_channel::bounded::<lsp_server::Message>(64);
    let orig_sender = connection.sender.clone();
    let seq = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0));
    let seq_clone = seq.clone();
    std::thread::spawn(move || {
        while let Ok(msg) = monitored_rx.recv() {
            let n = seq_clone.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let json = serde_json::to_string(&JsonRpcMsg { jsonrpc: "2.0", msg }).unwrap();
            let header = format!("Content-Length: {}\r\n\r\n", json.len());
            eprintln!("[STDOUT #{:04}] {}", n, header);
            for line in json.lines() {
                eprintln!("[STDOUT #{:04}] {}", n, line);
            }
            eprintln!("[STDOUT #{:04}] (end, {} bytes total)", n, header.len() + json.len());
            let reconstructed: lsp_server::Message = serde_json::from_str(&json).unwrap();
            if orig_sender.send(reconstructed).is_err() {
                eprintln!("[STDOUT] channel closed, stopping monitor");
                break;
            }
        }
    });
    let (stdin_tx, stdin_rx) = crossbeam_channel::bounded::<lsp_server::Message>(64);
    let orig_receiver = connection.receiver.clone();
    std::thread::spawn(move || {
        while let Ok(msg) = orig_receiver.recv() {
            let json = serde_json::to_string(&JsonRpcMsg { jsonrpc: "2.0", msg }).unwrap();
            let header = format!("Content-Length: {}\r\n\r\n", json.len());
            eprintln!("[STDIN ] {}", header);
            for line in json.lines() {
                eprintln!("[STDIN ] {}", line);
            }
            eprintln!("[STDIN ] (end, {} bytes total)", header.len() + json.len());
            let reconstructed: lsp_server::Message = serde_json::from_str(&json).unwrap();
            if stdin_tx.send(reconstructed).is_err() {
                eprintln!("[STDIN] channel closed, stopping monitor");
                break;
            }
        }
    });
    lsp_server::Connection {
        sender: monitored_tx,
        receiver: stdin_rx,
    }
}

#[cfg(test)]
mod namespace_l2_tests {
    use super::*;
    use crate::client::CliClient;

    #[test]
    fn import_completion_prefix_parses_forms() {
        assert_eq!(import_completion_prefix("import mylib."), Some(("mylib".into(), "".into())));
        assert_eq!(import_completion_prefix("import mylib.fo"), Some(("mylib".into(), "fo".into())));
        assert_eq!(import_completion_prefix("import mylib.Tree."), Some(("mylib.Tree".into(), "".into())));
        assert_eq!(import_completion_prefix("import mylib.{ "), Some(("mylib".into(), "".into())));
        assert_eq!(import_completion_prefix("import mylib.{ a, fo"), Some(("mylib".into(), "fo".into())));
        assert_eq!(import_completion_prefix("  import mylib.fo"), Some(("mylib".into(), "fo".into())));
        assert_eq!(import_completion_prefix("import"), None);
        assert_eq!(import_completion_prefix("import "), None);
        assert_eq!(import_completion_prefix("def f = 1"), None);
        assert_eq!(import_completion_prefix(""), None);
    }

    #[test]
    fn import_context_completion_offers_first_level_members() {
        let b = Arc::new(Backend::new(CliClient::new()));
        b.load_prelude_skip_hdl();
        b.process_file(
            &Url::parse("file:///a.typort").unwrap(),
            "package mylib\n\ndef foo(x: Nat): Nat = succ x\n\nstruct Tree {\n    h: Nat\n}\n",
            Some(1),
        );
        // Cursor right after `import mylib.` → offer all first-level members.
        let text = "import mylib.";
        let rope = Rope::from_str(text);
        let items = b.import_context_completions(&rope, text.len(), text);
        let labels: Vec<String> = items.iter().map(|i| i.label.clone()).collect();
        assert!(labels.iter().any(|l| l == "foo"), "应建议 foo，labels: {:?}", labels);
        assert!(labels.iter().any(|l| l == "Tree"), "应建议 Tree，labels: {:?}", labels);
        assert!(!labels.iter().any(|l| l.contains('.')), "不应建议带点成员，labels: {:?}", labels);

        // Typed prefix filters.
        let text = "import mylib.fo";
        let rope = Rope::from_str(text);
        let items = b.import_context_completions(&rope, text.len(), text);
        let labels: Vec<String> = items.iter().map(|i| i.label.clone()).collect();
        assert_eq!(labels, vec!["foo".to_string()], "typed 前缀应过滤出 foo");
    }

    #[test]
    fn cross_file_references_find_uses_in_other_files() {
        let b = Arc::new(Backend::new(CliClient::new()));
        b.load_prelude_skip_hdl();
        let a_uri = Url::parse("file:///a.typort").unwrap();
        let a_text = "package mylib\n\ndef foo(x: Nat): Nat = succ x\n";
        b.process_file(&a_uri, a_text, Some(1));
        b.process_file(
            &Url::parse("file:///b.typort").unwrap(),
            "import mylib._\n\ndef bar: Nat = foo zero\n",
            Some(1),
        );
        b.process_file(
            &Url::parse("file:///c.typort").unwrap(),
            "import mylib._\n\ndef baz: Nat = foo zero\n",
            Some(1),
        );

        // Cursor inside A's `foo` definition token.
        let def_off = a_text.find("foo").unwrap() + 1;
        let refs = b.cross_file_references(&a_uri, def_off).expect("references");
        let refs: Vec<String> = refs.iter()
            .map(|l| l.uri.to_string())
            .collect();
        assert!(refs.iter().any(|u| u.contains("a.typort")), "应含定义文件 A，refs: {:?}", refs);
        assert!(refs.iter().any(|u| u.contains("b.typort")), "应含引用文件 B，refs: {:?}", refs);
        assert!(refs.iter().any(|u| u.contains("c.typort")), "应含引用文件 C，refs: {:?}", refs);
    }

    #[test]
    fn rename_edits_def_and_all_uses_across_files() {
        let b = Arc::new(Backend::new(CliClient::new()));
        b.load_prelude_skip_hdl();
        let a_uri = Url::parse("file:///a.typort").unwrap();
        let a_text = "package mylib\n\ndef foo(x: Nat): Nat = succ x\n";
        b.process_file(&a_uri, a_text, Some(1));
        b.process_file(
            &Url::parse("file:///b.typort").unwrap(),
            "import mylib._\n\ndef bar: Nat = foo zero\n",
            Some(1),
        );
        let c_text = "import mylib._\n\ndef baz: Nat = mylib.foo zero\n";
        b.process_file(&Url::parse("file:///c.typort").unwrap(), c_text, Some(1));

        let def_off = a_text.find("foo").unwrap() + 1;
        let edit = b.rename_at(&a_uri, def_off, "barfoo").expect("rename edit");

        let changes = edit.changes.as_ref().expect("changes");
        assert!(changes.contains_key(&a_uri), "应含定义文件 A");
        let mut uris: Vec<&Url> = changes.keys().collect();
        uris.sort_by_key(|u| u.to_string());
        assert_eq!(uris.len(), 3, "应覆盖 A/B/C 三个文件，uris: {:?}", uris);

        // Every edit must insert the new name.
        for (u, edits) in changes.iter() {
            for e in edits {
                assert_eq!(e.new_text, "barfoo", "uri {} 的编辑应替换为 barfoo", u);
            }
        }

        // C's qualified use `mylib.foo` keeps the `mylib.` prefix.
        let c_uri = Url::parse("file:///c.typort").unwrap();
        let c_rope = Rope::from_str(c_text);
        let c_edit = &changes[&c_uri][0];
        let start = position_to_offset(c_edit.range.start, &c_rope).unwrap();
        assert_eq!(&c_rope.byte_slice(0..start).to_string(), "import mylib._\n\ndef baz: Nat = mylib.",
            "qualified use 应保留前缀，只替换最后一段");
    }
}
