#![feature(pattern)]

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

mod parser_lib;
mod parser_lib_resilient;
mod list;
mod bimap;
pub mod ls;
pub mod client;
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

pub mod sampler;

use std::collections::{HashMap, HashSet};
use std::error::Error;

use client::{Client, ClientLike};
use dashmap::DashMap;
use log::debug;
use ls::LanguageServer;
use lsp_server::{Connection, ExtractError, Message, ProtocolError, Request, RequestId, Response};
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
    /// Macro expansion data collected during parsing (keyed by URI)
    pub macro_expansion_map: DashMap<String, Vec<MacroExpansionInfo>>,
    // 状态标记和条件变量
    processing_uris: DashMap<String, bool>, // URI -> 是否正在处理
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
            macro_expansion_map: DashMap::new(),
            processing_uris: DashMap::new(),
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
        use lsp_types::Url;
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///op.typort").unwrap(),
            text: include_str!("prelude/op.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///eq.typort").unwrap(),
            text: include_str!("prelude/eq.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///nat.typort").unwrap(),
            text: include_str!("prelude/nat.typort"),
            version: None,
        });
        // Register nat_to_dec builtin (required by hdl.typort for Verilog generation)
        {
            let infer = self.infer.lock().unwrap();
            let mut cxt = self.cxt.lock().unwrap();
            L13_namespace::cxt::Cxt::register_nat_to_dec(&mut cxt, &infer);
        }
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///natarith.typort").unwrap(),
            text: include_str!("prelude/natarith.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///bool.typort").unwrap(),
            text: include_str!("prelude/bool.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///option.typort").unwrap(),
            text: include_str!("prelude/option.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///result.typort").unwrap(),
            text: include_str!("prelude/result.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///order.typort").unwrap(),
            text: include_str!("prelude/order.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///void.typort").unwrap(),
            text: include_str!("prelude/void.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///decidable.typort").unwrap(),
            text: include_str!("prelude/decidable.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///vec.typort").unwrap(),
            text: include_str!("prelude/vec.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///either.typort").unwrap(),
            text: include_str!("prelude/either.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///list.typort").unwrap(),
            text: include_str!("prelude/list.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///string.typort").unwrap(),
            text: include_str!("prelude/string.typort"),
            version: None,
        });
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///nonempty.typort").unwrap(),
            text: include_str!("prelude/nonempty.typort"),
            version: None,
        });
        if !skip_hdl {
            self.on_change::<true>(TextDocumentItem {
                uri: Url::parse("builtin:///hdl.typort").unwrap(),
                text: include_str!("prelude/hdl.typort"),
                version: None,
            });
        }
        self.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///show.typort").unwrap(),
            text: include_str!("prelude/show.typort"),
            version: None,
        });
        // Auto-import prelude: create short aliases for enum cases (e.g., Nat.zero → zero)
        {
            let cxt_lock = self.cxt.lock().unwrap();
            let aliases: Vec<(SmolStr, _)> = cxt_lock.decl.iter()
                .filter(|(k, _)| k.contains('.'))
                .map(|(k, v)| {
                    let short = SmolStr::new(k.split('.').last().unwrap());
                    (short, v.clone())
                })
                .collect();
            drop(cxt_lock);
            let mut cxt_lock = self.cxt.lock().unwrap();
            let decl_map = Arc::make_mut(&mut cxt_lock.decl);
            for (short, v) in aliases {
                decl_map.entry(short).or_insert(v);
            }
        }
        self.infer.lock().unwrap().hover_table.clear();
        self.infer.lock().unwrap().hover_table.shrink_to_fit();
        self.infer.lock().unwrap().completion_table.clear();
        self.infer.lock().unwrap().completion_table.shrink_to_fit();
        self.infer.lock().unwrap().mutable_map.write().unwrap().clear();
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
                {
                    let (lock, _) = &*self.processed_signal;
                    let mut processed = lock.lock().unwrap();
                    processed.remove(&uri_str);
                    drop(processed);
                }
                self.processing_uris.insert(uri_str.clone(), true);

                // 此时锁已释放，主线程可以放入新任务，我们在处理当前最新的任务
                self.client.log_message(MessageType::LOG, format!("Worker starting job for version {:?}", job.version));
                self.on_change::<false>(TextDocumentItem {
                    uri: job.uri,
                    text: &job.text,
                    version: job.version,
                });

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
            self.client.log_message(MessageType::LOG, format!("parser {:?}", start.elapsed().as_secs_f32()));
            let parser_dur = start.elapsed().as_secs_f64();
            // Merge newly exported macros into the global table
            for (name, rules) in new_exports {
                self.exported_macros.insert(name, rules);
            }
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
            let mut terms = vec![];
            let start = std::time::Instant::now();
            for tm in decls {
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
            }
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
                self.hover_table.insert(params.uri.to_string(), infer.clone());
            }
            infer.hover_table.clear();
            infer.hover_table.shrink_to_fit();
            infer.completion_table.clear();
            infer.completion_table.shrink_to_fit();
            infer.shrink();
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

            // 发布诊断
            self.client.publish_diagnostics(params.uri.clone(), diags, params.version);
            // 存储 Quick Fix 映射（覆盖旧的）
            self.quickfix_map.insert(params.uri.to_string(), quickfixes_for_uri);
        } else {
            // Parser returned None — file has syntax errors.
            // Clear any stale analysis results for this URI so the editor
            // doesn't show outdated hovers / type info from the last good parse.
            self.type_map.remove(params.uri.as_str());
            self.hover_table.remove(params.uri.as_str());
            self.quickfix_map.remove(params.uri.as_str());
            self.macro_expansion_map.remove(params.uri.as_str());
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
        self.client.log_message(MessageType::LOG, format!("change {:?}", start_all.elapsed().as_secs_f32()));
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
                            rope.remove(start..end);
                            rope.insert(start, &change.text);
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
        self.document_buffers.lock().unwrap().remove(params.text_document.uri.as_str());
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
                        .and_then(|x| x.hover_table.iter()
                            .filter(|x| x.0.path_id == *id)
                            .find(|x| x.0.contains(offset))
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

    fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let definition = || -> Option<GotoDefinitionResponse> {
            let uri = params.text_document_position_params.text_document.uri;
            let uri = normalize_builtin_uri(&uri);
            let semantic = self.hover_table.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let position = params.text_document_position_params.position;
            let offset = position_to_offset(position, &rope)?;

            let interval = semantic.hover_table
                .iter()
                .find(|x| x.0.contains(offset))
                .and_then(|x| {
                    let def_span = &x.1;
                    // Look up the source file URI for the definition span's path_id
                    let def_uri = self.document_id.iter()
                        .find(|e| *e.value() == def_span.path_id)
                        .map(|e| Url::parse(e.key()).ok())
                        .flatten()
                        .unwrap_or_else(|| uri.clone());
                    let def_rope = if def_uri == uri {
                        rope.clone()
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
            interval
        }();
        Ok(definition)
    }

    fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let reference_list = || -> Option<Vec<Location>> {
            let uri = params.text_document_position.text_document.uri;
            let uri = normalize_builtin_uri(&uri);
            let semantic = self.hover_table.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let position = params.text_document_position.position;
            let offset = position_to_offset(position, &rope)?;

            let ret: Vec<Location> = semantic.hover_table
                .iter()
                .filter(|x| x.1.contains(offset))
                .map(|x| x.0)
                .flat_map(|x| {
                    let ref_uri = self.document_id.iter()
                        .find(|e| *e.value() == x.path_id)
                        .map(|e| Url::parse(e.key()).ok())
                        .flatten()
                        .unwrap_or_else(|| uri.clone());
                    let ref_rope = if ref_uri == uri {
                        rope.clone()
                    } else {
                        self.document_map.get(ref_uri.as_str())?.clone()
                    };
                    Some(Location::new(
                        ref_uri,
                        Range::new(
                            offset_to_position(x.start_offset as usize, &ref_rope)?,
                            offset_to_position(x.end_offset as usize, &ref_rope)?,
                        )
                    ))
                })
                .collect();
            Some(ret)
        }();
        Ok(reference_list)
    }

    fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let uri = normalize_builtin_uri(&uri);

        self.client.log_message(MessageType::LOG, "on completion".to_string());
        let position = params.text_document_position.position;
        let completions = || -> Option<Vec<CompletionItem>> {
            let rope = self.document_map.get(&uri.to_string())?;
            let infer = self.hover_table.get(&uri.to_string())?;
            let char = rope.try_line_to_char(position.line as usize).ok()?;
            let offset = char + position.character as usize;
            let completions = infer.completion_table
                .iter()
                .filter(|x| x.0.contains(offset.saturating_sub(2)))
                .map(|x| CompletionItem {
                    label: x.1.to_string(),
                    insert_text: Some(x.1.to_string()),
                    kind: Some(CompletionItemKind::VARIABLE),
                    detail: Some(x.1.to_string()),
                    ..Default::default()
                })
                .collect();
            Some(completions)
        }();
        Ok(completions.map(CompletionResponse::Array))
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
                    eprintln!("searching...");
                    code_actions.iter().flat_map(|x| {
                        let ret = x();
                        eprintln!("{:?}", ret);
                        ret
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
                                let uri = params.uri;
                                let result = self.macro_expansion_map.get(&uri).and_then(|expansions| {
                                    let rope = self.document_map.get(&uri)?;
                                    let offset = position_to_offset(params.position, &rope)?;
                                    expansions.iter().find(|e| {
                                        offset >= e.start_offset as usize && offset < e.end_offset as usize
                                    }).map(|e| {
                                        let start = offset_to_position(e.start_offset as usize, &rope)?;
                                        let end = offset_to_position(e.end_offset as usize, &rope)?;
                                        Some(ExpandMacroResult {
                                            name: e.name.clone(),
                                            range: lsp_types::Range::new(start, end),
                                            expanded_text: e.expanded_text.clone(),
                                        })
                                    }).flatten()
                                });
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
    let (connection, io_threads) = Connection::stdio();

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
