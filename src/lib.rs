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

use std::collections::HashMap;
use std::error::Error;

use client::{Client, ClientLike};
use dashmap::DashMap;
use log::debug;
use ls::LanguageServer;
use lsp_server::{Connection, ExtractError, Message, ProtocolError, Request, RequestId, Response};
use lsp_types::request::{CodeActionRequest, Completion, ExecuteCommand, GotoDefinition, HoverRequest, InlayHintRequest, References, Rename, SemanticTokensFullRequest, SemanticTokensRangeRequest};
use ropey::Rope;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use lsp_types::notification::{DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, DidSaveTextDocument, Notification};
use lsp_types::*;
use crate::ls::Result;

use L12_canonical::pretty::pretty_tm;
use L12_canonical::parser::parser;
use L12_canonical::parser::syntax::Decl;
use L12_canonical::{DeclTm, Infer, preprocess};
use L12_canonical::cxt::Cxt;

use std::sync::{Arc, Mutex, Condvar};
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
    pub hover_table: DashMap<String, Infer>,
    pub quickfix_map: DashMap<String, HashMap<String, Vec<Box<dyn Fn() -> Option<String> + Send + Sync>>>>,
    // 状态标记和条件变量
    processing_uris: DashMap<String, bool>, // URI -> 是否正在处理
    // 信号机制：(任务槽, 条件变量)
    worker_signal: Arc<(Mutex<Option<AnalysisJob>>, Condvar)>,
    // 处理完成的信号
    processed_signal: Arc<(Mutex<HashMap<String, bool>>, Condvar)>,

    infer: Arc<Mutex<Infer>>,
    cxt: Arc<Mutex<Cxt>>,
}

impl<C: ClientLike + Send + Sync + 'static> Backend<C> {
    pub fn new(client: C) -> Arc<Self> {
        let ast_map = Default::default();
        let type_map = Default::default();
        let document_map = Default::default();
        let document_id = Default::default();
        let hover_table = Default::default();

        let worker_signal = Arc::new((Mutex::new(None), Condvar::new()));
        let signal_clone = worker_signal.clone();

        let processed_signal = Arc::new((Mutex::new(HashMap::new()), Condvar::new()));
        let infer = Infer::new();
        let cxt = Cxt::new();

        let ret = Arc::new(Backend {
            client,
            ast_map,
            type_map,
            document_map,
            document_id,
            hover_table,
            quickfix_map: DashMap::new(),
            processing_uris: DashMap::new(),
            worker_signal,
            processed_signal,
            infer: Arc::new(Mutex::new(infer)),
            cxt: Arc::new(Mutex::new(cxt)),
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///op.typort").unwrap(),
            text: include_str!("prelude/op.typort"),
            version: None,
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///eq.typort").unwrap(),
            text: include_str!("prelude/eq.typort"),
            version: None,
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///nat.typort").unwrap(),
            text: include_str!("prelude/nat.typort"),
            version: None,
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///bool.typort").unwrap(),
            text: include_str!("prelude/bool.typort"),
            version: None,
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///option.typort").unwrap(),
            text: include_str!("prelude/option.typort"),
            version: None,
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///vec.typort").unwrap(),
            text: include_str!("prelude/vec.typort"),
            version: None,
        });
        ret.on_change::<true>(TextDocumentItem {
            uri: Url::parse("builtin:///hdl.typort").unwrap(),
            text: include_str!("prelude/hdl.typort"),
            version: None,
        });
        ret.infer.lock().unwrap().hover_table.clear();
        ret.infer.lock().unwrap().completion_table.clear();
        ret.infer.lock().unwrap().mutable_map.write().unwrap().clear();
        let for_thread = ret.clone();
        thread::spawn(move || {
            for_thread.worker_loop(signal_clone);
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

    fn worker_loop(
        &self,
        signal: Arc<(Mutex<Option<AnalysisJob>>, Condvar)>,
    ) {
        loop {
            // 1. 等待任务
            let job = {
                let (lock, cvar) = &*signal;
                let mut pending = lock.lock().unwrap();
                while pending.is_none() {
                    pending = cvar.wait(pending).unwrap();
                }
                pending.take().unwrap() // 取出任务，并将槽置空
            };

            let uri_str = job.uri.to_string();
            {
                let (lock, _) = &*self.processed_signal;
                let mut processed = lock.lock().unwrap();
                processed.remove(&uri_str);
                drop(processed);
            }
            self.processing_uris.insert(uri_str.clone(), true);

            // 此时锁已释放，主线程可以放入新任务，我们在处理当前最新的任务
            eprintln!("Worker starting job for version {:?}", job.version);
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

    pub fn on_change<const MUT:bool>(&self, params: TextDocumentItem<'_>) {
        let start_all = std::time::Instant::now();
        //dbg!(&params.version);
        let rope = ropey::Rope::from_str(params.text);
        self.document_map
            .insert(params.uri.to_string(), rope.clone());
        let now_id = self.document_id.get(params.uri.as_str())
            .map(|x| *x)
            .unwrap_or(self.document_id.len() as u32);
        self.document_id.insert(params.uri.to_string(), now_id);
        let start = std::time::Instant::now();
        if let Some(ast) = parser(&preprocess(params.text), now_id) {
            eprintln!("parser {:?}", start.elapsed().as_secs_f32());
            let mut err_collect = vec![];
            self.ast_map.insert(params.uri.to_string(), ast.0.clone());
            let mut i = self.infer.lock().unwrap();
            let mut ic = i.clone();
            let mut c = self.cxt.lock().unwrap();
            let mut cc = c.clone();
            let infer: &mut Infer;
            let cxt: &mut Cxt;
            if MUT {
                infer = &mut i;
                cxt = &mut c;
            } else {
                infer = &mut ic;
                cxt = &mut cc;
            };
            let mut terms = vec![];
            let start = std::time::Instant::now();
            for tm in ast.0 {
                match infer.infer(cxt, tm.clone()) {
                    Ok((x, _, new_cxt)) => {
                        if let DeclTm::Println(_, ref s, span) = x {
                            err_collect.push((
                                crate::L12_canonical::Error(span.map(|_| s.clone()), vec![]),
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
            eprintln!("infer {:?}", start.elapsed().as_secs_f32());
            self.type_map.insert(params.uri.to_string(), terms);
            self.hover_table.insert(params.uri.to_string(), infer.clone());
            let mut diags = Vec::new();
            let mut quickfixes_for_uri = HashMap::new();

            // 生成诊断（原有的 err_collect + parse errors）
            for (e, severity) in err_collect.into_iter().chain(ast.1.into_iter().map(|e| (e.to_err(), DiagnosticSeverity::ERROR))) {
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
            self.client
                .publish_diagnostics(params.uri.clone(), vec![Diagnostic::new_simple(
                    Range::new(
                        Position { line: 0, character: 0 },
                        Position { line: 0, character: 1 },
                    ), "parse error".to_owned())], params.version);
        }
        eprintln!("change {:?}", start_all.elapsed().as_secs_f32());
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
                        change: Some(TextDocumentSyncKind::FULL),
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
        let job = AnalysisJob {
            uri: params.text_document.uri.clone(),
            text: params.text_document.text.to_string(),
            version: Some(params.text_document.version),
        };

        let (lock, cvar) = &*self.worker_signal;
        let mut pending = lock.lock().unwrap();
        *pending = Some(job);
        cvar.notify_one();
    }

    fn did_change(&self, params: DidChangeTextDocumentParams) {
        let job = AnalysisJob {
            uri: params.text_document.uri.clone(),
            text: params.content_changes[0].text.to_string(),
            version: Some(params.text_document.version),
        };

        let (lock, cvar) = &*self.worker_signal;
        let mut pending = lock.lock().unwrap();
        *pending = Some(job);
        cvar.notify_one();
    }

    fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            let job = AnalysisJob {
                uri: params.text_document.uri.clone(),
                text,
                version: None,
            };

            let (lock, cvar) = &*self.worker_signal;
            let mut pending = lock.lock().unwrap();
            *pending = Some(job);
            cvar.notify_one();
        }
        debug!("file saved!");
    }
    fn did_close(&self, _: DidCloseTextDocumentParams) {
        debug!("file closed!");
    }

    fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let hover = || -> Option<Hover> {
            let uri = params.text_document_position_params.text_document.uri;
            let semantic = self.type_map.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
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
                            .find(|x| x.0.contains(offset))
                            .map(|(span, _, cxt, val)| (*span, pretty_tm(0, cxt.names(), &x.quote(&cxt.decl, cxt.lvl, val))))
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
            let semantic = self.hover_table.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let position = params.text_document_position_params.position;
            let offset = position_to_offset(position, &rope)?;

            let interval = semantic.hover_table
                .iter()
                .find(|x| x.0.contains(offset))
                .and_then(|x| {
                    let start_position = offset_to_position(x.1.start_offset as usize, &rope)?;
                    let end_position = offset_to_position(x.1.end_offset as usize, &rope)?;
                    Some(GotoDefinitionResponse::Scalar(
                        Location::new(
                            uri.clone(),
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
            let semantic = self.hover_table.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let position = params.text_document_position.position;
            let offset = position_to_offset(position, &rope)?;

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
            Some(ret)
        }();
        Ok(reference_list)
    }

    fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let uri_str = uri.to_string();

        // 5. 等待当前URI处理完成（带超时）
        let (lock, cvar) = &*self.processed_signal;
        let mut processed = lock.lock().unwrap();

        // 等待直到该URI已处理完成（或超时）
        let start = std::time::Instant::now();
        while self.processing_uris.contains_key(&uri_str) && start.elapsed() < Duration::from_millis(3500) {
            // 检查是否已处理完成
            if processed.get(&uri_str).is_some() {
                break;
            }
            processed = cvar.wait_timeout(processed, Duration::from_millis(100)).unwrap().0;
        }

        // 清理已处理的标记
        processed.remove(&uri_str);
        drop(processed);

        eprintln!("on completion");
        let position = params.text_document_position.position;
        let completions = || -> Option<Vec<CompletionItem>> {
            let rope = self.document_map.get(&uri.to_string())?;
            let infer = self.hover_table.get(&uri.to_string())?;
            let char = rope.try_line_to_char(position.line as usize).ok()?;
            let offset = char + position.character as usize;
            let completions = infer.completion_table
                .iter()
                .filter(|x| x.0.contains(offset - 2))
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
        let uri = params.text_document.uri.to_string();
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
        eprintln!("starting example main loop");
        for msg in self.client.connection.receiver.clone() {
            match msg {
                Message::Request(req) => {
                    if self.client.connection.handle_shutdown(&req)? {
                        return Ok(());
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
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
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
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    match cast::<SemanticTokensRangeRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = self.semantic_tokens_range(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
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
        Ok(())
    }
}

#[allow(unused)]
enum CustomNotification {}
impl Notification for CustomNotification {
    type Params = InlayHintParams;
    const METHOD: &'static str = "custom/notification";
}

pub struct TextDocumentItem<'a> {
    pub uri: Url,
    pub text: &'a str,
    pub version: Option<i32>,
}

pub fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
    let line = rope.try_char_to_line(offset).ok()?;
    let first_char_of_line = rope.try_line_to_char(line).ok()?;
    let column = offset - first_char_of_line;
    Some(Position::new(line as u32, column as u32))
}

pub fn position_to_offset(position: Position, rope: &Rope) -> Option<usize> {
    let line_char_offset = rope.try_line_to_char(position.line as usize).ok()?;
    let slice = rope.slice(0..line_char_offset + position.character as usize);
    Some(slice.len_bytes())
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
