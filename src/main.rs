#![feature(pattern)]

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


use std::collections::HashMap;
use std::error::Error;
use std::fs;

use client::Client;
use dashmap::DashMap;
use log::debug;
use ls::LanguageServer;
use lsp_server::{Connection, ExtractError, Message, ProtocolError, Request, RequestId, Response};
use lsp_types::request::{Completion, GotoDefinition, HoverRequest, InlayHintRequest, References, Rename, SemanticTokensFullRequest, SemanticTokensRangeRequest};
//use crate::completion::completion;
use ropey::Rope;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use lsp_types::notification::{DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, DidSaveTextDocument, Notification};
use lsp_types::*;
use crate::L11_macro::pretty::pretty_tm;
use crate::ls::Result;

use L11_macro::parser::parser;
use L11_macro::parser::syntax::Decl;
use L11_macro::{DeclTm, Infer};
use L11_macro::cxt::Cxt;

use std::sync::{Arc, Mutex, RwLock, Condvar};
use std::thread;
use crossbeam_channel::Sender; // lsp_server 内部使用的是 crossbeam 或类似的 channel

// 2. 定义传递给工作线程的任务包
struct AnalysisJob {
    uri: Url,
    text: String,
    version: Option<i32>,
}

// 3. 修改 Backend 结构
struct Backend {
    client: Client,
    ast_map: DashMap<String, Vec<Decl>>,
    type_map: DashMap<String, Vec<DeclTm>>,
    document_map: DashMap<String, Rope>,
    document_id: DashMap<String, u32>,
    hover_table: DashMap<String, Infer>,
    // 状态标记和条件变量
    processing_uris: DashMap<String, bool>, // URI -> 是否正在处理
    // 信号机制：(任务槽, 条件变量)
    worker_signal: Arc<(Mutex<Option<AnalysisJob>>, Condvar)>,
    // 处理完成的信号
    processed_signal: Arc<(Mutex<HashMap<String, bool>>, Condvar)>,
}

impl Backend {
    pub fn new(client: Client) -> Arc<Self> {
        let ast_map = Default::default();
        let type_map = Default::default();
        let document_map = Default::default();
        let document_id = Default::default();
        let hover_table = Default::default();
        
        let worker_signal = Arc::new((Mutex::new(None), Condvar::new()));
        
        // 4. 启动后台工作线程
        let signal_clone = worker_signal.clone();
        let sender_clone = client.connection.sender.clone(); // 假设 Connection sender 是可 Clone 的

        let processed_signal = Arc::new((Mutex::new(HashMap::new()), Condvar::new()));

        /*thread::spawn(move || {
            worker_loop(state_clone, signal_clone, sender_clone);
        });*/

        let ret = Arc::new(Backend {
            client,
            ast_map,
            type_map,
            document_map,
            document_id,
            hover_table,
            processing_uris: DashMap::new(),
            worker_signal,
            processed_signal,
        });
        let for_thread = ret.clone();
        thread::spawn(move || {
            for_thread.worker_loop(signal_clone);
        });
        ret
    }
    pub fn init(&self) -> std::result::Result<serde_json::Value, ProtocolError> {
        let server_capabilities = serde_json::to_value(
            self.initialize(Default::default()).unwrap().capabilities
        ).unwrap();
        self.client.connection.initialize(server_capabilities)
    }
    pub fn main_loop(&self) -> std::result::Result<(), Box<dyn Error + Sync + Send>> {
        eprintln!("starting example main loop");
        for msg in self.client.connection.receiver.clone() {
            //eprintln!("got msg: {msg:?}");
            match msg {
                Message::Request(req) => {
                    if self.client.connection.handle_shutdown(&req)? {
                        return Ok(());
                    }
                    //eprintln!("got request: {req:?}");
                    match cast::<GotoDefinition>(req.clone()) {
                        Ok((id, params)) => {
                            //eprintln!("got gotoDefinition request #{id}: {params:?}");
                            let result = self.goto_definition(params)?;
                            //eprintln!("return {result:?}");
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
                            //eprintln!("got inlay hint request #{id}: {params:?}");
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
                            //eprintln!("got completion request #{id}: {params:?}");
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
                            //eprintln!("got references request #{id}: {params:?}");
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
                            //eprintln!("got semanticTokensFull request #{id}: {params:?}");
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
                            //eprintln!("got semanticTokensRange request #{id}: {params:?}");
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
                            //eprintln!("got rename request #{id}: {params:?}");
                            let result = self.rename(params)?;
                            let result = serde_json::to_value(&result).unwrap();
                            let resp = Response { id, result: Some(result), error: None };
                            self.client.connection.sender.send(Message::Response(resp))?;
                            continue;
                        }
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(req)) => req,
                    };
                    // ...
                }
                Message::Response(resp) => {
                    //eprintln!("got response: {resp:?}");
                }
                Message::Notification(not) => {
                    //eprintln!("got notification: {not:?}");
                    match on::<DidOpenTextDocument>(not.clone()) {
                        Ok(params) => {
                            //eprintln!("got didOpenTextDocument notification: {params:?}");
                            self.did_open(params);
                        },
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(not)) => (),
                    }
                    match on::<DidChangeTextDocument>(not.clone()) {
                        Ok(params) => {
                            //eprintln!("got didChangeTextDocument notification: {params:?}");
                            self.did_change(params);
                        },
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(not)) =>(),
                    }
                    match on::<DidCloseTextDocument>(not.clone()) {
                        Ok(params) => {
                            //eprintln!("got didCloseTextDocument notification: {params:?}");
                            self.did_close(params);
                        },
                        Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                        Err(ExtractError::MethodMismatch(not)) => (),
                    }
                    match on::<DidSaveTextDocument>(not) {
                        Ok(params) => {
                            //eprintln!("got didSaveTextDocument notification: {params:?}");
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

impl LanguageServer for Backend {
    fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            server_info: None,
            offset_encoding: None,
            capabilities: ServerCapabilities {
                //inlay_hint_provider: Some(OneOf::Left(true)),
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
                /*execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec!["dummy.do_something".to_string()],
                    work_done_progress_options: Default::default(),
                }),*/

                workspace: Some(WorkspaceServerCapabilities {
                    workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                        supported: Some(true),
                        change_notifications: Some(OneOf::Left(true)),
                    }),
                    file_operations: None,
                }),
                /*semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensRegistrationOptions(
                        SemanticTokensRegistrationOptions {
                            text_document_registration_options: {
                                TextDocumentRegistrationOptions {
                                    document_selector: Some(vec![DocumentFilter {
                                        language: Some("nrs".to_string()),
                                        scheme: Some("file".to_string()),
                                        pattern: None,
                                    }]),
                                }
                            },
                            semantic_tokens_options: SemanticTokensOptions {
                                work_done_progress_options: WorkDoneProgressOptions::default(),
                                legend: SemanticTokensLegend {
                                    token_types: LEGEND_TYPE.into(),
                                    token_modifiers: vec![],
                                },
                                range: Some(true),
                                full: Some(SemanticTokensFullOptions::Bool(true)),
                            },
                            static_registration_options: StaticRegistrationOptions::default(),
                        },
                    ),
                ),*/
                // definition: Some(GotoCapability::default()),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                //rename_provider: Some(OneOf::Left(true)),
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
        //debug!("file opened");
        /*self.on_change(TextDocumentItem {
            uri: params.text_document.uri,
            text: &params.text_document.text,
            version: Some(params.text_document.version),
        })*/
        let job = AnalysisJob {
            uri: params.text_document.uri.clone(),
            text: params.text_document.text.to_string(),
            version: Some(params.text_document.version),
        };

        // 3. 更新任务槽并通知
        let (lock, cvar) = &*self.worker_signal;
        let mut pending = lock.lock().unwrap();
        *pending = Some(job); // 覆盖之前的任务（如果 worker 还没来得及拿，旧的就丢弃了）
        cvar.notify_one();
    }

    fn did_change(&self, params: DidChangeTextDocumentParams) {
        /*self.on_change(TextDocumentItem {
            text: &params.content_changes[0].text,
            uri: params.text_document.uri,
            version: Some(params.text_document.version),
        })*/
        let job = AnalysisJob {
            uri: params.text_document.uri.clone(),
            text: params.content_changes[0].text.to_string(),
            version: Some(params.text_document.version),
        };

        // 3. 更新任务槽并通知
        let (lock, cvar) = &*self.worker_signal;
        let mut pending = lock.lock().unwrap();
        *pending = Some(job); // 覆盖之前的任务（如果 worker 还没来得及拿，旧的就丢弃了）
        cvar.notify_one();
    }

    fn did_save(&self, params: DidSaveTextDocumentParams) {
        //dbg!(&params.text);
        if let Some(text) = params.text {
            /*let item = TextDocumentItem {
                uri: params.text_document.uri,
                text: &text,
                version: None,
            };
            self.on_change(item);*/
            let job = AnalysisJob {
                uri: params.text_document.uri.clone(),
                text,
                version: None,
            };

            // 3. 更新任务槽并通知
            let (lock, cvar) = &*self.worker_signal;
            let mut pending = lock.lock().unwrap();
            *pending = Some(job); // 覆盖之前的任务（如果 worker 还没来得及拿，旧的就丢弃了）
            cvar.notify_one();
            //TODO:_ = self.client.semantic_tokens_refresh();
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
                            .map(|(span, _, cxt, val)| (*span, pretty_tm(0, cxt.names(), &x.quote(&cxt.decl, cxt.lvl, &val))))
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

    /*fn semantic_tokens_full(
        &mut self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri.to_string();
        debug!("semantic_token_full");
        let semantic_tokens = || -> Option<Vec<SemanticToken>> {
            let mut im_complete_tokens = self.semantic_token_map.get_mut(&uri)?;
            let rope = self.document_map.get(&uri)?;
            im_complete_tokens.sort_by(|a, b| a.start.cmp(&b.start));
            let mut pre_line = 0;
            let mut pre_start = 0;
            let semantic_tokens = im_complete_tokens
                .iter()
                .filter_map(|token| {
                    let line = rope.try_byte_to_line(token.start).ok()? as u32;
                    let first = rope.try_line_to_char(line as usize).ok()? as u32;
                    let start = rope.try_byte_to_char(token.start).ok()? as u32 - first;
                    let delta_line = line - pre_line;
                    let delta_start = if delta_line == 0 {
                        start - pre_start
                    } else {
                        start
                    };
                    let ret = Some(SemanticToken {
                        delta_line,
                        delta_start,
                        length: token.length as u32,
                        token_type: token.token_type as u32,
                        token_modifiers_bitset: 0,
                    });
                    pre_line = line;
                    pre_start = start;
                    ret
                })
                .collect::<Vec<_>>();
            Some(semantic_tokens)
        }();
        if let Some(semantic_token) = semantic_tokens {
            return Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
                result_id: None,
                data: semantic_token,
            })));
        }
        Ok(None)
    }*/

    /*fn semantic_tokens_range(
        &self,
        params: SemanticTokensRangeParams,
    ) -> Result<Option<SemanticTokensRangeResult>> {
        let uri = params.text_document.uri.to_string();
        let semantic_tokens = || -> Option<Vec<SemanticToken>> {
            let im_complete_tokens = self.semantic_token_map.get(&uri)?;
            let rope = self.document_map.get(&uri)?;
            let mut pre_line = 0;
            let mut pre_start = 0;
            let semantic_tokens = im_complete_tokens
                .iter()
                .filter_map(|token| {
                    let line = rope.try_byte_to_line(token.start).ok()? as u32;
                    let first = rope.try_line_to_char(line as usize).ok()? as u32;
                    let start = rope.try_byte_to_char(token.start).ok()? as u32 - first;
                    let ret = Some(SemanticToken {
                        delta_line: line - pre_line,
                        delta_start: if start >= pre_start {
                            start - pre_start
                        } else {
                            start
                        },
                        length: token.length as u32,
                        token_type: token.token_type as u32,
                        token_modifiers_bitset: 0,
                    });
                    pre_line = line;
                    pre_start = start;
                    ret
                })
                .collect::<Vec<_>>();
            Some(semantic_tokens)
        }();
        Ok(semantic_tokens.map(|data| {
            SemanticTokensRangeResult::Tokens(SemanticTokens {
                result_id: None,
                data,
            })
        }))
    }*/

    /*fn inlay_hint(
        &self,
        params: lsp_types::InlayHintParams,
    ) -> Result<Option<Vec<InlayHint>>> {
        debug!("inlay hint");
        let uri = &params.text_document.uri;
        let mut hashmap = HashMap::new();
        if let Some(ast) = self.ast_map.get(uri.as_str()) {
            ast.iter().for_each(|(func, _)| {
                type_inference(&func.body, &mut hashmap);
            });
        }

        let document = match self.document_map.get(uri.as_str()) {
            Some(rope) => rope,
            None => return Ok(None),
        };
        let inlay_hint_list = hashmap
            .into_iter()
            .map(|(k, v)| {
                (
                    k.start,
                    k.end,
                    match v {
                        crate::nrs_lang::Value::Null => ": null".to_string(),
                        crate::nrs_lang::Value::Bool(_) => ": bool".to_string(),
                        crate::nrs_lang::Value::Num(_) => ": number".to_string(),
                        crate::nrs_lang::Value::Str(_) => ": string".to_string(),
                    },
                )
            })
            .filter_map(|item| {
                // let start_position = offset_to_position(item.0, document)?;
                let end_position = offset_to_position(item.1, &document)?;
                let inlay_hint = InlayHint {
                    text_edits: None,
                    tooltip: None,
                    kind: Some(InlayHintKind::TYPE),
                    padding_left: None,
                    padding_right: None,
                    data: None,
                    position: end_position,
                    label: InlayHintLabel::LabelParts(vec![InlayHintLabelPart {
                        value: item.2,
                        tooltip: None,
                        location: Some(Location {
                            uri: params.text_document.uri.clone(),
                            range: Range {
                                start: Position::new(0, 4),
                                end: Position::new(0, 10),
                            },
                        }),
                        command: None,
                    }]),
                };
                Some(inlay_hint)
            })
            .collect::<Vec<_>>();

        Ok(Some(inlay_hint_list))
    }*/

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
            //eprintln!("{}: {:?}", offset, infer.completion_table);
            let completions = infer.completion_table
                .iter()
                .filter(|x| x.0.contains(offset - 2))
                //.inspect(|x| eprintln!("{}", x.1))
                .map(|x| CompletionItem {
                    label: x.1.clone(),
                    insert_text: Some(x.1.clone()),
                    kind: Some(CompletionItemKind::VARIABLE),
                    detail: Some(x.1.clone()),
                    ..Default::default()
                })
                .collect();
            /*let mut ret = Vec::with_capacity(completions.len());
            for (_, item) in completions {
                match item {
                    crate::completion::ImCompleteCompletionItem::Variable(var) => {
                        ret.push(CompletionItem {
                            label: var.clone(),
                            insert_text: Some(var.clone()),
                            kind: Some(CompletionItemKind::VARIABLE),
                            detail: Some(var),
                            ..Default::default()
                        });
                    }
                    crate::completion::ImCompleteCompletionItem::Function(
                        name,
                        args,
                    ) => {
                        ret.push(CompletionItem {
                            label: name.clone(),
                            kind: Some(CompletionItemKind::FUNCTION),
                            detail: Some(name.clone()),
                            insert_text: Some(format!(
                                "{}({})",
                                name,
                                args.iter()
                                    .enumerate()
                                    .map(|(index, item)| { format!("${{{}:{}}}", index + 1, item) })
                                    .collect::<Vec<_>>()
                                    .join(",")
                            )),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            ..Default::default()
                        });
                    }
                }
            }*/
            Some(completions)
        }();
        Ok(completions.map(CompletionResponse::Array))
    }

    /*fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let workspace_edit = || -> Option<WorkspaceEdit> {
            let uri = params.text_document_position.text_document.uri;
            let semantic = self.semantic_map.get(uri.as_str())?;
            let rope = self.document_map.get(uri.as_str())?;
            let position = params.text_document_position.position;
            let offset = position_to_offset(position, &rope)?;
            let reference_list = get_references(&semantic, offset, offset + 1, true)?;

            let new_name = params.new_name;
            (!reference_list.is_empty()).then_some(()).map(|_| {
                let edit_list = reference_list
                    .into_iter()
                    .filter_map(|range| {
                        let start_position = offset_to_position(range.start, &rope)?;
                        let end_position = offset_to_position(range.end, &rope)?;
                        Some(TextEdit::new(
                            Range::new(start_position, end_position),
                            new_name.clone(),
                        ))
                    })
                    .collect::<Vec<_>>();
                let mut map = HashMap::new();
                map.insert(uri, edit_list);
                WorkspaceEdit::new(map)
            })
        }();
        Ok(workspace_edit)
    }*/

    fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        debug!("configuration changed!");
    }

    fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {
        debug!("workspace folders changed!");
    }

    fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        debug!("watched files have changed!");
    }

    fn execute_command(&self, _: ExecuteCommandParams) -> Result<Option<Value>> {
        debug!("command executed!");

        /*TODO:match self.client.apply_edit(WorkspaceEdit::default()) {
            Ok(res) if res.applied => self.client.log_message(MessageType::INFO, "applied"),
            Ok(_) => self.client.log_message(MessageType::INFO, "rejected"),
            Err(err) => self.client.log_message(MessageType::ERROR, err),
        }*/

        Ok(None)
    }
}

#[allow(unused)]
enum CustomNotification {}
impl Notification for CustomNotification {
    type Params = InlayHintParams;
    const METHOD: &'static str = "custom/notification";
}
struct TextDocumentItem<'a> {
    uri: Url,
    text: &'a str,
    version: Option<i32>,
}

impl Backend {
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
                let (lock, cvar) = &*self.processed_signal;
                let mut processed = lock.lock().unwrap();
                processed.remove(&uri_str);
                drop(processed);
            }
            self.processing_uris.insert(uri_str.clone(), true);

            // 此时锁已释放，主线程可以放入新任务，我们在处理当前最新的任务
            eprintln!("Worker starting job for version {:?}", job.version);
            self.on_change(TextDocumentItem {
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
    fn on_change(&self, params: TextDocumentItem<'_>) {
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
        if let Some(ast) = parser(params.text, now_id) {
            eprintln!("parser {:?}", start.elapsed().as_secs_f32());
            let mut err_collect = vec![];
            self.ast_map.insert(params.uri.to_string(), ast.0.clone());
            let mut infer = Infer::new();
            let mut terms = vec![];
            let mut cxt = Cxt::new();
            let mut ret = String::new();
            let start = std::time::Instant::now();
            for tm in ast.0 {
                match infer.infer(&cxt, tm.clone()) {
                    Ok((x, _, new_cxt)) => {
                        terms.push(x);
                        cxt = new_cxt;
                    },
                    Err(err) => {
                        err_collect.push(err);
                        //Diagnostic::new_simple(Range::new(start, end), format!("{:?}", err))
                    }
                }
                /*if let DeclTm::Println(x) = x {
                    ret += &format!("{:?}", infer.nf(&cxt.env, x));
                    ret += "\n";
                }*/
            }
            eprintln!("infer {:?}", start.elapsed().as_secs_f32());
            self.type_map.insert(params.uri.to_string(), terms);
            self.hover_table.insert(params.uri.to_string(), infer.clone());
            //eprintln!("{:?}", err_collect);
            let diag = err_collect
                .into_iter()
                .chain(ast.1.into_iter().map(|e| e.to_err()))
                .filter_map(|e| {
                    let start_position = offset_to_position(e.0.start_offset as usize, &rope)?;
                    let end_position = offset_to_position(e.0.end_offset as usize, &rope)?;
                    Some(Diagnostic::new_simple(
                        Range::new(start_position, end_position),
                        e.0.data,
                    ))
                })
                .collect();
            self.client
                .publish_diagnostics(params.uri.clone(), diag, params.version);
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

fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
    let line = rope.try_char_to_line(offset).ok()?;
    let first_char_of_line = rope.try_line_to_char(line).ok()?;
    let column = offset - first_char_of_line;
    Some(Position::new(line as u32, column as u32))
}

fn position_to_offset(position: Position, rope: &Rope) -> Option<usize> {
    let line_char_offset = rope.try_line_to_char(position.line as usize).ok()?;
    let slice = rope.slice(0..line_char_offset + position.character as usize);
    Some(slice.len_bytes())
}

/*fn get_references(
    semantic: &Semantic,
    start: usize,
    end: usize,
    include_definition: bool,
) -> Option<Vec<Span>> {
    let interval = semantic.ident_range.find(start, end).next()?;
    let interval_val = interval.val;
    match interval_val {
        IdentType::Binding(symbol_id) => {
            let references = semantic.table.symbol_id_to_references.get(&symbol_id)?;
            let mut reference_span_list: Vec<Span> = references
                .iter()
                .map(|reference_id| {
                    semantic.table.reference_id_to_reference[*reference_id]
                        .span
                        .clone()
                })
                .collect();
            if include_definition {
                let symbol_range = semantic.table.symbol_id_to_span.get(symbol_id)?;
                reference_span_list.push(symbol_range.clone());
            }
            Some(reference_span_list)
        }
        IdentType::Reference(_) => None,
    }
}*/

fn main() -> std::result::Result<(), Box<dyn Error + Sync + Send>> {
    // Note that  we must have our logging only write out to stderr.
    eprintln!("starting generic LSP server");

    // This is a workaround for a deadlock issue in WASI libc.
    // See https://github.com/WebAssembly/wasi-libc/pull/491
    fs::metadata("/workspace").unwrap();

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let mut backend = Backend::new(Client { connection });
    let _initialization_params = match backend.init() {
        Ok(it) => it,
        Err(e) => {
            if e.channel_is_disconnected() {
                io_threads.join()?;
            }
            return Err(e.into());
        }
    };
    backend.main_loop()?;
    io_threads.join()?;

    // Shut down gracefully.
    eprintln!("shutting down server");
    Ok(())
}

fn cast<R>(req: Request) -> std::result::Result<(RequestId, R::Params), ExtractError<Request>>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

fn on<N>(not: lsp_server::Notification) -> std::result::Result<N::Params, ExtractError<lsp_server::Notification>>
where
    N: lsp_types::notification::Notification,
    N::Params: serde::de::DeserializeOwned,
{
    not.extract(N::METHOD)
}
