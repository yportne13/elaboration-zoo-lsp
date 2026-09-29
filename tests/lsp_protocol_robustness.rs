//! LSP 协议健壮性回归测试（协议评审修复组）。
//!
//! 直接驱动 `Backend::main_loop`：`lsp_server::Connection` 的字段公有，用
//! crossbeam 双通道手工拼一个连接——消息批量注入后立即断开发送端（模拟
//! EOF），main_loop 在测试线程同步跑完，再对收到的响应做断言。这样协议错
//! 误导致的 panic / main_loop Err / 响应缺失都会让测试失败。
//!
//! 覆盖：semanticTokens 分派臂删除、畸形 params、空 contentChanges、越界
//! range、executeCommand 参数、未知请求 -32601、$/cancelRequest id 保真。

use lsp_server::{Message, Request, RequestId, Response};
use lsp_types::{
    DidChangeTextDocumentParams, DidOpenTextDocumentParams, TextDocumentContentChangeEvent,
    TextDocumentItem, Url, VersionedTextDocumentIdentifier,
};
use ropey::Rope;
use serde_json::json;

use elaboration_zoo_lsp::client::Client;
use elaboration_zoo_lsp::ls::LanguageServer;
use elaboration_zoo_lsp::Backend;

const URI: &str = "file:///robust.typort";
const SRC: &str = "def foo(x: Nat): Nat = succ x\n";

/// 直接调 Backend 方法（不经 main_loop）的测试夹具。LanguageServer 只为
/// Backend<Client> 实现，所以仍用真实 Client：诊断/通知发进无人消费的
/// unbounded 通道，两端刻意泄漏保活（ClientLike 的 send().unwrap() 依赖
/// 接收端存活）。
fn direct_backend() -> std::sync::Arc<Backend<Client>> {
    let (to_server_tx, to_server_rx) = crossbeam_channel::unbounded::<Message>();
    let (to_test_tx, to_test_rx) = crossbeam_channel::unbounded::<Message>();
    let connection = lsp_server::Connection { sender: to_test_tx, receiver: to_server_rx };
    let b = Backend::new(Client { connection });
    b.load_prelude_skip_hdl();
    std::mem::forget((to_server_tx, to_test_rx));
    b
}

/// 一次批量会话的结果。
struct Session {
    responses: Vec<Response>,
    notifications: Vec<lsp_server::Notification>,
}

/// 搭一个预置了 `SRC` 文档的会话：先注入 `msgs` 再断开发送端，同步跑完
/// main_loop 并收集测试端收到的全部消息。
fn run_session(msgs: Vec<Message>) -> Session {
    let (to_server_tx, to_server_rx) = crossbeam_channel::unbounded::<Message>();
    let (to_test_tx, to_test_rx) = crossbeam_channel::unbounded::<Message>();
    let connection = lsp_server::Connection { sender: to_test_tx, receiver: to_server_rx };
    let b = Backend::new(Client { connection });
    b.load_prelude_skip_hdl();
    b.process_file(&Url::parse(URI).unwrap(), SRC, Some(1));
    for m in msgs {
        to_server_tx.send(m).unwrap();
    }
    // 规范关闭路径：shutdown + exit 让 main_loop 走正常退出（对"无
    // shutdown 的断连"它返回 Err——那是 exit-code 修复要抓的异常路径）。
    // 注意 lsp-server 的 handle_shutdown 在响应 shutdown 后会阻塞等 exit
    // 通知，只发 shutdown 会以 ProtocolError 收场。
    to_server_tx
        .send(request(0xF000, "shutdown", json!(null)))
        .unwrap();
    to_server_tx.send(notification("exit", json!(null))).unwrap();
    drop(to_server_tx); // EOF：main_loop 处理完队列后自然退出
    b.main_loop()
        .expect("main_loop 不得返回 Err（协议层错误必须回包，不能终结会话）");
    drop(b); // 释放 Connection.sender，让响应通道断开
    let mut responses = Vec::new();
    let mut notifications = Vec::new();
    for m in to_test_rx {
        match m {
            Message::Response(r) => responses.push(r),
            Message::Notification(n) => notifications.push(n),
            _ => {}
        }
    }
    Session { responses, notifications }
}

fn request(id: i32, method: &str, params: serde_json::Value) -> Message {
    Message::Request(Request::new(RequestId::from(id), method.to_owned(), params))
}

fn notification(method: &str, params: serde_json::Value) -> Message {
    Message::Notification(lsp_server::Notification::new(method.to_owned(), params))
}

fn response_for(s: &Session, id: i32) -> Option<&Response> {
    let want = RequestId::from(id);
    s.responses.iter().find(|r| r.id == want)
}

fn hover_params() -> serde_json::Value {
    json!({"textDocument": {"uri": URI}, "position": {"line": 0, "character": 4}})
}

// ── 修复1：semanticTokens 分派臂终结会话 ─────────────────────────────────────
//
// capabilities 从未声明 semanticTokens，服务端也未实现：旧分派臂把 trait 默
// 认实现的 Err 用 `?` 抛出，main_loop 直接返回 Err → 服务端假死。回归：发
// semanticTokens/full 之后服务端必须还能应答 hover。

#[test]
fn semantic_tokens_full_does_not_kill_session() {
    let s = run_session(vec![
        request(
            1,
            "textDocument/semanticTokens/full",
            json!({"textDocument": {"uri": URI}}),
        ),
        request(2, "textDocument/hover", hover_params()),
    ]);
    let hover = response_for(&s, 2).expect("semanticTokens 之后 hover 必须仍被应答");
    assert!(
        hover.error.is_none(),
        "hover 必须成功: {:?}",
        hover.error
    );
    // semanticTokens 不允许产生成功响应（未声明的能力）。
    if let Some(r) = response_for(&s, 1) {
        assert!(
            r.error.is_some(),
            "semanticTokens/full 不能返回成功响应: {:?}",
            r.result
        );
    }
}

// ── 修复2：畸形 params panic 终结会话 ────────────────────────────────────────
//
// 旧实现对 cast::<T>/on::<T> 的 JsonError 一律 panic!，一个畸形请求/通知就
// 能终结 main_loop。回归：畸形请求收到 -32602 错误响应，畸形通知被丢弃，
// 两者之后服务端都必须继续应答。

#[test]
fn malformed_request_params_get_invalid_params_response() {
    let s = run_session(vec![
        // 缺 position 字段 → cast::<HoverRequest> JsonError
        request(1, "textDocument/hover", json!({"textDocument": {"uri": URI}})),
        request(2, "textDocument/hover", hover_params()),
    ]);
    let err = response_for(&s, 1).expect("畸形 params 的请求必须收到错误响应");
    let err = err.error.as_ref().expect("应为 error 响应");
    assert_eq!(err.code, -32602, "畸形 params 应回 -32602: {:?}", err);
    let hover = response_for(&s, 2).expect("错误响应之后服务端必须继续应答");
    assert!(hover.error.is_none(), "后续合法 hover 必须成功: {:?}", hover.error);
}

#[test]
fn malformed_notification_is_dropped_and_session_survives() {
    let s = run_session(vec![
        // 缺 contentChanges 字段 → on::<DidChangeTextDocument> JsonError
        notification(
            "textDocument/didChange",
            json!({"textDocument": {"uri": URI, "version": 2}}),
        ),
        request(3, "textDocument/hover", hover_params()),
    ]);
    let hover = response_for(&s, 3).expect("畸形通知被丢弃后服务端必须继续应答");
    assert!(hover.error.is_none(), "后续合法 hover 必须成功: {:?}", hover.error);
}

// ── 修复3：did_change 空 contentChanges 越界 panic ───────────────────────────
//
// 旧实现 buffer 缺失时取 content_changes[0].text：对未 open 的 URI 发
// contentChanges: [] 会索引越界 panic（document_buffers Mutex 中毒）。
// LSP 规范里空数组是合法 no-op。

#[test]
fn empty_content_changes_is_noop() {
    let b = direct_backend();
    let uri = Url::parse(URI).unwrap();

    // 未 open 的 URI + 空数组：不得 panic（旧实现 content_changes[0] 越界）。
    b.did_change(DidChangeTextDocumentParams {
        text_document: VersionedTextDocumentIdentifier { uri: uri.clone(), version: 1 },
        content_changes: vec![],
    });

    // 已 open 的 URI + 空数组：缓冲与文档内容不变。
    b.did_open(DidOpenTextDocumentParams {
        text_document: TextDocumentItem {
            uri: uri.clone(),
            language_id: "typort".to_owned(),
            version: 1,
            text: SRC.to_owned(),
        },
    });
    b.did_change(DidChangeTextDocumentParams {
        text_document: VersionedTextDocumentIdentifier { uri: uri.clone(), version: 2 },
        content_changes: vec![],
    });
    b.drain_analysis_jobs();
    let rope = b.document_map.get(uri.as_str()).unwrap();
    assert_eq!(rope.to_string(), SRC, "空 contentChanges 不得改动文档");
}

// ── 修复4：越界 range 的破坏性 fallback ─────────────────────────────────────
//
// 旧实现 position_to_offset 失败时把整个 buffer 替换成 change.text（增量
// 片段冒充全文）；URI 未 open 时取 [0].text 当全文且不回插 buffer。回归：
// 越界端点 clamp 后照常应用增量；无 buffer 注册后能继续增量。

#[test]
fn out_of_range_incremental_change_clamps_instead_of_clobbering() {
    let b = direct_backend();
    let uri = Url::parse(URI).unwrap();
    b.did_open(DidOpenTextDocumentParams {
        text_document: TextDocumentItem {
            uri: uri.clone(),
            language_id: "typort".to_owned(),
            version: 1,
            text: "line0\nline1\n".to_owned(),
        },
    });
    b.drain_analysis_jobs();

    // start 合法、end 行号越界：期望 clamp 到文档末尾后增量替换
    // （"line0\nline1\n" 从 (0,1) 到文档末尾替换为 "X" → "lX"）。
    // 旧实现 position_to_offset 失败 → buffer 整卷变成 "X"。
    b.did_change(DidChangeTextDocumentParams {
        text_document: VersionedTextDocumentIdentifier { uri: uri.clone(), version: 2 },
        content_changes: vec![TextDocumentContentChangeEvent {
            range: Some(lsp_types::Range {
                start: lsp_types::Position { line: 0, character: 1 },
                end: lsp_types::Position { line: 99, character: 0 },
            }),
            range_length: None,
            text: "X".to_owned(),
        }],
    });
    b.drain_analysis_jobs();
    let rope = b.document_map.get(uri.as_str()).unwrap();
    assert_eq!(rope.to_string(), "lX", "越界 range 应 clamp 后增量应用，而非整卷替换");
}

#[test]
fn missing_buffer_registers_and_continues_incremental_path() {
    let b = direct_backend();
    let uri = Url::parse(URI).unwrap();

    // 刻意不 did_open：第一笔 ranged change 从空内容起步并注册 buffer。
    b.did_change(DidChangeTextDocumentParams {
        text_document: VersionedTextDocumentIdentifier { uri: uri.clone(), version: 1 },
        content_changes: vec![TextDocumentContentChangeEvent {
            range: Some(lsp_types::Range {
                start: lsp_types::Position { line: 0, character: 0 },
                end: lsp_types::Position { line: 0, character: 0 },
            }),
            range_length: None,
            text: "hello".to_owned(),
        }],
    });

    b.drain_analysis_jobs();

    // 注意：DashMap 的读守卫不能跨 did_change/drain 持有——同线程对同 key
    // 的 insert 要等读锁释放（非重入），守卫活到函数尾就会死锁。作用域内
    // 用完即弃。
    assert_eq!(b.document_map.get(uri.as_str()).unwrap().to_string(), "hello");

    // 第二笔增量必须基于注册后的 buffer（旧实现拿不到 buffer，继续把
    // [0].text 当全文，文档会变成 " world"）。

    b.did_change(DidChangeTextDocumentParams {
        text_document: VersionedTextDocumentIdentifier { uri: uri.clone(), version: 2 },
        content_changes: vec![TextDocumentContentChangeEvent {
            range: Some(lsp_types::Range {
                start: lsp_types::Position { line: 0, character: 5 },
                end: lsp_types::Position { line: 0, character: 5 },
            }),
            range_length: None,
            text: " world".to_owned(),
        }],
    });

    b.drain_analysis_jobs();

    assert_eq!(b.document_map.get(uri.as_str()).unwrap().to_string(), "hello world", "注册 buffer 后续增量应正常累积");
}

// ── 修复6：executeCommand 参数畸形 ──────────────────────────────────────────
//
// 旧实现 args[0]/args[1] 直接索引 + serde unwrap：空参/单参/类型不符都会
// panic 终结会话。回归：畸形参数收到 -32602，之后服务端继续应答。

#[test]
fn execute_command_bad_arguments_get_invalid_params_response() {
    let s = run_session(vec![
        request(1, "workspace/executeCommand", json!({
            "command": "typort.applyQuickFix",
            "arguments": []
        })),
        request(2, "workspace/executeCommand", json!({
            "command": "typort.applyQuickFix",
            "arguments": ["file:///a.typort"]
        })),
        request(3, "workspace/executeCommand", json!({
            "command": "typort.applyQuickFix",
            "arguments": [42, "id"]
        })),
        request(4, "textDocument/hover", hover_params()),
    ]);
    for id in [1, 2, 3] {
        let r = response_for(&s, id).expect("畸形 arguments 的 executeCommand 必须收到错误响应");
        let err = r.error.as_ref().expect("应为 error 响应");
        assert_eq!(err.code, -32602, "缺参/类型错应回 -32602: {:?}", err);
    }
    let hover = response_for(&s, 4).expect("错误响应之后服务端必须继续应答");
    assert!(hover.error.is_none(), "后续合法 hover 必须成功: {:?}", hover.error);
}

// ── 修复7a：未识别请求回 -32601 ─────────────────────────────────────────────
//
// 旧实现对未识别的请求静默丢弃（永不回包），客户端 promise 挂到自身超时。
// 回归：未知方法收到 -32601，服务端继续应答。

#[test]
fn unknown_request_gets_method_not_found() {
    let s = run_session(vec![
        request(1, "textDocument/documentSymbol", json!({"textDocument": {"uri": URI}})),
        request(2, "textDocument/hover", hover_params()),
    ]);
    let r = response_for(&s, 1).expect("未识别的请求必须收到错误响应");
    let err = r.error.as_ref().expect("应为 error 响应");
    assert_eq!(err.code, -32601, "未识别请求应回 -32601: {:?}", err);
    let hover = response_for(&s, 2).expect("-32601 之后服务端必须继续应答");
    assert!(hover.error.is_none(), "后续合法 hover 必须成功: {:?}", hover.error);
}

// ── 修复7e：inlay 单条越界不再让全文件 inlay 消失 ────────────────────────────
//
// 旧实现循环内 `offset_to_position(...)?`：任何一条越界（陈旧表）都让
// inlay_hint_at 整体返回 None。回归：把 document_map 换成更短的 rope 模拟
// 陈旧表后，仍应返回 Some（过滤后剩余项，可能为空），而不是 None。

#[test]
fn inlay_hint_skips_out_of_bounds_entries_instead_of_returning_none() {
    let b = direct_backend();
    let uri = Url::parse(URI).unwrap();
    let src = "def f(x: Nat) = let y = x + 1; y\n";
    b.process_file(&uri, src, Some(1));
    b.drain_analysis_jobs();
    // 测试前提：源码确实产出 inlay（否则本测试退化为 no-op）。
    let hints = b.inlay_hint_at(&uri).unwrap_or_default();
    assert!(!hints.is_empty(), "测试前提：源码应产出 inlay（实际 0 条）");
    // 模拟陈旧表：rope 被替换成更短的文本而 inlay 表未重建——全部条目
    // 都越界。旧实现走到第一条就 `?` 成 None；新实现逐条跳过后返回 Some。
    b.document_map.insert(uri.to_string(), Rope::from_str("x\n"));
    assert!(
        b.inlay_hint_at(&uri).is_some(),
        "越界条目应被逐条跳过，不得让整个文件的 inlay 变 None"
    );
}

// ── 修复7c：memfs:// 写侧归一化 ─────────────────────────────────────────────
//
// 读侧请求全部把 memfs:// normalize 成 file:// 键，写侧（did_open/process_
// file）却按原始 memfs URI 存——web 宿主文档永远查不到。回归：memfs
// did_open 后必须以 file:// 键入库，且不得另存原始键。

#[test]
fn memfs_open_is_normalized_to_file_scheme() {
    let b = direct_backend();
    let uri = Url::parse("memfs:///workspace/m.typort").unwrap();
    b.did_open(DidOpenTextDocumentParams {
        text_document: TextDocumentItem {
            uri: uri.clone(),
            language_id: "typort".to_owned(),
            version: 1,
            text: SRC.to_owned(),
        },
    });
    b.drain_analysis_jobs();
    assert!(
        b.document_map.get("file:///workspace/m.typort").is_some(),
        "memfs did_open 应归一化为 file:// 键入库"
    );
    assert!(
        b.document_map.get("memfs:///workspace/m.typort").is_none(),
        "不得以原始 memfs 键另存一份"
    );
}

// ── 修复7d：builtin 只读文档不做格式化 ──────────────────────────────────────
//
// 旧实现对 builtin:// 虚拟文档（prelude）也返回整卷 TextEdit，客户端会对
// 只读编辑器报错。回归：返回空编辑集。

#[test]
fn formatting_builtin_readonly_document_returns_no_edits() {
    let b = direct_backend();
    let uri = Url::parse("builtin:///nat.typort").unwrap();
    let edits = b.format_document_at(&uri, &lsp_types::FormattingOptions::default());
    assert_eq!(edits, Some(vec![]), "builtin 只读文档应回空编辑");
}
