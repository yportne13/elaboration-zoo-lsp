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
use lsp_types::Url;
use serde_json::json;

use elaboration_zoo_lsp::client::Client;
use elaboration_zoo_lsp::Backend;

const URI: &str = "file:///robust.typort";
const SRC: &str = "def foo(x: Nat): Nat = succ x\n";

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
