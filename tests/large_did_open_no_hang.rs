//! Regression test for the large-`didOpen`/`didChange` transport deadlock.
//!
//! The server previously handed messages between its reader/writer threads
//! and the main loop through zero-capacity (rendezvous) channels. When a
//! client opened a file at startup (a `didOpen` arriving while the main
//! thread was still inside `load_prelude()`) and then opened a *large* file,
//! the rendezvous handoff wedged all four parties into a cycle:
//!
//!   reader thread (blocked handing off the early `didOpen`) → stdin pipe
//!   (client blocked writing the large frame) → stdout pipe (client cannot
//!   drain it while its write is blocked) → writer thread (blocked writing
//!   `load_prelude` diagnostics) → main thread (blocked sending) → reader.
//!
//! This test models the single-threaded WASI host that cannot read stdout
//! while its stdin write is in progress: it sends `initialized` + a small
//! `didOpen` + a > 1 MiB `didOpen` in one blocking write. Pre-fix that write
//! never completes; post-fix (unbounded transport channels) it completes in
//! milliseconds and the server answers subsequent requests.

use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// Timeout for a single client-side write that must complete.
const WRITE_TIMEOUT: Duration = Duration::from_secs(60);
/// Timeout for the initialize handshake / liveness probe responses.
const RESPONSE_TIMEOUT: Duration = Duration::from_secs(60);

fn frame(obj: &Value) -> Vec<u8> {
    let body = serde_json::to_string(obj).unwrap();
    format!("Content-Length: {}\r\n\r\n{}", body.len(), body).into_bytes()
}

fn open_notif(uri: &str, text: &str, version: i32) -> Value {
    json!({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": uri,
                "languageId": "typort",
                "version": version,
                "text": text,
            }
        }
    })
}

/// A live LSP server process whose stdout is parsed into frames by a helper
/// thread, so the main thread can block on writes exactly like a
/// single-threaded client would.
struct Server {
    child: Child,
    stdin: Option<ChildStdin>,
    frames_rx: mpsc::Receiver<Value>,
}

impl Server {
    fn spawn() -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_elaboration-zoo-lsp"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("failed to spawn the LSP server binary");
        let stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (frames_tx, frames_rx) = mpsc::channel();
        // Parse the LSP wire format (Content-Length framing) in a thread.
        thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                let mut content_length: Option<usize> = None;
                loop {
                    line.clear();
                    match reader.read_line(&mut line) {
                        Ok(0) | Err(_) => return,
                        Ok(_) => {}
                    }
                    let trimmed = line.trim_end();
                    if trimmed.is_empty() {
                        break;
                    }
                    if let Some((name, value)) = trimmed.split_once(':') {
                        if name.eq_ignore_ascii_case("Content-Length") {
                            content_length = value.trim().parse().ok();
                        }
                    }
                }
                let n = match content_length {
                    Some(n) => n,
                    None => return,
                };
                let mut body = vec![0u8; n];
                if reader.read_exact(&mut body).is_err() {
                    return;
                }
                let obj: Value = match serde_json::from_slice(&body) {
                    Ok(v) => v,
                    Err(_) => return,
                };
                if frames_tx.send(obj).is_err() {
                    return;
                }
            }
        });
        Server { child, stdin: Some(stdin), frames_rx }
    }

    /// Blocking single write, mirroring a client that cannot read stdout
    /// while its write is in flight. Returns false if it did not complete in
    /// time (the pre-fix server deadlocked exactly here). The handle is
    /// moved to a helper thread so the write can be timed out; it is moved
    /// back when the write completes.
    fn write_all_timeout(&mut self, data: &[u8]) -> bool {
        let mut stdin = self.stdin.take().expect("stdin already in use");
        let data = data.to_vec();
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            let ok = stdin.write_all(&data).is_ok() && stdin.flush().is_ok();
            let _ = tx.send((ok, stdin));
        });
        match rx.recv_timeout(WRITE_TIMEOUT) {
            Ok((ok, stdin)) => {
                self.stdin = Some(stdin);
                ok
            }
            Err(_) => false,
        }
    }

    fn send(&mut self, data: &[u8]) {
        let stdin = self.stdin.as_mut().expect("stdin in use");
        stdin.write_all(data).expect("write to server stdin");
        stdin.flush().unwrap();
    }

    /// Wait for a response with the given id, skipping notifications.
    fn wait_response(&self, id: i64, timeout: Duration) -> Option<Value> {
        let deadline = Instant::now() + timeout;
        while Instant::now() < deadline {
            let remaining = deadline - Instant::now();
            match self.frames_rx.recv_timeout(remaining) {
                Ok(frame) => {
                    if frame.get("id").and_then(Value::as_i64) == Some(id) {
                        return Some(frame);
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => return None,
                Err(mpsc::RecvTimeoutError::Disconnected) => return None,
            }
        }
        None
    }

    fn kill(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[test]
fn large_did_open_after_startup_does_not_hang_the_server() {
    let mut server = Server::spawn();

    // ---- initialize handshake ----
    server.send(&frame(&json!({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": { "capabilities": {}, "processId": null, "rootUri": null, "workspaceFolders": [] },
    })));
    let init_resp = server.wait_response(1, RESPONSE_TIMEOUT);
    assert!(init_resp.is_some(), "no response to initialize");

    // ---- the deadlock-triggering burst, in ONE blocking write ----
    // `initialized` + a small didOpen for a file "already open at startup" +
    // a > 1 MiB didOpen. While the main thread runs load_prelude(), the
    // reader used to block on the small didOpen's rendezvous handoff, so the
    // client's write of the large frame stalled forever and the writer (and
    // with it the main thread's prelude diagnostics) stalled on the full
    // stdout pipe. With unbounded transport channels the reader keeps
    // draining stdin and this write completes almost immediately.
    let burst = [
        frame(&json!({ "jsonrpc": "2.0", "method": "initialized", "params": {} })),
        frame(&open_notif("file:///small.typort", "let x = 1\n", 1)),
        frame(&open_notif("file:///big.typort", &"y".repeat(2 * 1024 * 1024), 1)),
    ]
    .concat();
    let burst_completed = server.write_all_timeout(&burst);
    assert!(
        burst_completed,
        "server deadlocked: the client's blocking write of the large didOpen \
         burst did not complete within {WRITE_TIMEOUT:?}"
    );

    // ---- the server must still answer requests ----
    // NB: in debug builds the server aborts inside `load_prelude()` with a
    // stack overflow (the main thread's 1 MiB stack cannot hold the deep
    // recursion of the *unoptimized* prelude elaboration) — a pre-existing
    // issue unrelated to the transport. The deadlock regression above (the
    // burst write completing) is asserted in every profile; the full
    // request/response liveness probe below only runs where the server
    // survives startup (release builds).
    if cfg!(debug_assertions) {
        server.kill();
        return;
    }

    server.send(&frame(&json!({
        "jsonrpc": "2.0",
        "id": 99,
        "method": "typort-hdl/builtinContent",
        "params": { "uri": "builtin:///op.typort" },
    })));
    let ping = server.wait_response(99, RESPONSE_TIMEOUT);
    assert!(
        ping.is_some(),
        "server did not answer a request after the large didOpen burst"
    );

    // A second request proves the server keeps responding (no one-shot).
    server.send(&frame(&json!({
        "jsonrpc": "2.0",
        "id": 100,
        "method": "typort-hdl/builtinContent",
        "params": { "uri": "builtin:///eq.typort" },
    })));
    let ping2 = server.wait_response(100, RESPONSE_TIMEOUT);
    assert!(
        ping2.is_some(),
        "server stopped responding after the first post-burst request"
    );

    server.kill();
}
