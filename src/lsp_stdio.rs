//! Chunked stdio transport for the LSP server.
//!
//! `lsp_server::Connection::stdio()` performs each LSP frame with a single
//! `read_exact` / `write_all` call, which becomes one giant `fd_read` /
//! `fd_write` syscall on the underlying stdin/stdout. WASI-style runtimes
//! (e.g. VS Code web's `@vscode/wasm-wasi`) cap a single read/write call at
//! 64 KiB; larger requests fail or get truncated, which crashed the server on
//! big JSON frames such as `textDocument/didOpen` payloads and large
//! `publishDiagnostics` results.
//!
//! This module reimplements the lsp-server 0.7.x stdio transport (same two
//! reader/writer threads) but wraps stdin/stdout in [`ChunkedReader`] /
//! [`ChunkedWriter`] so every underlying read/write call is at most [`CHUNK`]
//! bytes. The `BufRead`/`Write`-level framing is unchanged, so the wire
//! protocol and desktop behavior are identical.
//!
//! # Why the message channels are unbounded (not rendezvous)
//!
//! Upstream lsp-server hands messages between its reader/writer threads and
//! the main loop through zero-capacity (rendezvous) crossbeam channels. That
//! couples the transport to the main thread's message-processing schedule and
//! can deadlock the whole server once a client writes a frame larger than the
//! OS pipe buffer (or the WASI ring buffer):
//!
//! 1. The reader thread reads a frame and blocks on the rendezvous `send`
//!    until the main loop calls `recv`. While the main thread is busy (e.g.
//!    `load_prelude()` runs synchronously before `main_loop()` starts, or a
//!    request handler is running), the reader stops draining stdin.
//! 2. The client's blocking write of a large frame (big `didOpen`/`didChange`)
//!    then stalls on the full stdin pipe, so the client cannot drain stdout.
//! 3. The main thread's next send (prelude diagnostics / log messages / a
//!    response) rendezvous-blocks on the writer thread, which is blocked
//!    writing to the full stdout pipe.
//!
//! That closes a 4-way cycle: main thread → writer → stdout pipe → client →
//! stdin pipe → reader thread → main thread. It is easy to trip at startup,
//! when a `didOpen` for an already-open editor tab arrives while
//! `load_prelude()` is still emitting diagnostics, and the client then opens
//! a large file (a single-threaded WASI host cannot poll stdout while its
//! stdin write is blocked).
//!
//! Unbounded channels break the cycle: the reader thread always drains stdin
//! (the client's writes always complete, so it always returns to reading
//! stdout) and the main loop / worker never block on `connection.sender.send`
//! (the writer thread drains at its own pace). Message ordering is preserved
//! (one sender per channel direction) and the 64 KiB chunking is unchanged.

use std::io::{self, Read, Write};
use std::thread;

use crossbeam_channel::{unbounded, Receiver, Sender};
use log::debug;
use lsp_server::Message;

/// Maximum number of bytes handed to the underlying stdin/stdout per call.
/// 64 KiB is the de-facto per-call buffer limit of WASI-style runtimes.
pub(crate) const CHUNK: usize = 64 * 1024;

/// Write wrapper that forwards at most `chunk` bytes per underlying write
/// call, so `write_all()` loops and each `fd_write` stays small (WASI-safe).
pub(crate) struct ChunkedWriter<W: Write> {
    inner: W,
    chunk: usize,
}

impl<W: Write> ChunkedWriter<W> {
    fn new(inner: W, chunk: usize) -> Self {
        ChunkedWriter { inner, chunk }
    }
}

impl<W: Write> Write for ChunkedWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = buf.len().min(self.chunk);
        self.inner.write(&buf[..n])
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

/// Read wrapper that requests at most `chunk` bytes per underlying read call,
/// so `read_exact()` loops and each `fd_read` stays small (WASI-safe).
pub(crate) struct ChunkedReader<R: Read> {
    inner: R,
    chunk: usize,
}

impl<R: Read> ChunkedReader<R> {
    fn new(inner: R, chunk: usize) -> Self {
        ChunkedReader { inner, chunk }
    }
}

impl<R: Read> Read for ChunkedReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = buf.len().min(self.chunk);
        self.inner.read(&mut buf[..n])
    }
}

/// Handles to the reader/writer threads of the stdio transport.
pub(crate) struct IoThreads {
    reader: thread::JoinHandle<io::Result<()>>,
    writer: thread::JoinHandle<io::Result<()>>,
}

impl IoThreads {
    pub(crate) fn join(self) -> io::Result<()> {
        match self.reader.join() {
            Ok(r) => r?,
            Err(err) => std::panic::panic_any(err),
        }
        match self.writer.join() {
            Ok(r) => r,
            Err(err) => {
                std::panic::panic_any(err);
            }
        }
    }
}

/// Creates an LSP connection over stdin/stdout whose underlying reads and
/// writes never exceed [`CHUNK`] bytes per call. Mirrors
/// `lsp_server::Connection::stdio()` (same `Connection` type, same thread
/// names) plus the chunked wrappers.
pub(crate) fn stdio() -> (lsp_server::Connection, IoThreads) {
    let (sender, receiver, threads) = stdio_transport();
    (lsp_server::Connection { sender, receiver }, threads)
}

/// Spawns the reader and writer threads around a chunked stdin/stdout.
///
/// `io::stdin()` / `io::stdout()` are passed directly (not their `lock()`
/// guards, which are not `Send`): each underlying read/write call locks
/// briefly, which is equivalent for the single reader/writer threads and
/// keeps the 64 KiB chunking intact.
fn stdio_transport() -> (Sender<Message>, Receiver<Message>, IoThreads) {
    transport(
        ChunkedReader::new(io::stdin(), CHUNK),
        ChunkedWriter::new(io::stdout(), CHUNK),
    )
}

/// Spawns the reader and writer threads around an arbitrary reader/writer
/// pair (chunked stdin/stdout in production, in-memory pipes in tests).
fn transport<R, W>(reader: R, writer: W) -> (Sender<Message>, Receiver<Message>, IoThreads)
where
    R: Read + Send + 'static,
    W: Write + Send + 'static,
{
    // Unbounded channels (see the module docs): with capacity-0 rendezvous
    // channels the reader stalls on the first message the main loop is not
    // ready for, which can wedge stdin/stdout against a client blocked on a
    // large frame write.
    let (writer_sender, writer_receiver) = unbounded::<Message>();
    let writer = thread::Builder::new()
        .name("LspServerWriter".to_owned())
        .spawn(move || {
            let mut writer = writer;
            writer_receiver.into_iter().try_for_each(|it| it.write(&mut writer))
        })
        .unwrap();
    let (reader_sender, reader_receiver) = unbounded::<Message>();
    let reader = thread::Builder::new()
        .name("LspServerReader".to_owned())
        .spawn(move || {
            let mut stdin = io::BufReader::new(reader);
            while let Some(msg) = Message::read(&mut stdin)? {
                // `Notification::is_exit()` is pub(crate) inside lsp-server,
                // so detect the exit notification via its public method name.
                let is_exit = matches!(&msg, Message::Notification(n) if n.method == "exit");

                debug!("sending message {:#?}", msg);
                if let Err(e) = reader_sender.send(msg) {
                    return Err(io::Error::new(io::ErrorKind::Other, e));
                }

                if is_exit {
                    break;
                }
            }
            Ok(())
        })
        .unwrap();
    let threads = IoThreads { reader, writer };
    (writer_sender, reader_receiver, threads)
}

#[cfg(test)]
mod tests {
    use super::{transport, ChunkedReader, ChunkedWriter, CHUNK};
    use lsp_server::{Message, Notification};
    use serde_json::json;
    use std::io::{self, BufReader, Read, Write};
    use std::thread;
    use std::time::Duration;

    /// Records the largest single buffer that reached the pipe, proving the
    /// chunking wrapper caps every underlying read/write call.
    struct WriteTracker<W: Write> {
        inner: W,
        max_request: usize,
    }

    impl<W: Write> Write for WriteTracker<W> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.max_request = self.max_request.max(buf.len());
            self.inner.write(buf)
        }

        fn flush(&mut self) -> io::Result<()> {
            self.inner.flush()
        }
    }

    struct ReadTracker<R: Read> {
        inner: R,
        max_request: usize,
    }

    impl<R: Read> Read for ReadTracker<R> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            self.max_request = self.max_request.max(buf.len());
            self.inner.read(buf)
        }
    }

    /// Pushes `msg` through an in-memory pipe: a spawned thread writes it via
    /// a `ChunkedWriter` (like the real LspServerWriter thread, so a small
    /// pipe buffer can never deadlock the test), while this thread reads it
    /// back via `BufReader<ChunkedReader>` (like the real LspServerReader
    /// thread). Asserts the payload survives byte-for-byte and returns the
    /// largest single read/write request that reached the pipe.
    fn roundtrip_tracked(msg: &Message) -> (usize, usize) {
        let (pipe_reader, pipe_writer) = io::pipe().unwrap();
        let msg_clone = msg.clone();
        let writer_thread = thread::spawn(move || {
            let mut tracker = WriteTracker { inner: pipe_writer, max_request: 0 };
            let mut writer = ChunkedWriter::new(&mut tracker, CHUNK);
            msg_clone.write(&mut writer).unwrap();
            writer.flush().unwrap();
            tracker
        });
        let mut read_tracker = ReadTracker { inner: pipe_reader, max_request: 0 };
        let mut reader = BufReader::new(ChunkedReader::new(&mut read_tracker, CHUNK));
        let got = Message::read(&mut reader).unwrap().expect("expected one message");
        drop(reader);
        let write_tracker = writer_thread.join().unwrap();
        assert_eq!(
            serde_json::to_string(msg).unwrap(),
            serde_json::to_string(&got).unwrap(),
            "payload must survive the chunked roundtrip unchanged"
        );
        (write_tracker.max_request, read_tracker.max_request)
    }

    fn assert_chunked(max_write: usize, max_read: usize) {
        assert!(max_write <= CHUNK, "single write to the pipe was {max_write} bytes");
        assert!(max_read <= CHUNK, "single read from the pipe was {max_read} bytes");
    }

    #[test]
    fn roundtrip_message_larger_than_one_megabyte() {
        // didOpen-style frame carrying a document body > 1 MiB: far beyond any
        // WASI per-call buffer limit, and several times the 64 KiB chunk.
        let big = "x".repeat(1024 * 1024 + 42_000);
        let msg = Message::Notification(Notification::new(
            "textDocument/didOpen".to_owned(),
            json!({ "text": big }),
        ));
        let (max_write, max_read) = roundtrip_tracked(&msg);
        assert_chunked(max_write, max_read);
    }

    #[test]
    fn roundtrip_message_crossing_several_chunk_boundaries() {
        // Build a message whose JSON body is exactly CHUNK*3 + 1234 bytes, so
        // the frame spans four 64 KiB chunks on the wire.
        let target = CHUNK * 3 + 1234;
        let probe = Message::Notification(Notification::new(
            "textDocument/didChange".to_owned(),
            json!({ "text": "x" }),
        ));
        let overhead = serde_json::to_string(&probe).unwrap().len() - 1; // minus the one-byte payload
        let msg = Message::Notification(Notification::new(
            "textDocument/didChange".to_owned(),
            json!({ "text": "x".repeat(target - overhead) }),
        ));
        assert_eq!(
            serde_json::to_string(&msg).unwrap().len(),
            target,
            "test message must land exactly on the target wire size"
        );
        let (max_write, max_read) = roundtrip_tracked(&msg);
        assert_chunked(max_write, max_read);
    }

    // ---------------------------------------------------------------------
    // Large-frame transport deadlock regressions.
    //
    // With zero-capacity (rendezvous) channels the transport wedges whenever
    // the reader cannot hand off a message to a busy main loop: the reader
    // stops draining stdin, the client's blocking write of a large frame
    // stalls, the client cannot drain stdout, the writer stalls on the full
    // stdout pipe, and the main loop's next send blocks forever. These tests
    // exercise the transport over `io::pipe()` pairs so the cycle is driven
    // purely by the channels — no dependence on OS pipe buffer sizes.

    /// Wire-encodes a message exactly like the writer thread does.
    fn encode(msg: &Message) -> Vec<u8> {
        let mut buf = Vec::new();
        msg.clone().write(&mut buf).unwrap();
        buf
    }

    /// The reader thread must keep draining stdin even while the main loop
    /// never calls `recv` again after the first message. Otherwise a client
    /// blocked on a large `didOpen` write can never make progress.
    #[test]
    fn reader_keeps_draining_stdin_while_main_loop_is_busy() {
        let (in_r, mut in_w) = io::pipe().unwrap();
        let (out_r, out_w) = io::pipe().unwrap();
        let (_sender, receiver, _threads) = transport(in_r, out_w);

        // Three frames in one blocking client write: a small didOpen, a small
        // didChange, then a > 1 MiB didOpen. The reader reads each frame
        // fully before handing it off, so the client's write can only stall
        // once the reader is blocked on an *earlier* frame's handoff while
        // the large frame is still in flight — exactly the startup pattern
        // (initialized + already-open file + large file).
        let burst = [
            encode(&Message::Notification(Notification::new(
                "textDocument/didOpen".to_owned(),
                json!({ "textDocument": { "uri": "file:///small.typort", "text": "let x = 1\n" } }),
            ))),
            encode(&Message::Notification(Notification::new(
                "textDocument/didChange".to_owned(),
                json!({ "textDocument": { "uri": "file:///small.typort", "version": 2 }, "contentChanges": [{ "text": "let x = 2\n" }] }),
            ))),
            encode(&Message::Notification(Notification::new(
                "textDocument/didOpen".to_owned(),
                json!({ "textDocument": { "uri": "file:///big.typort", "text": "y".repeat(1024 * 1024 + 42) } }),
            ))),
        ]
        .concat();

        let (done_tx, done_rx) = crossbeam_channel::unbounded();
        thread::spawn(move || {
            let result = in_w.write_all(&burst).and_then(|()| in_w.flush());
            drop(in_w); // EOF so the reader thread can exit afterwards
            let _ = done_tx.send(result);
        });

        // Main loop: consume the first message, then go "busy" (never recv).
        let first = receiver.recv().unwrap();
        assert!(matches!(
            first,
            Message::Notification(n) if n.method == "textDocument/didOpen"
        ));

        // The client's whole burst must still be written within a generous
        // timeout even though the main loop is not receiving: the reader
        // thread buffers it in its unbounded channel. Pre-fix, the reader
        // blocks on the didChange's rendezvous handoff while the large
        // didOpen is still in flight, and this write never completes.
        match done_rx.recv_timeout(Duration::from_secs(30)) {
            Ok(Ok(())) => {}
            Ok(Err(e)) => panic!("client burst write failed: {e:?}"),
            Err(_) => panic!(
                "client burst write blocked: the reader thread stopped draining stdin \
                 while the main loop was busy (rendezvous deadlock)"
            ),
        }

        // Cleanup: close the unread output pipe and drop the sender so both
        // transport threads end.
        drop(out_r);
        drop(_sender);
    }

    /// A send from the main loop must complete even while the writer thread
    /// is stuck on a full stdout pipe. Pre-fix, the rendezvous handoff
    /// blocks forever the moment the writer is busy.
    #[test]
    fn sender_send_does_not_block_when_writer_is_stuck() {
        let (in_r, _in_w) = io::pipe().unwrap();
        let (out_r, out_w) = io::pipe().unwrap();
        let (sender, _receiver, _threads) = transport(in_r, out_w);

        // Stuff a frame larger than any pipe buffer through the writer and
        // never read the output pipe: the writer thread blocks mid-write.
        let big = Message::Notification(Notification::new(
            "textDocument/publishDiagnostics".to_owned(),
            json!({ "uri": "file:///big.typort", "diagnostics": [{ "message": "x".repeat(1024 * 1024) }] }),
        ));
        sender.send(big).unwrap();

        // A second send must complete immediately. Pre-fix it rendezvous-
        // blocks: the writer thread is inside `write`, not `recv`.
        let small = Message::Notification(Notification::new(
            "window/logMessage".to_owned(),
            json!({ "type": 4, "message": "ping" }),
        ));
        let (done_tx, done_rx) = crossbeam_channel::unbounded();
        thread::spawn(move || {
            let result = sender.send(small);
            let _ = done_tx.send(result);
        });
        match done_rx.recv_timeout(Duration::from_secs(10)) {
            Ok(Ok(())) => {}
            Ok(Err(e)) => panic!("send failed: {e:?}"),
            Err(_) => panic!(
                "connection send blocked while the writer thread is busy \
                 (rendezvous deadlock)"
            ),
        }

        // Cleanup: breaking the output pipe unblocks the writer thread.
        drop(out_r);
    }
}
