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
//! reader/writer threads and rendezvous channels) but wraps stdin/stdout in
//! [`ChunkedReader`] / [`ChunkedWriter`] so every underlying read/write call
//! is at most [`CHUNK`] bytes. The `BufRead`/`Write`-level framing is
//! unchanged, so the wire protocol and desktop behavior are identical.

use std::io::{self, Read, Write};
use std::thread;

use crossbeam_channel::{bounded, Receiver, Sender};
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
fn stdio_transport() -> (Sender<Message>, Receiver<Message>, IoThreads) {
    let (writer_sender, writer_receiver) = bounded::<Message>(0);
    let writer = thread::Builder::new()
        .name("LspServerWriter".to_owned())
        .spawn(move || {
            let stdout = io::stdout();
            let stdout = stdout.lock();
            let mut stdout = ChunkedWriter::new(stdout, CHUNK);
            writer_receiver.into_iter().try_for_each(|it| it.write(&mut stdout))
        })
        .unwrap();
    let (reader_sender, reader_receiver) = bounded::<Message>(0);
    let reader = thread::Builder::new()
        .name("LspServerReader".to_owned())
        .spawn(move || {
            let stdin = io::stdin();
            let stdin = stdin.lock();
            let mut stdin = io::BufReader::new(ChunkedReader::new(stdin, CHUNK));
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
    use super::{ChunkedReader, ChunkedWriter, CHUNK};
    use lsp_server::{Message, Notification};
    use serde_json::json;
    use std::io::{self, BufReader, Read, Write};
    use std::thread;

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
}
