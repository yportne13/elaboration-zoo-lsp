# LSP Server Architecture

## Text Sync: Why Incremental

**2026-06-02** — Switched from `TextDocumentSyncKind::FULL` to `INCREMENTAL`.

### Problem

The LSP server communicates with VS Code (or the web demo) over stdio. In the WASM
(web demo) build, stdio is implemented via a `SharedArrayBuffer` ring buffer — the
LSP wire format (Content-Length headers + JSON bodies) is serialized into this
buffer and read by the client.

When the document is large (e.g. 1000+ lines), each `didChange` notification under
**Full** sync sends the **entire document text** as a single message. The large
message can overflow or misalign the shared buffer, causing **framing errors**
(commonly called "粘包" — packet sticking/tearing). Consequence: multiple rapid
edits cause the LSP connection to corrupt and the web demo hangs.

### Solution

Switch to **Incremental** sync:
- Client sends only the changed `range` + `text` on each edit, not the whole file
- Server maintains a `document_buffers: HashMap<String, String>` to store the
  full document text per URI
- On `didOpen`: store full text from the notification
- On `didChange`: apply the incremental edit (using `Rope` for position/offset
  conversion) to the stored buffer, then pass the reconstructed full text to the
  analysis worker
- On `didClose`: clean up the buffer

This dramatically reduces per-edit message size (~100 bytes instead of ~100 KB
for a large file), eliminating shared buffer overflows in the WASM transport.

### Trade-offs
- Server must maintain its own document copy (one extra `String` per open file)
- Position/offset conversion requires UTF-16 → byte offset mapping (already
  handled by `position_to_offset` / `offset_to_position` in `lib.rs`)

---

## Stdio Wire Monitor

**2026-06-02** — Added debugging support for LSP wire format inspection.

When debugging LSP protocol issues (especially shared-buffer framing), enable
the `stdio-monitor` feature:

```bash
cargo build --features stdio-monitor
```

This creates proxy threads that dump every LSP message (both directions) to
stderr with full Content-Length headers and JSON bodies. Useful for diagnosing
framing errors, malformed messages, or unexpected server responses.

See `create_monitored_connection()` in `lib.rs`.

---

## Quick Fix (Code Actions)

The server supports code actions via the `typort.applyQuickFix` command.

- Diagnostics with associated fixes store a unique ID in `diagnostic.data`
- `codeAction` request returns a "Search solution" action linking to the fix
- `workspace/executeCommand` with `typort.applyQuickFix` executes the fix
  closure and displays the result via `window/showMessage`

Disabled in commit `d003e52` (2026-05-26), restored in `33bea4c` (2026-06-02).
