#!/usr/bin/env python3
# Drive the real `typort lsp` CLI over stdio and issue textDocument/hover
# requests — validates the SHIPPED binary over the real LSP wire protocol.
#
# Uses standard LSP Content-Length framing, with hard timeouts on every
# read so this script can never hang the caller.
import json, subprocess, sys, os, tempfile, time, queue, threading

# Validate the hover member-list feature over the real LSP wire protocol.
# Usage:  python tools/lsp_hover_probe.py [path-to-typort-binary]
# Env:    TYPORT_LSP_PROBE_READ_TIMEOUT  (per-request timeout, default 60)
#         TYPORT_LSP_PROBE_DEBUG=1       (print server notifications)
DEFAULT_SERVER = r"F:\projects\hermes\elaboration-zoo-lsp\target\release\typort.exe"
SERVER = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_SERVER
READ_TIMEOUT = float(os.environ.get("TYPORT_LSP_PROBE_READ_TIMEOUT", "60"))
BOOT_GRACE    = 0.5   # brief pause; the didOpen job drains in the request arm

class FrameReader(threading.Thread):
    """Dedicated reader thread: parses Content-Length frames off stdout and
    pushes (obj, error) to a queue.  Blocking reads live here; the main
    thread only ever does queue.get(timeout=...) so it can never hang."""
    def __init__(self, f):
        super().__init__(daemon=True)
        self.f = f
        self.q = queue.Queue()

    def _read_exact(self, n):
        buf = b""
        while len(buf) < n:
            c = os.read(self.f, n - len(buf))
            if not c:
                return None
            buf += c
        return buf

    def run(self):
        try:
            while True:
                # read headers
                h = b""
                while b"\r\n\r\n" not in h:
                    c = self._read_exact(1)
                    if c is None:
                        self.q.put((None, "EOF"))
                        return
                    h += c
                length = 0
                for line in h.decode(errors="replace").split("\r\n"):
                    if line.lower().startswith("content-length:"):
                        length = int(line.split(":", 1)[1].strip())
                body = self._read_exact(length)
                if body is None:
                    self.q.put((None, "EOF"))
                    return
                self.q.put((json.loads(body), None))
        except Exception as e:  # pragma: no cover
            self.q.put((None, repr(e)))

def msg(obj):
    body = json.dumps(obj, separators=(",", ":")).encode()
    return (f"Content-Length: {len(body)}\r\n\r\n").encode() + body

def recv(q, deadline):
    """Pop one frame with a hard deadline via queue.get(timeout=...)."""
    remaining = deadline - time.time()
    if remaining <= 0:
        return None, "timeout"
    try:
        return q.get(timeout=remaining)
    except queue.Empty:
        return None, "timeout"

def main():
    ws = tempfile.mkdtemp(prefix="typort_ws_")
    src = ("/// 颜色。\n"
           "enum Color {\n"
           "    red\n"
           "    green(weight: Nat)\n"
           "}\n"
           "\n"
           "def pick(c: Color): Nat = match c {\n"
           "    case red => 0\n"
           "    case green(w) => w\n"
           "}\n")
    uri = "file:///" + os.path.join(ws, "main.typort").replace("\\", "/")
    with open(uri.replace("file:///", ""), "w", encoding="utf-8") as f:
        f.write(src)

    p = subprocess.Popen([SERVER, "lsp"], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    reader = FrameReader(p.stdout.fileno())
    reader.start()
    req_id = 0
    global_deadline = time.time() + 120

    def send_raw(obj):
        p.stdin.write(msg(obj))
        p.stdin.flush()

    def send_notification(method, params):
        send_raw({"jsonrpc": "2.0", "method": method, "params": params})

    def rpc_request(method, params, timeout=READ_TIMEOUT):
        nonlocal req_id
        i = req_id
        req_id += 1
        send_raw({"jsonrpc": "2.0", "id": i, "method": method, "params": params})
        deadline = min(time.time() + timeout, global_deadline)
        while True:
            obj, err = recv(reader.q, deadline)
            if err:
                return {"_transport_error": err}
            if obj is None:
                return {"_transport_error": "no frame"}
            if obj.get("id") == i:
                return obj
            # drain notifications
            if "method" in obj and os.environ.get("TYPORT_LSP_PROBE_DEBUG"):
                print(f"  [notif] {obj['method']} params={json.dumps(obj.get('params'), ensure_ascii=False)[:200]}", flush=True)

    r = rpc_request("initialize", {
        "processId": None, "rootUri": "file:///" + ws.replace("\\", "/"),
        "capabilities": {}, "workspaceFolders": [],
    })
    if "error" in r:
        print("initialize ERROR:", json.dumps(r["error"], ensure_ascii=False)); sys.exit(1)
    if "_transport_error" in r:
        print("initialize TRANSPORT:", r["_transport_error"]); sys.exit(1)
    print("initialize: ok (server pid", p.pid, ")")

    send_notification("initialized", {})
    send_notification("textDocument/didOpen", {
        "textDocument": {"uri": uri, "languageId": "typort", "version": 1, "text": src},
    })
    print(f"didOpen sent; sleeping {BOOT_GRACE}s for prelude load...")
    time.sleep(BOOT_GRACE)

    lines = src.split("\n")
    line_pick = lines.index("def pick(c: Color): Nat = match c {")
    col_color = lines[line_pick].find("Color")
    r = rpc_request("textDocument/hover", {
        "textDocument": {"uri": uri},
        "position": {"line": line_pick, "character": col_color},
    })
    print("=== hover on `Color` in `def pick` ===")
    if "_transport_error" in r:
        print("TRANSPORT:", r["_transport_error"])
    else:
        print(json.dumps(r.get("result"), ensure_ascii=False, indent=2))

    # hover on the enum's own def name (line 1, char 6 = 'Color'), expect docs too
    r = rpc_request("textDocument/hover", {
        "textDocument": {"uri": uri},
        "position": {"line": 1, "character": 6},
    })
    print("=== hover on `Color` def name (should carry /// docs) ===")
    if "_transport_error" in r:
        print("TRANSPORT:", r["_transport_error"])
    else:
        print(json.dumps(r.get("result"), ensure_ascii=False, indent=2))

    # hover on `Nat` in the `: Nat` return type of def pick
    col_nat = lines[line_pick].rfind("Nat")
    r = rpc_request("textDocument/hover", {
        "textDocument": {"uri": uri},
        "position": {"line": line_pick, "character": col_nat},
    })
    print("=== hover on `Nat` return type ===")
    if "_transport_error" in r:
        print("TRANSPORT:", r["_transport_error"])
    else:
        print(json.dumps(r.get("result"), ensure_ascii=False, indent=2))

    # sanity: definition + completion should also resolve if analysis ran
    r = rpc_request("textDocument/definition", {
        "textDocument": {"uri": uri},
        "position": {"line": line_pick, "character": col_color},
    })
    print("=== definition on `Color` ===")
    if "_transport_error" in r:
        print("TRANSPORT:", r["_transport_error"])
    else:
        print(json.dumps(r.get("result"), ensure_ascii=False, indent=2))

    r = rpc_request("textDocument/completion", {
        "textDocument": {"uri": uri},
        "position": {"line": line_pick, "character": len(lines[line_pick])},
        "context": {"triggerKind": 1},
    })
    print("=== completion at end of `def pick` body line ===")
    if "_transport_error" in r:
        print("TRANSPORT:", r["_transport_error"])
    else:
        res = r.get("result")
        if isinstance(res, dict):
            res = res.get("items", res)
        print(json.dumps(res, ensure_ascii=False)[:400])

    try:
        p.stdin.close()
        p.wait(timeout=10)
    except Exception as e:
        print("(server didn't exit cleanly:", e, ")")
        p.kill()
    errs = p.stderr.read().decode(errors="replace")
    if errs.strip():
        print("=== stderr (tail) ===")
        print("\n".join(errs.strip().splitlines()[-15:]))

if __name__ == "__main__":
    main()
