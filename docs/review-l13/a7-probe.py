#!/usr/bin/env python3
"""A7 R2 probe harness for the two LSP process-lifecycle fixes (no cargo needed).

Usage (from the review worktree root, Python 3.10+):

  python docs/review-l13/a7-probe.py <exe> shutdown [engine]
  python docs/review-l13/a7-probe.py <exe> open <file.typort> [engine]
  python docs/review-l13/a7-probe.py <exe> builtin [engine]

  <exe>    path to a freshly built LSP server binary, e.g.
           target\\release\\elaboration-zoo-lsp.exe   (src/main.rs -> run_lsp_server)
           target\\release\\typort.exe   with args "lsp" (use the TYPORT_EXE_ARGS env var)
  engine   optional TYPORT_LSP_ENGINE value: "twin" (LSP default) or "reference"

Modes:
  shutdown  initialize -> initialized -> shutdown -> exit, then assert the
            process exits BY ITSELF within 20 s with code 0.
            BEFORE A7's fix this hangs forever (writer channel never
            disconnects because Arc<Backend> keeps Connection.sender alive).
  open      initialize -> initialized -> didOpen(<file>), then wait up to 120 s
            for the process to exit on its own.  A panic inside main_loop must
            surface as exit code 1 ("main loop panicked: ..." on stderr);
            BEFORE A7's fix it was caught, then the process hung (join on a
            writer that never finishes).  Exit 0 = fix regressed.
  builtin   same as `open` but opens a builtin:/// URI (no file needed) --
            smoke test that the harness itself works and the server is live.

Exit status of this script: 0 = expectation met, 2 = expectation violated,
3 = watchdog killed the server (hang), 1 = harness/setup error.
"""

import json
import os
import subprocess
import sys
import tempfile
import threading
import time

EXE = None
ARGS = []
MODE = "shutdown"
FILE = None
ENGINE = None
STDERR_LOG = None

# Fixture from tests/l13_fast_parity.rs:697-743
# (`parity_into_add_nat_uint_field_projection`): documented to panic in BOTH
# engines (reference: hardened `lvl2ix` diagnostic; twin: same message after
# bump_spine_iter/syntax.rs::lvl2ix hardening).  Under the real LSP path the
# full prelude is loaded, so reproduction is *not* guaranteed -- reported as
# needs-verify; see docs/review-l13/a7-r2.md.
LVL2IX_SRC = r'''def outParam[A](a: A): A = a
enum Nat {
    zero
    succ(n: Nat)
}
enum Expr {
    binary(lhs: Expr, op: String, rhs: Expr)
    literal(v: Nat)
}
enum Option[A] {
    none
    some(a: A)
}
def nat_add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (nat_add n y)
    }
trait Add[T, O: outParam(Type 0)] {
    def +(that: T): O
}
trait Into[O: outParam(Type 0)] {
    def into: O
}
struct UInt[width: Nat] {
    name: Option[String]
    zz_expr: Expr
}
def binary(lhs: Expr, op: String, rhs: Expr): Expr = Expr.binary(lhs, op, rhs)
impl[T] Into[T] for T {
    def into: T = this
}
impl[width: Nat] Into[UInt[width]] for Nat {
    def into: UInt[width] = UInt.mk(none, literal(this))
}
impl Add[Nat, Nat] for Nat {
    def +(that: Nat): Nat = nat_add this that
}
impl[width: Nat] Add[UInt[width], UInt[width]] for UInt[width] {
    def +(that: UInt[width]): UInt[width] = UInt.mk(none, binary(this.zz_expr, "+", that.zz_expr))
}
impl[width: Nat] Add[Nat, UInt[width]] for UInt[width] {
    def +(that: Nat): UInt[width] = this + that.into
}
def u: UInt[succ zero] = UInt.mk(none, literal(zero))
def lifted: UInt[succ zero] = u + (succ zero)
println lifted
'''


def log(msg):
    print("[probe] %s" % msg, flush=True)


def frame(obj):
    body = json.dumps(obj).encode("utf-8")
    return b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body


def read_msg(proc, timeout):
    """Read one LSP frame; returns dict, or None on EOF/timeout."""
    deadline = time.time() + timeout
    n = None
    while True:
        if time.time() > deadline:
            return None
        line = proc.stdout.readline()
        if not line:
            return None
        if line.strip() == b"":
            break
        low = line.lower()
        if low.startswith(b"content-length:"):
            n = int(line.split(b":", 1)[1].strip())
    if n is None:
        return None
    body = b""
    while len(body) < n:
        chunk = proc.stdout.read(n - len(body))
        if not chunk:
            return None
        body += chunk
    try:
        return json.loads(body)
    except Exception:
        return {"raw": body[:200].decode("utf-8", "replace")}


def send(proc, obj):
    proc.stdin.write(frame(obj))
    proc.stdin.flush()


def watchdog(proc, secs):
    def kill():
        if proc.poll() is None:
            log("WATCHDOG: killing server after %ss (it never exited)" % secs)
            try:
                proc.kill()
            except Exception:
                pass
    t = threading.Timer(secs, kill)
    t.daemon = True
    t.start()
    return t


def main():
    global EXE, ARGS, MODE, FILE, ENGINE, STDERR_LOG
    if len(sys.argv) < 3:
        print(__doc__)
        return 1
    EXE = sys.argv[1]
    MODE = sys.argv[2]
    rest = sys.argv[3:]
    if MODE == "open":
        if not rest:
            print("mode `open` needs a .typort path")
            return 1
        FILE = rest.pop(0)
    if rest:
        ENGINE = rest.pop(0)
    ARGS = os.environ.get("TYPORT_EXE_ARGS", "").split()

    env = dict(os.environ)
    if ENGINE:
        env["TYPORT_LSP_ENGINE"] = ENGINE
    else:
        env.pop("TYPORT_LSP_ENGINE", None)

    STDERR_LOG = os.path.join(tempfile.gettempdir(), "a7_probe_stderr.log")
    errf = open(STDERR_LOG, "wb")
    cmd = [EXE] + ARGS
    log("exec: %s (TYPORT_LSP_ENGINE=%s)" % (" ".join(cmd), env.get("TYPORT_LSP_ENGINE", "<unset>")))
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errf, env=env)

    total = 20 if MODE == "shutdown" else 150
    # Safety net only (handshake phase): fire AFTER proc.wait()'s own timeout,
    # so a hang is reported as TimeoutExpired (clear message) and not as a
    # killed process with a confusing negative rc.
    wd = watchdog(proc, total + 15)

    try:
        # ---- initialize handshake (lsp-server 0.7.9: the response to
        # `initialize` is sent, then the server blocks waiting for the
        # `initialized` notification before init() returns -- without it the
        # main loop never runs.  Verified in lsp-server-0.7.9/src/lib.rs.)
        send(proc, {"jsonrpc": "2.0", "id": 1, "method": "initialize",
                    "params": {"capabilities": {}, "processId": None,
                               "rootUri": None, "workspaceFolders": []}})
        while True:
            m = read_msg(proc, 30)
            if m is None:
                log("FAIL: no response to initialize (server died or stdin closed)")
                return 1
            if m.get("id") == 1:
                break
        log("initialize answered")

        send(proc, {"jsonrpc": "2.0", "method": "initialized", "params": {}})
        time.sleep(0.5)  # let load_prelude() finish (twin prime can take ~3 s)

        if MODE == "builtin" or MODE == "open":
            if MODE == "builtin":
                req = {"jsonrpc": "2.0", "id": 99, "method": "typort-hdl/builtinContent",
                       "params": {"uri": "builtin:///op.typort"}}
                send(proc, req)
                while True:
                    m = read_msg(proc, 60)
                    if m is None:
                        log("FAIL: no response to builtinContent (server died)")
                        return 1
                    if m.get("id") == 99:
                        break
                log("builtinContent answered -> harness OK; server is alive")
                rc = proc.poll()
                log("server still running (rc=%s) -- killing it" % rc)
                proc.kill()
                proc.wait()
                return 0
            src = open(FILE, "r", encoding="utf-8").read()
            uri = "file:///" + os.path.basename(FILE).replace(" ", "_")
            send(proc, {"jsonrpc": "2.0", "method": "textDocument/didOpen",
                        "params": {"textDocument": {"uri": uri, "languageId": "typort",
                                                    "version": 1, "text": src}}})
            log("didOpen sent (%d bytes, uri=%s)" % (len(src), uri))
        elif MODE == "shutdown":
            pass
        else:
            log("unknown mode %s" % MODE)
            return 1

        if MODE == "shutdown":
            send(proc, {"jsonrpc": "2.0", "id": 2, "method": "shutdown", "params": None})
            while True:
                m = read_msg(proc, 30)
                if m is None:
                    log("FAIL: no response to shutdown")
                    return 1
                if m.get("id") == 2:
                    break
            send(proc, {"jsonrpc": "2.0", "method": "exit", "params": None})
            log("shutdown+exit sent; waiting up to 20s for the process to exit by itself")

        t0 = time.time()
        try:
            rc = proc.wait(timeout=total)
            wd.cancel()
            dt = time.time() - t0
            log("process exited rc=%s after %.1fs" % (rc, dt))
            errf.flush()
            with open(STDERR_LOG, "r", encoding="utf-8", errors="replace") as f:
                tail = f.read().strip().splitlines()[-12:]
            if tail:
                log("stderr tail:")
                for line in tail:
                    print("    " + line)
            if MODE == "shutdown":
                if rc == 0:
                    log("PASS: clean shutdown exits 0 by itself (P1-1 fix holds)")
                    return 0
                log("FAIL: clean shutdown exited with rc=%s (expected 0)" % rc)
                return 2
            # open mode: a main_loop panic must be visible as rc != 0
            if rc == 0:
                log("FAIL: didOpen path exited 0 -- either it did NOT panic, or the "
                    "panic was swallowed again (P1-2 regressed). Check stderr tail.")
                return 2
            log("PASS: non-zero exit rc=%s (panic surfaced; P1-2 fix holds)" % rc)
            return 0
        except subprocess.TimeoutExpired:
            wd.cancel()
            log("FAIL/HANG: process still alive after %ss" % total)
            try:
                proc.kill()
                proc.wait()
            except Exception:
                pass
            return 3
    finally:
        try:
            errf.close()
        except Exception:
            pass


if __name__ == "__main__":
    sys.exit(main())
