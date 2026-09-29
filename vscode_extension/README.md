# TyportHDL

VS Code extension for the [Typort](https://github.com/yportne13/elaboration-zoo-lsp) language — a dependently typed language that elaborates to HDL (Verilog/VHDL). Provides LSP-powered hover, completion, diagnostics and macro expansion for `.typort` files.

## Language server backends

The extension ships two backends, selected by the `typort-hdl.lsp-mode` setting:

- **wasm** (default): the bundled WebAssembly server (`client/server.wasm`, built for `wasm32-wasip1-threads`). Works on desktop and on the web (vscode.dev); requires the [ms-vscode.wasm-wasi-core](https://marketplace.visualstudio.com/items?itemName=ms-vscode.wasm-wasi-core) extension, which is installed automatically as an extension dependency.
- **cli**: an external `typort` binary (desktop only). Set `typort-hdl.cli-server.path` to the binary, or leave it empty to look up `typort` in `PATH`.

## Elaboration engine

`typort-hdl.cli-server.engine` picks the elaboration engine (it sets `TYPORT_LSP_ENGINE` for the server):

- **reference** — the reference elaborator; default on the web/wasm backend (lower memory, fits the wasm 2 GiB linear-memory ceiling).
- **twin** — the L13 twin elaborator; default on the desktop CLI backend (~3.8x faster per edit and faster startup, at ~2x memory). Files with project imports or twin-unsupported constructs fall back to the reference engine automatically.

An explicit setting overrides the host default on both backends.

## Diagnostics trace

`typort-language-server.trace.server` traces LSP communication between VS Code and the server (`off` / `messages` / `verbose`).

## Building

Requirements: Node.js 20, a Rust toolchain with the `wasm32-wasip1-threads` target.

```sh
npm install        # also installs client dependencies (postinstall)
npm run build      # compiles the client and cross-builds server.wasm
npx vsce package   # packs the .vsix
```
