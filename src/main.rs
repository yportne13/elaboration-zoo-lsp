use std::error::Error;
use std::fs;

use elaboration_zoo_lsp::client::{Client, ClientLike};
use elaboration_zoo_lsp::Backend;
use lsp_server::Connection;

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
    let backend = Backend::new(Client { connection });
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
