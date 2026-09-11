//! Minimal static file server for `typort doc --serve`.
//!
//! Single-threaded, loopback-only, no directory listing: enough to preview a
//! generated site over HTTP without adding a dependency.

use std::io::{BufRead, BufReader, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::path::{Path, PathBuf};

pub struct Server {
    listener: TcpListener,
    pub addr: SocketAddr,
}

pub fn bind(port: u16) -> Result<Server, String> {
    let listener = TcpListener::bind(("127.0.0.1", port))
        .map_err(|e| format!("binding 127.0.0.1:{port}: {e}"))?;
    let addr = listener.local_addr().map_err(|e| e.to_string())?;
    Ok(Server { listener, addr })
}

pub fn serve(root: &Path, server: Server) -> Result<(), String> {
    for stream in server.listener.incoming() {
        let Ok(stream) = stream else { continue };
        let _ = handle(stream, root);
    }
    Ok(())
}

fn handle(mut stream: TcpStream, root: &Path) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut request_line = String::new();
    if reader.read_line(&mut request_line)? == 0 {
        return Ok(());
    }
    // Drain headers up to the blank line.
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 || line == "\r\n" || line == "\n" {
            break;
        }
    }
    let target = request_line.split_whitespace().nth(1).unwrap_or("/");
    let path = target.split(['?', '#']).next().unwrap_or("/");
    let mut path = path.trim_start_matches('/').to_string();
    if path.is_empty() {
        path = "index.html".to_string();
    }

    match resolve(root, &path) {
        Some(file) => {
            let body = std::fs::read(&file)?;
            let ctype = content_type(&file);
            write!(
                stream,
                "HTTP/1.1 200 OK\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
                body.len()
            )?;
            stream.write_all(&body)?;
        }
        None => {
            let body = b"404 Not Found";
            write!(
                stream,
                "HTTP/1.1 404 Not Found\r\nContent-Type: text/plain\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                body.len()
            )?;
            stream.write_all(body)?;
        }
    }
    stream.flush()
}

/// Resolve a URL path inside `root`, refusing traversal outside it.
fn resolve(root: &Path, path: &str) -> Option<PathBuf> {
    if path.split('/').any(|seg| seg == "..") {
        return None;
    }
    let candidate = root.join(path);
    let root = root.canonicalize().ok()?;
    let candidate = candidate.canonicalize().ok()?;
    if candidate.starts_with(&root) && candidate.is_file() {
        Some(candidate)
    } else {
        None
    }
}

fn content_type(path: &Path) -> &'static str {
    match path.extension().and_then(|e| e.to_str()) {
        Some("html") | Some("htm") => "text/html; charset=utf-8",
        Some("css") => "text/css; charset=utf-8",
        Some("js") => "text/javascript; charset=utf-8",
        Some("json") => "application/json; charset=utf-8",
        Some("svg") => "image/svg+xml",
        Some("png") => "image/png",
        _ => "text/plain; charset=utf-8",
    }
}
