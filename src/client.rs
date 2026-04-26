use std::sync::Arc;

use codespan_reporting::{
    diagnostic::{Diagnostic as CsDiagnostic, Label, Severity as CsSeverity},
    files::SimpleFiles,
    term::{self, termcolor::{ColorChoice, StandardStream}},
};
use dashmap::DashMap;
use lsp_server::Connection;
use lsp_types::{notification::ShowMessage, *};
use notification::{LogMessage, Notification, PublishDiagnostics};

/// Convert LSP Position (line, character) to byte offset in source text.
fn position_to_byte_offset(text: &str, position: Position) -> Option<usize> {
    let mut offset = 0usize;
    for _ in 0..position.line {
        let rest = text.get(offset..)?;
        let newline_pos = rest.find('\n')?;
        offset += newline_pos + 1;
    }
    // At the correct line, advance by character offset
    let line_rest = text.get(offset..)?;
    let mut char_count = 0u32;
    for (i, _) in line_rest.char_indices() {
        if char_count == position.character {
            return Some(offset + i);
        }
        char_count += 1;
    }
    // If position is at end of line
    if char_count == position.character {
        Some(offset + line_rest.len())
    } else {
        None
    }
}

/// Trait that abstracts the client-side operations.
/// LSP client and CLI client both implement this trait.
pub trait ClientLike: Send + Sync {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>);
    fn show_message(&self, typ: MessageType, message: String);
    fn log_message(&self, typ: MessageType, message: String);
}

/// LSP client: sends notifications/messages via the LSP connection.
pub struct Client {
    pub connection: Connection,
}

impl ClientLike for Client {
    fn log_message(&self, typ: MessageType, message: String) {
        self.connection
            .sender
            .send(lsp_server::Message::Notification(
                lsp_server::Notification::new(
                    LogMessage::METHOD.to_owned(),
                    LogMessageParams {
                        typ,
                        message,
                    },
                ),
            ))
            .unwrap();
    }
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
        self.connection
            .sender
            .send(lsp_server::Message::Notification(
                lsp_server::Notification::new(
                    PublishDiagnostics::METHOD.to_owned(),
                    PublishDiagnosticsParams {
                        uri,
                        diagnostics,
                        version,
                    },
                ),
            ))
            .unwrap();
    }
    fn show_message(&self, typ: MessageType, message: String) {
        self.connection
            .sender
            .send(lsp_server::Message::Notification(
                lsp_server::Notification::new(
                    ShowMessage::METHOD.to_owned(),
                    ShowMessageParams {
                        typ,
                        message,
                    }
                )
            ))
            .unwrap();
    }
}

/// CLI client: prints diagnostics and messages to stderr/stdout.
/// Uses codespan-reporting for Rust-compiler-style error formatting.
pub struct CliClient {
    /// Maps URI string -> source text, used to render diagnostics with source context.
    pub source_map: Arc<DashMap<String, String>>,
}

impl CliClient {
    pub fn new() -> Self {
        CliClient {
            source_map: Arc::new(DashMap::new()),
        }
    }
}

impl ClientLike for CliClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
        let uri_str = uri.as_str().to_string();
        let source_text = self.source_map.get(&uri_str);

        if source_text.is_none() || diagnostics.is_empty() {
            // No source available or no diagnostics, just print a summary
            if !diagnostics.is_empty() {
                eprintln!("Diagnostics for {}:", uri.as_str());
                for d in &diagnostics {
                    eprintln!("  {:?}: {}", d.severity, d.message);
                }
            }
            return;
        }

        let source_text_ref = source_text.unwrap();
        let mut files = SimpleFiles::new();

        // Use the file path from the URI for display
        let file_path = uri.path();
        let file_id = files.add(file_path, source_text_ref.value().as_str());

        let cs_diags: Vec<CsDiagnostic<usize>> = diagnostics
            .iter()
            .filter_map(|d| {
                let severity = match d.severity {
                    Some(DiagnosticSeverity::ERROR) => CsSeverity::Error,
                    Some(DiagnosticSeverity::WARNING) => CsSeverity::Warning,
                    Some(DiagnosticSeverity::INFORMATION) => CsSeverity::Note,
                    Some(DiagnosticSeverity::HINT) => CsSeverity::Help,
                    _ => CsSeverity::Error,
                };

                let start_offset =
                    position_to_byte_offset(source_text_ref.value(), d.range.start)?;
                let end_offset =
                    position_to_byte_offset(source_text_ref.value(), d.range.end)?;

                Some(
                    CsDiagnostic::new(severity)
                        .with_message(d.message.clone())
                        .with_labels(vec![Label::primary(file_id, start_offset..end_offset)])
                        .with_notes(
                            d.related_information
                                .as_ref()
                                .map(|info| {
                                    info.iter()
                                        .map(|ri| {
                                            format!(
                                                "note: {} {}:{}:{}",
                                                ri.message,
                                                ri.location.uri.as_str(),
                                                ri.location.range.start.line,
                                                ri.location.range.start.character,
                                            )
                                        })
                                        .collect()
                                })
                                .unwrap_or_default(),
                        ),
                )
            })
            .collect();

        if cs_diags.is_empty() {
            return;
        }

        let config = term::Config::default();
        let mut writer = StandardStream::stderr(ColorChoice::Auto);
        for cs_diag in &cs_diags {
            term::emit(&mut writer, &config, &files, cs_diag).unwrap();
        }
    }

    fn show_message(&self, typ: MessageType, message: String) {
        let prefix = match typ {
            MessageType::ERROR => "error",
            MessageType::WARNING => "warning",
            MessageType::INFO => "info",
            MessageType::LOG => "log",
            _ => "unknown",
        };
        eprintln!("[{}] {}", prefix, message);
    }

    fn log_message(&self, typ: MessageType, message: String) {
        let prefix = match typ {
            MessageType::ERROR => "LOG error",
            MessageType::WARNING => "LOG warning",
            MessageType::INFO => "LOG info",
            MessageType::LOG => "LOG log",
            _ => "LOG unknown",
        };
        eprintln!("[{}] {}", prefix, message);
    }
}
