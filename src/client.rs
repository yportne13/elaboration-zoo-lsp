use lsp_server::Connection;
use lsp_types::{notification::ShowMessage, *};
use notification::{LogMessage, Notification, PublishDiagnostics};

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
pub struct CliClient;

impl ClientLike for CliClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
        eprintln!("Diagnostics for {} (version {:?}):", uri.as_str(), version);
        for d in &diagnostics {
            let range = &d.range;
            eprintln!(
                "  {:?} {}:{} - {}:{}: {}",
                d.severity,
                range.start.line,
                range.start.character,
                range.end.line,
                range.end.character,
                d.message
            );
        }
    }
    fn show_message(&self, typ: MessageType, message: String) {
        eprintln!("[{:?}] {}", typ, message);
    }
    fn log_message(&self, typ: MessageType, message: String) {
        eprintln!("[LOG {:?}] {}", typ, message);
    }
}
