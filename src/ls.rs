
use std::fmt::Display;

use lsp_types::*;
use serde_json::Value;

/// A JSON-RPC error object.
#[derive(Clone, Debug)]
/// #[serde(deny_unknown_fields)]
pub struct Error {}

impl Error {
    fn method_not_found() -> Self {
        Error {}
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

pub trait LanguageServer {
    fn initialize(&self, params: InitializeParams) -> Result<InitializeResult>;

    fn initialized(&self, params: InitializedParams) {
        let _ = params;
    }

    fn shutdown(&self) -> Result<()>;

    fn did_open(&mut self, params: DidOpenTextDocumentParams) {
        let _ = params;
    }

    fn did_change(&mut self, params: DidChangeTextDocumentParams) {
        let _ = params;
    }

    fn did_save(&mut self, params: DidSaveTextDocumentParams) {
        let _ = params;
    }

    fn did_close(&self, params: DidCloseTextDocumentParams) {
        let _ = params;
    }

    fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let _ = params;
        //error!("Got a textDocument/definition request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let _ = params;
        //error!("Got a textDocument/references request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn semantic_tokens_full(
        &mut self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let _ = params;
        //error!("Got a textDocument/semanticTokens/full request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn semantic_tokens_range(
        &self,
        params: SemanticTokensRangeParams,
    ) -> Result<Option<SemanticTokensRangeResult>> {
        let _ = params;
        //error!("Got a textDocument/semanticTokens/range request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn inlay_hint(
        &self,
        params: lsp_types::InlayHintParams,
    ) -> Result<Option<Vec<InlayHint>>> {
        let _ = params;
        //error!("Got a textDocument/inlayHint request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let _ = params;
        //error!("Got a textDocument/completion request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let _ = params;
        //error!("Got a textDocument/rename request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn did_change_configuration(&self, _: DidChangeConfigurationParams) {
        //error!("Got a workspace/didChangeConfiguration request, but it is not implemented");
    }

    fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {
        //error!("Got a workspace/didChangeWorkspaceFolders request, but it is not implemented");
    }

    fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
        //error!("Got a workspace/didChangeWatchedFiles request, but it is not implemented");
    }

    fn execute_command(&self, _: ExecuteCommandParams) -> Result<Option<Value>> {
        //error!("Got a workspace/executeCommand request, but it is not implemented");
        Err(Error::method_not_found())
    }

    fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let _ = params;
        //error!("Got a textDocument/hover request, but it is not implemented");
        Err(Error::method_not_found())
    }
}
