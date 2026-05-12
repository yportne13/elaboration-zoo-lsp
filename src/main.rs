use std::error::Error;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    elaboration_zoo_lsp::run_lsp_server()
}
