use std::error::Error;
use std::fs;
use std::path::PathBuf;

use elaboration_zoo_lsp::Backend;
use elaboration_zoo_lsp::client::{CliClient, ClientLike};
use elaboration_zoo_lsp::TextDocumentItem;
use lsp_types::Url;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: typort <file.typort> [<file2.typort> ...]");
        std::process::exit(1);
    }

    // Create backend with CLI client.
    // Backend::new loads the builtin prelude, sets up Infer/Cxt.
    let backend = Backend::new(CliClient);

    for filepath in &args[1..] {
        let path = PathBuf::from(filepath);
        let contents = fs::read_to_string(&path)?;
        let uri = Url::from_file_path(path.canonicalize()?).unwrap();

        eprintln!("Analyzing: {} ({} bytes)", uri.as_str(), contents.len());

        // Run the analysis pipeline (parse + infer + diagnostics).
        backend.on_change::<false>(TextDocumentItem {
            uri: uri.clone(),
            text: &contents,
            version: None,
        });

        // Print inferred results
        if let Some(type_map) = backend.type_map.get(uri.as_str()) {
            println!("\n=== Inferred definitions in {} ===", filepath);
            for tm in type_map.iter() {
                match tm {
                    elaboration_zoo_lsp::L12_canonical::DeclTm::Def { name, typ_pretty, body_pretty, .. } => {
                        println!("  {} : {}", name.data, typ_pretty);
                        println!("    = {}", body_pretty);
                    }
                    elaboration_zoo_lsp::L12_canonical::DeclTm::Println(_, s, _) => {
                        println!("  println: {}", s);
                    }
                    _ => {
                        println!("  {:?}", tm);
                    }
                }
            }
        }

        // Print hover info (type of each expression)
        if let Some(hover_table) = backend.hover_table.get(uri.as_str()) {
            if !hover_table.hover_table.is_empty() {
                println!("\n=== Hover info ===");
                for (span, def_span, cxt, val) in &hover_table.hover_table {
                    let pretty = elaboration_zoo_lsp::L12_canonical::pretty::pretty_tm(
                        0,
                        cxt.names(),
                        &hover_table.quote(&cxt.decl, cxt.lvl, val),
                    );
                    println!("  [{}..{}] : {} (defined at {}..{})",
                        span.start_offset, span.end_offset,
                        pretty,
                        def_span.start_offset, def_span.end_offset,
                    );
                }
            }
        }
    }

    Ok(())
}
