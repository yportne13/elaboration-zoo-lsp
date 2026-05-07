use std::error::Error;
use std::fs;
use std::path::PathBuf;

use elaboration_zoo_lsp::Backend;
use elaboration_zoo_lsp::client::CliClient;
use elaboration_zoo_lsp::TextDocumentItem;
use lsp_types::Url;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
    let args: Vec<String> = std::env::args().collect();
    let mut verilog_mode = false;
    let files: Vec<&String> = args.iter().skip(1).filter(|a| {
        if a.as_str() == "--verilog" {
            verilog_mode = true;
            false
        } else {
            true
        }
    }).collect();

    if files.is_empty() {
        eprintln!("Usage: typort [--verilog] <file.typort> [<file2.typort> ...]");
        std::process::exit(1);
    }

    // Create CLI client with source map for pretty-printed diagnostics.
    let cli_client = CliClient::new();
    let source_map = cli_client.source_map.clone();

    // Create backend with CLI client.
    // Backend::new loads the builtin prelude, sets up Infer/Cxt.
    let backend = Backend::new(cli_client);

    for filepath in &files {
        let path = PathBuf::from(filepath);
        let contents = fs::read_to_string(&path)?;
        let uri = Url::from_file_path(path.canonicalize()?).unwrap();

        eprintln!("Analyzing: {} ({} bytes)", uri.as_str(), contents.len());

        // Store source text so the CLI client can render diagnostics with source context.
        source_map.insert(uri.as_str().to_string(), contents.clone());

        // Run the analysis pipeline (parse + infer + diagnostics).
        backend.on_change::<false>(TextDocumentItem {
            uri: uri.clone(),
            text: &contents,
            version: None,
        });

        // Emit Verilog if requested
        if verilog_mode {
            let infer = backend.get_infer();
            let cxt = backend.get_cxt();
            let infer = infer.lock().unwrap();
            let cxt = cxt.lock().unwrap();
            let verilog = elaboration_zoo_lsp::L12_canonical::verilog::emit_verilog(
                &infer,
                &cxt.decl,
                cxt.lvl,
            );
            if !verilog.is_empty() {
                println!("{}", verilog);
            }
        }

        // Print inferred results
        /*if let Some(type_map) = backend.type_map.get(uri.as_str()) {
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
        }*/
    }

    Ok(())
}
