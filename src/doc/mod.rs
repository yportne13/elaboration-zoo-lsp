//! `typort doc` — generate API documentation from `.typort` sources.
//!
//! Pipeline: resolve inputs (explicit files or `Typort.toml`) → [`collect`]
//! builds a renderer-independent [`model::DocModel`] by running the reference
//! elaborator and re-parsing each file for structure → render to HTML and/or
//! JSON.  See `docs/docgen-design.md` for the design rationale.

pub mod markup;
pub mod model;

mod collect;
mod render_html;
mod render_json;
mod serve;

use std::path::PathBuf;

pub use model::{DocItem, DocModel, ItemKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DocFormat {
    Html,
    Json,
}

#[derive(Clone, Debug)]
pub struct DocOptions {
    /// Explicit source files; empty means "use Typort.toml".
    pub files: Vec<PathBuf>,
    /// Output directory; `None` defaults to `<target>/doc`.
    pub out: Option<PathBuf>,
    pub formats: Vec<DocFormat>,
    /// Skip prelude item pages (analysis still loads the prelude).
    pub no_prelude: bool,
    /// Open `index.html` (or the served URL) when done.
    pub open: bool,
    /// External source-link template with `{path}` / `{line}` placeholders.
    /// When set, no `src/` browser pages are generated.
    pub source_link: Option<String>,
    /// Serve the output over HTTP on this port and block (0 = pick a free port).
    pub serve: Option<u16>,
    /// Exit non-zero when any warning was emitted.
    pub deny_warnings: bool,
    /// Exit non-zero when documentation coverage is below this percentage.
    pub min_coverage: Option<f64>,
}

impl Default for DocOptions {
    fn default() -> Self {
        DocOptions {
            files: Vec::new(),
            out: None,
            formats: vec![DocFormat::Html],
            no_prelude: false,
            open: false,
            source_link: None,
            serve: None,
            deny_warnings: false,
            min_coverage: None,
        }
    }
}

fn resolve_inputs(
    opts: &DocOptions,
) -> Result<(Vec<PathBuf>, String, String, PathBuf), String> {
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    if opts.files.is_empty() {
        match crate::config::Config::discover(&cwd) {
            Ok(pc) => {
                let files = pc.collect_sources().map_err(|e| e.to_string())?;
                let out = pc.target_dir().join("doc");
                Ok((
                    files,
                    pc.config.project.name.clone(),
                    pc.root.display().to_string(),
                    out,
                ))
            }
            Err(e) => Err(format!(
                "{e}; pass source files or run inside a Typort.toml project"
            )),
        }
    } else {
        Ok((
            opts.files.clone(),
            "typort project".to_string(),
            cwd.display().to_string(),
            cwd.join("doc"),
        ))
    }
}

/// Build the doc model without writing anything (used by tests).
pub fn build_model(opts: &DocOptions) -> Result<DocModel, String> {
    let (files, project, root, _) = resolve_inputs(opts)?;
    collect::collect(opts, &files, &project, &root)
}

pub fn run(opts: DocOptions) -> Result<(), String> {
    let (files, project, root, default_out) = resolve_inputs(&opts)?;
    let model = collect::collect(&opts, &files, &project, &root)?;
    let out = opts.out.clone().unwrap_or(default_out);
    std::fs::create_dir_all(&out).map_err(|e| format!("creating {}: {e}", out.display()))?;

    let mut wrote: Vec<&str> = Vec::new();
    let html = opts.formats.is_empty() || opts.formats.contains(&DocFormat::Html);
    if html {
        render_html::write_site(&model, &out)?;
        wrote.push("html");
    }
    if opts.formats.contains(&DocFormat::Json) {
        render_json::write(&model, &out.join("doc.json"))?;
        wrote.push("json");
    }

    let coverage = if model.items.is_empty() {
        100.0
    } else {
        100.0 * model.documented as f64 / model.items.len() as f64
    };
    eprintln!(
        "typort doc: {} items ({}/{} documented, {:.0}%), {} packages -> {} ({})",
        model.items.len(),
        model.documented,
        model.items.len(),
        coverage,
        model.packages.len(),
        out.display(),
        wrote.join(", ")
    );
    for w in &model.warnings {
        eprintln!("warning: {w}");
    }

    if let Some(port) = opts.serve {
        let server = serve::bind(port)?;
        let base = format!("http://{}/", server.addr);
        eprintln!("serving {} at {} (Ctrl+C to stop)", out.display(), base);
        if opts.open {
            open_browser_str(&base);
        }
        serve::serve(&out, server)?;
        return Ok(());
    }

    if opts.open {
        open_browser(&out.join("index.html"));
    }
    if opts.deny_warnings && !model.warnings.is_empty() {
        return Err(format!(
            "{} documentation warning(s) (denied by --deny-warnings)",
            model.warnings.len()
        ));
    }
    if let Some(min) = opts.min_coverage {
        if coverage + f64::EPSILON < min {
            return Err(format!(
                "documentation coverage {:.1}% is below --min-coverage {:.1}%",
                coverage, min
            ));
        }
    }
    Ok(())
}

fn open_browser(path: &std::path::Path) {
    open_browser_str(&path.display().to_string());
}

fn open_browser_str(target: &str) {
    #[cfg(target_os = "windows")]
    {
        let _ = std::process::Command::new("cmd")
            .args(["/C", "start", ""])
            .arg(target)
            .spawn();
    }
    #[cfg(target_os = "macos")]
    {
        let _ = std::process::Command::new("open").arg(target).spawn();
    }
    #[cfg(all(unix, not(target_os = "macos")))]
    {
        let _ = std::process::Command::new("xdg-open").arg(target).spawn();
    }
}
