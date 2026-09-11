// `typort doc` end-to-end: build a small project, collect the model, and
// render the static site.  The elaboration pipeline is shared across the
// assertions in one test so the prelude is paid for once.

use std::fs;
use std::path::PathBuf;

use elaboration_zoo_lsp::doc::{build_model, markup, run, DocFormat, DocOptions, ItemKind};

fn temp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("typort-docgen-{}-{tag}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

const SOURCE: &str = r#"//! Demo package docs.

package demo

/// A color.
enum Color {
    /// Warm red.
    red
    /// Cool green.
    green
}

/// A pair of values.
struct Pair[A, B] {
    /// The first component.
    fst: A
    /// The second component.
    snd: B
}

trait Describable {
    /// Describe this value.
    def describe: String
}

impl Describable for Color {
    /// Red or green.
    def describe: String = "color"
}

impl Color {
    /// Is this red?
    def is_red: Boolean =
        match this {
            case red => true
            case green => false
        }
}

/// The identity function.
def id[A](x: A): A = x
"#;

#[test]
fn docgen_model_and_site() {
    let dir = temp_dir("site");
    let src = dir.join("lib.typort");
    fs::write(&src, SOURCE).unwrap();

    let opts = DocOptions {
        files: vec![src.clone()],
        out: Some(dir.join("out")),
        formats: vec![DocFormat::Html, DocFormat::Json],
        no_prelude: true,
        ..DocOptions::default()
    };

    // ── model ──
    let model = build_model(&opts).expect("collect model");
    let find = |key: &str| model.items.iter().find(|i| i.key == key);

    let color = find("demo.Color").expect("demo.Color item");
    assert_eq!(color.kind, ItemKind::Enum);
    assert!(
        color.docs.as_deref().unwrap_or("").contains("A color"),
        "doc comment extracted: {:?}",
        color.docs
    );
    assert!(
        color.sig.as_deref().unwrap_or("").contains("Color"),
        "enum signature rendered: {:?}",
        color.sig
    );

    // Member-level docs: enum cases.
    let member_doc = |item: &elaboration_zoo_lsp::doc::DocItem, name: &str| {
        item.members
            .iter()
            .find(|m| m.name == name)
            .and_then(|m| m.docs.clone())
    };
    assert!(
        member_doc(color, "red").as_deref().unwrap_or("").contains("Warm red"),
        "enum case docs: {:?}",
        color.members
    );

    let pair = find("demo.Pair").expect("demo.Pair item");
    assert_eq!(pair.kind, ItemKind::Struct);
    // Member-level docs: struct fields.
    assert!(
        member_doc(pair, "fst").as_deref().unwrap_or("").contains("first component"),
        "struct field docs: {:?}",
        pair.members
    );

    let desc = find("demo.Describable").expect("demo.Describable item");
    assert_eq!(desc.kind, ItemKind::Trait);
    assert!(
        member_doc(desc, "describe").as_deref().unwrap_or("").contains("Describe this value"),
        "trait method docs: {:?}",
        desc.members
    );

    let id = find("demo.id").expect("demo.id item");
    assert_eq!(id.kind, ItemKind::Fn);
    assert!(id.sig.is_some(), "def signature from the decl table");
    assert!(id.docs.as_deref().unwrap_or("").contains("identity"));

    assert!(!model.impls.is_empty(), "impl blocks collected");
    // Trait-impl method signatures come from the raw AST (not the decl table).
    let trait_impl = model
        .impls
        .iter()
        .find(|i| i.trait_name.as_deref() == Some("Describable"))
        .expect("trait impl collected");
    assert!(
        trait_impl.methods[0]
            .sig
            .as_deref()
            .unwrap_or("")
            .contains("def describe"),
        "trait impl method signature: {:?}",
        trait_impl.methods
    );
    // Inherent impls are not duplicated (AST preferred over the namespace).
    let color_inherent: Vec<_> = model
        .impls
        .iter()
        .filter(|i| i.trait_name.is_none() && i.self_type.contains("Color"))
        .collect();
    assert_eq!(color_inherent.len(), 1, "one inherent impl for Color");
    assert!(
        color_inherent[0].methods[0]
            .sig
            .as_deref()
            .unwrap_or("")
            .contains("def is_red"),
        "inherent method signature: {:?}",
        color_inherent[0].methods
    );

    // Package `//!` docs.
    let demo_pkg = model
        .packages
        .iter()
        .find(|p| p.path == "demo")
        .expect("demo package");
    assert!(
        demo_pkg.docs.as_deref().unwrap_or("").contains("Demo package docs"),
        "package docs: {:?}",
        demo_pkg.docs
    );
    assert!(model.documented >= 4, "coverage counted: {}", model.documented);

    // ── site ──
    run(opts).expect("render site");
    let out = dir.join("out");
    assert!(out.join("index.html").is_file());
    assert!(out.join("search-index.js").is_file());
    assert!(out.join("doc.css").is_file());
    assert!(out.join("doc.json").is_file(), "json format requested");
    let index = fs::read_to_string(out.join("index.html")).unwrap();
    assert!(index.contains("demo.Color"), "index lists the item");
    let search = fs::read_to_string(out.join("search-index.js")).unwrap();
    assert!(search.starts_with("window.TYPORT_SEARCH"));
    assert!(search.contains("demo.Color"));

    let color_page = out.join(&color.url);
    assert!(color_page.is_file(), "item page written: {}", color.url);
    let page = fs::read_to_string(&color_page).unwrap();
    assert!(page.contains("A color"), "docs rendered on the item page");
    assert!(page.contains("Warm red"), "member docs rendered: {page}");
    assert!(page.contains("Source"), "source block rendered");
    // Source browser page + view-source link.
    assert!(out.join("src").is_dir(), "src/ browser written");
    assert!(page.contains("view source"), "view-source link rendered");
    let src_pages: Vec<_> = fs::read_dir(out.join("src")).unwrap().collect();
    assert_eq!(src_pages.len(), 1, "one source page for one file");
    let src_html = fs::read_to_string(
        src_pages[0].as_ref().unwrap().path(),
    )
    .unwrap();
    assert!(src_html.contains("id=\"L1\""), "line anchors in source page");

    // Coverage gate: every item is documented here, so a >100% gate fails.
    let gated = DocOptions {
        files: vec![src.clone()],
        out: Some(dir.join("out2")),
        formats: vec![DocFormat::Json],
        no_prelude: true,
        min_coverage: Some(200.0),
        ..DocOptions::default()
    };
    assert!(run(gated).is_err(), "min-coverage gate should reject");
}

#[test]
fn markup_extended() {
    let html = markup::to_html(
        "> quoted\n> more\n\n---\n\n| A | B |\n|---|---|\n| 1 | 2 |\n\nSetext\n===\n",
    );
    assert!(html.contains("<blockquote>"), "{html}");
    assert!(html.contains("<hr>"), "{html}");
    assert!(html.contains("<th>A</th>"), "{html}");
    assert!(html.contains("<td>1</td>"), "{html}");
    assert!(html.contains("<h2>Setext</h2>"), "{html}");
}

#[test]
fn markup_subset() {
    // Doc extraction: only the contiguous `///` block directly above the
    // span; a plain `//` line terminates the scan.
    let src = "/// First line.\n/// Second line.\n// not doc\n/// Last.\ndef foo = 1\n";
    let idx = src.find("foo").unwrap() as u32;
    assert_eq!(
        markup::extract_doc_text(src, idx).as_deref(),
        Some("Last.")
    );
    let src2 = "/// First line.\n/// Second line.\ndef bar = 1\n";
    let idx2 = src2.find("bar").unwrap() as u32;
    assert_eq!(
        markup::extract_doc_text(src2, idx2).as_deref(),
        Some("First line.\nSecond line.")
    );

    // `//!` package docs: leading run, blank lines tolerated before it.
    assert_eq!(
        markup::extract_inner_doc("\n//! Module docs.\n//! More.\npackage x\n").as_deref(),
        Some("Module docs.\nMore.")
    );
    assert_eq!(markup::extract_inner_doc("def foo = 1\n"), None);

    // Rendering: headings, fenced code, inline code, links, escaping.
    let html = markup::to_html("# Title\n\nUse `foo` and [bar](bar.html).\n\n```typort\nx < y\n```\n");
    assert!(html.contains("<h2>Title</h2>"), "{html}");
    assert!(html.contains("<code>foo</code>"));
    assert!(html.contains("href=\"bar.html\""));
    assert!(html.contains("x &lt; y"), "code escaped: {html}");
}
