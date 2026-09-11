//! Documentation model (IR): a renderer-independent snapshot of one project's
//! public surface, produced by [`super::collect`] and consumed by the HTML /
//! JSON renderers.
//!
//! The model deliberately holds only owned strings and indices — no
//! `Rc<Tm>` / `Rc<Val>` — so the elaborator state may be dropped before
//! rendering and every renderer stays decoupled from `Backend`.

use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
pub enum ItemKind {
    Fn,
    Enum,
    Struct,
    Trait,
    Class,
}

impl ItemKind {
    pub fn label(self) -> &'static str {
        match self {
            ItemKind::Fn => "def",
            ItemKind::Enum => "enum",
            ItemKind::Struct => "struct",
            ItemKind::Trait => "trait",
            ItemKind::Class => "class",
        }
    }

    pub fn slug(self) -> &'static str {
        match self {
            ItemKind::Fn => "fn",
            ItemKind::Enum => "enum",
            ItemKind::Struct => "struct",
            ItemKind::Trait => "trait",
            ItemKind::Class => "class",
        }
    }

    /// Grouping order on package pages (rustdoc-ish: types, then traits, then fns).
    pub fn sort_key(self) -> u8 {
        match self {
            ItemKind::Enum => 0,
            ItemKind::Struct => 1,
            ItemKind::Class => 2,
            ItemKind::Trait => 3,
            ItemKind::Fn => 4,
        }
    }
}

/// Where an item (or member) came from: URI plus a 1-based line and the first
/// source line as a snippet. `path` is `None` for builtin prelude URIs.
///
/// `url` is the resolved "view source" target (a generated `src/*.html`
/// anchor, or an external template expansion) and is `None` when source
/// linking is disabled.
#[derive(Clone, Debug, Serialize)]
pub struct SourceRef {
    pub uri: String,
    pub path: Option<String>,
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub snippet: String,
    pub url: Option<String>,
}

/// A source file kept for the generated source-browser pages.  Not serialized
/// to JSON (the texts would dwarf the API model).
#[derive(Clone, Debug)]
pub struct SourceFile {
    /// Output file name under `src/`.
    pub url: String,
    /// Display title (path or builtin name).
    pub title: String,
    pub text: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct DocMember {
    pub name: String,
    pub sig: Option<String>,
    pub docs: Option<String>,
    pub source: Option<SourceRef>,
}

/// One `impl` block. `trait_name == None` means an inherent impl.
#[derive(Clone, Debug, Serialize)]
pub struct DocImpl {
    pub trait_name: Option<String>,
    pub self_type: String,
    pub methods: Vec<DocMember>,
    pub source: Option<SourceRef>,
    pub docs: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DocItem {
    pub kind: ItemKind,
    /// Fully-qualified key as registered in `Cxt.decl` (package prefix applied).
    pub key: String,
    pub short: String,
    /// Display package ("" = root, "builtin" = prelude).
    pub pkg: String,
    pub sig: Option<String>,
    pub docs: Option<String>,
    pub members: Vec<DocMember>,
    pub source: Option<SourceRef>,
    /// Output file name relative to the doc root.
    pub url: String,
    pub inherent_impls: Vec<usize>,
    pub trait_impls: Vec<usize>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DocPackage {
    pub path: String,
    /// `//!` file/package docs (multiple files in a package are concatenated).
    pub docs: Option<String>,
    pub items: Vec<usize>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DocModel {
    pub project: String,
    pub root: String,
    pub items: Vec<DocItem>,
    pub packages: Vec<DocPackage>,
    pub impls: Vec<DocImpl>,
    pub warnings: Vec<String>,
    /// Items carrying a `///` doc comment (directly or on a member).
    pub documented: usize,
    /// Source texts for the generated `src/` browser; excluded from JSON.
    #[serde(skip)]
    pub sources: Vec<SourceFile>,
    /// Whether per-item source links were requested.
    pub source_links: bool,
}
