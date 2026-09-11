//! Collect a [`DocModel`] from source files.
//!
//! The collector runs the *reference* elaborator exactly the way `typort emit`
//! does — a throwaway [`Backend`] with a silent client, then one
//! `on_change::<false>` per file — so the global declaration table ends up
//! holding every elaborated signature.  Structure (item kinds, member
//! ownership, impl relations, source order) is not in that table, so each file
//! is additionally re-parsed with the real macro table.
//!
//! `preprocess` replaces comments with equal-length whitespace, so spans from
//! the re-parse line up byte-for-byte with the original source; doc-comment
//! extraction and source snippets slice the original text by those offsets.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

use lsp_types::{Diagnostic, MessageType, Url};

use crate::client::ClientLike;
use crate::config::Config;
use crate::list::List;
use crate::L13_namespace::parser::macros::MacroRule;
use crate::L13_namespace::parser::parser_with_macros;
use crate::L13_namespace::parser::syntax::{ClassItem, Decl as AstDecl, Either, Icit, Raw};
use crate::L13_namespace::{pretty::pretty_tm, pretty_sum_definition, preprocess};
use crate::L13_namespace::{Decl as DeclTable, Tm, PRELUDE_CORE, PRELUDE_HDL, PRELUDE_SHOW};
use crate::parser_lib::{Span, ToSpan};
use crate::{Backend, Engine};

use super::markup;
use super::model::{
    DocImpl, DocItem, DocMember, DocModel, DocPackage, ItemKind, SourceFile, SourceRef,
};
use super::DocOptions;

/// A `ClientLike` that swallows diagnostics and log messages.  Doc generation
/// runs the elaborator for its tables, not for its output.
struct DocClient;

impl ClientLike for DocClient {
    fn publish_diagnostics(&self, _uri: Url, _diagnostics: Vec<Diagnostic>, _version: Option<i32>) {}
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

/// One parsed source file.
struct Unit {
    uri: String,
    path: Option<String>,
    text: String,
    decls: Vec<AstDecl>,
    prelude: bool,
}

/// A not-yet-attached `impl` block.
struct ImplSpec {
    inherent: bool,
    self_type: String,
    trait_name: Option<String>,
    methods: Vec<DocMember>,
    source: Option<SourceRef>,
    docs: Option<String>,
}

pub fn collect(
    opts: &DocOptions,
    files: &[PathBuf],
    project: &str,
    root: &str,
) -> Result<DocModel, String> {
    // Documentation needs the reference engine's cross-file decl table; the
    // twin only owns the per-file observation surface.
    let backend = Backend::new_with_engine(DocClient, Engine::Reference);
    backend.load_prelude();
    let prelude_macros = snapshot_macros(&backend);

    let mut warnings: Vec<String> = Vec::new();
    let mut units: Vec<Unit> = Vec::new();
    let mut next_id: u32 = 0;

    // ── Prelude ASTs (for pages) ──────────────────────────────────────────
    if !opts.no_prelude {
        let mut macros: HashMap<String, Vec<MacroRule>> = HashMap::new();
        let mut all: Vec<(&str, &str)> = Vec::new();
        for (n, t) in PRELUDE_CORE.iter() {
            all.push((n, t));
        }
        for (n, t) in PRELUDE_HDL.iter() {
            all.push((n, t));
        }
        all.push((PRELUDE_SHOW.0, PRELUDE_SHOW.1));
        for (name, text) in all {
            let id = next_id;
            next_id += 1;
            let uri = format!("builtin:///{name}.typort");
            match parser_with_macros(&preprocess(text), id, &macros) {
                Some((decls, _errs, exports, _exp)) => {
                    for (k, v) in exports {
                        macros.insert(k, v);
                    }
                    units.push(Unit {
                        uri,
                        path: None,
                        text: text.to_string(),
                        decls,
                        prelude: true,
                    });
                }
                None => warnings.push(format!("prelude parse failed: {name}")),
            }
        }
    }

    // ── User files: elaborate (fills the global decl table) then re-parse ──
    let mut macros: HashMap<String, Vec<MacroRule>> = prelude_macros;
    for path in files {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());
        let text = std::fs::read_to_string(&canonical)
            .map_err(|e| format!("reading {}: {e}", path.display()))?;
        let uri = Url::from_file_path(&canonical)
            .map_err(|()| format!("not an absolute path: {}", canonical.display()))?;
        // `process_file` is the reference analysis entry that merges the
        // file's declarations into the global `cxt.decl` (unlike `on_change`,
        // which elaborates a throwaway clone).
        backend.process_file(&uri, &text, None);
        let id = next_id;
        next_id += 1;
        match parser_with_macros(&preprocess(&text), id, &macros) {
            Some((decls, _errs, exports, _exp)) => {
                for (k, v) in exports {
                    macros.insert(k, v);
                }
                units.push(Unit {
                    uri: uri.to_string(),
                    path: Some(canonical.display().to_string()),
                    text,
                    decls,
                    prelude: false,
                });
            }
            None => warnings.push(format!("parse failed: {}", path.display())),
        }
    }

    let cxt_arc = backend.get_cxt();
    let cxt = cxt_arc.lock().unwrap();

    let mut items: Vec<DocItem> = Vec::new();
    let mut impl_specs: Vec<ImplSpec> = Vec::new();
    // Types that have an inherent `impl` block in the parsed AST; the
    // namespace enumeration below only fills in types the AST did not cover
    // (otherwise every inherent impl would be listed twice).
    let mut ast_inherent_heads: HashSet<String> = HashSet::new();

    for unit in &units {
        let mut prefix: Option<String> = None;
        for d in &unit.decls {
            match d {
                AstDecl::Package { path } => {
                    prefix = Some(
                        path.iter()
                            .map(|s| s.data.as_str())
                            .collect::<Vec<_>>()
                            .join("."),
                    );
                }
                AstDecl::Import { .. } | AstDecl::Println(_) => {}
                AstDecl::Def { name, .. } => {
                    let span = name.to_span();
                    let key = qualify(&prefix, &name.data);
                    let sig = decl_sig(&cxt.decl, &key).or_else(|| {
                        decl_tm(&cxt.decl, &key)
                            .map(|tm| pretty_tm(0, List::new(), &tm))
                    });
                    items.push(DocItem {
                        kind: ItemKind::Fn,
                        key,
                        short: name.data.to_string(),
                        pkg: pkg_of(unit, &prefix),
                        sig,
                        docs: markup::extract_doc_text(&unit.text, span.start_offset),
                        members: Vec::new(),
                        source: source_ref(unit, span),
                        url: String::new(),
                        inherent_impls: Vec::new(),
                        trait_impls: Vec::new(),
                    });
                }
                AstDecl::Enum {
                    is_trait,
                    name,
                    cases,
                    ..
                } => {
                    let span = name.to_span();
                    let key = qualify(&prefix, &name.data);
                    let is_struct =
                        !*is_trait && cases.len() == 1 && cases[0].0.data.ends_with(".mk");
                    let kind = if *is_trait {
                        ItemKind::Trait
                    } else if is_struct {
                        ItemKind::Struct
                    } else {
                        ItemKind::Enum
                    };
                    // A struct's fields are its single `.mk` case's params; an
                    // enum's members are the constructors (cases) themselves.
                    let members: Vec<DocMember> = if is_struct {
                        cases
                            .first()
                            .map(|case| {
                                case.1
                                    .iter()
                                    .map(|(fspan, _fty, _icit)| DocMember {
                                        name: fspan.data.to_string(),
                                        sig: None,
                                        docs: markup::extract_doc_text(
                                            &unit.text,
                                            fspan.start_offset,
                                        ),
                                        source: source_ref(unit, fspan.to_span()),
                                    })
                                    .collect()
                            })
                            .unwrap_or_default()
                    } else {
                        cases
                            .iter()
                            .map(|(cspan, _params, _ret)| {
                                let ckey = format!("{key}.{}", cspan.data);
                                DocMember {
                                    name: cspan.data.to_string(),
                                    sig: decl_sig(&cxt.decl, &ckey),
                                    docs: markup::extract_doc_text(
                                        &unit.text,
                                        cspan.start_offset,
                                    ),
                                    source: source_ref(unit, cspan.to_span()),
                                }
                            })
                            .collect()
                    };
                    items.push(DocItem {
                        kind,
                        key: key.clone(),
                        short: name.data.to_string(),
                        pkg: pkg_of(unit, &prefix),
                        sig: sum_sig(&cxt.decl, &key),
                        docs: markup::extract_doc_text(&unit.text, span.start_offset),
                        members,
                        source: source_ref(unit, span),
                        url: String::new(),
                        inherent_impls: Vec::new(),
                        trait_impls: Vec::new(),
                    });
                }
                AstDecl::TraitDecl { name, methods, .. } => {
                    let span = name.to_span();
                    let key = qualify(&prefix, &name.data);
                    let members: Vec<DocMember> = methods
                        .iter()
                        .map(|(mspan, _params, _ret, _body)| DocMember {
                            name: mspan.data.to_string(),
                            sig: None,
                            docs: markup::extract_doc_text(
                                &unit.text,
                                mspan.start_offset,
                            ),
                            source: source_ref(unit, mspan.to_span()),
                        })
                        .collect();
                    items.push(DocItem {
                        kind: ItemKind::Trait,
                        key: key.clone(),
                        short: name.data.to_string(),
                        pkg: pkg_of(unit, &prefix),
                        sig: sum_sig(&cxt.decl, &key),
                        docs: markup::extract_doc_text(&unit.text, span.start_offset),
                        members,
                        source: source_ref(unit, span),
                        url: String::new(),
                        inherent_impls: Vec::new(),
                        trait_impls: Vec::new(),
                    });
                }
                AstDecl::Class {
                    name,
                    params,
                    items: citems,
                    traits,
                } => {
                    let span = name.to_span();
                    let key = qualify(&prefix, &name.data);
                    items.push(DocItem {
                        kind: ItemKind::Class,
                        key,
                        short: name.data.to_string(),
                        pkg: pkg_of(unit, &prefix),
                        sig: Some(render_class(&name.data, params, citems, traits)),
                        docs: markup::extract_doc_text(&unit.text, span.start_offset),
                        members: Vec::new(),
                        source: source_ref(unit, span),
                        url: String::new(),
                        inherent_impls: Vec::new(),
                        trait_impls: Vec::new(),
                    });
                }
                AstDecl::ImplDecl {
                    name,
                    trait_name,
                    methods,
                    inherent,
                    ..
                } => {
                    let self_type = raw_str(name);
                    let method_members: Vec<DocMember> = methods
                        .iter()
                        .filter_map(|(m, _static)| match m {
                            AstDecl::Def {
                                name: mname,
                                params,
                                ret_type,
                                ..
                            } => Some(DocMember {
                                name: mname.data.to_string(),
                                // Trait-impl methods are not in the decl
                                // table, so render the raw AST signature.
                                sig: Some(render_def_sig(&mname.data, params, ret_type)),
                                docs: markup::extract_doc_text(
                                    &unit.text,
                                    mname.to_span().start_offset,
                                ),
                                source: source_ref(unit, mname.to_span()),
                            }),
                            _ => None,
                        })
                        .collect();
                    if *inherent {
                        ast_inherent_heads.insert(type_head(&self_type));
                    }
                    let (anchor, trait_display) = if *inherent {
                        (name.to_span(), None)
                    } else {
                        (
                            trait_name.to_span(),
                            Some(trait_name.data.to_string()),
                        )
                    };
                    impl_specs.push(ImplSpec {
                        inherent: *inherent,
                        self_type,
                        trait_name: trait_display,
                        methods: method_members,
                        source: source_ref(unit, anchor),
                        docs: None,
                    });
                }
                AstDecl::Derive { .. } => {}
            }
        }
    }

    // Inherent impls are registered in the type namespace, not the decl table;
    // `Cxt.namespace` is the authoritative enumeration of `TypeHead.method`.
    for entry in cxt.namespace.iter() {
        let (_ty, methods, type_name) = entry;
        let mut names: Vec<String> = methods.iter().map(|s| s.to_string()).collect();
        names.sort();
        if names.is_empty() || ast_inherent_heads.contains(type_name.as_str()) {
            continue;
        }
        let head = type_name.to_string();
        let methods: Vec<DocMember> = names
            .iter()
            .map(|m| DocMember {
                name: m.clone(),
                sig: decl_sig(&cxt.decl, &format!("{head}.{m}")),
                docs: None,
                source: None,
            })
            .collect();
        impl_specs.push(ImplSpec {
            inherent: true,
            self_type: head,
            trait_name: None,
            methods,
            source: None,
            docs: None,
        });
    }

    let short_index = build_short_index(&items);
    let mut impls: Vec<DocImpl> = Vec::new();
    for spec in impl_specs {
        let self_idx = resolve_type(&items, &short_index, &spec.self_type);
        let trait_idx = spec
            .trait_name
            .as_ref()
            .and_then(|t| resolve_type(&items, &short_index, t));
        // Only warn for impls that came from an AST we parsed (namespace-
        // derived entries for builtin types are expected to be skipped when
        // prelude pages are disabled).  Generic parameters (`T`, `A`, ...) and
        // primitive type names without a page (`String`) are not typos.
        if spec.source.is_some() && !is_generic_or_builtin(&spec.self_type) {
            if spec.inherent && self_idx.is_none() {
                warnings.push(format!(
                    "impl: could not resolve type `{}` in an inherent impl",
                    spec.self_type
                ));
            }
            if !spec.inherent && trait_idx.is_none() {
                warnings.push(format!(
                    "impl: could not resolve trait `{}` (impl {} for {})",
                    spec.trait_name.as_deref().unwrap_or("?"),
                    spec.trait_name.as_deref().unwrap_or("?"),
                    spec.self_type
                ));
            }
            if !spec.inherent && self_idx.is_none() {
                warnings.push(format!(
                    "impl: could not resolve type `{}` for trait `{}`",
                    spec.self_type,
                    spec.trait_name.as_deref().unwrap_or("?")
                ));
            }
        }
        if spec.inherent && self_idx.is_none() {
            continue;
        }
        if !spec.inherent && self_idx.is_none() && trait_idx.is_none() {
            continue;
        }
        let self_key = self_idx
            .map(|i| items[i].key.clone())
            .unwrap_or_else(|| spec.self_type.clone());
        let idx = impls.len();
        impls.push(DocImpl {
            trait_name: spec.trait_name.clone(),
            self_type: self_key,
            methods: spec.methods,
            source: spec.source,
            docs: spec.docs,
        });
        if spec.inherent {
            if let Some(si) = self_idx {
                items[si].inherent_impls.push(idx);
            }
        } else {
            if let Some(si) = self_idx {
                items[si].trait_impls.push(idx);
            }
            if let Some(ti) = trait_idx {
                // On a trait page these render as implementors.
                if Some(ti) != self_idx {
                    items[ti].trait_impls.push(idx);
                }
            }
        }
    }

    // ── Package `//!` docs ────────────────────────────────────────────────
    let mut pkg_docs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for unit in &units {
        let declared = unit.decls.iter().find_map(|d| match d {
            AstDecl::Package { path } => Some(
                path.iter()
                    .map(|s| s.data.as_str())
                    .collect::<Vec<_>>()
                    .join("."),
            ),
            _ => None,
        });
        let pkg = match declared {
            Some(p) if !p.is_empty() => p,
            _ => {
                if unit.prelude {
                    "builtin".to_string()
                } else {
                    String::new()
                }
            }
        };
        if let Some(doc) = markup::extract_inner_doc(&unit.text) {
            pkg_docs.entry(pkg).or_default().push(doc);
        }
    }

    // ── Deterministic packages ────────────────────────────────────────────
    let mut pkg_map: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (i, it) in items.iter().enumerate() {
        pkg_map.entry(it.pkg.clone()).or_default().push(i);
    }
    let mut packages: Vec<DocPackage> = pkg_map
        .into_iter()
        .map(|(path, mut idxs)| {
            idxs.sort_by(|&a, &b| {
                (items[a].kind.sort_key(), items[a].key.as_str())
                    .cmp(&(items[b].kind.sort_key(), items[b].key.as_str()))
            });
            let docs = pkg_docs.get(&path).map(|v| v.join("\n\n"));
            DocPackage { path, docs, items: idxs }
        })
        .collect();
    packages.shrink_to_fit();

    let documented = items
        .iter()
        .filter(|i| i.docs.is_some() || i.members.iter().any(|m| m.docs.is_some()))
        .count();

    // ── Unique output file names ──────────────────────────────────────────
    let mut used: HashSet<String> = HashSet::new();
    for it in items.iter_mut() {
        let base = sanitize(&it.key);
        let mut name = format!("{base}.html");
        let mut n = 2;
        while used.contains(&name) {
            name = format!("{base}_{n}.html");
            n += 1;
        }
        used.insert(name.clone());
        it.url = name;
    }

    // ── Source browser pages + per-reference "view source" URLs ──────────
    let external = opts.source_link.as_deref();
    let mut sources: Vec<SourceFile> = Vec::new();
    let mut uri_to_src: HashMap<String, String> = HashMap::new();
    if external.is_none() {
        let mut used_src: HashSet<String> = HashSet::new();
        for unit in &units {
            let base = if unit.prelude {
                sanitize(unit.uri.trim_start_matches("builtin:///"))
            } else {
                let name = unit
                    .path
                    .as_deref()
                    .and_then(|p| std::path::Path::new(p).file_name())
                    .and_then(|n| n.to_str())
                    .unwrap_or("source");
                sanitize(name)
            };
            let mut name = format!("{base}.html");
            let mut n = 2;
            while used_src.contains(&name) {
                name = format!("{base}_{n}.html");
                n += 1;
            }
            used_src.insert(name.clone());
            let title = unit.path.clone().unwrap_or_else(|| unit.uri.clone());
            uri_to_src.insert(unit.uri.clone(), name.clone());
            sources.push(SourceFile {
                url: name,
                title,
                text: unit.text.clone(),
            });
        }
    }
    let link_source = |s: &mut SourceRef| {
        s.url = match external {
            Some(template) => {
                // `{path}` prefers the on-disk path; builtin prelude entries
                // fall back to their bare file name (no `builtin:///`).
                let disp = s
                    .path
                    .clone()
                    .unwrap_or_else(|| s.uri.trim_start_matches("builtin:///").to_string());
                Some(
                    template
                        .replace("{path}", &disp)
                        .replace("{line}", &s.line.to_string()),
                )
            }
            None => uri_to_src
                .get(&s.uri)
                .map(|u| format!("src/{u}#L{}", s.line)),
        };
    };
    for it in items.iter_mut() {
        if let Some(s) = &mut it.source {
            link_source(s);
        }
        for m in it.members.iter_mut() {
            if let Some(s) = &mut m.source {
                link_source(s);
            }
        }
    }
    for im in impls.iter_mut() {
        if let Some(s) = &mut im.source {
            link_source(s);
        }
        for m in im.methods.iter_mut() {
            if let Some(s) = &mut m.source {
                link_source(s);
            }
        }
    }

    // ── Dead intra-doc links ─────────────────────────────────────────────
    {
        let mut valid: HashSet<String> = used.clone();
        valid.insert("index.html".to_string());
        for s in &sources {
            valid.insert(format!("src/{}", s.url));
        }
        let mut check = |docs: &Option<String>, where_: &str| {
            let Some(text) = docs else { return };
            for target in markdown_link_targets(text) {
                if target.starts_with("http://")
                    || target.starts_with("https://")
                    || target.starts_with("mailto:")
                    || target.starts_with('#')
                {
                    continue;
                }
                let file = target.split('#').next().unwrap_or("");
                if file.is_empty() {
                    continue;
                }
                if !valid.contains(file) {
                    warnings.push(format!("dead doc link `{target}` in {where_}"));
                }
            }
        };
        for it in &items {
            check(&it.docs, &it.key);
            for m in &it.members {
                check(&m.docs, &format!("{}.{}", it.key, m.name));
            }
        }
        for p in &packages {
            check(&p.docs, &format!("package `{}`", p.path));
        }
    }

    Ok(DocModel {
        project: project.to_string(),
        root: root.to_string(),
        items,
        packages,
        impls,
        warnings,
        documented,
        source_links: external.is_some() || !uri_to_src.is_empty(),
        sources,
    })
}

/// A type expression that legitimately has no item page: a bare generic
/// parameter (`T`, `A`, ...) or a primitive without a declaration (`String`).
fn is_generic_or_builtin(s: &str) -> bool {
    let head = type_head(s);
    let mut chars = head.chars();
    let single_upper = matches!((chars.next(), chars.next()), (Some(c), None) if c.is_ascii_uppercase());
    single_upper || matches!(head.as_str(), "String" | "Unit" | "Type")
}

/// Markdown link targets `](...)`, for dead-link checking.
fn markdown_link_targets(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b']' && bytes[i + 1] == b'(' {
            let start = i + 2;
            if let Some(close) = text[start..].find(')') {
                let target = text[start..start + close].trim();
                if !target.is_empty() {
                    out.push(target.to_string());
                }
                i = start + close + 1;
                continue;
            }
        }
        i += 1;
    }
    out
}

// ── helpers ───────────────────────────────────────────────────────────────

fn snapshot_macros(backend: &Arc<Backend<DocClient>>) -> HashMap<String, Vec<MacroRule>> {
    backend
        .exported_macros
        .iter()
        .map(|e| (e.key().clone(), e.value().clone()))
        .collect()
}

fn qualify(prefix: &Option<String>, name: &str) -> String {
    match prefix {
        Some(p) if !p.is_empty() => format!("{p}.{name}"),
        _ => name.to_string(),
    }
}

fn pkg_of(unit: &Unit, prefix: &Option<String>) -> String {
    match prefix {
        Some(p) if !p.is_empty() => p.clone(),
        _ => {
            if unit.prelude {
                "builtin".to_string()
            } else {
                String::new()
            }
        }
    }
}

fn decl_sig(decl: &DeclTable, key: &str) -> Option<String> {
    decl.get(key)
        .map(|e| e.6.clone())
        .filter(|s| !s.trim().is_empty())
}

fn decl_tm(decl: &DeclTable, key: &str) -> Option<Rc<Tm>> {
    decl.get(key).map(|e| e.1.clone())
}

fn sum_sig(decl: &DeclTable, key: &str) -> Option<String> {
    let tm = decl_tm(decl, key)?;
    pretty_sum_definition(key, &tm, decl)
}

fn source_ref(unit: &Unit, span: Span<()>) -> Option<SourceRef> {
    let start = span.start_offset as usize;
    if start > unit.text.len() || !unit.text.is_char_boundary(start) {
        return None;
    }
    let line = unit.text[..start].bytes().filter(|&b| b == b'\n').count() as u32 + 1;
    let line_start = unit.text[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = unit.text[start..]
        .find('\n')
        .map(|i| start + i)
        .unwrap_or(unit.text.len());
    let snippet = unit.text[line_start..line_end].trim().to_string();
    Some(SourceRef {
        uri: unit.uri.clone(),
        path: unit.path.clone(),
        start: span.start_offset,
        end: span.end_offset,
        line,
        snippet,
        url: None,
    })
}

fn build_short_index(items: &[DocItem]) -> HashMap<String, Vec<usize>> {
    let mut index: HashMap<String, Vec<usize>> = HashMap::new();
    for (i, it) in items.iter().enumerate() {
        index.entry(it.short.clone()).or_default().push(i);
    }
    index
}

/// Resolve a source-level type expression (e.g. `Option[T]`, `Nat`) to an item.
/// Ambiguity is not guessed: a bare short name must be unique, otherwise the
/// fully-qualified head is tried.
fn resolve_type(
    items: &[DocItem],
    short_index: &HashMap<String, Vec<usize>>,
    s: &str,
) -> Option<usize> {
    let head = type_head(s);
    if head.is_empty() {
        return None;
    }
    if let Some(v) = short_index.get(&head) {
        if v.len() == 1 {
            return Some(v[0]);
        }
    }
    let suffix = format!(".{head}");
    let cands: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, it)| it.key == head || it.key.ends_with(&suffix))
        .map(|(i, _)| i)
        .collect();
    if cands.len() == 1 {
        Some(cands[0])
    } else {
        None
    }
}

/// Leading identifier run of a type expression, package dots included.
fn leading_ident(s: &str) -> String {
    s.chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
        .collect()
}

/// The head type name used for decl-table method keys (`TypeHead.method`).
fn type_head(s: &str) -> String {
    let lead = leading_ident(s);
    lead.rsplit('.').next().unwrap_or(&lead).to_string()
}

fn sanitize(key: &str) -> String {
    let mut s = String::with_capacity(key.len());
    for c in key.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            s.push(c);
        } else {
            s.push('_');
        }
    }
    if s.is_empty() {
        s.push('_');
    }
    s
}

/// Source-style rendering of a raw (unelaborated) term, for spans the decl
/// table cannot describe (class fields, impl self types).
fn raw_str(r: &Raw) -> String {
    match r {
        Raw::Var(n) => n.data.to_string(),
        Raw::Obj(e, Some(n)) => format!("{}.{}", raw_str(e), n.data),
        Raw::Obj(e, None) => raw_str(e),
        Raw::App(f, a, ic) => match ic {
            Either::Name(n) => format!("{}[{}={}]", raw_str(f), n.data, raw_str(a)),
            Either::Icit(Icit::Impl) => format!("{}[{}]", raw_str(f), raw_str(a)),
            Either::Icit(Icit::Expl) => {
                // Infix sugar: the parser represents `a + b` as `(a.+) b`
                // (`Obj(base, op)` applied to the right operand).  Render it
                // back in source form instead of the dotted field-access shape.
                if let Raw::Obj(base, Some(op)) = f.as_ref() {
                    let symbolic = op
                        .data
                        .chars()
                        .next()
                        .is_some_and(|c| !(c.is_alphanumeric() || c == '_'));
                    if symbolic {
                        return format!("{} {} {}", raw_str(base), op.data, raw_str(a));
                    }
                }
                format!("{} {}", raw_str(f), raw_str(a))
            }
        },
        Raw::U(n) => format!("Type {n}"),
        Raw::Nat(n) => n.data.to_string(),
        Raw::LiteralIntro(s) => format!("{:?}", s.data),
        Raw::Hole(_) => "_".to_string(),
        Raw::Pi(x, Icit::Impl, a, b) => format!("[{}: {}] -> {}", x.data, raw_str(a), raw_str(b)),
        Raw::Pi(x, Icit::Expl, a, b) => format!("({}: {}) -> {}", x.data, raw_str(a), raw_str(b)),
        Raw::Lam(x, Either::Icit(Icit::Impl), b) => format!("[{}] => {}", x.data, raw_str(b)),
        Raw::Lam(x, Either::Icit(Icit::Expl), b) => format!("{} => {}", x.data, raw_str(b)),
        Raw::Lam(x, Either::Name(n), b) => format!("[{}={}] => {}", n.data, x.data, raw_str(b)),
        _ => format!("{r}"),
    }
}

/// Render a `def` signature from its raw (unelaborated) AST form.  Used for
/// positions the decl table cannot describe: trait-impl methods and class
/// methods.
fn render_def_sig(
    name: &str,
    params: &[(Span<smol_str::SmolStr>, Raw, Icit)],
    ret: &Raw,
) -> String {
    let mut implicit: Vec<String> = Vec::new();
    let mut explicit: Vec<String> = Vec::new();
    for (p, ty, ic) in params {
        match ic {
            Icit::Impl => implicit.push(p.data.to_string()),
            Icit::Expl => explicit.push(format!("{}: {}", p.data, raw_str(ty))),
        }
    }
    let mut sig = format!("def {name}");
    if !implicit.is_empty() {
        sig.push_str(&format!("[{}]", implicit.join(", ")));
    }
    if !explicit.is_empty() {
        sig.push_str(&format!("({})", explicit.join(", ")));
    }
    sig.push_str(&format!(": {}", raw_str(ret)));
    sig
}

/// Render a `class` / HDL `module` declaration.  Ports and signals are class
/// fields; `let` bindings surface as methods.  Statements (HDL assignments)
/// are intentionally omitted.
fn render_class(
    name: &str,
    params: &[(Span<smol_str::SmolStr>, Raw, Icit)],
    items: &[ClassItem],
    traits: &[(Span<smol_str::SmolStr>, Vec<Raw>)],
) -> String {
    let mut impls: Vec<String> = Vec::new();
    let mut expls: Vec<String> = Vec::new();
    for (p, ty, ic) in params {
        match ic {
            Icit::Impl => impls.push(p.data.to_string()),
            Icit::Expl => expls.push(format!("{}: {}", p.data, raw_str(ty))),
        }
    }
    let mut out = format!("class {name}");
    if !impls.is_empty() {
        out.push_str(&format!("[{}]", impls.join(", ")));
    }
    if !expls.is_empty() {
        out.push_str(&format!("({})", expls.join(", ")));
    }
    for (t, _args) in traits {
        out.push_str(&format!("\nimpl {} for {name}", t.data));
    }
    let mut lines: Vec<String> = Vec::new();
    for item in items {
        match item {
            ClassItem::Field(n, ty, _v) => lines.push(format!("{}: {}", n.data, raw_str(ty))),
            ClassItem::Method(AstDecl::Def {
                name,
                params,
                ret_type,
                ..
            }, _) => {
                lines.push(render_def_sig(&name.data, params, ret_type));
            }
            ClassItem::Method(_decl, _) => {}
            ClassItem::Stmt(_) => {}
        }
    }
    if lines.is_empty() {
        out.push_str(" { }");
    } else {
        out.push_str(" {");
        for l in lines {
            out.push_str(&format!("\n    {l}"));
        }
        out.push_str("\n}");
    }
    out
}
