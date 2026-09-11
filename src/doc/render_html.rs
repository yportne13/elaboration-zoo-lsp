//! Static HTML renderer: one page per item plus a searchable index page.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use super::markup;
use super::model::{DocImpl, DocItem, DocModel, ItemKind};

const CSS: &str = include_str!("assets/doc.css");
const JS: &str = include_str!("assets/doc.js");

pub fn write_site(model: &DocModel, out: &Path) -> Result<(), String> {
    fs::create_dir_all(out).map_err(|e| format!("creating {}: {e}", out.display()))?;
    fs::write(out.join("doc.css"), CSS).map_err(|e| format!("writing doc.css: {e}"))?;
    fs::write(out.join("doc.js"), JS).map_err(|e| format!("writing doc.js: {e}"))?;
    fs::write(out.join("search-index.js"), search_index(model))
        .map_err(|e| format!("writing search-index.js: {e}"))?;
    fs::write(out.join("index.html"), index_page(model))
        .map_err(|e| format!("writing index.html: {e}"))?;
    for it in &model.items {
        let html = item_page(model, it);
        fs::write(out.join(&it.url), html)
            .map_err(|e| format!("writing {}: {e}", it.url))?;
    }
    // Generated source browser.
    if !model.sources.is_empty() {
        let dir = out.join("src");
        fs::create_dir_all(&dir).map_err(|e| format!("creating {}: {e}", dir.display()))?;
        for sf in &model.sources {
            fs::write(dir.join(&sf.url), source_page(sf))
                .map_err(|e| format!("writing src/{}: {e}", sf.url))?;
        }
    }
    Ok(())
}

fn source_page(sf: &super::model::SourceFile) -> String {
    let mut b = String::new();
    b.push_str("<p class=\"crumbs\"><a href=\"../index.html\">&larr; index</a></p>\n");
    let _ = write!(b, "<h1 class=\"src-title\">{}</h1>\n", markup::escape_html(&sf.title));
    b.push_str("<pre class=\"source-page\"><code>");
    for (i, line) in sf.text.lines().enumerate() {
        let n = i + 1;
        let _ = write!(
            b,
            "<a class=\"ln\" id=\"L{n}\" href=\"#L{n}\">{n:>5}</a> {}\n",
            markup::escape_html(line)
        );
    }
    b.push_str("</code></pre>\n");
    page_at(&sf.title, &b, "../")
}

fn link_map(model: &DocModel) -> HashMap<String, String> {
    let mut count: HashMap<&str, usize> = HashMap::new();
    for it in &model.items {
        *count.entry(it.short.as_str()).or_insert(0) += 1;
    }
    let mut map = HashMap::new();
    for it in &model.items {
        if count.get(it.short.as_str()) == Some(&1) {
            map.insert(it.short.clone(), it.url.clone());
        }
        map.insert(it.key.clone(), it.url.clone());
    }
    map
}

fn page(title: &str, body: &str) -> String {
    page_at(title, body, "")
}

/// `base` is the relative prefix back to the doc root ("../" for `src/`).
fn page_at(title: &str, body: &str, base: &str) -> String {
    format!(
        "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
         <title>{}</title>\n<link rel=\"stylesheet\" href=\"{base}doc.css\">\n</head>\n\
         <body>\n<main>\n{}</main>\n<script src=\"{base}doc.js\"></script>\n</body>\n</html>\n",
        markup::escape_html(title),
        body
    )
}

fn item_page(model: &DocModel, it: &DocItem) -> String {
    let links = link_map(model);
    let mut b = String::new();
    b.push_str("<p class=\"crumbs\"><a href=\"index.html\">&larr; index</a></p>\n");
    let _ = write!(
        b,
        "<h1><span class=\"kind kind-{}\">{}</span> {}</h1>\n",
        it.kind.slug(),
        it.kind.label(),
        markup::escape_html(&it.short)
    );
    let _ = write!(
        b,
        "<p class=\"fq\">{}</p>\n",
        markup::escape_html(&it.key)
    );
    if let Some(sig) = &it.sig {
        b.push_str("<pre class=\"signature\"><code>");
        b.push_str(&markup::linkify(sig, &links));
        b.push_str("</code></pre>\n");
    } else {
        b.push_str(
            "<p class=\"muted\">signature unavailable (elaboration failed for this item)</p>\n",
        );
    }
    if let Some(docs) = &it.docs {
        b.push_str("<div class=\"docs\">\n");
        b.push_str(&markup::to_html(docs));
        b.push_str("</div>\n");
    }
    // Members: only those carrying docs are listed (the signature block
    // already shows the structure, so undocumented members would duplicate).
    let documented: Vec<&super::model::DocMember> = it
        .members
        .iter()
        .filter(|m| m.docs.is_some())
        .collect();
    if !documented.is_empty() {
        b.push_str("<h2>Members</h2>\n");
        for m in documented {
            let _ = write!(
                b,
                "<div class=\"member\"><h3 id=\"member.{}\"><code>{}</code></h3>\n",
                markup::escape_html(&m.name),
                markup::escape_html(&m.name)
            );
            if let Some(sig) = &m.sig {
                let _ = write!(
                    b,
                    "<pre class=\"member-sig\"><code>{}</code></pre>\n",
                    markup::linkify(sig, &links)
                );
            }
            if let Some(docs) = &m.docs {
                b.push_str("<div class=\"docs\">\n");
                b.push_str(&markup::to_html(docs));
                b.push_str("</div>\n");
            }
            b.push_str("</div>\n");
        }
    }
    if !it.inherent_impls.is_empty() {
        b.push_str("<h2>Implementations</h2>\n");
        for &i in &it.inherent_impls {
            b.push_str(&impl_block(&model.impls[i], true, &links));
        }
    }
    if !it.trait_impls.is_empty() {
        let title = if it.kind == ItemKind::Trait {
            "Implementors"
        } else {
            "Trait implementations"
        };
        let _ = write!(b, "<h2>{title}</h2>\n");
        for &i in &it.trait_impls {
            b.push_str(&impl_block(&model.impls[i], false, &links));
        }
    }
    if let Some(src) = &it.source {
        let _ = write!(
            b,
            "<details class=\"source-block\"><summary>Source &mdash; {}:{}</summary>\n\
             <pre class=\"source\"><code>{}</code></pre>\n</details>\n",
            markup::escape_html(src.path.as_deref().unwrap_or(&src.uri)),
            src.line,
            markup::escape_html(&src.snippet)
        );
        if let Some(url) = &src.url {
            let _ = write!(
                b,
                "<p class=\"src-link\"><a href=\"{}\">view source</a></p>\n",
                markup::escape_html(url)
            );
        }
    }
    page(&format!("{} {}", it.kind.label(), it.key), &b)
}

fn impl_block(di: &DocImpl, inherent: bool, links: &HashMap<String, String>) -> String {
    let mut s = String::new();
    s.push_str("<div class=\"impl\">\n");
    let header = if inherent {
        format!("impl {}", di.self_type)
    } else {
        format!(
            "impl {} for {}",
            di.trait_name.clone().unwrap_or_default(),
            di.self_type
        )
    };
    let _ = write!(
        s,
        "<pre class=\"impl-sig\"><code>{}</code></pre>\n",
        markup::linkify(&header, links)
    );
    if !di.methods.is_empty() {
        s.push_str("<ul class=\"methods\">\n");
        for m in &di.methods {
            s.push_str("<li>");
            match &m.sig {
                Some(sig) => {
                    let _ = write!(s, "<code>{}</code>", markup::linkify(sig, links));
                }
                None => {
                    let _ = write!(s, "<code>{}</code>", markup::escape_html(&m.name));
                }
            }
            if let Some(docs) = &m.docs {
                s.push_str("<div class=\"docs\">");
                s.push_str(&markup::to_html(docs));
                s.push_str("</div>");
            }
            s.push_str("</li>\n");
        }
        s.push_str("</ul>\n");
    }
    s.push_str("</div>\n");
    s
}

fn index_page(model: &DocModel) -> String {
    let mut b = String::new();
    let _ = write!(b, "<h1>{}</h1>\n", markup::escape_html(&model.project));
    let coverage = if model.items.is_empty() {
        0.0
    } else {
        100.0 * model.documented as f64 / model.items.len() as f64
    };
    let _ = write!(
        b,
        "<p class=\"muted\">root: {} &middot; {} items &middot; {}/{} documented ({:.0}%)</p>\n",
        markup::escape_html(&model.root),
        model.items.len(),
        model.documented,
        model.items.len(),
        coverage
    );
    b.push_str(
        "<input id=\"search\" type=\"search\" placeholder=\"Search items...\" autocomplete=\"off\">\n\
         <div id=\"results\"></div>\n<div id=\"listing\">\n",
    );
    for pkg in &model.packages {
        let title = if pkg.path.is_empty() {
            "(root)"
        } else {
            pkg.path.as_str()
        };
        let _ = write!(b, "<h2>{}</h2>\n", markup::escape_html(title));
        if let Some(docs) = &pkg.docs {
            b.push_str("<div class=\"docs pkg-docs\">\n");
            b.push_str(&markup::to_html(docs));
            b.push_str("</div>\n");
        }
        b.push_str("<ul class=\"items\">\n");
        let mut by_kind: Vec<(ItemKind, Vec<&DocItem>)> = Vec::new();
        for &i in &pkg.items {
            let it = &model.items[i];
            match by_kind.iter_mut().find(|(k, _)| *k == it.kind) {
                Some((_, v)) => v.push(it),
                None => by_kind.push((it.kind, vec![it])),
            }
        }
        by_kind.sort_by_key(|(k, _)| k.sort_key());
        for (k, list) in by_kind {
            let _ = write!(b, "<li class=\"kind-head\">{}</li>\n", k.label());
            for it in list {
                let _ = write!(
                    b,
                    "<li><a href=\"{}\">{}</a> <span class=\"key\">{}</span></li>\n",
                    markup::escape_html(&it.url),
                    markup::escape_html(&it.short),
                    markup::escape_html(&it.key)
                );
            }
        }
        b.push_str("</ul>\n");
    }
    b.push_str("</div>\n");
    if !model.warnings.is_empty() {
        b.push_str("<details class=\"warnings\"><summary>warnings</summary>\n<ul>\n");
        for w in &model.warnings {
            let _ = write!(b, "<li>{}</li>\n", markup::escape_html(w));
        }
        b.push_str("</ul>\n</details>\n");
    }
    page(&model.project, &b)
}

fn search_index(model: &DocModel) -> String {
    let arr: Vec<serde_json::Value> = model
        .items
        .iter()
        .map(|it| {
            let desc: String = it
                .docs
                .as_deref()
                .unwrap_or("")
                .replace('\n', " ")
                .chars()
                .take(140)
                .collect();
            serde_json::json!({
                "n": it.short,
                "k": it.kind.label(),
                "u": it.url,
                "f": it.key,
                "d": desc,
            })
        })
        .collect();
    let json = serde_json::to_string(&arr).unwrap_or_else(|_| "[]".to_string());
    format!("window.TYPORT_SEARCH = {json};\n")
}
