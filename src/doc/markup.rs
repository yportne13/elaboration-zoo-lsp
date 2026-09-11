//! Doc-comment extraction and a small Markdown subset renderer.
//!
//! `///` doc comments are *not* lexer-level: they are ordinary `//` line
//! comments, so the AST carries no documentation.  Like the hover path
//! (`Backend::hover_doc_text`), we recover them textually by scanning the
//! source lines immediately above a declaration's name token.
//!
//! The Markdown renderer intentionally covers only the subset the language
//! and the hover path already speak: paragraphs, ATX headings, fenced code,
//! inline code, emphasis, links and single-level lists.  Anything else is
//! left as literal text rather than silently mangled.

use std::collections::HashMap;

/// Extract the `///` block immediately above a declaration from the text
/// *before* it.  Shared by hover (`Backend::hover_doc_text`) and doc
/// generation so the two can never drift.
///
/// Complete lines above the declaration are scanned upward until a non-`///`
/// line; the `///` marker and one following space are stripped; lines are
/// joined with `\n`.
pub fn extract_doc_prefix(before: &str) -> Option<String> {
    // Cut after the last newline so the declaration's own partial line
    // (`def foo…`) is skipped without discarding separating blank lines.
    let cut = before.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let above = &before[..cut];
    let mut docs: Vec<&str> = Vec::new();
    for line in above.lines().rev() {
        match line.trim_start().strip_prefix("///") {
            Some(rest) => docs.push(rest.strip_prefix(' ').unwrap_or(rest)),
            None => break,
        }
    }
    if docs.is_empty() {
        return None;
    }
    docs.reverse();
    Some(docs.join("\n"))
}

/// Extract the `///` block immediately above `start_offset` in `text`.
pub fn extract_doc_text(text: &str, start_offset: u32) -> Option<String> {
    let start = start_offset as usize;
    if start > text.len() || !text.is_char_boundary(start) {
        return None;
    }
    extract_doc_prefix(&text[..start])
}

/// Leading `//!` block at the top of a file (module / package docs).  Blank
/// lines before the first `//!` are tolerated; the first non-`//!` line ends
/// the run.
pub fn extract_inner_doc(text: &str) -> Option<String> {
    let mut docs: Vec<&str> = Vec::new();
    for line in text.lines() {
        let t = line.trim_start();
        if let Some(rest) = t.strip_prefix("//!") {
            docs.push(rest.strip_prefix(' ').unwrap_or(rest));
        } else if t.is_empty() && docs.is_empty() {
            continue;
        } else {
            break;
        }
    }
    if docs.is_empty() {
        None
    } else {
        Some(docs.join("\n"))
    }
}

pub fn escape_html(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        push_escaped(&mut out, c);
    }
    out
}

fn push_escaped(out: &mut String, c: char) {
    match c {
        '&' => out.push_str("&amp;"),
        '<' => out.push_str("&lt;"),
        '>' => out.push_str("&gt;"),
        '"' => out.push_str("&quot;"),
        _ => out.push(c),
    }
}

/// Linkify an already-rendered signature string: identifier runs (including
/// dotted chains) that exactly match a known item name become links.  Names
/// must be unambiguous — the caller's map only contains unique short names
/// and full keys.
pub fn linkify(sig: &str, links: &HashMap<String, String>) -> String {
    let mut out = String::with_capacity(sig.len());
    let mut token = String::new();
    for c in sig.chars() {
        if c.is_alphanumeric() || c == '_' || c == '.' {
            token.push(c);
        } else {
            flush_token(&mut token, &mut out, links);
            push_escaped(&mut out, c);
        }
    }
    flush_token(&mut token, &mut out, links);
    out
}

fn flush_token(token: &mut String, out: &mut String, links: &HashMap<String, String>) {
    if token.is_empty() {
        return;
    }
    match links.get(token.as_str()) {
        Some(url) => out.push_str(&format!(
            "<a href=\"{}\">{}</a>",
            escape_html(url),
            escape_html(token)
        )),
        None => out.push_str(&escape_html(token)),
    }
    token.clear();
}

/// Render a Markdown subset to HTML.  Input is raw doc text (not escaped).
pub fn to_html(md: &str) -> String {
    let lines: Vec<&str> = md.lines().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim_end();
        let trimmed = line.trim_start();

        if let Some(fence) = fence_marker(trimmed) {
            let lang = trimmed[fence.len()..].trim();
            let mut code = String::new();
            i += 1;
            while i < lines.len() {
                let l = lines[i];
                if l.trim_start().starts_with(fence) {
                    i += 1;
                    break;
                }
                code.push_str(l);
                code.push('\n');
                i += 1;
            }
            out.push_str("<pre><code");
            if !lang.is_empty() {
                out.push_str(&format!(" class=\"language-{}\"", escape_html(lang)));
            }
            out.push('>');
            out.push_str(&escape_html(&code));
            out.push_str("</code></pre>\n");
            continue;
        }

        if line.trim().is_empty() {
            i += 1;
            continue;
        }

        if let Some((level, body)) = heading(line) {
            out.push_str(&format!(
                "<h{level}>{}</h{level}>\n",
                inline(body.trim())
            ));
            i += 1;
            continue;
        }

        // Setext heading: a text line followed by `===` / `---`.
        if i + 1 < lines.len() && !trimmed.is_empty() && !is_hr(trimmed) {
            if let Some(level) = setext_level(lines[i + 1]) {
                out.push_str(&format!("<h{level}>{}</h{level}>\n", inline(trimmed)));
                i += 2;
                continue;
            }
        }

        if is_hr(trimmed) {
            out.push_str("<hr>\n");
            i += 1;
            continue;
        }

        if trimmed.starts_with('>') {
            let mut inner = String::new();
            while i < lines.len() {
                let lt = lines[i].trim_start();
                let Some(rest) = lt.strip_prefix('>') else {
                    break;
                };
                inner.push_str(rest.strip_prefix(' ').unwrap_or(rest));
                inner.push('\n');
                i += 1;
            }
            out.push_str("<blockquote>\n");
            out.push_str(&to_html(&inner));
            out.push_str("</blockquote>\n");
            continue;
        }

        if trimmed.contains('|') && i + 1 < lines.len() && is_table_sep(lines[i + 1]) {
            let header = table_cells(trimmed);
            i += 2;
            out.push_str("<table>\n<thead><tr>");
            for c in &header {
                out.push_str(&format!("<th>{}</th>", inline(c)));
            }
            out.push_str("</tr></thead>\n<tbody>\n");
            while i < lines.len() {
                let lt = lines[i].trim();
                if lt.is_empty() || !lt.contains('|') {
                    break;
                }
                out.push_str("<tr>");
                for c in table_cells(lt) {
                    out.push_str(&format!("<td>{}</td>", inline(&c)));
                }
                out.push_str("</tr>\n");
                i += 1;
            }
            out.push_str("</tbody></table>\n");
            continue;
        }

        if ul_marker(trimmed).is_some() {
            out.push_str("<ul>\n");
            while i < lines.len() {
                match ul_marker(lines[i].trim_start().trim_end()) {
                    Some(rest) => {
                        out.push_str(&format!("<li>{}</li>\n", inline(rest.trim())));
                        i += 1;
                    }
                    None => break,
                }
            }
            out.push_str("</ul>\n");
            continue;
        }

        if ol_marker(trimmed).is_some() {
            out.push_str("<ol>\n");
            while i < lines.len() {
                match ol_marker(lines[i].trim_start().trim_end()) {
                    Some(rest) => {
                        out.push_str(&format!("<li>{}</li>\n", inline(rest.trim())));
                        i += 1;
                    }
                    None => break,
                }
            }
            out.push_str("</ol>\n");
            continue;
        }

        // Paragraph: consume until a blank line or a block starter.
        let mut para = String::new();
        while i < lines.len() {
            let l = lines[i].trim_end();
            if l.trim().is_empty() {
                break;
            }
            let lt = l.trim_start();
            if fence_marker(lt).is_some()
                || heading(l).is_some()
                || ul_marker(lt).is_some()
                || ol_marker(lt).is_some()
                || is_hr(lt)
                || lt.starts_with('>')
                || (lt.contains('|') && i + 1 < lines.len() && is_table_sep(lines[i + 1]))
                || (i + 1 < lines.len() && setext_level(lines[i + 1]).is_some())
            {
                break;
            }
            if !para.is_empty() {
                para.push(' ');
            }
            para.push_str(l.trim());
            i += 1;
        }
        out.push_str(&format!("<p>{}</p>\n", inline(&para)));
    }
    out
}

fn fence_marker(s: &str) -> Option<&'static str> {
    if s.starts_with("```") {
        Some("```")
    } else if s.starts_with("~~~") {
        Some("~~~")
    } else {
        None
    }
}

fn heading(line: &str) -> Option<(usize, &str)> {
    let t = line.trim_start();
    let hashes = t.chars().take_while(|&c| c == '#').count();
    if hashes == 0 || hashes > 6 || t.len() <= hashes || t.as_bytes()[hashes] != b' ' {
        return None;
    }
    // `#` is reserved for the item title; doc headings start at h2.
    Some(((hashes + 1).min(6), &t[hashes..]))
}

/// A horizontal rule: 3+ identical `-`, `*` or `_`.
fn is_hr(s: &str) -> bool {
    let t = s.trim();
    let mut chars = t.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !matches!(first, '-' | '*' | '_') {
        return false;
    }
    t.len() >= 3 && chars.all(|c| c == first)
}

/// Setext underline level: `===` -> h2, `---` -> h3.
fn setext_level(line: &str) -> Option<usize> {
    let t = line.trim();
    if t.is_empty() {
        return None;
    }
    if t.chars().all(|c| c == '=') {
        Some(2)
    } else if t.chars().all(|c| c == '-') {
        Some(3)
    } else {
        None
    }
}

fn is_table_sep(line: &str) -> bool {
    let cols: Vec<&str> = line
        .trim()
        .trim_matches('|')
        .split('|')
        .map(|c| c.trim())
        .collect();
    !cols.is_empty()
        && cols.iter().all(|c| {
            !c.is_empty()
                && c.chars().all(|ch| ch == '-' || ch == ':')
                && c.contains('-')
        })
}

fn table_cells(line: &str) -> Vec<String> {
    line.trim()
        .trim_matches('|')
        .split('|')
        .map(|c| c.trim().to_string())
        .collect()
}

fn ul_marker(s: &str) -> Option<&str> {
    for m in ["- ", "* ", "+ "] {
        if let Some(rest) = s.strip_prefix(m) {
            return Some(rest);
        }
    }
    None
}

fn ol_marker(s: &str) -> Option<&str> {
    let digits = s.chars().take_while(|c| c.is_ascii_digit()).count();
    if digits == 0 {
        return None;
    }
    let rest = &s[digits..];
    rest.strip_prefix(". ")
}

/// Inline Markdown: code spans, links, strong and emphasis.  HTML is escaped
/// as it is emitted; nested emphasis recurses only on the emphasised slice.
pub fn inline(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '`' {
            if let Some(j) = find_char(&chars, i + 1, '`') {
                let code: String = chars[i + 1..j].iter().collect();
                out.push_str("<code>");
                out.push_str(&escape_html(code.trim()));
                out.push_str("</code>");
                i = j + 1;
                continue;
            }
        }
        if c == '[' {
            if let Some(close) = find_char(&chars, i + 1, ']') {
                if close + 1 < chars.len() && chars[close + 1] == '(' {
                    if let Some(rp) = find_char(&chars, close + 2, ')') {
                        let text: String = chars[i + 1..close].iter().collect();
                        let url: String = chars[close + 2..rp].iter().collect();
                        let url = url.trim();
                        let external = url.starts_with("http://") || url.starts_with("https://");
                        out.push_str(&format!(
                            "<a href=\"{}\"{}>{}</a>",
                            escape_html(url),
                            if external {
                                " target=\"_blank\" rel=\"noopener\""
                            } else {
                                ""
                            },
                            inline(text.trim())
                        ));
                        i = rp + 1;
                        continue;
                    }
                }
            }
        }
        if c == '*' {
            if i + 1 < chars.len() && chars[i + 1] == '*' {
                if let Some(j) = find_pair(&chars, i + 2, "**") {
                    let inner: String = chars[i + 2..j].iter().collect();
                    out.push_str("<strong>");
                    out.push_str(&inline(&inner));
                    out.push_str("</strong>");
                    i = j + 2;
                    continue;
                }
            } else if let Some(j) = find_char(&chars, i + 1, '*') {
                let inner: String = chars[i + 1..j].iter().collect();
                out.push_str("<em>");
                out.push_str(&inline(&inner));
                out.push_str("</em>");
                i = j + 1;
                continue;
            }
        }
        push_escaped(&mut out, c);
        i += 1;
    }
    out
}

fn find_char(chars: &[char], from: usize, needle: char) -> Option<usize> {
    (from..chars.len()).find(|&i| chars[i] == needle)
}

fn find_pair(chars: &[char], from: usize, needle: &str) -> Option<usize> {
    let n: Vec<char> = needle.chars().collect();
    if n.is_empty() || from + n.len() > chars.len() {
        return None;
    }
    (from..=chars.len() - n.len()).find(|&i| chars[i..i + n.len()] == n[..])
}
