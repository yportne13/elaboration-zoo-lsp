//! surface：L09_mltt 的 owned 观察快照契约（L07/L08 的平移）。
//!
//! 设计对齐 L06（docs/l06-lsp-port-2026-11-20.md §1.10 / §3）与 L13 的
//! 「阶段 0 契约」：表里只放 owned 值（Span<()> + String），bump/Rc<Val>
//! 都不跨表存活；消费端只做 pretty/查询，不再对 live Val 求值。
//!
//! L07 与 L06 的差异（都是语言面带来的）：
//! - Raw 多了 Obj（字段投影）/ Match / Sum / SumCase（构造子），
//!   故 raw_span 按这些形态折叠；
//! - Decl 与 L07 同形（含 Enum）：失败 decl 的名字集要带构造子限定键（E.c）；
//! - 观察表多一条「构造子 hover」通道（见 observe.rs 的 push_ctor_hover）。
//!
//! span 来源一律是共享 parser AST（Span<String>）；Raw::Hole / Raw::U
//! 没有源码 span，折叠结果退化到邻近叶子。

use crate::parser_lib::{Span, ToSpan};

use super::empty_span;
use super::parser::syntax::{Decl, Pattern, Raw};

/// 一条 hover 条目：(使用处 span, 定义处 span, 渲染串)。与 L06/L13 逐字段同型。
pub type HoverEntry = (Span<()>, Span<()>, String);

/// 一轮（一次 run* 调用）的观察面快照。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LspSurface {
    /// 悬浮：使用处 span → 定义处 span → 渲染后的类型串。
    pub hover: Vec<HoverEntry>,
    /// 补全候选 (receiver span, 名字)。L07 有成员投影与限定构造子，但候选集
    /// 需要按 receiver 类型过滤——留待后续（当前恒空，契约字段保留）。
    pub completion: Vec<(Span<()>, String)>,
    /// inlay hint (插入点字节偏移, ": <type>")。
    pub inlay_hint: Vec<(u32, String)>,
    /// println 输出 (println 体的 span, 渲染串)。
    pub println_spans: Vec<(Span<()>, String)>,
    /// 自检行 (decl 下标, "code|module|signal|message")：L07 的
    /// report_check_issue builtin 写入 CheckIssues 全局，本通道只读排水。
    pub check_issues: Vec<(usize, String)>,
    /// 本轮失败的 decl 名字（opt-in 继续驱动填充）。
    pub failed_decls: Vec<String>,
}

impl LspSurface {
    /// 同 path_id 内包含 offset 的条目里取 span 最窄者（并列取先入表）。
    pub fn hover_entry_at(&self, path_id: u32, offset: usize) -> Option<&HoverEntry> {
        self.hover
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }

    /// hover_entry_at 的文本快捷。
    pub fn hover_text_at(&self, path_id: u32, offset: usize) -> Option<&str> {
        self.hover_entry_at(path_id, offset).map(|e| e.2.as_str())
    }

    /// 全部通道是否为空（"默认关闭时什么都没采"的断言用）。
    pub fn is_empty(&self) -> bool {
        self.hover.is_empty()
            && self.completion.is_empty()
            && self.inlay_hint.is_empty()
            && self.println_spans.is_empty()
            && self.check_issues.is_empty()
            && self.failed_decls.is_empty()
    }
}

/// 观察面的**查询口径**（惰性采集）：hover 是光标偏移（只渲染命中它的悬停
/// 条目），inlay 是可见区字节区间（只渲染锚点落在其中的 inlay）。None =
/// 该通道全量。语义与 L06 的同名结构一致。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SurfaceQuery {
    pub hover: Option<usize>,
    pub inlay: Option<(u32, u32)>,
}

impl SurfaceQuery {
    /// 只关心一个光标的悬停（inlay 全量）。
    pub fn hover_only(offset: usize) -> Self {
        Self { hover: Some(offset), inlay: None }
    }

    /// 光标 + 可见区（LSP 一次请求的常见形态）。
    pub fn view(hover: usize, inlay_start: u32, inlay_end: u32) -> Self {
        Self { hover: Some(hover), inlay: Some((inlay_start, inlay_end)) }
    }
}

/// 两个 span 的并集（空 span 让位；两侧都空时保留左值）。
pub(crate) fn span_union(a: Span<()>, b: Span<()>) -> Span<()> {
    let a_empty = a.start_offset == a.end_offset;
    let b_empty = b.start_offset == b.end_offset;
    match (a_empty, b_empty) {
        (true, true) => a,
        (true, false) => b,
        (false, true) => a,
        (false, false) => Span {
            data: (),
            start_offset: a.start_offset.min(b.start_offset),
            end_offset: a.end_offset.max(b.end_offset),
            path_id: a.path_id,
        },
    }
}

/// Raw 的源码区间（折叠到能拿到的最外叶子）。只依赖 AST 结构。
pub(crate) fn raw_span(t: &Raw) -> Span<()> {
    match t {
        Raw::Var(s) => s.to_span(),
        Raw::LiteralIntro(s) => s.to_span(),
        Raw::Obj(x, f) => span_union(raw_span(x), f.to_span()),
        Raw::Lam(x, _, body) => span_union(x.to_span(), raw_span(body)),
        Raw::App(f, a, _) => span_union(raw_span(f), raw_span(a)),
        Raw::Pi(x, _, a, b) => span_union(x.to_span(), span_union(raw_span(a), raw_span(b))),
        Raw::Let(x, a, t2, u) => span_union(
            x.to_span(),
            span_union(raw_span(a), span_union(raw_span(t2), raw_span(u))),
        ),
        Raw::U(_) | Raw::Hole => empty_span(()),
        // match：scrutinee ∪ 各臂（模式 span ∪ 体 span）
        Raw::Match(scrut, arms) => arms.iter().fold(raw_span(scrut), |acc, (p, body)| {
            span_union(acc, span_union(pattern_span(p), raw_span(body)))
        }),
        // enum 声明表达式：名字 ∪ 参数域 ∪ 构造子名
        Raw::Sum(n, params, cases, _) => {
            let s = params
                .iter()
                .fold(n.to_span(), |acc, (_, _, a)| span_union(acc, raw_span(a)));
            cases.iter().fold(s, |acc, c| span_union(acc, c.to_span()))
        }
        Raw::SumCase { typ, case_name, datas } => datas.iter().fold(
            span_union(case_name.to_span(), raw_span(typ)),
            |acc, (_, r, _)| span_union(acc, raw_span(r)),
        ),
    }
}

/// Pattern 的源码区间（模式本身带 Span<()>；子模式递归）。
fn pattern_span(p: &Pattern) -> Span<()> {
    match p {
        Pattern::Any(s, _) => *s,
        Pattern::Con(n, subs, _) => subs
            .iter()
            .fold(n.to_span(), |acc, sub| span_union(acc, pattern_span(sub))),
    }
}

/// inlay 标签：": <type>"，超 80 字符按字符截断并补省略号（L06/L13 同口径）。
pub(crate) fn inlay_label(rendered: &str) -> String {
    let mut label = format!(": {}", rendered);
    const MAX_LEN: usize = 80;
    if label.chars().count() > MAX_LEN {
        let truncated: String = label.chars().take(MAX_LEN.saturating_sub(1)).collect();
        label = format!("{}\u{2026}", truncated);
    }
    label
}

/// 失败 decl 携带的名字集：def 本名；enum 本名 + 各构造子限定键（E.c，与
/// decl 表键一致）；println 无名。
pub(crate) fn failed_decl_names(t: &Decl) -> Vec<String> {
    match t {
        Decl::Def { name, .. } => vec![name.data.to_string()],
        Decl::Enum { name, cases, .. } => {
            let mut v = vec![name.data.to_string()];
            v.extend(cases.iter().map(|(c, _, _)| format!("{}.{}", name.data, c.data)));
            v
        }
        Decl::Println(_) => vec![],
    }
}

/// "code|module|signal|message" → 人类可读的警告行（逐字节照 L06/L13）。
pub fn format_check_warning(line: &str) -> String {
    let parts: Vec<&str> = line.splitn(4, '|').collect();
    match parts.as_slice() {
        [code, module, signal, message] => {
            let tag = if code.starts_with("HDL") || code.starts_with("HDV") {
                "hdl"
            } else {
                "typort"
            };
            if signal.is_empty() {
                format!("[{}][warning] {} [{}] {}", tag, code, module, message)
            } else {
                format!("[{}][warning] {} [{}] {}: {}", tag, code, module, signal, message)
            }
        }
        _ => format!("[hdl][warning] {}", line),
    }
}

/// 可变全局 CheckIssues 的内容按行切分（空行丢弃）。
pub(crate) fn split_issue_lines(text: &str) -> impl Iterator<Item = &str> {
    text.split('\n').filter(|l| !l.is_empty())
}
