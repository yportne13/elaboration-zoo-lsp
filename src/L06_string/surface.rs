//! surface：两版引擎共用的 **owned 观察快照**契约（LSP 引擎侧接线阶段 0 的
//! L06 版，对应 `docs/lsp-twin-wiring-2026-09.md` §0 与
//! `docs/l06-lsp-port-2026-11-20.md` §1.10）。
//!
//! 设计要点（与 L13 逐条对齐，差异只在 L06 的语言面）：
//!
//! 1. **表里只放 owned 值**：`Span<()>`（`Copy`）+ `String`。参考版与孪生的
//!    项表示（`Rc<Tm>` / bump `Tm`）都不跨表存活，消费端不再对 live `Val`
//!    做 quote——这是 bump arena 唯一可行的契约形态。
//! 2. **`hover_entry_at` 取同 path 内含 offset 的最小 span**（L13
//!    `mod.rs:1613-1619` / `bump_spine_iter/observe.rs:189-199` 同规则）：
//!    更窄的条目（binder 名、字面量）压过更宽的（整条 def 类型/整条 println）。
//! 3. **`completion` 恒空**：L06 没有成员访问（`Raw` 无 `Obj`，parser 不消费
//!    `.`），无从产生候选。字段保留是为了与 L13 的三表契约同型。
//! 4. **失败 decl** 用 `Vec<String>`（保留首次失败序）而不是 `HashSet`：
//!    L06 的失败集规模是 decl 数级，`contains` 线性扫足够，且快照可比对。
//!
//! span 来源一律是**共享 parser AST**（`Span<String>`），不是引擎的 `Tm`：
//! 孪生的 `Tm` 不存 span（`bump_spine_iter/syntax.rs`），参考版项里的 span
//! 也不能当源码位置用（`empty_span` 遍布）。L06 的 `Raw` 只有叶子带自己的
//! span，故 [`raw_span`] 按节点折叠；`Raw::Hole` / `Raw::U` 没有 span，
//! 折叠结果退化到邻近叶子（见各臂注释）。

use crate::parser_lib::{Span, ToSpan};

use super::empty_span;
use super::parser::syntax::{Decl, Raw};

/// 一条 hover 条目：`(使用处 span, 定义处 span, 渲染串)`。与 L13
/// `HoverEntry`（`L13_namespace/mod.rs:1459`）逐字段同型。
pub type HoverEntry = (Span<()>, Span<()>, String);

/// 观察面的**查询口径**（惰性采集）：`hover` 是光标偏移（只渲染命中它的悬停
/// 条目），`inlay` 是可见区字节区间（只渲染插入点落在其中的 inlay——inlay 是
/// 全文件通道，LSP 一次 inlay 请求也带可见区）。`None` = 该通道全量。
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

/// 一轮（一次 `run*` 调用）的观察面快照。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LspSurface {
    /// 悬浮：使用处 span → 定义处 span → 渲染后的类型串。
    pub hover: Vec<HoverEntry>,
    /// 补全候选 `(receiver span, 名字)`。L06 恒空（无成员访问），字段仅为
    /// 与 L13 三表契约同型。
    pub completion: Vec<(Span<()>, String)>,
    /// inlay hint `(插入点字节偏移, ": <type>")`。
    pub inlay_hint: Vec<(u32, String)>,
    /// println 输出 `(println 体的 span, 渲染串)`——LSP 侧 INFORMATION 诊断。
    pub println_spans: Vec<(Span<()>, String)>,
    /// HDL 自检行 `(decl 下标, "code|module|signal|message")`——WARNING 诊断。
    pub check_issues: Vec<(usize, String)>,
    /// 本轮失败的 decl 名字（opt-in 继续驱动填充；见
    /// `docs/l06-lsp-port-2026-11-20.md` §1.5）。
    pub failed_decls: Vec<String>,
}

impl LspSurface {
    /// 与参考版 `Infer::hover_entry_at` / 孪生 `Machine::hover_entry_at`
    /// 同规则：同 `path_id` 内包含 `offset` 的条目里取 span 最窄的那个
    /// （并列取先入表者）。
    pub fn hover_entry_at(&self, path_id: u32, offset: usize) -> Option<&HoverEntry> {
        self.hover
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }

    /// [`Self::hover_entry_at`] 的文本快捷（测试/消费端常用）。
    pub fn hover_text_at(&self, path_id: u32, offset: usize) -> Option<&str> {
        self.hover_entry_at(path_id, offset).map(|e| e.2.as_str())
    }

    /// 三张观察表与两条通道是否全空（"默认关闭时什么都没采"的断言用）。
    pub fn is_empty(&self) -> bool {
        self.hover.is_empty()
            && self.completion.is_empty()
            && self.inlay_hint.is_empty()
            && self.println_spans.is_empty()
            && self.check_issues.is_empty()
            && self.failed_decls.is_empty()
    }
}

/// 两个 span 的并集（保持"空 span 不参与端点"的直觉）：
///
/// L06 的 `Raw` 里 `U` / `Hole` 没有 span，折叠时用 `empty_span(())`；若直接
/// 用 `Span::add`（`parser_lib.rs:158-169`，取左端 `start` + 右端 `end`），
/// `U` 在前会把 `path_id` 和起点都拉成 0。这里让**空 span 让位**给有内容的
/// 那个；两侧都空时保留左值。
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

/// `Raw` 的源码区间（折叠到能拿到的最外叶子）。**逐点与两版 elaboration
/// 的遍历序无关**：只依赖 AST 结构，故两版对同一源给出同一 span。
pub(crate) fn raw_span(t: &Raw) -> Span<()> {
    match t {
        Raw::Var(s) => s.to_span(),
        Raw::LiteralIntro(s) => s.to_span(),
        Raw::Lam(x, _, body) => span_union(x.to_span(), raw_span(body)),
        Raw::App(f, a, _) => span_union(raw_span(f), raw_span(a)),
        Raw::Pi(x, _, _, body) => span_union(x.to_span(), raw_span(body)),
        Raw::Let(x, _, _, body) => span_union(x.to_span(), raw_span(body)),
        // `U` / `Hole` 无 span：折叠为同 path 的零长区间（`path_id` 由
        // 邻近叶子提供；单独一个 `U` 作 println 体时只能是 0 号 path）。
        Raw::U | Raw::Hole => empty_span(()),
    }
}

/// `"code|module|signal|message"` → 人类可读的警告行。逐字节照 L13
/// `format_check_warning`（`L13_namespace/mod.rs:4633-4649`）：HDL/HDV 码打
/// `[hdl]` 标签、其余打 `[typort]`，signal 为空时不打冒号段。
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

/// 失败 decl 携带的名字集（L13 `failed_decl_names` 的 L06 版：
/// `L13_namespace/mod.rs:1643-1659`）。L06 只有 `Def` 有名字（`Println` 无）。
pub(crate) fn failed_decl_names(t: &Decl) -> Vec<String> {
    match t {
        Decl::Def { name, .. } => vec![name.data.clone()],
        Decl::Println(_) => vec![],
    }
}

/// 可变全局 `"CheckIssues"` 的内容按行切分（空行丢弃）。两版 prim 写进去的
/// 是同一个 `\n` 分隔串（`cxt.rs:57-79` / `bump_spine_iter/prim.rs:162-189`），
/// 故排水侧共用这一份切分规则。
pub(crate) fn split_issue_lines(text: &str) -> impl Iterator<Item = &str> {
    text.split('\n').filter(|l| !l.is_empty())
}

/// inlay hint 标签：`: <type>`，超 80 字符按字符截断并补省略号（L13
/// `push_inlay_hint` 同款，`elaboration.rs:488-494`）。
pub(crate) fn inlay_label(rendered: &str) -> String {
    let mut label = format!(": {}", rendered);
    const MAX_LEN: usize = 80;
    if label.chars().count() > MAX_LEN {
        let truncated: String = label.chars().take(MAX_LEN.saturating_sub(1)).collect();
        label = format!("{}\u{2026}", truncated);
    }
    label
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_span_folds_to_outer_leaf() {
        let src = "def f = x => x";
        let decls = super::super::parser::parser(src, 7).expect("parse");
        let Decl::Def { body, .. } = &decls[0] else { panic!() };
        let sp = raw_span(body);
        assert_eq!(sp.path_id, 7);
        // `x => x` 覆盖从首个 x 到体里的 x（不含 def 名）
        assert_eq!(&src[sp.start_offset as usize..sp.end_offset as usize], "x => x");
    }

    #[test]
    fn hover_entry_at_prefers_narrowest() {
        let (wide, narrow) = (
            (0, 20),
            (4, 8),
        );
        let s = LspSurface {
            hover: vec![
                (
                    Span { data: (), start_offset: wide.0, end_offset: wide.1, path_id: 1 },
                    Span { data: (), start_offset: 0, end_offset: 0, path_id: 1 },
                    "wide".to_owned(),
                ),
                (
                    Span { data: (), start_offset: narrow.0, end_offset: narrow.1, path_id: 1 },
                    Span { data: (), start_offset: 0, end_offset: 0, path_id: 1 },
                    "narrow".to_owned(),
                ),
            ],
            ..Default::default()
        };
        assert_eq!(s.hover_text_at(1, 5), Some("narrow"));
        assert_eq!(s.hover_text_at(1, 15), Some("wide"));
        // 别的 path / 界外一律 miss
        assert_eq!(s.hover_text_at(2, 5), None);
        assert_eq!(s.hover_text_at(1, 20), None);
    }

    #[test]
    fn check_warning_formatting() {
        assert_eq!(
            format_check_warning("HDL001|mod|sig|bad width"),
            "[hdl][warning] HDL001 [mod] sig: bad width"
        );
        assert_eq!(
            format_check_warning("TY001|mod||nat defaulted"),
            "[typort][warning] TY001 [mod] nat defaulted"
        );
        assert_eq!(format_check_warning("junk"), "[hdl][warning] junk");
    }

    #[test]
    fn inlay_label_truncates_by_chars() {
        assert_eq!(inlay_label("String"), ": String");
        let long = "x".repeat(200);
        let l = inlay_label(&long);
        assert_eq!(l.chars().count(), 80);
        assert!(l.ends_with('\u{2026}'));
    }
}
