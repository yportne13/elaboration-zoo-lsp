//! surface：L13 的 owned 观察快照契约（L07/L08/L09–L12 的**上游原版**，本文件是把它
//! 从 `Infer` 上散落的六张表收敛成一个可整体交出的结构）。
//!
//! 设计不变式（与 L07–L12 一致）：表里只放 owned 值（`Span<()>` + `String`），
//! `Rc<Val>` / bump 分配的项都不跨表存活；消费端（`src/lib.rs` 的 LSP 层）只做查询与
//! 拷贝，不再对 live `Infer` 求值。
//!
//! L13 与下游各层的差异：
//! - `completion` 的键是 `SmolStr`（不是 L07 的 `String`）——沿用 L13 既有口径；
//! - `println` 通道**不在**快照里：L13 的 println 是「延迟作业」（`println_jobs`），
//!   由 `src/lib.rs` 在轮末统一执行，快照只带 span + 渲染串的对应关系（`println_spans`）；
//! - `check_issues` 走 `accumulated_errors`（每轮检查的错误列表），本快照只搬运计数与
//!   已渲染的文本，不做分流。

use crate::parser_lib::Span;

use super::{HoverEntry, Infer};

/// 一轮（一次 run* 调用）的观察面快照。字段顺序与 L07–L12 的 `LspSurface` 对齐。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LspSurface {
    /// 悬浮：使用处 span → 定义处 span → 渲染后的类型串。
    pub hover: Vec<HoverEntry>,
    /// 补全候选 (receiver span, 名字)。L13 用 `SmolStr`（既有口径）。
    pub completion: Vec<(Span<()>, smol_str::SmolStr)>,
    /// inlay hint (插入点字节偏移, ": <type>")。
    pub inlay_hint: Vec<(u32, String)>,
    /// 已完成 println 的 (体 span, 渲染串)。
    pub println_spans: Vec<(Span<()>, String)>,
    /// 本轮累积的类型错误（已渲染成单行，给 LSP 逐条诊断用）。
    pub check_issues: Vec<String>,
    /// 本轮失败的 decl 名字（A2 根因抑制用）。
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

    /// `hover_entry_at` 的文本快捷。
    pub fn hover_text_at(&self, path_id: u32, offset: usize) -> Option<&str> {
        self.hover_entry_at(path_id, offset).map(|e| e.2.as_str())
    }

    /// 全部通道是否为空。
    pub fn is_empty(&self) -> bool {
        self.hover.is_empty()
            && self.completion.is_empty()
            && self.inlay_hint.is_empty()
            && self.println_spans.is_empty()
            && self.check_issues.is_empty()
            && self.failed_decls.is_empty()
    }
}

/// 观察面的**查询口径**（惰性采集）：hover 是光标偏移，inlay 是可见区字节区间。
/// `None` = 该通道全量。语义与 L07–L12 的同名结构一致。
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

impl Infer {
    /// 悬停条目是否要采：采集总闸 + 可选的按偏移采集过滤。
    #[inline]
    pub(crate) fn hover_wanted(&self, span: Span<()>) -> bool {
        self.lsp_collect && self.hover_query.map_or(true, |q| span.contains(q))
    }

    /// inlay 条目是否要采：采集总闸 + 可选的可见区过滤。
    #[inline]
    pub(crate) fn inlay_wanted(&self, offset: u32) -> bool {
        self.lsp_collect && self.inlay_query.map_or(true, |(lo, hi)| offset >= lo && offset <= hi)
    }

    /// 应用一次查询口径（`SurfaceQuery`）。
    pub fn set_surface_query(&mut self, q: SurfaceQuery) {
        self.hover_query = q.hover;
        self.inlay_query = q.inlay;
    }

    /// 从当前 `Infer` 的六张表快照出一个 owned `LspSurface`。
    ///
    /// 这是 LSP 侧唯一应当读取的观察面入口：调用方拿到 owned 值后即可释放 `Infer`。
    pub fn lsp_surface(&self) -> LspSurface {
        LspSurface {
            hover: self.hover_table.clone(),
            completion: self.completion_table.clone(),
            inlay_hint: self.inlay_hint_table.clone(),
            println_spans: self.println_spans(),
            check_issues: self.accumulated_errors.iter().map(|e| e.0.data.to_string()).collect(),
            failed_decls: self.failed_decls.iter().map(|x| x.to_string()).collect(),
        }
    }

    /// println 通道：`println_jobs` 里的体 span。
    ///
    /// L13 的 println 是**延迟作业**（`PrintlnJob` 存的是未求值的 `tm` + 上下文，
    /// 渲染在轮末由 `src/lib.rs` 执行），所以快照在这里只能给 span —— 渲染串由
    /// 消费方从作业执行结果拿到，不在观察面里重复存。
    pub fn println_spans(&self) -> Vec<(Span<()>, String)> {
        self.println_jobs
            .iter()
            .map(|j| (j.span, String::new()))
            .collect()
    }

    /// 清空观察面六张表（prelude 装载收尾 / 逐文件重置用）。
    pub fn clear_observation_tables(&mut self) {
        self.hover_table.clear();
        self.hover_table.shrink_to_fit();
        self.completion_table.clear();
        self.inlay_hint_table.clear();
        self.accumulated_errors.clear();
        self.failed_decls.clear();
        self.decl_shapes.borrow_mut().clear();
    }
}
