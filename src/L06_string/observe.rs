//! observe：参考版（`Infer` + `Cxt`）的观察面（LSP 引擎侧接线）——观察表的
//! push / 排水 / 清空 / 快照，独立 `impl Infer` 块承载（与 L13
//! `bump_spine_iter/observe.rs` 同拆分风格）。
//!
//! 契约见 [`super::surface`]：表里只放 owned `Span<()>` + `String`；push 期
//! 用站点上下文把类型引读成串（`quote → pretty_tm`），消费端不再需要 live
//! `Infer`。渲染管线与 `run` 的 println 输出同一条（`mod.rs` 的
//! `pretty_tm(0, cxt.names(), &nf)`），故两版逐字节可比。
//!
//! **总闸**：[`Infer::lsp_collect`] 默认 `false`（与 L13 相反，理由见
//! `docs/l06-lsp-port-2026-11-20.md` §1.1——L06 的 `run` / bench 口径不带
//! 渲染，且没有 prelude 装载段可豁免）。关闭时每个 push 点只多一次 `bool`
//! 判定。

use crate::parser_lib::{Span, ToSpan};

use super::pretty;
use super::syntax::Locals;
use super::surface::{inlay_label, split_issue_lines, HoverEntry, LspSurface};
use super::parser::syntax::Decl;
use super::*;

impl Infer {
    /// 悬停条目是否要采：采集总闸 + 可选的"按偏移采集"过滤（见
    /// [`Infer::hover_query`]）。**只影响 hover**——inlay / println /
    /// check issue 是全文件消费，仍按采集总闸走。
    #[inline]
    fn hover_wanted(&self, span: Span<()>) -> bool {
        self.lsp_collect && self.hover_query.map_or(true, |q| span.contains(q))
    }

    /// 观察表清空（轮入口用；`Infer` 每轮新建，本方法服务多轮复用的调用方）。
    pub(crate) fn clear_observation_tables(&mut self) {
        self.hover_table.clear();
        self.completion_table.clear();
        self.inlay_hint_table.clear();
        self.println_spans.clear();
        self.check_issue_lines.clear();
        self.issue_drained = 0;
    }

    /// push 期渲染：站点上下文引读 + pretty（与 `run` 的 println 同管线）。
    fn render_val(&self, cxt: &Cxt, v: &Rc<Val>) -> String {
        pretty::pretty_tm(0, cxt.names(), &self.quote(cxt.lvl, v))
    }

    /// 登记处类型渲染 + `final` 判定（L13 `render_typ_pretty` /
    /// `typ_pretty_final` 同义）：引出项无未解 meta 时，串与使用处实时渲染
    /// 逐字节一致，`push_hover_cached` 可安全复用。
    pub(crate) fn render_typ_pretty(&self, cxt: &Cxt, v: &Rc<Val>) -> (String, bool) {
        let q = self.quote(cxt.lvl, v);
        let final_ = !self.tm_has_unsolved_meta(&q);
        (pretty::pretty_tm(0, cxt.names(), &q), final_)
    }

    /// 项里是否有**未解** meta（`Tm::Meta` 指向 `MetaEntry::Unsolved`）。
    /// 迭代走查、零分配；只看 `quote` 产出的形态（无 `AppPruning`）。
    pub(crate) fn tm_has_unsolved_meta(&self, t: &Tm) -> bool {
        let mut stack: Vec<&Tm> = vec![t];
        while let Some(x) = stack.pop() {
            match x {
                Tm::Meta(m) => {
                    if matches!(self.lookup_meta(m), MetaEntry::Unsolved(_)) {
                        return true;
                    }
                }
                Tm::Var(_) | Tm::U | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Decl(_) => {}
                Tm::Lam(_, _, b) => stack.push(b),
                Tm::App(f, a, _) => {
                    stack.push(f);
                    stack.push(a);
                }
                Tm::AppPruning(h, _) => stack.push(h),
                Tm::Pi(_, _, a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                Tm::Let(_, a, v, u) => {
                    stack.push(a);
                    stack.push(v);
                    stack.push(u);
                }
            }
        }
        false
    }

    /// 观察面 hover：`(使用处 span, 定义处 span, 渲染串)`。
    pub(crate) fn push_hover(&mut self, cxt: &Cxt, t_span: Span<()>, def_span: Span<()>, v: &Rc<Val>) {
        if !self.hover_wanted(t_span) {
            return;
        }
        let rendered = self.render_val(cxt, v);
        self.hover_table.push((t_span, def_span, rendered));
    }

    /// 已有渲染串的 hover（def 定义处：渲染一次喂两处消费，L13 评审机会 4）。
    pub(crate) fn push_hover_rendered(&mut self, t_span: Span<()>, def_span: Span<()>, rendered: &str) {
        if !self.hover_wanted(t_span) {
            return;
        }
        self.hover_table.push((t_span, def_span, rendered.to_owned()));
    }

    /// 全局名使用处 hover：登记期串 `final` 时直推缓存（L13
    /// `push_hover_cached` 同款），否则实时渲染。`cached` 用 `Rc<String>`
    /// 而非 `&str`——调用方在 `self.decls` 上取完引用就要 `&mut self`
    /// push，两者不能同时借。
    pub(crate) fn push_hover_decl(
        &mut self,
        cxt: &Cxt,
        t_span: Span<()>,
        entry_span: Span<()>,
        cached: Option<Rc<String>>,
        cached_final: bool,
        v: &Rc<Val>,
    ) {
        if !self.hover_wanted(t_span) {
            return;
        }
        if let (Some(s), true) = (&cached, cached_final) {
            self.hover_table.push((t_span, entry_span, (**s).clone()));
            return;
        }
        let rendered = self.render_val(cxt, v);
        self.hover_table.push((t_span, entry_span, rendered));
    }

    /// 观察面 inlay：含未解 meta 的类型跳过，标签超 80 字符截断（L13
    /// `push_inlay_hint` 同口径）。
    pub(crate) fn push_inlay_hint(&mut self, cxt: &Cxt, offset: u32, v: &Rc<Val>) {
        if !self.lsp_collect {
            return;
        }
        let q = self.quote(cxt.lvl, v);
        if self.tm_has_unsolved_meta(&q) {
            return;
        }
        let label = inlay_label(&pretty::pretty_tm(0, cxt.names(), &q));
        self.inlay_hint_table.push((offset, label));
    }

    /// 已渲染的 inlay（def 返回类型：peel/quote/names 由调用方按各自引擎
    /// 的上下文拼好，标签格式统一在 [`super::surface::inlay_label`]）。
    pub(crate) fn push_inlay_label(&mut self, offset: u32, label: String) {
        if !self.lsp_collect {
            return;
        }
        self.inlay_hint_table.push((offset, label));
    }

    /// println 观察条目（driver 在渲染完 println 后调用；与 L13 孪生
    /// `println_spans` 同口径）。
    pub(crate) fn push_println_span(&mut self, span: Span<()>, rendered: &str) {
        if !self.lsp_collect {
            return;
        }
        self.println_spans.push((span, rendered.to_owned()));
    }

    /// HDL 自检行排水（L13 `take_fresh_check_issues` 的**只读**版）：
    /// 每 decl 把可变全局 `"CheckIssues"` 的**新增**行摘进观察表。
    ///
    /// 与 L13 的两点差异（都为了不动 L06 的 Ok 输出）：
    /// 1. **不清空**全局——L06 的 `DEMO_SRC` 把它当用户可见值打印
    ///    （`println (get_global "CheckIssues")`），清空会改输出；
    /// 2. 用 `issue_drained` 游标（已处理字节数）而不是 `CheckIssuesSeen`
    ///    全局：prim 只追加（行级去重），故游标后缀就是新增行，摊销 O(新增)。
    pub(crate) fn drain_check_issues(&mut self, decl_idx: usize) {
        if !self.lsp_collect {
            return;
        }
        let text = {
            let map = self.mutable_map.borrow();
            match map.get("CheckIssues") {
                Some(v) => match v.as_ref() {
                    Val::LiteralIntro(s) => s.data.clone(),
                    _ => String::new(),
                },
                None => String::new(),
            }
        };
        // 全局被外部改写（`change_mutable "CheckIssues"`）时游标可能越界
        if text.len() < self.issue_drained {
            self.issue_drained = 0;
        }
        if text.len() == self.issue_drained {
            return;
        }
        let fresh: Vec<String> = split_issue_lines(&text[self.issue_drained..])
            .map(|l| l.to_owned())
            .collect();
        self.issue_drained = text.len();
        for line in fresh {
            self.check_issue_lines.push((decl_idx, line));
        }
    }

    /// 失败 decl 的名字集记入本通道（L13 `note_failed_decl` 的记录面；
    /// 消费面见 `docs/l06-lsp-port-2026-11-20.md` §1.5）。
    pub(crate) fn note_failed_decl(&mut self, d: &Decl) {
        for n in super::surface::failed_decl_names(d) {
            if !self.failed_decls.contains(&n) {
                self.failed_decls.push(n);
            }
        }
    }

    /// 本轮 owned 快照。
    pub(crate) fn surface(&self) -> LspSurface {
        LspSurface {
            hover: self.hover_table.clone(),
            completion: self.completion_table.clone(),
            inlay_hint: self.inlay_hint_table.clone(),
            println_spans: self.println_spans.clone(),
            check_issues: self.check_issue_lines.clone(),
            failed_decls: self.failed_decls.clone(),
        }
    }

    /// 与 L13 `Infer::hover_entry_at` 同规则（同 path 内含 offset 的最小 span）。
    pub(crate) fn hover_entry_at(&self, path_id: u32, offset: usize) -> Option<&HoverEntry> {
        self.hover_table
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }

    /// 局部 binder 的定义处 span：`Locals` 链按层回走（`bind` / `define` /
    /// `new_binder` 各压一层，与 `lvl` 同序）。**只在采集开启时**被调用，
    /// 故这条 O(深度) 走查不进热路径。
    pub(crate) fn local_binder_span(&self, cxt: &Cxt, blvl: Lvl) -> Span<()> {
        let mut cur = cxt.lvl.0;
        let mut ls = &cxt.locals;
        loop {
            cur -= 1;
            match ls {
                Locals::Here => return empty_span(()),
                Locals::Bind(prev, x, _) => {
                    if cur == blvl.0 {
                        return x.to_span();
                    }
                    ls = prev.as_ref();
                }
                Locals::Define(prev, x, _, _) => {
                    if cur == blvl.0 {
                        return x.to_span();
                    }
                    ls = prev.as_ref();
                }
            }
        }
    }

    /// 逐层剥 Π（参考版 `peel_pi` + 参数名收集）：返回 (余定义域, 新层级,
    /// **外→内**的参数名)。`quote` 在返回的层级上会把新引入的 rigid 编号成
    /// 0..k（内→外），故调用方拼名字表时按"外→内逐个 prepend"（头部 = 最内层）。
    pub(crate) fn peel_pi_collect(&self, cxt: &Cxt, vtyp: &Rc<VTy>) -> (Rc<Val>, Lvl, Vec<String>) {
        let mut t = self.force(vtyp);
        let mut lvl = cxt.lvl;
        let mut peeled: Vec<String> = Vec::new();
        while let Val::Pi(name, _, _, cod) = t.as_ref() {
            peeled.push(name.data.clone());
            t = self.closure_apply(cod, Val::vvar(lvl).into());
            lvl = lvl + 1;
            t = self.force(&t);
        }
        (t, lvl, peeled)
    }
}
