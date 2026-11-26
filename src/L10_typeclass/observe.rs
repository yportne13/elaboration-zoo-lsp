//! observe：L10 参考版的观察面（L09 observe.rs 的平移，逐项继承）。
//!
//! 契约见 super::surface：表里只放 owned Span<()> + String；push 期用站点
//! 上下文把值引读成串（quote → pretty_tm），消费端不再需要 live Val。
//!
//! 与 L06 的差异：
//! - 引读要传 decl 表（quote 签名 quote(&Decls, Lvl, Val)）；
//! - Value 是按值 Val（不是 Rc<Val>），故渲染/校验接口收 Val；
//! - 多一条构造子 hover（限定键 E.c，按 key 记忆化渲染串）；
//! - 登记面用 Infer 侧的旁表（decl_spans / decl_pretty）承载 def/enum 的
//!   span 与登记期渲染串，不动 cxt::DeclEntry 的所有构造点。
//!
//! 总闸 lsp_collect 默认 false（与 L13 相反：L07 的 run/bench 口径不带渲染）。

use std::rc::Rc;

use smol_str::SmolStr;

use crate::parser_lib::{Span, ToSpan};

/// 从名字造一个零 span（显示用途：pretty 只需要 `data`）。
fn span_from_name(name: &str) -> Span<SmolStr> {
    let mut s: Span<SmolStr> = crate::L10_typeclass::empty_span(SmolStr::new(""));
    s.data = SmolStr::new(name);
    s
}

use super::parser::syntax::Decl;
use super::syntax::Locals;
use super::surface::{inlay_label, split_issue_lines, HoverEntry, LspSurface};
use super::*;

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

    /// push 期渲染：站点上下文引读 + pretty（与 run 的 println 同管线）。
    pub(crate) fn render_val(&self, cxt: &Cxt, v: Val) -> String {
        // 方案 3（形状认回 decl）：类型里的卡住 match 若能按形状认回某个 def，
        // 就打回 `g n` 而不是 `match n { … }`——无类型注解的 def 也因此保真。
        if let Some(s) = self.render_by_shape(cxt, v.clone()) {
            return s;
        }
        let q = self.quote(cxt.decl(), cxt.lvl, v);
        pretty_tm(0, cxt.names(), &q)
    }

    /// 形状认回：逐层剥离 Π，若余定义域是能认回 def 的 `Val::Match`，就合成
    /// `head args` 形态的项；否则返回 None（调用方回落到普通引读）。
    fn render_by_shape(&self, cxt: &Cxt, vtyp: Val) -> Option<String> {
        if self.decl_shapes.borrow().is_empty() {
            return None;
        }
        let decl = cxt.decl();
        // 剥 Π：收集 binder 名与域（显示用）
        let mut t = self.force(decl, vtyp);
        let mut l = cxt.lvl;
        let mut binders: Vec<(String, Val)> = Vec::new();
        loop {
            match t {
                Val::Pi(name, _, dom, cod) => {
                    binders.push((name.data.to_string(), (*dom).clone()));
                    let u = Val::vvar(l);
                    t = self.force(decl, self.closure_apply(decl, &cod, u));
                    l = l + 1;
                }
                ref m @ Val::Match(..) => {
                    let head = super::shape::match_to_decl(self, m)?;
                    let Val::Match(scrut, _, _, pending) = m else { return None };
                    // 尾部：`head scrut args…`
                    let mut tail = Tm::App(
                        Box::new(Tm::Decl(SmolStr::new(&head)),
                        ),
                        Box::new(self.quote(decl, l, (**scrut).clone())),
                        super::parser::syntax::Icit::Expl,
                    );
                    for (u, i) in pending.iter() {
                        tail = Tm::App(
                            Box::new(tail),
                            Box::new(self.quote(decl, l, u.clone())),
                            *i,
                        );
                    }
                    // 重新套上 Π（域用 normal quote）
                    let mut names = cxt.names();
                    let mut tm = tail;
                    for (bname, dom) in binders.iter().rev() {
                        tm = Tm::Pi(
                            span_from_name(bname),
                            super::parser::syntax::Icit::Expl,
                            Rc::new(self.quote(decl, l, dom.clone())),
                            Rc::new(tm),
                        );
                        names = names.prepend(SmolStr::new(&*bname));
                    }
                    let _ = names;
                    return Some(pretty_tm(0, cxt.names(), &tm));
                }
                _ => return None,
            }
        }
    }

    /// 登记处类型渲染 + final 判定（引出项无未解 meta 时，串与使用处实时渲染
    /// 一致，可直接复用）。
    pub(crate) fn render_typ_pretty(&self, cxt: &Cxt, v: Val) -> (String, bool) {
        // 方案 3：先试形状认回（无类型注解的 def 也走这里）。
        if let Some(s) = self.render_by_shape(cxt, v.clone()) {
            return (s, true);
        }
        let q = self.quote(cxt.decl(), cxt.lvl, v);
        let fin = !self.tm_has_unsolved_meta(&q);
        (pretty_tm(0, cxt.names(), &q), fin)
    }

    /// 项里是否有未解 meta（迭代走查、零分配）。
    pub(crate) fn tm_has_unsolved_meta(&self, t: &Tm) -> bool {
        let mut stack: Vec<&Tm> = vec![t];
        while let Some(x) = stack.pop() {
            match x {
                Tm::Var(_)
                | Tm::Decl(_)
                | Tm::U(_)
                | Tm::LiteralType
                | Tm::LiteralIntro(_)
                | Tm::Prim(_) => {}
                Tm::Obj(x, _) | Tm::AppPruning(x, _) => stack.push(x),
                Tm::Lam(_, _, b) => stack.push(b),
                Tm::App(f, a, _) => {
                    stack.push(f);
                    stack.push(a);
                }
                Tm::Pi(_, _, a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                Tm::Let(_, a, t2, u) => {
                    stack.push(a);
                    stack.push(t2);
                    stack.push(u);
                }
                Tm::Meta(m) => {
                    if matches!(self.lookup_meta(*m), MetaEntry::Unsolved(_)) {
                        return true;
                    }
                }
                Tm::Sum(_, params, _) => {
                    for (_, tm, ty, _) in params {
                        stack.push(tm);
                        stack.push(ty);
                    }
                }
                Tm::SumCase { typ, datas, .. } => {
                    stack.push(typ);
                    for (_, tm, _) in datas {
                        stack.push(tm);
                    }
                }
                Tm::Match(scrut, arms) => {
                    stack.push(scrut);
                    for (_, body) in arms {
                        stack.push(body);
                    }
                }
            }
        }
        false
    }

    // ── 观察面 push 方法 ──────────────────────────────────────────────────

    /// 观察面 hover：(使用处 span, 定义处 span, 渲染串)。
    pub(crate) fn push_hover(&mut self, cxt: &Cxt, t_span: Span<()>, def_span: Span<()>, v: Val) {
        if !self.hover_wanted(t_span) {
            return;
        }
        let rendered = self.render_val(cxt, v);
        self.hover_table.push((t_span, def_span, rendered));
    }

    /// 已有渲染串的 hover（def 定义处：渲染一次喂两处消费）。
    pub(crate) fn push_hover_rendered(&mut self, t_span: Span<()>, def_span: Span<()>, rendered: &str) {
        if !self.hover_wanted(t_span) {
            return;
        }
        self.hover_table.push((t_span, def_span, rendered.to_owned()));
    }

    /// 全局名使用处 hover：登记期串 final 时直取缓存，否则实时渲染。
    pub(crate) fn push_hover_decl(&mut self, cxt: &Cxt, t_span: Span<()>, key: &str, v: Val) {
        if !self.hover_wanted(t_span) {
            return;
        }
        let entry_span = self.decl_spans.get(key).copied().unwrap_or_else(|| empty_span(()));
        if let Some((s, true)) = self.decl_pretty.get(key) {
            self.hover_table.push((t_span, entry_span, (**s).clone()));
            return;
        }
        let rendered = self.render_val(cxt, v);
        self.hover_table.push((t_span, entry_span, rendered));
    }

    /// 构造子使用处 hover（SumCase / Obj 限定键）：闭合值的渲染与站点上下文
    /// 无关，按限定键记忆化。
    pub(crate) fn push_ctor_hover(&mut self, cxt: &Cxt, t_span: Span<()>, key: &str, v: Val) {
        if !self.hover_wanted(t_span) {
            return;
        }
        let def_span = self.decl_spans.get(key).copied().unwrap_or_else(|| empty_span(()));
        if let Some(s) = self.ctor_pretty.get(key) {
            self.hover_table.push((t_span, def_span, (**s).clone()));
            return;
        }
        let rendered = self.render_val(cxt, v);
        self.hover_table.push((t_span, def_span, rendered.clone()));
        self.ctor_pretty.insert(SmolStr::new(key), Rc::new(rendered));
    }

    /// inlay：含未解 meta 的类型跳过，标签超 80 字符截断。
    pub(crate) fn push_inlay_hint(&mut self, cxt: &Cxt, offset: u32, v: Val) {
        if !self.inlay_wanted(offset) {
            return;
        }
        let q = self.quote(cxt.decl(), cxt.lvl, v);
        if self.tm_has_unsolved_meta(&q) {
            return;
        }
        let label = inlay_label(&pretty_tm(0, cxt.names(), &q));
        self.inlay_hint_table.push((offset, label));
    }

    /// 已渲染的 inlay（def 返回类型：peel/quote/names 由调用方拼好）。
    pub(crate) fn push_inlay_label(&mut self, offset: u32, label: String) {
        if !self.inlay_wanted(offset) {
            return;
        }
        self.inlay_hint_table.push((offset, label));
    }

    /// println 观察条目。
    pub(crate) fn push_println_span(&mut self, span: Span<()>, rendered: &str) {
        if !self.lsp_collect {
            return;
        }
        self.println_spans.push((span, rendered.to_owned()));
    }

    /// 自检行排水（只读：L07 把 CheckIssues 当用户可见值打印，不能清空）。
    pub(crate) fn drain_check_issues(&mut self, decl_idx: usize) {
        if !self.lsp_collect {
            return;
        }
        let text = {
            let map = self.mutable_map.borrow();
            match map.get("CheckIssues") {
                Some(Val::LiteralIntro(s)) => s.data.clone(),
                _ => String::new(),
            }
        };
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

    /// 失败 decl 的名字集记入通道。
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

    /// 同 path 内包含 offset 的最窄条目。
    pub(crate) fn hover_entry_at(&self, path_id: u32, offset: usize) -> Option<&HoverEntry> {
        self.hover_table
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }

    /// 局部 binder 的定义处 span：Locals 链按层回走（只在采集开启时调用）。
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

    /// 逐层剥 Π（返回余定义域、新层级、外→内参数名）。
    pub(crate) fn peel_pi_collect(&self, cxt: &Cxt, vtyp: Val) -> (Val, Lvl, Vec<String>) {
        let mut t = self.force(cxt.decl(), vtyp);
        let mut lvl = cxt.lvl;
        let mut peeled: Vec<String> = Vec::new();
        while let Val::Pi(name, _, _, cod) = t {
            peeled.push(name.data.to_string());
            let u = Val::vvar(lvl);
            t = self.force(cxt.decl(), self.closure_apply(cxt.decl(), &cod, u));
            lvl = lvl + 1;
        }
        (t, lvl, peeled)
    }
}
