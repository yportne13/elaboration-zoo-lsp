//! observe：孪生（`Machine`）的观察面（LSP 引擎侧接线）——与参考版
//! `src/L06_string/observe.rs` 逐点同契约的 push / 排水 / 快照实现，独立
//! `impl Machine` 块承载（与 L13 `bump_spine_iter/observe.rs` 同拆分风格）。
//!
//! 契约见 [`super::super::surface`]：表里只放 owned `Span<()>` + `String`；
//! push 期把 bump 域的值引读成串（`quote → export → pretty_tm`，与 println
//! 输出同一条管线），bump 值出表即弃。
//!
//! **总闸**：[`Machine::observe`] **默认 false**（与 L13 相反，见移植文档
//! §1.1）。关闭时每个 push 点只多一次 `bool` 判定，`decl_reg` 也不渲染。

use bumpalo::Bump;
use smol_str::SmolStr;

use crate::parser_lib::Span;

use super::super::parser::syntax::Decl;
use super::super::pretty;
use super::super::surface::{inlay_label, split_issue_lines, HoverEntry, LspSurface};
use super::entry::export;
use super::machine::{no_metas, types_names_list, Cxt};
use super::prim::lit_of;
use super::syntax::{v_lvl, v_pi_of, v_tag};
use super::env::env_ext;
use super::Machine;
use super::syntax::V;
use super::spine::Spine;

impl Machine {
    /// 观察表清空（`clear_round` 已内联同一组清空；本方法服务"轮内清表"
    /// 的调用方——L13 的 prelude 装载收尾等价物）。
    pub(super) fn clear_observation_tables(&mut self) {
        self.hover_table.clear();
        self.completion_table.clear();
        self.inlay_hint_table.clear();
        self.println_spans.clear();
        self.check_issue_lines.clear();
        self.issue_drained = 0;
        self.failed_decls.clear();
        self.binder_spans.clear();
    }

    /// push 期渲染：`quote → export → pretty`（与 `run_decls` 的 println 输出
    /// 同管线，两版逐字节可比）。
    pub(super) fn render_val<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, v: V) -> String {
        let q = self.quote(bump, cxt.lvl, v);
        pretty::pretty_tm(0, types_names_list(cxt.types), &export(q))
    }

    /// 登记处类型渲染 + `final`（无未解 meta）判定（L13 `render_typ_pretty`
    /// 同义）。采集关闭时返回 `None`——`decl_reg` 的调用点据此零渲染。
    pub(super) fn render_typ_pretty<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        vtyp: V,
    ) -> Option<(std::rc::Rc<String>, bool)> {
        if !self.observe {
            return None;
        }
        let q = self.quote(bump, cxt.lvl, vtyp);
        let final_ = !no_metas(q, &self.metas);
        let rendered = pretty::pretty_tm(0, types_names_list(cxt.types), &export(q));
        Some((std::rc::Rc::new(rendered), final_))
    }

    /// 观察面 inlay：含未解 meta 的类型跳过，标签超 80 字符截断（L13
    /// `push_inlay_hint` 同口径）。
    pub(super) fn push_inlay_hint<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, offset: u32, v: V) {
        if !self.inlay_wanted(offset) {
            return;
        }
        let q = self.quote(bump, cxt.lvl, v);
        if no_metas(q, &self.metas) {
            return;
        }
        let rendered = pretty::pretty_tm(0, types_names_list(cxt.types), &export(q));
        self.inlay_hint_table.push((offset, inlay_label(&rendered)));
    }

    /// 逐层剥 Π + 收集参数名（参考版 `peel_pi_collect` 的孪生版）：返回
    /// (余定义域, 新层级, **外→内**参数名)。
    pub(super) fn peel_pi_collect<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        vtyp: V,
    ) -> (V, u32, Vec<SmolStr>) {
        let mut t = vtyp;
        let mut lvl = cxt.lvl;
        let mut peeled: Vec<SmolStr> = Vec::new();
        loop {
            let tf = self.force_v(bump, t);
            if v_tag(tf) != 4 {
                return (t, lvl, peeled);
            }
            let p = v_pi_of(tf);
            peeled.push(SmolStr::new(p.name));
            let body = p.body;
            let penv = p.env;
            t = {
                let env = env_ext(bump, penv, v_lvl(lvl));
                self.eval(bump, env, body)
            };
            lvl += 1;
        }
    }

    /// HDL 自检行排水（**只读**版，理由见参考版 `observe.rs` 同名方法）。
    pub(super) fn drain_check_issues(&mut self, decl_idx: usize) {
        if !self.observe {
            return;
        }
        let text = {
            let map = self.mutable_map.borrow();
            match map.get("CheckIssues") {
                Some(v) => lit_of(*v).unwrap_or("").to_owned(),
                None => String::new(),
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

    /// println 观察条目。
    pub(super) fn push_println_span(&mut self, span: Span<()>, rendered: &str) {
        if !self.observe {
            return;
        }
        self.println_spans.push((span, rendered.to_owned()));
    }

    /// 失败 decl 的名字集（记录面；消费面见移植文档 §1.5）。
    pub(super) fn note_failed_decl(&mut self, d: &Decl) {
        for n in super::super::surface::failed_decl_names(d) {
            if !self.failed_decls.contains(&n) {
                self.failed_decls.push(n);
            }
        }
    }

    /// 本轮 owned 快照。
    pub(super) fn surface(&self) -> LspSurface {
        LspSurface {
            hover: self.hover_table.clone(),
            completion: self
                .completion_table
                .iter()
                .map(|(s, n)| (*s, n.as_str().to_owned()))
                .collect(),
            inlay_hint: self.inlay_hint_table.clone(),
            println_spans: self.println_spans.clone(),
            check_issues: self.check_issue_lines.clone(),
            failed_decls: self.failed_decls.clone(),
        }
    }

    /// 与 L13 `hover_entry_at` 同规则（同 path 内含 offset 的最小 span）。
    pub(super) fn hover_entry_at(&self, path_id: u32, offset: usize) -> Option<&HoverEntry> {
        self.hover_table
            .iter()
            .filter(|x| x.0.path_id == path_id)
            .filter(|x| x.0.contains(offset))
            .min_by_key(|x| x.0.end_offset - x.0.start_offset)
    }
}
