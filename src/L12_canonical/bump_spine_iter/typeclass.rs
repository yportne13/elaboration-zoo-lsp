//! typeclass（孪生）：trait 状态 + 打包值 V → 参考 Val 的转换（供 Val 级求解器）。
//!
//! 2026-11-17 重建：L12 参考版求解器改为 Val 级（typeclass.rs），孪生不再维护
//! Typ 世界；断言侧把 V 深解码成参考 Val 后交同一 Synth（旧 L12 孪生的
//! v_to_ref_val 同款口径，解码对非构造子形态降级为永不匹配标记）。

use std::rc::Rc;
use rustc_hash::FxHashMap as HashMap;

use crate::list::List;
use crate::parser_lib::Span;
use smol_str::SmolStr;

use super::parser::syntax::{Icit, Raw};
use crate::L12_canonical::typeclass::{Assertion, Instance, Synth};
use crate::L12_canonical::{Val, Lvl, vspan};
use super::spine::Spine;
use super::syntax::{V, v_lvl_of, v_meta_of, v_spine_of, v_tag, v_u_of, v_xcell_of, XCell};

/// trait 定义 / 合成状态（参考版 Infer 三张表同构；每轮由 TraitDecl 重建）。
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    pub(super) solver: Synth,
    pub(super) definition: HashMap<
        String,
        (
            Vec<(Span<String>, Raw, Icit)>,
            Vec<bool>,
            Vec<(Span<String>, Vec<(Span<String>, Raw, Icit)>, Raw)>,
        ),
    >,
    pub(super) out_param: HashMap<String, Vec<bool>>,
}

fn span_of(name: &str) -> Span<String> {
    Span { data: name.to_owned(), start_offset: 0, end_offset: 0, path_id: 0 }
}

fn unmatchable() -> Val {
    Val::LiteralIntro(vspan(span_of("$unmatchable$")))
}

/// 打包值 V 深解码成参考 Val（trait 求解器匹配用；不可解码形态 → 永不匹配）。
pub(crate) fn v_to_val(spine: &Spine, defs: &[V], v: V) -> Val {
    match v_tag(v) {
        0 => Val::Rigid(Lvl(v_lvl_of(v)), List::new()),
        2 => {
            // 链：头裸变量 → Rigid；其余链头（Decl/Sum/...）→ 宽放占位。
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args);
            let base = match v_tag(hd) {
                5 => Val::Flex(super::MetaVar(v_meta_of(hd)), List::new()),
                0 => Val::Rigid(Lvl(v_lvl_of(hd)), List::new()),
                _ => Val::Flex(super::MetaVar(u32::MAX), List::new()),
            };
            // 带实参的链：降级为通配 Flex（val_match 的 Flex 臂匹配一切）
            if args.is_empty() { base } else { Val::Flex(super::MetaVar(u32::MAX), List::new()) }
        }
        3 => Val::U(v_u_of(v)),
        5 => Val::Flex(super::MetaVar(v_meta_of(v)), List::new()),
        6 => Val::LiteralType,
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Val::LiteralIntro(vspan(span_of(s))),
            XCell::Sum { name, params, cases } => Val::Sum(
                vspan(span_of(name)),
                Rc::new(
                    params
                        .iter()
                        .map(|p| {
                            (
                                vspan(span_of(p.name)),
                                Rc::new(v_to_val(spine, defs, p.val)),
                                Rc::new(v_to_val(spine, defs, p.ty)),
                                p.icit,
                            )
                        })
                        .collect(),
                ),
                Rc::new(cases.iter().map(|c| vspan(span_of(c))).collect()),
            ),
            XCell::SumCase { typ, case_name, datas } => Val::SumCase {
                typ: Rc::new(v_to_val(spine, defs, *typ)),
                case_name: vspan(span_of(case_name)),
                datas: Rc::new(
                    datas
                        .iter()
                        .map(|d| (vspan(span_of(d.name)), Rc::new(v_to_val(spine, defs, d.val)), d.icit))
                        .collect(),
                ),
            },
            _ => unmatchable(),
        },
        _ => unmatchable(),
    }
}

// 供 machine 直接使用的求解器类型/断言（避免重复 import 路径）。
pub(super) use crate::L12_canonical::typeclass::Assertion as _Assertion;
pub(super) use crate::L12_canonical::typeclass::Instance as _Instance;

/// 保留给 machine 的 trait 表别名（旧机器代码引用 Assertion/Instance）。
pub(crate) type TraitAssertion = Assertion;
pub(crate) type TraitInstance = Instance;
