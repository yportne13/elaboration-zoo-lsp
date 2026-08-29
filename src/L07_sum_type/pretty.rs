//! 项的 pretty printing。约定与 L07/L07a 保持一致：
//! 隐式参数用 `[..]`、构造子值打印成 `Enum::case(...)`、卡住的 match
//! 打印出完整的分支结构。相比 L07a 修复：`AppPruning` 不再 `todo!()`，
//! `SumCase.typ` 不是展开的 `Tm::Sum` 时也不再 panic（沿 App 链找头名）。

use crate::list::List;

use super::{parser::syntax::Icit, Tm};

const ATP: i32 = 3; // atom
const APPP: i32 = 2; // app
const PIP: i32 = 1; // pi
const LETP: i32 = 0; // let / lam

fn bracket(s: String) -> String {
    format!("[{s}]")
}

fn paren(f: String) -> String {
    format!("({f})")
}

fn fresh(ns: List<String>, suggested: &str) -> String {
    if suggested == "_" {
        return "_".to_string();
    }
    let mut candidate = suggested.to_string();
    while ns.iter().any(|x| *x == candidate) {
        candidate = format!("{candidate}'");
    }
    candidate
}

fn go_ix(ns: List<String>, ix: u32) -> String {
    let mut current_ix = ix;
    let mut current_ns = ns.iter();
    while let Some(name) = current_ns.next() {
        if current_ix == 0 {
            if name == "_" {
                return format!("@{ix}");
            }
            return name.to_string();
        }
        current_ix -= 1;
    }
    // 越界说明显示上下文里没有这个名字，退化显示索引而不是 panic
    format!("@{ix}")
}

/// `AppPruning` 只显示内核（它几乎总是 fresh_meta 的 `?m` 包装，
/// pruning 只表示"元变量取哪些可见参数"，对显示无益）。
fn go_app_pruning(prec: i32, ns: List<String>, t: &Tm) -> String {
    pretty_tm(prec, ns, t)
}pub fn pretty_tm(prec: i32, ns: List<String>, tm: &Tm) -> String {
    match tm {
        Tm::Var(ix) => go_ix(ns, ix.0),
        Tm::Decl(name) => name.to_string(),
        Tm::Obj(x, name) => format!("{}.{}", pretty_tm(prec, ns, x), name.data),
        Tm::App(t, u, i) => {
            let need_paren = prec > APPP;
            let f_t = pretty_tm(APPP, ns.clone(), t);
            let f_u = match i {
                Icit::Expl => pretty_tm(ATP, ns, u),
                Icit::Impl => bracket(pretty_tm(ATP, ns, u)),
            };
            if need_paren {
                format!("{{{f_t} {f_u}}}")
            } else {
                format!("{f_t} {f_u}")
            }
        }
        Tm::Lam(span, i, body) => {
            let need_paren = prec > LETP;
            let x = fresh(ns.clone(), &span.data);
            let new_ns = ns.prepend(x.clone());
            let binder = match i {
                Icit::Expl => x,
                Icit::Impl => bracket(x),
            };
            let ret = format!("{binder} => {}", pretty_tm(LETP, new_ns, body));
            if need_paren {
                paren(ret)
            } else {
                ret
            }
        }
        Tm::U => "U".to_owned(),
        Tm::Pi(name_span, i, a, b) => {
            let need_paren = prec > PIP;
            let is_anonymous = name_span.data == "_";
            if is_anonymous {
                let f_a = pretty_tm(APPP, ns.clone(), a);
                let f_b = pretty_tm(PIP, ns.prepend("_".to_owned()), b);
                let ret = format!("{f_a} → {f_b}");
                if need_paren {
                    paren(ret)
                } else {
                    ret
                }
            } else {
                let x = fresh(ns.clone(), &name_span.data);
                let new_ns = ns.prepend(x.clone());
                let binder = match i {
                    Icit::Expl => paren(format!("{x}: {}", pretty_tm(LETP, ns, a))),
                    Icit::Impl => bracket(format!("{x}: {}", pretty_tm(LETP, ns, a))),
                };
                let ret = format!("{binder} → {}", pretty_tm(PIP, new_ns, b));
                if need_paren {
                    paren(ret)
                } else {
                    ret
                }
            }
        }
        Tm::Let(name_span, a, t, u) => {
            let need_paren = prec > LETP;
            let x = fresh(ns.clone(), &name_span.data);
            let new_ns = ns.prepend(x.clone());
            let ret = format!(
                "let {x}: {} = {};\n{}",
                pretty_tm(LETP, ns.clone(), a),
                pretty_tm(LETP, ns, t),
                pretty_tm(LETP, new_ns, u),
            );
            if need_paren {
                paren(ret)
            } else {
                ret
            }
        }
        Tm::Meta(m) => format!("?{}", m.0),
        Tm::AppPruning(t, _) => go_app_pruning(prec, ns, t),
        Tm::LiteralType => "String".to_owned(),
        Tm::LiteralIntro(span) => span.data.clone(),
        Tm::Prim => "<prim>".to_owned(),
        Tm::Sum(span, params, _) => format!(
            "{}{}",
            span.data,
            params
                .iter()
                .map(|(_, v, _, i)| match i {
                    Icit::Expl => pretty_tm(ATP, ns.clone(), v),
                    Icit::Impl => bracket(pretty_tm(ATP, ns.clone(), v)),
                })
                .reduce(|acc, x| format!("{acc}, {x}"))
                .map(|x| format!("[{x}]"))
                .unwrap_or_default(),
        ),
        Tm::SumCase {
            typ,
            case_name,
            datas,
        } => format!(
            "{}::{}{}",
            sum_head_name(typ),
            case_name.data,
            datas
                .iter()
                .map(|(_, v, i)| match i {
                    Icit::Expl => pretty_tm(ATP, ns.clone(), v),
                    Icit::Impl => bracket(pretty_tm(ATP, ns.clone(), v)),
                })
                .reduce(|acc, x| format!("{acc} {x}"))
                .map(|x| format!("({x})"))
                .unwrap_or_default(),
        ),
        Tm::Match(scrut, cases) => {
            let inner = cases
                .iter()
                .map(|(pat, body)| {
                    format!(
                        "case {} => {}",
                        pretty_pattern(pat),
                        pretty_tm(LETP, prepend_pattern_ns(ns.clone(), pat), body)
                    )
                })
                .reduce(|a, b| format!("{a}; {b}"))
                .unwrap_or_default();
            let ret = format!("match {} {{ {inner} }}", pretty_tm(ATP, ns, scrut));
            if prec > LETP {
                paren(ret)
            } else {
                ret
            }
        }
    }
}

/// SumCase.typ 可能是 `Decl` / 应用链（构造子的 `-> ret` 原样存储），
/// 沿 App 链找头部的 Sum/Decl 名字；找不到就显示 `?`。
fn sum_head_name(tm: &Tm) -> String {
    match tm {
        Tm::Sum(name, _, _) => name.data.clone(),
        Tm::Decl(name) => name.to_string(),
        Tm::App(f, _, _) => sum_head_name(f),
        _ => "?".to_owned(),
    }
}

fn pretty_pattern(pat: &super::PatternDetail) -> String {
    match pat {
        super::PatternDetail::Any(_) => "_".to_owned(),
        super::PatternDetail::Bind(name) => name.data.clone(),
        super::PatternDetail::Con(name, subs) => {
            if subs.is_empty() {
                name.data.clone()
            } else {
                format!(
                    "{}({})",
                    name.data,
                    subs.iter()
                        .map(pretty_pattern)
                        .reduce(|a, b| format!("{a}, {b}"))
                        .unwrap_or_default()
                )
            }
        }
    }
}

/// 分支体的显示名字表：按 bind_count 前置哑名（Con 自身占一槽，名字未知用 `_`）。
fn prepend_pattern_ns(ns: List<String>, pat: &super::PatternDetail) -> List<String> {
    match pat {
        super::PatternDetail::Any(_) => ns.prepend("_".to_owned()),
        super::PatternDetail::Bind(name) => ns.prepend(name.data.clone()),
        super::PatternDetail::Con(_, subs) => {
            let ns = ns.prepend("_".to_owned());
            subs.iter().rev().fold(ns, |ns, sub| prepend_pattern_ns(ns, sub))
        }
    }
}
