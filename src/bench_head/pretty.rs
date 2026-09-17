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
}

/// `pretty_tm` 的增量核心：逐节点写入单个输出缓冲，任何字节只写一次。
/// 旧实现逐节点 `format!` 从子串拼新串——深度 d 处的字符串上下文 O(d)，
/// 嵌套链全链 O(n²) 字节复制（perf-debt 剩余机会 9，同 L11/L12 P3 模板）。
/// 输出与旧实现逐字节一致。
fn go(prec: i32, ns: List<String>, tm: &Tm, out: &mut String) {
    match tm {
        Tm::Var(ix) => out.push_str(&go_ix(ns, ix.0)),
        Tm::Decl(name) => out.push_str(name),
        Tm::Obj(x, name) => {
            go(prec, ns, x, out);
            out.push('.');
            out.push_str(&name.data);
        }
        Tm::App(t, u, i) => {
            let need_paren = prec > APPP;
            if need_paren {
                out.push('(');
            }
            go(APPP, ns.clone(), t, out);
            out.push(' ');
            match i {
                Icit::Expl => go(ATP, ns, u, out),
                Icit::Impl => {
                    out.push('[');
                    go(ATP, ns, u, out);
                    out.push(']');
                }
            }
            if need_paren {
                out.push(')');
            }
        }
        Tm::Lam(span, i, body) => {
            let need_paren = prec > LETP;
            let x = fresh(ns.clone(), &span.data);
            let new_ns = ns.prepend(x.clone());
            if need_paren {
                out.push('(');
            }
            match i {
                Icit::Expl => out.push_str(&x),
                Icit::Impl => {
                    out.push('[');
                    out.push_str(&x);
                    out.push(']');
                }
            }
            out.push_str(" => ");
            go(LETP, new_ns, body, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::U => out.push('U'),
        Tm::Pi(name_span, i, a, b) => {
            let need_paren = prec > PIP;
            let is_anonymous = name_span.data == "_";
            if need_paren {
                out.push('(');
            }
            if is_anonymous {
                go(APPP, ns.clone(), a, out);
                out.push_str(" → ");
                go(PIP, ns.prepend("_".to_owned()), b, out);
            } else {
                let x = fresh(ns.clone(), &name_span.data);
                let new_ns = ns.prepend(x.clone());
                // binder 里的域类型是小串，单独渲染（binder 需要整体加括号）
                let dom = pretty_tm(LETP, ns, a);
                match i {
                    Icit::Expl => out.push_str(&paren(format!("{x}: {dom}"))),
                    Icit::Impl => out.push_str(&bracket(format!("{x}: {dom}"))),
                }
                out.push_str(" → ");
                go(PIP, new_ns, b, out);
            }
            if need_paren {
                out.push(')');
            }
        }
        Tm::Let(name_span, a, t, u) => {
            let need_paren = prec > LETP;
            let x = fresh(ns.clone(), &name_span.data);
            let new_ns = ns.prepend(x.clone());
            if need_paren {
                out.push('(');
            }
            out.push_str("let ");
            out.push_str(&x);
            out.push_str(": ");
            go(LETP, ns.clone(), a, out);
            out.push_str(" = ");
            go(LETP, ns, t, out);
            out.push_str(";\n");
            go(LETP, new_ns, u, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::Meta(m) => out.push_str(&format!("?{}", m.0)),
        Tm::AppPruning(t, _) => out.push_str(&go_app_pruning(prec, ns, t)),
        Tm::LiteralType => out.push_str("String"),
        Tm::LiteralIntro(span) => out.push_str(&span.data),
        Tm::Prim(name) => out.push_str(name),
        Tm::Sum(span, params, _) => {
            out.push_str(&span.data);
            if !params.is_empty() {
                out.push('[');
                for (idx, (_, v, _, i)) in params.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    match i {
                        Icit::Expl => go(ATP, ns.clone(), v, out),
                        Icit::Impl => {
                            out.push('[');
                            go(ATP, ns.clone(), v, out);
                            out.push(']');
                        }
                    }
                }
                out.push(']');
            }
        }
        Tm::SumCase {
            typ,
            case_name,
            datas,
        } => {
            out.push_str(&sum_head_name(typ));
            out.push_str("::");
            out.push_str(&case_name.data);
            if !datas.is_empty() {
                out.push('(');
                for (idx, (_, v, i)) in datas.iter().enumerate() {
                    if idx > 0 {
                        out.push(' ');
                    }
                    match i {
                        Icit::Expl => go(ATP, ns.clone(), v, out),
                        Icit::Impl => {
                            out.push('[');
                            go(ATP, ns.clone(), v, out);
                            out.push(']');
                        }
                    }
                }
                out.push(')');
            }
        }
        Tm::Match(scrut, cases) => {
            let need_paren = prec > LETP;
            if need_paren {
                out.push('(');
            }
            out.push_str("match ");
            go(ATP, ns.clone(), scrut, out);
            out.push_str(" { ");
            for (idx, (pat, body)) in cases.iter().enumerate() {
                if idx > 0 {
                    out.push_str("; ");
                }
                out.push_str("case ");
                out.push_str(&pretty_pattern(pat));
                out.push_str(" => ");
                go(LETP, prepend_pattern_ns(ns.clone(), pat), body, out);
            }
            out.push_str(" }");
            if need_paren {
                out.push(')');
            }
        }
    }
}

pub fn pretty_tm(prec: i32, ns: List<String>, tm: &Tm) -> String {
    let mut out = String::with_capacity(64);
    go(prec, ns, tm, &mut out);
    out
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
