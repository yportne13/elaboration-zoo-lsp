use crate::list::List;
use super::syntax::Pruning;

use super::parser::syntax::Icit;

use super::Tm;

const ATP: i32 = 3;  // atomp
const APPP: i32 = 2; // appp
const PIP: i32 = 1;  // pip
const LETP: i32 = 0; // letp

fn bracket(s: String) -> String {
    format!("{{{}}}", s)
}

fn paren(f: String) -> String {
    format!("({})", f)
}

fn fresh(ns: List<String>, suggested: &str) -> String {
    if suggested == "_" {
        return "_".to_string();
    }
    
    let mut candidate = suggested.to_string();
    while ns.iter().any(|x| *x == candidate) {
        candidate = format!("{}'", candidate);
    }
    candidate
}

fn go_ix(ns: List<String>, ix: u32) -> String {
    let mut current_ix = ix;
    for name in ns.iter() {
        if current_ix == 0 {
            if name == "_" {
                return format!("@{}", ix)
            } else {
                return name.to_string()
            }
        }
        current_ix -= 1;
    }
    // 名字表短于索引（如 hover 类调用方拿错名字表）：退化成固定文案而
    // 不是 panic——显示路径绝不能崩（L13 pretty 同款行为）。
    "Variable index out of bounds".to_owned()
}

/// `AppPruning` 是项层的洞形态（`fresh_meta` 产出）；常规 pretty 只吃
/// quote 出的 nf 项（quote 不产该形态），但显示路径必须兜底：掩码槽位
/// 与名字表按位置配对，保留槽打印 binder 名（`_` 槽退化 `@序号`），
/// 名字表不足时退化位置占位（L13 `go_pr_inner` 同款，不 panic）。
fn go_app_pruning(p: i32, top_ns: List<String>, ns: List<String>, t: &Tm, pr: &Pruning) -> String {
    fn go_pr_inner(
        p: i32,
        top_ns: &List<String>,
        mut ns: List<String>,
        t: &Tm,
        mut pr: Pruning,
        arg_index: u32,
    ) -> String {
        loop {
            match (ns.split(), pr.split()) {
                ((None, _), (None, _)) => return pretty_tm(p, top_ns.clone(), t),
                ((Some(n), rest_ns), (Some(prune), rest_pr)) => {
                    if let Some(i) = prune {
                        let need_paren = p > APPP;
                        let arg_str = if n == "_" {
                            format!("@{}", arg_index)
                        } else {
                            n.clone()
                        };
                        let arg_display = match i {
                            Icit::Expl => arg_str,
                            Icit::Impl => format!("[{arg_str}]"),
                        };
                        let inner = go_pr_inner(APPP, top_ns, rest_ns, t, rest_pr, arg_index + 1);
                        let result = format!("{} {}", inner, arg_display);
                        return if need_paren { paren(result) } else { result };
                    } else {
                        ns = rest_ns;
                        pr = rest_pr;
                    }
                }
                // 名字表短于掩码（AppPruning 的 meta 在更深的签名 binder
                // 里创建、显示时名字表更短）：退化 `@序号` 占位而不是 panic。
                ((None, _), (Some(prune), rest_pr)) => {
                    if let Some(i) = prune {
                        let need_paren = p > APPP;
                        let arg_str = format!("@{}", arg_index);
                        let arg_display = match i {
                            Icit::Expl => arg_str,
                            Icit::Impl => format!("[{arg_str}]"),
                        };
                        let inner = go_pr_inner(APPP, top_ns, ns.clone(), t, rest_pr, arg_index + 1);
                        let result = format!("{} {}", inner, arg_display);
                        return if need_paren { paren(result) } else { result };
                    } else {
                        pr = rest_pr;
                    }
                }
                ((Some(_), rest_ns), (None, _)) => {
                    ns = rest_ns;
                }
            }
        }
    }

    go_pr_inner(p, &top_ns, ns, t, pr.clone(), 0)
}

pub fn pretty_tm(prec: i32, ns: List<String>, tm: &Tm) -> String {
    match tm {
        Tm::Var(ix) => go_ix(ns, ix.0),
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

            let body_printer = format!("=> {}", pretty_tm(LETP, new_ns, &body));

            let ret = format!("{binder}{body_printer}");
            if need_paren {
                paren(ret)
            } else {
                ret
            }
        }
        Tm::U => "U".to_owned(),
        Tm::Pi(name_span, i, a, b) => {
            let need_paren = prec > PIP;
            let is_anonymous = name_span.data == "_" || matches!(i, Icit::Impl);
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
                let f_b = pretty_tm(PIP, new_ns, b);
                let ret = format!("{binder} → {f_b}");
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
                "let {x}: {} = {};\n\n{}",
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
        Tm::AppPruning(t, pr) => go_app_pruning(prec, ns.clone(), ns, t, pr),
        Tm::LiteralType => "String".to_owned(),
        Tm::LiteralIntro(span) => span.data.clone(),
        Tm::Decl(span) => span.data.clone(),
    }
}