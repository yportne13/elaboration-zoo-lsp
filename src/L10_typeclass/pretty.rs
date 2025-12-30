use crate::list::List;
use super::syntax::Pruning;

use super::parser::syntax::Icit;

use super::Tm;

type ShowS = Box<dyn FnOnce(&mut String)>;

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
    while ns.iter().find(|x| *x == &candidate).is_some() {
        candidate = format!("{}'", candidate);
    }
    candidate
}

fn go_ix(ns: List<String>, ix: u32) -> String {
    let mut current_ix = ix;
    let mut current_ns = ns.iter();
    while let Some(name) = current_ns.next() {
        if current_ix == 0 {
            if name == "_" {
                return format!("@{}", ix)
            } else {
                return name.to_string()
            }
        }
        current_ix -= 1;
    }
    panic!("Variable index out of bounds");
}

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
                            Icit::Impl => bracket(arg_str),
                        };
                        let inner = go_pr_inner(APPP, top_ns, rest_ns, t, rest_pr, arg_index + 1);
                        let result = format!("{} {}", inner, arg_display);
                        return if need_paren { paren(result) } else { result };
                    } else {
                        // Skip implicit argument
                        ns = rest_ns;
                        pr = rest_pr;
                        // continue loop
                    }
                }
                _ => panic!("Mismatch between names and pruning list"),
            }
        }
    }

    go_pr_inner(p, &top_ns, ns, t, pr.clone(), 0)
}

pub fn pretty_tm(prec: i32, ns: List<String>, tm: &Tm) -> String {
    match tm {
        Tm::Var(ix) => if ix.0 >= 1919810 {format!("recursive_{}", ix.0 - 1919810)} else {go_ix(ns, ix.0)},
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

            let body_printer = format!(" => {}", pretty_tm(LETP, new_ns, body));

            let ret = format!("{binder}{body_printer}");
            if need_paren {
                paren(ret)
            } else {
                ret
            }
        }
        Tm::U(uni) => format!("Type {uni}"),
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
        Tm::Prim => "Prim Func".to_owned(),
        Tm::Sum(span, tms, items, _) => format!(
            "{}{}",
            span.data,
            tms.iter()
                .map(|tm| pretty_tm(prec, ns.clone(), &tm.1))
                .reduce(|acc, x| acc + ", " + &x)
                .map(|x| format!("[{x}]"))
                .unwrap_or("".to_owned()),
        ),
        Tm::SumCase { is_trait, typ, case_name, datas: params } => format!(
            "{}::{}{}",
            match typ.as_ref() {
                Tm::Sum(name, _, _, _) => &name.data,
                _ => panic!("Sum case must be applied to a sum"),
            },
            case_name.data,
            params
                .iter()
                .map(|tm| pretty_tm(prec, ns.clone(), &tm.1))
                .reduce(|acc, x| acc + ", " + &x)
                .map(|x| format!("({x})"))
                .unwrap_or("".to_owned()),
        ),
        Tm::Match(tm, _) => format!(
            "(unsolved match {})",
            pretty_tm(prec, ns, tm),
        ),
        /*Tm::Match(tm, cases) => format!(
            "(match {} {{\n{}\n}})",
            pretty_tm(prec, ns.clone(), tm),
            cases
                .iter()
                .map(|(pat, tm)| format!("{:?} => {}", pat, pretty_tm(prec, ns.prepend("n".to_owned()), tm)))
                .reduce(|acc, x| acc + ",\n" + &x)
                .unwrap_or("".to_owned())
        ),*/
    }
}