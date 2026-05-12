use smol_str::SmolStr;

use crate::list::List;
use super::syntax::Pruning;

use super::parser::syntax::Icit;

use super::Tm;

const ATP: i32 = 3;
const APPP: i32 = 2;
const PIP: i32 = 1;
const LETP: i32 = 0;

fn bracket(s: String) -> String {
    format!("{{{}}}", s)
}

fn paren(f: String) -> String {
    format!("({})", f)
}

fn fresh(ns: List<SmolStr>, suggested: &str) -> String {
    if suggested == "_" {
        return "_".to_string();
    }

    let mut candidate = suggested.to_string();
    while ns.iter().any(|x| x == &candidate) {
        candidate = format!("{}'", candidate);
    }
    candidate
}

fn go_ix(ns: List<SmolStr>, ix: u32) -> String {
    let mut current_ix = ix;
    let current_ns = ns.iter();
    for name in current_ns {
        if current_ix == 0 {
            if name == "_" {
                return format!("@{}", ix)
            } else {
                return name.to_string()
            }
        }
        current_ix -= 1;
    }
    "Variable index out of bounds".to_owned()
}

fn go_app_pruning(p: i32, top_ns: List<SmolStr>, ns: List<SmolStr>, t: &Tm, pr: &Pruning) -> String {
    fn go_pr_inner(
        p: i32,
        top_ns: &List<SmolStr>,
        mut ns: List<SmolStr>,
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
                            n.clone().to_string()
                        };
                        let arg_display = match i {
                            Icit::Expl => arg_str,
                            Icit::Impl => bracket(arg_str),
                        };
                        let inner = go_pr_inner(APPP, top_ns, rest_ns, t, rest_pr, arg_index + 1);
                        let result = format!("{} {}", inner, arg_display);
                        return if need_paren { paren(result) } else { result };
                    } else {
                        ns = rest_ns;
                        pr = rest_pr;
                    }
                }
                _ => panic!("Mismatch between names and pruning list"),
            }
        }
    }

    go_pr_inner(p, &top_ns, ns, t, pr.clone(), 0)
}

pub fn pretty_tm(prec: i32, ns: List<SmolStr>, tm: &Tm) -> String {
    pretty_tm_indent(prec, 0, ns, tm)
}

fn pretty_tm_indent(prec: i32, indent: usize, ns: List<SmolStr>, tm: &Tm) -> String {
    match tm {
        Tm::Var(ix) => go_ix(ns, ix.0),
        Tm::Decl(x) => x.data.to_string(),
        Tm::Obj(x, name) => format!("{}.{}", pretty_tm_indent(prec, indent, ns, x), name.data),
        Tm::App(t, u, i) => {
            let need_paren = prec > APPP;
            let f_t = pretty_tm_indent(APPP, indent, ns.clone(), t);
            let f_u = match i {
                Icit::Expl => pretty_tm_indent(ATP, indent, ns, u),
                Icit::Impl => bracket(pretty_tm_indent(ATP, indent, ns, u)),
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
            let new_ns = ns.prepend(SmolStr::new(&x));

            let binder = match i {
                Icit::Expl => x,
                Icit::Impl => bracket(x),
            };

            let body_printer = format!(" => {}", pretty_tm_indent(LETP, indent, new_ns, body));

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
            let is_anonymous = name_span.data == "_";
            if is_anonymous {
                let f_a = pretty_tm_indent(APPP, indent, ns.clone(), a);
                let f_b = pretty_tm_indent(PIP, indent, ns.prepend(SmolStr::new("_")), b);
                let ret = format!("{f_a} → {f_b}");
                if need_paren {
                    paren(ret)
                } else {
                    ret
                }
            } else {
                let x = fresh(ns.clone(), &name_span.data);
                let new_ns = ns.prepend(SmolStr::new(&x));
                let binder = match i {
                    Icit::Expl => paren(format!("{x}: {}", pretty_tm_indent(LETP, indent, ns, a))),
                    Icit::Impl => bracket(format!("{x}: {}", pretty_tm_indent(LETP, indent, ns, a))),
                };
                let f_b = pretty_tm_indent(PIP, indent, new_ns, b);
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
            let new_ns = ns.prepend(SmolStr::new(&x));
            let ret = format!(
                "let {x}: {} = {};\n{}  {}",
                pretty_tm_indent(LETP, indent, ns.clone(), a),
                pretty_tm_indent(LETP, indent, ns, t),
                "  ".repeat(indent),
                pretty_tm_indent(LETP, indent + 1, new_ns, u),
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
        Tm::Prim(_, _) => "Prim Func".to_owned(),
        Tm::Sum(span, tms, items, _) => format!(
            "{}{}",
            span.data,
            tms.iter()
                .map(|tm| {
                    match &tm.3 {
                        Icit::Expl => pretty_tm_indent(prec, indent, ns.clone(), &tm.1),
                        Icit::Impl => bracket(pretty_tm_indent(prec, indent, ns.clone(), &tm.1)),
                    }
                })
                .reduce(|acc, x| acc + ", " + &x)
                .map(|x| format!("[{x}]"))
                .unwrap_or("".to_owned()),
        ),
        Tm::SumCase { is_trait, typ, case_name, datas: params } if matches!(
            typ.as_ref(),
            Tm::Sum(name, _, _, _) if name.data == "Nat",
        ) => if case_name.data == "zero" {"0".to_owned()} else {pretty_nat(prec, indent, ns, params.first().map(|x| x.1.as_ref()), 1)},
        Tm::SumCase { is_trait, typ, case_name, datas: params } => format!(
            "{}::{}{}",
            match typ.as_ref() {
                Tm::Sum(name, params, _, _) => params
                    .iter()
                    .filter(|x| x.3 == Icit::Impl)
                    .map(|x| &x.1)
                    .map(|x| pretty_tm_indent(prec, indent, ns.clone(), x).to_string())
                    .reduce(|a, b| a + ", " + &b)
                    .map(|x| format!("{}[{}]", name.data, x))
                    .unwrap_or(name.data.to_string()),
                _ => panic!("Sum case must be applied to a sum"),
            },
            case_name.data,
            params
                .iter()
                .map(|tm| pretty_tm_indent(prec, indent, ns.clone(), &tm.1))
                .reduce(|acc, x| acc + ", " + &x)
                .map(|x| format!("({x})"))
                .unwrap_or("".to_owned()),
        ),
        Tm::Call(name, args, body) => {
            if matches!(body.as_ref(), Tm::Match(..)) {
                let args_str = args.iter()
                    .map(|a| pretty_tm_indent(prec, indent, ns.clone(), a))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", name, args_str)
            } else {
                pretty_tm_indent(prec, indent, ns, body)
            }
        },
        Tm::Match(tm, cases) => {
            let need_paren = prec > LETP;
            let i = "  ".repeat(indent);
            let scrutinee = pretty_tm_indent(prec, indent, ns.clone(), tm);
            let arms: Vec<String> = cases.iter().map(|(pat, body)| {
                let body_ns = pat.bind_names(&ns);
                let body_str = pretty_tm_indent(prec, indent + 2, body_ns, body);
                if body_str.contains('(') || body_str.contains('{') || body_str.contains('\n') {
                    format!("{i}  {} => ...", pat)
                } else {
                    format!("{i}  {} => {}", pat, body_str)
                }
            }).collect();
            let ret = format!("{}match {} {{\n{}\n{}}}",
                i, scrutinee, arms.join("\n"), i);
            if need_paren { paren(ret) } else { ret }
        },
    }
}

fn pretty_nat(prec: i32, indent: usize, ns: List<SmolStr>, param: Option<&Tm>, sum: u128) -> String {
    match param {
        Some(Tm::SumCase { is_trait, typ, case_name, datas: params }) if matches!(
            typ.as_ref(),
            Tm::Sum(name, _, _, _) if name.data == "Nat",
        ) => if case_name.data == "zero" {
            format!("{sum}")
        } else {
            pretty_nat(prec, indent, ns, params.first().map(|x| x.1.as_ref()), sum + 1)
        },
        Some(tm) => format!("{} + {}", pretty_tm_indent(prec, indent, ns, tm), sum),
        None => format!("unknown + {}", sum),
    }
}
