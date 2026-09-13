use crate::list::List;
use super::syntax::Pruning;

use super::parser::syntax::Icit;

use super::Tm;

const ATP: i32 = 3;  // atomp
const APPP: i32 = 2; // appp
const PIP: i32 = 1;  // pip
const LETP: i32 = 0; // letp

fn bracket(s: &str) -> String {
    format!("{{{}}}", s)
}

fn paren(s: &str) -> String {
    format!("({})", s)
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

    // 越界说明显示上下文里没有这个名字（错误文案对更浅上下文的项做
    // pretty 时可达），退化显示索引而不是 panic（L08/L09/L10 `go_ix`
    // 同款）。
    format!("@{}", ix)

}

/// `pretty_tm` 的增量核心：逐节点写入单个输出缓冲，任何字节只写一次。
/// 旧实现逐节点 `format!` 从子串拼新串——深度 d 处的字符串上下文 O(d)，
/// 嵌套链全链 O(n²) 字节复制（perf-debt P3）。输出与旧实现逐字节一致。
fn go(prec: i32, ns: List<String>, tm: &Tm, out: &mut String) {
    match tm {
        Tm::Var(ix) => out.push_str(&go_ix(ns, ix.0)),
        Tm::Decl(x) => out.push_str(&x.data),
        Tm::Obj(x, name) => {
            go(prec, ns, x, out);
            out.push('.');
            out.push_str(&name.data);
        }
        Tm::App(t, u, i) => {
            let need_paren = prec > APPP;
            if need_paren {
                out.push('{');
            }
            go(APPP, ns.clone(), t, out);
            out.push(' ');
            match i {
                Icit::Expl => go(ATP, ns, u, out),
                Icit::Impl => {
                    out.push('{');
                    go(ATP, ns, u, out);
                    out.push('}');
                }
            }
            if need_paren {
                out.push('}');
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
                    out.push('{');
                    out.push_str(&x);
                    out.push('}');
                }
            }
            out.push_str(" => ");
            go(LETP, new_ns, body, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::U(uni) => out.push_str(&format!("Type {uni}")),
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
                    Icit::Expl => out.push_str(&paren(&format!("{x}: {dom}"))),
                    Icit::Impl => out.push_str(&bracket(&format!("{x}: {dom}"))),
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
            out.push_str(";\n  ");
            go(LETP, new_ns, u, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::Meta(m) => out.push_str(&format!("?{}", m.0)),
        Tm::AppPruning(t, pr) => go_app_pruning(prec, ns.clone(), ns, t, pr, out),
        Tm::LiteralType => out.push_str("String"),
        Tm::LiteralIntro(span) => out.push_str(&span.data),
        Tm::Prim(_, _) => out.push_str("Prim Func"),
        Tm::Sum(span, tms, items, _) => {
            out.push_str(&span.data);
            if !tms.is_empty() {
                out.push('[');
                for (idx, tm) in tms.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    go(prec, ns.clone(), &tm.1, out);
                }
                out.push(']');
            }
        }
        Tm::SumCase { is_trait, typ, case_name, datas: params } => {
            // 头部：typ 的隐式参数串（小串，单独渲染）
            let head = match typ.as_ref() {
                Tm::Sum(name, params, _, _) => {
                    let impls: Vec<String> = params
                        .iter()
                        .filter(|x| x.3 == Icit::Impl)
                        .map(|x| pretty_tm(prec, ns.clone(), &x.1))
                        .collect();
                    if impls.is_empty() {
                        name.data.to_string()
                    } else {
                        format!("{}[{}]", name.data, impls.join(", "))
                    }
                }
                // typ 非 `Tm::Sum`（构造子的 `-> ret` 原样存储，可以是 App
                // 链）：沿链找头部 Sum 名字，找不到退化 `?` 而不是 panic
                // （L08/L09/L10 `sum_head_name` 同款降级）。
                _ => sum_head_name(typ.as_ref()),
            };
            out.push_str(&head);
            out.push_str("::");
            out.push_str(&case_name.data);
            if !params.is_empty() {
                out.push('(');
                for (idx, tm) in params.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    go(prec, ns.clone(), &tm.1, out);
                }
                out.push(')');
            }
        }
        Tm::Match(tm, _) => {
            out.push_str("(unsolved match ");
            go(prec, ns, tm, out);
            out.push(')');
        }
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

fn go_app_pruning(p: i32, top_ns: List<String>, ns: List<String>, t: &Tm, pr: &Pruning, out: &mut String) {
    fn go_pr_inner(
        p: i32,
        top_ns: &List<String>,
        mut ns: List<String>,
        t: &Tm,
        mut pr: Pruning,
        arg_index: u32,
        out: &mut String,
    ) {
        loop {
            match (ns.split(), pr.split()) {
                ((None, _), (None, _)) => {
                    go(p, top_ns.clone(), t, out);
                    return;
                }
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
                            Icit::Impl => bracket(&arg_str),
                        };
                        if need_paren {
                            out.push('(');
                        }
                        go_pr_inner(APPP, top_ns, rest_ns, t, rest_pr, arg_index + 1, out);
                        out.push(' ');
                        out.push_str(&arg_display);
                        if need_paren {
                            out.push(')');
                        }
                        return;
                    } else {
                        // Skip implicit argument
                        ns = rest_ns;
                        pr = rest_pr;
                        // continue loop
                    }
                }
                // A pruning longer than the display name list (e.g. a decl
                // type printed under a shallower context than the meta's
                // elaboration depth) degrades to positional placeholders
                // instead of panicking.
                ((None, _), (Some(prune), rest_pr)) => {
                    if let Some(i) = prune {
                        let need_paren = p > APPP;
                        let arg_str = format!("@{}", arg_index);
                        let arg_display = match i {
                            Icit::Expl => arg_str,
                            Icit::Impl => bracket(&arg_str),
                        };
                        if need_paren {
                            out.push('(');
                        }
                        go_pr_inner(APPP, top_ns, ns.clone(), t, rest_pr, arg_index + 1, out);
                        out.push(' ');
                        out.push_str(&arg_display);
                        if need_paren {
                            out.push(')');
                        }
                        return;
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

    go_pr_inner(p, &top_ns, ns, t, pr.clone(), 0, out)
}

pub fn pretty_tm(prec: i32, ns: List<String>, tm: &Tm) -> String {
    let mut out = String::with_capacity(64);
    go(prec, ns, tm, &mut out);
    out
}

/// `SumCase.typ` 可能不是展开的 `Tm::Sum`（构造子的 `-> ret` 原样存储，
/// 可以是 App 链）：沿 App 链找头部的 Sum 名字，找不到就显示 `?`
/// （L08/L09/L10 同款降级，不再 panic）。
fn sum_head_name(tm: &Tm) -> String {
    match tm {
        Tm::Sum(name, ..) => name.data.clone(),
        Tm::App(f, _, _) => sum_head_name(f),
        _ => "?".to_owned(),
    }
}
