use smol_str::SmolStr;

use crate::list::List;
use super::syntax::Pruning;

use super::parser::syntax::Icit;

use super::Tm;

const ATP: i32 = 3;
const APPP: i32 = 2;
const PIP: i32 = 1;
const LETP: i32 = 0;

fn bracket(s: &str) -> String {
    format!("{{{}}}", s)
}

fn paren(s: &str) -> String {
    format!("({})", s)
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
    // 越界说明显示上下文里没有这个名字（错误文案对更浅上下文的项做
    // pretty 时可达），退化显示索引而不是 panic/整句文案（L08/L09/L10
    // `go_ix` 同款）。
    format!("@{}", ix)
}

/// `pretty_tm` 的增量核心：逐节点写入单个输出缓冲，任何字节只写一次。
/// 旧实现逐节点 `format!` 从子串拼新串——深度 d 处的字符串上下文 O(d)，
/// 嵌套链全链 O(n²) 字节复制（perf-debt P3）。输出与旧实现逐字节一致。
/// 需要整体子串做决策的臂（Sum 参数表 / Match 分支体等）仍走
/// [`pretty_tm_indent`] 取小串。
fn go(prec: i32, indent: usize, ns: List<SmolStr>, tm: &Tm, out: &mut String) {
    match tm {
        Tm::Var(ix) => out.push_str(&go_ix(ns, ix.0)),
        Tm::Decl(x) => out.push_str(&x.data),
        Tm::Obj(x, name) => {
            go(prec, indent, ns, x, out);
            out.push('.');
            out.push_str(&name.data);
        }
        Tm::App(t, u, i) => {
            let need_paren = prec > APPP;
            if need_paren {
                out.push('{');
            }
            go(APPP, indent, ns.clone(), t, out);
            out.push(' ');
            match i {
                Icit::Expl => go(ATP, indent, ns, u, out),
                Icit::Impl => {
                    out.push('{');
                    go(ATP, indent, ns, u, out);
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
            let new_ns = ns.prepend(SmolStr::new(&x));

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
            go(LETP, indent, new_ns, body, out);
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
                go(APPP, indent, ns.clone(), a, out);
                out.push_str(" → ");
                go(PIP, indent, ns.prepend(SmolStr::new("_")), b, out);
            } else {
                let x = fresh(ns.clone(), &name_span.data);
                let new_ns = ns.prepend(SmolStr::new(&x));
                // binder 里的域类型是小串，单独渲染（binder 需要整体加括号）
                let dom = pretty_tm_indent(LETP, indent, ns, a);
                match i {
                    Icit::Expl => out.push_str(&paren(&format!("{x}: {dom}"))),
                    Icit::Impl => out.push_str(&bracket(&format!("{x}: {dom}"))),
                }
                out.push_str(" → ");
                go(PIP, indent, new_ns, b, out);
            }
            if need_paren {
                out.push(')');
            }
        }
        Tm::Let(name_span, a, t, u) => {
            let need_paren = prec > LETP;
            let x = fresh(ns.clone(), &name_span.data);
            let new_ns = ns.prepend(SmolStr::new(&x));
            if need_paren {
                out.push('(');
            }
            out.push_str("let ");
            out.push_str(&x);
            out.push_str(": ");
            go(LETP, indent, ns.clone(), a, out);
            out.push_str(" = ");
            go(LETP, indent, ns, t, out);
            out.push_str(";\n");
            for _ in 0..indent {
                out.push_str("  ");
            }
            out.push_str("  ");
            go(LETP, indent + 1, new_ns, u, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::Meta(m) => out.push_str(&format!("?{}", m.0)),
        Tm::AppPruning(t, pr) => go_app_pruning(prec, indent, ns.clone(), ns, t, pr, out),
        Tm::LiteralType => out.push_str("String"),
        Tm::LiteralIntro(span) => out.push_str(&span.data),
        Tm::Prim(_, _) => out.push_str("Prim Func"),
        Tm::Sum(span, tms, items, _) => {
            // call 形态：隐式实参 `[..]`、显式实参 `(..)` 分组（小串，
            // 单独渲染后拼接）
            let impls: Vec<String> = tms.iter()
                .filter(|tm| tm.3 == Icit::Impl)
                .map(|tm| pretty_tm_indent(prec, indent, ns.clone(), &tm.1))
                .collect();
            let expls: Vec<String> = tms.iter()
                .filter(|tm| tm.3 == Icit::Expl)
                .map(|tm| pretty_tm_indent(prec, indent, ns.clone(), &tm.1))
                .collect();
            out.push_str(&span.data);
            if !impls.is_empty() {
                out.push('[');
                out.push_str(&impls.join(", "));
                out.push(']');
            }
            if !impls.is_empty() && !expls.is_empty() {
                out.push_str("\u{200b}");
            }
            if !expls.is_empty() {
                out.push('(');
                out.push_str(&expls.join(", "));
                out.push(')');
            }
        }
        Tm::SumCase { is_trait, typ, case_name, datas: params } if matches!(
            typ.as_ref(),
            Tm::Sum(name, _, _, _) if name.data == "Nat",
        ) => if case_name.data == "zero" {
            out.push('0')
        } else {
            out.push_str(&pretty_nat(prec, indent, ns, params.first().map(|x| x.1.as_ref()), 1))
        },
        Tm::SumCase { is_trait, typ, case_name, datas: params } => {
            let head = match typ.as_ref() {
                Tm::Sum(name, params, _, _) => {
                    let impls: Vec<String> = params
                        .iter()
                        .filter(|x| x.3 == Icit::Impl)
                        .map(|x| pretty_tm_indent(prec, indent, ns.clone(), &x.1))
                        .collect();
                    if impls.is_empty() {
                        name.data.to_string()
                    } else {
                        format!("{}[{}]", name.data, impls.join(", "))
                    }
                }
                // typ 非 `Tm::Sum`（构造子的 `-> ret` 原样存储，可以是 App
                // 链）：沿链找头部 Sum 名字，找不到退化 `?` 而不是 panic
                // （L08/L09/L10/L11 `sum_head_name` 同款降级）。
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
                    go(prec, indent, ns.clone(), &tm.1, out);
                }
                out.push(')');
            }
        }
        Tm::Call(name, args, _, body) => {
            if matches!(body.as_ref(), Tm::Match(..)) {
                let args_str = args.iter()
                    .map(|a| pretty_tm_indent(prec, indent, ns.clone(), a))
                    .collect::<Vec<_>>()
                    .join(", ");
                out.push_str(&name);
                out.push('(');
                out.push_str(&args_str);
                out.push(')');
            } else {
                go(prec, indent, ns, body, out);
            }
        }
        Tm::Match(tm, cases) => {
            let need_paren = prec > LETP;
            let i = "  ".repeat(indent);
            if need_paren {
                out.push('(');
            }
            out.push_str(&i);
            out.push_str("match ");
            go(prec, indent, ns.clone(), tm, out);
            out.push_str(" {\n");
            for (idx, (pat, body)) in cases.iter().enumerate() {
                if idx > 0 {
                    out.push('\n');
                }
                let body_ns = pat.bind_names(&ns);
                // 分支体需整体判断括号/换行形态（"..." 截断），走小串渲染
                let body_str = pretty_tm_indent(prec, indent + 2, body_ns, body);
                if body_str.contains('(') || body_str.contains('{') || body_str.contains('\n') {
                    out.push_str(&format!("{i}  {} => ...", pat));
                } else {
                    out.push_str(&format!("{i}  {} => {}", pat, body_str));
                }
            }
            out.push('\n');
            out.push_str(&i);
            out.push('}');
            if need_paren {
                out.push(')');
            }
        }
    }
}

fn go_app_pruning(p: i32, indent: usize, top_ns: List<SmolStr>, ns: List<SmolStr>, t: &Tm, pr: &Pruning, out: &mut String) {
    fn go_pr_inner(
        p: i32,
        indent: usize,
        top_ns: &List<SmolStr>,
        mut ns: List<SmolStr>,
        t: &Tm,
        mut pr: Pruning,
        arg_index: u32,
        out: &mut String,
    ) {
        loop {
            match (ns.split(), pr.split()) {
                ((None, _), (None, _)) => {
                    go(p, indent, top_ns.clone(), t, out);
                    return;
                }
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
                            Icit::Impl => bracket(&arg_str),
                        };
                        if need_paren {
                            out.push('(');
                        }
                        go_pr_inner(APPP, indent, top_ns, rest_ns, t, rest_pr, arg_index + 1, out);
                        out.push(' ');
                        out.push_str(&arg_display);
                        if need_paren {
                            out.push(')');
                        }
                        return;
                    } else {
                        ns = rest_ns;
                        pr = rest_pr;
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
                        go_pr_inner(APPP, indent, top_ns, ns.clone(), t, rest_pr, arg_index + 1, out);
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

    go_pr_inner(p, indent, &top_ns, ns, t, pr.clone(), 0, out)
}

pub fn pretty_tm(prec: i32, ns: List<SmolStr>, tm: &Tm) -> String {
    pretty_tm_indent(prec, 0, ns, tm)
}

fn pretty_tm_indent(prec: i32, indent: usize, ns: List<SmolStr>, tm: &Tm) -> String {
    let mut out = String::with_capacity(64);
    go(prec, indent, ns, tm, &mut out);
    out
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

/// `SumCase.typ` 可能不是展开的 `Tm::Sum`（构造子的 `-> ret` 原样存储，
/// 可以是 App 链）：沿 App 链找头部的 Sum 名字，找不到就显示 `?`
/// （L08/L09/L10/L11 同款降级，不再 panic）。
fn sum_head_name(tm: &Tm) -> String {
    match tm {
        // L12 的 Sum 名字是 SmolStr：转 String 与函数签名/邻层同型。
        Tm::Sum(name, ..) => name.data.to_string(),
        Tm::App(f, _, _) => sum_head_name(f),
        _ => "?".to_owned(),
    }
}
