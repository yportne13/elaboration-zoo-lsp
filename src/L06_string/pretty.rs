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
    let mut out = String::with_capacity(64);
    go(prec, ns, tm, &mut out);
    out
}

/// `pretty_tm` 的增量核心：逐节点写入单个输出缓冲，任何字节只写一次。
///
/// 旧实现逐节点 `format!` 从子串拼新串——深度 d 处的字符串上下文 O(d)，
/// 嵌套链全链 O(n²) 字节复制（L07 性能评审的同款修复）。输出与旧实现
/// 逐字节一致：括号/分隔符的插入点与 `bracket`/`paren` 的包裹关系不变。
fn go(prec: i32, ns: List<String>, tm: &Tm, out: &mut String) {
    match tm {
        Tm::Var(ix) => out.push_str(&go_ix(ns, ix.0)),
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
            out.push_str("=> ");
            go(LETP, new_ns, body, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::U => out.push('U'),
        Tm::Pi(name_span, i, a, b) => {
            let need_paren = prec > PIP;
            let is_anonymous = name_span.data == "_" || matches!(i, Icit::Impl);
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
                    Icit::Expl => {
                        out.push('(');
                        out.push_str(&x);
                        out.push_str(": ");
                        out.push_str(&dom);
                        out.push(')');
                    }
                    Icit::Impl => {
                        out.push('{');
                        out.push_str(&x);
                        out.push_str(": ");
                        out.push_str(&dom);
                        out.push('}');
                    }
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
            out.push_str(";\n\n");
            go(LETP, new_ns, u, out);
            if need_paren {
                out.push(')');
            }
        }
        Tm::Meta(m) => out.push_str(&format!("?{}", m.0)),
        Tm::AppPruning(t, pr) => out.push_str(&go_app_pruning(prec, ns.clone(), ns, t, pr)),
        Tm::LiteralType => out.push_str("String"),
        Tm::LiteralIntro(span) => out.push_str(&span.data),
        Tm::Decl(span) => out.push_str(&span.data),
    }
}