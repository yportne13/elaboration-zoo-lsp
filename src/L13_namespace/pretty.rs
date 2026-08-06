use smol_str::SmolStr;

use std::sync::Arc;

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

/// Renders `name` applied to a display-order argument list in call form:
/// implicit arguments (`Icit::Impl`) are grouped in square brackets and
/// explicit arguments in parens — `f[a, b](x, y)` — matching the parser's
/// `f[x](y)` application syntax (same convention as `Sum`/`SumCase`, which
/// also quote their args at the incoming `prec`).  A zero-width space keeps
/// the `](` boundary from forming a markdown link.
fn go_call(prec: i32, indent: usize, ns: &List<SmolStr>, name: &str, args: &List<(Arc<Tm>, Icit)>) -> String {
    let impls: Vec<String> = args.iter()
        .filter(|(_, i)| *i == Icit::Impl)
        .map(|(a, _)| pretty_tm_indent(prec, indent, ns.clone(), a))
        .collect();
    let expls: Vec<String> = args.iter()
        .filter(|(_, i)| *i == Icit::Expl)
        .map(|(a, _)| pretty_tm_indent(prec, indent, ns.clone(), a))
        .collect();
    let impl_str = if impls.is_empty() {
        String::new()
    } else {
        format!("[{}]", impls.join(", "))
    };
    let expl_str = if expls.is_empty() {
        String::new()
    } else {
        format!("({})", expls.join(", "))
    };
    let zwsp = if !impls.is_empty() && !expls.is_empty() { "\u{200b}" } else { "" };
    format!("{name}{impl_str}{zwsp}{expl_str}")
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
                _ => panic!("Mismatch between names and pruning list"),
            }
        }
    }

    go_pr_inner(p, &top_ns, ns, t, pr.clone(), 0)
}

/// Returns true when `tm` references any of the `n` innermost context
/// binders.  Used by arrow-chain folding: a subsequent Pi domain may only be
/// merged into the current parameter group when it does not depend on any
/// binder already in the group — otherwise the merged form would silently
/// drop a dependency (e.g. `(x: A) → (y: B x) → C` must stay unfolded
/// because `B x` references `x`).  Binders introduced *inside* `tm`
/// (Pi/Lam/Let) shift variable indices and are counted by the `depth`
/// argument.
fn mentions_outer_n(tm: &Tm, n: u32) -> bool {
    fn go(t: &Tm, depth: u32, n: u32) -> bool {
        if depth >= n {
            return false;
        }
        match t {
            Tm::Var(ix) => ix.0 < n - depth,
            Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => false,
            Tm::Obj(x, _) => go(x, depth, n),
            Tm::Lam(_, _, body) => go(body, depth + 1, n),
            Tm::App(f, u, _) => go(f, depth, n) || go(u, depth, n),
            // `AppPruning` consumes its context entries without binding
            // anything for its inner term (which is printed under the full
            // scope again), so it is transparent for the check.
            Tm::AppPruning(t, _) => go(t, depth, n),
            Tm::Pi(_, _, a, b) => go(a, depth, n) || go(b, depth + 1, n),
            Tm::Let(_, a, t2, u) => go(a, depth, n) || go(t2, depth, n) || go(u, depth + 1, n),
            Tm::Sum(_, tms, _, _) => tms.iter().any(|tm| go(&tm.1, depth, n)),
            Tm::SumCase { typ, datas, .. } => {
                go(typ, depth, n) || datas.iter().any(|d| go(&d.1, depth, n))
            }
            Tm::Call(_, args, body) => {
                args.iter().any(|(a, _)| go(a, depth, n)) || go(body, depth, n)
            }
            Tm::OpCall { args, body, .. } => {
                args.iter().any(|(a, _)| go(a, depth, n)) || go(body, depth, n)
            }
            Tm::Match(t, cases) => {
                go(t, depth, n) || cases.iter().any(|(_, b)| go(b, depth, n))
            }
        }
    }
    go(tm, 0, n)
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
            // Operator-symbol recovery: applications whose head is an
            // operator declaration (restored from an inlined helper call by
            // `quote`) render in infix (`x + y`) or prefix (`!x`) form.
            // The head name determines the form, so user-defined operator
            // symbols work automatically; ordinary applications fall through
            // to the `{f_t} {f_u}` form below.
            if *i == Icit::Expl {
                if let Tm::App(t2, arg1, Icit::Expl) = t.as_ref() {
                    if let Tm::Decl(name) = t2.as_ref() {
                        if name.data.chars().next().map(super::is_operator_char).unwrap_or(false) {
                            let ret = format!(
                                "{} {} {}",
                                pretty_tm_indent(ATP, indent, ns.clone(), arg1),
                                name.data,
                                pretty_tm_indent(ATP, indent, ns, u),
                            );
                            return if prec > APPP { bracket(ret) } else { ret };
                        }
                    }
                } else if let Tm::Decl(name) = t.as_ref() {
                    if name.data.chars().next().map(super::is_operator_char).unwrap_or(false) {
                        let ret = format!("{}{}", name.data, pretty_tm_indent(ATP, indent, ns, u));
                        return if prec > APPP { bracket(ret) } else { ret };
                    }
                }
            }
            let need_paren = prec > APPP;
            let f_t = pretty_tm_indent(APPP, indent, ns.clone(), t);
            let f_u = match i {
                Icit::Expl => pretty_tm_indent(ATP, indent, ns, u),
                // Implicit application arguments use square brackets to
                // match the parser's `f[x]` syntax (`{...}` stays reserved
                // for precedence grouping at ATP level).
                Icit::Impl => format!("[{}]", pretty_tm_indent(ATP, indent, ns, u)),
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
                // Implicit lambda binders use the parser's square-bracket
                // syntax `[x] => ...` (curly braces stay reserved for
                // precedence grouping at ATP level).
                Icit::Impl => format!("[{x}]"),
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
                // Arrow-chain folding: consecutive Pi binders whose domain
                // does not reference any binder already collected are merged
                // into one parameter group — `(x: A, y: B) → C` instead of
                // the nested `(x: A) → (y: B) → C` chain.  Merging is only
                // safe when the later domain is independent of the earlier
                // binders (a dependent type must keep its own `→` so the
                // binder stays in scope).  Implicit binders group in square
                // brackets `[T: Type]` (the parser's implicit syntax, same
                // as `Sum`/`Call` args); explicit ones in parens.  Groups of
                // different icities concatenate like the source form
                // `def f[T](x: A)`, with a zero-width space at the `](`
                // boundary to keep markdown links from forming.
                let mut binders: Vec<(SmolStr, Icit, Arc<Tm>, List<SmolStr>)> = Vec::new();
                let mut ns_cur = ns.clone();
                let mut cur_name = name_span.clone();
                let mut cur_i = *i;
                let mut cur_a = a.clone();
                let mut cur_b = b.clone();
                loop {
                    let x = fresh(ns_cur.clone(), &cur_name.data);
                    binders.push((SmolStr::new(&x), cur_i, cur_a.clone(), ns_cur.clone()));
                    ns_cur = ns_cur.prepend(SmolStr::new(&x));
                    match cur_b.as_ref() {
                        Tm::Pi(n2, i2, a2, b2)
                            if n2.data != "_" && !mentions_outer_n(a2, binders.len() as u32) =>
                        {
                            cur_name = n2.clone();
                            cur_i = *i2;
                            cur_a = a2.clone();
                            cur_b = b2.clone();
                        }
                        _ => break,
                    }
                }
                let mut groups: Vec<(Icit, Vec<String>)> = Vec::new();
                for (x, icit, a2, dom_ns) in &binders {
                    let dom = pretty_tm_indent(LETP, indent, dom_ns.clone(), a2);
                    let item = format!("{x}: {dom}");
                    match groups.last_mut() {
                        Some((i0, seg)) if i0 == icit => seg.push(item),
                        _ => groups.push((*icit, vec![item])),
                    }
                }
                let mut group_str = String::new();
                for (idx, (icit, seg)) in groups.iter().enumerate() {
                    if idx > 0 && group_str.ends_with(']') {
                        group_str.push('\u{200b}');
                    }
                    let inner = seg.join(", ");
                    match icit {
                        Icit::Expl => group_str.push_str(&format!("({inner})")),
                        Icit::Impl => group_str.push_str(&format!("[{inner}]")),
                    }
                }
                let f_b = pretty_tm_indent(PIP, indent, ns_cur, &cur_b);
                let ret = format!("{group_str} → {f_b}");
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
        Tm::Sum(span, tms, items, _) => {
            let impls: Vec<_> = tms.iter()
                .filter(|tm| tm.3 == Icit::Impl)
                .map(|tm| pretty_tm_indent(prec, indent, ns.clone(), &tm.1))
                .collect();
            let expls: Vec<_> = tms.iter()
                .filter(|tm| tm.3 == Icit::Expl)
                .map(|tm| pretty_tm_indent(prec, indent, ns.clone(), &tm.1))
                .collect();
            let impl_str = if impls.is_empty() {
                String::new()
            } else {
                format!("[{}]", impls.join(", "))
            };
            let expl_str = if expls.is_empty() {
                String::new()
            } else {
                format!("({})", expls.join(", "))
            };
            let zwsp = if !impls.is_empty() && !expls.is_empty() { "\u{200b}" } else { "" };
            format!("{}{}{}{}", span.data, impl_str, zwsp, expl_str)
        },
        Tm::SumCase { is_trait, typ, index, datas: params } if matches!(
            typ.as_ref(),
            Tm::Sum(name, _, _, _) if name.data == "Nat",
        ) => if *index == 0 {"0".to_owned()} else {pretty_nat(prec, indent, ns, params.first().map(|x| x.1.as_ref()), 1)},
        Tm::SumCase { is_trait, typ, index, datas: params } => {
            let case_name = match typ.as_ref() {
                Tm::Sum(_, _, cases, _) => cases.get(*index as usize).map(|c| c.data.as_str()).unwrap_or("?"),
                _ => "?",
            };
            format!(
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
                    other => panic!(
    "SumCase expected Tm::Sum, but got `{other:?}`\n  at pretty_tm(prec={prec}, indent={indent})"
),
                },
                case_name,
                params
                    .iter()
                    .map(|tm| pretty_tm_indent(prec, indent, ns.clone(), &tm.1))
                    .reduce(|acc, x| acc + ", " + &x)
                    .map(|x| format!("({x})"))
                    .unwrap_or("".to_owned()),
            )
        },
        Tm::Call(name, args, body) => {
            if matches!(body.as_ref(), Tm::Match(..)) {
                go_call(prec, indent, &ns, name, args)
            } else {
                pretty_tm_indent(prec, indent, ns, body)
            }
        },
        Tm::OpCall { symbol, name, args, .. } => {
            // Operator-symbol recovery: an inlined helper call backing an
            // operator method (`nat_add_helper x y` for `x + y`) renders in
            // infix (`x + y`) or prefix (`!x`) form.  Args are quoted in
            // display order (head first).
            match (args.len(), args.head()) {
                (2, Some((a1, Icit::Expl))) => {
                    let tail = args.tail();
                    let a2 = tail.head().unwrap();
                    let ret = format!(
                        "{} {} {}",
                        pretty_tm_indent(ATP, indent, ns.clone(), a1),
                        symbol,
                        pretty_tm_indent(ATP, indent, ns, &a2.0),
                    );
                    if prec > APPP { bracket(ret) } else { ret }
                }
                (1, Some((a1, Icit::Expl))) => {
                    let ret = format!("{}{}", symbol, pretty_tm_indent(ATP, indent, ns, a1));
                    if prec > APPP { bracket(ret) } else { ret }
                }
                _ => {
                    // Unreachable in practice (quote only builds 1/2-arg
                    // all-explicit OpCalls); fall back to the plain call form.
                    go_call(prec, indent, &ns, name, args)
                }
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
    // Iterative: big `Nat` literals are million-deep `succ` chains, and the
    // recursive version consumed one native stack frame per `succ`.
    let mut sum = sum;
    let mut param = param;
    loop {
        match param {
            Some(Tm::SumCase { is_trait, typ, index, datas: params }) if matches!(
                typ.as_ref(),
                Tm::Sum(name, _, _, _) if name.data == "Nat",
            ) => {
                if *index == 0 {
                    return format!("{sum}");
                }
                sum += 1;
                param = params.first().map(|x| x.1.as_ref());
            }
            Some(tm) => return format!("{} + {}", pretty_tm_indent(prec, indent, ns, tm), sum),
            None => return format!("unknown + {}", sum),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::list::List;
    use crate::parser_lib::Span;

    fn decl(name: &str) -> std::sync::Arc<Tm> {
        Tm::Decl(Span {
            data: SmolStr::new(name),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        })
        .into()
    }

    fn app(f: std::sync::Arc<Tm>, u: std::sync::Arc<Tm>) -> std::sync::Arc<Tm> {
        Tm::App(f, u, Icit::Expl).into()
    }

    fn pretty(tm: &Tm) -> String {
        pretty_tm(0, List::new(), tm)
    }

    fn pi(name: &str, icit: Icit, a: Arc<Tm>, b: Arc<Tm>) -> Arc<Tm> {
        Tm::Pi(
            Span { data: SmolStr::new(name), start_offset: 0, end_offset: 0, path_id: 0 },
            icit,
            a,
            b,
        ).into()
    }

    fn lam(name: &str, icit: Icit, body: Arc<Tm>) -> Arc<Tm> {
        Tm::Lam(
            Span { data: SmolStr::new(name), start_offset: 0, end_offset: 0, path_id: 0 },
            icit,
            body,
        ).into()
    }

    #[test]
    fn pi_chain_folds_independent_binders() {
        // `(x: A) → (y: B) → C` folds to `(x: A, y: B) → C` when the second
        // domain does not reference the first binder.
        let chain = pi("x", Icit::Expl, decl("A"), pi("y", Icit::Expl, decl("B"), decl("C")));
        assert_eq!(pretty(&chain), "(x: A, y: B) → C");
    }

    #[test]
    fn pi_chain_keeps_dependent_binder_separate() {
        // `(x: A) → (y: B x) → C`: y's domain references x, so the groups
        // must stay separate — folding would silently drop the dependency.
        let dep = pi(
            "x",
            Icit::Expl,
            decl("A"),
            pi("y", Icit::Expl, app(decl("B"), Tm::Var(crate::L13_namespace::Ix(0)).into()), decl("C")),
        );
        assert_eq!(pretty(&dep), "(x: A) → (y: B x) → C");
    }

    #[test]
    fn pi_folds_deep_chain_with_dependent_head() {
        // `(x: A) → (y: B x) → (z: C) → D`: y depends on x, but z is
        // independent of y — each segment folds on its own.
        let chain = pi(
            "x",
            Icit::Expl,
            decl("A"),
            pi(
                "y",
                Icit::Expl,
                app(decl("B"), Tm::Var(crate::L13_namespace::Ix(0)).into()),
                pi("z", Icit::Expl, decl("C"), decl("D")),
            ),
        );
        assert_eq!(pretty(&chain), "(x: A) → (y: B x, z: C) → D");
    }

    #[test]
    fn pi_implicit_binder_uses_square_brackets() {
        // Implicit binders use the parser's `[x: A]` syntax, not `{x: A}`.
        let impl_pi = pi("T", Icit::Impl, Tm::U(0).into(), Tm::U(0).into());
        assert_eq!(pretty(&impl_pi), "[T: Type 0] → Type 0");
    }

    #[test]
    fn lam_implicit_binder_uses_square_brackets() {
        // Implicit lambda binders use `[x] => ...`, not `{x} => ...`.
        let lam_impl = lam("T", Icit::Impl, lam("x", Icit::Expl, Tm::Var(crate::L13_namespace::Ix(0)).into()));
        assert_eq!(pretty(&lam_impl), "[T] => x => x");
    }

    #[test]
    fn pi_merges_independent_implicit_binders() {
        // `[A: Type 0] → [B: Type 0] → C` folds to `[A: Type 0, B: Type 0] → C`.
        let chain = pi("A", Icit::Impl, Tm::U(0).into(), pi("B", Icit::Impl, Tm::U(0).into(), decl("C")));
        assert_eq!(pretty(&chain), "[A: Type 0, B: Type 0] → C");
    }

    #[test]
    fn pi_groups_mix_implicit_and_explicit() {
        // Independent mixed-icity binders concatenate like the source
        // `def f[T](x: A)` form; a zero-width space keeps the `](` boundary
        // from forming a markdown link (same convention as `Call`/`Sum`).
        let mixed = pi("T", Icit::Impl, Tm::U(0).into(), pi("x", Icit::Expl, decl("Nat"), decl("Nat")));
        assert_eq!(pretty(&mixed), "[T: Type 0]\u{200b}(x: Nat) → Nat");
    }

    #[test]
    fn pi_folding_preserves_shadowing_renames() {
        // Binder names are freshened in order; folding must not change names.
        let chain = pi("x", Icit::Expl, decl("A"), pi("x", Icit::Expl, decl("B"), decl("C")));
        assert_eq!(pretty(&chain), "(x: A, x': B) → C");
    }

    #[test]
    fn pi_anonymous_codomain_keeps_arrow() {
        // Anonymous binders (`A → B`) are not folded into named groups.
        let chain = pi("x", Icit::Expl, decl("A"), pi("_", Icit::Expl, decl("B"), decl("C")));
        assert_eq!(pretty(&chain), "(x: A) → B → C");
    }

    #[test]
    fn mentions_outer_n_tracks_binder_depths() {
        use crate::L13_namespace::Ix;
        // Var(0) is the innermost of n=1 binders.
        assert!(mentions_outer_n(&Tm::Var(Ix(0)), 1));
        // Var(1) is beyond n=1, but inside n=2.
        assert!(!mentions_outer_n(&Tm::Var(Ix(1)), 1));
        assert!(mentions_outer_n(&Tm::Var(Ix(1)), 2));
        assert!(!mentions_outer_n(&Tm::Var(Ix(2)), 2));
        // A binder introduced inside the term shifts indices: a Pi's domain
        // is still under the outer scope (Var(0) = outer binder), while its
        // codomain's Var(0) refers to the internal binder only.
        let dom_ref = pi("z", Icit::Expl, Tm::Var(Ix(0)).into(), decl("W"));
        assert!(mentions_outer_n(&dom_ref, 1));
        let codom_ref = pi("z", Icit::Expl, decl("W"), Tm::Var(Ix(0)).into());
        assert!(!mentions_outer_n(&codom_ref, 1));
        // Nested applications propagate the check to all subterms.
        assert!(mentions_outer_n(&app(app(decl("F"), Tm::Var(Ix(0)).into()), decl("G")), 1));
    }

    #[test]
    fn infix_recovery_for_operator_declarations() {
        // Full two-argument applications of an operator declaration
        // (restored by `quote` from an inlined helper call) render in
        // infix form.
        assert_eq!(pretty(&app(app(decl("+"), decl("x")), decl("y"))), "x + y");
        assert_eq!(pretty(&app(app(decl("*"), decl("a")), decl("b"))), "a * b");
        assert_eq!(pretty(&app(app(decl("-"), decl("a")), decl("b"))), "a - b");
        assert_eq!(pretty(&app(app(decl("/"), decl("a")), decl("b"))), "a / b");
        assert_eq!(pretty(&app(app(decl("%"), decl("a")), decl("b"))), "a % b");
        // Multi-character user-defined operators work automatically.
        assert_eq!(pretty(&app(app(decl("+++"), decl("a")), decl("b"))), "a +++ b");
        assert_eq!(pretty(&app(app(decl("<=>"), decl("a")), decl("b"))), "a <=> b");
        // One-argument operator applications render in prefix form.
        assert_eq!(pretty(&app(decl("!"), decl("x"))), "!x");
        assert_eq!(pretty(&app(decl("~"), decl("x"))), "~x");
    }

    #[test]
    fn no_recovery_for_plain_identifiers() {
        // Non-operator declarations keep the ordinary application form,
        // whether partial or fully applied.
        assert_eq!(pretty(&app(decl("nat_add_helper"), decl("x"))), "nat_add_helper x");
        assert_eq!(
            pretty(&app(app(decl("nat_add_helper"), decl("x")), decl("y"))),
            "nat_add_helper x y"
        );
        assert_eq!(pretty(&app(app(decl("nat_max"), decl("a")), decl("b"))), "nat_max a b");
    }

    #[test]
    fn infix_recovery_requires_explicit_arguments() {
        // An implicit second argument must not trigger infix recovery;
        // the inner explicit one-argument app still renders prefix.
        let implicit = Tm::App(
            app(decl("+"), decl("x")).into(),
            decl("y").into(),
            Icit::Impl,
        );
        assert_eq!(pretty(&implicit), "+x [y]");
        // An implicit first argument must not trigger infix recovery either.
        let implicit_first = Tm::App(
            Tm::App(decl("+").into(), decl("x").into(), Icit::Impl).into(),
            decl("y").into(),
            Icit::Expl,
        );
        assert_eq!(pretty(&implicit_first), "+ [x] y");
    }

    #[test]
    fn infix_recovery_parens_match_application_style() {
        // Inside an application, the infix result gets the same `{...}`
        // brackets that a plain application would get at ATP precedence.
        let nested = app(decl("f"), app(app(decl("+"), decl("x")), decl("y")));
        assert_eq!(pretty(&nested), "f {x + y}");
        // Nested operator applications: the left argument is bracketed.
        let left_nested = app(app(decl("+"), app(app(decl("+"), decl("x")), decl("y"))), decl("z"));
        assert_eq!(pretty(&left_nested), "{x + y} + z");
        let right_nested = app(app(decl("+"), decl("x")), app(app(decl("+"), decl("y")), decl("z")));
        assert_eq!(pretty(&right_nested), "x + {y + z}");
    }

    /// The `OpCall` shape produced by quote recovery (an inlined helper
    /// call carrying the operator symbol) renders in infix/prefix form.
    #[test]
    fn infix_recovery_for_opcall() {
        fn opcall(symbol: &str, args: &[&str]) -> std::sync::Arc<Tm> {
            let mut list = List::new();
            for arg in args.iter().rev() {
                list = list.prepend((decl(arg), Icit::Expl));
            }
            Tm::OpCall {
                symbol: SmolStr::new(symbol),
                name: SmolStr::new("helper"),
                args: list,
                body: Tm::Match(decl("y").into(), Vec::new()).into(),
            }
            .into()
        }
        assert_eq!(pretty(&opcall("+", &["x", "y"])), "x + y");
        assert_eq!(pretty(&opcall("+++", &["a", "b"])), "a +++ b");
        assert_eq!(pretty(&opcall("!", &["x"])), "!x");
        // Parens inside an application match the ATP bracket style.
        let nested = app(decl("f"), opcall("+", &["x", "y"]));
        assert_eq!(pretty(&nested), "f {x + y}");
    }

    /// A `Tm::Call` with a `Match` body renders in call form: implicit
    /// arguments grouped in square brackets, explicit arguments in parens.
    #[test]
    fn call_form_splits_implicit_and_explicit_args() {
        fn call(args: &[(&str, Icit)]) -> std::sync::Arc<Tm> {
            let mut list = List::new();
            for (arg, icit) in args.iter().rev() {
                list = list.prepend((decl(arg), *icit));
            }
            Tm::Call(
                SmolStr::new("foo"),
                list,
                Tm::Match(decl("y").into(), Vec::new()).into(),
            )
            .into()
        }

        // Mixed implicit + explicit args: `foo[xxx](xx, xxx)` (a zero-width
        // space keeps the `](` boundary from forming a markdown link, cf. `Sum`).
        assert_eq!(
            pretty(&call(&[
                ("x", Icit::Impl),
                ("y", Icit::Impl),
                ("a", Icit::Expl),
                ("b", Icit::Expl),
            ])),
            "foo[x, y]\u{200b}(a, b)"
        );
        // Implicit args only.
        assert_eq!(
            pretty(&call(&[("x", Icit::Impl), ("y", Icit::Impl)])),
            "foo[x, y]"
        );
        // Explicit args only (unchanged plain call form).
        assert_eq!(
            pretty(&call(&[("a", Icit::Expl), ("b", Icit::Expl)])),
            "foo(a, b)"
        );
        // Implicit args that are themselves applications stay quoted.
        let mut nested_list = List::new();
        nested_list = nested_list.prepend((decl("y"), Icit::Expl));
        nested_list = nested_list.prepend((app(decl("g"), decl("x")), Icit::Impl));
        let nested_call = Tm::Call(
            SmolStr::new("foo"),
            nested_list,
            Tm::Match(decl("y").into(), Vec::new()).into(),
        );
        assert_eq!(pretty(&nested_call), "foo[g x]\u{200b}(y)");
        // The `Tm::OpCall` fallback path uses the same call form.
        let mut list = List::new();
        list = list.prepend((decl("y"), Icit::Expl));
        list = list.prepend((decl("x"), Icit::Impl));
        let opcall = Tm::OpCall {
            symbol: SmolStr::new("+"),
            name: SmolStr::new("helper"),
            args: list,
            body: Tm::Match(decl("y").into(), Vec::new()).into(),
        };
        assert_eq!(pretty(&opcall), "helper[x]\u{200b}(y)");
    }
}
