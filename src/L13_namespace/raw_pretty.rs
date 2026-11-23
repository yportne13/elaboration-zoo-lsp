//! `Raw`（源码 AST）的 pretty：用于**源码注解渲染**（L13 版，L07/L08 的平移）。
//!
//! 有显式类型注解的 def，hover/登记串直接打印**源码里的类型文本**，而不是求值后的值。
//! 这样 `def g(n: Nat): T n` 显示 `(n : Nat) → T n`，而不是展开成 `match n { … }`；
//! 也**完全绕开** `quote` / `quote_nat`（后者会把 `Val::Nat(k)` 展开成 k 层 SumCase 链）。

use crate::parser_lib::Span;

use super::parser::syntax::{Either, Icit, Pattern, Raw};

const ATP: u8 = 3; // atom
const APPP: u8 = 2; // app
const PIP: u8 = 1; // pi
const LETP: u8 = 0; // let / lam

fn go(prec: u8, t: &Raw, out: &mut String) {
    match t {
        Raw::Var(x) => out.push_str(x.data.as_str()),
        Raw::Obj(x, f) => {
            let need = prec > ATP;
            if need {
                out.push('(');
            }
            go(ATP, x, out);
            out.push('.');
            if let Some(f) = f {
                out.push_str(f.data.as_str());
            }
            if need {
                out.push(')');
            }
        }
        // `U(u32, Span)`：只打层级（`U` = 0）。
        Raw::U(n, _) => {
            if *n == 0 {
                out.push('U');
            } else {
                out.push_str("U(");
                out.push_str(&n.to_string());
                out.push(')');
            }
        }
        // `Nat(Span<u64>)`：源码里的十进制字面量，原样打印（不建链）。
        Raw::Nat(n) => out.push_str(&n.data.to_string()),
        Raw::Hole(_) => out.push('_'),
        Raw::LiteralIntro(s) => out.push_str(&s.data),
        Raw::App(f, a, i) => {
            let need = prec > APPP;
            if need {
                out.push('(');
            }
            go(APPP, f, out);
            out.push(' ');
            match i {
                Either::Icit(Icit::Impl) => {
                    out.push('[');
                    go(ATP, a, out);
                    out.push(']');
                }
                _ => go(ATP, a, out),
            }
            if need {
                out.push(')');
            }
        }
        Raw::Lam(x, i, body) => {
            let need = prec > LETP;
            if need {
                out.push('(');
            }
            out.push_str(x.data.as_str());
            match i {
                Either::Name(n) => {
                    out.push_str(" = ");
                    out.push_str(n.data.as_str());
                    out.push_str(" => ");
                }
                Either::Icit(_) => out.push_str(" => "),
            }
            go(LETP, body, out);
            if need {
                out.push(')');
            }
        }
        Raw::Pi(x, i, a, b) => {
            let need = prec > PIP;
            if need {
                out.push('(');
            }
            match i {
                Icit::Impl => {
                    out.push('[');
                    out.push_str(x.data.as_str());
                    out.push_str(" : ");
                    go(LETP, a, out);
                    out.push(']');
                }
                Icit::Expl => {
                    out.push('(');
                    out.push_str(x.data.as_str());
                    out.push_str(" : ");
                    go(LETP, a, out);
                    out.push(')');
                }
            }
            out.push_str(" → ");
            go(PIP, b, out);
            if need {
                out.push(')');
            }
        }
        Raw::Let(x, a, t, u) => {
            let need = prec > LETP;
            if need {
                out.push('(');
            }
            out.push_str("let ");
            out.push_str(x.data.as_str());
            out.push_str(" : ");
            go(LETP, a, out);
            out.push_str(" = ");
            go(LETP, t, out);
            out.push_str("; ");
            go(LETP, u, out);
            if need {
                out.push(')');
            }
        }
        Raw::Match(scrut, cases) => {
            let need = prec > LETP;
            if need {
                out.push('(');
            }
            out.push_str("match ");
            go(ATP, scrut, out);
            out.push_str(" { ");
            for (idx, (p, b)) in cases.iter().enumerate() {
                if idx > 0 {
                    out.push_str("; ");
                }
                out.push_str("case ");
                out.push_str(&pattern(p));
                out.push_str(" => ");
                go(LETP, b, out);
            }
            out.push_str(" }");
            if need {
                out.push(')');
            }
        }
        // `Sum(名, 参数, 构造子, universe, is_trait)`：类型级的和/枚举。
        Raw::Sum(name, params, cases, universe, is_trait) => {
            if *is_trait {
                out.push_str("trait ");
            } else {
                out.push_str("enum ");
            }
            out.push_str(name.data.as_str());
            for (n, _, ty) in params.iter() {
                out.push('(');
                out.push_str(n.data.as_str());
                out.push_str(" : ");
                go(LETP, ty, out);
                out.push(')');
            }
            if *universe != 0 {
                out.push_str(&format!(" : U({universe})"));
            }
            out.push_str(" { ");
            for c in cases.iter() {
                out.push_str(c.data.as_str());
                out.push(' ');
            }
            out.push('}');
        }
        Raw::SumCase {
            is_trait,
            typ,
            case_name,
            ..
        } => {
            if *is_trait {
                out.push_str("trait.");
            }
            go(APPP, typ, out);
            out.push('.');
            out.push_str(case_name.data.as_str());
        }
        // pre-checked 值（class Phase B 内部节点，用户源码里不出现）：按占位打印，
        // 调用方应当在此前回落到值渲染（`has_source_type` 的守卫只认用户可写的形态）。
        Raw::Tm(..) => out.push_str("<pre-checked>"),
    }
}

fn pattern(p: &Pattern) -> String {
    match p {
        Pattern::Any(_, _) => "_".to_owned(),
        Pattern::Con(n, subs, _) => {
            if subs.is_empty() {
                n.data.to_string()
            } else {
                let inner: Vec<String> = subs.iter().map(pattern).collect();
                format!("{}({})", n.data, inner.join(", "))
            }
        }
    }
}

/// 从 def 的签名（params + ret_type）拼出源码形态的类型串。
pub fn def_type_from_source(params: &[(Span<smol_str::SmolStr>, Raw, Icit)], ret: &Raw) -> String {
    let mut out = String::new();
    for (name, ty, icit) in params.iter() {
        match icit {
            Icit::Impl => {
                out.push('[');
                out.push_str(name.data.as_str());
                out.push_str(" : ");
                go(LETP, ty, &mut out);
                out.push_str("] → ");
            }
            Icit::Expl => {
                out.push('(');
                out.push_str(name.data.as_str());
                out.push_str(" : ");
                go(LETP, ty, &mut out);
                out.push_str(") → ");
            }
        }
    }
    go(LETP, ret, &mut out);
    out
}

/// 签名里是否有用户可写的类型（不是洞）。额外排除 `Raw::Tm`（pre-checked 内部节点）。
pub fn has_source_type(ret: &Raw) -> bool {
    !matches!(ret, Raw::Hole(_)) && !contains_prechecked(ret)
}

fn contains_prechecked(t: &Raw) -> bool {
    match t {
        Raw::Tm(..) => true,
        Raw::Obj(x, _) => contains_prechecked(x),
        Raw::Lam(_, _, b) => contains_prechecked(b),
        Raw::App(f, a, _) => contains_prechecked(f) || contains_prechecked(a),
        Raw::Pi(_, _, a, b) => contains_prechecked(a) || contains_prechecked(b),
        Raw::Let(_, a, x, u) => contains_prechecked(a) || contains_prechecked(x) || contains_prechecked(u),
        Raw::Match(s, arms) => contains_prechecked(s) || arms.iter().any(|(_, b)| contains_prechecked(b)),
        Raw::Sum(_, params, _, _, _) => params.iter().any(|(_, _, ty)| contains_prechecked(ty)),
        Raw::SumCase { typ, datas, .. } => {
            contains_prechecked(typ) || datas.iter().any(|(_, r, _)| contains_prechecked(r))
        }
        _ => false,
    }
}
