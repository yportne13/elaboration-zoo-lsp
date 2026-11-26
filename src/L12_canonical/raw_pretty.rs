//! `Raw`（源码 AST）的 pretty：用于**源码注解渲染**（方案 4）。
//!
//! 有显式类型注解的 def，hover/登记串直接打印**源码里的类型文本**，而不是求值后的
//! 值——因此 `def g(n: Nat): T n` 显示 `(n: Nat) → T n` 而不是展开的 `match n { … }`。
//! 无注解（`ret_type == Hole`）仍走值渲染（那里没有源码可打）。

use smol_str::SmolStr;
use super::parser::syntax::{Decl, Either, Icit, Pattern, Raw};

const ATP: u8 = 3; // atom
const APPP: u8 = 2; // app
const PIP: u8 = 1; // pi
const LETP: u8 = 0; // let / lam

fn go(prec: u8, t: &Raw, out: &mut String) {
    match t {
        Raw::Var(x) => out.push_str(&x.data),
        Raw::Obj(x, f) => {
            let need = prec > ATP;
            if need {
                out.push('(');
            }
            go(ATP, x, out);
            out.push('.');
            out.push_str(&f.data);
            if need {
                out.push(')');
            }
        }
// TYPE_UNI_ARM（2026-11-25）：本层起 `U` **不是关键字**（lexer 只认 `Type`，
        // 见 parser/lex.rs 的 KEYWORD 表），所以源码注解渲染必须打 `Type N` 才能回灌
        // 自解析；层级也必须保留——此前一律打成裸 `U`，`Type 1` 与 `Type 0` 无法区分。
        // 与同层 `pretty.rs` 的 `Tm::U(uni)` → `Type {uni}` 对齐。
        Raw::U(n) => {
            out.push_str("Type ");
            out.push_str(&n.to_string());
        }
        Raw::Hole => out.push('_'),
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
            out.push_str(&x.data);
            match i {
                Either::Icit(Icit::Impl) => out.push_str(" => "),
                Either::Name(n) => {
                    out.push_str(" = ");
                    out.push_str(&n.data);
                    out.push_str(" => ");
                }
                Either::Icit(Icit::Expl) => out.push_str(" => "),
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
                    out.push_str(&x.data);
                    out.push_str(" : ");
                    go(LETP, a, out);
                    out.push(']');
                }
                Icit::Expl => {
                    out.push('(');
                    out.push_str(&x.data);
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
            out.push_str(&x.data);
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
        Raw::Sum(name, params, cases, _) => {
            out.push_str(&name.data);
            for (n, _, _) in params.iter() {
                out.push('(');
                out.push_str(&n.data);
                out.push_str(" : _)");
            }
            out.push_str(" { ");
            for c in cases.iter() {
                out.push_str(&c.data);
                out.push(' ');
            }
            out.push('}');
        }
        Raw::SumCase { typ, case_name, .. } => {
            go(APPP, typ, out);
            out.push('.');
            out.push_str(&case_name.data);
        }
    }
}

fn pattern(p: &Pattern) -> String {
    // 保守：模式只在 match 的臂里出现，类型注解里几乎不会有；给个形状即可。
    format!("{p:?}")
}

/// 从 def 的签名（params + ret_type）拼出源码形态的类型串。
pub fn def_type_from_source(
    params: &[(crate::parser_lib::Span<SmolStr>, Raw, Icit)],
    ret: &Raw,
) -> String {
    let mut out = String::new();
    for (name, ty, icit) in params.iter() {
        match icit {
            Icit::Impl => {
                out.push('[');
                out.push_str(&name.data);
                out.push_str(" : ");
                go(LETP, ty, &mut out);
                out.push_str("] → ");
            }
            Icit::Expl => {
                out.push('(');
                out.push_str(&name.data);
                out.push_str(" : ");
                go(LETP, ty, &mut out);
                out.push_str(") → ");
            }
        }
    }
    go(LETP, ret, &mut out);
    out
}

/// 声明是否值得用源码渲染（有显式返回类型注解）。
pub fn has_source_type(ret: &Raw) -> bool {
    !matches!(ret, Raw::Hole)
}
