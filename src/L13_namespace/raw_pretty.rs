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
        // `U(u32, Span)`：打 `Type N`（2026-11-25）。本层 lexer 里 `U` **不是关键字**
        // （只有 `Type`，见 parser/lex.rs 的 KEYWORD 表），所以旧的 `U` / `U(n)`
        // 两种形态都回灌不了自解析；改成与 `pretty.rs` 的 `Tm::U(uni)` → `Type {uni}` 一致。
        Raw::U(n, _) => {
            out.push_str("Type ");
            out.push_str(&n.to_string());
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

/// `Raw` 里是否引用了**本组已收集的** binder（按 De Bruijn 深度粗判）。
///
/// `depth` = 已收集的 binder 数；`Raw::Var` 命中名字表里最近的同名 binder ⇒ 引用本组。
fn mentions_group(t: &Raw, group: &[smol_str::SmolStr], depth: usize) -> bool {
    match t {
        Raw::Var(x) => group.iter().any(|g| g.as_str() == x.data.as_str()),
        Raw::Obj(x, _) => mentions_group(x, group, depth),
        Raw::Lam(_, _, b) => mentions_group(b, group, depth),
        Raw::App(f, a, _) => mentions_group(f, group, depth) || mentions_group(a, group, depth),
        Raw::Pi(_, _, a, b) => mentions_group(a, group, depth) || mentions_group(b, group, depth),
        Raw::Let(_, a, x, u) => {
            mentions_group(a, group, depth)
                || mentions_group(x, group, depth)
                || mentions_group(u, group, depth)
        }
        Raw::Match(s, arms) => {
            mentions_group(s, group, depth) || arms.iter().any(|(_, b)| mentions_group(b, group, depth))
        }
        Raw::Sum(_, params, _, _, _) => params.iter().any(|(_, _, ty)| mentions_group(ty, group, depth)),
        Raw::SumCase { typ, datas, .. } => {
            mentions_group(typ, group, depth) || datas.iter().any(|(_, r, _)| mentions_group(r, group, depth))
        }
        Raw::Tm(..) => true, // 保守：pre-checked 节点一律视为依赖
        _ => false,
    }
}
/// 从 def 的签名（params + ret_type）拼出源码形态的类型串。
pub fn def_type_from_source(
    params: &[(Span<smol_str::SmolStr>, Raw, Icit)],
    ret: &Raw,
) -> String {
    // 与 `pretty_tm` 的 Pi 折叠口径一致：域不依赖本组已收集 binder 的相邻参数
    // 合并成一组（`(x: A, y: B) → C`），依赖的另起一组。隐式参数用方括号。
    let mut out = String::new();
    let mut group: Vec<(smol_str::SmolStr, &Raw, Icit)> = Vec::new();
    let mut names: Vec<smol_str::SmolStr> = Vec::new();

    let flush = |group: &mut Vec<(smol_str::SmolStr, &Raw, Icit)>,
                 names: &mut Vec<smol_str::SmolStr>,
                 out: &mut String| {
        if group.is_empty() {
            return;
        }
        let mut cur_icit = group[0].2;
        out.push(if cur_icit == Icit::Impl { '[' } else { '(' });
        for (idx, (n, ty, icit)) in group.iter().enumerate() {
            if icit != &cur_icit {
                out.push(']');
                out.push('(');
                cur_icit = *icit;
            } else if idx > 0 {
                out.push_str(", ");
            }
            out.push_str(n.as_str());
            // L13 既有显示口径：冒号前**无空格**（`(a: Nat, b: Boolean)`）。
            out.push_str(": ");
            go(LETP, ty, out);
            names.push(n.clone());
        }
        out.push(if cur_icit == Icit::Impl { ']' } else { ')' });
        out.push_str(" → ");
        group.clear();
        names.clear();
    };

    for (name, ty, icit) in params.iter() {
        if !group.is_empty() {
            // 新参数的域若引用了本组已收集的 binder，就另起一组。
            let cur_names: Vec<smol_str::SmolStr> = group.iter().map(|(n, _, _)| n.clone()).collect();
            if mentions_group(ty, &cur_names, 0) {
                flush(&mut group, &mut names, &mut out);
            }
        }
        group.push((name.data.clone(), ty, *icit));
    }
    if !group.is_empty() {
        // 最后一组之后是返回类型：组内合并，但组间靠 `→` 分开。
        let cur_names: Vec<smol_str::SmolStr> = group.iter().map(|(n, _, _)| n.clone()).collect();
        if !mentions_group(ret, &cur_names, 0) {
            // 返回类型独立 ⇒ 全部参数合并成一组（`(x: A, y: B) → C`）。
            // 已经在 group 里，直接 flush 即可。
            flush(&mut group, &mut names, &mut out);
        } else {
            flush(&mut group, &mut names, &mut out);
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
