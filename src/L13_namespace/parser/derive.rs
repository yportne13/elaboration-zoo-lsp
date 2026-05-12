use std::collections::HashMap;

use smol_str::SmolStr;

use super::syntax::{Decl, Either, Icit, Raw};
use crate::parser_lib::{Span, ToSpan};
use super::empty_span;

pub type DeriveMacro = fn(&Decl) -> Vec<Decl>;
pub type DeriveRegistry = HashMap<String, DeriveMacro>;

pub fn default_derive_registry() -> DeriveRegistry {
    let mut registry: DeriveRegistry = HashMap::new();
    registry.insert("Show".to_string(), derive_show);
    registry
}

/// Generate impl blocks for the given derive traits on the given declaration.
pub fn expand_derive(
    registry: &DeriveRegistry,
    traits: &[Span<SmolStr>],
    decl: &Decl,
) -> Vec<Decl> {
    let mut result = vec![];
    for trait_name in traits {
        if let Some(derive_fn) = registry.get(trait_name.data.as_str()) {
            result.extend(derive_fn(decl));
        }
    }
    result
}

/// Build the self type expression from the type name and its type parameters.
/// e.g., for `Span[T]` returns `Span T` (applied to type param)
fn build_self_ty(name: &Span<SmolStr>, params: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    params.iter().fold(
        Raw::Var(name.clone()),
        |ret, (pname, _, icit)| Raw::App(
            Box::new(ret),
            Box::new(Raw::Var(pname.clone())),
            Either::Icit(*icit),
        ),
    )
}

/// Derive Show: generates a `show` method that pretty-prints the value.
fn derive_show(decl: &Decl) -> Vec<Decl> {
    match decl {
        Decl::Enum { name, params, cases, .. } => {
            let self_ty = build_self_ty(name, params);
            let impl_params: Vec<_> = params.iter()
                .filter(|(_, _, icit)| *icit == Icit::Impl)
                .cloned()
                .collect();

            if cases.len() == 1 {
                // Struct: just return the type name as a string
                let body = Raw::LiteralIntro(empty_span(format!("\"{}()\"", name.data)));

                vec![Decl::ImplDecl {
                    name: self_ty,
                    params: impl_params,
                    trait_name: name.to_span().map(|_| SmolStr::new("")),
                    trait_params: vec![],
                    methods: vec![Decl::Def {
                        name: empty_span(SmolStr::new("show")),
                        params: vec![],
                        ret_type: Raw::Var(empty_span(SmolStr::new("String"))),
                        body,
                    }],
                    need_create: true,
                }]
            } else {
                // Enum: match on constructors and return their names
                let mut match_body = vec![];
                for (case_name, fields, _) in cases {
                    let body = Raw::LiteralIntro(empty_span(format!("\"{}\"", case_name.data)));
                    let pat_fields: Vec<super::syntax::Pattern> = fields.iter().map(|(_, _, icit)| {
                        super::syntax::Pattern::Any(empty_span(true), Either::Icit(*icit))
                    }).collect();
                    let pattern = super::syntax::Pattern::Con(
                        case_name.clone(),
                        pat_fields,
                        Either::Icit(Icit::Expl),
                    );
                    match_body.push((pattern, body));
                }

                let match_expr = Raw::Match(
                    Box::new(Raw::Var(empty_span(SmolStr::new("this")))),
                    match_body,
                );

                vec![Decl::ImplDecl {
                    name: self_ty,
                    params: impl_params,
                    trait_name: name.to_span().map(|_| SmolStr::new("")),
                    trait_params: vec![],
                    methods: vec![Decl::Def {
                        name: empty_span(SmolStr::new("show")),
                        params: vec![],
                        ret_type: Raw::Var(empty_span(SmolStr::new("String"))),
                        body: match_expr,
                    }],
                    need_create: true,
                }]
            }
        }
        _ => vec![],
    }
}
