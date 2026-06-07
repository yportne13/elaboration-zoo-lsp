use std::collections::HashMap;

use smol_str::SmolStr;

use super::syntax::{Decl, Either, Icit, Pattern, Raw};
use crate::parser_lib::{Span, ToSpan};
use super::empty_span;

pub type DeriveMacro = fn(&Decl) -> Vec<Decl>;
pub type DeriveRegistry = HashMap<String, DeriveMacro>;

pub fn default_derive_registry() -> DeriveRegistry {
    let mut registry: DeriveRegistry = HashMap::new();
    registry.insert("Show".to_string(), derive_show);
    registry.insert("Bundle".to_string(), derive_bundle);
    registry
}

/// Expand derive macros: for each trait in `traits`, generate the corresponding
/// impl blocks and return them alongside the original declaration.
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
/// e.g., for `Span[T]` returns `Span T` (type applied to its implicit param)
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

/// Build `string_concat a b`
fn str_cat(a: Raw, b: Raw) -> Raw {
    Raw::App(
        Box::new(Raw::App(
            Box::new(Raw::Var(empty_span(SmolStr::new("string_concat")))),
            Box::new(a),
            Either::Icit(Icit::Expl),
        )),
        Box::new(b),
        Either::Icit(Icit::Expl),
    )
}

/// Build a show body for a struct-like type (single constructor).
/// Generates: `"TypeName(f1, f2)"` showing field values via `.show`.
fn build_struct_show_body(name: &Span<SmolStr>, fields: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    let type_name = name.data.as_str();

    if fields.is_empty() {
        return Raw::LiteralIntro(empty_span(type_name.to_owned()));
    }

    let mut result = Raw::LiteralIntro(empty_span(format!("{}(", type_name)));

    for (i, (field_name, _, _)) in fields.iter().enumerate() {
        let field_val = Raw::Obj(
            Box::new(Raw::Var(empty_span(SmolStr::new("this")))),
            Some(field_name.clone()),
        );
        let field_show = Raw::Obj(
            Box::new(field_val),
            Some(empty_span(SmolStr::new("show"))),
        );
        result = str_cat(result, field_show);

        if i + 1 < fields.len() {
            result = str_cat(result, Raw::LiteralIntro(empty_span(", ".to_owned())));
        }
    }

    str_cat(result, Raw::LiteralIntro(empty_span(")".to_owned())))
}

/// Build a show body for an enum constructor case with fields.
/// Generates a pattern that binds each field as a variable,
/// and a body that concatenates the constructor name with the field shows.
fn build_enum_case(
    case_name: &Span<SmolStr>,
    fields: &[(Span<SmolStr>, Raw, Icit)],
) -> (Pattern, Raw) {
    let name_str = case_name.data.as_str();

    let pat_fields: Vec<Pattern> = fields.iter().map(|(field_name, _, icit)| {
        Pattern::Con(field_name.clone(), vec![], Either::Icit(*icit))
    }).collect();

    let pattern = Pattern::Con(case_name.clone(), pat_fields, Either::Icit(Icit::Expl));

    let body = if fields.is_empty() {
        Raw::LiteralIntro(empty_span(name_str.to_owned()))
    } else {
        let mut result = Raw::LiteralIntro(empty_span(format!("{}(", name_str)));
        for (i, (field_name, _, _)) in fields.iter().enumerate() {
            let field_show = Raw::Obj(
                Box::new(Raw::Var(field_name.clone())),
                Some(empty_span(SmolStr::new("show"))),
            );
            result = str_cat(result, field_show);
            if i + 1 < fields.len() {
                result = str_cat(result, Raw::LiteralIntro(empty_span(", ".to_owned())));
            }
        }
        str_cat(result, Raw::LiteralIntro(empty_span(")".to_owned())))
    };

    (pattern, body)
}

/// Build a bundle `:=` body: sequences field assignments as nested let-bindings.
/// For struct fields [f1: T1, f2: T2, ...], generates:
///   let __b0 = this.f1 := that.f1;
///   let __b1 = this.f2 := that.f2;
///   unit
fn build_bundle_body(fields: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    if fields.is_empty() {
        return Raw::Var(empty_span(SmolStr::new("unit")));
    }

    let mut result = Raw::Var(empty_span(SmolStr::new("unit")));

    for (i, (field_name, _, _)) in fields.iter().enumerate().rev() {
        let assign = Raw::App(
            Box::new(Raw::Obj(
                Box::new(Raw::Obj(
                    Box::new(Raw::Var(empty_span(SmolStr::new("this")))),
                    Some(field_name.clone()),
                )),
                Some(empty_span(SmolStr::new(":="))),
            )),
            Box::new(Raw::Obj(
                Box::new(Raw::Var(empty_span(SmolStr::new("that")))),
                Some(field_name.clone()),
            )),
            Either::Icit(Icit::Expl),
        );

        result = Raw::Let(
            empty_span(SmolStr::new(format!("__b{}", i))),
            Box::new(Raw::Hole(empty_span(()))),
            Box::new(assign),
            Box::new(result),
        );
    }

    result
}

/// Check whether a Raw type expression is one of the recognised primitive HDL types.
fn is_primitive_type(t: &Raw) -> bool {
    match t {
        Raw::Var(v) => v.data == "Bool",
        Raw::App(inner, _, _) => match inner.as_ref() {
            Raw::Var(v) => v.data == "UInt" || v.data == "SInt" || v.data == "Bits",
            _ => false,
        },
        _ => false,
    }
}

/// Build the signal creation expression for a single field.
/// Recognizes: UInt[w], SInt[w], Bits[w], Bool.
/// Returns `newUInt(prefix+"name", w)`, `newBool(prefix+"name")`, etc.
fn build_field_create_expr(field_name: &Span<SmolStr>, field_type: &Raw) -> Raw {
    let name_expr = str_cat(
        Raw::Var(empty_span(SmolStr::new("prefix"))),
        Raw::LiteralIntro(empty_span(field_name.data.to_string())),
    );

    match field_type {
        Raw::App(inner, width, _) => {
            if let Raw::Var(v) = inner.as_ref() {
                let create_fn = match v.data.as_str() {
                    "UInt" => "newUInt",
                    "SInt" => "newSInt",
                    "Bits" => "newBits",
                    _ => return Raw::Hole(empty_span(())),
                };
                Raw::app(Raw::app(Raw::Var(empty_span(SmolStr::new(create_fn))), name_expr), width.as_ref().clone())
            } else {
                Raw::Hole(empty_span(()))
            }
        }
        Raw::Var(v) if v.data == "Bool" => {
            Raw::app(Raw::Var(empty_span(SmolStr::new("newBool"))), name_expr)
        }
        _ => Raw::Hole(empty_span(())),
    }
}

/// Build the body of `create(prefix: String): Self`.
/// For fields [f1: T1, f2: T2, …]:
///   let __f0 = createSignal("prefix_f1", …);
///   let __f1 = createSignal("prefix_f2", …);
///   new BundleType(__f0, __f1)
fn build_create_body(name: &Span<SmolStr>, fields: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    let ctor = Raw::Var(empty_span(SmolStr::new(format!("{}.mk", name.data))));

    if fields.is_empty() {
        return ctor;
    }

    // Wrap constructor with field variables (in forward order)
    let mut body = ctor;
    for (field_name, _, _) in fields.iter() {
        let var = Raw::Var(empty_span(SmolStr::new(format!("__f{}", field_name.data))));
        body = Raw::App(Box::new(body), Box::new(var), Either::Icit(Icit::Expl));
    }

    // Wrap each let around the body (in reverse order)
    for (field_name, field_type, _) in fields.iter().rev() {
        let var_name = SmolStr::new(format!("__f{}", field_name.data));
        let create_expr = build_field_create_expr(field_name, field_type);
        body = Raw::Let(
            empty_span(var_name),
            Box::new(Raw::Hole(empty_span(()))),
            Box::new(create_expr),
            Box::new(body),
        );
    }

    body
}

/// Derive Bundle: for a single-constructor enum (struct), generates:
///   impl Bundle for StructName { def :=(that: StructName): Unit = ... }
///   impl Into[Self] for Self { … }
///   impl StructName { def create(prefix: String): Self = … }
/// with sequenced field-by-field assignments.
fn derive_bundle(decl: &Decl) -> Vec<Decl> {
    match decl {
        Decl::Enum { name, params, cases, .. } if cases.len() == 1 => {
            let self_ty = build_self_ty(name, params);
            let fields = &cases[0].1;

            let impl_params: Vec<_> = params.iter()
                .filter(|(_, _, icit)| *icit == Icit::Impl)
                .cloned()
                .collect();

            // ── 1. Bundle trait impl (:= bulk assignment) ──
            let bundle_body = build_bundle_body(fields);
            let that_param = (
                empty_span(SmolStr::new("that")),
                self_ty.clone(),
                Icit::Expl,
            );
            let bundle_impl = Decl::ImplDecl {
                name: self_ty.clone(),
                params: impl_params.clone(),
                trait_name: empty_span(SmolStr::new("Bundle")),
                trait_params: vec![],
                methods: vec![(Decl::Def {
                    name: empty_span(SmolStr::new(":=")),
                    params: vec![that_param],
                    ret_type: Raw::Var(empty_span(SmolStr::new("Unit"))),
                    body: bundle_body,
                }, false)],
                need_create: false,
            };

            // ── 2. Into[Self] for Self (so Expr macro's lhs := rhs works) ──
            let into_impl = Decl::ImplDecl {
                name: self_ty.clone(),
                params: impl_params.clone(),
                trait_name: empty_span(SmolStr::new("Into")),
                trait_params: vec![self_ty.clone()],
                methods: vec![(Decl::Def {
                    name: empty_span(SmolStr::new("into")),
                    params: vec![],
                    ret_type: self_ty.clone(),
                    body: Raw::Var(empty_span(SmolStr::new("this"))),
                }, false)],
                need_create: false,
            };

            let mut result = vec![bundle_impl, into_impl];

            // ── 3. Standalone create function (signal factory) ──
            // Generates:
            //   def create_<TypeName>$(typeParams)(prefix: String): TypeName$(typeParams) = …
            // Only emitted when every field is a recognised primitive HDL type
            // (UInt, SInt, Bits, Bool) so we know how to auto-create signals.
            if fields.iter().all(|(_, ft, _)| is_primitive_type(ft)) {
                let create_body = build_create_body(name, fields);
                let mut create_params: Vec<(Span<SmolStr>, Raw, Icit)> = params.iter()
                    .map(|(pn, pt, pi)| (pn.clone(), pt.clone(), *pi))
                    .collect();
                create_params.push((
                    empty_span(SmolStr::new("prefix")),
                    Raw::Var(empty_span(SmolStr::new("String"))),
                    Icit::Expl,
                ));
                result.push(Decl::Def {
                    name: empty_span(SmolStr::new(format!("create_{}", name.data))),
                    params: create_params,
                    ret_type: self_ty,
                    body: create_body,
                });
            }

            result
        }
        _ => vec![],
    }
}

/// Derive Show: generates a proper `impl Show for Type { def show = ... }` block.
fn derive_show(decl: &Decl) -> Vec<Decl> {
    match decl {
        Decl::Enum { name, params, cases, .. } => {
            let self_ty = build_self_ty(name, params);
            let impl_params: Vec<_> = params.iter()
                .filter(|(_, _, icit)| *icit == Icit::Impl)
                .cloned()
                .collect();

            let body = if cases.len() == 1 {
                build_struct_show_body(name, &cases[0].1)
            } else {
                let match_body: Vec<_> = cases.iter()
                    .map(|(case_name, fields, _)| build_enum_case(case_name, fields))
                    .collect();
                Raw::Match(
                    Box::new(Raw::Var(empty_span(SmolStr::new("this")))),
                    match_body,
                )
            };

            vec![Decl::ImplDecl {
                name: self_ty,
                params: impl_params,
                trait_name: empty_span(SmolStr::new("")),
                trait_params: vec![],
                methods: vec![(Decl::Def {
                    name: empty_span(SmolStr::new("show")),
                    params: vec![],
                    ret_type: Raw::Var(empty_span(SmolStr::new("String"))),
                    body,
                }, false)],
                need_create: true,
            }]
        }
        _ => vec![],
    }
}
