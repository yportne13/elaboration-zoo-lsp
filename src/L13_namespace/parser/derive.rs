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
/// For primitive fields, the assignment is guarded by an isInputPort check so
/// that driving an input port (illegal Verilog) is skipped — this lets a
/// master/slave pair be connected with `:=` in both directions.
fn build_bundle_body(fields: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    if fields.is_empty() {
        return Raw::Var(empty_span(SmolStr::new("unit")));
    }

    let mut result = Raw::Var(empty_span(SmolStr::new("unit")));

    for (i, (field_name, field_type, _)) in fields.iter().enumerate().rev() {
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

        // Guard primitive fields with `match isInputPort(this.<f>.zz_expr)`.
        let step = if is_primitive_type(field_type) {
            let lhs_expr = Raw::Obj(
                Box::new(Raw::Obj(
                    Box::new(Raw::Var(empty_span(SmolStr::new("this")))),
                    Some(field_name.clone()),
                )),
                Some(empty_span(SmolStr::new("zz_expr"))),
            );
            let check = Raw::app(Raw::Var(empty_span(SmolStr::new("isInputPort"))), lhs_expr);
            let skip = Raw::Var(empty_span(SmolStr::new("unit")));
            Raw::Match(
                Box::new(check),
                vec![
                    (
                        Pattern::Con(empty_span(SmolStr::new("true")), vec![], Either::Icit(Icit::Expl)),
                        skip,
                    ),
                    (
                        Pattern::Con(empty_span(SmolStr::new("false")), vec![], Either::Icit(Icit::Expl)),
                        assign,
                    ),
                ],
            )
        } else {
            assign
        };

        result = Raw::Let(
            empty_span(SmolStr::new(format!("__b{}", i))),
            Box::new(Raw::Hole(empty_span(()))),
            Box::new(step),
            Box::new(result),
        );
    }

    result
}

/// Direction mode of a generated signal factory.
#[derive(Clone, Copy, PartialEq)]
enum CreateMode {
    /// Plain wires (create_TypeName) — direction markers are ignored.
    Wire,
    /// Master-perspective directed ports (the asMaster method body).
    Master,
    /// Slave-perspective directed ports (the asSlave method body).
    Slave,
}

/// Unwrap a direction marker (`in(...)` / `out(...)` / `inout(...)`) applied to
/// a field type. Returns the marker name (if any) and the wrapped type.
/// The markers are type-level identity functions defined in hdl-bus.typort;
/// the derive reads them before elaboration to learn each field's direction
/// (from the master's point of view).
fn unwrap_dir_marker(t: &Raw) -> (Option<&str>, &Raw) {
    if let Raw::App(inner, arg, Either::Icit(Icit::Expl)) = t {
        if let Raw::Var(v) = inner.as_ref() {
            let name = v.data.as_str();
            if name == "in" || name == "out" || name == "inout" {
                return (Some(name), arg.as_ref());
            }
        }
    }
    (None, t)
}

/// Check whether a Raw type expression is one of the recognised primitive HDL
/// types (possibly wrapped in a direction marker).
fn is_primitive_type(t: &Raw) -> bool {
    let (_, inner) = unwrap_dir_marker(t);
    match inner {
        Raw::Var(v) => v.data == "Bool",
        Raw::App(inner, _, _) => match inner.as_ref() {
            Raw::Var(v) => v.data == "UInt" || v.data == "SInt" || v.data == "Bits",
            _ => false,
        },
        _ => false,
    }
}

/// Build the auto-naming expression for a field inside a factory body:
///   match str_eq(bn.name, "") {
///     case true  => "field"
///     case false => string_concat(string_concat(bn.name, "_"), "field")
///   }
/// `bn` is the factory's implicit BindingName parameter; the compiler fills it
/// with the caller's let-binding name, so `let master = create_AxiLite` names
/// the fields "master_awaddr", … (empty binding name ⇒ no prefix).
fn build_field_name_expr(field_name: &str) -> Raw {
    let bn_name = Raw::Obj(
        Box::new(Raw::Var(empty_span(SmolStr::new("bn")))),
        Some(empty_span(SmolStr::new("name"))),
    );
    let is_empty = Raw::app(
        Raw::app(
            Raw::Var(empty_span(SmolStr::new("str_eq"))),
            bn_name.clone(),
        ),
        Raw::LiteralIntro(empty_span(String::new())),
    );
    let plain = Raw::LiteralIntro(empty_span(field_name.to_string()));
    let prefixed = str_cat(
        str_cat(bn_name, Raw::LiteralIntro(empty_span("_".to_string()))),
        Raw::LiteralIntro(empty_span(field_name.to_string())),
    );
    Raw::Match(
        Box::new(is_empty),
        vec![
            (
                Pattern::Con(empty_span(SmolStr::new("true")), vec![], Either::Icit(Icit::Expl)),
                plain,
            ),
            (
                Pattern::Con(empty_span(SmolStr::new("false")), vec![], Either::Icit(Icit::Expl)),
                prefixed,
            ),
        ],
    )
}

/// Resolve the signal creation function for a primitive type and a port
/// direction: `dir == None` → plain wire, `Some("In")` → input port,
/// `Some("Out")` → output port.
fn create_fn_name(base: &str, dir: Option<&str>) -> &'static str {
    match dir {
        Some("In") => match base {
            "UInt" => "newUIntInput",
            "SInt" => "newSIntInput",
            "Bits" => "newBitsInput",
            _ => "newBoolInput",
        },
        Some("Out") => match base {
            "UInt" => "newUIntOutput",
            "SInt" => "newSIntOutput",
            "Bits" => "newBitsOutput",
            _ => "newBoolOutput",
        },
        Some("InOut") => match base {
            "UInt" => "newUIntInOut",
            "SInt" => "newSIntInOut",
            "Bits" => "newBitsInOut",
            _ => "newBoolInOut",
        },
        _ => match base {
            "UInt" => "newUInt",
            "SInt" => "newSInt",
            "Bits" => "newBits",
            _ => "newBool",
        },
    }
}

/// Build the signal creation expression for a single field.
/// Recognizes: UInt[w], SInt[w], Bits[w], Bool (optionally wrapped in a
/// direction marker). Returns `newUInt(bn-prefixed name, w)`, etc. — for
/// master/slave factories the directed port variants (newUIntInput/…).
fn build_field_create_expr(field_name: &Span<SmolStr>, field_type: &Raw, mode: CreateMode) -> Raw {
    let name_expr = build_field_name_expr(&field_name.data);

    // Port direction of this field from the factory's point of view.
    // Master: declared direction applied (out → output port, in → input
    //   port, inout → inout port); unmarked fields default to output.
    // Slave:  declared direction flipped (out → input port, in → output
    //   port, inout stays inout); unmarked fields default to input.
    let dir = match mode {
        CreateMode::Wire => None,
        CreateMode::Master => match unwrap_dir_marker(field_type).0 {
            Some("in") => Some("In"),
            Some("inout") => Some("InOut"),
            _ => Some("Out"),
        },
        CreateMode::Slave => match unwrap_dir_marker(field_type).0 {
            Some("out") => Some("In"),
            Some("in") => Some("Out"),
            Some("inout") => Some("InOut"),
            _ => Some("In"), // unmarked → received by the slave
        },
    };

    let (_, inner) = unwrap_dir_marker(field_type);
    match inner {
        Raw::App(inner, width, _) => {
            if let Raw::Var(v) = inner.as_ref() {
                let create_fn = create_fn_name(v.data.as_str(), dir);
                Raw::app(Raw::app(Raw::Var(empty_span(SmolStr::new(create_fn))), name_expr), width.as_ref().clone())
            } else {
                Raw::Hole(empty_span(()))
            }
        }
        Raw::Var(v) if v.data == "Bool" => {
            let create_fn = create_fn_name("Bool", dir);
            Raw::app(Raw::Var(empty_span(SmolStr::new(create_fn))), name_expr)
        }
        _ => Raw::Hole(empty_span(())),
    }
}

/// Build the body of a signal factory.
/// For fields [f1: T1, f2: T2, …]:
///   let __f0 = createSignal(bn-named "f1", …);
///   let __f1 = createSignal(bn-named "f2", …);
///   new BundleType(__f0, __f1)
/// `mode` selects wire vs. directed-port creation (master/slave).
fn build_create_body(name: &Span<SmolStr>, fields: &[(Span<SmolStr>, Raw, Icit)], mode: CreateMode) -> Raw {
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
        let create_expr = build_field_create_expr(field_name, field_type, mode);
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
///   impl Bundle for StructName { def :=(that: StructName): Unit = … }
///   impl Into[Self] for Self { … }
///   impl StructName { def asMaster[bn: BindingName]: StructName = …;
///                     def asSlave[bn: BindingName]: StructName = … }
///   def create_StructName$(typeParams)[bn: BindingName]: StructName$(typeParams) = …
/// with sequenced field-by-field assignments, auto-named signal factories
/// (binding name + "_" + field name) and — when fields carry in()/out()
/// direction markers — asMaster/asSlave methods returning directed-port
/// bundles (SpinalHDL style).
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
                inherent: false,
                from_class: false,
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
                inherent: false,
                from_class: false,
            };

            let mut result = vec![bundle_impl, into_impl];

            // ── 3. Standalone wire factory ──
            // Generates:
            //   def create_<TypeName>$(typeParams)[bn: BindingName]: TypeName$(typeParams) = …
            // Only emitted when every field is a recognised primitive HDL type
            // (UInt, SInt, Bits, Bool) so we know how to auto-create signals.
            // The implicit BindingName parameter is filled by the compiler with
            // the caller's let-binding name, which prefixes every signal
            // (SpinalHDL-style auto-naming).
            if fields.iter().all(|(_, ft, _)| is_primitive_type(ft)) {
                let has_dirs = fields.iter().any(|(_, ft, _)| unwrap_dir_marker(ft).0.is_some());

                let factory_params: Vec<(Span<SmolStr>, Raw, Icit)> = params.iter()
                    .map(|(pn, pt, pi)| (pn.clone(), pt.clone(), *pi))
                    .chain(std::iter::once((
                        empty_span(SmolStr::new("bn")),
                        Raw::Var(empty_span(SmolStr::new("BindingName"))),
                        Icit::Impl,
                    )))
                    .collect();

                let mut push_factory = |fname: &str, body: Raw| {
                    result.push(Decl::Def {
                        name: empty_span(SmolStr::new(fname)),
                        params: factory_params.clone(),
                        ret_type: self_ty.clone(),
                        body,
                    });
                };

                push_factory(
                    &format!("create_{}", name.data),
                    build_create_body(name, fields, CreateMode::Wire),
                );

                // ── 4. asMaster / asSlave direction methods (SpinalHDL style) ──
                // When at least one field carries an in()/out() direction marker,
                // generate an inherent impl (empty trait name + inherent: true —
                // the same shape derive_show emits) so the methods resolve through
                // `bundle.asMaster` / `bundle.asSlave` method calls:
                //   impl StructName {
                //     def asMaster[bn: BindingName]: StructName = …
                //     def asSlave[bn: BindingName]: StructName = …
                //   }
                // Each method rebuilds the bundle with directed ports — master:
                // out-marked fields become output ports, in-marked fields input
                // ports; slave: exactly the opposite. `bn` picks up the caller's
                // let-binding name, so `let master = create_AxiLite.asMaster` still
                // names its ports "master_awaddr", …. The plain wires left behind
                // by the inner create_TypeName call are dropped by the Verilog
                // generator (a port declaration takes precedence over a
                // same-named wire; see collectPortNames in hdl-verilog.typort).
                if has_dirs {
                    let bn_param = vec![(
                        empty_span(SmolStr::new("bn")),
                        Raw::Var(empty_span(SmolStr::new("BindingName"))),
                        Icit::Impl,
                    )];
                    let dir_methods: Vec<(Decl, bool)> = [
                        ("asMaster", CreateMode::Master),
                        ("asSlave", CreateMode::Slave),
                    ]
                    .iter()
                    .map(|(mname, mode)| {
                        (
                            Decl::Def {
                                name: empty_span(SmolStr::new(*mname)),
                                params: bn_param.clone(),
                                ret_type: self_ty.clone(),
                                body: build_create_body(name, fields, *mode),
                            },
                            false,
                        )
                    })
                    .collect();
                    result.push(Decl::ImplDecl {
                        name: self_ty.clone(),
                        params: impl_params,
                        trait_name: empty_span(SmolStr::new("")),
                        trait_params: vec![],
                        methods: dir_methods,
                        inherent: true,
                        from_class: false,
                    });
                }
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
                inherent: true,
                from_class: false,
            }]
        }
        _ => vec![],
    }
}
