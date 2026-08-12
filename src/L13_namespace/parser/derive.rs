use std::collections::HashMap;

use smol_str::SmolStr;

use super::syntax::{Decl, Either, Icit, Pattern, Raw};
use crate::parser_lib::{Span, ToSpan};
use super::empty_span;

pub type DeriveMacro = fn(&Decl, &BundleSet) -> Vec<Decl>;
pub type DeriveRegistry = HashMap<String, DeriveMacro>;

/// The set of struct names in the current file that carry `#[derive(Bundle)]`.
/// Used by derive_bundle to recognise nested-bundle fields (a field whose
/// type is another Bundle struct declared in the same file), so
/// TypeName.create can recursively create them.
pub type BundleSet = std::collections::HashSet<SmolStr>;

pub fn default_derive_registry() -> DeriveRegistry {
    let mut registry: DeriveRegistry = HashMap::new();
    registry.insert("Show".to_string(), derive_show);
    registry.insert("Bundle".to_string(), derive_bundle);
    registry
}

/// Expand derive macros: for each trait in `traits`, generate the corresponding
/// impl blocks and return them alongside the original declaration.
/// `bundle_types` names the file's `#[derive(Bundle)]` structs (used by
/// derive_bundle to create nested-bundle fields recursively).
pub fn expand_derive(
    registry: &DeriveRegistry,
    traits: &[Span<SmolStr>],
    decl: &Decl,
    bundle_types: &BundleSet,
) -> Vec<Decl> {
    let mut result = vec![];
    for trait_name in traits {
        if let Some(derive_fn) = registry.get(trait_name.data.as_str()) {
            result.extend(derive_fn(decl, bundle_types));
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

/// Build a bundle bulk-assignment body between `lhs` and `rhs` (normally
/// `this` and `that`): sequences field assignments as nested let-bindings
/// ending with `tail` (normally `unit`).
/// For struct fields [f1: T1, f2: T2, ...], generates:
///   let __b0 = this.f1 := that.f1;
///   let __b1 = this.f2 := that.f2;
///   unit
/// For primitive fields, the assignment is guarded by an isInputPort check on
/// the LHS so that driving an input port (illegal Verilog) is skipped — this
/// lets a master/slave pair be connected in both directions. The `let` names
/// are prefixed so two chains can be nested without shadowing (the `<>` body
/// is the forward chain with the backward chain as its tail).
fn build_bundle_body_ex(
    fields: &[(Span<SmolStr>, Raw, Icit)],
    lhs: &str,
    rhs: &str,
    let_prefix: &str,
    tail: Raw,
) -> Raw {
    if fields.is_empty() {
        return tail;
    }

    let mut result = tail;

    for (i, (field_name, field_type, _)) in fields.iter().enumerate().rev() {
        let assign = Raw::App(
            Box::new(Raw::Obj(
                Box::new(Raw::Obj(
                    Box::new(Raw::Var(empty_span(SmolStr::new(lhs)))),
                    Some(field_name.clone()),
                )),
                Some(empty_span(SmolStr::new(":="))),
            )),
            Box::new(Raw::Obj(
                Box::new(Raw::Var(empty_span(SmolStr::new(rhs)))),
                Some(field_name.clone()),
            )),
            Either::Icit(Icit::Expl),
        );

        // Guard primitive fields with `match isInputPort(<lhs>.<f>.zz_expr)`.
        let step = if is_primitive_type(field_type) {
            let lhs_expr = Raw::Obj(
                Box::new(Raw::Obj(
                    Box::new(Raw::Var(empty_span(SmolStr::new(lhs)))),
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
            empty_span(SmolStr::new(format!("__{}{}", let_prefix, i))),
            Box::new(Raw::Hole(empty_span(()))),
            Box::new(step),
            Box::new(result),
        );
    }

    result
}

/// The one-way `:=` bulk-assignment body (this := that).
fn build_bundle_body(fields: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    build_bundle_body_ex(
        fields,
        "this",
        "that",
        "b",
        Raw::Var(empty_span(SmolStr::new("unit"))),
    )
}

/// The `<>` bidirectional body: drive both sides, each through its own
/// one-way bulk assignment (which skips input-port LHS):
///   let __b0 = this.f1 := that.f1; ...;
///   let __c0 = that.f1 := this.f1; ...;
///   unit
fn build_connect_body(fields: &[(Span<SmolStr>, Raw, Icit)]) -> Raw {
    build_bundle_body_ex(
        fields,
        "this",
        "that",
        "b",
        build_bundle_body_ex(
            fields,
            "that",
            "this",
            "c",
            Raw::Var(empty_span(SmolStr::new("unit"))),
        ),
    )
}

/// Direction mode of a generated signal factory.
#[derive(Clone, Copy, PartialEq)]
enum CreateMode {
    /// Plain wires (TypeName.create) — directions are ignored.
    Wire,
    /// Master-perspective directed ports (the asMaster method body).
    Master,
    /// Slave-perspective directed ports (the asSlave method body).
    Slave,
}

/// Direction of a bundle field, as consumed by `create_fn_name`:
/// `"In"`, `"Out"` or `"InOut"`. The spec is already in the perspective of
/// the method being generated (master spec for asMaster, slave spec for
/// asSlave); `derive_imasterslave` flips the master spec when no explicit
/// asSlave is given.
type DirSpec = Vec<(SmolStr, &'static str)>;

/// Flip a master-perspective direction to the slave perspective
/// (In ↔ Out; InOut stays InOut).
fn flip_dir(dir: &str) -> &'static str {
    match dir {
        "In" => "Out",
        "Out" => "In",
        _ => "InOut",
    }
}

/// Check whether a Raw type expression is one of the recognised primitive HDL
/// types (Bool, or UInt/SInt/Bits applied to a width).
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

/// Build the auto-naming expression for a field inside a factory body:
///   match str_eq(bn.name, "") {
///     case true  => "field"
///     case false => string_concat(string_concat(bn.name, "_"), "field")
///   }
/// `bn` is the factory's implicit BindingName parameter; the compiler fills it
/// with the caller's let-binding name, so `let master = AxiLite.create` names
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
/// The `Named` variants take an explicit name string — the derive builds
/// field names from the factory's BindingName (`bn.name + "_" + field`),
/// which is NOT the name of the enclosing `let __f0 = ...` binding, so the
/// bn-based new* family cannot be used here.
fn create_fn_name(base: &str, dir: Option<&str>) -> &'static str {
    match dir {
        Some("In") => match base {
            "UInt" => "newUIntInputNamed",
            "SInt" => "newSIntInputNamed",
            "Bits" => "newBitsInputNamed",
            _ => "newBoolInputNamed",
        },
        Some("Out") => match base {
            "UInt" => "newUIntOutputNamed",
            "SInt" => "newSIntOutputNamed",
            "Bits" => "newBitsOutputNamed",
            _ => "newBoolOutputNamed",
        },
        Some("InOut") => match base {
            "UInt" => "newUIntInOutNamed",
            "SInt" => "newSIntInOutNamed",
            "Bits" => "newBitsInOutNamed",
            _ => "newBoolInOutNamed",
        },
        _ => match base {
            "UInt" => "newUIntNamed",
            "SInt" => "newSIntNamed",
            "Bits" => "newBitsNamed",
            _ => "newBoolNamed",
        },
    }
}

/// Is this field's type a nested bundle struct of the same file (one of
/// `bundle_types`)? e.g. `inner: InnerBus` or `inner: InnerBus[w]`.
/// Returns the head type name and its type arguments (in order, with their
/// implicit/explicit icit) when it is one.
fn bundle_field_type<'a>(t: &'a Raw, bundle_types: &BundleSet) -> Option<(&'a str, Vec<(Raw, Either)>)> {
    fn collect<'a>(t: &'a Raw, head: &mut Option<&'a str>, args: &mut Vec<(Raw, Either)>) {
        match t {
            Raw::App(f, arg, either) => {
                collect(f, head, args);
                args.push((arg.as_ref().clone(), either.clone()));
            }
            Raw::Var(v) => *head = Some(v.data.as_str()),
            _ => {}
        }
    }
    let mut head = None;
    let mut args = vec![];
    collect(t, &mut head, &mut args);
    let head = head?;
    if !bundle_types.contains(head) {
        return None;
    }
    Some((head, args))
}

/// Build the signal creation expression for a single field.
/// Recognizes: UInt[w], SInt[w], Bits[w], Bool, and nested bundle fields
/// (a type named in `bundle_types`). Returns `newUIntNamed(bn-prefixed name,
/// w)`, etc. — for master/slave factories the directed port variants
/// (newUIntInputNamed/…), with the field's direction taken from `dir_spec`
/// (already in the factory's own perspective). A nested bundle field becomes
/// a recursive factory call `<TypeName>.create[<type args>][bn]` — `bn` is
/// passed explicitly so the caller's binding name keeps prefixing the inner
/// signals (`let outer = OuterBus.create` → "outer_value", …).
fn build_field_create_expr(
    field_name: &Span<SmolStr>,
    field_type: &Raw,
    mode: CreateMode,
    dir_spec: &DirSpec,
    bundle_types: &BundleSet,
) -> Raw {
    // Nested bundle field: recurse through the child's own factory
    // (`<ChildType>.create`), with an optional direction method —
    // `out(this.aw)` → <T>.create[...].asMaster, `in(this.aw)` →
    // <T>.create[...].asSlave (the direction spec is already in this
    // factory's own perspective). Both `bn`s are passed explicitly — the
    // child factory's own implicit BindingName and the direction method's —
    // because this expression elaborates at this def's definition site,
    // where the caller's binding name is not available.
    if let Some((head, args)) = bundle_field_type(field_type, bundle_types) {
        let create_fn = Raw::Obj(
            Box::new(Raw::Var(empty_span(SmolStr::new(head)))),
            Some(empty_span(SmolStr::new("create"))),
        );
        let mut app = create_fn;
        for (arg, either) in args {
            app = Raw::App(Box::new(app), Box::new(arg), either);
        }
        // Explicitly pass the child factory's implicit `bn: BindingName` so
        // the caller's binding name keeps prefixing the inner signals.
        app = Raw::App(
            Box::new(app),
            Box::new(Raw::Var(empty_span(SmolStr::new("bn")))),
            Either::Icit(Icit::Impl),
        );
        if mode != CreateMode::Wire {
            // dir "Out" → the child is built as a master (its own asMaster),
            // dir "In" → as a slave (its own asSlave).
            let dir = dir_spec
                .iter()
                .find(|(n, _)| n == &field_name.data)
                .map(|(_, d)| *d);
            let method = match dir {
                Some("In") => "asSlave",
                _ => "asMaster", // "Out", or unreachable dirs (validation rejects "InOut")
            };
            app = Raw::Obj(Box::new(app), Some(empty_span(SmolStr::new(method))));
            // ... and the direction method's own implicit `[bn]`.
            app = Raw::App(
                Box::new(app),
                Box::new(Raw::Var(empty_span(SmolStr::new("bn")))),
                Either::Icit(Icit::Impl),
            );
        }
        return app;
    }

    let name_expr = build_field_name_expr(&field_name.data);

    // Port direction of this field from the factory's point of view.
    // Wire: plain wires. Master/Slave: looked up in the direction spec
    // (master spec for asMaster, slave spec for asSlave).
    let dir = match mode {
        CreateMode::Wire => None,
        CreateMode::Master | CreateMode::Slave => dir_spec
            .iter()
            .find(|(n, _)| n == &field_name.data)
            .map(|(_, d)| *d),
    };

    match field_type {
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
/// `mode` selects wire vs. directed-port creation (master/slave); `dir_spec`
/// supplies the per-field port directions for the directed modes; nested
/// bundle fields recurse through their own <ChildType>.create factories
/// (`bundle_types`).
fn build_create_body(
    name: &Span<SmolStr>,
    fields: &[(Span<SmolStr>, Raw, Icit)],
    mode: CreateMode,
    dir_spec: &DirSpec,
    bundle_types: &BundleSet,
) -> Raw {
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
        let create_expr = build_field_create_expr(field_name, field_type, mode, dir_spec, bundle_types);
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
///   def StructName.create$(typeParams)[bn: BindingName]: StructName$(typeParams) = …
/// with sequenced field-by-field assignments and auto-named signal factories
/// (binding name + "_" + field name). Nested bundle fields (types named in
/// `bundle_types`) are created recursively through their own factories.
/// Directionality is NOT derived here: a separate `impl IMasterSlave for
/// StructName` (see derive_imasterslave) supplies the asMaster/asSlave
/// directed-port methods.
fn derive_bundle(decl: &Decl, bundle_types: &BundleSet) -> Vec<Decl> {
    match decl {
        Decl::Enum { name, params, cases, .. } if cases.len() == 1 => {
            let self_ty = build_self_ty(name, params);
            let fields = &cases[0].1;

            let impl_params: Vec<_> = params.iter()
                .filter(|(_, _, icit)| *icit == Icit::Impl)
                .cloned()
                .collect();

            // ── 1. Bundle trait impl (:= bulk assignment + <> connect) ──
            // `<>` is generated alongside `:=` with the same body rather than
            // relying on the trait's default method: the default's `:=` method
            // dispatch leaves the solver with an unsolved meta for parametric
            // bundles (`MyBus[w]` with `w` bound), while a generated method
            // elaborates through the normal path (like a user's `a := b`).
            let bundle_body = build_bundle_body(fields);
            let that_param = (
                empty_span(SmolStr::new("that")),
                self_ty.clone(),
                Icit::Expl,
            );
            let bundle_method = |name: &str, body: Raw| (Decl::Def {
                name: empty_span(SmolStr::new(name)),
                params: vec![that_param.clone()],
                ret_type: Raw::Var(empty_span(SmolStr::new("Unit"))),
                body,
            }, false);
            let bundle_impl = Decl::ImplDecl {
                name: self_ty.clone(),
                params: impl_params.clone(),
                trait_name: empty_span(SmolStr::new("Bundle")),
                trait_params: vec![],
                methods: vec![
                    bundle_method(":=", build_bundle_body(fields)),
                    bundle_method("<>", build_connect_body(fields)),
                ],
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

            // ── 3. Wire factory ──
            // Generates (same shape as a module's `Name.create`):
            //   def TypeName.create$(typeParams)[bn: BindingName]: TypeName$(typeParams) = …
            // Emitted when every field is either a recognised primitive HDL
            // type (UInt, SInt, Bits, Bool) or a nested bundle struct of this
            // file (so we know how to auto-create the signals). The implicit
            // BindingName parameter is filled by the compiler with the
            // caller's let-binding name, which prefixes every signal
            // (SpinalHDL-style auto-naming).
            let can_factory = fields.iter().all(|(_, ft, _)| {
                is_primitive_type(ft) || bundle_field_type(ft, bundle_types).is_some()
            });
            if can_factory {
                let factory_params: Vec<(Span<SmolStr>, Raw, Icit)> = params.iter()
                    .map(|(pn, pt, pi)| (pn.clone(), pt.clone(), *pi))
                    .chain(std::iter::once((
                        empty_span(SmolStr::new("bn")),
                        Raw::Var(empty_span(SmolStr::new("BindingName"))),
                        Icit::Impl,
                    )))
                    .collect();

                result.push(Decl::Def {
                    name: empty_span(SmolStr::new(format!("{}.create", name.data))),
                    params: factory_params,
                    ret_type: self_ty,
                    body: build_create_body(name, fields, CreateMode::Wire, &Vec::new(), bundle_types),
                });
            }

            result
        }
        _ => vec![],
    }
}

/// Parse an asMaster/asSlave direction spec body — a nested-let chain
///   let _ = out(this.awaddr);
///   let _ = in(this.awready);
///   …
///   <terminator ignored>
/// where each step's value is a direction function (`in`/`out`/`inout` from
/// hdl-bus.typort) applied to a field projection `this.<field>`. The body is
/// read syntactically before elaboration (the functions are identities and
/// can never change a value), so the trailing expression may be anything.
fn parse_dir_spec(body: &Raw) -> Result<DirSpec, String> {
    let mut spec: DirSpec = Vec::new();
    let mut cur = body;
    loop {
        match cur {
            Raw::Let(_, _, val, rest) => {
                let entry = match val.as_ref() {
                    Raw::App(f, arg, Either::Icit(Icit::Expl)) => {
                        let dir = match f.as_ref() {
                            Raw::Var(v) => match v.data.as_str() {
                                "in" => Some("In"),
                                "out" => Some("Out"),
                                "inout" => Some("InOut"),
                                _ => None,
                            },
                            _ => None,
                        };
                        dir.and_then(|dir| match arg.as_ref() {
                            Raw::Obj(receiver, Some(fname)) => match receiver.as_ref() {
                                Raw::Var(v) if v.data == "this" => Some((fname.data.clone(), dir)),
                                _ => None,
                            },
                            _ => None,
                        })
                    }
                    _ => None,
                };
                match entry {
                    Some(entry) => {
                        spec.push(entry);
                        cur = rest;
                    }
                    None => {
                        return Err(format!(
                            "bad direction statement `{}` in impl IMasterSlave: expected `let _ = in(this.<field>)` / `out(this.<field>)` / `inout(this.<field>)`",
                            val
                        ));
                    }
                }
            }
            _ => break,
        }
    }
    Ok(spec)
}

/// Validate a parsed direction spec against the struct's fields: reject
/// duplicates, unknown field names, and struct fields missing from the spec.
fn validate_dir_spec(
    spec: &DirSpec,
    struct_name: &Span<SmolStr>,
    fields: &[(Span<SmolStr>, Raw, Icit)],
) -> Result<(), String> {
    for (i, (fname, _)) in spec.iter().enumerate() {
        if spec.iter().skip(i + 1).any(|(n, _)| n == fname) {
            return Err(format!(
                "field `{}` has a duplicate direction in impl IMasterSlave for `{}`",
                fname, struct_name.data
            ));
        }
        if !fields.iter().any(|(f, _, _)| &f.data == fname) {
            return Err(format!(
                "field `{}` in impl IMasterSlave for `{}` is not a field of the struct",
                fname, struct_name.data
            ));
        }
    }
    let missing: Vec<&SmolStr> = fields.iter()
        .filter(|(f, _, _)| !spec.iter().any(|(n, _)| n == &f.data))
        .map(|(f, _, _)| &f.data)
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "fields [{}] of `{}` have no direction in impl IMasterSlave: every field must be declared in `asMaster` (`let _ = in(this.<field>)` / `out(...)` / `inout(...)`)",
            missing.iter().map(|n| n.as_str()).collect::<Vec<_>>().join(", "),
            struct_name.data
        ));
    }
    Ok(())
}

/// Derive the asMaster/asSlave methods of an `impl IMasterSlave for TypeName`
/// block (TypeName a `#[derive(Bundle)]` struct). The user writes only the
/// direction specs (see parse_dir_spec); this generates both methods:
///   def asMaster[bn: BindingName]: TypeName = …  // directions as declared
///   def asSlave[bn: BindingName]: TypeName = …   // directions flipped
/// An explicit user-written asSlave spec is used as-is (slave perspective);
/// otherwise asSlave flips the asMaster spec (In ↔ Out, InOut stays InOut).
/// The generated methods rebuild the bundle with directed ports; `bn` picks
/// up the caller's let-binding name, so `let master = AxiLite.create.asMaster`
/// names its ports "master_awaddr", …. Nested bundle fields (types named in
/// `bundle_types`) are directed through their own factories:
/// `out(this.aw)` → `<T>.create[...].asMaster[bn]`, `in(this.aw)` →
/// `<T>.create[...].asSlave[bn]`. The plain wires left behind by the inner
/// TypeName.create call are dropped by the Verilog generator (a port
/// declaration takes precedence over a same-named wire; see collectPortNames
/// in hdl-verilog.typort).
///
/// Returns a user-facing error message when the spec is malformed: unknown
/// method names, fields not declared in the struct, duplicate or missing
/// directions, `inout` on a nested bundle field, or field types that are
/// neither primitive HDL types nor Bundle structs of this file.
pub fn derive_imasterslave(
    struct_name: &Span<SmolStr>,
    struct_params: &[(Span<SmolStr>, Raw, Icit)],
    fields: &[(Span<SmolStr>, Raw, Icit)],
    impl_params: &[(Span<SmolStr>, Raw, Icit)],
    methods: &[(Decl, bool)],
    bundle_types: &BundleSet,
    imasterslave_types: &BundleSet,
) -> Result<Vec<(Decl, bool)>, String> {
    // Only asMaster / asSlave spec methods are recognised.
    let mut master_spec: Option<DirSpec> = None;
    let mut slave_spec: Option<DirSpec> = None;
    for (decl, _) in methods {
        if let Decl::Def { name, body, .. } = decl {
            match name.data.as_str() {
                "asMaster" => master_spec = Some(parse_dir_spec(body)?),
                "asSlave" => slave_spec = Some(parse_dir_spec(body)?),
                other => {
                    return Err(format!(
                        "unsupported method `{}` in impl IMasterSlave for `{}`: only `asMaster` (and optionally `asSlave`) are allowed",
                        other, struct_name.data
                    ));
                }
            }
        } else {
            return Err(format!(
                "unsupported item in impl IMasterSlave for `{}`: only `asMaster` / `asSlave` defs are allowed",
                struct_name.data
            ));
        }
    }
    let master_spec = master_spec.ok_or_else(|| {
        format!(
            "impl IMasterSlave for `{}` must define `asMaster` — a `let _ = in(this.<field>)` / `out(...)` / `inout(...)` direction spec",
            struct_name.data
        )
    })?;
    validate_dir_spec(&master_spec, struct_name, fields)?;

    // Every field must be either a recognised primitive or a nested bundle
    // struct of this file; the directed-port factories handle each kind
    // accordingly (primitive → directed port constructors, nested bundle →
    // recursive <T>.create[...].asMaster/asSlave).
    for (fname, fty, _) in fields {
        if is_primitive_type(fty) {
            continue;
        }
        if let Some((head, _)) = bundle_field_type(fty, bundle_types) {
            // A nested bundle takes only out/in (the whole child is directed
            // through its own asMaster/asSlave); inout has no meaning for a
            // bundle field.
            let dir = master_spec.iter().find(|(n, _)| n == &fname.data).map(|(_, d)| *d);
            if dir == Some("InOut") {
                return Err(format!(
                    "field `{}` of `{}`: `inout` direction is only valid for primitive fields (nested bundles use `out` / `in` to direct the whole child)",
                    fname.data, struct_name.data
                ));
            }
            // The generated code calls the child's own asMaster/asSlave, so
            // the child must implement IMasterSlave itself (like SpinalHDL's
            // Axi4AW extends Bundle with IMasterSlave).
            if !imasterslave_types.contains(head) {
                return Err(format!(
                    "field `{}` of `{}`: nested bundle `{}` must itself implement IMasterSlave (its `asMaster` / `asSlave` direct the child's fields)",
                    fname.data, struct_name.data, head
                ));
            }
            continue;
        }
        return Err(format!(
            "field `{}` of `{}` has type `{}` which is neither a primitive HDL type (UInt/SInt/Bits/Bool) nor a #[derive(Bundle)] struct of this file",
            fname.data, struct_name.data, fty
        ));
    }

    // A parametric bundle's impl must bind the struct's implicit params
    // (`impl[w: Nat] IMasterSlave for MyBus[w]`), since the generated method
    // bodies reference them (e.g. the width `w` of `UInt[w]`).
    let struct_impl_params: Vec<SmolStr> = struct_params.iter()
        .filter(|(_, _, icit)| *icit == Icit::Impl)
        .map(|(n, _, _)| n.data.clone())
        .collect();
    for pname in &struct_impl_params {
        if !impl_params.iter().any(|(n, _, _)| &n.data == pname) {
            return Err(format!(
                "impl IMasterSlave for the parametric bundle `{}` must bind its parameters: `impl[{}] IMasterSlave for {}({})`",
                struct_name.data,
                pname,
                struct_name.data,
                struct_impl_params.join(", "),
            ));
        }
    }

    // asSlave: an explicit spec is used as-is; otherwise flip the master spec.
    let slave_spec = match slave_spec {
        Some(spec) => {
            validate_dir_spec(&spec, struct_name, fields)?;
            spec
        }
        None => master_spec.iter().map(|(n, d)| (n.clone(), flip_dir(d))).collect(),
    };

    let self_ty = build_self_ty(struct_name, struct_params);
    let bn_param = vec![(
        empty_span(SmolStr::new("bn")),
        Raw::Var(empty_span(SmolStr::new("BindingName"))),
        Icit::Impl,
    )];
    let mk = |mname: &str, spec: DirSpec, mode: CreateMode| -> (Decl, bool) {
        (
            Decl::Def {
                name: empty_span(SmolStr::new(mname)),
                params: bn_param.clone(),
                ret_type: self_ty.clone(),
                body: build_create_body(struct_name, fields, mode, &spec, bundle_types),
            },
            false,
        )
    };

    Ok(vec![
        mk("asMaster", master_spec, CreateMode::Master),
        mk("asSlave", slave_spec, CreateMode::Slave),
    ])
}

/// Derive Show: generates a proper `impl Show for Type { def show = ... }` block.
fn derive_show(decl: &Decl, _bundle_types: &BundleSet) -> Vec<Decl> {
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
