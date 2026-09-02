use std::collections::HashMap;

use super::{
    syntax::{Locals, Pruning},
    *,
};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum NameOrigin {
    Inserted,
    Source,
}

type Types = List<(Span<String>, NameOrigin, Val)>;

// === builtin native implementations (ported from L13's cxt.rs) ===
//
// Each receives the applied arguments in natural order; `None` keeps the
// application stuck (`Val::Prim(name, spine)`), e.g. on partial application
// or non-literal arguments.

fn string_concat(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            Some(Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into())
        },
        _ => None,
    }
}

/// String equality.  L13's version returns the prelude's `Boolean`; L06 has
/// no Boolean, so the result is the `"true"`/`"false"` STRING literal (same
/// shape as `file_exists`'s result in L13).
fn str_eq(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            let eq = a.data == b.data;
            let name = if eq { "true" } else { "false" };
            Some(Val::LiteralIntro(empty_span(name.to_owned())).into())
        },
        _ => None,
    }
}

/// Indent each line in a string by 2 spaces (for multi-line strings)
fn str_indent2(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(s) => {
            let indented = s.data.replace('\n', "\n  ");
            Some(Val::LiteralIntro(empty_span(indented)).into())
        },
        _ => None,
    }
}

/// HDL self-check reporting (ported from L13): append one
/// "code|module|signal|message" line to the mutable global "CheckIssues",
/// skipping lines already present (line-level dedup keeps the report
/// idempotent).
fn report_check_issue(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 4 { return None; }
    let get = |i: usize| match args[i].as_ref() {
        Val::LiteralIntro(s) => s.data.to_string(),
        _ => String::new(),
    };
    let (code, module, signal, message) = (get(0), get(1), get(2), get(3));
    if code.is_empty() || module.is_empty() { return Some(Val::U.into()); }
    let line = format!("{}|{}|{}|{}", code, module, signal, message);
    let mut map = infer.mutable_map.borrow_mut();
    let existing = match map.get("CheckIssues") {
        Some(v) => match v.as_ref() {
            Val::LiteralIntro(s) => s.data.clone(),
            _ => String::new(),
        },
        None => String::new(),
    };
    if !existing.split('\n').any(|l| l == line) {
        let next = if existing.is_empty() { line } else { format!("{}\n{}", existing, line) };
        map.insert("CheckIssues".to_string(), Rc::new(Val::LiteralIntro(empty_span(next))));
    }
    Some(Val::U.into())
}

/// Look a name up in the decl table and return its VALUE as a "dynamic type"
/// (types are values here): `string_to_global_type "String"` reduces to the
/// String type, `"Nat"` to the Nat type, ...  A missing name stays a stuck
/// `Val::Decl`, which a `get_global`/`create_global` call then constrains
/// (e.g. against `String`) via the loose LiteralType arm in unify.  Ported
/// from L13 (there it evals `Tm::Decl(name)` through the decl table).
fn string_to_global_type(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => Some(
            infer.decls.get(&a.data)
                .map(|e| e.vt.clone())
                .unwrap_or_else(|| Val::Decl(empty_span(a.data.clone()), List::new()).into())
        ),
        _ => None,
    }
}

fn create_global(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            infer.mutable_map.borrow_mut().insert(a.data.clone(), args[1].clone());
            Some(Val::U.into())
        },
        _ => None,
    }
}

fn change_mutable(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Some(x) = infer.mutable_map.borrow_mut().get_mut(&a.data) {
                *x = infer.v_app(args[1].clone(), x.clone(), Icit::Expl)
            };
            Some(Val::U.into())
        },
        _ => None,
    }
}

fn get_global(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => Some(infer.mutable_map.borrow().get(&a.data).unwrap().clone()),
        _ => None,
    }
}

/// Pure read of a mutable global with a fallback default — never WRITES the
/// map, so calling it during declaration-time check evaluation cannot
/// pollute design-level globals.  Missing key -> `args[1]` (the default).
fn get_global_default(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            Some(infer.mutable_map.borrow().get(&a.data).cloned().unwrap_or_else(|| args[1].clone()))
        },
        _ => None,
    }
}

fn change_mutable_default(infer: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 3 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            let mut map = infer.mutable_map.borrow_mut();
            if let Some(x) = map.get_mut(&a.data) {
                *x = infer.v_app(args[1].clone(), x.clone(), Icit::Expl)
            } else {
                map.insert(a.data.clone(), args[2].clone());
            };
            Some(Val::U.into())
        },
        _ => None,
    }
}

fn file_read_all_text(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            let content = std::fs::read_to_string(&path.data)
                .unwrap_or_else(|e| panic!("file_read_all_text: failed to read '{}': {}", path.data, e));
            Some(Val::LiteralIntro(path.clone().map(|_| content.clone())).into())
        },
        _ => None,
    }
}

fn file_write_all_text(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(path), Val::LiteralIntro(content)) => {
            std::fs::write(&path.data, &content.data)
                .unwrap_or_else(|e| panic!("file_write_all_text: failed to write '{}': {}", path.data, e));
            Some(Val::U.into())
        },
        _ => None,
    }
}

fn file_append_all_text(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(path), Val::LiteralIntro(content)) => {
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .append(true)
                .create(true)
                .open(&path.data)
                .unwrap_or_else(|e| panic!("file_append_all_text: failed to open '{}': {}", path.data, e));
            write!(file, "{}", content.data)
                .unwrap_or_else(|e| panic!("file_append_all_text: failed to append to '{}': {}", path.data, e));
            Some(Val::U.into())
        },
        _ => None,
    }
}

fn file_exists(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            let exists = std::path::Path::new(&path.data).exists();
            Some(Val::LiteralIntro(path.clone().map(|_| if exists { "true".to_string() } else { "false".to_string() })).into())
        },
        _ => None,
    }
}

fn file_delete(_: &Infer, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            std::fs::remove_file(&path.data)
                .unwrap_or_else(|e| panic!("file_delete: failed to delete '{}': {}", path.data, e));
            Some(Val::U.into())
        },
        _ => None,
    }
}

/// `(String ->)^n ret` — every L06 builtin argument type is `String`.
fn str_pi(params: &[&str], ret: Tm) -> Tm {
    params.iter().rev().fold(ret, |acc, name| {
        Tm::Pi(empty_span((*name).to_owned()), Icit::Expl, Box::new(Tm::LiteralType), Box::new(acc))
    })
}

/// `(name : dom) -> cod` — local Pi builder for builtin signatures.
fn tm_pi(name: &str, dom: Tm, cod: Tm) -> Tm {
    Tm::Pi(empty_span(name.to_owned()), Icit::Expl, Box::new(dom), Box::new(cod))
}

/// `string_to_global_type Var(ix)` — the de Bruijn ref resolves at eval time
/// to the corresponding preceding parameter (L13 builds these with
/// tm_app/tm_decl; the domains evaluate under the env at their position).
fn st2g_app(ix: u32) -> Tm {
    Tm::App(
        Box::new(Tm::Decl(empty_span("string_to_global_type".to_owned()))),
        Box::new(Tm::Var(Ix(ix))),
        Icit::Expl,
    )
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    pub src_names: HashMap<String, (Lvl, Rc<VTy>)>,
}

impl Cxt {
    pub fn new(infer: &mut Infer) -> Self {
        let mut cxt = Self::empty().define(
            empty_span("String".to_owned()),
            Tm::LiteralType,
            Val::LiteralType.into(),
            Tm::U,
            Val::U.into(),
        );
        // Builtin registration, ported from L13's startup builtins (cxt.rs):
        // the whole string / file / global group.  str_eq returns the
        // `"true"`/`"false"` STRING literals because L06 has no Boolean type
        // (L13 returns the prelude's Boolean).  The nat/vconn builtins are
        // not ported: they need L13-only infra (native Nat / prelude types).
        infer.decls.insert("String".to_owned(), DeclEntry {
            vt: Val::LiteralType.into(),
            va: Val::U.into(),
            prim: None,
        });
        cxt = cxt.add_builtin(infer, "string_concat", str_pi(&["x", "y"], Tm::LiteralType), PrimFunc(Rc::new(string_concat)));
        cxt = cxt.add_builtin(infer, "str_eq", str_pi(&["x", "y"], Tm::LiteralType), PrimFunc(Rc::new(str_eq)));
        cxt = cxt.add_builtin(infer, "str_indent2", str_pi(&["x"], Tm::LiteralType), PrimFunc(Rc::new(str_indent2)));
        cxt = cxt.add_builtin(infer, "report_check_issue",
            str_pi(&["code", "module", "signal", "message"], Tm::U),
            PrimFunc(Rc::new(report_check_issue)));
        cxt = cxt.add_builtin(infer, "string_to_global_type",
            str_pi(&["x"], Tm::U),
            PrimFunc(Rc::new(string_to_global_type)));
        cxt = cxt.add_builtin(infer, "create_global",
            tm_pi("x", Tm::LiteralType, tm_pi("y", st2g_app(0), Tm::U)),
            PrimFunc(Rc::new(create_global)));
        cxt = cxt.add_builtin(infer, "change_mutable",
            tm_pi("x", Tm::LiteralType,
                tm_pi("f", tm_pi("_", st2g_app(0), st2g_app(1)), Tm::U)),
            PrimFunc(Rc::new(change_mutable)));
        cxt = cxt.add_builtin(infer, "get_global",
            tm_pi("x", Tm::LiteralType, st2g_app(0)),
            PrimFunc(Rc::new(get_global)));
        cxt = cxt.add_builtin(infer, "get_global_default",
            tm_pi("x", Tm::LiteralType, tm_pi("z", st2g_app(0), st2g_app(1))),
            PrimFunc(Rc::new(get_global_default)));
        cxt = cxt.add_builtin(infer, "change_mutable_default",
            tm_pi("x", Tm::LiteralType,
                tm_pi("f", tm_pi("_", st2g_app(0), st2g_app(1)), tm_pi("z", st2g_app(1), Tm::U))),
            PrimFunc(Rc::new(change_mutable_default)));
        cxt = cxt.add_builtin(infer, "file_read_all_text", str_pi(&["path"], Tm::LiteralType), PrimFunc(Rc::new(file_read_all_text)));
        cxt = cxt.add_builtin(infer, "file_write_all_text", str_pi(&["path", "content"], Tm::U), PrimFunc(Rc::new(file_write_all_text)));
        cxt = cxt.add_builtin(infer, "file_append_all_text", str_pi(&["path", "content"], Tm::U), PrimFunc(Rc::new(file_append_all_text)));
        cxt = cxt.add_builtin(infer, "file_exists", str_pi(&["path"], Tm::LiteralType), PrimFunc(Rc::new(file_exists)));
        cxt = cxt.add_builtin(infer, "file_delete", str_pi(&["path"], Tm::U), PrimFunc(Rc::new(file_delete)));
        cxt
    }

    /// Register a builtin in the decl table: value = stuck head
    /// `Val::Decl(name, [])` (the prim fires on application), type = `ty`
    /// evaluated against the empty env (all our builtin types are closed),
    /// plus a positional definition so the name is usable in code — L13's
    /// `add_builtin` analog (there the table lives on `Cxt.decl`, here on
    /// `Infer.decls`).
    pub fn add_builtin(self, infer: &mut Infer, name: &str, ty: Tm, prim: PrimFunc) -> Self {
        let va = infer.eval(&List::new(), &ty);
        let name_span = empty_span(name.to_owned());
        infer.register_builtin(
            name,
            Val::Decl(name_span.clone(), List::new()).into(),
            va.clone(),
            prim,
        );
        self.define(
            name_span.clone(),
            Tm::Decl(name_span.clone()),
            Val::Decl(name_span, List::new()).into(),
            ty,
            va,
        )
    }
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: HashMap::new(),
        }
    }

    pub fn names(&self) -> List<String> {
        fn go(locals: &Locals) -> List<String> {
            match locals {
                Locals::Here => List::new(),
                Locals::Define(locals, name, _, _) => go(locals).prepend(name.data.clone()),
                Locals::Bind(locals, name, _) => go(locals).prepend(name.data.clone()),
            }
        }
        go(&self.locals)
    }

    pub fn bind(&self, x: Span<String>, a_quote: Tm, a: Rc<Val>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, a));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
        }
    }

    pub fn new_binder(&self, x: Span<String>, a_quote: Tm) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
        }
    }

    pub fn define(&self, x: Span<String>, t: Tm, vt: Rc<Val>, a: Ty, va: Rc<VTy>) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, va));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Box::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
        }
    }
}
