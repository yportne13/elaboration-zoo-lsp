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

fn string_concat(args: &[Rc<Val>]) -> Option<Rc<Val>> {
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
fn str_eq(args: &[Rc<Val>]) -> Option<Rc<Val>> {
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
fn str_indent2(args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(s) => {
            let indented = s.data.replace('\n', "\n  ");
            Some(Val::LiteralIntro(empty_span(indented)).into())
        },
        _ => None,
    }
}

fn file_read_all_text(args: &[Rc<Val>]) -> Option<Rc<Val>> {
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

fn file_write_all_text(args: &[Rc<Val>]) -> Option<Rc<Val>> {
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

fn file_append_all_text(args: &[Rc<Val>]) -> Option<Rc<Val>> {
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

fn file_exists(args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            let exists = std::path::Path::new(&path.data).exists();
            Some(Val::LiteralIntro(path.clone().map(|_| if exists { "true".to_string() } else { "false".to_string() })).into())
        },
        _ => None,
    }
}

fn file_delete(args: &[Rc<Val>]) -> Option<Rc<Val>> {
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
        // Builtin registration, ported from L13's startup builtins (cxt.rs).
        // The `String`-typed builtins (concat/eq/indent/file head group) are
        // pure ports; str_eq returns the `"true"`/`"false"` STRING literals
        // because L06 has no Boolean type (L13 returns the prelude's
        // Boolean).  The L13 globals/nat/vconn builtins are not ported: they
        // need L13-only infrastructure (a decl table for
        // string_to_global_type, mutable globals on Infer, native Nat).
        cxt = cxt.add_builtin(infer, "string_concat", str_pi(&["x", "y"], Tm::LiteralType), PrimFunc(Rc::new(string_concat)));
        cxt = cxt.add_builtin(infer, "str_eq", str_pi(&["x", "y"], Tm::LiteralType), PrimFunc(Rc::new(str_eq)));
        cxt = cxt.add_builtin(infer, "str_indent2", str_pi(&["x"], Tm::LiteralType), PrimFunc(Rc::new(str_indent2)));
        cxt = cxt.add_builtin(infer, "file_read_all_text", str_pi(&["path"], Tm::LiteralType), PrimFunc(Rc::new(file_read_all_text)));
        cxt = cxt.add_builtin(infer, "file_write_all_text", str_pi(&["path", "content"], Tm::U), PrimFunc(Rc::new(file_write_all_text)));
        cxt = cxt.add_builtin(infer, "file_append_all_text", str_pi(&["path", "content"], Tm::U), PrimFunc(Rc::new(file_append_all_text)));
        cxt = cxt.add_builtin(infer, "file_exists", str_pi(&["path"], Tm::LiteralType), PrimFunc(Rc::new(file_exists)));
        cxt = cxt.add_builtin(infer, "file_delete", str_pi(&["path"], Tm::U), PrimFunc(Rc::new(file_delete)));
        cxt
    }

    /// Register a builtin: name -> native impl (registry on `Infer`, mirroring
    /// the prim slot of L13's `Decl` table) plus a named definition whose
    /// value is the (stuck) head `Val::Prim(name, [])`.  The declared type is
    /// evaluated against the empty env, so it must be closed (all our builtin
    /// types are); L13 evaluates with its decl/env analogously.
    pub fn add_builtin(self, infer: &mut Infer, name: &str, ty: Tm, prim: PrimFunc) -> Self {
        let va = infer.eval(&List::new(), &ty);
        let name_span = empty_span(name.to_owned());
        infer.register_builtin(name, prim);
        self.define(
            name_span.clone(),
            Tm::Prim(name_span.clone()),
            Val::Prim(name_span, List::new()).into(),
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
