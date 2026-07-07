use crate::bimap::BiMap;
use crate::parser_lib::ToSpan;

use super::{
    syntax::{Locals, Pruning},
    *,
};

fn count_nat(val: &Rc<Val>) -> u64 {
    try_count_nat(val).unwrap_or(0)
}

pub(super) fn try_count_nat(val: &Rc<Val>) -> Option<u64> {
    let mut count = 0u64;
    let mut current = val.clone();
    loop {
        match current.as_ref() {
            Val::SumCase { case_name, datas, .. } if case_name.data == "zero" => {
                return Some(count);
            }
            Val::SumCase { case_name, datas, .. } if case_name.data == "succ" => {
                let (_, prev, _) = datas.first()?;
                count = count.checked_add(1)?;
                current = prev.clone();
            }
            _ => return None,
        }
    }
}

pub(super) fn build_nat(count: u64, nat_type: &Rc<Val>) -> Rc<Val> {
    let mut result = Rc::new(Val::SumCase {
        is_trait: false,
        typ: nat_type.clone(),
        case_name: empty_span(SmolStr::new("zero")),
        datas: Rc::new(vec![]),
    });
    for _ in 0..count {
        result = Rc::new(Val::SumCase {
            is_trait: false,
            typ: nat_type.clone(),
            case_name: empty_span(SmolStr::new("succ")),
            datas: Rc::new(vec![(
                empty_span(SmolStr::new("n")),
                result,
                Icit::Expl,
            )]),
        });
    }
    result
}

pub(super) fn nat_to_dec(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    let nat_val = &args[0];
    let count = count_nat(nat_val);
    Some(Val::LiteralIntro(empty_span(count.to_string())).into())
}

/// Minimal context for hover display — only stores what pretty_tm/quote actually needs.
#[derive(Debug, Clone)]
pub struct HoverCxt {
    pub lvl: Lvl,
    pub locals: Locals,
    pub decl: Rc<HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>, Option<PrimFunc>)>>,
}

impl HoverCxt {
    pub fn names(&self) -> List<SmolStr> {
        fn go(locals: &Locals) -> List<SmolStr> {
            match locals {
                Locals::Here => List::new(),
                Locals::Define(locals, name, _, _) => go(locals).prepend(name.data.clone()),
                Locals::Bind(locals, name, _) => go(locals).prepend(name.data.clone()),
            }
        }
        go(&self.locals)
    }
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    pub src_names: Rc<BiMap<SmolStr, Lvl, (Span<()>, Rc<VTy>)>>,
    pub decl: Rc<HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>, Option<PrimFunc>)>>,
    pub namespace: List<(Rc<Val>, HashSet<SmolStr>, Raw)>,
    pub namespace_prefix: Option<SmolStr>,
    pub namespaces: Rc<HashSet<SmolStr>>,
    update_from: Option<usize>,
}

fn string_concat(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            Some(Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into())
        },
        _ => None,
    }
}

fn string_to_global_type(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            Some(infer.eval(decl, &List::new(), &Tm::Decl(a.clone().map(|a| SmolStr::new(a))).into()))
        }
        _ => None,
    }
}

fn create_global(infer: &Infer, _decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                x.insert(a.data.clone(), args[1].clone());
            };
            Some(Val::U(0).into())
        }
        _ => None,
    }
}

fn change_mutable(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                if let Some(x) = x.get_mut(&a.data) {
                    *x = infer.v_app(
                        decl,
                        &args[1],
                        x.clone(),
                        Icit::Expl
                    )
                }
            };
            Some(Val::U(0).into())
        }
        _ => None,
    }
}

fn get_global(infer: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            Some(infer.mutable_map.write().unwrap().get(&a.data).unwrap().clone())
        }
        _ => None,
    }
}

fn change_mutable_default(infer: &Infer, decl: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 3 { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                if let Some(x) = x.get_mut(&a.data) {
                    *x = infer.v_app(
                        decl,
                        &args[1],
                        x.clone(),
                        Icit::Expl
                    )
                } else {
                    x.insert(a.data.clone(), args[2].clone());
                }
            };
            Some(Val::U(0).into())
        }
        _ => None,
    }
}

fn file_read_all_text(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
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

fn file_write_all_text(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.len() < 2 { return None; }
    match (args[0].as_ref(), args[1].as_ref()) {
        (Val::LiteralIntro(path), Val::LiteralIntro(content)) => {
            std::fs::write(&path.data, &content.data)
                .unwrap_or_else(|e| panic!("file_write_all_text: failed to write '{}': {}", path.data, e));
            Some(Val::U(0).into())
        },
        _ => None,
    }
}

fn file_append_all_text(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
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
            Some(Val::U(0).into())
        },
        _ => None,
    }
}

fn file_exists(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            let exists = std::path::Path::new(&path.data).exists();
            Some(Val::LiteralIntro(path.clone().map(|_| if exists { "true".to_string() } else { "false".to_string() })).into())
        },
        _ => None,
    }
}

fn file_delete(_: &Infer, _: &Decl, args: &[Rc<Val>]) -> Option<Rc<Val>> {
    if args.is_empty() { return None; }
    match args[0].as_ref() {
        Val::LiteralIntro(path) => {
            std::fs::remove_file(&path.data)
                .unwrap_or_else(|e| panic!("file_delete: failed to delete '{}': {}", path.data, e));
            Some(Val::U(0).into())
        },
        _ => None,
    }
}

// === helpers for building Tm trees ===

pub(super) fn tm_lam(names: &[&str], inner: Rc<Tm>) -> Rc<Tm> {
    names.iter().rev().fold(inner, |acc, name|
        Tm::Lam(empty_span(SmolStr::new(*name)), Icit::Expl, acc).into())
}

pub(super) fn tm_pi(args: &[(&str, Rc<Tm>)], ret: Rc<Tm>) -> Rc<Tm> {
    args.iter().rev().fold(ret, |acc, (name, ty)|
        Tm::Pi(empty_span(SmolStr::new(*name)), Icit::Expl, ty.clone(), acc).into())
}

pub(super) fn tm_decl(name: &str) -> Rc<Tm> {
    Tm::Decl(empty_span(SmolStr::new(name))).into()
}

pub(super) fn tm_app(f: Rc<Tm>, arg: Rc<Tm>) -> Rc<Tm> {
    Tm::App(f, arg, Icit::Expl).into()
}

impl Cxt {
    pub fn new(infer: &Infer) -> Self {
        let mut cxt = Self::empty();

        cxt = cxt.decl(
            empty_span(SmolStr::new("String")),
            Tm::LiteralType.into(),
            Val::LiteralType.into(),
            Tm::U(0).into(),
            Val::U(0).into(),
            None,
        ).unwrap();

        cxt = cxt.add_builtin(infer, "string_concat",
            tm_pi(&[("x", tm_decl("String")), ("y", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(string_concat)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "string_to_global_type",
            tm_pi(&[("x", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(string_to_global_type)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "create_global",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("y", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(create_global)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "change_mutable",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(change_mutable)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "get_global",
            tm_pi(&[("x", tm_decl("String"))],
                tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            PrimFunc(Rc::new(get_global)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "change_mutable_default",
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
                ("z", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into())),
            ], Tm::U(0).into()),
            PrimFunc(Rc::new(change_mutable_default)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_read_all_text",
            tm_pi(&[("path", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(file_read_all_text)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_write_all_text",
            tm_pi(&[("path", tm_decl("String")), ("content", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(file_write_all_text)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_append_all_text",
            tm_pi(&[("path", tm_decl("String")), ("content", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(file_append_all_text)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_exists",
            tm_pi(&[("path", tm_decl("String"))], tm_decl("String")),
            PrimFunc(Rc::new(file_exists)),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "file_delete",
            tm_pi(&[("path", tm_decl("String"))], Tm::U(0).into()),
            PrimFunc(Rc::new(file_delete)),
        ).unwrap();

        cxt
    }

    pub fn add_builtin(self, infer: &Infer, name: &str, ty: Rc<Tm>, prim: PrimFunc) -> Result<Self, Error> {
        let va = infer.eval(&self.decl, &self.env, &ty);
        let name_span = empty_span(SmolStr::new(name));
        let val_tm = Tm::Decl(name_span.clone()).into();
        let vt = Val::Decl(name_span.clone(), List::new()).into();
        self.decl(name_span, val_tm, vt, ty, va, Some(prim))
    }

    /// Register nat_to_dec builtin (must be called AFTER nat.typort is loaded)
    pub(crate) fn register_nat_to_dec(cxt: &mut Cxt, infer: &Infer) {
        let f_nat_to_dec = PrimFunc(Rc::new(nat_to_dec));
        let old = std::mem::replace(cxt, Self::empty());
        *cxt = old.add_builtin(infer, "nat_to_dec",
            tm_pi(&[("n", tm_decl("Nat"))], tm_decl("String")),
            f_nat_to_dec,
        ).unwrap();
    }

    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: Rc::new(BiMap::new()),
            decl: Rc::new(HashMap::new()),
            namespace: List::new(),
            namespace_prefix: None,
            namespaces: Rc::new(HashSet::new()),
            update_from: None,
        }
    }
    pub fn clone_without_src_names(&self) -> Self {
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: Rc::new(BiMap::new()),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
        }
    }

    pub fn names(&self) -> List<SmolStr> {
        fn go(locals: &Locals) -> List<SmolStr> {
            match locals {
                Locals::Here => List::new(),
                Locals::Define(locals, name, _, _) => go(locals).prepend(name.data.clone()),
                Locals::Bind(locals, name, _) => go(locals).prepend(name.data.clone()),
            }
        }
        go(&self.locals)
    }

    pub fn bind(&self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        Rc::make_mut(&mut src_names).insert(x.data.clone(), (self.lvl, (x.to_span(), a)));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
        }
    }

    pub fn fake_bind(&self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<Self, Error> {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut decl = self.decl.clone();
        let decl_map = Rc::make_mut(&mut decl);
        let t = decl_map.insert(x.data.clone(), (x.to_span(), Tm::Decl(x.clone()).into(), Val::Decl(x.clone(), List::new()).into(), a_quote, a, None));
        if t.is_some() {
            return Err(Error(x.to_span().map(|_| format!("redefine {}", x.data)), vec![]));
        }
        Ok(Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl,
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
        })
    }

    pub fn new_binder(&self, x: Span<SmolStr>, a_quote: Rc<Tm>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
        }
    }

    pub fn define(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut src_names = self.src_names.clone();
        Rc::make_mut(&mut src_names).insert(x.data.clone(), (self.lvl, (x.to_span(), va)));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Rc::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
        }
    }

    pub fn decl(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>, prim: Option<PrimFunc>) -> Result<Self, Error> {
        let mut decl = self.decl.clone();
        let decl_map = Rc::make_mut(&mut decl);
        decl_map.insert(x.data.clone(), (x.to_span(), t, vt, a, va, prim));
        Ok(Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl,
            namespace: self.namespace.clone(),
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            update_from: self.update_from,
        })
    }

    /// freshVal 函数实现
    /// 参考 Haskell 代码: freshVal def from to = eval def to . quote def from (Lvl (length from))
    pub fn fresh_val(&self, infer: &Infer, from: &Env, to: &Env, val: &Rc<Val>) -> Rc<Val> {
        // quote def from (Lvl (length from))
        let quoted = infer.quote(&self.decl, Lvl(from.len() as u32), val);

        // eval def to
        infer.eval(&self.decl, to, &quoted)
    }

    pub fn update_cxt(&self, infer: &Infer, x: Lvl, v: Rc<Val>, update_prune: bool) -> Cxt {
        match v.as_ref() {
            Val::Flex(..) => self.clone(),
            _ => {
                let update_from = if let Some(u) = self.update_from {
                    if u < x.0 as usize {
                        u
                    } else {
                        x.0 as usize
                    }
                } else {
                    x.0 as usize
                };
                let x_prime = lvl2ix(self.lvl, x).0 as usize;
                /*println!(
                    " update {}: {} with {}",
                    x.0,
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, self.env.iter().nth(x_prime).unwrap().clone())),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, v.clone()))
                );*/
                //let locals = self.locals.update_at(x_prime, infer.quote(&self.decl, self.lvl, &v));
                let env = self.env.change_n(x_prime, |_| v);
                let mut new_src_names = self.src_names.clone();
                let env_t = self.refresh(infer, &self.env, Rc::make_mut(&mut new_src_names), env, self.lvl.0 as usize - update_from);
                let locals = self.locals.clone().update_by_cxt(infer, &self.decl, self.lvl, &env_t);
        
                Cxt {
                    env: env_t,
                    lvl: self.lvl,
                    locals: if update_prune {locals} else {self.locals.clone()},//TODO: lookup env_t, if is not Val::vavar(lvl), set local to Define
                    //locals: self.locals.clone().update_by_cxt(infer, &self.decl, self.lvl, &self.env),
                    //locals,
                    pruning: if update_prune {self.pruning.change_n(x_prime, |_| None)} else {self.pruning.clone()},
                    src_names: new_src_names,
                    decl: self.decl.clone(),
                    namespace: self.namespace.clone(),
                    namespace_prefix: self.namespace_prefix.clone(),
                    namespaces: self.namespaces.clone(),
                    update_from: Some(update_from),
                }
            }
        }
    }

    fn refresh(&self, infer: &Infer, env: &List<Rc<Val>>, src_names: &mut BiMap<SmolStr, Lvl, (Span<()>, Rc<Val>)>, env2: List<Rc<Val>>, walk: usize) -> List<Rc<Val>> {
        if env.is_empty() {
            List::new()
        } else {
            let env_t = if walk == 0 {env.tail()} else {self.refresh(infer, &env.tail(), src_names, env2.clone(), walk - 1)};
            let env_tt = env2.change_tail(env_t.clone());
            let ret = self.fresh_val(infer, &self.env, &env_tt, env.head().unwrap());
            /*let a = pretty_tm(0, self.names(), &infer.quote(self.lvl, env.head().unwrap().clone()));
            let b = pretty_tm(0, self.names(), &infer.quote(self.lvl, ret.clone()));
            if a != b {
                println!(
                    "refresh {}: {} with {}",
                    env.len(),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, env.head().unwrap().clone())),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, ret.clone()))
                );
            }*/
            
            let ret = env_t.prepend(ret);
            if let Some((_, x)) = src_names.get_by_key2_mut(&Lvl(env_t.len() as u32)) {
                *x = self.fresh_val(infer, &self.env, &env_tt, x);
            }
            ret
        }
    }
}

impl Cxt {
    #[allow(unused)]
    pub fn print_env(&self, infer: &Infer) {
        self.env
            .iter()
            .zip(self.names().iter())
            .for_each(|(x, name)| {
                println!("{name}: {}", pretty_tm(0, self.names(), &infer.quote(&self.decl, self.lvl, x)))
            });
    }
}
