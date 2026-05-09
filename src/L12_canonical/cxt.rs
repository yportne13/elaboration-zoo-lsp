use std::collections::HashSet;

use crate::{bimap::BiMap, parser_lib::ToSpan};

use super::{
    syntax::{Locals, Pruning},
    *,
};

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    pub src_names: BiMap<SmolStr, Lvl, (Span<()>, Rc<VTy>)>,
    pub decl: HashMap<SmolStr, (Span<()>, Rc<Tm>, Rc<Val>, Rc<Ty>, Rc<VTy>)>,
    pub namespace: List<(Rc<Val>, HashSet<SmolStr>, Raw)>,
    update_from: Option<usize>,
}

fn string_concat(_: &Infer, _: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    match (env.iter().nth(1).unwrap().as_ref(), env.iter().next().unwrap().as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into()
        },
        _ => Val::Prim(typ, PrimFunc(Rc::new(string_concat))).into(),
    }
}

fn string_to_global_type(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    match env.iter().next().unwrap().as_ref() {
        Val::LiteralIntro(a) => {
            infer.eval(decl, env, &Tm::Decl(a.clone().map(|a| SmolStr::new(a))).into())
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(string_to_global_type))).into(),
    }
}

fn create_global(infer: &Infer, _decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    match env.iter().nth(1).unwrap().as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                x.insert(a.data.clone(), env.iter().next().unwrap().clone());
            };
            Val::U(0).into()
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(create_global))).into(),
    }
}

fn change_mutable(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    match env.iter().nth(1).unwrap().as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                if let Some(x) = x.get_mut(&a.data) {
                    *x = infer.v_app(
                        decl,
                        env.iter().next().unwrap(),
                        x.clone(),
                        Icit::Expl
                    )
                }
            };
            Val::U(0).into()
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(change_mutable))).into(),
    }
}

fn get_global(infer: &Infer, _: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    match env.iter().next().unwrap().as_ref() {
        Val::LiteralIntro(a) => {
            infer.mutable_map.write().unwrap().get(&a.data).unwrap().clone()
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(get_global))).into(),
    }
}

fn change_mutable_default(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    match env.iter().nth(2).unwrap().as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                if let Some(x) = x.get_mut(&a.data) {
                    *x = infer.v_app(
                        decl,
                        env.iter().nth(1).unwrap(),
                        x.clone(),
                        Icit::Expl
                    )
                } else {
                    x.insert(a.data.clone(), env.iter().next().unwrap().clone());
                }
            };
            Val::U(0).into()
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(change_mutable_default))).into(),
    }
}

// === helpers for building Tm trees ===

fn tm_lam(names: &[&str], inner: Rc<Tm>) -> Rc<Tm> {
    names.iter().rev().fold(inner, |acc, name|
        Tm::Lam(empty_span(SmolStr::new(*name)), Icit::Expl, acc).into())
}

fn tm_pi(args: &[(&str, Rc<Tm>)], ret: Rc<Tm>) -> Rc<Tm> {
    args.iter().rev().fold(ret, |acc, (name, ty)|
        Tm::Pi(empty_span(SmolStr::new(*name)), Icit::Expl, ty.clone(), acc).into())
}

fn tm_decl(name: &str) -> Rc<Tm> {
    Tm::Decl(empty_span(SmolStr::new(name))).into()
}

fn tm_app(f: Rc<Tm>, arg: Rc<Tm>) -> Rc<Tm> {
    Tm::App(f, arg, Icit::Expl).into()
}

impl Cxt {
    pub fn new(infer: &Infer) -> Self {
        let f_concat = PrimFunc(Rc::new(string_concat));
        let f_to_global = PrimFunc(Rc::new(string_to_global_type));
        let f_create = PrimFunc(Rc::new(create_global));
        let f_change = PrimFunc(Rc::new(change_mutable));
        let f_get = PrimFunc(Rc::new(get_global));
        let f_change_def = PrimFunc(Rc::new(change_mutable_default));

        let mut cxt = Self::empty();

        cxt = cxt.decl(
            empty_span(SmolStr::new("String")),
            Tm::LiteralType.into(),
            Val::LiteralType.into(),
            Tm::U(0).into(),
            Val::U(0).into(),
        ).unwrap();

        let str_val = infer.eval(&cxt.decl, &cxt.env, &tm_decl("String"));

        cxt = cxt.add_builtin(infer, "string_concat",
            tm_lam(&["x", "y"], Tm::Prim(str_val.clone(), f_concat).into()),
            tm_pi(&[("x", tm_decl("String")), ("y", tm_decl("String"))], tm_decl("String")),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "string_to_global_type",
            tm_lam(&["x"], Tm::Prim(str_val.clone(), f_to_global).into()),
            tm_pi(&[("x", tm_decl("String"))], Tm::U(0).into()),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "create_global",
            tm_lam(&["x", "y"], Tm::Prim(Val::U(0).into(), f_create).into()),
            tm_pi(&[
                ("x", tm_decl("String")),
                ("y", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            ], Tm::U(0).into()),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "change_mutable",
            tm_lam(&["x", "y"], Tm::Prim(Val::U(0).into(), f_change).into()),
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
            ], Tm::U(0).into()),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "get_global",
            tm_lam(&["x"], Tm::Prim(Val::U(0).into(), f_get).into()),
            tm_pi(&[("x", tm_decl("String"))],
                tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
        ).unwrap();

        cxt = cxt.add_builtin(infer, "change_mutable_default",
            tm_lam(&["x", "y", "z"], Tm::Prim(Val::U(0).into(), f_change_def).into()),
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
                ("z", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into())),
            ], Tm::U(0).into()),
        ).unwrap();

        cxt
    }

    pub fn add_builtin(self, infer: &Infer, name: &str, val: Rc<Tm>, ty: Rc<Tm>) -> Result<Self, Error> {
        let vt = infer.eval(&self.decl, &self.env, &val);
        let va = infer.eval(&self.decl, &self.env, &ty);
        self.decl(empty_span(SmolStr::new(name)), val, vt, ty, va)
    }

    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: BiMap::new(),
            decl: HashMap::new(),
            namespace: List::new(),
            update_from: None,
        }
    }
    pub fn clone_without_src_names(&self) -> Self {
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: BiMap::new(),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
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
        src_names.insert(x.data.clone(), (self.lvl, (x.to_span(), a)));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            update_from: self.update_from,
        }
    }

    pub fn fake_bind(&self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<Self, Error> {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut decl = self.decl.clone();
        let t = decl.insert(x.data.clone(), (x.to_span(), Tm::Decl(x.clone()).into(), Val::Decl(x.clone(), List::new()).into(), a_quote, a));
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
            update_from: self.update_from,
        }
    }

    pub fn define(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, (x.to_span(), va)));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Rc::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
            update_from: self.update_from,
        }
    }

    pub fn decl(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Result<Self, Error> {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut decl = self.decl.clone();
        let t = decl.insert(x.data.clone(), (x.to_span(), t, vt, a, va));
        /*if let Some((span, _, _, _, _)) = t {
            return Err(Error(span.map(|_| format!("redefine {}", x.data))));
        }*/
        Ok(Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl,
            namespace: self.namespace.clone(),
            update_from: self.update_from,
        })
    }

    /// freshVal 函数实现
    /// 参考 Haskell 代码: freshVal def from to = eval def to . quote def from (Lvl (length from))
    pub fn fresh_val(&self, infer: &Infer, from: &Env, to: &Env, val: &Rc<Val>) -> Rc<Val> {
        // quote def from (Lvl (length from))
        let quoted = infer.quote(&self.decl, Lvl(from.iter().count() as u32), val);

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
                let env_t = self.refresh(infer, &self.env, &mut new_src_names, env, self.lvl.0 as usize - update_from);
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
