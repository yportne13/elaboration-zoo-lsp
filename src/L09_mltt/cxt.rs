use crate::bimap::BiMap;

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
    pub src_names: BiMap<String, Lvl, VTy>,
}

impl Cxt {
    pub fn new() -> Self {
        Self::empty()
            .define(
                empty_span("String".to_owned()),
                Tm::LiteralType,
                Val::LiteralType,
                Tm::U(0),
                Val::U(0),
            )
            .define(
                empty_span("string_concat".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Box::new(Tm::Lam(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Box::new(Tm::Prim),
                    )),
                ),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new().prepend(Val::LiteralType),
                        Box::new(Tm::Lam(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Box::new(Tm::Prim),
                        )),
                    ),
                ),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Box::new(Tm::Var(Ix(0))),
                    Box::new(Tm::Pi(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Box::new(Tm::Var(Ix(1))),
                        Box::new(Tm::Var(Ix(2))),
                    )),
                ),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Box::new(Val::LiteralType),
                    Closure(
                        List::new().prepend(Val::LiteralType),
                        Box::new(Tm::Pi(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Box::new(Tm::Var(Ix(1))),
                            Box::new(Tm::Var(Ix(2))),
                        )),
                    ),
                ),
            )
    }
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: BiMap::new(),
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

    pub fn bind(&self, x: Span<String>, a_quote: Tm, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, a));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
        }
    }

    pub fn fake_bind(&self, x: Span<String>, a: Val) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl + 1919810, a));
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names,
        }
    }

    pub fn new_binder(&self, x: Span<String>, a_quote: Tm) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
        }
    }

    pub fn define(&self, x: Span<String>, t: Tm, vt: Val, a: Ty, va: VTy) -> Self {
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

    /// freshVal 函数实现
    /// 参考 Haskell 代码: freshVal def from to = eval def to . quote def from (Lvl (length from))
    pub fn fresh_val(&self, infer: &Infer, from: &Env, to: &Env, val: Val) -> Val {
        // quote def from (Lvl (length from))
        let quoted = infer.quote(Lvl(from.iter().count() as u32), val);

        // eval def to
        infer.eval(to, quoted)
    }

    pub fn update_cxt(&self, infer: &Infer, x: Lvl, v: Val) -> Cxt {
        match v {
            Val::Flex(..) => self.clone(),
            v => {
                let x_prime = lvl2ix(self.lvl, x).0 as usize;
                /*println!(
                    " update {}: {} with {}",
                    x.0,
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, self.env.iter().nth(x_prime).unwrap().clone())),
                    pretty_tm(0, self.names(), &infer.quote(self.lvl, v.clone()))
                );*/
                let env = self.env.change_n(x_prime, |_| v);
                let mut new_src_names = self.src_names.clone();
                let env_t = self.refresh(infer, &self.env, &mut new_src_names, env);
        
                Cxt {
                    env: env_t,
                    lvl: self.lvl,
                    locals: self.locals.clone(),//TODO: lookup env_t, if is not Val::vavar(lvl), set local to Define
                    pruning: self.pruning.change_n(x_prime, |_| None),
                    src_names: new_src_names,
                }
            }
        }
    }

    fn refresh(&self, infer: &Infer, env: &List<Val>, src_names: &mut BiMap<String, Lvl, Val>, env2: List<Val>) -> List<Val> {
        if env.is_empty() {
            List::new()
        } else {
            let env_t = self.refresh(infer, &env.tail(), src_names, env2.clone());
            let env_tt = env2.change_tail(env_t.clone());
            let ret = self.fresh_val(infer, &self.env, &env_tt, env.head().unwrap().clone());
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
            let src_change=  src_names.get_by_key2_mut(&Lvl(env_t.len() as u32)).unwrap();
            *src_change = self.fresh_val(infer, &self.env, &env_tt, src_change.clone());
            ret
        }
    }
}

impl Cxt {
    #[allow(unused)]
    pub fn print_env(&self, infer: &Infer) {
        self.env
            .iter()
            .for_each(|x| {
                println!("{}", pretty_tm(0, self.names(), &infer.quote(self.lvl, x.clone())))
            });
    }
}
