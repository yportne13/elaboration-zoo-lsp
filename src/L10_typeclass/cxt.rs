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
    pub src_names: BiMap<String, Lvl, Rc<VTy>>,
}

impl Cxt {
    pub fn new() -> Self {
        Self::empty()
            .define(
                empty_span("String".to_owned()),
                Tm::LiteralType.into(),
                Val::LiteralType.into(),
                Tm::U(0).into(),
                Val::U(0).into(),
            )
            .define(
                empty_span("string_concat".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Lam(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Prim),
                    )),
                ).into(),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new().prepend(Val::LiteralType.into()),
                        Tm::Lam(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Rc::new(Tm::Prim),
                        ).into(),
                    ),
                ).into(),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Var(Ix(0))),
                    Rc::new(Tm::Pi(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Var(Ix(1))),
                        Rc::new(Tm::Var(Ix(2))),
                    )),
                ).into(),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Val::LiteralType),
                    Closure(
                        List::new().prepend(Val::LiteralType.into()),
                        Rc::new(Tm::Pi(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Rc::new(Tm::Var(Ix(1))),
                            Rc::new(Tm::Var(Ix(2))),
                        )),
                    ),
                ).into(),
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

    pub fn bind(&self, x: Span<String>, a_quote: Rc<Tm>, a: Rc<Val>) -> Self {
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

    pub fn fake_bind(&self, x: Span<String>, a: Rc<Val>, global_idx: Lvl) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (global_idx + 1919810, a));
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names,
        }
    }

    pub fn new_binder(&self, x: Span<String>, a_quote: Rc<Tm>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
        }
    }

    pub fn define(&self, x: Span<String>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
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

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// src_names 的类型包 `VSub`；lvl / locals / pruning 不动——**槽位布局
    /// （= 运行时布局）不变**，被解变量仍在原槽位，读点经 force 推开看到解。
    /// σ 为空时零开销直通。
    ///
    /// 替代旧的 `update_cxt`/`refresh`（改写 env 槽 + 全量重引用）：解不再
    /// 改写既有值，只包在外面，消费点惰性展开——旧架构"已捕获旧上下文的值
    /// 过期、槽位错位"的 bug 族按构造消除。
    pub fn subst_cxt(&self, sub: &Rc<Subst>) -> Self {
        if sub.is_empty() {
            return self.clone();
        }
        let wrap = |v: &Rc<Val>| Rc::new(Val::VSub(v.clone(), sub.clone()));
        let mut src_names = BiMap::new();
        for (k, l, ty) in self.src_names.iter_all() {
            src_names.insert(k.clone(), (*l, wrap(ty)));
        }
        Cxt {
            env: self.env.map(wrap),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names,
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
                println!("{name}: {}", pretty_tm(0, self.names(), &infer.quote(self.lvl, x)))
            });
    }
}
