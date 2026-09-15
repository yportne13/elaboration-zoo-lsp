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

    pub fn fake_bind(&self, x: Span<String>, a: Val, global_idx: Lvl) -> Self {
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

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// src_names 的类型值包 `VSub`；lvl / locals / pruning 一概不动——
    /// **槽位布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经 force
    /// 展开看到解。σ 为空时零开销直通。
    ///
    /// 取代旧 `update_cxt`/`refresh`（改写目标槽 + 全槽重引用）——旧架构
    /// 正是 L07 README §6 所述已淘汰的载体：已捕获旧上下文的值会过期、
    /// 刷新后槽位可漂移。
    pub fn subst_cxt(&self, sub: &Rc<Subst>) -> Self {
        if sub.is_empty() {
            return self.clone();
        }
        let wrap = |v: &Val| Val::VSub(Box::new(v.clone()), sub.clone());
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

    /// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
    /// 这些是模式特化方程可以求解的对象。let 定义槽（槽里是值不是 vvar）
    /// 天然不在其中。嵌套 match 的入口上下文可能已被外层精化包裹
    /// （`subst_cxt`）——解包 VSub 看**槽的原始形态**；外层已解变量也按
    /// raw 层级进入基线（无害：方程里它不再以 bare rigid 出现，force 在
    /// 读点已展开）。
    pub fn bind_slots(&self) -> Vec<Lvl> {
        let n = self.lvl.0;
        self.env
            .iter()
            .enumerate()
            .filter_map(|(i, v)| {
                let mut raw = v;
                while let Val::VSub(inner, _) = raw {
                    raw = inner;
                }
                match raw {
                    Val::Rigid(l, sp) if sp.is_empty() && l.0 + (i as u32) + 1 == n => Some(*l),
                    _ => None,
                }
            })
            .collect()
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
