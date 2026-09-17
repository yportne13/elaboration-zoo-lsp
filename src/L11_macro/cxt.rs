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
    pub src_names: BiMap<String, Lvl, (Span<()>, Rc<VTy>)>,
    /// 全局 decl 表，按 `Rc` 共享（对齐 L13 与 L07 口径）：`Cxt` 的每次构造
    /// （bind / define / new_binder / subst_cxt …）只需递增引用计数，不再克隆
    /// 整张表。此前是**按值**持有 `HashMap`，每次 `Cxt` 构造都深克隆一遍
    /// ——`struct` 负载 k=11 单次 run 实测约 7 万次整表克隆、1.04 亿次条目
    /// 拷贝（键是 `String`，每次克隆都是一次堆分配）。写入仍走写时复制
    /// （`fake_bind` / `decl` 里的 `Rc::make_mut`），占位语义不变。
    pub decl: Rc<Decl>,
    pub namespace: List<(Rc<Val>, HashSet<String>, Raw)>,
}


fn string_concat(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    // 精化 σ 包裹的槽值先 force 推开（臂体内引用被解槽时 env 带 VSub；
    // 旧 refresh 世界槽值已物化）
    let a = infer.force(decl, &env.iter().nth(1).unwrap());
    let b = infer.force(decl, &env.iter().nth(0).unwrap());
    match (a.as_ref(), b.as_ref()) {
        (Val::LiteralIntro(a), Val::LiteralIntro(b)) => {
            Val::LiteralIntro(a.clone().map(|x| format!("{x}{}", b.data))).into()
        },
        _ => Val::Prim(typ, PrimFunc(Rc::new(string_concat))).into(),
    }
}

fn string_to_global_type(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    let a = infer.force(decl, &env.iter().next().unwrap());
    match a.as_ref() {
        Val::LiteralIntro(a) => {
            infer.eval(decl, env, &Tm::Decl(a.clone()).into())
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(string_to_global_type))).into(),
    }
}

fn create_global(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    let a = infer.force(decl, &env.iter().nth(1).unwrap());
    match a.as_ref() {
        Val::LiteralIntro(a) => {
            if let Ok(mut x) = infer.mutable_map.write() {
                x.insert(a.data.clone(), env.iter().nth(0).unwrap().clone());
            };
            Val::U(0).into()
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(change_mutable))).into(),
    }
}

fn change_mutable(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    let a = infer.force(decl, &env.iter().nth(1).unwrap());
    match a.as_ref() {
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

fn get_global(infer: &Infer, decl: &Decl, env: &Env, typ: Rc<Val>) -> Rc<Val> {
    let a = infer.force(decl, &env.iter().next().unwrap());
    match a.as_ref() {
        Val::LiteralIntro(a) => {
            infer.mutable_map.write().unwrap().get(&a.data).unwrap().clone()
        }
        _ => Val::Prim(typ, PrimFunc(Rc::new(change_mutable))).into(),
    }
}

impl Cxt {
    pub fn new() -> Self {
        let string_concat = PrimFunc(Rc::new(string_concat));
        let string_to_global_type = PrimFunc(Rc::new(string_to_global_type));
        let create_global = PrimFunc(Rc::new(create_global));
        let change_mutable = PrimFunc(Rc::new(change_mutable));
        let get_global = PrimFunc(Rc::new(get_global));
        Self::empty()
            .decl(
                empty_span("String".to_owned()),
                Tm::LiteralType.into(),
                Val::LiteralType.into(),
                Tm::U(0).into(),
                Val::U(0).into(),
            )
            .unwrap()
            .decl(
                empty_span("string_concat".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Lam(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Prim(Val::LiteralType.into(), string_concat.clone())),
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
                            Rc::new(Tm::Prim(Val::LiteralType.into(), string_concat)),
                        ).into(),
                    ),
                ).into(),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                    Rc::new(Tm::Pi(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                        Rc::new(Tm::Decl(empty_span("String".to_owned()))),
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
                            Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                            Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                        )),
                    ),
                ).into(),
            )
            .unwrap()
            .decl(
                empty_span("string_to_global_type".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Prim(Val::LiteralType.into(), string_to_global_type.clone())),
                ).into(),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new(),
                        Tm::Prim(Val::LiteralType.into(), string_to_global_type).into(),
                    ),
                ).into(),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                    Rc::new(Tm::U(0)),
                ).into(),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Val::LiteralType),
                    Closure(
                        List::new(),
                        Rc::new(Tm::U(0)),
                    ),
                ).into(),
            )
            .unwrap()
            .decl(
                empty_span("create_global".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Lam(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Prim(Val::U(0).into(), create_global.clone())),
                    )),
                ).into(),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new(),
                        Tm::Lam(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Rc::new(Tm::Prim(Val::U(0).into(), create_global)),
                        ).into(),
                    ),
                ).into(),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                    Rc::new(Tm::Pi(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl)),
                        Rc::new(Tm::U(0)),
                    )),
                ).into(),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Val::LiteralType),
                    Closure(
                        List::new(),
                        Rc::new(Tm::Pi(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Rc::new(Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl).into()),
                            Rc::new(Tm::U(0)),
                        )),
                    ),
                ).into(),
            )
            .unwrap()
            .decl(
                empty_span("change_mutable".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Lam(
                        empty_span("y".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Prim(Val::U(0).into(), change_mutable.clone())),
                    )),
                ).into(),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new(),
                        Tm::Lam(
                            empty_span("y".to_owned()),
                            Icit::Expl,
                            Rc::new(Tm::Prim(Val::U(0).into(), change_mutable)),
                        ).into(),
                    ),
                ).into(),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                    Rc::new(Tm::Pi(
                        empty_span("f".to_owned()),
                        Icit::Expl,
                        Rc::new(Tm::Pi(
                            empty_span("_".to_owned()),
                            Icit::Expl,
                            Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl).into(),
                            Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(1)).into(), Icit::Expl).into(),
                        )),
                        Rc::new(Tm::U(0)),
                    )),
                ).into(),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Val::LiteralType),
                    Closure(
                        List::new(),
                        Rc::new(Tm::Pi(
                            empty_span("f".to_owned()),
                            Icit::Expl,
                            Rc::new(Tm::Pi(
                                empty_span("_".to_owned()),
                                Icit::Expl,
                                Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl).into(),
                                Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(1)).into(), Icit::Expl).into(),
                            )),
                            Rc::new(Tm::U(0)),
                        )),
                    ),
                ).into(),
            )
            .unwrap()
            .decl(
                empty_span("get_global".to_owned()),
                Tm::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Prim(
                        //Rc::new(Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl)),
                        Val::U(0).into(),
                        get_global.clone()
                    )),
                ).into(),
                Val::Lam(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Closure(
                        List::new(),
                        Tm::Prim(
                            //Rc::new(Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl)),
                            Val::U(0).into(),
                            get_global
                        ).into(),
                    ),
                ).into(),
                Tm::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Tm::Decl(empty_span("String".to_owned()))),
                    Rc::new(Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl).into()),
                ).into(),
                Val::Pi(
                    empty_span("x".to_owned()),
                    Icit::Expl,
                    Rc::new(Val::LiteralType),
                    Closure(
                        List::new(),
                        Rc::new(Tm::App(Tm::Decl(empty_span("string_to_global_type".to_owned())).into(), Tm::Var(Ix(0)).into(), Icit::Expl).into()),
                    ),
                ).into(),
            )
            .unwrap()
    }
    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: BiMap::new(),
            decl: Rc::new(HashMap::new()),
            namespace: List::new(),
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
        src_names.insert(x.data.clone(), (self.lvl, (x.to_span(), a)));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
        }
    }

    pub fn fake_bind(&self, x: Span<String>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<Self, Error> {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let mut decl = self.decl.clone();
        let t = Rc::make_mut(&mut decl).insert(x.data.clone(), (x.to_span(), Tm::Decl(x.clone()).into(), Val::Decl(x.clone(), List::new()).into(), a_quote, a));
        if let Some((span, _, _, _, _)) = t {
            return Err(Error(x.to_span().map(|_| format!("redefine {}", x.data))));
        }
        Ok(Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
            decl,
            namespace: self.namespace.clone(),
        })
    }

    pub fn new_binder(&self, x: Span<String>, a_quote: Rc<Tm>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
        }
    }

    pub fn define(&self, x: Span<String>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
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
        }
    }

    pub fn decl(&self, x: Span<String>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Result<Self, Error> {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let mut decl = self.decl.clone();
        let t = Rc::make_mut(&mut decl).insert(x.data.clone(), (x.to_span(), t, vt, a, va));
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
        })
    }

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// src_names 的类型包 `VSub`；lvl / locals / pruning / decl / namespace
    /// 不动——**槽位布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经
    /// force 推开看到解。decl 表是全局声明登记（旧 `update_cxt` 也从不改写
    /// 它，故此处保持原样）。σ 为空时零开销直通。
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
        for (k, l, (sp, ty)) in self.src_names.iter_all() {
            src_names.insert(k.clone(), (*l, (*sp, wrap(ty))));
        }
        Cxt {
            env: self.env.map(wrap),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
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
