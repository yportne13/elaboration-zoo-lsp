use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::parser_lib::ToSpan;

use super::{
    syntax::{Locals, Pruning},
    *,
};

/// 源码名表 + 撤销轨迹（L07 `d411debe` 的 `NameState` 的 L12 版；L08 孪生
/// `name_map`+`name_trail` 的参考版对应物）。
///
/// 旧实现是 `BiMap` 持久表：`bind`/`define` 里 `Rc::clone` + `Rc::make_mut`
/// ——强计数恒为 2 ⇒ `make_mut` 每次**深拷整张表**（逐键 SmolStr 分配 +
/// 逐条 Rc 递增），n 个绑定器的精化是 O(n²)。
///
/// 新实现改为"单张表 + 撤销轨迹 + 按 mark 惰性回退"：`bind`/`define` 只做
/// 一次哈希插入 + 追加一条 (名字, 旧值) 轨迹，O(1)；上下文退出不显式
/// 撤销，而在**下一次访问名字表前**把轨迹裁回本上下文的 `name_mark`——
/// 语义与持久表一致（每个 Cxt 看到的名字集 = 创建时的快照），但不再有
/// 整表拷贝。轨迹是单线程深度优先遍历的日志，(mark, 轨迹长度) 一一对应
/// 地标识一个名字表版本。
#[derive(Debug, Default)]
pub struct NameState {
    map: FxHashMap<SmolStr, Rc<(Lvl, (Span<()>, Rc<VTy>))>>,
    /// (名字, 旧值)；旧值 `None` = 该名字此前不在表里。
    trail: Vec<(SmolStr, Option<Rc<(Lvl, (Span<()>, Rc<VTy>))>>)>,
}

impl NameState {
    /// 把轨迹裁回 `mark`（= 某个上下文的基线）：逆序还原被覆盖/删除的
    /// 条目。调用方保证 `mark <= trail.len()`（mark 只会取自已发生过的
    /// 轨迹长度，且深度优先下不会访问比自身更浅的上下文之后再用更深上下文
    /// ——见 `Cxt::unwind_names` 的 debug_assert）。
    fn unwind(&mut self, mark: u32) {
        debug_assert!(
            mark as usize <= self.trail.len(),
            "unwind: mark {} 超出轨迹长度 {}",
            mark,
            self.trail.len()
        );
        while self.trail.len() > mark as usize {
            let (k, prev) = self.trail.pop().expect("unwind: 轨迹为空");
            match prev {
                Some(v) => {
                    self.map.insert(k, v);
                }
                None => {
                    self.map.remove(&k);
                }
            }
        }
    }

    /// 插入一条（名字, (层级, (span, 类型))），旧值入轨迹。
    fn insert(&mut self, k: SmolStr, v: Rc<(Lvl, (Span<()>, Rc<VTy>))>) {
        let prev = self.map.insert(k.clone(), v);
        self.trail.push((k, prev));
    }
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    /// 源码变量名 → (绑定层级, (span, 类型值))，共享可变表（见 [`NameState`]）。
    /// 每次访问前先把轨迹裁回 `name_mark`，本上下文看到的名字集合恒等于
    /// 创建时的快照；条目值仍是 `Rc`（O(1)）。
    names: Rc<RefCell<NameState>>,
    /// 本上下文的名字表基线（轨迹长度）。
    name_mark: u32,
    /// 全局 decl 表，按 `Rc` 共享（对齐 L13 与 L07/L11 口径）：`Cxt` 的每次
    /// 构造（bind / define / new_binder / subst_cxt …）只需递增引用计数，
    /// 不再克隆整张表。写入仍走写时复制（`fake_bind` / `decl` 里的
    /// `Rc::make_mut`），占位语义不变。
    pub decl: Rc<Decl>,
    pub namespace: List<(Rc<Val>, FxHashSet<SmolStr>, Raw)>,
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

        cxt.decl_mut(
            empty_span(SmolStr::new("String")),
            Tm::LiteralType.into(),
            Val::LiteralType.into(),
            Tm::U(0).into(),
            Val::U(0).into(),
        );

        let str_val = infer.eval(&cxt.decl, &cxt.env, &tm_decl("String"));

        cxt.add_builtin_mut(infer, "string_concat",
            tm_lam(&["x", "y"], Tm::Prim(str_val.clone(), f_concat).into()),
            tm_pi(&[("x", tm_decl("String")), ("y", tm_decl("String"))], tm_decl("String")),
        );

        cxt.add_builtin_mut(infer, "string_to_global_type",
            tm_lam(&["x"], Tm::Prim(str_val.clone(), f_to_global).into()),
            tm_pi(&[("x", tm_decl("String"))], Tm::U(0).into()),
        );

        cxt.add_builtin_mut(infer, "create_global",
            tm_lam(&["x", "y"], Tm::Prim(Val::U(0).into(), f_create).into()),
            tm_pi(&[
                ("x", tm_decl("String")),
                ("y", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
            ], Tm::U(0).into()),
        );

        cxt.add_builtin_mut(infer, "change_mutable",
            tm_lam(&["x", "y"], Tm::Prim(Val::U(0).into(), f_change).into()),
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
            ], Tm::U(0).into()),
        );

        cxt.add_builtin_mut(infer, "get_global",
            tm_lam(&["x"], Tm::Prim(Val::U(0).into(), f_get).into()),
            tm_pi(&[("x", tm_decl("String"))],
                tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
        );

        cxt.add_builtin_mut(infer, "change_mutable_default",
            tm_lam(&["x", "y", "z"], Tm::Prim(Val::U(0).into(), f_change_def).into()),
            tm_pi(&[
                ("x", tm_decl("String")),
                ("f", tm_pi(&[
                    ("_", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(0)).into())),
                ], tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into()))),
                ("z", tm_app(tm_decl("string_to_global_type"), Tm::Var(Ix(1)).into())),
            ], Tm::U(0).into()),
        );

        cxt
    }

    pub fn add_builtin(self, infer: &Infer, name: &str, val: Rc<Tm>, ty: Rc<Tm>) -> Result<Self, Error> {
        let mut cxt = self;
        cxt.add_builtin_mut(infer, name, val, ty);
        Ok(cxt)
    }

    /// 就地注册 builtin（顺序构造路径专用）：调用方持有 `Cxt` 所有权，
    /// decl 表 `Rc` 强计数为 1，`decl_mut` 的 `Rc::make_mut` 原地写。
    fn add_builtin_mut(&mut self, infer: &Infer, name: &str, val: Rc<Tm>, ty: Rc<Tm>) {
        let vt = infer.eval(&self.decl, &self.env, &val);
        let va = infer.eval(&self.decl, &self.env, &ty);
        self.decl_mut(empty_span(SmolStr::new(name)), val, vt, ty, va);
    }

    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            names: Rc::new(RefCell::new(NameState::default())),
            name_mark: 0,
            decl: Rc::new(FxHashMap::default()),
            namespace: List::new(),
        }
    }
    pub fn clone_without_src_names(&self) -> Self {
        Cxt {
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            names: Rc::new(RefCell::new(NameState::default())),
            name_mark: 0,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
        }
    }

    /// 名字表访问前统一入口：把共享轨迹裁回本上下文的基线（惰性回滚）。
    /// 深度优先遍历下这是幂等的零/常数开销；跨兄弟作用域时把对方残留的
    /// 绑定逐条还原（每条只还原一次，均摊 O(1)）。
    #[inline]
    fn unwind_names(&self) {
        self.names.borrow_mut().unwind(self.name_mark);
    }

    /// 查一个源码局部名（局部 binder 优先于 decl 表）：返回共享条目
    /// `(绑定层级, (span, 类型值))`（克隆 = 一次 Rc 递增）。
    pub fn lookup_src(&self, n: &SmolStr) -> Option<Rc<(Lvl, (Span<()>, Rc<VTy>))>> {
        self.unwind_names();
        self.names.borrow().map.get(n).cloned()
    }

    /// 源码名是否已在本作用域绑定（`Enum.case` 限定构造子快捷路径的
    /// 局部遮蔽判定用）。
    pub fn has_src(&self, n: &SmolStr) -> bool {
        self.unwind_names();
        self.names.borrow().map.contains_key(n)
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
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            s.insert(x.data.clone(), Rc::new((self.lvl, (x.to_span(), a))));
            s.trail.len() as u32
        };
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            names: Rc::clone(&self.names),
            name_mark,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
        }
    }

    /// 持久化 `fake_bind` 包装（保留旧 `&Cxt` 调用方）：浅克隆上下文后就地写。
    pub fn fake_bind(&self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<Self, Error> {
        let mut cxt = self.clone();
        cxt.fake_bind_mut(x, a_quote, a)?;
        Ok(cxt)
    }

    /// 就地插入递归定义占位（顺序声明路径专用）：调用方持有 `Cxt` 所有权，
    /// `Rc::make_mut` 原地写，不再先 `clone` 整表（旧实现强计数恒 2 ⇒ 每个
    /// 顶层 def 深拷一次整张 decl 表；port L07 c2fffd3f）。撞名报 redefine。
    pub fn fake_bind_mut(&mut self, x: Span<SmolStr>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<(), Error> {
        if self.decl.contains_key(x.data.as_str()) {
            return Err(Error(x.to_span().map(|_| format!("redefine {}", x.data)), vec![]));
        }
        Rc::make_mut(&mut self.decl).insert(
            x.data.clone(),
            (x.to_span(), Tm::Decl(x.clone()).into(), Val::Decl(x.clone(), List::new()).into(), a_quote, a),
        );
        Ok(())
    }

    pub fn new_binder(&self, x: Span<SmolStr>, a_quote: Rc<Tm>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl).into()),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Rc::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            names: Rc::clone(&self.names),
            name_mark: self.name_mark,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
        }
    }

    pub fn define(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            s.insert(x.data.clone(), Rc::new((self.lvl, (x.to_span(), va))));
            s.trail.len() as u32
        };
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Rc::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            names: Rc::clone(&self.names),
            name_mark,
            decl: self.decl.clone(),
            namespace: self.namespace.clone(),
        }
    }

    /// 持久化 `decl` 包装（保留旧 `&Cxt` 调用方）：浅克隆上下文后就地写。
    pub fn decl(&self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Result<Self, Error> {
        let mut cxt = self.clone();
        cxt.decl_mut(x, t, vt, a, va);
        Ok(cxt)
    }

    /// 就地注册一个顶层 decl（顺序声明路径专用，port L07 c2fffd3f）：
    /// 调用方持有 `Cxt` 所有权 ⇒ 表 `Rc` 强计数为 1 ⇒ `Rc::make_mut` 原地写，
    /// 不再深拷整表。重定义静默覆盖（与旧 `decl` 一致：其撞名检查曾注释）。
    pub fn decl_mut(&mut self, x: Span<SmolStr>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) {
        Rc::make_mut(&mut self.decl).insert(x.data.clone(), (x.to_span(), t, vt, a, va));
    }

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// src_names 的类型包 `VSub`；lvl / locals / pruning 不动——**槽位布局
    /// （= 运行时布局）不变**，被解变量仍在原槽位，读点经 force 推开看到解。
    /// σ 为空时零开销直通。
    ///
    /// 替代旧的 `update_cxt`/`refresh`（改写 env 槽 + 全量重引用）：解不再
    /// 改写既有值，只包在外面，消费点惰性展开——旧架构"已捕获旧上下文的值
    /// 过期、槽位错位"的 bug 族按构造消除。
    pub fn subst_cxt(&self, sub: &Rc<super::Subst>) -> Self {
        if sub.is_empty() {
            return self.clone();
        }
        let wrap = |v: &Rc<Val>| Rc::new(Val::VSub(v.clone(), sub.clone()));
        // 名字表按轨迹改写：现有条目（父链 + 本作用域）逐条换成包了 VSub 的
        // 新条目并记录旧值，`name_mark` 指到轨迹新长度；父上下文下次访问时
        // 惰性还原（与 bind/define 同一机制）。语义与旧的整表重建一致。
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            let entries: Vec<_> = s.map.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
            for (k, e) in entries {
                let (lvl, (span, ty)) = e.as_ref();
                let new_e = Rc::new((*lvl, (span.clone(), wrap(ty))));
                let prev = s.map.insert(k.clone(), new_e);
                s.trail.push((k, prev));
            }
            s.trail.len() as u32
        };
        Cxt {
            env: self.env.map(wrap),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            names: Rc::clone(&self.names),
            name_mark,
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
