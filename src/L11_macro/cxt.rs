use std::cell::RefCell;
use std::collections::HashSet;

use crate::parser_lib::ToSpan;

use super::{
    syntax::{Locals, Pruning},
    *,
};

/// 源码名表 + 撤销轨迹（L07 `d411debe` 的参考版对应物，双表版）。
///
/// 旧实现是**按值** `BiMap<String, Lvl, (Span<()>, Rc<VTy>)>`：`bind` /
/// `define` 各深拷两张 FxHashMap——n 个绑定器的精化 O(n²)。新实现为
/// "单张 shared 表 + 撤销轨迹 + 按 mark 惰性回退"：`bind`/`define` 只做
/// 一次双表插入 + 追加一条轨迹，O(1)；上下文退出不显式撤销，而是在
/// **下一次访问名字表前** 把轨迹裁回本上下文的 `name_mark`——语义与持久
/// 表一致（每个 Cxt 看到的名字集 = 创建时快照）。
#[derive(Debug)]
struct NameTrailEntry {
    /// 插入/覆盖的源码名（`Wrap` 式替换时为 None）。
    name: Option<String>,
    old_lvl: Option<Lvl>,
    lvl: Lvl,
    old_val: Option<(Span<()>, Rc<VTy>)>,
}

#[derive(Debug, Default)]
struct NameState {
    by_name: rustc_hash::FxHashMap<String, Lvl>,
    by_lvl: rustc_hash::FxHashMap<Lvl, (Span<()>, Rc<VTy>)>,
    trail: Vec<NameTrailEntry>,
}

impl NameState {
    fn unwind(&mut self, mark: u32) {
        debug_assert!(mark as usize <= self.trail.len(), "unwind: mark 超出轨迹");
        while self.trail.len() > mark as usize {
            let e = self.trail.pop().expect("unwind: 轨迹为空");
            if let Some(k) = e.name {
                match e.old_lvl {
                    Some(l) => {
                        self.by_name.insert(k, l);
                    }
                    None => {
                        self.by_name.remove(&k);
                    }
                }
            }
            match e.old_val {
                Some(v) => {
                    self.by_lvl.insert(e.lvl, v);
                }
                None => {
                    self.by_lvl.remove(&e.lvl);
                }
            }
        }
    }

    fn insert(&mut self, k: String, lvl: Lvl, val: (Span<()>, Rc<VTy>)) {
        let old_lvl = self.by_name.insert(k.clone(), lvl);
        let old_val = self.by_lvl.insert(lvl, val);
        self.trail.push(NameTrailEntry {
            name: Some(k),
            old_lvl,
            lvl,
            old_val,
        });
    }
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // Used for evaluation
    pub lvl: Lvl, // Used for unification
    pub locals: Locals,
    pub pruning: Pruning,
    /// 源码变量名 → (绑定层级, 类型值)，共享可变表（见 [`NameState`]）。
    /// 每次访问前先把轨迹裁回 `name_mark`，因此本上下文看到的名字集合恒等于
    /// 创建时的快照；`bind` 条目值仍是 `Rc<VTy>`（O(1)）。旧实现是按值
    /// `BiMap`：每次 bind/define 深拷两张表（def/n 层绑定器的 O(n²) 来源）。
    names: Rc<RefCell<NameState>>,
    /// 本上下文的名字表基线（轨迹长度）。
    name_mark: u32,
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
            names: Rc::new(RefCell::new(NameState::default())),
            name_mark: 0,
            decl: Rc::new(Default::default()),
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

    /// 名字表访问前统一入口：把共享轨迹裁回本上下文基线（惰性回滚）。
    #[inline]
    fn unwind_names(&self) {
        self.names.borrow_mut().unwind(self.name_mark);
    }

    /// 查一个源码局部名（局部 binder 优先于 decl 表）：返回
    /// `(绑定层级, span, 类型值)` 的拷贝（Rc 递增）。
    pub fn lookup_src(&self, n: &str) -> Option<(Lvl, Span<()>, Rc<VTy>)> {
        self.unwind_names();
        let s = self.names.borrow();
        let lvl = *s.by_name.get(n)?;
        let (sp, ty) = s.by_lvl.get(&lvl)?;
        Some((lvl, sp.clone(), ty.clone()))
    }

    pub fn bind(&self, x: Span<String>, a_quote: Rc<Tm>, a: Rc<Val>) -> Self {
        //println!("{} {x:?} {a:?} at {}", "bind".bright_purple(), self.lvl.0);
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            s.insert(x.data.clone(), self.lvl, (x.to_span(), a));
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

    /// 递归 def 占位插入（就地版，L07 `c2fffd3f` 同款）：调用方持有 `Cxt`
    /// 所有权、decl 表 `Rc` 强计数为 1 时 `Rc::make_mut` 原地写；被共享时
    /// 自动回退深拷贝，隔离语义不变。旧 `&self` 版先 `self.decl.clone()`
    /// 再 `make_mut` ⇒ 强计数恒为 2、每个顶层 def 深拷整表。
    pub fn fake_bind_mut(
        &mut self,
        x: Span<String>,
        a_quote: Rc<Tm>,
        a: Rc<Val>,
    ) -> Result<(), Error> {
        if self.decl.contains_key(&x.data) {
            return Err(Error(x.to_span().map(|_| format!("redefine {}", x.data))));
        }
        Rc::make_mut(&mut self.decl).insert(
            x.data.clone(),
            (
                x.to_span(),
                Tm::Decl(x.clone()).into(),
                Val::Decl(x.clone(), List::new()).into(),
                a_quote,
                a,
            ),
        );
        Ok(())
    }

    /// 持久化包装（保持旧 `&self` 接口）：浅克隆上下文后就地写。
    pub fn fake_bind(&self, x: Span<String>, a_quote: Rc<Tm>, a: Rc<Val>) -> Result<Self, Error> {
        let mut cxt = self.clone();
        cxt.fake_bind_mut(x, a_quote, a)?;
        Ok(cxt)
    }

    pub fn new_binder(&self, x: Span<String>, a_quote: Rc<Tm>) -> Self {
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

    pub fn define(&self, x: Span<String>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Self {
        //println!("{} {}\n{t:?}\n{vt:?}\n{a:?}\n{va:?}", "define".bright_purple(), x.data);
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            s.insert(x.data.clone(), self.lvl, (x.to_span(), va));
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

    /// 顶层声明登记（就地版，L07 `c2fffd3f` 同款）：撞名静默覆盖（旧
    /// `decl` 的注释掉的 redefine 检查保持原样）。
    pub fn decl_mut(&mut self, x: Span<String>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) {
        Rc::make_mut(&mut self.decl).insert(x.data.clone(), (x.to_span(), t, vt, a, va));
    }

    /// 持久化包装（保持旧 `&self` 接口）：浅克隆上下文后就地写。
    pub fn decl(&self, x: Span<String>, t: Rc<Tm>, vt: Rc<Val>, a: Rc<Ty>, va: Rc<VTy>) -> Result<Self, Error> {
        let mut cxt = self.clone();
        cxt.decl_mut(x, t, vt, a, va);
        Ok(cxt)
    }

    /// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx`）：env 槽与
    /// 名字表的类型包 `VSub`；lvl / locals / pruning / decl / namespace 不动
    /// ——**槽位布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经
    /// force 推开看到解。decl 表是全局声明登记（旧 `update_cxt` 也从不改写
    /// 它，故此处保持原样）。σ 为空时零开销直通。
    ///
    /// 名字表按轨迹改写（L07 `d411debe` 同款）：现有条目的类型逐条换成包了
    /// `VSub` 的新值并记录旧值，`name_mark` 指到轨迹新长度；父上下文下次
    /// 访问时惰性还原（与 `bind`/`define` 同一机制）。
    pub fn subst_cxt(&self, sub: &Rc<Subst>) -> Self {
        if sub.is_empty() {
            return self.clone();
        }
        let wrap = |v: &Rc<Val>| Rc::new(Val::VSub(v.clone(), sub.clone()));
        let name_mark = {
            let mut s = self.names.borrow_mut();
            s.unwind(self.name_mark);
            let lvls: Vec<Lvl> = s.by_lvl.keys().copied().collect();
            for l in lvls {
                let old = s.by_lvl.get(&l).cloned().expect("by_lvl key vanished");
                let newv = (old.0.clone(), wrap(&old.1));
                s.by_lvl.insert(l, newv);
                s.trail.push(NameTrailEntry {
                    name: None,
                    old_lvl: None,
                    lvl: l,
                    old_val: Some(old),
                });
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
