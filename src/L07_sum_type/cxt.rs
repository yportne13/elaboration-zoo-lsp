use std::{collections::HashMap, rc::Rc};

use crate::{list::List, parser_lib::Span};
use smol_str::SmolStr;

use super::{
    Closure, Env, Ix, Lvl, Tm, Ty, Val, VTy,
    empty_span,
    parser::syntax::Icit,
    syntax::{Locals, Pruning},
};

/// 全局 decl 表：名字 → (类型值, WHNF 值)。
///
/// 顶层定义（def / enum / 构造子）都登记在这里；项层引用用 `Tm::Decl(名字)`，
/// 求值时查表取缓存的 WHNF。递归通过"先插入指向自身的占位值、检查完再覆盖"实现。
pub type Decls = HashMap<SmolStr, DeclEntry>;

#[derive(Debug, Clone)]
pub struct DeclEntry {
    pub ty: VTy,
    pub val: Val,
}

#[derive(Debug, Clone)]
pub struct Cxt {
    pub env: Env, // 求值环境（局部变量，内层在前）
    pub lvl: Lvl, // 下一个 fresh 层级（unify / quote 用）
    pub locals: Locals,
    pub pruning: Pruning, // 与 env 一一对应：Some(icit) = 该槽是待插入的隐式参数
    pub src_names: HashMap<String, (Lvl, VTy)>,
    pub decl: Rc<Decls>,
}

impl Cxt {
    pub fn new() -> Self {
        Self::empty()
            .decl_insert(
                "String",
                DeclEntry {
                    ty: Val::U,
                    val: Val::LiteralType,
                },
            )
            .decl_insert(
                "string_concat",
                DeclEntry {
                    ty: Val::Pi(
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
                    val: Val::Lam(
                        empty_span("x".to_owned()),
                        Icit::Expl,
                        Closure(
                            List::new(),
                            Box::new(Tm::Lam(
                                empty_span("y".to_owned()),
                                Icit::Expl,
                                Box::new(Tm::Prim(SmolStr::new("string_concat"))),
                            )),
                        ),
                    ),
                },
            )
    }

    pub fn empty() -> Self {
        Cxt {
            env: List::new(),
            lvl: Lvl(0),
            locals: Locals::Here,
            pruning: List::new(),
            src_names: HashMap::new(),
            decl: Rc::new(HashMap::new()),
        }
    }

    pub fn decl(&self) -> &Decls {
        &self.decl
    }

    pub fn decl_get(&self, k: &str) -> Option<&DeclEntry> {
        self.decl.get(k)
    }

    /// 写入一个 decl。写时复制：Rc 共享时才克隆整表，父上下文不受影响——
    /// 这正是递归定义需要的"占位只对本定义的检查可见"。
    pub fn decl_insert(&self, k: impl Into<SmolStr>, e: DeclEntry) -> Self {
        let mut decl = self.decl.clone();
        Rc::make_mut(&mut decl).insert(k.into(), e);
        Cxt {
            decl,
            env: self.env.clone(),
            lvl: self.lvl,
            locals: self.locals.clone(),
            pruning: self.pruning.clone(),
            src_names: self.src_names.clone(),
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

    /// 引入一个源码变量（模式绑定 / λ 参数 / Π 域）：env 压入 fresh rigid。
    pub fn bind(&self, x: Span<String>, a_quote: Tm, a: VTy) -> Self {
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, a));
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names,
            decl: self.decl.clone(),
        }
    }

    /// 引入一个"编译器插入"的绑定器（非 λ 项 against 隐式 Π 时）：不进 src_names。
    pub fn new_binder(&self, x: Span<String>, a_quote: Tm) -> Self {
        Cxt {
            env: self.env.prepend(Val::vvar(self.lvl)),
            lvl: self.lvl + 1,
            locals: Locals::Bind(Box::new(self.locals.clone()), x, a_quote),
            pruning: self.pruning.prepend(Some(Icit::Expl)),
            src_names: self.src_names.clone(),
            decl: self.decl.clone(),
        }
    }

    /// let 绑定：env 压入定义的值，pruning 对应槽为 None（后续隐式插入不再经过它）。
    pub fn define(&self, x: Span<String>, t: Tm, vt: Val, a: Ty, va: VTy) -> Self {
        let mut src_names = self.src_names.clone();
        src_names.insert(x.data.clone(), (self.lvl, va));
        Cxt {
            env: self.env.prepend(vt),
            lvl: self.lvl + 1,
            locals: Locals::Define(Box::new(self.locals.clone()), x, a, t),
            pruning: self.pruning.prepend(None),
            src_names,
            decl: self.decl.clone(),
        }
    }

    /// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
    /// 这些是模式特化方程可以求解的对象。let 定义槽（槽里是值不是
    /// vvar）天然不在其中。
    pub fn bind_slots(&self) -> Vec<Lvl> {
        let n = self.lvl.0;
        self.env
            .iter()
            .enumerate()
            .filter_map(|(i, v)| match v {
                Val::Rigid(l, sp) if sp.is_empty() && l.0 + (i as u32) + 1 == n => Some(*l),
                _ => None,
            })
            .collect()
    }
}
