use std::{collections::HashMap, rc::Rc};

use crate::{list::List, parser_lib::Span};
use smol_str::SmolStr;

use super::{
    Closure, Env, Infer, Ix, Lvl, Tm, Ty, Val, VTy,
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

/// `(name : dom) -> cod` 的 Tm 层 Π 链（builtin 注册期类型描述用）。
fn tm_pi(name: &str, dom: Tm, cod: Tm) -> Tm {
    Tm::Pi(
        empty_span(name.to_owned()),
        Icit::Expl,
        Box::new(dom),
        Box::new(cod),
    )
}

/// `(String ->)^n ret` 的 Tm 层 Π 链——builtin 参数类型全部是 String。
fn str_pi(params: &[&str], ret: Tm) -> Tm {
    params
        .iter()
        .rev()
        .fold(ret, |cod, name| tm_pi(name, Tm::LiteralType, cod))
}

/// `string_to_global_type Var(ix)`——de Bruijn 引用第 ix 个前导参数
/// （动态类型：check 期求值时查 decl 表取登记类型；未登记名 → 卡住
/// Decl 逃逸舱口）。
fn st2g_app(ix: u32) -> Tm {
    Tm::App(
        Box::new(Tm::Decl(SmolStr::new("string_to_global_type"))),
        Box::new(Tm::Var(Ix(ix))),
        Icit::Expl,
    )
}

impl Cxt {
    /// builtin 注册表（L06 全组移植）：`String` 类型 + string /
    /// report_check_issue / string_to_global_type / 可变全局族 / 文件 IO
    /// 族。归约统一在 `Infer::force` 的 `prim_reduce`（L07 的 force 触发
    /// 语义；L06 是应用时触发）。
    ///
    /// 注册顺序敏感：`string_to_global_type` 必须先于引用它的 global 族
    /// （其类型的闭包体在 check 期才查表，但防御性保持 L06 顺序）。
    pub fn new(infer: &Infer) -> Self {
        let cxt = Self::empty().decl_insert(
            "String",
            DeclEntry {
                ty: Val::U,
                val: Val::LiteralType,
            },
        );
        cxt.add_builtin(infer, "string_concat", str_pi(&["x", "y"], Tm::LiteralType))
            .add_builtin(infer, "str_eq", str_pi(&["x", "y"], Tm::LiteralType))
            .add_builtin(infer, "str_indent2", str_pi(&["x"], Tm::LiteralType))
            .add_builtin(
                infer,
                "report_check_issue",
                str_pi(&["code", "module", "signal", "message"], Tm::U),
            )
            .add_builtin(infer, "string_to_global_type", str_pi(&["x"], Tm::U))
            .add_builtin(
                infer,
                "create_global",
                tm_pi("x", Tm::LiteralType, tm_pi("y", st2g_app(0), Tm::U)),
            )
            .add_builtin(
                infer,
                "change_mutable",
                tm_pi(
                    "x",
                    Tm::LiteralType,
                    tm_pi("f", tm_pi("_", st2g_app(0), st2g_app(1)), Tm::U),
                ),
            )
            .add_builtin(
                infer,
                "get_global",
                tm_pi("x", Tm::LiteralType, st2g_app(0)),
            )
            .add_builtin(
                infer,
                "get_global_default",
                tm_pi(
                    "x",
                    Tm::LiteralType,
                    tm_pi("z", st2g_app(0), st2g_app(1)),
                ),
            )
            .add_builtin(
                infer,
                "change_mutable_default",
                tm_pi(
                    "x",
                    Tm::LiteralType,
                    tm_pi(
                        "f",
                        tm_pi("_", st2g_app(0), st2g_app(1)),
                        tm_pi("z", st2g_app(1), Tm::U),
                    ),
                ),
            )
            .add_builtin(
                infer,
                "file_read_all_text",
                str_pi(&["path"], Tm::LiteralType),
            )
            .add_builtin(
                infer,
                "file_write_all_text",
                str_pi(&["path", "content"], Tm::U),
            )
            .add_builtin(
                infer,
                "file_append_all_text",
                str_pi(&["path", "content"], Tm::U),
            )
            .add_builtin(infer, "file_exists", str_pi(&["path"], Tm::LiteralType))
            .add_builtin(infer, "file_delete", str_pi(&["path"], Tm::U))
    }

    /// 注册一个 builtin：类型在 Tm 层描述，经 `infer.eval` 求值成 Π 链值
    /// （只有最外层域被立即求值——恒为 String 常量；引用参数的内层域留在
    /// 闭包里到 check 期才解）；值 = λ 参数链 → `Tm::Prim(name)`，应用满
    /// 元数后由 `force` 的 `prim_reduce` 归约。
    fn add_builtin(self, infer: &Infer, name: &str, ty_tm: Tm) -> Self {
        let ty = infer.eval(&self.decl, &List::new(), ty_tm.clone());
        // 值 = λ 参数链 → Prim(name)；参数名从类型的 Π 链取（与域同序）
        let mut names = Vec::new();
        let mut cur = &ty_tm;
        while let Tm::Pi(n, _, _, body) = cur {
            names.push(n.data.clone());
            cur = body;
        }
        let mut val = Tm::Prim(SmolStr::new(name));
        for p in names.iter().rev() {
            val = Tm::Lam(empty_span(p.clone()), Icit::Expl, Box::new(val));
        }
        let val = infer.eval(&self.decl, &List::new(), val);
        self.decl_insert(SmolStr::new(name), DeclEntry { ty, val })
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
