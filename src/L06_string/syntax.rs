use std::rc::Rc;

use crate::{list::List, parser_lib::Span};

use super::{parser::syntax::Icit, Tm, Ty};

pub type Pruning = List<Option<Icit>>;

/// 局部 telescope（持久栈：只压不退）。脊与载荷都是 `Rc`（对齐 L13
/// `syntax.rs` 的同名形态）：旧版 `Box` 脊 + 按值 `Ty`/`Tm` 载荷让每次
/// `bind`/`define` 深拷整条链（节点数 = 作用域深度 D），strchain k=11
/// （D=4096）参考版实测 1215 ms（同负载 L07/L08 参考版 123/124 ms）。
/// Rc 化后扩展 O(1)（引用计数递增），载荷只在 `close_ty` 取用时按层取出；
/// 全程只读共享、无 `&mut` 别名，语义零变化。
#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Rc<Locals>, Span<String>, Rc<Ty>, Rc<Tm>),
    Bind(Rc<Locals>, Span<String>, Rc<Ty>),
}

/// 收 `&Locals` 借用遍历（旧版按值消耗整条链，调用方必须先深拷一份）。
pub fn close_ty(mcl: &Locals, b: Ty) -> Ty {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => close_ty(
            mcl,
            Tm::Pi(x.clone(), Icit::Expl, Box::new((**a).clone()), Box::new(b)),
        ),
        Locals::Define(mcl, x, a, t) => close_ty(
            mcl,
            Tm::Let(
                x.clone(),
                Box::new((**a).clone()),
                Box::new((**t).clone()),
                Box::new(b),
            ),
        ),
    }
}

/// `Locals` 链是否**全为 define 槽**（无 Bind）——`fresh_meta` 闭类型快捷的
/// 守卫：Bind 槽会把闭类型多出一层显式 Π，结果类型本身不同，不能跳过构造。
/// 逐节点走查 O(D)（零分配；孪生版把同一查询缓存在 `LCons.prefix` 上 O(1)，
/// 参考版按需走查——比被省掉的 O(D²) 链求值低两个数量级）。
pub fn all_define_slots(mut l: &Locals) -> bool {
    loop {
        match l {
            Locals::Here => return true,
            Locals::Bind(..) => return false,
            Locals::Define(next, ..) => l = next,
        }
    }
}

/// `q` 的求值是否与 env / decl 表**都**无关（`fresh_meta` 快捷的第二半守卫）：
/// - 无 `Var`（de Bruijn 查 env）、无 `AppPruning`（按 scope 掩码应用，同样读
///   env）⇒ `eval env q` 对任何 env 同值；
/// - 无 `Decl`（查 decl 表、且可能触发 prim——prim 能读写 `mutable_map` /
///   文件，而链上载荷的重求值也会触发 prim）⇒ 略去载荷求值不影响 q 的值。
///
/// 保守起见**任何** `Var`（含被内层 binder 绑定的）与任何 `Decl` 都算不纯，
/// 宁可回落全构造。
pub fn env_independent(t: &Tm) -> bool {
    match t {
        Tm::Var(_) | Tm::AppPruning(..) | Tm::Decl(_) => false,
        Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => true,
        Tm::Lam(_, _, b) => env_independent(b),
        Tm::App(f, a, _) => env_independent(f) && env_independent(a),
        Tm::Pi(_, _, a, b) => env_independent(a) && env_independent(b),
        Tm::Let(_, a, t, u) => env_independent(a) && env_independent(t) && env_independent(u),
    }
}
