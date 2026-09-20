use std::rc::Rc;

use crate::{list::List, parser_lib::Span};

use super::{Tm, Ty, parser::syntax::Icit};

pub type Pruning = List<Option<Icit>>;

/// telescope 链（`Cxt.locals` 累积的 binder/define 栈，头 = 最内层）。
///
/// **脊 Box → Rc（2026-09-20 参考版 O(D²) 修复，L09 同款处置）**：旧表示是
/// `Box` 脊（载荷已是 Rc），`bind`/`new_binder`/`define`/`fake_bind` 每次都
/// `self.locals.clone()` **深拷整条链**——D = 已累积槽数，链节点逐次分配，
/// 顶层 def 每声明付两次 O(D)，总计 O(D²)（L10 strchain k=11 实测 929ms，
/// 孪生同负载 3.2ms；L09 骨架同源，见 `docs/perf-debt-2026-09-12.md` P2）。
///
/// Rc 脊后节点**构造后不变**、被所有派生 Cxt 共享：prepend 与克隆都是 O(1)
/// 指针操作，语义不变（链只在头部增长，无人改写既有节点；`close_ty` 走
/// 引用读，载荷本就是 Rc、逐节零拷贝）。`Cxt.locals` 随之持 `Rc<Locals>`。
#[derive(Debug, Clone)]
pub enum Locals {
    Here,
    Define(Rc<Locals>, Span<String>, Rc<Ty>, Rc<Tm>),
    Bind(Rc<Locals>, Span<String>, Rc<Ty>),
}

/// 沿 telescope 链把项 `b` 闭包成类型：Bind → 显式 Π、Define → Let。
///
/// **走引用（2026-09-20 参考版 O(D²) 修复）**：旧签名按值消费 `Locals`
/// （`*mcl` 逐节移出），唯一调用点只能先 `cxt.locals.clone()` 把整条链深拷
/// 一份再交出来——fresh_meta 每挂一个洞付 O(D)（`docs/perf-debt-2026-09-12.md`
/// D-F1 的参考版侧残余）。链改为共享 Rc 脊后按引用走查，每节只克隆 Rc
/// 载荷（引用计数），链本身零分配。
pub fn close_ty(mcl: &Locals, b: Rc<Ty>) -> Rc<Ty> {
    match mcl {
        Locals::Here => b,
        Locals::Bind(mcl, x, a) => {
            close_ty(mcl, Tm::Pi(x.clone(), Icit::Expl, a.clone(), b).into())
        }
        Locals::Define(mcl, x, a, t) => {
            close_ty(mcl, Tm::Let(x.clone(), a.clone(), t.clone(), b).into())
        }
    }
}
