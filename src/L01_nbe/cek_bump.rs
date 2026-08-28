//! CEK 机 + bump 全分配：栈安全方向的结合实验。
//!
//! `cek`（Rc 链表 + 字节码 + 全迭代）是唯一不爆栈的变体但慢 ~11×；
//! `bump_tree`（bump 全分配 + 递归）是速度王但深度受进程栈限。这里把
//! 两者的长处拼起来：**求值 = 显式 kont 栈的 CEK 机（深度不受限），
//! 值/环境/结果 = bump 引用式（零 malloc）**。
//!
//! quote 用任务栈迭代（`bump_arena::quote_bump_iter`）——递归版在这个
//! 场景会以结果树深度爆栈。实测在第 5 轮 readme：速度贴近 `bump_tree`，
//! 深度与 `cek` 同级（n = 26 万不爆栈）。

use bumpalo::Bump;

use super::bump_arena::{self, Bt, Bv, Env};
use super::term::Term;

/// continuation 栈条目。
enum Kont<'a> {
    /// 函数已求得，实参待求值（实参项 + 其求值环境）。
    Fun(&'a Bt<'a>, Option<&'a Env<'a>>),
    /// 实参已求得（值），等函数来应用。
    Arg(Bv<'a>),
}

/// eval env tm = …（递归定义，见 `cek.rs` 的转移规则注释）。
/// bump 版的差异：env 是 bump 内持久链表（`&Env`），值在 bump 内引用式。
fn eval<'a>(bump: &'a Bump, env0: Option<&'a Env<'a>>, tm0: &'a Bt<'a>) -> Bv<'a> {
    let mut env = env0;
    let mut tm: Option<&'a Bt<'a>> = Some(tm0);
    let mut val: Option<Bv<'a>> = None;
    let mut kont: Vec<Kont<'a>> = Vec::new();

    loop {
        if let Some(t) = tm.take() {
            match t {
                Bt::Idx(i) => val = Some(bump_arena::nth(env, *i).clone()),
                Bt::Lam(body) => val = Some(Bv::Clo(env, body)),
                Bt::App(f, a) => {
                    kont.push(Kont::Fun(a, env));
                    tm = Some(f);
                },
            }
            continue; // 转值状态
        }

        let v = val.take().expect("值状态必须持有值");
        match kont.pop() {
            Some(Kont::Fun(a, e)) => {
                env = e;
                tm = Some(a);
                kont.push(Kont::Arg(v));
            },
            Some(Kont::Arg(f)) => match f {
                Bv::Clo(e, body) => {
                    let node = bump.alloc(Env { val: v, next: e });
                    env = Some(node);
                    tm = Some(body);
                },
                // 中立项：一次分配 [Bv; 2]（相邻存放），拆引用
                f => {
                    let arr = bump.alloc([f, v]);
                    val = Some(Bv::App(&arr[0], &arr[1]));
                },
            },
            None => return v,
        }
    }
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
/// eval（CEK 迭代）+ quote（任务栈迭代）都深度无上限。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    bump_arena::quote_bump_iter(bump, eval(bump, None, tm))
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import(&bump, &t);
    bump_arena::export(normalize_imported(&bump, tm))
}