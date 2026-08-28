//! `bump_tree` 递归的直接改造（回答"栈安全只有 cek 一种做法吗"——不是）。
//!
//! bump_tree 的 eval 递归结构是"求 f → 求 a → apply"，β 归约是纯尾调用。
//! 把这条链压平为**双栈**：
//!
//! ```text
//! work 栈：Tm(&Bt, env)     待求值的项
//!         Apply            值栈顶两个值做一次应用（每个 App 推入一枚）
//! vals 栈：Bv              已求出的值（LIFO 与 work 的 Apply 配对）
//! ```
//!
//! 与 `cek_bump` 的通用 CEK kont 栈（`Fun`/`Arg` 两条）相比：栈条目种类
//! 更少、β 归约不再产生额外条目（归约 = 直接推入体的 `Tm`，天然循环）。
//! quote 复用 `bump_arena::quote_bump_iter`（任务栈）。

use bumpalo::Bump;

use super::bump_arena::{self, Bt, Bv, Env};
use super::term::Term;

/// 双栈迭代 eval：与 `bump_arena::eval` 语义相同（先函数后实参）。
fn eval<'a>(bump: &'a Bump, env0: Option<&'a Env<'a>>, tm0: &'a Bt<'a>) -> Bv<'a> {
    enum W<'a> {
        Tm(&'a Bt<'a>, Option<&'a Env<'a>>),
        Apply,
    }
    let mut work: Vec<W<'a>> = vec![W::Tm(tm0, env0)];
    let mut vals: Vec<Bv<'a>> = Vec::new();
    while let Some(w) = work.pop() {
        match w {
            W::Tm(tm, env) => match tm {
                Bt::Idx(i) => vals.push(bump_arena::nth(env, *i).clone()),
                Bt::Lam(body) => vals.push(Bv::Clo(env, body)),
                Bt::App(f, a) => {
                    work.push(W::Apply);
                    work.push(W::Tm(a, env));
                    work.push(W::Tm(f, env));
                },
            },
            W::Apply => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                match vf {
                    // β 归约是尾调用：直接推入体，继续循环（无额外栈条目）
                    Bv::Clo(e, body) => {
                        let node = bump.alloc(Env { val: va, next: e });
                        work.push(W::Tm(body, Some(node)));
                    },
                    // 中立项：一次分配 [Bv; 2]（相邻存放），拆引用后回值栈
                    f => {
                        let arr = bump.alloc([f, va]);
                        vals.push(Bv::App(&arr[0], &arr[1]));
                    },
                }
            },
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

/// 对已导入 bump 的项做 NBE（基准计时对象；import 在计时外）。
/// eval（双栈迭代）+ quote（任务栈迭代）都深度无上限。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, tm: &'a Bt<'a>) -> &'a Bt<'a> {
    bump_arena::quote_bump_iter(bump, eval(bump, None, tm))
}

/// 便捷入口：import + normalize 一步完成（计时含转换成本）。
pub(crate) fn normalize(t: Term) -> Term {
    let bump = Bump::new();
    let tm = bump_arena::import(&bump, &t);
    bump_arena::export(normalize_imported(&bump, tm))
}