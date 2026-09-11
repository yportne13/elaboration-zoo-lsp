//! 指令数组求值：项被**编译**成对齐的 `&[Ins]`（连续内存、定长枚举直读，
//! 无指针追逐），求值与 quote 的 Clo 重入都用同一个指令解释器。
//!
//! 值 / 环境 / 结果树仍在 bump 里（与 `bump_tree` 同构）——只替换"项
//! 访问"这一层：指针式 AST（`&Bt`）换成数组 + 下标。
//!
//! `Ins` 布局（前缀序，每条 16B）：
//!
//! ```text
//! Idx(i)             de Bruijn 索引
//! Lam(body_ip, len)  闭包体入口（指令偏移）与体指令数；eval 直接用 body_ip
//!                    跳转，`len` 当前只记录、无人读取（保留字段）
//! App(f_len)         函数表达式在 ip+1 起、长 f_len 条指令；实参紧随其后
//! ```
//!
//! 与 `bytes_env_list` 的字节码差异：字节码是 tag + 变长数据的逐字节
//! 解析，这里是定长对齐的枚举直读（无字节组装，可预取）。

use bumpalo::Bump;

use super::Term;

/// 编译产物：连续指令数组（前缀序）。
#[derive(Clone, Copy)]
pub(crate) enum Ins {
    Idx(usize),
    Lam(u32, u32),
    App(u32),
}

/// 把 `Box<Term>` 树编译成指令数组（基准里放在计时外，与 import 同口径）。
pub(crate) fn compile(t: &Term) -> Vec<Ins> {
    let mut out = Vec::new();
    compile_into(t, &mut out);
    out
}

fn compile_into(t: &Term, out: &mut Vec<Ins>) {
    match t {
        Term::Idx(i) => out.push(Ins::Idx(*i)),
        Term::Lam(body) => {
            out.push(Ins::Lam(0, 0)); // 占位
            let body_ip = out.len() as u32; // 体紧跟 Lam 指令
            let start = out.len();
            compile_into(body, out);
            let len = (out.len() - start) as u32;
            out[body_ip as usize - 1] = Ins::Lam(body_ip, len);
        },
        Term::App(f, a) => {
            out.push(Ins::App(0)); // 占位
            let f_start = out.len();
            compile_into(f, out);
            let f_len = (out.len() - f_start) as u32;
            compile_into(a, out);
            out[f_start - 1] = Ins::App(f_len);
        },
    }
}

/// bump 内分配的环境节点（持久链表）。
struct Env<'a> {
    val: Val<'a>,
    next: Option<&'a Env<'a>>,
}

/// bump 内分配的值。
#[derive(Clone)]
enum Val<'a> {
    Lvl(usize),
    Clo(Option<&'a Env<'a>>, u32), // 闭包：环境 + 体指令入口
    App(&'a Val<'a>, &'a Val<'a>),
}

/// bump 内分配的结果树（与 `bump_arena::Bt` 同构）。
pub(crate) enum Bt<'a> {
    Idx(usize),
    Lam(&'a Bt<'a>),
    App(&'a Bt<'a>, &'a Bt<'a>),
}

fn nth<'a>(env: Option<&'a Env<'a>>, idx: usize) -> &'a Val<'a> {
    let mut e = env.expect("de Bruijn 越界：闭项不应查空环境");
    for _ in 0..idx {
        e = e.next.expect("de Bruijn 越界：闭项不应查越深");
    }
    &e.val
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
fn eval<'a>(bump: &'a Bump, env: Option<&'a Env<'a>>, prog: &'a [Ins], ip: usize) -> Val<'a> {
    match prog[ip] {
        Ins::Idx(i) => nth(env, i).clone(),
        Ins::Lam(body_ip, _len) => Val::Clo(env, body_ip),
        Ins::App(f_len) => {
            // 顺序求值（先函数后实参），与 bump_arena 同序
            let vf = eval(bump, env, prog, ip + 1);
            let va = eval(bump, env, prog, ip + 1 + f_len as usize);
            apply_val(bump, prog, vf, va)
        },
    }
}

/// apply_val vf va =
///      match vf with
///      | VLam(env, body) -> eval (va :: env) body
///      | _               -> VApp(vf, va)
fn apply_val<'a>(bump: &'a Bump, prog: &'a [Ins], vf: Val<'a>, va: Val<'a>) -> Val<'a> {
    match vf {
        Val::Clo(env, body_ip) => {
            let node = bump.alloc(Env { val: va, next: env });
            eval(bump, Some(node), prog, body_ip as usize)
        },
        _ => {
            // 与 `bump_arena::apply_val` 的中性分支对齐：一次分配 [Val; 2]
            // （相邻存放，单次对齐/检查/推进）再拆引用。曾分别 alloc 两次，
            // 使本变体相对 `bump_tree` 多出一个混杂变量（见 bench 对照注释）。
            let arr = bump.alloc([vf, va]);
            Val::App(&arr[0], &arr[1])
        },
    }
}

/// 对已编译的项做 NBE（基准计时对象；compile 在计时外）。
/// `bump` 与 `prog` 的生命周期由调用方统一锚定。
pub(crate) fn normalize_imported<'a>(bump: &'a Bump, prog: &'a [Ins]) -> &'a Bt<'a> {
    quote(bump, prog, 0, eval(bump, None, prog, 0))
}

/// 把 bump 内结果树转回 `Box<Term>`（递归；仅用于断言/消费侧，不计时）。
pub(crate) fn export(t: &Bt) -> Term {
    match t {
        Bt::Idx(i) => Term::Idx(*i),
        Bt::Lam(b) => Term::Lam(Box::new(export(b))),
        Bt::App(f, a) => Term::App(Box::new(export(f)), Box::new(export(a))),
    }
}

/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
fn quote<'a>(bump: &'a Bump, prog: &'a [Ins], level: usize, value: Val<'a>) -> &'a Bt<'a> {
    match value {
        Val::Lvl(lvl) => bump.alloc(Bt::Idx(level - lvl - 1)),
        Val::Clo(env, body_ip) => {
            let node = bump.alloc(Env { val: Val::Lvl(level), next: env });
            let body = quote(bump, prog, level + 1, eval(bump, Some(node), prog, body_ip as usize));
            bump.alloc(Bt::Lam(body))
        },
        Val::App(vf, va) => {
            let f = quote(bump, prog, level, vf.clone());
            let a = quote(bump, prog, level, va.clone());
            bump.alloc(Bt::App(f, a))
        }
    }
}

#[cfg(test)]
mod tests {
    use bumpalo::Bump;

    use super::super::term::{self, Term};
    use super::{compile, export, normalize_imported};

    /// import + normalize + 转回 `Term`（本变体没有 `Term -> Term` 便捷入口）。
    fn norm(t: Term) -> Term {
        let bump = Bump::new();
        let prog = compile(&t);
        export(normalize_imported(&bump, &prog))
    }

    #[test]
    fn church_pair_ok() {
        assert_eq!(norm(term::church_pair(5)), term::church(10));
    }

    #[test]
    fn already_normal_right_chain() {
        // λf.λx. f (f (f (f x)))：已正态，归一化须逐字还原
        let input = {
            let mut t = Term::Idx(0);
            for _ in 0..4 {
                t = Term::App(Box::new(Term::Idx(1)), Box::new(t));
            }
            Term::Lam(Box::new(Term::Lam(Box::new(t))))
        };
        assert_eq!(norm(input.clone()), input);
    }

    #[test]
    fn beta_under_binder() {
        // λg. (λx. x) g → λg. g
        let inner = Term::App(Box::new(Term::Lam(Box::new(Term::Idx(0)))), Box::new(Term::Idx(0)));
        let input = Term::Lam(Box::new(inner));
        assert_eq!(norm(input), Term::Lam(Box::new(Term::Idx(0))));
    }

    #[test]
    fn interleaved_chains_fallback() {
        // λf.λg.λx. (λy. (f y) (g y)) (f x) → λf.λg.λx. (f (f x)) (g (f x))
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let inner = app(app(idx(3), idx(0)), app(idx(2), idx(0)));
        let input = lam(lam(lam(app(lam(inner), app(idx(2), idx(0))))));
        let expect = lam(lam(lam(app(
            app(idx(2), app(idx(2), idx(0))),
            app(idx(1), app(idx(2), idx(0))),
        ))));
        assert_eq!(norm(input), expect);
    }

    #[test]
    fn chain_beta_fork() {
        // (λf.λx. f (f x)) (λu.u) → λx. x：compiled 的 Clo 重入走同一解释器
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let id = lam(idx(0));
        let church2 = lam(lam(app(idx(1), app(idx(1), idx(0)))));
        let input = app(church2, id.clone());
        assert_eq!(norm(input), id);
    }

    #[test]
    fn chain_mixed_heads() {
        // λf.λg.λx. f (g x)：连续右链、链头不同
        let idx = |i: usize| Term::Idx(i);
        let app = |f: Term, a: Term| Term::App(Box::new(f), Box::new(a));
        let lam = |b: Term| Term::Lam(Box::new(b));
        let input = lam(lam(lam(app(idx(2), app(idx(1), idx(0))))));
        assert_eq!(norm(input.clone()), input);
    }
}