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
//! Lam(body_ip, len)  闭包体入口（指令偏移）与体指令数（len 供 eval 跳过）
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
            let vf = bump.alloc(vf);
            let va = bump.alloc(va);
            Val::App(vf, va)
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
        },
    }
}