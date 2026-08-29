//! L02 — 双向类型检查 + 闭包/de Bruijn 求值（elaboration zoo L02
//! `typecheck-closures-debruijn` 的 Rust 移植，规格见 elaboration-zoo 上游
//! 同名层的 `Main.hs`）。
//!
//! 本文件是**参考实现**（与 L03 同一代码风格：`Box<Tm>` 项、`List` Rc 持久
//! 环境、递归 eval/quote），语义与 Main.hs 一一对应；极致性能版见
//! [`bump_spine_iter`]（L01 调研成果的移植），两版输出逐字节一致（互检测试）。
//!
//! 与 L03（holes）的语义差别：没有 meta/ hole，只有 `check`/`infer` 双向
//! 走廊 + beta-eta `conv`；`RLam` 只在 `VPi` 下可检查，否则报"无法推断"。

pub(crate) mod bump_spine_iter;
pub(crate) mod parser;

use parser::Raw;

use crate::list::List;
use crate::parser_lib::Span;

// syntax
// --------------------------------------------------------------------------------

/// De Bruijn 索引。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Ix(u32);

/// De Bruijn 层级。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lvl(u32);

impl std::ops::Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

type Name = Span<String>;

/// 表面语法经 elaboration 产出的核心语法。
#[derive(Debug, Clone)]
enum Tm {
    Var(Ix),
    Lam(Name, Box<Tm>),
    App(Box<Tm>, Box<Tm>),
    U,
    Pi(Name, Box<Ty>, Box<Ty>),
    Let(Name, Box<Ty>, Box<Tm>, Box<Tm>),
}

type Ty = Tm;

// values
// --------------------------------------------------------------------------------

type Env = List<Val>;

#[derive(Debug, Clone)]
struct Closure(Env, Box<Tm>);

type VTy = Val;

/// 中性应用的两个子值用 `Rc` 共享：`eval(Var x)` 会 clone 环境里的值，
/// 而 let 绑定的 church 数一类的中性链会被 β-级联反复引用——`Box` 树的
/// clone 是 O(子树) 深拷贝（church 翻倍负载实测 O(n²)），`Rc` 的 clone
/// 是引用计数（Haskell 原版的 GC 共享在此处的对应物；L03 值表示同款）。
#[derive(Debug, Clone)]
enum Val {
    VVar(Lvl),
    VApp(Rc<Val>, Rc<Val>),
    VLam(Name, Closure),
    VPi(Name, Box<VTy>, Closure),
    VU,
}

use std::rc::Rc;

// `($$) (Closure env t) ~u = eval (u:env) t`（Haskell 里是 infixl 8 的 `$$`）
fn closure_apply(clo: &Closure, u: Val) -> Val {
    eval(&clo.0.prepend(u), &clo.1)
}

fn eval(env: &Env, tm: &Tm) -> Val {
    match tm {
        Tm::Var(Ix(x)) => env
            .iter()
            .nth(*x as usize)
            .expect("de Bruijn 越界：闭项不应查越深")
            .clone(),
        Tm::App(t, u) => match (eval(env, t), eval(env, u)) {
            (Val::VLam(_, clo), u) => closure_apply(&clo, u),
            (t, u) => Val::VApp(Rc::new(t), Rc::new(u)),
        },
        Tm::Lam(x, t) => Val::VLam(x.clone(), Closure(env.clone(), t.clone())),
        Tm::Pi(x, a, b) => Val::VPi(x.clone(), Box::new(eval(env, a)), Closure(env.clone(), b.clone())),
        Tm::Let(_, _, t, u) => {
            let vt = eval(env, t);
            eval(&env.prepend(vt), u)
        }
        Tm::U => Val::VU,
    }
}

fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
    Ix(l.0 - x.0 - 1)
}

fn quote(l: Lvl, v: &Val) -> Tm {
    match v {
        Val::VVar(x) => Tm::Var(lvl2ix(l, *x)),
        Val::VApp(t, u) => Tm::App(Box::new(quote(l, t)), Box::new(quote(l, u))),
        Val::VLam(x, t) => Tm::Lam(
            x.clone(),
            Box::new(quote(l + 1, &closure_apply(t, Val::VVar(l)))),
        ),
        Val::VPi(x, a, b) => Tm::Pi(
            x.clone(),
            Box::new(quote(l, a)),
            Box::new(quote(l + 1, &closure_apply(b, Val::VVar(l)))),
        ),
        Val::VU => Tm::U,
    }
}

fn nf(env: &Env, t: &Tm) -> Tm {
    quote(Lvl(env.size as u32), &eval(env, t))
}

/// Beta-eta 转换检查。前提：两个值的类型相同。
fn conv(l: Lvl, t: &Val, u: &Val) -> bool {
    match (t, u) {
        (Val::VU, Val::VU) => true,

        (Val::VPi(_, a, b), Val::VPi(_, a2, b2)) => {
            conv(l, a, a2)
                && conv(
                    l + 1,
                    &closure_apply(b, Val::VVar(l)),
                    &closure_apply(b2, Val::VVar(l)),
                )
        }

        (Val::VLam(_, t), Val::VLam(_, t2)) => conv(
            l + 1,
            &closure_apply(t, Val::VVar(l)),
            &closure_apply(t2, Val::VVar(l)),
        ),

        // eta：λ 与中性项比较，两边都应用到同一个新变量
        (Val::VLam(_, t), _) => conv(
            l + 1,
            &closure_apply(t, Val::VVar(l)),
            &Val::VApp(Rc::new(u.clone()), Rc::new(Val::VVar(l))),
        ),
        (_, Val::VLam(_, t2)) => conv(
            l + 1,
            &Val::VApp(Rc::new(t.clone()), Rc::new(Val::VVar(l))),
            &closure_apply(t2, Val::VVar(l)),
        ),

        (Val::VVar(x), Val::VVar(x2)) => x == x2,
        (Val::VApp(t, u), Val::VApp(t2, u2)) => conv(l, t, t2) && conv(l, u, u2),

        _ => false,
    }
}

// Elaboration
// --------------------------------------------------------------------------------

// type of every variable in scope
type Types = List<(Name, VTy)>;

/// Elaboration 上下文。"unzipped" 记录（与 Main.hs 一致，性能与便利各半）。
#[derive(Debug, Clone)]
struct Cxt {
    env: Env,
    types: Types,
    lvl: Lvl,
    pos: Span<()>,
}

impl Cxt {
    fn empty(pos: Span<()>) -> Self {
        Cxt {
            env: List::new(),
            types: List::new(),
            lvl: Lvl(0),
            pos,
        }
    }

    /// Extend Cxt with a bound variable.
    fn bind(&self, x: Name, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(Val::VVar(self.lvl)),
            types: self.types.prepend((x, a)),
            lvl: self.lvl + 1,
            pos: self.pos,
        }
    }

    /// Extend Cxt with a definition.
    fn define(&self, x: Name, t: VTy, a: VTy) -> Cxt {
        Cxt {
            env: self.env.prepend(t),
            types: self.types.prepend((x, a)),
            lvl: self.lvl + 1,
            pos: self.pos,
        }
    }
}

/// 类型检查错误：消息 + 当前源位置。
#[derive(Debug)]
pub struct Error {
    pub msg: String,
    pub pos: Span<()>,
}

type M<A> = Result<A, Error>;

pub(crate) fn report_at(pos: Span<()>, msg: String) -> Error {
    Error { msg, pos }
}

fn report(cxt: &Cxt, msg: String) -> Error {
    report_at(cxt.pos, msg)
}

fn show_val(cxt: &Cxt, v: &Val) -> String {
    let ns: Vec<String> = cxt.types.iter().map(|(x, _)| x.data.clone()).collect();
    pretty_tm(0, &ns, &quote(cxt.lvl, v))
}

// bidirectional algorithm:
//   use check when the type is already known
//   use infer if the type is unknown
// (original Hindley-Milner does not use bidirectionality)
// (even if you don't strictly need bidir, it's faster and has better errors)

fn check(cxt: &Cxt, t: &Raw, a: &VTy) -> M<Tm> {
    match (t, a) {
        // setting the source pos
        (Raw::SrcPos(pos, t), _) => {
            let mut cxt = cxt.clone();
            cxt.pos = *pos;
            check(&cxt, t, a)
        }

        // checking Lam with Pi type (canonical checking case)
        // (\x. t) : ((x : A) -> B)
        (Raw::Lam(x, t), Val::VPi(_, a, b)) => {
            // go under a binder as usual
            let body = check(&cxt.bind(x.clone(), (**a).clone()), t, &closure_apply(b, Val::VVar(cxt.lvl)))?;
            Ok(Tm::Lam(x.clone(), Box::new(body)))
        }

        // checking Let（let x : a = t in u）
        (Raw::Let(x, a, t, u), a2) => {
            let a = check(cxt, a, &Val::VU)?;
            let va = eval(&cxt.env, &a);
            let t = check(cxt, t, &va)?; // (I need to check with a VTy)
            let vt = eval(&cxt.env, &t);
            let u = check(&cxt.define(x.clone(), vt, va), u, a2)?;
            Ok(Tm::Let(x.clone(), Box::new(a), Box::new(t), Box::new(u)))
        }

        // only Lam and Let is checkable
        // if the term is not checkable, we switch to infer (change of direction)
        _ => {
            let (t, tty) = infer(cxt, t)?;
            if !conv(cxt.lvl, &tty, a) {
                return Err(report(
                    cxt,
                    format!(
                        "type mismatch\n\nexpected type:\n\n  {}\n\ninferred type:\n\n  {}\n",
                        show_val(cxt, a),
                        show_val(cxt, &tty)
                    ),
                ));
            }
            Ok(t)
        }
    }
}

fn infer(cxt: &Cxt, t: &Raw) -> M<(Tm, VTy)> {
    match t {
        Raw::SrcPos(pos, t) => {
            let mut cxt = cxt.clone();
            cxt.pos = *pos;
            infer(&cxt, t)
        }

        Raw::Var(x) => {
            let mut i = 0u32;
            for (x2, a) in cxt.types.iter() {
                if x.data == x2.data {
                    return Ok((Tm::Var(Ix(i)), a.clone()));
                }
                i += 1;
            }
            Err(report(cxt, format!("variable out of scope: {}", x.data)))
        }

        Raw::U => Ok((Tm::U, Val::VU)), // U : U rule

        Raw::App(t, u) => {
            let (t, tty) = infer(cxt, t)?;
            match &tty {
                Val::VPi(_, a, b) => {
                    let u = check(cxt, u, a)?;
                    let ty = closure_apply(b, eval(&cxt.env, &u)); // t u : B[x |-> u]
                    Ok((Tm::App(Box::new(t), Box::new(u)), ty))
                }
                tty => Err(report(
                    cxt,
                    format!(
                        "Expected a function type, instead inferred:\n\n  {}\n",
                        show_val(cxt, tty)
                    ),
                )),
            }
        }

        Raw::Lam(..) => Err(report(
            cxt,
            "Can't infer type for lambda expression".to_string(),
        )),

        Raw::Pi(x, a, b) => {
            let a = check(cxt, a, &Val::VU)?;
            let b = check(&cxt.bind(x.clone(), eval(&cxt.env, &a)), b, &Val::VU)?;
            Ok((Tm::Pi(x.clone(), Box::new(a), Box::new(b)), Val::VU))
        }

        Raw::Let(x, a, t, u) => {
            let a = check(cxt, a, &Val::VU)?;
            let va = eval(&cxt.env, &a);
            let t = check(cxt, t, &va)?;
            let vt = eval(&cxt.env, &t);
            let (u, uty) = infer(&cxt.define(x.clone(), vt, va), u)?;
            Ok((Tm::Let(x.clone(), Box::new(a), Box::new(t), Box::new(u)), uty))
        }
    }
}

// printing
// --------------------------------------------------------------------------------

fn fresh(ns: &[String], x: &str) -> String {
    if x == "_" {
        "_".to_string()
    } else if ns.iter().any(|n| n == x) {
        fresh(ns, &format!("{x}'"))
    } else {
        x.to_string()
    }
}

// printing precedences
const ATOMP: usize = 3; // U, var
const APPP: usize = 2; // application
const PIP: usize = 1; // pi
const LETP: usize = 0; // let, lambda

/// ns 按 Main.hs 的约定：**最内层 binder 在头部**（`x:ns` 前插），
/// `Var (Ix x) -> ns !! x`。
pub fn pretty_tm(prec: usize, ns: &[String], t: &Tm) -> String {
    let mut out = String::new();
    go(prec, ns, t, &mut out);
    out
}

/// Wrap in parens if expression precedence is lower than enclosing precedence.
fn go(p: usize, ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Var(Ix(x)) => out.push_str(&ns[*x as usize]),

        Tm::App(t, u) => {
            let paren = APPP < p;
            if paren {
                out.push('(');
            }
            go(APPP, ns, t, out);
            out.push(' ');
            go(ATOMP, ns, u, out);
            if paren {
                out.push(')');
            }
        }

        Tm::Lam(name, body) => {
            let paren = LETP < p;
            if paren {
                out.push('(');
            }
            out.push_str("λ ");
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            out.push_str(&x);
            ns.insert(0, x);
            go_lam(&ns, body, out);
            if paren {
                out.push(')');
            }
        }

        Tm::U => out.push('U'),

        Tm::Pi(name, a, b) => {
            let paren = PIP < p;
            if paren {
                out.push('(');
            }
            if name.data == "_" {
                go(APPP, ns, a, out);
                out.push_str(" → ");
                let mut ns = ns.to_vec();
                ns.insert(0, "_".to_string());
                go(PIP, &ns, b, out);
            } else {
                let mut ns = ns.to_vec();
                let x = fresh(&ns, &name.data);
                pi_bind(&ns, &x, a, out);
                ns.insert(0, x);
                go_pi(&ns, b, out);
            }
            if paren {
                out.push(')');
            }
        }

        Tm::Let(name, a, t, u) => {
            let paren = LETP < p;
            if paren {
                out.push('(');
            }
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            out.push_str("let ");
            out.push_str(&x);
            out.push_str(" : ");
            go(LETP, &ns, a, out);
            out.push_str("\n    = ");
            go(LETP, &ns, t, out);
            out.push_str("\n;\n");
            ns.insert(0, x);
            go(LETP, &ns, u, out);
            if paren {
                out.push(')');
            }
        }
    }
}

fn go_lam(ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Lam(name, body) => {
            out.push(' ');
            let x = fresh(ns, &name.data);
            out.push_str(&x);
            let mut ns = ns.to_vec();
            ns.insert(0, x);
            go_lam(&ns, body, out);
        }
        t => {
            out.push_str(". ");
            go(LETP, ns, t, out);
        }
    }
}

fn go_pi(ns: &[String], t: &Tm, out: &mut String) {
    match t {
        Tm::Pi(name, a, b) if name.data == "_" => {
            out.push_str(" → ");
            go(APPP, ns, a, out);
            out.push_str(" → ");
            let mut ns = ns.to_vec();
            ns.insert(0, "_".to_string());
            go(PIP, &ns, b, out);
        }
        Tm::Pi(name, a, b) => {
            let mut ns = ns.to_vec();
            let x = fresh(&ns, &name.data);
            pi_bind(&ns, &x, a, out);
            ns.insert(0, x);
            go_pi(&ns, b, out);
        }
        t => {
            out.push_str(" → ");
            go(PIP, ns, t, out);
        }
    }
}

fn pi_bind(ns: &[String], x: &str, a: &Tm, out: &mut String) {
    out.push('(');
    out.push_str(x);
    out.push_str(" : ");
    go(LETP, ns, a, out);
    out.push(')');
}

// errors & main
// --------------------------------------------------------------------------------

fn line_col(file: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (i, b) in file.bytes().enumerate() {
        if i >= offset {
            break;
        }
        if b == b'\n' {
            line += 1;
            line_start = i + 1;
        }
    }
    (line, offset - line_start + 1)
}

/// Main.hs 的 `displayError`（megaparsec 风格的源码摘录 + caret）。
/// 位置来自 elaboration 时记录的最内层 `SrcPos`。
pub fn display_error(file: &str, err: &Error) -> String {
    let (linum, colnum) = line_col(file, err.pos.start_offset as usize);
    let lnum = linum.to_string();
    let lpad = " ".repeat(lnum.len());
    let line = file
        .split('\n')
        .nth(linum - 1)
        .unwrap_or("")
        .trim_end_matches('\r');
    format!(
        "(stdin):{}:{}:\n{} |\n{} | {}\n{} | {}^\n{}\n",
        linum,
        colnum,
        lpad,
        lnum,
        line,
        lpad,
        " ".repeat(colnum - 1),
        err.msg
    )
}

const HELP_MSG: &str = "usage: elabzoo-typecheck-closures-debruijn [--help|nf|type]\n\
  \x20 --help : display this message\n\
  \x20 nf     : read & typecheck expression from stdin, print its normal form and type\n\
  \x20 type   : read & typecheck expression from stdin, print its type\n";

fn initial_pos() -> Span<()> {
    Span {
        data: (),
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

/// Main.hs 的 `mainWith`：`--help` / `nf` / `type` 三种模式，返回本应打印
/// 到 stdout 的全部文本（供测试断言）。
pub fn main_with(mode: &str, file: &str) -> String {
    match mode {
        "--help" => HELP_MSG.to_string(),
        "nf" => match parser::parser(file, 0) {
            None => "parse error\n".to_string(),
            Some(t) => match infer(&Cxt::empty(initial_pos()), &t) {
                Err(err) => display_error(file, &err),
                Ok((t, a)) => format!(
                    "{}\n  :\n{}\n",
                    pretty_tm(0, &[], &nf(&List::new(), &t)),
                    pretty_tm(0, &[], &quote(Lvl(0), &a))
                ),
            },
        },
        "type" => match parser::parser(file, 0) {
            None => "parse error\n".to_string(),
            Some(t) => match infer(&Cxt::empty(initial_pos()), &t) {
                Err(err) => display_error(file, &err),
                Ok((_, a)) => format!("{}\n", pretty_tm(0, &[], &quote(Lvl(0), &a))),
            },
        },
        _ => HELP_MSG.to_string(),
    }
}

// examples
// --------------------------------------------------------------------------------

pub const EX0_SRC: &str = "\
let id : (A : U) -> A -> A
     = \\A x. x;
let foo : U = U;
let bar : U = id id;     -- we cannot apply any function to itself (already true in simple TT)
id
";

pub const EX1_SRC: &str = "\
let id : (A : U) -> A -> A
      = \\A x. x;
let const : (A B : U) -> A -> B -> A
      = \\A B x y. x;
id ((A B : U) -> A -> B -> A) const
";

/// Church-coded natural numbers (standard test for finding eval bugs)
pub const EX2_SRC: &str = "\
let Nat  : U = (N : U) -> (N -> N) -> N -> N;
let five : Nat = \\N s z. s (s (s (s (s z))));
let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);
let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;
let ten      : Nat = add five five;
let hundred  : Nat = mul ten ten;
let thousand : Nat = mul ten hundred;
thousand
";

#[allow(non_snake_case)]
pub fn ex0() -> String {
    main_with("nf", EX0_SRC)
}

#[allow(non_snake_case)]
pub fn ex1() -> String {
    main_with("nf", EX1_SRC)
}

#[allow(non_snake_case)]
pub fn ex2() -> String {
    main_with("nf", EX2_SRC)
}

// benchmark entries（l02bench 用）
// --------------------------------------------------------------------------------

/// 基准口径：check + nf，产出丢弃。深 Box 树的递归析构会爆栈，基准里
/// mem::forget（进程退出统一回收；L01 readme「已知限制」同款处理）。
/// 解析在计时外（bench 直接传 Raw，与 fast 口径一致）。
pub(crate) fn bench_check_nf(raw: &Raw) {
    if let Ok((t, _)) = infer(&Cxt::empty(initial_pos()), raw) {
        let n = nf(&List::new(), &t);
        std::mem::forget(n);
    }
}

/// 基准口径：仅 check（conv 工作负载的转换检查发生在 check 里）。
pub(crate) fn bench_check(raw: &Raw) {
    let _ = infer(&Cxt::empty(initial_pos()), raw);
}

/// church n 的 nf-mode 期望输出（`λ N s z. s (s (… z))`）。
pub(crate) fn church_nf(n: usize) -> String {
    fn f(k: usize) -> String {
        match k {
            0 => "z".to_string(),
            1 => "s z".to_string(),
            k => format!("s ({})", f(k - 1)),
        }
    }
    format!("λ N s z. {}\n", f(n))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ex0_reports_self_application_error() {
        // main.hs ex0：`id id` 无法通过检查（U 里没有自应用），报错位置在第二个 id
        assert_eq!(
            ex0(),
            r#"(stdin):4:18:
  |
4 | let bar : U = id id;     -- we cannot apply any function to itself (already true in simple TT)
  |                  ^
type mismatch

expected type:

  U

inferred type:

  (A : U) → A → A

"#
        );
    }

    #[test]
    fn ex1_nf_and_type() {
        assert_eq!(
            ex1(),
            "λ A B x y. x\n  :\n(A : U)(B : U) → A → B → A\n"
        );
    }

    #[test]
    fn ex2_church_thousand() {
        assert_eq!(
            ex2(),
            format!("{}  :\n(N : U) → (N → N) → N → N\n", church_nf(1000))
        );
    }

    #[test]
    fn type_mode() {
        assert_eq!(
            main_with("type", "let id : (A : U) -> A -> A\n      = \\A x. x;\nid"),
            "(A : U) → A → A\n"
        );
    }

    #[test]
    fn help_mode() {
        assert!(main_with("--help", "").starts_with("usage: elabzoo-typecheck-closures-debruijn"));
        assert!(main_with("bogus", "").starts_with("usage:"));
    }

    #[test]
    fn out_of_scope_variable() {
        let out = main_with("type", "id");
        assert_eq!(
            out,
            r#"(stdin):1:1:
  |
1 | id
  | ^
variable out of scope: id
"#
        );
    }

    #[test]
    fn cant_infer_lam() {
        let out = main_with("type", "\\x. x");
        assert!(out.ends_with("Can't infer type for lambda expression\n"), "{out}");
    }

    #[test]
    fn expected_function_type() {
        let out = main_with("type", "let f : U = U;\nf f");
        assert!(out.contains("Expected a function type"), "{out}");
    }

    /// λ 两种前缀（`\` 与 `λ`）等价；`_` 可作 binder 名。
    #[test]
    fn lambda_spellings_and_underscore_binder() {
        let a = main_with("type", "let f : U -> U -> U = \\x _. x;\nf");
        let b = main_with("type", "let f : U -> U -> U = λx y. x;\nf");
        assert_eq!(a, b);
        assert_eq!(a, "U → U → U\n");
    }

    /// 与性能版（bump_spine_iter）互检：所有示例的输出逐字节一致。
    #[test]
    fn fast_impl_matches_basic_on_examples() {
        for (name, src) in [
            ("ex0", EX0_SRC),
            ("ex1", EX1_SRC),
            ("ex2", EX2_SRC),
            ("type id", "let id : (A : U) -> A -> A\n      = \\A x. x;\nid"),
        ] {
            for mode in ["nf", "type"] {
                let basic = main_with(mode, src);
                let fast = bump_spine_iter::main_with(mode, src);
                assert_eq!(basic, fast, "mismatch on {name} ({mode})");
            }
        }
    }
}
