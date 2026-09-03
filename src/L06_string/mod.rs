use colored::Colorize;
use cxt::Cxt;
use parser::syntax::{Either, Icit, Raw};
use syntax::{close_ty, Pruning};

use crate::list::List;
use crate::parser_lib::Span;

pub(crate) mod parser;
mod elaboration;
mod cxt;
mod unification;
mod syntax;
mod pretty;
pub(crate) mod bump_spine_iter;

#[derive(Debug, Clone, Copy, PartialEq)]
struct MetaVar(u32);

#[derive(Debug)]
enum MetaEntry {
    Solved(Rc<Val>, Rc<VTy>),
    Unsolved(Rc<VTy>),
}

#[derive(Debug, Clone, Copy)]
struct Ix(u32);

#[derive(Debug, Clone)]
enum BD {
    Bound,
    Defined,
}

#[derive(Clone, Debug)]
pub enum DeclTm {
    Def {
        /*name: Span<String>,
        params: Vec<(Span<String>, Tm, Icit)>,
        ret_type: Tm,
        body: Tm,*/
    },
    Println(Tm),
}

#[derive(Debug, Clone)]
enum Tm {
    Var(Ix),
    Lam(Span<String>, Icit, Box<Tm>),
    App(Box<Tm>, Box<Tm>, Icit),
    AppPruning(Box<Tm>, Pruning),
    U,
    Pi(Span<String>, Icit, Box<Ty>, Box<Ty>),
    Let(Span<String>, Box<Ty>, Box<Tm>, Box<Tm>),
    Meta(MetaVar),
    LiteralType,
    LiteralIntro(Span<String>),
    Decl(Span<String>),
}

type Ty = Tm;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Lvl(u32);

impl Add<u32> for Lvl {
    type Output = Lvl;
    fn add(self, rhs: u32) -> Lvl {
        Lvl(self.0 + rhs)
    }
}

type Env = List<Rc<Val>>;
type Spine = List<(Rc<Val>, Icit)>;

#[derive(Debug, Clone)]
struct Closure(Env, Rc<Tm>);

#[derive(Debug, Clone)]
enum Val {
    Flex(MetaVar, Spine),
    Rigid(Lvl, Spine),
    Lam(Span<String>, Icit, Closure),
    Pi(Span<String>, Icit, Rc<VTy>, Closure),
    U,
    LiteralType,
    LiteralIntro(Span<String>),
    Decl(Span<String>, Spine),
}

type VTy = Val;

impl Val {
    fn vvar(x: Lvl) -> Self {
        Val::Rigid(x, List::new())
    }

    fn vmeta(m: MetaVar) -> Self {
        Val::Flex(m, List::new())
    }
}

fn lvl2ix(l: Lvl, x: Lvl) -> Ix {
    Ix(l.0 - x.0 - 1)
}

use std::ops::Add;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Debug)]
struct UnifyError;

fn empty_span<T>(data: T) -> Span<T> {
    Span {
        data,
        start_offset: 0,
        end_offset: 0,
        path_id: 0,
    }
}

#[derive(Debug)]
pub struct Error(String);

/// Native implementation of a builtin function, registered by name in the
/// decl table (`Cxt::add_builtin`; ported from L13's `PrimFunc`).  Invoked
/// at application time (`Infer::v_app`) with the accumulated arguments in
/// natural order; returning `None` keeps the application stuck
/// (`Val::Decl(name, spine)`), e.g. on partial application or non-literal
/// arguments.
pub struct PrimFunc(Rc<dyn Fn(&Infer, &[Rc<Val>]) -> Option<Rc<Val>> + Send + Sync>);

impl std::fmt::Debug for PrimFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PrimFunc")
    }
}

/// One decl-table entry (L06's stand-in for the L13 `Decl` map value):
/// the definition's value and type, plus the optional native implementation
/// that makes it a builtin.  Top-level `def`s are inserted by the elaborator
/// (runtime name lookup, e.g. `string_to_global_type`), builtins by
/// `Cxt::add_builtin`.
#[derive(Debug)]
pub(crate) struct DeclEntry {
    pub(crate) vt: Rc<Val>,
    pub(crate) va: Rc<VTy>,
    pub(crate) prim: Option<PrimFunc>,
}

pub struct Infer {
    meta: Vec<MetaEntry>,
    /// Decl table: name -> (value, type, optional native impl).  Held on
    /// `Infer` because L06's eval / v_app / quote only receive `&Infer`
    /// (L13 threads `&Decl` through them instead).
    pub(crate) decls: HashMap<String, DeclEntry>,
    /// Runtime-global store for the create_global / get_global / ... builtins
    /// (L13 uses a RwLock; single-threaded here, so RefCell).
    pub(crate) mutable_map: RefCell<HashMap<String, Rc<Val>>>,
}

impl Infer {
    pub fn new() -> Self {
        Self { meta: vec![], decls: HashMap::new(), mutable_map: RefCell::new(HashMap::new()) }
    }
    /// Insert a builtin entry: head value `Val::Decl(name, [])` (prim fires
    /// on application), declared type, native implementation.
    pub(crate) fn register_builtin(&mut self, name: &str, vt: Rc<Val>, va: Rc<VTy>, prim: PrimFunc) {
        self.decls.insert(name.to_owned(), DeclEntry { vt, va, prim: Some(prim) });
    }
    fn new_meta(&mut self, a: Rc<VTy>) -> u32 {
        self.meta.push(MetaEntry::Unsolved(a));
        self.meta.len() as u32 - 1
    }
    fn fresh_meta(&mut self, cxt: &Cxt, a: &Rc<VTy>) -> Tm {
        let closed = self.eval(&List::new(), &close_ty(cxt.locals.clone(), self.quote(cxt.lvl, a)));
        let m = self.new_meta(closed);
        Tm::AppPruning(Box::new(Tm::Meta(MetaVar(m))), cxt.pruning.clone())
    }
    fn lookup_meta(&self, m: &MetaVar) -> &MetaEntry {
        &self.meta[m.0 as usize]
    }
    fn force(&self, t: &Rc<Val>) -> Rc<Val> {
        //println!("{} {:?}", "force".red(), t);
        match t.as_ref() {
            Val::Flex(m, sp) => match self.lookup_meta(m) {
                MetaEntry::Solved(t_solved, _) => self.force(&self.v_app_sp(t_solved.clone(), sp.clone())),
                MetaEntry::Unsolved(_) => Val::Flex(*m, sp.clone()).into(),
            },
            _ => t.clone(),
        }
    }
    fn v_meta(&self, m: &MetaVar) -> Rc<Val> {
        match self.lookup_meta(m) {
            MetaEntry::Solved(v, _) => v.clone(),
            MetaEntry::Unsolved(_) => Val::vmeta(*m).into(),
        }
    }

    fn closure_apply(&self, closure: &Closure, u: Rc<Val>) -> Rc<Val> {
        //println!("{} {:?} {:?}", "closure apply".yellow(), closure, u);
        self.eval(&closure.0.prepend(u), &closure.1)
    }

    fn v_app(&self, t: Rc<Val>, u: Rc<Val>, i: Icit) -> Rc<Val> {
        match t.as_ref() {
            Val::Lam(_, _, closure) => self.closure_apply(&closure, u),
            Val::Flex(m, sp) => Val::Flex(*m, sp.prepend((u, i))).into(),
            Val::Rigid(x, sp) => Val::Rigid(*x, sp.prepend((u, i))).into(),
            // Decl-headed application (ported from L13's `v_app` Decl arm):
            // if the head is a builtin, fire its prim on the accumulated
            // arguments in natural order.  None (partial application / stuck
            // non-literal args) keeps the application stuck, carrying the
            // name so it quotes/prints as `name args...`.
            Val::Decl(name, sp) => {
                let acc = sp.prepend((u, i));
                if let Some(entry) = self.decls.get(&name.data) {
                    if let Some(prim) = &entry.prim {
                        let args: Vec<Rc<Val>> = {
                            let mut v: Vec<Rc<Val>> = acc.iter().map(|(v, _)| v.clone()).collect();
                            v.reverse();
                            v
                        };
                        if let Some(result) = prim.0(self, &args) {
                            return result;
                        }
                    }
                }
                Val::Decl(name.clone(), acc).into()
            },
            _ => panic!("impossible"),
        }
    }

    fn v_app_sp(&self, t: Rc<Val>, spine: Spine) -> Rc<Val> {
        //spine.iter().rev().fold(t, |acc, (u, i)| self.v_app(acc, u.clone(), *i))
        match spine {
            List { head: None, .. } => t,
            a => {
                let (u, i) = a.head().unwrap();
                self.v_app(self.v_app_sp(t, a.tail()), u.clone(), *i)
            },
        }
    }

    fn v_app_pruning(&self, env: &Env, v: Rc<Val>, pr: &Pruning) -> Rc<Val> {
        //println!("{} {:?} {:?}", "v_app_bds".green(), v, bds);
        match (env, pr) {
            (List { head: None, .. }, List { head: None, .. }) => v,
            (a, b) if a.head().is_some() && matches!(b.head(), Some(Some(_))) => self.v_app(
                self.v_app_pruning(&a.tail(), v, &b.tail()),
                a.head().unwrap().clone(),
                b.head().unwrap().unwrap(),
            ),
            (a, b) if a.head().is_some() && matches!(b.head(), Some(None)) => {
                self.v_app_pruning(&a.tail(), v, &b.tail())
            }
            _ => panic!("impossible"),
        }
    }

    fn eval(&self, env: &Env, tm: &Tm) -> Rc<Val> {
        //println!("{} {:?}", "eval".yellow(), tm);
        match tm {
            Tm::Var(x) => env.iter().nth(x.0 as usize).unwrap().clone(),
            Tm::App(t, u, i) => self.v_app(self.eval(env, t), self.eval(env, u), *i),
            Tm::Lam(x, i, t) => Val::Lam(x.clone(), *i, Closure(env.clone(), t.clone().into())).into(),//TODO:use reference?
            Tm::Pi(x, i, a, b) => Val::Pi(x.clone(), *i, self.eval(env, a), Closure(env.clone(), b.clone().into())).into(),//TODO:use reference?
            Tm::Let(_, _, t, u) => {
                let t_val = self.eval(env, t);
                self.eval(&env.prepend(t_val), u)
            }
            Tm::U => Val::U.into(),
            Tm::Meta(m) => self.v_meta(m),
            Tm::AppPruning(t, pr) => self.v_app_pruning(env, self.eval(env, t), &pr),
            Tm::LiteralIntro(x) => Val::LiteralIntro(x.clone()).into(),
            Tm::LiteralType => Val::LiteralType.into(),
            // Name lookup: a decl-table hit evaluates to the stored value
            // (a builtin hits its stuck head; calling fires the prim in
            // `v_app`), a miss stays a stuck `Val::Decl` head.
            Tm::Decl(name) => match self.decls.get(&name.data) {
                Some(entry) => entry.vt.clone(),
                None => Val::Decl(name.clone(), List::new()).into(),
            },
        }
    }

    fn quote_sp(&self, l: Lvl, t: Tm, spine: Spine) -> Tm {
        /*spine.iter().fold(t, |acc, u| {
            Tm::App(Box::new(acc), Box::new(self.quote(l, u.0.clone())), u.1)
        })*/
        match spine {
            List { head: None, .. } => t,
            _ => {
                let head = spine.head().unwrap();
                Tm::App(Box::new(self.quote_sp(l, t, spine.tail())), Box::new(self.quote(l, &head.0)), head.1)
            }
        }
    }

    fn quote(&self, l: Lvl, t: &Rc<Val>) -> Tm {
        //println!("{} {:?}", "quote".green(), t);
        let t = self.force(t);
        match t.as_ref() {
            Val::Flex(m, sp) => self.quote_sp(l, Tm::Meta(*m), sp.clone()),
            Val::Rigid(x, sp) => self.quote_sp(l, Tm::Var(lvl2ix(l, *x)), sp.clone()),
            Val::Lam(x, i, closure) => Tm::Lam(
                x.clone(),
                *i,
                Box::new(self.quote(l + 1, &self.closure_apply(&closure, Val::vvar(l).into()))),
            ),
            Val::Pi(x, i, a, closure) => Tm::Pi(
                x.clone(),
                *i,
                Box::new(self.quote(l, a)),
                Box::new(self.quote(l + 1, &self.closure_apply(&closure, Val::vvar(l).into()))),
            ),
            Val::U => Tm::U,
            Val::LiteralIntro(x) => Tm::LiteralIntro(x.clone()),
            Val::LiteralType => Tm::LiteralType,
            Val::Decl(name, sp) => self.quote_sp(l, Tm::Decl(name.clone()), sp.clone()),
        }
    }

    pub fn nf(&self, env: &Env, t: Tm) -> Tm {
        let l = Lvl(env.iter().count() as u32);
        self.quote(l, &self.eval(env, &t))
    }

    fn close_val(&self, cxt: &Cxt, t: &Rc<Val>) -> Closure {
        Closure(cxt.env.clone(), Rc::new(self.quote(cxt.lvl + 1, t)))
    }

    fn unify_catch(&mut self, cxt: &Cxt, t: &Rc<Val>, t_prime: &Rc<Val>) -> Result<(), Error> {
        self.unify(cxt.lvl, t, t_prime)
            .map_err(|_| {
                /*Error::CantUnify(
                    cxt.clone(),
                    self.quote(cxt.lvl, t),
                    self.quote(cxt.lvl, t_prime),
                )*/
                Error(format!("can't unify {:?} == {:?}", self.quote(cxt.lvl, t), self.quote(cxt.lvl, t_prime)))
                //Error(format!("can't unify {:?} == {:?}", t, t_prime))
            })
    }
}

pub fn run(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = match parser::parser(&preprocess(input), path_id) {
        Some(ast) => ast,
        None => return Err(Error("parse error".to_owned())),
    };
    let mut cxt = Cxt::new(&mut infer);
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            //ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += &pretty::pretty_tm(0, cxt.names(), &infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    Ok(ret)
}

/// 注释剥离(行 `//` 与块 `/* */`),**字符串字面量内不生效**——旧版对
/// `//` / `/*` 做纯文本剥离,会把 `"http://…"` 之类的字面量截成未闭合
/// 字符串导致解析失败。现按词法规则跳过字符串区间(含 `\` 转义);注释
/// 内容只替换为空白,保持 span 偏移稳定。块注释不嵌套(与旧版一致)。
pub fn preprocess(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    let mut in_string = false;
    let mut escaped = false;
    while let Some(c) = chars.next() {
        if in_string {
            out.push(c);
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_string = false;
            }
            continue;
        }
        match c {
            '"' => {
                in_string = true;
                out.push(c);
            }
            '/' if chars.peek() == Some(&'/') => {
                chars.next();
                out.push_str("  ");
                // 行注释:换行前的内容替换为空白(保留换行符)
                for rc in chars.by_ref() {
                    if rc == '\n' {
                        out.push('\n');
                        break;
                    }
                    out.push(if rc.is_whitespace() { rc } else { ' ' });
                }
            }
            '/' if chars.peek() == Some(&'*') => {
                chars.next();
                out.push_str("  ");
                // 块注释:到 `*/` 为止的内容替换为空白
                while let Some(rc) = chars.next() {
                    if rc == '*' && chars.peek() == Some(&'/') {
                        chars.next();
                        out.push_str("  ");
                        break;
                    }
                    out.push(if rc.is_whitespace() { rc } else { ' ' });
                }
            }
            _ => out.push(c),
        }
    }
    out
}

/// 内嵌 `test` 与性能版（`bump_spine_iter`）互检共用的演示源：pruning 全套
/// （Eq/refl/the/m 的非线性与交集剪枝）+ String 字面量 + builtin 注册表
/// （str_eq / str_indent2 / 文件 IO）+ decl 表按名取值 + 可变全局。
pub(crate) const DEMO_SRC: &str = r#"
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px
def symmetry [A : U] (a: A, b: A) (eqab : Eq a b) : Eq b a =
  eqab (bb => (Eq bb a)) refl

def the(A : U)(x: A): A = x

def m(A : U)(B : U): U -> U -> U = _
def test = a => b => the (Eq (m a a) (x => y => y)) refl

def m : U -> U -> U -> U = _
def test = a => b => c => the (Eq (m a b c) (m c b a)) refl


def pr1 = f => x => f x
def pr2 = f => x => y => f x y
def pr3 = f => f U

def Nat : U
    = (N : U) -> (N -> N) -> N -> N
def mul : Nat -> Nat -> Nat
    = a => b => N => s => z => a _ (b _ s) z
def ten : Nat
    = N => s => z => s (s (s (s (s (s (s (s (s (s z)))))))))
def hundred = mul ten ten

println hundred

def mystr = "hello world"

def add_tail(x: String): String = string_concat x "!"

def mystr2 = add_tail mystr

/*
multi line comment
*/

//final
println mystr2

/*
builtin registry demos (ported from L13): str_eq / str_indent2 / file IO
*/
def eq1 = str_eq "foo" "foo"
println eq1

def eq2 = str_eq "foo" "bar"
println eq2

def ind = str_indent2 "line1\nline2"
println ind

def demo_path = "l06_builtin_demo.txt"
def demo_write : U = file_write_all_text demo_path "hello file"
def demo_append : U = file_append_all_text demo_path "!"
def read_back : String = file_read_all_text demo_path
println read_back

def exists1 : String = file_exists demo_path
println exists1

def demo_delete : U = file_delete demo_path
def exists2 : String = file_exists demo_path
println exists2

/*
decl-table by-name lookup (L13 port): defs go into the table at elaboration,
string_to_global_type fetches their VALUE (= "dynamic type"); globals store
runtime values in Infer's mutable map.
*/
def st : U = string_to_global_type "String"
println st

def st_nat : U = string_to_global_type "Nat"
println st_nat

def store1 : U = create_global "greeting" "hi"
def upd1 : U = change_mutable "greeting" (s => string_concat s "!")
def g1 : String = get_global "greeting"
println g1

def g2 : String = get_global_default "greeting" "fallback"
println g2

def g3 : String = get_global_default "missing_name" "fallback"
println g3

def upd2 : U = change_mutable_default "greeting" (s => string_concat s "?") "x"
def g4 : String = get_global "greeting"
println g4

def upd3 : U = change_mutable_default "created_now" (s => s) "fresh"
def g5 : String = get_global "created_now"
println g5

def rep1 : U = report_check_issue "E1" "demo_mod" "sig" "message"
def issues : String = get_global "CheckIssues"
println issues

"#;

/// 文件 IO builtin 的演示用固定文件名（`l06_builtin_demo.txt`）——做文件
/// 副作用的测试（参考版内嵌 `test` 与性能版互检/稳态测试）经它串行，
/// 避免并行测试线程在 Windows 上的文件句柄竞争（删除报 os error 5）。
pub(crate) static FILE_IO_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[test]
fn test() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    println!("{}", run(DEMO_SRC, 0).unwrap());
    println!("success");
}


pub fn run1(input: &str, path_id: u32) -> Result<String, Error> {
    let mut infer = Infer::new();
    let ast = parser::parser(input, path_id).unwrap();
    let mut cxt = Cxt::new(&mut infer);
    let mut ret = String::new();
    for tm in ast {
        let (x, _, new_cxt) = infer.infer(&cxt, tm.clone())?;
        cxt = new_cxt;
        if let DeclTm::Println(x) = x {
            ret += &format!("{:?}", infer.nf(&cxt.env, x));
            ret += "\n";
        }
    }
    println!("{:?}", cxt);
    Ok(ret)
}

#[test]
fn test1() {
    let input = r#"
def str_id(x: String, y: String): String = "builtin"

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id(x: String, y: String): String = x

"#;
    println!("{}", run1(input, 0).unwrap());
    let input = r#"
def str_id: String = string_concat "hello " "world"

println str_id

"#;
    println!("{}", run1(input, 0).unwrap());
    println!("success");
}

// benchmark entries（l06bench 用）
// --------------------------------------------------------------------------------

/// 参考版基准口径：全量 elaborate（def 注册 + 上下文延伸），返回是否通过。
/// 每次调用新建 `Infer`（内置表 + 可变全局随之重置，与 `run` 的每调用新
/// 状态一致）。
pub(crate) fn bench_check(decls: &[parser::syntax::Decl]) -> bool {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&mut infer);
    for d in decls {
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return false,
        }
    }
    true
}

/// 参考版项的节点数（与性能版 `tm_size` 同口径地数 AppPruning 掩码链）。
fn tm_size_ref(t: &Tm) -> u64 {
    let mut stack: Vec<&Tm> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Decl(_) => {}
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                n += pr.iter().count() as u64;
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
        }
    }
    n
}

/// 参考版基准口径：elaborate 全部 decl 后，取**最后一个 def** 在 decl 表里
/// 登记的值，空层级引读并数节点（深 Box 树的递归析构会爆栈，基准里
/// `mem::forget`——L03/L04/L05 同款处理）。
pub(crate) fn bench_check_nf(decls: &[parser::syntax::Decl]) -> u64 {
    let mut infer = Infer::new();
    let mut cxt = Cxt::new(&mut infer);
    let mut last = None;
    for d in decls {
        match d {
            parser::syntax::Decl::Def { name, .. } => last = Some(name.data.clone()),
            parser::syntax::Decl::Println(_) => {}
        }
        match infer.infer(&cxt, d.clone()) {
            Ok((_, _, nc)) => cxt = nc,
            Err(_) => return 0,
        }
    }
    let Some(name) = last else { return 0 };
    let Some(entry) = infer.decls.get(&name) else { return 0 };
    let q = infer.quote(Lvl(0), &entry.vt);
    let n = tm_size_ref(&q);
    std::mem::forget(q);
    n
}
