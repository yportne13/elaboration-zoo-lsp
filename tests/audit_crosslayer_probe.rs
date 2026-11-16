//! 跨层正确性探针（audit 专用，2026-11-16）。不要删除——由 Lead 决定去留。
//!
//! 目的：把同一批小程序分别喂给 L07..L13 的**参考版** `run(input, 0)`，
//! 建立「程序 × 层」矩阵，归一化记录 Ok 输出（去空白 hash + 文本）/ Err
//! （Debug 文本 + 类别）/ Panic / Timeout，供 .audit/correctness.md 判读。
//!
//! - L09/L10/L11 在 src/lib.rs 是私有模块，按 tests/gadt_refine_cross_layer_tests.rs
//!   同款用 `#[path]` 直接编入；L07/L08/L12/L13 走库入口。
//! - 每层每次 run 放在 256MB 栈线程里 + catch_unwind + mpsc recv_timeout，
//!   防深递归栈溢出/挂死（栈溢出仍是进程 abort，无法 catch；语料已按既有
//!   测试套件里可跑通的形态挑选）。
//! - 运行：cargo test --release --test audit_crosslayer_probe -- --nocapture
//!   结果同时落盘 .audit/raw-correctness/probe-matrix.tsv（逐层 flush，
//!   便于进程异常中止时保留已有行）与 probe-programs.tsv（语料原文）。
//!
//! 判定口径：本文件**不做断言**（除基本自检），只产出矩阵原始数据；层间
//! 「特性门 / 真回归 / 输出漂移 / 层内精化缺陷」的判读在 correctness.md。

#![allow(non_snake_case)]

#[path = "../src/list.rs"]
mod list;
#[path = "../src/bimap.rs"]
mod bimap;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L09_mltt/mod.rs"]
mod L09_mltt;
#[path = "../src/L10_typeclass/mod.rs"]
mod L10_typeclass;
#[path = "../src/L11_macro/mod.rs"]
mod L11_macro;

use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::mpsc;
use std::time::Duration;

use elaboration_zoo_lsp::{L07_sum_type, L08_product_type, L12_canonical, L13_namespace};

// ---------------------------------------------------------------------------
// 基础工具
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Outcome {
    Ok { raw: String, norm: String, hash: u64 },
    Err { text: String },
    Panic(String),
    Timeout,
    Spawn(String),
}

impl Outcome {
    fn kind(&self) -> &'static str {
        match self {
            Outcome::Ok { .. } => "Ok",
            Outcome::Err { .. } => "Err",
            Outcome::Panic(_) => "Panic",
            Outcome::Timeout => "Timeout",
            Outcome::Spawn(_) => "SpawnFail",
        }
    }
    /// Err 类别：只做粗分类，正文另存，避免把文案漂移误判为判定漂移。
    fn class(&self) -> String {
        match self {
            Outcome::Ok { .. } => "ok".into(),
            Outcome::Err { text } => classify_err(text).into(),
            Outcome::Panic(_) => "panic".into(),
            Outcome::Timeout => "timeout".into(),
            Outcome::Spawn(_) => "spawn".into(),
        }
    }
    fn hash_hex(&self) -> String {
        match self {
            Outcome::Ok { hash, .. } => format!("{:016x}", hash),
            _ => "-".into(),
        }
    }
    fn text(&self) -> String {
        match self {
            Outcome::Ok { raw, .. } => raw.clone(),
            Outcome::Err { text } => text.clone(),
            Outcome::Panic(p) => p.clone(),
            Outcome::Timeout => "TIMEOUT".into(),
            Outcome::Spawn(e) => e.clone(),
        }
    }
}

fn classify_err(text: &str) -> &'static str {
    if text.contains("parse error")
        || text.contains("unexpected token")
        || text.contains("Expect")
        || text.contains("residual")
    {
        "parse"
    } else if text.contains("redefine") {
        "redefine"
    } else if text.contains("can't unify") || text.contains("unify") {
        "unify"
    } else if text.contains("不可达") || text.contains("Unreachable") || text.contains("unreachable") {
        "unreachable"
    } else if text.contains("不完整") || text.contains("Unmatched") || text.contains("missing") {
        "coverage"
    } else if text.contains("has no field") || text.contains("cannot project") {
        "project"
    } else if text.contains("universe") {
        "universe"
    } else if text.contains("has no object") {
        "no-object"
    } else if text.contains("Too much effort") {
        "effort"
    } else if text.is_empty() {
        "empty"
    } else {
        "other"
    }
}

fn norm_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn hash_str(s: &str) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

fn esc(s: &str, max_chars: usize) -> String {
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i >= max_chars {
            out.push('…');
            break;
        }
        match c {
            '\\' => out.push_str("\\\\"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\r' => {}
            _ => out.push(c),
        }
    }
    out
}

fn panic_text(p: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = p.downcast_ref::<&str>() {
        format!("panic: {s}")
    } else if let Some(s) = p.downcast_ref::<String>() {
        format!("panic: {s}")
    } else {
        "panic: <non-string payload>".into()
    }
}

/// 在 256MB 栈线程里跑一层；超时返回 Timeout（线程被放弃，不 join）。
fn run_generic<F, E>(src: &str, timeout: Duration, f: F) -> Outcome
where
    F: FnOnce(String) -> Result<String, E> + Send + 'static,
    E: Debug,
{
    let (tx, rx) = mpsc::channel::<Outcome>();
    let input = src.to_owned();
    let spawned = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let o = match catch_unwind(AssertUnwindSafe(|| f(input))) {
                Ok(Ok(raw)) => {
                    let norm = norm_ws(&raw);
                    let hash = hash_str(&norm);
                    Outcome::Ok { raw, norm, hash }
                }
                Ok(Err(e)) => Outcome::Err {
                    text: esc(&format!("{:?}", e), 400),
                },
                Err(p) => Outcome::Panic(esc(&panic_text(&*p), 400)),
            };
            let _ = tx.send(o);
        });
    match spawned {
        Ok(_handle) => match rx.recv_timeout(timeout) {
            Ok(o) => o,
            Err(_) => Outcome::Timeout,
        },
        Err(e) => Outcome::Spawn(esc(&e.to_string(), 200)),
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Layer {
    L07,
    L08,
    L09,
    L10,
    L11,
    L12,
    L13,
}

const LAYERS: [Layer; 7] = [
    Layer::L07,
    Layer::L08,
    Layer::L09,
    Layer::L10,
    Layer::L11,
    Layer::L12,
    Layer::L13,
];

impl Layer {
    fn name(self) -> &'static str {
        match self {
            Layer::L07 => "L07",
            Layer::L08 => "L08",
            Layer::L09 => "L09",
            Layer::L10 => "L10",
            Layer::L11 => "L11",
            Layer::L12 => "L12",
            Layer::L13 => "L13",
        }
    }
}

fn run_layer(layer: Layer, src: &str, timeout: Duration) -> Outcome {
    match layer {
        Layer::L07 => run_generic(src, timeout, |s| L07_sum_type::run(&s, 0)),
        Layer::L08 => run_generic(src, timeout, |s| L08_product_type::run(&s, 0)),
        Layer::L09 => run_generic(src, timeout, |s| L09_mltt::run(&s, 0)),
        Layer::L10 => run_generic(src, timeout, |s| L10_typeclass::run(&s, 0)),
        Layer::L11 => run_generic(src, timeout, |s| L11_macro::run(&s, 0)),
        Layer::L12 => run_generic(src, timeout, |s| L12_canonical::run(&s, 0)),
        Layer::L13 => run_generic(src, timeout, |s| L13_namespace::run(&s, 0)),
    }
}

// ---------------------------------------------------------------------------
// 语料
// ---------------------------------------------------------------------------

struct Prog {
    id: &'static str,
    group: &'static str,
    /// 该程序「最早已应支持」的层（用于把早期层的失败判成特性门而非回归）。
    min: Layer,
    /// 该程序每层的预期（ok / err / any-no-hang），供摘要快速标红。
    expect: &'static str,
    note: &'static str,
    src: &'static str,
}

// —— CORE（L07 即应支持）-----------------------------------------------------

const P_CORE_POLY_ID: &str = r#"enum Bool {
    true
    false
}

def id[A](x: A): A = x

println (id true)
println (id Bool)
"#;

const P_CORE_NAT_ADD: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def two = succ (succ zero)

println (add two two)
"#;

const P_CORE_GADT_HEAD: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Fin(len: Nat) {
    fzero[n: Nat] -> Fin (succ n)
    fsucc[n: Nat](i: Fin n) -> Fin (succ n)
}

def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }
println (head (cons zero nil))
"#;

const P_CORE_VEC_LEN_PROJ: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def two = succ (succ zero)

def three = succ (succ (succ zero))

def t = cons zero (cons two (cons three (cons two nil)))

println t.len
"#;

const P_CORE_IMPLICIT_PRINT: &str = r#"enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

println true
println false
println zero
println (succ zero)
println nil
println (cons true nil)
println (cons true (cons false nil))
println "hello world"
println Bool
"#;

const P_CORE_STUCK_PRIM: &str = r#"def mystr = "hello world"

def stuck_concat = string_concat mystr

println stuck_concat
println (stuck_concat "!")
"#;

const P_CORE_CTOR_ETA: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

println succ
"#;

const P_CORE_ILLTYPED_APP: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

println (succ zero zero)
"#;

const P_CORE_MISSING_CASE: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def f(x: Nat): Nat =
    match x {
        case zero => zero
    }
"#;

const P_CORE_UNREACHABLE_ARM: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def f(x: Nat): Nat =
    match x {
        case _ => zero
        case succ(n) => n
    }
"#;

const P_CORE_STUCK_MATCH: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def f(n: Nat): Nat -> Nat =
    match n {
        case zero => succ
        case succ(k) => succ
    }

println f
println (f zero)
println ((f zero) zero)
"#;

// —— STRUCT（L08+）----------------------------------------------------------

const P_STRUCT_SIMPLE: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

struct Pair2[A] {
    fst: A
    snd: A
}

def getf[A](p: Pair2[A]): A =
    match p {
        case Pair2 { fst, snd } => fst
    }
println (getf (Pair2.mk zero zero))
"#;

const P_STRUCT_PROJ_NEW: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

struct Point {
    x: Nat
    y: Nat
}

def two = succ (succ zero)

def p = new Point(two, zero)

println p
println p.x
"#;

const P_STRUCT_WEAK03: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Fin(len: Nat) {
    fzero[n: Nat] -> Fin (succ n)
    fsucc[n: Nat](i: Fin n) -> Fin (succ n)
}

struct Boxed[A, len: Nat] {
    vec: Vec[A] len
    wit: Fin (succ len)
}

def get_wit[A, len: Nat](b: Boxed[A, len]): Fin (succ len) =
    match b {
        case Boxed { nil, w } => w
        case Boxed { cons(x, xs), w } => w
    }
println (get_wit (Boxed.mk nil fzero))
"#;

const P_STRUCT_WEAK05: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Fin(len: Nat) {
    fzero[n: Nat] -> Fin (succ n)
    fsucc[n: Nat](i: Fin n) -> Fin (succ n)
}

struct VecHolder[A, len: Nat] {
    vec: Vec[A] len
    last: Fin (succ len)
}

def vec_last[A, len: Nat](vh: VecHolder[A, len]): A = match vh {
    case VecHolder { cons(x, xs), fzero } => x
    case VecHolder { cons(x, xs), fsucc(i) } => vec_last (new VecHolder(xs, i))
}
println (vec_last (VecHolder.mk (cons zero nil) fzero))
"#;

const P_STRUCT_WEAK02_ERR: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

struct WrapVec[A, len: Nat] {
    inner: Vec[A] len
}

def vtail[A, len: Nat](w: WrapVec[A, len]): Vec[A] len =
    match w {
        case WrapVec { nil } => nil
        case WrapVec { cons(x, xs) } => xs
    }
println (vtail (WrapVec.mk nil))
"#;

const P_STRUCT_WEAK04_ERR: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

struct Inner[A, len: Nat] {
    v: Vec[A] len
}
struct Outer[A, len: Nat] {
    inner: Inner[A, len]
}

def outer_tail_gen[A, len: Nat](o: Outer[A, len]): Vec[A] len =
    match o {
        case Outer { Inner { nil } } => nil
        case Outer { Inner { cons(x, xs) } } => xs
    }
println (outer_tail_gen (Outer.mk (Inner.mk nil)))
"#;

// —— UNIVERSE（L09+）--------------------------------------------------------

const P_UNIV_LEVELS: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def test0: Type 1 = Type 0

def test1: Type 2 = Type 1 -> Type 0

enum HighLvl[A] {
    case1(a: A)
    case2(a: test1)
}

def test2: HighLvl[Nat] = case1 zero

def test3: Type 2 = HighLvl[Nat]

println test0
println test1
println test3
"#;

const P_UNIV_ILLTYPED: &str = r#"enum Nat {
    zero
}

def bad : Type 0 = Type 1
"#;

const P_UNIV_STRUCT_HIGH: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def test1: Type 2 = Type 1 -> Type 0

def test2_t: Type 1 -> Type 0 = t => Nat

struct HighLvl[A] {
    case1: A
    case2: test1
}

def test2: HighLvl[Nat] = new HighLvl(zero, test2_t)

def test3: Type 2 = HighLvl[Nat]

println test3
"#;

// —— TRAIT（L10+）-----------------------------------------------------------

const P_TRAIT_TOSTRING: &str = r#"enum Bool {
    true
    false
}

trait ToString {
    def to_string: String
}

impl ToString for Bool {
    def to_string: String =
        match this {
            case true => "true"
            case false => "false"
        }
}

def t[T][s: ToString[T]](x: T): String =
    s.to_string x

println (t true)
println (t false)
"#;

const P_TRAIT_OUTPARAM: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def outParam[A](a: A): A = a

trait Add[T, O: outParam(Type 0)] {
    def add(that: T): O
}

def nat_add_helper(x: Nat, y: Nat): Nat =
    match y {
        case zero => x
        case succ(n) => succ (nat_add_helper x n)
    }

impl Add[Nat, Nat] for Nat {
    def add(that: Nat): Nat =
        nat_add_helper this that
}

def two = succ (succ zero)

def four = two.add two

println four
println (four.add four)
"#;

const P_TRAIT_BLANKET: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

trait Say {
    def say(x: Nat): String
}

impl[T] Say for T {
    def say(x: Nat): String = "hello"
}

println (zero.say zero)
"#;

const P_TRAIT_NO_INSTANCE: &str = r#"enum Bool {
    true
    false
}

trait Foo[T] {
    def foo(x: T): String
}

def bad[T](x: T): String = foo(x)

println (bad true)
"#;

// —— MACRO（L11+）-----------------------------------------------------------

const P_MACRO_STRINGIFY: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def x = 42

println (stringify t123)
"#;

const P_MACRO_DECL_LEVEL: &str = r#"macro_rules make_bool {
    (yes) => {
        enum Yes { y }
    }
}

make_bool yes

def b = y

println b
"#;

const P_MACRO_MODULE: &str = r#"macro_rules module {
    ($name: ident) => {def $name = string_concat("module ", stringify $name)}
}

module test2

println test2
"#;

const P_MACRO_DEPTH_GUARD: &str = r#"macro_rules m { () => { m } }
def x = m
"#;

// —— 语义断点（Lead 定向假设）-----------------------------------------------

const P_REDEFINE_DEF: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def dup : Nat = zero

def dup : Nat = succ zero

println dup
"#;

const P_REDEFINE_CTOR: &str = r#"enum Nat {
    zero
    succ(x: Nat)
}

def succ : Nat = zero

println succ
"#;

const P_PRIM_IDENTITY_BAD: &str = r#"enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def p(x: String): String = string_concat x "a"

def q(y: String): String = string_concat y "b"

def bad(x: String, y: String): Eq[String] (p x) (q y) = refl
"#;

const P_PRIM_IDENTITY_CTRL: &str = r#"enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def p(x: String): String = string_concat x "a"

def good(x: String): Eq[String] (p x) (p x) = refl
"#;

// rfl 显式构造子版本（L07/L08 黑盒惯例：enum 用显式参数 refl(a: A)，再经
// def rfl 包一层），用于把「裸隐式构造子 refl」因素与 prim 等式因素分开。
const P_PRIM_IDENTITY_BAD_RFL: &str = r#"enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq[A] a a
}

def rfl[A][a: A]: Eq[A] a a = refl a

def p(x: String): String = string_concat x "a"

def q(y: String): String = string_concat y "b"

def bad(x: String, y: String): Eq[String] (p x) (q y) = rfl
"#;

const P_PRIM_IDENTITY_CTRL_RFL: &str = r#"enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq[A] a a
}

def rfl[A][a: A]: Eq[A] a a = refl a

def p(x: String): String = string_concat x "a"

def good(x: String): Eq[String] (p x) (p x) = rfl
"#;

// —— L12 定向定位探针（core_vec_len_proj / core_implicit_print 的 L12 回归最小化）——

const P_L12_PROBE_NIL: &str = r#"enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

println nil
"#;

const P_L12_PROBE_CONS: &str = r#"enum Bool {
    true
    false
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

println (cons true nil)
"#;

const P_L12_PROBE_ENUM_ANNOT: &str = r#"enum Bool {
    true
    false
}

enum List[A : Type 0] {
    nil
    cons(head: A, tail: List[A])
}

println (cons true nil)
"#;

const P_MATCH_CMP_STUCK: &str = r#"enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def f(x: Bool): Nat =
    match x {
        case true => zero
        case false => zero
    }

def g(y: Bool): Nat =
    match y {
        case true => zero
        case false => zero
    }

def bad(p: Bool, q: Bool): Eq[Nat] (f p) (g q) = refl
"#;

// —— L13 语言面（L13 only）--------------------------------------------------

const P_L13_PACKAGE: &str = r#"package demo

enum Nat {
    zero
    succ(x: Nat)
}

def two : Nat = succ (succ zero)

println two
"#;

const PROGS: &[Prog] = &[
    Prog { id: "core_poly_id", group: "CORE", min: Layer::L07, expect: "ok", note: "多态 id + 隐式实参推断", src: P_CORE_POLY_ID },
    Prog { id: "core_nat_add", group: "CORE", min: Layer::L07, expect: "ok", note: "Nat 递归 match + 求值", src: P_CORE_NAT_ADD },
    Prog { id: "core_gadt_head", group: "CORE", min: Layer::L07, expect: "ok", note: "enum Vec/Fin 索引 + 依赖 match（GADT head）", src: P_CORE_GADT_HEAD },
    Prog { id: "core_vec_len_proj", group: "CORE", min: Layer::L07, expect: "ok", note: "Sum 索引投影 t.len", src: P_CORE_VEC_LEN_PROJ },
    Prog { id: "core_implicit_print", group: "CORE", min: Layer::L07, expect: "ok", note: "隐式参数 binding/构造子打印（[] vs {} 漂移点）", src: P_CORE_IMPLICIT_PRINT },
    Prog { id: "core_stuck_prim", group: "CORE", min: Layer::L07, expect: "ok", note: "卡住 string_concat 的打印/再应用", src: P_CORE_STUCK_PRIM },
    Prog { id: "core_ctor_eta", group: "CORE", min: Layer::L07, expect: "ok", note: "构造子函数值 η 展开显示", src: P_CORE_CTOR_ETA },
    Prog { id: "core_illtyped_app", group: "CORE", min: Layer::L07, expect: "err", note: "ill-typed 应用应拒", src: P_CORE_ILLTYPED_APP },
    Prog { id: "core_missing_case", group: "CORE", min: Layer::L07, expect: "err", note: "覆盖不全应拒（诊断面）", src: P_CORE_MISSING_CASE },
    Prog { id: "core_unreachable_arm", group: "CORE", min: Layer::L07, expect: "err", note: "通配臂后的不可达臂（诊断面）", src: P_CORE_UNREACHABLE_ARM },
    Prog { id: "core_stuck_match", group: "CORE", min: Layer::L07, expect: "ok", note: "卡住 match 值打印/应用/splice", src: P_CORE_STUCK_MATCH },
    Prog { id: "struct_simple", group: "STRUCT", min: Layer::L08, expect: "ok", note: "struct 声明 + Name { .. } 模式糖（2026-11-15 修复点）", src: P_STRUCT_SIMPLE },
    Prog { id: "struct_proj_new", group: "STRUCT", min: Layer::L08, expect: "ok", note: "struct 投影 + new + 值打印", src: P_STRUCT_PROJ_NEW },
    Prog { id: "struct_weak03", group: "STRUCT", min: Layer::L08, expect: "ok", note: "跨字段 GADT 精化（well-typed）", src: P_STRUCT_WEAK03 },
    Prog { id: "struct_weak05", group: "STRUCT", min: Layer::L08, expect: "ok", note: "VecHolder 递归交叉精化（well-typed；本轮重点）", src: P_STRUCT_WEAK05 },
    Prog { id: "struct_weak02_err", group: "STRUCT", min: Layer::L08, expect: "err", note: "单层 struct 返回尾 ill-typed 应拒", src: P_STRUCT_WEAK02_ERR },
    Prog { id: "struct_weak04_err", group: "STRUCT", min: Layer::L08, expect: "err", note: "嵌套 struct 返回尾 ill-typed 应拒", src: P_STRUCT_WEAK04_ERR },
    Prog { id: "univ_levels", group: "UNIVERSE", min: Layer::L09, expect: "ok", note: "Type 0/1/2 层级 + 高宇宙 enum", src: P_UNIV_LEVELS },
    Prog { id: "univ_illtyped", group: "UNIVERSE", min: Layer::L09, expect: "err", note: "层级不等应拒", src: P_UNIV_ILLTYPED },
    Prog { id: "univ_struct_high", group: "UNIVERSE", min: Layer::L09, expect: "ok", note: "high-universe struct 打印", src: P_UNIV_STRUCT_HIGH },
    Prog { id: "trait_tostring", group: "TRAIT", min: Layer::L10, expect: "ok", note: "trait/impl + 约束传递方法", src: P_TRAIT_TOSTRING },
    Prog { id: "trait_outparam", group: "TRAIT", min: Layer::L10, expect: "ok", note: "outParam trait + 接收者方法 + 算符方法", src: P_TRAIT_OUTPARAM },
    Prog { id: "trait_blanket", group: "TRAIT", min: Layer::L10, expect: "ok", note: "毛毯实例 impl[T] Say for T", src: P_TRAIT_BLANKET },
    Prog { id: "trait_no_instance", group: "TRAIT", min: Layer::L10, expect: "err", note: "无实例 trait 调用（可恢复 Err vs panic）", src: P_TRAIT_NO_INSTANCE },
    Prog { id: "macro_stringify", group: "MACRO", min: Layer::L11, expect: "ok", note: "stringify 内建宏", src: P_MACRO_STRINGIFY },
    Prog { id: "macro_decl_level", group: "MACRO", min: Layer::L11, expect: "ok", note: "声明级宏展开成 enum", src: P_MACRO_DECL_LEVEL },
    Prog { id: "macro_module", group: "MACRO", min: Layer::L11, expect: "ok", note: "声明级宏 + stringify 生成 def", src: P_MACRO_MODULE },
    Prog { id: "macro_depth_guard", group: "MACRO", min: Layer::L11, expect: "any-no-hang", note: "自递归宏深度守卫：不得栈溢出/挂死", src: P_MACRO_DEPTH_GUARD },
    Prog { id: "redefine_def", group: "SEMANTIC", min: Layer::L07, expect: "err", note: "同名 def 重复定义（L09/L10 README 声称静默覆盖 vs 实测）", src: P_REDEFINE_DEF },
    Prog { id: "redefine_ctor", group: "SEMANTIC", min: Layer::L07, expect: "err", note: "def 撞构造子裸名", src: P_REDEFINE_CTOR },
    Prog { id: "prim_identity_bad", group: "SEMANTIC", min: Layer::L07, expect: "err", note: "不同实参的卡住 prim 应用被 Eq 判等？(P x) vs (Q y)", src: P_PRIM_IDENTITY_BAD },
    Prog { id: "prim_identity_ctrl", group: "SEMANTIC", min: Layer::L07, expect: "ok", note: "同实参 prim 应用 Eq 正控（不得误拒）", src: P_PRIM_IDENTITY_CTRL },
    Prog { id: "prim_identity_bad_rfl", group: "SEMANTIC", min: Layer::L07, expect: "err", note: "rfl 显式版：不同实参卡住 prim 应拒（分离裸构造子因素）", src: P_PRIM_IDENTITY_BAD_RFL },
    Prog { id: "prim_identity_ctrl_rfl", group: "SEMANTIC", min: Layer::L07, expect: "ok", note: "rfl 显式版：同实参卡住 prim 不得误拒", src: P_PRIM_IDENTITY_CTRL_RFL },
    Prog { id: "l12_probe_nil", group: "L12PROBE", min: Layer::L07, expect: "ok", note: "L12 定位：泛型 nil 值打印", src: P_L12_PROBE_NIL },
    Prog { id: "l12_probe_cons", group: "L12PROBE", min: Layer::L07, expect: "ok", note: "L12 定位：cons true nil（core_implicit_print 失败点最小化）", src: P_L12_PROBE_CONS },
    Prog { id: "l12_probe_enum_annot", group: "L12PROBE", min: Layer::L09, expect: "ok", note: "L12 定位：显式标注隐式域 [A : Type 0] 是否规避失败", src: P_L12_PROBE_ENUM_ANNOT },
    Prog { id: "match_cmp_stuck", group: "SEMANTIC", min: Layer::L07, expect: "err", note: "两个卡住 match 的相等比较（MATCH_CMP_BUDGET 覆盖面）", src: P_MATCH_CMP_STUCK },
    Prog { id: "l13_package", group: "L13SURF", min: Layer::L13, expect: "ok", note: "package 命名空间（L13 语言面 gate）", src: P_L13_PACKAGE },
];

fn timeout_for(prog: &Prog) -> Duration {
    match prog.id {
        "match_cmp_stuck" => Duration::from_secs(10),
        "macro_depth_guard" => Duration::from_secs(15),
        _ => Duration::from_secs(20),
    }
}

// ---------------------------------------------------------------------------
// 矩阵测试
// ---------------------------------------------------------------------------

#[test]
fn probe_cross_layer_matrix() {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(".audit/raw-correctness");
    std::fs::create_dir_all(&dir).expect("create .audit/raw-correctness");
    let matrix_path = dir.join("probe-matrix.tsv");
    let progs_path = dir.join("probe-programs.tsv");

    let mut progs_out = std::fs::File::create(&progs_path).expect("create programs tsv");
    writeln!(progs_out, "prog\tgroup\tmin_layer\texpect\tnote\tsrc").unwrap();
    for p in PROGS {
        writeln!(
            progs_out,
            "{}\t{}\t{}\t{}\t{}\t{}",
            p.id,
            p.group,
            p.min.name(),
            p.expect,
            p.note,
            esc(p.src, 4000)
        )
        .unwrap();
    }
    progs_out.flush().unwrap();

    let mut f = std::fs::File::create(&matrix_path).expect("create matrix tsv");
    writeln!(f, "prog\tgroup\tmin_layer\texpect\tlayer\tkind\tclass\thash\ttext").unwrap();
    f.flush().unwrap();

    println!("PROBE-BEGIN\tprogs={}", PROGS.len());
    for prog in PROGS {
        let tmo = timeout_for(prog);
        let mut collected: Vec<(Layer, Outcome)> = Vec::new();
        for layer in LAYERS {
            let t0 = std::time::Instant::now();
            let out = run_layer(layer, prog.src, tmo);
            let dt = t0.elapsed();
            writeln!(
                f,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                prog.id,
                prog.group,
                prog.min.name(),
                prog.expect,
                layer.name(),
                out.kind(),
                out.class(),
                out.hash_hex(),
                esc(&out.text(), 400)
            )
            .unwrap();
            f.flush().unwrap();
            println!(
                "PROBE\t{}\t{}\t{}\t{}\t{}\t{}\t{}ms\t{}",
                prog.id,
                prog.group,
                prog.min.name(),
                layer.name(),
                out.kind(),
                out.class(),
                dt.as_millis(),
                esc(&out.text(), 160)
            );
            collected.push((layer, out));
        }
        // 摘要：按 (kind,class,hash) 分组，一眼看到断点/漂移。
        let mut groups: Vec<(String, Vec<&'static str>)> = Vec::new();
        for (layer, out) in &collected {
            let key = format!("{}:{}:{}", out.kind(), out.class(), out.hash_hex());
            let mut hit: Option<usize> = None;
            for i in 0..groups.len() {
                if groups[i].0 == key {
                    hit = Some(i);
                    break;
                }
            }
            match hit {
                Some(i) => groups[i].1.push(layer.name()),
                None => groups.push((key, vec![layer.name()])),
            }
        }
        println!(
            "PROBE-SUMMARY\t{}\t{}",
            prog.id,
            groups
                .iter()
                .map(|(k, ls)| format!("{}={}", k, ls.join(",")))
                .collect::<Vec<_>>()
                .join(" | ")
        );
    }
    println!("PROBE-END\t{}", matrix_path.display());
}
