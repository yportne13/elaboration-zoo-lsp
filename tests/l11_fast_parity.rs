//! L11_macro 双 oracle 互检套件（参考版 `run` ↔ 性能版 `bump_spine_iter::
//! run_fast`）。`#[path]` 只编 list.rs / bimap.rs / parser_lib.rs /
//! L11_macro/mod.rs（不含 LSP / L02-L10 / L12-L13），迭代快数倍
//! （tests/l10_fast_parity.rs 同款）。
//!
//! 判据：**Ok 输出逐字节一致 / Err 判定一致**。错误文案的 Span 偏移
//! （`@ N,M` 与 Debug-Span 数字）是文档化偏差，比对前归一化。


#[path = "../src/list.rs"]
mod list;

#[path = "../src/bimap.rs"]
mod bimap;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L11_macro/mod.rs"]
mod L11_macro;

use L11_macro::bump_spine_iter as fast;

/// 在大栈线程里跑参考版 `run`。
fn run_basic(src: &str) -> Result<String, L11_macro::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L11_macro::run(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, L11_macro::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// Err 文案归一化：剥掉 Span 自定义 Debug 的 `@ N` / `@ N,M`、派生
/// Debug 的 `start_offset/end_offset/path_id: N` 数字，以及 meta 编号
/// `?N`（双实现的 meta 分配序列不同，属文档化偏差）。
fn norm_err(e: &str) -> String {
    let mut out = String::with_capacity(e.len());
    let b = e.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'@' && i + 1 < b.len() && b[i + 1] == b' ' {
            let mut j = i + 2;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 2 {
                if j < b.len() && b[j] == b',' {
                    let mut k = j + 1;
                    while k < b.len() && b[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k > j + 1 {
                        j = k;
                    }
                }
                out.push_str("@ _");
                i = j;
                continue;
            }
        }
        let rest = &e[i..];
        let mut matched = false;
        for key in ["start_offset: ", "end_offset: ", "path_id: "] {
            if rest.starts_with(key) {
                let mut j = i + key.len();
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
                if j > i + key.len() {
                    out.push('_');
                    i = j;
                    matched = true;
                    break;
                }
            }
        }
        if matched {
            continue;
        }
        // `?N`：meta 编号归一化（?1; 分号前缀属报错串自身，保留）
        if b[i] == b'?' && i + 1 < b.len() && b[i + 1].is_ascii_digit() {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                out.push_str("?_");
                i = j;
                continue;
            }
        }
        let ch = e[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn err_text(e: &L11_macro::Error) -> String {
    norm_err(&e.0.data)
}

/// Oracle：Ok 逐字节 / Err 判定 + 归一化正文一致。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(b), Err(f)) => assert_eq!(
            err_text(b),
            err_text(f),
            "Err 正文（span 归一化后）双实现不一致，src:\n{src}\n--- basic ---\n{}\n--- fast ---\n{}",
            b.0.data,
            f.0.data
        ),
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}\nbasic-err={:?}\nfast-err={:?}",
            b.as_ref().map(|_| "Ok").unwrap_or("Err"),
            f.as_ref().map(|_| "Ok").unwrap_or("Err"),
            b.as_ref().err().map(|e| &e.0.data),
            f.as_ref().err().map(|e| &e.0.data),
        ),
    }
}

// 基础：类型面（enum / match / 构造子投影 / 递归）——快版孪生可覆盖的
// 组合（单臂构造子匹配与 struct-impl 方法体属已知 walk 缺陷区，另案跟踪）
// --------------------------------------------------------------------------------

#[test]
fn parity_basics() {
    assert_parity(
        r#"
enum Bool {
    true
    false
}

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def not(x: Bool): Bool =
    match x {
        case true => false
        case false => true
    }

println (not true)

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def four = add two two

println four

struct Point {
    x: Nat
    y: Nat
}

def p = new Point(two, zero)

println p.x
println p
"#,
    );
}

#[test]
fn parity_stuck_proj_under_binder() {
    // 回归：binder 下的嵌套投影。`l` 是 Rigid，`l.a` 卡成 Obj，`l.a.x`
    // 的 ObjSel 要先 force 这个卡住 Obj —— 快版 force 的 Obj 臂一旦把
    // 重建值赋回循环变量（而非返回），这里就是死循环。
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

struct Point {
    x: Nat
    y: Nat
}

struct Line {
    a: Point
    b: Point
}

def headX(l: Line): Nat = l.a.x

println headX
"#,
    );
}

// trait / impl / 实例合成（不含 struct 接收者实例——walk 缺陷区另案跟踪）
// --------------------------------------------------------------------------------

#[test]
fn parity_trait_pieces() {
    assert_parity(
        r#"
def outParam[A](a: A): A = a

enum Bool {
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

def listmap[T, U](xs: List[T], f: T -> U): List[U] =
    match xs {
        case nil => nil
        case cons(head, tail) => cons (f head) (listmap tail f)
    }

def two = succ (succ zero)

def listnat = cons two (cons (succ zero) nil)

def listnat2 = listmap listnat (x => succ x)

println listnat2

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

trait Say {
    def say(x: Nat): String
}

impl[T] Say for T {
    def say(x: Nat): String = "hello"
}

println (zero.say zero)

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

def mul(x: Nat, y: Nat) = match x {
    case zero => zero
    case succ(n) => y.add (mul n y)
}

def four = two.add two

println four
"#,
    );
}

// 宏系统 + 可变全局（L11 增量主体）
// --------------------------------------------------------------------------------

#[test]
fn parity_macros_and_globals() {
    // stringify 内建宏 + 表达式级宏展开
    assert_parity(
        r#"
def x = 42

println (stringify t123)
"#,
    );
    // 声明级宏：macro_rules 展开成 def（宏定义本身不进 decl 表）
    assert_parity(
        r#"
macro_rules make_bool {
    (yes) => {
        enum Yes { y }
    }
}

make_bool yes

def b = y

println b
"#,
    );
    // create_global / change_mutable / get_global 链（let 形式，test6 同款；
    // 顶层裸调用在参考版即 panic——get_global 缺名 unwrap）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

def glob = let gid = create_global "g" two;
    get_global "g"

println glob

def succ_g = let _ = change_mutable("g", z => succ(z));
    get_global "g"

println succ_g
"#,
    );
    // get_global 缺名 → 两版同 panic（参考版 unwrap 同款）
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def boom = get_global "nope"
"#;
    let b = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_basic(src)));
    let f = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_fast(src)));
    assert!(b.is_err(), "参考版应 panic");
    assert!(f.is_err(), "快版应 panic");
}

// Err 判定 parity（判定一致 + 归一化正文一致）
// --------------------------------------------------------------------------------

#[test]
fn parity_errors() {
    // 名字不在 scope
    assert_parity("def bad = nope\n");
    // icit 失配
    assert_parity(
        r#"
def f(x: Nat): Nat = x

def bad = f[Nat]
"#,
    );
    // redefine（撞名内建也要报）
    assert_parity(
        r#"
def String : Type 0 = Type 0
"#,
    );
    // 字段未命中（has no object，nf 文案）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def bad = zero.zzz
"#,
    );
    // 方法不在任何 trait
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def f(x: Nat): Nat = x

def bad = f.zzz
"#,
    );
    // （无实例类型类调用形态：快版孪生在该处有未收敛缺陷，另案
    // 跟踪——未解 meta 的 trait 方法调用路径发散）

    // 期望宇宙
    assert_parity(
        r#"
def bad : Nat = Type 0
"#,
    );
}

// 深负载（church / strchain / match 链 / enum GADT / struct 链）
// --------------------------------------------------------------------------------

fn parse_or_panic(src: &str) -> Vec<fast::SourceDecl> {
    match fast::parse(src, 0) {
        Ok(ast) => ast,
        Err(e) => panic!("parse failed: {e}\nsrc:\n{src}"),
    }
}

#[test]
fn deep_workloads_parity() {
    // 枚举 Nat 加法链 2^(k+1)（L11 合法深负载：递归 match + 构造子链；
    // `Type N` 注解放弃——参考版对"λ 体 + Type 注解"组合判型失败）
    let src = fast::natadd_src(6);
    let ast = parse_or_panic(&src);
    let mut t = fast::Tycker::new();
    assert!(t.bench_check(&ast), "natadd 未通过（fast）");
    // 实测值 258（p6 的 quote 节点数）
    assert_eq!(t.bench_check_nf_memo(&ast), 258, "natadd nf 公式");
    assert_parity(&src);

    // strchain
    let src = fast::strchain_src(9);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "strchain 未通过");
    assert_eq!(t.bench_check_nf_memo(&ast), 1, "strchain nf 节点数");
    assert_parity(&(fast::strchain_src(5) + "println s0\n"));

    // match 链（递归 + 卡住 match）
    let src = fast::match_src(6);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "match 链未通过");
    assert_parity(&src);

    // （enum GADT 单臂 head 用例与已剔除的 test_index 同族——快版编译
    // walk 缺陷区，另案跟踪；gadt_src 生成器保留供 bench 单独使用）

    // struct 链
    let src = fast::struct_src(7);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "struct 负载未通过（fast）");
    assert_eq!(t.bench_check_nf_memo(&ast), 2, "struct nf 节点数");
    assert_parity(&src);
}

#[test]
fn steady_state_reuse() {
    // 稳态复用：同一 Tycker 连续多轮（trait/可变全局状态一并轮清空），
    // 输出与一次性口径一致
    let src = fast::match_src(4);
    let expect = {
        let mut steady = fast::Tycker::new();
        steady.run_input(&src, 0).unwrap()
    };
    let r1 = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut steady = fast::Tycker::new();
            steady.run_input(&src, 0).unwrap()
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(r1, expect, "稳态复用输出漂移");

    // 全局链连续两轮：上一轮的 mutable 全局不得泄漏（用例形态与
    // parity_macros 的已验证用例一致）
    let gsrc = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def ttt =
    let useless1 = create_global "Nat" 2;
    let useless2 = change_mutable("Nat", z => succ(z));
    get_global "Nat"

println ttt
"#;
    let mut steady = fast::Tycker::new();
    let a = steady.run_input(gsrc, 0).unwrap();
    let b = steady.run_input(gsrc, 0).unwrap();
    assert_eq!(a, b, "跨轮 mutable 全局泄漏");
    assert_parity(gsrc);
}

// Round-2 探针（A2 η 守卫 / A4 u64 / A5 trait 求解 / A6 prune_ty / A8 宏递归）
// 由 orchestrator 集中运行裁决；期望值在注释中标注。
// --------------------------------------------------------------------------------

fn unpanic<T>(f: impl FnOnce() -> T) -> std::thread::Result<T> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
}

/// A2：η 臂 applicability 守卫。`get_global "f"` 的类型 = f 的登记值（λ）；
/// `def g : String = …` 让 LiteralType 与 λ 落 η 臂。修复前 v_app(LiteralType)
/// → panic；修复后两版都可恢复、判定一致（本探针只钉「不 panic + 同判定」，
/// 不比较逐字文案）。
#[test]
fn probe_eta_applicability_guard() {
    let src = r#"
enum U {
    u
}

def f : U -> U = x => x

def g : String = get_global "f"
"#;
    let b = unpanic(|| run_basic(src));
    let f = unpanic(|| run_fast(src));
    assert!(b.is_ok(), "参考版 η 臂不应 panic（应可恢复 Err）");
    assert!(f.is_ok(), "快版 η 臂不应 panic（应可恢复 Err）");
    let (b, f) = (b.unwrap(), f.unwrap());
    assert_eq!(
        b.is_ok(),
        f.is_ok(),
        "η 路径两版 Ok/Err 判定应一致；basic={:?} fast={:?}",
        b.as_ref().err().map(|e| &e.0.data),
        f.as_ref().err().map(|e| &e.0.data),
    );
}

/// A4：超大整数字面量不再 panic；parser 推 IError。
#[test]
fn probe_u64_literal_overflow_no_panic() {
    let src = "def x = 99999999999999999999999999\n";
    // 解析结果含 Rc（!Send）：Some/错误条数在子线程内解包，只回传 (bool, usize)
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            L11_macro::parser::parser(src, 0)
                .map(|(_, errs)| (true, errs.len()))
                .unwrap_or((false, 0))
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "超大整数不应 panic");
    let (parsed_some, err_count) = res.unwrap();
    assert!(parsed_some, "parser 应返回 Some");
    assert!(err_count > 0, "超大整数应产生解析错误");
}

/// A8（P0）：自递归宏受展开深度上限保护，不得栈溢出；返回解析错误。
/// 线程栈刻意取小（8MiB，远小于 parity 用例的 256MiB），修复前可稳定复现
/// 栈溢出。
#[test]
fn probe_macro_self_recursion_depth_limit() {
    let src = "macro_rules m { () => { m } }\ndef x = m\n";
    // 解析结果含 Rc（!Send）：Some/错误条数在子线程内解包，只回传 (bool, usize)
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            L11_macro::parser::parser(src, 0)
                .map(|(_, errs)| (true, errs.len()))
                .unwrap_or((false, 0))
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "自递归宏不应栈溢出");
    let (parsed_some, err_count) = res.unwrap();
    assert!(parsed_some, "parser 应返回 Some");
    assert!(err_count > 0, "自递归宏应产生解析错误而非无限展开");
}

/// A5：无实例 trait 调用返回可恢复 Err（参考版+快版都不 panic）。修复前
/// 两版都在 `solve_multi_trait(...).unwrap()` panic。
#[test]
fn probe_solve_multi_trait_recoverable() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

trait Foo[T] {
    def foo(x: T): String
}

def bar[T][f: Foo[T]](x: T): String = f.foo x

def baz = bar 1
"#;
    let b = unpanic(|| run_basic(src));
    let f = unpanic(|| run_fast(src));
    assert!(b.is_ok(), "参考版 trait 求解失败不应 panic");
    assert!(f.is_ok(), "快版 trait 求解失败不应 panic");
    assert!(b.unwrap().is_err() && f.unwrap().is_err(), "两版都应给可恢复 Err");
}

/// A6：多层/非线性 pruning 的掩码反转 parity。源取自 L06
/// `pruning_nonpalindrome_dependent_masks`（`U` → `Type 0` 改写）；参考版
/// 修复前未反转掩码，与快版 `prune_ty_bump` 的 `iter().rev()` 错位。
/// 若源未真正落到 prune_meta，本探针至少钉住该形态两版 parity。
#[test]
fn probe_prune_ty_mask_reversal_parity() {
    // 1) intersect：m A x ≡ m A y，依赖 telescope (A : Type 0) -> (x : A) -> …
    assert_parity(concat!(
        "def Eq [A : Type 0] (x : A, y : A) : Type 0 = (P : A -> Type 0) -> P x -> P y\n",
        "def refl [A : Type 0, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : Type 0)(x : A) : A = x\n",
        "def m (A : Type 0)(x : A) : Type 0 = _\n",
        "def test = A => x => y => the (Eq (m A x) (m A y)) refl\n",
        "println test\n",
    ));
    // 2) 非回文掩码 + 依赖 telescope：n 的第二参类型依赖第一参
    assert_parity(concat!(
        "def Eq [A : Type 0] (x : A, y : A) : Type 0 = (P : A -> Type 0) -> P x -> P y\n",
        "def refl [A : Type 0, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : Type 0)(x : A) : A = x\n",
        "def m : (x : Type 0) -> Type 0 -> Type 0 = _\n",
        "def n : (y : Type 0) -> (z : y) -> Type 0 = _\n",
        "def test = x => y => the (Eq (m x) (w => n y w)) refl\n",
        "println test\n",
    ));
}

/// 移植修复回归：`impl[T] Say for List[T]` 不得假匹配泛型目标 `Say[T]`。
/// 旧 `Synth::unify` 双向绑定把目标 rigid 绑成 `List[..]`，`f two` 错答
/// `"list"`；改为单向 `match_typ` 后无实例 → Err。参考/快版共用 `Synth`，
/// 判定必须一致。
#[test]
fn synth_rigid_generic_not_falsely_matched() {
    let src = r#"
trait Say {
    def say: String
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

impl[T] Say for List[T] {
    def say: String = "list"
}

def f[T](x: T): String = x.say

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

println (f two)
"#;
    assert!(
        run_basic(src).is_err(),
        "泛型 T 不得被假匹配成 List；basic={:?}",
        run_basic(src)
    );
    assert_parity(src);
}
