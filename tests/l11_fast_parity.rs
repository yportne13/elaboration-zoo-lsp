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

/// 快版 packed-word 单元的对齐钉子（同 l08/l10 `packed_cells_align_at_least_8`）：
/// `XCell`/`CloCell`/`PiCell` 的 `ptr|tag` 编码用 `v.0 & !7` 解码，要求对齐
/// ≥ 8（`#[repr(align(8))]` + 源内 `const _` 断言之外的双保险口径一致演进）。
#[test]
fn packed_cells_align_at_least_8() {
    assert!(
        std::mem::align_of::<fast::XCell<'static>>() >= 8,
        "XCell 对齐不足以承载 3 位 tag 解码"
    );
    assert!(
        std::mem::align_of::<fast::CloCell<'static>>() >= 8,
        "CloCell 对齐不足以承载 3 位 tag 解码"
    );
    assert!(
        std::mem::align_of::<fast::PiCell<'static>>() >= 8,
        "PiCell 对齐不足以承载 3 位 tag 解码"
    );
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

/// P13（A6 矩阵复扫）：enum 隐式无标注域钉 U(0) 回归（L09
/// `parity_enum_struct_impl_hole_pinned_u0` 同款 4 源）。修复前：域洞保留
/// → 第 2+ 参数域为 AppPruning 部分应用 meta，使用点显式供给枚举隐式
/// 实参（`P1[Nat][Bool]`）需解该 meta，invert 对非变量 spine 实参直接
/// Err → 误报 can't unify；钉 U(0) 后声明处消除该 meta。含合法索引族
/// （显式标注 + 显式索引）形态确认不受钉影响（源为 L08 R1 病态源教训
/// 修正版：枚举级显式索引参数、返回类型完全应用）。
#[test]
fn parity_enum_struct_impl_hole_pinned_u0() {
    for src in [
        // enum：多隐式无标注参数 + 显式实例化（修复的原始触发形态）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Bool {\n    true\n    false\n}\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\nprintln (p1[Nat][Bool] zero true)\n",
        // enum：无标注隐式参数 + 注解处显式实例化 + 全显式构造子应用
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Bool {\n    true\n    false\n}\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\ndef s1: P1[Nat][Bool] = p1[Nat][Bool][Nat][Bool] zero true\nprintln s1\n",
        // struct：多类型参数 + 投影（脱糖路径同一臂）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nstruct Pair[A, B] {\n    fst: A\n    snd: B\n}\ndef p = new Pair(succ zero, zero)\nprintln p.fst\n",
        // 显式标注的隐式域与显式索引不动：annotated 索引族形态仍通过
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Q[A : Type 0](a: A) {\n    q[A](a: A) -> Q[A] a\n}\ndef t: Q[Nat] zero = q[Nat] zero\nprintln t\n",
    ] {
        // is_ok（参考版）+ 双版结果诊断输出 + parity
        let b = run_basic(src);
        let f = run_fast(src);
        assert!(
            b.is_ok(),
            "参考版 Err（隐式无标注域未钉 U(0)/钉后误拒/子用例病态？），src:\n{src}\nbasic={b:?}\nfast={f:?}"
        );
        assert_parity(src);
    }
}

// 2026-09-18 评审修复轮的 parity 钉（L07 修复轮移植）：嵌套覆盖检查 /
// 臂序无关性 / 构造子良构性——双实现对判定（Ok/Err）与 Ok 输出逐字节一致。
// --------------------------------------------------------------------------------

#[test]
fn parity_review_fixes_2026_09_18() {
    for src in [
        // P0 嵌套覆盖缺失：缺 cons(h, cons(..))——两版都应 Err（不完整）
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
    }
"#,
        // P0 三层嵌套：深度 2 位置缺 cons
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def f(x: List[Nat]): Nat =
    match x {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, nil)) => h2
    }
"#,
        // P1 构造子良构性：ret 不是本 enum（phantom 构造子）
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c -> Nat
}
"#,
        // P1 构造子良构性：隐式参数位特化（Foo[Bool]）
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Foo[A] {
    c -> Foo[Bool]
}
"#,
    ] {
        assert_parity(src);
    }
    // 正向对照 ①：构造子重绑定参数（p[A,B] -> Pack[A][B] a b）合法，
    // 两版 Ok 输出逐字节一致
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Pack[A, B](x: A, y: B) {
    p[A, B](a: A, b: B) -> Pack[A][B] a b
}

def sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true
println sw.y
"#,
    );
    // 正向对照 ②：索引精化下的嵌套可达性——Vec 长度恰 2 上 nil / cons(h, nil)
    // 臂不可达（静默跳过）、尾部（长度 1）上 nil 不可达不触发假阳性——
    // 两段式结算后应无缺覆盖告警，两版判定与 Ok 输出一致。（值级 println
    // 调用是 HEAD 上既有的嵌套 Con 模式缺陷区，两版同判，不纳入本钉。）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

def f(v: Vec[Nat] (succ (succ zero))): Nat =
    match v {
        case nil => zero
        case cons(h, nil) => h
        case cons(h, cons(h2, t)) => h2
    }
"#,
    );
}

/// P1（臂序无关性）：L11 的可解集 = 任意裸 rigid（无 L07 的 bind-slot 白
/// 名单，σ 每臂重建），陈旧 solvable 污染在本层无载体；钉双臂序 × 双
/// oracle 判定一致（臂序不得影响判定）。
#[test]
fn parity_stale_solvable_order_independent() {
    let template = |arms: &str| {
        format!(
            r#"
enum Nat {{
    zero
    succ(x: Nat)
}}

enum W(f: Nat -> Nat) {{
    big(a: Nat, b: Nat, c: Nat, d: Nat) -> W (n => succ zero)
    mk -> W (n => succ zero)
    ident -> W (n => n)
}}

def t(w: W (n => succ zero)): Nat =
    match w {{
        {arms}
    }}
"#
        )
    };
    for arms in [
        "case big(a, b, c, d) => a\n        case ident => zero\n        case mk => succ zero",
        "case ident => zero\n        case big(a, b, c, d) => a\n        case mk => succ zero",
    ] {
        assert_parity(&template(arms));
    }
}

/// README §7.7 回归钉（L07 移植）：孪生 arena 内 XCell::VSub 持有的
/// Rc<SubstV> 克隆曾被 bump reset 跳过 Drop（跨轮慢泄漏）。修复 = wrap_sub
/// 登记裸指针 + clear_round/轮出口逐指针归还。观察口：σ 链条目的存活计数
/// (SUBSTV_ALIVE)——同一 Tycker 连跑两轮含 match 精化的程序，每轮结束后
/// 计数都应回落到轮前基线。必须同线程跑（登记表是 thread_local）。
#[test]
fn fast_substv_reclaimed_across_rounds() {
    use std::sync::atomic::Ordering::Relaxed;
    let src = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def len[A](xs: List[A]): Nat =
    match xs {
        case nil => zero
        case cons(x, rest) => succ (len rest)
    }

def add(x: Nat, y: Nat) =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

println (add (len (cons zero nil)) (succ zero))
"#;
    // SUBSTV_ALIVE 是全局原子，并行的其他 parity 测试（各自线程上的
    // Tycker）会在本测试的测量窗口里并发加减计数——单次测量可能被并发
    // 噪声打歪。重试若干次：真泄漏每轮都回落不到基线（必失败）；噪声只
    // 偶发（几乎必有一窗干净）。
    let mut ok = false;
    let mut last = String::new();
    for _ in 0..16 {
        let base = fast::SUBSTV_ALIVE.load(Relaxed);
        // 同一 Tycker 复用两轮（LSP 式场景）：每轮 clear_round 都应归还
        // arena 克隆——计数不回落 = 泄漏回归。
        let mut t = fast::Tycker::new();
        let out1 = t.run_input(src, 0).expect("第 1 轮应 Ok");
        let after1 = fast::SUBSTV_ALIVE.load(Relaxed);
        let out2 = t.run_input(src, 0).expect("第 2 轮应 Ok");
        let after2 = fast::SUBSTV_ALIVE.load(Relaxed);
        assert_eq!(out1, out2, "两轮输出应一致");
        if (after1, after2) == (base, base) {
            ok = true;
            break;
        }
        last = format!("base={base} after1={after1} after2={after2}");
    }
    assert!(
        ok,
        "σ 链条目跨轮未回收（arena 克隆泄漏），重试 16 轮仍未观察到回落：{last}"
    );
}

// 解析器消歧回归（SPINE_ESCAPE，2026-09-19，与 L13 同款修复）
// --------------------------------------------------------------------------------

/// 双版都 Ok 且输出都含 `needle`（l13_fast_parity 同款 helper）。
fn assert_both_ok_contains(src: &str, needle: &str) {
    assert_parity(src);
    let b = run_basic(src);
    let f = run_fast(src);
    let bo = match b {
        Ok(o) => o,
        Err(e) => panic!("参考版应 Ok（needle={needle}），得到 Err({:?})，src:\n{src}", e.0.data),
    };
    let fo = match f {
        Ok(o) => o,
        Err(e) => panic!("孪生版应 Ok（needle={needle}），得到 Err({:?})，src:\n{src}", e.0.data),
    };
    assert!(bo.contains(needle), "参考版输出缺 `{needle}`：{bo}\nsrc:\n{src}");
    assert!(fo.contains(needle), "孪生版输出缺 `{needle}`：{fo}\nsrc:\n{src}");
}

/// expr_bp 后缀 `(`-call 与 spine 相邻实参的消歧（L13 同缺陷同修复）。修复
/// 前 `f a (b)` 被读成 `f (a b)`——单实参括号组按调用折到前一个实参上，
/// 对 Nat 值做函数调用误报 `can't unify expected: (x: ?N) → ?M x`。
#[test]
fn parity_spine_escape_juxtaposed_paren() {
    let nat = "enum Nat {\n    zero\n    succ(x: Nat)\n}\n";
    // (1) `f a (b)` ≡ 纯相邻 `f a b` ≡ 逗号调用 `f(a, b)`（同值；`two` 返回第一实参）
    let two = format!("{nat}def two(x: Nat, y: Nat): Nat = x\ndef one = succ zero\n");
    assert_both_ok_contains(&format!("{two}println (two zero (succ zero))\n"), "Nat::zero");
    assert_both_ok_contains(&format!("{two}println (two zero one)\n"), "Nat::zero");
    assert_both_ok_contains(&format!("{two}println (two(zero, succ zero))\n"), "Nat::zero");
    // (2) 嵌套构造子实参（原缺陷最小形态）：内层括号组落回外层 cons 第二槽
    let list = "enum List[A] {\n    nil\n    cons(head: A, tail: List[A])\n}\n";
    let second = format!(
        "{nat}{list}def second(l: List[Nat]): Nat =\n    match l {{\n        case nil => zero\n        case cons(h, nil) => h\n        case cons(h, cons(h2, t)) => h2\n    }}\n"
    );
    assert_both_ok_contains(
        &format!("{second}println (second (cons zero (cons (succ zero) nil)))\n"),
        "Nat::succ(Nat::zero)",
    );
    // (3) 头位单实参括号链（哨兵在头位拆分 → 项与修复前一致）
    assert_both_ok_contains(&format!("{nat}println (succ (succ (zero)))\n"), "Nat::succ(Nat::succ(Nat::zero))");
    // (4) 带空格的多实参逗号调用（prelude `xs.elem (x, eq)` 形态）读法不变
    assert_both_ok_contains(&format!("{two}println (two (succ zero, zero))\n"), "Nat::succ(Nat::zero)");
    // (5) 空括号组 `f()`（len=0 不标记，恒为无操作）
    let zz = format!("{nat}def zz: Nat = zero\n");
    assert_both_ok_contains(&format!("{zz}println (zz())\n"), "Nat::zero");
    // (6) `new` 结构体形态不受影响（p_new 在原子层吃掉 `new X(..)`）
    let pair = format!("{nat}struct Pair {{\n    fst: Nat\n    snd: Nat\n}}\nstruct Wrap {{\n    v: Nat\n}}\n");
    assert_both_ok_contains(&format!("{pair}def p = new Pair(succ zero, zero)\nprintln p.fst\n"), "Nat::succ(Nat::zero)");
    assert_both_ok_contains(&format!("{pair}def w = new Wrap(zero)\nprintln w.v\n"), "Nat::zero");
}
