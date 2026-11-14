//! backport3 回归套件：L11/L12 隐含实参/Π binder 的方括号打印 + L12 迭代
//! pretty_nat。
//!
//! 背景（旧分支 task/l13-backport3 的 5a5f31dd / e636e5a2，按当前 master 重做）：
//!
//! * L11/L12 的 pretty 曾把隐含实参打成 {...}（应用实参、λ binder、Π binder、
//!   AppPruning 的隐含位），而这两层的 parser 只有 [...] 的隐式语法、没有
//!   可用于该位置的 { 表达式语法，于是这些 pretty 结果回读即报错。本套件钉
//!   住「隐含用 []、显式用 ()/裸串」以及「输出能被本层 parser 再解析」。
//! * L12 的 pretty_nat 原为递归：大 Nat 字面量是百万层 succ 链，每层吃一个
//!   原生栈帧。改为迭代后本套件用 10 万层 succ 链 + 256 KiB 小栈钉住 O(1) 栈。
//!
//! 结构说明：与 tests/l11_fast_parity.rs / l12_fast_parity.rs 同款，用 #[path]
//! 只编 list/bimap/parser_lib（不含 LSP 与其它层）。两层共用同一个 list 根模块。
//!
//! 已知偏差（既有，非本轮引入）：两层的词法里没有 U+2192 的 Π 箭头——pretty 的
//! Π 箭头输出因此不可回读，L13 亦然。round-trip 断言对 Π 输出把该箭头归一化成
//! parser 的 ->（写入方式见下方 const ARROW）后再解析，[...] 部分原样解析。

#![allow(non_snake_case)]
#![allow(dead_code)]

/// pretty 输出的 Π 箭头（U+2192）；本层 parser 的词法只认 ASCII 的 ->。
const ARROW: char = '\u{2192}';

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

#[path = "../src/L12_canonical/mod.rs"]
mod L12_canonical;

use std::sync::Arc;

/// L11 的 Tm 构造助手（Rc 在层内是 Arc 别名；Ty 是 Tm 别名）。
mod l11 {
    pub use super::L11_macro::parser::syntax::Icit;
    pub use super::L11_macro::pretty::pretty_tm;
    pub use super::L11_macro::Tm;
    pub use super::list::List;
    pub use super::parser_lib::Span;
    pub use std::sync::Arc;

    pub fn sp(s: &str) -> Span<String> {
        Span { data: s.to_owned(), start_offset: 0, end_offset: 0, path_id: 0 }
    }
    pub fn decl(s: &str) -> Arc<Tm> {
        Arc::new(Tm::Decl(sp(s)))
    }
    pub fn app(f: Arc<Tm>, u: Arc<Tm>, i: Icit) -> Arc<Tm> {
        Arc::new(Tm::App(f, u, i))
    }
    pub fn lam(name: &str, i: Icit, body: Arc<Tm>) -> Arc<Tm> {
        Arc::new(Tm::Lam(sp(name), i, body))
    }
    pub fn pi(name: &str, i: Icit, a: Arc<Tm>, b: Arc<Tm>) -> Arc<Tm> {
        Arc::new(Tm::Pi(sp(name), i, a, b))
    }
    pub fn pretty(tm: &Tm) -> String {
        pretty_tm(0, List::new(), tm)
    }
    pub fn pretty_ns(ns: List<String>, tm: &Tm) -> String {
        pretty_tm(0, ns, tm)
    }
}

/// L12 的 Tm 构造助手（同 L11，但名字/构造子名是 SmolStr）。
mod l12 {
    pub use super::L12_canonical::parser::syntax::Icit;
    pub use super::L12_canonical::pretty::pretty_tm;
    pub use super::L12_canonical::Tm;
    pub use super::list::List;
    pub use super::parser_lib::Span;
    pub use smol_str::SmolStr;
    pub use std::sync::Arc;

    pub fn sp(s: &str) -> Span<SmolStr> {
        Span { data: SmolStr::new(s), start_offset: 0, end_offset: 0, path_id: 0 }
    }
    pub fn decl(s: &str) -> Arc<Tm> {
        Arc::new(Tm::Decl(sp(s)))
    }
    pub fn app(f: Arc<Tm>, u: Arc<Tm>, i: Icit) -> Arc<Tm> {
        Arc::new(Tm::App(f, u, i))
    }
    pub fn lam(name: &str, i: Icit, body: Arc<Tm>) -> Arc<Tm> {
        Arc::new(Tm::Lam(sp(name), i, body))
    }
    pub fn pi(name: &str, i: Icit, a: Arc<Tm>, b: Arc<Tm>) -> Arc<Tm> {
        Arc::new(Tm::Pi(sp(name), i, a, b))
    }
    pub fn pretty(tm: &Tm) -> String {
        pretty_tm(0, List::new(), tm)
    }
}

/// 在大栈线程里跑 L11 参考版 run（elaboration 对项递归）。
fn run_l11(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L11_macro::run(&input, 0).map_err(|e| e.0.data.clone()))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑 L12 参考版 run（Error 携带非 Send 的重试闭包，只在
/// 子线程内取文案）。
fn run_l12(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L12_canonical::run(&input, 0).map_err(|e| e.0.data.clone()))
        .unwrap()
        .join()
        .unwrap()
}

/// parser 的解析错误条数（None 表示连 AST 都没有）。两层 parser 都会在
/// 恢复后返回 Some((decls, errs))，所以「可回读」= Some(0)。
fn l11_parse_errors(src: &str) -> Option<usize> {
    L11_macro::parser::parser(src, 0).map(|(_, errs)| errs.len())
}

fn l12_parse_errors(src: &str) -> Option<usize> {
    L12_canonical::parser::parser(src, 0).map(|(_, errs)| errs.len())
}

// ---------------------------------------------------------------------------
// 1) 直接构造 Tm：隐含用 []、显式保持裸串/()，花括号只用于优先级分组
// ---------------------------------------------------------------------------

#[test]
fn l11_implicit_syntax_uses_square_brackets() {
    use l11::Icit;

    // 隐含应用实参 f [Nat]（花括号留给 APPP 优先级分组）。
    let impl_app = l11::app(l11::decl("f"), l11::decl("Nat"), Icit::Impl);
    assert_eq!(l11::pretty(&impl_app), "f [Nat]");
    // 显式实参照旧：f Nat。
    let expl_app = l11::app(l11::decl("f"), l11::decl("Nat"), Icit::Expl);
    assert_eq!(l11::pretty(&expl_app), "f Nat");

    // 隐含 λ binder：[T] => ...（不是 {T} => ...）。
    let impl_lam = l11::lam("T", Icit::Impl, l11::lam("x", Icit::Expl, l11::decl("y")));
    assert_eq!(l11::pretty(&impl_lam), "[T] => x => y");
    assert!(!l11::pretty(&impl_lam).contains('{'));

    // 隐含 Π binder：[T: Type 0] → ...。
    let u0 = Arc::new(l11::Tm::U(0));
    let impl_pi = l11::pi("T", Icit::Impl, u0, l11::decl("Nat"));
    let pi_out = l11::pretty(&impl_pi);
    assert_eq!(pi_out, format!("[T: Type 0] {ARROW} Nat"));
    assert!(!pi_out.contains('{'));

    // AppPruning 的隐含位（?m 展开的实参显示）：f [y]。
    let pr = l11::List::new().prepend(Some(Icit::Impl));
    let pruning = Arc::new(l11::Tm::AppPruning(l11::decl("f"), pr));
    let ns = l11::List::new().prepend("y".to_owned());
    assert_eq!(l11::pretty_ns(ns, &pruning), "f [y]");
    // 显式位不受影响。
    let pr_expl = l11::List::new().prepend(Some(Icit::Expl));
    let pruning_expl = Arc::new(l11::Tm::AppPruning(l11::decl("f"), pr_expl));
    let ns2 = l11::List::new().prepend("y".to_owned());
    assert_eq!(l11::pretty_ns(ns2, &pruning_expl), "f y");

    // 嵌套：外侧显式应用要把内层隐含应用整体括起来（{...} 仍是优先级分组，
    // 其内部实参必须仍是 [...]）。
    let nested = l11::app(l11::decl("f"), impl_app.clone(), Icit::Expl);
    assert_eq!(l11::pretty(&nested), "f {f [Nat]}");
}

#[test]
fn l12_implicit_syntax_uses_square_brackets() {
    use l12::Icit;

    let impl_app = l12::app(l12::decl("f"), l12::decl("Nat"), Icit::Impl);
    assert_eq!(l12::pretty(&impl_app), "f [Nat]");
    let expl_app = l12::app(l12::decl("f"), l12::decl("Nat"), Icit::Expl);
    assert_eq!(l12::pretty(&expl_app), "f Nat");

    let impl_lam = l12::lam("T", Icit::Impl, l12::lam("x", Icit::Expl, l12::decl("y")));
    assert_eq!(l12::pretty(&impl_lam), "[T] => x => y");
    assert!(!l12::pretty(&impl_lam).contains('{'));

    let u0 = Arc::new(l12::Tm::U(0));
    let impl_pi = l12::pi("T", Icit::Impl, u0, l12::decl("Nat"));
    let pi_out = l12::pretty(&impl_pi);
    assert_eq!(pi_out, format!("[T: Type 0] {ARROW} Nat"));
    assert!(!pi_out.contains('{'));

    let pr = l12::List::new().prepend(Some(Icit::Impl));
    let pruning = Arc::new(l12::Tm::AppPruning(l12::decl("f"), pr));
    let ns = l12::List::new().prepend(l12::SmolStr::new("y"));
    assert_eq!(l12::pretty_tm(0, ns, &pruning), "f [y]");
    let pr_expl = l12::List::new().prepend(Some(Icit::Expl));
    let pruning_expl = Arc::new(l12::Tm::AppPruning(l12::decl("f"), pr_expl));
    let ns2 = l12::List::new().prepend(l12::SmolStr::new("y"));
    assert_eq!(l12::pretty_tm(0, ns2, &pruning_expl), "f y");

    let nested = l12::app(l12::decl("f"), impl_app.clone(), Icit::Expl);
    assert_eq!(l12::pretty(&nested), "f {f [Nat]}");
}

// ---------------------------------------------------------------------------
// 2) 程序级：println 的 nf pretty（run 输出的正是 pretty_tm）不得出现
//    {...} 形式的隐含语法
// ---------------------------------------------------------------------------

/// 隐含应用实参在 stuck 位置（g 是变量，g[Nat] 不归约）。
const IMPLICIT_APP_SRC: &str = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def k (g: [A: Type 0] -> A -> A): Nat -> Nat =
    y => g[Nat] y

println k
"#;

/// 带隐含类型参数的 def：它的值是一层隐含 λ。
const IMPLICIT_LAM_SRC: &str = r#"
def id[T](x: T): T = x

println id
"#;

/// Π 类型的隐含 binder（类型级输出）。
const IMPLICIT_PI_SRC: &str = r#"
println ([A: Type 0] -> A -> A)
"#;

fn expected_pi_output() -> String {
    format!("[A: Type 0] {ARROW} A {ARROW} A\n")
}

#[test]
fn l11_program_output_uses_square_brackets() {
    assert_eq!(
        run_l11(IMPLICIT_APP_SRC).expect("L11 隐含应用程序应通过"),
        "g => y => g [Nat] y\n",
    );
    assert_eq!(
        run_l11(IMPLICIT_LAM_SRC).expect("L11 隐含 λ 程序应通过"),
        "[T] => x => x\n",
    );
    assert_eq!(
        run_l11(IMPLICIT_PI_SRC).expect("L11 隐含 Π 程序应通过"),
        expected_pi_output(),
    );
    for src in [IMPLICIT_APP_SRC, IMPLICIT_LAM_SRC, IMPLICIT_PI_SRC] {
        let out = run_l11(src).unwrap();
        assert!(!out.contains('{'), "L11 输出出现花括号隐含语法：{out}");
    }
}

#[test]
fn l12_program_output_uses_square_brackets() {
    assert_eq!(
        run_l12(IMPLICIT_APP_SRC).expect("L12 隐含应用程序应通过"),
        "g => y => g [Nat] y\n",
    );
    assert_eq!(
        run_l12(IMPLICIT_LAM_SRC).expect("L12 隐含 λ 程序应通过"),
        "[T] => x => x\n",
    );
    assert_eq!(
        run_l12(IMPLICIT_PI_SRC).expect("L12 隐含 Π 程序应通过"),
        expected_pi_output(),
    );
    for src in [IMPLICIT_APP_SRC, IMPLICIT_LAM_SRC, IMPLICIT_PI_SRC] {
        let out = run_l12(src).unwrap();
        assert!(!out.contains('{'), "L12 输出出现花括号隐含语法：{out}");
    }
}

// ---------------------------------------------------------------------------
// 3) Round-trip：pretty 输出能被本层 parser 重新解析
// ---------------------------------------------------------------------------

/// 把一个 pretty 片段当作 def 体喂回 parser，断言零错误。
fn assert_l11_reparses(fragment: &str, wrap: &str) {
    let src = format!("{wrap}{fragment}");
    assert_eq!(l11_parse_errors(&src), Some(0), "L11 pretty 输出不可回读：{src:?}");
}

fn assert_l12_reparses(fragment: &str, wrap: &str) {
    let src = format!("{wrap}{fragment}");
    assert_eq!(l12_parse_errors(&src), Some(0), "L12 pretty 输出不可回读：{src:?}");
}

#[test]
fn implicit_pretty_output_round_trips_through_parsers() {
    use l11::Icit as I11;
    use l12::Icit as I12;

    // (a) 隐含应用实参串：f [Nat] y
    let l11_app = l11::app(
        l11::app(l11::decl("f"), l11::decl("Nat"), I11::Impl),
        l11::decl("y"),
        I11::Expl,
    );
    let s = l11::pretty(&l11_app);
    assert_eq!(s, "f [Nat] y");
    assert_l11_reparses(&s, "def w = ");

    let l12_app = l12::app(
        l12::app(l12::decl("f"), l12::decl("Nat"), I12::Impl),
        l12::decl("y"),
        I12::Expl,
    );
    let s = l12::pretty(&l12_app);
    assert_eq!(s, "f [Nat] y");
    assert_l12_reparses(&s, "def w = ");

    // (b) 隐含 λ binder：[T] => x => x（parser 的 p_lam_binder 接受 [x]）
    let l11_lam = l11::lam("T", I11::Impl, l11::lam("x", I11::Expl, l11::decl("x")));
    let s = l11::pretty(&l11_lam);
    assert_eq!(s, "[T] => x => x");
    assert_l11_reparses(&s, "def w = ");

    let l12_lam = l12::lam("T", I12::Impl, l12::lam("x", I12::Expl, l12::decl("x")));
    let s = l12::pretty(&l12_lam);
    assert_eq!(s, "[T] => x => x");
    assert_l12_reparses(&s, "def w = ");

    // (c) 隐含 Π binder：[T: Type 0] → T。箭头不在本层词法里（既有偏差，
    //     L13 同款），归一化成 -> 后断言 [...] binder 可回读。
    let u0_11 = Arc::new(l11::Tm::U(0));
    let l11_pi = l11::pi("T", I11::Impl, u0_11, l11::decl("T"));
    let s = l11::pretty(&l11_pi);
    assert_eq!(s, format!("[T: Type 0] {ARROW} T"));
    let src = format!("def w : {} = _", s.replace(ARROW, "->"));
    assert_eq!(l11_parse_errors(&src), Some(0), "L11 Π 输出不可回读：{src:?}");

    let u0_12 = Arc::new(l12::Tm::U(0));
    let l12_pi = l12::pi("T", I12::Impl, u0_12, l12::decl("T"));
    let s = l12::pretty(&l12_pi);
    assert_eq!(s, format!("[T: Type 0] {ARROW} T"));
    let src = format!("def w : {} = _", s.replace(ARROW, "->"));
    assert_eq!(l12_parse_errors(&src), Some(0), "L12 Π 输出不可回读：{src:?}");

    // (d) AppPruning 隐含位：f [y]
    let pr = l11::List::new().prepend(Some(I11::Impl));
    let pruning = Arc::new(l11::Tm::AppPruning(l11::decl("f"), pr));
    let ns = l11::List::new().prepend("y".to_owned());
    let s = l11::pretty_ns(ns, &pruning);
    assert_eq!(s, "f [y]");
    assert_l11_reparses(&s, "def w = ");

    let pr = l12::List::new().prepend(Some(I12::Impl));
    let pruning = Arc::new(l12::Tm::AppPruning(l12::decl("f"), pr));
    let ns = l12::List::new().prepend(l12::SmolStr::new("y"));
    let s = l12::pretty_tm(0, ns, &pruning);
    assert_eq!(s, "f [y]");
    assert_l12_reparses(&s, "def w = ");
}

// ---------------------------------------------------------------------------
// 4) L12 pretty_nat：三个分支的格式与迭代语义
// ---------------------------------------------------------------------------

fn l12_nat_typ() -> Arc<l12::Tm> {
    Arc::new(l12::Tm::Sum(l12::sp("Nat"), vec![], vec![], false))
}

fn l12_nat_zero() -> Arc<l12::Tm> {
    Arc::new(l12::Tm::SumCase {
        typ: l12_nat_typ(),
        case_name: l12::sp("zero"),
        datas: vec![],
        is_trait: false,
    })
}

fn l12_nat_succ(inner: Option<Arc<l12::Tm>>) -> Arc<l12::Tm> {
    Arc::new(l12::Tm::SumCase {
        typ: l12_nat_typ(),
        case_name: l12::sp("succ"),
        datas: inner
            .map(|t| vec![(l12::sp("n"), t, l12::Icit::Expl)])
            .unwrap_or_default(),
        is_trait: false,
    })
}

/// zero → 0；succ^k zero → 十进制 k（两个分支与递归版逐字节一致）。
#[test]
fn l12_nat_literals_print_decimal() {
    assert_eq!(l12::pretty(&l12_nat_zero()), "0");
    let mut n = l12_nat_zero();
    for expected in 1..=5 {
        n = l12_nat_succ(Some(n));
        assert_eq!(l12::pretty(&n), expected.to_string());
    }
}

/// 卡住的参数打印 tm + n，缺参数打印 unknown + n（递归版同款文案）。
#[test]
fn l12_nat_stuck_and_unknown_branches() {
    // succ(x)，x 不是 Nat 字面量链：x + 1
    let stuck = l12_nat_succ(Some(l12::decl("x")));
    assert_eq!(l12::pretty(&stuck), "x + 1");
    // 参数不是 SumCase：Type 0 + 1
    let non_nat = l12_nat_succ(Some(Arc::new(l12::Tm::U(0))));
    assert_eq!(l12::pretty(&non_nat), "Type 0 + 1");
    // 无参数的 succ：unknown + 1
    let unknown = l12_nat_succ(None);
    assert_eq!(l12::pretty(&unknown), "unknown + 1");
}

/// 10 万层 succ 链在 256 KiB 小栈上打印：递归版每层一帧必溢出，迭代版
/// O(1) 栈。链的 Rc Drop 同样是递归的，故构造/打印后 mem::forget 泄漏
/// （测试进程一次性开销，换取「测的正是 pretty 而非 Drop」）。
#[test]
fn l12_deep_succ_chain_prints_iteratively() {
    const DEPTH: usize = 100_000;
    let out = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            use l12::Icit;
            let nat = l12_nat_typ();
            let mut n = l12_nat_zero();
            for _ in 0..DEPTH {
                n = Arc::new(l12::Tm::SumCase {
                    typ: nat.clone(),
                    case_name: l12::sp("succ"),
                    datas: vec![(l12::sp("n"), n, Icit::Expl)],
                    is_trait: false,
                });
            }
            let printed = l12::pretty(&n);
            std::mem::forget(n);
            printed
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(out, DEPTH.to_string());
}
