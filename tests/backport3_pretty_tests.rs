//! backport3 回归套件：L11/L12 隐含实参/Π binder 的方括号打印 + L12
//! 构造子 pretty 的深链定深行为。
//!
//! 2026-11-18 迁移：L11/L12 链重建（13c4e56f / 73d68cf2）后按新 API 重写构造助手：
//! App/AppPruning 用 Box、Lam/Pi 用 Rc、Decl 用 SmolStr、parser 严格返回
//! Result、Error.0 直接是 String；测试意图（隐含实参/绑定子用 []、可回读）不变。
//!
//! 背景（旧分支 task/l13-backport3 的 5a5f31dd / e636e5a2）：
//!
//! * L11/L12 的 pretty 曾把隐含实参打成 {...}（应用实参、λ binder、Π binder、
//!   AppPruning 的隐含位），而这两层的 parser 只有 [...] 的隐式语法、没有
//!   可用于该位置的 { 表达式语法，于是这些 pretty 结果回读即报错。本套件钉
//!   住「隐含用 []、显式用 ()/裸串」以及「输出能被本层 parser 再解析」。
//! * L12 重建后构造子按 Enum::case(...) 结构打印，pretty 用 MAX_DEPTH=1024
//!   定深截断；10 万层 succ 链钉住「不爆栈且输出被截断」。
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

/// L11 的 Tm 构造助手（重建后：App/AppPruning 用 Box、Lam/Pi 用 Rc、
/// Decl 用 SmolStr）。
mod l11 {
    pub use super::L11_macro::parser::syntax::Icit;
    pub use super::L11_macro::pretty::pretty_tm;
    pub use super::L11_macro::Tm;
    pub use super::list::List;
    pub use super::parser_lib::Span;
    use smol_str::SmolStr;

    pub fn sp(s: &str) -> Span<String> {
        Span { data: s.to_owned(), start_offset: 0, end_offset: 0, path_id: 0 }
    }
    pub fn decl(s: &str) -> Tm {
        Tm::Decl(SmolStr::new(s))
    }
    pub fn app(f: Tm, u: Tm, i: Icit) -> Tm {
        Tm::App(Box::new(f), Box::new(u), i)
    }
    pub fn lam(name: &str, i: Icit, body: Tm) -> Tm {
        Tm::Lam(sp(name), i, std::rc::Rc::new(body))
    }
    pub fn pi(name: &str, i: Icit, a: Tm, b: Tm) -> Tm {
        Tm::Pi(sp(name), i, std::rc::Rc::new(a), std::rc::Rc::new(b))
    }
    pub fn pruning(f: Tm, pr: List<Option<Icit>>) -> Tm {
        Tm::AppPruning(Box::new(f), pr)
    }
    pub fn pretty(tm: &Tm) -> String {
        pretty_tm(0, List::new(), tm)
    }
    pub fn pretty_ns(ns: List<String>, tm: &Tm) -> String {
        pretty_tm(0, ns, tm)
    }
}

/// L12 的 Tm 构造助手（与 L11 同构）。
mod l12 {
    pub use super::L12_canonical::parser::syntax::Icit;
    pub use super::L12_canonical::pretty::pretty_tm;
    pub use super::L12_canonical::Tm;
    pub use super::list::List;
    pub use super::parser_lib::Span;
    use smol_str::SmolStr;

    pub fn sp(s: &str) -> Span<String> {
        Span { data: s.to_owned(), start_offset: 0, end_offset: 0, path_id: 0 }
    }
    pub fn decl(s: &str) -> Tm {
        Tm::Decl(SmolStr::new(s))
    }
    pub fn app(f: Tm, u: Tm, i: Icit) -> Tm {
        Tm::App(Box::new(f), Box::new(u), i)
    }
    pub fn lam(name: &str, i: Icit, body: Tm) -> Tm {
        Tm::Lam(sp(name), i, std::rc::Rc::new(body))
    }
    pub fn pi(name: &str, i: Icit, a: Tm, b: Tm) -> Tm {
        Tm::Pi(sp(name), i, std::rc::Rc::new(a), std::rc::Rc::new(b))
    }
    pub fn pruning(f: Tm, pr: List<Option<Icit>>) -> Tm {
        Tm::AppPruning(Box::new(f), pr)
    }
    pub fn pretty(tm: &Tm) -> String {
        pretty_tm(0, List::new(), tm)
    }
    pub fn pretty_ns(ns: List<String>, tm: &Tm) -> String {
        pretty_tm(0, ns, tm)
    }
}

/// 在大栈线程里跑 L11 参考版 run（elaboration 对项递归）。
fn run_l11(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L11_macro::run(&input, 0).map_err(|e| e.0.clone()))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑 L12 参考版 run。
fn run_l12(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L12_canonical::run(&input, 0).map_err(|e| e.0.clone()))
        .unwrap()
        .join()
        .unwrap()
}

/// 重建后的 parser 严格返回 Result：Ok = 可回读，Err = 不可回读。
fn l11_parse_errors(src: &str) -> Option<usize> {
    L11_macro::parser::parser(src, 0).ok().map(|_| 0)
}

fn l12_parse_errors(src: &str) -> Option<usize> {
    L12_canonical::parser::parser(src, 0).ok().map(|_| 0)
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
    let impl_pi = l11::pi("T", Icit::Impl, l11::Tm::U(0), l11::decl("Nat"));
    let pi_out = l11::pretty(&impl_pi);
    assert_eq!(pi_out, format!("[T: Type 0] {ARROW} Nat"));
    assert!(!pi_out.contains('{'));

    // AppPruning：重建后的 pretty 只显示内核（丢弃 pruning），仍是 f。
    let pr = l11::List::new().prepend(Some(Icit::Impl));
    let pruning = l11::pruning(l11::decl("f"), pr);
    assert_eq!(l11::pretty(&pruning), "f");
    // 显式位不受影响。
    let pr_expl = l11::List::new().prepend(Some(Icit::Expl));
    let pruning_expl = l11::pruning(l11::decl("f"), pr_expl);
    assert_eq!(l11::pretty(&pruning_expl), "f");

    // 嵌套：外侧显式应用要把内层隐含应用整体括起来（重建后分组用 ()，
    // 其内部实参必须仍是 [...]）。
    let nested = l11::app(l11::decl("f"), impl_app.clone(), Icit::Expl);
    assert_eq!(l11::pretty(&nested), "f (f [Nat])");
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

    let impl_pi = l12::pi("T", Icit::Impl, l12::Tm::U(0), l12::decl("Nat"));
    let pi_out = l12::pretty(&impl_pi);
    assert_eq!(pi_out, format!("[T: Type 0] {ARROW} Nat"));
    assert!(!pi_out.contains('{'));

    // AppPruning：重建后的 pretty 只显示内核（丢弃 pruning）。
    let pr = l12::List::new().prepend(Some(Icit::Impl));
    let pruning = l12::pruning(l12::decl("f"), pr);
    assert_eq!(l12::pretty(&pruning), "f");
    let pr_expl = l12::List::new().prepend(Some(Icit::Expl));
    let pruning_expl = l12::pruning(l12::decl("f"), pr_expl);
    assert_eq!(l12::pretty(&pruning_expl), "f");

    let nested = l12::app(l12::decl("f"), impl_app.clone(), Icit::Expl);
    assert_eq!(l12::pretty(&nested), "f (f [Nat])");
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
    let l11_pi = l11::pi("T", I11::Impl, l11::Tm::U(0), l11::decl("T"));
    let s = l11::pretty(&l11_pi);
    assert_eq!(s, format!("[T: Type 0] {ARROW} T"));
    let src = format!("def w : {} = _", s.replace(ARROW, "->"));
    assert_eq!(l11_parse_errors(&src), Some(0), "L11 Π 输出不可回读：{src:?}");

    let l12_pi = l12::pi("T", I12::Impl, l12::Tm::U(0), l12::decl("T"));
    let s = l12::pretty(&l12_pi);
    assert_eq!(s, format!("[T: Type 0] {ARROW} T"));
    let src = format!("def w : {} = _", s.replace(ARROW, "->"));
    assert_eq!(l12_parse_errors(&src), Some(0), "L12 Π 输出不可回读：{src:?}");

    // (d) AppPruning：重建后 pretty 只显示内核 f（pruning 位不再打印）。
    let pr = l11::List::new().prepend(Some(I11::Impl));
    let pruning = l11::pruning(l11::decl("f"), pr);
    let s = l11::pretty(&pruning);
    assert_eq!(s, "f");
    assert_l11_reparses(&s, "def w = ");

    let pr = l12::List::new().prepend(Some(I12::Impl));
    let pruning = l12::pruning(l12::decl("f"), pr);
    let s = l12::pretty(&pruning);
    assert_eq!(s, "f");
    assert_l12_reparses(&s, "def w = ");
}

// ---------------------------------------------------------------------------
// 4) L12 构造子输出：重建后 pretty 打印 Enum::case(...) 而非 Nat 十进制字面量
// ---------------------------------------------------------------------------

fn l12_nat_typ() -> l12::Tm {
    l12::Tm::Sum(l12::sp("Nat"), vec![], vec![])
}

fn l12_nat_zero() -> l12::Tm {
    l12::Tm::SumCase {
        typ: Box::new(l12_nat_typ()),
        case_name: l12::sp("zero"),
        datas: vec![],
    }
}

fn l12_nat_succ(inner: Option<l12::Tm>) -> l12::Tm {
    l12::Tm::SumCase {
        typ: Box::new(l12_nat_typ()),
        case_name: l12::sp("succ"),
        datas: inner
            .map(|t| vec![(l12::sp("n"), t, l12::Icit::Expl)])
            .unwrap_or_default(),
    }
}

/// zero/succ 逐层展开成 Nat::zero / Nat::succ(...)。
#[test]
fn l12_nat_constructors_print_structurally() {
    assert_eq!(l12::pretty(&l12_nat_zero()), "Nat::zero");
    let mut n = l12_nat_zero();
    for _ in 1..=5 {
        n = l12_nat_succ(Some(n));
    }
    let out = l12::pretty(&n);
    assert!(out.starts_with("Nat::succ("), "{out}");
    assert!(out.contains("Nat::zero"), "{out}");
}

/// 卡住/缺参数的 succ：新 pretty 只按结构打印，不再有 + 1 / unknown 文案。
#[test]
fn l12_nat_stuck_and_unknown_branches() {
    let stuck = l12_nat_succ(Some(l12::decl("x")));
    assert_eq!(l12::pretty(&stuck), "Nat::succ(x)");
    let non_nat = l12_nat_succ(Some(l12::Tm::U(0)));
    assert_eq!(l12::pretty(&non_nat), "Nat::succ(Type 0)");
    let unknown = l12_nat_succ(None);
    assert_eq!(l12::pretty(&unknown), "Nat::succ");
}

/// 10 万层 succ 链不得爆栈：新 pretty 用 MAX_DEPTH=1024 定深截断（输出省略号），
/// 1024 帧需要数 MiB 栈（256 KiB 不够），但仍远小于 10 万层展开所需栈；
/// Drop 仍递归，构造后 mem::forget 泄漏。
#[test]
fn l12_deep_succ_chain_does_not_overflow() {
    const DEPTH: usize = 100_000;
    let out = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            use l12::Icit;
            let nat = l12_nat_typ();
            let mut n = l12_nat_zero();
            for _ in 0..DEPTH {
                n = l12::Tm::SumCase {
                    typ: Box::new(nat.clone()),
                    case_name: l12::sp("succ"),
                    datas: vec![(l12::sp("n"), n, Icit::Expl)],
                };
            }
            let printed = l12::pretty(&n);
            std::mem::forget(n);
            printed
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(out.contains('…'), "深链应被定深截断，实际输出长度 {}", out.len());
    assert!(out.len() < 20_000, "深链输出不应展开整条链：{}", out.len());
}

