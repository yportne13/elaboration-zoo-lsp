//! backport3 回归套件（A.3 扩展）：L09/L10 隐含实参/λ binder 的方括号打印
//! 与回读。
//!
//! 背景：b0694c96 把 L11/L12 的 pretty 隐含位从 {...} 改成 [...]（与
//! L07/L08/L13 一致）。L09/L10 有同款 bug——pretty.rs 的 fn bracket 仍是
//! format!("{{{}}}", s)，而两层 parser 的隐式语法只有 [...]：
//! parser/mod.rs 的 p_arg（f[A] 隐含实参）、p_lam_binder（[x] =>）、
//! p_pi_impl_binder（[x: A] ->），词法里 { } 只用于 match/def 体，没有
//! 表达式分组语义。于是 pretty 的隐含位回读即报错。本套件钉住「隐含用 []、
//! 显式保持裸串/()、花括号只留给优先级分组」以及「输出能被本层 parser 再
//! 解析」。
//!
//! 结构：与 tests/l09_fast_parity.rs / l10_fast_parity.rs 同款，用 #[path]
//! 只编 list/bimap/parser_lib（不含 LSP 与其它层），两层共用同一个 list 根
//! 模块，参考版 run 跑在 256 MiB 大栈线程里。
//!
//! 与 L11/L12 的结构差异（照搬会错，故逐条说明）：
//!
//! 1. **隐含 Π binder 在本层不可达**：L09/L10 的 Pi pretty 用
//!    is_anonymous = name_span == 「_」 || matches!(i, Icit::Impl)，隐含
//!    binder 走匿名臂、打印成 "A → B"（L11/L12 只把「_」当匿名，隐含
//!    binder 打印 "[x: A] → B"）。因此 pretty.rs 里 Pi 的 Icit::Impl =>
//!    bracket(...) 分支是死代码：本轮仍按 L11/L12 改成 [x: A] 并删除
//!    bracket 助手（避免留陷阱），但本套件只能按实际输出断言匿名形态。
//!    改 is_anonymous 会改动既有程序输出（超出本轮修复范围），未做。
//! 2. **优先级分组用 {...}**：本层 App/Lam 的 need_paren 分支输出
//!    "{f u}"（L11/L12 同款；L07/L08 用 "(...)"），按任务要求保持原样。
//!    分组括号不是 parser 的原子语法，故 round-trip 只喂不触发分组的片段。
//! 3. **原子项构造**：L09/L10 的 Ix/MetaVar 字段私有，层外无法构造
//!    Tm::Var/Tm::Meta；本套件用 Tm::Sum 空参数（pretty 直接打印名字，如
//!    f/Nat）做原子项，效果等价于 L11/L12 的 Tm::Decl。
//! 4. 两层的 pretty/parser 在 mod.rs 里原本是私有 mod（L11–L13 是
//!    pub mod）；本轮为让本套件直接调 pretty/parser，把这两个 mod 放宽到
//!    pub(crate)（层模块本身在 lib.rs 里私有，不扩大对外 API）。
//!
//! 已知偏差（既有，非本轮引入）：两层词法里没有 U+2192 的 Π 箭头——pretty
//! 的 Π 箭头输出因此不可回读，L11/L12/L13 亦然。round-trip 断言对 Π 输出把
//! 该箭头归一化成 parser 的 ->（同 tests/backport3_pretty_tests.rs）后再
//! 解析，[...] 部分原样解析。

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

#[path = "../src/L09_mltt/mod.rs"]
mod L09_mltt;

#[path = "../src/L10_typeclass/mod.rs"]
mod L10_typeclass;

/// L09 的 Tm 构造助手（Lam/Pi 体是 std::rc::Rc，App 是 Box）。
mod l09 {
    pub use super::L09_mltt::parser::syntax::Icit;
    pub use super::L09_mltt::pretty::pretty_tm;
    pub use super::L09_mltt::Tm;
    pub use super::list::List;
    pub use super::parser_lib::Span;

    pub fn sp(s: &str) -> Span<String> {
        Span { data: s.to_owned(), start_offset: 0, end_offset: 0, path_id: 0 }
    }
    /// 原子项：Tm::Sum 无参数时 pretty 只打印名字（层外构造不了 Tm::Var）。
    pub fn atom(s: &str) -> Tm {
        Tm::Sum(sp(s), vec![], vec![])
    }
    pub fn u0() -> Tm {
        Tm::U(0)
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

/// L10 的 Tm 构造助手（同 L09，但 App/AppPruning 的子项也是 Rc，Sum 多一个
/// is_trait 字段）。
mod l10 {
    pub use super::L10_typeclass::parser::syntax::Icit;
    pub use super::L10_typeclass::pretty::pretty_tm;
    pub use super::L10_typeclass::Tm;
    pub use super::list::List;
    pub use super::parser_lib::Span;

    pub fn sp(s: &str) -> Span<String> {
        Span { data: s.to_owned(), start_offset: 0, end_offset: 0, path_id: 0 }
    }
    pub fn atom(s: &str) -> Tm {
        Tm::Sum(sp(s), vec![], vec![], false)
    }
    pub fn u0() -> Tm {
        Tm::U(0)
    }
    pub fn app(f: Tm, u: Tm, i: Icit) -> Tm {
        Tm::App(std::rc::Rc::new(f), std::rc::Rc::new(u), i)
    }
    pub fn lam(name: &str, i: Icit, body: Tm) -> Tm {
        Tm::Lam(sp(name), i, std::rc::Rc::new(body))
    }
    pub fn pi(name: &str, i: Icit, a: Tm, b: Tm) -> Tm {
        Tm::Pi(sp(name), i, std::rc::Rc::new(a), std::rc::Rc::new(b))
    }
    pub fn pruning(f: Tm, pr: List<Option<Icit>>) -> Tm {
        Tm::AppPruning(std::rc::Rc::new(f), pr)
    }
    pub fn pretty(tm: &Tm) -> String {
        pretty_tm(0, List::new(), tm)
    }
    pub fn pretty_ns(ns: List<String>, tm: &Tm) -> String {
        pretty_tm(0, ns, tm)
    }
}

/// 在大栈线程里跑 L09 参考版 run（elaboration 对项递归）。
fn run_l09(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L09_mltt::run(&input, 0).map_err(|e| e.0.data.clone()))
        .unwrap()
        .join()
        .unwrap()
}

fn run_l10(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L10_typeclass::run(&input, 0).map_err(|e| e.0.data.clone()))
        .unwrap()
        .join()
        .unwrap()
}

/// parser 的解析错误条数（None 表示连 AST 都没有）。两层 parser 都会在
/// 恢复后返回 Some((decls, errs))，所以「可回读」= Some(0)。
fn l09_parse_errors(src: &str) -> Option<usize> {
    L09_mltt::parser::parser(src, 0).map(|(_, errs)| errs.len())
}

fn l10_parse_errors(src: &str) -> Option<usize> {
    L10_typeclass::parser::parser(src, 0).map(|(_, errs)| errs.len())
}

/// 把一个 pretty 片段当作 def 体喂回 parser，断言零错误。
fn assert_l09_reparses(fragment: &str) {
    let src = format!("def w = {fragment}");
    assert_eq!(l09_parse_errors(&src), Some(0), "L09 pretty 输出不可回读：{src:?}");
}

fn assert_l10_reparses(fragment: &str) {
    let src = format!("def w = {fragment}");
    assert_eq!(l10_parse_errors(&src), Some(0), "L10 pretty 输出不可回读：{src:?}");
}

/// Π 输出回读：箭头归一化成 ->（既有词法偏差），其余原样。
fn assert_l09_type_reparses(pretty_pi: &str) {
    let src = format!("def w : {} = _", pretty_pi.replace(ARROW, "->"));
    assert_eq!(l09_parse_errors(&src), Some(0), "L09 Π 输出不可回读：{src:?}");
}

fn assert_l10_type_reparses(pretty_pi: &str) {
    let src = format!("def w : {} = _", pretty_pi.replace(ARROW, "->"));
    assert_eq!(l10_parse_errors(&src), Some(0), "L10 Π 输出不可回读：{src:?}");
}

// ---------------------------------------------------------------------------
// 1) 直接构造 Tm：隐含用 []、显式保持裸串/()，花括号只用于优先级分组
// ---------------------------------------------------------------------------

#[test]
fn l09_implicit_syntax_uses_square_brackets() {
    use l09::Icit;
    use l09::List;

    // (a) 隐含应用实参 f [Nat]（不是 f {Nat}）；显式实参照旧 f Nat。
    let impl_app = l09::app(l09::atom("f"), l09::atom("Nat"), Icit::Impl);
    assert_eq!(l09::pretty(&impl_app), "f [Nat]");
    assert!(!l09::pretty(&impl_app).contains('{'));
    let expl_app = l09::app(l09::atom("f"), l09::atom("Nat"), Icit::Expl);
    assert_eq!(l09::pretty(&expl_app), "f Nat");

    // (b) 隐含 λ binder：[T] => ...（不是 {T} => ...）。
    let impl_lam = l09::lam("T", Icit::Impl, l09::lam("x", Icit::Expl, l09::atom("y")));
    assert_eq!(l09::pretty(&impl_lam), "[T] => x => y");
    assert!(!l09::pretty(&impl_lam).contains('{'));

    // (c) Π binder：隐含在本层走匿名臂（见文件头第 1 条），显式保持 (x: A)。
    let impl_pi = l09::pi("T", Icit::Impl, l09::u0(), l09::atom("Nat"));
    assert_eq!(l09::pretty(&impl_pi), format!("Type 0 {ARROW} Nat"));
    assert!(!l09::pretty(&impl_pi).contains('{'));
    let expl_pi = l09::pi("T", Icit::Expl, l09::u0(), l09::atom("Nat"));
    assert_eq!(l09::pretty(&expl_pi), format!("(T: Type 0) {ARROW} Nat"));

    // (d) AppPruning 两个槽位（?m 展开的实参显示）：f [y] / f y。
    let pr = List::new().prepend(Some(Icit::Impl));
    let pruning = l09::pruning(l09::atom("f"), pr);
    let ns = List::new().prepend("y".to_owned());
    assert_eq!(l09::pretty_ns(ns, &pruning), "f [y]");
    assert!(!l09::pretty_ns(List::new().prepend("y".to_owned()), &pruning).contains('{'));

    let pr_expl = List::new().prepend(Some(Icit::Expl));
    let pruning_expl = l09::pruning(l09::atom("f"), pr_expl);
    let ns2 = List::new().prepend("y".to_owned());
    assert_eq!(l09::pretty_ns(ns2, &pruning_expl), "f y");

    // 名字表短于掩码的降级臂（占位 @序号）也必须用 []。
    let pr_short = List::new().prepend(Some(Icit::Impl));
    let pruning_short = l09::pruning(l09::atom("f"), pr_short);
    assert_eq!(l09::pretty_ns(List::new(), &pruning_short), "f [@0]");

    // (e) 嵌套：外侧显式应用要把内层隐含应用整体括起来（{...} 仍是优先级
    //     分组，其内部实参必须仍是 [...]）。
    let nested = l09::app(l09::atom("f"), impl_app.clone(), Icit::Expl);
    assert_eq!(l09::pretty(&nested), "f {f [Nat]}");
}

#[test]
fn l10_implicit_syntax_uses_square_brackets() {
    use l10::Icit;
    use l10::List;

    let impl_app = l10::app(l10::atom("f"), l10::atom("Nat"), Icit::Impl);
    assert_eq!(l10::pretty(&impl_app), "f [Nat]");
    assert!(!l10::pretty(&impl_app).contains('{'));
    let expl_app = l10::app(l10::atom("f"), l10::atom("Nat"), Icit::Expl);
    assert_eq!(l10::pretty(&expl_app), "f Nat");

    let impl_lam = l10::lam("T", Icit::Impl, l10::lam("x", Icit::Expl, l10::atom("y")));
    assert_eq!(l10::pretty(&impl_lam), "[T] => x => y");
    assert!(!l10::pretty(&impl_lam).contains('{'));

    let impl_pi = l10::pi("T", Icit::Impl, l10::u0(), l10::atom("Nat"));
    assert_eq!(l10::pretty(&impl_pi), format!("Type 0 {ARROW} Nat"));
    assert!(!l10::pretty(&impl_pi).contains('{'));
    let expl_pi = l10::pi("T", Icit::Expl, l10::u0(), l10::atom("Nat"));
    assert_eq!(l10::pretty(&expl_pi), format!("(T: Type 0) {ARROW} Nat"));

    // AppPruning 两处（L10 本轮之前两处都还是 {...}）。
    let pr = List::new().prepend(Some(Icit::Impl));
    let pruning = l10::pruning(l10::atom("f"), pr);
    let ns = List::new().prepend("y".to_owned());
    assert_eq!(l10::pretty_ns(ns, &pruning), "f [y]");
    assert!(!l10::pretty_ns(List::new().prepend("y".to_owned()), &pruning).contains('{'));

    let pr_expl = List::new().prepend(Some(Icit::Expl));
    let pruning_expl = l10::pruning(l10::atom("f"), pr_expl);
    let ns2 = List::new().prepend("y".to_owned());
    assert_eq!(l10::pretty_ns(ns2, &pruning_expl), "f y");

    let pr_short = List::new().prepend(Some(Icit::Impl));
    let pruning_short = l10::pruning(l10::atom("f"), pr_short);
    assert_eq!(l10::pretty_ns(List::new(), &pruning_short), "f [@0]");

    let nested = l10::app(l10::atom("f"), impl_app.clone(), Icit::Expl);
    assert_eq!(l10::pretty(&nested), "f {f [Nat]}");
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

def use (g: [A: Type 0] -> A -> A): Nat -> Nat =
    y => g[Nat] y

println use
"#;

/// 带隐含类型参数的 def：它的值是一层隐含 λ。
const IMPLICIT_LAM_SRC: &str = r#"
def id[T](x: T): T = x

println id
"#;

/// 多个隐含 binder 连续出现（[A] => [B] => ...）。
const MULTI_IMPLICIT_SRC: &str = r#"
def const[A, B](a: A, b: B): A = a

println const
"#;

const PROGRAMS: [&str; 3] = [IMPLICIT_APP_SRC, IMPLICIT_LAM_SRC, MULTI_IMPLICIT_SRC];

const EXPECTED: [&str; 3] = [
    "g => y => g [Nat] y\n",
    "[T] => x => x\n",
    "[A] => [B] => a => b => a\n",
];

#[test]
fn l09_program_output_uses_square_brackets() {
    for (src, expected) in PROGRAMS.iter().zip(EXPECTED) {
        let out = run_l09(src).expect("L09 程序应通过");
        assert_eq!(out, expected, "L09 输出与预期不符，src:\n{src}");
        assert!(!out.contains('{'), "L09 输出出现花括号隐含语法：{out}");
    }
}

#[test]
fn l10_program_output_uses_square_brackets() {
    for (src, expected) in PROGRAMS.iter().zip(EXPECTED) {
        let out = run_l10(src).expect("L10 程序应通过");
        assert_eq!(out, expected, "L10 输出与预期不符，src:\n{src}");
        assert!(!out.contains('{'), "L10 输出出现花括号隐含语法：{out}");
    }
}

// ---------------------------------------------------------------------------
// 3) Round-trip：pretty 输出能被本层 parser 重新解析
// ---------------------------------------------------------------------------

#[test]
fn implicit_pretty_output_round_trips_through_parsers() {
    use crate::list::List;
    use l09::Icit as I09;
    use l10::Icit as I10;

    // (a) 隐含应用实参串：f [Nat] y
    let s09 = l09::pretty(&l09::app(
        l09::app(l09::atom("f"), l09::atom("Nat"), I09::Impl),
        l09::atom("y"),
        I09::Expl,
    ));
    assert_eq!(s09, "f [Nat] y");
    assert_l09_reparses(&s09);

    let s10 = l10::pretty(&l10::app(
        l10::app(l10::atom("f"), l10::atom("Nat"), I10::Impl),
        l10::atom("y"),
        I10::Expl,
    ));
    assert_eq!(s10, "f [Nat] y");
    assert_l10_reparses(&s10);

    // (b) 隐含 λ binder：[T] => x => x（parser 的 p_lam_binder 接受 [x]）
    let s09 = l09::pretty(&l09::lam("T", I09::Impl, l09::lam("x", I09::Expl, l09::atom("x"))));
    assert_eq!(s09, "[T] => x => x");
    assert_l09_reparses(&s09);

    let s10 = l10::pretty(&l10::lam("T", I10::Impl, l10::lam("x", I10::Expl, l10::atom("x"))));
    assert_eq!(s10, "[T] => x => x");
    assert_l10_reparses(&s10);

    // (c) Π：隐含 binder 走匿名臂（见文件头 1），输出 Type 0 → T；箭头不在
    //     本层词法里（既有偏差），归一化成 -> 后断言可回读。
    let s09 = l09::pretty(&l09::pi("T", I09::Impl, l09::u0(), l09::atom("T")));
    assert_eq!(s09, format!("Type 0 {ARROW} T"));
    assert_l09_type_reparses(&s09);

    let s10 = l10::pretty(&l10::pi("T", I10::Impl, l10::u0(), l10::atom("T")));
    assert_eq!(s10, format!("Type 0 {ARROW} T"));
    assert_l10_type_reparses(&s10);

    // (d) AppPruning 隐含位：f [y]
    let pr09 = List::new().prepend(Some(I09::Impl));
    let pruning09 = l09::pruning(l09::atom("f"), pr09);
    let ns09 = List::new().prepend("y".to_owned());
    let s09 = l09::pretty_ns(ns09, &pruning09);
    assert_eq!(s09, "f [y]");
    assert_l09_reparses(&s09);

    let pr10 = List::new().prepend(Some(I10::Impl));
    let pruning10 = l10::pruning(l10::atom("f"), pr10);
    let ns10 = List::new().prepend("y".to_owned());
    let s10 = l10::pretty_ns(ns10, &pruning10);
    assert_eq!(s10, "f [y]");
    assert_l10_reparses(&s10);

    // (e) 程序级输出同样可回读（每行包成 def 体）。
    for out in EXPECTED {
        let fragment = out.trim_end_matches('\n');
        assert_l09_reparses(fragment);
        assert_l10_reparses(fragment);
    }
}
