//! 方案 4：**源码注解渲染** —— 有显式类型注解的 def，hover 直接显示源码文本。
//!
//! 背景：`eval(Tm::Decl)` 返回已求值 WHNF，所以类型里的 `T n` 会变成展开的
//! `match n { … }`（65–264 字符）。对**有注解**的 def，我们不需要值——源码里就写着
//! 类型，直接打印即可：零性能代价、零表示层风险。
//!
//! 无注解（`def h(n : Nat) = g n`）仍走值渲染（那里没有源码可打）。

#[path = "../src/list.rs"]
mod list;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L07_sum_type/mod.rs"]
mod L07_sum_type;

fn hover_text(src: &str, needle: &str, nth: usize) -> Option<String> {
    let (_, s) = L07_sum_type::run_with_surface(src, 0).expect("surface");
    let off = src.match_indices(needle).nth(nth).map(|(i, _)| i)?;
    s.hover_text_at(0, off).map(|t| t.to_owned())
}

fn with_stack<T: Send + 'static>(f: fn() -> T) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .expect("thread")
        .join()
        .expect("no panic")
}

const TY_FAMILY: &str = concat!(
    "enum Nat {\n    zero\n    succ(x: Nat)\n}\n",
    "enum Bool {\n    true\n    false\n}\n",
    "def T(n: Nat): U =\n    match n {\n        case zero => Bool\n        case succ(m) => Nat\n    }\n",
    "def g(n: Nat): T n =\n    match n {\n        case zero => true\n        case succ(m) => zero\n    }\n",
);

/// 类型级 match 卡在 rigid 上：值渲染会展开成 `match n { … }`，源码渲染保住 `T n`。
#[test]
fn annotated_def_hover_shows_source_form() {
    with_stack(|| {
        // "g" 在源码里只出现一次（`def g(...)`），取第 0 个（定义处的条目）
        let t = hover_text(TY_FAMILY, "g", 0).expect("g 的悬停条目");
        assert_eq!(t, "(n : Nat) → T n", "应显示源码形态");
        assert!(!t.contains("match"), "不得展开成 match: {t}");
    });
}

/// 嵌套索引：源码里的 `add (add n zero) zero` 原样出现，长度线性。
#[test]
fn annotated_def_hover_keeps_nested_index() {
    with_stack(|| {
        let head = concat!(
            "enum Nat {\n    zero\n    succ(x: Nat)\n}\n",
            "def add(x: Nat, y: Nat): Nat =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\n",
            "enum Box[A](n: Nat) {\n    mk[l: Nat](x: A) -> Box[A] l\n}\n",
        );
        let src = format!(
            "{head}def mkx (n : Nat) (a : Nat) : Box[Nat](add (add n zero) zero) = Box.mk a\ndef use = mkx\n"
        );
        let t = hover_text(&src, "mkx", 1).expect("mkx 的悬停条目");
        assert!(
            t.contains("add (add n zero) zero"),
            "嵌套索引应保源码形态: {t}"
        );
        assert!(!t.contains("match"), "不得展开: {t}");
        assert!(t.len() < 90, "长度应线性: len={} {t}", t.len());
    });
}

/// 无注解的 def 仍走值渲染（源码里没有类型可打）——不应崩、应给出某个类型。
#[test]
fn unannotated_def_still_renders_from_value() {
    with_stack(|| {
        let src = format!("{TY_FAMILY}def h(n : Nat) = g n\n");
        // 取 `def h` 里的 h（TY_FAMILY 里 "h" 不出现在别处，但用 nth=0 会撞 `Nat` 的 …
        // 这里直接用名字定位：`def h(` 的偏移 + 4
        let off = src.find("def h(").expect("def h") + 4;
        let (_, s) = L07_sum_type::run_with_surface(&src, 0).expect("surface");
        let t = s.hover_text_at(0, off).expect("h 的悬停条目").to_owned();
        assert!(!t.is_empty());
    });
}
