//! L12_canonical 观察面（L07/L08 移植）：源码注解渲染 + 形状认回。

#[path = "../src/list.rs"]
mod list;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L12_canonical/mod.rs"]
mod L12_canonical;

fn hover_at(src: &str, off: usize) -> Option<String> {
    let (_, s) = L12_canonical::run_with_surface(src, 0).expect("surface");
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
    "def T(n: Nat): Type 0 =\n    match n {\n        case zero => Bool\n        case succ(m) => Nat\n    }\n",
    "def g(n: Nat): T n =\n    match n {\n        case zero => true\n        case succ(m) => zero\n    }\n",
);

/// 有显式类型注解：源码注解渲染。
#[test]
fn annotated_def_shows_source_form() {
    with_stack(|| {
        let off = TY_FAMILY.find("def g(").expect("def g") + 4;
        let t = hover_at(TY_FAMILY, off).expect("g 的悬停条目");
        assert_eq!(t, "(n : Nat) → T n", "应为源码形态");
        assert!(!t.contains("match"), "不得展开: {t}");
    });
}

/// 无注解：形状认回（同样 `T n`）。
#[test]
fn unannotated_def_recovers_type_name() {
    with_stack(|| {
        let src = format!("{TY_FAMILY}def h(n : Nat) = g n\n");
        let off = src.find("def h(").expect("def h") + 4;
        let t = hover_at(&src, off).expect("h 的悬停条目");
        assert_eq!(t, "(n: Nat) → T n", "应认回类型级 def 名");
        assert!(!t.contains("match"), "不得展开: {t}");
    });
}

/// 采集不影响 run 输出。
#[test]
fn surface_does_not_change_run_output() {
    with_stack(|| {
        let src = format!("{TY_FAMILY}def h(n : Nat) = g n\nprintln (g zero)\n");
        let a = L12_canonical::run(&src, 0).expect("run");
        let (b, _) = L12_canonical::run_with_surface(&src, 0).expect("surface");
        assert_eq!(a, b);
    });
}
