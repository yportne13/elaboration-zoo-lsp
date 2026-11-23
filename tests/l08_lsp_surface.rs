//! L08 观察面（L07 移植）：源码注解渲染 + 形状认回。

#[path = "../src/list.rs"]
mod list;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L08_product_type/mod.rs"]
mod L08_product_type;

fn hover_at(src: &str, off: usize) -> Option<String> {
    let (_, s) = L08_product_type::run_with_surface(src, 0).expect("surface");
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

/// 有显式类型注解的 def：源码注解渲染（`T n`，不是展开的 match）。
#[test]
fn annotated_def_shows_source_form() {
    with_stack(|| {
        let off = TY_FAMILY.find("def g(").expect("def g") + 4;
        let t = hover_at(TY_FAMILY, off).expect("g 的悬停条目");
        assert_eq!(t, "(n : Nat) → T n", "应为源码形态");
        assert!(!t.contains("match"), "不得展开: {t}");
    });
}

/// 无类型注解的 def：形状认回（同样显示 `T n`）。
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

/// 采集关闭时 `run` 输出与 `run_with_surface` 的 Ok 部分逐字节一致。
#[test]
fn surface_does_not_change_run_output() {
    with_stack(|| {
        let src = format!("{TY_FAMILY}def h(n : Nat) = g n\nprintln (g zero)\n");
        let a = L08_product_type::run(&src, 0).expect("run");
        let (b, _) = L08_product_type::run_with_surface(&src, 0).expect("surface");
        assert_eq!(a, b);
    });
}

/// println 通道：每个 println 体都有 span + 渲染串。
#[test]
fn println_spans_are_collected() {
    with_stack(|| {
        let src = concat!(
            "enum Nat {\n    zero\n    succ(x: Nat)\n}\n",
            "def two = succ (succ zero)\n",
            "println two\n",
        );
        let (out, s) = L08_product_type::run_with_surface(src, 0).expect("surface");
        assert_eq!(s.println_spans.len(), 1, "应有一条 println 通道");
        assert_eq!(s.println_spans[0].1, out.trim_end(), "渲染串应与输出一致");
        assert!(s.println_spans[0].0.end_offset > s.println_spans[0].0.start_offset);
    });
}

/// inlay 通道：洞（已知期望类型）补 `: <type>`。
#[test]
fn hole_inlay_is_collected() {
    with_stack(|| {
        let src = "enum Nat {\n    zero\n    succ(x: Nat)\n}\ndef f : Nat = _\n";
        let (_, s) = L08_product_type::run_with_surface(src, 0).expect("surface");
        assert!(
            s.inlay_hint.iter().any(|(_, t)| t == ": Nat"),
            "洞的期望类型已知时应推 inlay: {:?}",
            s.inlay_hint
        );
    });
}
