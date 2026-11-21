//! L07 参考版的观察面（LSP 引擎侧）测试：docs/l07-lsp-port-2026-11-21.md
//!
//! 被测对象：`src/L07_sum_type/surface.rs`（owned 快照契约）与 `observe.rs`
//! （push/排水点），入口 `run_with_surface` / `run_with_surface_at` /
//! `run_with_surface_query` / `check_with_surface`。
//!
//! 口径：默认关闭时 `run` 输出逐字节不变且快照全空；开启时钉住各来源的
//! hover / inlay / println / check issue / 失败 decl。

#[path = "../src/list.rs"]
mod list;
#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;
#[path = "../src/L07_sum_type/mod.rs"]
mod L07_sum_type;

use L07_sum_type::surface::SurfaceQuery;

/// L07 的精化合一递归很深：黑盒套件的口径是 64MB 栈线程，这里给 256MB。
fn with_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// 源里第 nth（0 基）个 needle 的起始字节偏移。
fn at(src: &str, needle: &str, nth: usize) -> usize {
    src.match_indices(needle)
        .nth(nth)
        .unwrap_or_else(|| panic!("源里找不到第 {nth} 个 {needle:?}"))
        .0
}

const DEF_USE_SRC: &str = "def foo : String = \"x\"\ndef bar : String = foo\nprintln bar\n";

#[test]
fn default_run_unchanged_and_collects_nothing() {
    with_stack(|| {
        let plain = L07_sum_type::run(DEF_USE_SRC, 0).expect("run");
        assert_eq!(plain, "x\n");
        // 带采集入口的 Ok 输出必须与 run 逐字节一致
        let (out, s) = L07_sum_type::run_with_surface(DEF_USE_SRC, 0).expect("surface");
        assert_eq!(out, plain);
        assert!(!s.is_empty(), "采集开启时应有条目");
    });
}

#[test]
fn def_site_and_use_site_hover() {
    with_stack(|| {
        let (_, s) = L07_sum_type::run_with_surface(DEF_USE_SRC, 0).expect("surface");
        let (def_off, use_off) = (at(DEF_USE_SRC, "foo", 0), at(DEF_USE_SRC, "foo", 1));
        let d = s.hover_entry_at(0, def_off).expect("def 定义处应有 hover");
        assert_eq!(d.2, "String");
        let u = s.hover_entry_at(0, use_off).expect("使用处应有 hover");
        assert_eq!(u.2, "String");
        assert_eq!(
            (u.1.start_offset as usize, u.1.end_offset as usize),
            (def_off, def_off + 3),
            "使用处条目的 def_span 应指向 def 名"
        );
        assert!(s.hover_entry_at(1, use_off).is_none(), "别的 path 一律 miss");
    });
}

#[test]
fn literal_hover_and_println_span() {
    with_stack(|| {
        let (out, s) = L07_sum_type::run_with_surface(DEF_USE_SRC, 0).expect("surface");
        assert_eq!(out, "x\n");
        let lit = at(DEF_USE_SRC, "\"x\"", 0) + 1;
        assert_eq!(s.hover_text_at(0, lit), Some("String"), "字面量 hover");
        assert_eq!(s.println_spans.len(), 1, "一条 println: {:?}", s.println_spans);
        assert_eq!(s.println_spans[0].1, "x");
    });
}

#[test]
fn hover_query_renders_only_entry_at_offset() {
    with_stack(|| {
        let use_off = at(DEF_USE_SRC, "foo", 1);
        let (out, s) = L07_sum_type::run_with_surface_at(DEF_USE_SRC, 0, use_off).expect("at");
        assert_eq!(out, "x\n");
        assert_eq!(s.hover.len(), 1, "只应命中一条: {:?}", s.hover);
        assert_eq!(s.hover_text_at(0, use_off), Some("String"));
        // 与全量采集的同一条逐字节相同
        let (_, full) = L07_sum_type::run_with_surface(DEF_USE_SRC, 0).expect("full");
        assert_eq!(&s.hover[0], full.hover_entry_at(0, use_off).unwrap());
        // 未命中：hover 空，println 通道仍在
        let miss = at(DEF_USE_SRC, "println", 0) + 7;
        let (_, m) = L07_sum_type::run_with_surface_at(DEF_USE_SRC, 0, miss).expect("miss");
        assert!(m.hover.is_empty(), "未命中不应渲染: {:?}", m.hover);
        assert_eq!(m.println_spans.len(), 1);
    });
}

#[test]
fn inlay_only_for_holes_in_view() {
    with_stack(|| {
        let src = "def q = \"y\"\n";
        let (_, full) = L07_sum_type::run_with_surface(src, 0).expect("full");
        assert!(
            full.inlay_hint.iter().any(|(_, l)| l == ": String"),
            "无返回类型注解的 def 应推 inlay，实际 {:?}",
            full.inlay_hint
        );
        let name_end = (at(src, "q", 0) + 1) as u32;
        let q = SurfaceQuery::view(name_end as usize, 0, name_end);
        let (_, in_view) = L07_sum_type::run_with_surface_query(src, 0, q).expect("view");
        assert!(
            in_view.inlay_hint.iter().any(|(p, l)| *p <= name_end && l == ": String"),
            "视口内应保留该 inlay: {:?}",
            in_view.inlay_hint
        );
        // 视口远离锚点 ⇒ 该 inlay 不渲染
        let q_far = SurfaceQuery::view(0, 1 << 20, (1 << 20) + 10);
        let (_, far) = L07_sum_type::run_with_surface_query(src, 0, q_far).expect("far");
        assert!(
            far.inlay_hint.is_empty(),
            "视口外不应渲染 inlay: {:?}",
            far.inlay_hint
        );
    });
}

#[test]
fn check_issue_lines_are_drained_once() {
    with_stack(|| {
        let src = concat!(
            "def r1 : U = report_check_issue \"HDL001\" \"m\" \"sig\" \"bad\"\n",
            "println (get_global \"CheckIssues\")\n",
        );
        let (out, s) = L07_sum_type::run_with_surface(src, 0).expect("surface");
        assert!(
            s.check_issues.iter().any(|(d, l)| *d == 0 && l == "HDL001|m|sig|bad"),
            "自检行应进观察通道: {:?}",
            s.check_issues
        );
        assert!(out.contains("HDL001|m|sig|bad"), "Ok 输出保留 CheckIssues: {out:?}");
    });
}

#[test]
fn failed_decl_channel_records_and_continues() {
    with_stack(|| {
        let src = concat!(
            "def good : String = \"ok\"\n",
            "def bad : String = \"ok\" \"ok\"\n",
            "println good\n",
        );
        let (err, s) = L07_sum_type::check_with_surface(src, 0);
        assert!(err.is_some(), "参考版应报错");
        assert_eq!(s.failed_decls, vec!["bad".to_string()]);
        assert_eq!(s.println_spans.len(), 1, "失败后仍继续处理: {:?}", s.println_spans);
        assert_eq!(s.println_spans[0].1, "ok");
        // 错误文案不变（与 run 一致）
        let plain = L07_sum_type::run(src, 0).expect_err("run 也报错");
        assert_eq!(format!("{:?}", plain), format!("{:?}", err.unwrap()));
    });
}

#[test]
fn demo_src_surface_smoke() {
    with_stack(|| {
        let _guard = L07_sum_type::FILE_IO_LOCK.lock().unwrap();
        let plain = L07_sum_type::run(L07_sum_type::DEMO_SRC, 0).expect("run");
        let (out, s) = L07_sum_type::run_with_surface(L07_sum_type::DEMO_SRC, 0).expect("surface");
        assert_eq!(out, plain, "Ok 输出不得因采集改变");
        assert!(!s.hover.is_empty(), "DEMO_SRC 应产生 hover");
        assert!(!s.println_spans.is_empty(), "DEMO_SRC 应产生 println 条目");
        assert!(s.completion.is_empty(), "completion 当前恒空");
    });
}

#[test]
fn ctor_use_site_hover() {
    with_stack(|| {
        let src = concat!(
            "enum Nat {\n    zero\n    succ(x: Nat)\n}\n",
            "def two : Nat = succ (succ zero)\n",
        );
        let (_, s) = L07_sum_type::run_with_surface(src, 0).expect("surface");
        let decl_off = at(src, "succ", 0);
        let use_off = at(src, "succ", 1);
        let e = s.hover_entry_at(0, use_off).expect("构造子使用处应有 hover");
        assert!(e.2.contains("Nat"), "构造子类型应提到 Nat: {:?}", e.2);
        assert_eq!(
            (e.1.start_offset as usize, e.1.end_offset as usize),
            (decl_off, decl_off + 4),
            "def_span 应指向构造子声明"
        );
    });
}
