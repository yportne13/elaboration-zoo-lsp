//! L06 的 LSP 引擎侧观察面测试（`docs/l06-lsp-port-2026-11-20.md`）。
//!
//! 被测对象：`src/L06_string/surface.rs`（owned 快照契约）、参考版
//! `observe.rs`（`Infer`）与孪生 `bump_spine_iter/observe.rs`（`Machine`）
//! 的 push/排水点。核心断言：
//!
//! 1. **默认关闭**：`run` / `bench_check*` 与改动前逐字节一致，且快照全空；
//! 2. **两版逐条一致**：同一源在参考版与孪生上产生的 hover / inlay /
//!    println / check_issues / failed_decls 逐条相等（这是 owned 契约的
//!    可测形式）；
//! 3. 各来源的 hover 都钉住：def 定义处、builtin 定义处、使用处、let
//!    binder、字面量、`?N` 洞；
//! 4. println span、check issue 行、失败 decl 通道；
//! 5. 求值预算：发散求值在预算内落成 `Err` 而不是挂死。
//!
//! 入口说明见移植文档 §2.2：参考版 `run_with_surface` /
//! `check_with_surface` / `run_with_surface_budget`；孪生
//! `Tycker::run_input_with_surface` / `check_with_surface` /
//! `run_input_with_surface_budget`。
//!
//! 观察面的**已知降级**（与两版一致，测试按降级后的值断言）：
//! - builtin 条目零 def_span（无源码定义处）；
//! - `Raw::Hole` / `Raw::U` 无源码 span，折叠到邻近叶子（洞的 inlay 锚点
//!   退到 binder 尾 / 0）；
//! - 引自 `Raw` 折叠的 span 覆盖"能拿到的最外叶子"，必要时不含括号。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L06_string/mod.rs"]
mod L06_string;

use L06_string::bump_spine_iter as fast;
use L06_string::surface::LspSurface;

type Pair = (String, LspSurface);

/// 两版同时跑同一源（采集开启），返回 (参考版, 孪生)。
fn both(src: &str, path_id: u32) -> (Pair, Pair) {
    let b = L06_string::run_with_surface(src, path_id).expect("参考版应通过");
    let mut t = fast::Tycker::new();
    let f = t.run_input_with_surface(src, path_id).expect("孪生应通过");
    (b, f)
}

/// 有序序列逐条相等，失败时只打印**首个差异**与窗口（整表 Debug 动辄上万
/// 字符，定位不了）。
fn assert_seq_same<T: std::fmt::Debug + PartialEq>(l: &[T], r: &[T], what: &str) {
    if l == r {
        return;
    }
    if l.len() != r.len() {
        let tail = |v: &[T]| -> Vec<String> { v[v.len().saturating_sub(3)..].iter().map(|x| format!("{x:?}")).collect() };
        panic!(
            "{what} 长度不一致: 参考版 {} 条 vs 孪生 {} 条\n  参考版尾部 {:?}\n  孪生尾部   {:?}",
            l.len(),
            r.len(),
            tail(l),
            tail(r)
        );
    }
    if let Some(i) = l.iter().zip(r.iter()).position(|(x, y)| x != y) {
        let lo = i.saturating_sub(3);
        let hi = (i + 4).min(l.len());
        panic!(
            "{what} 第 {i} 条不一致:\n  参考版 {:?}\n  孪生   {:?}\n  前文(参考版) {:?}\n  前文(孪生)   {:?}",
            l[i],
            r[i],
            &l[lo..i],
            &r[lo..i]
        );
    }
    panic!("{what} 不一致（无可定位差异）");
}

/// 两版观察面逐条相等（`hover` 连同顺序；全部通道）。
///
/// `prime_allow`：允许多少条 hover 串仅在**撇号（fresh 后缀）**上不同——
/// 两版共用的 `pretty::fresh` 在"名字表里已有同名"时补 `'`，而两版在
/// push 时刻的局部名字表快照可以差一个 binder（L13 把这一类记作"残余
/// fresh 后缀显示差异"）。类型本身是 alpha-等价的，故按可数豁免处理：
/// 默认 0，DEMO_SRC 全量互检恰好 1 条（`x` vs `x'`）。
fn assert_surface_parity_impl(b: &LspSurface, f: &LspSurface, prime_allow: usize) {
    assert_seq_same(&b.completion, &f.completion, "completion");
    assert_seq_same(&b.inlay_hint, &f.inlay_hint, "inlay");
    assert_seq_same(&b.println_spans, &f.println_spans, "println");
    assert_seq_same(&b.check_issues, &f.check_issues, "check issue");
    assert_seq_same(&b.failed_decls, &f.failed_decls, "failed decl");
    if b.hover == f.hover {
        return;
    }
    assert_eq!(
        b.hover.len(),
        f.hover.len(),
        "hover 条目数不一致: 参考版 {} / 孪生 {}\n  参考版 {:?}\n  孪生   {:?}",
        b.hover.len(),
        f.hover.len(),
        b.hover,
        f.hover
    );
    let mut hard: Vec<usize> = Vec::new();
    let mut prime_only: Vec<usize> = Vec::new();
    for (i, (x, y)) in b.hover.iter().zip(f.hover.iter()).enumerate() {
        if x == y {
            continue;
        }
        if x.0 == y.0 && x.1 == y.1 && x.2.replace('\'', "") == y.2.replace('\'', "") {
            prime_only.push(i);
            continue;
        }
        hard.push(i);
    }
    if let Some(&i) = hard.first() {
        panic!(
            "hover 有 {} 条非撇号差异（首条 #{i}）:\n  参考版 {:?}\n  孪生   {:?}",
            hard.len(),
            b.hover[i],
            f.hover[i]
        );
    }
    assert!(
        prime_only.len() <= prime_allow,
        "hover 撇号差异 {} 条（允许 {prime_allow}）: {prime_only:?}\n  参考版 {:?}\n  孪生   {:?}",
        prime_only.len(),
        b.hover[prime_only[0]],
        f.hover[prime_only[0]]
    );
}

fn assert_surface_parity(b: &LspSurface, f: &LspSurface) {
    assert_surface_parity_impl(b, f, 0);
}

/// 在源里找第 `nth`（0 基）个 `needle` 的起始字节偏移。
fn at(src: &str, needle: &str, nth: usize) -> usize {
    src.match_indices(needle)
        .nth(nth)
        .unwrap_or_else(|| panic!("源里找不到第 {nth} 个 {needle:?}"))
        .0
}

// ── 1. 默认关闭：既有行为不变 + 快照全空 ────────────────────────────────

#[test]
fn default_run_is_unchanged_and_collects_nothing() {
    let src = "def s : String = \"hi\"\nprintln s\n";
    let plain = L06_string::run(src, 0).expect("run");
    assert_eq!(plain, "hi\n");

    let mut t = fast::Tycker::new();
    assert_eq!(t.run_input(src, 0).expect("fast run"), plain);

    let raw = L06_string::parser::parser(&L06_string::preprocess(src), 0).expect("parse");
    assert!(L06_string::bench_check(&raw));
    // bench 的 nf 口径取最后一个 **def** 的登记值（本源的 println 不算）
    assert_eq!(L06_string::bench_check_nf(&raw), 1, "`s` 的 nf 是字面量节点");

    // 采集关闭：`run_input` 之后快照全空
    assert!(t.surface().is_empty(), "默认关闭时不应采到任何条目");
    assert!(!t.observe_on(), "孪生默认不采集");
}

// ── 2. def 定义处 + 使用处 hover（两版逐条一致）────────────────────────

#[test]
fn def_site_and_use_site_hover() {
    let src = "def foo : String = \"x\"\ndef bar : String = foo\n";
    let (b, f) = both(src, 7);
    assert_surface_parity(&b.1, &f.1);

    let (def_off, use_off) = (at(src, "foo", 0), at(src, "foo", 1));
    let e = b.1.hover_entry_at(7, use_off).expect("使用处应有 hover");
    assert_eq!(e.2, "String");
    assert_eq!(
        (e.1.start_offset as usize, e.1.end_offset as usize),
        (def_off, def_off + 3),
        "使用处条目的 def_span 应指向 def 名"
    );

    let d = b.1.hover_entry_at(7, def_off).expect("定义处应有 hover");
    assert_eq!(d.2, "String");
    assert_eq!(
        (d.0.start_offset as usize, d.0.end_offset as usize),
        (def_off, def_off + 3)
    );
    // 别的 path_id 一律 miss（span 的 path_id 参与过滤）
    assert!(b.1.hover_entry_at(8, use_off).is_none());
}

// ── 3. builtin 的 def-site hover（span 为零，但文本必须对）──────────────

#[test]
fn builtin_use_site_hover_text() {
    let src = "def s : String = string_concat \"a\" \"b\"\nprintln s\n";
    let (b, f) = both(src, 0);
    assert_surface_parity(&b.1, &f.1);
    let off = at(src, "string_concat", 0);
    let e = b.1.hover_entry_at(0, off).expect("builtin 使用处应有 hover");
    assert_eq!(
        e.2, "(x: String) → (y: String) → String",
        "builtin 类型应渲染成 Π 链（实际 {:?}）", e.2
    );
    // builtin 无源码定义处 ⇒ 零 span（与 L13 的"零 span 条目"同族）
    assert_eq!((e.1.start_offset, e.1.end_offset), (0, 0));
}

// ── 4. let binder：定义处 hover + 无注解时的 inlay ──────────────────────

#[test]
fn let_binder_hover_and_inlay() {
    let src = "def f : String = let x = \"v\"; x\n";
    let (b, f) = both(src, 0);
    assert_surface_parity(&b.1, &f.1);

    // binder 是 let 的名字 `x`（不是字面量里的字符）：定义处 hover 与 inlay
    // 都锚在它上面（inlay 在名尾）。
    let binder = at(src, "x", 0);
    let use_off = at(src, "x", 1);
    let e = b.1.hover_entry_at(0, binder).expect("let binder 应有 hover");
    assert_eq!(e.2, "String", "binder 的 hover 是它的类型");

    // 无类型注解 ⇒ 一条 inlay `: String`，锚点是 binder 名尾
    let hint = b
        .1
        .inlay_hint
        .iter()
        .find(|(pos, _)| *pos as usize == binder + 1)
        .unwrap_or_else(|| panic!("缺 let inlay，实际 {:?}", b.1.inlay_hint));
    assert_eq!(hint.1, ": String", "inlay 必须显示**类型**而不是值");

    // 体内使用处回指 binder（def_span 是 binder 名）
    let u = b.1.hover_entry_at(0, use_off).expect("使用处应有 hover");
    assert_eq!(u.2, "String");
    assert_eq!(u.1.start_offset as usize, binder);
}

// ── 5. 字面量 hover（L06 增量）──────────────────────────────────────────

#[test]
fn string_literal_hover() {
    let src = "def s : String = \"hello\"\nprintln s\n";
    let (b, f) = both(src, 0);
    assert_surface_parity(&b.1, &f.1);
    let lit = at(src, "\"hello\"", 0) + 1; // 引号内
    let e = b.1.hover_entry_at(0, lit).expect("字面量应有 hover");
    assert_eq!(e.2, "String");
    // 字面量条目的 span 精确覆盖引号内的内容（parser 的 Str token 不含引号）
    assert_eq!(
        (e.0.start_offset as usize, e.0.end_offset as usize),
        (lit, lit + 5)
    );
}

// ── 6. 洞 / `?N`：类型已知时补 inlay，未定时不推 ────────────────────────

#[test]
fn hole_inlay_only_when_type_is_known() {
    // 期望类型 `String` 已知 ⇒ 推 `: String`
    let src = "def s : String = _\nprintln s\n";
    let (b, f) = both(src, 0);
    assert_surface_parity(&b.1, &f.1);
    assert!(
        b.1.inlay_hint.iter().any(|(_, l)| l == ": String"),
        "洞的期望类型已知时应推 inlay，实际 {:?}",
        b.1.inlay_hint
    );
    // println 输出仍是 `?N` 形态（既有契约不因采集改变）
    assert!(b.0.starts_with('?'), "println 输出应保持 `?N` 形态: {:?}", b.0);

    // 期望类型未定（推断位置的洞，类型是刚造的未解 meta）⇒ 不推 inlay
    // （不把 `?N` 泄漏到提示里）。`println _` 同时是 L06 的既有习语（输出 `?0`）。
    let src2 = "println _\n";
    let (b2, f2) = both(src2, 0);
    assert_surface_parity(&b2.1, &f2.1);
    assert!(
        b2.1.inlay_hint.is_empty(),
        "推断位置的洞类型未定 ⇒ 不推 inlay，实际 {:?}",
        b2.1.inlay_hint
    );
    assert!(b2.0.starts_with('?'), "println 输出应保持 `?N` 形态: {:?}", b2.0);
}

// ── 7. println span ─────────────────────────────────────────────────────

#[test]
fn println_spans_cover_the_printed_expression() {
    let src = "def s : String = \"v\"\nprintln string_concat s \"!\"\n";
    let (b, f) = both(src, 0);
    assert_surface_parity(&b.1, &f.1);
    assert_eq!(b.1.println_spans.len(), 1);
    let (span, rendered) = &b.1.println_spans[0];
    assert_eq!(rendered, "v!");
    let start = at(src, "string_concat", 0);
    assert_eq!(span.start_offset as usize, start);
    assert!(span.end_offset as usize > start, "span 应覆盖整条 println 体");
}

// ── 8. check issue 行（`report_check_issue` → 观察通道）────────────────

#[test]
fn check_issue_lines_are_drained_once() {
    let src = concat!(
        "def r1 : U = report_check_issue \"HDL001\" \"m\" \"sig\" \"bad\"\n",
        "def r2 : U = report_check_issue \"HDL001\" \"m\" \"sig\" \"bad\"\n",
        "def r3 : U = report_check_issue \"HDL002\" \"m\" \"\" \"other\"\n",
        "println (get_global \"CheckIssues\")\n",
    );
    let (b, f) = both(src, 0);
    assert_surface_parity(&b.1, &f.1);
    // 行级去重（prim 侧）⇒ 两条不同行；排水按 decl 归属
    let lines: Vec<&str> = b.1.check_issues.iter().map(|(_, l)| l.as_str()).collect();
    assert_eq!(lines, vec!["HDL001|m|sig|bad", "HDL002|m||other"]);
    assert_eq!(b.1.check_issues[0].0, 0, "首行属 decl 0");
    assert_eq!(b.1.check_issues[1].0, 2, "第二行属 decl 2（decl 1 重复被去重）");
    assert_eq!(
        L06_string::surface::format_check_warning(lines[0]),
        "[hdl][warning] HDL001 [m] sig: bad"
    );
    // **既有 Ok 输出不变**：排水只读，全局仍可读
    assert!(
        b.0.contains("HDL001|m|sig|bad"),
        "println 输出应保留 CheckIssues: {:?}",
        b.0
    );
}

// ── 9. 失败 decl 通道（opt-in 继续驱动）────────────────────────────────

#[test]
fn failed_decl_channel_records_and_continues() {
    // `def bad : String = 42` 失败（字面量不是 String 类型）
    let src = concat!(
        "def good : String = \"ok\"\n",
        "def bad : String = \"ok\" \"ok\"\n",
        "println good\n",
    );
    let (err_b, sb) = L06_string::check_with_surface(src, 0);
    let raw = L06_string::parser::parser(&L06_string::preprocess(src), 0).expect("parse");
    let mut t = fast::Tycker::new();
    let (err_f, sf) = t.check_with_surface(&raw);
    assert!(err_b.is_some(), "参考版应报错");
    assert!(err_f.is_some(), "孪生应报错");
    assert_eq!(sb.failed_decls, vec!["bad".to_string()]);
    assert_eq!(sf.failed_decls, sb.failed_decls);
    // 继续驱动：失败之后的 decl 仍被处理（println 仍产出渲染串）
    assert_eq!(sb.println_spans.len(), 1);
    assert_eq!(sb.println_spans[0].1, "ok");
    assert_eq!(sf.println_spans, sb.println_spans);
    // 失败通道**不改错误文案**（L06 的既有判定/文案契约）
    assert!(
        err_b.unwrap().to_string().contains("can't unify"),
        "错误文案应保持原样"
    );
}

// ── 10. 求值预算：发散求值落成 Err，不挂死 ──────────────────────────────

#[test]
fn eval_budget_stops_divergent_recursion() {
    // `def loop (x : U) : U = loop x` + 应用 ⇒ delta 展开无基底，求值发散
    let src = "def loop (x : U) : U = loop x\nprintln loop U\n";

    // 参考版：递归求值器 ⇒ 栈增长先于时间预算耗尽。生产口径（LSP/CLI 主线程
    // 64 MiB 栈，见 .cargo/config.toml）下预算能中止；测试线程默认 2 MiB 会先
    // 爆栈，故这里显式开 64 MiB 线程复现生产口径（能力边界见移植文档 §3.3）。
    let handle = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let started = std::time::Instant::now();
            let r = L06_string::run_with_surface_budget(src, 0, 20);
            (r, started.elapsed())
        })
        .expect("spawn");
    let (b, elapsed) = handle.join().expect("参考版线程不应爆栈（64 MiB 口径）");
    let e = b.expect_err("参考版预算应中止发散求值");
    assert!(e.to_string().starts_with("elab timeout"), "实际错误: {e}");
    assert!(
        elapsed < std::time::Duration::from_secs(20),
        "预算应在 20ms 量级中止，实际 {elapsed:?}"
    );

    // 孪生同一负载（迭代求值器：无预算会真挂死）
    let started = std::time::Instant::now();
    let mut t = fast::Tycker::new();
    let f = t.run_input_with_surface_budget(src, 0, 20);
    let elapsed = started.elapsed();
    let e = f.expect_err("孪生预算应中止发散求值");
    assert!(e.to_string().starts_with("elab timeout"), "实际错误: {e}");
    assert!(
        elapsed < std::time::Duration::from_secs(20),
        "孪生预算应在 20ms 量级中止，实际 {elapsed:?}"
    );

    // 预算作用域随入口退出（不泄漏到后续调用）
    assert_eq!(L06_string::eval_budget::current_budget_ms(), None);
}

// ── 11. 预算默认关闭：正常负载不受影响 ─────────────────────────────────

#[test]
fn budget_is_off_by_default() {
    assert!(L06_string::eval_budget::current_budget_ms().is_none());
    let src = "def s : String = \"v\"\nprintln s\n";
    let (b, f) = both(src, 0);
    assert_eq!(b.0, "v\n");
    assert_eq!(f.0, b.0);
    assert_surface_parity(&b.1, &f.1);
    assert!(!b.1.is_empty(), "采集开启时应有条目");
}

// ── 12. DEMO_SRC 全量两版互检 ───────────────────────────────────────────

#[test]
fn demo_src_surface_parity() {
    let _guard = L06_string::FILE_IO_LOCK.lock().unwrap();
    let (b, f) = both(L06_string::DEMO_SRC, 0);
    // 全量语料（217 条 hover）：逐条相等，除**恰好 1 条**撇号差异（`x` vs
    // `x'`）。根因是"登记期缓存串 vs 使用处实时渲染"的局部名字表快照差
    // （参考版在使用处实时渲染，孪生复用登记期串；alpha-等价，L13 记作
    // "残余 fresh 后缀显示差异"）。豁免数是回归钉：再出现第二条即失败。
    assert_surface_parity_impl(&b.1, &f.1, 1);
    // Ok 输出与关闭采集的 `run` 逐字节一致
    let plain = L06_string::run(L06_string::DEMO_SRC, 0).expect("run");
    assert_eq!(b.0, plain, "采集不得改动 Ok 输出（参考版）");
    assert_eq!(f.0, plain, "采集不得改动 Ok 输出（孪生）");
    assert!(!b.1.hover.is_empty(), "DEMO_SRC 应产生 hover 条目");
    assert!(!b.1.println_spans.is_empty(), "DEMO_SRC 应产生 println 条目");
    // 已知降级：completion 恒空（L06 无成员访问）
    assert!(b.1.completion.is_empty(), "L06 无成员访问 ⇒ completion 恒空");
}

// ── 13. 按偏移采集（惰性 hover）：只在光标处渲染 ───────────────────────

#[test]
fn hover_query_renders_only_the_entry_at_the_offset() {
    let src = "def foo : String = \"x\"\ndef bar : String = foo\n";
    let use_off = at(src, "foo", 1);

    let b = L06_string::run_with_surface_at(src, 0, use_off).expect("参考版 _at");
    let mut t = fast::Tycker::new();
    let f = t
        .run_input_with_surface_at(src, 0, use_off)
        .expect("孪生 _at");
    assert_eq!(b.0, f.0, "Ok 输出与全量采集一致");
    assert_surface_parity(&b.1, &f.1);
    assert_eq!(b.1.hover.len(), 1, "按偏移采集只应命中一条: {:?}", b.1.hover);
    assert_eq!(b.1.hover_text_at(0, use_off), Some("String"));

    // 与全量采集的**同一条**逐字节一致（同一渲染管线、同一站点上下文）
    let full = L06_string::run_with_surface(src, 0).expect("参考版 full");
    let want = full.1.hover_entry_at(0, use_off).expect("全量里应有该条");
    assert_eq!(&b.1.hover[0], want, "按偏移采集的条目应与全量逐字节相同");

    // 命中 def 名（定义处）：同样只一条，且渲染的是登记串
    let def_off = at(src, "foo", 0);
    let bd = L06_string::run_with_surface_at(src, 0, def_off).expect("参考版 _at def");
    let mut td = fast::Tycker::new();
    let fd = td.run_input_with_surface_at(src, 0, def_off).expect("孪生 _at def");
    assert_surface_parity(&bd.1, &fd.1);
    assert_eq!(bd.1.hover.len(), 1);
    assert_eq!(bd.1.hover_text_at(0, def_off), Some("String"));
}

#[test]
fn hover_query_miss_leaves_file_wide_channels_intact() {
    let src = "def a : String = \"x\"\nprintln a\n";
    // 落在 \"println\" 之后、不在任何使用处 span 内的偏移：hover 空，但
    // println 通道（全文件消费）仍在。
    let miss = at(src, "println", 0) + 7;
    let b = L06_string::run_with_surface_at(src, 0, miss).expect("参考版 _at");
    let mut t = fast::Tycker::new();
    let f = t.run_input_with_surface_at(src, 0, miss).expect("孪生 _at");
    assert_eq!(b.0, f.0);
    assert_surface_parity(&b.1, &f.1);
    assert!(b.1.hover.is_empty(), "未命中时不应渲染悬停: {:?}", b.1.hover);
    assert_eq!(b.1.println_spans.len(), 1, "println 通道不随偏移过滤");
    assert_eq!(b.1.println_spans[0].1, "x");
}

// ── 14. inlay 可见区（查询口径的 inlay 半边）────────────────────────────

#[test]
fn inlay_view_only_renders_hints_in_range() {
    // 两个无返回类型注解的 def ⇒ 每个各两条 inlay：洞型注解的 `: U`（锚点退到
    // 0，顶层无 binder）与 def 名尾的 `: String`（推断返回类型）。
    let src = "def a = \"x\"\ndef b = \"y\"\n";
    let full = L06_string::run_with_surface(src, 0).expect("全量");
    let full_str: Vec<&(u32, String)> =
        full.1.inlay_hint.iter().filter(|(_, l)| l == ": String").collect();
    assert_eq!(full_str.len(), 2, "全量应有两条名尾 inlay: {:?}", full.1.inlay_hint);

    // 视口只覆盖 def a 的名尾（0..=5）：def b 的名尾 inlay 必须不渲染。
    // （洞型注解的 `: U` 锚点被降级到 0，落在视口内，属既有降级规则。）
    let a_end = (at(src, "a", 0) + 1) as u32;
    let q = L06_string::surface::SurfaceQuery::view(a_end as usize, 0, a_end);
    let b = L06_string::run_with_surface_query(src, 0, q).expect("参考版 view");
    let mut t = fast::Tycker::new();
    let f = t.run_input_with_surface_query(src, 0, q).expect("孪生 view");
    assert_eq!(b.0, f.0);
    assert_surface_parity(&b.1, &f.1);
    let view_str: Vec<&(u32, String)> =
        b.1.inlay_hint.iter().filter(|(_, l)| l == ": String").collect();
    assert_eq!(
        view_str.len(),
        1,
        "视口只含第一个 def 的名尾 inlay: {:?}",
        b.1.inlay_hint
    );
    assert!(view_str[0].0 <= a_end);
    // 视口外的 inlay 不渲染，但 println 通道等全量通道不受影响
    assert_eq!(b.1.println_spans.len(), full.1.println_spans.len());
}
