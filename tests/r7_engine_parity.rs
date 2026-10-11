// R7 (2026-10-11): reference-vs-twin engine parity on a compact matrix.
//
// Each case is elaborated through BOTH engines (Backend::on_change with
// Engine::Reference / Engine::Twin) and the verdicts must agree: same
// error/no-error classification, and same println notes when clean.
// Known asymmetries (recorded in the round docs) are excluded here.

use std::sync::{Arc, Mutex};

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{Backend, Engine, TextDocumentItem};
use lsp_types::{MessageType, Url};

#[derive(Default)]
struct Cap {
    diags: Mutex<Vec<(Url, Vec<lsp_types::Diagnostic>, Option<i32>)>>,
}

impl ClientLike for Cap {
    fn publish_diagnostics(&self, uri: Url, d: Vec<lsp_types::Diagnostic>, v: Option<i32>) {
        self.diags.lock().unwrap().push((uri, d, v));
    }
    fn show_message(&self, _: MessageType, _: String) {}
    fn log_message(&self, _: MessageType, _: String) {}
}

fn run(engine: Engine, text: &str) -> (bool, Vec<String>) {
    let b = Backend::new_with_engine(Cap::default(), engine);
    b.load_prelude();
    let uri = Url::parse("file:///probe/r7_parity.typort").unwrap();
    b.on_change::<false>(TextDocumentItem { uri: uri.clone(), text, version: None });
    let ds = b.client.diags.lock().unwrap().iter()
        .filter(|(u, _, _)| u == &uri)
        .flat_map(|(_, d, _)| d.iter().cloned())
        .collect::<Vec<_>>();
    let has_err = ds.iter().any(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR));
    let notes = ds.iter()
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::INFORMATION))
        .map(|d| {
            // normalize: keep only the leading `note: ` payload up to the
            // first newline/whitespace gap (spans differ between engines)
            let m = d.message.trim();
            m.split_whitespace().next().unwrap_or(m).to_string()
        })
        .collect();
    (has_err, notes)
}

fn parity(name: &str, src: &str) {
    let (ref_err, ref_notes) = run(Engine::Reference, src);
    let (tw_err, tw_notes) = run(Engine::Twin, src);
    assert_eq!(
        ref_err, tw_err,
        "{name}: error verdict diverged (ref={ref_err} twin={tw_err})\nsrc:\n{src}"
    );
    if !ref_err {
        assert_eq!(
            ref_notes, tw_notes,
            "{name}: println notes diverged\nref:   {ref_notes:?}\ntwin:  {tw_notes:?}\nsrc:\n{src}"
        );
    }
}

const NATD: &str = "enum Nat2 {\n  zero2\n  succ2(x: Nat2)\n}\n";

#[test]
fn parity_matrix() {
    // --- evaluation / conversion ---
    parity("beta", "def p1: Nat = nat_add(2, 3)\nprintln(p1)\n");
    parity("literal", "println(123)\n");
    parity("recursion", "def f6(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => f6(m) + 1\n}\nprintln(f6(5))\n");
    parity("ackermann", "def ack2(m: Nat, n: Nat): Nat = match m {\n  case zero => n + 1\n  case succ(mm) => match n {\n    case zero => ack2(mm, 1)\n    case succ(nn) => ack2(mm, ack2(m, nn))\n  }\n}\nprintln(ack2(2, 3))\n");
    parity("eq_refl", "def q1: Eq(nat_add(2, 3), 5) = rfl\nprintln(q1)\n");
    parity("universe_ok", "def u1: Type 3 = Type 2\nprintln(0)\n");
    parity("universe_err", "def u2: Type 4294967295 = Type 0\nprintln(0)\n");
    parity("type_err", "def t9: Nat = \"s\"\nprintln(0)\n");
    parity("undefined", "println(nope9)\n");

    // --- match / data ---
    parity("match_nat", "def p2(n: Nat): Nat = match n {\n  case zero => 1\n  case succ(m) => m\n}\nprintln(p2(7))\n");
    parity("match_bool", "def p3(v: Boolean): Nat = match v {\n  case true => 1\n  case false => 0\n}\nprintln(p3(false))\n");
    parity("enum_match", "enum C2 {\n  r2\n  b2\n}\ndef p4(c: C2): Nat = match c {\n  case r2 => 1\n  case b2 => 2\n}\nprintln(p4(b2))\n");
    parity("recursive_enum", "enum T2 {\n  leaf2(v: Nat)\n  node2(l: T2, r: T2)\n}\ndef s2(t: T2): Nat = match t {\n  case leaf2(v) => v\n  case node2(l, r) => s2(l) + s2(r)\n}\nprintln(s2(node2(leaf2(1), node2(leaf2(2), leaf2(3)))))\n");
    parity("gadt_index", "enum F2(n: Nat) {\n  fz2[m: Nat] -> F2(m + 1)\n}\ndef g2(i: F2(2)): Nat = match i {\n  case fz2 => 0\n}\nprintln(g2(fz2))\n");
    parity("eq_match", "def p5[A: Type 0](x: A, y: A)(e: Eq(x, y)): Eq(y, x) = match e {\n  case refl(a) => rfl\n}\nprintln(p5(1, 1)(rfl))\n");

    // --- implicit / typeclass ---
    parity("implicit_solved", "def idd3[A: Type 0](x: A): A = x\nprintln(idd3(5))\n");
    parity("typeclass", "trait Doub {\n  def dbl_v(x: Nat): Nat\n}\nimpl Doub for Nat {\n  def dbl_v(x: Nat): Nat = x + x\n}\ndef useD[T][d: Doub[T]](t: T): Nat = d.dbl_v t\nprintln(useD(6))\n");
    parity("supertrait_order", "trait B7 {\n  def bm7: Nat\n}\ntrait S7: B7 {\n  def sm7: Nat\n}\nimpl S7 for Nat {\n  def bm7: Nat = 1\n  def sm7: Nat = 2\n}\ndef useS7[T][d: S7[T]](t: T): Nat = d.sm7 t\nprintln(useS7(0))\n");
    parity("default_method", "trait Gr {\n  def hello: String = \"hi\"\n}\nimpl Gr for Nat {\n}\ndef n1: Nat = 1\nprintln(n1.hello)\n");
    parity("ty001_defaulting", "def t10: Type 0 = _\nprintln(3)\n");
    parity("hole_err", "def h9: Nat = _\nprintln(0)\n");

    // --- namespace / packages ---
    parity("package_call", "package pm\ndef sq9(x: Nat): Nat = x * x\nprintln(pm.sq9(4))\n");
    parity("import_wildcard", "package pn\ndef hf(x: Nat): Nat = nat_div(x, 2)\nimport pn.hf\nprintln(hf(8))\n");
    parity("qualified_ctor", "package ps\nenum E8 {\n  c8\n}\ndef g8(x: E8): Nat = 1\nprintln(ps.g8(ps.E8.c8))\n");
    parity("ns_member_err", "package pq\ndef ok9(x: Nat): Nat = x\nprintln(pq.missing9(1))\n");

    // --- macros ---
    parity("macro_decl", "macro_rules mk9 {\n  ($n:ident) => {\n    def $n: Nat = 42;\n  };\n}\nmk9 nine9\nprintln(nine9)\n");
    parity("macro_too_deep", "macro_rules rl9 {\n  (a) => { rl9 a };\n}\nrl9 a\nprintln(0)\n");
    parity("stringify", "println(stringify zz)\n");

    // --- structs / tuples ---
    parity("struct_basic", "struct PP {\n  a1: Nat\n  b1: Nat\n}\ndef pp: PP = PP.mk(3, 4)\nprintln(pp.a1 + pp.b1)\n");
    parity("tuple_literal", "def t7 = (1, 2)\nprintln(t7)\n");
    parity("nat2_enum", &format!("{NATD}def two2: Nat2 = succ2(zero2)\nprintln(two2)\n"));

    // --- termination ---
    parity("term_ok", "def f7(n: Nat): Nat = match n {\n  case zero => 0\n  case succ(m) => f7(m) + 1\n}\nprintln(f7(3))\n");
    parity("term_err", "def bad7(n: Nat): Nat = bad7(n)\nprintln(0)\n");
    parity("term_lambda", "def f8: Nat -> Nat = n => match n {\n  case zero => 0\n  case succ(m) => f8(m)\n}\nprintln(f8(2))\n");
}
