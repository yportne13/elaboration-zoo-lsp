// Goto-definition for `impl` headers (typeclass impls): integration tests
// that drive the LSP `Backend` and assert that
//   - clicking the typeclass name in `impl XXX for xx` resolves to the trait
//     declaration (`trait XXX`) — not back into the impl itself;
//   - clicking a method name in the impl body resolves to the method's
//     declaration in the trait;
// including cross-file jumps into the prelude's `hdl-bus.typort` (loaded as
// `builtin:///hdl-bus.typort`).

use std::sync::Mutex;

use elaboration_zoo_lsp::client::ClientLike;
use elaboration_zoo_lsp::{position_to_offset, Backend};
use lsp_types::{Diagnostic, GotoDefinitionResponse, MessageType, Url};

#[derive(Default)]
struct CapturingClient {
    diagnostics: Mutex<Vec<(Url, Vec<Diagnostic>, Option<i32>)>>,
}

impl ClientLike for CapturingClient {
    fn publish_diagnostics(&self, uri: Url, diagnostics: Vec<Diagnostic>, version: Option<i32>) {
        self.diagnostics.lock().unwrap().push((uri, diagnostics, version));
    }
    fn show_message(&self, _typ: MessageType, _message: String) {}
    fn log_message(&self, _typ: MessageType, _message: String) {}
}

/// Byte offset of `needle` in `src` (single occurrence expected).
fn byte_offset(src: &str, needle: &str) -> usize {
    src.find(needle).unwrap_or_else(|| panic!("{needle:?} not found in:\n{src}"))
}

/// Location (uri + byte range) that the full `goto_definition` resolution
/// (`Backend::goto_definition_at`, the same logic the LSP
/// `textDocument/definition` handler runs) returns for the cursor at `offset`.
fn goto_full(b: &Backend<CapturingClient>, uri: &Url, offset: usize) -> Option<(String, usize, usize)> {
    match b.goto_definition_at(uri, offset) {
        Some(GotoDefinitionResponse::Scalar(loc)) => {
            let rope = b.document_map.get(loc.uri.as_str()).unwrap();
            let start = position_to_offset(loc.range.start, &rope)
                .expect("start position should convert back to offset");
            let end = position_to_offset(loc.range.end, &rope)
                .expect("end position should convert back to offset");
            Some((loc.uri.to_string(), start, end))
        }
        Some(GotoDefinitionResponse::Array(_)) => panic!("expected a scalar location"),
        Some(GotoDefinitionResponse::Link(_)) => panic!("expected a scalar location"),
        None => None,
    }
}

/// The prelude (including hdl-bus.typort with `trait IMasterSlave`) is loaded
/// through the same on_change path as the real server, so `document_id`/
/// `document_map` contain the builtin URIs and def spans carry the prelude's
/// path_id.
fn setup() -> std::sync::Arc<Backend<CapturingClient>> {
    let client = CapturingClient::default();
    let b = Backend::new(client);
    b.load_prelude();
    b
}

#[test]
fn goto_impl_trait_name_jumps_to_trait_decl() {
    let b = setup();
    let uri = Url::parse("file:///trait_impl.typort").unwrap();
    let src = "\
trait Foo {
    def m: Nat
}
impl Foo for Nat {
    def m: Nat = 1
}
";
    b.process_file(&uri, src, Some(1));

    // Click on the typeclass name `Foo` in the impl header → `trait Foo`.
    let impl_name = byte_offset(src, "impl Foo") + "impl ".len();
    let (def_uri, start, end) = goto_full(&b, &uri, impl_name)
        .expect("click on the impl header's typeclass name must resolve to a definition");
    assert_eq!(def_uri, uri.to_string(), "the trait is declared in the same file");
    let trait_name = byte_offset(src, "trait Foo") + "trait ".len();
    assert_eq!((start, end), (trait_name, trait_name + "Foo".len()),
        "must target the `Foo` name token of `trait Foo`, not the impl itself");

    // Click on the same name at the trait declaration → itself (defining occurrence).
    let (def_uri2, start2, end2) = goto_full(&b, &uri, trait_name)
        .expect("click on the trait declaration's name resolves to itself");
    assert_eq!(def_uri2, uri.to_string());
    assert_eq!((start2, end2), (trait_name, trait_name + "Foo".len()));
}

#[test]
fn goto_impl_method_jumps_to_trait_method_decl() {
    let b = setup();
    let uri = Url::parse("file:///trait_impl.typort").unwrap();
    let src = "\
trait Foo {
    def m: Nat
}
impl Foo for Nat {
    def m: Nat = 1
}
";
    b.process_file(&uri, src, Some(1));

    // Click on the method name `m` in the impl body → the trait's `def m`.
    let impl_def = byte_offset(src, "def m: Nat = 1") + "def ".len();
    let (def_uri, start, end) = goto_full(&b, &uri, impl_def)
        .expect("click on an impl method name must resolve to a definition");
    assert_eq!(def_uri, uri.to_string(), "the trait is declared in the same file");
    let trait_def = byte_offset(src, "def m: Nat\n") + "def ".len();
    assert_eq!((start, end), (trait_def, trait_def + 1),
        "must target the `m` name token of the trait's `def m` declaration");
}

#[test]
fn goto_impl_header_type_name_still_resolves_to_type_decl() {
    // Regression guard for the impl-instance registration: the synthetic
    // instance name must not claim any token of the impl header, so the
    // `for`-target type name keeps resolving to its own declaration.
    let b = setup();
    let uri = Url::parse("file:///trait_impl.typort").unwrap();
    let src = "\
trait Foo {
    def m: Nat
}
impl Foo for Nat {
    def m: Nat = 1
}
";
    b.process_file(&uri, src, Some(1));

    let nat_off = byte_offset(src, "impl Foo for Nat") + "impl Foo for ".len();
    let (def_uri, start, end) = goto_full(&b, &uri, nat_off)
        .expect("click on the impl's `for`-target type name must resolve to a definition");
    assert_eq!(def_uri, "builtin:///nat.typort",
        "`Nat` resolves to its prelude declaration");
    let nat_src = include_str!("../src/prelude/core/nat.typort");
    let def = nat_src.find("enum Nat").expect("Nat enum in prelude");
    let exp_start = def + "enum ".len();
    assert_eq!((start, end), (exp_start, exp_start + "Nat".len()),
        "must target the `Nat` name token of the enum declaration");
}

#[test]
fn goto_impl_header_trait_name_cross_file_prelude() {
    // Real usage from examples/hdl/10-bundle.typort: `impl IMasterSlave for
    // AxiLite` — the trait is declared in the prelude's hdl-bus.typort, so
    // the target must land in the other file.
    let b = setup();
    let uri = Url::parse("file:///bundle.typort").unwrap();
    let src = "\
#[derive(Bundle)]
struct AxiLite {
    awaddr: UInt[8]
}

impl IMasterSlave for AxiLite {
    def asMaster: AxiLite =
        let _ = in(this.awaddr);
        this
}
";
    b.process_file(&uri, src, Some(1));

    let ms_off = byte_offset(src, "impl IMasterSlave") + "impl ".len();
    let (def_uri, start, end) = goto_full(&b, &uri, ms_off)
        .expect("click on the impl header's typeclass name must resolve to a definition");
    assert_eq!(def_uri, "builtin:///hdl-bus.typort",
        "IMasterSlave is declared in the prelude's hdl-bus.typort");
    let bus_src = include_str!("../src/prelude/hdl/hdl-bus.typort");
    let def = bus_src.find("trait IMasterSlave").expect("trait decl in prelude");
    let exp_start = def + "trait ".len();
    assert_eq!((start, end), (exp_start, exp_start + "IMasterSlave".len()),
        "must target the `IMasterSlave` name token of `trait IMasterSlave`");
}

#[test]
fn goto_impl_derived_method_jumps_to_trait_method_decl() {
    // `impl IMasterSlave for TriBus` on a `#[derive(Bundle)]` struct: the
    // user's `def asMaster` direction spec is replaced at parse time by
    // generated methods — but the user's name token must still resolve to
    // the trait's `def asMaster` declaration (cross-file into hdl-bus.typort).
    let b = setup();
    let uri = Url::parse("file:///bundle.typort").unwrap();
    let src = "\
#[derive(Bundle)]
struct TriBus {
    data: UInt[8]
}

impl IMasterSlave for TriBus {
    def asMaster: TriBus =
        let _ = inout(this.data);
        this
}
";
    b.process_file(&uri, src, Some(1));

    let asm_off = byte_offset(src, "def asMaster") + "def ".len();
    let (def_uri, start, end) = goto_full(&b, &uri, asm_off)
        .expect("click on the impl method name must resolve to a definition");
    assert_eq!(def_uri, "builtin:///hdl-bus.typort",
        "asMaster is declared in the prelude's hdl-bus.typort");
    let bus_src = include_str!("../src/prelude/hdl/hdl-bus.typort");
    let def = bus_src.find("def asMaster[bn: BindingName]").expect("asMaster in trait decl");
    let exp_start = def + "def ".len();
    assert_eq!((start, end), (exp_start, exp_start + "asMaster".len()),
        "must target the `asMaster` name token of the trait's `def asMaster`");
}
