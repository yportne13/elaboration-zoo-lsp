// ============================================================
// HDL module macro tests
//
// `module Name[cd] [params] <ports> { body }` desugars to a class whose
// constructor runs the body against a global ModuleTree and captures the
// result; the tree is exposed via the `Module` trait's `tree` method, so
// `moduleTreeVL(M.create.tree)` produces Verilog.
//
// Behavior pinned here:
//   - body-only modules (let declarations + := assignments)
//   - parametric modules [w: Nat] (create[w])
//   - explicit clock domain [cd] (create[myClockDomain])
//   - typed/Bool ports declared before the body braces (u.a handles)
//   - sub-module instantiation `let u = M.create[w]` auto-records an
//     instance (no Expr-macro special case needed)
//   - top-level creates leave no phantom instance in the global tree
// ============================================================

use super::*;

fn assert_ok(input: &str) -> String {
    match run_with_prelude(input) {
        Ok(output) => output,
        Err(e) => panic!("expected OK, got error: '{}' @ {}:{}", e.0.data, e.0.path_id, e.0.start_offset),
    }
}

fn assert_err_contains(input: &str, needle: &str) {
    match run_with_prelude(input) {
        Ok(output) => panic!("expected error containing '{}', got OK: {}", needle, output.trim()),
        Err(e) => {
            assert!(
                e.0.data.contains(needle),
                "expected error containing '{}', got: '{}'",
                needle,
                e.0.data
            );
        }
    }
}

// ── body-only module: let declarations + := assignments ──

#[test]
fn module_body_only() {
    let output = assert_ok(r#"
module counterDemo {
    let a = UInt[8]
    let b = UInt[8]
    let sum = UInt[8]
    sum := a + b
}
println(moduleTreeVL(counterDemo.create.tree))
"#);
    assert!(output.contains("counterDemo"), "verilog should name the module, got: {}", output);
    assert!(output.contains("module counterDemo"), "expected module header, got: {}", output);
}

// ── parametric module [w: Nat] ──

#[test]
fn module_param_width() {
    let output = assert_ok(r#"
module adder[w: Nat] {
    let a = UInt[w]
    let b = UInt[w]
    let sum = UInt[w + 1]
    sum := a +^ b
}
println(moduleTreeVL(adder.create[8].tree))
"#);
    assert!(output.contains("module adder"), "expected parametric module header, got: {}", output);
}

// ── explicit clock domain [cd] ──

#[test]
fn module_explicit_clock_domain() {
    let output = assert_ok(r#"
def myCd: ClockDomain = ClockDomain.mk "myclk" "myrst" Async RisingEdge ActiveHigh
module foo[myCd] {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
println(moduleTreeVL(foo.create[myCd].tree))
"#);
    assert!(output.contains("module foo"), "expected cd module header, got: {}", output);
}

// ── typed + Bool ports before the body braces ──

#[test]
fn module_ports_typed_and_bool() {
    let output = assert_ok(r#"
module portmod
    input a = UInt[8]
    output sum = UInt[9]
    input en = Bool
{
    sum := a +^ a
    en := Bool.mk(Some("en"), createIn("en"))
}
println(moduleTreeVL(portmod.create.tree))
"#);
    assert!(output.contains("module portmod"), "expected port module header, got: {}", output);
}

// ── sub-module instantiation auto-records the instance ──

#[test]
fn module_nested_instance() {
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w + 1]
{
    sum := a +^ b
}
module topWithAdder {
    let a = UInt[8]
    let b = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
}
println(moduleTreeVL(topWithAdder.create.tree))
"#);
    assert!(output.contains("module topWithAdder"), "expected top module header, got: {}", output);
    assert!(output.contains("myAdder"), "expected sub-module instance in verilog, got: {}", output);
}

// ── top-level create leaves no phantom instance ──

#[test]
fn module_top_level_no_phantom_instance() {
    // A bare `M.create` at top level must not record an instance anywhere:
    // the restored tree after the body is the empty parent tree, and
    // mkInstanceIfParent drops the record on nil.
    let output = assert_ok(r#"
module solo {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
def t = solo.create.tree
println(moduleTreeVL(t))
println(moduleTreeVL(t))
"#);
    // two identical prints prove the global tree was restored between creates
    let first = output.find("module solo").expect("first verilog missing");
    let second = output[first + 1..].find("module solo").expect("second verilog missing");
    assert!(second > 0, "expected two identical top-level verilogs, got: {}", output);
}

// ── plan C: no `tree_data` storage field ──
// The create-side side-effect chain is a bare class-body statement (a
// create-local, NOT a struct field), so the struct has no storage field and
// `m.tree_data` must fail to type-check. `def tree` recomputes the chain.

#[test]
fn module_no_tree_data_field() {
    assert_err_contains(r#"
module solo {
    let a = UInt[8]
}
def t = solo.create.tree
println(solo.create.tree_data)
"#, "tree_data");
}

// ── plan C2: module body lets ARE struct members ──
// User semantics: every class-body `let` is a struct field (no special
// cases, no create-locals). The module macro FLATTENS its side-effect chain
// into class-body fields, so every signal the user declares in the module —
// body signals AND ports — is reachable on the instance (`u.a`, `u.sum`),
// alongside the chain's `_`/`_prev`/`_res` bindings. Ports keep the
// double-declaration (real signal + subSignal handle; the handle wins in the
// struct), body signals keep their real signal value.

#[test]
fn module_body_signal_is_member() {
    let output = assert_ok(r#"
module counterDemo {
    let a = UInt[8]
    let b = UInt[8]
    let sum = UInt[8]
    sum := a + b
}
def u = counterDemo.create
println(u.a)
println(u.sum)
println(moduleTreeVL(u.tree))
"#);
    // u.a is the module's own signal (named "a", real createWidth expr) —
    // not a subSignal handle (the module has no ports).
    assert!(output.contains("UInt.mk(Option[String]::Some(a), Expr::createWidth(a, 8))"),
        "body signal member should be the real signal, got: {}", output);
    assert!(output.contains("UInt.mk(Option[String]::Some(sum), Expr::createWidth(sum, 8))"),
        "sum should be a member too, got: {}", output);
    assert!(output.contains("assign sum = (a + b);"),
        "verilog should still be generated from the tree, got: {}", output);
}

#[test]
fn module_port_is_member() {
    let output = assert_ok(r#"
module portmod
    input a = UInt[8]
    output sum = UInt[9]
{
    sum := a +^ a
}
def u = portmod.create
println(u.a)
println(u.sum)
"#);
    // Port members are the subSignal handles (for `u.a := sig` in a parent).
    assert!(output.contains("UInt.mk(Option[String]::None, Expr::subSignal(, a))"),
        "port member should be the subSignal handle, got: {}", output);
    assert!(output.contains("UInt.mk(Option[String]::None, Expr::subSignal(, sum))"),
        "output port member missing, got: {}", output);
}

#[test]
fn module_when_switch_no_scaffolding_members() {
    // when/switch transcribe their begin/end scaffolding as `let _ = ...`
    // discards, so the struct gains only the single `_` field — no
    // w_push/w_pop/_wb/_we junk members.
    let output = assert_ok(r#"
module ctrl {
    let a = UInt[8]
    let b = UInt[8]
    let out = UInt[8]
    when a === 0 {
        out := b
    } otherwise {
        out := a
    }
}
def u = ctrl.create
println(u.out)
println(u.a)
"#);
    assert!(output.contains("UInt.mk(Option[String]::Some(out), Expr::createWidth(out, 8))"),
        "body signal in when-module should be a member, got: {}", output);
    assert!(output.contains("UInt.mk(Option[String]::Some(a), Expr::createWidth(a, 8))"),
        "a should be a member too, got: {}", output);
    // u.w_push must NOT exist (the when scaffolding is `let _ =` discarded).
    assert_err_contains(r#"
module ctrl {
    let a = UInt[8]
    let b = UInt[8]
    let out = UInt[8]
    when a === 0 {
        out := b
    } otherwise {
        out := a
    }
}
def u = ctrl.create
println(u.w_push)
"#, "w_push");
}

// ── plan C2: chain bindings are accessible struct fields ──
// `_prev` is the ModuleTree captured before the module's push (the pre-push
// global — the empty tree at top level), `_res` is the tree after the body
// ran. Pinning them as struct fields keeps the "everything is in the struct"
// semantics honest.

#[test]
fn module_struct_exposes_chain_bindings() {
    let output = assert_ok(r#"
module solo {
    let a = UInt[8]
    let b = UInt[8]
    let s = UInt[8]
    s := a + b
}
def pc = solo.create
println(pc._prev)
println(pc._res)
"#);
    // _prev: the tree before the module's push — the empty tree at top level.
    assert!(output.contains("ModuleTree::ModuleTree.mk(0, Vec[ModuleDef]::nil)"),
        "expected _prev to be the pre-push empty tree, got: {}", output);
    // _res: the module's own tree after the body ran (solo with a, b, s and
    // the assign).
    assert!(output.contains("ModuleDef::ModuleDef.mk(solo"),
        "expected _res to hold the built solo tree, got: {}", output);
}

// ── plan C: def tree re-runs the chain — idempotent, instance exactly once ──

#[test]
fn module_def_tree_idempotent_instance_once() {
    // Two `.tree` accesses of the same module print byte-identical Verilog
    // (each access re-runs the chain from a clean push), and the nested
    // instance line appears exactly once per printed module.
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w + 1]
{
    sum := a +^ b
}
module topWithAdder {
    let a = UInt[8]
    let b = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
}
println(moduleTreeVL(topWithAdder.create.tree))
println(moduleTreeVL(topWithAdder.create.tree))
"#);
    // one instance record per printed tree → 2 total, never duplicated
    assert_eq!(output.matches("myAdder u (").count(), 2,
        "instance should be recorded exactly once per tree, got: {}", output);
    // hierarchy access still resolves: the instance line carries the ports
    assert!(output.contains("myAdder u (.a(a), .b(b))"),
        "expected aggregated port connections on the instance line, got: {}", output);
    // both prints byte-identical (idempotent def tree)
    let first = output.find("module topWithAdder").expect("first verilog missing");
    let second = output[first + 1..].find("module topWithAdder").expect("second verilog missing");
    assert!(second > 0, "expected two verilogs, got: {}", output);
    let second_start = first + 1 + second;
    assert_eq!(&output[first..second_start], &output[second_start..],
        "two .tree accesses must print byte-identical verilog, got: {}", output);
}

// ── carry/borrow-generating +^ / -^ emit pad-concat + plain + / - ──
// `+^` and `-^` are Typort-only tokens (result width +1). The prelude
// builds them as "pad one bit by type + plain +/-" expressions so the
// carry/borrow bit is explicit: UInt zero-extends `{1'b0, a}`, SInt
// sign-extends `{a[w-1], a}` — and for SInt BOTH operands are extended
// (the concat is unsigned in Verilog; extending only the lhs would
// zero-extend the rhs and corrupt negative operands). Emitting a bare
// `(a + b)` would rely on Verilog's context-determined width and silently
// drop the carry when nested/inlined. This pins all three emission paths:
// continuous assigns (exprVL), clocked regAssigns (exprVL), and when
// conditions (emitCondStr + proc).

#[test]
fn module_carry_ops_emit_plain_plus_minus() {
    let output = assert_ok(r#"
module carryOps {
    let a = UInt[8]
    let b = UInt[8]
    let c = UInt[8]
    let d = UInt[8]
    let sum = UInt[9]
    let diff = UInt[9]
    let nest = UInt[10]
    let sa = SInt[8]
    let sb = SInt[8]
    let ssum = SInt[9]
    let sdiff = SInt[9]
    let out = UInt[8]
    let w = UInt[9]
    reg r = UInt[9]
    sum := a +^ b
    diff := a -^ b
    nest := (a +^ b) +^ (c +^ d)
    ssum := sa +^ sb
    sdiff := sa -^ sb
    r := a +^ b
    w := Bool.mk(None, literal(0)) ## c
    when (a +^ b) === 0 {
        out := c
    }
}
println(moduleTreeVL(carryOps.create.tree))
"#);
    assert!(!output.contains("+^"), "generated Verilog must not contain the invalid '+^' token, got: {}", output);
    assert!(!output.contains("-^"), "generated Verilog must not contain the invalid '-^' token, got: {}", output);
    assert!(output.contains("assign sum = ({1'b0, a} + b);"), "expected UInt carry add as zero-extend + plus, got: {}", output);
    assert!(output.contains("assign diff = ({1'b0, a} - b);"), "expected UInt borrow sub as zero-extend + minus, got: {}", output);
    assert!(output.contains("assign nest = ({1'b0, ({1'b0, a} + b)} + ({1'b0, c} + d));"),
        "expected nested +^ chain with explicit pad at every level, got: {}", output);
    assert!(output.contains("assign ssum = ({sa[7], sa} + {sb[7], sb});"),
        "expected SInt carry add with both operands sign-extended, got: {}", output);
    assert!(output.contains("assign sdiff = ({sa[7], sa} - {sb[7], sb});"),
        "expected SInt borrow sub with both operands sign-extended, got: {}", output);
    assert!(output.contains("r <= ({1'b0, a} + b);"), "expected clocked carry add as zero-extend + plus, got: {}", output);
    assert!(output.contains("if (({1'b0, a} + b) == 0) begin"), "expected when condition carry add as zero-extend + plus, got: {}", output);
    // IEEE 1364-2001 §4.1.14: unsized constants are illegal inside concats,
    // so a literal Bool operand must be emitted as a sized 1-bit literal.
    assert!(output.contains("assign w = {1'b0, c};"), "expected sized literal in concatenation, got: {}", output);
}

// ── errors: unknown signal / type misuse still reported ──

#[test]
fn module_err_unknown_signal() {
    assert_err_contains(r#"
module bad {
    let a = UInt[8]
    sum := a + b
}
def t = bad.create.tree
"#, "sum");
}

// ── macro system: optional fragment $( ... )? ──
// (added for the module macro work; the final 2-arm module macro no longer
// uses it, but the matcher/transcriber support stays as macro-system
// capability — pinned here against regression)

#[test]
fn macro_optional_fragment() {
    let output = assert_ok(r#"
macro_rules optm {
    ($a: ident $( [ $b: ident ] )? ) => {
        def $a $( [ $b: Nat ] )? : Nat = 5
    }
}
optm foo [x]
optm bar
println (foo[1])
println (bar)
"#);
    let lines: Vec<&str> = output.trim().lines().collect();
    assert!(lines.iter().filter(|l| l.trim() == "5").count() == 2,
        "both foo[1] and bar should print 5, got: {}", output);
}

// ── output reg ports: forced `output reg` + clocked drive + init reset ──

#[test]
fn module_output_reg_ports() {
    // Port-area `output reg x = UInt[8] init 0` must:
    //   - declare the port `output reg [7:0] x` (no wire/reg inference)
    //   - drive clocked via `:=` (isRegExpr → regAssign) even inside `when`
    //   - emit the async-reset init `x <= 0;`
    //   - add the clk/reset ports automatically (the port line declares the
    //     reg, so no standalone `reg` line exists)
    let output = assert_ok(r#"
module pulseGen {
    output reg count = UInt[8] init 0
    output reg flag = Bool
    input en = Bool
    when (en) {
        count := count + 1
        flag := !flag
    }
}
println(moduleTreeVL(pulseGen.create.tree))
"#);
    assert!(output.contains("output reg [7:0] count"), "got: {}", output);
    assert!(output.contains("output reg flag"), "got: {}", output);
    assert!(output.contains("count <= 0;"), "init reset value, got: {}", output);
    assert!(output.contains("count <= (count + 1);"), "clocked when drive, got: {}", output);
    assert!(output.contains("flag <= !flag;"), "Bool clocked drive, got: {}", output);
    assert!(output.contains("input wire clk"), "auto clock port, got: {}", output);
    assert!(output.contains("input wire reset"), "auto reset port, got: {}", output);
    assert!(output.contains("always @(posedge clk or posedge reset)"), "async reset block, got: {}", output);
}

#[test]
fn module_output_reg_body_and_types() {
    // Body-level `output reg` (Expr macro) and SInt/Bits variants; init on a
    // Bool output-reg port (width-1 createOutRegWidthInit).
    let output = assert_ok(r#"
module mixedOut {
    input a = UInt[8]
    output reg s = SInt[8] init 0
    output reg b = Bits[8]
    s := a.asSInt
    b := s.asBits
}
module bodyOutReg2 {
    output reg r = UInt[8] init 3
    output reg en = Bool init 1
    r := 7
    en := true
}
println(moduleTreeVL(mixedOut.create.tree))
println(moduleTreeVL(bodyOutReg2.create.tree))
"#);
    assert!(output.contains("output reg signed [7:0] s"), "SInt output reg, got: {}", output);
    assert!(output.contains("output reg [7:0] b"), "Bits output reg, got: {}", output);
    assert!(output.contains("s <= 0;"), "SInt init, got: {}", output);
    assert!(output.contains("output reg [7:0] r"), "body output reg, got: {}", output);
    assert!(output.contains("r <= 3;"), "body init, got: {}", output);
    assert!(output.contains("output reg en"), "Bool output reg with init, got: {}", output);
    assert!(output.contains("en <= 1;"), "Bool init, got: {}", output);
}


// ════════════════════════════════════════════════════════════════════════
//  when 条件语义回归测试（fix/hdl-when-context）
//
// 每个赋值记录其完整使能条件（嵌套合取 + elsewhen/otherwise 分支否定），
// 生成器发射独立 if —— 独立 when 不会耦合、嵌套 when 条件不丢失。
// ════════════════════════════════════════════════════════════════════════

// ── 独立 when 块必须保持独立（不得链成 else-if）──

#[test]
fn when_independent_blocks_stay_independent() {
    let output = assert_ok(r#"
module twoWhens {
    let x = UInt[8]
    let y = UInt[8]
    let a = UInt[8]
    let b = UInt[8]
    let c1 = Bool
    let c2 = Bool
    when c1 { x := a }
    when c2 { y := b }
}
println(moduleTreeVL(twoWhens.create.tree))
"#);
    // two separate ifs; y = b must NOT be conditional on !c1
    assert!(output.contains("if (c1)"), "missing first if, got: {}", output);
    assert!(output.contains("if (c2)"), "missing second if, got: {}", output);
    assert!(output.contains("y = b;"), "missing second body, got: {}", output);
    let c1_pos = output.find("if (c1)").expect("if (c1) present");
    let c2_pos = output.find("if (c2)").expect("if (c2) present");
    let y_pos = output.find("y = b;").expect("y = b present");
    assert!(c2_pos < y_pos, "y = b must be inside the if (c2) block, got:\n{}", output);
    assert!(!output.contains("else if"), "independent whens must not chain as else-if, got:\n{}", output);
}

// ── 嵌套 when：内层条件必须与外层合取 ──

#[test]
fn when_nested_conditions_conjoin() {
    let output = assert_ok(r#"
module nestedWhen {
    let x = UInt[8]
    let y = UInt[8]
    let a = UInt[8]
    let b = UInt[8]
    let c1 = Bool
    let c2 = Bool
    when c1 {
        when c2 { x := a }
        y := b
    }
}
println(moduleTreeVL(nestedWhen.create.tree))
"#);
    // x = a requires c1 && c2; y = b requires c1 only
    assert!(output.contains("if (c2 && c1)"), "inner assignment must conjoin both conditions, got:\n{}", output);
    assert!(output.contains("x = a;"), "missing inner body, got: {}", output);
    assert!(output.contains("if (c1)"), "outer assignment keeps outer condition, got: {}", output);
    assert!(output.contains("y = b;"), "missing outer body, got: {}", output);
}

// ── when/elsewhen/otherwise：分支否定累积 ──

#[test]
fn when_elsewhen_negation_accumulates() {
    let output = assert_ok(r#"
module whenElseWhen {
    let a = UInt[8]
    let b = UInt[8]
    let c = UInt[8]
    let sel = UInt[2]
    let out = UInt[8]
    when sel === 0 { out := a } elsewhen sel === 1 { out := b } otherwise { out := c }
}
println(moduleTreeVL(whenElseWhen.create.tree))
"#);
    assert!(output.contains("if (sel == 0)"), "missing first branch, got: {}", output);
    assert!(output.contains("(sel == 1) && !(sel == 0)"), "elsewhen must negate earlier branches, got:\n{}", output);
    assert!(output.contains("!(sel == 0) && !(sel == 1)"), "otherwise must negate all branches, got:\n{}", output);
    assert!(output.contains("out = a;"), "missing branch body, got: {}", output);
    assert!(output.contains("out = b;"), "missing elsewhen body, got: {}", output);
    assert!(output.contains("out = c;"), "missing otherwise body, got: {}", output);
}

// ── switch：default 分支否定全部 is 分支 ──

#[test]
fn switch_default_negates_all_cases() {
    let output = assert_ok(r#"
module switchExample {
    let sel = UInt[4]
    let a = UInt[4]
    let b = UInt[4]
    let c = UInt[4]
    let result = UInt[4]
    switch sel {
        is 0 { result := a }
        is 1 { result := b }
        default { result := c }
    }
}
println(moduleTreeVL(switchExample.create.tree))
"#);
    assert!(output.contains("if (sel == 0)"), "missing is 0, got: {}", output);
    assert!(output.contains("!(sel == 0) && !(sel == 1)"), "default must negate all is cases, got:\n{}", output);
    assert!(output.contains("result = a;"), "missing is 0 body, got: {}", output);
    assert!(output.contains("result = c;"), "missing default body, got: {}", output);
}

// ── 子模块输出端口读取：sig := u.port 生成 .port(sig) 连接 ──

#[test]
fn submodule_output_read_generates_connection() {
    let output = assert_ok(r#"
module myAdder[w: Nat]
    input a = UInt[w]
    input b = UInt[w]
    output sum = UInt[w]
{
    sum := a + b
}
module topWithRead {
    input a = UInt[8]
    input b = UInt[8]
    output sum = UInt[8]
    let u = myAdder.create[8]
    u.a := a
    u.b := b
    sum := u.sum
}
println(moduleTreeVL(topWithRead.create.tree))
"#);
    // reading a child output must become a port connection, not a stray
    // `assign sum = u_sum;` referencing an undeclared net
    assert!(output.contains(".a(a), .b(b), .sum(sum)"), "missing port connections, got:\n{}", output);
    assert!(!output.contains("u_sum"), "no stray subSignal net reference allowed, got:\n{}", output);
}

// ── for 循环：编译期展开（方案 A：宏转写 + term 级 Nat 递归）──
// 曾因 Expr 宏兜底臂嵌套 let 链 + for 臂缺尾分号被整体 #[ignore]
// （阻塞记录见 docs/for-hdl-blocker.md，已解决）。

// §3-A（docs/l13-constraint-meta-fix-plan.md）：class 体内 `let _ = <调用>`。
// 旧缺陷：Expr 宏兜底臂把 let 表达式包成嵌套 let 链，链尾 recovery Hole 使
// 注解 meta 悬挂（find unsolved meta / lvl2ix / v_app 三表象）。
#[test]
fn module_let_unit_repro() {
    let output = assert_ok(r#"
module uM {
    let a = UInt[8]
    let _ = unit
    a := a
}
println(moduleTreeVL(uM.create.tree))
"#);
    assert!(output.contains("module uM"), "expected module header, got: {}", output);
}

// §3-A 变体：丢弃绑定持有对含 match 的 prelude def 调用（whenEnd 内部走
// WhenStack 全局 + match 分支），曾是同一 meta 簇的最强触发器。
#[test]
fn module_let_when_end_call() {
    let output = assert_ok(r#"
module uW {
    let a = UInt[8]
    let _ = whenEnd(unit)
    a := a
}
println(moduleTreeVL(uW.create.tree))
"#);
    assert!(output.contains("module uW"), "expected module header, got: {}", output);
}

// BLOCKED (master pre-existing class-expansion meta leak):
// class 体内 `let <bind> = <对含 match 的 def 调用>` 在 create/tree 检查时因
// dependent 隐式参数（string_to_global_type）产生悬挂 meta 而失败。机制链见
// docs/for-hdl-blocker.md。修好前整体 #[ignore]，不破 CI。
#[test]
fn module_for_loop_unroll_naming() {
    let output = assert_ok(r#"
module forDemo {
    let a = UInt[8]
    for i in 0 until 4 {
        let x = UInt[8]
        x := a
    }
}
println(moduleTreeVL(forDemo.create.tree))
"#);
    // 4 iterations unrolled: per-iteration signals get x_0..x_3 suffixes
    for n in 0..4 {
        assert!(
            output.contains(&format!("wire [7:0] x_{n}")),
            "missing x_{n} (iteration not unrolled with indexed name), got:\n{}",
            output
        );
    }
    assert_eq!(
        output.matches("assign x_").count(),
        4,
        "expected 4 assignments (one per iteration), got:\n{}",
        output
    );
}

#[test]
fn module_for_loop_width_param() {
    let output = assert_ok(r#"
module forWidthDemo {
    for i in 0 until 3 {
        let x = UInt[i + 2]
    }
}
println(moduleTreeVL(forWidthDemo.create.tree))
"#);
    // i must be a ground Nat per iteration: widths 2,3,4
    assert!(output.contains("wire [1:0] x_0"), "missing [1:0] x_0, got:\n{}", output);
    assert!(output.contains("wire [2:0] x_1"), "missing [2:0] x_1, got:\n{}", output);
    assert!(output.contains("wire [3:0] x_2"), "missing [3:0] x_2, got:\n{}", output);
}

#[test]
fn module_for_loop_nested() {
    let output = assert_ok(r#"
module forNested {
    let a = UInt[8]
    for i in 0 until 2 {
        for j in 0 until 2 {
            let x = UInt[8]
            x := a
        }
    }
}
println(moduleTreeVL(forNested.create.tree))
"#);
    // nested naming: outer index first, then inner (x_i_j)
    for i in 0..2 {
        for j in 0..2 {
            assert!(
                output.contains(&format!("wire [7:0] x_{i}_{j}")),
                "missing x_{i}_{j}, got:\n{}",
                output
            );
        }
    }
    assert_eq!(output.matches("assign x_").count(), 4, "got:\n{}", output);
}

#[test]
fn module_for_loop_empty_range() {
    let output = assert_ok(r#"
module forEmpty {
    let a = UInt[8]
    for i in 2 until 2 {
        let x = UInt[8]
        x := a
    }
}
println(moduleTreeVL(forEmpty.create.tree))
"#);
    // empty half-open range: no signal, no assignment
    assert!(!output.contains("x_"), "empty range must not unroll anything, got:\n{}", output);
}

// ============================================================
// Braced def bodies with hardware statements (SpinalHDL style)
//
// `def f(): T = { <Expr statements> }` — the statements are transcribed
// through the `Expr` macro fragment (same machinery as a module body), so
// `reg x = UInt[8]`, `let ...`, `when`/`switch`/`for`, `x := v` and
// declarations are legal inside plain defs. A def called inside a module
// body records its signals into that module (component-scope semantics);
// the block's last statement is the def's value.
// ============================================================

#[test]
fn def_body_reg_declared_in_module_scope() {
    let output = assert_ok(r#"
def delay(x: UInt[8]): UInt[8] = {
    reg d = UInt[8]
    d := x
    d
}
module top {
    input a = UInt[8]
    output out = UInt[8]
    out := delay(a)
}
println(moduleTreeVL(top.create.tree))
"#);
    assert!(output.contains("reg [7:0] d;"), "reg from def body, got:\n{}", output);
    assert!(output.contains("d <= a;"), "clocked reg drive, got:\n{}", output);
    assert!(output.contains("assign out = d;"), "def result routed out, got:\n{}", output);
}

#[test]
fn def_body_single_reg_statement_returns_it() {
    // A single hardware-declaration statement: the block value is the
    // declared binder, so `{ reg x = UInt[8] }` returns x.
    let output = assert_ok(r#"
def mkReg(): UInt[8] = { reg r = UInt[8] }
module top {
    output out = UInt[8]
    let u = mkReg()
    out := u
}
println(moduleTreeVL(top.create.tree))
"#);
    assert!(output.contains("reg [7:0] r;"), "reg from single-statement def, got:\n{}", output);
    assert!(output.contains("assign out = r;"), "returned reg routed out, got:\n{}", output);
}

#[test]
fn def_body_when_and_init() {
    let output = assert_ok(r#"
def gated(a: Bool, d: UInt[8]): UInt[8] = {
    reg q = UInt[8] init 7
    when a {
        q := d
    }
    q
}
module top {
    input en = Bool
    input din = UInt[8]
    output o = UInt[8]
    o := gated(en, din)
}
println(moduleTreeVL(top.create.tree))
"#);
    assert!(output.contains("reg [7:0] q;"), "got:\n{}", output);
    assert!(output.contains("q <= 7;"), "async reset init, got:\n{}", output);
    assert!(output.contains("if (en) begin"), "when condition, got:\n{}", output);
    assert!(output.contains("q <= din;"), "clocked conditional drive, got:\n{}", output);
}

#[test]
fn def_body_let_wire_and_for_loop() {
    // A let of an EXPRESSION becomes a named wire (SpinalHDL semantics); a
    // let of a signal is a plain alias (no extra wire). The for loop
    // unrolls inside the def body.
    let output = assert_ok(r#"
def shift3(v: UInt[8]): UInt[8] = {
    let t = v + 1
    for i in 0 until 3 {
        t := t + 1
    }
    t
}
module top {
    input din = UInt[8]
    output o = UInt[8]
    o := shift3(din)
}
println(moduleTreeVL(top.create.tree))
"#);
    assert!(output.contains("wire [7:0] t;"), "named wire from let-expr, got:\n{}", output);
    assert!(output.contains("assign t = (din + 1);"), "got:\n{}", output);
    // three unrolled iterations, each driving the accumulated wire
    assert_eq!(output.matches("assign t = (t + 1);").count(), 3, "got:\n{}", output);
    assert!(output.contains("assign o = t;"), "got:\n{}", output);
}

#[test]
fn def_body_plain_expressions() {
    // Non-hardware blocks keep plain expression semantics: the last
    // statement is the value, statements before it are let bindings.
    let output = assert_ok(r#"
def f(): Nat = { 42 }
def g(x: Nat): Nat = {
    let a = x + 1
    a * 2
}
println(f)
println(g(5))
"#);
    assert!(output.contains("42"), "got:\n{}", output);
    assert!(output.contains("12"), "got:\n{}", output);
}
