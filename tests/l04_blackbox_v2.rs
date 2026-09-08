//! L04_implicit 黑盒测试套件 · 第二卷（v2）。
//!
//! 与 `tests/l04_blackbox.rs`（第一卷）互补：第一卷钉住上游示例套件、隐式
//! 插入主干、命名隐式与错误主干；本卷面向**边缘与分支**：
//!   - 隐式插入的边界形态：显式/隐式实参交错、隐式 Pi 链的部分插入、
//!     洞对插入 binder 的捕获（`?m A B`）、隐式在 spine 头/尾、嵌套隐式
//!     λ、非 λ 项对多隐式 Π 的连续 inserted binder；
//!   - 求解分支：插入 meta 由实参类型求解的顺序（elab 逐条钉）、
//!     flex-flex 转发解（`λ x1. ?m x1`）、非 pattern spine 悬挂、
//!     meta 被解成 Π（check 侧）、混合 icit 的解显示（`λ {x1} x2.`）、
//!     η 与隐式插入的相互作用（comp 式 η 转发解 `λ x1 x2 x3 {x4} x5. …`）；
//!   - 「解后到值」时序：meta 先被应用进 spine、随后才被解的输入族
//!     （对照 L05 65269fb 修复的 β-redex 引读缺陷——同款链分解代码在
//!     L04 潜伏；5.4 万例差分扫描（含本卷语料）未在 L04 触发：无剪枝时
//!     meta 链实参个数恒等于其 bds 长度，解的 λ 数与链长一致，不存在
//!     「部分应用闭包」形态。本卷以 golden 钉住现行为）；
//!   - 错误路径与解析残缺：`[`/`{` 不闭、截断、`U U` 应用非函数、
//!     过度应用、多行/CRLF/Tab 的错误位置渲染、CJK 标识符、
//!     行注释到 EOF——不得 panic、不得挂死、位置合理；
//!   - parity 扫描：声明 × 实参组合语料参考版↔孪生版三模式逐字节比对，
//!     以及潜在慢输入的看门狗表征（不挂死套件）。
//!
//! 已核对为「按实现如此」并在此钉住的怪癖（解析器沿用 L05 已文档化的
//! 「不强制 EOF」口径，与上游 megaparsec `pSrc <* eof` 有差）：
//!   - 首项完整后尾随 token 被丢弃——`g {}`、`g {U = } U`、`U)`、`U 1 2`
//!     等输入的尾随垃圾静默丢弃（不报 parse error）；
//!   - 命名实参 `{U = }` 的 `=` 右侧残缺时整个实参连同 `{}` 一起被丢弃。
//!
//! 双 oracle 与第一卷相同：
//!   1. golden 输出串（上游 Main.hs 语义推导 + 实测核对，逐字节断言）；
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）三模式
//!      （nf/type/elab）逐字节互检。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L04_implicit/mod.rs"]
mod L04_implicit;

use L04_implicit::bump_spine_iter as fast;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L04_implicit::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L04_implicit::main_with("type", src)
}

fn elab(src: &str) -> String {
    L04_implicit::main_with("elab", src)
}

/// Oracle 2：参考版与性能版在全部三种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    for mode in ["nf", "type", "elab"] {
        let b = L04_implicit::main_with(mode, src);
        let f = fast::main_with(mode, src);
        assert_eq!(
            b, f,
            "{mode} 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        );
    }
}

/// 按 `display_error`（megaparsec 风格）的构造规则重建期望错误块。
fn render_err(line: usize, col: usize, src_line: &str, msg: &str) -> String {
    let lnum = line.to_string();
    let lpad = " ".repeat(lnum.len());
    format!(
        "(stdin):{line}:{col}:\n{lpad} |\n{lnum} | {src_line}\n{lpad} | {}^\n{msg}\n",
        " ".repeat(col - 1)
    )
}

/// 报错输出 = 重建的完整错误块（位置、pad 宽、caret 列逐字节）+ 双实现互检。
fn assert_err_block(src: &str, line: usize, col: usize, src_line: &str, msg: &str) {
    assert_eq!(ty(src), render_err(line, col, src_line, msg), "src:\n{src}");
    assert_parity(src);
}

/// 报错输出：以 `(stdin):{line}:{col}:` 开头且包含消息片段。
fn assert_error_at(src: &str, line: usize, col: usize, needle: &str) {
    let out = ty(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains(needle), "错误消息缺 {needle:?}：\n{out}");
    assert_parity(src);
}

/// nf 模式输出以 type 模式输出结尾。
fn assert_nf_embeds_type(src: &str) {
    let t = ty(src);
    assert!(
        nf(src).ends_with(&format!("  :\n{t}")),
        "nf 输出未以 type 模式输出结尾：\nsrc:\n{src}\ntype:\n{t}\nnf:\n{}",
        nf(src),
    );
}

/// 看门狗：在带超时的子线程里表征「可能挂死」的输入。超时则 panic 让测试
/// 失败（孤儿线程随进程退出回收），保证套件永不卡死。
fn assert_terminates_within(src: &str, secs: u64) {
    let s = src.to_string();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut outs = Vec::new();
            for mode in ["nf", "type", "elab"] {
                outs.push(L04_implicit::main_with(mode, &s));
                outs.push(fast::main_with(mode, &s));
            }
            let _ = tx.send(outs);
        })
        .expect("看门狗线程创建失败");
    match rx.recv_timeout(std::time::Duration::from_secs(secs)) {
        Ok(outs) => {
            // 顺带核对：六份输出两两成对一致（nf/type/elab × basic/fast）
            for pair in outs.chunks(2) {
                assert_eq!(pair[0], pair[1], "看门狗用例 parity 失败：\n{src}");
            }
        }
        Err(_) => panic!("输入在 {secs}s 内未终止（疑似挂死）：\n{src}"),
    }
}

/// 在指定栈大小的线程里跑（深度负载：参考版 eval/quote/pretty 全递归）。
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

const HELP: &str = "usage: elabzoo-implicit-args [--help|elab|nf|type]\n  --help : display this message\n  elab   : read & elaborate expression from stdin\n  nf     : read & typecheck expression from stdin, print its normal form and type\n  type   : read & typecheck expression from stdin, print its type\n";

// --------------------------------------------------------------------------------
// 一、隐式插入的边界形态
// --------------------------------------------------------------------------------

/// 显式/隐式实参交错：`{A} → U → {C} → U → U` 的裸引用不插入（顶层无
/// 应用），nf 保持 λ 形。
#[test]
fn implicit_explicit_interleave_in_type() {
    let src = "let f : {A : U} -> U -> {C : U} -> U -> U = \\{A} x {C} y. x;\nf\n";
    assert_eq!(
        nf(src),
        "λ {A} x {C} y. x\n  :\n{A : U} → U → {C : U} → U → U\n"
    );
    assert_eq!(elab(src), "\nlet f : {A : U} → U → {C : U} → U → U\n  = λ {A} x {C} y. x;\n\nf\n");
    assert_parity(src);
}

/// 隐式 Pi 链的部分插入：三个隐式全悬挂时逐个补 meta（?0/?1/?2），显式
/// 实参 U 只把应用推进到 `f {?0} {?1} {?2} U`。注意 {B : A -> U} 的 meta
// 无方程可解（U 的类型是 U 而非 A → U 的实例）——保持未解不报错。
#[test]
fn implicit_pi_chain_partial_insertion() {
    let src = "let f : {A : U}{B : A -> U}{C : U} -> U -> U = \\{A}{B}{C} x. x;\nf U\n";
    assert_eq!(elab(src), "let ?0 = ?;\nlet ?1 = ?;\nlet ?2 = ?;\n\n\
         let f : {A : U}{B : A → U}{C : U} → U → U\n  = λ {A} {B} {C} x. x;\n\nf {?0} {?1} {?2} U\n");
    assert_parity(src);
}

/// 洞捕获全部插入 binder：`λ {A} {B}. ?0 A B`——洞 meta 的 bds 与两层
/// inserted binder 平行，nf 以 spine 形态展开（外层 binder 先应用）。
#[test]
fn hole_captures_two_inserted_binders() {
    let src = "let f : {A : U}{B : U} -> U = \\{A}{B}. _;\nf\n";
    assert_eq!(nf(src), "λ {A} {B}. ?0 A B\n  :\n{A : U}{B : U} → U\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\nlet f : {A : U}{B : U} → U\n  = λ {A} {B}. ?0 A B;\n\nf\n"
    );
    assert_parity(src);
}

/// 嵌套隐式 λ 顶层推断：两层隐式 binder 的域洞按嵌套依赖显示
/// （`{A : ?0}{B : ?1 A}`——B 的域 meta 挂外层 A）。
#[test]
fn nested_implicit_lambdas_infer() {
    let src = "\\{A}. \\{B}. U\n";
    assert_eq!(ty(src), "{A : ?0}{B : ?1 A} → U\n");
    assert_eq!(elab(src), "let ?0 = ?;\nlet ?1 = ?;\n\nλ {A} {B}. U\n");
    assert_parity(src);
}

/// 隐式在 spine 头部：位置隐式实参直接给值，不产生插入 meta（elab 空
/// metacontext——与第一卷 explicit_implicit_arg_needs_no_insertion_meta
/// 互补，这里钉 spine 中段混合 `{U}` 与命名形态）。
#[test]
fn implicit_args_head_and_middle() {
    let src = "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {U} {B = U} U U\n";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. U;\n\n\
         let const : {A : ?0}{B : ?1 A} → A → B → A\n  = λ {A} {B} x y. x;\n\nconst {U} {U} U U\n"
    );
    assert_parity(src);
}

/// 隐式在 spine 尾部：`id {U}` 停在 `U → U`，不喂显式实参就不插 meta。
#[test]
fn implicit_arg_tail_no_insertion() {
    let src = "let id : {A : U} -> A -> A = \\x. x;\nid {U}\n";
    assert_eq!(ty(src), "U → U\n");
    assert_eq!(nf(src), "λ x. x\n  :\nU → U\n");
    assert_parity(src);
}

/// 命名实参乱序：`f {B = U} {A = U}`——B 消化后类型已显式化，A 无处定位
/// → `No named implicit argument with name A`。
#[test]
fn named_args_swapped_error() {
    assert_err_block(
        "let f : {A B C : U} -> A -> B -> C -> A = \\a b c. a;\nf {B = U} {A = U} U U U\n",
        2,
        1,
        "f {B = U} {A = U} U U U",
        "No named implicit argument with name A",
    );
}

/// 显式实参之后再接命名实参：隐式前缀已在第一个显式实参处插完/给完，
/// `{C = U}` 找不到 → 报错位置 = spine 起点。
#[test]
fn named_arg_after_positional_error() {
    assert_err_block(
        "let f : {A B : U} -> A -> B -> A = \\a b. a;\nf U {C = U}\n",
        2,
        1,
        "f U {C = U}",
        "No named implicit argument with name C",
    );
}

/// 命名 λ `\{B = y}` 与多隐式 Π：首个隐式 A 由 inserted binder 补上，
/// 命名 binder 按名定位 B（本地名 y，pretty 防撞改 y'）。
#[test]
fn named_lambda_second_binder() {
    let src = "let f : {A B : U} -> A -> B -> A = \\{B = y} x y. x;\nf U U\n";
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = U;\n\n\
         let f : {A : U}{B : U} → A → B → A\n  = λ {A} {y} x y'. x;\n\nf {?0} {?1} U U\n"
    );
    assert_parity(src);
}

/// 非 λ 项检查到多隐式 Π：连续补两个 inserted binder（对源码名不可见），
/// nf 折叠出 `λ {A} {B} x y. x`。
#[test]
fn non_lambda_inserts_two_binders() {
    let src = "let f : {A : U}{B : U} -> A -> B -> A = \\x y. x;\nf\n";
    assert_eq!(
        nf(src),
        "λ {A} {B} x y. x\n  :\n{A : U}{B : U} → A → B → A\n"
    );
    assert_eq!(
        elab(src),
        "\nlet f : {A : U}{B : U} → A → B → A\n  = λ {A} {B} x y. x;\n\nf\n"
    );
    assert_parity(src);
}

/// 过度应用：`id U U`——`id U : U`（插入 meta 由实参类型解为 U），第二个
/// U 应用到 U → 合成 Π 与 U 失配。最小惊讶：与上游一致报 Cannot unify，
/// expected = 已应用的类型 U，inferred = 合成 Π。
#[test]
fn over_application_of_implicit_id() {
    assert_err_block(
        "let id : {A : U} -> A -> A = \\x. x;\nid U U\n",
        2,
        1,
        "id U U",
        "Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?1) → ?2 x",
    );
}

/// `U U`：宇宙不可应用——合成 Π 与 U 失配，位置 = spine 起点。
#[test]
fn apply_universe_error() {
    assert_err_block(
        "U U\n",
        1,
        1,
        "U U",
        "Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?0) → ?1 x",
    );
}

/// 裸隐式 λ 顶层推断免插：`\{A}. U` 的类型只有自身域洞，无插入 meta。
#[test]
fn bare_implicit_lambda_no_insertion() {
    let src = "\\{A}. U\n";
    assert_eq!(ty(src), "{A : ?0} → U\n");
    assert_eq!(elab(src), "let ?0 = ?;\n\nλ {A}. U\n");
    assert_parity(src);
}

// --------------------------------------------------------------------------------
// 二、求解：顺序、转发、悬挂、混合 icit
// --------------------------------------------------------------------------------

/// 插入 meta 的求解顺序：`p1 = id p0`、`p2 = id p1` 每层一个 meta，按
/// elaboration 顺序编号（?0 在 p1、?1 在 p2），各自解为 Nat。
#[test]
fn insertion_metas_solved_in_order() {
    let src = "\
let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
let id : {A : U} -> A -> A = \\x. x;\n\
let p0 : Nat = \\N s z. s (s z);\n\
let p1 : Nat = id p0;\n\
let p2 : Nat = id p1;\n\
p0\n";
    assert_eq!(
        elab(src),
        "let ?0 = (N : U) → (N → N) → N → N;\nlet ?1 = (N : U) → (N → N) → N → N;\n\n\
         let Nat : U\n  = (N : U) → (N → N) → N → N;\n\n\
         let id : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         let p0 : Nat\n  = λ N s z. s (s z);\n\n\
         let p1 : Nat\n  = id {?0} p0;\n\n\
         let p2 : Nat\n  = id {?1} p1;\n\n\
         p0\n"
    );
    assert_eq!(nf(src), "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n");
    assert_parity(src);
}

/// flex-flex 转发解：`m {a} a ≡ n {a} a` 同 spine 异 meta——`n` 被解成
/// 1-λ 转发（解体引用 ?m），?m 悬挂；随后 P 应用失配，错误块里两侧行
/// 为 `?0 a a` vs `?6 a`（插入 meta ?6 = λ x1. ?m?——保持现行为）。
#[test]
fn flex_flex_forwarding_solution() {
    let src = format!(
        "let Eq : {{A : U}} -> A -> A -> U = \\{{A}} x y. (P : A -> U) -> P x -> P y;\n\
         let refl : {{A : U}}{{x : A}} -> Eq {{A}} x x = \\ _ px. px;\n\
         let the : (A : U) -> A -> A = \\ _ x. x;\n\
         let m : {{A : U}} -> U -> U = _;\n\
         let n : {{A : U}} -> U -> U = _;\n\
         let t = \\ a. the (Eq (m {{a}} a) (n {{a}} a)) refl;\n\
         U\n"
    );
    let out = ty(&src);
    assert!(
        out.contains("Cannot unify expected type\n\n  (P : U → U) → P (?0 a a) → P (?1 a a)\n\nwith inferred type\n\n  (P : U → U) → P (?6 a) → P (?6 a)"),
        "{out}"
    );
    assert_error_at(&src, 6, 43, "Cannot unify expected type");
}

/// meta 被解成 Π：`let f : _ = \x. x;`——注解洞经 check 回落与 λ 的推断
/// 类型合一，`?0 := (x : U) → U`（域 meta ?1 由 `f U` 的实参解为 U）。
#[test]
fn meta_solved_to_pi() {
    let src = "let f : _ = \\x. x;\nf U\n";
    assert_eq!(
        elab(src),
        "let ?0 = (x : U) → U;\nlet ?1 = U;\n\nlet f : ?0\n  = λ x. x;\n\nf U\n"
    );
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_parity(src);
}

/// 非 pattern spine 悬挂（两名独立实参非全变量）：解不了但不报错。
/// `m {U} (g U)` 的 spine 含非变量实参，?0 保持 `?`。
#[test]
fn non_pattern_two_args_unsolved() {
    let src = "\
let g : U -> U = \\x. x;\n\
let m : {A : U} -> U -> U = _;\n\
let t = m {U} (g U);\n\
U\n";
    // 判定通过即可（m 的洞不闭合但方程不失败）；elab 钉住 meta 形态
    assert_eq!(ty(src), "U\n");
    let e = elab(src);
    assert!(e.contains("let m : {A : U} → U → U\n  = λ {A}. ?0 A;\n"), "{e}");
    assert!(e.contains("t : ?1 U (g U);\n") || e.contains("t :"), "{e}");
    assert_parity(src);
}

/// 混合 icit 的解显示：comp 的 η 转发（`h = comp` 对隐式 Π 逐层插
/// binder + 部分插入），最后一段解 `?13 = λ x1 x2 x3 {x4} x5. x3 {x4} x5`
/// ——λ 标签取应用序（第 4 槽隐式），β 不看 icit。
#[test]
fn mixed_icit_forward_solution_display() {
    let src = "\
let comp : {A}{B : A -> U}{C : {a} -> B a -> U}\n\
           (f : {a}(b : B a) -> C b)\n\
           (g : (a : A) -> B a)\n\
           (a : A)\n\
           -> C (g a)\n\
    = \\f g a. f (g a);\n\
let h : {A}{B : A -> U}{C : {a} -> B a -> U}\n\
           (f : {a}(b : B a) -> C b)\n\
           (g : (a : A) -> B a)\n\
           (a : A)\n\
           -> C (g a)\n\
  = comp;\n\
h\n";
    let e = elab(src);
    assert!(
        e.contains("let ?13 = λ x1 x2 x3 {x4} x5. x3 {x4} x5;\n"),
        "混合 icit 转发解显示不符：\n{e}"
    );
    assert!(
        e.contains("= λ {A} {B} {C}. comp {?11 A B C} {?12 A B C} {?13 A B C};\n"),
        "h 的部分插入形态不符：\n{e}"
    );
    assert_eq!(
        nf(src),
        "λ {A} {B} {C} f g a. f {a} (g a)\n  :\n\
         {A : U}{B : A → U}{C : {a : A} → B a → U}(f : {a : A}(b : B a) → C {a} b)(g : (a : A) → B a)(a : A) → C {a} (g a)\n"
    );
    assert_parity(src);
}

/// η 与插入的相互作用：中性 `g`（其类型带隐式 Π 前缀）检查到两层隐式
/// Π——先插两个 binder，体内 `g` infer 后再插两个 meta（挂 A、B），
/// 插入 meta 与外层同构方程 η-塌缩（恒真不解），保持未解 `?0/?1`。
#[test]
fn eta_through_two_implicit_pis() {
    let src = "\
let f : {A : U} -> A -> A = \\x. x;\n\
let g : {A : U}{B : U} -> U -> U = \\z. z;\n\
let k : {A : U}{B : U} -> U -> U = g;\n\
k\n";
    assert_eq!(
        elab(src),
        "let ?0 = ?;\nlet ?1 = ?;\n\n\
         let f : {A : U} → A → A\n  = λ {A} x. x;\n\n\
         let g : {A : U}{B : U} → U → U\n  = λ {A} {B} z. z;\n\n\
         let k : {A : U}{B : U} → U → U\n  = λ {A} {B}. g {?0 A B} {?1 A B};\n\nk\n"
    );
    assert_eq!(nf(src), "λ {A} {B} z. z\n  :\n{A : U}{B : U} → U → U\n");
    assert_parity(src);
}

/// 域洞的依赖显示：注解 `_ -> _` 的余域洞在 binder 之下 elaboration，
/// 显示为 `?1 _`（匿名 binder 名进 ns）；`f U` 把域 ?0 解为 U。
#[test]
fn annotation_hole_dependent_display() {
    let src = "let f : _ -> _ = \\x. x;\nf U\n";
    assert_eq!(
        elab(src),
        "let ?0 = U;\nlet ?1 = λ x1. U;\n\nlet f : ?0 → ?1 _\n  = λ x. x;\n\nf U\n"
    );
    assert_parity(src);
}

/// EX1 子集（church mul）：`mul ten ten` 的展开 + the/refl 的隐式全谱，
/// nf 只断言前后缀（church 100 展开太长），三模式 parity 全查。
#[test]
fn ex1_subset_mul_hundred() {
    let src = "\
let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
let mul : Nat -> Nat -> Nat = \\a b N s z. a _ (b _ s) z;\n\
let ten : Nat = \\N s z. s (s (s (s (s (s (s (s (s (s z)))))))));\n\
let hundred = mul ten ten;\n\
hundred\n";
    let out = nf(src);
    assert!(out.starts_with("λ N s z. s ("), "{out}");
    // church 100：99 层 `s (` 嵌套 + 最内层 `s z`
    assert_eq!(out.matches("s (").count(), 99, "{out}");
    assert!(out.contains("s z)"), "{out}");
    assert!(out.contains("(N : U) → (N → N) → N → N"), "{out}");
    assert_parity(src);
    assert_nf_embeds_type(src);
}

// --------------------------------------------------------------------------------
// 三、「解后到值」时序（L05 65269fb 同款代码在 L04 的现行为钉住）
// --------------------------------------------------------------------------------
//
// L05 的教训：meta 先被应用进 spine 值、随后才被解成多 λ 时，快版 quote
// 的链分解/二叉 fallback 会单独引读「函数部分」，停在部分应用的闭包上，
// 重拼 App 产出 β-redex。L04 的 bump_spine_iter 含同款链分解代码
// （潜伏，L05 修复提交明确标注跨章嫌疑）。与 L05 的差别：L04 无剪枝，
// 未解 meta 的链实参个数恒等于其 bds 长度，解的 λ 数又取自求解 spine
// 的长度，因此「链实参 < 解 λ 数」的部分应用形态不可达——5.4 万例
// 差分扫描（声明 × 实参组合 + 随机片段）未发现分歧。本组以 golden 钉住
// 现行为（无红ex、错误块逐字节），并加看门狗防挂死。

const EQ_PRELUDE: &str = "\
let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;\n\
let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;\n\
let the : (A : U) -> A -> A = \\ _ x. x;\n";

/// L05 最小复现在 L04 的直译：错误块里出现「陈旧 spine」形态
/// `?0 (?5 a b) b`（?5/?6 未解、转发解 ?8 = λ x1 x2. …），但**无红ex**
/// ——两版逐字节一致。
#[test]
fn stale_value_l05_repro_no_redex() {
    let src = format!(
        "{EQ_PRELUDE}let m1 : {{A : U}} -> U -> U = _;\n\
         let t = \\ a b. the (Eq (m1 b) (m1 a)) refl;\n\
         U\n"
    );
    let golden = render_err(
        5,
        39,
        "let t = \\ a b. the (Eq (m1 b) (m1 a)) refl;",
        "Cannot unify expected type\n\n  (P : U → U) → P (?0 (?5 a b) b) → P (?0 (?6 a b) a)\n\nwith inferred type\n\n  (P : U → U) → P (?8 a b) → P (?8 a b)",
    );
    assert_eq!(ty(&src), golden, "src:\n{src}");
    // infer 失败短路：三模式同形
    assert_eq!(elab(&src), golden);
    assert_eq!(nf(&src), golden);
    assert_parity(&src);
}

/// 同族镜像与阴性对照（显式 m1、`{a}` 给值），错误块干净、无红ex。
/// 例外：`\ z. m1 a z` 一侧经 η 渲染出 `(λ z. ?0 a z)`——这是**合法的
/// η 展开 λ**（中性在 λ 侧应用后整体渲染），不是 `(λ …) (…)` 红ex，
/// 单独断言其形态。
#[test]
fn stale_value_family_mirrors() {
    for (d, body) in [
        ("let m1 : {A : U} -> U -> U = _;", "\\ a b. the (Eq (m1 a) (m1 b)) refl"),
        ("let m1 : U -> U -> U = _;", "\\ a b. the (Eq (m1 a) (m1 b)) refl"),
        ("let m1 : {A : U} -> U -> U = _;", "\\ a b. the (Eq (m1 {a} b) (m1 a)) refl"),
        ("let m1 : {A : U} -> U -> U -> U = _;", "\\ a b. the (Eq (m1 a b) (m1 b a)) refl"),
    ] {
        let src = format!("{EQ_PRELUDE}{d}\nlet t = {body};\nU\n");
        let out = ty(&src);
        assert!(out.contains("Cannot unify"), "应失配：\n{out}");
        assert!(!out.contains("(λ"), "输出不得含 λ（红ex 嫌疑）：\n{out}");
        assert_parity(&src);
    }
    // η 形态（合法 λ 渲染）单独钉住
    let src = format!(
        "{EQ_PRELUDE}let m1 : (A : U) -> U -> U = _;\n\
         let t = \\ a b. the (Eq (\\ z. m1 a z) (m1 b)) refl;\n\
         U\n"
    );
    let out = ty(&src);
    assert!(
        out.contains("(P : ((z : U) → U) → U) → P (λ z. ?0 a z) → P (?0 b)"),
        "{out}"
    );
    assert_parity(&src);
}

/// 「先建短链、后解多 λ」直构族：f 的洞 meta 先以 1 实参链挂进未解头
// ?0 下，随后用 2 实参链的方程求解——引用陈旧链的项三模式判定/渲染
// 与参考版一致，不 panic、不挂死。
#[test]
fn stale_chain_under_unsolved_head() {
    for tail in [
        "the U (bad U)",
        "bad U",
        "the (Eq (bad U) (bad U)) refl",
        "the (Eq (bad U) U) refl",
        "let h : U = bad U;\nh",
        "\\ x. bad x",
        "g (bad U) U",
    ] {
        let src = format!(
            "let f : {{A : U}} -> U = \\{{A}}. _;\n\
             let g : U -> U -> U = _;\n\
             let bad = \\ a. g (f {{a}}) U;\n\
             let good = \\ a. the (Eq (f {{a}} U) U) refl;\n\
             {tail}\n"
        );
        assert_terminates_within(&src, 60);
    }
}

// --------------------------------------------------------------------------------
// 四、错误路径与解析残缺
// --------------------------------------------------------------------------------

/// 括号/花括号/方括号不闭合与各种截断 → `parse error`（不得 panic）。
#[test]
fn parse_resilience_unclosed() {
    for src in [
        "let x : {U = U", // `{` 不闭
        "let x : U = U[", // `[` 非法 token
        "(U\n",           // `(` 不闭
        ".",              // 孤点
        "\\x x\n",        // λ 缺点
        "let x U;\n",     // let 缺 =
        "let x : U =;",   // let 值残缺
        "{",              // 花括号在项首
    ] {
        for mode in ["nf", "type", "elab"] {
            assert_eq!(
                L04_implicit::main_with(mode, src),
                "parse error\n",
                "src {src:?} mode {mode}"
            );
            assert_eq!(
                fast::main_with(mode, src),
                "parse error\n",
                "src {src:?} mode {mode} (fast)"
            );
        }
    }
}

/// 多行源的错误位置：行号、caret 列逐字节（第 3 行第 13 列）。
#[test]
fn error_position_multiline() {
    assert_err_block(
        "let a : U = U;\nlet b : U = U;\nlet c : U = a b;\nc\n",
        3,
        13,
        "let c : U = a b;",
        "Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?0) → ?1 x",
    );
}

/// 行首 Tab：位置按字节列（第 2 行第 2 列），源码摘录原样带 Tab。
#[test]
fn error_position_with_tab() {
    let src = "let g : U -> U -> U = \\x y. x;\n\tg {U}\n";
    let out = ty(src);
    let expect = render_err(
        2,
        2,
        "\tg {U}",
        "Function icitness mismatch: expected implicit, got explicit.",
    );
    assert_eq!(out, expect, "{out}");
    assert_parity(src);
}

/// CRLF 行尾：正常判定不受影响；残缺输入照样 parse error。
#[test]
fn crlf_inputs() {
    let ok = "let g : U -> U -> U = \\x y. x;\r\ng U\r\n";
    assert_eq!(nf(ok), "λ y. U\n  :\nU → U\n");
    assert_parity(ok);
    let bad = "let x : U =;\r\n";
    assert_eq!(ty(bad), "parse error\n");
    assert_parity(bad);
}

/// CJK 标识符与 Unicode λ：ident 的 is_alphabetic 口径接受 CJK；
/// `λx.` 的 λ 拆分与 ASCII `\` 等价。
#[test]
fn cjk_and_unicode_lambda() {
    let src = "let 设 : U = U;\nλx. 设\n";
    assert_eq!(nf(src), "λ x. U\n  :\n(x : ?0) → U\n");
    assert_eq!(elab(src), "let ?0 = ?;\n\nlet 设 : U\n  = U;\n\nλ x. 设\n");
    assert_parity(src);
    let src2 = "let 设 : U = U;\n\\x. 设\n";
    assert_eq!(nf(src), nf(src2));
}

/// 行注释延伸到 EOF、块注释夹在实参间：不影响判定。
#[test]
fn comments_at_args_and_eof() {
    assert_eq!(nf("U -- → -> comment to eof"), "U\n  :\nU\n");
    let src = "let g : U -> U -> U = \\x y. x;\ng {- c -} U\n";
    assert_eq!(nf(src), "λ y. U\n  :\nU → U\n");
    assert_parity(src);
}

/// 尾随垃圾被丢弃的怪癖（解析器不强制 EOF，与 L05 同款、上游有差）：
/// `{}` 空实参、`{U = }` 残缺命名实参、`U)`、`U 1 2`、行尾不闭的
/// `{U`——首项完整后尾随 token 静默丢弃，不报 parse error。按实现
/// 如此钉住。
#[test]
fn trailing_tokens_dropped_quirk() {
    let g = "let g : U -> U -> U = \\x y. x;\n";
    for tail in ["g {}\n", "g {U = } U\n", "g {U = }\n", "g {U"] {
        let src = format!("{g}{tail}");
        assert_eq!(ty(&src), "U → U → U\n", "src {tail:?}");
        assert_parity(&src);
    }
    for src in ["U)\n", "U 1 2 3\n"] {
        assert_eq!(ty(src), "U\n", "src {src:?}");
        assert_parity(src);
    }
}

/// λ 自应用：`\{A} x. x x`——合成 Π 与洞类型失配，expected 侧显示挂
/// binder 的 spine `?1 A`（第一卷同款错误在 nf 模式下的形态）。
#[test]
fn self_application_error_message() {
    assert_err_block(
        "\\{A} x. x x\n",
        1,
        9,
        "\\{A} x. x x",
        "Cannot unify expected type\n\n  ?1 A\n\nwith inferred type\n\n  (x' : ?2 A x) → ?3 A x x'",
    );
    // nf 模式同块
    assert_eq!(
        nf("\\{A} x. x x\n"),
        render_err(
            1,
            9,
            "\\{A} x. x x",
            "Cannot unify expected type\n\n  ?1 A\n\nwith inferred type\n\n  (x' : ?2 A x) → ?3 A x x'"
        )
    );
}

/// 隐式 λ 对显式 Pi 的 binder 错位在 unify 的 Π/Π icit 失配（check 侧
// 路径，与 App 侧 icitness mismatch 是两条路），第一卷已钉 nf；这里补
/// elab/nf 同形短路（infer 失败时三模式同块）。
#[test]
fn infer_failure_modes_identical() {
    for src in [
        "let f : (A : U) -> A -> A = \\{A} x. x;\nf U\n",
        "let g : U -> U -> U = \\x y. x;\ng {U}\n",
        "\\{A} x. x x\n",
        "id\n",
        "let f : {A : U} -> A -> A = \\{B = x} x. x;\nf\n",
    ] {
        let t = ty(src);
        assert_eq!(nf(src), t, "nf 与 type 不同形：\n{src}");
        assert_eq!(elab(src), t, "elab 与 type 不同形：\n{src}");
        assert_parity(src);
    }
}

// --------------------------------------------------------------------------------
// 五、parity 扫描与负载
// --------------------------------------------------------------------------------

/// 组合语料扫描：声明族 × λ 上下文族 × 实参组合，三模式参考版↔孪生版
/// 逐字节比对（判定结果不断言——错误也是输出）。
#[test]
fn parity_scan_corpus() {
    let decls = [
        "let m1 : {A : U} -> U -> U = _;",
        "let m1 : U -> U -> U = _;",
        "let m1 : {A : U} -> U -> U -> U = _;",
        "let m1 : (A : U) -> U -> U = _;",
        "let m1 : {A : U} -> {B : U} -> U -> U = _;",
        "let m1 = _;",
    ];
    let ctxs = ["\\ a b.", "\\ {A} a.", "\\ {A} {B} a b.", "\\ (a : U) (b : U).", ""];
    let terms = [
        "m1 a",
        "m1 b",
        "m1 {a} b",
        "m1 a b",
        "m1 {a}",
        "\\ z. m1 a z",
        "id a",
        "id {a} b",
        "_ {a}",
        "the U (_ {a} {b})",
        "m1 (id a)",
        "m1 {a = a} b",
    ];
    let mut count = 0usize;
    for d in decls {
        for c in ctxs {
            for (i, t1) in terms.iter().enumerate() {
                for (j, t2) in terms.iter().enumerate() {
                    // 抽样：同项配对 + 偶序组合（减半保持覆盖面）
                    if i != j && (i + j) % 2 != 0 {
                        continue;
                    }
                    let body = format!("the (Eq ({t1}) ({t2})) refl");
                    let lambda = if c.is_empty() {
                        format!("let t = {body};")
                    } else {
                        format!("let t = {c} {body};")
                    };
                    let src = format!("{EQ_PRELUDE}{d}\n{lambda}\nU\n");
                    count += 1;
                    assert_parity(&src);
                }
            }
        }
    }
    assert!(count > 2000, "扫描语料过少：{count}");
}

/// 随机片段扫描（固定种子 xorshift64）：嵌套 λ/应用/隐式实参/命名实参/
/// 洞/Eq-refl 的组合，双实现逐字节一致；任何输入都不得 panic。
#[test]
fn parity_scan_random_fragment() {
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }
    fn gen_term(rng: &mut Rng, depth: usize, vars: &[&str]) -> String {
        if depth == 0 {
            let mut cs: Vec<&str> = vars.to_vec();
            cs.extend(["U", "_"]);
            return cs[rng.below(cs.len())].to_string();
        }
        match rng.below(10) {
            0 => format!("({} {})", gen_term(rng, depth - 1, vars), gen_term(rng, depth - 1, vars)),
            1 => format!("({} {{a}})", gen_term(rng, depth - 1, vars)),
            2 => format!("({} {{x = {}}})", gen_term(rng, depth - 1, vars), gen_term(rng, depth - 1, vars)),
            3 => format!("(\\ {}. {})", vars[0], gen_term(rng, depth - 1, vars)),
            4 => format!("(\\ {{z}}. {})", gen_term(rng, depth - 1, vars)),
            5 => format!("(the (Eq ({}) ({})) refl)", gen_term(rng, depth - 1, vars), gen_term(rng, depth - 1, vars)),
            6 => format!("(id {})", gen_term(rng, depth - 1, vars)),
            7 => format!("(id {{a}} {})", gen_term(rng, depth - 1, vars)),
            8 => format!("(the U {})", gen_term(rng, depth - 1, vars)),
            _ => {
                let mut cs: Vec<&str> = vars.to_vec();
                cs.push("_");
                cs[rng.below(cs.len())].to_string()
            }
        }
    }
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..400 {
        let decl = [
            "let m1 : {A : U} -> U -> U = _;",
            "let m1 : U -> U -> U = _;",
            "let m1 : {A}{B : U} -> U -> U = _;",
        ][rng.below(3)];
        let lam = ["\\ a b.", "\\ {A} a b.", "\\ (a : U) b.", ""][rng.below(4)];
        let t1 = gen_term(&mut rng, 2, &["a", "b"]);
        let t2 = gen_term(&mut rng, 2, &["a", "b"]);
        let body = format!("the (Eq ({t1}) ({t2})) refl");
        let lambda = if lam.is_empty() {
            format!("let t = {body};")
        } else {
            format!("let t = {lam} {body};")
        };
        let src = format!("{EQ_PRELUDE}{decl}\n{lambda}\nU\n");
        assert_parity(&src);
    }
}

/// 潜在慢输入的看门狗表征：L05 v3 的 redex 家族语料直译 + 深层交错
/// η/隐式实参组合，60s 内必须终止且两两一致。
#[test]
fn watchdog_family_terminates() {
    let decls = [
        "let m1 : {A : U} -> U -> U = _;",
        "let m1 : U -> U -> U = _;",
        "let m1 : {A : U} -> U -> U -> U = _;",
    ];
    let bodies = [
        "let t = \\ a b. the (Eq (m1 b) (m1 a)) refl;",
        "let t = \\ a b. the (Eq (m1 a) (m1 b)) refl;",
        "let t = \\ a b. the (Eq (m1 {a} b) (m1 a)) refl;",
        "let t = \\ a b. the (Eq (\\ z. m1 a z) (m1 b)) refl;",
        "let t = \\ a b. the (Eq (m1 {a} {b}) (\\ {z}. m1 {a} {b} {z})) refl;",
    ];
    for d in decls {
        for b in bodies {
            assert_terminates_within(&format!("{EQ_PRELUDE}{d}\n{b}\nU"), 60);
        }
    }
}

/// 深度负载：church 2^13 的 check + nf + type 三模式在大栈线程下双实现
/// 逐字节一致（第一卷只查了 k=11 的 type）。
#[test]
fn deep_church_k13_full_parity() {
    // church_src 是性能版 pub(crate) 基准生成器（测试 crate 不可达），手拼同款。
    let src = {
        let mut s = String::from(
            "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
             let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
             let p0 : Nat = \\N s z. s (s z);\n",
        );
        for i in 1..=12 {
            s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
        }
        s += "p12\n";
        s
    };
    with_big_stack(move || {
        let b = nf(&src);
        let f = fast::main_with("nf", &src);
        assert_eq!(b, f, "k=12 nf 不一致");
        assert!(b.starts_with("λ N s z. s ("), "{b}");
    });
}

/// implicit 负载（每层一次插入 + 一次求解）：k=4 全模式互检 + golden。
#[test]
fn implicit_workload_k4() {
    use L04_implicit::bump_spine_iter::implicit_src;
    let src = implicit_src(4);
    with_big_stack(move || {
        assert_parity(&src);
        assert_eq!(
            nf(&src),
            "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
        );
    });
}

/// solve 负载（Eq _ p_k p_k = refl _ _）：k=9 大解 + 互检（rename 沿
/// church 链走，第一卷 deep_church_under_big_stack 只查 k=11 的 type）。
/// 注：eqTest 的类型是 Eq 实例本身（P 应用到 church 1024 展开后的
/// `(P : Nat → U) → P … → P …`），不等于 U——只断言前缀与 parity。
#[test]
fn solve_workload_k9() {
    use L04_implicit::bump_spine_iter::solve_src;
    let src = solve_src(9);
    with_big_stack(move || {
        let b = ty(&src);
        let f = fast::main_with("type", &src);
        assert_eq!(b, f, "k=9 solve type 不一致");
        assert!(b.starts_with("(P : ((N : U) → (N → N) → N → N) → U) → P (λ N s z. s (s ("), "{b}");
        let b = elab(&src);
        let f = fast::main_with("elab", &src);
        assert_eq!(b, f, "k=9 solve elab 不一致");
        assert!(b.contains("let eqTest"), "{b}");
    });
}

/// nf ⊇ type 嵌入关系在本卷语料上成立。
#[test]
fn nf_embeds_type_on_v2_corpus() {
    for src in [
        "let f : {A : U}{B : U} -> U = \\{A}{B}. _;\nf\n",
        "\\{A}. \\{B}. U\n",
        "let f : _ = \\x. x;\nf U\n",
        "let f : {A : U}{B : U} -> A -> B -> A = \\x y. x;\nf\n",
        "\\{A}. U\n",
        "let 设 : U = U;\n设\n",
    ] {
        assert_nf_embeds_type(src);
        assert_parity(src);
    }
}

/// define 槽在洞 meta 的 bds 里被跳过（求值不应用、pretty 跳名）：
/// 洞在 λ 体内 define 之下捕获 inserted binder——`?0 A`（d 不进实参、
/// 不进显示），nf/elab 双侧一致。这是 vAppBds / goBDS 的 Defined 分支。
#[test]
fn hole_bds_skips_define_slots() {
    let src = "let f : {A : U} -> U = \\{A}. let d : U = U; _;\nf\n";
    assert_eq!(nf(src), "λ {A}. ?0 A\n  :\n{A : U} → U\n");
    // elab 打印的是 elaborated 项（let 原样保留），?0 A 的显示证明
    // pretty 的 Defined 跳名
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\nlet f : {A : U} → U\n  = λ {A}. let d : U\n  = U;\n\n?0 A;\n\nf\n"
    );
    assert_parity(src);
    // define 与 binder 交错：bds = [Bound B, Defined d, Bound A]
    // → 实参序 A 先、B 后，显示 `?0 A B`（d 跳名）。
    // （显式 Π 避免隐式 Π 对 let 的 inserted-binder 包裹——那条路径
    //  由上一条语义决定，见 check 臂序。）
    let src2 = "let g : (A : U) -> (B : U) -> U = \\A. let d : U = U; \\B. _;\ng\n";
    assert_eq!(nf(src2), "λ A B. ?0 A B\n  :\n(A : U)(B : U) → U\n");
    assert_parity(src2);
}

/// 错误列按字节计的怪癖（与上游 megaparsec 的字符列有差，L05 v2 已
/// 文档化同款）：错误位置之前的 CJK 字符按 UTF-8 字节数推进 caret 列
/// ——`设设`（6 字节）使纯 ASCII 基准的列 32 右移到 36。
#[test]
fn error_column_counts_bytes_not_chars() {
    let cjk = "let 设设 : U = U; let r : U = U; r U\n";
    let ascii = "let ab : U = U; let r : U = U; r U\n";
    let out_c = ty(cjk);
    let out_a = ty(ascii);
    assert_eq!(
        out_c, "(stdin):1:36:\n  |\n1 | let 设设 : U = U; let r : U = U; r U\n  |                                    ^\n\
               Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?0) → ?1 x\n",
        "{out_c}"
    );
    assert_eq!(
        out_a, "(stdin):1:32:\n  |\n1 | let ab : U = U; let r : U = U; r U\n  |                                ^\n\
               Cannot unify expected type\n\n  U\n\nwith inferred type\n\n  (x : ?0) → ?1 x\n",
        "{out_a}"
    );
    assert_parity(cjk);
}

/// help 消息与未知模式（快版入口直接走参考版 HELP_MSG）。
#[test]
fn help_and_unknown_modes_v2() {
    for mode in ["--help", "", "x", "NF"] {
        assert_eq!(fast::main_with(mode, ""), L04_implicit::main_with(mode, ""));
        assert!(fast::main_with(mode, "").starts_with("usage: elabzoo-implicit-args"));
    }
}

