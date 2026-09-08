//! L05_pruning 黑盒测试套件 · 第三卷（v3）。
//!
//! 与 `tests/l05_blackbox.rs`（主干）/ `l05_blackbox_v2.rs`（分支与布局）互
//! 补，本卷专攻两版孪生实现最容易走岔的**状态化角落**：
//!
//!   - **陈旧值引读（本轮发现并修复的真 bug）**：elaboration 期间 meta 先被
//!     应用进某条 spine 值、随后才被解成多 λ——快版 quote 的链分解会把该
//!     spine 的「函数部分」单独引读再重拼 `App`，函数部分 force 后是（部分
//!     应用的）闭包，重拼即产出 **β-红ex 项**（如 `?0 ((λ b'. ?5 a b') b)`）；
//!     参考版整值 force 经 `vAppSp` 一路 β，永不产出红ex。修复后钉死回归
//!     （见 `redex_*` 组）。
//!   - **occurs check 全谱**：meta 经由 spine 实参、闭包体、η 展开出现在自
//!     己的解里；二跳/三跳转发链的循环解；以及「方程恒真故不解」的
//!     η-塌缩（`?m ≡ λ x. ?m x` 不写解、不触发 occurs——双实现一致的
//!     已知不完备，按上游行为钉住）。
//!   - **剪枝与掩码渲染**：部分剪枝（中槽剪除保留两端）、隐式槽保留
//!     （`?n A` 形态）、依赖前缀剪枝失败的报错位置、交错 telescope
//!     （define 夹在 binder 间→fresh_meta 全 close 路径）、shadow binder。
//!   - **隐式插入 × meta 类型**：命名隐式定位、插入位洞的掩码显示、
//!     define-洞（D 族）与 meta 类型相互引用。
//!   - **错误路径与残缺输入**：不 panic、位置合理、三模式 parity。
//!   - **parity 扫描**：组合语料（m 族声明 × 实参组合）+ 中等规模负载 +
//!     潜在发散形状的看门狗表征（不挂死套件）。
//!
//! 双 oracle 与前两卷相同：
//!   1. golden 输出串（参考版语义推导 + 实测核对）；
//!   2. 参考版（`mod.rs`）↔ 性能版（`bump_spine_iter.rs`）三模式逐字节互检。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L05_pruning/mod.rs"]
mod L05_pruning;

use L05_pruning::bump_spine_iter as fast;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L05_pruning::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L05_pruning::main_with("type", src)
}

fn elab(src: &str) -> String {
    L05_pruning::main_with("elab", src)
}

/// Oracle 2：参考版与性能版在全部三种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    for mode in ["nf", "type", "elab"] {
        let b = L05_pruning::main_with(mode, src);
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

/// 报错输出 = 重建的完整错误块 + 双实现互检。
fn assert_err_block(src: &str, line: usize, col: usize, src_line: &str, msg: &str) {
    assert_eq!(ty(src), render_err(line, col, src_line, msg));
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

fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
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
                outs.push(L05_pruning::main_with(mode, &s));
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

/// `Eq / refl / the` 三件套前奏（上游 05 触发 unification 的标准模式）。
const PRELUDE: &str = r#"let Eq : {A : U} -> A -> A -> U = \{A} x y. (P : A -> U) -> P x -> P y;
let refl : {A : U}{x : A} -> Eq {A} x x = \ _ px. px;
let the : (A : U) -> A -> A = \ _ x. x;
"#;

fn zoo(body: &str) -> String {
    format!("{PRELUDE}{body}\nU\n")
}

const CANNOT_UNIFY: &str = "Cannot unify expected type";

// --------------------------------------------------------------------------------
// 一、陈旧值引读（quote β-红ex）回归——本轮修复的钉子
// --------------------------------------------------------------------------------

/// 最小复现：`m1 : {A : U} -> U -> U` 的两个部分应用做 Eq。解 `m1` 的隐式槽
/// 时，`?0` 的 spine 里挂了 `?5 a b`；随后 `?5` 被 flex_flex 解成**双 λ 转发
/// 解**，而引用它的 spine 值（建链早于求解）仍是陈旧位模式。quote 的链分解
/// 若单独引函数部分会停在部分应用的 λ 上，重拼出 `?0 ((λ b'. ?5 a b') b)`
/// 红ex；参考版整值 force 一路 β。修复后两版都给干净形态，报错逐字节一致。
#[test]
fn redex_regression_eq_swapped_args() {
    let src = zoo("let m1 : {A : U} -> U -> U = _;\nlet t = \\ a b. the (Eq (m1 b) (m1 a)) refl;");
    let golden = render_err(
        5,
        39,
        "let t = \\ a b. the (Eq (m1 b) (m1 a)) refl;",
        &format!(
            "{CANNOT_UNIFY}\n\n  (P : U → U) → P (?0 (?5 a b) b) → P (?0 (?5 a b) a)\n\nwith inferred type\n\n  (P : U → U) → P (?0 (?5 a b) b) → P (?0 (?5 a b) b)"
        ),
    );
    assert_eq!(ty(&src), golden);
    // infer 失败短路：三模式同形
    assert_eq!(elab(&src), golden);
    assert_eq!(nf(&src), golden);
    assert_parity(&src);
}

/// 同族：实参顺序互换（`m1 a` vs `m1 b`），失败方向镜像。
#[test]
fn redex_regression_eq_args_order_mirror() {
    let src = zoo("let m1 : {A : U} -> U -> U = _;\nlet t = \\ a b. the (Eq (m1 a) (m1 b)) refl;");
    let golden = render_err(
        5,
        39,
        "let t = \\ a b. the (Eq (m1 a) (m1 b)) refl;",
        &format!(
            "{CANNOT_UNIFY}\n\n  (P : U → U) → P (?0 (?5 a b) a) → P (?0 (?5 a b) b)\n\nwith inferred type\n\n  (P : U → U) → P (?0 (?5 a b) a) → P (?0 (?5 a b) a)"
        ),
    );
    assert_eq!(ty(&src), golden);
    assert_parity(&src);
}

/// 同族：混合隐式/显式实参（`m1 a` vs `m1 {a} b`）。此例里没有多 λ 转发解
/// （`?0` 的隐式槽直接被解掉），作为红ex 家族的**阴性对照**：报错干净、
/// 无部分应用 λ 出现。
#[test]
fn redex_family_negative_control() {
    let src = zoo("let m1 : {A : U} -> U -> U = _;\nlet t = \\ a b. the (Eq (m1 a) (m1 {a} b)) refl;");
    let golden = render_err(
        5,
        43,
        "let t = \\ a b. the (Eq (m1 a) (m1 {a} b)) refl;",
        &format!(
            "{CANNOT_UNIFY}\n\n  (P : U → U) → P (?0 a a) → P (?0 a b)\n\nwith inferred type\n\n  (P : U → U) → P (?0 a a) → P (?0 a a)"
        ),
    );
    assert_eq!(ty(&src), golden);
    assert_parity(&src);
}

/// 同族可解例：η 展开后经 intersect 剪掉差异槽，方程解出 `?0 := λ x0 x1.
/// ?7 x1`（丢首槽）、`?7 : U → U` 保持未解。钉住解形态 + 全模式 parity。
#[test]
fn redex_family_solvable_eta_intersect() {
    let src = zoo("let m1 : U -> U -> U = _;\nlet t = \\ a b. the (Eq (m1 a) (\\ z. m1 b z)) refl;");
    assert_eq!(ty(&src), "U\n");
    let e = elab(&src);
    assert!(
        e.contains("let ?0 : U → U → U = λ x0 x1. ?7 x1;\n"),
        "m1 的解应丢弃与方程无关的首槽：\n{e}"
    );
    assert!(e.contains("let ?7 : U → U = ?;\n"), "应余出共享的未解 meta ?7：\n{e}");
    assert_parity(&src);
}

/// 红ex 家族批量 parity（覆盖二叉 fallback 与链 bail 两个修复位点的形状），
/// 全部带看门狗表征。
#[test]
fn redex_family_parity_scan() {
    let bodies = [
        "let t = \\ a b. the (Eq (m1 b) (m1 a)) refl;",
        "let t = \\ a b. the (Eq (m1 a) (m1 b)) refl;",
        "let t = \\ a b. the (Eq (m1 {a} b) (m1 a)) refl;",
        "let t = \\ a b. the (Eq (m1 a b) (m1 b a)) refl;",
        "let t = \\ a b. the (Eq (\\ z. m1 a z) (m1 b)) refl;",
        "let t = \\ a b. the (Eq (m1 {a} {b}) (\\ {z}. m1 {a} {b} {z})) refl;",
    ];
    for d in [
        "let m1 : {A : U} -> U -> U = _;",
        "let m1 : U -> U -> U = _;",
        "let m1 : {A : U} -> U -> U -> U = _;",
    ] {
        for b in bodies {
            assert_terminates_within(&format!("{PRELUDE}{d}\n{b}\nU"), 60);
        }
    }
}

// --------------------------------------------------------------------------------
// 二、occurs check：自引用 / 解链循环 / η-塌缩
// --------------------------------------------------------------------------------

/// `?m U ≡ ?n (?m U)`：长侧反演遇非变量实参回落短侧，解 `?n := λ x0. ?m x0`
/// 转发后，`?m` 与 `?n (?m U)` 的余方程触发 occurs——失败落在 refl 位。
#[test]
fn occurs_via_spine_argument() {
    let src = zoo("let m : U -> U = _;\nlet n : U -> U = _;\nlet t = the (Eq (m U) (n (m U))) refl;");
    let golden = render_err(
        6,
        34,
        "let t = the (Eq (m U) (n (m U))) refl;",
        &format!(
            "{CANNOT_UNIFY}\n\n  (P : U → U) → P (?0 U) → P (?1 (?0 U))\n\nwith inferred type\n\n  (P : U → U) → P (?0 U) → P (?0 U)"
        ),
    );
    assert_eq!(ty(&src), golden);
    assert_parity(&src);
}

/// `?m U ≡ ?m (?m U)`：同头 flex，实参里嵌自身——intersect 的实参非裸变量
/// 回落 unify_sp，最终 occurs 失败。
#[test]
fn occurs_same_head_nested_self() {
    let src = zoo("let m : U -> U = _;\nlet t = the (Eq (m U) (m (m U))) refl;");
    let out = ty(&src);
    assert!(out.contains(CANNOT_UNIFY), "{out}");
    assert!(out.contains("P (?0 U) → P (?0 (?0 U))"), "{out}");
    assert_parity(&src);
}

/// η-塌缩（按上游行为钉住的「恒真方程」）：`?m ≡ λ x. ?m x` 经 η 后两侧同
/// 为 `?m x`，intersect 全等即成立——**不写解、不触发 occurs**（无循环解落
/// 表）。这是模式合一的已知不完备而非不可靠，双实现一致。
#[test]
fn eta_collapse_equation_without_occurs() {
    let src = zoo("let m : U -> U = _;\nlet t = the (Eq (\\ x. m x) m) refl;");
    assert_eq!(ty(&src), "U\n");
    let e = elab(&src);
    // m 的解是到新 meta 的转发（λ x0. ?5 x0），不存在自引用解体
    assert!(e.contains("let ?0 : U → U = λ x0. ?5 x0;\n"), "{e}");
    assert!(e.contains("let ?5 : (x : U) → U = ?;\n"), "{e}");
    assert_parity(&src);
}

/// 三跳解链：`m1 (m2 U) ≡ m3 (m1 (m2 U))`——转发后 occurs 仍在最内层引用处
/// 失败，错误渲染含整条链。
#[test]
fn occurs_three_hop_chain() {
    let src = zoo("let m1 : U -> U = _;\nlet m2 : U -> U = _;\nlet m3 : U -> U = _;\nlet t = the (Eq (m1 (m2 U)) (m3 (m1 (m2 U)))) refl;");
    let out = ty(&src);
    assert!(out.contains(CANNOT_UNIFY), "{out}");
    assert!(
        out.contains("P (?0 (?1 U)) → P (?2 (?0 (?1 U)))"),
        "链形态应完整出现在报错里：\n{out}"
    );
    assert_parity(&src);
}

/// 方向镜像：长侧在左（`?n (?m U)` ≡ `?m U`），occurs 失败对称。
#[test]
fn occurs_mirror_longer_side_left() {
    let src = zoo("let m : U -> U = _;\nlet n : U -> U = _;\nlet t = the (Eq (n (m U)) (m U)) refl;");
    let out = ty(&src);
    assert!(out.contains(CANNOT_UNIFY), "{out}");
    assert!(out.contains("P (?1 (?0 U)) → P (?0 U)"), "{out}");
    assert_parity(&src);
}

/// 自应用：`\ A x. x x`——x 的类型 meta 合成 Π 后与自身定义域失配，
/// Cannot unify 定位到 λ 体。
#[test]
fn self_application_type_error() {
    let src = "\\ A x. x x";
    let golden = render_err(
        1,
        10,
        "\\ A x. x x",
        &format!(
            "{CANNOT_UNIFY}\n\n  ?4 A\n\nwith inferred type\n\n  (x' : ?4 A) → ?5 A x'"
        ),
    );
    assert_eq!(ty(src), golden);
    assert_parity(src);
}

// --------------------------------------------------------------------------------
// 三、剪枝：部分剪枝 / 隐式槽保留 / 依赖失败 / 交错 telescope / shadow
// --------------------------------------------------------------------------------

/// 交集剪枝保留**隐式槽**：`m {a} b a ≡ m {a} b b`——A、b 槽保留（尾槽 a/b
/// 剪除），解 `?0 := λ A x1 x2. ?7 x1`；按实现口径（Cxt.bind 的文档化怪癖）
/// 源隐式槽在掩码里恒按显式应用打印（`?0 A` 而非 `?0 {A}`）。
#[test]
fn intersect_keeps_implicit_slot() {
    let src = zoo("let m : {A : U} -> U -> U -> U = _;\nlet t = \\ a b. the (Eq (m {a} b a) (m {a} b b)) refl;");
    assert_eq!(ty(&src), "U\n");
    let e = elab(&src);
    assert!(
        e.contains("let ?0 : (A : U) → U → U → U = λ A x1 x2. ?7 x1;\n"),
        "{e}"
    );
    assert!(e.contains("let ?7 : (b : U) → U = ?;\n"), "{e}");
    assert!(e.contains("let m : {A : U} → U → U → U\n  = λ {A}. ?0 A;\n"), "{e}");
    assert_parity(&src);
}

/// 部分剪枝（中槽剪除保留两端）：`m a b c ≡ m a c c`——中槽 b/c 剪除，
/// `?8 : (a : U)(c : U) → U`，解 `?0 := λ x0 x1 x2. ?8 x0 x2`。
#[test]
fn intersect_prunes_middle_slot_keeps_ends() {
    let src = zoo("let m : U -> U -> U -> U = _;\nlet t = \\ a b c. the (Eq (m a b c) (m a c c)) refl;");
    assert_eq!(ty(&src), "U\n");
    let e = elab(&src);
    assert!(
        e.contains("let ?0 : U → U → U → U = λ x0 x1 x2. ?8 x0 x2;\n"),
        "{e}"
    );
    assert!(e.contains("let ?8 : (a : U)(c : U) → U = ?;\n"), "{e}");
    assert!(
        e.contains("(P : U → U) → P (?8 a c) → P (?8 a c)"),
        "剪后类型应只剩两端槽：\n{e}"
    );
    assert_parity(&src);
}

/// 依赖前缀的非线性剪枝在**实参位**失败：`m : (x : U)(y : x) -> U` 的
/// `m a a`——第二个 `a` 过不了 `x := a` 的检查（expected `a`，inferred `U`），
/// 根本走不到 solve。
#[test]
fn dependent_prefix_fails_at_argument() {
    let src = zoo("let m : (x : U)(y : x) -> U = _;\nlet t = \\ a. the (Eq (m a a) _) refl;");
    assert_error_at(&src, 5, 27, CANNOT_UNIFY);
    let out = ty(&src);
    assert!(out.contains("  a\n\nwith inferred type\n\n  U"), "{out}");
}

/// 越界转义 × 隐式槽位（负例对照）：两侧 arity 不齐时在 Eq 位报
/// `U` vs `(w : U) → U`——错误路径 parity（不触发剪枝，但钉住该形状不炸）。
#[test]
fn prune_escape_implicit_slots_arity_mismatch() {
    let src = zoo("let m1 : {A : U} -> U -> U = _;\nlet m2 : {A : U} -> U -> U = _;\nlet t = \\ x y. the (Eq (m1 {x} y) (\\ w. m2 {y} w)) refl;");
    assert_error_at(&src, 6, 36, CANNOT_UNIFY);
    let out = ty(&src);
    assert!(out.contains("  U\n\nwith inferred type\n\n  (w : U) → U"), "{out}");
}

/// 交错 telescope（define 夹在 binder 之后→`fresh_meta` 走全 close 路径）：
/// 洞的掩码仍是 `?1 a b`（define 槽 q 不产生实参），类型显示不含 let 层。
#[test]
fn interleaved_telescope_hole() {
    let src = "let f : U -> (b : U) -> U = \\a. let q = a; \\b. _;\nf";
    assert_eq!(ty(src), "U → (b : U) → U\n");
    let e = elab(src);
    assert!(e.contains("let ?0 : (a : U) → U = λ a. U;\n"), "{e}");
    assert!(e.contains("let ?1 : (a : U)(b : U) → U = ?;\n"), "{e}");
    assert!(e.contains("λ b. ?1 a b;"), "{e}");
    assert_parity(src);
}

/// shadow binder：`\a a. _`——类型里第二个 binder fresh 成 `a'`，掩码实参
/// 逐级命名。
#[test]
fn shadowed_binders_in_hole_mask() {
    let src = "let f = \\a a. _;\nf";
    assert_eq!(ty(src), "(a : ?1)(a' : ?2 a) → ?3 a a'\n");
    let e = elab(src);
    assert!(e.contains("let ?4 : (a : ?1)(a' : ?2 a) → ?3 a a' = ?;\n"), "{e}");
    assert!(e.contains("= λ a a'. ?4 a a';"), "{e}");
    assert_parity(src);
}

/// 三次非线性（v1 已钉 `m a a a` 的 triple）：这里补**依赖结果版**——
/// `m : (x : U)(y : U)(z : U) -> x` 的 `m a a a` 类型合法（结果 `a`），
/// 但 refl 方程 `?0 a a a ≡ ?6 a` 里 `?0` 的 spine 三次非线性，剪枝后类型
/// 掉出 Π（结果 `a` 非 Π）且右侧含非线性变量，最终卡死在 refl 位。
#[test]
fn nonlinear_triple_dependent_result() {
    let src = zoo("let m : (x : U)(y : U)(z : U) -> x = _;\nlet t = \\ a. the (Eq (m a a a) _) refl;");
    let out = ty(&src);
    assert!(
        out.starts_with("(stdin):5:35:\n"),
        "失败应落在 refl 位：\n{out}"
    );
    assert!(out.contains(CANNOT_UNIFY), "{out}");
    assert!(out.contains("P (?0 a a a)"), "{out}");
    assert_parity(&src);
}

// --------------------------------------------------------------------------------
// 四、隐式插入 × meta 类型
// --------------------------------------------------------------------------------

/// 命名隐式定位：`f {B = U} U`——按名跳过 A（插入 `?1`）、停在 B（显式给
/// `U`）。elab 显示插入的 `?1` 与调用形态 `f {?1} {U} U`。
#[test]
fn named_implicit_inserts_and_locates() {
    let src = "let f : {A : U}{B : U} -> U -> U = _;\nf {B = U} U";
    assert_eq!(ty(src), "U\n");
    let e = elab(src);
    assert!(e.contains("let ?0 : (A : U)(B : U) → U → U = ?;\n"), "{e}");
    assert!(e.contains("let ?1 : U = ?;\n"), "{e}");
    assert!(e.contains("f {?1} {U} U"), "{e}");
    assert_parity(src);
}

/// 命名隐式 λ binder `{A = aa}`：体内本地名 aa；掩码按实现口径（源隐式
/// binder 入掩码恒 Some(Expl)，v2 已记录的怪癖）打印裸名 `?0 aa`。
#[test]
fn named_implicit_lambda_local_name_in_mask() {
    let src = "let f : {A : U} -> U = \\{A = aa}. _;\nf {A = U}";
    assert_eq!(ty(src), "U\n");
    let e = elab(src);
    assert!(e.contains("let ?0 : (aa : U) → U = ?;\n"), "{e}");
    assert!(e.contains("= λ {aa}. ?0 aa;"), "{e}");
    assert!(e.contains("f {U}"), "{e}");
    assert_parity(src);
}

/// 命名隐式「乱序」的边界：`f {B = U} {A = U} U`——定位 B 时跳过 A 的槽位
/// 已被插入 meta 消耗，后续 `{A = U}` 在剩余类型（U → U，无隐式前缀）里找
/// 不到 A，报 No named implicit argument。
#[test]
fn named_implicit_out_of_order() {
    let src = "let f : {A : U}{B : U} -> U -> U = _;\nf {B = U} {A = U} U";
    assert_error_at(src, 2, 1, "No named implicit argument with name A");
}

/// D 族：define 的值是洞（`D : U = _`）。`f` 的注解余定义域是 `D`（值为
/// 未解 `?0`），其洞类型引用 `?0`；随后 `g` 把 `?0` 解成 `U`（check Π 值对
/// `D` 时 unify `?0 := U`），显示经 force 展开为解后形态。
#[test]
fn define_hole_type_forward_reference() {
    let src = "let D : U = _;\nlet f : (a : U) -> D = \\a. _;\nlet g : D = (x : U) -> U;\nf";
    assert_eq!(ty(src), "(a : U) → U\n");
    let e = elab(src);
    // D 的解：?0 := U（Π 值的类型是 U）
    assert!(e.contains("let ?0 : U = U;\n"), "{e}");
    // f 的洞类型引用 ?0（显示时 force 成解后形态 U）
    assert!(e.contains("let ?1 : (a : U) → U = ?;\n"), "{e}");
    assert!(e.contains("let D : U\n  = ?0;"), "{e}");
    assert_parity(src);
}

/// D 族变体：`g : D = \x. x` 的 λ 推断类型是 Π，把 `?0` 解成 **Π 值**
/// （而非 U）——`f` 的类型显示随之展开为 `(a : U)(x : ?2) → ?2`。
#[test]
fn define_hole_solved_to_pi() {
    let src = "let D : U = _;\nlet f : (a : U) -> D = \\a. _;\nlet g : D = \\x. x;\nf";
    assert_eq!(ty(src), "(a : U)(x : ?2) → ?2\n");
    assert_parity(src);
}

/// D 族错误路径：`D : U -> U` 的值不符合宇宙——`(a : U) -> D` 的余定义域
/// 检查在 D 位报 `U` vs `U → U`。
#[test]
fn define_hole_family_type_error() {
    let src = "let D : U -> U = _;\nlet f : (a : U) -> D = \\a. _;\nlet g : D = \\x. x;\nf";
    assert_error_at(src, 2, 20, CANNOT_UNIFY);
    let out = ty(src);
    assert!(out.contains("  U\n\nwith inferred type\n\n  U → U"), "{out}");
}

/// 命名隐式 λ 的推断不可行（v1 已钉）；这里钉**裸命名 λ** 的应用位错误。
#[test]
fn infer_named_lambda_body_error() {
    assert_error_at("\\{A = x}. x", 1, 1, "Cannot infer type for lambda with named argument");
}

// --------------------------------------------------------------------------------
// 五、错误路径与残缺输入（不 panic、位置合理、三模式 parity）
// --------------------------------------------------------------------------------

/// 残缺/怪输入语料（v2 未覆盖的补充）：全部 `parse error` 或类型错误，
/// 不 panic、双实现一致。
#[test]
fn malformed_corpus_extended() {
    for src in [
        "λ (A : U) (x : A). x x", // λ binder 不吃类型注解（那是 Pi 的语法）
        "\\{A}. {A}",             // `{A}` 不是表达式（隐式只出现在实参/binder 位）
        "_ _ _",
        "let x =;",
        "let x : U = U", // 缺分号
        "(\\x. x x) (\\x. x x)",
        "U U U",
        "f U",
        "let x : x = x;\nx",
        "let x : U = x;\nlet y : U = y;\ny",
        "\\x. \\{y = z}. z x",
        "let m : U -> U = _;\nm m m",
    ] {
        let out = ty(src);
        assert!(
            out.starts_with("(stdin):") || out == "parse error\n",
            "残缺输入应报错而非成功：src={src:?}\n{out}"
        );
        assert_parity(src);
    }
}

/// 命名隐式实参找不到同名 binder（隐式前缀耗尽/重名消耗）。
#[test]
fn named_implicit_not_found() {
    assert_error_at(
        "let f : {A : U} -> U = _;\nf {B = U}",
        2,
        1,
        "No named implicit argument with name B",
    );
    assert_error_at(
        "let f : {A : U} -> U = _;\nf {A = U} {A = U}",
        2,
        1,
        "No named implicit argument with name A",
    );
}

/// `the {U} U`（无 prelude）：作用域错误优先于 icit 检查。
#[test]
fn scope_error_before_icit() {
    assert_error_at("the {U} U", 1, 1, "Name not in scope: the");
}

/// λ 体内 define 的值位自引用不可见（进入 scope 前检查）。
#[test]
fn define_value_self_reference_invisible() {
    assert_error_at(
        "let f : U -> U = \\u. let q : U = q; q;\nf\n",
        1,
        34,
        "Name not in scope: q",
    );
}

/// 报错块字节级金样（CRLF + Tab 混合源；v2 钉过单一形态，这里补混合）。
#[test]
fn error_block_byte_layout_mixed() {
    assert_eq!(
        ty("let ok : U = U;\r\n\tid q\r\n"),
        render_err(2, 2, "\tid q", "Name not in scope: id")
    );
    assert_parity("let ok : U = U;\r\n\tid q\r\n");
}

// --------------------------------------------------------------------------------
// 六、parity 扫描（组合语料 + 中等负载 + 看门狗）
// --------------------------------------------------------------------------------

/// 组合语料：m 族声明（7 种 arity/icit 形态）× 方程两侧实参（8 种）全叉乘，
/// 三模式 parity。每例只要求「成功 or 报错」两态一致（成功态不追金样，
/// 金样由上面各组钉住）。
#[test]
fn parity_scan_m_family_matrix() {
    let mdecls = [
        "let m1 : U -> U = _;",
        "let m1 : U -> U -> U = _;",
        "let m1 : {A : U} -> U -> U = _;",
        "let m1 : (a : U) -> U -> U = _;",
        "let m1 : {A : U} -> A -> A -> U = _;",
        "let m1 : U -> U -> U -> U = _;",
        "let m1 : (a : U) (b : a) -> U = _;",
    ];
    let args = ["a", "b", "a a", "b a", "m2 a", "m2 b", "{a} b", "a {b}"];
    for d in mdecls {
        for l in args {
            for r in args {
                let src = format!(
                    "{PRELUDE}let m2 : U -> U = _;\n{d}\nlet t = \\ a b. the (Eq (m1 {l}) (m1 {r})) refl;\nU"
                );
                assert_parity(&src);
                let out = ty(&src);
                assert!(
                    out == "U\n" || out.contains("(stdin):"),
                    "矩阵用例应成功或报错：{src}\n{out}"
                );
            }
        }
    }
}

/// η × icit 矩阵：λ 侧 binder 的 icit 与 flex 侧 spine 槽 icit 的组合。
#[test]
fn parity_scan_eta_icit_matrix() {
    let eqs = [
        "the (Eq (m1 {a}) (\\ z. m1 {a} z)) refl",
        "the (Eq (m1 {a}) (\\ {z}. m1 {a} z)) refl",
        "the (Eq (m1 a) (\\ {z}. m1 a {z})) refl",
        "the (Eq (\\ z. m1 a z) (m1 a)) refl",
        "the (Eq (\\ {z}. m1 {a} {z}) (m1 {a})) refl",
        "the (Eq (m1 a b) (\\ z. m1 a b z)) refl",
    ];
    for d in [
        "let m1 : {A : U} -> U -> U = _;",
        "let m1 : U -> U -> U = _;",
        "let m1 : {A : U} -> U -> U -> U = _;",
    ] {
        for e in eqs {
            let src = format!("{PRELUDE}{d}\nlet t = \\ a b. {e};\nU");
            assert_parity(&src);
        }
    }
}

/// 剪枝转义矩阵：隐式/显式槽混合的越界变量（含负例 arity 失配）。
#[test]
fn parity_scan_escape_matrix() {
    let eqs = [
        "the (Eq (m1 x) (\\ w. m2 y w)) refl",
        "the (Eq (m1 x) (\\ w. m2 {y} w)) refl",
        "the (Eq (m1 {x}) (\\ w. m2 y w)) refl",
        "the (Eq (m1 x y) (\\ w. m2 y w)) refl",
        "the (Eq (m1 y) (\\ w. m2 x w)) refl",
    ];
    for d in [
        "let m1 : U -> U -> U = _;\nlet m2 : U -> U -> U = _;",
        "let m1 : {A : U} -> U -> U = _;\nlet m2 : {A : U} -> U -> U = _;",
    ] {
        for e in eqs {
            let src = format!("{PRELUDE}{d}\nlet t = \\ x y. {e};\nU");
            assert_parity(&src);
        }
    }
}

/// 多方程交互：共享 meta 的先后解（先非线性求解、再交集、再等 spine）。
#[test]
fn multi_equation_interactions() {
    for body in [
        "let t1 = the (Eq (m1 a a) (\\ x y. y)) refl;\nlet t2 = the (Eq (m1 b c) (m1 b c)) refl;",
        "let t1 = the (Eq (m1 a b) (m1 b a)) refl;\nlet t2 = the (Eq (m1 a b) (m1 a b)) refl;",
        "let t1 = the (Eq (m1 a) (m1 a)) refl;\nlet t2 = the (Eq (m1 a) (m1 b)) refl;",
    ] {
        let src = format!("{PRELUDE}let m1 : U -> U -> U = _;\n{body}\nU");
        assert_parity(&src);
    }
}

/// 交错 telescope 矩阵：define 与 binder 的各种交错 + 洞（fresh_meta 全
/// close 路径全覆盖）。
#[test]
fn interleaved_telescope_matrix() {
    for s in [
        "let f : U -> (b : U) -> U = \\a. let q = a; \\b. _;",
        "let f : U -> U -> (c : U) -> U = \\a. let q = a; \\b. let r = b; \\c. _;",
        "let f : U -> U = \\a. let q = _; let r = a; _;",
        "let f : (a : U) -> U = \\a. let q = a; \\{B}. _;",
        "let f : {A : U} -> U -> U = \\{A}. let q = A; \\x. _;",
        "let f = \\a. let q = a; \\b. let r = b; \\c. _;",
    ] {
        for tail in ["U", "f"] {
            let src = format!("{s}\n{tail}");
            assert_parity(&src);
        }
    }
}

/// 洞家族（掩码/telescope 形态）：bind 前缀快路径与全 close 路径两口径下
/// 双实现一致，三态输出非空。
#[test]
fn hole_telescope_matrix() {
    for s in [
        "let f : (a : U) -> U = \\a. _;",
        "let f : (a : U) -> U = \\a. let q : U = U; _;",
        "let f = \\a b. let q = a; _;",
        "let f : {A : U} -> U -> U = \\{A} x. _;",
        "let f : {A : U} -> U -> U = \\{A = aa} x. _;",
        "let f : (a : U) -> (b : U) -> U = \\a b. let q1 : U = a; let q2 : U = b; _;",
        "let f : (a : U) -> U = \\a. let q : a = a; _;",
        "let f : (a : U) -> (x : a) -> U = \\a x. _;",
    ] {
        for tail in ["U", "f"] {
            let src = format!("{s}\n{tail}");
            assert_parity(&src);
            assert!(!ty(&src).is_empty());
        }
    }
}

/// 中等规模负载（k=5..6）全模式 parity：覆盖 church/solve/prune/implicit
/// 等生成器在「深到有状态、浅到不炸栈」区间的表现。
#[test]
fn workload_medium_k_parity() {
    for k in 5..=6u32 {
        assert_parity(&fast::church_src(k));
        assert_parity(&fast::implicit_src(k));
        assert_parity(&fast::chain_src(k));
        assert_parity(&fast::conv_src(k));
        assert_parity(&fast::conv_dup_src(k));
        assert_parity(&fast::dup_src(k));
        assert_parity(&fast::dup_deep_src(k));
    }
    for k in 4..=5u32 {
        assert_parity(&fast::solve_src(k));
        assert_parity(&fast::prune_src(k));
    }
}

/// 40 层 define 链 + λ 下洞；λ 内 30 层 define 链 + 洞（bind_prefix 快路径
/// 深层）。参考版放深栈线程。
#[test]
fn deep_define_chain_with_holes_big_stack() {
    {
        let mut s = String::from("let x0 : U = U;\n");
        for i in 1..40 {
            s.push_str(&format!("let x{i} : U = x{};\n", i - 1));
        }
        s.push_str("let f : (a : U) -> U = \\a. _;\nf\n");
        let b = {
            let s2 = s.clone();
            with_big_stack(move || L05_pruning::main_with("type", &s2))
        };
        let f = fast::main_with("type", &s);
        assert_eq!(b, f);
        assert_eq!(f, "(a : U) → U\n");
    }
    {
        let mut s = String::from("let f : (a : U) -> U -> U = \\a b.\n");
        for i in 0..30 {
            s.push_str(&format!("let q{i} : U = a;\n"));
        }
        s.push_str("_;\nf\n");
        let b = {
            let s2 = s.clone();
            with_big_stack(move || L05_pruning::main_with("elab", &s2))
        };
        let f = fast::main_with("elab", &s);
        assert_eq!(b, f);
        // 注解具体（无 binder 类型 meta）：唯一的 meta 是末尾洞，掩码只剩
        // 2 个绑定槽（define 槽全部塌缩）
        assert!(f.contains("let ?0 : (a : U)(b : U) → U = ?;\n"), "{f}");
        assert!(f.contains("?0 a b;"), "{f}");
    }
}

/// 潜在发散形状的看门狗表征（η-塌缩、互 η、深层转发、嵌套 flex 同头）——
/// 全部应在时限内终止且 parity。
#[test]
fn potentially_looping_shapes_terminate() {
    for src in [
        // η-塌缩（恒真方程，不解）
        zoo("let m : U -> U = _;\nlet t = the (Eq (\\ x. m x) m) refl;"),
        // 互 η
        zoo("let m : U -> U = _;\nlet n : U -> U = _;\nlet t = the (Eq (\\ x. m (n x)) (\\ x. n (m x))) refl;"),
        // 深转发链
        zoo("let m1 : U -> U = _;\nlet m2 : U -> U = _;\nlet m3 : U -> U = _;\nlet t = the (Eq (m1 (m2 U)) (m3 (m1 (m2 U)))) refl;"),
        // 同头交集中嵌套 flex 实参
        zoo("let m : U -> U -> U = _;\nlet t = \\ a. the (Eq (m a (m a a)) (m a a)) refl;"),
    ] {
        assert_terminates_within(&src, 60);
    }
}
