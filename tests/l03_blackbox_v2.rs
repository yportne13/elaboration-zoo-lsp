//! L03_holes 黑盒攻击套件 v2（第二轮黑盒巡查；风格与 helper 向 l03_blackbox.rs 看齐）。
//!
//! 被测对象与唯一入口同 v1：`L03_holes::main_with(mode, src)` 与孪生
//! `L03_holes::bump_spine_iter::main_with`（mode ∈ {nf, type, elab}），经
//! `#[path]` 独立编译进本测试 crate。双 oracle：
//!   1. 期望输出字符串 —— 全部整串断言均与实际输出逐字节核对过（探测
//!      脚本实测），语义判读以 src/L03_holes/readme.md 与上游
//!      elaboration-zoo `03-holes/Main.hs` 为准（RApp 的 cod 洞绑定、
//!      vAppBDs 掩码应用、solve 的模式解限制均逐函数比对过上游源码）；
//!   2. 参考版（mod.rs）↔ 性能版（bump_spine_iter.rs）**三模式**
//!      （nf/type/elab）逐字节互检。
//!
//! v2 的新增覆盖（v1 未钉住的攻击面）：
//!   - 洞编号顺序、多洞共享上下文、洞作为函数头/实参的 elaboration 形态；
//!   - 求解金样：cod 洞投影、Defined 槽位跳过、meta→引用链、dup×洞 memo；
//!   - **非模式解限制的钉子**（readme「已知限制」/上游一致行为）：
//!     `?m x x` 同变量 spine、`?m U` 非变量实参等一律 Cannot unify——
//!     这些用例同时是「行为不变」的哨兵，L04 起引入 pruning 才会改变；
//!   - η 双参吸收 / meta 实参短侧的二元变体（v1 只钉了一元）；
//!   - 错误路径：CRLF、tab、多行 caret、let 非递归、匿名 binder 不可引用；
//!   - 解析残缺 battery（带 30s 看门狗，防套件挂死）；
//!   - 大栈压力：深括号、200 binder 洞、200 洞链（参考版递归 quote/pretty
//!     与 parser 都吃栈，小栈输入会直接 abort 进程——见下「已知包络」）。
//!
//! 套件记录的「已知怪癖/包络」（非 bug，勿重复上报）：
//!   - v1 头部的全部怪癖（尾随垃圾、字节列号等）继续有效；
//!   - `?` 不是表面语法（只有 `_` 是 hole），输入 `?` 得 parse error；
//!   - `\_x. x` 的 `_x` 被切成两个 binder（`_` 与 `x`），词法层面 `_` 恒
//!     单独成 token（与 L02 同款切分）；
//!   - **parser 栈深包络**：两版共用的递归下降 parser 在 ~300 层嵌套括号
//!     附近会栈溢出（libtest 默认线程栈，debug 构建；直接 abort 进程，
//!     无法捕获）。这与 readme「已知限制」的参考版递归深度同属一类包络，
//!     且 L02/L04~L07 的 parser 同构（跨章共性）。深度用例一律在
//!     `with_big_stack` 里跑，套件不在小栈上触碰 ≥350 层括号。
//!   - **参考版多 binder × 未解洞的性能包络**：infer 的 closeVal 逐层
//!     re-quote（上游 `closeVal = quote (lvl+1)` 的忠实移植）在 200 个
//!     binder 的 `\. _` 上实测 ~87s（快版 <1s、输出逐字节一致）——参考版
//!     的算法性超线性，非移植缺陷，v2 首次量化；深 binder 用例大 n 只跑
//!     快版。
//!   - 消融环境变量（L03_NO_CONV_MEMO / L03_NO_NAME_MAP）是进程级
//!     LazyLock，v1 已覆盖，v2 不碰 env（避免与本套件并行测试互染）。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L03_holes/mod.rs"]
mod L03_holes;

use L03_holes::bump_spine_iter as fast;

// helpers
// --------------------------------------------------------------------------------

fn nf(src: &str) -> String {
    L03_holes::main_with("nf", src)
}

fn ty(src: &str) -> String {
    L03_holes::main_with("type", src)
}

fn elab(src: &str) -> String {
    L03_holes::main_with("elab", src)
}

fn fast_nf(src: &str) -> String {
    fast::main_with("nf", src)
}

/// Oracle 2：参考版与性能版在全部三种模式下输出逐字节一致。
fn assert_parity(src: &str) {
    for mode in ["nf", "type", "elab"] {
        let b = L03_holes::main_with(mode, src);
        let f = fast::main_with(mode, src);
        assert_eq!(
            b, f,
            "{mode} 模式双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        );
    }
}

/// 报错输出：以 `(stdin):{line}:{col}:` 开头且包含消息片段（含 parity）。
fn assert_error_at(src: &str, line: usize, col: usize, needle: &str) {
    let out = nf(src);
    assert!(
        out.starts_with(&format!("(stdin):{line}:{col}:\n")),
        "错误位置不符：期望 ({line}:{col})，实际：\n{out}"
    );
    assert!(out.contains(needle), "错误消息缺 {needle:?}：\n{out}");
    assert_parity(src);
}

/// 在大栈线程里跑（深度负载：参考版 quote/pretty 与共用 parser 都是递归）。
fn with_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// 看门狗：在带超时的子线程里跑三模式（错误路径不得挂死；超时即败，
/// 泄漏的工作线程随进程退出回收——正经实现毫秒级返回，只是兜底）。
fn assert_terminates(src: &str) {
    let (tx, rx) = std::sync::mpsc::channel();
    let owned = src.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            for mode in ["nf", "type", "elab"] {
                let _ = L03_holes::main_with(mode, &owned);
                let _ = fast::main_with(mode, &owned);
            }
            tx.send(()).expect("看门狗：主端已放弃等待");
        })
        .unwrap();
    if rx.recv_timeout(std::time::Duration::from_secs(30)).is_err() {
        panic!("疑似挂死（30s 无输出）：{src:?}");
    }
}

/// church n 的 nf 文本（无尾换行）。
fn church_tm(n: usize) -> String {
    fn f(k: usize) -> String {
        match k {
            0 => "z".to_string(),
            1 => "s z".to_string(),
            k => format!("s ({})", f(k - 1)),
        }
    }
    format!("λ N s z. {}", f(n))
}

fn nat_type() -> &'static str {
    "(N : U) → (N → N) → N → N"
}

// 洞的基本形态与编号
// --------------------------------------------------------------------------------

#[test]
fn hole_numbering_infer_creates_two_check_creates_one() {
    // infer 位置的洞挂一对 meta（类型 + 项）；check 位置的洞只挂一个。
    // `let x : _ = _; x`：注解洞与值洞都在 check 位置，共两个 meta，
    // 编号按出现顺序 ?0（注解）、?1（值）。
    let src = "let x : _ = _; x";
    assert_eq!(nf(src), "?1\n  :\n?0\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\nlet ?1 = ?;\n\nlet x : ?0\n  = ?1;\n\nx\n"
    );
    assert_parity(src);
}

#[test]
fn hole_as_head_applied_golden() {
    // `_ _`：头洞的类型 meta 被合成 Π 解掉（?0 := (x : ?2) → ?3 x），
    // 实参洞与余定义域洞保持未解。
    let src = "_ _";
    assert_eq!(nf(src), "?1 ?4\n  :\n?3 ?4\n");
    assert_eq!(ty(src), "?3 ?4\n");
    assert_eq!(
        elab(src),
        "let ?0 = (x : ?2) → ?3 x;\n\
         let ?1 = ?;\n\
         let ?2 = ?;\n\
         let ?3 = ?;\n\
         let ?4 = ?;\n\n\
         ?1 ?4\n"
    );
    assert_parity(src);
}

#[test]
fn hole_head_three_applications_hits_non_pattern() {
    // `_ _ _`：第二次应用要对 `?3 ?4`（flex spine）合成 Π 求解，
    // spine 实参 `?4` 不是 rigid 变量 → 非模式 → Cannot unify
    // （readme「已知限制」，上游 solve/invert 同款）。
    let src = "_ _ _";
    assert_error_at(src, 1, 1, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("(x : ?5) → ?6 x"), "{out}");
    assert!(out.contains("?3 ?4"), "{out}");
}

#[test]
fn multi_binder_hole_numbering_and_spine_order() {
    // 洞抽象当前全部 Bound 槽位，引读按「外层 binder 在前」：
    assert_eq!(
        nf("\\x y. _"),
        "λ x y. ?3 x y\n  :\n(x : ?0)(y : ?1 x) → ?2 x y\n"
    );
    // 阴影 binder 换 fresh 名后实参顺序仍是外层在前：
    assert_eq!(
        nf("\\x x. _"),
        "λ x x'. ?3 x x'\n  :\n(x : ?0)(x' : ?1 x) → ?2 x x'\n"
    );
    // 生成名 x1/x2 与用户 binder 同名也不冲突（binder 名只在 pretty 里 fresh）：
    assert_eq!(
        nf("let f : U -> U -> U = \\x1 x2. _; f"),
        "λ x1 x2. ?0 x1 x2\n  :\nU → U → U\n"
    );
    assert_parity("\\x y. _");
    assert_parity("\\x x. _");
    assert_parity("let f : U -> U -> U = \\x1 x2. _; f");
}

#[test]
fn parens_around_hole_are_transparent() {
    assert_eq!(nf("((((_))))"), nf("_"));
    assert_eq!(ty("((((_))))"), "?0\n");
    assert_parity("((((_))))");
}

#[test]
fn let_context_shared_by_two_holes() {
    // 前一个洞在 check 位置（一个 meta），后一个在 infer 位置（一对）。
    let src = "let x : U = U; let y : U = _; _";
    assert_eq!(nf(src), "?2\n  :\n?1\n");
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\
         let ?1 = ?;\n\
         let ?2 = ?;\n\n\
         let x : U\n  = U;\n\n\
         let y : U\n  = ?0;\n\n\
         ?2\n"
    );
    assert_parity(src);
}

#[test]
fn hole_skips_let_defined_slot_in_spine() {
    // Defined 槽位不进洞的实参 spine：`λ y. ?2 y`（x 被跳过）。
    let src = "let x : U = U; \\y. _";
    assert_eq!(nf(src), "λ y. ?2 y\n  :\n(y : ?0) → ?1 y\n");
    assert_parity(src);

    // 洞应用 binder 时 Defined 槽位同样跳过；dom 洞解为常数函数
    //（?3 := λ x1. ?0：`?3 y ≡ ?0` 的反解）。
    let src2 = "let x : U = U; \\y. _ y";
    assert_eq!(nf(src2), "λ y. ?2 y y\n  :\n(y : ?0) → ?4 y y\n");
    assert_eq!(
        elab(src2),
        "let ?0 = ?;\n\
         let ?1 = λ x1. (x : ?0) → ?4 x1 x;\n\
         let ?2 = ?;\n\
         let ?3 = λ x1. ?0;\n\
         let ?4 = ?;\n\n\
         let x : U\n  = U;\n\n\
         λ y. ?2 y y\n"
    );
    assert_parity(src2);
}

#[test]
fn hole_in_pi_cod_renders_with_bound_args() {
    assert_eq!(
        nf("(A : U) -> (x : A) -> _"),
        "(A : U)(x : A) → ?0 A x\n  :\nU\n"
    );
    assert_eq!(nf("(A : U) -> _ -> A"), "(A : U) → ?0 A → A\n  :\nU\n");
    assert_parity("(A : U) -> (x : A) -> _");
    assert_parity("(A : U) -> _ -> A");
}

#[test]
fn annotation_hole_solves_to_pi() {
    // `f : _` 的洞与 λ 的合成 Π 合一 → ?0 := (x : ?1) → ?1。
    let src = "let f : _ = \\x. x; f";
    assert_eq!(nf(src), "λ x. x\n  :\n(x : ?1) → ?1\n");
    assert_eq!(
        elab(src),
        "let ?0 = (x : ?1) → ?1;\n\
         let ?1 = ?;\n\n\
         let f : ?0\n  = λ x. x;\n\n\
         f\n"
    );
    assert_parity(src);
}

#[test]
fn solved_annotation_hole_reused_by_second_let() {
    // 已解的 `?2`（g 的类型洞）在 f 的 dom/cod 两侧复用；
    // cod 侧的 ?3 解为「忽略实参、返回 ?2」的常数（g 的 cod 本就与实参无关）。
    let src = "let g : _ = \\a. a; let f : _ -> _ = \\x. g x; f";
    assert_eq!(nf(src), "λ x. x\n  :\n?2 → ?2\n");
    assert_eq!(
        elab(src),
        "let ?0 = (a : ?2) → ?2;\n\
         let ?1 = ?2;\n\
         let ?2 = ?;\n\
         let ?3 = λ x1. ?2;\n\n\
         let g : ?0\n  = λ a. a;\n\n\
         let f : ?2 → ?3 _\n  = λ x. g x;\n\n\
         f\n"
    );
    assert_parity(src);
}

#[test]
fn hole_multi_binder_body_golden() {
    let src = "let f : (A : U) -> (B : U) -> A -> B -> A = \\A B x y. _; f";
    assert_eq!(
        nf(src),
        "λ A B x y. ?0 A B x y\n  :\n(A : U)(B : U) → A → B → A\n"
    );
    assert_eq!(
        elab(src),
        "let ?0 = ?;\n\n\
         let f : (A : U)(B : U) → A → B → A\n  = λ A B x y. ?0 A B x y;\n\n\
         f\n"
    );
    assert_parity(src);
}

#[test]
fn eta_shaped_hole_applied_to_binder_is_non_pattern() {
    // `\x. _ x` 在 U → U 注解下：洞作为函数头，其余定义域 meta 抽象
    // [实参, binder] 得 `?m x x`——同变量 spine 非模式 → Cannot unify。
    // 上游 03-holes 同款（RApp 的 cod meta 绑定 "x" + vAppBDs）；
    // L04 pruning 之后才接受。
    let src = "let f : U -> U = \\x. _ x; f";
    assert_error_at(src, 1, 22, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("?3 x x"), "{out}");
}

#[test]
fn cod_hole_solved_by_body() {
    // 余定义域洞被 λ 体解成常数：?0 := λ x1. U。
    let src = "let f : (x : U) -> _ = \\x. x; f";
    assert_eq!(nf(src), "λ x. x\n  :\n(x : U) → U\n");
    assert_eq!(
        elab(src),
        "let ?0 = λ x1. U;\n\n\
         let f : (x : U) → ?0 x\n  = λ x. x;\n\n\
         f\n"
    );
    assert_parity(src);

    // 体经 let（Defined 槽位）中转同样解出。
    let src2 = "let f : (x : U) -> _ = \\x. let y : U = x; y; f";
    assert_eq!(nf(src2), "λ x. x\n  :\n(x : U) → U\n");
    assert_eq!(
        elab(src2),
        "let ?0 = λ x1. U;\n\n\
         let f : (x : U) → ?0 x\n  = λ x. let y : U\n  = x;\n\ny;\n\n\
         f\n"
    );
    assert_parity(src2);
}

#[test]
fn cod_hole_projects_argument() {
    // 体是 binder 时解为投影：`?0 x y ≡ U` ⟹ ?0 := λ x1 x2. U（常数 U——
    // 洞在 cod **类型**位置，body x : U 提供的是 U 而非 x）。
    let src = "let f : (x : U) -> (y : U) -> _ = \\x y. x; f";
    assert_eq!(nf(src), "λ x y. x\n  :\n(x : U)(y : U) → U\n");
    assert_eq!(
        elab(src),
        "let ?0 = λ x1 x2. U;\n\n\
         let f : (x : U)(y : U) → ?0 x y\n  = λ x y. x;\n\n\
         f\n"
    );
    assert_parity(src);

    // 三 binder 版本。
    let src2 = "let f : (x : U) -> (y : U) -> (z : U) -> _ = \\x y z. z; f";
    assert_eq!(nf(src2), "λ x y z. z\n  :\n(x : U)(y : U)(z : U) → U\n");
    assert!(elab(src2).starts_with("let ?0 = λ x1 x2 x3. U;\n"), "{}", elab(src2));
    assert_parity(src2);
}

#[test]
fn two_type_holes_solved_by_arguments() {
    // `f _ _ U U`：两个类型洞都被实参检查解成 U。
    let src = "let f : (A : U) -> (B : U) -> (x : A) -> (y : B) -> A = \\A B x y. x;\n\
               let p : _ = f _ _ U U; p";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\n\
         let ?1 = U;\n\
         let ?2 = U;\n\n\
         let f : (A : U)(B : U)(x : A)(y : B) → A\n  = λ A B x y. x;\n\n\
         let p : ?0\n  = f ?1 ?2 U U;\n\n\
         p\n"
    );
    assert_parity(src);
}

#[test]
fn id_hole_solved_to_u_and_unsolved_value_hole() {
    let src = "let id : (A : U) -> A -> A = \\A x. x; id _ U";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert!(elab(src).starts_with("let ?0 = U;\n"), "{}", elab(src));
    assert_parity(src);

    // 反过来 `id U _`：类型实参直接给 U，值洞无人约束 → 保持未解。
    let src2 = "let id : (A : U) -> A -> A = \\A x. x; id U _";
    assert_eq!(nf(src2), "?0\n  :\nU\n");
    assert_eq!(ty(src2), "U\n");
    assert_parity(src2);
}

#[test]
fn dependent_type_holes_solved_pairwise() {
    let src = "let f : (A : U) -> (x : A) -> A = \\A x. x;\n\
               let y : _ = f _ U; y";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\n\
         let ?1 = U;\n\n\
         let f : (A : U)(x : A) → A\n  = λ A x. x;\n\n\
         let y : ?0\n  = f ?1 U;\n\n\
         y\n"
    );
    assert_parity(src);
}

#[test]
fn chained_app_solves_cod_meta_to_pi() {
    // `id _ _ U`：第二个洞 check 进 ?0；第三次应用对 ?0 合成 Π
    //（dom 洞 ?2 随后被实参 U 解掉），项 nf 是 `?1 U`。
    let src = "let id : (A : U) -> A -> A = \\A x. x; id _ _ U";
    assert_eq!(nf(src), "?1 U\n  :\n?3 U\n");
    assert_eq!(
        elab(src),
        "let ?0 = (x : U) → ?3 x;\n\
         let ?1 = ?;\n\
         let ?2 = U;\n\
         let ?3 = ?;\n\n\
         let id : (A : U) → A → A\n  = λ A x. x;\n\n\
         id ?0 ?1 U\n"
    );
    assert_parity(src);
}

#[test]
fn dup_forcing_with_hole_arg() {
    // 复制强制 × 记忆化与洞共存：`g (f U) (f U)` 的两处 `?0 U` 同句柄。
    let src = "let d : (A : U) -> A -> (A -> A -> A) -> A = \\A x g. g x x;\n\
               let f : (A : U) -> A = \\A. _;\n\
               d U (f U) (\\a b. a)";
    assert_eq!(nf(src), "?0 U\n  :\nU\n");
    assert_parity(src);
}

#[test]
fn nested_double_hole_solved_to_projection() {
    // 两个同形洞都解成「取第一个实参」：`id _ x` 的方程是 `?m A x ≡ A`
    //（check 的是 x : A），所以解是 λ x1 x2. x1 而非 x2——与上游 ex0 注释
    // `?α := λ A x. A` 一致。
    let src = "let id : (A : U) -> A -> A = \\A x. x;\n\
               let id2 : (A : U) -> A -> A = \\A x. id _ (id _ x);\n\
               id2";
    assert_eq!(nf(src), "λ A x. x\n  :\n(A : U) → A → A\n");
    assert_eq!(
        elab(src),
        "let ?0 = λ x1 x2. x1;\n\
         let ?1 = λ x1 x2. x1;\n\n\
         let id : (A : U) → A → A\n  = λ A x. x;\n\n\
         let id2 : (A : U) → A → A\n  = λ A x. id (?0 A x) (id (?1 A x) x);\n\n\
         id2\n"
    );
    assert_parity(src);
}

#[test]
fn small_solve_battery_full_golden() {
    // `Eq _ p0 p0 = refl _ _`：三洞全解的金样（nf/type/elab 三模式）。
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let p0 : Nat = \\N s z. s z;\n\
               let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
               let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
               let eqTest : Eq _ p0 p0 = refl _ _;\n\
               eqTest";
    let ch = church_tm(1);
    let expected_ty = format!("(P : ({nat}) → U) → P ({ch}) → P ({ch})\n", nat = nat_type());
    assert_eq!(nf(src), format!("λ P px. px\n  :\n{expected_ty}"));
    assert_eq!(ty(src), expected_ty);
    assert_eq!(
        elab(src),
        "let ?0 = (N : U) → (N → N) → N → N;\n\
         let ?1 = (N : U) → (N → N) → N → N;\n\
         let ?2 = λ x1 x2 x3. x2 x3;\n\n\
         let Nat : U\n  = (N : U) → (N → N) → N → N;\n\n\
         let p0 : Nat\n  = λ N s z. s z;\n\n\
         let Eq : (A : U) → A → A → U\n  = λ A x y. (P : A → U) → P x → P y;\n\n\
         let refl : (A : U)(x : A) → Eq A x x\n  = λ A x P px. px;\n\n\
         let eqTest : Eq ?0 p0 p0\n  = refl ?1 ?2;\n\n\
         eqTest\n"
    );
    assert_parity(src);
}

#[test]
fn solve_through_let_defined_function() {
    // 洞的 rhs 经 let 定义的函数（Defined 槽位）彻底 β 展开：解是 church 2。
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
               let p0 : Nat = \\N s z. s z;\n\
               let lift : Nat -> Nat = \\n. add n p0;\n\
               let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
               let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
               let eqTest : Eq _ (lift p0) (lift p0) = refl _ _;\n\
               eqTest";
    let ch = church_tm(2);
    assert_eq!(
        nf(src),
        format!("λ P px. px\n  :\n(P : ({nat}) → U) → P ({ch}) → P ({ch})\n", nat = nat_type())
    );
    // 解 ?2 的引读走 lift p0 的完整展开（定义不进解，值已展开）。
    let e = elab(src);
    assert!(e.starts_with("let ?0 = (N : U) → (N → N) → N → N;\nlet ?1 = (N : U) → (N → N) → N → N;\nlet ?2 = λ x1 x2 x3. x2 (x2 x3);\n"), "{e}");
    assert!(e.contains("let eqTest : Eq ?0 (lift p0) (lift p0)\n  = refl ?1 ?2;"), "{e}");
    assert_parity(src);
}

#[test]
fn conv_hole_predicate_solved_by_unify() {
    // `Eq _ (add p0 p0) p1`：类型洞在 check 两实参时被解成 Nat，
    // refl 的值洞解为 church 2（add p0 p0 ≡ p1 的完整展开）。
    let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
               let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
               let p0 : Nat = \\N s z. s z;\n\
               let p1 : Nat = add p0 p0;\n\
               let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
               let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
               let eqT : Eq _ (add p0 p0) p1 = refl _ _;\n\
               eqT";
    let ch = church_tm(2);
    assert_eq!(
        nf(src),
        format!("λ P px. px\n  :\n(P : ({nat}) → U) → P ({ch}) → P ({ch})\n", nat = nat_type())
    );
    assert_parity(src);
}

// 非模式解限制的钉子（readme「已知限制」；上游一致，L04 pruning 才改变）
// --------------------------------------------------------------------------------

#[test]
fn non_pattern_same_var_spine_documented() {
    // `\x. _ x x`：cod meta 抽象 [实参, binder] 得 `?m x x`——同变量双实参
    // 非模式，invert 必败 → Cannot unify（readme 明文记载，与上游一致）。
    let src = "let t : (x : U) -> U = \\x. _ x x; t";
    assert_error_at(src, 1, 28, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("(x' : ?4 x) → ?5 x x'"), "{out}");
    assert!(out.contains("?3 x x"), "{out}");
}

#[test]
fn non_pattern_non_var_spine_arg_documented() {
    // `let x : U = U; _ x x`：第二次应用对 `?3 U` 求解——实参 U 不是
    // rigid 变量 → 非模式 → Cannot unify。
    let src = "let x : U = U; _ x x";
    assert_error_at(src, 1, 16, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("(x' : ?4) → ?5 x'"), "{out}");
    assert!(out.contains("?3 U"), "{out}");
}

#[test]
fn non_pattern_hole_through_defined_function() {
    // `f x` 的类型是 x 本身（f 的 cod 就是 A）：与 U 的合一不含洞，
    // 刚性失配（洞已被 A[x:=x] 消掉）。
    let src = "let f : (A : U) -> A = \\A. _;\n\
               let t : (x : U) -> U = \\x. f x;\n\
               t U";
    assert_error_at(src, 2, 28, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("with inferred type\n\n  x\n"), "{out}");
}

#[test]
fn non_pattern_cod_hole_with_u_arg_documented() {
    // `g U` 的 cod 洞带非变量实参 U：`?1 U ≡ U` 解不了（pruning 是 L04 的事）。
    let src = "let g : (w : U) -> _ = \\w. _;\n\
               let h : (w : U) -> g w -> g U -> U = \\w x y. y;\n\
               h";
    assert_error_at(src, 2, 46, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("with inferred type\n\n  ?1 U\n"), "{out}");
}

#[test]
fn same_meta_two_spines_with_defined_binders_accepted() {
    // `k w a b`：g 的 cod 洞在 y : g w 的检查处被解（实参 w 是变量，可解）；
    // 随后 g w 与 g w 的 flex-flex 同号比较逐实参通过（v1「cod 双求值」的
    // Defined 槽位变体）。
    let src = "let g : (w : U) -> _ = \\w. _;\n\
               let k : (w : U) -> g w -> g w -> U = \\w x y. y;\n\
               let bad : (w : U) -> U -> g w -> g w -> U = \\w a b c. k w a b;\n\
               bad";
    assert_eq!(
        nf(src),
        "λ w a b c. b\n  :\n(w : U) → U → U → U → U\n"
    );
    assert_eq!(
        elab(src),
        "let ?0 = λ x1. U;\n\
         let ?1 = λ x1. U;\n\n\
         let g : (w : U) → ?0 w\n  = λ w. ?1 w;\n\n\
         let k : (w : U) → g w → g w → U\n  = λ w x y. y;\n\n\
         let bad : (w : U) → U → g w → g w → U\n  = λ w a b c. k w a b;\n\n\
         bad\n"
    );
    assert_parity(src);
}

// η 与洞（二元变体；v1 只钉了一元形态）
// --------------------------------------------------------------------------------

/// η 双参吸收：`P h` vs `P (\x z. h x z)`（h 是 lambda-bound 变量，两次
/// η 展开后同头 spine 对齐）。v1 的一元形态（`P (h y)` vs `P (\x. h y x)`）
/// 已钉；这里是 2-arg 版本，专门打 unify 工作表的连续 η 步。
const ETA_2ARG_SRC: &str = "\
let big : (P : ((U -> U -> U) -> U -> U) -> U) -> (h : (U -> U -> U) -> U -> U)
       -> (v : P h) -> (f : P (\\x z. h x z) -> U) -> U
      = \\P h v f. f v;
big
";

/// meta 实参短侧的二元变体：`P _` vs `P (\x z. h x z)`——η 把两个 fresh
/// 实参积到未解 flex 的 spine 上再转求解（readme「优化教训 2」的 2-arg 版）。
const META_SHORT_2ARG_SRC: &str = "\
let big : (P : ((U -> U -> U) -> U -> U) -> U) -> (h : (U -> U -> U) -> U -> U)
       -> (v : P h) -> (f : P _ -> U) -> U
      = \\P h v f. f v;
big
";

#[test]
fn unify_eta_absorption_two_arg() {
    let out = ty(ETA_2ARG_SRC);
    assert!(!out.contains("Cannot unify"), "二元 η 等价不应被拒：\n{out}");
    assert_parity(ETA_2ARG_SRC);
}

#[test]
fn unify_meta_short_side_two_arg() {
    let out = ty(META_SHORT_2ARG_SRC);
    assert!(!out.contains("Cannot unify"), "meta 短侧二元求解不应被拒：\n{out}");
    // 短侧洞解为 h（解按应用序摔上去后 f 的类型显示实例化形态）。
    assert!(out.contains("(f : P"), "f 的类型应出现在 P 应用形态下：\n{out}");
    assert_parity(META_SHORT_2ARG_SRC);
}

#[test]
fn solve_before_failure_visible_in_message() {
    // 同头 spine 实参比较次序的哨兵：v : P m x 对 w : P a b 的检查里，
    // 第一对实参 m↔a 触发求解（?m := 投影 a 的 λ），第二对 x↔b 失败——
    // 错误消息里 expected 侧显示**已解**形态 `P a x`。参考版 unify_sp
    // 与快版受控内联环的派发序在此必须一致（快版「先压本层实参对、
    // 后压函数部分对」的 LIFO 弹序 = 应用序）。两边逐字节一致即通过。
    let src = "\
let test : (P : U -> U -> U) -> (a : U) -> (b : U) -> (x : U) -> U
  = \\P a b x.
      let m : U = _;
      let w : P a b = _;
      let v : P m x = w;
      v;
test";
    let expected = "\
(stdin):5:23:
  |
5 |       let v : P m x = w;
  |                       ^
Cannot unify expected type

  P a x

with inferred type

  P a b
";
    assert_eq!(nf(src), expected);
    assert_eq!(nf(src), fast_nf(src));
    assert_eq!(ty(src), fast::main_with("type", src));
    assert_eq!(elab(src), fast::main_with("elab", src));
}

// 渲染边角
// --------------------------------------------------------------------------------

#[test]
fn shadowed_let_binder_rendering() {
    // 同名 binder 阴影：elab 里 let 名换 x'，洞实参是外层 x（Bound 槽位）。
    let src = "\\x. let x : U = x; _";
    assert_eq!(nf(src), "λ x. ?2 x\n  :\n(x : U) → ?1 x\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\n\
         let ?1 = ?;\n\
         let ?2 = ?;\n\n\
         λ x. let x' : U\n  = x;\n\n?2 x\n"
    );
    assert_parity(src);
}

#[test]
fn nested_shadowed_binder_hole_args_are_values() {
    // `(\x. _ x) x`：内层洞的实参是内层 binder，β 后三个实参同为 x 的值；
    // elab 保留未归约形态（内层 binder 换名 x'）。
    let src = "\\x. (\\x. _ x) x";
    assert_eq!(nf(src), "λ x. ?3 x x x\n  :\n(x : ?0) → ?5 x x x\n");
    let e = elab(src);
    assert!(e.contains("λ x. (λ x'. ?3 x x' x') x"), "{e}");
    assert_parity(src);
}

#[test]
fn two_anonymous_hole_doms_render() {
    let src = "(A : _) -> (B : _) -> A -> B -> A";
    assert_eq!(nf(src), "(A : U)(B : U) → A → B → A\n  :\nU\n");
    assert_eq!(
        elab(src),
        "let ?0 = U;\n\
         let ?1 = λ x1. U;\n\n\
         (A : ?0)(B : ?1 A) → A → B → A\n"
    );
    assert_parity(src);
}

#[test]
fn pi_cod_let_with_hole_is_parenthesized() {
    let src = "(x : U) -> let y : U = x; _";
    assert_eq!(nf(src), "(x : U) → ?0 x\n  :\nU\n");
    let e = elab(src);
    assert!(e.contains("(x : U) → (let y : U\n  = x;\n\n?0 x)"), "{e}");
    assert_parity(src);
}

#[test]
fn underscore_let_binder_cannot_be_referenced() {
    // `_` 作 let binder 只是匿名名字；体里的 `_` 是**新洞**（与上游一致：
    // `_` 在项位置恒为 hole），所以 `let _ : U -> U = \x. x; _ U` 的体是
    // 「洞应用于 U」而非引用该 let。
    let src = "let _ : U -> U = \\x. x; _ U";
    assert_eq!(nf(src), "?1 U\n  :\n?3 U\n");
    let e = elab(src);
    assert!(e.contains("let _ : U → U\n  = λ x. x;"), "{e}");
    assert!(e.ends_with("?1 U\n"), "{e}");
    assert_parity(src);
}

#[test]
fn underscore_adjacent_binders_split_lexically() {
    // `\_x. x`：`_x` 切成两个 binder（`_` 与 `x`）——词法层面 `_` 恒单独
    // 成 token（与 L02 同款），不是「名为 _x 的 binder」。
    let src = "\\_x. x";
    assert_eq!(nf(src), "λ _ x. x\n  :\n?0 → (x : ?1 _) → ?1 _\n");
    assert_eq!(nf("λ_x. x"), nf(src));
    assert_parity(src);
}

#[test]
fn unicode_identifiers_are_idents() {
    let src = "let α : U = U; α";
    assert_eq!(nf(src), "U\n  :\nU\n");
    assert_eq!(
        elab(src),
        "\nlet α : U\n  = U;\n\nα\n"
    );
    assert_parity(src);
}

#[test]
fn tab_prefix_is_whitespace() {
    assert_eq!(nf("\tU"), "U\n  :\nU\n");
    assert_parity("\tU");
}

#[test]
fn question_mark_is_not_surface_syntax() {
    // L03 的 hole 只有 `_`；`?` 是 Op/Err token：作为唯一内容时 parse
    // error，作尾随 junk 时被吞掉（与 v1 的尾随 junk 怪癖一致）。
    for src in ["let x : U = U; ?", "?"] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_eq!(elab(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
    // `_ ? _`：`?` 之后 p_spine 已完整，`? _` 整段是尾随 junk → 等价 `_`。
    assert_eq!(nf("_ ? _"), nf("_"));
    assert_parity("_ ? _");
}

// 错误路径（位置 / 消息 / 不挂死）
// --------------------------------------------------------------------------------

#[test]
fn unbound_in_hole_application_positions() {
    // 错误落在洞的实参上（洞是合法头，先于实参 elaborat 的位置报 y）。
    assert_error_at("let f : U -> U = \\x. _ y; f", 1, 24, "Name not in scope: y");
    assert_error_at("let f : U = _ z; f", 1, 15, "Name not in scope: z");
    assert_error_at("_ x", 1, 3, "Name not in scope: x");
}

#[test]
fn let_is_not_recursive() {
    assert_error_at("let f : U -> U = \\x. f x; f", 1, 22, "Name not in scope: f");
}

#[test]
fn error_positions_multiline_and_crlf() {
    // 第三行 caret。
    let src = "let a : U = U;\nlet b : U = U;\nlet c : U = q;\nc";
    let out = nf(src);
    assert!(out.starts_with("(stdin):3:13:\n"), "{out}");
    assert!(out.contains("3 | let c : U = q;\n  |             ^"), "{out}");
    assert_parity(src);

    // CRLF：\r 不进摘录、不影响列号。
    let src = "let x : U = U;\r\nlet y : U = z;\r\ny";
    let out = nf(src);
    assert!(out.starts_with("(stdin):2:13:\n"), "{out}");
    assert!(out.contains("2 | let y : U = z;\n  |             ^"), "{out}");
    assert!(!out.contains('\r'), "\\r 不应出现在错误摘录里：{out}");
    assert_parity(src);

    // 首行 CRLF 结尾的错误：列按字节算，\r 在 caret 之后不影响。
    let src = "U U\r\n";
    let out = nf(src);
    assert!(out.starts_with("(stdin):1:1:\n"), "{out}");
    assert!(out.contains("1 | U U\n"), "{out}");
    assert_parity(src);
}

#[test]
fn hole_applied_inside_lambda_application_chain() {
    // `(\y. _ y) x`：内层洞的 cod meta 抽象 [y, x]，β 后三个实参同为 x
    // 的值，类型 `?5 x x x` 全程未解；elab 保留未归约形态。
    let src = "\\x. (\\y. _ y) x";
    assert_eq!(nf(src), "λ x. ?3 x x x\n  :\n(x : ?0) → ?5 x x x\n");
    let e = elab(src);
    assert!(e.contains("λ x. (λ y. ?3 x y y) x"), "{e}");
    assert_parity(src);
}

#[test]
fn hole_under_hole_application() {
    let src = "\\x. _ (_ x)";
    assert_eq!(nf(src), "λ x. ?2 x (?6 x x)\n  :\n(x : ?0) → ?4 x (?6 x x)\n");
    let e = elab(src);
    assert!(e.contains("let ?1 = λ x1. (x : ?8 x1 x1) → ?4 x1 x;"), "{e}");
    assert!(e.contains("let ?3 = λ x1. ?8 x1 x1;"), "{e}");
    assert_parity(src);
}

#[test]
fn mixed_bound_defined_slots_error_shape() {
    // `\w. \x. let y : U = w; _ x y w`：洞作头应用三实参，cod meta 抽象
    // [x', x, w]（y 是 Defined 跳过）；第二参 y 的值 = w 与 x' 实参配对后
    // 出现 `?5 w x x`——同变量双实参非模式 → Cannot unify。
    let src = "\\w. \\x. let y : U = w; _ x y w";
    assert_error_at(src, 1, 24, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("(x' : ?6 w x) → ?7 w x x'"), "{out}");
    assert!(out.contains("?5 w x x"), "{out}");
}

#[test]
fn pi_dom_hole_applied_to_binder_is_non_pattern() {
    // `(x : _ A) -> x`：dom 位置的 `_ A` 是「洞作头」应用，其合成类型是
    // cod meta 应用到 [实参, A, x]——check 对 U 的合一撞上重复变量。
    // 上游同款行为（非模式限制），钉住防漂移。
    let src = "(A : U) -> (x : _ A) -> x";
    assert_error_at(src, 1, 17, "Cannot unify expected type");
    let out = nf(src);
    assert!(out.contains("?3 A A"), "{out}");
}

// 解析残缺 battery（parse error + 不挂死 + parity）
// --------------------------------------------------------------------------------

#[test]
fn malformed_parse_battery_no_hang() {
    for src in [
        "_",          // 合法：单洞（进这里对照「只有 _」不是 parse error）
        "(_",         // 括号残缺
        "let _",      // let 截断
        "let _ : _ = _;", // let 缺体
        "\\_.",       // λ 缺体
        "\\x",        // λ 缺点与体
        "\\x.",       // λ 缺体
        "\\x. .",     // 体位置是点
        "\\x..",
        "-> U",       // 箭头无左部
        "U ->",       // 箭头后无物（尾随 junk 吞掉 → U，见下）
        ": U",
        "let x",      // let 截断
        "((",         // 括号不平衡
        ")))",
        "(()",
        "())",
        "{-",         // 未闭合块注释
        "--",         // 只有行注释
        "let x : U = _;", // let 缺体
        "let let : U = U; U", // 关键字作 binder
        "λ",          // 裸 λ
        "λx",
        "λ.",
        "U : U",      // `:` 尾随 junk（→ U）
        "let x : U = U; ; U", // 双分号
        "let x : U = U; U;",  // 尾分号 junk（→ U）
        "_x. x",      // `_`+`x` 两 token 的应用，x 未绑定 → 名字错误
        "\\1. x",     // 数字 binder
        "\\x.x",      // 无空格体（合法）
        "\\_. _",     // 匿名 binder + 洞体（合法）
        "((U : U))",  // junk 只在顶层被吞；括号内 `:` 后必须紧跟 `)` → parse error
        "((U : U) -> U",  // 括号残缺
        "(U : U) -> U",   // v1 已钉 parse error
    ] {
        assert_terminates(src);
    }
    // 其中确定是 parse error 的子集：
    for src in [
        "(", "(_", "let _", "let _ : _ = _;", "\\_.", "\\x", "\\x.", "\\x. .", "\\x..",
        "-> U", ": U", "let x", "((", ")))", "(()", "())", "{-", "--",
        "let x : U = _;", "let let : U = U; U", "λ", "λx", "λ.",
        "let x : U = U; ; U", "(U : U) -> U", "((U : U) -> U", "\\1. x", "((U : U))",
        "\\_._",      // `._` 被 op 字符类贪婪吃成一个 Op token（readme 记载的
                      // `_.` 同类；`\` 与 `_` 特判只覆盖这两字符自身）
    ] {
        assert_eq!(nf(src), "parse error\n", "src: {src:?}");
        assert_eq!(ty(src), "parse error\n", "src: {src:?}");
        assert_eq!(elab(src), "parse error\n", "src: {src:?}");
        assert_parity(src);
    }
    // 尾随 junk 吞掉后合法的子集（与 v1 的 trailing_junk 一致的行为面）：
    for src in ["U ->", "U : U", "let x : U = U; U;", "_", "\\x.x"] {
        assert_terminates(src);
        assert_parity(src);
    }
    assert_eq!(nf("U ->"), "U\n  :\nU\n");
    assert_eq!(nf("\\x.x"), "λ x. x\n  :\n(x : ?0) → ?0\n");
    assert_eq!(nf("\\_. _"), "λ _. ?2 _\n  :\n?0 → ?1 _\n");
    // `_x. x`：`_ x` 是洞应用未绑定名。
    assert_error_at("_x. x", 1, 2, "Name not in scope: x");
}

// parity 扫描（本套件金样之外的整体互检）
// --------------------------------------------------------------------------------

#[test]
fn parity_scan_battery_v2() {
    for src in [
        "_",
        "_ _",
        "_ _ _",
        "\\x y. _",
        "\\x y z w. _ w z y x",
        "\\x x. _",
        "((((_))))",
        "let x : U = U; \\y. _",
        "let x : U = U; \\y. _ y",
        "let x : U = U; let y : U = _; _",
        "\\x. let y : U = x; _",
        "\\x. let y : U = _; y x",
        "(A : U) -> (x : A) -> _",
        "(A : U) -> _ -> A",
        "(A : _) -> (B : _) -> A -> B -> A",
        "(x : U) -> let y : U = x; _",
        "let f : _ = \\x. x; f",
        "let g : _ = \\a. a; let f : _ -> _ = \\x. g x; f",
        "let f : U -> U = \\x. _ x; f",
        "let f : U -> U -> U = \\x y. _ y; f",
        "let f : (x : U) -> _ = \\x. x; f",
        "let f : (x : U) -> (y : U) -> _ = \\x y. x; f",
        "let f : (A : U) -> (B : U) -> (x : A) -> (y : B) -> A = \\A B x y. x;\nlet p : _ = f _ _ U U; p",
        "let id : (A : U) -> A -> A = \\A x. x; id _ U",
        "let id : (A : U) -> A -> A = \\A x. x; id U _",
        "let id : (A : U) -> A -> A = \\A x. x; id _ _ U",
        "let id : (A : U) -> A -> A = \\A x. x;\nlet id2 : (A : U) -> A -> A = \\A x. id _ (id _ x);\nid2",
        "let f : (A : U) -> A = \\A. _;\nlet t : (x : U) -> U = \\x. f x;\nt U",
        "let g : (w : U) -> _ = \\w. _;\nlet h : (w : U) -> g w -> g U -> U = \\w x y. y;\nh",
        "let g : (w : U) -> _ = \\w. _;\nlet k : (w : U) -> g w -> g w -> U = \\w x y. y;\nlet bad : (w : U) -> U -> g w -> g w -> U = \\w a b c. k w a b;\nbad",
        "\\x. (\\x. _ x) x",
        "\\x. (\\y. _ y) x",
        "\\x. _ (_ x)",
        "\\w. \\x. let y : U = w; _ x y w",
        "let x : U = U; _ x x",
        "let t : (x : U) -> U = \\x. _ x x; t",
        "let f : U -> U = \\x. f x; f",
        "let _ : U -> U = \\x. x; _ U",
        "\\_x. x",
        "λ_x. x",
        "let α : U = U; α",
        "\tU",
        "let f : U = _ z; f",
        "let a : U = U;\nlet b : U = U;\nlet c : U = q;\nc",
        "let x : U = U;\r\nlet y : U = z;\r\ny",
        "U U\r\n",
        L03_holes::EX0_SRC,
        L03_holes::EX1_SRC,
        L03_holes::EX2_SRC,
    ] {
        assert_parity(src);
    }
}

// 压力与深度（大栈线程；小栈上深括号会 abort 进程——见文件头「已知包络」）
// --------------------------------------------------------------------------------

#[test]
fn deep_parens_do_not_break_on_big_stack() {
    with_big_stack(|| {
        for depth in [400usize, 1000, 5000] {
            let src = format!("{}U{}", "(".repeat(depth), ")".repeat(depth));
            let b = nf(&src);
            assert_eq!(b, "U\n  :\nU\n", "depth {depth}");
            assert_eq!(b, fast_nf(&src), "depth {depth}");
            let src = format!("{}{}", "(".repeat(depth), "_".to_string() + &")".repeat(depth));
            let b = nf(&src);
            assert_eq!(b, "?1\n  :\n?0\n", "depth {depth} (洞版)");
            assert_eq!(b, fast_nf(&src), "depth {depth} (洞版)");
        }
    });
}

#[test]
fn deep_binders_with_hole() {
    with_big_stack(|| {
        // n=60：参考版参与互检。注意参考版在「未解洞 + 深 binder」下
        // infer 的 closeVal 逐层 re-quote 是超线性 blowup（实测 n=100 →
        // ~5s、n=200 → ~87s，约 O(n³⁺)，快版同规模 <1s）——这是上游
        // `closeVal = quote (lvl+1)` 逐层结构的忠实移植代价，属参考版
        // 性能包络（非正确性 bug，v2 首次量化），故大 n 只跑快版。
        let n = 60usize;
        let mut names = String::new();
        for i in 0..n {
            names.push_str(&format!("x{i} "));
        }
        let src = format!("\\{}. _", names.trim_end());
        let b = nf(&src);
        assert!(b.starts_with("λ x0 x1 x2"), "{b}");
        for i in 0..n {
            assert!(b.contains(&format!("x{i}")), "缺 x{i}：{b}");
        }
        assert_eq!(b, fast_nf(&src));
        assert_eq!(ty(&src), fast::main_with("type", &src));

        // n=200：仅快版（迭代 quote 深度无上限 + 秒级；参考版 type 口径
        // 在此规模 ~85s，见上注）。
        let mut names = String::new();
        for i in 0..200 {
            names.push_str(&format!("x{i} "));
        }
        let src = format!("\\{}. _", names.trim_end());
        let f = fast_nf(&src);
        assert!(f.starts_with("λ x0 x1 x2"), "{f}");
        for i in 0..200 {
            assert!(f.contains(&format!("x{i}")), "缺 x{i}：{f}");
        }
        // 类型前缀：每个 binder 的 dom 都是「前一 meta 应用于此前全部
        // binder」的 spine 形态（外层在前）。
        let ft = fast::main_with("type", &src);
        assert!(ft.starts_with("(x0 : ?0)(x1 : ?1 x0)(x2 : ?2 x0 x1)"), "{ft}");
        // 稳态：同输入两次输出一致。
        assert_eq!(ft, fast::main_with("type", &src));

        // 洞应用到首尾 binder：与 `\x. _ x` 同族——cod meta 抽象全部 binder
        // 后，实参 x0 与 binder 槽位 x0 重复 → 非模式 → Cannot unify
        //（文档化限制的 200-binder 压力版；两实现一致拒绝，快版口径）。
        let src2 = format!("\\{}. _ x0 x199", names.trim_end());
        let b2 = fast_nf(&src2);
        assert!(b2.starts_with("(stdin):1:893:"), "{b2}");
        assert!(b2.contains("Cannot unify expected type"), "{b2}");
    });
}

#[test]
fn many_holes_chain_on_big_stack() {
    with_big_stack(|| {
        // 200 条 let、每条一个 check 洞：metacontext 200 条，nf 与类型平凡。
        let mut s = String::new();
        for i in 0..200 {
            s.push_str(&format!("let h{i} : U = _; "));
        }
        s.push_str("U");
        let b = nf(&s);
        assert_eq!(b, "U\n  :\nU\n");
        assert_eq!(b, fast_nf(&s));
        let e = elab(&s);
        for i in 0..200 {
            assert!(e.contains(&format!("let h{i} : U\n  = ?{i};")), "缺 h{i}：{e}");
        }
        assert_eq!(e, fast::main_with("elab", &s));
    });
}

#[test]
fn solve_scale_16_full_output() {
    // k=3：p0 = church 2，三次翻倍 → church 16 的 solve 全量输出金样
    //（v1 的深度口径只有前缀断言）。
    with_big_stack(|| {
        let src = L03_holes::bump_spine_iter::solve_src(3);
        let ch = church_tm(16);
        let expected = format!(
            "λ P px. px\n  :\n(P : ((N : U) → (N → N) → N → N) → U) → P ({ch}) → P ({ch})\n"
        );
        assert_eq!(nf(&src), expected);
        assert_eq!(nf(&src), fast_nf(&src));
        // elab：解 ?2 的引读是 16 层 `x2 (… (x2 x3))`。
        fn fold(k: usize) -> String {
            match k {
                0 => "x3".to_string(),
                1 => "x2 x3".to_string(),
                k => format!("x2 ({})", fold(k - 1)),
            }
        }
        let e = elab(&src);
        let expect_sol = format!(
            "let ?0 = (N : U) → (N → N) → N → N;\n\
             let ?1 = (N : U) → (N → N) → N → N;\n\
             let ?2 = λ x1 x2 x3. {};\n\n",
            fold(16)
        );
        assert!(
            e.starts_with(&expect_sol),
            "期望前缀:\n{expect_sol}--- 实际:\n{e}"
        );
        assert_eq!(e, fast::main_with("elab", &src));
    });
}
