//! L07_sum_type 黑盒测试套件 v3（第三轮独立攻击面）。
//!
//! 与 `tests/l07_blackbox.rs`（49 例）和 `tests/l07_blackbox_v2.rs`（53 例）
//! 互补，本套件聚焦其未触及的角落：
//!   - 依赖模式匹配深水区：匹配返回类型依赖已匹配构造子（`T n` 族）、
//!     臂体换行后的嵌套 match、内外双重精化（同一 scrutinee 再 match）、
//!     `add` 型索引算术（Vec 拼接返回 `Vec[A] (add m n)`）、荒谬嵌套模式
//!     同时报「不可达 + 缺构造子」、零臂 match（假前提 = 荒谬消去）、
//!     精化喂给投影、隐式子模式具名绑定 `cons[l](x, xs)`；
//!   - 被通配臂遮蔽的臂**不做任何检查**（类型错误也不报）；
//!   - enum 与隐式交互：跨 enum 构造子名当模式 = 通配（变量模式后备）、
//!     构造子与 enum 同名（裸名被构造子遮蔽）、多索引 GADT、
//!     命名隐式实参 `[A = Nat]`、无标注 enum 隐式参数；
//!   - unification 边界：rigid 头不同、spine 长度不齐、自引用占位 Decl 头、
//!     flex-flex（不同 meta 双向求解）+ 后续可解、卡住投影与 rigid 不证等
//!     （无 Vec 指数 eta 的严格语义）；
//!   - 性能悬崖表征（带超时防护）：深嵌套模式线性下钻、卡住 match 的
//!     多 pending 实参（quote 拼接 O(k)）；
//!   - 解析残缺：截断输入一律 Err 不 panic、match 位置的精确刻画
//!     （单行臂才是解析失败的根因；多行内联 match 在检查位置可用、
//!     在推断位置报 "match cannot be inferred"）、CRLF、非 ASCII；
//!   - parity：参考版 `run` ↔ 孪生版 `run_fast` 对本轮全部新攻击面
//!     逐字节互检（`#[path]` 独立编译，同 l07_fast_parity）。
//!
//! 唯一黑盒入口：`elaboration_zoo_lsp::L07_sum_type::run(input, path_id)
//!   -> Result<String, Error>`。全部在 ≥64MB 栈线程内执行。

use elaboration_zoo_lsp::L07_sum_type::run;

// helpers
// --------------------------------------------------------------------------------

/// 在 64MB 栈线程里跑 `run`；期待成功，失败则 panic 并带出输出/错误。
fn check(src: &str) -> String {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            run(&input, 0).unwrap_or_else(|e| panic!("expected ok, got Err: {e:?}\nsrc:\n{input}"))
        })
        .unwrap()
        .join()
        .unwrap()
}

/// 在 64MB 栈线程里跑 `run`；期待 Err，返回 Debug 文本（`Error("...")`）。
fn check_err(src: &str) -> String {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || match run(&input, 0) {
            Err(e) => format!("{e:?}"),
            Ok(out) => panic!("expected Err, got Ok:\n{out}\nsrc:\n{input}"),
        })
        .unwrap()
        .join()
        .unwrap()
}

/// 在 64MB 栈线程里跑 `run`；返回 panic 消息（若有），Ok/Err 返回 None。
fn check_panic(src: &str) -> Option<String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&input, 0)));
            match r {
                Ok(_) => None,
                Err(payload) => {
                    let msg = payload
                        .downcast_ref::<&str>()
                        .map(|s| s.to_string())
                        .or_else(|| payload.downcast_ref::<String>().cloned())
                        .unwrap_or_else(|| format!("{payload:?}"));
                    Some(msg)
                }
            }
        })
        .unwrap()
        .join()
        .unwrap_or_else(|_| panic!("worker aborted (stack overflow?) for src:\n{src}"))
}

/// 带超时的成功路径：性能悬崖表征用——超时/恐慌时 worker 泄漏但套件存活，
/// panic 信息带出源码供定位。
fn check_timeout(src: &str, secs: u64) -> String {
    let input = src.to_owned();
    let (tx, rx) = std::sync::mpsc::channel::<Result<String, String>>();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let r = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&input, 0)))
            {
                Ok(Ok(out)) => Ok(out),
                Ok(Err(e)) => Err(format!("{e:?}")),
                Err(p) => Err(format!("PANIC {p:?}")),
            };
            let _ = tx.send(r);
        })
        .unwrap();
    match rx.recv_timeout(std::time::Duration::from_secs(secs)) {
        Ok(Ok(out)) => out,
        Ok(Err(m)) => panic!("expected ok, got failure: {m}\nsrc:\n{src}"),
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            panic!("TIMEOUT after {secs}s (性能悬崖?)\nsrc:\n{src}")
        }
        Err(_) => panic!("worker panicked/exited\nsrc:\n{src}"),
    }
}

/// 成功路径 + 逐行精确断言。
fn assert_lines(src: &str, expected: &[&str]) {
    let out = check(src);
    let got: Vec<&str> = out.lines().collect();
    assert_eq!(got, expected, "src:\n{src}\n--- actual ---\n{out}");
}

/// 错误路径 + 消息片段断言。
fn assert_err(src: &str, needle: &str) {
    let msg = check_err(src);
    assert!(msg.contains(needle), "err 缺 {needle:?}:\n{msg}\nsrc:\n{src}");
}

/// 解析失败 → Err 且先排除 panic（截断输入契约：可恢复错误而非崩溃）。
fn assert_parse_err_no_panic(src: &str) {
    if let Some(p) = check_panic(src) {
        panic!("截断输入不应 panic:\n{p}\nsrc:\n{src}");
    }
    let msg = check_err(src);
    assert!(msg.contains("parse error"), "expected parse error, got:\n{msg}\nsrc:\n{src}");
}

// 共享前言
// --------------------------------------------------------------------------------

const NAT: &str = r#"
enum Nat {
    zero
    succ(x: Nat)
}
"#;

const BOOL: &str = r#"
enum Bool {
    true
    false
}
"#;

const VEC: &str = r#"
enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}
"#;

const EQ: &str = r#"
enum Eq[A](x: A, y: A) {
    refl(a: A) -> Eq a a
}
"#;

const ADD: &str = r#"
def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }
"#;

const TWO: &str = "def two = succ (succ zero)\n\ndef three = succ (succ (succ zero))\n";

// --------------------------------------------------------------------------------
// A. 依赖模式匹配深水区
// --------------------------------------------------------------------------------

/// 匹配返回类型依赖已匹配构造子：`T n` 是卡住 match 类族，臂内精化
/// `n := zero` 经 force 重选把 `T n` 归约到具体分支类型。
#[test]
fn v3_match_result_type_depends_on_ctor() {
    assert_lines(
        &format!(
            "{NAT}{BOOL}
def T(n: Nat): U =
    match n {{
        case zero => Bool
        case succ(m) => Nat
    }}

def g(n: Nat): T n =
    match n {{
        case zero => true
        case succ(m) => zero
    }}

println (g zero)
println (g (succ (succ zero)))
"
        ),
        &["Bool::true", "Nat::zero"],
    );
}

/// 臂体写在 `=>` 的下一行（EndLine 可选）→ 嵌套 match 合法；内层 match
/// 精化外层模式变量（`case zero => k`，k 被 `:= zero` 精化）。
#[test]
fn v3_arm_body_next_line_inner_match() {
    assert_lines(
        &format!(
            "{NAT}
def f(x: Nat): Nat =
    match x {{
        case zero => zero
        case succ(k) =>
            match k {{
                case zero => k
                case succ(j) => j
            }}
    }}

println (f zero)
println (f (succ zero))
println (f (succ (succ zero)))
println (f (succ (succ (succ zero))))
"
        ),
        &[
            "Nat::zero",
            "Nat::zero",
            "Nat::zero",
            "Nat::succ(Nat::zero)",
        ],
    );
}

/// 内层 match 的 scrutinee 是**同一个**外层变量：编译期它已被精化成
/// 构造子值，运行时 force 重选命中 succ 臂——双重精化的传播链。
#[test]
fn v3_inner_match_same_scrutinee_reselect() {
    assert_lines(
        &format!(
            "{NAT}
def h(x: Nat): Nat =
    match x {{
        case succ(k) =>
            match x {{
                case succ(k2) => k2
                case zero => zero
            }}
        case zero => zero
    }}

println (h (succ zero))
println (h (succ (succ zero)))
"
        ),
        &["Nat::zero", "Nat::succ(Nat::zero)"],
    );
}

/// `add` 型索引算术：拼接函数返回 `Vec[A] (add m n)`——nil 臂的期望类型
/// `add zero n` 要靠「m := zero 精化 + force 的 Match 重选」归约到 n。
#[test]
fn v3_vec_append_add_index() {
    assert_lines(
        &format!(
            "{NAT}{VEC}{ADD}
def app[A, m: Nat, n: Nat](xs: Vec[A] m, ys: Vec[A] n): Vec[A] (add m n) =
    match xs {{
        case nil => ys
        case cons(x, rest) => cons x (app rest ys)
    }}

def v = app (cons zero nil) (cons (succ zero) nil)

println v
println v.len
"
        ),
        &[
            "Vec::cons([Nat::succ(Nat::zero)] Nat::zero Vec::cons([Nat::zero] Nat::succ(Nat::zero) Vec::nil))",
            "Nat::succ(Nat::succ(Nat::zero))",
        ],
    );
}

/// 荒谬嵌套模式：`Vec[Nat] (succ zero)` 上的 `cons(h, cons(h2, t))`——
/// 外层 cons 可达（l := zero），内层 cons 结构冲突 → 整臂不可达；
/// nil 在该头部类型上同样不可达 → 不计覆盖要求（只报不可达一条）。
#[test]
fn v3_absurd_nested_pattern_both_errors() {
    let msg = check_err(&format!(
        "{NAT}{VEC}
def bad(v: Vec[Nat] (succ zero)): Nat =
    match v {{
        case cons(h, cons(h2, t)) => h2
    }}
"
    ));
    assert!(msg.contains("分支不可达"), "err: {msg}");
    assert!(!msg.contains("缺少构造子"), "nil 在 succ zero 上不可达，不应报缺:\n{msg}");
}

/// 零臂 match 的覆盖报错只列**可达**构造子：`Vec[Nat] (succ zero)` 上
/// nil 不可达不计入，只报缺 cons。
#[test]
fn v3_zero_arms_missing_only_accessible() {
    let msg = check_err(&format!(
        "{NAT}{VEC}
def f(v: Vec[Nat] (succ zero)): Nat =
    match v {{
    }}
"
    ));
    assert!(msg.contains("缺少构造子 cons"), "err: {msg}");
    assert!(!msg.contains("缺少构造子 nil"), "nil 不可达不应报:\n{msg}");
}

/// 索引矛盾前提（`Eq two three`）上唯一的 refl 臂：特化方程 two ≡ three
/// 结构冲突 → 臂不可达；refl 同时不可达 → 不报缺构造子。
#[test]
fn v3_absurd_eq_arm_unreachable() {
    let msg = check_err(&format!(
        "{NAT}{EQ}{TWO}
def bad(e: Eq two three): Nat =
    match e {{
        case refl(a) => zero
    }}
"
    ));
    assert!(msg.contains("分支不可达"), "err: {msg}");
    assert!(!msg.contains("缺少构造子"), "refl 不可达不应报缺:\n{msg}");
}

/// 假前提零臂 match = 荒谬消去：不报错、无输出（探针：覆盖检查对
/// 不可达构造子零要求，臂集为空合法）。
#[test]
fn v3_zero_arms_false_hypothesis_ok() {
    let out = check(&format!(
        "{NAT}{EQ}{TWO}
def f(e: Eq two three): Nat =
    match e {{
    }}
"
    ));
    assert_eq!(out, "");
}

/// scrutinee 是投影（`v.len`）：覆盖检查按投影的**声明类型**（Nat）做——
/// 索引事实（v : Vec[Nat] zero ⇒ v.len ≡ zero）不收窄可达集，所以 succ
/// 臂必须写出（保守但健全；投影不传播索引精化，表征固化）。
#[test]
fn v3_match_scrutinee_projection() {
    assert_lines(
        &format!(
            "{NAT}{VEC}
def f(v: Vec[Nat] zero): Nat =
    match v.len {{
        case zero => zero
        case succ(k) => k
    }}

def g(v: Vec[Nat] (succ zero)): Nat =
    match v.len {{
        case zero => zero
        case succ(k) => succ k
    }}

println (f nil)
println (g (cons zero nil))
"
        ),
        &["Nat::zero", "Nat::succ(Nat::zero)"],
    );
}

/// 卡住 match 的多 pending 实参：`pick n a b` 卡住期收 3 个实参，
/// 具体调用后值层逐个应用（README §3.3 的 pending 语义）。
#[test]
fn v3_stuck_pending_multi_args() {
    let out = check(&format!(
        "{NAT}
def pick(n: Nat): Nat -> Nat -> Nat =
    match n {{
        case zero => a => b => a
        case succ(k) => a => b => b
    }}

def g(n: Nat, a: Nat, b: Nat): Nat = pick n a b

println (g zero (succ zero) (succ (succ zero)))
println (g (succ zero) (succ zero) (succ (succ zero)))
println g
"
    ));
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[0], "Nat::succ(Nat::zero)");
    assert_eq!(lines[1], "Nat::succ(Nat::succ(Nat::zero))");
    assert!(lines[2].contains("match n {"), "stuck print: {}", lines[2]);
}

/// 隐式子模式具名绑定 `cons[l](x, xs)`：方括号子模式对准隐式绑定器，
/// 绑定名 `l` 在臂体可用（l = 尾部长度）。
#[test]
fn v3_pattern_implicit_subpattern_named() {
    assert_lines(
        &format!(
            "{NAT}{VEC}
def f[A, l: Nat](v: Vec[A] (succ l)): Nat =
    match v {{
        case cons[l](x, xs) => succ l
    }}

println (f (cons zero nil))
println (f (cons (succ zero) nil))
println (f (cons zero (cons (succ zero) nil)))
"
        ),
        &[
            "Nat::succ(Nat::zero)",
            "Nat::succ(Nat::zero)",
            "Nat::succ(Nat::succ(Nat::zero))",
        ],
    );
}

/// 被通配臂遮蔽的臂**完全跳过**（运行时不可达，编译期也不查体）：
/// 遮蔽臂里的类型错误不报——首匹配语义的编译期投影。
#[test]
fn v3_shadowed_arm_body_not_checked() {
    assert_lines(
        &format!(
            "{NAT}{BOOL}
def f(x: Bool): Nat =
    match x {{
        case b => zero
        case true => \"若被检查此处会类型错误\"
    }}

println (f true)
println (f false)
"
        ),
        &["Nat::zero", "Nat::zero"],
    );
}

/// 索引封闭值 vs 构造子索引的解包：`Vec[Nat] two` 上嵌套两层 cons——
/// 特化方程 `two ≡ succ l` 经构造子 datas zip 解出 `l := succ zero`，
/// 内层再解 `l2 := zero`。
#[test]
fn v3_len_two_nested_pattern_refine() {
    assert_lines(
        &format!(
            "{NAT}{VEC}{TWO}
def len_two(v: Vec[Nat] two): Nat =
    match v {{
        case cons(h, cons(h2, t)) => h2
    }}

println (len_two (cons zero (cons two nil)))
"
        ),
        &["Nat::succ(Nat::succ(Nat::zero))"],
    );
}

/// 臂内 let 的类型标注引用模式变量：`let rest: Vec[A] l = xs` +
/// 自递归调用——精化过的索引在 let 传播后保持一致。
#[test]
fn v3_arm_let_annotation_uses_pattern_var() {
    assert_lines(
        &format!(
            "{NAT}{VEC}
def f[A, n: Nat](v: Vec[A] n): Nat =
    match v {{
        case nil => zero
        case cons[l](x, xs) =>
            let rest: Vec[A] l = xs;
            succ (f rest)
    }}

println (f (cons zero (cons (succ zero) nil)))
"
        ),
        &["Nat::succ(Nat::succ(Nat::zero))"],
    );
}

/// 精化喂给投影：`v := nil` 精化后 `v.len` 在读点 force 出 `zero`。
#[test]
fn v3_refine_feeds_projection() {
    assert_lines(
        &format!(
            "{NAT}{VEC}
def f(v: Vec[Nat] zero): Nat =
    match v {{
        case nil => v.len
    }}

println (f nil)
"
        ),
        &["Nat::zero"],
    );
}

// --------------------------------------------------------------------------------
// B. enum 与隐式交互
// --------------------------------------------------------------------------------

/// 构造子与 enum 同名：构造子注册覆盖裸名 `E`——println 得到构造子值
/// `E::E`；但名字 `E` 的**类型**也变成构造子类型（E : E），用它做类型
/// 注解时 universe 预检定向拒绝（表征：枚举类型被自己的构造子遮蔽，
/// 与「构造子裸名跨 enum 最后注册者胜」同一条注册路径）。
#[test]
fn v3_ctor_named_as_enum_shadow() {
    assert_lines("\nenum E {\n    E\n}\n\nprintln E\n", &["E::E"]);
    assert_err(
        "\nenum E {\n    E\n}\ndef x : E = E\nprintln x\n",
        "expected universe",
    );
}

/// 多索引 GADT：两个显式索引 + 两个隐式参数，投影取两个索引值，
/// match 精化双索引。隐式参数无标注（域洞）也必须可用——构造子上
/// 显式供给枚举隐式实参 `p[Nat][Bool]` 是对域洞求解机制的回归钉
/// （修复前 `?m A := U` 因 invert 倒序不了 Decl 头 spine 而误报）。
#[test]
fn v3_multi_index_gadt() {
    assert_lines(
        &format!(
            "{NAT}{BOOL}
enum Pack[A, B](x: A, y: B) {{
    p[A, B](a: A, b: B) -> Pack[A][B] a b
}}

def sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true

println sw
println sw.x
println sw.y

def un(p: Pack[Nat][Bool] zero true): Bool =
    match p {{
        case p(a, b) => b
    }}
println (un (p[Nat][Bool] zero true))

enum Pack2[A : U, B : U](x: A, y: B) {{
    p2[A, B](a: A, b: B) -> Pack2[A][B] a b
}}

def sw2: Pack2[Nat][Bool] zero true = p2[Nat][Bool] zero true

println sw2.y
println (p2 zero false).x
"
        ),
        &[
            "Pack::p([Nat] [Bool] Nat::zero Bool::true)",
            "Nat::zero",
            "Bool::true",
            "Bool::true",
            "Bool::true",
            "Nat::zero",
        ],
    );
}

/// enum 隐式参数不带类型标注（域是洞）：洞随后由使用点解出。构造子的
/// 隐式绑定器（`w` 的 A）进 datas，打印成 `[Nat]`（与 cons 的 `[l]` 同律）。
#[test]
fn v3_unannotated_enum_implicit_param() {
    assert_lines(
        &format!(
            "{NAT}
enum W[A] {{
    w[A](a: A) -> W[A]
}}

def n : W[Nat] = w[Nat][Nat] zero

println n
"
        ),
        &["W::w([Nat] Nat::zero)"],
    );
}

/// 命名隐式实参供给构造子的隐式槽：`cons[A = Nat][l = zero]`。
#[test]
fn v3_named_implicit_ctor_app() {
    assert_lines(
        &format!(
            "{NAT}{VEC}
println (cons[A = Nat][l = zero] zero nil)
println (nil[A = Nat])
"
        ),
        &["Vec::cons([Nat::zero] Nat::zero Vec::nil)", "Vec::nil"],
    );
}

/// 跨 enum 构造子名写在模式里：不是 scrutinee 类型的构造子 → 变量模式
/// 后备（首臂通配一切，后续臂被遮蔽），且**绑定同名变量遮蔽全局构造子**
/// ——臂体里的 `zero` 是 Bool 型模式变量，作 Nat 实参即 Nat == Bool 冲突。
#[test]
fn v3_cross_enum_ctor_pattern_wildcard() {
    // 变量模式遮蔽全局构造子：臂体的 zero 解析到模式绑定（类型 Bool）
    assert_err(
        &format!(
            "{NAT}{BOOL}
def f(x: Bool): Nat =
    match x {{
        case zero => zero
    }}
"
        ),
        "can't unify Nat == Bool",
    );
    // 避开遮蔽后：首臂（跨 enum 名）就是通配，两输入都走它；后续臂被遮蔽
    assert_lines(
        &format!(
            "{NAT}{BOOL}
def one = succ zero

def f(x: Bool): Nat =
    match x {{
        case zero => one
        case true => zero
    }}

println (f true)
println (f false)
"
        ),
        &["Nat::succ(Nat::zero)", "Nat::succ(Nat::zero)"],
    );
}

/// 对照组：def 的隐式参数域洞不受枚举钉 U 修复影响——def 隐式参数
/// 不限于类型，域洞保留；显式供参（`two_params[Nat][Bool]`）走
/// 逐参求解照常工作（enum 的差异在其构造子类型检查会 elaborator
/// 自身的类型应用，把域 meta 提前解成 Π 链）。
#[test]
fn v3_def_impl_params_supply_ok() {
    assert_lines(
        &format!(
            "{NAT}{BOOL}
def two_params[A, B](x: A, y: B): A = x

println (two_params[Nat][Bool] zero true)
println (two_params zero false)
"
        ),
        // 两次调用都返回 x（结果类型 A := Nat）
        &["Nat::zero", "Nat::zero"],
    );
}

/// 构造子显式绑定器缺类型标注 → 解析失败（p_pi_binder 的显式形态
/// 要求 `:`）。
#[test]
fn v3_ctor_binder_needs_annotation_parse_err() {
    assert_parse_err_no_panic("\nenum Bad {\n    mk(a)\n}\n");
}

/// enum 显式参数的类型不是 universe（`zero : Nat` 不是类型）→
/// universe 定向报错。
#[test]
fn v3_enum_param_type_not_universe() {
    assert_err(
        &format!("{NAT}\nenum E[x: zero] {{\n    c\n}}\n"),
        "expected universe",
    );
}

// --------------------------------------------------------------------------------
// C. unification / struct_eq 边界
// --------------------------------------------------------------------------------

/// rigid 头不同（变量型函数头 f vs g）：can't unify，不 panic。
#[test]
fn v3_rigid_head_mismatch() {
    assert_err(
        &format!(
            "{NAT}{EQ}
def bad(f: Nat -> Nat, g: Nat -> Nat, x: Nat): Eq (f x) (g x) = refl (f x)
"
        ),
        "can't unify",
    );
}

/// 同头 spine 长度不齐（`f x` vs `f x x`）：unify_sp 长度失配 → can't unify。
#[test]
fn v3_spine_length_mismatch() {
    assert_err(
        &format!(
            "{NAT}{EQ}
def bad(f: Nat -> Nat -> Nat, x: Nat): Eq (f x) (f x x) = refl (f x)
"
        ),
        "can't unify",
    );
}

/// 自引用占位 Decl 头 vs 全局 Decl 头（不同名）：`bad f x` 是指向自身的
/// 中性占位（体检查期间），与 `h x` 归约出的构造子值不同 → can't unify。
/// 注意自引用只在**体**里可见——注解里引用自身是 name not in scope。
#[test]
fn v3_self_ref_stuck_head() {
    assert_err(
        &format!(
            "{NAT}{EQ}
def h(x: Nat): Nat = succ x

def bad(f: Nat -> Nat, x: Nat): Eq (h x) (h x) = refl (bad f x)
"
        ),
        "can't unify",
    );
    // 自引用在注解里：占位尚未登记 → name not in scope（表征）
    assert_err(
        &format!(
            "{NAT}{EQ}
def bad2(f: Nat -> Nat, x: Nat): Eq (bad2 f x) (h2 x) = refl (h2 x)

def h2(x: Nat): Nat = x
"
        ),
        "name not in scope: bad2",
    );
}

/// flex-flex（不同 meta 的 Π 域/余域逐对相融）+ 参数求解沿链传播：
/// `k (refl zero)` 的实参把域 meta 解成 zero，经 ?3 := ?1 方向的
/// flex-flex 解，余类型跟解码成 Eq zero zero。
#[test]
fn v3_flex_flex_later_solve() {
    assert_lines(
        &format!(
            "{NAT}{EQ}
def k : Eq _ _ -> Eq _ _ = x => x

def kk : Eq zero zero = k (refl zero)

println kk
println (k (refl zero))
"
        ),
        &["Eq::refl(Nat::zero)", "Eq::refl(Nat::zero)"],
    );
}

/// 卡住投影与 rigid 不证等：`v.len`（v 是变量）卡住，与 `n` 只能
/// 严格相等——无 Vec 指数的定义性 eta（严格语义，doc 化）。
#[test]
fn v3_stuck_projection_not_refl() {
    assert_err(
        &format!(
            "{NAT}{VEC}{EQ}
def bad[A, n: Nat](v: Vec[A] n): Eq (v.len) n = refl v.len
"
        ),
        "can't unify",
    );
}

// --------------------------------------------------------------------------------
// D. 性能悬崖表征（带超时防护）
// --------------------------------------------------------------------------------

/// 深嵌套模式的编译/运行时成本：depth 层嵌套 cons 模式 + 通配兜底臂。
/// 逐臂独立下钻是线性的——depth=40 必须在秒级完成（超时 120s 防护，
/// 超时即视为性能悬崖回归）。
#[test]
fn v3_deep_pattern_linear() {
    let depth = 40;
    let mut big = "nil".to_owned();
    for i in 0..depth {
        // 外层元素最后包裹：i+1 == depth 的那一层即 h0
        let elem = if i + 1 == depth { "succ zero" } else { "zero" };
        big = format!("cons ({elem}) ({big})");
    }
    let mut pat = "nil".to_owned();
    for i in (0..depth).rev() {
        pat = format!("cons(h{i}, {pat})");
    }
    let src = format!(
        "{NAT}{VEC}
def big = {big}

def f[n: Nat](v: Vec[Nat] n): Nat =
    match v {{
        case {pat} => h0
        case _ => zero
    }}

println (f big)
"
    );
    let out = check_timeout(&src, 120);
    assert_eq!(out.lines().next(), Some("Nat::succ(Nat::zero)"), "src:\n{src}");
}

/// 卡住 match 的多 pending 实参（README 性能 backlog 提到的逐应用
/// 拷贝路径）：k=60 个实参卡在 pending 里，quote 拼接 + 具体调用
/// 都必须多项式内完成。
#[test]
fn v3_stuck_many_pending_apps() {
    let k = 60;
    let binders: Vec<String> = (1..=k).map(|i| format!("x{i}")).collect();
    let lam = |body: &str| {
        format!(
            "{} {body}",
            binders.iter().map(|b| format!("{b} =>")).collect::<Vec<_>>().join(" ")
        )
    };
    let params: Vec<String> = (1..=k).map(|i| format!("a{i}: Nat")).collect();
    let args: Vec<String> = (1..=k).map(|i| format!("a{i}")).collect();
    let call_args: Vec<String> = (1..=k)
        .map(|i| if i == 1 { "(succ zero)".to_owned() } else { "zero".to_owned() })
        .collect();
    let src = format!(
        "{NAT}
def pick(n: Nat): {} =
    match n {{
        case zero => {}
        case succ(k) => {}
    }}

def g(n: Nat, {}): Nat = pick n {}

println (g zero {})
println g
",
        format!("{}Nat", "Nat -> ".repeat(k)),
        lam("x1"),
        lam("x2"),
        params.join(", "),
        args.join(" "),
        call_args.join(" "),
    );
    let out = check_timeout(&src, 120);
    let mut lines = out.lines();
    assert_eq!(lines.next(), Some("Nat::succ(Nat::zero)"), "src tail:\n{src}");
    assert!(lines.next().unwrap().contains("match n {"), "out: {out}");
}

// --------------------------------------------------------------------------------
// E. 解析残缺与错误路径
// --------------------------------------------------------------------------------

/// 截断输入：一律可恢复的 parse error，绝不 panic（lexer 未闭合字符串 /
/// 未闭合括号 / 半个 decl / 半个 match / 半个臂）。
#[test]
fn v3_truncated_inputs_no_panic() {
    let cases: Vec<String> = vec![
        "def f(x: Nat): Nat =".to_owned(),
        "enum E {".to_owned(),
        "enum E".to_owned(),
        "println".to_owned(),
        "println (".to_owned(),
        "println \"abc".to_owned(),
        "def".to_owned(),
        "match x {".to_owned(),
        "def f = match x { case zero =>".to_owned(),
        "{".to_owned(),
        "}".to_owned(),
        "(".to_owned(),
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\ndef two =".to_owned(),
        "def f(x: Nat): Nat =\n    match x {\n        case zero => zero\n".to_owned(),
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nprintln (cons zero".to_owned(),
        "def s = \"unterminated".to_owned(),
    ];
    for src in cases {
        assert_parse_err_no_panic(&src);
    }
}

/// match 位置的精确刻画（对 v1 怪癖 #3 的修正）：解析失败的根因是
/// **单行臂**（臂间缺 EndLine 分隔），不是 match 出现的行位置——
///   a) `def mf =` 换行 match：合法，期望洞被首臂类型实例化；
///   b) println 里的内联 match（多行）：解析合法，但 println 是推断
///      位置 → "match cannot be inferred"；
///   c) 臂间无换行 → 解析失败（v1 已钉，此处不重复）。
#[test]
fn v3_match_positions_clarified() {
    // a) 无标注 def 的换行 match 被接受（期望洞吃首臂类型 Bool）
    assert_lines(
        &format!(
            "{NAT}{BOOL}
def mf =
    match (succ zero) {{
        case zero => true
        case succ(k) => false
    }}

println mf
"
        ),
        &["Bool::false"],
    );
    // b) println（推断位置）里的多行内联 match：解析过、elaboration 拒绝
    assert_err(
        &format!(
            "{NAT}{BOOL}
println (match zero {{
    case zero => true
    case succ(k) => false
}})
"
        ),
        "match cannot be inferred",
    );
}

/// 内联多行 match 在**检查位置**可用：`the Nat (match ...)` 的实参
/// 按期望类型检查（v1 只测过 println 的推断位置失败面）。
#[test]
fn v3_inline_match_check_position() {
    assert_lines(
        &format!(
            "{NAT}
def the(A : U)(x: A): A = x

println (the Nat (
    match zero {{
        case zero => succ zero
        case succ(k) => k
    }}
))
"
        ),
        &["Nat::succ(Nat::zero)"],
    );
}

/// 构造子裸名被 def 占用：redefine 定向报错（decl 表已有 `zero`）。
#[test]
fn v3_redefine_ctor_as_def() {
    assert_err(
        &format!("{NAT}\ndef zero : Nat = zero\nprintln zero\n"),
        "redefine zero",
    );
}

/// 构造子 `-> ret` 不是 universe（字符串字面量）→ universe 定向报错。
#[test]
fn v3_ctor_ret_not_universe() {
    assert_err(
        "\nenum E {\n    mk(x: E) -> \"s\"\n}\n",
        "expected universe",
    );
}

/// 模式元数错误与隐式槽的交互：`cons(x, y, z)`——隐式 l 自动通配后
/// 显式子模式仍多 1 个 → 定向报「多了 1 个子模式」。
#[test]
fn v3_pattern_too_many_with_implicit() {
    assert_err(
        &format!(
            "{NAT}{VEC}
def bad(v: Vec[Nat] zero): Nat =
    match v {{
        case nil => zero
        case cons(x, y, z) => x
    }}
"
        ),
        "多了 1 个子模式",
    );
}

/// 非 ASCII：字符串字面量、标识符、行注释内容——输出与解析不受影响
/// （preprocess 的空白替换会移动偏移，仅影响错误消息里的数字）。
#[test]
fn v3_unicode_string_ident_comment() {
    assert_lines(
        &format!(
            "{NAT}\nprintln \"中文✓\"\n\ndef 数 = succ zero\n\n// 注释里的中文不算 token\n\nprintln 数\n"
        ),
        &["中文✓", "Nat::succ(Nat::zero)"],
    );
}

/// CRLF 行尾（Windows 常见）：`\r` 是空白、`\n` 是 EndLine——
/// 行导向语法（match 换行、臂分隔）在 CRLF 下与 LF 等价。
#[test]
fn v3_crlf_input() {
    let src = format!(
        "enum Nat {{\r\n    zero\r\n    succ(x: Nat)\r\n}}\r\n\r\ndef f(x: Nat): Nat =\r\n    match x {{\r\n        case zero => zero\r\n        case succ(k) => succ k\r\n    }}\r\n\r\nprintln (f (succ zero))\r\n"
    );
    assert_lines(&src, &["Nat::succ(Nat::zero)"]);
}

// --------------------------------------------------------------------------------
// F. parity：参考版 run ↔ 孪生版 run_fast
// --------------------------------------------------------------------------------

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L07_sum_type/mod.rs"]
mod L07_sum_type;

use L07_sum_type::bump_spine_iter as fast;

/// 在大栈线程里跑参考版 `run`。
fn run_basic(src: &str) -> Result<String, L07_sum_type::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L07_sum_type::run(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, L07_sum_type::Error> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0))
        .unwrap()
        .join()
        .unwrap()
}

/// Oracle：Ok 输出逐字节一致 / Err 判定一致（l07_fast_parity 同款）。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(_), Err(_)) => {}
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}",
            b.map(|_| "Ok").unwrap_or("Err"),
            f.map(|_| "Ok").unwrap_or("Err")
        ),
    }
}

/// Ok 用例 parity：v3 新攻击面的全部成功路径。
#[test]
fn v3_parity_ok_suite() {
    // T n 族：返回类型依赖已匹配构造子
    assert_parity(&format!(
        "{NAT}{BOOL}
def T(n: Nat): U =
    match n {{
        case zero => Bool
        case succ(m) => Nat
    }}

def g(n: Nat): T n =
    match n {{
        case zero => true
        case succ(m) => zero
    }}

println (g zero)
println (g (succ (succ zero)))
println g
"
    ));
    // 嵌套 match + 双重精化
    assert_parity(&format!(
        "{NAT}
def h(x: Nat): Nat =
    match x {{
        case succ(k) =>
            match x {{
                case succ(k2) => k2
                case zero => zero
            }}
        case zero => zero
    }}

println (h (succ (succ zero)))
"
    ));
    // add 型索引算术（Vec 拼接）
    assert_parity(&format!(
        "{NAT}{VEC}{ADD}
def app[A, m: Nat, n: Nat](xs: Vec[A] m, ys: Vec[A] n): Vec[A] (add m n) =
    match xs {{
        case nil => ys
        case cons(x, rest) => cons x (app rest ys)
    }}

def v = app (cons zero nil) (cons (succ zero) nil)

println v
println v.len
"
    ));
    // 隐式子模式具名绑定 + let 标注用模式变量 + 自递归
    assert_parity(&format!(
        "{NAT}{VEC}
def f[A, n: Nat](v: Vec[A] n): Nat =
    match v {{
        case nil => zero
        case cons[l](x, xs) =>
            let rest: Vec[A] l = xs;
            succ (f rest)
    }}

println (f (cons zero (cons (succ zero) nil)))
"
    ));
    // 投影 scrutinee / 精化喂投影 / 卡住 pending / 多索引 GADT
    assert_parity(&format!(
        "{NAT}{VEC}
def g(v: Vec[Nat] (succ zero)): Nat =
    match v.len {{
        case succ(k) => succ k
    }}

println (g (cons zero nil))

def f(v: Vec[Nat] zero): Nat =
    match v {{
        case nil => v.len
    }}
println (f nil)

def pick(n: Nat): Nat -> Nat -> Nat =
    match n {{
        case zero => a => b => a
        case succ(k) => a => b => b
    }}

def gg(n: Nat, a: Nat, b: Nat): Nat = pick n a b

println (gg zero (succ zero) (succ (succ zero)))
println gg

enum Pack[A, B](x: A, y: B) {{
    p[A, B](a: A, b: B) -> Pack[A][B] a b
}}

def sw: Pack[Nat][Nat] zero zero = p[Nat][Nat] zero zero

println sw.x
println sw.y
println (p[Nat][Nat] (succ zero) zero).y
"
    ));
    // flex-flex + 后续求解
    assert_parity(&format!(
        "{NAT}{EQ}
def k : Eq _ _ -> Eq _ _ = x => x

def kk : Eq zero zero = k (refl zero)

println kk
println k
"
    ));
    // 深负载小样：深嵌套模式（depth=12，逐臂线性下钻）
    let depth = 12;
    let mut big = "nil".to_owned();
    for _i in 0..depth {
        big = format!("cons (zero) ({big})");
    }
    let mut pat = "nil".to_owned();
    for i in (0..depth).rev() {
        pat = format!("cons(h{i}, {pat})");
    }
    assert_parity(&format!(
        "{NAT}{VEC}
def big = {big}

def f[n: Nat](v: Vec[Nat] n): Nat =
    match v {{
        case {pat} => h0
        case _ => zero
    }}

println (f big)
"
    ));
    // 卡住 match 多 pending（k=8）：quote 拼接与值层重应用
    let k = 8;
    let binders: Vec<String> = (1..=k).map(|i| format!("x{i}")).collect();
    let lam = |body: &str| {
        format!(
            "{} {body}",
            binders.iter().map(|b| format!("{b} =>")).collect::<Vec<_>>().join(" ")
        )
    };
    let params: Vec<String> = (1..=k).map(|i| format!("a{i}: Nat")).collect();
    let args: Vec<String> = (1..=k).map(|i| format!("a{i}")).collect();
    assert_parity(&format!(
        "{NAT}
def pick(n: Nat): {} =
    match n {{
        case zero => {}
        case succ(k) => {}
    }}

def g(n: Nat, {}): Nat = pick n {}

println (g zero {})
println g
",
        format!("{}Nat", "Nat -> ".repeat(k)),
        lam("x1"),
        lam("x2"),
        params.join(", "),
        args.join(" "),
        args.iter().map(|_| "zero".to_owned()).collect::<Vec<_>>().join(" "),
    ));
}

/// Err 用例 parity：判定一致（错误文案的 span 偏移是文档化偏差，不比内容）。
#[test]
fn v3_parity_err_suite() {
    // 荒谬嵌套模式（不可达 + 缺构造子）
    assert_parity(&format!(
        "{NAT}{VEC}
def bad(v: Vec[Nat] (succ zero)): Nat =
    match v {{
        case cons(h, cons(h2, t)) => h2
    }}
"
    ));
    // 零臂 match：只列可达构造子
    assert_parity(&format!(
        "{NAT}{VEC}
def f(v: Vec[Nat] (succ zero)): Nat =
    match v {{
    }}
"
    ));
    // 索引矛盾前提的 refl 臂不可达
    assert_parity(&format!(
        "{NAT}{EQ}{TWO}
def bad(e: Eq two three): Nat =
    match e {{
        case refl(a) => zero
    }}
"
    ));
    // rigid 头不同 / spine 长度不齐 / 卡住投影
    assert_parity(&format!(
        "{NAT}{EQ}
def bad(f: Nat -> Nat, g: Nat -> Nat, x: Nat): Eq (f x) (g x) = refl (f x)
"
    ));
    assert_parity(&format!(
        "{NAT}{EQ}
def bad(f: Nat -> Nat -> Nat, x: Nat): Eq (f x) (f x x) = refl (f x)
"
    ));
    assert_parity(&format!(
        "{NAT}{VEC}
def bad[A, n: Nat](v: Vec[A] n): Eq (v.len) n = refl v.len
"
    ));
    // 模式多子模式（隐式槽交互）/ universe 定向报错 / 重定义
    assert_parity(&format!(
        "{NAT}{VEC}
def bad(v: Vec[Nat] zero): Nat =
    match v {{
        case nil => zero
        case cons(x, y, z) => x
    }}
"
    ));
    assert_parity(&format!("{NAT}\nenum E[x: zero] {{\n    c\n}}\n"));
    assert_parity(&format!("{NAT}\ndef zero : Nat = zero\nprintln zero\n"));
    // 解析残缺：截断 / 单行臂
    assert_parity("def f(x: Nat): Nat =");
    assert_parity("println \"abc");
    assert_parity(&format!(
        "{NAT}\ndef bad(x: Nat): Nat = match x {{ case zero => zero case succ(k) => k }}\n"
    ));
    // 构造子与 enum 同名后用作类型注解
    assert_parity("\nenum E {\n    E\n}\ndef x : E = E\nprintln x\n");
}

// 格式探针（行为存疑时重跑对账；-- --ignored --nocapture）
// --------------------------------------------------------------------------------

/// 探针：无标注 enum 隐式参数 / flex-flex 直接打印 / E::E 遮蔽形态 /
/// 多索引 enum 参数标注的隔离变体。
#[test]
#[ignore]
fn v3_probe_formats() {
    let probes: Vec<(&str, String)> = vec![
        (
            "unannotated_impl_param",
            format!("{NAT}\nenum W[A] {{\n    w[A](a: A) -> W[A]\n}}\n\ndef n : W[Nat] = w[Nat][Nat] zero\n\nprintln n\n"),
        ),
        (
            "flex_flex_raw",
            format!("{NAT}{EQ}\ndef k : Eq _ _ -> Eq _ _ = x => x\nprintln (k (refl zero))\n"),
        ),
        (
            "ctor_shadows_enum",
            "\nenum E {\n    E\n}\nprintln E\n".to_owned(),
        ),
        (
            "zero_arm_false_hypothesis",
            format!("{NAT}{EQ}{TWO}\ndef f(e: Eq two three): Nat =\n    match e {{\n    }}\nprintln \"ok\"\n"),
        ),
        // 多索引 enum：隔离变体
        (
            "pack_annotated_params",
            format!("{NAT}{BOOL}\nenum Pack[A : U, B : U](x: A, y: B) {{\n    p[A, B](a: A, b: B) -> Pack[A][B] a b\n}}\n\ndef sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true\n\nprintln sw\nprintln sw.x\nprintln sw.y\n"),
        ),
        (
            "pack_unannotated_no_index",
            format!("{NAT}{BOOL}\nenum P1[A, B] {{\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}}\n\nprintln (p1[Nat][Bool] zero true)\n"),
        ),
        (
            "pack_unannotated_no_index_implicit_given",
            format!("{NAT}{BOOL}\nenum P1[A, B] {{\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}}\n\ndef s1: P1[Nat][Bool] = p1[Nat][Bool][Nat][Bool] zero true\nprintln s1\n"),
        ),
        (
            "pack_unannotated_no_index_bare",
            format!("{NAT}{BOOL}\nenum P1[A, B] {{\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}}\n\nprintln (p1 zero true)\n"),
        ),
        (
            "pack_unannotated_one_index",
            format!("{NAT}\nenum P2[A](x: A) {{\n    p2[A](a: A) -> P2[A] a\n}}\n\ndef s2: P2[Nat] zero = p2[Nat][Nat] zero\n\nprintln s2\n"),
        ),
        (
            "pack_unannotated_decl_only",
            format!("{NAT}{BOOL}\nenum Pack[A, B](x: A, y: B) {{\n    p[A, B](a: A, b: B) -> Pack[A][B] a b\n}}\nprintln Pack\n"),
        ),
        (
            "vec_unannotated_use",
            format!("{NAT}{VEC}\ndef t = cons[Nat][zero] zero nil\nprintln t\nprintln t.len\n"),
        ),
        // 对照组：def 的隐式参数域洞（def 隐式参数不限于类型，不能钉 U——
        // 显式供参是否受限属于通用合一器的非可逆 flex spine 限制，表征用）
        (
            "def_impl_params_supply",
            format!("{NAT}{BOOL}\ndef two_params[A, B](x: A, y: B): A = x\n\nprintln (two_params[Nat][Bool] zero true)\n"),
        ),
        (
            "def_impl_params_bare",
            format!("{NAT}{BOOL}\ndef two_params[A, B](x: A, y: B): A = x\n\nprintln (two_params zero true)\n"),
        ),
    ];
    for (name, src) in probes {
        println!("=====PROBE v3 {name}=====");
        let input = src.clone();
        let out = std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || match run(&input, 0) {
                Ok(o) => format!("OK\n{o}"),
                Err(e) => format!("ERR {e:?}"),
            })
            .unwrap()
            .join()
            .unwrap_or_else(|_| "PANIC/ABORT".to_owned());
        println!("{out}");
    }
}

// --------------------------------------------------------------------------------
// G. 回灌回归：L05 孪生 quote 链「陈旧函数部分」——β-红ex 混入输出
// --------------------------------------------------------------------------------
//
// L05 章在孪生版发现的真 bug 的 L07 回灌（L05 fix 65269fb 同款位点）：
// meta 先被应用进某条 spine 值、随后才被解成多 λ 时，快版 quote 的链分解
// （ChainRun bail 的 `prev: Some(prev)` + `Q(fi)`、二叉 fallback 的
// `Q(stack[h].f)`）把该 spine 的「函数部分」单独 force 后引读——它停在
// **部分应用的闭包**上，重拼 App 即产出 β-红ex 项（修复前快版实测输出
// `?0 ((b' => ?5 a b') b) a`）；参考版整值 force 经 vAppSp 一路 β，永不
// 产出红ex。修复：两处分解位点在函数部分 force 为闭包（tag 1）时改走
// β 语义——按本槽实参求闭包体（env_ext + eval_iter）再引应用结果，
// ChainRun 恢复点以 prev:None 直接取该结果为已累计项（不再拼接）；中性
// 路径（变量/未解 meta）保持原速路。
//
// 判据：本节的 can't unify 错误文案不含 Span（快版 span 全零的文档化偏差
// 不涉及），两版**全文逐字节**一致即钉死。F 节 `assert_parity` 对 Err 只比
// 判定——修复前双版同为 Err，抓不住快版文案里的红ex；本节 oracle 加严。

/// Church 编码前奏（Eq / refl / the；触发 unification 的标准模式）。
const CHURCH: &str = "def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px
def the(A : U)(x: A): A = x
";

/// Ok 输出 / Err 文案全文逐字节 parity（比 F 节加严：Err 也比全文）。
fn assert_full_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    let bt = match &b {
        Ok(s) => s.clone(),
        Err(e) => format!("{e:?}"),
    };
    let ft = match &f {
        Ok(s) => s.clone(),
        Err(e) => format!("{e:?}"),
    };
    assert_eq!(
        bt, ft,
        "双实现全文不一致，src:\n{src}\n--- basic ---\n{bt}--- fast ---\n{ft}"
    );
}

/// 看门狗 + 全文 parity（家族批量扫描用；超时/恐慌让测试失败，套件不挂死）。
fn assert_terminates_full_parity(src: &str, secs: u64) {
    let input = src.to_owned();
    let (tx, rx) = std::sync::mpsc::channel::<()>();
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            assert_full_parity(&input);
            let _ = tx.send(());
        })
        .expect("看门狗线程创建失败");
    if rx
        .recv_timeout(std::time::Duration::from_secs(secs))
        .is_err()
    {
        panic!("输入在 {secs}s 内未终止（疑似挂死/发散）：\n{src}");
    }
    handle.join().unwrap();
}

/// 最小复现（L05 同款输入的 L07 语法移植）：`m1 : [A : U] -> U -> U` 的两个
/// 部分应用做 Church-Eq。解 `m1` 的隐式槽时 `?0` 的 spine 里挂了 `?5 a b`；
/// 随后 `?5` 被 flex_flex 解成**双 λ 转发解**，而引用它的 spine 值（建链早
/// 于求解）仍是陈旧位模式。修复前快版报错混入红ex
/// `?0 ((b' => ?5 a b') b) a`；修复后两版都给干净形态 `?0 (?5 a b)`。
#[test]
fn redex_regression_eq_swapped_args() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U = _\ndef t = a => b => the (Eq (m1 b) (m1 a)) refl\n"
    );
    let golden = r#"Error("can't unify (P: U → U) → P (?0 (?5 a b) b) → P (?0 (?5 a b) a) == (P: U → U) → P (?0 (?5 a b) b) → P (?0 (?5 a b) b)")"#;
    // 参考版：干净形态（无重拼红ex），golden 钉死
    let b = run_basic(&src).unwrap_err();
    assert_eq!(format!("{b:?}"), golden);
    // 快版：修复后与参考版逐字节同形
    let f = run_fast(&src).unwrap_err();
    assert_eq!(format!("{f:?}"), golden);
}

/// 同族镜像：实参顺序互换（`m1 a` vs `m1 b`），失败方向镜像。
#[test]
fn redex_regression_eq_args_order_mirror() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U = _\ndef t = a => b => the (Eq (m1 a) (m1 b)) refl\n"
    );
    let golden = r#"Error("can't unify (P: U → U) → P (?0 (?5 a b) a) → P (?0 (?5 a b) b) == (P: U → U) → P (?0 (?5 a b) a) → P (?0 (?5 a b) a)")"#;
    let b = run_basic(&src).unwrap_err();
    assert_eq!(format!("{b:?}"), golden);
    let f = run_fast(&src).unwrap_err();
    assert_eq!(format!("{f:?}"), golden);
}

/// 同族：`m1` 多一个显式域（P 的定义域带箭头），转发解照旧、红ex 照旧。
#[test]
fn redex_regression_extra_domain() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U -> U = _\ndef t = a => b => the (Eq (m1 b) (m1 a)) refl\n"
    );
    let golden = r#"Error("can't unify (P: (U → U) → U) → P (?0 (?5 a b) b) → P (?0 (?5 a b) a) == (P: (U → U) → U) → P (?0 (?5 a b) b) → P (?0 (?5 a b) b)")"#;
    let b = run_basic(&src).unwrap_err();
    assert_eq!(format!("{b:?}"), golden);
    let f = run_fast(&src).unwrap_err();
    assert_eq!(format!("{f:?}"), golden);
}

/// 家族批量全文 parity（L05 同款形状网格：6 体 × 3 声明），带看门狗。
/// 覆盖转发解（红ex 位点）、可解 η-intersect、icit 失配、双版本 Ok 等形态。
#[test]
fn redex_family_full_parity_scan() {
    let bodies = [
        "def t = a => b => the (Eq (m1 b) (m1 a)) refl",
        "def t = a => b => the (Eq (m1 a) (m1 b)) refl",
        "def t = a => b => the (Eq (m1 [a] b) (m1 a)) refl",
        "def t = a => b => the (Eq (m1 a b) (m1 b a)) refl",
        "def t = a => b => the (Eq (z => m1 a z) (m1 b)) refl",
        "def t = a => b => the (Eq (m1 [a] [b]) ([z] => m1 [a] [b] [z])) refl",
    ];
    let decls = [
        "def m1[A : U] : U -> U = _",
        "def m1 : U -> U -> U = _",
        "def m1[A : U] : U -> U -> U = _",
    ];
    for d in decls {
        for b in bodies {
            assert_terminates_full_parity(&format!("{CHURCH}{d}\n{b}\n"), 60);
        }
    }
}

/// 可解例（Ok 路径对照）：η 展开后经 intersect 剪掉差异槽，方程可解、
/// 程序成功——修复不得影响中性路径的正常引读。
#[test]
fn redex_family_solvable_ok() {
    let src = format!(
        "{CHURCH}def m1 : U -> U -> U = _\ndef t = a => b => the (Eq (m1 a) (z => m1 b z)) refl\nprintln U\n"
    );
    assert_lines(&src, &["U"]);
    assert_full_parity(&src);
}
