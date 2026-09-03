//! L06_string 黑盒测试套件 · 第二卷（v2）。
//!
//! Round-1 评审补盖的语义角落，第一卷（`l06_blackbox.rs`）没有覆盖的：
//!
//! - **pruning 剪枝路径**：intersect / 非线性 solve / prune_vflex（含
//!   非回文掩码与依赖 telescope）三条路径的双实现互检——参考版 `prune_ty`
//!   已补上游 `pruneTy (revPruning pr)` 的掩码反转、`prune_vflex` 折叠改
//!   外先序、`intersect_go` 长度失配优雅回落（对齐 L05 同款修复），快版
//!   `invert_bump` 掩码改产内先序（兑现 `prune_ty_bump` 的
//!   `mask_inner_first` 契约），本组用例钉住修复后的 parity；
//! - **(Lit, Lit) 恒败**：readme 招牌声明（连相同字面量也不可合一）此前
//!   零覆盖；
//! - **跨轮隔离**：快版 `Tycker` 稳态复用时 mutable_map / decl 表 / meta
//!   编号随轮清空（旧稳态测试同一 src 跑两遍，对泄漏不敏感）；
//! - **prim 触发语义角落**：decl 表登记的卡住部分应用再吃实参时补触发、
//!   def 覆盖 builtin 名抹掉 prim、`change_mutable` 缺名静默 no-op、
//!   `report_check_issue` 行级去重；
//! - **词法角落**：`\\` / `\"` 转义、字符串尾 `\` 后接注释、`""` 空字面量
//!   （lexer 曾把 `end == 0` 误判为未闭合）、解析失败带首个残余 token 定位。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L06_string/mod.rs"]
mod L06_string;

use L06_string::bump_spine_iter as fast;

fn run_basic(src: &str) -> Result<String, L06_string::Error> {
    L06_string::run(src, 0)
}

fn run_fast(src: &str) -> Result<String, L06_string::Error> {
    fast::run_fast(src, 0)
}

/// 参考版与性能版的 Ok 输出逐字节一致；Err 判定一致（第一卷同款）。
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

/// 双实现都 Err 且消息含 needle；另附消息全文一致断言（Error 字段私有，
/// 经 Debug 形态读内容）。
fn assert_error_parity(src: &str, needle: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    assert!(b.is_err(), "basic 应报错：{src}");
    assert!(f.is_err(), "fast 应报错：{src}");
    let (b, f) = (format!("{:?}", b.unwrap_err()), format!("{:?}", f.unwrap_err()));
    assert!(b.contains(needle), "basic 消息缺 {needle:?}：{b}");
    assert!(f.contains(needle), "fast 消息缺 {needle:?}：{f}");
    assert_eq!(b, f, "错误消息全文不一致（不含偏移的稳定片段也该一致）");
}

// pruning 剪枝路径（非回文掩码 + 依赖 telescope）
// --------------------------------------------------------------------------------

/// 四个场景分别穿过 intersect / 非线性 solve / prune_vflex / 依赖 telescope
/// 上的 prune_meta 四条剪枝相关路径，钉住掩码方向修复后的双实现 parity。
#[test]
fn pruning_nonpalindrome_dependent_masks() {
    // 1) intersect：m A x ≡ m A y（同 meta 同长度 spine，实参部分相异）
    //    → intersect 取交 + prune_meta 在依赖 telescope (A : U) -> (x : A) -> U
    //    上剪枝
    let intersect = concat!(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
        "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : U)(x : A) : A = x\n",
        "def m (A : U)(x : A) : U = _\n",
        "def test = A => x => y => the (Eq (m A x) (m A y)) refl\n",
        "println test\n",
    );
    assert_parity(intersect);

    // 2) 非线性 solve：Eq 的 x 位解 `?x := m A x` 后，y 位过 force 再解
    //    ——solve/invert/λ 包裹链路上的 parity
    let solve = concat!(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
        "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : U)(x : A) : A = x\n",
        "def m (A : U)(x : A) : U = _\n",
        "def test = A => x => the (Eq U (m A x)) refl\n",
        "println test\n",
    );
    assert_parity(solve);

    // 3) prune_vflex：η 展开后 m x x1 ≡ n x y x1 w，rename rhs 的 n spine
    //    时 y 越出 renaming 定义域——flex_flex 长边求解 + 转发链路
    let vflex = concat!(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
        "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : U)(x : A) : A = x\n",
        "def m : U -> U -> U -> U = _\n",
        "def n : U -> U -> U -> U -> U = _\n",
        "def test = x => x1 => y => the (Eq (m x x1) (w => n x y x1 w)) refl\n",
        "println test\n",
    );
    assert_parity(vflex);

    // 4) 剪枝 mask 非回文（[Some, None]，实证探针观测）：n 的第二个参数
    //    类型依赖第一个（z : y）——η 展开后 y 越出 renaming 定义域被剪、
    //    w 槽保留，prune_meta 在**依赖** telescope 上剪枝
    let escape_dep = concat!(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
        "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : U)(x : A) : A = x\n",
        "def m : (x : U) -> U -> U = _\n",
        "def n : (y : U) -> (z : y) -> U = _\n",
        "def test = x => y => the (Eq (m x) (w => n y w)) refl\n",
        "println test\n",
    );
    assert_parity(escape_dep);
}

// (Lit, Lit) 恒败
// --------------------------------------------------------------------------------

/// readme 招牌声明：`(Lit, Lit)` 恒败——连相同字面量也不可合一（参考版
/// unify 无字面量臂；快版 tag 7 位相等守卫如实复刻）。经刚性 spine 的
/// `F "a" ≡ F "a"` 才是源码级唯一可达形态。
#[test]
fn lit_lit_unify_always_fails_even_identical() {
    let pre = concat!(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
        "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
        "def h (F : String -> U) : ",
    );
    for (xy, desc) in [
        ("(F \"a\") (F \"a\")", "相同字面量"),
        ("(F \"a\") (F \"b\")", "不同字面量"),
    ] {
        let src = format!("{pre}Eq U {xy} = refl\nprintln \"unreachable\"\n");
        assert_error_parity(&src, "can't unify");
        let _ = desc;
    }
}

// 跨轮隔离
// --------------------------------------------------------------------------------

/// 快版 `Tycker` 稳态复用时的轮间隔离：mutable_map / decl 表 / meta 编号
/// 随轮清空。参考版每次 `run` 新建 `Infer`，逐条对应断言。
#[test]
fn cross_round_isolation() {
    let mut t = fast::Tycker::new();
    // 轮 1：写全局 + 登记顶层 def
    t.run_input("def a : U = create_global \"k\" \"v\"", 0).unwrap();
    // 轮 2：全局不可见 → 走缺省；上轮 def 不可见 → Err；meta 编号复位
    assert_eq!(
        t.run_input(
            "def g : String = get_global_default \"k\" \"fallback\"\nprintln g\n",
            0,
        )
        .unwrap(),
        "fallback\n",
        "mutable_map 应随轮清空"
    );
    assert!(
        t.run_input("println a\n", 0).is_err(),
        "上轮 def 不得跨轮可见"
    );
    assert_eq!(
        t.run_input("def s : String = _\nprintln s\n", 0).unwrap(),
        "?0\n",
        "meta 编号应随轮复位"
    );
    // 参考版同语义（每次 run 新建 Infer）
    run_basic("def a : U = create_global \"k\" \"v\"").unwrap();
    assert_eq!(
        run_basic("def g : String = get_global_default \"k\" \"fallback\"\nprintln g\n")
            .unwrap(),
        "fallback\n"
    );
    assert!(run_basic("println a\n").is_err());
}

// prim 触发语义角落
// --------------------------------------------------------------------------------

/// readme「应用时触发」：decl 表里**登记过的卡住部分应用**再吃到实参时，
/// prim 对全条累积实参（自然序）补触发。
#[test]
fn decl_table_partial_application_refires() {
    let src = concat!(
        "def partial = string_concat \"a\"\n",
        "def full : String = partial \"b\"\n",
        "println full\n",
    );
    assert_eq!(run_basic(src).unwrap(), "ab\n");
    assert_parity(src);
}

/// def 覆盖 builtin 名：decl 表单写入语义——同名 def 登记时 prim 被抹掉，
/// 之后走用户定义的值。
#[test]
fn def_overrides_builtin_clears_prim() {
    let src = concat!(
        "def string_concat : String -> String -> String = x => y => x\n",
        "def r : String = string_concat \"a\" \"b\"\n",
        "println r\n",
    );
    assert_eq!(run_basic(src).unwrap(), "a\n");
    assert_parity(src);
}

/// `change_mutable` 对缺失名是静默 no-op（不建档）——与
/// `change_mutable_default` 的 miss-建档行为互为对照。
#[test]
fn change_mutable_missing_name_is_noop() {
    let src = concat!(
        "def u : U = change_mutable \"ghost\" (s => string_concat s \"!\")\n",
        "def g : String = get_global_default \"ghost\" \"absent\"\n",
        "println g\n",
    );
    assert_eq!(run_basic(src).unwrap(), "absent\n");
    assert_parity(src);
}

/// `report_check_issue` 的行级去重 + 追加形态。
#[test]
fn report_check_issue_dedups_lines() {
    let src = concat!(
        "def i1 : U = report_check_issue \"E1\" \"demo_mod\" \"sig\" \"message\"\n",
        "def i2 : U = report_check_issue \"E1\" \"demo_mod\" \"sig\" \"message\"\n",
        "def i3 : U = report_check_issue \"E2\" \"demo_mod\" \"sig\" \"message\"\n",
        "def issues : String = get_global \"CheckIssues\"\n",
        "println issues\n",
    );
    assert_eq!(
        run_basic(src).unwrap(),
        "E1|demo_mod|sig|message\nE2|demo_mod|sig|message\n"
    );
    assert_parity(src);
}

/// 未解 meta 的打印编号（?N 双洞递增）。
#[test]
fn unsolved_meta_numbering() {
    let src = "def a : String = _\nprintln a\ndef b : String = _\nprintln b\n";
    assert_eq!(run_basic(src).unwrap(), "?0\n?1\n");
    assert_parity(src);
}

// 词法角落
// --------------------------------------------------------------------------------

/// `\\` / `\"` 转义、字符串尾 `\` 后接行注释、`""` 空字面量、解析失败的
/// 残余 token 定位。
#[test]
fn string_escapes_and_empty_literal() {
    // 源码里 `\\` 是转义的反斜杠（打印原文 `a\nb` 四个字符）
    assert_eq!(run_basic("println \"a\\\\nb\"\n").unwrap(), "a\\nb\n");
    assert_parity("println \"a\\\\nb\"\n");
    // `\"` 打印引号
    assert_eq!(
        run_basic("println \"say \\\"hi\\\"\"\n").unwrap(),
        "say \"hi\"\n"
    );
    assert_parity("println \"say \\\"hi\\\"\"\n");
    // 字符串尾的 `\` 后接行注释：内容 `a\`，注释正常剥离
    assert_eq!(
        run_basic("def s = \"a\\\\\" // comment\nprintln s\n").unwrap(),
        "a\\\n"
    );
    assert_parity("def s = \"a\\\\\" // comment\nprintln s\n");
    // 空字符串字面量（lexer 曾把 `end == 0` 误判为未闭合 → 整文件 parse error）
    assert_eq!(run_basic("println \"\"\n").unwrap(), "\n");
    assert_parity("println \"\"\n");
    assert_eq!(run_basic("def e : String = \"\"\nprintln e\n").unwrap(), "\n");
    assert_parity("def e : String = \"\"\nprintln e\n");
    assert_eq!(
        run_basic("println (string_concat \"\" \"x\")\n").unwrap(),
        "x\n"
    );
    assert_parity("println (string_concat \"\" \"x\")\n");
    assert_eq!(run_basic("println (str_eq \"\" \"\")\n").unwrap(), "true\n");
    assert_parity("println (str_eq \"\" \"\")\n");
}

/// 解析失败的残余 token 定位：`;` 结尾这类最常见错误不再裸报 "parse error"。
#[test]
fn parse_error_reports_leftover_token() {
    assert_error_parity("def a : U = U\n;\n", "leftover token `;`");
}
