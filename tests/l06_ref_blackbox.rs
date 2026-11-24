//! L06 参考版黑盒 —— 被封印 gate 掉的**参考版断言的回收**。
//!
//! ## 为什么有这个文件
//!
//! 孪生引擎 L06_string::bump_spine_iter 于 2026-11-24 硬封印：src/L06_string/mod.rs
//! 里的 bump_spine_iter 子模块现挂 `#[cfg(feature = "l06-twin")]`，默认不编译。
//! 于是 tests/l06_blackbox.rs / _v2 / _v3 / l06_lsp_surface.rs 整文件挂
//! `#![cfg(feature = "twins")]`，L06 的参考版黑盒覆盖从 133 例掉到 10 例（-92%）。
//! 这些被门掉的用例里，约 70 例其实**只依赖参考版**（调用 L06_string::run），
//! 断言语义与孪生无关，现在跟着一起消失——这就是真损失，本文件把它们救回来。
//!
//! ## 素材与锚点（逐例一一对应，用例名照抄，集成测试是独立 crate 不冲突）
//!
//! 1. **tests/l06_blackbox_v3.rs** —— 主体（原 70 个 #[test] 回收 67 例）。原文件
//!    的 `steady_state_redef_allowed_next_round`（fast::Tycker 稳态复用）、
//!    `mixed_batch_parity_scan`（纯 parity 扫描）、`redex_family_full_parity_scan`
//!    （纯 parity 网格扫描）三例无参考版可断言内容，未回收；
//! 2. **tests/l06_blackbox.rs** —— 前 12 个基础用例（u_and_hole_and_string …
//!    registered_decl_not_loosely_string），按任务口径只取这 12 例。该文件其余
//!    16 例中，只有 deep_church_and_strchain（fast::church_src/strchain_src）、
//!    steady_state_reuse（fast::Tycker）、workload_node_counts（Tycker + bench 对照）
//!    三例真正依赖 fast::；其余 13 例（error_cases / redefine_error /
//!    expected_universe_on_bad_annotation / parse_error_on_trailing_tokens /
//!    file_io_builtins / full_demo_parity / bb_recursive_* ）只是超出了「前 12 例」
//!    的回收范围，留作后续增量（见交付报告）；
//! 3. **tests/l06_blackbox_v2.rs** —— 10 例全收（pruning / (Lit,Lit) 恒败 / 跨轮隔离 /
//!    prim 触发角落 / 词法角落）。
//!
//! ## 移植纪律（不自己改写断言内容）
//!
//! - **只调用参考版** L06_string::run：不 use bump_spine_iter、不需要任何 feature，
//!   默认 cargo test --test l06_ref_blackbox 即跑；
//! - 用例名、期望输出串、错误 needle 逐字节照抄原文件；
//! - `assert_parity(src)`（ref↔twin 逐字节互检）**删除**；
//! - `assert_error_parity(src, needle)` 收窄为 `assert_error`：只断言参考版 Err 且
//!   Debug 文案含 needle；
//! - `assert_out(src, expect)` 去掉首行的 assert_parity，保留「参考版 Ok 且输出恰为
//!   expect」；
//! - 原文**只有** assert_parity 的纯 parity 用例（v1 的 4 例 + v2 pruning 1 例 +
//!   v3 deep_parenthesized_expr）退化为「参考版判定钉子」：原用例断言的是「两版
//!   判定一致」，其参考版半边即「参考版给出该判定」——这里按封印前参考版的实测
//!   判定钉住（绝大多数为 Ok，用 `assert_ref_accepts`；两处实测为 Err 的源用
//!   `assert_ref_rejects`，调用点有注释说明）。比 parity 弱，但仍是真实的参考版
//!   回归信号；
//! - 各例文档注释照原文保留：其中提到的「双实现 / 快版 / parity」是**原文件语境**，
//!   本文件只跑参考版那一半。
//!
//! 文件 IO 用例仍经 L06_string::FILE_IO_LOCK 串行（同原文件口径：本 crate 内嵌的
//! L06 单元测试用同一把锁，独立锁不互斥会撞同一物理文件）。

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L06_string/mod.rs"]
mod L06_string;

/// 文件 IO builtin 用固定文件名——本 crate 里所有做文件副作用的用例统一经模块内
/// 的这把锁串行（同原文件口径）。
use L06_string::FILE_IO_LOCK;

fn run_basic(src: &str) -> Result<String, L06_string::Error> {
    L06_string::run(src, 0)
}

fn run_basic_at(src: &str, path_id: u32) -> Result<String, L06_string::Error> {
    L06_string::run(src, path_id)
}

/// v3 `assert_out` 的参考版半边：去掉首行的 assert_parity（ref↔twin 互检），
/// 只留「参考版 Ok 且输出恰为 expect」。
fn assert_out(src: &str, expect: &str) {
    let out = run_basic(src).unwrap_or_else(|e| panic!("应 Ok：{src}\nerr: {e:?}"));
    assert_eq!(out, expect, "输出不符，src:\n{src}");
}

/// `assert_error_parity` 的参考版半边：参考版必须 Err，且 Debug 文案含 needle。
fn assert_error(src: &str, needle: &str) {
    assert!(run_basic(src).is_err(), "参考版应报错：{src}");
    assert!(
        format!("{:?}", run_basic(src).unwrap_err()).contains(needle),
        "参考版消息缺 {needle:?}：{src}"
    );
}

/// 纯 parity 用例的参考版半边：参考版必须接受该程序（Ok）。
fn assert_ref_accepts(src: &str) {
    assert!(run_basic(src).is_ok(), "参考版应接受：{src}");
}

/// 纯 parity 用例的参考版半边（判定为 Err 的源）：原用例只断言「两版判定一致」，
/// 参考版实测给出 Err——这里钉住该判定（比 parity 弱，仍是参考版回归信号）。
fn assert_ref_rejects(src: &str) {
    assert!(run_basic(src).is_err(), "参考版应拒绝：{src}");
}

/// 深递归用例的 256MB 栈线程（v1/v3 同款口径）。
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// 剥掉 Debug 文案里的 Span 注记（" @ 行,列"）：v3 陈旧函数部分 β-红ex 回归节的
/// 原文工具（那里用于 ref↔twin 全文比对，本文件只对参考版用）。
fn strip_spans(s: &str) -> String {
    let b = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        if b[i..].starts_with(b" @ ") {
            let mut j = i + 3;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 3 && j < b.len() && b[j] == b',' {
                let mut k = j + 1;
                while k < b.len() && b[k].is_ascii_digit() {
                    k += 1;
                }
                if k > j + 1 {
                    i = k;
                    continue;
                }
            }
        }
        out.push(b[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// 归一化文本：Ok 原样、Err 剥 Span（Err 文案全文比对形态）。
fn normalized_text(r: &Result<String, L06_string::Error>) -> String {
    match r {
        Ok(s) => s.clone(),
        Err(e) => strip_spans(&format!("{e:?}")),
    }
}

/// 参考版归一化文本：redex 回归节的参考版半边（Err 剥 Span 后钉项形态）。
fn normalized_ref_text(src: &str) -> String {
    normalized_text(&run_basic(src))
}

// ==============================================================================
// 回收自 tests/l06_blackbox.rs —— 前 12 个基础用例
// ==============================================================================

#[test]
fn u_and_hole_and_string() {
    assert_eq!(run_basic("println U").unwrap(), "U\n");
    // 字面量的类型是 String；打印原文（无引号——参考版 pretty 同款）
    assert_eq!(run_basic("println \"hello\"").unwrap(), "hello\n");
    assert_eq!(
        run_basic("def s : String = \"abc\"\nprintln s").unwrap(),
        "abc\n"
    );
}

#[test]
fn church_and_application() {
    let src = concat!(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n",
        "def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n",
        "def p0 : Nat = N => s => z => s (s z)\n",
        "def p1 : Nat = add p0 p0\n",
        "def p2 : Nat = add p1 p1\n",
        "println p2\n",
    );
    let out = run_basic(src).unwrap();
    // 8 个 s：λ N s z. s^8 z（pretty：binder 无点号，`=>` 接体）
    assert_eq!(
        out,
        "N=> s=> z=> s {s {s {s {s {s {s {s z}}}}}}}\n"
    );
}

#[test]
fn let_in_body_and_define_inside_lambda() {
    let src = concat!(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n",
        "def id [A : U] : A -> A = x => x\n",
        "def p0 : Nat = N => s => z => s (s z)\n",
        // let 体以分号接续（p_let 语法，`in` 不是关键字）；let 在 λ 体内
        // 即 define-inside-lambda 路径（平坦 def 区域 tip 判定）
        "def f : Nat -> Nat = u => let q : Nat = id u; id q\n",
        "println (f p0)\n",
    );
    assert_ref_accepts(src);
}

#[test]
fn implicit_insertion_and_pruning() {
    for src in [
        // 插入 + 求解
        "def id [A : U] : A -> A = x => x\nprintln (id U)\n",
        // 剪枝三例（README 的 pr1/pr2/pr3）
        "def pr1 = f => x => f x\nprintln pr1\n",
        "def pr2 = f => x => y => f x y\nprintln pr2\n",
        "def pr3 = f => f U\nprintln pr3\n",
        // 非线性 spine 可解（m 的类型不依赖非线性实参）
        concat!(
            "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
            "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
            "def the (A : U)(x : A) : A = x\n",
            "def m (A : U)(B : U) : U -> U -> U = _\n",
            "def test = a => b => the (Eq (m a a) (x => y => y)) refl\n",
            "println test\n",
        ),
        // 交集剪枝：m a b c =? m c b a 剪 a/c 取 b
        concat!(
            "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
            "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
            "def the (A : U)(x : A) : A = x\n",
            "def m : U -> U -> U -> U = _\n",
            "def test = a => b => c => the (Eq (m a b c) (m c b a)) refl\n",
            "println test\n",
        ),
    ] {
        assert_ref_accepts(src);
    }
}

#[test]
fn named_lambda_matches_by_name() {
    // 命名 binder 按名匹配 Π（Span 的 PartialEq 只比 data）
    assert_ref_accepts("def f : [A : U] -> A -> A = [A = a] x => x\nprintln f\n");
    // 名字不匹配 → 按 Π 名补 inserted binder——参考版判定为 Err（原用例只断言
    // 双版判定一致，参考版半边按其实际判定钉住）
    assert_ref_rejects("def g : [A : U] -> A -> A = [B = b] y => y\nprintln g\n");
}

#[test]
fn named_implicit_argument() {
    // 命名隐式实参：insertUntilName
    let src = concat!(
        "def konst [A : U] [B : U] : A -> B -> A = x => y => x\n",
        "println (konst [B = U] U U)\n",
    );
    assert_ref_accepts(src);
}

#[test]
fn string_builtins() {
    for src in [
        "def s : String = string_concat \"hello \" \"world\"\nprintln s\n",
        "def eq1 = str_eq \"foo\" \"foo\"\nprintln eq1\n",
        "def eq2 = str_eq \"foo\" \"bar\"\nprintln eq2\n",
        "def ind = str_indent2 \"line1\nline2\"\nprintln ind\n",
        // 部分应用卡住：quote 出 `string_concat x` 形态（decl 头 + 实参）
        "def f = x => string_concat x\nprintln f\n",
    ] {
        assert_ref_accepts(src);
    }
    assert_eq!(
        run_basic("def s : String = string_concat \"hello \" \"world\"\nprintln s").unwrap(),
        "hello world\n"
    );
    assert_eq!(run_basic("def e = str_eq \"a\" \"a\"\nprintln e").unwrap(), "true\n");
    assert_eq!(run_basic("def e = str_eq \"a\" \"b\"\nprintln e").unwrap(), "false\n");
}

#[test]
fn decl_table_and_globals() {
    // decl 表按名取值：String/Nat 的登记值（类型即值）；
    // miss 时**值**卡住但**类型**仍是 U——def 合法，println 打印卡住的名字
    let src = concat!(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n",
        "def st : U = string_to_global_type \"String\"\nprintln st\n",
        "def stn : U = string_to_global_type \"Nat\"\nprintln stn\n",
        "def stm : U = string_to_global_type \"Missing\"\nprintln stm\n",
    );
    assert_eq!(
        run_basic(src).unwrap(),
        "String\n(N: U) → (N → N) → N → N\nMissing\n"
    );
    // 可变全局族
    let src = concat!(
        "def store1 : U = create_global \"greeting\" \"hi\"\n",
        "def g1 : String = get_global \"greeting\"\nprintln g1\n",
        "def g2 : String = get_global_default \"greeting\" \"fallback\"\nprintln g2\n",
        "def g3 : String = get_global_default \"missing_name\" \"fallback\"\nprintln g3\n",
    );
    assert_eq!(
        run_basic("def s : U = create_global \"x\" \"v\"\ndef g : String = get_global \"x\"\nprintln g").unwrap(),
        "v\n"
    );
}

/// preprocess 的注释剥离感知字符串字面量：`//` / `/* */` 在字符串内不生效
/// （旧版纯文本剥离会把字面量截成未闭合字符串，解析失败）。
#[test]
fn string_with_comment_markers() {
    let src = concat!(
        "def url = \"http://example.com/a/*b*/c\"\n",
        "println url\n",
    );
    assert_eq!(run_basic(src).unwrap(), "http://example.com/a/*b*/c\n");
}

/// change_mutable 的 f 求值可再触发 prim（get_global）：旧版持有
/// borrow_mut 求值，重入即 BorrowError panic。
#[test]
fn change_mutable_reentrant_prim() {
    let src = concat!(
        "def g0 : U = create_global \"k\" \"v\"\n",
        "def upd : U = change_mutable \"k\" (s => string_concat s (get_global \"k\"))\n",
        "def v : String = get_global \"k\"\n",
        "println v\n",
    );
    assert_eq!(run_basic(src).unwrap(), "vv\n");
}

/// get_global 缺名不再 panic：保持卡住的 Decl 头（println 打卡住名）。
#[test]
fn get_global_missing_stays_stuck() {
    let src = "def v : String = get_global \"missing\"\nprintln v\n";
    assert_eq!(run_basic(src).unwrap(), "get_global missing\n");
}

/// String 与卡住 Decl 的宽松合一只对 decl 表**未登记**名放行；已登记名按
/// 登记类型把关（U 型 builtin 的卡住值不再冒充 String 型）。
#[test]
fn registered_decl_not_loosely_string() {
    // file_delete 已登记且类型 String -> U：其值作类型与 String 不再合一
    assert_error(
        "def bad : String = get_global \"file_delete\"\nprintln bad\n",
        "can't unify",
    );
    // 动态名（变量实参）同样收紧：get_global x 的类型不可静态得知
    assert_error(
        "def dyn(x : String) : String = get_global x\nprintln (dyn \"a\")\n",
        "can't unify",
    );
}

// ==============================================================================
// 回收自 tests/l06_blackbox_v2.rs —— 10 例
// ==============================================================================

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
    assert_ref_accepts(intersect);

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
    assert_ref_accepts(solve);

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
    assert_ref_accepts(vflex);

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
    // 参考版判定为 Err（原用例只断言双版判定一致，参考版半边按其实际判定钉住）
    assert_ref_rejects(escape_dep);
}

/// readme 招牌声明：`(Lit, Lit)` 恒败——连相同字面量也不可合一（参考版
/// unify 无字面量臂；快版 tag 7 位相等守卫如实复刻）。源码级可达形态是
/// 命名隐式实参把 refl 的 x 位钉成刚性 spine 实参：`F "a" ≡ F "a"`。
/// 探针实证：消息含 `LiteralIntro`（字面量确实进了 unify）；同/异字面量
/// 均 Err。消息带 span 偏移（快版全零），只做 needle 断言。
#[test]
fn lit_lit_unify_always_fails_even_identical() {
    let pre = concat!(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
        "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
    );
    for (xy, extra) in [
        ("(F \"a\") (F \"a\")", "[x = F \"a\"]"),
        ("(F \"a\") (F \"b\")", "[x = F \"a\"]"),
    ] {
        let src = format!(
            "{pre}def h (F : String -> U) : Eq [U] {xy} = refl [U] {extra}\nprintln \"unreachable\"\n"
        );
        let b = run_basic(&src);
        assert!(b.is_err(), "参考版应 Err：{src}");
        let side = "参考版";
        let e = b.unwrap_err();
        let msg = e.to_string();
        assert!(msg.contains("can't unify"), "{side} 消息缺 can't unify");
        // 字面量确实进入 unify（否则测试没打到 (Lit, Lit) 臂）
        assert!(msg.contains("LiteralIntro"), "{side} 消息缺 LiteralIntro：{msg}");
    }
}

/// 快版 `Tycker` 稳态复用时的轮间隔离：mutable_map / decl 表 / meta 编号
/// 随轮清空。参考版每次 `run` 新建 `Infer`，逐条对应断言。
#[test]
fn cross_round_isolation() {
    // 参考版每次 run 新建 Infer：跨轮隔离天然成立（原文同段保留）。
    run_basic("def a : U = create_global \"k\" \"v\"").unwrap();
    assert_eq!(
        run_basic("def g : String = get_global_default \"k\" \"fallback\"\nprintln g\n")
            .unwrap(),
        "fallback\n"
    );
    assert!(run_basic("println a\n").is_err());
}

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
}

/// def 覆盖 builtin 名 → **重定义报错**（L13 `fake_bind` 移植）：decl 表
/// 写入语义从静默覆盖改为定向报错，"同名 def 抹掉 prim"路径随之不可达。
#[test]
fn def_overrides_builtin_is_redefine_error() {
    let src = concat!(
        "def string_concat : String -> String -> String = x => y => x\n",
        "def r : String = string_concat \"a\" \"b\"\n",
        "println r\n",
    );
    assert_error(src, "redefine string_concat");
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
}

/// 未解 meta 的打印编号（?N 双洞递增）。
#[test]
fn unsolved_meta_numbering() {
    let src = "def a : String = _\nprintln a\ndef b : String = _\nprintln b\n";
    assert_eq!(run_basic(src).unwrap(), "?0\n?1\n");
}

/// `\\` / `\"` 转义、字符串尾 `\` 后接行注释、`""` 空字面量、解析失败的
/// 残余 token 定位。
#[test]
fn string_escapes_and_empty_literal() {
    // 源码里 `\\` 是转义的反斜杠（打印原文 `a\nb` 四个字符）
    assert_eq!(run_basic("println \"a\\\\nb\"\n").unwrap(), "a\\nb\n");
    // `\"` 打印引号
    assert_eq!(
        run_basic("println \"say \\\"hi\\\"\"\n").unwrap(),
        "say \"hi\"\n"
    );
    // 字符串尾的 `\` 后接行注释：内容 `a\`，注释正常剥离
    assert_eq!(
        run_basic("def s = \"a\\\\\" // comment\nprintln s\n").unwrap(),
        "a\\\n"
    );
    // 空字符串字面量（lexer 曾把 `end == 0` 误判为未闭合 → 整文件 parse error）
    assert_eq!(run_basic("println \"\"\n").unwrap(), "\n");
    assert_eq!(run_basic("def e : String = \"\"\nprintln e\n").unwrap(), "\n");
    assert_eq!(
        run_basic("println (string_concat \"\" \"x\")\n").unwrap(),
        "x\n"
    );
    assert_eq!(run_basic("println (str_eq \"\" \"\")\n").unwrap(), "true\n");
}

/// 解析失败的残余 token 定位：`;` 结尾这类最常见错误不再裸报 "parse error"。
#[test]
fn parse_error_reports_leftover_token() {
    assert_error("def a : U = U\n;\n", "leftover token `;`");
}

// ==============================================================================
// 回收自 tests/l06_blackbox_v3.rs —— 67 例（原 70 例中 3 例纯双实现口径未回收）
// ==============================================================================

/// 全转义表：`\n` `\t` `\r` `\0` 各打印真实控制字符（Rust 源里 `\\n` 是
/// ty 源的转义序列两字符）。
#[test]
fn escape_table_control_chars() {
    // \n → 换行
    assert_out("println \"a\\nb\"\n", "a\nb\n");
    // \t → 制表
    assert_out("println \"a\\tb\"\n", "a\tb\n");
    // \r → 回车
    assert_out("println \"a\\rb\"\n", "a\rb\n");
    // \0 → NUL
    assert_out("println \"a\\0b\"\n", "a\u{0}b\n");
}

/// 未知转义原样保留（`\` + 字符两字符原文）；`\\` 与未知转义相邻不串扰。
#[test]
fn unknown_escape_kept_verbatim() {
    assert_out("println \"a\\qb\"\n", "a\\qb\n");
    assert_out("println \"\\\\x\\y\"\n", "\\x\\y\n");
}

/// 多字节/emoji 内容：打印、拼接、str_eq 的字节级 parity（快版 string_concat
/// 是裸 memcpy + from_utf8_unchecked，多字节拼接不得产生坏 UTF-8）。
#[test]
fn unicode_multibyte_content() {
    assert_out("println \"你好，世界！🎉 αβγ\"\n", "你好，世界！🎉 αβγ\n");
    assert_out(
        "println (string_concat \"你\" \"好\")\n",
        "你好\n",
    );
    assert_out("println (str_eq \"你\" \"好\")\n", "false\n");
    assert_out("println (str_eq \"🎉α\" \"🎉α\")\n", "true\n");
    // 转义与多字节相邻（`\` 跳 2 字节的配对不得咬到多字节序列）
    assert_out("println \"a\\n你好\"\n", "a\n你好\n");
}

/// 超长串（2 万字符）：字面量引读、str_eq 逐字节相等/不等、两半拼接复原。
#[test]
fn very_long_literal() {
    let half1 = "ab".repeat(5000); // 10_000 chars
    let half2 = "cd".repeat(5000);
    let long = format!("{half1}{half2}");
    let src = format!(
        "def a : String = \"{long}\"\n\
         println a\n\
         def b : String = \"{long}\"\n\
         println (str_eq a b)\n\
         def c : String = string_concat a \"{half2}\"\n\
         println (str_eq a c)\n\
         println (string_concat \"{half1}\" \"{half2}\")\n"
    );
    let out = run_basic(&src).unwrap();
    assert_eq!(&out[..long.len()], &long[..], "长串引读必须逐字节一致");
    let rest = &out[long.len() + 1..];
    assert_eq!(rest, "true\nfalse\n{long}\n".replace("{long}", &long), "后三行不符");
}

/// 源码内原生换行/制表进字面量（lexer 不拒多行 token）；CRLF 行尾的 decl 流。
#[test]
fn raw_newline_tab_and_crlf() {
    // 字面量跨行：源码里就是真实换行
    assert_out("println \"l1\nl2\"\n", "l1\nl2\n");
    // 源码内原生制表符
    assert_out("println \"a\tb\"\n", "a\tb\n");
    // CRLF 行尾
    assert_out("def s : String = \"a\"\r\nprintln s\r\n", "a\n");
    // `\r\n` 在字面量内部原样保留（缩进只看 `\n`，`\r` 挂在行尾）
    assert_out("println (str_indent2 \"a\r\nb\")\n", "a\r\n  b\n");
}

/// 注释与字面量的互不干扰（v1 钉过 `//`/`/*` 在字面量内；这里攻击反向）：
/// 注释内出现引号不得开启字符串、行注释无换行收尾、空块注释。
#[test]
fn comments_containing_quotes_and_tail_cases() {
    // 行注释里有未闭合引号——不得把后续源码吞成字符串
    assert_out("def s = \"x\" // \"unclosed quote in comment\nprintln s\n", "x\n");
    // 块注释里有未闭合引号同理
    assert_out("/* \"unterminated */\nprintln \"y\"\n", "y\n");
    // 行注释在文件末尾无换行（注释吞到 EOF，println 在注释前）
    assert_out("println \"z\" // tail", "z\n");
    // 空块注释紧跟字面量
    assert_out("def s = \"w\"/**/\nprintln s\n", "w\n");
    // `*/` 出现在字面量里（无配对 `/*`）原样保留
    assert_out("println \"a*/b\"\n", "a*/b\n");
}

/// 文档化怪癖钉住：未闭合块注释静默吞掉余下全部 decl（readme「已知限制」
/// 明示的历史行为，无告警）——run 以 Ok("") 结束而非报错。
#[test]
fn unterminated_block_comment_swallows_rest() {
    assert_out("def s = \"a\" /* oops\nprintln s\n", "");
}

/// 残缺输入一律解析 Err（不 panic、不静默空转）。
#[test]
fn truncated_inputs_all_parse_error() {
    for src in [
        "",                                  // 空文件
        "   \n\t  ",                         // 纯空白
        "// only comment\n",                 // 纯行注释
        "/* only block */",                  // 纯块注释
        "println\n",                         // println 缺体
        "def println : U = U\n",             // 关键字当 def 名
        "def def = U\n",                     // 关键字当 def 名（第二 token）
        "println 42\n",                      // 数字不是 atom
        "def a : String = \"unclosed\n",     // 未闭合字符串（lex 失败）
        "println (string_concat \"a\" \"b\"\n", // 括号不闭
    ] {
        let b = run_basic(src);
        assert!(b.is_err(), "basic 应报错：{src:?}");
        assert!(
            format!("{:?}", b.unwrap_err()).contains("parse error"),
            "缺 parse error：{src:?}"
        );
    }
}

/// 残余 token 的偏移定位精确到字节（共用 parser，两版消息全文一致）。
/// 注意 op 的 pmatch 是贪心连续段：`???`/`%%` 各是**一个** Op token
///（不在 OP 表内 → kind=Op，内容保留整段）。
#[test]
fn leftover_token_offset_exact() {
    // "def a : U = U" 13 字节 + `\n` → `???` 起于 14，止于 17
    let src = "def a : U = U\n???\n";
    assert_eq!(src.find("???").unwrap(), 14);
    let b = run_basic(src).unwrap_err().to_string();
    assert!(b.contains("leftover token `???` @ 14,17"), "basic: {b}");
    // 字符串后的垃圾 op：`%%` 起于 12（println+空格+"x"+空格）
    let src2 = "println \"x\" %%\n";
    let b2 = run_basic(src2).unwrap_err().to_string();
    assert!(b2.contains("leftover token `%%` @ 12,14"), "basic: {b2}");
    // 单字符残余（`;`）的定位（v2 已钉消息，这里钉偏移）
    let src3 = "def a : U = U\n;\n";
    let b3 = run_basic(src3).unwrap_err().to_string();
    assert!(b3.contains("leftover token `;` @ 14,15"), "basic: {b3}");
}

/// 深层括号（300 层）解析与求值不爆栈、输出不变（大栈线程）。
#[test]
fn deep_parenthesized_expr() {
    let depth = 300;
    let src = format!(
        "println {}U{}\n",
        "(".repeat(depth),
        ")".repeat(depth)
    );
    let src2 = src.clone();
    let out = with_big_stack(move || run_basic(&src2).unwrap());
    assert_eq!(out, "U\n");
    with_big_stack(move || {
        assert_ref_accepts(&src);
    });
}

/// 30 连 λ 链的 pretty 逐字节（binder 名去重不触发——名字全异）。
#[test]
fn deep_lambda_chain_exact() {
    let binders: Vec<String> = (0..30).map(|i| format!("b{i}")).collect();
    let lam = binders.iter().map(|b| format!("{b} => ")).collect::<String>();
    let src = format!("def deep = {lam}b0\nprintln deep\n");
    let expect = format!(
        "{}b0\n",
        binders.iter().map(|b| format!("{b}=> ")).collect::<String>()
    );
    assert_out(&src, &expect);
}

/// 元数不足卡住（不 panic）：3 参的 report 只喂 2 参、1 参的 indent 空头、
/// 部分应用经 println 直接引读。
#[test]
fn prim_arity_short_stays_stuck() {
    assert_out("println (string_concat \"a\")\n", "string_concat a\n");
    assert_out("println (report_check_issue \"A\" \"m\")\n", "report_check_issue A m\n");
    assert_out("println (report_check_issue \"A\" \"m\" \"s\")\n", "report_check_issue A m s\n");
    assert_out("println str_indent2\n", "str_indent2\n");
    assert_out("println file_exists\n", "file_exists\n");
}

/// 实参为洞（未解 meta）卡住 + meta 编号连续性：洞进 prim 实参位不被求解、
/// 按创建顺序 ?0 ?1 打出。
#[test]
fn prim_hole_args_stuck_and_meta_numbering() {
    assert_out("println (str_indent2 _)\n", "str_indent2 ?0\n");
    assert_out("println (get_global _)\n", "get_global ?0\n");
    assert_out("println (string_concat _ _)\n", "string_concat ?0 ?1\n");
    // 编号跨 def 延续：?0 被第一个 def 捕获，后续洞是 ?1
    assert_out(
        "def s : String = string_concat \"a\" _\nprintln s\nprintln (string_concat \"b\" _)\n",
        "string_concat a ?0\nstring_concat b ?1\n",
    );
}

/// 嵌套 prim 链化简：str_eq 产出字面量喂 string_concat、indent 叠加、
/// concat 产出喂 indent（内层先触发，外层拿到的是字面量）。
#[test]
fn prim_nested_chains() {
    assert_out("println (string_concat (str_eq \"x\" \"y\") \"!\")\n", "false!\n");
    assert_out("println (string_concat (str_eq \"\" \"\") \"z\")\n", "truez\n");
    assert_out("def d = str_indent2 (str_indent2 \"a\nb\")\nprintln d\n", "a\n    b\n");
    assert_out("println (str_indent2 (string_concat \"x\n\" \"y\"))\n", "x\n  y\n");
    // 三层链：eq → concat → concat
    assert_out(
        "println (string_concat (string_concat (str_eq \"x\" \"y\") \"!\") \"?\")\n",
        "false!?\n",
    );
}

/// 卡住 prim 的 pretty 形态：实参位的应用要裹花括号（与 church 输出同款
/// 约定），字面量实参打印原文。
#[test]
fn stuck_prim_pretty_shapes() {
    // get_global "zz" 卡住 → 实参位整体是应用 → {…}
    assert_out(
        "println (string_concat \"P\" (get_global \"zz\"))\n",
        "string_concat P {get_global zz}\n",
    );
    // 两层卡住实参
    assert_out(
        "println (string_concat (get_global \"z1\") (get_global \"z2\"))\n",
        "string_concat {get_global z1} {get_global z2}\n",
    );
}

/// 命名实参喂 prim：insert_until_name 找不到隐式 Π 位 → 定向报错。
#[test]
fn prim_named_arg_is_error() {
    assert_error(
        "println (string_concat [y = \"b\"] \"a\")\n",
        "no named implicit arg",
    );
}

/// 隐式实参喂 Expl-only prim：icit mismatch 定向报错。
#[test]
fn prim_implicit_arg_is_icit_mismatch() {
    assert_error("println (str_eq [U] \"a\" \"b\")\n", "icit mismatch");
}

/// 非字面量实参（类型 U 的名字）喂 prim → 类型层先报 can't unify。
#[test]
fn prim_nonliteral_typed_arg_is_error() {
    assert_error("def n : U = U\nprintln (string_concat \"a\" n)\n", "can't unify");
}

/// report_check_issue 的元数/跳过/去重/顺序：module 位是洞（非字面量）
/// → 整条跳过且不建档；行级去重按整行相等；追加保序。
#[test]
fn report_check_issue_variants() {
    assert_out(
        concat!(
            "def i1 : U = report_check_issue \"A\" \"m\" \"s1\" \"msg1\"\n",
            "def i2 : U = report_check_issue \"A\" \"m\" \"s2\" \"msg2\"\n",
            "def i3 : U = report_check_issue \"A\" \"m\" \"s1\" \"msg1\"\n",
            "def issues : String = get_global \"CheckIssues\"\n",
            "println issues\n",
        ),
        "A|m|s1|msg1\nA|m|s2|msg2\n",
    );
    // 非 module（洞）→ 跳过：CheckIssues 未建档 → get_global 卡住
    assert_out(
        "def i0 : U = report_check_issue \"E9\" _ \"sig\" \"msg\"\nprintln (get_global \"CheckIssues\")\n",
        "get_global CheckIssues\n",
    );
    // 3 参不足卡住（不触发、不 panic）
    assert_out("println (report_check_issue \"A\" \"m\" \"s\")\n", "report_check_issue A m s\n");
}

/// st2g 取 builtin 名：值 = 注册的卡住头（打印名字本身）；st2g 自身亦可。
#[test]
fn st2g_of_builtin_names() {
    assert_out(
        concat!(
            "def t1 : U = string_to_global_type \"str_indent2\"\nprintln t1\n",
            "def t2 : U = string_to_global_type \"string_to_global_type\"\nprintln t2\n",
            "def t3 : U = string_to_global_type \"String\"\nprintln t3\n",
        ),
        "str_indent2\nstring_to_global_type\nString\n",
    );
}

/// st2g 取 def 的函数值：登记值整体（λ 打印原文形态）。
#[test]
fn st2g_of_def_function_value() {
    assert_out(
        "def f : U -> U = x => x\ndef t : U = string_to_global_type \"f\"\nprintln t\n",
        "x=> x\n",
    );
}

/// st2g 的动态（变量）名：应用时触发，卡住/命中都按当时 decl 表。
#[test]
fn st2g_dynamic_variable_name() {
    assert_out(
        concat!(
            "def dyn(x : String) : U = string_to_global_type x\n",
            "println (dyn \"String\")\n",
            "println (dyn \"get_global\")\n",
            "println (dyn \"Nope\")\n",
        ),
        "String\nget_global\nNope\n",
    );
}

/// st2g 取的是登记**值**（类型即值）：String 型 def 名的"动态类型"是
/// 字面量值本身 → 与 String 注解不可合一（unify 无 LiteralIntro 臂的
/// 推论面）；bare println（无注解）则 eval 走 map miss → 卡住的 prim 头。
#[test]
fn get_global_of_string_typed_def_name() {
    assert_out(
        "def s : String = \"a\"\nprintln (get_global \"s\")\n",
        "get_global s\n",
    );
    assert_error(
        "def s : String = \"a\"\ndef g : String = get_global \"s\"\nprintln g\n",
        "can't unify",
    );
}

/// 交错序列：create → 读 → change → 读 → change_default（已有则 f）→
/// change_default（缺失则建档为 default，f 不施加）。
#[test]
fn global_interleave_sequence() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"1\"\n",
            "println (get_global \"k\")\n",
            "def u1 : U = change_mutable \"k\" (s => string_concat s \"2\")\n",
            "println (get_global \"k\")\n",
            "def u2 : U = change_mutable_default \"k\" (s => string_concat s \"3\") \"x\"\n",
            "println (get_global \"k\")\n",
            "def u3 : U = change_mutable_default \"n2\" (s => string_concat s \"!\") \"fresh\"\n",
            "println (get_global \"n2\")\n",
        ),
        "1\n12\n123\nfresh\n",
    );
}

/// 同轮重复 create 覆盖；get_global_default 纯读不建档（miss 后再 get 仍卡住）。
#[test]
fn global_overwrite_and_default_readonly() {
    assert_out(
        concat!(
            "def a : U = create_global \"k\" \"1\"\n",
            "def b : U = create_global \"k\" \"2\"\n",
            "println (get_global \"k\")\n",
        ),
        "2\n",
    );
    assert_out(
        concat!(
            "def d1 : String = get_global_default \"fk\" \"d\"\n",
            "println d1\n",
            "println (get_global \"fk\")\n",
        ),
        "d\nget_global fk\n",
    );
}

/// global 存自身卡住头：create 时 map 还空 → get_global 卡在自己的
/// prim 头（`get_global k`）入表；之后 change_mutable 的 f 拿到的是
/// 卡住值 → 整体保持卡住（非字面量不触发）。
#[test]
fn global_self_stuck_storage() {
    assert_out(
        concat!(
            "def g : U = create_global \"k\" (get_global \"k\")\n",
            "println (get_global \"k\")\n",
            "def u : U = change_mutable \"k\" (s => string_concat s \"!\")\n",
            "println (get_global \"k\")\n",
        ),
        "get_global k\nstring_concat {get_global k} !\n",
    );
    // 有值（即便卡住）时 default 被忽略
    assert_out(
        concat!(
            "def g2 : U = create_global \"k2\" (get_global \"k2\")\n",
            "def d : String = get_global_default \"k2\" \"fb\"\nprintln d\n",
        ),
        "get_global k2\n",
    );
}

/// prim / 部分应用当 `change_mutable` 的函数实参（f 的类型与卡住 decl 的
/// 宽松臂互锁）：bare `str_indent2`（元数 1 立即触发）、`string_concat "P"`
/// （部分应用补触发）、bare `string_concat`（余域不是 String → 定向 Err）。
#[test]
fn global_prim_as_change_function() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"a\nb\"\n",
            "def u1 : U = change_mutable \"k\" str_indent2\n",
            "def v1 : String = get_global \"k\"\nprintln v1\n",
            "def g2 : U = create_global \"k2\" \"v\"\n",
            "def u2 : U = change_mutable \"k2\" (string_concat \"P\")\n",
            "def v2 : String = get_global \"k2\"\nprintln v2\n",
        ),
        "a\n  b\nPv\n",
    );
    // bare string_concat 的余域是 Pi 而非卡住 decl → can't unify
    assert_error(
        "def g : U = create_global \"k\" \"v\"\ndef u : U = change_mutable \"k\" string_concat\n",
        "can't unify",
    );
}

/// 闭包捕获时机：λ 体里的 get_global 在**应用时**求值——定义在前、
/// change 在后、应用最后 → 读到的是改后值。
#[test]
fn global_closure_capture_timing() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"v1\"\n",
            "def f : String -> String = x => string_concat x (get_global \"k\")\n",
            "def u1 : U = change_mutable \"k\" (s => string_concat s \"!\")\n",
            "println (f \"cur=\")\n",
        ),
        "cur=v1!\n",
    );
}

/// 同名 global 与 def 冲突（readme「已登记名按登记类型把关」的推论面）：
/// `create_global "k" "v"` 的第二实参类型 st2g"k" 查表得已登记的 U →
/// 与 String 定向 can't unify（写都写不进去）；bare `get_global "k"` 无
/// 注解不受影响——map miss 卡住头照打。
#[test]
fn global_name_clash_with_def() {
    assert_error(
        "def k : U = U\ndef g0 : U = create_global \"k\" \"v\"\n",
        "can't unify",
    );
    // bare println（无注解）：map miss → 卡住的 get_global prim 头
    assert_out("def k : U = U\nprintln (get_global \"k\")\n", "get_global k\n");
}

/// 空名/含空格键：map 键就是字面量内容，无转义无修剪。
#[test]
fn global_empty_and_space_keys() {
    assert_out(
        concat!(
            "def a : U = create_global \"\" \"empty\"\n",
            "def b : U = create_global \"a b\" \"spaced\"\n",
            "println (get_global \"\")\n",
            "println (get_global \"a b\")\n",
        ),
        "empty\nspaced\n",
    );
}

/// 未解 meta 存进 global：create 的实参位是洞 → 值是 Flex；get 回读打印 ?0。
#[test]
fn global_stores_unsolved_meta() {
    assert_out(
        concat!(
            "def g : U = create_global \"k\" _\n",
            "def v : String = get_global \"k\"\nprintln v\n",
        ),
        "?0\n",
    );
}

/// 洞当 global 键名：st2g 对非字面量卡住 → 实参类型是卡住的
/// `string_to_global_type ?0` 头（已登记名）→ 与 String 不再宽松 → Err。
#[test]
fn global_hole_name_is_error() {
    assert_error("def g : U = create_global _ \"v\"\n", "can't unify");
}

/// println 多行输出顺序（定义与字面量交错）。
#[test]
fn println_multi_line_order() {
    assert_out(
        concat!(
            "println \"one\"\n",
            "def a : String = \"two\"\n",
            "println a\n",
            "println \"three\"\nprintln (string_concat \"four\" \"five\")\n",
        ),
        "one\ntwo\nthree\nfourfive\n",
    );
}

/// β-redex 里触发 prim：λ 体在应用时求值，实参先于外层应用求值。
#[test]
fn beta_redex_with_prim() {
    assert_out("println ((x => string_concat x \"!\") \"a\")\n", "a!\n");
    assert_out("println ((x => x) \"raw\")\n", "raw\n");
}

/// let 无注解（洞注解可解）+ let 内触发 prim。
#[test]
fn let_without_annotation_with_prim() {
    assert_out(
        "def s = let t = \"a\"; string_concat t \"b\"\nprintln s\n",
        "ab\n",
    );
    assert_out(
        "def s : String = let t : String = \"L\"; string_concat t \"R\"\nprintln s\n",
        "LR\n",
    );
}

/// def 无返回类型注解（洞类型可解）+ 值引读。
#[test]
fn def_without_ret_annotation() {
    assert_out(
        "def f (x : U) = x\nprintln (f U)\nprintln f\n",
        "U\nx=> x\n",
    );
}

/// binder 名遮蔽 builtin（String）后再用 builtin 不受影响。
#[test]
fn binder_shadows_builtin_name() {
    assert_out(
        "def g (String : U) : U = String\nprintln (g U)\nprintln \"after\"\n",
        "U\nafter\n",
    );
}

/// Π 类型的 pretty：匿名域的箭头形态（金样）。
#[test]
fn pi_type_pretty() {
    assert_out("def T : U = U -> U\nprintln T\n", "U → U\n");
}

/// 递归 def 的新角度：**值级**自引用冻结在 def 时刻——体的求值发生在
/// 占位替换之前，`string_concat h "!"` 里的 h 命中占位（卡住 Decl 头）
/// 且 prim 对非字面量不触发 → 登记值整体卡住，println 引读安全（不发散；
/// 对照：λ 体里的自**应用**会在引读时经终值 β 展开，即 v1 记录的发散形
/// 态，不可 println——本套件不触发）。
#[test]
fn recursive_def_value_level_stuck() {
    assert_out(
        "def h : String = string_concat h \"!\"\nprintln h\n",
        "string_concat h !\n",
    );
}

/// def 先用后定义 → 定向 name not in scope（run 在首错即停）。
#[test]
fn use_before_def_is_scope_error() {
    assert_error("println later\ndef later : U = U\n", "name not in scope");
}

/// 文件组与 string 组的组合嵌套：写空内容、多字节内容、覆盖写、
/// exists("") → false；内容经 string_concat 拼装。
#[test]
fn file_io_combinations() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    let p = "l06_blackbox_v3_tmp.txt";
    let src = format!(
        concat!(
            "def w0 : U = file_write_all_text \"{p}\" \"\"\n",
            "def r0 : String = file_read_all_text \"{p}\"\nprintln r0\n",
            "def w1 : U = file_write_all_text \"{p}\" (string_concat \"你好\" \"世界\")\n",
            "def r1 : String = file_read_all_text \"{p}\"\nprintln r1\n",
            "def w2 : U = file_write_all_text \"{p}\" \"second\"\n",
            "def r2 : String = file_read_all_text \"{p}\"\nprintln r2\n",
            "println (file_exists \"\")\n",
            "println (str_eq r2 \"second\")\n",
        ),
        p = p
    );
    assert_eq!(
        run_basic(&src).unwrap(),
        "\n你好世界\nsecond\nfalse\ntrue\n"
    );
    let _ = std::fs::remove_file(p);
}

/// path_id 变化不影响 Ok 输出（Err 判定也不受影响）。
#[test]
fn path_id_variations() {
    let src = "def s : String = string_concat \"a\" \"b\"\nprintln s\n";
    for pid in [0u32, 7, 42] {
        assert_eq!(
            run_basic_at(src, pid).unwrap(),
            "ab\n",
            "path_id={pid} 的 Ok 输出应一致"
        );
    }
    // Err 判定与 path_id 无关
    assert!(run_basic_at("println nope\n", 3).is_err());
}

/// 【Bug-1 回归】st2g 把 def 的登记值（可以是 λ）当"动态类型"返回后，λ 值
/// 会以类型身份流入 unify：`get_global "f"` 的类型就是 f 的 λ 值，与
/// String 注解（LiteralType）比较时 η 臂曾对**不可应用值**做 v_app——
/// 参考版命中 impossible panic、快版压栈后 Err，判定发散。修复后两版
/// 一致 Err（λ 与非函数值的比较直接失败）。
#[test]
fn bug1_eta_on_inapplicable_literal() {
    assert_error(
        "def f : U -> U = x => x\ndef g : String = get_global \"f\"\nprintln g\n",
        "can't unify",
    );
}

/// 【Bug-1 回归】同族变体：η 的另一侧——λ 值（作为注解实参求出）在
/// `(_, Lam)` 臂吃 **Π 值**的应用，参考版同样 impossible panic。
#[test]
fn bug1_eta_on_inapplicable_pi() {
    assert_error(
        "def f : U -> U = x => x\ndef g : string_to_global_type \"f\" = \"s\"\nprintln g\n",
        "can't unify",
    );
    // change_mutable 的 f 实参位注解是 Π 值（dom_f），get_global "f" 的
    // 类型是 λ 值 → (Π, λ) 比较，同一守卫拦下
    assert_error(
        "def f : U -> U = x => x\ndef g : U = create_global \"k\" \"v\"\ndef u : U = change_mutable \"k\" (get_global \"f\")\n",
        "can't unify",
    );
}

/// 【Bug-1 回归】get_global_default 同族（Lit vs λ 值）。
#[test]
fn bug1_eta_on_inapplicable_default() {
    assert_error(
        "def f : U -> U = x => x\ndef g : String = get_global_default \"f\" \"z\"\n",
        "can't unify",
    );
}

/// st2g 对**函数 def** 名的取值在无注解路径照常（println 引读 λ 值，无
/// unify 参与）；st2g 结果（U 型）喂 string_concat 在类型层先报错。
#[test]
fn st2g_lambda_value_without_unify_is_ok() {
    assert_out(
        "def f : U -> U = x => x\ndef t : U = string_to_global_type \"f\"\nprintln t\n",
        "x=> x\n",
    );
    assert_error(
        "println (string_concat (string_to_global_type \"nope\") \"!\")\n",
        "can't unify",
    );
}

/// change_mutable 的 f 实参位允许绑定变量（Rigid 值 η/β 均安全——守卫
/// 不影响中性值路径）。
#[test]
fn change_mutable_with_bound_function_var() {
    assert_out(
        concat!(
            "def g0 : U = create_global \"k\" \"v\"\n",
            "def run (g : String -> String) : U = change_mutable \"k\" g\n",
            "def u : U = run (s => string_concat s \"!\")\n",
            "println (get_global \"k\")\n",
        ),
        "v!\n",
    );
}

/// def 的值在登记时刻**冻结**：r 先于 create 登记——r 的值是登记时 map
/// miss 的卡住 prim 头，后续 create 不回填（打印经 r 引读仍卡住）。
#[test]
fn def_value_freeze_order() {
    assert_out(
        concat!(
            "def r : String = get_global \"late\"\n",
            "def c : U = create_global \"late\" \"v\"\n",
            "println r\n",
            "println (get_global \"late\")\n",
        ),
        "get_global late\nv\n",
    );
}

/// 洞的 pruning 形态经 λ 引读：体是 `AppPruning ?m [x]`，eval 时掩码应用
/// → `?0 x`；应用后实参代入 → `?0 q`。
#[test]
fn flex_in_lambda_print() {
    assert_out("def f (x : String) : String = _\nprintln f\n", "x=> ?0 x\n");
    assert_out(
        "def f (x : String) : String = _\nprintln (f \"q\")\n",
        "?0 q\n",
    );
}

/// `_` 命名 binder 的打印：Var 位退化为 `@序号`（pretty 的 go_ix 约定）。
#[test]
fn underscore_binder_print() {
    assert_out("def f (_ : String) : String = _\nprintln f\n", "_=> ?0 @0\n");
}

/// 重复 binder 名的 fresh 去重（`a'` 后缀）。
#[test]
fn fresh_name_dedup() {
    assert_out("def d = a => a => a\nprintln d\n", "a=> a'=> a'\n");
}

/// str_eq 的 `'static` 真假字面量存进 global，再被部分应用 prim 改写
///（跨分配层的内容流转：'static → bump 拷贝）。
#[test]
fn static_bool_into_global_chain() {
    assert_out(
        concat!(
            "def b : U = create_global \"k\" (str_eq \"a\" \"a\")\n",
            "def u : U = change_mutable \"k\" (string_concat \"P\")\n",
            "println (get_global \"k\")\n",
        ),
        "Ptrue\n",
    );
}

/// def 别名 prim（0 参头登记为值），后续经别名补触发。
#[test]
fn def_alias_prim_zero_arg_refires() {
    assert_out(
        concat!(
            "def sc : String -> String -> String = string_concat\n",
            "println (sc \"a\" \"b\")\n",
        ),
        "ab\n",
    );
}

/// 隐式实例化与字面量：`f "s"` 的隐式 A 解为 LiteralType。
#[test]
fn implicit_instantiation_with_string() {
    assert_out(
        "def f [A : U] (x : A) : A = x\nprintln (f \"s\")\n",
        "s\n",
    );
}

/// 注解位全是洞：?0 ?1 编号与打印。
#[test]
fn hole_annotations_numbering() {
    assert_out("def f : _ -> _ = x => x\nprintln f\n", "x=> x\n");
}

/// global 不能存类型/函数值（第二实参类型 st2g"k" 是卡住 decl，与 U/
/// Π 无宽松臂）——只有 String 值与同名卡住 decl 可入表。
#[test]
fn global_cannot_store_types_or_functions() {
    assert_error("def g : U = create_global \"k\" U\n", "can't unify");
    assert_error(
        "def f : U -> U = x => x\ndef g : U = create_global \"k\" f\n",
        "can't unify",
    );
}

/// get_global_default 的 default 位是卡住 prim 头：miss 时原样返回。
/// （default 位的类型是 st2g"m"——卡住 decl 与卡住 decl 的宽松臂只认
/// 同名/字面量，异名 prim 头在类型层先报错；同名 `get_global "m"` 可过。）
#[test]
fn default_value_is_stuck_prim() {
    assert_out(
        "println (get_global_default \"m\" (get_global \"m\"))\n",
        "get_global m\n",
    );
    assert_error(
        "println (get_global_default \"m\" (get_global \"zz\"))\n",
        "can't unify",
    );
}

/// 100 对 create/get 的顺序烟雾（输出顺序 = decl 序）。
#[test]
fn many_globals_smoke() {
    let mut src = String::new();
    let mut expect = String::new();
    for i in 0..100 {
        src.push_str(&format!("def c{i} : U = create_global \"k{i}\" \"v{i}\"\n"));
        src.push_str(&format!("println (get_global \"k{i}\")\n"));
        expect.push_str(&format!("v{i}\n"));
    }
    assert_out(&src, &expect);
}

/// 洞对上 λ 值类型：fresh meta 的类型是 λ 值（不求解、仅打印 ?0）。
#[test]
fn hole_against_lambda_typed_annotation() {
    assert_out(
        "def f : U -> U = x => x\ndef g : string_to_global_type \"f\" = _\nprintln g\n",
        "?0\n",
    );
}

/// LiteralIntro 值当 Π 定义域（st2g 取 String 型 def 的登记值）：λ 本体
/// 可定义可打印（体不触域）；但字面量实参落进 (LiteralType, LiteralIntro)
/// 的无臂比较 → Err（(Lit,·) 家族的推论面）。
#[test]
fn literal_intro_as_pi_domain() {
    assert_out(
        concat!(
            "def s : String = \"a\"\n",
            "def h : string_to_global_type \"s\" -> U = x => U\n",
            "println h\n",
        ),
        "x=> U\n",
    );
    assert_error(
        "def s : String = \"a\"\ndef h : string_to_global_type \"s\" -> U = x => U\nprintln (h \"a\")\n",
        "can't unify",
    );
}

/// 多字节未知名报错路径（ident 词法的 unicode 分支 + Debug 文案）。
#[test]
fn multibyte_unknown_ident_error() {
    assert_error("println 你好\n", "name not in scope");
}

/// Church 编码前奏（Eq / refl / the；触发 unification 的标准模式）。
///
/// 原文件里这是节常量（redex 回归节），参考版半边照抄。
const CHURCH: &str = "def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = _ => px => px
def the(A : U)(x: A): A = x
";

/// 最小复现（L05/L07 同款输入的 L06 语法移植）：`m1 : [A : U] -> U -> U`
/// 的两个部分应用做 Church-Eq。解 `m1` 的隐式槽时 `?0` 的 spine 里挂了
/// `?5 a b`；随后 `?5` 被 flex_flex 解成**双 λ 转发解**，而引用它的 spine
/// 值（建链早于求解）仍是陈旧位模式。修复前快版报错混入红ex
/// `App(Lam("b" …), Var)`；修复后两版都给干净形态 `?5 a b`。
#[test]
fn redex_regression_eq_swapped_args() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U = _\ndef t = a => b => the (Eq (m1 b) (m1 a)) refl\n"
    );
    let bt = normalized_ref_text(&src);
    // 无红ex 形态（Lam 节点 = `(b' => ?5 a b') b` 的重拼残留）
    // 干净形态 ?5 a b 钉死（参考版即此形态）
    assert!(
        bt.contains("App(App(Meta(MetaVar(5)), Var(Ix(2)), Expl), Var(Ix(1)), Expl)"),
        "参考版文案缺干净形态 ?5 a b：{bt}"
    );
}

/// 同族镜像：实参顺序互换（`m1 a` vs `m1 b`），失败方向镜像。
#[test]
fn redex_regression_eq_args_order_mirror() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U = _\ndef t = a => b => the (Eq (m1 a) (m1 b)) refl\n"
    );
    let bt = normalized_ref_text(&src);
    assert!(
        bt.contains("App(App(Meta(MetaVar(5)), Var(Ix(3)), Expl), Var(Ix(2)), Expl)"),
        "参考版文案缺干净形态 ?5 b a：{bt}"
    );
}

/// 同族：`m1` 多一个显式域（P 的定义域带箭头），转发解照旧、红ex 照旧。
#[test]
fn redex_regression_extra_domain() {
    let src = format!(
        "{CHURCH}def m1[A : U] : U -> U -> U = _\ndef t = a => b => the (Eq (m1 b) (m1 a)) refl\n"
    );
    let bt = normalized_ref_text(&src);
    assert!(
        bt.contains("App(App(Meta(MetaVar(5)), Var(Ix(2)), Expl), Var(Ix(1)), Expl)"),
        "参考版文案缺干净形态 ?5 a b：{bt}"
    );
}

/// 可解例（Ok 路径对照）：η 展开后经 intersect 剪掉差异槽，方程可解、
/// 程序成功——修复不得影响中性路径的正常引读。
#[test]
fn redex_family_solvable_ok() {
    let src = format!(
        "{CHURCH}def m1 : U -> U -> U = _\ndef t = a => b => the (Eq (m1 a) (z => m1 b z)) refl\nprintln U\n"
    );
    assert_out(&src, "U\n");
}

/// `preprocess` 注释替换**保持字节长度**（L07 review R7）：非 ASCII 注释
/// 之后 token 的 span 偏移必须仍对应原文本。
///
/// 旧实现每个注释字符只写一个空格：`// 中文注释` 之后所有偏移前移
/// `len_utf8 - 1` 字节。回归钉用"解析错误消息里的偏移"读回原文坐标——
/// 该消息由共用 parser 产出，与两版实现无关，因此能直接校验 preprocess。
#[test]
fn preprocess_comment_keeps_byte_offsets() {
    // "def a : U = U\n" = 14 字节；`// 中文`（2+2 字 × 3 字节）占 2+1+6 = 9 字节 + \n
    let src = "def a : U = U\n// 中文注释\n???\n";
    let want = src.find("???").unwrap();
    let basic = run_basic(src).unwrap_err().to_string();
    assert!(
        basic.contains(&format!("@ {want},")),
        "basic 残余 token 偏移应保持原文坐标 {want}（非 ASCII 注释不得前移），实际：{basic}"
    );
    // 块注释同理
    let src2 = "def b : U = U\n/* 块注释 */\n???\n";
    let want2 = src2.find("???").unwrap();
    let out2 = run_basic(src2).unwrap_err().to_string();
    assert!(
        out2.contains(&format!("@ {want2},")),
        "块注释后偏移应保持原文坐标 {want2}，实际：{out2}"
    );
}

/// 无注解 `let` 走推断快路径（L07 同款）：不再为 binder 造闭合 meta。
///
/// 回归钉取**编号面**：注解位是洞的 `let` 若先造 meta 再解，会占掉一个
/// `?N` 编号并使后续洞编号后移。快路径直接推断类型，编号保持连续。
#[test]
fn let_without_annotation_skips_binder_meta() {
    // let 无注解 + 后续洞：洞编号应从 ?0 起（旧路径会先消耗 ?0 给 binder）
    assert_out(
        "def f : _ -> _ = x => x\nprintln f\n",
        "x=> x\n",
    );
    // 深层嵌套无注解 let（快路径专治的 O(n²) 形态）：只钉终值与 parity
    let mut src = String::from("def r : U = ");
    let n = 60;
    for i in 0..n {
        src.push_str(&format!("let v{i} = U; "));
    }
    src.push_str("U\nprintln r\n");
    assert_out(&src, "U\n");
}
