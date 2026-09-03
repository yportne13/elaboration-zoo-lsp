//! L06_string 黑盒测试套件。
//!
//! 被测对象：`src/L06_string`（elaboration-zoo `06-string` 风格的 Rust 移植：
//! L05 的 typed metas + pruning 之上加 **String 字面量类型 / decl 表按名
//! 取值 / builtin 注册表（prim 于应用时触发）/ 可变全局**），黑盒入口是
//! `run(src, path_id)`（预处理 → 解析 decl 序列 → 逐条推断 → println 的
//! nf 经 pretty 输出），经 `#[path]` 独立编译进本测试 crate。
//!
//! 双 oracle：
//!   1. 期望输出字符串 —— 参考版实际输出核对（demo 全串与上游 06 的
//!      pretty 形态一致：λ 无反斜杠 `x => e`、隐式实参裹 `{}`、字面量打印
//!      原文内容）；
//!   2. 参考版（`mod.rs` 及其子模块）↔ 性能版（`bump_spine_iter.rs`）
//!      **Ok 输出逐字节互检**；Err 只比判定（错误文案 `{:?}` 直接 Debug
//!      引读项/名字 Span，携带源码偏移——快版项不存偏移，同构但数字不同，
//!      属文档化偏差）。
//!
//! 与 L05 的语义差别（本套件专门覆盖）：
//!   - **String 字面量**：`"..."` 是 `LiteralType`（打印 `String`）的
//!     `LiteralIntro` 值；`(Lit, Lit)` 不可合一（参考版 unify 无该臂）。
//!   - **decl 表**：顶层 def 登记值/类型；`string_to_global_type "名"` 取
//!     登记值（miss 保持卡住 Decl 头，与 LiteralType 宽松合一）。
//!   - **builtin prim**：`string_concat` / `str_eq` / `str_indent2` /
//!     文件 IO 组在**应用时**触发（元数足够且实参为字面量），否则卡住。
//!   - **可变全局**：`create_global` / `change_mutable{,_default}` /
//!     `get_global{,_default}` 读写运行期全局表。

#![feature(pattern)]

#[path = "../src/list.rs"]
mod list;

#[path = "../src/parser_lib.rs"]
mod parser_lib;

#[path = "../src/L06_string/mod.rs"]
mod L06_string;

use L06_string::bump_spine_iter as fast;

/// 文件 IO builtin 用固定文件名——本 crate 里所有做文件副作用的用例
/// （含 `#[path]` 编进来的 L06 内嵌测试）统一经模块内的这把锁串行：
/// 黑盒自带一把独立锁会与内嵌测试的锁互不互斥，同一物理文件就会竞争。
use L06_string::FILE_IO_LOCK;

fn run_basic(src: &str) -> Result<String, L06_string::Error> {
    L06_string::run(src, 0)
}

fn run_fast(src: &str) -> Result<String, L06_string::Error> {
    fast::run_fast(src, 0)
}

/// Oracle 2：参考版与性能版的 Ok 输出逐字节一致；Err 判定一致。
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

/// 双实现都 Err 且消息含 needle（只断言不含偏移的稳定片段；Error 字段
/// 私有，经 Debug 形态 `Error("…")` 读内容）。
fn assert_error_parity(src: &str, needle: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    assert!(b.is_err(), "basic 应报错：{src}");
    assert!(f.is_err(), "fast 应报错：{src}");
    assert!(
        format!("{:?}", b.unwrap_err()).contains(needle),
        "basic 消息缺 {needle:?}"
    );
    assert!(
        format!("{:?}", f.unwrap_err()).contains(needle),
        "fast 消息缺 {needle:?}"
    );
}

// 基础形态与 println 输出
// --------------------------------------------------------------------------------

#[test]
fn u_and_hole_and_string() {
    assert_eq!(run_basic("println U").unwrap(), "U\n");
    assert_parity("println U");
    // 字面量的类型是 String；打印原文（无引号——参考版 pretty 同款）
    assert_eq!(run_basic("println \"hello\"").unwrap(), "hello\n");
    assert_parity("println \"hello\"");
    assert_eq!(
        run_basic("def s : String = \"abc\"\nprintln s").unwrap(),
        "abc\n"
    );
    assert_parity("def s : String = \"abc\"\nprintln s");
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
    assert_parity(src);
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
    assert_parity(src);
}

// 隐式 / 剪枝（L04/L05 语义回归）
// --------------------------------------------------------------------------------

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
        assert_parity(src);
    }
}

#[test]
fn named_lambda_matches_by_name() {
    // 命名 binder 按名匹配 Π（Span 的 PartialEq 只比 data）
    assert_parity("def f : [A : U] -> A -> A = [A = a] x => x\nprintln f\n");
    // 名字不匹配 → 按 Π 名补 inserted binder
    assert_parity("def g : [A : U] -> A -> A = [B = b] y => y\nprintln g\n");
}

#[test]
fn named_implicit_argument() {
    // 命名隐式实参：insertUntilName
    let src = concat!(
        "def konst [A : U] [B : U] : A -> B -> A = x => y => x\n",
        "println (konst [B = U] U U)\n",
    );
    assert_parity(src);
}

// String / builtin / decl 表（L06 特色）
// --------------------------------------------------------------------------------

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
        assert_parity(src);
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
    assert_parity(src);
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
    assert_parity(src);
    assert_eq!(
        run_basic("def s : U = create_global \"x\" \"v\"\ndef g : String = get_global \"x\"\nprintln g").unwrap(),
        "v\n"
    );
}

// 修复/行为变更回归（review 探针转正）
// --------------------------------------------------------------------------------

/// preprocess 的注释剥离感知字符串字面量：`//` / `/* */` 在字符串内不生效
/// （旧版纯文本剥离会把字面量截成未闭合字符串，解析失败）。
#[test]
fn string_with_comment_markers() {
    let src = concat!(
        "def url = \"http://example.com/a/*b*/c\"\n",
        "println url\n",
    );
    assert_eq!(run_basic(src).unwrap(), "http://example.com/a/*b*/c\n");
    assert_parity(src);
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
    assert_parity(src);
}

/// get_global 缺名不再 panic：保持卡住的 Decl 头（println 打卡住名）。
#[test]
fn get_global_missing_stays_stuck() {
    let src = "def v : String = get_global \"missing\"\nprintln v\n";
    assert_eq!(run_basic(src).unwrap(), "get_global missing\n");
    assert_parity(src);
}

/// String 与卡住 Decl 的宽松合一只对 decl 表**未登记**名放行；已登记名按
/// 登记类型把关（U 型 builtin 的卡住值不再冒充 String 型）。
#[test]
fn registered_decl_not_loosely_string() {
    // file_delete 已登记且类型 String -> U：其值作类型与 String 不再合一
    assert_error_parity(
        "def bad : String = get_global \"file_delete\"\nprintln bad\n",
        "can't unify",
    );
    // 动态名（变量实参）同样收紧：get_global x 的类型不可静态得知
    assert_error_parity(
        "def dyn(x : String) : String = get_global x\nprintln (dyn \"a\")\n",
        "can't unify",
    );
}

/// parser 要求 decl 流吃完全部 token：`;` / 垃圾 token 的静默截断改为
/// 解析报错（run 返回 Err，不再 panic/空转）。
#[test]
fn parse_error_on_trailing_tokens() {
    assert_error_parity("def pr1 = f => x => f x;\nprintln pr1\n", "parse error");
    assert_error_parity("println U\nGARBAGE!!!\n", "parse error");
}

#[test]
fn file_io_builtins() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    let src = concat!(
        "def p = \"l06_blackbox_tmp.txt\"\n",
        "def w : U = file_write_all_text p \"hello file\"\n",
        "def a : U = file_append_all_text p \"!\"\n",
        "def r : String = file_read_all_text p\n",
        "println r\n",
        "def e1 : String = file_exists p\nprintln e1\n",
        "def d : U = file_delete p\n",
        "def e2 : String = file_exists p\nprintln e2\n",
    );
    assert_parity(src);
    assert_eq!(
        run_basic(src).unwrap(),
        "hello file!\ntrue\nfalse\n"
    );
}

#[test]
fn full_demo_parity() {
    let _guard = FILE_IO_LOCK.lock().unwrap();
    // 参考版内嵌 demo 的全量串（pruning + 字面量 + builtin + decl 表 +
    // 可变全局 + 文件 IO + report）：双实现逐字节，且关键行金样。
    let out = run_basic(L06_string::DEMO_SRC).unwrap();
    assert!(out.contains("hello world!\n"), "{out}");
    assert!(out.contains("true\nfalse\n"), "{out}");
    assert!(out.contains("hello file!\n"), "{out}");
    assert!(
        out.contains("String\n(N: U) → (N → N) → N → N\n"),
        "{out}"
    );
    assert!(out.contains("hi!\nhi!\nfallback\nhi!?\nfresh\n"), "{out}");
    assert!(out.contains("E1|demo_mod|sig|message\n"), "{out}");
    assert_parity(L06_string::DEMO_SRC);
}

// 报错路径（判定 + 稳定消息片段）
// --------------------------------------------------------------------------------

#[test]
fn error_cases() {
    assert_error_parity("println nope", "name not in scope");
    // icit 失配：显式 Π 头收到隐式实参（消息不含 span，可全文比对）
    assert_error_parity(
        "def g : U -> U -> U = x => y => x\nprintln (g [U])",
        "icit mismatch",
    );
    // 命名 λ 不可推断
    assert_error_parity("def h = [B = x] y => y\nprintln h", "infer named lambda");
    // 命名隐式实参找不到
    assert_error_parity(
        "def konst [A : U] [B : U] : A -> B -> A = x => y => x\nprintln (konst [C = U] U U)",
        "no named implicit arg",
    );
    // 字面量不是类型
    assert_error_parity("def bad : U = \"not a type\"\nprintln bad", "can't unify");
}

// 深负载与稳态
// --------------------------------------------------------------------------------

/// 深负载（参考版 eval/quote/rename 全递归，深栈线程里跑——L05 黑盒同款
/// `with_big_stack` 口径）。
fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn deep_church_and_strchain() {
    // church k=11（2048）：println 输出逐字节（输出 ~2048 节点的 pretty；
    // 双实现的 pretty 都递归——整测放深栈线程）
    let church = fast::church_src(11) + "println p11\n";
    let f = with_big_stack({
        let church = church.clone();
        move || run_fast(&church).unwrap()
    });
    let b = with_big_stack(move || run_basic(&church).unwrap());
    assert_eq!(f, b, "church k=11 判定与参考版不一致");
    // strchain 512：每层 builtin prim 触发
    let chain = fast::strchain_src(9) + "println s511\n";
    assert_parity(&chain);
    assert_eq!(run_fast(&chain).unwrap().len(), 512 + 1);
}

#[test]
fn steady_state_reuse() {
    let src = concat!(
        "def s : String = string_concat \"a\" \"b\"\n",
        "def g : U = create_global \"k\" \"v\"\n",
        "def v : String = get_global \"k\"\nprintln v\n",
    );
    let mut steady = fast::Tycker::new();
    let r1 = steady.run_input(src, 0).unwrap();
    let r2 = steady.run_input(src, 0).unwrap();
    assert_eq!(r1, r2, "稳态两轮不一致");
    assert_eq!(r1, run_fast(src).unwrap(), "稳态与一次性不一致");
}

/// 负载生成器节点数公式（bench 的正确性口径在黑盒再钉一层）。
#[test]
fn workload_node_counts() {
    for (k, expect) in [(9u32, 2u64 * (1 << 10) + 4), (11, 2 * (1 << 12) + 4)] {
        let src = fast::church_src(k);
        let raw = L06_string::parser::parser(&L06_string::preprocess(&src), 0).unwrap();
        let mut t = fast::Tycker::new();
        assert_eq!(t.bench_check_nf(&raw), expect, "church k={k} 节点数");
        assert_eq!(
            L06_string::bench_check_nf(&raw),
            expect,
            "church k={k} 参考版节点数"
        );
    }
    let src = fast::strchain_src(9);
    let raw = L06_string::parser::parser(&L06_string::preprocess(&src), 0).unwrap();
    let mut t = fast::Tycker::new();
    assert_eq!(t.bench_check_nf(&raw), 1, "strchain 节点数");
    assert_eq!(L06_string::bench_check_nf(&raw), 1, "strchain 参考版节点数");
}
