//! L13_namespace 双 oracle 互检套件（参考版 `run` ↔ 性能版 `bump_spine_iter::
//! run_fast`）。`#[path]` 只编 list.rs / bimap.rs / parser_lib.rs /
//! parser_lib_resilient.rs / L13_namespace/mod.rs（不含 LSP / L02-L12），
//! 迭代快数倍（tests/l12_fast_parity.rs 同款）。
//!
//! 判据：**Ok 输出逐字节一致 / Err 判定一致**。错误文案的 Span 偏移、
//! meta 编号（`?N`）与 Debug-Span 数字是文档化偏差，比对前归一化。
//!
//! # 语言面注意（共用 parser 的形态约束）
//!
//! 枚举构造子 / match case 必须**换行分隔**（`many0_sep(kw(EndLine))`）。
//! 把构造子写在同一行（如 `enum Nat { zero succ(x: Nat) }`）时，恢复性
//! 解析会在第二个构造子处丢弃后续 token——两版拿到同样残缺的 AST，行为
//! 依旧逐字节一致，但该形态的语言面**无构造子可用**（`succ` 未注册，
//! 程序在首个引用处报 name-not-in-scope）。本套件早期版本全部用单行
//! 枚举书写，parity"全绿"实为两版同错的假阴性；现已改用 multiline 声明
//! 提供真覆盖（`parity_multiline_enum`）。
//!
//! # 覆盖
//! - multiline 枚举（**标准声明形态**）：构造子子模式匹配 + 求值、递归
//!   def + match（natadd / match_src 形态）、非穷尽报错（单臂 match 的
//!   文案逐字节一致：`non-exhaustive pattern: ... not covered`）。
//! - 单行枚举形态的行为钉子（两版同错，防分叉回归）。
//! - Err 判定 + 归一化正文：name-not-in-scope、universe 报错。
//! - 稳态复用（trait/可变全局跨轮清空）。


#[path = "../src/list.rs"]
mod list;

#[path = "../src/bimap.rs"]
mod bimap;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L13_namespace/mod.rs"]
mod L13_namespace;

use L13_namespace::bump_spine_iter as fast;

/// 在大栈线程里跑参考版 `run`。线程边界只传归一化后的 Err 文案
/// （L13 的 `Error` 携带非 Send 的重试闭包）。
fn run_basic(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L13_namespace::run(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, String> {
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || fast::run_fast(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// Err 文案归一化：剥掉 Span 自定义 Debug 的 `@ N` / `@ N,M`、派生
/// Debug 的 `start_offset/end_offset/path_id: N` 数字，以及 meta 编号
/// `?N`（双实现 meta 分配序列不同，文档化偏差）。
fn norm_err(e: &str) -> String {
    let mut out = String::with_capacity(e.len());
    let b = e.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        if b[i] == b'@' && i + 1 < b.len() && b[i + 1] == b' ' {
            let mut j = i + 2;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 2 {
                if j < b.len() && b[j] == b',' {
                    let mut k = j + 1;
                    while k < b.len() && b[k].is_ascii_digit() {
                        k += 1;
                    }
                    if k > j + 1 {
                        j = k;
                    }
                }
                out.push_str("@ _");
                i = j;
                continue;
            }
        }
        if b[i] == b'?' && i + 1 < b.len() && b[i + 1].is_ascii_digit() {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                out.push_str("?_");
                i = j;
                continue;
            }
        }
        let rest = &e[i..];
        let mut matched = false;
        for key in ["start_offset: ", "end_offset: ", "path_id: "] {
            if rest.starts_with(key) {
                let mut j = i + key.len();
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
                if j > i + key.len() {
                    out.push('_');
                    i = j;
                    matched = true;
                    break;
                }
            }
        }
        if matched {
            continue;
        }
        let ch = e[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Oracle：Ok 逐字节 / Err 判定 + 归一化正文一致。
fn assert_parity(src: &str) {
    let b = run_basic(src);
    let f = run_fast(src);
    match (&b, &f) {
        (Ok(b), Ok(f)) => assert_eq!(
            b, f,
            "Ok 输出双实现不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
        ),
        (Err(b), Err(f)) => assert_eq!(
            b, f,
            "Err 正文（归一化后）双实现不一致，src:\n{src}\n--- basic ---\n{b}\n--- fast ---\n{f}"
        ),
        _ => panic!(
            "判定不一致（basic={}，fast={}），src:\n{src}\nbasic-err={:?}\nfast-err={:?}",
            b.as_ref().map(|_| "Ok").unwrap_or("Err"),
            f.as_ref().map(|_| "Ok").unwrap_or("Err"),
            b.as_ref().err(),
            f.as_ref().err(),
        ),
    }
}

// 基础语言面（单行枚举声明——共用 parser 的恢复性解析会吞掉第二个及之后的
// 构造子，两版同错；此处钉住该形态的逐字节一致，真覆盖见 parity_multiline_enum）
// --------------------------------------------------------------------------------

#[test]
fn parity_single_line() {
    // enum + 构造子匹配（含子模式绑定 `succ(x)`）
    assert_parity(
        "enum Nat { zero succ(x: Nat) } def two = succ (succ zero) \
         def mono(n: Nat): Nat = match n { case zero => zero case succ(x) => x } \
         println (mono two)\n",
    );
    // 递归 def + match（natadd 雏形，含求值）
    assert_parity(
        "enum Nat { zero succ(x: Nat) } \
         def add(x: Nat, y: Nat): Nat = match x { case zero => y case succ(n) => succ (add n y) } \
         def p0 : Nat = add (succ (succ zero)) (succ zero) \
         println p0\n",
    );
    // 字符串拼接（无 prelude 时 String 无 `+` 实例——两版一致报错）
    assert_parity("println (\"a\" + \"b\" + \"c\")\n");
    // 纯字符串字面量输出
    assert_parity("println \"hello\"\n");
}

// Err 判定 parity（判定一致 + 归一化正文一致）
// --------------------------------------------------------------------------------

#[test]
fn parity_errors() {
    // 名字不在 scope
    assert_parity("def bad = nope\n");
    // 期望宇宙（`: Nat` 无 prelude 时不解析——两版一致报 name not in scope）
    assert_parity("def bad : Nat = Type 0\n");
    // 单臂 match 的非穷尽（multiline 枚举：`succ` 真实存在，非穷尽真实可判，
    // 文案逐字节一致 = "non-exhaustive pattern: `succ` not covered"）
    assert_parity(
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\
         def mono(n: Nat): Nat = match n { case zero => zero }\n",
    );
}

// multiline 枚举（标准声明形态：构造子换行分隔）——原"已知缺陷"场景
// --------------------------------------------------------------------------------

#[test]
fn parity_multiline_enum() {
    // 构造子子模式匹配 + 求值（multiline match 臂；原 ACCESS_VIOLATION
    // 崩溃场景——快版 nat_step_value 对中性字段无 tag 守卫的野指针解引用）
    assert_parity(
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\
         def two = succ (succ zero)\n\
         def mono(n: Nat): Nat =\n  match n {\n    case zero => zero\n    case succ(x) => x\n  }\n\
         println (mono two)\n",
    );
    // inline 单行 match 臂（同一 match，臂内布局不影响语义）
    assert_parity(
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\
         def three = succ (succ (succ zero))\n\
         def pred(n: Nat): Nat = match n { case zero => zero case succ(x) => x }\n\
         println (pred three)\n",
    );
    // 递归 def + match（natadd / match_src 形态：自递归 + 构造子链求值）
    assert_parity(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\
         def add(x: Nat, y: Nat): Nat =\n    match x {\n        case zero => y\n        case succ(n) => succ (add n y)\n    }\n\
         def p0 : Nat = succ (succ zero)\n\
         def p1 : Nat = add p0 p0\n\
         def p2 : Nat = add p1 p1\n\
         println p2\n",
    );
    // 自递归 def（match_src 形态：全局占位/覆盖 + 运行时首匹配）
    assert_parity(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\
         def f_0(x : Nat) : Nat =\n    match x {\n        case zero => zero\n        case succ(n) => succ (f_0 n)\n    }\n\
         def two : Nat = succ (succ zero)\n\
         println (f_0 two)\n",
    );
}

// 卡住 Call 的实参序（L13 Call/OpCall 专用面）
// --------------------------------------------------------------------------------

#[test]
fn parity_stuck_call_arg_order() {
    // `wrap_match_in_call` 把 λ 链体的 Match 包成 Call(name, Var 链, Match)；
    // 该 Call 在 λ 下求值仍卡住 → quote 的 CallAsm 必须按自然序输出实参。
    // 回归：曾经逐槽 done.pop 得逆序、还与 icits 错配（2+ 实参全倒序）。
    assert_parity(
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\
         def add(x: Nat, y: Nat): Nat =\n  match x {\n    case zero => y\n    case succ(n) => succ (add n y)\n  }\n\
         def two: Nat = succ (succ zero)\n\
         def f = (a => add a two)\n\
         println f\n",
    );
    assert_parity(
        "enum Nat {\n  zero\n  succ(x: Nat)\n}\n\
         def add3(x: Nat, y: Nat, z: Nat): Nat =\n  match x {\n    case zero => y\n    case succ(n) => succ (add3 n y z)\n  }\n\
         def two: Nat = succ (succ zero)\n\
         def f = (a => add3 a two zero)\n\
         println f\n",
    );
}

// trait 实例选择（flex goal 推迟）
// --------------------------------------------------------------------------------

#[test]
fn parity_trait_flex_goal_instance_pick() {
    // 回归：trait 求解的 flex 判据曾用 `v_tag(v) == 5`（只认裸 meta），漏掉
    // meta 头链 `?m x`——goal 参数恰是后者时不推迟，Phase 1 的 val_match 对
    // 每个实例恒真，Phase 2 按登记序选中错误实例（core prelude `a + 0` 命中
    // Add[String,String] for String，报 `can't unify expected: String find: Nat`）。
    // 这个源是 core prelude 的最小化形态（op.typort 的 Add + String 实例 +
    // nat.typort 的 Nat 实例），String 实例先登记是触发条件。
    assert_parity(
        "def outParam[A](a: A): A = a\n\
         trait Add[T, O: outParam(Type 0)] {\n    def +(that: T): O\n}\n\
         impl Add[String, String] for String {\n    def +(that: String): String = string_concat this that\n}\n\
         enum Nat {\n    zero\n    succ(n: Nat)\n}\n\
         def nat_add(x: Nat, y: Nat): Nat =\n    match y {\n        case zero => x\n        case succ(n) => succ (nat_add x n)\n    }\n\
         impl Add[Nat, Nat] for Nat {\n    def +(that: Nat): Nat = nat_add this that\n}\n\
         def f(a: Nat): Nat = a + zero\n\
         println f\n",
    );
}

// 稳态复用（trait/可变全局跨轮清空）
// --------------------------------------------------------------------------------

#[test]
fn steady_state_reuse() {
    // 全局链连续两轮：上一轮的 mutable 全局不得泄漏（test6 同款）
    let gsrc = "enum Nat { zero succ(x: Nat) } \
         def ttt = let useless1 = create_global \"Nat\" 2; \
         let useless2 = change_mutable(\"Nat\", z => succ(z)); \
         get_global \"Nat\" \
         println ttt\n";
    let mut steady = fast::Tycker::new();
    let a = steady.run_input(gsrc, 0).unwrap();
    let b = steady.run_input(gsrc, 0).unwrap();
    assert_eq!(a, b, "跨轮 mutable 全局泄漏");
    assert_parity(gsrc);
}

// 解析护栏（L11/L12 同款探针，f51a0e4 家族在 L13 的贴齐验证）
// --------------------------------------------------------------------------------

/// 超大整数字面量（>u64::MAX）不得 panic：推一条解析错误并退化为 Hole。
#[test]
fn probe_big_int_literal_recoverable() {
    let src = "def x = 99999999999999999999999999\n";
    // parser 返回值含 Rc（!Send）不能跨线程传递：Some/错误条数的解包与
    // 判定在线程内完成，只回传 Send 的 (是否 Some, 解析错误条数)。
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || match L13_namespace::parser::parser(src, 0) {
            Some((_, errs)) => (true, errs.len()),
            None => (false, 0usize),
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "超大整数不应 panic");
    let (some, n_errs) = res.unwrap();
    assert!(some, "parser 应返回 Some");
    assert!(n_errs > 0, "超大整数应产生解析错误");
}

/// 自递归宏受展开深度上限保护（thread_local + RAII，上限 256），不得栈溢出。
#[test]
fn probe_macro_self_recursion_depth_limit() {
    let src = "macro_rules m { () => { m } }\ndef x = m\n";
    // 同上：!Send 的解析结果不留出线程，线程只回传 (是否 Some, 解析错误条数)。
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || match L13_namespace::parser::parser(src, 0) {
            Some((_, errs)) => (true, errs.len()),
            None => (false, 0usize),
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "自递归宏不应栈溢出");
    let (some, n_errs) = res.unwrap();
    assert!(some, "parser 应返回 Some");
    assert!(n_errs > 0, "自递归宏应产生解析错误而非无限展开");
}
