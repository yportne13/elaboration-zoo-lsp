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

// 上轮 L01-L12 同族修复移植回归探针（docs/review-l01l12/FINAL.md §2.2/§2.3）
// --------------------------------------------------------------------------------

/// 超大整数字面量（> u64::MAX）不得 panic：推解析错误并退化为 Hole
/// （L11/L12 parser 同款修复；L13 的原生 Nat 数字字面量路径同族）。
#[test]
fn probe_oversized_int_literal_recoverable() {
    let src = "def x = 99999999999999999999999999\n";
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            // L13 解析树含 Rc 非 Send：断言收进线程内，只回传错误数
            L13_namespace::parser::parser(src, 0).map(|(_, errs)| errs.len())
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "超大整数不应 panic");
    let errs = res.unwrap().expect("parser 应返回 Some");
    assert!(errs > 0, "超大整数应产生解析错误");
}

/// 自递归宏不得栈溢出：受展开深度上限（256）保护，超限给解析错误
/// （L11/L12 MacroDepthGuard 同款；L13 parser 三处展开点均加守卫）。
#[test]
fn probe_macro_self_recursion_depth_limit() {
    let src = "macro_rules m { () => { m } }\ndef x = m\n";
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            // 同上：解析树非 Send，只回传错误数
            L13_namespace::parser::parser(src, 0).map(|(_, errs)| errs.len())
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "自递归宏不应栈溢出");
    let errs = res.unwrap().expect("parser 应返回 Some");
    assert!(errs > 0, "自递归宏应产生解析错误而非无限展开");
}

/// R2 移植修复回归（对齐 l10/l11/l12 探针）：`impl[T] Say for List[T]`
/// 不得假匹配泛型目标 `Say[T]`。L13 的 `val_match` 原第三臂 or-模式
/// `(_, Rigid) | (Rigid, _)` 允许**目标侧** rigid 被实例构造子绑定
/// （`f two` 会错选 List 实例答 `"list"`），与本函数文档注释宣称的单向
/// 语义相悖；改为仅实例侧绑定（对齐 L10/L11 的 `match_typ`）后无实例
/// → Err。参考/快版共用同一 `Synth`（twin 经 `Synth::val_match` 复用），
/// 一处修复两版同判。
#[test]
fn synth_rigid_generic_not_falsely_matched() {
    let src = r#"
trait Say {
    def say: String
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

impl[T] Say for List[T] {
    def say: String = "list"
}

def f[T](x: T): String = x.say

enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

println (f two)
"#;
    assert!(
        run_basic(src).is_err(),
        "泛型 T 不得被假匹配成 List；basic={:?}",
        run_basic(src)
    );
    assert_parity(src);
}

/// P13 补钉（A6 矩阵复扫路由）：enum 隐式无标注域钉 U(0) 回归（L09
/// `parity_enum_struct_impl_hole_pinned_u0` / L12 同款 4 源）。修复前：
/// 域洞保留 → 第 2+ 参数域为 AppPruning 部分应用 meta（`?m A`），使用点
/// 显式供给枚举隐式实参（`p1[Nat][Bool]`）需解该 meta，invert_go 对非
/// 变量 spine 实参直接 Stuck → 误报 can't unify；钉 U(0) 后声明处消除
/// 该 meta。L13 触发链核实：parser p_pi_impl_binder 允许 `[A]` 无标注 →
/// Hole、fresh_meta AppPruning、invert_go `_ => Err(Stuck)`、
/// check_universe 只解洞的类型 meta。含合法索引族（显式标注 + 显式索引）
/// 形态确认不受钉影响（源为 L08 R1 病态源教训修正版：枚举级显式索引
/// 参数、返回类型完全应用——L13 同构于 legacy_tests 的 `Vec[A](len: Nat)`
/// 形态）。L13 语法适配已核实：multiline 构造子、p_arg 的无名方括号实参
/// （`[Nat]` → Icit::Impl）。
#[test]
fn parity_enum_struct_impl_hole_pinned_u0() {
    for src in [
        // enum：多隐式无标注参数 + 显式实例化（修复的原始触发形态）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Bool {\n    true\n    false\n}\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\nprintln (p1[Nat][Bool] zero true)\n",
        // enum：无标注隐式参数 + 注解处显式实例化 + 全显式构造子应用
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Bool {\n    true\n    false\n}\nenum P1[A, B] {\n    p1[A, B](a: A, b: B) -> P1[A][B]\n}\ndef s1: P1[Nat][Bool] = p1[Nat][Bool][Nat][Bool] zero true\nprintln s1\n",
        // struct：多类型参数 + 投影（脱糖路径同一臂）
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nstruct Pair[A, B] {\n    fst: A\n    snd: B\n}\ndef p = new Pair(succ zero, zero)\nprintln p.fst\n",
        // 显式标注的隐式域与显式索引不动：annotated 索引族形态仍通过
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\nenum Q[A : Type 0](a: A) {\n    q[A](a: A) -> Q[A] a\n}\ndef t: Q[Nat] zero = q[Nat] zero\nprintln t\n",
    ] {
        // is_ok（参考版）+ 双版结果诊断输出 + parity
        let b = run_basic(src);
        let f = run_fast(src);
        assert!(
            b.is_ok(),
            "参考版 Err（隐式无标注域未钉 U(0)/钉后误拒/子用例病态？），src:\n{src}\nbasic={b:?}\nfast={f:?}"
        );
        assert_parity(src);
    }
}
