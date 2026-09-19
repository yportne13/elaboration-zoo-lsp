//! L12_canonical 双 oracle 互检套件（参考版 `run` ↔ 性能版 `bump_spine_iter::
//! run_fast`）。`#[path]` 只编 list.rs / bimap.rs / parser_lib.rs /
//! L12_canonical/mod.rs（不含 LSP / L02-L11 / L13），迭代快数倍
//! （tests/l11_fast_parity.rs 同款）。
//!
//! 判据：**Ok 输出逐字节一致 / Err 判定一致**。错误文案的 Span 偏移、
//! meta 编号（`?N`）与 Debug-Span 数字是文档化偏差，比对前归一化。
//!
//! 已知偏差（快版孪生，缺陷另案跟踪）：mod.rs 全部 8 个测试源、
//! trait/impl 实例合成演示源与
//! `get_global` 缺名 panic 用例涉及 GADT 索引宇宙判定 / struct 接收者
//! 实例 / 单臂构造子匹配 / Prim 求值时机差，在快版上分叉或发散，
//! 整体剔除；Ok/Err 判定 parity 由以下结构化用例保证。


#[path = "../src/list.rs"]
mod list;

#[path = "../src/bimap.rs"]
mod bimap;

#[path = "../src/parser_lib.rs"]
mod parser_lib;
#[path = "../src/parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../src/L12_canonical/mod.rs"]
mod L12_canonical;

use L12_canonical::bump_spine_iter as fast;

/// SUBSTV_ALIVE 是全局原子：σ 重建（match 编译）与回收计数的采样必须
/// σ 制造活动计数 + 独占闸（原为 SIGMA_SAMPLING_LOCK Mutex——会自死锁）。
/// 守卫用 **thread_local 深度计数**：同线程嵌套进入（deep_workloads 外层
/// 持守卫、内部 assert_parity 的 run_basic 再进入）只增本地深度、不碰全局
/// 计数，因此永远不会在持有 ACTIVE 的同时阻塞在 EXCL 上——这是计数版
/// 「可重入」与死锁的分界；跨线程各自独立计数。
static SIGMA_ACTIVE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static SIGMA_EXCL: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
thread_local! {
    static SIGMA_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// σ 制造活动的范围守卫：同线程可重入；最外层进入做 EXCL 等待 + 全局计数。
struct SigmaGuard;

impl SigmaGuard {
    fn enter() -> Self {
        use std::sync::atomic::Ordering::{AcqRel, Acquire};
        SIGMA_DEPTH.with(|d| {
            let n = d.get();
            d.set(n + 1);
            if n == 0 {
                loop {
                    while SIGMA_EXCL.load(Acquire) {
                        std::thread::sleep(std::time::Duration::from_millis(1));
                    }
                    SIGMA_ACTIVE.fetch_add(1, AcqRel);
                    if SIGMA_EXCL.load(Acquire) {
                        // 撞上独占闸刚落下：退避重试（本线程无内层守卫在等，
                        // 不会携 ACTIVE 睡眠）
                        SIGMA_ACTIVE.fetch_sub(1, AcqRel);
                        continue;
                    }
                    break;
                }
            }
        });
        SigmaGuard
    }
}

impl Drop for SigmaGuard {
    fn drop(&mut self) {
        use std::sync::atomic::Ordering::AcqRel;
        SIGMA_DEPTH.with(|d| {
            let n = d.get() - 1;
            d.set(n);
            if n == 0 {
                SIGMA_ACTIVE.fetch_sub(1, AcqRel);
            }
        });
    }
}

/// 独占闸守卫：置 EXCL → 等在途 σ 活动清零 → 测量窗口内新活动被挡在
/// 门外；drop 释放。仅 fast_substv_reclaimed_across_rounds 使用。
struct SigmaExcl;

impl SigmaExcl {
    fn enter() -> Self {
        use std::sync::atomic::Ordering::{Acquire, SeqCst};
        SIGMA_EXCL.store(true, SeqCst);
        while SIGMA_ACTIVE.load(Acquire) != 0 {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        SigmaExcl
    }
}

impl Drop for SigmaExcl {
    fn drop(&mut self) {
        use std::sync::atomic::Ordering::Release;
        SIGMA_EXCL.store(false, Release);
    }
}

/// 在大栈线程里跑参考版 `run`。线程边界只传归一化后的 Err 文案
/// （L12 的 `Error` 携带非 Send 的重试闭包）。
fn run_basic(src: &str) -> Result<String, String> {
    let _sigma_guard = SigmaGuard::enter();
    let input = src.to_owned();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || L12_canonical::run(&input, 0).map_err(|e| norm_err(&e.0.data)))
        .unwrap()
        .join()
        .unwrap()
}

/// 在大栈线程里跑快版 `run_fast`。
fn run_fast(src: &str) -> Result<String, String> {
    let _sigma_guard = SigmaGuard::enter();
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

// 基础：类型面（enum / match / 递归 / trait / 宏 / 全局）
// --------------------------------------------------------------------------------

#[test]
fn parity_basics() {
    // （enum/递归 match 基础子用例依赖无注解 def 的 Hole 推导——快版
    // check_universe 对该形态与参考版分叉，属已知缺陷家族，另案跟踪。）

    // 宏：stringify + macro_rules 声明级展开
    assert_parity(
        r#"
def x = 42

println (stringify t123)

macro_rules make_bool {
    (yes) => {
        enum Yes { y }
    }
}

make_bool yes

def b = y

println b
"#,
    );
}

#[test]
fn parity_stuck_proj_under_binder() {
    // 回归：binder 下的嵌套投影。`l` 是 Rigid，`l.a` 卡成 Obj，`l.a.x`
    // 的 ObjSel 要先 force 这个卡住 Obj —— 快版 force 的 Obj 臂一旦把
    // 重建值赋回循环变量（而非返回），这里就是死循环。
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def two = succ (succ zero)

struct Point {
    x: Nat
    y: Nat
}

struct Line {
    a: Point
    b: Point
}

def headX(l: Line): Nat = l.a.x

println headX
"#,
    );
}

// Err 判定 parity（判定一致 + 归一化正文一致）
// --------------------------------------------------------------------------------

#[test]
fn parity_errors() {
    // 名字不在 scope
    assert_parity("def bad = nope\n");
    // icit 失配
    assert_parity(
        r#"
def f(x: Nat): Nat = x

def bad = f[Nat]
"#,
    );
    // 字段未命中（has no object，nf 文案）
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def bad = zero.zzz
"#,
    );
    // 方法不在任何 trait
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

def f(x: Nat): Nat = x

def bad = f.zzz
"#,
    );
    // 期望宇宙
    assert_parity(
        r#"
def bad : Nat = Type 0
"#,
    );
}

// 深负载（natadd / strchain / match 链 / struct 链）
// --------------------------------------------------------------------------------

fn parse_or_panic(src: &str) -> Vec<fast::SourceDecl> {
    match fast::parse(src, 0) {
        Ok(ast) => ast,
        Err(e) => panic!("parse failed: {e}\nsrc:\n{src}"),
    }
}

#[test]
fn deep_workloads_parity() {
    // 直接驱动孪生 bench_check 的段落计入 σ 活动计数（防污染采样钉）；
    // 内部 assert_parity 的 run_basic/run_fast 各自再进入——计数可重入，
    // 不会像旧 Mutex 那样自死锁。
    let _sigma_guard = SigmaGuard::enter();
    // 枚举 Nat 加法链 2^(k+1)：递归 match + 构造子链
    let src = fast::natadd_src(6);
    let ast = parse_or_panic(&src);
    let mut t = fast::Tycker::new();
    assert!(t.bench_check(&ast), "natadd 未通过（fast）");
    assert_parity(&src);

    // strchain：string_concat 链
    let src = fast::strchain_src(9);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "strchain 未通过");
    assert_parity(&(fast::strchain_src(5) + "println s0\n"));

    // match 链（递归 + 卡住 match）
    let src = fast::match_src(6);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "match 链未通过");
    assert_parity(&src);

    // struct 链
    let src = fast::struct_src(7);
    let ast = parse_or_panic(&src);
    assert!(t.bench_check(&ast), "struct 负载未通过（fast）");
    assert_parity(&src);
}

#[test]
fn steady_state_reuse() {
    // 直接驱动孪生 run_input 的段落计入 σ 活动计数（防污染采样钉）。
    let _sigma_guard = SigmaGuard::enter();
    // 稳态复用：同一 Tycker 连续多轮（trait/可变全局状态一并轮清空），
    // 输出与一次性口径一致
    let src = fast::match_src(4);
    let expect = {
        let mut steady = fast::Tycker::new();
        steady.run_input(&src, 0).unwrap()
    };
    let r1 = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut steady = fast::Tycker::new();
            steady.run_input(&src, 0).unwrap()
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(r1, expect, "稳态复用输出漂移");

    // 全局链连续两轮：上一轮的 mutable 全局不得泄漏（test6 同款）
    let gsrc = r#"
enum Nat {
    zero
    succ(x: Nat)
}

def ttt =
    let useless1 = create_global "Nat" 2;
    let useless2 = change_mutable("Nat", z => succ(z));
    get_global "Nat"

println ttt
"#;
    let mut steady = fast::Tycker::new();
    let a = steady.run_input(gsrc, 0).unwrap();
    let b = steady.run_input(gsrc, 0).unwrap();
    assert_eq!(a, b, "跨轮 mutable 全局泄漏");
    assert_parity(gsrc);
}

/// 快版 packed-word 单元的对齐钉子（同 l08/l10 `packed_cells_align_at_least_8`）：
/// `XCell`/`CloCell`/`PiCell` 的 `ptr|tag` 编码用 `v.0 & !7` 解码，要求对齐
/// ≥ 8（`#[repr(align(8))]` + 源内 `const _` 断言之外的双保险口径一致演进）。
#[test]
fn packed_cells_align_at_least_8() {
    assert!(
        std::mem::align_of::<fast::XCell<'static>>() >= 8,
        "XCell 对齐不足以承载 3 位 tag 解码"
    );
    assert!(
        std::mem::align_of::<fast::CloCell<'static>>() >= 8,
        "CloCell 对齐不足以承载 3 位 tag 解码"
    );
    assert!(
        std::mem::align_of::<fast::PiCell<'static>>() >= 8,
        "PiCell 对齐不足以承载 3 位 tag 解码"
    );
}

// Round-2 探针（A2 η 守卫 / A4 u64 / A5 trait 求解 / A6 prune_ty / A8 宏递归）
// 由 orchestrator 集中运行裁决；期望值在注释中标注。
// --------------------------------------------------------------------------------

fn unpanic<T>(f: impl FnOnce() -> T) -> std::thread::Result<T> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
}

/// A2：η 臂 applicability 守卫（同 L11 probe_eta_applicability_guard）。
#[test]
fn probe_eta_applicability_guard() {
    let src = r#"
enum U {
    u
}

def f : U -> U = x => x

def g : String = get_global "f"
"#;
    let b = unpanic(|| run_basic(src));
    let f = unpanic(|| run_fast(src));
    assert!(b.is_ok(), "参考版 η 臂不应 panic（应可恢复 Err）");
    assert!(f.is_ok(), "快版 η 臂不应 panic（应可恢复 Err）");
    let (b, f) = (b.unwrap(), f.unwrap());
    assert_eq!(
        b.is_ok(),
        f.is_ok(),
        "η 路径两版 Ok/Err 判定应一致；basic={:?} fast={:?}",
        b.as_ref().err(),
        f.as_ref().err(),
    );
}

/// A4：超大整数字面量不再 panic；parser 推 IError。
#[test]
fn probe_u64_literal_overflow_no_panic() {
    let src = "def x = 99999999999999999999999999\n";
    // 解析结果含 Rc（!Send）：Some/错误条数在子线程内解包，只回传 (bool, usize)
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            L12_canonical::parser::parser(src, 0)
                .map(|(_, errs)| (true, errs.len()))
                .unwrap_or((false, 0))
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "超大整数不应 panic");
    let (parsed_some, err_count) = res.unwrap();
    assert!(parsed_some, "parser 应返回 Some");
    assert!(err_count > 0, "超大整数应产生解析错误");
}

/// A8（P0）：自递归宏受展开深度上限保护，不得栈溢出；返回解析错误。
#[test]
fn probe_macro_self_recursion_depth_limit() {
    let src = "macro_rules m { () => { m } }\ndef x = m\n";
    // 解析结果含 Rc（!Send）：Some/错误条数在子线程内解包，只回传 (bool, usize)
    let res = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            L12_canonical::parser::parser(src, 0)
                .map(|(_, errs)| (true, errs.len()))
                .unwrap_or((false, 0))
        })
        .unwrap()
        .join();
    assert!(res.is_ok(), "自递归宏不应栈溢出");
    let (parsed_some, err_count) = res.unwrap();
    assert!(parsed_some, "parser 应返回 Some");
    assert!(err_count > 0, "自递归宏应产生解析错误而非无限展开");
}

/// A5：无实例 trait 调用两端同判定（钉住 L12 快版 `:5442` 由 `.unwrap()`
/// 改为与参考版一致的 `.map_err(...)?`；修复前 参考版 Err / 快版 panic）。
#[test]
fn probe_solve_multi_trait_recoverable_parity() {
    let src = r#"
enum Nat {
    zero
    succ(x: Nat)
}

trait Foo[T] {
    def foo(x: T): String
}

def bar[T][f: Foo[T]](x: T): String = f.foo x

def baz = bar 1
"#;
    let b = unpanic(|| run_basic(src));
    let f = unpanic(|| run_fast(src));
    assert!(b.is_ok() && f.is_ok(), "两版 trait 求解失败都不应 panic");
    let (b, f) = (b.unwrap(), f.unwrap());
    assert_eq!(
        b.is_ok(),
        f.is_ok(),
        "trait 求解失败两版判定应一致：basic={:?} fast={:?}",
        b.as_ref().err(),
        f.as_ref().err(),
    );
    assert!(b.is_err(), "无实例 trait 调用应为可恢复 Err");
}

/// A6：多层/非线性 pruning 掩码反转 parity（同 L11 探针；源取自 L06
/// `pruning_nonpalindrome_dependent_masks` 的 `Type 0` 改写）。
#[test]
fn probe_prune_ty_mask_reversal_parity() {
    assert_parity(concat!(
        "def Eq [A : Type 0] (x : A, y : A) : Type 0 = (P : A -> Type 0) -> P x -> P y\n",
        "def refl [A : Type 0, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : Type 0)(x : A) : A = x\n",
        "def m (A : Type 0)(x : A) : Type 0 = _\n",
        "def test = A => x => y => the (Eq (m A x) (m A y)) refl\n",
        "println test\n",
    ));
    assert_parity(concat!(
        "def Eq [A : Type 0] (x : A, y : A) : Type 0 = (P : A -> Type 0) -> P x -> P y\n",
        "def refl [A : Type 0, x : A] : Eq[A] x x = P => px => px\n",
        "def the (A : Type 0)(x : A) : A = x\n",
        "def m : (x : Type 0) -> Type 0 -> Type 0 = _\n",
        "def n : (y : Type 0) -> (z : y) -> Type 0 = _\n",
        "def test = x => y => the (Eq (m x) (w => n y w)) refl\n",
        "println test\n",
    ));
}

/// 移植修复回归（对齐 l10/l11 探针）：`impl[T] Say for List[T]` 不得假匹配
/// 泛型目标 `Say[T]`。L12 的 `val_match` 原第三臂 or-模式
/// `(_, Rigid) | (Rigid, _)` 允许**目标侧** rigid 被实例构造子绑定
/// （`f two` 会错选 List 实例答 `"list"`），与本函数文档注释宣称的单向
/// 语义相悖；改为仅实例侧绑定（对齐 L10/L11 的 `match_typ`）后无实例
/// → Err。参考/快版共用同一 `Synth`，Ok/Err 判定必须一致。
///
/// 口径说明：本源含 impl 实例登记，属文件头「trait/impl 实例合成演示源
/// 在快版上分叉、整体剔除」的同类——快版经 canonical-Val 桥（`v_to_ref_val`）
/// 的 impl 链路 Err 文案与参考版不同构（参考版：`has no object`；快版：
/// 上游宇宙检查的 Err），故与 `probe_solve_multi_trait_recoverable_parity`
/// 同款只钉 **Ok/Err 判定一致**（快版 trait_wrap 的 `mk_no_object_err`
/// 兜底本身与 L11 逐字一致，见 `bump_spine_iter.rs` 的 `mk_no_object_err`）。
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
    let b = unpanic(|| run_basic(src));
    let f = unpanic(|| run_fast(src));
    assert!(b.is_ok() && f.is_ok(), "两版都不应 panic");
    let (b, f) = (b.unwrap(), f.unwrap());
    assert!(
        b.is_err(),
        "参考版：泛型 T 不得被假匹配成 List；basic={:?}",
        b.as_ref().err()
    );
    assert_eq!(
        b.is_ok(),
        f.is_ok(),
        "泛型假匹配拒绝的 Ok/Err 判定两版应一致：basic={:?} fast={:?}",
        b.as_ref().err(),
        f.as_ref().err(),
    );
}

/// P13（A6 矩阵复扫）：enum 隐式无标注域钉 U(0) 回归（L09
/// `parity_enum_struct_impl_hole_pinned_u0` 同款 4 源）。修复前：域洞保留
/// → 第 2+ 参数域为 AppPruning 部分应用 meta，使用点显式供给枚举隐式
/// 实参（`P1[Nat][Bool]`）需解该 meta，invert 对非变量 spine 实参直接
/// Err → 误报 can't unify；钉 U(0) 后声明处消除该 meta。含合法索引族
/// （显式标注 + 显式索引）形态确认不受钉影响（源为 L08 R1 病态源教训
/// 修正版：枚举级显式索引参数、返回类型完全应用）。
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

// 2026-09-18 评审修复轮的 parity 钉（L07 修复轮同款场景向本层移植：嵌套
// 模式覆盖检查 / 构造子良构性 / VSUB_REGS σ 跨轮回收）——双实现对判定
// （Ok/Err）与归一化文案逐字节一致。
//
// 场景载体说明：L07 钉子的 List/Vec 载体在孪生侧踩中**既有的**
// check_pm_final 分叉族（带注解 def + 非索引/嵌套构造子 raw 的臂特化在
// 快版静默失败 → 臂全部跳过 → Ok 空编译；套件头注"已知偏差"登记的同族，
// 与本轮修复无关——已用 env 门控逐项差分排除本轮改动）。parity 钉改用
// 具体枚举（无类型参数/索引）载体，嵌套覆盖的记账/两段式/探测/cover_at
// /去重/文案全链路两版仍逐字节对齐；List/Vec 场景保留在参考版单侧的
// `src/L12_canonical/mod.rs` 回归钉里。
// --------------------------------------------------------------------------------

#[test]
fn parity_review_fixes_2026_09_18() {
    for src in [
        // P0 嵌套覆盖缺失（具体枚举载体）：位置 mk#2 两臂都是 false——
        // true 无臂覆盖，两版一致报"模式位置 mk#2 缺少构造子 true"
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum P {
    mk(a: Bool, b: Bool)
}

def g(p: P): Bool =
    match p {
        case mk(true, false) => false
        case mk(false, false) => false
    }
"#,
        // P0 三层嵌套：node 的第二字段（Tree）上 leaf 有臂、node 无臂覆盖
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Tree {
    leaf(v: Bool)
    node(l: Tree, r: Tree)
}

def h(t: Tree): Bool =
    match t {
        case leaf(true) => true
        case leaf(false) => false
        case node(l, leaf(v)) => v
    }
"#,
        // 嵌套覆盖的正向对照：全位置完整覆盖 → 两版 Ok 且输出逐字节一致
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum P {
    mk(a: Bool, b: Bool)
}

def g(p: P): Bool =
    match p {
        case mk(true, true) => true
        case mk(true, false) => false
        case mk(false, true) => false
        case mk(false, false) => true
    }

println (g (mk true false))
"#,
        // P1 构造子良构性：ret 不是本 enum（phantom 构造子）
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Foo {
    c -> Nat
}
"#,
        // P1 构造子良构性：隐式参数位特化（Foo[Bool]）
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Foo[A] {
    c -> Foo[Bool]
}
"#,
        // 侧向对照（L07 stale-solvable 场景）：本层可解集 = 任意裸 Rigid
        //（无白名单可污染），两种臂序判定必须一致且双版一致（L12 语义下
        // ident 臂的瞬态 η 方程两序皆可解 → 判定臂序无关）
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum W(f: Nat -> Nat) {
    big(a: Nat, b: Nat, c: Nat, d: Nat) -> W (n => succ zero)
    mk -> W (n => succ zero)
    ident -> W (n => n)
}

def t(w: W (n => succ zero)): Nat =
    match w {
        case big(a, b, c, d) => a
        case ident => zero
        case mk => succ zero
    }
"#,
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum W(f: Nat -> Nat) {
    big(a: Nat, b: Nat, c: Nat, d: Nat) -> W (n => succ zero)
    mk -> W (n => succ zero)
    ident -> W (n => n)
}

def t(w: W (n => succ zero)): Nat =
    match w {
        case ident => zero
        case big(a, b, c, d) => a
        case mk => succ zero
    }
"#,
    ] {
        assert_parity(src);
    }
    // 正向对照：构造子重绑定参数（p[A,B] -> Pack[A][B] a b）合法——
    // WF 检查不误伤该惯用法，两版 Ok 输出逐字节一致
    assert_parity(
        r#"
enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Pack[A, B](x: A, y: B) {
    p[A, B](a: A, b: B) -> Pack[A][B] a b
}

def sw: Pack[Nat][Bool] zero true = p[Nat][Bool] zero true

println sw.y
"#,
    );
}

/// L07 §7.7 回归钉的本层移植：孪生 arena 内 XCell::VSub 持有的 Rc<SubstV>
/// 克隆曾被 bump reset 跳过 Drop（跨轮慢泄漏）。修复 = wrap_sub 登记（alloc
/// 成功后置）+ clear_round 逐指针归还 + run_decls 轮尾 ReclaimOnExit 守卫。
/// 观察口：σ 链条目的存活计数 (SUBSTV_ALIVE)——同一 Tycker 连跑两轮含
/// match 精化的程序，每轮结束后计数都应回落到轮前基线。必须同线程跑
/// （登记表是 thread_local）。注：def 一律显式注解返回类型（无注解 def 的
/// Hole 推导是快版已知分叉家族，套件头注登记）；该钉只断言双轮稳定与
/// 计数回落，不作双版比对。
#[test]
fn fast_substv_reclaimed_across_rounds() {
    use std::sync::atomic::Ordering::Relaxed;
    let src = r#"enum Nat {
    zero
    succ(x: Nat)
}

enum List[A] {
    nil
    cons(head: A, tail: List[A])
}

def len[A](xs: List[A]): Nat =
    match xs {
        case nil => zero
        case cons(x, rest) => succ (len rest)
    }

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

println (add (len (cons zero nil)) (succ zero))
"#;
    let sigma_guard = SigmaExcl::enter();
    let base = fast::SUBSTV_ALIVE.load(Relaxed);
    // 同一 Tycker 复用两轮（LSP 式场景）：每轮 clear_round 都应归还 arena
    // 克隆——计数不回落 = 泄漏回归。
    let mut t = fast::Tycker::new();
    let out1 = t.run_input(src, 0).expect("第 1 轮应 Ok");
    let after1 = fast::SUBSTV_ALIVE.load(Relaxed);
    let out2 = t.run_input(src, 0).expect("第 2 轮应 Ok");
    let after2 = fast::SUBSTV_ALIVE.load(Relaxed);
    assert_eq!(out1, out2, "两轮输出应一致");
    assert_eq!(
        (after1, after2),
        (base, base),
        "σ 链条目跨轮未回收（arena 克隆泄漏）：base={base} after1={after1} after2={after2}"
    );
}
