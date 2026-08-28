//! 12 个 NBE 变体的对比基准（独立二进制 `l01bench`，见 `src/bin/l01bench.rs`）。
//!
//! 工作负载固定为丘奇数加法：`church_pair(n)` = `add (church n) (church n)`，
//! 规范化结果必须等于 `church(2n)`。流程：
//!
//! 1. 每个变体先做一次**正确性断言**（结果解码回 `Term` 后与 `church(2n)` 比较）；
//! 2. 预热 1 次；3. 计时 `rounds` 次，报告最小与中位时间（毫秒）。
//!
//! 口径：只计 `normalize`——入参编码（`to_vec`/`to_vec2`/`to_vec3`/`into_rc`）
//! 在计时前完成，断言在计时窗口外；arena 变体跨轮次复用 `ListArena`（追加式，
//! 下标永不过期，见 `persistent_list` 的说明），测的是稳态。
//!
//! n > 8000 时只有 `cek` 能跑：其余变体的构造/求值/比较全链路都是递归，
//! 在此规模直接栈溢出。大 n 的 cek 段改用迭代构造 + 迭代比较（`church_iter`/
//! `iter_eq`），同样先断言再计时。

use std::time::{Duration, Instant};

use bumpalo::Bump;

use super::persistent_list::ListArena;
use super::term::{self, Term};
use super::{
    ast_env_arena, bytes_env_arena, bytes_env_arena_tm, bytes_env_list, bytes_flat_value,
    bump_arena, cek, naive, rc_term, rc_value, rpn_owned,
};

/// 递归变体（构造/求值/比较全链路）的栈安全规模上限。
const RECURSION_SAFE_MAX: usize = 8000;

pub fn run(max_church: usize, rounds: usize, only: Option<&str>) {
    println!("L01 NBE bench: church_pair(n) = add (church n) (church n) -> church(2n)");
    match only {
        Some(names) => println!("rounds per variant = {rounds}, only variants = {names}\n"),
        None => println!("rounds per variant = {rounds}, sizes double from 1000\n"),
    }

    let mut n = 1000;
    loop {
        bench_size(n, rounds, only);
        if n >= max_church {
            break;
        }
        n = n.saturating_mul(2);
    }
}

fn bench_size(n: usize, rounds: usize, only: Option<&str>) {
    // 逗号分隔多值，如 --only bump_arena,bump_tree
    let want = move |name: &'static str| match only {
        None => true,
        Some(list) => list.split(',').any(|x| x == name),
    };

    if n > RECURSION_SAFE_MAX {
        if want("cek") {
            bench_cek_deep(n, rounds);
        }
        return;
    }

    let check = term::church(n + n);
    let mut rows: Vec<(&'static str, Duration, Duration)> = Vec::new();

    // naive — Box<Term> AST + crate::list::List 环境
    if want("naive") {
        let got = naive::normalize(term::church_pair(n));
        assert_eq!(got, check, "naive 结果不正确");
        naive::normalize(term::church_pair(n)); // 预热
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n);
            let start = Instant::now();
            let got = naive::normalize(input);
            ts.push(start.elapsed());
            assert_eq!(got, check);
        }
        rows.push(("naive", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // rc_value — 值与 naive 相同，只是值带 Rc 骨架
    if want("rc_value") {
        let got = rc_value::normalize(term::church_pair(n));
        assert_eq!(got, check, "rc_value 结果不正确");
        rc_value::normalize(term::church_pair(n));
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n);
            let start = Instant::now();
            let got = rc_value::normalize(input);
            ts.push(start.elapsed());
            assert_eq!(got, check);
        }
        rows.push(("rc_value", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // rc_term — 项也换成 Rc<TermRc>
    if want("rc_term") {
        let got = rc_term::normalize(term::church_pair(n).into_rc());
        assert_eq!(got, check, "rc_term 结果不正确");
        rc_term::normalize(term::church_pair(n).into_rc());
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n).into_rc();
            let start = Instant::now();
            let got = rc_term::normalize(input);
            ts.push(start.elapsed());
            assert_eq!(got, check);
        }
        rows.push(("rc_term", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // bytes_env_list — 前缀字节码 + List 环境
    if want("bytes_env_list") {
        let input = term::church_pair(n).to_vec2();
        let got = Term::from_vec2(bytes_env_list::normalize(input.clone())).0;
        assert_eq!(got, check, "bytes_env_list 结果不正确");
        bytes_env_list::normalize(input);
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n).to_vec2();
            let start = Instant::now();
            let out = bytes_env_list::normalize(input);
            ts.push(start.elapsed());
            assert_eq!(Term::from_vec2(out).0, check);
        }
        rows.push(("bytes_env_list", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // bytes_env_arena — 前缀字节码 + ListArena 环境（L01a 时代的“最快”）
    if want("bytes_env_arena") {
        let input = term::church_pair(n).to_vec2();
        let mut arena = ListArena::new(); // 跨轮次复用：追加式下标永不过期
        let got = Term::from_vec2(bytes_env_arena::normalize(input.clone(), &mut arena)).0;
        assert_eq!(got, check, "bytes_env_arena 结果不正确");
        bytes_env_arena::normalize(input, &mut arena);
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n).to_vec2();
            let start = Instant::now();
            let out = bytes_env_arena::normalize(input, &mut arena);
            ts.push(start.elapsed());
            assert_eq!(Term::from_vec2(out).0, check);
        }
        rows.push(("bytes_env_arena", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // bytes_env_arena_tm — 再加项体共享 arena（to_vec3 编码）
    if want("bytes_env_arena_tm") {
        let mut arena_tm = Vec::new(); // 编码期与求值期共用同一个项 arena
        let input = term::church_pair(n).to_vec3(&mut arena_tm);
        let mut arena = ListArena::new();
        let got = Term::from_vec3(
            bytes_env_arena_tm::normalize(input.clone(), &mut arena, &mut arena_tm),
            &arena_tm,
        ).0;
        assert_eq!(got, check, "bytes_env_arena_tm 结果不正确");
        bytes_env_arena_tm::normalize(input, &mut arena, &mut arena_tm);
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let mut arena_tm_in = Vec::new();
            let input = term::church_pair(n).to_vec3(&mut arena_tm_in);
            let start = Instant::now();
            let out = bytes_env_arena_tm::normalize(input, &mut arena, &mut arena_tm_in);
            ts.push(start.elapsed());
            assert_eq!(Term::from_vec3(out, &arena_tm_in).0, check);
        }
        rows.push(("bytes_env_arena_tm", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // bytes_flat_value — 值也压成扁平字节
    if want("bytes_flat_value") {
        let input = term::church_pair(n).to_vec2();
        let mut arena = ListArena::new();
        let got = Term::from_vec2(bytes_flat_value::normalize(input.clone(), &mut arena)).0;
        assert_eq!(got, check, "bytes_flat_value 结果不正确");
        bytes_flat_value::normalize(input, &mut arena);
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n).to_vec2();
            let start = Instant::now();
            let out = bytes_flat_value::normalize(input, &mut arena);
            ts.push(start.elapsed());
            assert_eq!(Term::from_vec2(out).0, check);
        }
        rows.push(("bytes_flat_value", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // rpn_owned — 后缀（RPN）编码 + 自持 Vec<u8>
    if want("rpn_owned") {
        let input = term::church_pair(n).to_vec();
        let got = Term::from_vec(rpn_owned::normalize(input.clone())).0;
        assert_eq!(got, check, "rpn_owned 结果不正确");
        rpn_owned::normalize(input);
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n).to_vec();
            let start = Instant::now();
            let out = rpn_owned::normalize(input);
            ts.push(start.elapsed());
            assert_eq!(Term::from_vec(out).0, check);
        }
        rows.push(("rpn_owned", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // cek — CEK 机：迭代 eval + 迭代 quote/解码（全链路栈安全）
    if want("cek") {
        let got = cek::normalize(term::church_pair(n));
        assert_eq!(got, check, "cek 结果不正确");
        cek::normalize(term::church_pair(n));
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n);
            let start = Instant::now();
            let got = cek::normalize(input);
            ts.push(start.elapsed());
            assert_eq!(got, check);
        }
        rows.push(("cek", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // ast_env_arena — Box<Term> AST + ListArena 环境（naive 的 arena 演进）
    if want("ast_env_arena") {
        let input = term::church_pair(n);
        let mut arena = ListArena::new(); // 跨轮次复用：追加式下标永不过期
        let got = ast_env_arena::normalize(input.clone(), &mut arena);
        assert_eq!(got, check, "ast_env_arena 结果不正确");
        ast_env_arena::normalize(input, &mut arena);
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let input = term::church_pair(n);
            let start = Instant::now();
            let out = ast_env_arena::normalize(input, &mut arena);
            ts.push(start.elapsed());
            assert_eq!(out, check);
        }
        rows.push(("ast_env_arena", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // bump_arena — bumpalo 全 arena：项/值/环境全 bump 分配，引用式结构
    if want("bump_arena") {
        let got = {
            let bump = Bump::with_capacity(1 << 20); // 预分配 1MB chunk，避免中途再申请
            let tm = bump_arena::import(&bump, &term::church_pair(n));
            bump_arena::normalize_imported(&bump, tm)
        };
        assert_eq!(got, check, "bump_arena 结果不正确");
        {
            let bump = Bump::with_capacity(1 << 20); // 预分配 1MB chunk，避免中途再申请
            let tm = bump_arena::import(&bump, &term::church_pair(n));
            bump_arena::normalize_imported(&bump, tm);
        }
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let bump = Bump::with_capacity(1 << 20); // 预分配 1MB chunk，避免中途再申请
            let tm = bump_arena::import(&bump, &term::church_pair(n)); // import 在计时外
            let start = Instant::now();
            let got = bump_arena::normalize_imported(&bump, tm);
            ts.push(start.elapsed());
            assert_eq!(got, check);
        }
        rows.push(("bump_arena", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    // bump_tree — bump_arena 的结果树也 bump 化：求值+结果生成全程零 Rust 堆分配
    if want("bump_tree") {
        let got = {
            let bump = Bump::with_capacity(1 << 20); // 预分配 1MB chunk，避免中途再申请
            let tm = bump_arena::import(&bump, &term::church_pair(n));
            bump_arena::export(bump_arena::normalize_imported_bump(&bump, tm)) // 转回只在断言前
        };
        assert_eq!(got, check, "bump_tree 结果不正确");
        {
            let bump = Bump::with_capacity(1 << 20); // 预分配 1MB chunk，避免中途再申请
            let tm = bump_arena::import(&bump, &term::church_pair(n));
            bump_arena::normalize_imported_bump(&bump, tm);
        }
        let mut ts = Vec::with_capacity(rounds);
        for _ in 0..rounds {
            let bump = Bump::with_capacity(1 << 20); // 预分配 1MB chunk，避免中途再申请
            let tm = bump_arena::import(&bump, &term::church_pair(n)); // import 在计时外
            let start = Instant::now();
            let res = bump_arena::normalize_imported_bump(&bump, tm);
            ts.push(start.elapsed());
            assert_eq!(bump_arena::export(res), check);
        }
        rows.push(("bump_tree", *ts.iter().min().unwrap(), median(&mut ts)));
    }

    print_table(n, &rows);
}

/// n > 8000 的 cek 独占段：构造/比较全部迭代化，展示 CEK 机的栈安全。
fn bench_cek_deep(n: usize, rounds: usize) {
    let check = church_iter(n + n);
    let got = cek::normalize(church_pair_iter(n));
    assert!(iter_eq(&got, &check), "cek 大 n 结果不正确");

    cek::normalize(church_pair_iter(n)); // 预热
    let mut ts = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let input = church_pair_iter(n); // 迭代构造，计时外（与其余变体口径一致）
        let start = Instant::now();
        let got = cek::normalize(input);
        ts.push(start.elapsed());
        assert!(iter_eq(&got, &check), "cek 大 n 结果不正确");
    }
    let min = *ts.iter().min().unwrap();
    let med = median(&mut ts);
    println!("== church_pair({n}) — 大 n：仅 cek（其余变体递归链在此规模栈溢出）==");
    println!("  {:<18} {:>10} {:>10}", "variant", "min_ms", "med_ms");
    println!(
        "  {:<18} {:>10.3} {:>10.3} *",
        "cek",
        min.as_secs_f64() * 1000.0,
        med.as_secs_f64() * 1000.0,
    );
    println!();
}

fn print_table(n: usize, rows: &[(&'static str, Duration, Duration)]) {
    if rows.is_empty() {
        println!("（此规模没有选中的变体）\n");
        return;
    }
    println!("== church_pair({n}) ==");
    println!("  {:<18} {:>10} {:>10}", "variant", "min_ms", "med_ms");
    let best = rows.iter().map(|r| r.1).min().unwrap();
    for (name, min, med) in rows {
        let mark = if *min == best { " *" } else { "" };
        println!(
            "  {name:<18} {:>10.3} {:>10.3}{mark}",
            min.as_secs_f64() * 1000.0,
            med.as_secs_f64() * 1000.0,
        );
    }
    println!();
}

fn median(ts: &mut [Duration]) -> Duration {
    ts.sort();
    ts[ts.len() / 2]
}

/// 迭代构造教堂数 `church(n)`（term.rs 的递归版在此规模爆栈）。
fn church_iter(n: usize) -> Term {
    let mut t = Term::Idx(0);
    for _ in 0..n {
        t = Term::App(Box::new(Term::Idx(1)), Box::new(t));
    }
    Term::Lam(Box::new(Term::Lam(Box::new(t))))
}

/// 迭代构造工作负载 `add (church n) (church n)`。
///
/// 与 `term::church_pair` 完全同构（`apply(f, args)` = `App(App(f, a1), a2)`），
/// 只是嵌套部分也用迭代搭出来，避免递归构造爆栈。
fn church_pair_iter(n: usize) -> Term {
    let a = church_iter(n);
    let b = church_iter(n);
    let lam = |t: Term| Term::Lam(Box::new(t));
    // add = λa.λb.λf.λx. a f (b f x)；de Bruijn：a=3, b=2, f=1, x=0
    let x = Term::Idx(0);
    // apply(Idx(2), [Idx(1), Idx(0)]) = (b f) x
    let b_f_x = Term::App(Box::new(Term::App(Box::new(Term::Idx(2)), Box::new(Term::Idx(1)))), Box::new(x));
    // apply(Idx(3), [Idx(1), b_f_x]) = a f ((b f) x)
    let body = Term::App(Box::new(Term::App(Box::new(Term::Idx(3)), Box::new(Term::Idx(1)))), Box::new(b_f_x));
    let add = lam(lam(lam(lam(body))));
    Term::App(Box::new(Term::App(Box::new(add), Box::new(a))), Box::new(b))
}

/// 迭代树比较（递归 `==` 在此规模爆栈）。
fn iter_eq(a: &Term, b: &Term) -> bool {
    let mut stack = vec![(a, b)];
    while let Some((x, y)) = stack.pop() {
        match (x, y) {
            (Term::Idx(i), Term::Idx(j)) if i == j => {},
            (Term::Lam(x), Term::Lam(y)) => stack.push((x, y)),
            (Term::App(f1, a1), Term::App(f2, a2)) => {
                stack.push((f1, f2));
                stack.push((a1, a2));
            },
            _ => return false,
        }
    }
    true
}