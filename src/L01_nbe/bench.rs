//! 8 个 NBE 变体的对比基准（入口：`typort bench`，见 `src/bin/cli.rs`）。
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

use std::time::{Duration, Instant};

use super::persistent_list::ListArena;
use super::term::{self, Term};
use super::{
    bytes_env_arena, bytes_env_arena_tm, bytes_env_list, bytes_flat_value, naive,
    rc_term, rc_value, rpn_owned,
};

pub fn run(max_church: usize, rounds: usize) {
    println!("L01 NBE bench: church_pair(n) = add (church n) (church n) -> church(2n)");
    println!("rounds per variant = {rounds}, sizes double from 1000\n");

    let mut n = 1000;
    loop {
        bench_size(n, rounds);
        if n >= max_church {
            break;
        }
        n = n.saturating_mul(2);
    }
}

fn bench_size(n: usize, rounds: usize) {
    let check = term::church(n + n);
    let mut rows: Vec<(&'static str, Duration, Duration)> = Vec::new();

    // naive — Box<Term> AST + crate::list::List 环境
    {
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
    {
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
    {
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
    {
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
    {
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
    {
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
    {
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
    {
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

    println!("== church_pair({n}) ==");
    println!("  {:<18} {:>10} {:>10}", "variant", "min_ms", "med_ms");
    let best = rows.iter().map(|r| r.1).min().unwrap();
    for (name, min, med) in &rows {
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