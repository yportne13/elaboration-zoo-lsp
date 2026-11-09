//! Scratch deep-scope probe (not committed): N nested lambdas / N let binders.
//! Used to compare the src_names routes beyond the shallow l07bench corpus.

#[path = "../list.rs"]
mod list;

#[path = "../parser_lib.rs"]
mod parser_lib;
#[path = "../parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../L07_sum_type/mod.rs"]
mod L07_sum_type;

use std::time::Instant;

use L07_sum_type::parser::parser;

fn lam_src(n: usize) -> String {
    let mut ty = String::from("def deep : ");
    for _ in 0..n {
        ty.push_str("U -> ");
    }
    ty.push('U');
    ty.push_str(" = ");
    for i in 0..n {
        ty.push_str(&format!("x{i} => "));
    }
    ty.push_str("x0");
    ty
}

fn let_src(n: usize) -> String {
    let mut s = String::from("def p0 : U = U\ndef deep : U = ");
    for i in 0..n {
        let rhs = if i == 0 { "p0".to_string() } else { format!("a{}", i - 1) };
        s.push_str(&format!("let a{i} = {rhs}; "));
    }
    s.push_str("a0");
    s
}

fn median(ts: &mut [u128]) -> u128 {
    ts.sort_unstable();
    ts[ts.len() / 2]
}

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|x| x.parse().ok()).unwrap_or(500);
    let rounds: usize = std::env::args().nth(2).and_then(|x| x.parse().ok()).unwrap_or(3);
    for (kind, src) in [("lam", lam_src(n)), ("let", let_src(n))] {
        let Ok(raw) = parser(&L07_sum_type::preprocess(&src), 0) else {
            println!("{kind}\tn={n}\tPARSE-FAILED");
            continue;
        };
        // correctness: result must be non-zero (nf node count)
        let nf = L07_sum_type::bench_check_nf(&raw);
        let mut ts = Vec::new();
        for _ in 0..rounds {
            let start = Instant::now();
            L07_sum_type::bench_check_nf(&raw);
            ts.push(start.elapsed().as_micros());
        }
        println!("{kind}\tn={n}\tnf={nf}\tmin={:.3}ms\tmed={:.3}ms",
            *ts.iter().min().unwrap() as f64 / 1000.0,
            median(&mut ts) as f64 / 1000.0);
    }
}
