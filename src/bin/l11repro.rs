//! 一次性复现器：把源文本喂给 L11 参考版 `run`，打印 Ok/Err。
//! 用法：l11repro <file> [twin-first] [runs=N]

#![allow(dead_code)]

#[path = "../list.rs"]
mod list;
#[path = "../bimap.rs"]
mod bimap;
#[path = "../parser_lib.rs"]
mod parser_lib;
#[path = "../parser_lib_resilient.rs"]
mod parser_lib_resilient;

#[path = "../L11_macro/mod.rs"]
mod L11_macro;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).expect("usage: l11repro <file> [twin-first] [runs=N]");
    let twin_first = args.iter().any(|a| a == "twin-first");
    let runs: usize = args
        .iter()
        .find_map(|a| a.strip_prefix("runs="))
        .and_then(|n| n.parse().ok())
        .unwrap_or(1);
    let src = std::fs::read_to_string(path).expect("read failed");
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            for i in 0..runs {
                if twin_first {
                    match L11_macro::bump_spine_iter::run_fast(&src, 0) {
                        Ok(o) => eprintln!("[twin] Ok: {}", o.trim()),
                        Err(e) => eprintln!("[twin] Err: {}", e.0.data),
                    }
                }
                match L11_macro::run(&src, 0) {
                    Ok(out) => println!("[ref run {i}] Ok: {}", out.trim()),
                    Err(e) => println!("[ref run {i}] Err: {}", e.0.data),
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
