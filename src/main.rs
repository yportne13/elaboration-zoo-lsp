#![feature(pattern)]

use std::time::Duration;

mod parser_lib;
mod list;
mod L01_eval;
mod L01a_fast;
mod L02_tyck;
mod L03_holes;
mod L04_implicit;
mod L05_pruning;
mod L06_string;
mod L07_sum_type;
mod L07a_depend_pm;
mod L08_product_type;
mod L09_mltt;
//mod L10_typeclass;

fn calcu<F>(f: F, name: &str)
where
    F: Fn() -> Duration
{
    let mut ret = Duration::new(0, 0);
    for _i in 0..10 {
        ret += f()
    }
    println!("{name}: {ret:?}")
}

fn main() {
    //println!("Hello, world!");
    calcu(L01a_fast::main, "basic");
    calcu(L01a_fast::main1, "rc");
    calcu(L01a_fast::main2, "vec");
    calcu(L01a_fast::main3, "vec2");
    calcu(L01a_fast::main32, "vec2 arena");
    calcu(L01a_fast::main4, "value vec");
    calcu(L01a_fast::main5, "tail vec");
    calcu(L01a_fast::main11, "rc2");
}
