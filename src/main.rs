#![feature(pattern)]

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

fn main() {
    //println!("Hello, world!");
    L01a_fast::main();
    L01a_fast::main2();
}
