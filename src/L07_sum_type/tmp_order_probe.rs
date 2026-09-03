#[test]
fn tmp_order() {
    let src = "def s : String = string_concat \"a\" \"b\"\nprintln s\n";
    println!("OUT: {:?}", crate::L07_sum_type::run(src, 0));
}
