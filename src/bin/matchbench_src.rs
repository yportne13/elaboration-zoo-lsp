//! 多分支多层次 match 负载生成器（L07–L13 共用语料）。
//!
//! 三个可调轴：
//!   * depth  —— 单条级联的嵌套层数（每层在 succ 臂里再开一个 match）；
//!   * copies —— 级联条数（放大总工作量，深度不变）；
//!   * width  —— 叶子 Wide 的构造子数（直接压覆盖检查与可达性探测）。
//!
//! 形态上刻意只依赖 L07 就有的语法面（enum / def / match / 构造子应用 /
//! println），这样同一份源可以喂给 L07…L13 七章而不触发各章的已知偏差。

/// 生成一份 depth 层嵌套、copies 条级联、width 个叶子构造子的源。
pub fn match_cascade_src(depth: u32, copies: u32, width: u32) -> String {
    let mut s = String::new();
    s.push_str("enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n");
    s.push_str("enum Wide {\n");
    for i in 0..width {
        s.push_str(&format!("    w{i}\n"));
    }
    s.push_str("}\n\n");

    for c in 0..copies {
        s.push_str(&format!("def cascade_{c}(x: Nat): Wide =\n"));
        s.push_str(&cascade_body("x", depth, 1, width, c));
        s.push('\n');
    }

    s.push_str("def seed : Nat = succ (succ (succ (succ zero)))\n");
    for c in 0..copies {
        s.push_str(&format!("def use_{c} : Wide = cascade_{c} seed\n"));
    }
    s
}

/// 递归生成 depth 层嵌套 match 体；indent 是当前缩进级数（4 空格一级）。
fn cascade_body(var: &str, depth: u32, indent: usize, width: u32, seed: u32) -> String {
    let pad = "    ".repeat(indent);
    let mut s = format!("{pad}match {var} {{\n");
    s.push_str(&format!(
        "{pad}    case zero => w{}\n",
        (seed as usize) % (width as usize)
    ));
    s.push_str(&format!("{pad}    case succ(n{depth}) =>\n"));
    if depth <= 1 {
        s.push_str(&format!(
            "{pad}        w{}\n",
            (seed as usize + 1) % (width as usize)
        ));
    } else {
        let body = cascade_body(&format!("n{depth}"), depth - 1, indent + 2, width, seed + 1);
        s.push_str(&body);
    }
    s.push_str(&format!("{pad}}}\n"));
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cascade_source_shape() {
        let src = match_cascade_src(3, 2, 4);
        // 深度 3 表示每层一个 match：2 条级联 x 3 层 = 6 个 match。
        assert_eq!(src.matches("match ").count(), 6, "2 copies x 3 levels");
        assert!(src.contains("case succ(n3)"));
        assert!(src.contains("case succ(n2)"));
        assert!(src.contains("w0"));
        assert!(src.contains("w3"));
    }

    #[test]
    fn wide_enum_has_requested_branches() {
        let src = match_cascade_src(1, 1, 7);
        // 只数 enum Wide 里的成员行（4 空格缩进 + `w` + 数字 + 换行）；
        // 级联体里的叶子更深缩进，不能混进来。
        let mut n = 0usize;
        for line in src.lines() {
            if let Some(rest) = line.strip_prefix("    w") {
                if rest.parse::<u32>().is_ok() {
                    n += 1;
                }
            }
        }
        assert_eq!(n, 7, "enum Wide 应有 7 个成员");
    }
}
