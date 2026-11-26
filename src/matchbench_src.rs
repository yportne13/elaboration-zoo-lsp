//! 多分支多层次 match 负载生成器（L07–L13 共用语料）。
//!
//! 三个可调轴，**都作用在 match 结构本身**：
//!   * depth  -- 嵌套层数：每个非叶子臂里再开一个 match；
//!   * copies -- 级联条数（线性放大总量，不改变单条形态）；
//!   * width  -- 每个 match 的**臂数**（被匹配 enum 的构造子数）。
//!
//! 结构（depth=3, width=4 时）：
//!
//! ```text
//! def cascade_0(x: Tag): Tag =
//!     match x {                       <- 第 1 层，4 个臂
//!         case t0 =>
//!             match x {               <- 第 2 层，4 个臂
//!                 case t0 =>
//!                     match x {       <- 第 3 层，4 个臂
//!                         case t0 => t1
//!                         case t1 => t2
//!                         case t2 => t3
//!                         case t3 => t0
//!                     }
//!                 case t1 => t2
//!                 case t2 => t3
//!                 case t3 => t0
//!             }
//!         case t1 => t2
//!         case t2 => t3
//!         case t3 => t0
//!     }
//! ```
//!
//! 只有第 0 个臂向下钻（其余臂直接给叶子），所以 match 块数 = depth、
//! 总臂数 = depth x width —— 宽度与深度因此**可独立调节**，不会组合爆炸。
//!
//! 语法面只用 L07 就有的（enum / def / match / println），同一份源可喂 L07…L13。

/// 生成一份 depth 层嵌套、copies 条级联、每层 width 个臂的源。
pub fn match_cascade_src(depth: u32, copies: u32, width: u32) -> String {
    assert!(depth >= 1 && width >= 1, "depth/width must be >= 1");
    let mut s = String::new();
    s.push_str("enum Tag {\n");
    for i in 0..width {
        s.push_str(&format!("    t{i}\n"));
    }
    s.push_str("}\n\n");

    for c in 0..copies {
        s.push_str(&format!("def cascade_{c}(x: Tag): Tag =\n"));
        s.push_str(&cascade_body("x", depth, 1, width));
        s.push('\n');
    }

    // 驱动定义：让每条级联真的被调用（否则体检查可能被惰性跳过）。
    for c in 0..copies {
        s.push_str(&format!("def use_{c} : Tag = cascade_{c} t0\n"));
    }
    s
}

/// 递归生成 depth 层嵌套 match 体；indent 是当前缩进级数（4 空格一级）。
///
/// 每层都有 width 个臂：`case t0` 向下钻一层（depth-1），其余臂直接给叶子。
fn cascade_body(var: &str, depth: u32, indent: usize, width: u32) -> String {
    let pad = "    ".repeat(indent);
    let mut s = format!("{pad}match {var} {{\n");
    for b in 0..width {
        let leaf = format!("t{}", (b + 1) % width);
        s.push_str(&format!("{pad}    case t{b} =>\n"));
        if b == 0 && depth > 1 {
            let inner = cascade_body(var, depth - 1, indent + 2, width);
            s.push_str(&inner);
        } else {
            s.push_str(&format!("{pad}        {leaf}\n"));
        }
    }
    s.push_str(&format!("{pad}}}\n"));
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count_matches(src: &str) -> usize {
        src.lines().filter(|l| l.trim_start().starts_with("match ")).count()
    }

    fn count_arms(src: &str) -> usize {
        src.lines().filter(|l| l.trim_start().starts_with("case ")).count()
    }

    #[test]
    fn arm_count_is_depth_times_width() {
        for (depth, width) in [(1, 2), (3, 4), (5, 8)] {
            let src = match_cascade_src(depth, 1, width);
            assert_eq!(count_matches(&src), depth as usize, "match blocks == depth");
            assert_eq!(
                count_arms(&src),
                (depth * width) as usize,
                "arms == depth * width (depth={depth}, width={width})"
            );
        }
    }

    #[test]
    fn width_actually_creates_arms_not_just_enum_members() {
        // width=2 与 width=8 在**同一个** depth 下的臂数必须差 4 倍。
        let narrow = match_cascade_src(4, 1, 2);
        let wide = match_cascade_src(4, 1, 8);
        assert_eq!(count_arms(&narrow), 8);
        assert_eq!(count_arms(&wide), 32);
    }

    #[test]
    fn enum_has_requested_members() {
        let src = match_cascade_src(1, 1, 7);
        let mut n = 0usize;
        for line in src.lines() {
            if let Some(rest) = line.strip_prefix("    t") {
                if rest.parse::<u32>().is_ok() {
                    n += 1;
                }
            }
        }
        assert_eq!(n, 7);
    }
}
