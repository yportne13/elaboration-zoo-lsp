//! 模式匹配编译策略受控实验 · 两层共用的源生成器。
//!
//! 目的：把同一份源文本分别喂给 L07（逐臂下钻）与 L09（决策树矩阵）的
//! 参考版编译器，扫描两个维度，检验 `docs/perf-ab-l07l12-2026-09-16.md`
//! 与理论推导给出的两条预测：
//!
//! - **扫描 A（臂数 n）**：扁平 match，n+1 条臂各占一个不同构造子。
//!   预测：L07 的覆盖扫描有 O(C·n·C) 项、逐臂走查是 O(Σ|pᵢ|)=O(n)；
//!   L09 在单个分叉节点上对 (构造子 × 臂) 逐个重算可达性，每算一次
//!   整表克隆 meta，单项  O(n·C·(M + C·E))，合计 O(n²·M + n³·E)。
//!
//! - **扫描 B（列数 m / 通配重数）**：`Box` 有 m 个 `Bool` 字段，第 j 条臂
//!   只在第 j 列写具体构造子、其余列全通配，末条全通配。每列都不是
//!   "全通配"（默认列优化不触发），带通配的臂进入全部 2 个分支 →
//!   臂的分支重数积 Π βᵢ = 2^m。预测：L09 按 2^m 放大，L07 仍是
//!   O(Σ|pᵢ|) = O(m²)。
//!
//! 语言只用两层的最小公共子集：`enum` / `def` / `match` / `_` 通配。
//! 所有负载都不含 `println`，所以 `run` 不做 nf，计时面就是
//! preprocess + parse + 逐 decl 推导（其中 match 编译是随规模增长的那一项）。

/// 最小公共前缀：一个二构造子枚举，供各负载当返回类型与字段类型。
const BOOL_ENUM: &str = "enum Bool {\n    t\n    f\n}\n\n";

/// 扫描 A：`C = n+1` 个零元构造子、`n+1` 条臂、单列扁平 match。
pub fn flat_src(n: usize) -> String {
    let mut s = String::from(BOOL_ENUM);
    s.push_str("enum E {\n");
    for i in 0..=n {
        s.push_str(&format!("    c{i}\n"));
    }
    s.push_str("}\n\n");
    s.push_str("def g(x : E) : Bool =\n    match x {\n");
    for i in 0..=n {
        s.push_str(&format!("        case c{i} => t\n"));
    }
    s.push_str("    }\n");
    s
}

/// 扫描 A 的对照：同样的枚举，但没有 match——用于扣掉非 match 的固定成本。
pub fn flat_ctrl(n: usize) -> String {
    let mut s = String::from(BOOL_ENUM);
    s.push_str("enum E {\n");
    for i in 0..=n {
        s.push_str(&format!("    c{i}\n"));
    }
    s.push_str("}\n\n");
    s.push_str("def g(x : E) : Bool = t\n");
    s
}

/// 扫描 B：`Box` 有 `m` 个 `Bool` 字段；第 j 条臂只在第 j 列具体、其余列
/// 通配，末条全通配。臂数 = m+1，分支重数积 = 2^m。
pub fn wild_src(m: usize) -> String {
    let mut s = String::from(BOOL_ENUM);
    s.push_str("enum Box {\n    mk(");
    for c in 0..m {
        if c > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!("b{c} : Bool"));
    }
    s.push_str(")\n}\n\n");
    s.push_str("def g(x : Box) : Bool =\n    match x {\n");
    for j in 0..m {
        s.push_str("        case mk(");
        for c in 0..m {
            if c > 0 {
                s.push_str(", ");
            }
            s.push_str(if c == j { "t" } else { "_" });
        }
        s.push_str(") => t\n");
    }
    s.push_str("        case mk(");
    for c in 0..m {
        if c > 0 {
            s.push_str(", ");
        }
        s.push_str("_");
    }
    s.push_str(") => t\n    }\n");
    s
}

/// 扫描 B 的对照：同样的 `Box`，无 match。
pub fn wild_ctrl(m: usize) -> String {
    let mut s = String::from(BOOL_ENUM);
    s.push_str("enum Box {\n    mk(");
    for c in 0..m {
        if c > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!("b{c} : Bool"));
    }
    s.push_str(")\n}\n\n");
    s.push_str("def g(x : Box) : Bool = t\n");
    s
}

/// 扫描 C：`m` 列的**完整交叉积**——2^m 条臂枚举全部 `t`/`f` 组合。
/// 这是"决策树本该赢"的形态（无通配、前缀全共享），用来对照 B：
/// 两边都只能指数增长，看的是常数差而非指数差。
pub fn cart_src(m: usize) -> String {
    let mut s = String::from(BOOL_ENUM);
    s.push_str("enum Box {\n    mk(");
    for c in 0..m {
        if c > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!("b{c} : Bool"));
    }
    s.push_str(")\n}\n\n");
    s.push_str("def g(x : Box) : Bool =\n    match x {\n");
    for combo in 0..(1usize << m) {
        s.push_str("        case mk(");
        for c in 0..m {
            if c > 0 {
                s.push_str(", ");
            }
            s.push_str(if (combo >> c) & 1 == 0 { "t" } else { "f" });
        }
        s.push_str(") => t\n");
    }
    s.push_str("    }\n");
    s
}

const NAT: &str = "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n";
const VEC: &str = "enum Vec[A](len: Nat) {\n    \
                   nil -> Vec[A] zero\n    \
                   cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)\n}\n\n";

/// 扫描 D：深嵌套 Con 模式（GADT 索引族，σ 链长 = 深度 d）。
///
/// 形态取自 `src/L07_sum_type/tests.rs` 的 `test_deep_pattern_fuel_budget_regression`
/// ——逐层 cons 嵌套的 Vec 模式，每层解一次 `len := succ l`，σ 链长 = d。
/// 这正是 `docs/explicit-subst-refactor-status.md` §2 记的 deep40/deep80
/// 微基准（旧 pm_defs 16.9/62.2 ms → 链式 σ 18.4/67.5 ms）的负载族，但仓库里
/// **没有任何 bench 覆盖它**（`docs/review-l07l12/d5-performance.md` P2-4 已指出）。
/// 本函数把它参数化，供 L07 前后版本对撞。
/// 注意：这里**不**含具体值（原测试里的 `def big` + `println` 只为运行时求值，
/// 编译期测量不需要）。`def big` 是一棵 d 深的 Vec 值，它的推导成本与 match
/// 无关却在两侧都存在，会让"大数相减"的净值噪声压过信号——去掉后净值直接
/// 就是那条深模式 match 的编译代价。
pub fn deep_src(d: usize) -> String {
    format!(
        "{NAT}{VEC}def g[n: Nat](v : Vec[Nat] n) : Nat =\n    match v {{\n        case {} => h0\n        case _ => zero\n    }}\n",
        deep_pat(d)
    )
}

/// 扫描 D 的对照：同样的枚举与同一个 def 签名，但把深模式 match 换成常量体。
pub fn deep_ctrl(d: usize) -> String {
    format!("{NAT}{VEC}def g[n: Nat](v : Vec[Nat] n) : Nat = zero\n")
}

fn deep_pat(d: usize) -> String {
    let mut pat = "nil".to_owned();
    for i in (0..d).rev() {
        pat = format!("cons(h{i}, {pat})");
    }
    pat
}
