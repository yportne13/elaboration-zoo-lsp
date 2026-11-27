//! 非 match 基准的负载生成器（L07–L13 共用语料）。
//!
//! 与 `L07_sum_type/bump_spine_iter/bench_src.rs` 的五族同形（church /
//! strchain / global / enum / natadd），但只依赖 L07 语法面，因此同一份源
//! 可喂 L07…L13。`match` 族不在此列——它由 `matchbench` 覆盖。

/// 按名字生成负载源；未知名字 panic（CLI 已校验）。
pub fn make_src(workload: &str, k: u32) -> String {
    match workload {
        "church" => church_src(k),
        "strchain" => strchain_src(k),
        "global" => globals_src(k),
        "enum" => enum_src(),
        "natadd" => natadd_src(k),
        other => panic!("unknown workload: {other}"),
    }
}

/// church 式 2^(k+1) 翻倍链，但建在 **sum type** 上（L06 那套 Phong 的 λ 编码
/// 只在 L07/L08 的语法里成立；L09+ 的 `def Nat : U = (N : U) -> …` 会被
/// 当成新的 `Nat` 声明与内置 Nat 冲突）。这里用 `enum Nat` + `add` 的同一
/// 形状，语义等价（k 次 ×2 翻倍）。
pub fn church_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n\
         def add(x: Nat, y: Nat): Nat =\n\
    match x {\n\
        case zero => y\n\
        case succ(n) => succ (add n y)\n\
    }\n\n\
         def p0 : Nat = succ (succ zero)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

/// strchain 2^(k+1)：每层 `string_concat s_{i-1} "x"`。
pub fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

/// globals 2^(k+1)：每层 `change_mutable "k" (s => string_concat s "x")`。
///
/// 类型注解用 `Type 0` 而不是 L06/L07 的 `U` 别名：L09 起内置的
/// `create_global` 返回 `Type 0`（见 L09 内置表），且 `U` 在 L09+ 是
/// `Type n` 的语法糖而不再是可独立命名的常量。
pub fn globals_src(k: u32) -> String {
    globals_src_with(k, "Type 0")
}

/// 同 `globals_src`，但类型注解可指定：L07/L08 只认 `U`，L09+ 只认 `Type 0`。
pub fn globals_src_with(k: u32, ty: &str) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def g0 : U = create_global \"k\" \"x\"\n");
    s = s.replace(": U =", &format!(": {ty} ="));
    for i in 1..n {
        s += &format!("def g{i} : {ty} = change_mutable \"k\" (s => string_concat s \"x\")\n");
    }
    s
}

/// enum 负载（固定源）：多 enum + Vec 风格 GADT + 投影 + 索引等式 + 递归。
pub fn enum_src() -> String {
    String::from(
        r#"enum Nat {
    zero
    succ(x: Nat)
}

enum Bool {
    true
    false
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

enum Eq[A](x: A, y: A) {
    refl[a: A] -> Eq[A] a a
}

def two = succ (succ zero)

def t = cons zero (cons two nil)

println t.len

def ok : Eq two two = refl

def length[T, l: Nat](x: Vec[T] l): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (length xs)
    }

println (length t)

def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

def rep[n: Nat](x: Vec[Nat] n): Nat =
    match x {
        case nil => zero
        case cons(h, xs) => add h (rep xs)
    }

println (rep (cons two (cons two nil)))
"#,
    )
}

/// natadd 负载：enum Nat + 递归 add + p{i} = add p{i-1} p{i-1} 翻倍链。
pub fn natadd_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n\
         def add(x: Nat, y: Nat): Nat =\n\
    match x {\n\
        case zero => y\n\
        case succ(n) => succ (add n y)\n\
    }\n\n\
         def p0 : Nat = succ (succ zero)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn church_scales_with_k() {
        let base = church_src(0).lines().count();
        assert_eq!(church_src(1).lines().count(), base + 1);
        assert_eq!(church_src(4).lines().count(), base + 4);
    }

    #[test]
    fn strchain_is_two_pow_k_plus_one() {
        assert_eq!(strchain_src(4).lines().count(), 32);
    }

    #[test]
    fn enum_has_matches_but_is_fixed() {
        let a = enum_src();
        let b = enum_src();
        assert_eq!(a, b, "enum source is fixed");
        assert!(a.contains("match x"));
    }

    #[test]
    fn natadd_has_k_plus_one_defs() {
        let s = natadd_src(5);
        assert_eq!(s.matches("def p").count(), 6);
    }
}