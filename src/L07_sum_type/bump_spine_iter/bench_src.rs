//! bench_src：基准负载生成器（L06 全家桶的 L07 语法版 + sum-type 特色
//! 负载）。bins（l07bench）与 tests/l07_fast_parity 经 #[path] 引用，
//! 逐行搬运（2026-09-19 拆分）。

// 基准负载生成器（L06 全家桶的 L07 语法版 + sum-type 特色负载）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （L07 顶层是 decl 序列：**无尾表达式行、def 无分号**；nf 节点数与
/// L06 同为 2n + 4）。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s
}

/// strchain 2^(k+1)（**L06 特色负载**）：每层 `string_concat s_{i-1} "x"`
/// ——decl 表增长 + 每层一次 builtin prim 触发（force 时字面量拼接），
/// 末值是长度 n 的字面量（nf 节点数 = 1）。
pub(crate) fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

/// globals 2^(k+1)（L06 特色：可变全局 + 重入 prim）：每层
/// `change_mutable "k" (s => string_concat s "x")`——mutable_map 读写 +
/// 函数实参的 β 应用 + 重入 prim 触发；末值 = U（nf 节点数 = 1）。
pub(crate) fn globals_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def g0 : U = create_global \"k\" \"x\"\n");
    for i in 1..n {
        s += &format!("def g{i} : U = change_mutable \"k\" (s => string_concat s \"x\")\n");
    }
    s
}

/// match 2^(k+1)（**L07 特色负载**）：每层一个**自递归**的依赖 match def
/// ——decl 表占位/覆盖 + 编译期特化合一 + 运行时首匹配 + 卡住 match 在
/// check 期（期望类型）与 quote 期（分支体简化表）的协同。
pub(crate) fn match_src(k: u32) -> String {
    let mut s = String::from("enum Nat {\n    zero\n    succ(x: Nat)\n}\n");
    for i in 0..=k {
        s += &format!(
            "def f_{i}(x : Nat) : Nat =\n    match x {{\n        case zero => zero\n        case succ(n) => succ (f_{i} n)\n    }}\n"
        );
    }
    s += &format!(
        "def two : Nat = succ (succ zero)\nprintln (f_{k} two)\n"
    );
    s
}

/// enum 负载（**L07 特色**）：多 enum + 依赖索引（Vec 风格 GADT）+ 投影
/// + 索引等式（Eq）+ 递归 length——覆盖 Sum/SumCase 值的 unify / quote /
/// rename 全链路。
pub(crate) fn enum_src() -> String {
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
