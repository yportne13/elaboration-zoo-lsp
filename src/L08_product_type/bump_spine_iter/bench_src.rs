//! bench_src：基准负载生成器（L06 全家桶的 L07 语法版 + sum-type 特色
//! 负载 + L08 struct 负载）。bins（l08bench）与 tests/l08_fast_parity 经
//! #[path] 引用，逐行搬运（2026-09-23 拆分）。

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

/// struct 负载（**L08 特色**）：固定深度的嵌套 Box（4 层：类型级 `.mk`
/// 剥链 + 左结合投影链 + 一个浅嵌套值）+ 规模按 2^(k+1) 的**浅值投影
/// def 链**（`def q{i} : Nat = get_x (new P(q{i-1}, zero))`——每层一次
/// 构造子 β + 类型级投影 + 合一）。末值 = `zero`（nf 节点数 = 2：
/// SumCase + typ 的 Sum 两个节点）。
///
/// 设计注记：**不**用深嵌套值链（`b_i` 含 `b_{i-1}`）作主负载——参考版
/// 的 decl 表 `Rc` 写时复制 + `Val` 深拷贝语义下，深度 i 的值树在插入
/// 第 n 个 def 时被整体克隆，复杂度 O(n³)（k=700 即分钟级）；孪生版的
/// 平铺表无此问题，但双 oracle 同负载对比失去意义。嵌套深度固定为 4，
/// 规模轴走浅值。
pub(crate) fn struct_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\n\
         struct Box0 {\n    v: Nat\n}\n\n\
         struct Box1 {\n    v: Nat\n    inner: Box0\n}\n\n\
         struct Box2 {\n    v: Nat\n    inner: Box1\n}\n\n\
         struct Box3 {\n    v: Nat\n    inner: Box2\n}\n\n\
         def get_v2(p: Box2): Nat = p.inner.v\n\n\
         def seed : Nat = get_v2(new Box2(zero, new Box1(succ zero, new Box0(succ (succ zero)))))\n\n\
         struct P {\n    x: Nat\n    y: Nat\n}\n\n\
         def get_x(p: P): Nat = p.x\n\n\
         def q0 : Nat = get_x(new P(zero, seed))\n",
    );
    for i in 1..n {
        s += &format!("def q{i} : Nat = get_x(new P(q{}, zero))\n", i - 1);
    }
    s += &format!("println q{}\n", n - 1);
    s
}
