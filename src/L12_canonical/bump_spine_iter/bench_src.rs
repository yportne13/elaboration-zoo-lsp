//! bench_src：基准负载生成器（church/natadd/gadt/strchain/match/enum/
//! struct 源码串；L09/L12 语法子集）。原 bump_spine_iter.rs 的 "基准负载
//! 生成器" 节，逐行搬运（2026-09-23 拆分）。

// 基准负载生成器（L09 语法子集：`Type N` 宇宙、string_concat、enum/match、
// 递归 def、struct/new）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （nf 节点数与 L06/L08 同为 2n + 4）。
///
/// **2026-09-12 语法订正**：`add` 体的高阶嵌套应用改逗号调用
/// `a(N, s, b(N, s, z))`——旧空格形式 `a N s (b N s z)` 在 L11+ 的
/// parser 下括号组并进前一个实参（实测两版一致报
/// `can't unify expected: N → N find: N`，L09/L10 同源绿），逗号形式
/// 两版一致通过（L13 --file 探针 nf=12/36 与 L02 闭式 2n+4 吻合）。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "def Nat : Type 1 = (N : Type 0) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a(N, s, b(N, s, z))\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    // println 强制末值求值：L11/L12 参考版无强制引读的 bench_check_nf，
    // 唯一 basic 口径是全流程 run()——λ 体在无 println 时不被强制
    // （basic 会退化成 elaborate-only 平坦值），println 让两版都走
    // 「check + 强制 nf + 输出」的完整路径。
    s += &format!("println p{}\n", k);
    s
}

/// 枚举 Nat 加法链 2^(k+1)：`p0 = 2`、`p{i} = add p{i-1} p{i-1}`——递归
/// match + 构造子链的深负载（L11 合法语法：函数注解是完整类型，`Type N`
/// 注解放弃——参考版对"λ 体 + Type 注解"组合判型失败）。
pub(crate) fn natadd_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         def add(x: Nat, y: Nat): Nat =
    match x {
        case zero => y
        case succ(n) => succ (add n y)
    }

         def p0 : Nat = succ (succ zero)
",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}
", i - 1, i - 1);
    }
    s
}

/// GADT 负载（test_index 同款：Vec 依赖索引 + head/length 递归）。
pub(crate) fn gadt_src() -> String {
    String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

         def two = succ (succ zero)

         def three = succ (succ (succ zero))

         def t = cons (zero, cons(two, cons(three, cons two nil)))

         println t.len

         def head[T, L: Nat](x: Vec[T] (succ L)): T =
    match x {
        case cons(x, _) => x
    }

         println (head (cons zero nil))

         def length[T, l: Nat](x: (Vec[T] l)): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (xs.len)
    }

         println (length t)
",
    )
}

/// strchain 2^(k+1)：每层 `string_concat s_{i-1} "x"`——每层一次 builtin
/// 触发（eval 的 env 双槽字面量拼接），末值是长度 n 的字面量（nf 节点数
/// = 1）。
pub(crate) fn strchain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from("def s0 : String = \"x\"\n");
    for i in 1..n {
        s += &format!("def s{i} : String = string_concat s{} \"x\"\n", i - 1);
    }
    s
}

/// match 2^(k+1)：每层一个**自递归**的依赖 match def——global 占位/覆盖
/// + check_pm 精化 + 运行时首匹配 + 卡住 match 在 check 期与 quote 期
/// （分支体中性重求值）的协同。
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

/// enum 负载：多 enum + 依赖索引（Vec 风格 GADT）+ 投影 + 索引等式（Eq）
/// + 递归 length——覆盖 Sum/SumCase 值的 unify / quote / rename 全链路。
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

/// struct 负载（L09 语义子集）：两层嵌套 struct（`Line{a, b: P}`）+
/// 规模按 2^(k+1) 的**浅值投影 def 链**（每层一次构造子 β + 类型级投影
/// + 合一）。末值 = `zero`（nf 节点数 = 2：SumCase + typ 的 Sum 两个
/// 节点）。注：L09 参考版的 `.mk` 剥链带 U(0) 占位怪癖，三层嵌套 struct
/// 的构造子应用两版一致地 Err——负载避开该形态（parity 不受影响）。
pub(crate) fn struct_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "enum Nat {
    zero
    succ(x: Nat)
}

         struct P {
    x: Nat
    y: Nat
}

         struct Line {
    a: P
    b: P
}

         def get_x(p: P): Nat = p.x

         def q0 : Nat = get_x(new P(zero, zero))
",
    );
    for i in 1..n {
        s += &format!("def q{i} : Nat = get_x(new P(q{}, zero))
", i - 1);
    }
    s += &format!("println q{}
", n - 1);
    s
}
