//! bench_src：基准负载生成器（l06bench 共用；L05 全家桶的 L06 语法版 +
//! string 特色负载）。原 bump_spine_iter.rs 的 "基准负载生成器" 一节，
//! 逐行搬运（2026-09-23 拆分）。

// 基准负载生成器（l06bench 共用；L05 全家桶的 L06 语法版 + string 特色负载）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 def 链，末位 def 为 `p_k`
/// （L06 顶层是 decl 序列：**无尾表达式行、def 无分号**——parser 只取
/// decl 前缀，多余 token 会把后续 println 截掉；nf 节点数 = 2n + 4）。
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

/// implicit 2^(k+1)（L04/L05 同款链的 L06 版）：每层 `id p_{i-1}` 触发一次
/// 隐式插入 + 一次求解——插入口的 fresh meta 类型恒为 `U`（tag 3 快捷
/// 全命中），掩码全 define 槽（eval_fresh 跳段）。
pub(crate) fn implicit_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def id [A : U] : A -> A = x => x\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..n {
        s += &format!("def p{i} : Nat = id p{}\n", i - 1);
    }
    s
}

/// prune 2^(k+1)（L05 特色负载的 L06 版）：每层 `m_i`（洞类型
/// `(A : U)(B : U) -> U -> U -> U`）+ `t_i` 的 `m_i a a` 非线性 spine——
/// invert 的重复变量掩码 + prune_ty 验证 + solve。
pub(crate) fn prune_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n\
         def refl [A : U, x : A] : Eq[A] x x = P => px => px\n\
         def the (A : U)(x : A) : A = x\n",
    );
    for i in 0..n {
        s += &format!(
            "def m{i} : (A : U)(B : U) -> U -> U -> U = _\n\
             def t{i} = a => b => the (Eq (m{i} a a) (x => y => y)) refl\n"
        );
    }
    s
}

/// solve 2^(k+1)：`Eq _ p_k p_k = refl _ _`——rename 沿 church 展开的整条
/// neutral 链走的主展示负载。
pub(crate) fn solve_src(k: u32) -> String {
    let mut s = String::from(
        // Eq/refl 都用**显式**参数（L05 solve 负载同款）：`Eq _ p_k p_k` 与
        // `refl _ _` 的显式实参恰好填满，洞走 unify 求解（隐式版会先走
        // insert 造出头是 meta 的应用，invert 非模式而失败）
        "def Nat : U = (N : U) -> (N -> N) -> N -> N\n\
         def add : Nat -> Nat -> Nat = a => b => N => s => z => a N s (b N s z)\n\
         def Eq (A : U)(x : A, y : A) : U = (P : A -> U) -> P x -> P y\n\
         def refl (A : U)(x : A) : Eq A x x = P => px => px\n\
         def p0 : Nat = N => s => z => s (s z)\n",
    );
    for i in 1..=k {
        s += &format!("def p{i} : Nat = add p{} p{}\n", i - 1, i - 1);
    }
    s += &format!("def eqTest : Eq _ p{k} p{k} = refl _ _\n");
    s
}

/// strchain 2^(k+1)（**L06 特色负载**）：每层 `string_concat s_{i-1} "x"`
/// ——define 链 + decl 表增长 + 每层一次 builtin prim 触发（字面量拼接），
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
