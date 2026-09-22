//! bench_src：基准负载生成器（L09 语法子集：church/natadd/gadt/strchain/
//! match/enum/moduletree/struct；bins（l13bench、l06l13mem）与互检套件经
//! `bump_spine_iter::` 路径引用）。原 bump_spine_iter.rs 的 "基准负载生成器"
//! 节，逐行搬运（2026-09-23 拆分）。


// 基准负载生成器（L09 语法子集：`Type N` 宇宙、string_concat、enum/match、
// 递归 def、struct/new）
// --------------------------------------------------------------------------------

/// church 2^(k+1)（L13 合法版）：**具体 Nat 类型上的高阶迭代倍增**——`d0`
/// 是"两次 succ"的自函数，`d{i} = n => d{i-1} (d{i-1} n)` 每层翻倍，末位
/// `total : Nat = d{k} zero` 把组合链完全展开成 2^(k+1) 个 succ 的深正规式。
///
/// 注：原 impredicative Church 编码（`Nat = (N : Type 0) -> (N -> N) -> N -> N`
/// 配 `add p p` 式高阶应用）在 L13 **两版一致**判型失败——把 pattern-free 的
/// 多态 church 数嵌套应用于其自身绑定的类型变量 `N`（`a N s (b N s z)`）触发
/// `can't unify expected: N → N find: N`，单层 eta（`a N s z`）则可过。这是该
/// elaborator 语言面限制（非孪生分叉），故换成本形态：同样是高阶函数复合驱动
/// 的 2^(k+1) 深归一化，但两版都能过、可对照计时。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "enum Nat {\n    zero\n    succ(x: Nat)\n}\n\
         def d0 : Nat -> Nat = n => succ (succ n)\n",
    );
    for i in 1..=k {
        s += &format!("def d{i} : Nat -> Nat = n => d{} (d{} n)\n", i - 1, i - 1);
    }
    s += &format!("def total : Nat = d{k} zero\n");
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
/// + 递归 length/rep——覆盖 Sum/SumCase 值的 unify / quote / rename 全链路。
///
/// 注（L13 合法化，两版一致）：
/// - 构造子应用用元组形式 `cons (x, xs)`；分离位置形式 `cons zero (...)`
///   在本语言面两版一致报 `can't unify expected: (x: ?) → ? x find: Nat`。
/// - `rep` 体内不对 pattern 精化出的 `xs : Vec[Nat] l` 调用**类型泛型**的
///   `length[T]`——把精化 existential 再喂进另一索引多态函数，两版一致报
///   `expected: (x': ? _l h xs) → ? _l h xs x' find: Nat`（已知偏差 2 家族，
///   非孪生分叉）。故 `rep` 走自身递归 `succ (rep xs)`，`add`/`length` 各自
///   独立用 `println` 触发、互不嵌套。
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

def t = cons (zero, cons (two, nil))

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

println (add two two)

def rep[n: Nat](x: Vec[Nat] n): Nat =
    match x {
        case nil => zero
        case cons(_, xs) => succ (rep xs)
    }

println (rep (cons (two, cons (two, nil))))

println (length (cons (two, cons (two, nil))))
"#,
    )
}

/// 最小 struct + inherent impl（`impl Name { def ... }`）+ 依赖索引 Vec
/// —— HDL prelude decl 171（`impl $trait_name$ModuleTree`）unify 失败的
/// 最小化形态：struct 脱糖出的 inherent impl，方法体带 `succ(this.num)`
/// 构造子链与 `m :: this.data` 的 cons 链。
pub(crate) fn moduletree_src() -> String {
    String::from(
        r#"enum Nat {
    zero
    succ(n: Nat)
}

enum Vec[A](len: Nat) {
    nil -> Vec[A] zero
    cons[l: Nat](x: A, xs: Vec[A] l) -> Vec[A] (succ l)
}

struct ModuleDef {
    expr_num: Nat
}

struct ModuleTree {
    num: Nat
    data: Vec[ModuleDef] num
}

impl ModuleTree {
    def insert(m: ModuleDef): ModuleTree = ModuleTree.mk(succ(this.num), cons m this.data)
}

def md: ModuleDef = ModuleDef.mk(zero)

def t: ModuleTree = ModuleTree.mk(zero, nil)

println (t.insert md).num
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
