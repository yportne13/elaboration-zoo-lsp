//! L07/L08（type-in-type：单一 U）上的 smalltt 迁移用例。
//!
//! 对应 smalltt bench/conv_eval.stt：
//! - natconv   ~ convn1M/n5M/n10M   ：两个 Church 自然数的转换检查（elab）
//! - treeconv  ~ convt15..t23       ：两棵完整 Church 二叉树转换检查（elab）
//! - treeconvm ~ convmt15..m23      ：一侧含 hole 的树转换（elab，approximate conv）
//! - forcetree ~ forcet15..t23      ：forceTree 折叠（nf）
//! - nftree    ~ nft15..t23         ：整棵树的 nf（nf）
//!
//! 对应 smalltt bench/asymptotics.stt：
//! - idtest    ~ idTest             ：40 次迭代的 id（elab）
//! - pairtest  ~ pairTest           ：dup 嵌套 Pair（let 链，elab）
//! - vectest   ~ vecTest            ：length-indexed Vec 的 cons 链（elab）
//!
//! 写域：本文件由 porter-l07l08 负责；其他 agent 不要动。

pub static SPECS: &[super::Spec] = &[
    // 默认 fuel（4096）下 natconv 实测上限 = 4k（1k..4k PASS，5k/10k 燃料耗尽）；
    // 5k/10k/100k 是留给 TYPORT_UNIFY_FUEL 放大口径的探测点。
    super::Spec {
        name: "natconv",
        sizes: &[
            "1k", "2k", "3k", "4k", "5k", "10k", "100k", "1M", "5M", "10M",
        ],
        nf: false,
    },
    // tree 族 curated 深度集合（与 Lead 约定的最终测量集）：10 默认 fuel 可跑；
    // 11/12 做 fuel 放大曲线的细档；15 直接对照 smalltt 公布数字；18 是重档
    // （19..23 会爆时间预算，不列入）。
    super::Spec {
        name: "treeconv",
        sizes: &["10", "11", "12", "15", "18", "19", "20", "21", "22", "23"],
        nf: false,
    },
    super::Spec {
        name: "treeconvm",
        sizes: &["10", "11", "12", "15", "18", "19", "20"],
        nf: false,
    },
    super::Spec {
        name: "forcetree",
        sizes: &["10", "12", "14", "15", "18", "19", "20"],
        nf: true,
    },
    super::Spec {
        name: "nftree",
        sizes: &["10", "12", "14", "15", "18", "19", "20"],
        nf: true,
    },
    // 以下三例 smalltt 用 type-in-type（U : U）表达，L07/L08 直译；L09/L10 分层
    // 宇宙下不可直译（见 l09_l10.rs / 报告）。
    // idtest = 40 次 id（上游一致）。
    super::Spec {
        name: "idtest",
        sizes: &["40"],
        nf: false,
    },
    // pairtest：上游 x0..x30（31 个 let，30 次 dup）。L07/L08 无 glued eval/meta
    // 共享 ⇒ let 类型 quote 指数爆炸：实测 10=7ms、15=0.26s、20=7.7s（1 轮，载荷下），
    // 25/30 外推 ~4min/~2h，不可作基准 → SPECS 只留 10/15/20，25/30 记「不可行」。
    super::Spec {
        name: "pairtest",
        sizes: &["10", "15", "20"],
        nf: false,
    },
    // vecTest：上游恰好 960 个 cons U；240 作缩放对照。
    super::Spec {
        name: "vectest",
        sizes: &["240", "960"],
        nf: false,
    },
];

pub fn source(case: &str, size: &str) -> Result<String, String> {
    match case {
        "natconv" => natconv(size),
        "treeconv" => tree_core(size, TreeKind::Conv),
        "treeconvm" => tree_core(size, TreeKind::ConvM),
        "forcetree" => tree_core(size, TreeKind::Force),
        "nftree" => tree_core(size, TreeKind::Nf),
        "idtest" => idtest(size),
        "pairtest" => pairtest(size),
        "vectest" => vectest(size),
        other => Err(format!("l07_l08: unsupported case {other}")),
    }
}

fn nat_head() -> String {
    String::from(
        "def NatC : U = (N : U) -> (N -> N) -> N -> N
def add : NatC -> NatC -> NatC = a => b => N => s => z => a N s (b N s z)
def mul : NatC -> NatC -> NatC = a => b => N => s => z => a N (b N s) z
def n2 : NatC = N => s => z => s (s z)
def n3 : NatC = N => s => z => s (s (s z))
def n4 : NatC = N => s => z => s (s (s (s z)))
def n5 : NatC = N => s => z => s (s (s (s (s z))))
def n10 = mul n2 n5
def n10b = mul n5 n2
def n100 = mul n10 n10
def n100b = mul n10b n10b
def n1k = mul n100 n10
def n1kb = mul n100b n10b
def n2k = mul n1k n2
def n2kb = mul n1kb n2
def n3k = mul n1k n3
def n3kb = mul n1kb n3
def n4k = mul n2k n2
def n4kb = mul n2kb n2
def n5k = mul n1k n5
def n5kb = mul n1kb n5
def n10k = mul n1k n10
def n10kb = mul n1kb n10b
def n100k = mul n10k n10
def n100kb = mul n10kb n10b
def n1M = mul n1k n1k
def n1Mb = mul n1kb n1kb
def n5M = mul n1M n5
def n5Mb = mul n5 n1Mb
def n10M = mul n5M n2
def n10Mb = mul n2 n5Mb
",
    )
}

fn eq_head() -> String {
    String::from(
        "def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = P => px => px
",
    )
}

fn nat_side(size: &str) -> Result<(&'static str, &'static str), String> {
    Ok(match size {
        "1k" => ("n1k", "n1kb"),
        "2k" => ("n2k", "n2kb"),
        "3k" => ("n3k", "n3kb"),
        "4k" => ("n4k", "n4kb"),
        "5k" => ("n5k", "n5kb"),
        "10k" => ("n10k", "n10kb"),
        "100k" => ("n100k", "n100kb"),
        "1M" => ("n1M", "n1Mb"),
        "5M" => ("n5M", "n5Mb"),
        "10M" => ("n10M", "n10Mb"),
        other => return Err(format!("natconv: unknown size {other}")),
    })
}

fn natconv(size: &str) -> Result<String, String> {
    let (a, b) = nat_side(size)?;
    let mut s = nat_head();
    s.push_str(&eq_head());
    s.push_str(&format!(
        "def conv : Eq {a} {b} = refl
def nf_dummy : U = U
"
    ));
    Ok(s)
}

// ── tree 族 ────────────────────────────────────────────────────────────────

enum TreeKind {
    Conv,
    ConvM,
    Force,
    Nf,
}

fn nat_tower() -> String {
    // d = 10..=23 的 n_d / n_db：两侧结构不同（add 顺序 / mul 拆分不同）但数值相同。
    let mut s = String::from(
        "def n1 : NatC = N => s => z => s z
def n6 = add n5 n1
def n7 = add n5 n2
def n8 = add n5 n3
def n9 = add n5 n4
def n11 = add n10 n1
def n11b = add n1 n10b
def n12 = add n10 n2
def n12b = add n2 n10b
def n13 = add n10 n3
def n13b = add n3 n10b
def n14 = add n10 n4
def n14b = add n4 n10b
def n15 = add n14 n1
def n15b = add n1 n14b
def n16 = add n15 n1
def n16b = add n1 n15b
def n17 = add n15 n2
def n17b = add n2 n15b
def n18 = add n15 n3
def n18b = add n3 n15b
def n19 = add n15 n4
def n19b = add n4 n15b
def n20 = add n15 n5
def n20b = add n5 n15b
def n21 = add n20 n1
def n21b = add n1 n20b
def n22 = add n21 n1
def n22b = add n1 n21b
def n23 = add n22 n1
def n23b = add n1 n22b
",
    );
    s.push_str("");
    s
}

fn tree_core(size: &str, kind: TreeKind) -> Result<String, String> {
    let d: u32 = size
        .parse()
        .map_err(|_| format!("tree: bad depth {size}"))?;
    if !(8..=24).contains(&d) {
        return Err(format!("tree: depth {d} out of range"));
    }
    let mut s = String::from(
        "def BoolC : U = (B : U) -> B -> B -> B
def true : BoolC = B => t => f => t
def and : BoolC -> BoolC -> BoolC = a => b => B => t => f => a B (b B t f) f
def NatC : U = (N : U) -> (N -> N) -> N -> N
def add : NatC -> NatC -> NatC = a => b => N => s => z => a N s (b N s z)
def mul : NatC -> NatC -> NatC = a => b => N => s => z => a N (b N s) z
def n2 : NatC = N => s => z => s (s z)
def n3 : NatC = N => s => z => s (s (s z))
def n4 : NatC = N => s => z => s (s (s (s z)))
def n5 : NatC = N => s => z => s (s (s (s (s z))))
def n10 = mul n2 n5
def n10b = mul n5 n2
def TreeC : U = (T : U) -> (T -> T -> T) -> T -> T
def leaf : TreeC = T => n => l => l
def node : TreeC -> TreeC -> TreeC = t1 => t2 => T => n => l => n (t1 T n l) (t2 T n l)
def fullTree : NatC -> TreeC = n => n TreeC (t => node t t) leaf
def fullTreeWithLeaf : TreeC -> NatC -> TreeC = bottom => n => n TreeC (t => node t t) bottom
def forceTree : TreeC -> BoolC = t => t BoolC and true
def Eq[A : U](x: A, y: A): U = (P : A -> U) -> P x -> P y
def refl[A : U, x: A]: Eq[A] x x = P => px => px
",
    );
    s.push_str(&nat_tower());
    s.push_str(&format!(
        "def t{d} = fullTree n{d}
def t{d}b = fullTree n{d}b
"
    ));
    let tail = match kind {
        TreeKind::Conv => format!(
            "def convt{d} : Eq t{d} t{d}b = refl
def nf_dummy : U = U
"
        ),
        TreeKind::ConvM => format!(
            "def convmt{d} : Eq t{d}b (fullTreeWithLeaf _ n{d}) = refl
def nf_dummy : U = U
"
        ),
        TreeKind::Force => format!("def forcet{d} = forceTree t{d}\n"),
        TreeKind::Nf => format!("def nft{d} = t{d}\n"),
    };
    s.push_str(&tail);
    Ok(s)
}

// ── asymptotics 族（smalltt bench/asymptotics.stt）─────────────────────────
//
// 三例都依赖 type-in-type（U : U / U 可以当实参传给泛型 id、dup、cons），
// L07/L08 可直译。每个用例最后一个 def 必须是极小项（nf_dummy），否则
// ref_nf 口径会把巨型类型/值 quote 出来（pairTest 的 2^k 节点）。

/// idTest：`id id … id`，size = id 的个数（smalltt 原例 = 40，elab 口径）。
fn idtest(size: &str) -> Result<String, String> {
    let n: u32 = size
        .parse()
        .map_err(|_| format!("idtest: bad size {size}"))?;
    if n == 0 {
        return Err(String::from("idtest: size must be >= 1"));
    }
    let mut s = String::from("def id[A : U](x : A) : A = x\n");
    s.push_str("def idtest : [A : U] -> A -> A =");
    for _ in 0..n {
        s.push_str(" id");
    }
    s.push_str("\ndef nf_dummy : U = U\n");
    Ok(s)
}

/// pairTest：size = dup 的层数（x0 = dup U，x1 = dup x0 …，smalltt 原例 x0..x30）。
/// 用 let 链（无类型注解），复刻 smalltt 的「类型逐层翻转」负载。
fn pairtest(size: &str) -> Result<String, String> {
    let depth: u32 = size
        .parse()
        .map_err(|_| format!("pairtest: bad depth {size}"))?;
    if depth == 0 || depth > 64 {
        return Err(format!("pairtest: depth {depth} out of range 1..=64"));
    }
    let mut s = String::from(
        "def Pair : U -> U -> U = A => B => (P : U) -> (A -> B -> P) -> P
def dup[A : U](a : A) : Pair A A = P => p => p a a
",
    );
    s.push_str(&format!("def pairtest{depth} =\n    let x0 = dup U;\n"));
    for i in 1..depth {
        s.push_str(&format!("    let x{i} = dup x{};\n", i - 1));
    }
    s.push_str(&format!("    x{}\ndef nf_dummy : U = U\n", depth - 1));
    Ok(s)
}

/// vecTest：size = Church Vec 的 cons 个数（smalltt 原例 = 960，elab 口径）。
fn vectest(size: &str) -> Result<String, String> {
    let n: u32 = size
        .parse()
        .map_err(|_| format!("vectest: bad size {size}"))?;
    if n > 4096 {
        return Err(format!("vectest: size {n} too large"));
    }
    let mut body = String::from("nil");
    for _ in 0..n {
        body = format!("cons U ({body})");
    }
    let mut s = String::from(
        "def NatC : U = (N : U) -> (N -> N) -> N -> N
def zero : NatC = N => s => z => z
def suc : NatC -> NatC = a => N => s => z => s (a N s z)
def Vec : U -> NatC -> U = A => n => (V : NatC -> U) -> ([k : NatC] -> A -> V k -> V (suc k)) -> V zero -> V n
def nil[A : U] : Vec A zero = V => c => z => z
def cons[A : U, n : NatC](a : A)(as : Vec A n) : Vec A (suc n) = V => c => z => c a (as V c z)
",
    );
    s.push_str(&format!("def vectest{n} = {body}\ndef nf_dummy : U = U\n"));
    Ok(s)
}
