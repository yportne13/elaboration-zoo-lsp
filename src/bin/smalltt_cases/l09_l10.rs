//! L09/L10（分层宇宙 Type 0 / Type 1 / ...，**非累积**）上的 smalltt 迁移用例。
//!
//! smalltt（András Kovács）是 type-in-type：U : U，Church 编码可以任意自应用。
//! L09/L10 是分层、非累积宇宙，所以 Church 编码不能直译，必须做「宇宙层级标注 +
//! 按层级复制」：
//!
//! - Type n : Type (n+1)；Type n 与 Type m（n != m）不可合一；
//!   裸 U 在 L09 只是普通变量名（未绑定 -> error name not in scope）。
//! - Pi 的层级 = max(check_universe(域), check_universe(余域))，其中
//!   check_universe(Type n) = n + 1（因为 infer_expr(Type n) = U(n+1)）。
//!   所以 (N : Type 1) -> ... 自身活在 Type 2。
//! - 没有 impredicativity：Church 编码的宿主类型必须严格高于其迭代类型
//!   （(N : Type v) -> ... : Type (v+1)）。
//!
//! 本文件的编码（与 smalltt 的对应关系）：
//!
//! | smalltt | 本层编码 | 说明 |
//! |---|---|---|
//! | Nat : U = (n:U)->(n->n)->n->n | NatC : Type 3 = (N : Type 2) -> (N->N) -> N -> N | 抬到 Type 3：tree 用例要求 N := TreeC（TreeC : Type 2） |
//! | Tree : U = (T:U)->(T->T->T)->T->T | TreeC : Type 2 = (T : Type 1) -> (T->T->T) -> T -> T | T 必须 >= Type 1，否则 forceTree 无法把 T 实例化成 BoolC : Type 1 |
//! | Bool : U = (B:U)->B->B->B | BoolC : Type 1 = (B : Type 0) -> B -> B -> B | 迭代目标（leaf/true）在 Type 1 |
//! | Eq {A:U} x y = (P : A->U) -> P x -> P y | 两个归纳 enum EqN/EqT | 分层宇宙没有 universe polymorphism，按 A 的层级各复制一份 |
//!
//! 转换检查口径与 smalltt 相同：reflN[NatC] n1k 的返回类型是
//! EqN[NatC] n1k n1k，与注解 EqN[NatC] n1k n1kb 做合一 -> 两个 Church 数
//! 的值在 unify 里被逐层展开比较（这就是 benchmark 的口径）。
//!
//! 与 smalltt 的用例映射：
//! - natconv   ~ convn1M/5M/10M（[elabtime]：Eq n n' = refl）
//! - treeconv  ~ convt15..23（[elabtime]：Eq t t' = refl）
//! - treeconvm ~ convmt15..23（含 meta 的树转换：fullTreeWithLeaf _ n）
//! - forcetree ~ forcet15..23（[nftime]：forceTree t 的 nf）
//! - nftree    ~ nft15..23（[nftime]：树本身 t 的 nf）
//!
//! 不可直译用例（见 docs/smalltt-port-notes-l09l10.md）：
//! - idtest / pairtest / vectest：smalltt 里都是「大类型字面量 / 逐层嵌套的
//!   U 自应用」驱动的 elaboration，分层宇宙下每一层自应用都抬一级宇宙，
//!   U 的大消除在非累积宇宙里不可表达。

pub static SPECS: &[super::Spec] = &[
    super::Spec {
        name: "natconv",
        sizes: &["1k", "2k", "3k", "4k", "10k", "100k", "1M", "5M", "10M"],
        nf: false,
    },
    super::Spec {
        name: "treeconv",
        sizes: &[
            "8", "9", "10", "11", "12", "15", "18", "19", "20", "21", "22", "23",
        ],
        nf: false,
    },
    super::Spec {
        name: "treeconvm",
        sizes: &["8", "9", "10", "11", "12", "15", "18", "19", "20"],
        nf: false,
    },
    super::Spec {
        name: "forcetree",
        sizes: &["8", "9", "10", "11", "12", "15", "18", "19", "20"],
        nf: true,
    },
    super::Spec {
        name: "nftree",
        sizes: &["8", "9", "10", "11", "12", "15", "18", "19", "20"],
        nf: true,
    },
];

pub fn source(case: &str, size: &str) -> Result<String, String> {
    match case {
        "natconv" => natconv(size),
        "treeconv" => tree_case(size, TreeKind::Conv),
        "treeconvm" => tree_case(size, TreeKind::ConvM),
        "forcetree" => tree_case(size, TreeKind::Force),
        "nftree" => tree_case(size, TreeKind::Nf),
        other => Err(format!("l09_l10: unsupported case {other}")),
    }
}

// ── 编码头部 ────────────────────────────────────────────────────────────────

/// Church Nat。N : Type 2 是为了让 tree 用例能把 N 实例化成 TreeC : Type 2；
/// Pi 层级 = max(check_universe(Type 2)=3, check_universe(N->N)=2) = 3，
/// 所以 NatC 自身活在 Type 3。
const NAT_HEAD: &str = "\
def NatC : Type 3 = (N : Type 2) -> (N -> N) -> N -> N
def addC : NatC -> NatC -> NatC = a => b => N => s => z => a N s (b N s z)
def mulC : NatC -> NatC -> NatC = a => b => N => s => z => a N (b N s) z
def sucC : NatC -> NatC = a => N => s => z => s (a N s z)
";

/// Church Bool（B : Type 0 -> 自身 Type 1）：forceTree 的折叠目标，
/// 与 smalltt 的 Bool : U = (B:U)->B->B->B 同形。
const BOOL_HEAD: &str = "\
def BoolC : Type 1 = (B : Type 0) -> B -> B -> B
def trueC : BoolC = B => t => f => t
def falseC : BoolC = B => t => f => f
def andC : BoolC -> BoolC -> BoolC = a => b => B => t => f => a B (b B t f) f
";

/// Church Tree。T : Type 1（不是 Type 0）：tree 折叠目标是最低 Type 1 的
/// BoolC；若 T : Type 0 则 forceTree 无法把 T 实例化成 BoolC（非累积）。
/// Pi 层级 = max(check_universe(Type 1)=2, check_universe(T->T->T)=1) = 2。
const TREE_HEAD: &str = "\
def TreeC : Type 2 = (T : Type 1) -> (T -> T -> T) -> T -> T
def leaf : TreeC = T => n => l => l
def node : TreeC -> TreeC -> TreeC = t1 => t2 => T => n => l => n (t1 T n l) (t2 T n l)
def fullTree : NatC -> TreeC = n => n TreeC (t => node t t) leaf
def fullTreeWithLeaf : TreeC -> NatC -> TreeC = bottom => n => n TreeC (t => node t t) bottom
def forceTree : TreeC -> BoolC = t => t BoolC andC trueC
";

/// 分层宇宙没有 universe polymorphism：Eq 必须按 A 所在层级各复制一份
/// （proj_universe_stack.typort 的 stratified identity 同款做法）。
/// 每个 Eq 都是「参数 + 两个显式索引 + 一个 refl 构造子」的归纳 enum，
/// 转换检查发生在构造子返回类型 Eq a a 与期望类型 Eq x y 的合一里。
/// 注意：A 是隐式参数（方括号），x/y 与构造子字段 a 都是显式（圆括号），
/// 所以使用点是 reflN[NatC] n1k（不是 reflN[NatC, n1k]）。
const EQ_NAT: &str = "\
enum EqN[A : Type 3](x: A, y: A) {
    reflN(a: A) -> EqN a a
}
";

const EQ_TREE: &str = "\
enum EqT[A : Type 2](x: A, y: A) {
    reflT(a: A) -> EqT a a
}
";

/// 非 nf 用例的哨兵尾 def：让 ref_nf 口径只做一次平凡 quote，
/// 使时间都花在 check（= 用例的 elaboration）上。
const NF_DUMMY: &str = "def nf_dummy : Type 1 = Type 0\n";

// ── 数字阶梯 ────────────────────────────────────────────────────────────────

/// natconv 用的完整 Church 数阶梯（对齐 smalltt conv_eval.stt 的构造方式）。
fn numerals_nat() -> String {
    let mut s = String::new();
    s += "def n1 : NatC = N => s => z => s z\n";
    s += "def n2 : NatC = N => s => z => s (s z)\n";
    s += "def n3 : NatC = N => s => z => s (s (s z))\n";
    s += "def n4 : NatC = N => s => z => s (s (s (s z)))\n";
    s += "def n5 : NatC = N => s => z => s (s (s (s (s z))))\n";
    s += "def n2b = addC n1 n1\n";
    s += "def n3b = addC n2 n1\n";
    s += "def n4b = addC n3 n1\n";
    s += "def n5b = addC n4 n1\n";
    s += "def n10 = mulC n2 n5\n";
    s += "def n10b = mulC n5 n2\n";
    s += "def n20 = mulC n2 n10\n";
    s += "def n20b = mulC n2 n10b\n";
    s += "def n100 = mulC n10 n10\n";
    s += "def n100b = mulC n10b n10b\n";
    s += "def n1k = mulC n100 n10\n";
    s += "def n1kb = mulC n100b n10b\n";
    s += "def n2k = mulC n1k n2\n";
    s += "def n2kb = mulC n1kb n2\n";
    s += "def n3k = mulC n1k n3\n";
    s += "def n3kb = mulC n1kb n3\n";
    s += "def n4k = mulC n2k n2\n";
    s += "def n4kb = mulC n2kb n2\n";
    s += "def n5k = mulC n1k n5\n";
    s += "def n5kb = mulC n1kb n5\n";
    s += "def n10k = mulC n1k n10\n";
    s += "def n10kb = mulC n1kb n10b\n";
    s += "def n100k = mulC n10k n10\n";
    s += "def n100kb = mulC n10kb n10b\n";
    s += "def n1M = mulC n10k n100\n";
    s += "def n1Mb = mulC n10kb n100b\n";
    s += "def n5M = mulC n1M n5\n";
    s += "def n5Mb = mulC n1Mb n5\n";
    s += "def n10M = mulC n5M n2\n";
    s += "def n10Mb = mulC n5Mb n2\n";
    s
}

/// tree 用例用的数字阶梯（n10/n10b 起，add 逐级 +1，对齐 smalltt 的
/// n15 = add n10 n5 / n15b = add n10b n5 的「两条不同推导」口径）。
fn numerals_tree() -> String {
    let mut s = String::new();
    // 小档（10/11/12）与 smalltt 的冻结点之外的可行性探测点；n15 起完全照
    // conv_eval.stt 的推导链（n15 = add n10 n5，n18 = add n15 n3，…）。
    s += "def n1 : NatC = N => s => z => s z\n";
    s += "def n2 : NatC = N => s => z => s (s z)\n";
    s += "def n2b = addC n1 n1\n";
    s += "def n3 : NatC = N => s => z => s (s (s z))\n";
    s += "def n4 : NatC = N => s => z => s (s (s (s z)))\n";
    s += "def n4b = addC n3 n1\n";
    s += "def n5 : NatC = N => s => z => s (s (s (s (s z))))\n";
    s += "def n5b = addC n4 n1\n";
    s += "def n6 = addC n5 n1\n";
    s += "def n6b = addC n5b n1\n";
    s += "def n7 = addC n6 n1\n";
    s += "def n7b = addC n6b n1\n";
    s += "def n8 = addC n7 n1\n";
    s += "def n8b = addC n7b n1\n";
    s += "def n9 = addC n8 n1\n";
    s += "def n9b = addC n8b n1\n";
    s += "def n10 = mulC n2 n5\n";
    s += "def n10b = mulC n5 n2\n";
    s += "def n11 = addC n10 n1\n";
    s += "def n11b = addC n10b n1\n";
    s += "def n12 = addC n11 n1\n";
    s += "def n12b = addC n11b n1\n";
    s += "def n15 = addC n10 n5\n";
    s += "def n15b = addC n10b n5\n";
    s += "def n18 = addC n15 n3\n";
    s += "def n18b = addC n15b n3\n";
    s += "def n19 = addC n15 n4\n";
    s += "def n19b = addC n15b n4\n";
    s += "def n20 = mulC n2 n10\n";
    s += "def n20b = mulC n2 n10b\n";
    s += "def n21 = sucC n20\n";
    s += "def n21b = sucC n20b\n";
    s += "def n22 = sucC n21\n";
    s += "def n22b = sucC n21b\n";
    s += "def n23 = sucC n22\n";
    s += "def n23b = sucC n22b\n";
    s
}

// ── natconv ────────────────────────────────────────────────────────────────

fn nat_pair(size: &str) -> Result<(&'static str, &'static str), String> {
    Ok(match size {
        // 冒烟档（调试用；SPECS 里不暴露）
        "2" => ("n2", "n2b"),
        "3" => ("n3", "n3b"),
        "4" => ("n4", "n4b"),
        "5" => ("n5", "n5b"),
        "10" => ("n10", "n10b"),
        "20" => ("n20", "n20b"),
        "100" => ("n100", "n100b"),
        // 正式档
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
    let (a, b) = nat_pair(size)?;
    let mut s = String::new();
    s += NAT_HEAD;
    s += &numerals_nat();
    s += EQ_NAT;
    // 语义闸门 + benchmark 主体：reflN[NatC] a 的返回类型索引是 (a,a)，
    // 与注解的 (a,b) 合一 -> a ~ b 的转换检查。
    s += &format!("def conv : EqN[NatC] {a} {b} = reflN[NatC] {a}\n");
    s += NF_DUMMY;
    Ok(s)
}

// ── tree 家族 ──────────────────────────────────────────────────────────────

enum TreeKind {
    /// EqT[TreeC] t t' = reflT[TreeC] t
    Conv,
    /// EqT[TreeC] t' (fullTreeWithLeaf _ n) = reflT[TreeC] t'（转换中含 meta）
    ConvM,
    /// forceTree t 的 nf
    Force,
    /// 树本身 t 的 nf
    Nf,
}

fn tree_pair(size: &str) -> Result<(&'static str, &'static str), String> {
    Ok(match size {
        "2" => ("n2", "n2b"),
        "4" => ("n4", "n4b"),
        "5" => ("n5", "n5b"),
        "6" => ("n6", "n6b"),
        "7" => ("n7", "n7b"),
        "8" => ("n8", "n8b"),
        "9" => ("n9", "n9b"),
        "10" => ("n10", "n10b"),
        "11" => ("n11", "n11b"),
        "12" => ("n12", "n12b"),
        "15" => ("n15", "n15b"),
        "18" => ("n18", "n18b"),
        "19" => ("n19", "n19b"),
        "20" => ("n20", "n20b"),
        "21" => ("n21", "n21b"),
        "22" => ("n22", "n22b"),
        "23" => ("n23", "n23b"),
        other => return Err(format!("tree: unknown depth {other}")),
    })
}

fn tree_case(size: &str, kind: TreeKind) -> Result<String, String> {
    let (n, nb) = tree_pair(size)?;
    let mut s = String::new();
    s += BOOL_HEAD;
    s += NAT_HEAD;
    s += TREE_HEAD;
    s += &numerals_tree();
    s += &format!("def t{size} = fullTree {n}\n");
    s += &format!("def t{size}b = fullTree {nb}\n");
    match kind {
        TreeKind::Conv => {
            s += EQ_TREE;
            s += &format!("def conv : EqT[TreeC] t{size} t{size}b = reflT[TreeC] t{size}\n");
            s += NF_DUMMY;
        }
        TreeKind::ConvM => {
            s += EQ_TREE;
            // 期望类型里带一个洞 _（类型 TreeC 的 meta）；转换比较到叶子时
            // 由合一解出 ?leaf := leaf——smalltt convmt 的 meta 口径。
            s += &format!(
                "def convm : EqT[TreeC] t{size}b (fullTreeWithLeaf _ {n}) = reflT[TreeC] t{size}b\n"
            );
            s += NF_DUMMY;
        }
        TreeKind::Force => {
            s += &format!("def ft{size} : BoolC = forceTree t{size}\n");
        }
        TreeKind::Nf => {
            s += &format!("def nt{size} : TreeC = t{size}\n");
        }
    }
    Ok(s)
}
