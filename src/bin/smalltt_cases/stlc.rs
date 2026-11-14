//! smalltt bench/stlc.stt、stlc_lessimpl.stt、stlc_small.stt 的 L07/L08 迁移。
//!
//! smalltt 的 stlc 家族是「大文件 elaboration 吞吐」用例：一个模板文件按
//! GenTestFiles.hs 的 render/times 规则复制 N 份（百分号 → 拷贝序号；序号 0
//! 替换为空串，其余替换为十进制数字），每份定义名唯一。本文件负责：
//! 1. 把 smalltt 模板翻译成 typort 语法（type-in-type，L07/L08 可直译）；
//! 2. 用同样的复制/改名策略生成 1/8/40/80/96/192 份的源码；
//! 3. 与 smalltt 公布的数字对齐口径（整文件 elaborate）。
//!
//! 语法映射（详见 docs/smalltt-port-notes-stlc.md）：
//! - λ x y. t → x => y => t；→ 改成 ->
//! - {Γ A} → T（隐式 Π）→ [Γ : _, A : _] -> T；def 头 {Γ A} → [Γ, A] 参数
//! - smalltt 的 _ 洞 → typort _
//! - case 是 typort 关键字 → 模板里改名为 scase
//! - 隐式实参：full stlc 用裸应用（靠隐式插入），stlc_lessimpl/stlc_small 用
//!   模板自带的 _ _ 显式占位（对应 smalltt 的 less-implicit 版本）
//!
//! 每个用例的源码最后追加 def nf_dummy : U = U：驱动取「最后一个 def」做
//! ref_nf 口径，尾 def 必须极小（stlc 是 elab 用例，nf 不计分）。
//!
//! 写域：本文件由 porter-stlc 负责。

pub static SPECS: &[super::Spec] = &[
    // stlc 家族：stlc.stt（165 行完整模板：Ty/Con/Tm Church 编码 + 内部函数）
    super::Spec {
        name: "stlc",
        sizes: &["1", "8", "40", "80"],
        nf: false,
    },
    // stlc_small 家族：stlc_small.stt（71 行最小模板：只有 var/lam/app）
    super::Spec {
        name: "stlcs",
        sizes: &["1", "8", "96", "192"],
        nf: false,
    },
    // stlc_lessimpl 家族：stlc_lessimpl.stt（同 stlc 但 Church 编码内无隐式参数）
    super::Spec {
        name: "stlcl",
        sizes: &["1", "40", "80"],
        nf: false,
    },
];

pub fn source(case: &str, size: &str) -> Result<String, String> {
    let tpl = match case {
        "stlc" => STLC_TPL,
        "stlcs" => STLCS_TPL,
        "stlcl" => STLCL_TPL,
        other => return Err(format!("stlc: unsupported case {other}")),
    };
    let n: usize = size
        .parse()
        .map_err(|_| format!("{case}: bad size label {size}"))?;
    if n == 0 || n > 4096 {
        return Err(format!("{case}: copy count {n} out of range (1..=4096)"));
    }
    Ok(render(tpl, n))
}

/// GenTestFiles.hs 的 render/times 等价物：第 i 份把百分号换成 i
/// （i == 0 换成空串，与 smalltt 的 if n == 0 then "" else show n 一致），
/// 再把 N 份首尾相接。最后追加极小尾 def 供 ref_nf 口径选取。
fn render(tpl: &str, n: usize) -> String {
    let mut out = String::with_capacity(tpl.len() * n + 64 * n + 32);
    for i in 0..n {
        let suffix = if i == 0 { String::new() } else { i.to_string() };
        let copy = tpl.replace('%', &suffix);
        out.push_str(&copy);
        out.push('\n');
    }
    out.push_str("def nf_dummy : U = U\n");
    out
}

// ── stlc_small.stt：最小模板（19 defs） ─────────────────────────────────────
//
// Church-coded STLC + interpreter 的最小版本：只有 Ty/Con/Var/Tm 与
// var/lam/app，变量 v0..v4，最后一个 test 是 6 层嵌套应用。
// Church 编码内部的 binder 采用 smalltt 原文件的显式 (Γ : _)(A : _) 写法，
// 应用处用 _ 占位（对应 smalltt 的 vz _ _）。
const STLCS_TPL: &str = r#"def Ty% : U = (Ty : U) -> (ι : Ty) -> (arr : Ty -> Ty -> Ty) -> Ty
def ι% : Ty% = _ => ι => _ => ι
def arr% : Ty% -> Ty% -> Ty% = A => B => Ty => ι => arr => arr (A Ty ι arr) (B Ty ι arr)
def Con% : U = (Con : U) -> (nil : Con) -> (snoc : Con -> Ty% -> Con) -> Con
def nil% : Con% = Con => nil => snoc => nil
def snoc% : Con% -> Ty% -> Con% = Γ => A => Con => nil => snoc => snoc (Γ Con nil snoc) A
def Var% : Con% -> Ty% -> U = Γ => A => (Var : Con% -> Ty% -> U) -> (vz : (Γ : _) -> (A : _) -> Var (snoc% Γ A) A) -> (vs : (Γ : _) -> (B : _) -> (A : _) -> Var Γ A -> Var (snoc% Γ B) A) -> Var Γ A
def vz%[Γ, A] : Var% (snoc% Γ A) A = Var => vz => vs => vz _ _
def vs%[Γ, B, A](x : Var% Γ A) : Var% (snoc% Γ B) A = Var => vz => vs => vs _ _ _ (x Var vz vs)
def Tm% : Con% -> Ty% -> U = Γ => A => (Tm : Con% -> Ty% -> U) -> (var : (Γ : _) -> (A : _) -> Var% Γ A -> Tm Γ A) -> (lam : (Γ : _) -> (A : _) -> (B : _) -> Tm (snoc% Γ A) B -> Tm Γ (arr% A B)) -> (app : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ (arr% A B) -> Tm Γ A -> Tm Γ B) -> Tm Γ A
def var%[Γ, A](x : Var% Γ A) : Tm% Γ A = Tm => var => lam => app => var _ _ x
def lam%[Γ, A, B](t : Tm% (snoc% Γ A) B) : Tm% Γ (arr% A B) = Tm => var => lam => app => lam _ _ _ (t Tm var lam app)
def app%[Γ, A, B](t : Tm% Γ (arr% A B), u : Tm% Γ A) : Tm% Γ B = Tm => var => lam => app => app _ _ _ (t Tm var lam app) (u Tm var lam app)
def v0%[Γ, A] : Tm% (snoc% Γ A) A = var% vz%
def v1%[Γ, A, B] : Tm% (snoc% (snoc% Γ A) B) A = var% (vs% vz%)
def v2%[Γ, A, B, C] : Tm% (snoc% (snoc% (snoc% Γ A) B) C) A = var% (vs% (vs% vz%))
def v3%[Γ, A, B, C, D] : Tm% (snoc% (snoc% (snoc% (snoc% Γ A) B) C) D) A = var% (vs% (vs% (vs% vz%)))
def v4%[Γ, A, B, C, D, E] : Tm% (snoc% (snoc% (snoc% (snoc% (snoc% Γ A) B) C) D) E) A = var% (vs% (vs% (vs% (vs% vz%))))
def test%[Γ, A] : Tm% Γ (arr% (arr% A A) (arr% A A)) = lam% (lam% (app% v1% (app% v1% (app% v1% (app% v1% (app% v1% (app% v1% v0%)))))))
"#;

// ── stlc.stt：完整模板（40 defs） ───────────────────────────────────────────
//
// 与 stlc_small 相比多了 nat/top/bot/arr/prod/sum 的 Ty 构造子、Tm 的
// tt/pair/fst/snd/left/right/case/zero/suc/rec 字段，以及 tbool/true/tfalse/
// ifthenelse/times4/add/mul/fact 等内部定义。Church 编码内部的字段是隐式
// Π（{Γ A} →），本模板忠实保留为 [Γ : _, A : _] ->，应用处写裸应用
// （同 smalltt 原文件，靠隐式插入补实参）。case 改名为 scase（关键字冲突）。
const STLC_TPL: &str = r#"def Ty% : U = (Ty : U) -> (nat : Ty) -> (top : Ty) -> (bot : Ty) -> (arr : Ty -> Ty -> Ty) -> (prod : Ty -> Ty -> Ty) -> (sum : Ty -> Ty -> Ty) -> Ty
def nat% : Ty% = _ => nat => _ => _ => _ => _ => _ => nat
def top% : Ty% = _ => _ => top => _ => _ => _ => _ => top
def bot% : Ty% = _ => _ => _ => bot => _ => _ => _ => bot
def arr% : Ty% -> Ty% -> Ty% = A => B => Ty => nat => top => bot => arr => prod => sum => arr (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)
def prod% : Ty% -> Ty% -> Ty% = A => B => Ty => nat => top => bot => arr => prod => sum => prod (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)
def sum% : Ty% -> Ty% -> Ty% = A => B => Ty => nat => top => bot => arr => prod => sum => sum (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)
def Con% : U = (Con : U) -> (nil : Con) -> (snoc : Con -> Ty% -> Con) -> Con
def nil% : Con% = Con => nil => snoc => nil
def snoc% : Con% -> Ty% -> Con% = Γ => A => Con => nil => snoc => snoc (Γ Con nil snoc) A
def Var% : Con% -> Ty% -> U = Γ => A => (Var : Con% -> Ty% -> U) -> (vz : [Γ : _, A : _] -> Var (snoc% Γ A) A) -> (vs : [Γ : _, B : _, A : _] -> Var Γ A -> Var (snoc% Γ B) A) -> Var Γ A
def vz%[Γ, A] : Var% (snoc% Γ A) A = Var => vz => vs => vz
def vs%[Γ, B, A](x : Var% Γ A) : Var% (snoc% Γ B) A = Var => vz => vs => vs (x Var vz vs)
def Tm% : Con% -> Ty% -> U = Γ => A => (Tm : Con% -> Ty% -> U) -> (var : [Γ : _, A : _] -> Var% Γ A -> Tm Γ A) -> (lam : [Γ : _, A : _, B : _] -> Tm (snoc% Γ A) B -> Tm Γ (arr% A B)) -> (app : [Γ : _, A : _, B : _] -> Tm Γ (arr% A B) -> Tm Γ A -> Tm Γ B) -> (tt : [Γ : _] -> Tm Γ top%) -> (pair : [Γ : _, A : _, B : _] -> Tm Γ A -> Tm Γ B -> Tm Γ (prod% A B)) -> (fst : [Γ : _, A : _, B : _] -> Tm Γ (prod% A B) -> Tm Γ A) -> (snd : [Γ : _, A : _, B : _] -> Tm Γ (prod% A B) -> Tm Γ B) -> (left : [Γ : _, A : _, B : _] -> Tm Γ A -> Tm Γ (sum% A B)) -> (right : [Γ : _, A : _, B : _] -> Tm Γ B -> Tm Γ (sum% A B)) -> (scase : [Γ : _, A : _, B : _, C : _] -> Tm Γ (sum% A B) -> Tm Γ (arr% A C) -> Tm Γ (arr% B C) -> Tm Γ C) -> (zero : [Γ : _] -> Tm Γ nat%) -> (suc : [Γ : _] -> Tm Γ nat% -> Tm Γ nat%) -> (rec : [Γ : _, A : _] -> Tm Γ nat% -> Tm Γ (arr% nat% (arr% A A)) -> Tm Γ A -> Tm Γ A) -> Tm Γ A
def var%[Γ, A](x : Var% Γ A) : Tm% Γ A = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => var x
def lam%[Γ, A, B](t : Tm% (snoc% Γ A) B) : Tm% Γ (arr% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => lam (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def app%[Γ, A, B](t : Tm% Γ (arr% A B), u : Tm% Γ A) : Tm% Γ B = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => app (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec)
def tt%[Γ] : Tm% Γ top% = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => tt
def pair%[Γ, A, B](t : Tm% Γ A, u : Tm% Γ B) : Tm% Γ (prod% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => pair (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec)
def fst%[Γ, A, B](t : Tm% Γ (prod% A B)) : Tm% Γ A = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => fst (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def snd%[Γ, A, B](t : Tm% Γ (prod% A B)) : Tm% Γ B = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => snd (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def left%[Γ, A, B](t : Tm% Γ A) : Tm% Γ (sum% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => left (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def right%[Γ, A, B](t : Tm% Γ B) : Tm% Γ (sum% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => right (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def scase%[Γ, A, B, C](t : Tm% Γ (sum% A B), u : Tm% Γ (arr% A C), v : Tm% Γ (arr% B C)) : Tm% Γ C = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => scase (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec) (v Tm var lam app tt pair fst snd left right scase zero suc rec)
def zero%[Γ] : Tm% Γ nat% = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => zero
def suc%[Γ](t : Tm% Γ nat%) : Tm% Γ nat% = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => suc (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def rec%[Γ, A](t : Tm% Γ nat%, u : Tm% Γ (arr% nat% (arr% A A)), v : Tm% Γ A) : Tm% Γ A = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => rec (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec) (v Tm var lam app tt pair fst snd left right scase zero suc rec)
def v0%[Γ, A] : Tm% (snoc% Γ A) A = var% vz%
def v1%[Γ, A, B] : Tm% (snoc% (snoc% Γ A) B) A = var% (vs% vz%)
def v2%[Γ, A, B, C] : Tm% (snoc% (snoc% (snoc% Γ A) B) C) A = var% (vs% (vs% vz%))
def v3%[Γ, A, B, C, D] : Tm% (snoc% (snoc% (snoc% (snoc% Γ A) B) C) D) A = var% (vs% (vs% (vs% vz%)))
def tbool% : Ty% = sum% top% top%
def true%[Γ] : Tm% Γ tbool% = left% tt%
def tfalse%[Γ] : Tm% Γ tbool% = right% tt%
def ifthenelse%[Γ, A] : Tm% Γ (arr% tbool% (arr% A (arr% A A))) = lam% (lam% (lam% (scase% v2% (lam% v2%) (lam% v1%))))
def times4%[Γ, A] : Tm% Γ (arr% (arr% A A) (arr% A A)) = lam% (lam% (app% v1% (app% v1% (app% v1% (app% v1% v0%)))))
def add%[Γ] : Tm% Γ (arr% nat% (arr% nat% nat%)) = lam% (rec% v0% (lam% (lam% (lam% (suc% (app% v1% v0%))))) (lam% v0%))
def mul%[Γ] : Tm% Γ (arr% nat% (arr% nat% nat%)) = lam% (rec% v0% (lam% (lam% (lam% (app% (app% add% (app% v1% v0%)) v0%)))) (lam% zero%))
def fact%[Γ] : Tm% Γ (arr% nat% nat%) = lam% (rec% v0% (lam% (lam% (app% (app% mul% (suc% v1%)) v0%))) (suc% zero%))
"#;

// ── stlc_lessimpl.stt：完整模板、Church 编码内无隐式参数（40 defs） ────────
//
// 与 stlc.stt 结构相同，但 Var/Tm 的字段 binder 是显式 (Γ : _)(A : _)，
// 应用处写出 _ _ / _ _ _ 占位（smalltt 的 less-implicit 版本；Coq 只能跑
// 这个版本）。typort 侧与 stlc 只差这些占位与隐式 Π 的写法。
const STLCL_TPL: &str = r#"def Ty% : U = (Ty : U) -> (nat : Ty) -> (top : Ty) -> (bot : Ty) -> (arr : Ty -> Ty -> Ty) -> (prod : Ty -> Ty -> Ty) -> (sum : Ty -> Ty -> Ty) -> Ty
def nat% : Ty% = _ => nat => _ => _ => _ => _ => _ => nat
def top% : Ty% = _ => _ => top => _ => _ => _ => _ => top
def bot% : Ty% = _ => _ => _ => bot => _ => _ => _ => bot
def arr% : Ty% -> Ty% -> Ty% = A => B => Ty => nat => top => bot => arr => prod => sum => arr (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)
def prod% : Ty% -> Ty% -> Ty% = A => B => Ty => nat => top => bot => arr => prod => sum => prod (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)
def sum% : Ty% -> Ty% -> Ty% = A => B => Ty => nat => top => bot => arr => prod => sum => sum (A Ty nat top bot arr prod sum) (B Ty nat top bot arr prod sum)
def Con% : U = (Con : U) -> (nil : Con) -> (snoc : Con -> Ty% -> Con) -> Con
def nil% : Con% = Con => nil => snoc => nil
def snoc% : Con% -> Ty% -> Con% = Γ => A => Con => nil => snoc => snoc (Γ Con nil snoc) A
def Var% : Con% -> Ty% -> U = Γ => A => (Var : Con% -> Ty% -> U) -> (vz : (Γ : _) -> (A : _) -> Var (snoc% Γ A) A) -> (vs : (Γ : _) -> (B : _) -> (A : _) -> Var Γ A -> Var (snoc% Γ B) A) -> Var Γ A
def vz%[Γ, A] : Var% (snoc% Γ A) A = Var => vz => vs => vz _ _
def vs%[Γ, B, A](x : Var% Γ A) : Var% (snoc% Γ B) A = Var => vz => vs => vs _ _ _ (x Var vz vs)
def Tm% : Con% -> Ty% -> U = Γ => A => (Tm : Con% -> Ty% -> U) -> (var : (Γ : _) -> (A : _) -> Var% Γ A -> Tm Γ A) -> (lam : (Γ : _) -> (A : _) -> (B : _) -> Tm (snoc% Γ A) B -> Tm Γ (arr% A B)) -> (app : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ (arr% A B) -> Tm Γ A -> Tm Γ B) -> (tt : (Γ : _) -> Tm Γ top%) -> (pair : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ A -> Tm Γ B -> Tm Γ (prod% A B)) -> (fst : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ (prod% A B) -> Tm Γ A) -> (snd : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ (prod% A B) -> Tm Γ B) -> (left : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ A -> Tm Γ (sum% A B)) -> (right : (Γ : _) -> (A : _) -> (B : _) -> Tm Γ B -> Tm Γ (sum% A B)) -> (scase : (Γ : _) -> (A : _) -> (B : _) -> (C : _) -> Tm Γ (sum% A B) -> Tm Γ (arr% A C) -> Tm Γ (arr% B C) -> Tm Γ C) -> (zero : (Γ : _) -> Tm Γ nat%) -> (suc : (Γ : _) -> Tm Γ nat% -> Tm Γ nat%) -> (rec : (Γ : _) -> (A : _) -> Tm Γ nat% -> Tm Γ (arr% nat% (arr% A A)) -> Tm Γ A -> Tm Γ A) -> Tm Γ A
def var%[Γ, A](x : Var% Γ A) : Tm% Γ A = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => var _ _ x
def lam%[Γ, A, B](t : Tm% (snoc% Γ A) B) : Tm% Γ (arr% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => lam _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def app%[Γ, A, B](t : Tm% Γ (arr% A B), u : Tm% Γ A) : Tm% Γ B = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => app _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec)
def tt%[Γ] : Tm% Γ top% = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => tt _
def pair%[Γ, A, B](t : Tm% Γ A, u : Tm% Γ B) : Tm% Γ (prod% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => pair _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec)
def fst%[Γ, A, B](t : Tm% Γ (prod% A B)) : Tm% Γ A = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => fst _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def snd%[Γ, A, B](t : Tm% Γ (prod% A B)) : Tm% Γ B = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => snd _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def left%[Γ, A, B](t : Tm% Γ A) : Tm% Γ (sum% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => left _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def right%[Γ, A, B](t : Tm% Γ B) : Tm% Γ (sum% A B) = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => right _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def scase%[Γ, A, B, C](t : Tm% Γ (sum% A B), u : Tm% Γ (arr% A C), v : Tm% Γ (arr% B C)) : Tm% Γ C = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => scase _ _ _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec) (v Tm var lam app tt pair fst snd left right scase zero suc rec)
def zero%[Γ] : Tm% Γ nat% = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => zero _
def suc%[Γ](t : Tm% Γ nat%) : Tm% Γ nat% = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => suc _ (t Tm var lam app tt pair fst snd left right scase zero suc rec)
def rec%[Γ, A](t : Tm% Γ nat%, u : Tm% Γ (arr% nat% (arr% A A)), v : Tm% Γ A) : Tm% Γ A = Tm => var => lam => app => tt => pair => fst => snd => left => right => scase => zero => suc => rec => rec _ _ (t Tm var lam app tt pair fst snd left right scase zero suc rec) (u Tm var lam app tt pair fst snd left right scase zero suc rec) (v Tm var lam app tt pair fst snd left right scase zero suc rec)
def v0%[Γ, A] : Tm% (snoc% Γ A) A = var% vz%
def v1%[Γ, A, B] : Tm% (snoc% (snoc% Γ A) B) A = var% (vs% vz%)
def v2%[Γ, A, B, C] : Tm% (snoc% (snoc% (snoc% Γ A) B) C) A = var% (vs% (vs% vz%))
def v3%[Γ, A, B, C, D] : Tm% (snoc% (snoc% (snoc% (snoc% Γ A) B) C) D) A = var% (vs% (vs% (vs% vz%)))
def tbool% : Ty% = sum% top% top%
def true%[Γ] : Tm% Γ tbool% = left% tt%
def tfalse%[Γ] : Tm% Γ tbool% = right% tt%
def ifthenelse%[Γ, A] : Tm% Γ (arr% tbool% (arr% A (arr% A A))) = lam% (lam% (lam% (scase% v2% (lam% v2%) (lam% v1%))))
def times4%[Γ, A] : Tm% Γ (arr% (arr% A A) (arr% A A)) = lam% (lam% (app% v1% (app% v1% (app% v1% (app% v1% v0%)))))
def add%[Γ] : Tm% Γ (arr% nat% (arr% nat% nat%)) = lam% (rec% v0% (lam% (lam% (lam% (suc% (app% v1% v0%))))) (lam% v0%))
def mul%[Γ] : Tm% Γ (arr% nat% (arr% nat% nat%)) = lam% (rec% v0% (lam% (lam% (lam% (app% (app% add% (app% v1% v0%)) v0%)))) (lam% zero%))
def fact%[Γ] : Tm% Γ (arr% nat% nat%) = lam% (rec% v0% (lam% (lam% (app% (app% mul% (suc% v1%)) v0%))) (suc% zero%))
"#;
