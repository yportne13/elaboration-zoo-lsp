//! 方案 3：**形状认回 decl**（无注解 def 的显示保真，L13 版 / L07-L08 的平移）。
//!
//! 问题：`def h(n : Nat) = g n`（无类型注解）的 hover 只能走值渲染；它的类型在值层是
//! `Val::Match`（`T n` 被 force 成 `match n { … }`），于是显示 `(n: Nat) → (match n { … })`。
//!
//! 方案：登记每个 def 的**match 形状**，渲染时若展开出的 match 与某个已登记形状逐项一致，
//! 就打回该 def 的名字 + 实参。两种来源，**值来源优先**：
//!
//! - `FromValue`：def 的**注册值**剥 λ 后是 match（它是该 match 的定义者，认回最忠实）；
//! - `FromType`：def 的**返回类型**剥 Π 后是 match（认回 `g n` 也可读，但不如前者原始）。
//!
//! 优先级：**类型级 FromValue > 值级 FromValue > 类型级 FromType > 值级 FromType**。
//! 这条是必要的：`def T(n): Type 0 = match n {…}` 与 `def g(n): T n = match n {…}` 的形状
//! 完全相同，按登记顺序认就会打 `g n`（错）。`type_level` 判别（返回类型剥 Π 后是 `U`）
//! 用来把它们分开。
//!
//! 这是**显示层启发式**：只改 hover/inlay 的文案，不进任何语义/性能路径。

use super::{Closure, Decl, Env, Infer, Lvl, PatternDetail, Val};

/// 形状来源（决定认回优先级）。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShapeSource {
    /// def 的值本身是 match（该 match 的定义者）。
    FromValue,
    /// def 的返回类型是 match（match 的来源是别的 def）。
    FromType,
}

/// 一条 match 形状签名。
#[derive(Clone, Debug, PartialEq)]
pub struct MatchShape {
    /// 每臂的模式骨架（`PartialEq` 忽略 span）。
    pub pats: Vec<PatternDetail>,
    /// 捕获 env 的槽数（排除跨上下文误认）。
    pub env_len: usize,
    pub source: ShapeSource,
    /// 该 def 是否为**类型级**（声明返回类型剥 Π 后是 `U`）。
    pub type_level: bool,
}

impl MatchShape {
    pub(crate) fn from_val(v: &Val, source: ShapeSource, type_level: bool) -> Option<Self> {
        let Val::Match(_, env, cases) = v else {
            return None;
        };
        Some(MatchShape {
            pats: cases.iter().map(|(p, _)| p.clone()).collect(),
            env_len: env.len(),
            source,
            type_level,
        })
    }
}

/// 模式骨架的结构比较：**忽略 binder 名与 span**，只比构造子名与嵌套形状。
///
/// `PatternDetail::Any` 携带 binder 名（L13 里每个实例会拿 fresh 名，如 `_l0`/`_l1`），
/// 直接 `PartialEq` 会让同一类型函数在不同使用点认不回来（实测 `h` 认成 `h n` 而非 `T n`）。
fn pats_eq(a: &PatternDetail, b: &PatternDetail) -> bool {
    match (a, b) {
        (PatternDetail::Any(..), PatternDetail::Any(..)) => true,
        (PatternDetail::Bind(_), PatternDetail::Bind(_)) => true,
        (
            PatternDetail::Con(_, n1, s1, _),
            PatternDetail::Con(_, n2, s2, _),
        ) => n1.data == n2.data && s1.len() == s2.len() && s1.iter().zip(s2).all(|(x, y)| pats_eq(x, y)),
        _ => false,
    }
}
/// 逐层剥 Π / λ，返回余下的非函数形态。
fn peel(infer: &Infer, decl: &Decl, v: &std::rc::Rc<Val>, lam_mode: bool) -> std::rc::Rc<Val> {
    let mut t = infer.force(decl, v);
    let mut l = Lvl(0);
    loop {
        match t.as_ref() {
            Val::Pi(_, _, _, cod) if !lam_mode => {
                let c: &Closure = cod;
                t = infer.force(decl, &infer.closure_apply(decl, c, Val::vvar(l).into()));
                l = l + 1;
            }
            Val::Lam(_, _, cl) if lam_mode => {
                t = infer.force(decl, &infer.closure_apply(decl, cl, Val::vvar(l).into()));
                l = l + 1;
            }
            // L13 特有：eval 把内联的 def 体包成 `Val::Call(name, args, body)`（名字保留，
            // 供显示）。剥到 `body` 才能看到真正的 `Val::Match` 骨架——否则 `def T(n): … =
            // match n { … }` 的值永远不是 Match，值来源的形状登记全落空（实测只剩 FromType
            // 的 `h` 一个）。
            Val::Call(_, _, body) => {
                t = infer.force(decl, body);
            }
            _ => return t,
        }
    }
}

/// 登记形状：先看**值**（剥 λ），再看**类型**（剥 Π）。
pub(crate) fn shapes_for(
    infer: &Infer,
    decl: &Decl,
    vtyp: &std::rc::Rc<Val>,
    vt: &std::rc::Rc<Val>,
) -> Vec<MatchShape> {
    let mut out = Vec::new();
    // 该 def 是否类型级：声明返回类型剥 Π 后是 U。
    let type_level = matches!(peel(infer, decl, vtyp, false).as_ref(), Val::U(_));
    let val_peeled = peel(infer, decl, vt, true);
    if let Some(s) = MatchShape::from_val(val_peeled.as_ref(), ShapeSource::FromValue, type_level) {
        out.push(s);
    }
    let typ_peeled = peel(infer, decl, vtyp, false);
    if let Some(s) = MatchShape::from_val(typ_peeled.as_ref(), ShapeSource::FromType, type_level) {
        // 值来源已登记同一形状时不重复（值来源更优先）。
        if !out.iter().any(|x| x.pats == s.pats && x.env_len == s.env_len) {
            out.push(s);
        }
    }
    out
}

/// 展开出的值属于哪个已登记的 def。
pub(crate) fn match_to_decl(infer: &Infer, v: &Val) -> Option<String> {
    let shape = MatchShape::from_val(v, ShapeSource::FromValue, false)?;
    let map = infer.decl_shapes.borrow();
    for (want_src, want_ty) in [
        (ShapeSource::FromValue, true),
        (ShapeSource::FromValue, false),
        (ShapeSource::FromType, true),
        (ShapeSource::FromType, false),
    ] {
        for (name, shapes) in map.iter() {
            for s in shapes.iter() {
                // 只比模式骨架：`env` 是每个实例各自的捕获环境，长度随实例变化，
                // 用它做判据会让同一类型函数在不同使用点认不回来（实测 h → `h n`）。
                if s.source == want_src
                    && s.type_level == want_ty
                    && s.pats.len() == shape.pats.len()
                    && s.pats.iter().zip(&shape.pats).all(|(x, y)| pats_eq(x, y))
                {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}