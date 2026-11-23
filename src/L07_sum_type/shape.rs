//! 方案 3：**形状认回 decl**（无注解 def 的显示保真）。
//!
//! 问题：`def h(n : Nat) = g n`（无类型注解）的 hover 只能走值渲染；它的类型在值层是
//! `Val::Match`（`T n` 被 force 成 `match n { … }`），于是显示 `(n: Nat) → (match n { … })`。
//!
//! 方案：登记每个 def 的**match 形状**，渲染时若展开出的 match 与某个已登记形状逐项一致，
//! 就打回该 def 的名字 + 实参。两种来源，**值来源优先**：
//!
//! - `FromValue`：def 的**注册值**剥 λ 后是 match（如 `def T(n : Nat): U = match n { … }`）
//!   ——它是该 match 的定义者，认回 `T n` 最忠实；
//! - `FromType`：def 的**返回类型**剥 Π 后是 match（如 `def g(n : Nat): T n = …`）
//!   ——认回 `g n` 也可读，但不如前者原始。
//!
//! 这是**显示层启发式**：只改 hover/inlay 的文案，不进任何语义/性能路径。

use super::{Infer, PatternDetail, Val};

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
    /// 该 def 是否为**类型级**（其声明返回类型剥 Π 后是 `U`）。
    /// 用于区分"同形状"的两个 def：`def T(n): U = match n { … }`（类型级）与
    /// `def g(n): T n = match n { … }`（值级，形状恰好相同）——渲染**类型**时优先认类型级的。
    pub type_level: bool,
}

impl MatchShape {
    pub(crate) fn from_val(v: &Val, source: ShapeSource, type_level: bool) -> Option<Self> {
        let Val::Match(_, env, cases, _) = v else {
            return None;
        };
        Some(MatchShape {
            pats: cases.iter().map(|(p, _)| p.clone()).collect(),
            env_len: env.iter().count(),
            source,
            type_level,
        })
    }
}

/// 逐层剥 Π / λ，返回余下的非函数形态。
fn peel(infer: &Infer, decl: &super::cxt::Decls, v: Val, lam_mode: bool) -> Val {
    let mut t = infer.force(decl, v);
    let mut l = super::Lvl(0);
    loop {
        match t {
            Val::Pi(_, _, _, cod) if !lam_mode => {
                t = infer.force(decl, infer.closure_apply(decl, &cod, Val::vvar(l)));
                l = l + 1;
            }
            Val::Lam(_, _, cl) if lam_mode => {
                t = infer.force(decl, infer.closure_apply(decl, &cl, Val::vvar(l)));
                l = l + 1;
            }
            other => return other,
        }
    }
}

/// 登记形状：先看**值**（剥 λ），再看**类型**（剥 Π）。
pub(crate) fn shapes_for(infer: &Infer, decl: &super::cxt::Decls, vtyp: Val, vt: Val) -> Vec<MatchShape> {
    let mut out = Vec::new();
    // 该 def 是否类型级：声明返回类型剥 Π 后是 U。
    let type_level = matches!(peel(infer, decl, vtyp.clone(), false), Val::U);
    let val_peeled = peel(infer, decl, vt, true);
    if let Some(s) = MatchShape::from_val(&val_peeled, ShapeSource::FromValue, type_level) {
        out.push(s);
    }
    let typ_peeled = peel(infer, decl, vtyp, false);
    if let Some(s) = MatchShape::from_val(&typ_peeled, ShapeSource::FromType, type_level) {
        // 值来源已登记同一形状时不重复（值来源更优先）。
        if !out.iter().any(|x| x.pats == s.pats && x.env_len == s.env_len) {
            out.push(s);
        }
    }
    out
}

/// 展开出的值属于哪个已登记的 def；`FromValue` 优先，其次 `FromType`。
pub(crate) fn match_to_decl(infer: &Infer, v: &Val) -> Option<String> {
    let shape = MatchShape::from_val(v, ShapeSource::FromValue, false)?;
    let map = infer.decl_shapes.borrow();
    // 优先级：类型级 def 的值 > 值级 def 的值 > 类型来源。
    // 例：`def T(n): U = match n {…}` 与 `def g(n): T n = match n {…}` 形状相同，
    // 类型位置应认 `T`（它是这个 match 的定义者、且是类型级）。
    for (want_src, want_ty) in [
        (ShapeSource::FromValue, true),
        (ShapeSource::FromValue, false),
        (ShapeSource::FromType, true),
        (ShapeSource::FromType, false),
    ] {
        for (name, shapes) in map.iter() {
            for s in shapes.iter() {
                if s.source == want_src
                    && s.type_level == want_ty
                    && s.pats == shape.pats
                    && s.env_len == shape.env_len
                {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}

