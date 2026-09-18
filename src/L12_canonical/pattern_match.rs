use std::{
    collections::{BTreeSet, HashMap, HashSet},
};

use smol_str::SmolStr;

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Tm, Val,
    cxt::Cxt, Rc, Decl, Subst,
    elaboration::SpecSolve,
    empty_span, Either,
    parser::syntax::{Pattern, Raw, Icit},
    PatternDetail,
};

type Var = i32;

type Constructor = Span<SmolStr>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
}

pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Rc<Tm>)>,
    ret_type: Rc<Val>,
}

impl Compiler {
    pub fn new(ret_type: Rc<Val>) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
        }
    }

    /// 构造子可达性探测（值级，L07 `probe_accessible` 口径）：直接读 decl 表
    /// 拿构造子类型，走 Π 链实例化——枚举隐式参数用头部 Sum 的实参，其余绑定
    /// 器用超出上下文的 scratch 层 fresh rigid（同为刚性，可被方程解出；探测
    /// 状态全在本地，弃掉即回滚），返回类型再与头部类型跑一次索引方程。
    /// 成功 = 该构造子可能出现在头部类型的值里；结构冲突（`Vec[A] zero` 上
    /// 不可能有 `cons`）= absurd。
    fn probe_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        head_sum: &Rc<Val>,
        ctor: &str,
    ) -> bool {
        let (sum_name, head_params, impl_vals) = match head_sum.as_ref() {
            Val::Sum(name, params, ..) => (
                name.clone(),
                params.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
                params
                    .iter()
                    .filter(|p| p.3 == Icit::Impl)
                    .map(|p| p.1.clone())
                    .collect::<Vec<_>>(),
            ),
            _ => return false,
        };
        let entry = match cxt.decl.get(ctor) {
            Some(e) => e.4.clone(),
            None => return false,
        };
        // 每个探测独立充值：多构造子枚举的逐 ctor 探测不互相挤占共享池
        // （探测本身回滚，只有燃料单向消耗）。孪生版同点充值。
        infer.refuel();
        let snap = infer.meta.clone();
        let mut ty = entry;
        let mut impl_idx = 0;
        let mut scratch = 0u32;
        let ok = loop {
            let tyf = infer.force(&cxt.decl, &ty);
            match tyf.as_ref() {
                Val::Pi(_, _, _, closure) => {
                    let u = if impl_idx < impl_vals.len() {
                        let v = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        v
                    } else {
                        let l = cxt.lvl + scratch;
                        scratch += 1;
                        Val::vvar(l).into()
                    };
                    ty = infer.closure_apply(&cxt.decl, closure, u);
                }
                _ => break Self::unify_indices(infer, cxt, &sum_name, &head_params, &tyf),
            }
        };
        infer.meta = snap;
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ，弃掉即回滚。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        sum_name: &Span<SmolStr>,
        head_params: &[Rc<Val>],
        ret_ty: &Rc<Val>,
    ) -> bool {
        let ret_sum = infer.force(&cxt.decl, ret_ty);
        let rp = match ret_sum.as_ref() {
            Val::Sum(name, params, ..) if name.data == sum_name.data => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let mut spec = SpecSolve {
            acc: Rc::new(Subst::default()),
        };
        let span = empty_span(());
        head_params
            .iter()
            .zip(rp.iter())
            .all(|(a, b)| infer.unify_pm(cxt, a, &b.1, span, &mut spec).is_ok())
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；L11 同款）。
    /// 语义相对决策树的三处收窄（覆盖只做顶层 / 遮蔽只认通配臂 / 特化失败
    /// 静默跳过）见 L11 README 与 docs/l09l13-match-compiler-analysis。
    pub fn compile(
        &mut self,
        infer: &mut Infer,
        typ: Rc<Val>,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt,
        target_val: Rc<Val>,
    ) -> Result<Vec<Warning>, Error> {
        self.warnings = Vec::new();
        let typ = infer.force(&cxt.decl, &typ);
        let (constrs, ctor_names): (Vec<Constructor>, Vec<SmolStr>) = match typ.as_ref() {
            Val::Sum(_, _, cases, _) => (
                cases.clone(),
                cases.iter().map(|c| c.data.clone()).collect(),
            ),
            _ => (vec![], vec![]),
        };
        // 覆盖检查：可达且无臂覆盖 → Unmatched（fill_context(Outermost, ·)
        // 的形态就是「构造子 + 999 通配」）。不可达（如 `Vec[A] zero` 上的
        // `cons`）不报——索引方程不可解即结构上不可能出现。
        for ctor in &constrs {
            if Self::probe_accessible(infer, cxt, &typ, ctor.data.as_str())
                && !arms
                    .iter()
                    .any(|(pat, _)| covers(pat, ctor.data.as_str(), &ctor_names))
            {
                self.warnings.push(Warning::Unmatched(Pattern::Con(
                    ctor.clone(),
                    vec![Pattern::Any(empty_span(false), Either::Icit(Icit::Expl)); 999],
                    Either::Icit(Icit::Expl),
                )));
            }
        }
        let mut unreachable: Vec<Warning> = Vec::new();
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                unreachable.push(Warning::Unreachable(body.clone()));
                continue;
            }
            let (detail, cxt_walk) = match walk_pat(infer, cxt, pat, &typ) {
                Ok(x) => x,
                Err(_) => continue,
            };
            let raw = pat.to_raw();
            let Ok((_, sigma)) =
                infer.check_pm_final(&cxt_walk, raw, typ.clone(), target_val.clone())
            else {
                continue;
            };
            let cxt_arm = cxt_walk.subst_cxt(&sigma);
            let ret_type = match self.ret_type.as_ref() {
                Val::Flex(..) => self.ret_type.clone(),
                _ => {
                    let q = infer.quote(&cxt_arm.decl, cxt_arm.lvl, &self.ret_type);
                    infer.eval(&cxt_arm.decl, &cxt_arm.env, &q)
                }
            };
            let ret = infer.check::<false>(&cxt_arm, body.clone(), &ret_type)?;
            self.pats.push((detail, ret));
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        Ok(unreachable.into_iter().chain(self.warnings.clone()).collect())
    }
    pub fn eval_aux(
        infer: &Infer,
        heads: &Rc<Val>,
        decl: &Decl,
        cxt: &Env,
        arms: &[(PatternDetail, Rc<Tm>)],
    ) -> Option<(Rc<Tm>, Env)> {
        let head = infer.force(decl, heads);
        let (case_name, params) = match head.as_ref() {
            Val::SumCase {
                is_trait: _,
                typ: _,
                case_name,
                datas: params,
            } => (case_name, params),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (&empty_span(SmolStr::new("$unknown$")), &vec![])
        };

        arms.iter()
            .filter_map(|(pattern, body)| match pattern {
                PatternDetail::Any(_) => Some((body.clone(), cxt.prepend(heads.clone()))),
                PatternDetail::Bind(_) => {
                    Some((body.clone(), cxt.prepend(heads.clone())))
                }
                PatternDetail::Con(constr_, item_pats) if constr_ == case_name => {
                    params.iter()
                        //.filter(|x| x.2 == Icit::Expl)
                        .map(|x| &x.1)
                        .zip(item_pats.iter())
                        .try_fold(
                            (body.clone(), cxt.clone()),
                            |(body, cxt), (param, pat): (&Rc<Val>, &PatternDetail)| {
                                Self::eval_aux(infer, param, decl, &cxt, &[(pat.clone(), body)])
                            },
                        )
                }
                _ => None,
            })
            .next()
    }
}

/// 臂是否（结构上）覆盖构造子 `ctor`（L07 `covers` 同款）。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[SmolStr]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c.as_str() == name.data.as_str())
                || name.data.as_str() == ctor
        }
    }
}

/// 通配臂（L07 `is_catch_all` 同款）。
fn is_catch_all(pat: &Pattern, ctor_names: &[SmolStr]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c.as_str() == name.data.as_str())
        }
    }
}

/// 模式走查（L07 `walk_con` 口径；L11 `walk_pat` 的 L12 版）：绑定模式变量槽
/// 并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽、构造子隐式
/// 绑定器补虚通配、变量模式以用户名绑槽、**Con 本身不占槽**。
fn walk_pat(infer: &mut Infer, cxt: &Cxt, pat: &Pattern, head_ty: &Rc<Val>) -> Result<(PatternDetail, Cxt), Error> {
    match pat {
        Pattern::Any(span, _) => {
            let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
            let cxt2 = cxt.bind(empty_span(SmolStr::new("_")), a_t, head_ty.clone());
            Ok((PatternDetail::Any(span.to_span()), cxt2))
        }
        Pattern::Con(name, subs, _) => {
            let head_sum = infer.force(&cxt.decl, head_ty);
            let (sum_params, cases) = match head_sum.as_ref() {
                Val::Sum(_, params, cases, _) => (params.clone(), cases.clone()),
                _ => {
                    if !subs.is_empty() {
                        return Err(Error(
                            name.clone().map(|n| format!("`{n}` 不是构造子，不能带子模式解构")),
                            vec![],
                        ));
                    }
                    let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
                    let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                    return Ok((PatternDetail::Bind(name.clone()), cxt2));
                }
            };
            if !cases.iter().any(|c| c.data == name.data) {
                if !subs.is_empty() {
                    return Err(Error(
                        name.clone().map(|n| format!("`{n}` 不是该类型的构造子，不能带子模式解构")),
                        vec![],
                    ));
                }
                let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
                let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                return Ok((PatternDetail::Bind(name.clone()), cxt2));
            }
            // L12 的构造子以**裸名**登记（elaboration.rs 里 cxt.decl(c.0, ..)）
            let entry_ty = match cxt.decl.get(name.data.as_str()) {
                Some(e) => e.4.clone(),
                None => {
                    return Err(Error(
                        name.clone().map(|n| format!("找不到构造子 {}", n)),
                        vec![],
                    ))
                }
            };
            let mut impl_vals: Vec<Rc<Val>> = sum_params
                .iter()
                .filter(|p| p.3 == Icit::Impl)
                .map(|p| p.1.clone())
                .collect();
            impl_vals.reverse();
            let mut ty = entry_ty;
            let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
            let mut details: Vec<PatternDetail> = Vec::new();
            let mut cxt_arm = cxt.clone();
            loop {
                let tyf = infer.force(&cxt.decl, &ty);
                match tyf.as_ref() {
                    Val::Pi(bname, bicit, dom, closure) => {
                        let (bicit, dom, closure) = (*bicit, dom.clone(), closure.clone());
                        if let Some(v) = impl_vals.pop() {
                            ty = infer.closure_apply(&cxt.decl, &closure, v);
                            continue;
                        }
                        let sub: Option<&Pattern> = match bicit {
                            Icit::Impl => sub_queue
                                .first()
                                .filter(|p| p.get_icit().to_icit() == Icit::Impl)
                                .copied(),
                            Icit::Expl => match sub_queue.first() {
                                Some(p) if p.get_icit().to_icit() == Icit::Expl => Some(*p),
                                _ => None,
                            },
                        };
                        let u = Rc::new(Val::vvar(cxt_arm.lvl));
                        let detail = match sub {
                            None => {
                                let b = empty_span(SmolStr::new(format!("_{}", bname.data)));
                                let d_t = infer.quote(&cxt.decl, cxt_arm.lvl, &dom);
                                cxt_arm = cxt_arm.bind(b, d_t, dom.clone());
                                PatternDetail::Any(empty_span(()))
                            }
                            Some(Pattern::Any(span, _)) => {
                                sub_queue.remove(0);
                                let b = empty_span(SmolStr::new(format!("_{}", bname.data)));
                                let d_t = infer.quote(&cxt.decl, cxt_arm.lvl, &dom);
                                cxt_arm = cxt_arm.bind(b, d_t, dom.clone());
                                PatternDetail::Any(span.to_span())
                            }
                            Some(p @ Pattern::Con(..)) => {
                                sub_queue.remove(0);
                                let (d, c2) = walk_pat(infer, &cxt_arm, p, &dom)?;
                                cxt_arm = c2;
                                d
                            }
                        };
                        details.push(detail);
                        ty = infer.closure_apply(&cxt_arm.decl, &closure, u);
                    }
                    _ => break,
                }
            }
            Ok((PatternDetail::Con(name.clone(), details), cxt_arm))
        }
    }
}
