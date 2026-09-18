use std::rc::Rc;

use crate::parser_lib::Span;

use super::{
    Env, Error, Infer, Subst, Tm, Val,
    cxt::Cxt,
    empty_span, rc_take,
    parser::syntax::{Pattern, Raw, Icit},
    unification::SpecSolve,
    PatternDetail,
};

type Constructor = Span<String>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
}

pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Tm)>,
    ret_type: Val,
}

impl Compiler {
    pub fn new(ret_type: Val) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
        }
    }

    /// 构造子可达性探测（值级，L07 `probe_accessible` 口径）：L09 的全局表按
    /// **层级**存（`Infer.global`，无名字键的 decl 表），构造子类型走
    /// `cxt.src_names` 的 名字 → (层级, 类型值) 表——与 `infer_expr(Var(名))`
    /// 的 Var 臂同一次查找，不再走整条推断。Π 链上枚举隐式参数用头部 Sum 的
    /// 实参实例化，其余绑定器用超出上下文的 scratch 层 fresh rigid（同为刚性，
    /// 可被方程解出；探测状态全在本地，弃掉即回滚），返回类型再与头部类型跑
    /// 一次索引方程。成功 = 该构造子可能出现在头部类型的值里；结构冲突
    /// （`Vec[A] zero` 上不可能有 `cons`）= absurd。
    fn probe_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        head_sum: &Val,
        ctor: &String, // BiMap::get 的键口径（`&str` 借查不支持，避免每次探测多一次分配）
    ) -> bool {
        let (sum_name, head_params, impl_vals) = match infer.force(head_sum.clone()) {
            Val::Sum(name, params, _) => (
                name,
                params.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
                params
                    .iter()
                    .filter(|p| p.3 == Icit::Impl)
                    .map(|p| p.1.as_ref().clone())
                    .collect::<Vec<_>>(),
            ),
            _ => return false,
        };
        let entry = match cxt.src_names.get(ctor) {
            Some((_, ty)) => ty.clone(),
            None => return false,
        };
        // 每个探测独立充值：多构造子枚举的逐 ctor 探测不互相挤占共享池
        // （探测本身回滚，只有燃料单向消耗）。孪生版同点充值。
        infer.meta_refuel();
        let snap = infer.meta.clone();
        let mut ty = entry;
        let mut impl_idx = 0;
        let mut scratch = 0u32;
        let ok = loop {
            let tyf = infer.force(ty.clone());
            match tyf {
                Val::Pi(_, _, _, closure) => {
                    let u = if impl_idx < impl_vals.len() {
                        let v = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        v
                    } else {
                        let l = cxt.lvl + scratch;
                        scratch += 1;
                        Val::vvar(l)
                    };
                    ty = infer.closure_apply(&closure, u);
                }                _ => break Self::unify_indices(infer, cxt, &sum_name, &head_params, &tyf),
            }
        };
        // 纯探测：探测期解掉的 meta（含探测前已有的）整表回滚——探测期解掉的
        // 已有 meta 可能引用循环内新建 meta，必须整表 clone、不能 truncate。
        infer.meta = snap;
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ，弃掉即回滚。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        sum_name: &Span<String>,
        head_params: &[Rc<Val>],
        ret_ty: &Val,
    ) -> bool {
        let ret_sum = infer.force(ret_ty.clone());
        let rp = match ret_sum {
            Val::Sum(name, params, _) if name.data == sum_name.data => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let mut spec = SpecSolve {
            solvable: &cxt.bind_slots(),
            acc: Rc::new(Subst::default()),
        };
        let span = empty_span(());
        head_params
            .iter()
            .zip(rp.iter())
            .all(|(a, b)| {
                infer
                    .unify_pm(cxt, a.as_ref().clone(), b.1.as_ref().clone(), span, &mut spec)
                    .is_ok()
            })
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；L10-L12 同款）。
    /// 语义相对决策树的三处收窄（覆盖只做顶层 / 遮蔽只认通配臂 / 特化失败
    /// 静默跳过）见 L11 README 与 docs/l09l13-match-compiler-analysis。
    pub fn compile(
        &mut self,
        infer: &mut Infer,
        typ: Val,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt,
        target_val: Val,
    ) -> Result<Vec<Warning>, Error> {
        self.warnings = Vec::new();
        let typ = infer.force(typ);
        let (constrs, ctor_names): (Vec<Constructor>, Vec<String>) = match typ.clone() {
            Val::Sum(_, _, cases) => (
                cases.clone(),
                cases.iter().map(|c| c.data.clone()).collect(),
            ),
            _ => (vec![], vec![]),
        };
        // 覆盖检查：可达且无臂覆盖 → Unmatched（fill_context(Outermost, ·)
        // 的形态就是「构造子 + 999 通配」）。不可达（如 `Vec[A] zero` 上的
        // `cons`）不报——索引方程不可解即结构上不可能出现。
        for ctor in &constrs {
            if Self::probe_accessible(infer, cxt, &typ, &ctor.data)
                && !arms
                    .iter()
                    .any(|(pat, _)| covers(pat, ctor.data.as_str(), &ctor_names))
            {
                self.warnings.push(Warning::Unmatched(Pattern::Con(
                    ctor.clone(),
                    vec![Pattern::Any(empty_span(()), Icit::Expl); 999],
                    Icit::Expl,
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
            // 臂上下文置于精化 σ 之下（dpm-nbe `subst sub ctx`）：env 槽与
            // src_names 类型包 VSub，lvl/locals/pruning 不动——槽位布局
            // （= 运行时布局）永不漂移，读点 force 推开。
            let cxt_arm = cxt_walk.subst_cxt(&sigma);
            // 期望类型重锚到臂上下文：quote → eval（flex 免锚）。σ 经臂上下文
            // 的 wrapped env 在 eval 读点生效，无需预先包裹。
            let ret_type = match self.ret_type.clone() {
                t @ Val::Flex(_, _) => t,
                ret_type => {
                    let ret_type = infer.quote(cxt_arm.lvl, ret_type);
                    infer.eval(&cxt_arm.env, ret_type)
                }
            };
            let ret = infer.check(&cxt_arm, body.clone(), ret_type)?;
            self.pats.push((detail, ret));
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        Ok(unreachable.into_iter().chain(self.warnings.clone()).collect())
    }

    pub fn eval_aux(
        infer: &Infer,
        heads: &Val,
        cxt: &Env,
        arms: &[(PatternDetail, Tm)],
    ) -> Option<(Tm, Env)> {
        let (case_name, params, constrs_name) = match infer.force(heads.clone()) {
            Val::SumCase {
                typ,
                case_name,
                datas: params,
            } => (case_name, params, match infer.force((*typ).clone()) {
                Val::Sum(_, _, cases) => cases.clone(),
                _ => panic!("by now only can match a sum type, but get {:?}", heads),
            }),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (empty_span("$unknown$".to_owned()), vec![], vec![])
        };

        arms.iter()
            .filter_map(|(pattern, body)| match pattern {
                PatternDetail::Any(_) => Some((body.clone(), cxt.prepend(heads.clone()))),
                PatternDetail::Bind(_) => {
                    Some((body.clone(), cxt.prepend(heads.clone())))
                }
                PatternDetail::Con(constr_, item_pats) if !constrs_name.contains(&constr_) => {
                    /*if cxt.src_names.contains_key(&constr_.data) {
                        //return Err(Error(format!("match fail: {:?}", constr_)))
                        todo!()
                    } else */
                    {
                        //TODO: item_pats should be zero
                        Some((body.clone(), cxt.prepend(heads.clone())))
                    }
                }
                PatternDetail::Con(constr_, item_pats) if constr_ == &case_name => {
                    params.iter()
                        //.filter(|x| x.2 == Icit::Expl)
                        .map(|x| x.1.as_ref())
                        .zip(item_pats.iter())
                        .try_fold(
                            (body.clone(), cxt.clone()),
                            |(body, cxt), (param, pat): (&Val, &PatternDetail)| {
                                Self::eval_aux(infer, param, &cxt, &[(pat.clone(), body)])
                            },
                        )
                }
                _ => None,
            })
            .next()
    }
}

/// 臂是否（结构上）覆盖构造子 `ctor`（L07 `covers` 同款）。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor
        }
    }
}

/// 通配臂（L07 `is_catch_all` 同款）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data)
        }
    }
}

/// 模式走查（L07 `walk_con` 口径；L10 `walk_pat` 的 L09 版）：绑定模式变量槽
/// 并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽、构造子隐式
/// 绑定器补虚通配、变量模式以用户名绑槽、**Con 本身不占槽**。
/// L09 的全局表按**层级**存（`Infer.global`，无名字键的 decl 表），构造子
/// 类型经 `infer_expr(Var(名))` 取（树的头部展开同款）。
fn walk_pat(infer: &mut Infer, cxt: &Cxt, pat: &Pattern, head_ty: &Val) -> Result<(PatternDetail, Cxt), Error> {
    match pat {
        Pattern::Any(span, _) => {
            let a_t = infer.quote(cxt.lvl, head_ty.clone());
            let cxt2 = cxt.bind(empty_span("_".to_owned()), a_t, head_ty.clone());
            Ok((PatternDetail::Any(span.clone()), cxt2))
        }
        Pattern::Con(name, subs, _) => {
            let head_sum = infer.force(head_ty.clone());
            let (sum_params, cases) = match head_sum {
                Val::Sum(_, params, cases) => (params, cases),
                _ => {
                    if !subs.is_empty() {
                        return Err(Error(name.clone().map(|n| format!(
                            "`{n}` 不是构造子，不能带子模式解构"
                        ))));
                    }
                    let a_t = infer.quote(cxt.lvl, head_ty.clone());
                    let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                    return Ok((PatternDetail::Bind(name.clone()), cxt2));
                }
            };
            if !cases.iter().any(|c| c.data == name.data) {
                if !subs.is_empty() {
                    return Err(Error(name.clone().map(|n| format!(
                        "`{n}` 不是该类型的构造子，不能带子模式解构"
                    ))));
                }
                let a_t = infer.quote(cxt.lvl, head_ty.clone());
                let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                return Ok((PatternDetail::Bind(name.clone()), cxt2));
            }
            // 构造子类型：名字 → 层级 → Infer.global（树同款 infer_expr）
            let (_, ty0) = infer.infer_expr(cxt, Raw::Var(name.clone()))?;
            let mut impl_vals: Vec<Rc<Val>> = sum_params
                .iter()
                .filter(|p| p.3 == Icit::Impl)
                .map(|p| p.1.clone())
                .collect();
            impl_vals.reverse();
            let mut ty = ty0;
            let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
            let mut details: Vec<PatternDetail> = Vec::new();
            let mut cxt_arm = cxt.clone();
            loop {
                let tyf = infer.force(ty.clone());
                match tyf {
                    Val::Pi(bname, bicit, dom, closure) => {
                        if let Some(v) = impl_vals.pop() {
                            ty = infer.closure_apply(&closure, rc_take(v));
                            continue;
                        }
                        let sub: Option<&Pattern> = match bicit {
                            Icit::Impl => sub_queue
                                .first()
                                .filter(|p| p.get_icit() == Icit::Impl)
                                .copied(),
                            Icit::Expl => match sub_queue.first() {
                                Some(p) if p.get_icit() == Icit::Expl => Some(*p),
                                _ => None,
                            },
                        };
                        let u = Val::vvar(cxt_arm.lvl);
                        let detail = match sub {
                            None => {
                                let b = empty_span(format!("_{}", bname.data));
                                let d_t = infer.quote(cxt_arm.lvl, (*dom).clone());
                                cxt_arm = cxt_arm.bind(b, d_t, (*dom).clone());
                                PatternDetail::Any(empty_span(()))
                            }
                            Some(Pattern::Any(span, _)) => {
                                sub_queue.remove(0);
                                let b = empty_span(format!("_{}", bname.data));
                                let d_t = infer.quote(cxt_arm.lvl, (*dom).clone());
                                cxt_arm = cxt_arm.bind(b, d_t, (*dom).clone());
                                PatternDetail::Any(span.clone())
                            }
                            Some(p @ Pattern::Con(..)) => {
                                sub_queue.remove(0);
                                let (d, c2) = walk_pat(infer, &cxt_arm, p, &dom)?;
                                cxt_arm = c2;
                                d
                            }
                        };
                        details.push(detail);
                        ty = infer.closure_apply(&closure, u);
                    }
                    _ => break,
                }
            }
            Ok((PatternDetail::Con(name.clone(), details), cxt_arm))
        }
    }
}
