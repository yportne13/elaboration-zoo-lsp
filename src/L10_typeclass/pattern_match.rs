use std::{
    collections::{BTreeSet, HashMap, HashSet},
    rc::Rc,
};

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Tm, Val,
    cxt::Cxt,
    empty_span,
    parser::syntax::{Pattern, Raw, Icit},
    PatternDetail,
};

type Var = i32;

type Constructor = Span<String>;

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

    fn filter_accessible_constrs<'a>(
        &mut self,
        infer: &mut Infer,
        cxt: &Cxt,
        typ: &Rc<Val>, // The specific type of the matched term, e.g., Val for `Vec (Succ n)`
        all_constrs: &'a [Constructor],
    ) -> Result<
        Vec<(&'a Constructor, Vec<(Span<String>, Rc<Val>, Icit)>, Cxt)>,
        Error,
    > {
        let mut accessible = Vec::new();

        let typ = infer.force(typ);
        let forced_type = match typ.as_ref() {
            Val::Sum(..) => typ,
            _ => {
                for constr_def in all_constrs {
                    accessible.push((constr_def, vec![], cxt.clone()));
                }
                return Ok(accessible)
            }
        };

        // This is a pure probe: the per-constructor infer_expr/check_pm may
        // solve metas (including pre-existing ones) and allocate throwaway
        // fresh metas. L13 同款窄快照（快版 `run_pure_probe` 同口径）：只把
        // 探测面 `meta` 整表换入换出，循环结束**无条件**回滚（Success/Error
        // 皆然）。必须整表 clone、不能 truncate——探测期解掉的已有 meta 可能
        // 引用循环内新建 meta，截断会让解悬空（后续查找越界 panic）。其余
        // 字段探测期只读：`global`/`trait_definition`/`trait_out_param` 是
        // 注册表（探测只做表达式级 infer/check，无 decl 登记）；`trait_solver`
        // 每次真查询先 `clean()`（`unification.rs::solve_trait`），瞬态残留
        // 不跨查询生效。
        let meta_snapshot = infer.meta.clone();
        let result = (|| -> Result<Vec<_>, Error> {
            for constr_def @ constr_name in all_constrs {
                // We create a temporary, throwaway inference state for the unification check
                // to avoid polluting the main inference state with temporary metavariables.

                // 1. Create fresh metavariables for the constructor's own arguments.
                //    We need their types first, which are given as raw syntax.
                let mut to_check = Raw::Var(constr_name.clone());
                let mut params = vec![];
                let mut cxt = cxt.clone();
                loop {
                    let (_, typ) = infer.infer_expr(&cxt, to_check.clone())?;
                    // 精化 σ 包裹的类型先 force 推开（旧机制下 src_names 已被
                    // refresh 物化，这里必须显式推开才看得到 Π 形态）
                    let typ = infer.force(&typ);
                    match typ.as_ref() {
                        Val::Pi(name, icit, ty, _) => {
                            if *icit == Icit::Expl { // Only explicit args matter for the structure
                                params.push((name.clone(), ty.clone(), *icit));
                            }
                            to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole), super::Either::Icit(*icit));
                            cxt = cxt.bind(name.clone(), infer.quote(cxt.lvl, ty), ty.clone());
                        },
                        _ => {break;}
                    }
                }
                /*for (_, _, icit) in constr_arg_tys_raw {
                    if *icit == Icit::Expl { // Only explicit args matter for the structure
                        to_check = Raw::App(Box::new(to_check), Box::new(Raw::Hole), super::Either::Icit(Icit::Expl));
                    }
                }*/

                // 4. Try to unify it with the type of the matched term.
                // （精化 σ 在探测内被丢弃——探测只问可达性，与旧实现丢弃
                // check_pm 返回的精化 cxt 同口径；meta 整表回滚在闭包外）
                if infer.check_pm(&cxt, to_check.clone(), forced_type.clone()).is_ok() {
                    // If unification succeeds, the constructor is accessible.
                    accessible.push((constr_def, params, cxt.clone()));
                }
            }

            Ok(accessible)
        })();
        infer.meta = meta_snapshot;
        result
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；L11/L12 同款）。
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
        let typ = infer.force(&typ);
        let (constrs, ctor_names): (Vec<Constructor>, Vec<String>) = match typ.as_ref() {
            Val::Sum(_, _, cases, _) => (
                cases.clone(),
                cases.iter().map(|c| c.data.clone()).collect(),
            ),
            _ => (vec![], vec![]),
        };
        if !constrs.is_empty() {
            if let Ok(accessible) = self.filter_accessible_constrs(infer, cxt, &typ, &constrs) {
                for (ctor, ..) in &accessible {
                    if !arms
                        .iter()
                        .any(|(pat, _)| covers(pat, ctor.data.as_str(), &ctor_names))
                    {
                        self.warnings.push(Warning::Unmatched(Pattern::Con(
                            (*ctor).clone(),
                            vec![Pattern::Any(empty_span(true), Icit::Expl); 999],
                            Icit::Expl,
                        )));
                    }
                }
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
                    let q = infer.quote(cxt_arm.lvl, &self.ret_type);
                    infer.eval(&cxt_arm.env, &q)
                }
            };
            let ret = infer.check(&cxt_arm, body.clone(), &ret_type)?;
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
        cxt: &Env,
        arms: &[(PatternDetail, Rc<Tm>)],
    ) -> Option<(Rc<Tm>, Env)> {
        let head = infer.force(heads);
        let (case_name, params) = match head.as_ref() {
            Val::SumCase {
                is_trait: _,
                typ: _,
                case_name,
                datas: params,
            } => (case_name, params),
            //_ => panic!("by now only can match a sum type, but get {:?}", heads),
            _ => (&empty_span("$unknown$".to_owned()), &vec![])
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

/// 模式走查（L07 `walk_con` 口径；L11 `walk_pat` 的 L10 版）：绑定模式变量槽
/// 并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽、构造子隐式
/// 绑定器补虚通配、变量模式以用户名绑槽、**Con 本身不占槽**。
/// L10 的全局表按**层级**存（`Infer.global`，无名字键的 decl 表），构造子
/// 类型经 `infer_expr(Var(名))` 取（树的头部展开同款）。
fn walk_pat(infer: &mut Infer, cxt: &Cxt, pat: &Pattern, head_ty: &Rc<Val>) -> Result<(PatternDetail, Cxt), Error> {
    match pat {
        Pattern::Any(span, _) => {
            let a_t = infer.quote(cxt.lvl, head_ty);
            let cxt2 = cxt.bind(empty_span("_".to_owned()), a_t, head_ty.clone());
            Ok((PatternDetail::Any(span.to_span()), cxt2))
        }
        Pattern::Con(name, subs, _) => {
            let head_sum = infer.force(head_ty);
            let (sum_params, cases) = match head_sum.as_ref() {
                Val::Sum(_, params, cases, _) => (params.clone(), cases.clone()),
                _ => {
                    if !subs.is_empty() {
                        return Err(Error(name.clone().map(|n| format!(
                            "`{n}` 不是构造子，不能带子模式解构"
                        ))));
                    }
                    let a_t = infer.quote(cxt.lvl, head_ty);
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
                let a_t = infer.quote(cxt.lvl, head_ty);
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
                let tyf = infer.force(&ty);
                match tyf.as_ref() {
                    Val::Pi(bname, bicit, dom, closure) => {
                        let (bicit, dom, closure) = (*bicit, dom.clone(), closure.clone());
                        if let Some(v) = impl_vals.pop() {
                            ty = infer.closure_apply(&closure, v);
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
                        let u = Rc::new(Val::vvar(cxt_arm.lvl));
                        let detail = match sub {
                            None => {
                                let b = empty_span(format!("_{}", bname.data));
                                let d_t = infer.quote(cxt_arm.lvl, &dom);
                                cxt_arm = cxt_arm.bind(b, d_t, dom.clone());
                                PatternDetail::Any(empty_span(()))
                            }
                            Some(Pattern::Any(span, _)) => {
                                sub_queue.remove(0);
                                let b = empty_span(format!("_{}", bname.data));
                                let d_t = infer.quote(cxt_arm.lvl, &dom);
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
                        ty = infer.closure_apply(&closure, u);
                    }
                    _ => break,
                }
            }
            Ok((PatternDetail::Con(name.clone(), details), cxt_arm))
        }
    }
}
