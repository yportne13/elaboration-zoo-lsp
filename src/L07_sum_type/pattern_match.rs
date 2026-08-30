//! 模式匹配编译：把 `match` 的 (模式, 分支体) 列表编译成
//! `Vec<(PatternDetail, Tm)>`，并做覆盖性 / 可达性检查。
//!
//! ## 设计（依赖模式匹配的正向构造）
//!
//! 依赖模式匹配的标准理论（Coquand '92，Cockx & Abel 的 specialization by
//! unification）：对 scrutinee 类型 `D p̄ ī` 上的构造子模式 `c`，把构造子
//! 返回类型的索引 ū 与头部索引 ī 做一次**特化合一**。方程解得出 = 分支
//! 可达且解就是精化；结构冲突 = 分支不可能（absurd）。可达性、覆盖性、
//! 精化由同一套机制给出。
//!
//! 本实现把该理论映射到 NbE 上，三条纪律：
//!
//! - **模式变量一律刚性**：构造子的所有绑定器（含隐式）各占一个 env 槽、
//!   绑定为 fresh rigid，与运行时 `eval_aux` 的 prepend 严格同序同数。
//!   通配的隐式是"模式变量"而不是存在量词，不再用 fresh meta 充当。
//! - **特化解是上下文外的事实表**（`Infer::pm_defs`）：`len := succ l`、
//!   `a := zero` 只是 (层级 → 值) 记录；层级、env 槽、元变量 spine 一概
//!   不动，`force` 在读点惰性展开。不存在"改写上下文后，已捕获旧上下文
//!   的值（卡住的 match、meta 解）全部过期"的错位问题。
//! - **头部精化无条件**：被匹配变量本身也写入事实表（`a := succ t`）。
//!   旧实现按返回类型是否含卡住 match 门控这一步；现在 `force` 会在卡住
//!   match 的 scrutinee 上重试选分支，精化的传播不需要任何门控。
//!
//! 合一只有一套：`unify` 与特化的差别只在 `pm_solvable`（当前子句的
//! bind 槽）非空时 rigid 可解。逐臂（per-arm）下钻保持用户书写顺序，
//! 运行时首匹配 = 用户语义；通配臂（`case x`）之后的所有臂不可达。

use crate::parser_lib::Span;

use super::{
    Env, Error, Infer, Lvl, Tm, Val,
    cxt::{Cxt, Decls},
    empty_span,
    parser::syntax::{Icit, Pattern, Raw},
    PatternDetail,
};

pub struct Compiler {
    /// 收集所有错误（覆盖缺失 / 分支不可达），一次报全。
    pub errors: Vec<String>,
    pub pats: Vec<(PatternDetail, Tm)>,
}

enum Walk {
    Matched(PatternDetail, Cxt),
    Unreachable,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            errors: Vec::new(),
            pats: Vec::new(),
        }
    }

    pub fn compile(
        &mut self,
        infer: &mut Infer,
        scrut_ty: Val,
        scrut: Tm,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt,
        expected: Val,
    ) -> Result<(), Error> {
        // 被匹配对象的值（在 match 现场求值）：用于把"被匹配的变量本身"
        // 写入精化事实表（见 walk_con 末尾）
        let head_val = infer.eval(cxt.decl(), &cxt.env, scrut);
        // 编译期间的所有合一共享一个 fuel 池（深层递归防护）
        infer.meta_refuel();
        let head_sum = match infer.force(cxt.decl(), scrut_ty.clone()) {
            s @ Val::Sum(..) => s,
            _ => return Err(Error("match 的对象必须是和类型（enum）".to_owned())),
        };
        let ctor_names: Vec<String> = match &head_sum {
            Val::Sum(_, _, cases) => cases.iter().map(|c| c.data.clone()).collect(),
            _ => unreachable!(),
        };
        // 可解集基线：当前上下文的全部 bind 槽（def 参数 / λ 参数 / 外层
        // 模式变量）。走查中新绑的模式槽在此基础上追加；臂边界与探测回滚。
        let entry = infer.pm_mark();
        for l in cxt.bind_slots() {
            infer.pm_solvable_push(l);
        }
        // 覆盖检查：每个可达构造子必须被某个臂覆盖（通配臂覆盖全部）。
        // 可达性 = 在快照回滚下跑一次特化方程（与臂内走查同一套判定）。
        for ctor in head_sum.sum_cases() {
            if Self::probe_accessible(infer, cxt, &head_sum, &ctor)
                && !arms
                    .iter()
                    .any(|(pat, _)| covers(pat, &ctor.data, &ctor_names))
            {
                self.errors
                    .push(format!("match 不完整：缺少构造子 {}", ctor.data));
            }
        }
        // 逐臂下钻。一旦出现通配臂（覆盖所有取值），后续臂运行时永远不会被
        // 选中——保持用户顺序的首匹配语义即可，被遮蔽的臂跳过。
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                continue;
            }
            let mark = infer.pm_mark();
            match self.walk(infer, pat.clone(), scrut_ty.clone(), head_val.clone(), cxt)? {
                Walk::Matched(detail, cxt_arm) => {
                    // 分支体走**常规转换**检查（可解集摘走——体检查不得解
                    // 假设）。
                    let saved_solvable = infer.pm_solvable_take();
                    // 期望类型**重锚**到臂上下文：quote → eval 把其中所有
                    // rigid 引用重定向到臂 env（quote 时 defs 活跃，精化等式
                    // 一并烘焙进去）。语义上不重锚也正确（force 惰性展开
                    // defs），但值层面只有重锚后，期望里的卡住 match 与
                    // meta 解物化出来的副本才有同样的 env 布局——unify 的
                    // 结构快路径（val_eq）才能命中，否则双方逐层展开不收敛。
                    let ret_type = match infer.force(cxt_arm.decl(), expected.clone()) {
                        t @ Val::Flex(..) => t,
                        t => {
                            let tm = infer.quote(cxt_arm.decl(), cxt_arm.lvl, t);
                            infer.eval(cxt_arm.decl(), &cxt_arm.env, tm)
                        }
                    };
                    let tm = infer.check(&cxt_arm, body.clone(), ret_type)?;
                    infer.pm_solvable_set(saved_solvable);
                    self.pats.push((detail, tm));
                    if is_catch_all(pat, &ctor_names) {
                        shadowed = true;
                    }
                }
                Walk::Unreachable => {
                    self.errors
                        .push(format!("分支不可达：模式 {:?} 与被匹配类型不相容", pat));
                }
            }
            // 臂边界：回滚本臂的精化事实与可解集（本臂解出的 meta 保留——
            // 分支体 Tm 引用着它们，且解在 rename 时已烘焙为无 def 形式）。
            infer.pm_restore(mark);
        }
        infer.pm_restore(entry);
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(Error(self.errors.join("\n")))
        }
    }

    /// 构造子可达性探测：在（meta + 精化状态）快照回滚下跑一次特化方程。
    /// 探测不产生真槽——构造子绑定器用超出上下文的 scratch 层级实例化
    /// （同为刚性、同可被方程解出，回滚即可）。成功 = 该构造子可能出现在
    /// 头部类型的值里；结构冲突（`Vec[A] zero` 上不可能有 `cons`）= absurd。
    fn probe_accessible(infer: &mut Infer, cxt: &Cxt, head_sum: &Val, ctor: &Span<String>) -> bool {
        let (sum_name, impl_vals) = match head_sum {
            Val::Sum(name, params, _) => (
                name,
                params
                    .iter()
                    .filter(|(_, _, _, i)| *i == Icit::Impl)
                    .map(|(_, v, _, _)| v.clone())
                    .collect::<Vec<_>>(),
            ),
            _ => return false,
        };
        let entry = match cxt.decl_get(&format!("{}.{}", sum_name.data, ctor.data)) {
            Some(e) => e,
            None => return false,
        };
        let snap = infer.meta_snapshot();
        let mark = infer.pm_mark();
        let decl = cxt.decl().clone();
        let mut ty = entry.ty.clone();
        let mut impl_idx = 0;
        let mut scratch = 0u32;
        let ok = loop {
            match infer.force(&decl, ty) {
                Val::Pi(_, _, _, closure) => {
                    let u = if impl_idx < impl_vals.len() {
                        let v = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        v
                    } else {
                        let l = Lvl(cxt.lvl.0 + scratch);
                        scratch += 1;
                        infer.pm_solvable_push(l);
                        Val::vvar(l)
                    };
                    ty = infer.closure_apply(&decl, &closure, u);
                }
                ret => {
                    let ret_sum = match infer.force(&decl, ret) {
                        s @ Val::Sum(..) => s,
                        _ => break false,
                    };
                    break Self::unify_indices(infer, cxt, head_sum, &ret_sum, &ctor.data).is_ok();
                }
            }
        };
        infer.pm_restore(mark);
        infer.meta_restore(snap);
        ok
    }

    /// 特化方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽合一，
    /// **头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 := 构造子
    /// 侧值"（即"老的变量 := 新的变量"，与上下文顺序一致）。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        head_sum: &Val,
        ret_sum: &Val,
        ctor: &str,
    ) -> Result<(), Error> {
        let (hp, rp) = match (head_sum, ret_sum) {
            (Val::Sum(_, p1, _), Val::Sum(_, p2, _)) => (p1, p2),
            _ => return Err(Error(format!("构造子 {ctor} 的返回类型不是和类型"))),
        };
        if hp.len() != rp.len() {
            return Err(Error(format!("构造子 {ctor} 与被匹配类型的参数数不一致")));
        }
        for (a, b) in hp.iter().zip(rp.iter()) {
            infer
                .unify(cxt.decl(), cxt.lvl, cxt, a.1.clone(), b.1.clone())
                .map_err(|_| Error(format!("构造子 {ctor} 与被匹配类型不相容（分支不可达）")))?;
        }
        Ok(())
    }

    fn walk(
        &mut self,
        infer: &mut Infer,
        pat: Pattern,
        head_ty: Val,
        head_val: Val,
        cxt: &Cxt,
    ) -> Result<Walk, Error> {
        match pat {
            Pattern::Any(span, _) => {
                let lvl = cxt.lvl;
                let cxt = cxt.bind(
                    span.map(|_| "_".to_owned()),
                    infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
                    head_ty,
                );
                infer.pm_solvable_push(lvl);
                Ok(Walk::Matched(PatternDetail::Any(span), cxt))
            }
            Pattern::Con(name, subs, _) => self.walk_con(infer, name, subs, head_ty, head_val, cxt),
        }
    }

    /// 下钻一个构造子模式。槽位纪律：**每个绑定器一个槽，先绑定后下钻**——
    /// 构造子 Pi 链上每个绑定器都在当前 `cxt.lvl` 处绑定为 fresh rigid
    /// （枚举隐式参数除外：用头部 Sum 的实参实例化，不产生槽），然后按
    /// icit 对齐用户子模式继续下钻。嵌套 Con 模式由子 walk_con 入口绑自己
    /// 的 head 槽（槽值即本字段的实例化 rigid u），编译期绑定、运行时
    /// prepend、bind_count 三方同序同数。
    fn walk_con(
        &mut self,
        infer: &mut Infer,
        name: Span<String>,
        subs: Vec<Pattern>,
        head_ty: Val,
        head_val: Val,
        cxt: &Cxt,
    ) -> Result<Walk, Error> {
        let head_sum = match infer.force(cxt.decl(), head_ty.clone()) {
            s @ Val::Sum(..) => s,
            _ => {
                // 非和类型头部：只能当变量绑定
                if !subs.is_empty() {
                    return Err(Error(format!(
                        "`{}` 不是构造子，不能带子模式解构",
                        name.data
                    )));
                }
                let lvl = cxt.lvl;
                let cxt = cxt.bind(
                    name.clone(),
                    infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
                    head_ty,
                );
                infer.pm_solvable_push(lvl);
                return Ok(Walk::Matched(PatternDetail::Bind(name), cxt));
            }
        };
        let (sum_name, sum_params, cases) = match &head_sum {
            Val::Sum(name, params, cases) => (name, params, cases),
            _ => unreachable!(),
        };
        let is_ctor = cases.iter().any(|c| c.data == name.data);
        if !is_ctor {
            // 不是该类型的构造子 → 变量绑定
            if !subs.is_empty() {
                return Err(Error(format!(
                    "`{}` 不是 {} 的构造子，不能带子模式解构",
                    name.data, sum_name.data
                )));
            }
            let lvl = cxt.lvl;
            let cxt = cxt.bind(
                name.clone(),
                infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
                head_ty,
            );
            infer.pm_solvable_push(lvl);
            return Ok(Walk::Matched(PatternDetail::Bind(name), cxt));
        }
        let entry = cxt
            .decl_get(&format!("{}.{}", sum_name.data, name.data))
            .ok_or_else(|| Error(format!("找不到构造子 {}.{}", sum_name.data, name.data)))?;
        // head 槽：Con 模式自身占一槽。运行时 eval_aux 的 Con 路径把被匹配值
        // prepend 进 env，三方（编译期绑定 / 运行时 prepend / bind_count）
        // 同序同数。
        let lvl = cxt.lvl;
        let mut cxt = cxt.bind(
            empty_span(format!("_{}", name.data)),
            infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
            head_ty,
        );
        infer.pm_solvable_push(lvl);
        let mut ty = entry.ty.clone();
        let impl_vals: Vec<Val> = sum_params
            .iter()
            .filter(|(_, _, _, i)| *i == Icit::Impl)
            .map(|(_, v, _, _)| v.clone())
            .collect();
        let mut impl_idx = 0;
        let mut sub_queue: Vec<Pattern> = subs;
        let mut details: Vec<PatternDetail> = Vec::new();
        // 构造子自身绑定器的值（写入头部精化时用）
        let mut ctor_datas: Vec<(Span<String>, Val, Icit)> = Vec::new();
        let ret = loop {
            match infer.force(cxt.decl(), ty) {
                Val::Pi(bname, bicit, dom, closure) => {
                    let dom = *dom;
                    if impl_idx < impl_vals.len() {
                        // 枚举隐式参数：不产生模式槽
                        let u = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        ty = infer.closure_apply(cxt.decl(), &closure, u);
                        continue;
                    }
                    // 用户子模式按 icit 对齐：隐式绑定器可以缺省（自动通配），
                    // 显式绑定器必须提供；子模式必须与绑定器顺序一致
                    let sub = match bicit {
                        Icit::Impl => {
                            let matches_impl = sub_queue
                                .first()
                                .map(|p| p.get_icit() == Icit::Impl)
                                .unwrap_or(false);
                            if matches_impl {
                                Some(sub_queue.remove(0))
                            } else {
                                None
                            }
                        }
                        Icit::Expl => match sub_queue.first() {
                            Some(p) if p.get_icit() == Icit::Expl => Some(sub_queue.remove(0)),
                            _ => {
                                return Err(Error(format!(
                                    "构造子 {} 缺少字段 {} 的模式",
                                    name.data, bname.data
                                )))
                            }
                        },
                    };
                    // 绑定器的"值"：一律 fresh rigid（模式变量，可被特化方程解出）
                    let u = Val::vvar(cxt.lvl);
                    let (detail, new_cxt) = match sub {
                        None => {
                            let lvl = cxt.lvl;
                            let c = cxt.bind(
                                bname.clone().map(|n| format!("_{n}")),
                                infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                dom.clone(),
                            );
                            infer.pm_solvable_push(lvl);
                            (PatternDetail::Any(empty_span(())), c)
                        }
                        Some(Pattern::Any(span, _)) => {
                            let lvl = cxt.lvl;
                            let c = cxt.bind(
                                span.map(|_| "_".to_owned()),
                                infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                dom.clone(),
                            );
                            infer.pm_solvable_push(lvl);
                            (PatternDetail::Any(span), c)
                        }
                        Some(Pattern::Con(cn, csubs, _)) => {
                            let is_ctor = matches!(
                                infer.force(cxt.decl(), dom.clone()),
                                Val::Sum(_, _, cases) if cases.iter().any(|c| c.data == cn.data)
                            );
                            if is_ctor {
                                // 解构：子 walk_con 入口绑自己的 head 槽
                                // （槽值即本字段的实例化 rigid u）
                                match self.walk_con(
                                    infer, cn, csubs, dom.clone(), u.clone(), &cxt,
                                )? {
                                    Walk::Matched(d, c) => (d, c),
                                    Walk::Unreachable => return Ok(Walk::Unreachable),
                                }
                            } else {
                                if !csubs.is_empty() {
                                    return Err(Error(format!(
                                        "`{}` 不是构造子，不能带子模式解构",
                                        cn.data
                                    )));
                                }
                                let lvl = cxt.lvl;
                                let c = cxt.bind(
                                    cn.clone(),
                                    infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                    dom.clone(),
                                );
                                infer.pm_solvable_push(lvl);
                                (PatternDetail::Bind(cn), c)
                            }
                        }
                    };
                    cxt = new_cxt;
                    details.push(detail);
                    ctor_datas.push((bname.clone(), u.clone(), bicit));
                    ty = infer.closure_apply(cxt.decl(), &closure, u);
                }
                ret => break ret,
            }
        };
        if !sub_queue.is_empty() {
            return Err(Error(format!(
                "构造子 {} 的模式多了 {} 个子模式",
                name.data,
                sub_queue.len()
            )));
        }
        // 特化方程：头部索引 ≐ 构造子返回索引。失败 = 分支不可达。
        let ret_sum = match infer.force(cxt.decl(), ret) {
            s @ Val::Sum(..) => s,
            _ => {
                return Err(Error(format!(
                    "构造子 {} 的返回类型不是和类型",
                    name.data
                )))
            }
        };
        if Self::unify_indices(infer, &cxt, &head_sum, &ret_sum, &name.data).is_err() {
            return Ok(Walk::Unreachable);
        }
        // 头部精化（无条件）：被匹配变量本身写入事实表。`V a`、`add a zero`
        // 这类依赖被匹配变量的类型，要等 a := zero / a := succ t 之后才能
        // 归约——force 在读点展开这些事实。只对"本子句里尚未精化的变量"
        // 做（force 已展开过的不会再以 bare Rigid 出现）。
        if let Val::Rigid(x, sp) = &infer.force(cxt.decl(), head_val.clone()) {
            if sp.is_empty()
                && x.0 < cxt.lvl.0
                && infer.pm_solvable_contains(*x)
                && infer.pm_def(*x).is_none()
            {
                let ctor_val = Val::SumCase {
                    typ: Box::new(head_sum.clone()),
                    case_name: name.clone(),
                    datas: ctor_datas,
                };
                // 环守卫失败（typ 的索引提及 x 自身等病态情形）时跳过精化，
                // 不阻断分支检查
                infer.pm_solve(*x, &ctor_val);
            }
        }
        Ok(Walk::Matched(PatternDetail::Con(name, details), cxt))
    }

    /// 运行时分支选择：按模式首匹配。返回 (分支体, 扩展后的 env)。
    /// 任何 head 都不会 panic——不命中就返回 None，由调用方停成 `Val::Match`。
    pub fn eval_aux(
        infer: &Infer,
        decl: &Decls,
        head: Val,
        env: &Env,
        cases: &[(PatternDetail, Tm)],
    ) -> Option<(Tm, Env)> {
        let head = infer.force(decl, head);
        for (pat, body) in cases {
            match pat {
                PatternDetail::Any(_) | PatternDetail::Bind(_) => {
                    return Some((body.clone(), env.prepend(head.clone())));
                }
                PatternDetail::Con(name, subs) => {
                    let Val::SumCase {
                        typ,
                        case_name,
                        datas,
                    } = &head
                    else {
                        continue;
                    };
                    let Val::Sum(_, _, ctor_names) = typ.as_ref() else {
                        continue;
                    };
                    let in_type = ctor_names.iter().any(|c| c.data == name.data);
                    if in_type && case_name.data == name.data {
                        if subs.len() != datas.len() {
                            continue;
                        }
                        // datas 与子模式按声明序 zip，逐个下钻；先 prepend 被
                        // 匹配值本身（head 槽，编译期 walk_con 入口同序绑定），
                        // 再逐字段 prepend 子模式槽值（编译期字段槽在后）
                        let mut cur = (body.clone(), env.prepend(head.clone()));
                        let mut ok = true;
                        for ((_, v, _), sub) in datas.iter().zip(subs.iter()) {
                            match Compiler::eval_aux(
                                infer,
                                decl,
                                v.clone(),
                                &cur.1,
                                &[(sub.clone(), cur.0.clone())],
                            ) {
                                Some((b, e)) => cur = (b, e),
                                None => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        if ok {
                            return Some(cur);
                        }
                    } else if !in_type {
                        // 不是该类型的构造子名 → 变量模式（保守兼容）
                        return Some((body.clone(), env.prepend(head.clone())));
                    }
                    // 同类型不同构造子 → 试下一个分支
                }
            }
        }
        None
    }
}

/// 顶层覆盖判定：通配 / 变量模式覆盖一切；Con 只覆盖同名构造子。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor,
    }
}

/// 通配臂：覆盖所有取值的臂（其后的臂不可达）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data),
    }
}

impl Val {
    fn sum_cases(&self) -> Vec<Span<String>> {
        match self {
            Val::Sum(_, _, cases) => cases.clone(),
            _ => vec![],
        }
    }
}
