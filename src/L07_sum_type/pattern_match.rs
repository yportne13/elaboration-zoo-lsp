//! 模式匹配编译：把 `match` 的 (模式, 分支体) 列表编译成
//! `Vec<(PatternDetail, Tm)>`，并做覆盖性 / 可达性检查。
//!
//! 编译是**逐臂（per-arm）下钻**而非 L07/L07a 的"构造子矩阵"：
//! - 每个臂独立沿自己的模式走，沿途 `cxt.bind` 模式绑定器（深度优先，
//!   与运行时 `eval_aux` 的 prepend 顺序一致），并在每个构造子节点做
//!   索引精化（`unify_pm(头部类型, 构造子返回类型)`）；
//! - 分支体在**该臂精化后的上下文**里检查，期望返回类型也重新实例化；
//! - 输出保持用户书写顺序，运行时首匹配 = 用户语义；
//!   通配臂（`case x`）之后的所有臂不可达。
//!
//! 相比 L07a 的矩阵算法，这修掉了"通配臂与构造子臂混合时丢分支 /
//! 分支体跨上下文记忆化"两个 bug，同时支持 GADT 索引精化。

use crate::parser_lib::Span;

use super::{
    Env, Error, Infer, Tm, Val,
    cxt::{Cxt, Decls},
    empty_span,
    parser::syntax::{Icit, Pattern, Raw},
    PatternDetail,
};

pub struct Compiler {
    /// 收集所有错误（覆盖缺失 / 分支不可达），一次报全。
    pub errors: Vec<String>,
    pub pats: Vec<(PatternDetail, Tm)>,
    /// match 的期望返回类型（决定是否需要对被匹配变量做值级精化）
    ret_type: Val,
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
            ret_type: Val::U,
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
        // 精化成构造子值（返回类型依赖该变量时的关键一步，见 walk_con）
        let head_val = infer.eval(cxt.decl(), &cxt.env, scrut);
        self.ret_type = expected.clone();
        // 编译期间的所有合一共享一个 fuel 池（深层递归防护，
        // unify / force 的循环展开在耗尽时停止）
        infer.meta_refuel();
        let sum = match infer.force(cxt.decl(), scrut_ty.clone()) {
            s @ Val::Sum(..) => s,
            _ => return Err(Error("match 的对象必须是和类型（enum）".to_owned())),
        };
        let ctor_names = match &sum {
            Val::Sum(_, _, cases) => cases
                .iter()
                .map(|c| c.data.clone())
                .collect::<Vec<String>>(),
            _ => unreachable!(),
        };
        // 顶层覆盖检查：每个可达构造子都要被某个臂覆盖（通配臂覆盖全部）
        let accessible: Vec<Span<String>> = sum
            .sum_cases()
            .into_iter()
            .filter(|c| self.accessible(infer, cxt, &sum.clone(), c))
            .collect();
        for ctor in &accessible {
            if !arms.iter().any(|(pat, _)| covers(pat, &ctor.data, &ctor_names)) {
                self.errors
                    .push(format!("match 不完整：缺少构造子 {}", ctor.data));
            }
        }
        // 逐臂下钻。一旦出现通配臂（覆盖所有取值），后续臂运行时永远不会被
        // 选中——保持用户顺序的首匹配语义即可，被遮蔽的臂跳过（不做无意义的
        // 精化/检查；也不报错，与 L07/L07a 行为一致）。
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                continue;
            }
            match self.walk(infer, pat.clone(), scrut_ty.clone(), head_val.clone(), cxt)? {
                Walk::Matched(detail, cxt_arm) => {
                    // 分支体在精化后的上下文里检查；期望返回类型也重新实例化
                    // （索引精化会改写 env 槽，quote → eval 把精化传播进取值类型）
                    let ret_type = match infer.force(cxt_arm.decl(), expected.clone()) {
                        t @ Val::Flex(..) => t,
                        t => {
                            let tm = infer.quote(cxt_arm.decl(), cxt_arm.lvl, t);
                            infer.eval(cxt_arm.decl(), &cxt_arm.env, tm)
                        }
                    };
                    let tm = infer.check(&cxt_arm, body.clone(), ret_type)?;
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
        }
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(Error(self.errors.join("\n")))
        }
    }

    /// 构造子可达性探测：在克隆的上下文 + 元变量快照回滚下，用全 meta
    /// 实例化构造子类型并与头部类型 `unify_pm`。成功 = 可达。
    /// 探测不落任何副作用（meta 回滚、cxt 丢弃、精化只发生在克隆上）。
    fn accessible(&self, infer: &mut Infer, cxt: &Cxt, head_ty: &Val, ctor: &Span<String>) -> bool {
        let snap = infer.meta_snapshot();
        let ok = {
            let c = cxt.clone();
            self.peel_probe(infer, &c, head_ty.clone(), ctor).is_ok()
        };
        infer.meta_restore(snap);
        ok
    }

    /// 探测用剥 Pi：枚举隐式参数用头部 Sum 的实参值，其余绑定器全用 fresh meta
    /// （meta 是通配符：既能被头部约束，也不会像替身 rigid 那样被 refine 回落卡住）。
    fn peel_probe(
        &self,
        infer: &mut Infer,
        cxt: &Cxt,
        head_ty: Val,
        ctor: &Span<String>,
    ) -> Result<(), Error> {
        let (sum_name, params) = match infer.force(cxt.decl(), head_ty.clone()) {
            Val::Sum(name, params, _) => (name, params),
            _ => return Err(Error("probe: not a sum".to_owned())),
        };
        let entry = cxt
            .decl_get(&format!("{}.{}", sum_name.data, ctor.data))
            .ok_or_else(|| Error(format!("找不到构造子 {}.{}", sum_name.data, ctor.data)))?;
        let mut ty = entry.ty.clone();
        let impl_vals: Vec<Val> = params
            .iter()
            .filter(|(_, _, _, i)| *i == Icit::Impl)
            .map(|(_, v, _, _)| v.clone())
            .collect();
        let mut impl_idx = 0;
        loop {
            match infer.force(cxt.decl(), ty) {
                Val::Pi(_, _, dom, closure) => {
                    let u = if impl_idx < impl_vals.len() {
                        let v = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        v
                    } else {
                        let m = infer.fresh_meta(cxt.decl(), cxt, *dom);
                        infer.eval(cxt.decl(), &cxt.env, m)
                    };
                    ty = infer.closure_apply(cxt.decl(), &closure, u);
                }
                ret => {
                    // 约定：头部类型在前，构造子返回类型在后 → 精化方向正确
                    infer.unify_pm(cxt, head_ty.clone(), ret)?;
                    return Ok(());
                }
            }
        }
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
                let cxt = cxt.bind(
                    span.map(|_| "_".to_owned()),
                    infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
                    head_ty,
                );
                Ok(Walk::Matched(PatternDetail::Any(span), cxt))
            }
            Pattern::Con(name, subs, _) => self.walk_con(name, subs, head_ty, head_val, cxt, infer),
        }
    }

    /// 下钻一个构造子模式。核心不变量：**每个绑定器一个槽，先绑定后下钻**——
    /// 构造子 Pi 链上每个绑定器都在当前 `cxt.lvl` 处 bind（显式绑定器的实例化值
    /// 就是它自己的 fresh rigid，因此字段类型天然依赖已匹配前缀），然后按 icit
    /// 对齐用户子模式继续下钻。枚举隐式参数用头部 Sum 的实参实例化，不产生槽。
    ///
    /// `head_val` 是被匹配对象的值：如果它是当前上下文里尚未精化的变量，
    /// 匹配构造子后把它精化成构造子值——返回类型依赖被匹配变量本身时
    /// （如 `def f(n: Nat): V n = match n { case zero => … }`），分支体的
    /// 期望类型重实例化时 `V n` 才能归约成 `V zero`。
    fn walk_con(
        &mut self,
        name: Span<String>,
        subs: Vec<Pattern>,
        head_ty: Val,
        head_val: Val,
        cxt: &Cxt,
        infer: &mut Infer,
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
                let cxt = cxt.bind(
                    name.clone(),
                    infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
                    head_ty,
                );
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
            let cxt = cxt.bind(
                name.clone(),
                infer.quote(cxt.decl(), cxt.lvl, head_ty.clone()),
                head_ty,
            );
            return Ok(Walk::Matched(PatternDetail::Bind(name), cxt));
        }
        if !self.accessible(infer, cxt, &head_sum, &name) {
            return Ok(Walk::Unreachable);
        }
        let entry = cxt
            .decl_get(&format!("{}.{}", sum_name.data, name.data))
            .ok_or_else(|| Error(format!("找不到构造子 {}.{}", sum_name.data, name.data)))?;
        let mut ty = entry.ty.clone();
        let impl_vals: Vec<Val> = sum_params
            .iter()
            .filter(|(_, _, _, i)| *i == Icit::Impl)
            .map(|(_, v, _, _)| v.clone())
            .collect();
        let mut impl_idx = 0;
        let mut sub_queue: Vec<Pattern> = subs;
        let mut cxt = cxt.clone();
        let mut details: Vec<PatternDetail> = Vec::new();
        // 构造子形态（把被匹配变量精化成它的值时需要）
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
                    // 绑定器的"值"：显式 = 它自己的 fresh rigid（真实层级，无替身偏移），
                    // 隐式 = fresh meta（可被返回类型精化进一步约束）
                    let u = match bicit {
                        Icit::Impl => {
                            let m = infer.fresh_meta(cxt.decl(), &cxt, dom.clone());
                            infer.eval(cxt.decl(), &cxt.env, m)
                        }
                        Icit::Expl => Val::vvar(cxt.lvl),
                    };
                    // 槽绑定：每个绑定器占一槽（与运行时 prepend 对齐）
                    let (detail, new_cxt) = match sub {
                        None => {
                            let c = cxt.bind(
                                bname.clone().map(|n| format!("_{n}")),
                                infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                dom.clone(),
                            );
                            (PatternDetail::Any(empty_span(())), c)
                        }
                        Some(Pattern::Any(span, _)) => {
                            let c = cxt.bind(
                                span.map(|_| "_".to_owned()),
                                infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                dom.clone(),
                            );
                            (PatternDetail::Any(span), c)
                        }
                        Some(Pattern::Con(cn, csubs, _)) => {
                            let is_ctor = matches!(
                                infer.force(cxt.decl(), dom.clone()),
                                Val::Sum(_, _, cases) if cases.iter().any(|c| c.data == cn.data)
                            );
                            if is_ctor {
                                // 解构：槽用哑名（绑定器的值本身也可通过 Ix 引用），
                                // 子绑定器由子 walk 在更深层级引入
                                let c = cxt.bind(
                                    empty_span("_".to_owned()),
                                    infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                    dom.clone(),
                                );
                                match self.walk_con(
                                    cn,
                                    csubs,
                                    dom.clone(),
                                    u.clone(),
                                    &c,
                                    infer,
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
                                let c = cxt.bind(
                                    cn.clone(),
                                    infer.quote(cxt.decl(), cxt.lvl, dom.clone()),
                                    dom.clone(),
                                );
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
        // 返回类型与头部类型精化合一（头部在前 → 精化头部变量）
        let cxt = infer
            .unify_pm(&cxt, head_sum.clone(), ret)
            .map_err(|_| Error(format!("构造子 {} 与被匹配类型不相容（分支不可达）", name.data)))?;
        // 被匹配变量的值级精化的门控：**期望返回类型里包含卡住的 match 时**
        // 才做（`Eq (add a zero) a` 含 `add a zero` 的 stuck match；`V n`
        // 本身就是 stuck match）。这是 L07 相对 L07a 的增强：被匹配的变量
        // （def 参数或外层模式绑定器）被精化成构造子值后，分支体的期望
        // 类型重实例化时这些 match 能归约。**只在"尚未被精化"的变量上做**
        // （unify_pm 内部检查），且精化只改值不改类型（pruning 也保留——
        // 后续 meta 仍以它为参数，spine 视图一致，flex-flex 可协调）。
        // 注意：精化会改掉该变量的 env 槽，使其成为 SumCase —— 因此必须
        // 和"头部类型索引精化"（上面的 unify_pm）区分开：后者总是做。
        let refine_head = std::env::var_os("L07_NO_HEAD_REFINE").is_none() && super::val_contains_match(&infer.force(cxt.decl(), self.ret_type.clone()));
        let cxt = if refine_head {
            match infer.force(cxt.decl(), head_val) {
                Val::Rigid(x, sp)
                    if sp.is_empty()
                        && x.0 < cxt.lvl.0
                        && matches!(
                            cxt.env.iter().nth((cxt.lvl.0 - x.0 - 1) as usize),
                            Some(Val::Rigid(y, ys)) if *y == x && ys.is_empty()
                        ) =>
                {
                    let ctor_val = Val::SumCase {
                        typ: Box::new(head_sum),
                        case_name: name.clone(),
                        datas: ctor_datas,
                    };
                    infer.unify_pm(&cxt, Val::vvar(x), ctor_val).map_err(|_| {
                        Error(format!(
                            "构造子 {} 与被匹配变量不相容（分支不可达）",
                            name.data
                        ))
                    })?
                }
                _ => cxt,
            }
        } else {
            cxt
        };
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
                        // datas 与子模式按声明序 zip，逐个下钻；每个子模式把它的
                        // 槽值 prepend 进 env（第一个子模式最深，与编译期一致）
                        let mut cur = (body.clone(), env.clone());
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
