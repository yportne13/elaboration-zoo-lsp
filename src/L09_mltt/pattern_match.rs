use std::collections::HashSet;
use std::rc::Rc;

use crate::parser_lib::Span;

use super::{
    Env, Error, Infer, Subst, Tm, Val,
    cover_at, fmt_path, wrap_sub,
    cxt::Cxt,
    empty_span, rc_take,
    parser::syntax::{Pattern, Raw, Icit},
    unification::SpecSolve,
    PatternDetail, PosCover,
};

type Constructor = Span<String>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（L07 同文案：`match 不完整：模式位置 {path} 缺少
    /// 构造子 {ctor}`；2026-09-18 评审修复 P0 的 L09 移植）。
    IncompleteNested(String),
}

pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Tm)>,
    ret_type: Val,
    /// 嵌套覆盖检查的记账（走查中收集，臂循环结束后统一探测；L07 同款，
    /// 2026-09-18 评审修复 P0 的 L09 移植）。顶层覆盖检查只遍历 scrutinee
    /// 类型的构造子；嵌套 `Con` 字段位置的可达性从未被枚举会让非穷尽
    /// match 被静默接受。两段式：走查中只记 (路径, 字段 Sum, 本层 ret)；
    /// 本臂特化方程**解出后**（σ 为终态）才提升为完整记账——字段走查时
    /// 索引精化不在 σ 里，此时探测会把已精化下不可达的构造子误判可达。
    /// 整臂特化失败（荒谬臂，静默跳过）时丢弃记账。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待提升位置（结算方程成功后提升）。`ret` 是该层 Con 的
    /// 走查返回类型（槽位刚性即本层走查变量，L07 walk_con 的特化方程的
    /// 构造子侧）。
    pending_pos: Vec<(Vec<(String, usize)>, Val, Val)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账（L07 `NestedCheck` 同构）：路径 = 根到被拆字段
/// 的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂实例化下的
/// Sum 值；`cxt` 是臂走查上下文快照（探测的 scratch 层级须落在该臂全部
/// 真槽之外，spec_refine 的 `x >= cxt.lvl` 守卫以臂内层级为准）；σ 是臂
/// 终态的精化替换（延迟探测要在与臂内方程同构的状态下跑）。
struct NestedCheck {
    path: Vec<(String, usize)>,
    field_sum: Val,
    cxt: Cxt,
    sub: Rc<Subst>,
}

impl Compiler {
    pub fn new(ret_type: Val) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
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
    ///
    /// `init_sub` 显式穿参（L07/L10 同款，2026-09-18 评审修复 2/5 的 L09
    /// 移植）：顶层探测传空 σ；嵌套位置的延迟探测传记账时的臂内终态 σ。
    /// 顶层调用传 `cxt`（探测 cxt.lvl 起的 scratch）；嵌套调用传臂走查
    /// 上下文（src_names / bind_slots / lvl 均为臂内的）。
    fn probe_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        head_sum: &Val,
        ctor: &String, // BiMap::get 的键口径（`&str` 借查不支持，避免每次探测多一次分配）
        init_sub: &Rc<Subst>,
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
                }
                _ => {
                    break Self::unify_indices(infer, cxt, &sum_name, &head_params, &tyf, init_sub)
                        // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理
                        // （保守地要求覆盖）。反方向（判不可达 → 覆盖检查放
                        // 过该构造子）会让深负载下的非穷尽 match 被静默接受
                        // （L07 同款方向纠偏，2026-09-18 评审修复 2）。
                        || infer.fuel_exhausted()
                }
            }
        };
        // 纯探测：探测期解掉的 meta（含探测前已有的）整表回滚——探测期解掉的
        // 已有 meta 可能引用循环内新建 meta，必须整表 clone、不能 truncate。
        infer.meta = snap;
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子），弃掉即回滚。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        sum_name: &Span<String>,
        head_params: &[Rc<Val>],
        ret_ty: &Val,
        init_sub: &Rc<Subst>,
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
            acc: init_sub.clone(),
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
    /// 语义相对决策树的三处收窄（覆盖含嵌套位置 / 遮蔽只认通配臂 / 特化失败
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
        self.nested_checks = Vec::new();
        self.pending_pos = Vec::new();
        self.cur_path = Vec::new();
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
        let empty_sub: Rc<Subst> = Rc::new(Subst::default());
        for ctor in &constrs {
            if Self::probe_accessible(infer, cxt, &typ, &ctor.data, &empty_sub)
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
            // 本臂走查起点无遗留记账（上一臂已结算/丢弃，防御性清空）。
            self.pending_pos.clear();
            self.cur_path.clear();
            let (detail, cxt_walk, top_ret) = match self.walk_pat(infer, cxt, pat, &typ) {
                Ok(x) => x,
                Err(_) => {
                    // 走查失败臂的嵌套记账一并丢弃
                    self.pending_pos.clear();
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma0)) =
                infer.check_pm_final(&cxt_walk, raw, typ.clone(), target_val.clone())
            else {
                // 荒谬臂（特化失败静默跳过）：其嵌套位置不产生覆盖义务——
                // 臂本身被跳过已承担语义（L07 荒谬臂 clear pending 同款）
                self.pending_pos.clear();
                continue;
            };
            // 走查特化方程的结算（L07 walk_con 内联方程的等价物，2026-09-18
            // P0 修复的链接步骤）：本臂每层 Con 的「头部 ≐ 走查 ret」方程以
            // σ 作种子补解入，把**走查槽位刚性链接进 σ**——嵌套位置的延迟
            // 探测由此看到索引精化（如 `Vec[Nat] (succ zero)` 的尾部上
            // `nil` 不可达）。方程失败 = 该臂在走查实例化下不可匹配（荒谬
            // 臂）：连同嵌套记账一并静默跳过。
            let solvable = cxt_walk.bind_slots();
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc: sigma0.clone(),
            };
            let span = empty_span(());
            let mut absurd = false;
            if let Some(top_ret) = &top_ret {
                if infer
                    .unify_pm(&cxt_walk, typ.clone(), top_ret.clone(), span, &mut spec)
                    .is_err()
                {
                    absurd = true;
                }
            }
            if !absurd {
                for (_, field_sum, ret) in self.pending_pos.iter() {
                    if infer
                        .unify_pm(&cxt_walk, field_sum.clone(), ret.clone(), span, &mut spec)
                        .is_err()
                    {
                        absurd = true;
                        break;
                    }
                }
            }
            if absurd {
                self.pending_pos.clear();
                continue;
            }
            let sigma = spec.acc;
            // 嵌套位置结算：此刻本臂全部特化方程已解出、σ 为终态，字段 Sum
            // 置于 σ 之下再探测才能看到索引精化（两段式，L07 同款）。
            for (path, field_sum, _) in std::mem::take(&mut self.pending_pos) {
                self.nested_checks.push(NestedCheck {
                    path,
                    field_sum,
                    cxt: cxt_walk.clone(),
                    sub: sigma.clone(),
                });
            }
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
        let mut out: Vec<Warning> = unreachable
            .into_iter()
            .chain(std::mem::take(&mut self.warnings))
            .collect();
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，L07 同款，2026-09-18 评审
        // 修复 P0 的 L09 移植）：每条记账在记录臂的实例化（σ/臂上下文快照）
        // 下探测字段 Sum 的可达构造子；覆盖集 = 已走查臂的 PatternDetail
        // 沿路径的结构贡献（var/Any = 全覆盖；祖先异 ctor = 不可达该位置；
        // 同 ctor 前缀 = 贡献其末端构造子）。可达集取各记账臂探测的并集
        // （保守：任一臂实例化下可达的构造子都要求被覆盖）。荒谬臂 / 被
        // 遮蔽臂不在 pats 里，天然不贡献覆盖——与运行时首匹配结构语义一致。
        let mut reported = HashSet::new();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force：索引精化（如尾部
            // 长度 l := succ n）在 σ 里，推开后的 Sum 才是探测该用的类型
            let field_sum = infer.force(wrap_sub(&nc.sub, nc.field_sum.clone()));
            let ctor_cases: Vec<Span<String>> = match &field_sum {
                Val::Sum(_, _, cs) => cs.clone(),
                _ => continue,
            };
            for ctor in ctor_cases {
                if !Self::probe_accessible(infer, &nc.cxt, &field_sum, &ctor.data, &nc.sub) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    PosCover::All => true,
                    PosCover::Ctor(n) => n == ctor.data,
                    PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.data.clone())) {
                    out.push(Warning::IncompleteNested(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        fmt_path(&nc.path),
                        ctor.data
                    )));
                }
            }
        }
        Ok(out)
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

    /// 模式走查（L07 `walk_con` 口径；L10 `walk_pat` 的 L09 版）：绑定模式变量槽
    /// 并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽、构造子隐式
    /// 绑定器补虚通配、变量模式以用户名绑槽、**Con 本身不占槽**。
    /// L09 的全局表按**层级**存（`Infer.global`，无名字键的 decl 表），构造子
    /// 类型经 `infer_expr(Var(名))` 取（树的头部展开同款）。
    ///
    /// 返回值第三项 = 该层 Con 的走查返回类型（已 force，槽位刚性 = 本层
    /// 走查变量；compile 结算本层特化方程用；非 Con 模式为 `None`）。
    /// 嵌套 `Con` 字段位置记入 `pending_pos`（两段式记账；结算见 `compile`，
    /// 2026-09-18 评审修复 P0 的 L09 移植）。
    fn walk_pat(
        &mut self,
        infer: &mut Infer,
        cxt: &Cxt,
        pat: &Pattern,
        head_ty: &Val,
    ) -> Result<(PatternDetail, Cxt, Option<Val>), Error> {
        match pat {
            Pattern::Any(span, _) => {
                let a_t = infer.quote(cxt.lvl, head_ty.clone());
                let cxt2 = cxt.bind(empty_span("_".to_owned()), a_t, head_ty.clone());
                Ok((PatternDetail::Any(span.clone()), cxt2, None))
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
                        return Ok((PatternDetail::Bind(name.clone()), cxt2, None));
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
                    return Ok((PatternDetail::Bind(name.clone()), cxt2, None));
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
                                    // 嵌套 Con：字段 dom 是含该构造子的 Sum 时
                                    // 记一笔待提升的嵌套位置（该字段位置沿 ctor
                                    // 路径的可达构造子必须有臂覆盖），臂特化方
                                    // 程解出后以终态 σ 结算（见 compile）。
                                    let Pattern::Con(cn, ..) = p else {
                                        unreachable!()
                                    };
                                    let field_sum = infer.force((*dom).clone());
                                    let is_ctor = matches!(&field_sum,
                                        Val::Sum(_, _, cases)
                                            if cases.iter().any(|c| c.data == cn.data));
                                    let (d, c2) = if is_ctor {
                                        self.cur_path.push((name.data.clone(), details.len()));
                                        let (d, c2, inner_ret) =
                                            self.walk_pat(infer, &cxt_arm, p, &dom)?;
                                        self.cur_path.pop();
                                        if let Some(r) = inner_ret {
                                            let mut pa = self.cur_path.clone();
                                            pa.push((name.data.clone(), details.len()));
                                            self.pending_pos.push((pa, field_sum.clone(), r));
                                        }
                                        (d, c2)
                                    } else {
                                        let (d, c2, _) =
                                            self.walk_pat(infer, &cxt_arm, p, &dom)?;
                                        (d, c2)
                                    };
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
                let ret = infer.force(ty.clone());
                Ok((PatternDetail::Con(name.clone(), details), cxt_arm, Some(ret)))
            }
        }
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
