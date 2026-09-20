use std::{
    collections::{BTreeSet, HashMap, HashSet},
};

use smol_str::SmolStr;

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Tm, Val,
    cxt::Cxt, Rc, Decl, Subst,
    elaboration::SpecSolve,
    empty_span, Either, wrap_sub, cover_at,
    parser::syntax::{Pattern, Raw, Icit},
    PatternDetail,
};

type Var = i32;

type Constructor = Span<SmolStr>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（2026-09-18 评审 P0 修复前向传播，L07 同款）：
    /// 完整报错文案直营——路径无 Span 可挂，直塞字符串让 Debug 输出在
    /// 参考/孪生两侧逐字节一致（文案与 L07 统一：
    /// `match 不完整：模式位置 {fmt_path} 缺少构造子 {ctor}`）。
    UnmatchedAt(String),
}

pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Rc<Tm>)>,
    ret_type: Rc<Val>,
    /// 嵌套覆盖检查的记账（L07 pattern_match.rs 同款 2026-09-18 前向传播）。
    /// 顶层覆盖检查只遍历 scrutinee 类型的构造子；嵌套 `Con` 字段位置的
    /// 可达性从未被枚举，非穷尽 match（如 `cons(h, nil)` 缺
    /// `cons(h, cons(..))`）被静默接受、运行期卡死。两段式：走查中只记
    /// (路径, 字段 Sum)；`check_pm_final` **成功后**（特化方程已解出、σ
    /// 为终态）才提升为带 σ/lvl 快照的完整记账——字段走查时外层方程尚未
    /// 解出，索引精化不在 σ 里，此时探测会把已精化下不可达的构造子误判
    /// 可达（v3_len_two_nested_pattern_refine 抓过包）。臂失败（走查错 /
    /// 特化冲突）时丢弃记账：失败臂不产生覆盖义务。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待提升位置（臂边界结算）。
    pending_pos: Vec<(Vec<(String, usize)>, Rc<Val>)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账（L07 `NestedCheck` 同构）：路径 = 根到被拆字段
/// 的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂实例化下的
/// Sum 值；σ/lvl 是记账时刻（该臂 `check_pm_final` 成功后）的走查快照
/// ——延迟探测要在与臂内方程同构的状态下跑。L12 无 solvable 白名单
/// （特化合一的任意裸 Rigid 可解，见 elaboration.rs `SpecSolve` 注），
/// 记账少一项快照。
struct NestedCheck {
    path: Vec<(String, usize)>,
    field_sum: Rc<Val>,
    sub: Rc<Subst>,
    lvl: super::Lvl,
}

impl Compiler {
    pub fn new(ret_type: Rc<Val>) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
        }
    }

    /// 构造子可达性探测（值级，L07 `probe_accessible` 口径）：直接读 decl 表
    /// 拿构造子类型，走 Π 链实例化——枚举隐式参数用头部 Sum 的实参，其余绑定
    /// 器用超出上下文的 scratch 层 fresh rigid（同为刚性，可被方程解出；探测
    /// 状态全在本地，弃掉即回滚），返回类型再与头部类型跑一次索引方程。
    /// 成功 = 该构造子可能出现在头部类型的值里；结构冲突（`Vec[A] zero` 上
    /// 不可能有 `cons`）= absurd。
    /// `lvl` 显式穿参（L07 同款）：顶层探测传入口 `cxt.lvl`；嵌套位置的延迟
    /// 探测传记账时的臂内层级——scratch 层级必须落在该臂全部真槽之外，
    /// 否则会与臂内模式槽的 rigid 撞层级（探测方程误把真槽当 scratch 解）。
    fn probe_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        lvl: super::Lvl,
        head_sum: &Rc<Val>,
        ctor: &str,
        init_sub: &Rc<Subst>,
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
            let tyf = infer.force(&cxt.decl, &wrap_sub(init_sub, ty.clone()));
            match tyf.as_ref() {
                Val::Pi(_, _, _, closure) => {
                    let u = if impl_idx < impl_vals.len() {
                        let v = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        v
                    } else {
                        let l = lvl + scratch;
                        scratch += 1;
                        Val::vvar(l).into()
                    };
                    ty = infer.closure_apply(&cxt.decl, closure, u);
                }
                _ => {
                    break Self::unify_indices(infer, cxt, &sum_name, &head_params, &tyf, init_sub)
                        || infer.fuel_exhausted()
                }
            }
        };
        infer.meta = snap;
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子——嵌套位置的延迟探测在记账臂的 σ 之下解释方程，
    /// `unify_pm` 入口统一推开），弃掉即回滚。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        sum_name: &Span<SmolStr>,
        head_params: &[Rc<Val>],
        ret_ty: &Rc<Val>,
        init_sub: &Rc<Subst>,
    ) -> bool {
        let ret_sum = infer.force(&cxt.decl, &wrap_sub(init_sub, ret_ty.clone()));
        let rp = match ret_sum.as_ref() {
            Val::Sum(name, params, ..) if name.data == sum_name.data => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let mut spec = SpecSolve {
            acc: init_sub.clone(),
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
            if Self::probe_accessible(infer, cxt, cxt.lvl, &typ, ctor.data.as_str(), &Rc::new(Subst::default()))
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
            // 臂边界：本臂失败（走查错 / 特化冲突）时丢弃本臂的待提升记账
            // ——失败臂不产生覆盖义务（L07 荒谬臂语义：v3 钉；L12 的失败臂
            // 按 L11 口径静默跳过，义务同样不产生）。
            let pending_before = std::mem::take(&mut self.pending_pos);
            self.cur_path.clear();
            let (detail, cxt_walk) = match walk_pat(infer, self, cxt, pat, &typ) {
                Ok(x) => x,
                Err(_) => {
                    self.pending_pos = pending_before;
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma)) =
                infer.check_pm_final(&cxt_walk, raw, typ.clone(), target_val.clone())
            else {
                self.pending_pos = pending_before;
                continue;
            };
            // 嵌套位置结算（两段式，L07 同款）：此刻本臂全部特化方程已解出、
            // σ 为终态，字段 Sum 置于 σ 之下再探测才能看到索引精化（如
            // `Vec[A] (succ n)` 的尾部上 `nil` 不可达）。
            for (path, field_sum) in std::mem::take(&mut self.pending_pos) {
                self.nested_checks.push(NestedCheck {
                    path,
                    field_sum,
                    sub: sigma.clone(),
                    lvl: cxt_walk.lvl,
                });
            }
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
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，L07 同款）：每条记账在记录
        // 臂的实例化（σ/lvl 快照）下探测字段 Sum 的可达构造子；覆盖集 = 已
        // 走查臂的 PatternDetail 沿路径的结构贡献（var/Any = 全覆盖；祖先异
        // ctor = 不可达该位置；同 ctor 前缀 = 贡献其末端构造子）。可达集取
        // 各记账臂探测的并集（保守：任一臂实例化下可达的构造子都要求被覆
        // 盖）。失败臂 / 被遮蔽臂不在 pats 里，天然不贡献覆盖——与运行时
        // 首匹配结构语义一致。
        let mut reported = std::collections::HashSet::new();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force：索引精化（如尾部
            // 长度 l := succ n）在 σ 里，推开后的 Sum 才是探测该用的类型
            let field_sum = infer.force(&cxt.decl, &wrap_sub(&nc.sub, nc.field_sum.clone()));
            let cases = match field_sum.as_ref() {
                Val::Sum(_, _, cases, _) => cases.clone(),
                _ => continue,
            };
            for ctor in &cases {
                if !Self::probe_accessible(
                    infer,
                    cxt,
                    nc.lvl,
                    &field_sum,
                    ctor.data.as_str(),
                    &nc.sub,
                ) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    super::PosCover::All => true,
                    super::PosCover::Ctor(n) => n == ctor.data,
                    super::PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.data.clone())) {
                    self.warnings.push(Warning::UnmatchedAt(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        super::fmt_path(&nc.path),
                        ctor.data
                    )));
                }
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
///
/// `co`：编译器状态穿参——嵌套 Con 子模式处记一笔待提升的嵌套位置（该
/// 字段位置沿 ctor 路径的可达构造子必须有臂覆盖），`check_pm_final` 成功
/// 后以终态 σ 结算（见 `compile`，两段式）。`cur_path` 臂内 push/pop 平衡。
fn walk_pat(
    infer: &mut Infer,
    co: &mut Compiler,
    cxt: &Cxt,
    pat: &Pattern,
    head_ty: &Rc<Val>,
) -> Result<(PatternDetail, Cxt), Error> {
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
                                // 记一笔待提升的嵌套位置：字段 Sum 的可达构造子
                                // 必须被某臂在该位置覆盖。此处只记账（σ 尚未
                                // 解出——特化方程在 check_pm_final 里一次解
                                // 完），臂级成功后以终态 σ 提升（两段式）。
                                // 若字段并非和类型 / 子名非其构造子，walk_pat
                                // 回落 Bind/Err——Bind 在 cover_at 下全覆盖、
                                // Err 臂整体丢弃，均不产生假义务。
                                let field_sum = infer.force(&cxt.decl, &dom);
                                co.pending_pos.push((
                                    {
                                        let mut cp = co.cur_path.clone();
                                        cp.push((name.data.to_string(), details.len()));
                                        cp
                                    },
                                    field_sum,
                                ));
                                co.cur_path
                                    .push((name.data.to_string(), details.len()));
                                let walked = walk_pat(infer, co, &cxt_arm, p, &dom);
                                co.cur_path.pop();
                                let (d, c2) = walked?;
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
