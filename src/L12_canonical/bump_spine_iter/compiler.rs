//! compiler：模式匹配编译（`Compiler`/`Warning` + probe_accessible/
//! unify_indices/嵌套覆盖两段式 + covers/is_catch_all/walk_pat——后三者
//! 原文件位于 bench 生成器节尾，按内容归属）。原 bump_spine_iter.rs 的
//! "模式匹配编译" 节及上述内容段，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use smol_str::SmolStr;
use std::rc::Rc;

use super::parser::syntax::{Either, Icit, Pattern, Raw};
use super::{cover_at, empty_span, Error, PatternDetail};
use crate::parser_lib::ToSpan;

use super::env::env_ext;
use super::force::{fuel_exhausted, refuel};
use super::machine::{clone_cxt, subst_cxt, Cxt, Machine};
use super::spine::is_flex;
use super::subst::{wrap_sub, SpecSolve, SubstV};
use super::syntax::{
    SumParamV, Tm, V, XCell, v_lvl, v_pi_of, v_tag, v_xcell_of,
};

// 模式匹配编译（参考版 pattern_match.rs 的逐句移植）
// --------------------------------------------------------------------------------

type Var = i32;

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（参考版 pattern_match.rs `UnmatchedAt` 同款）：
    /// 完整报错文案直营，Debug 输出两侧逐字节一致。
    UnmatchedAt(String),
}

pub(crate) struct Compiler<'a> {
    pub(super) warnings: Vec<Warning>,
    pub(crate) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    ret_type: V,
    /// 嵌套覆盖检查的记账（参考版 pattern_match.rs 同款前向传播）：两段式
    /// ——走查中只记 (路径, 字段 Sum)；`check_pm_final` 成功后（σ 终态）
    /// 才提升为带 σ/lvl 快照的完整记账。臂失败时丢弃（失败臂不产生覆盖
    /// 义务）。L12 无 solvable 白名单（任意裸 Rigid 可解），记账少一项。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待提升位置（臂边界结算）。
    pending_pos: Vec<(Vec<(String, usize)>, V)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账（参考版 `NestedCheck` 同构）：路径 = 根到被拆
/// 字段的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂实例化下的
/// Sum 值；σ/lvl 是记账时刻（该臂 `check_pm_final` 成功后）的走查快照。
struct NestedCheck {
    path: Vec<(String, usize)>,
    field_sum: V,
    sub: Rc<SubstV>,
    lvl: u32,
}

impl<'a> Compiler<'a> {
    pub(super) fn new(ret_type: V) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
        }
    }

    /// 构造子可达性探测（值级，L07 孪生 `probe_accessible` 口径）：直接读
    /// decls 表取构造子类型值，走 Π 链实例化——枚举隐式参数用头部 Sum 的实参，
    /// 其余绑定器用超出上下文的 scratch 层 fresh rigid（同为刚性，可被方程解
    /// 出；探测状态全在本地，弃掉即回滚），返回类型再与头部跑一次索引方程。
    /// 成功 = 该构造子可能出现在头部类型的值里；结构冲突（`Vec[A] zero` 上
    /// 不可能有 `cons`）= absurd。
    /// `lvl` 显式穿参（参考版同款）：顶层探测传入口 `cxt.lvl`；嵌套位置的
    /// 延迟探测传记账时的臂内层级——scratch 层级必须落在该臂全部真槽之外。
    fn probe_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        lvl: u32,
        head_sum: V,
        ctor: &str,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let (sum_name, head_params, impl_vals) = match v_xcell_of(head_sum) {
            XCell::Sum { name, params, .. } => (
                *name,
                params.iter().map(|p| p.val).collect::<Vec<_>>(),
                params
                    .iter()
                    .filter(|p| p.icit == Icit::Impl)
                    .map(|p| p.val)
                    .collect::<Vec<_>>(),
            ),
            _ => return false,
        };
        let entry_ty = match cxt.decls.get(ctor) {
            Some(e) => e.vty,
            None => return false,
        };
        // 每个探测独立充值（参考版 probe_accessible 同点）：多构造子枚举
        // 的逐 ctor 探测不互相挤占共享池，避免后探的 ctor 假 absurd。
        refuel();
        let snap = mach.metas.clone();
        let mut ty = entry_ty;
        let mut impl_idx = 0;
        let mut scratch = 0u32;
        let ok = loop {
            let tyf = mach.force_v(bump, cxt, wrap_sub(bump, init_sub, ty));
            if v_tag(tyf) != 4 {
                break Self::unify_indices(mach, bump, cxt, sum_name, &head_params, tyf, init_sub)
                    || fuel_exhausted();
            }
            let p = v_pi_of(tyf);
            let u = if impl_idx < impl_vals.len() {
                let v = impl_vals[impl_idx];
                impl_idx += 1;
                v
            } else {
                let l = lvl + scratch;
                scratch += 1;
                v_lvl(l)
            };
            let env = env_ext(bump, p.env, u);
            ty = mach.eval(bump, cxt, env, p.body);
        };
        mach.metas = snap;
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子——嵌套位置的延迟探测在记账臂的 σ 之下解释方程，
    /// `unify_pm` 入口统一推开），弃掉即回滚。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        sum_name: &'a str,
        head_params: &[V],
        ret_ty: V,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let ret_sum = mach.force_v(bump, cxt, wrap_sub(bump, init_sub, ret_ty));
        let rp = match v_xcell_of(ret_sum) {
            XCell::Sum { name, params, .. } if *name == sum_name => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let span = empty_span(());
        let mut spec = SpecSolve {
            acc: init_sub.clone(),
        };
        for (a, b) in head_params.iter().zip(rp.iter()) {
            if mach.unify_pm(bump, cxt, *a, b.val, &span, &mut spec).is_err() {
                return false;
            }
        }
        true
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；L11 同款）。
    pub(super) fn compile(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        typ: V,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt<'a>,
        target_val: V,
    ) -> Result<(), Error> {
        self.warnings = Vec::new();
        let typ = mach.force_v(bump, cxt, typ);
        let (constrs, ctor_names): (Vec<crate::parser_lib::Span<SmolStr>>, Vec<SmolStr>) =
            if v_tag(typ) == 7 {
                match v_xcell_of(typ) {
                    XCell::Sum { cases, .. } => (
                        cases.iter().map(|c| empty_span(SmolStr::new(*c)))
                            .collect(),
                        cases.iter().map(|c| SmolStr::new(*c)).collect(),
                    ),
                    _ => (vec![], vec![]),
                }
            } else {
                (vec![], vec![])
            };
        // 覆盖检查：可达且无臂覆盖 → Unmatched（探测失败按"无结论"处理）。
        // 不可达（如 `Vec[A] zero` 上的 `cons`）不报——索引方程不可解即结构
        // 上不可能出现。
        for ctor in &constrs {
            if Self::probe_accessible(
                mach,
                bump,
                cxt,
                cxt.lvl,
                typ,
                ctor.data.as_str(),
                &Rc::new(SubstV::default()),
            ) && !arms
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
            // ——失败臂不产生覆盖义务（参考版同款；L12 的失败臂按 L11 口径
            // 静默跳过，义务同样不产生）。
            let pending_before = std::mem::take(&mut self.pending_pos);
            self.cur_path.clear();
            let (detail, cxt_walk) = match walk_pat(mach, bump, self, cxt, pat, typ) {
                Ok(x) => x,
                Err(_) => {
                    self.pending_pos = pending_before;
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma)) = mach.check_pm_final(bump, &cxt_walk, &raw, typ, target_val)
            else {
                self.pending_pos = pending_before;
                continue;
            };
            // 嵌套位置结算（两段式，参考版同款）：此刻本臂全部特化方程已解
            // 出、σ 为终态，字段 Sum 置于 σ 之下再探测才能看到索引精化。
            for (path, field_sum) in std::mem::take(&mut self.pending_pos) {
                self.nested_checks.push(NestedCheck {
                    path,
                    field_sum,
                    sub: sigma.clone(),
                    lvl: cxt_walk.lvl,
                });
            }
            let cxt_arm = subst_cxt(bump, &mach.defs, &sigma, &cxt_walk);
            let ret_type = {
                let t = mach.force_v(bump, &cxt_arm, self.ret_type);
                if is_flex(&mach.spine, t) {
                    t
                } else {
                    let tm = mach.quote(bump, &cxt_arm, cxt_arm.lvl, t);
                    mach.eval(bump, &cxt_arm, cxt_arm.env, tm)
                }
            };
            let ret = mach.check(bump, &cxt_arm, body, ret_type)?;
            self.pats.push((detail, ret));
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，参考版同款）：每条记账在
        // 记录臂的实例化（σ/lvl 快照）下探测字段 Sum 的可达构造子；覆盖集
        // = 已走查臂的 PatternDetail 沿路径的结构贡献。失败臂 / 被遮蔽臂
        // 不在 pats 里，天然不贡献覆盖——与运行时首匹配结构语义一致。
        let mut reported = std::collections::HashSet::new();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force（参考版同款）
            let field_sum = mach.force_v(bump, cxt, wrap_sub(bump, &nc.sub, nc.field_sum));
            let cases: Vec<&str> = if v_tag(field_sum) == 7 {
                match v_xcell_of(field_sum) {
                    XCell::Sum { cases, .. } => cases.to_vec(),
                    _ => continue,
                }
            } else {
                continue;
            };
            for ctor in &cases {
                if !Self::probe_accessible(mach, bump, cxt, nc.lvl, field_sum, ctor, &nc.sub) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    super::PosCover::All => true,
                    super::PosCover::Ctor(n) => n.as_str() == *ctor,
                    super::PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), SmolStr::new(*ctor))) {
                    self.warnings.push(Warning::UnmatchedAt(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        super::fmt_path(&nc.path),
                        ctor
                    )));
                }
            }
        }
        self.warnings = unreachable.into_iter().chain(self.warnings.drain(..)).collect();
        Ok(())
    }
}
/// 臂是否（结构上）覆盖构造子 `ctor`（参考版 `covers` 同款）。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[SmolStr]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c.as_str() == name.data.as_str())
                || name.data.as_str() == ctor
        }
    }
}

/// 通配臂（参考版 `is_catch_all` 同款）。
fn is_catch_all(pat: &Pattern, ctor_names: &[SmolStr]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c.as_str() == name.data.as_str())
        }
    }
}

/// 模式走查（L07 `walk_con` 口径；参考版 `walk_pat` 的快版）：绑定模式变量槽
/// 并构建运行时 `PatternDetail`。槽位纪律见参考版同名注释。
///
/// `co`：编译器状态穿参——嵌套 Con 子模式处记一笔待提升的嵌套位置，
/// `check_pm_final` 成功后以终态 σ 结算（两段式，参考版同款）。
fn walk_pat<'a>(
    mach: &mut Machine,
    bump: &'a Bump,
    co: &mut Compiler<'a>,
    cxt: &Cxt<'a>,
    pat: &Pattern,
    head_ty: V,
) -> Result<(PatternDetail, Cxt<'a>), Error> {
    match pat {
        Pattern::Any(span, _) => {
            let a_t = mach.quote(bump, cxt, cxt.lvl, head_ty);
            let cxt2 = mach.bind_name(bump, cxt, "_", a_t, head_ty);
            Ok((PatternDetail::Any(span.to_span()), cxt2))
        }
        Pattern::Con(name, subs, _) => {
            let head_sum = mach.force_v(bump, cxt, head_ty);
            let is_sum = v_tag(head_sum) == 7;
            let (sum_params, cases): (Vec<SumParamV<'a>>, Vec<&'a str>) = if is_sum {
                match v_xcell_of(head_sum) {
                    XCell::Sum { params, cases, .. } => (params.to_vec(), cases.to_vec()),
                    _ => (vec![], vec![]),
                }
            } else {
                (vec![], vec![])
            };
            if !is_sum || !cases.iter().any(|c| *c == name.data.as_str()) {
                if !subs.is_empty() {
                    return Err(Error(name.clone().map(|n| format!(
                        "`{n}` 不是构造子，不能带子模式解构"
                    )), vec![]));
                }
                let a_t = mach.quote(bump, cxt, cxt.lvl, head_ty);
                let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
                return Ok((PatternDetail::Bind(name.clone()), cxt2));
            }
            // L12 的构造子以**裸名**登记
            let entry_ty = match cxt.decls.get(name.data.as_str()) {
                Some(e) => e.vty,
                None => {
                    return Err(Error(
                        name.clone().map(|n| format!("找不到构造子 {}", n)),
                        vec![],
                    ))
                }
            };
            let mut impl_vals: Vec<V> = sum_params
                .iter()
                .filter(|p| p.icit == Icit::Impl)
                .map(|p| p.val)
                .collect();
            impl_vals.reverse();
            let mut ty = entry_ty;
            let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
            let mut details: Vec<PatternDetail> = Vec::new();
            let mut cxt_arm = clone_cxt(cxt);
            loop {
                let tyf = mach.force_v(bump, &cxt_arm, ty);
                if v_tag(tyf) != 4 {
                    break;
                }
                let cell = v_pi_of(tyf);
                let (bname, bicit, dom, body, env0) =
                    (cell.name, cell.icit, cell.dom, cell.body, cell.env);
                if let Some(v) = impl_vals.pop() {
                    let env = env_ext(bump, env0, v);
                    ty = mach.eval(bump, &cxt_arm, env, body);
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
                let u = v_lvl(cxt_arm.lvl);
                let detail = match sub {
                    None => {
                        let b = format!("_{}", bname);
                        let d_t = mach.quote(bump, &cxt_arm, cxt_arm.lvl, dom);
                        cxt_arm = mach.bind_name(bump, &cxt_arm, &b, d_t, dom);
                        PatternDetail::Any(empty_span(()))
                    }
                    Some(Pattern::Any(span, _)) => {
                        sub_queue.remove(0);
                        let b = format!("_{}", bname);
                        let d_t = mach.quote(bump, &cxt_arm, cxt_arm.lvl, dom);
                        cxt_arm = mach.bind_name(bump, &cxt_arm, &b, d_t, dom);
                        PatternDetail::Any(span.to_span())
                    }
                    Some(p @ Pattern::Con(..)) => {
                        sub_queue.remove(0);
                        // 记一笔待提升的嵌套位置（参考版同款）：字段 Sum 的
                        // 可达构造子必须被某臂在该位置覆盖。此处只记账，臂级
                        // 成功后以终态 σ 提升（两段式）。字段非和类型 / 子名
                        // 非其构造子时 walk_pat 回落 Bind/Err——Bind 在
                        // cover_at 下全覆盖、Err 臂整体丢弃，均无假义务。
                        let field_sum = mach.force_v(bump, &cxt_arm, dom);
                        co.pending_pos.push((
                            {
                                let mut cp = co.cur_path.clone();
                                cp.push((name.data.to_string(), details.len()));
                                cp
                            },
                            field_sum,
                        ));
                        co.cur_path.push((name.data.to_string(), details.len()));
                        let walked = walk_pat(mach, bump, co, &cxt_arm, p, dom);
                        co.cur_path.pop();
                        let (d, c2) = walked?;
                        cxt_arm = c2;
                        d
                    }
                };
                details.push(detail);
                let env = env_ext(bump, env0, u);
                ty = mach.eval(bump, &cxt_arm, env, body);
            }
            Ok((PatternDetail::Con(name.clone(), details), cxt_arm))
        }
    }
}
