//! compiler：模式匹配编译（参考版 pattern_match.rs 的逐句移植）——
//! `Compiler`/`Warning`/`NestedCheck`、覆盖与可达性（`covers`/`is_catch_all`/
//! `sum_case_names`/`probe_accessible`/`unify_indices`）、下钻 `walk_pat`。原
//! bump_spine_iter.rs 的 "模式匹配编译" 节 + 文件尾 sum_case_names/covers/
//! is_catch_all/walk_pat 段，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashSet;
use std::rc::Rc;

use super::parser::syntax::{Icit, Pattern, Raw};
use super::{cover_at, empty_span, fmt_path, Error, PatternDetail, PosCover};
use crate::parser_lib::ToSpan;

use super::env::env_ext;
use super::force::{pm_fuel_exhausted, refuel};
use super::machine::{clone_cxt, subst_cxt, Cxt, Machine};
use super::spine::is_flex;
use super::subst::{wrap_sub, SpecSolve, SubstV};
use super::syntax::{Tm, V, XCell, v_lvl, v_pi_of, v_tag, v_xcell_of};

// 模式匹配编译（参考版 pattern_match.rs 的逐句移植）
// --------------------------------------------------------------------------------

type Var = i32;

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套模式位置缺覆盖（2026-09-18 评审修复，与参考版同款）：携带已
    /// 格式化的完整文案（`match 不完整：模式位置 {fmt_path} 缺少构造子
    /// {ctor}`），两版共用 mod.rs 的 fmt_path 保证逐字节一致。
    Nested(String),
}

pub(crate) struct Compiler<'a> {
    pub(super) warnings: Vec<Warning>,
    pub(crate) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    ret_type: V,
    /// 嵌套覆盖检查的记账（参考版同款，2026-09-18）：顶层覆盖检查只遍历
    /// scrutinee 类型的构造子；嵌套 `Con` 字段位置的可达性也要枚举，否则
    /// 非穷尽 match 被静默接受（P0）。两段式：走查中只记节点方程（见
    /// [`PendingNode`]）；特化方程**成功后**（σ 为终态）才逐节点解槽位
    /// 方程、提升为带 σ/lvl 快照的完整记账。方程失败的荒谬臂丢弃记账。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待结算节点（特化方程成功后结算；根节点在前、嵌套节点
    /// 按下钻序——父先于子，槽位解逐层传递）。
    pending_pos: Vec<PendingNode>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 走查中的一个 Con 节点方程（参考版 `PendingNode` 同构）：`head` = 该
/// 节点的头部 Sum 值，`ret` = 构造子返回类型以**走查槽位 rigid** 实例化
/// 的结果。结算时对 `head.params ≐ ret.params` 逐槽跑 `unify_pm`（裸槽
/// rigid 可解入 σ）——L11 的臂特化方程走 raw 侧的 meta 间接，走查槽位不
/// 在其解里，必须由本方程把索引精化落到槽位上。`path` = Some(路径) 时该
/// 节点同时是一个嵌套覆盖义务位置（字段 Sum 即 `head`）；None = 根节点。
struct PendingNode {
    path: Option<Vec<(String, usize)>>,
    head: V,
    ret: V,
}

/// 一个嵌套拆分位置的记账（参考版 `NestedCheck` 同构）：路径 = 根到被拆
/// 字段的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂走查下的
/// Sum 值；σ/lvl 是记录臂特化方程终态的快照。
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
    /// `lvl` 显式穿参（L07 同款）：顶层探测传入口 `cxt.lvl`；嵌套位置的延迟
    /// 探测传记账时的臂内层级（scratch 层级必须落在该臂全部真槽之外）。
    /// `init_sub`：记账臂的终态 σ（顶层探测为空）——方程两侧经 `unify_pm`
    /// 在 acc 之下解释，索引精化对探测可见。
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
            let tyf = mach.force_v(bump, cxt, ty);
            if v_tag(tyf) != 4 {
                break Self::unify_indices(mach, bump, cxt, lvl, sum_name, &head_params, tyf, init_sub);
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
        // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理（保守地要求
        // 覆盖，2026-09-18 评审修复，参考版同款）。反方向（判不可达 → 覆盖
        // 检查放过该构造子）会让深负载下的非穷尽 match 被静默接受。
        ok || pm_fuel_exhausted()
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子），弃掉即回滚。`lvl` 显式穿参见 `probe_accessible`。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        lvl: u32,
        sum_name: &'a str,
        head_params: &[V],
        ret_ty: V,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let ret_sum = mach.force_v(bump, cxt, ret_ty);
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
            if mach.unify_pm(bump, cxt, lvl, *a, b.val, &span, &mut spec).is_err() {
                return false;
            }
        }
        true
    }

    /// 节点槽位方程（结算期，参考版 `node_indices` 同构）：`head.params ≐
    /// ret.params` 逐槽经 `unify_pm` 解入 `spec.acc`（走查槽位是裸 rigid，
    /// 可解——见 `PendingNode` 文档）。单槽失败不阻断后续槽：个别槽失败
    /// 只损失该槽的精化，覆盖检查按保守可达处理。
    fn node_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        lvl: u32,
        head_sum: V,
        ret_ty: V,
        spec: &mut SpecSolve,
    ) {
        let head_f = mach.force_v(bump, cxt, head_sum);
        let (sum_name, head_params) = match v_xcell_of(head_f) {
            XCell::Sum { name, params, .. } if v_tag(head_f) == 7 => (*name, params.to_vec()),
            _ => return,
        };
        let ret_f = mach.force_v(bump, cxt, ret_ty);
        let rp = match v_xcell_of(ret_f) {
            XCell::Sum { name, params, .. } if v_tag(ret_f) == 7 && *name == sum_name => {
                params.to_vec()
            }
            _ => return,
        };
        let span = empty_span(());
        for (a, b) in head_params.iter().zip(rp.iter()) {
            let _ = mach.unify_pm(bump, cxt, lvl, a.val, b.val, &span, spec);
        }
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；参考版同款）。
    ///
    /// 语义相对决策树的两处（与参考版一致，见 `pattern_match.rs` 同名注释）：
    /// ①遮蔽只认通配臂（`is_catch_all` 之后的臂报 `Unreachable`）；
    /// ②特化方程失败的臂静默跳过（不进 pats、不告警）。
    /// 嵌套覆盖检查（2026-09-18 评审修复，P0，参考版同款）：走查中沿模式
    /// 下钻逐节点记账，方程成功后以终态 σ 结算（两段式）；臂循环后按记账
    /// 快照探测字段 Sum 的可达构造子，覆盖集沿路径结构求出，缺失报
    /// `Nested`（文案与参考版逐字节一致）。
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
        let (constrs, ctor_names): (Vec<crate::parser_lib::Span<String>>, Vec<String>) =
            match v_xcell_of(typ) {
                XCell::Sum { cases, .. } if v_tag(typ) == 7 => (
                    cases.iter().map(|c| empty_span(c.to_string())).collect(),
                    cases.iter().map(|c| c.to_string()).collect(),
                ),
                _ => (vec![], vec![]),
            };
        // 覆盖检查：可达且无臂覆盖 → Unmatched（探测失败按"无结论"处理）。
        // 不可达（如 `Vec[A] zero` 上的 `cons`）不报——索引方程不可解即结构
        // 上不可能出现。
        for ctor in &constrs {
            if Self::probe_accessible(mach, bump, cxt, cxt.lvl, typ, ctor.data.as_str(), &Rc::new(SubstV::default()))
                && !arms
                    .iter()
                    .any(|(pat, _)| covers(pat, ctor.data.as_str(), &ctor_names))
            {
                self.warnings.push(Warning::Unmatched(Pattern::Con(
                    ctor.clone(),
                    vec![Pattern::Any(empty_span(false), Icit::Expl); 999],
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
            self.cur_path.clear();
            let walked =
                walk_pat(mach, bump, cxt, pat, typ, &mut self.pending_pos, &mut self.cur_path);
            let (detail, cxt_walk) = match walked {
                Ok(x) => x,
                Err(_) => {
                    // 结构冲突臂：不进 pats、不告警；其嵌套位置不产生
                    // 覆盖义务
                    self.pending_pos.clear();
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma)) = mach.check_pm_final(bump, &cxt_walk, &raw, typ, target_val)
            else {
                // 特化方程失败 = 臂不可达：嵌套位置不产生覆盖义务
                self.pending_pos.clear();
                continue;
            };
            // 嵌套位置结算（两段式，参考版同款）：先逐节点把槽位方程解进
            // σ（根在前——外层索引精化先落槽），再把有路径的节点提升为带
            // σ/lvl 快照的完整记账。
            let nodes = std::mem::take(&mut self.pending_pos);
            if nodes.iter().any(|n| n.path.is_some()) {
                let mut sigma_acc = sigma.clone();
                for node in &nodes {
                    let mut spec = SpecSolve {
                        acc: sigma_acc.clone(),
                    };
                    Self::node_indices(mach, bump, cxt, cxt_walk.lvl, node.head, node.ret, &mut spec);
                    sigma_acc = spec.acc;
                }
                for node in nodes {
                    if let Some(path) = node.path {
                        self.nested_checks.push(NestedCheck {
                            path,
                            field_sum: node.head,
                            sub: sigma_acc.clone(),
                            lvl: cxt_walk.lvl,
                        });
                    }
                }
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
        // = 已走查臂的 PatternDetail 沿路径的结构贡献（var/Any = 全覆盖；
        // 祖先异 ctor = 不可达该位置；同 ctor 前缀 = 贡献其末端构造子）。
        // 荒谬臂 / 被遮蔽臂不在 pats 里，天然不贡献覆盖。可达集取各记账臂
        // 探测的并集（保守）。
        let mut reported: FxHashSet<(Vec<(String, usize)>, String)> = FxHashSet::default();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force（参考版同款）
            let field_sum = mach.force_v(bump, cxt, wrap_sub(bump, &nc.sub, nc.field_sum));
            if !(v_tag(field_sum) == 7 && matches!(v_xcell_of(field_sum), XCell::Sum { .. })) {
                continue;
            }
            for ctor in sum_case_names(field_sum) {
                if !Self::probe_accessible(mach, bump, cxt, nc.lvl, field_sum, &ctor, &nc.sub) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    PosCover::All => true,
                    PosCover::Ctor(n) => n == ctor,
                    PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.clone())) {
                    self.warnings.push(Warning::Nested(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        fmt_path(&nc.path),
                        ctor
                    )));
                }
            }
        }
        self.warnings = unreachable.into_iter().chain(self.warnings.drain(..)).collect();
        Ok(())
    }
}
/// `Sum` 值的构造子名表（覆盖检查用；参考版 probe/覆盖循环同款取法）。
fn sum_case_names(v: V) -> Vec<String> {
    match v_xcell_of(v) {
        XCell::Sum { cases, .. } => cases.iter().map(|c| c.to_string()).collect(),
        _ => Vec::new(),
    }
}

/// 臂是否（结构上）覆盖构造子 `ctor`（参考版 `covers` 同款）。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c == name.data.as_str()) || name.data.as_str() == ctor
        }
    }
}

/// 通配臂（参考版 `is_catch_all` 同款）：其后的臂不可达。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == name.data.as_str())
        }
    }
}

/// 模式走查（L07 `walk`/`walk_con` 口径；参考版 `walk_pat` 的快版）：
/// 绑定模式变量槽并构建运行时 `PatternDetail`。槽位纪律见参考版同名注释：
/// 枚举隐式参数不占槽、构造子隐式绑定器补虚通配、变量模式以用户名绑槽、
/// **Con 本身不占槽**。
///
/// 嵌套覆盖记账（2026-09-18 评审修复，参考版同款）：子模式是 Con 且字段
/// 类型是含该构造子的 Sum 时，沿 `cur_path` 下钻（父 push、子 pop 平衡）；
/// 每个 Con 节点把自己的 (头部 Sum, 槽位实例化的返回类型) 记入 `pending`
/// ——臂的特化方程成功后由 `compile` 逐节点解槽位方程并以终态 σ 结算。
fn walk_pat<'a>(
    mach: &mut Machine,
    bump: &'a Bump,
    cxt: &Cxt<'a>,
    pat: &Pattern,
    head_ty: V,
    pending: &mut Vec<PendingNode>,
    cur_path: &mut Vec<(String, usize)>,
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
            let (sum_params, cases) = if is_sum {
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
                    ))));
                }
                let a_t = mach.quote(bump, cxt, cxt.lvl, head_ty);
                let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
                return Ok((PatternDetail::Bind(name.clone()), cxt2));
            }
            // L11 的构造子以**裸名**登记
            let entry_ty = match cxt.decls.get(name.data.as_str()) {
                Some(e) => e.vty,
                None => {
                    return Err(Error(name.clone().map(|n| format!("找不到构造子 {}", n))))
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
                        .filter(|p| p.get_icit() == Icit::Impl)
                        .copied(),
                    Icit::Expl => match sub_queue.first() {
                        Some(p) if p.get_icit() == Icit::Expl => Some(*p),
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
                        // 嵌套 Con：字段类型是含该构造子的 Sum → 沿路径
                        // 下钻（节点方程由子节点在 Con 分支末尾自行记账）
                        let nested_name = match p {
                            Pattern::Con(cn, _, _) => cn.data.clone(),
                            _ => unreachable!(),
                        };
                        let field_sum = mach.force_v(bump, &cxt_arm, dom);
                        let is_ctor = v_tag(field_sum) == 7
                            && matches!(v_xcell_of(field_sum), XCell::Sum { cases, .. }
                                if cases.iter().any(|c| *c == nested_name));
                        if is_ctor {
                            cur_path.push((name.data.clone(), details.len()));
                        }
                        let walked =
                            walk_pat(mach, bump, &cxt_arm, p, dom, pending, cur_path);
                        if is_ctor {
                            cur_path.pop();
                        }
                        let (d, c2) = walked?;
                        cxt_arm = c2;
                        d
                    }
                };
                details.push(detail);
                let env = env_ext(bump, env0, u);
                ty = mach.eval(bump, &cxt_arm, env, body);
            }
            // 节点记账（参考版同款）：头部 Sum + 以走查槽位实例化的返回
            // 类型。cur_path 非空 = 嵌套字段位置（同时产生覆盖义务）。
            let ret_sum = mach.force_v(bump, &cxt_arm, ty);
            let my_path = if cur_path.is_empty() {
                None
            } else {
                Some(cur_path.clone())
            };
            pending.push(PendingNode {
                path: my_path,
                head: head_sum,
                ret: ret_sum,
            });
            Ok((PatternDetail::Con(name.clone(), details), cxt_arm))
        }
    }
}
