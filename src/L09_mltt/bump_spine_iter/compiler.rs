//! compiler：模式匹配编译（`Compiler`/`Warning`，2026-09-18 起 L07 逐臂下钻
//! 款：特化合一 + 覆盖探测 `covers`/`is_catch_all`）。原 bump_spine_iter.rs
//! 的 "模式匹配编译" 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashSet;
use std::rc::Rc;

use super::parser::syntax::{Icit, Pattern, Raw};
use super::{Error, PatternDetail, PosCover, cover_at, empty_span, fmt_path};

use super::env::env_ext;
use super::force::{fuel_exhausted, refuel};
use super::machine::{Cxt, Machine, clone_cxt};
use super::spine::is_flex;
use super::subst::{SpecSolve, SubstV, wrap_sub};
use super::syntax::{SumParamV, Tm, V, XCell, v_lvl, v_pi_of, v_tag, v_xcell_of};

// 模式匹配编译（2026-09-18 自决策树矩阵重写为 L07 逐臂下钻；L10-L12 同款，
// 参考版 pattern_match.rs 同步替换）
// --------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（L07 同文案：`match 不完整：模式位置 {path} 缺少
    /// 构造子 {ctor}`；2026-09-18 评审修复 P0 的 L09 移植——文案与参考版
    /// 逐字一致，parity 按 Debug 形态比对）。
    IncompleteNested(String),
}

pub(crate) struct Compiler<'a> {
    pub(super) warnings: Vec<Warning>,
    pub(crate) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    ret_type: V,
    /// 嵌套覆盖检查的记账（走查中收集，臂循环结束后统一探测；L07 同款，
    /// 2026-09-18 评审修复 P0 的 L09 移植）。两段式：走查中只记
    /// (路径, 字段 Sum, 本层 ret)；本臂特化方程**解出后**（σ 为终态）才
    /// 提升为完整记账——字段走查时索引精化不在 σ 里，此时探测会把已精
    /// 化下不可达的构造子误判可达。整臂特化失败（荒谬臂，静默跳过）时
    /// 丢弃记账。
    nested_checks: Vec<NestedCheck<'a>>,
    /// 本臂走查中的待提升位置（结算方程成功后提升）。`ret` 是该层 Con 的
    /// 走查返回类型（槽位刚性即本层走查变量）。
    pending_pos: Vec<(Vec<(String, usize)>, V, V)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账（参考版 `NestedCheck` 同构）：路径 = 根到被拆
/// 字段的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂实例化下
/// 的 Sum 值；`cxt` 是臂走查上下文快照（探测的 scratch 层级须落在该臂
/// 全部真槽之外，spec_refine 的 `x >= cxt.lvl` 守卫以臂内层级为准）；
/// `sub` 是臂终态的精化替换（延迟探测要在与臂内方程同构的状态下跑）。
struct NestedCheck<'a> {
    path: Vec<(String, usize)>,
    field_sum: V,
    cxt: Cxt<'a>,
    sub: Rc<SubstV>,
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

    /// 构造子可达性探测（值级，L07 `probe_accessible` 口径；参考版同款）：
    /// Π 链上枚举隐式参数用头部 Sum 的实参实例化，其余绑定器用超出上下文的
    /// scratch 层 fresh rigid（同为刚性，可被方程解出；探测状态全在本地，
    /// 弃掉即回滚），返回类型再与头部类型跑一次索引方程。成功 = 该构造子
    /// 可能出现在头部类型的值里；结构冲突（`Vec[A] zero` 上不可能有
    /// `cons`）= absurd。构造子类型经 `infer_expr(Var(名))` 取（L09 的全局
    /// 表按层级存，无名字键的 decl 表——树同款）。
    ///
    /// `init_sub` 显式穿参（参考版同款，2026-09-18 评审修复 2/5 的 L09
    /// 移植）：顶层探测传空 σ；嵌套位置的延迟探测传记账时的臂内终态 σ，
    /// 并传臂走查上下文（bind_slots / lvl / 名字表均为臂内的）。方程两侧
    /// 由 unify_pm 入口置于 acc 之下解释。
    fn probe_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        head_sum: V,
        ctor: &crate::parser_lib::Span<String>,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let (sum_name, head_params, impl_vals) = {
            let f = mach.force_v(bump, head_sum);
            if v_tag(f) != 7 {
                return false;
            }
            match v_xcell_of(f) {
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
            }
        };
        // 逐构造子可达性探测是**纯探测**：infer_expr 与特化方程都可能分配/
        // 解掉 meta，探测期状态无需存活（本函数只带出布尔）。统一走
        // `run_pure_probe` 的 metas 快照换入换出（参考版 meta 快照同款机制）。
        mach.run_pure_probe(|mach| {
            // 每个探测独立充值：多构造子枚举的逐 ctor 探测不互相挤占共享池
            // （探测本身回滚，只有燃料单向消耗）。
            refuel();
            let (_, mut ty) = match mach.infer_expr(bump, cxt, &Raw::Var(ctor.clone())) {
                Ok(x) => x,
                Err(_) => return false,
            };
            let mut impl_idx = 0;
            let mut scratch = 0u32;
            loop {
                let tyf = mach.force_v(bump, ty);
                if v_tag(tyf) != 4 {
                    // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理
                    // （保守地要求覆盖）。反方向（判不可达 → 覆盖检查放
                    // 过该构造子）会让深负载下的非穷尽 match 被静默接受。
                    // 参考版 probe_accessible 同点。
                    break Self::unify_indices(mach, bump, cxt, sum_name, &head_params, tyf, init_sub)
                        || fuel_exhausted();
                }
                let p = v_pi_of(tyf);
                let u = if impl_idx < impl_vals.len() {
                    let v = impl_vals[impl_idx];
                    impl_idx += 1;
                    v
                } else {
                    let l = cxt.lvl + scratch;
                    scratch += 1;
                    v_lvl(l)
                };
                let env = env_ext(bump, p.env, u);
                ty = mach.eval(bump, env, p.body);
            }
        })
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子），弃掉即回滚。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        sum_name: &str,
        head_params: &[V],
        ret_ty: V,
        init_sub: &Rc<SubstV>,
    ) -> bool {
        let ret_sum = mach.force_v(bump, ret_ty);
        if v_tag(ret_sum) != 7 {
            return false;
        }
        let rp = match v_xcell_of(ret_sum) {
            XCell::Sum { name, params, .. } if *name == sum_name => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let span = empty_span(());
        let solvable = mach.bind_slots(cxt);
        let mut spec = SpecSolve {
            solvable: &solvable,
            acc: init_sub.clone(),
        };
        for (a, b) in head_params.iter().zip(rp.iter()) {
            if mach.unify_pm(bump, cxt, *a, b.val, &span, &mut spec).is_err() {
                return false;
            }
        }
        true
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；L10-L12 同款）。
    /// L09 的机器 API 是"env 口径"（`force_v`/`quote`/`eval` 不带 cxt）。
    /// 语义相对决策树的三处收窄（覆盖含嵌套位置 / 遮蔽只认通配臂 / 特化
    /// 失败静默跳过）见 L11 README 与 docs/l09l13-match-compiler-analysis。
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
        self.nested_checks = Vec::new();
        self.pending_pos = Vec::new();
        self.cur_path = Vec::new();
        let typ = mach.force_v(bump, typ);
        let (constrs, ctor_names): (Vec<crate::parser_lib::Span<String>>, Vec<String>) =
            if v_tag(typ) == 7 {
                match v_xcell_of(typ) {
                    XCell::Sum { cases, .. } => (
                        cases.iter().map(|c| empty_span(c.to_string())).collect(),
                        cases.iter().map(|c| c.to_string()).collect(),
                    ),
                    _ => (vec![], vec![]),
                }
            } else {
                (vec![], vec![])
            };
        // 覆盖检查：可达且无臂覆盖 → Unmatched（「构造子 + 999 通配」形态，
        // 与参考版逐字一致）。不可达（如 `Vec[A] zero` 上的 `cons`）不报——
        // 索引方程不可解即结构上不可能出现。
        let empty_sub = Rc::new(SubstV::default());
        for ctor in &constrs {
            if Self::probe_accessible(mach, bump, cxt, typ, ctor, &empty_sub)
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
            let (detail, cxt_walk, top_ret) = match self.walk_pat(mach, bump, cxt, pat, typ) {
                Ok(x) => x,
                Err(_) => {
                    // 走查失败臂的嵌套记账一并丢弃
                    self.pending_pos.clear();
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma0)) = mach.check_pm_final(bump, &cxt_walk, &raw, typ, target_val)
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
            let solvable = mach.bind_slots(&cxt_walk);
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc: sigma0.clone(),
            };
            let span = empty_span(());
            let mut absurd = false;
            if let Some(top_ret) = top_ret {
                if mach
                    .unify_pm(bump, &cxt_walk, typ, top_ret, &span, &mut spec)
                    .is_err()
                {
                    absurd = true;
                }
            }
            if !absurd {
                for (_, field_sum, ret) in self.pending_pos.iter() {
                    if mach
                        .unify_pm(bump, &cxt_walk, *field_sum, *ret, &span, &mut spec)
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
                    cxt: clone_cxt(&cxt_walk),
                    sub: sigma.clone(),
                });
            }
            // 臂上下文置于精化 σ 之下（env 槽 + types + names.by_lvl 包
            // VSub；lvl/locals/pruning 不动——槽位布局永不漂移，读点 force
            // 推开）。
            let cxt_arm = mach.subst_cxt(bump, &sigma, &cxt_walk);
            // 期望类型重锚到臂上下文：quote → eval（flex 免锚）。σ 经臂上下文
            // 的 wrapped env 在 eval 读点生效，无需预先包裹。
            let ret_type = {
                let t = self.ret_type;
                if is_flex(&mach.spine, t) {
                    t
                } else {
                    let tm = mach.quote(bump, cxt_arm.lvl, t);
                    mach.eval(bump, cxt_arm.env, tm)
                }
            };
            let ret = mach.check(bump, &cxt_arm, body, ret_type)?;
            self.pats.push((detail, ret));
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        // 参考版 `unreachable.into_iter().chain(self.warnings)`——不可达警告在前
        self.warnings = unreachable.into_iter().chain(self.warnings.drain(..)).collect();
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，L07 同款，2026-09-18 评审
        // 修复 P0 的 L09 移植）：每条记账在记录臂的实例化（σ/臂上下文快照）
        // 下探测字段 Sum 的可达构造子；覆盖集 = 已走查臂的 PatternDetail
        // 沿路径的结构贡献（var/Any = 全覆盖；祖先异 ctor = 不可达该位置；
        // 同 ctor 前缀 = 贡献其末端构造子）。可达集取各记账臂探测的并集
        // （保守）。荒谬臂 / 被遮蔽臂不在 pats 里，天然不贡献覆盖——与运
        // 行时首匹配结构语义一致。
        let mut reported: FxHashSet<(Vec<(String, usize)>, String)> = FxHashSet::default();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force：索引精化（如尾部
            // 长度 l := succ n）在 σ 里，推开后的 Sum 才是探测该用的类型
            let field_sum = mach.force_v(bump, wrap_sub(bump, &nc.sub, nc.field_sum));
            if !(v_tag(field_sum) == 7 && matches!(v_xcell_of(field_sum), XCell::Sum { .. })) {
                continue;
            }
            let ctor_cases: Vec<crate::parser_lib::Span<String>> = match v_xcell_of(field_sum) {
                XCell::Sum { cases, .. } => {
                    cases.iter().map(|c| empty_span(c.to_string())).collect()
                }
                _ => continue,
            };
            for ctor in ctor_cases {
                if !Self::probe_accessible(mach, bump, &nc.cxt, field_sum, &ctor, &nc.sub) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    PosCover::All => true,
                    PosCover::Ctor(n) => n == ctor.data,
                    PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.data.clone())) {
                    self.warnings.push(Warning::IncompleteNested(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        fmt_path(&nc.path),
                        ctor.data
                    )));
                }
            }
        }
        Ok(())
    }

    /// 模式走查（L07 `walk_con` 口径；参考版 `walk_pat` 的快版）：绑定模式变量槽
    /// 并构建运行时 `PatternDetail`。槽位纪律：枚举隐式参数不占槽、构造子隐式
    /// 绑定器补虚通配、变量模式以用户名绑槽、**Con 本身不占槽**。
    /// 构造子类型经 `infer_expr(Var(名))` 取（L09 的全局表按层级存，无名字键的
    /// decl 表——树同款）。
    ///
    /// 返回值第三项 = 该层 Con 的走查返回类型（已 force，槽位刚性 = 本层
    /// 走查变量；compile 结算本层特化方程用；非 Con 模式为 `None`）。
    /// 嵌套 `Con` 字段位置记入 `pending_pos`（两段式记账；结算见 `compile`，
    /// 2026-09-18 评审修复 P0 的 L09 移植）。
    fn walk_pat(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        pat: &Pattern,
        head_ty: V,
    ) -> Result<(PatternDetail, Cxt<'a>, Option<V>), Error> {
        match pat {
            Pattern::Any(span, _) => {
                let a_t = mach.quote(bump, cxt.lvl, head_ty);
                let cxt2 = mach.bind_name(bump, cxt, "_", a_t, head_ty);
                Ok((PatternDetail::Any(span.clone()), cxt2, None))
            }
            Pattern::Con(name, subs, _) => {
                let head_sum = mach.force_v(bump, head_ty);
                let is_sum = v_tag(head_sum) == 7
                    && matches!(v_xcell_of(head_sum), XCell::Sum { .. });
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
                        ))));
                    }
                    let a_t = mach.quote(bump, cxt.lvl, head_ty);
                    let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
                    return Ok((PatternDetail::Bind(name.clone()), cxt2, None));
                }
                let (_, mut ty) = mach.infer_expr(bump, cxt, &Raw::Var(name.clone()))?;
                let mut impl_vals: Vec<V> = sum_params
                    .iter()
                    .filter(|p| p.icit == Icit::Impl)
                    .map(|p| p.val)
                    .collect();
                impl_vals.reverse();
                let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
                let mut details: Vec<PatternDetail> = Vec::new();
                let mut cxt_arm = clone_cxt(cxt);
                loop {
                    let tyf = mach.force_v(bump, ty);
                    if v_tag(tyf) != 4 {
                        break;
                    }
                    let cell = v_pi_of(tyf);
                    let (bname, bicit, dom, body, env0) =
                        (cell.name, cell.icit, cell.dom, cell.body, cell.env);
                    if let Some(v) = impl_vals.pop() {
                        let env = env_ext(bump, env0, v);
                        ty = mach.eval(bump, env, body);
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
                            let d_t = mach.quote(bump, cxt_arm.lvl, dom);
                            cxt_arm = mach.bind_name(bump, &cxt_arm, &b, d_t, dom);
                            PatternDetail::Any(empty_span(()))
                        }
                        Some(Pattern::Any(span, _)) => {
                            sub_queue.remove(0);
                            let b = format!("_{}", bname);
                            let d_t = mach.quote(bump, cxt_arm.lvl, dom);
                            cxt_arm = mach.bind_name(bump, &cxt_arm, &b, d_t, dom);
                            PatternDetail::Any(span.clone())
                        }
                        Some(p @ Pattern::Con(..)) => {
                            sub_queue.remove(0);
                            // 嵌套 Con：字段 dom 是含该构造子的 Sum 时记一笔
                            // 待提升的嵌套位置（该字段位置沿 ctor 路径的可达
                            // 构造子必须有臂覆盖），臂特化方程解出后以终态 σ
                            // 结算（见 compile）。
                            let Pattern::Con(cn, ..) = p else {
                                unreachable!()
                            };
                            let field_sum = mach.force_v(bump, dom);
                            let is_ctor = v_tag(field_sum) == 7
                                && matches!(v_xcell_of(field_sum), XCell::Sum { cases, .. }
                                    if cases.iter().any(|c| *c == cn.data.as_str()));
                            let (d, c2) = if is_ctor {
                                self.cur_path.push((name.data.clone(), details.len()));
                                let (d, c2, inner_ret) =
                                    self.walk_pat(mach, bump, &cxt_arm, p, dom)?;
                                self.cur_path.pop();
                                if let Some(r) = inner_ret {
                                    let mut pa = self.cur_path.clone();
                                    pa.push((name.data.clone(), details.len()));
                                    self.pending_pos.push((pa, field_sum, r));
                                }
                                (d, c2)
                            } else {
                                let (d, c2, _) = self.walk_pat(mach, bump, &cxt_arm, p, dom)?;
                                (d, c2)
                            };
                            cxt_arm = c2;
                            d
                        }
                    };
                    details.push(detail);
                    let env = env_ext(bump, env0, u);
                    ty = mach.eval(bump, env, body);
                }
                let ret = mach.force_v(bump, ty);
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

/// 通配臂（参考版 `is_catch_all` 同款）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data)
        }
    }
}
