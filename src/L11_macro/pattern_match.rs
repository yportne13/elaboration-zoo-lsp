use std::{
    collections::{BTreeSet, HashMap, HashSet},
};

use crate::parser_lib::{Span, ToSpan};

use super::{
    Env, Error, Infer, Lvl, Tm, Val,
    cxt::Cxt, Rc, Decl, Subst,
    elaboration::SpecSolve,
    empty_span, wrap_sub,
    parser::syntax::{Pattern, Raw, Icit},
    PatternDetail, PosCover,
    cover_at, fmt_path,
};

type Var = i32;

type Constructor = Span<String>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套模式位置缺覆盖（2026-09-18 评审修复）：携带已格式化的完整文案
    /// （`match 不完整：模式位置 {fmt_path} 缺少构造子 {ctor}`），两版共用
    /// mod.rs 的 fmt_path 保证逐字节一致。
    Nested(String),
}

pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Rc<Tm>)>,
    ret_type: Rc<Val>,
    /// 嵌套覆盖检查的记账（走查中收集，臂循环结束后统一探测）。顶层覆盖
    /// 检查只遍历 scrutinee 类型的构造子；嵌套 `Con` 字段位置的可达性从未
    /// 被枚举会让非穷尽 match 被静默接受（P0，2026-09-18 评审修复）。
    /// 两段式：走查中只记节点方程（见 [`PendingNode`]）；特化方程**成功后**
    /// （σ 为终态）才逐节点解槽位方程、提升为带 σ/lvl 快照的完整记账——
    /// 字段走查时方程尚未解出，索引精化不在 σ 里，此时探测会把已精化下
    /// 不可达的构造子误判可达。特化方程失败的荒谬臂丢弃记账（其位置不产
    /// 生覆盖义务，本层口径是静默跳过）。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待结算节点（特化方程成功后结算；根节点在前、嵌套节点
    /// 按下钻序——父先于子，槽位解逐层传递）。
    pending_pos: Vec<PendingNode>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 走查中的一个 Con 节点方程（L07 `walk_con` 内联特化方程的本层等价物）：
/// `head` = 该节点的头部 Sum 值（根 = scrutinee 类型；嵌套 = 字段 Sum），
/// `ret` = 构造子返回类型以**走查槽位 rigid** 实例化的结果。结算时对
/// `head.params ≐ ret.params` 逐槽跑 `unify_pm`（裸槽 rigid 可解入 σ）——
/// L11 的臂特化方程走 raw 侧的 meta 间接，走查槽位不在其解里，必须由本
/// 方程把索引精化落到槽位上，嵌套字段的探测才能看到精化。
/// `path` = Some(路径) 时该节点同时是一个嵌套覆盖义务位置（字段 Sum 即
/// `head`）；None = 根节点（只参与方程传导，不产生覆盖义务）。
struct PendingNode {
    path: Option<Vec<(String, usize)>>,
    head: Rc<Val>,
    ret: Rc<Val>,
}

/// 一个嵌套拆分位置的记账：路径 = 根到被拆字段的 (构造子名, 字段下标)
/// 链；`field_sum` 是该字段在记录臂走查下的 Sum 值；σ/lvl 是记录臂槽位
/// 方程终态的快照（延迟探测要在与臂内方程同构的状态下跑）。
struct NestedCheck {
    path: Vec<(String, usize)>,
    field_sum: Rc<Val>,
    sub: Rc<Subst>,
    lvl: Lvl,
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
    /// 探测传记账时的臂内层级（scratch 层级必须落在该臂全部真槽之外）。
    /// `init_sub`：记账臂的终态 σ（顶层探测为空）——方程两侧经 `unify_pm`
    /// 在 acc 之下解释，索引精化对探测可见。
    fn probe_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        lvl: Lvl,
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
            let tyf = infer.force(&cxt.decl, &ty);
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
                _ => break Self::unify_indices(infer, cxt, lvl, &sum_name, &head_params, &tyf, init_sub),
            }
        };
        infer.meta = snap;
        // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理（保守地要求
        // 覆盖，2026-09-18 评审修复）。反方向（判不可达 → 覆盖检查放过该
        // 构造子）会让深负载下的非穷尽 match 被静默接受。
        ok || infer.fuel_exhausted()
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，**头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 :=
    /// 构造子侧值"（与上下文顺序一致）。解只累积进探测私有的 σ（以
    /// `init_sub` 作种子），弃掉即回滚。`lvl` 显式穿参见 `probe_accessible`。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        lvl: Lvl,
        sum_name: &Span<String>,
        head_params: &[Rc<Val>],
        ret_ty: &Rc<Val>,
        init_sub: &Rc<Subst>,
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
            acc: init_sub.clone(),
        };
        let span = empty_span(());
        head_params
            .iter()
            .zip(rp.iter())
            .all(|(a, b)| infer.unify_pm(cxt, lvl, a, &b.1, span, &mut spec).is_ok())
    }

    /// 节点槽位方程（结算期）：`head.params ≐ ret.params` 逐槽经 `unify_pm`
    /// 解入 `spec.acc`（走查槽位是裸 rigid，可解——见 [`PendingNode`] 文档）。
    /// 单槽失败不阻断后续槽：这里的解要传给嵌套字段，个别槽失败只损失该
    /// 槽的精化，覆盖检查按保守可达处理。
    fn node_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        lvl: Lvl,
        head_sum: &Rc<Val>,
        ret_ty: &Rc<Val>,
        spec: &mut SpecSolve,
    ) {
        let head_f = infer.force(&cxt.decl, head_sum);
        let (sum_name, head_params) = match head_f.as_ref() {
            Val::Sum(n, params, ..) => (n.data.clone(), params.clone()),
            _ => return,
        };
        let ret_f = infer.force(&cxt.decl, ret_ty);
        let rp = match ret_f.as_ref() {
            Val::Sum(n, params, ..) if n.data == sum_name => params.clone(),
            _ => return,
        };
        let span = empty_span(());
        for (a, b) in head_params.iter().zip(rp.iter()) {
            let _ = infer.unify_pm(cxt, lvl, &a.1, &b.1, span, spec);
        }
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写）。
    ///
    /// 决策树在每个 (构造子 × 臂) 上重复可达性探测并逐节点克隆上下文；
    /// 逐臂版把每臂的工作收敛为一次 `check_pm_final`（特化方程 + 头部精化，
    /// 与树叶子同款）加一次体检查，可达性探测每 match 只做一轮（**值级**
    /// `probe_accessible`，不再逐 ctor 走 infer/check）。
    ///
    /// 语义相对决策树的两处（已登记 README / 分析文档）：
    /// 1. 遮蔽检查只认**通配臂**（`is_catch_all`）：通配臂之后的臂报
    ///    `Unreachable`；非通配的联合遮蔽（如 `zero, succ, x` 的 x）不再报；
    /// 2. 特化方程失败的臂**静默跳过**（不进 pats、不告警），与树叶子
    ///    `check_pm_final` 失败即 `Ok(false)` 的口径一致。
    ///
    /// 嵌套覆盖检查（2026-09-18 评审修复，P0）：走查中沿模式下钻逐节点记
    /// 账（路径, 字段 Sum），方程成功后以终态 σ 结算（两段式）；臂循环后
    /// 对每条记账在记录臂实例化（σ/lvl 快照）下探测字段 Sum 的可达构造子，
    /// 覆盖集从已走查臂的 PatternDetail 沿路径结构求出（var/Any = 全覆盖、
    /// 祖先异 ctor = 不可达、末端 Con = 贡献构造子），缺失报
    /// `match 不完整：模式位置 {fmt_path} 缺少构造子 {ctor}` 并去重。
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
        let (constrs, ctor_names): (Vec<Constructor>, Vec<String>) = match typ.as_ref() {
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
            if Self::probe_accessible(infer, cxt, cxt.lvl, &typ, &ctor.data, &Rc::new(Subst::default()))
                && !arms
                    .iter()
                    .any(|(pat, _)| covers(pat, &ctor.data, &ctor_names))
            {
                self.warnings.push(Warning::Unmatched(Pattern::Con(
                    ctor.clone(),
                    vec![Pattern::Any(empty_span(true), Icit::Expl); 999],
                    Icit::Expl,
                )));
            }
        }
        // 逐臂下钻：每臂一次 check_pm_final → σ 之下的上下文里检查体。
        // 臂序 = 用户序；首匹配语义由运行时 eval_aux 保住。
        let mut unreachable: Vec<Warning> = Vec::new();
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                unreachable.push(Warning::Unreachable(body.clone()));
                continue;
            }
            self.cur_path.clear();
            // 先走查模式：绑定模式变量槽（体与 check_pm_final 的名字解析
            // 都依赖这些绑定），同时构建运行时 PatternDetail；嵌套 Con 字段
            // 位置记入 pending_pos（此时方程未解，只记路径与字段 Sum）。
            let walked = walk_pat(infer, cxt, pat, &typ, &mut self.pending_pos, &mut self.cur_path);
            let (detail, cxt_walk) = match walked {
                Ok(x) => x,
                Err(_) => {
                    // 结构冲突（absurd 臂）：不进 pats、不告警（同树叶子口径）；
                    // 其嵌套位置不产生覆盖义务
                    self.pending_pos.clear();
                    continue;
                }
            };
            let raw = pat.to_raw();
            let Ok((_, sigma)) = infer.check_pm_final(
                &cxt_walk,
                raw,
                typ.clone(),
                target_val.clone(),
            ) else {
                // 特化方程失败 = 臂不可达：嵌套位置不产生覆盖义务（本臂
                // 的语义承担 = 静默跳过）
                self.pending_pos.clear();
                continue;
            };
            // 嵌套位置结算（两段式）：此刻本臂特化方程已解出。先逐节点把
            // 槽位方程解进 σ（根在前——外层索引精化先落槽，嵌套字段的 Sum
            // 才带着精化，如 `Vec[Nat] (succ n)` 的尾部上 `nil` 不可达），
            // 再把有路径的节点提升为带 σ/lvl 快照的完整记账。
            let nodes = std::mem::take(&mut self.pending_pos);
            if nodes.iter().any(|n| n.path.is_some()) {
                let mut sigma_acc = sigma.clone();
                for node in &nodes {
                    let mut spec = SpecSolve { acc: sigma_acc.clone() };
                    Self::node_indices(infer, cxt, cxt_walk.lvl, &node.head, &node.ret, &mut spec);
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
            let cxt_arm = cxt_walk.subst_cxt(&sigma);
            let ret_type = match self.ret_type.as_ref() {
                Val::Flex(..) => self.ret_type.clone(),
                _ => {
                    let q = infer.quote(&cxt_arm.decl, cxt_arm.lvl, &self.ret_type);
                    infer.eval(&cxt_arm.decl, &cxt_arm.env, &q)
                }
            };
            let ret = infer.check(&cxt_arm, body.clone(), &ret_type)?;
            self.pats.push((detail, ret));
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        // 嵌套位置的覆盖检查（沿模式下钻逐节点）：每条记账在记录臂的
        // 实例化（σ/lvl 快照）下探测字段 Sum 的可达构造子；覆盖集 = 已走查
        // 臂的 PatternDetail 沿路径的结构贡献（var/Any = 全覆盖；祖先异
        // ctor = 不可达该位置；同 ctor 前缀 = 贡献其末端构造子）。荒谬臂 /
        // 被遮蔽臂不在 pats 里，天然不贡献覆盖——与运行时首匹配结构语义
        // 一致。可达集取各记账臂探测的并集（保守）。
        let mut reported: HashSet<(Vec<(String, usize)>, String)> = HashSet::new();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force：索引精化（如尾部
            // 长度 l := succ n）在 σ 里，推开后的 Sum 才是探测该用的类型
            let field_sum = infer.force(&cxt.decl, &Rc::new(wrap_sub(&nc.sub, (*nc.field_sum).clone())));
            let field_ctrs = match field_sum.as_ref() {
                Val::Sum(_, _, cases, _) => cases.clone(),
                _ => continue,
            };
            for ctor in field_ctrs {
                if !Self::probe_accessible(infer, cxt, nc.lvl, &field_sum, &ctor.data, &nc.sub) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    PosCover::All => true,
                    PosCover::Ctor(n) => n == ctor.data,
                    PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.data.clone())) {
                    self.warnings.push(Warning::Nested(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        fmt_path(&nc.path),
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
                                Self::eval_aux(infer, param, decl, &cxt, &[(pat.clone(), body)])
                            },
                        )
                }
                _ => None,
            })
            .next()
    }
}

/// 臂是否（结构上）覆盖构造子 `ctor`：通配覆盖一切；构造子名不在该类型的
/// 构造子表里 = 变量模式（覆盖一切）；否则同名才覆盖（L07 `covers` 同款）。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor
        }
    }
}

/// 通配臂：覆盖所有取值的臂（其后的臂不可达）。变量模式（构造子名不在
/// 构造子表里且无子模式）也算（L07 `is_catch_all` 同款）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data)
        }
    }
}

/// 模式 → 运行时 `PatternDetail`（L07 `walk` 的纯结构版，无槽位绑定）。
///
/// 槽位纪律与决策树的 patcon 记账一致：构造子 Π 链上**枚举隐式参数之后**
/// 的每个绑定器各占一个 detail 槽——枚举隐式参数用头部 Sum 的实参实例化
/// （不产生槽）；省写的构造子隐式绑定器补虚通配 `Any`；子模式按 icit 对齐
/// （隐式可缺省、显式必须提供，多余子模式忽略——特化方程已在
/// `check_pm_final` 里把关）。嵌套 Con 递归下钻（字段类型 = 该位置的
/// telescope 实例化）。非构造子名 = 变量模式 → `Bind`。

/// 模式走查（L07 `walk`/`walk_con` 的口径）：绑定模式变量槽并构建运行时
/// `PatternDetail`。
///
/// 槽位纪律与决策树的列走查一致：构造子 Π 链上**枚举隐式参数之后**的每个
/// 绑定器各绑一槽——枚举隐式参数用头部 Sum 的实参实例化（不绑槽）；省写
/// 的构造子隐式绑定器绑 `_名` 槽、detail 记虚通配 `Any`；通配绑 `_名`；
/// 变量模式（构造子名不在该类型构造子表里）以**用户名**绑槽、detail 记
/// `Bind`；嵌套 Con 递归下钻（字段类型 = 该位置的 telescope 实例化）。
/// **Con 本身不占槽**（运行时 eval_aux 的 Con 路径不 prepend，与树一致）。
/// Err = 头部不是和类型却又带子模式解构之类的硬错误。
///
/// 嵌套覆盖记账（2026-09-18 评审修复）：子模式是 Con 且字段类型是含该
/// 构造子的 Sum 时，沿 `cur_path` 下钻（父 push (本 ctor, 字段下标)、子
/// pop 平衡）；每个 Con 节点把自己的 (头部 Sum, 槽位实例化的返回类型)
/// 记入 `pending`——臂的特化方程成功后由 `compile` 逐节点解槽位方程并以
/// 终态 σ 结算（两段式，见 `PendingNode`/`NestedCheck` 文档）。
fn walk_pat(
    infer: &mut Infer,
    cxt: &Cxt,
    pat: &Pattern,
    head_ty: &Rc<Val>,
    pending: &mut Vec<PendingNode>,
    cur_path: &mut Vec<(String, usize)>,
) -> Result<(PatternDetail, Cxt), Error> {
    match pat {
        Pattern::Any(span, _) => {
            let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
            let cxt2 = cxt.bind(empty_span("_".to_owned()), a_t, head_ty.clone());
            Ok((PatternDetail::Any(span.to_span()), cxt2))
        }
        Pattern::Con(name, subs, _) => {
            let head_sum = infer.force(&cxt.decl, head_ty);
            let (sum_name, sum_params, cases) = match head_sum.as_ref() {
                Val::Sum(sum_name, params, cases, _) => (sum_name, params, cases),
                _ => {
                    if !subs.is_empty() {
                        return Err(Error(name.clone().map(|n| format!(
                            "`{n}` 不是构造子，不能带子模式解构"
                        ))));
                    }
                    let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
                    let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                    return Ok((PatternDetail::Bind(name.clone()), cxt2));
                }
            };
            if !cases.iter().any(|c| c.data == name.data) {
                if !subs.is_empty() {
                    return Err(Error(name.clone().map(|n| format!(
                        "`{n}` 不是 {} 的构造子，不能带子模式解构", sum_name.data
                    ))));
                }
                let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
                let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                return Ok((PatternDetail::Bind(name.clone()), cxt2));
            }
            // L11 的构造子以**裸名**登记（elaboration.rs 里 cxt.decl(c.0, ..)）
            let entry_ty = match cxt.decl.get(name.data.as_str()) {
                Some(e) => e.4.clone(),
                None => {
                    return Err(Error(name.clone().map(|n| format!("找不到构造子 {}", n))))
                }
            };
            // 枚举隐式参数（头部 Sum 的 Impl 实参）逐一实例化，不绑槽
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
                                .filter(|p| p.get_icit() == Icit::Impl)
                                .copied(),
                            Icit::Expl => match sub_queue.first() {
                                Some(p) if p.get_icit() == Icit::Expl => Some(*p),
                                _ => None,
                            },
                        };
                        // 本绑定器位置的 fresh rigid：绑槽即入 env
                        let u = Rc::new(Val::vvar(cxt_arm.lvl));
                        let detail = match sub {
                            None => {
                                let b = empty_span(format!("_{}", bname.data));
                                let d_t = infer.quote(&cxt.decl, cxt_arm.lvl, &dom);
                                cxt_arm = cxt_arm.bind(b, d_t, dom.clone());
                                PatternDetail::Any(empty_span(()))
                            }
                            Some(Pattern::Any(span, _)) => {
                                sub_queue.remove(0);
                                let b = empty_span(format!("_{}", bname.data));
                                let d_t = infer.quote(&cxt.decl, cxt_arm.lvl, &dom);
                                cxt_arm = cxt_arm.bind(b, d_t, dom.clone());
                                PatternDetail::Any(span.to_span())
                            }
                            Some(p @ Pattern::Con(..)) => {
                                sub_queue.remove(0);
                                // 嵌套 Con：字段类型是含该构造子的 Sum →
                                // 沿路径下钻（节点方程由子节点在 Con 分支
                                // 末尾自行记账，见 walk_pat 文档）
                                let nested_name = match p {
                                    Pattern::Con(cn, _, _) => cn.data.clone(),
                                    _ => unreachable!(),
                                };
                                let field_sum = infer.force(&cxt.decl, &dom);
                                let is_ctor = matches!(
                                    field_sum.as_ref(),
                                    Val::Sum(_, _, cases, _)
                                        if cases.iter().any(|c| c.data == nested_name)
                                );
                                if is_ctor {
                                    cur_path.push((name.data.clone(), details.len()));
                                }
                                let walked = walk_pat(infer, &cxt_arm, p, &dom, pending, cur_path);
                                if is_ctor {
                                    cur_path.pop();
                                }
                                let (d, c2) = walked?;
                                cxt_arm = c2;
                                d
                            }
                        };
                        details.push(detail);
                        // 下一层域：以本绑定器位置的 fresh rigid 实例化
                        ty = infer.closure_apply(&cxt_arm.decl, &closure, u);
                    }
                    _ => break,
                }
            }
            // 节点记账：头部 Sum + 以走查槽位实例化的返回类型（结算期解
            // 槽位方程的两侧，见 PendingNode）。cur_path 非空 = 嵌套字段
            // 位置（同时产生覆盖义务）；空 = 根节点（只传导方程）。
            let ret_sum = infer.force(&cxt.decl, &ty);
            let my_path = if cur_path.is_empty() {
                None
            } else {
                Some(cur_path.clone())
            };
            pending.push(PendingNode {
                path: my_path,
                head: head_sum.clone(),
                ret: ret_sum,
            });
            Ok((PatternDetail::Con(name.clone(), details), cxt_arm))
        }
    }
}
