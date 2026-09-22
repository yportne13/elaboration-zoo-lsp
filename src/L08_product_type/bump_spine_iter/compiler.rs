//! compiler：模式匹配编译（参考版 pattern_match.rs 的逐句移植）——
//! `Compiler`/`Walk`/`NestedCheck`、覆盖与可达性（`covers`/
//! `is_catch_all`/`sum_case_names`）、下钻 `walk_con`。原 bump_spine_iter.rs
//! 的 "模式匹配编译" 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use std::rc::Rc;

use super::parser::syntax::{Icit, Pattern, Raw};
use super::{cover_at, empty_span, Error, fmt_path, PatternDetail, PosCover};

use super::env::env_ext;
use super::force::val_mentions_lvl;
use super::machine::{bind_slots, Cxt, Machine, subst_cxt};
use super::prim::UNIFY_FUEL;
use super::subst::{SpecSolve, SubstV, wrap_sub};
use super::syntax::{SumDataV, Tm, V, v_lvl, v_lvl_of, v_pi_of, v_tag, v_xcell, v_xcell_of, XCell};

// 模式匹配编译（参考版 pattern_match.rs 的逐句移植）
// --------------------------------------------------------------------------------

/// 把 `match` 的 (模式, 分支体) 列表编译成 `Vec<(PatternDetail, Tm)>`，
/// 并做覆盖性 / 可达性检查。特化方程解得出 = 分支可达且解就是精化；结构
/// 冲突 = 分支不可能（absurd）。逐臂下钻保持用户书写顺序，运行时首匹配 =
/// 用户语义；通配臂之后的所有臂不可达（报「分支不可达」）。
pub(super) struct Compiler<'a> {
    /// 收集所有错误（覆盖缺失 / 分支不可达），一次报全。
    errors: Vec<String>,
    pub(super) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    /// 当前精化替换（参考版 `Compiler::sub`，dpm-nbe 的 explicit
    /// substitution）：特化方程的解在此累积；"解前构建、解后消费"的值在
    /// 读点用 [`wrap_sub`] 包裹，force 惰性推开。臂边界 / 探测边界回滚 =
    /// Rc 指针赋值。
    sub: Rc<SubstV>,
    /// 本子句可解的 rigid 层级（入口 bind 槽基线 + 走查中新绑的模式槽）。
    /// 只经 [`SpecSolve`] 穿参给方程合一；分支体检查走常规转换（spec 缺
    /// 席），不得解假设。
    solvable: Vec<u32>,
    /// 嵌套覆盖检查的记账（参考版同款，2026-09-18）：顶层覆盖检查只遍历
    /// scrutinee 类型的构造子；嵌套 `Con` 字段位置的可达性也要枚举，否则
    /// 非穷尽 match 被静默接受（P0）。两段式：走查中只记 (路径, 字段
    /// Sum)；臂走查**成功后**（特化方程已解出、σ 为终态）才提升为带
    /// σ/solvable/lvl 快照的完整记账。整臂 Unreachable 时丢弃。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待提升位置（臂边界结算）。
    pending_pos: Vec<(Vec<(String, usize)>, V)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账（参考版 `NestedCheck` 同构）：路径 = 根到被拆
/// 字段的 (构造子名, 字段下标) 链；`field_sum` 是该字段在记录臂实例化下的
/// Sum 值；σ/solvable/lvl 是臂终态的走查快照。
struct NestedCheck {
    path: Vec<(String, usize)>,
    field_sum: V,
    sub: Rc<SubstV>,
    solvable: Vec<u32>,
    lvl: u32,
}

enum Walk<'a> {
    Matched(PatternDetail, Cxt<'a>),
    Unreachable,
}

impl<'a> Walk<'a> {
    fn matched(self) -> Option<(PatternDetail, Cxt<'a>)> {
        match self {
            Walk::Matched(d, c) => Some((d, c)),
            Walk::Unreachable => None,
        }
    }
}

/// `Sum` 值的构造子名表（覆盖检查用）。
fn sum_case_names(v: V) -> Vec<String> {
    match v_xcell_of(v) {
        XCell::Sum { cases, .. } => cases.iter().map(|c| c.to_string()).collect(),
        _ => Vec::new(),
    }
}

/// 顶层覆盖判定：通配 / 变量模式覆盖一切；Con 只覆盖同名构造子。
fn covers(pat: &Pattern, ctor: &str, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, _, _) => {
            !ctor_names.iter().any(|c| c == &name.data) || name.data == ctor
        }
    }
}

/// 通配臂：覆盖所有取值的臂（其后的臂不可达）。
fn is_catch_all(pat: &Pattern, ctor_names: &[String]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_names.iter().any(|c| c == &name.data)
        }
    }
}

impl<'a> Compiler<'a> {
    pub(super) fn new() -> Self {
        Compiler {
            errors: Vec::new(),
            pats: Vec::new(),
            sub: Rc::new(SubstV::default()),
            solvable: Vec::new(),
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn compile(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        scrut_ty: V,
        scrut: &'a Tm<'a>,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt<'a>,
        expected: V,
    ) -> Result<(), Error> {
        let decls = cxt.decl.borrow();
        // 被匹配对象的值（在 match 现场求值）：用于把"被匹配的变量本身"
        // 写入精化替换（见 walk_con 末尾）
        let head_val = mach.eval(bump, &decls, cxt.env, scrut);
        // 编译期间的所有合一共享一个 fuel 池（深层递归防护）
        mach.fuel.set(UNIFY_FUEL);
        let head_sum = mach.force_v(bump, &decls, scrut_ty);
        if !(v_tag(head_sum) == 7 && matches!(v_xcell_of(head_sum), XCell::Sum { .. })) {
            return Err(Error("match 的对象必须是和类型（enum）".to_owned()));
        }
        let ctor_names = sum_case_names(head_sum);
        // 可解集基线：当前上下文的全部 bind 槽（def 参数 / λ 参数 / 外层
        // 模式变量；嵌套 match 的入口上下文可能带外层精化的 VSub 包裹，
        // bind_slots 解包取 raw 层级）。走查中新绑的模式槽在此基础上追加。
        self.solvable = bind_slots(&mach.defs, cxt);
        // 覆盖检查：每个可达构造子必须被某个臂覆盖（通配臂覆盖全部）。
        // 可达性 = 在（meta + σ + 本地可解集）快照回滚下跑一次特化方程
        // （与臂内走查同一套判定）。
        for ctor in &ctor_names {
            if Self::probe_accessible(mach, bump, cxt, cxt.lvl, head_sum, ctor, &self.sub, &self.solvable)
                && !arms.iter().any(|(pat, _)| covers(pat, ctor, &ctor_names))
            {
                self.errors
                    .push(format!("match 不完整：缺少构造子 {}", ctor));
            }
        }
        // 逐臂下钻。一旦出现通配臂（覆盖所有取值），后续臂运行时永远不会
        // 被选中——保持用户顺序的首匹配语义，且被遮蔽的臂报「分支不可达」。
        let mut shadowed = false;
        for (pat, body) in arms {
            if shadowed {
                // 被前面的通配臂遮蔽：运行时永不可达（首匹配语义）。
                // owner 2026-09-20 口径：不可达的臂**报错**（与 Walk::Unreachable
                // 的「分支不可达」同类），不静默跳过。
                self.errors
                    .push(format!("分支不可达：模式 {:?} 被前面的通配臂遮蔽", pat));
                continue;
            }
            // 臂边界的精化替换快照（回滚 = Rc 指针赋值，见循环尾）。
            let sub_snap = self.sub.clone();
            let solvable_snap = self.solvable.clone();
            // 臂边界同时是名字轨迹的基线：walk_con 经 bind_name 压入的
            // 模式绑定不在臂检查的 unwind 范围内，臂结束后显式截断
            // （参考版 src_names 随 Cxt 克隆天然隔离，快版轨迹需手动回滚）
            let name_mark = mach.name_mark();
            match self.walk(mach, bump, pat, scrut_ty, head_val, cxt)? {
                Walk::Matched(detail, cxt_arm) => {
                    // 嵌套位置结算：此刻本臂全部特化方程已解出、σ 为终态，
                    // 字段 Sum 置于 σ 之下再探测才能看到索引精化（参考版同款）
                    for (path, field_sum) in std::mem::take(&mut self.pending_pos) {
                        self.nested_checks.push(NestedCheck {
                            path,
                            field_sum,
                            sub: self.sub.clone(),
                            solvable: self.solvable.clone(),
                            lvl: cxt_arm.lvl,
                        });
                    }
                    // 分支体走**常规转换**检查：spec 不穿参，可解性不再需要
                    // "摘走/放回"的编排（旧 pm_solvable_take/set 已随之删除）。
                    // 上下文先置于精化之下（dpm-nbe `subst sub ctx`）：env 槽
                    // 与 types 类型包 VSub，lvl/locals/pruning 不动——槽位布局
                    //（= 运行时布局）永不漂移，读点 force 展开。
                    let cxt_arm = subst_cxt(bump, &mach.defs, &self.sub, &cxt_arm);
                    // name_map 影子同步（Raw::Var 的 O(1) 快路径绕过 types 链，
                    // 不补会让嵌套 match 看不到外层精化）
                    let name_undo = mach.wrap_names(&cxt_arm);
                    // 期望类型**重锚**到臂上下文：quote → eval 把其中所有
                    // rigid 引用重定向到臂 env（quote 时 VSub 全部推开——
                    // 精化等式一并烘焙进去）。语义上不重锚也正确（force 惰性
                    // 推开），但值层面只有重锚后，期望里的卡住 match 与
                    // meta 解物化出来的副本才有同样的 env 布局——unify 的
                    // 结构快路径（struct_eq）才能命中。
                    let decls_arm = cxt_arm.decl.borrow();
                    let ret_type = {
                        let t = mach.force_v(bump, &decls_arm, wrap_sub(bump, &self.sub, expected));
                        if mach.is_flex_v(t) {
                            t
                        } else {
                            let tm = mach.quote(bump, &decls_arm, cxt_arm.lvl, t);
                            mach.eval(bump, &decls_arm, cxt_arm.env, tm)
                        }
                    };
                    let tm = mach.check(bump, &cxt_arm, body, ret_type)?;
                    mach.restore_names(name_undo);
                    self.pats.push((detail, tm));
                    if is_catch_all(pat, &ctor_names) {
                        shadowed = true;
                    }
                }
                Walk::Unreachable => {
                    // 荒谬臂的嵌套位置不产生覆盖义务（参考版同款，v3 回归钉）
                    self.pending_pos.clear();
                    self.errors
                        .push(format!("分支不可达：模式 {:?} 与被匹配类型不相容", pat));
                }
            }
            // 臂边界：回滚本臂的精化替换与名字轨迹（本臂解出的 meta 保留
            // ——分支体 Tm 引用着它们，且解在 rename 时已烘焙为无 def 形
            // 式）。solvable 同步回滚：上一臂多绑的槽若残留，会让后续臂特
            // 化方程中的瞬态 rigid（Λ 下钻产生的、超出本臂槽位的层级）被
            // 误判为可解——臂序依赖的可达性漂移（stale-solvable 污染，
            // 参考版 stale-solvable 回归钉）。
            mach.unwind_names(name_mark);
            self.sub = sub_snap;
            self.solvable = solvable_snap;
            self.cur_path.clear();
        }
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，参考版同款）：每条记账在
        // 记录臂的实例化（σ/solvable/lvl 快照）下探测字段 Sum 的可达构造
        // 子；覆盖集 = 已走查臂的 PatternDetail 沿路径的结构贡献（var/Any
        // = 全覆盖；祖先异 ctor = 不可达该位置；同 ctor 前缀 = 贡献其末端
        // 构造子）。可达集取各记账臂探测的并集（保守）。荒谬臂 / 被遮蔽臂
        // 不在 pats 里，天然不贡献覆盖——与运行时首匹配结构语义一致。
        let mut reported = std::collections::HashSet::new();
        for nc in std::mem::take(&mut self.nested_checks) {
            // 字段 Sum 置于记录臂的终态 σ 之下再 force（参考版同款）
            let field_sum = mach.force_v(bump, &decls, wrap_sub(bump, &nc.sub, nc.field_sum));
            if !(v_tag(field_sum) == 7 && matches!(v_xcell_of(field_sum), XCell::Sum { .. })) {
                continue;
            }
            for ctor in sum_case_names(field_sum) {
                if !Self::probe_accessible(
                    mach,
                    bump,
                    cxt,
                    nc.lvl,
                    field_sum,
                    &ctor,
                    &nc.sub,
                    &nc.solvable,
                ) {
                    continue;
                }
                let covered = self.pats.iter().any(|(d, _)| match cover_at(d, &nc.path) {
                    PosCover::All => true,
                    PosCover::Ctor(n) => n == ctor,
                    PosCover::None => false,
                });
                if !covered && reported.insert((nc.path.clone(), ctor.clone())) {
                    self.errors.push(format!(
                        "match 不完整：模式位置 {} 缺少构造子 {}",
                        fmt_path(&nc.path),
                        ctor
                    ));
                }
            }
        }
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(Error(self.errors.join("\n")))
        }
    }

    /// 构造子可达性探测：在（meta + σ + 本地可解集）快照回滚下跑一次特化
    /// 方程。探测不产生真槽——构造子绑定器用超出上下文的 scratch 层级
    /// 实例化（同为刚性、同可被方程解出，探测状态全在本地，弃掉即回滚）。
    /// 成功 = 该构造子可能出现在头部类型的值里；结构冲突
    /// （`Vec[A] zero` 上不可能有 `cons`）= absurd。`lvl` 显式穿参（参考
    /// 版同款）：顶层探测传入口 `cxt.lvl`；嵌套位置的延迟探测传记账时的
    /// 臂内层级。
    fn probe_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        lvl: u32,
        head_sum: V,
        ctor: &str,
        init_sub: &Rc<SubstV>,
        base_solvable: &[u32],
    ) -> bool {
        let (sum_name, impl_vals) = match v_xcell_of(head_sum) {
            XCell::Sum { name, params, .. } => (
                *name,
                params
                    .iter()
                    .filter(|p| p.icit == Icit::Impl)
                    .map(|p| p.val)
                    .collect::<Vec<_>>(),
            ),
            _ => return false,
        };
        let entry = match cxt.decl.borrow().get(&format!("{}.{}", sum_name, ctor)) {
            Some(e) => *e,
            None => return false,
        };
        // 每个探测独立充值（参考版 probe_accessible 同点）：多构造子枚举
        // 的逐 ctor 探测不互相挤占共享池，避免后探的 ctor 假 absurd。
        mach.fuel.set(UNIFY_FUEL);
        let snap = mach.metas.clone();
        let decl = cxt.decl.borrow();
        let mut solvable = base_solvable.to_vec();
        let sub = init_sub.clone();
        let mut ty = entry.ty;
        let mut impl_idx = 0;
        let mut scratch = 0u32;
        let ok = loop {
            let tyf = mach.force_v(bump, &decl, wrap_sub(bump, &sub, ty));
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let u = if impl_idx < impl_vals.len() {
                    let v = impl_vals[impl_idx];
                    impl_idx += 1;
                    v
                } else {
                    let l = lvl + scratch;
                    scratch += 1;
                    solvable.push(l);
                    v_lvl(l)
                };
                let env = env_ext(bump, p.env, u);
                ty = mach.eval(bump, &decl, env, p.body);
            } else {
                let ret_sum = mach.force_v(bump, &decl, wrap_sub(bump, &sub, tyf));
                if !(v_tag(ret_sum) == 7 && matches!(v_xcell_of(ret_sum), XCell::Sum { .. })) {
                    break false;
                }
                break {
                    let mut spec = SpecSolve {
                        solvable: &solvable,
                        acc: sub.clone(),
                    };
                    // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理
                    // （保守地要求覆盖）——反方向（判不可达 → 覆盖检查放过
                    // 该构造子）会让深负载下的非穷尽 match 被静默接受。
                    // 参考版 probe_accessible 同点。
                    Self::unify_indices(mach, bump, cxt, lvl, &mut spec, head_sum, ret_sum, ctor)
                        .is_ok()
                        || mach.fuel.get() == 0
                };
            }
        };
        mach.metas = snap;
        ok
    }

    /// 特化方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽合一，
    /// **头部一侧在前**——两侧都是可解变量时解的方向是"头部变量 := 构造子
    /// 侧值"（即"老的变量 := 新的变量"，与上下文顺序一致）。解累积进
    /// `spec.acc`（调用方以当前 σ 作种子，方程后取回新 σ）；方程两侧由
    /// unify 入口置于 acc 之下解释（`subst ɑ vs` 的惰性等价物）。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        lvl: u32,
        spec: &mut SpecSolve<'_>,
        head_sum: V,
        ret_sum: V,
        ctor: &str,
    ) -> Result<(), Error> {
        let (hp, rp) = match (v_xcell_of(head_sum), v_xcell_of(ret_sum)) {
            (XCell::Sum { params: p1, .. }, XCell::Sum { params: p2, .. }) => (p1, p2),
            _ => return Err(Error(format!("构造子 {} 的返回类型不是和类型", ctor))),
        };
        if hp.len() != rp.len() {
            return Err(Error(format!(
                "构造子 {} 与被匹配类型的参数数不一致",
                ctor
            )));
        }
        let decl = cxt.decl.borrow();
        for (a, b) in hp.iter().zip(rp.iter()) {
            if !mach.unify_with(bump, &decl, lvl, a.val, b.val, Some(spec)) {
                // fuel 耗尽的失败是"假 absurd"（预算问题非结构冲突），
                // 文案带尾注供诊断——与 unify_catch 的同名尾注一致
                let fuel_note = if mach.fuel_exhausted() {
                    " (fuel exhausted)"
                } else {
                    ""
                };
                return Err(Error(format!(
                    "构造子 {} 与被匹配类型不相容（分支不可达）{fuel_note}",
                    ctor
                )));
            }
        }
        Ok(())
    }

    fn walk(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        pat: &Pattern,
        head_ty: V,
        head_val: V,
        cxt: &Cxt<'a>,
    ) -> Result<Walk<'a>, Error> {
        match pat {
            Pattern::Any(span, _) => {
                let lvl = cxt.lvl;
                let a_t = mach.quote(bump, &cxt.decl.borrow(), cxt.lvl, head_ty);
                let cxt2 = mach.bind_name(bump, cxt, "_", a_t, head_ty);
                self.solvable.push(lvl);
                Ok(Walk::Matched(PatternDetail::Any(*span), cxt2))
            }
            Pattern::Con(name, subs, _) => {
                self.walk_con(mach, bump, name, subs, head_ty, head_val, cxt)
            }
        }
    }

    /// 下钻一个构造子模式。槽位纪律：**每个绑定器一个槽，先绑定后下钻**——
    /// 构造子 Pi 链上每个绑定器都在当前 `cxt.lvl` 处绑定为 fresh rigid
    /// （枚举隐式参数除外：用头部 Sum 的实参实例化，不产生槽），然后按
    /// icit 对齐用户子模式继续下钻。嵌套 Con 模式由子 walk_con 入口绑自己
    /// 的 head 槽（槽值即本字段的实例化 rigid u），编译期绑定、运行时
    /// prepend、bind_count 三方同序同数。
    ///
    /// 读点纪律：telescope / 域 / 头值等"解前构建"的值，消费点用当前 σ
    /// 包裹（`wrap_sub`）——本 walk_con 及嵌套子模式的方程解出后，后续
    /// 读点经 force 推开看到解（dpm-nbe 的"剩余 telescope 置于解之下"）。
    #[allow(clippy::too_many_arguments)]
    fn walk_con(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        name: &crate::parser_lib::Span<String>,
        subs: &[Pattern],
        head_ty: V,
        head_val: V,
        cxt: &Cxt<'a>,
    ) -> Result<Walk<'a>, Error> {
        let decls = cxt.decl.borrow();
        let head_sum = mach.force_v(bump, &decls, wrap_sub(bump, &self.sub, head_ty));
        if !(v_tag(head_sum) == 7 && matches!(v_xcell_of(head_sum), XCell::Sum { .. })) {
            // 非和类型头部：只能当变量绑定
            if !subs.is_empty() {
                return Err(Error(format!(
                    "`{}` 不是构造子，不能带子模式解构",
                    name.data
                )));
            }
            let lvl = cxt.lvl;
            let a_t = mach.quote(bump, &decls, cxt.lvl, head_ty);
            let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
            self.solvable.push(lvl);
            return Ok(Walk::Matched(PatternDetail::Bind(name.clone()), cxt2));
        }
        let (sum_name, sum_params, cases) = match v_xcell_of(head_sum) {
            XCell::Sum {
                name,
                params,
                cases,
            } => (*name, *params, *cases),
            _ => unreachable!(),
        };
        let is_ctor = cases.iter().any(|c| *c == name.data);
        if !is_ctor {
            // 不是该类型的构造子 → 变量绑定
            if !subs.is_empty() {
                return Err(Error(format!(
                    "`{}` 不是 {} 的构造子，不能带子模式解构",
                    name.data, sum_name
                )));
            }
            let lvl = cxt.lvl;
            let a_t = mach.quote(bump, &decls, cxt.lvl, head_ty);
            let cxt2 = mach.bind_name(bump, cxt, &name.data, a_t, head_ty);
            self.solvable.push(lvl);
            return Ok(Walk::Matched(PatternDetail::Bind(name.clone()), cxt2));
        }
        let entry = *cxt
            .decl
            .borrow()
            .get(&format!("{}.{}", sum_name, name.data))
            .ok_or_else(|| Error(format!("找不到构造子 {}.{}", sum_name, name.data)))?;
        // head 槽：Con 模式自身占一槽。运行时 eval_aux 的 Con 路径把被匹配
        // 值 prepend 进 env，三方（编译期绑定 / 运行时 prepend / bind_count）
        // 同序同数。
        let lvl = cxt.lvl;
        let head_binder = format!("_{}", name.data);
        let a_t = mach.quote(bump, &decls, cxt.lvl, head_ty);
        let mut cxt = mach.bind_name(bump, cxt, &head_binder, a_t, head_ty);
        self.solvable.push(lvl);
        let mut ty = entry.ty;
        let impl_vals: Vec<V> = sum_params
            .iter()
            .filter(|p| p.icit == Icit::Impl)
            .map(|p| p.val)
            .collect();
        let mut impl_idx = 0;
        let mut sub_queue: Vec<&Pattern> = subs.iter().collect();
        let mut details: Vec<PatternDetail> = Vec::new();
        // 构造子自身绑定器的值（写入头部精化时用）
        let mut ctor_datas: Vec<SumDataV<'a>> = Vec::new();
        let ret = loop {
            let tyf = mach.force_v(bump, &decls, wrap_sub(bump, &self.sub, ty));
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let (bname, bicit, dom) = (p.name, p.icit, p.dom);
                if impl_idx < impl_vals.len() {
                    // 枚举隐式参数：不产生模式槽
                    let u = impl_vals[impl_idx];
                    impl_idx += 1;
                    let env = env_ext(bump, p.env, u);
                    ty = mach.eval(bump, &decls, env, p.body);
                    continue;
                }
                // 用户子模式按 icit 对齐：隐式绑定器可以缺省（自动通配），
                // 显式绑定器必须提供；子模式必须与绑定器顺序一致
                let sub: Option<&Pattern> = match bicit {
                    Icit::Impl => {
                        let matches_impl = sub_queue
                            .first()
                            .map(|p2| p2.get_icit() == Icit::Impl)
                            .unwrap_or(false);
                        if matches_impl {
                            Some(sub_queue.remove(0))
                        } else {
                            None
                        }
                    }
                    Icit::Expl => match sub_queue.first() {
                        Some(p2) if p2.get_icit() == Icit::Expl => Some(sub_queue.remove(0)),
                        _ => {
                            return Err(Error(format!(
                                "构造子 {} 缺少字段 {} 的模式",
                                name.data, bname
                            )))
                        }
                    },
                };
                // 绑定器的"值"：一律 fresh rigid（模式变量，可被特化方程解出）
                let u = v_lvl(cxt.lvl);
                let (detail, new_cxt) = match sub {
                    None => {
                        let lvl2 = cxt.lvl;
                        let bname2 = format!("_{bname}");
                        let dom_v = wrap_sub(bump, &self.sub, dom);
                        let d_t = mach.quote(bump, &decls, cxt.lvl, dom_v);
                        let c2 = mach.bind_name(bump, &cxt, &bname2, d_t, dom_v);
                        self.solvable.push(lvl2);
                        (PatternDetail::Any(empty_span(())), c2)
                    }
                    Some(Pattern::Any(span, _)) => {
                        let lvl2 = cxt.lvl;
                        let dom_v = wrap_sub(bump, &self.sub, dom);
                        let d_t = mach.quote(bump, &decls, cxt.lvl, dom_v);
                        let c2 = mach.bind_name(bump, &cxt, "_", d_t, dom_v);
                        self.solvable.push(lvl2);
                        (PatternDetail::Any(*span), c2)
                    }
                    Some(Pattern::Con(cn, csubs, _)) => {
                        let domf = mach.force_v(bump, &decls, wrap_sub(bump, &self.sub, dom));
                        let is_ctor2 = v_tag(domf) == 7
                            && match v_xcell_of(domf) {
                                XCell::Sum { cases: c2s, .. } => c2s.iter().any(|c| *c == cn.data),
                                _ => false,
                            };
                        if is_ctor2 {
                            // 解构：子 walk_con 入口绑自己的 head 槽（槽值即
                            // 本字段的实例化 rigid u）。同时记一笔待提升的嵌套
                            // 位置，臂走查成功后以终态 σ 结算（参考版同款）。
                            self.pending_pos.push((
                                {
                                    let mut p = self.cur_path.clone();
                                    p.push((name.data.clone(), details.len()));
                                    p
                                },
                                domf,
                            ));
                            self.cur_path.push((name.data.clone(), details.len()));
                            let walked = self
                                .walk_con(mach, bump, cn, csubs, dom, u, &cxt)?
                                .matched();
                            self.cur_path.pop();
                            match walked {
                                Some(dc) => dc,
                                None => return Ok(Walk::Unreachable),
                            }
                        } else {
                            if !csubs.is_empty() {
                                return Err(Error(format!(
                                    "`{}` 不是构造子，不能带子模式解构",
                                    cn.data
                                )));
                            }
                            let lvl2 = cxt.lvl;
                            let dom_v = wrap_sub(bump, &self.sub, dom);
                            let d_t = mach.quote(bump, &decls, cxt.lvl, dom_v);
                            let c2 = mach.bind_name(bump, &cxt, &cn.data, d_t, dom_v);
                            self.solvable.push(lvl2);
                            (PatternDetail::Bind(cn.clone()), c2)
                        }
                    }
                };
                cxt = new_cxt;
                details.push(detail);
                ctor_datas.push(SumDataV {
                    name: bump.alloc_str(bname),
                    val: u,
                    icit: bicit,
                });
                let env = env_ext(bump, p.env, u);
                ty = mach.eval(bump, &decls, env, p.body);
            } else {
                break tyf;
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
        // spec 以当前 σ 作种子；方程的解累积进 spec.acc，方程后取回为新 σ
        // （臂边界由 compile 的快照回滚）。
        let ret_sum = mach.force_v(bump, &decls, wrap_sub(bump, &self.sub, ret));
        if !(v_tag(ret_sum) == 7 && matches!(v_xcell_of(ret_sum), XCell::Sum { .. })) {
            return Err(Error(format!(
                "构造子 {} 的返回类型不是和类型",
                name.data
            )));
        }
        let mut spec = SpecSolve {
            solvable: &self.solvable,
            acc: self.sub.clone(),
        };
        let spec_res = Self::unify_indices(mach, bump, &cxt, cxt.lvl, &mut spec, head_sum, ret_sum, &name.data);
        self.sub = spec.acc;
        if spec_res.is_err() {
            return Ok(Walk::Unreachable);
        }
        // 头部精化（无条件）：被匹配变量本身写入精化替换。`V a`、`add a zero`
        // 这类依赖被匹配变量的类型，要等 a := zero / a := succ t 之后才能
        // 归约——force 在读点推进 VSub（σ 链逐层推开）。只对"本子句里尚未
        // 精化的变量"做（σ 已有解的不会再以 bare Rigid 出现）。存入的构造
        // 子值用当前 σ 包裹——后续嵌套方程的解经组合链对其保持可见。
        let head_val_f = mach.force_v(bump, &decls, wrap_sub(bump, &self.sub, head_val));
        if v_tag(head_val_f) == 0 {
            let x = v_lvl_of(head_val_f);
            if x < cxt.lvl && self.solvable.contains(&x) && !self.sub.has(x) {
                let ctor_val = v_xcell(bump.alloc(XCell::SumCase {
                    typ: head_sum,
                    case_name: bump.alloc_str(&name.data),
                    datas: bump.alloc_slice_fill_iter(ctor_datas),
                }));
                // 环守卫（浅 occurs）失败时跳过精化，不阻断分支检查
                if !val_mentions_lvl(&mach.spine, &mach.defs, ctor_val, x) {
                    let wrapped = wrap_sub(bump, &self.sub, ctor_val);
                    self.sub = SubstV::extend(&self.sub, x, wrapped);
                }
            }
        }
        Ok(Walk::Matched(PatternDetail::Con(name.clone(), details), cxt))
    }
}
