use smol_str::SmolStr;

use crate::parser_lib::{Span, ToSpan};

use super::{
    Decl, Either, Env, Error, Infer, PatternDetail, Rc, Tm, Val,
    cover_at, fmt_path, PosCover,
    cxt::Cxt,
    empty_span,
    parser::syntax::{Icit, Pattern, Raw},
};

type Constructor = Span<SmolStr>;

#[derive(Debug, Clone)]
pub enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（L07 同文案：`match 不完整：模式位置 {path} 缺少
    /// 构造子 {ctor}`；2026-09-18 评审修复 P0 的 L13 移植）。
    IncompleteNested(String),
}

impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::Unreachable(body) => write!(f, "unreachable pattern: {}", body),
            Warning::Unmatched(pat) => write!(f, "non-exhaustive pattern: `{}` not covered", pat),
            Warning::IncompleteNested(msg) => write!(f, "{msg}"),
        }
    }
}

pub struct Compiler {
    warnings: Vec<Warning>,
    pub pats: Vec<(PatternDetail, Rc<Tm>)>,
    ret_type: Rc<Val>,
    /// 分支体类型错误收集：不短路，一次性报全（签名与决策树版一致）。
    errors: Vec<Error>,
    /// 隐式绑定器名计数器（产出 `_l0`/`_l1`…）。同一构造子在**元组模式**里
    /// 出现多次时，每个出现的隐式绑定器必须拿到不同名——否则臂上下文里
    /// 两个 `_l0` 互相遮蔽，`Raw` 回读取错槽。
    implicit_counter: usize,
    /// 嵌套覆盖检查的记账（L07 修复 5 的 L13 移植，2026-09-18 评审 P0）：
    /// 嵌套 `Con` 字段位置的可达性从未被枚举会让非穷尽 match 被静默接受。
    /// 两段式：走查中只记 (路径, 字段 Sum)；臂特化**成功后**才提升为带
    /// 臂上下文快照的完整记账——L13 的精化载体是 `update_cxt`（解进臂
    /// Cxt 的 env 槽，不是 σ），嵌套位置的索引精化（如 `Vec[Nat] (succ
    /// zero)` 的尾部上 `nil` 把 `_l0` 解成 `zero`）在 check_pm 期就已写进
    /// 臂上下文，延迟探测以臂上下文跑 unify_pm 即可看到。整臂特化失败
    /// （荒谬臂）时丢弃（其位置不产生覆盖义务，语义由臂错误承担）。
    nested_checks: Vec<NestedCheck>,
    /// 本臂走查中的待提升位置（臂特化成功后结算）。
    pending_pos: Vec<(Vec<(String, usize)>, Rc<Val>)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
}

/// 一个嵌套拆分位置的记账：路径 = 根到被拆字段的 (构造子名, 字段下标)
/// 链；`field_sum` 是该字段在**走查实例化**下的 Sum 值（内含走查 rigid，
/// 精化状态在 arm_cxt 的 env 里）；arm_cxt 是臂特化成功后的精化上下文
/// 快照（延迟探测要在与臂方程同构的状态下跑）。
struct NestedCheck {
    path: Vec<(String, usize)>,
    field_sum: Rc<Val>,
    arm_cxt: Cxt,
}

// TEMP-PROBE: 参考版可达性探测计数。
thread_local! {
    pub static PROBE_COUNT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// 采样窗口内的探测次数增量用（`l13lspsample` 打印）。
pub fn probe_count() -> u64 {
    PROBE_COUNT.with(|c| c.get())
}

impl Compiler {
    pub fn new(ret_type: Rc<Val>) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
            errors: Vec::new(),
            implicit_counter: 0,
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
        }
    }

    /// 隐式绑定器名：`_{绑定器名}{序号}`（顶层绑定器名为空 → `_0`/`_1`…）。
    fn make_implicit_name(&mut self, head_name: &Span<SmolStr>) -> Span<SmolStr> {
        let counter = self.implicit_counter;
        self.implicit_counter += 1;
        head_name.clone().map(|x| SmolStr::new(format!("_{}{}", x, counter)))
    }

    /// 构造子可达性探测（值级，L07 `probe_accessible` 口径）：构造子类型经
    /// 命名空间解析取出（decl 只登记限定名 `Enum.case`，无裸名别名），走 Π 链
    /// 实例化——头部 Sum 的隐式参数用其实参，其余绑定器用超出上下文的 scratch
    /// 层 fresh rigid（同为刚性，可被方程解出；探测状态弃掉即回滚），返回类型再
    /// 与头部类型跑一次索引方程。成功 = 该构造子可能出现在头部类型的值里；
    /// 结构冲突（`Vec[A] zero` 上不可能有 `cons`）= absurd，不报缺失。
    fn probe_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        head_sum: &Rc<Val>,
        ctor: &Constructor,
    ) -> bool {
        // TEMP-PROBE: 参考版可达性探测次数（与孪生同口径对比）。
        PROBE_COUNT.with(|c| c.set(c.get() + 1));
        let (sum_name, head_params, impl_vals) = match head_sum.as_ref() {
            Val::Sum(name, params, ..) => {
                if params.is_empty() {
                    // 无参数 Sum 的短路（`enum Nat { zero; succ(x: Nat) }` 类，
                    // 普通枚举全在此列）：头部隐式实参表为空（impl_vals 空 →
                    // Π 链只绑 fresh rigid，不可能失败），构造子返回类型的两侧
                    // 参数表都是空 → `unify_indices` 的空表 zip 恒真，探测结论
                    // 恒为「可达」。直接短路省掉每构造子一次限定名解析 + hover
                    // 渲染（`infer_expr(Raw::Obj(..))` 会对声明的 case span 推一条
                    // hover——可达性探测不看渲染面）。带参数/索引的 Sum（Vec 型
                    // GADT）仍走完整探测。
                    return true;
                }
                (
                    name.clone(),
                    params.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
                    params
                        .iter()
                        .filter(|p| p.3 == Icit::Impl)
                        .map(|p| p.1.clone())
                        .collect::<Vec<_>>(),
                )
            }
            _ => return false,
        };
        // 限定名解析交给命名空间机制（struct 脱糖的 `Type.mk` 形态同路）
        let ctor_raw = Raw::Obj(Box::new(Raw::Var(sum_name.clone())), Some(ctor.clone()));
        let entry_ty = match infer.infer_expr(cxt, ctor_raw) {
            Ok((_, ty)) => ty,
            Err(_) => return false,
        };
        // 每个探测独立充值：多构造子枚举的逐 ctor 探测不互相挤占共享池
        // （探测本身回滚，只有燃料单向消耗）。
        infer.refuel();
        let snap = infer.meta.clone();
        // Π 链逐层实例化：头部 Sum 的隐式参数用其实参，其余绑定器用**探测
        // 上下文里的 fresh rigid**。绑定进探测器 cxt 而非用超上下文的 scratch
        // 层——L13 的 `unify_pm` 走 `update_cxt`（`lvl2ix`），层超出上下文会
        // 直接 panic（L12 的 σ 口径无此约束）。
        let mut probe_cxt = cxt.clone();
        let mut ty = entry_ty;
        let mut impl_idx = 0;
        let ok = loop {
            let tyf = infer.force(&probe_cxt.decl, &ty);
            match tyf.as_ref() {
                Val::Pi(bname, _, dom, closure) => {
                    let (bname, dom, closure) = (bname.clone(), dom.clone(), closure.clone());
                    let u = if impl_idx < impl_vals.len() {
                        let v = impl_vals[impl_idx].clone();
                        impl_idx += 1;
                        v
                    } else {
                        Rc::new(Val::vvar(probe_cxt.lvl))
                    };
                    let a_t = infer.quote(&probe_cxt.decl, probe_cxt.lvl, &dom);
                    probe_cxt = probe_cxt.bind(bname, a_t, dom);
                    ty = infer.closure_apply(&probe_cxt.decl, &closure, u);
                }
                _ => break Self::unify_indices(infer, &probe_cxt, &sum_name, &head_params, &tyf)
                    // fuel 耗尽的失败是预算问题而非结构冲突：按可达处理
                    // （保守地要求覆盖）。反方向（判不可达 → 覆盖检查放
                    // 过该构造子）会让深负载下的非穷尽 match 被静默接受
                    // （L07 修复 2 同款，unsound → incomplete）。
                    || infer.fuel_exhausted(),
            }
        };
        infer.meta = snap;
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽
    /// **特化**合一，头部一侧在前——两侧都是可解变量时解方向是「头部变量
    /// := 构造子侧值」。探测只问可达性，精化出的上下文弃掉即回滚。
    fn unify_indices(
        infer: &mut Infer,
        cxt: &Cxt,
        sum_name: &Span<SmolStr>,
        head_params: &[Rc<Val>],
        ret_ty: &Rc<Val>,
    ) -> bool {
        let ret_sum = infer.force(&cxt.decl, ret_ty);
        let rp = match ret_sum.as_ref() {
            Val::Sum(name, params, ..) if name.data == sum_name.data => params,
            _ => return false,
        };
        if head_params.len() != rp.len() {
            return false;
        }
        let span = empty_span(());
        head_params
            .iter()
            .zip(rp.iter())
            .all(|(a, b)| infer.unify_pm(cxt, a, &b.1, span).is_ok())
    }

    /// 可达性判定 + 每 match 的 memo（`constrs[i]`；覆盖检查与臂前置过滤
    /// 共用——同一入口上下文里同构造子判定不变，探测本身是纯探测）。
    fn ctor_accessible(
        infer: &mut Infer,
        cxt: &Cxt,
        typ: &Rc<Val>,
        constrs: &[Constructor],
        memo: &mut [Option<bool>],
        i: usize,
    ) -> bool {
        match memo[i] {
            Some(b) => b,
            None => {
                let b = Self::probe_accessible(infer, cxt, typ, &constrs[i]);
                memo[i] = Some(b);
                b
            }
        }
    }

    /// 单臂模式走查（L07 口径，2026-09-18 自决策树矩阵重写）：在**顶层整
    /// 模式**上逐构造子下钻，为每个构造子字段造一个 `PatternDetail` 槽，并把
    /// 对应模式变量绑进臂上下文。
    ///
    /// 槽位纪律（与运行时 `eval_aux` 的值-模式 zip 严格同序同数）：头部 Sum
    /// 的隐式参数**不占槽**（用头部实参直接实例化构造子 Π 链），构造子其余
    /// 绑定器各占一槽——用户写的子模式按 icit 对位消费（显式模式不被隐式
    /// 绑定器消费，反之亦然），没写/对不上就补虚通配。
    ///
    /// L13 适配：构造子以**限定名** `Enum.case` 登记（`elaboration.rs` 明写
    /// no bare caseName alias），取构造子类型走 `infer_expr(Raw::Obj(..))` 交给
    /// 命名空间机制，不手工拼键；`PatternDetail` 是三字段形态
    /// （`Con(idx, name, subs)` / `Any(var, param, icit)` / `Bind`），`idx` =
    /// 构造子在 Sum 里的下标、`Any.var` 由 `make_implicit_name` 计数生成。
    fn walk_pat(
        &mut self,
        infer: &mut Infer,
        cxt: &Cxt,
        pat: &Pattern,
        head_ty: &Rc<Val>,
    ) -> Result<(PatternDetail, Cxt), Error> {
        match pat {
            Pattern::Any(_, icit) => {
                // 整值通配：占一槽（无绑定器名 → `_0`/`_1`…）
                let b = self.make_implicit_name(&empty_span(SmolStr::new("")));
                let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
                let cxt2 = cxt.bind(b.clone(), a_t, head_ty.clone());
                Ok((PatternDetail::Any(b, Some(empty_span(SmolStr::new(""))), icit.to_icit()), cxt2))
            }
            Pattern::Con(name, subs, _) => {
                let head_sum = infer.force(&cxt.decl, head_ty);
                let (sum_name, sum_params, cases) = match head_sum.as_ref() {
                    Val::Sum(n, params, cases, _) => (n.clone(), params.clone(), cases.clone()),
                    _ => (
                        empty_span(SmolStr::new("")),
                        Rc::new(Vec::new()),
                        Rc::new(Vec::new()),
                    ),
                };
                let case_idx = match cases.iter().position(|c| c.data == name.data) {
                    Some(i) => i,
                    None => {
                        // 判型上不是该类型的构造子（含非 Sum 头）：裸变量
                        // 模式，按变量名绑一槽（决策树 `is_var_like` 同款）
                        if !subs.is_empty() {
                            return Err(Error(
                                name.clone().map(|n| {
                                    format!("`{n}` 不是该类型的构造子，不能带子模式解构")
                                }),
                                vec![],
                            ));
                        }
                        let a_t = infer.quote(&cxt.decl, cxt.lvl, head_ty);
                        let cxt2 = cxt.bind(name.clone(), a_t, head_ty.clone());
                        return Ok((PatternDetail::Bind(name.clone()), cxt2));
                    }
                };
                // 构造子类型：限定名 `Enum.case`，解析交给命名空间机制
                // 构造子类型：限定名 `Enum.case`。廉价通路 = decl 表直查
                //（`infer_expr(Raw::Obj(..))` 对 `Obj(Var(sum), Some(case))`
                // 的解析结果就是 `decl[qual].vty`，省掉完整解析链）。未命中
                // （import 限定 Sum 等）回退原 infer_expr 全链路。悬停面
                // 不变：case token 上的构造子条目仍由下方 push_hover 登记
                //（infer_expr 路径里 push_qualified_hover 只走 receiver
                // 链，对本形态在 token 上本就无条目）。
                let key = SmolStr::new(format!("{}.{}", sum_name.data, name.data));
                let (constr_pi, ctor_key) = match cxt.decl.get(&key) {
                    // decl 条目： (def span, Tm, VAL, Ty, VTy, prim, typ_pretty)
                    Some((_, _, _, _, vty, _, _)) => (vty.clone(), Some(key.clone())),
                    None => {
                        let ctor_raw =
                            Raw::Obj(Box::new(Raw::Var(sum_name.clone())), Some(name.clone()));
                        let (tm, constr_pi) = infer.infer_expr(cxt, ctor_raw)?;
                        // 解析出的全键（Tm::Decl 的键）供 detail 记录限定名
                        let ctor_key = match tm.as_ref() {
                            Tm::Decl(k) => Some(k.data.clone()),
                            _ => None,
                        };
                        (constr_pi, ctor_key)
                    }
                };
                // 悬停 / goto-definition：模式 token → 构造子。无参构造子给
                // 构造子值（`Boolean::true`），参数化构造子给 Π 签名而不是不可读
                // 的 λ 串；定义 span 指向枚举声明里的 case 名。渲染走 decl 键
                // 缓存（push_ctor_hover）：构造子 hover 值是闭合值，串与使用处
                // 上下文无关。
                {
                    let hover_val = match cxt.decl.get(&key).or_else(|| cxt.decl.get(&name.data)) {
                        Some((_, _, v, _, _, _, _)) => match v.as_ref() {
                            Val::Lam(..) => constr_pi.clone(),
                            _ => v.clone(),
                        },
                        None => constr_pi.clone(),
                    };
                    infer.push_ctor_hover(cxt, name.to_span(), cases[case_idx].to_span(), &hover_val, key.as_str());
                }
                // 头部 Sum 的隐式参数（构造子 Π 链最前的 n 个绑定器）不占槽
                let mut impl_vals: Vec<Rc<Val>> = sum_params
                    .iter()
                    .filter(|p| p.3 == Icit::Impl)
                    .map(|p| p.1.clone())
                    .collect();
                impl_vals.reverse();
                let mut cxt_arm = cxt.clone();
                let mut ty = constr_pi;
                let mut next = 0usize;
                let mut details: Vec<PatternDetail> = Vec::new();
                loop {
                    let tyf = infer.force(&cxt_arm.decl, &ty);
                    let (bname, bicit, dom, closure) = match tyf.as_ref() {
                        Val::Pi(bname, bicit, dom, closure) => {
                            (bname.clone(), *bicit, dom.clone(), closure.clone())
                        }
                        _ => break,
                    };
                    if let Some(v) = impl_vals.pop() {
                        ty = infer.closure_apply(&cxt_arm.decl, &closure, v);
                        continue;
                    }
                    // 该绑定器对应的用户子模式：icit 对位才消费
                    let head: Option<&Pattern> = match subs.get(next) {
                        Some(p) if p.get_icit().to_icit() == bicit => subs.get(next),
                        _ => None,
                    };
                    // 该字段自身的层（占槽前）：Π 闭包实例化的 fresh rigid
                    let u = Rc::new(Val::vvar(cxt_arm.lvl));
                    let detail = match head {
                        Some(Pattern::Con(vname, csubs, Either::Name(pname)))
                            if bicit == Icit::Impl && csubs.is_empty() =>
                        {
                            // 用户具名隐式绑定器（`cons[l=l0](..)`）：按用户
                            // 变量名占槽，参数名回写进 detail
                            next += 1;
                            let a_t = infer.quote(&cxt_arm.decl, cxt_arm.lvl, &dom);
                            cxt_arm = cxt_arm.bind(vname.clone(), a_t, dom.clone());
                            PatternDetail::Any(vname.clone(), Some(pname.clone()), Icit::Impl)
                        }
                        Some(Pattern::Any(_, _)) => {
                            next += 1;
                            let b = self.make_implicit_name(&bname);
                            let a_t = infer.quote(&cxt_arm.decl, cxt_arm.lvl, &dom);
                            cxt_arm = cxt_arm.bind(b.clone(), a_t, dom.clone());
                            PatternDetail::Any(b, Some(bname.clone()), bicit)
                        }
                        Some(p @ Pattern::Con(..)) => {
                            next += 1;
                            // 嵌套 Con：字段 dom 是含该子构造子的 Sum 时记一笔
                            // 待提升的嵌套位置（该字段位置沿 ctor 路径的可达
                            // 构造子必须有臂覆盖），臂特化成功后以臂上下文结
                            // 算（见 compile）。字段 Sum 用走查实例化下的值
                            // （内含走查 rigid，精化在臂上下文里）。cur_path
                            // 先推后弹（更深的记账要看到完整链）。
                            let Pattern::Con(cn, ..) = p else {
                                unreachable!()
                            };
                            let field_sum = infer.force(&cxt_arm.decl, &dom);
                            let is_ctor = matches!(field_sum.as_ref(),
                                Val::Sum(_, _, cases, _)
                                    if cases.iter().any(|c| c.data == cn.data)
                            );
                            self.cur_path.push((name.data.to_string(), details.len()));
                            let (d, c2) = self.walk_pat(infer, &cxt_arm, p, &dom)?;
                            self.cur_path.pop();
                            cxt_arm = c2;
                            if is_ctor {
                                let mut pa = self.cur_path.clone();
                                pa.push((name.data.to_string(), details.len()));
                                self.pending_pos.push((pa, field_sum));
                            }
                            d
                        }
                        None => {
                            // 用户没写这个字段（或 icit 对不上）：补虚槽
                            let b = self.make_implicit_name(&bname);
                            let a_t = infer.quote(&cxt_arm.decl, cxt_arm.lvl, &dom);
                            cxt_arm = cxt_arm.bind(b.clone(), a_t, dom.clone());
                            PatternDetail::Any(b, Some(bname.clone()), bicit)
                        }
                    };
                    details.push(detail);
                    ty = infer.closure_apply(&cxt_arm.decl, &closure, u);
                }
                if let Some(extra) = subs.get(next) {
                    // 模式比构造子字段多：叶上无法推进（决策树同文案）
                    return Err(Error(
                        match extra {
                            Pattern::Any(span, _) => span.map(|_| "invalid pattern".to_owned()),
                            Pattern::Con(span, _, _) => {
                                span.clone().map(|x| format!("invalid pattern {}", x))
                            }
                        },
                        vec![],
                    ));
                }
                Ok((
                    PatternDetail::Con(case_idx as u32, cases[case_idx].clone(), details, ctor_key),
                    cxt_arm,
                ))
            }
        }
    }

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写）。语义相对决策树
    /// 的三处收窄（覆盖只做顶层 / 遮蔽只认通配臂 / 特化失败静默跳过）同
    /// L10–L12，见 docs/l09l13-match-compiler-analysis-2026-09-17.md。
    ///
    /// 错误仍是**收集式**：某个臂的走查/特化/体检查失败只记进 `errors`，
    /// 其余臂照常检查（一次性报全），签名与决策树版一致。
    pub fn compile(
        &mut self,
        infer: &mut Infer,
        typ: Rc<Val>,
        arms: &[(Pattern, Raw)],
        cxt: &Cxt,
        target_val: Rc<Val>,
    ) -> Result<Vec<Warning>, Vec<Error>> {
        self.warnings = Vec::new();
        self.errors = Vec::new();
        self.nested_checks = Vec::new();
        self.pending_pos = Vec::new();
        self.cur_path = Vec::new();
        let typ = infer.force(&cxt.decl, &typ);
        let (constrs, ctor_names): (Vec<Constructor>, Vec<SmolStr>) = match typ.as_ref() {
            Val::Sum(_, _, cases, _) => (
                cases.to_vec(),
                cases.iter().map(|c| c.data.clone()).collect(),
            ),
            _ => (vec![], vec![]),
        };
        // 构造子可达性 memo（下标对齐 constrs）：覆盖检查与臂前置过滤共用同一
        // 判定（决策树 filter 的 probe_memo 同口径——同节点同构造子判定不变）。
        let mut accessible: Vec<Option<bool>> = vec![None; constrs.len()];
        // 覆盖检查：可达且无臂覆盖 → Unmatched（形态 = 「构造子 + 999 通配」，
        // 与 L10–L12 的产出一致）。不可达（如 `Vec[A] zero` 上的 `cons`）不报
        // ——索引方程不可解即结构上不可能。
        for (i, ctor) in constrs.iter().enumerate() {
            if Self::ctor_accessible(infer, cxt, &typ, &constrs, &mut accessible, i)
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
            // 本臂走查起点无遗留记账（上一臂已结算/丢弃，防御性清空）。
            self.pending_pos.clear();
            self.cur_path.clear();
            // 臂前置过滤（决策树构造子分支上的可达性筛选同口径）：首模式是头部
            // Sum 的构造子、但索引方程不可解（`Vec[A] zero` 上的 `cons`）——
            // 该臂不可能匹配，静默跳过并按「从未走到」记 `Unreachable`；不
            // 让它落进 check_pm_final 报出假的特化错误。
            if let Pattern::Con(name, _, _) = pat {
                if let Some(i) = ctor_names.iter().position(|c| c.as_str() == name.data.as_str()) {
                    if !Self::ctor_accessible(infer, cxt, &typ, &constrs, &mut accessible, i) {
                        unreachable.push(Warning::Unreachable(body.clone()));
                        continue;
                    }
                }
            }
            let (detail, cxt_walk) = match self.walk_pat(infer, cxt, pat, &typ) {
                Ok(x) => x,
                Err(e) => {
                    // 走查失败臂的嵌套记账一并丢弃
                    self.pending_pos.clear();
                    self.errors.push(e);
                    continue;
                }
            };
            // 特化用的模式从**走查产出的 detail** 重建（树 `patcon_raw` 同
            // 血统）：L13 的 check_pm 是依赖式特化——构造子隐含参数（如
            // `cons` 的 `l`，出现在字段类型 `Vec[A] l` 里）必须按**走查已绑
            // 定的具名 rigid** 传入（`[l=_l0]`），否则 check_pm 会为它新解
            // 一个 meta，臂上下文里的 `xs : Vec[A] _l0` 与特化出的
            // `Vec[A] ?m` 各说各话（实测 can't unify for unsolved meta）。
            // 用户写法、子模式形态仍原样保留在 detail 里。
            let raw = detail_to_raw(&detail);
            let cxt_arm = match infer.check_pm_final(
                &cxt_walk,
                raw,
                typ.clone(),
                target_val.clone(),
            ) {
                // L13 的 check_pm_final 返回**精化后的 Cxt**（update_cxt 血统，
                // 不是 σ）——直接当臂上下文用。
                Ok((_, cxt)) => cxt,
                Err(e) => {
                    // 荒谬臂（特化失败）：其嵌套位置不产生覆盖义务——臂本身
                    // 的特化错误已承担语义（L07 荒谬臂 clear pending 同款）
                    self.pending_pos.clear();
                    self.errors.push(e);
                    continue;
                }
            };
            // 嵌套位置结算（两段式）：此刻本臂特化方程已解出、精化写进了
            // 臂上下文的 env 槽，字段 Sum 置于臂上下文之下探测才能看到索引
            // 精化（如 `Vec[Nat] (succ zero)` 的尾部上 `nil` 不可达）。
            for (path, field_sum) in std::mem::take(&mut self.pending_pos) {
                self.nested_checks.push(NestedCheck {
                    path,
                    field_sum,
                    arm_cxt: cxt_arm.clone(),
                });
            }
            let ret_type = match self.ret_type.as_ref() {
                Val::Flex(_, _) => self.ret_type.clone(),
                _ => {
                    let q = infer.quote(&cxt_arm.decl, cxt_arm.lvl, &self.ret_type);
                    infer.eval(&cxt_arm.decl, &cxt_arm.env, &q)
                }
            };
            match infer.check::<false>(&cxt_arm, body.clone(), &ret_type) {
                Ok(ret) => self.pats.push((detail, ret)),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            }
            if is_catch_all(pat, &ctor_names) {
                shadowed = true;
            }
        }
        if !self.errors.is_empty() {
            Err(std::mem::take(&mut self.errors))
        } else {
            let mut out: Vec<Warning> = unreachable
                .into_iter()
                .chain(std::mem::take(&mut self.warnings))
                .collect();
            // 嵌套位置的覆盖检查（沿模式下钻逐节点，L07 同款）：每条记账在
            // 记录臂的实例化（臂上下文快照）下探测字段 Sum 的可达构造子；
            // 覆盖集 = 已走查臂的 PatternDetail 沿路径的结构贡献（var/Any =
            // 全覆盖；祖先异 ctor = 不可达该位置；同 ctor 前缀 = 贡献其末端
            // 构造子）。可达集取各记账臂探测的并集（保守：任一臂实例化下
            // 可达的构造子都要求被覆盖）。荒谬臂 / 被遮蔽臂不在 pats 里，
            // 天然不贡献覆盖——与运行时首匹配结构语义一致。
            let mut reported = std::collections::HashSet::new();
            for nc in std::mem::take(&mut self.nested_checks) {
                // 字段 Sum 在臂上下文下 force：走查 rigid 的索引精化由
                // unify_pm 探测时经臂 env 的 already-refined 查询看到
                //（L13 精化载体是 update_cxt，不是 σ/wrap_sub）。
                let field_sum = infer.force(&nc.arm_cxt.decl, &nc.field_sum);
                let ctor_cases: Vec<Constructor> = match field_sum.as_ref() {
                    Val::Sum(_, _, cs, _) => cs.to_vec(),
                    _ => continue,
                };
                for ctor in ctor_cases {
                    if !Self::probe_accessible(infer, &nc.arm_cxt, &field_sum, &ctor) {
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
    }


    pub fn eval_aux(
        infer: &Infer,
        heads: &Rc<Val>,
        decl: &Decl,
        cxt: &Env,
        arms: &[(PatternDetail, Rc<Tm>)],
    ) -> Option<(Rc<Tm>, Env)> {
        // Only the head constructor is needed for dispatch.  Forcing the
        // whole scrutinee here would re-walk a deep constructor chain at
        // every match step (O(n) per step, i.e. O(n^2) for `nat_add_helper`
        // on a big literal).  Force only non-constructor heads (e.g. metas).
        let (index, params) = match heads.as_ref() {
            Val::SumCase {
                is_trait: _,
                typ: _,
                index,
                datas,
            } => (*index, datas.clone()),
            // Native Nat: dispatch on the constructor head without building
            // a unary chain.  `Nat 0` is `zero`; `Nat k` (k>0) is `succ` of
            // `Nat (k-1)` — the O(1) analogue of walking one `succ`.
            Val::Nat(k) if *k == 0 => (0, Rc::new(vec![])),
            Val::Nat(k) => (1, Rc::new(vec![(
                empty_span(SmolStr::new("n")),
                Val::Nat(k - 1).into(),
                Icit::Expl,
            )])),
            _ => match infer.force(decl, heads).as_ref() {
                Val::SumCase {
                    is_trait: _,
                    typ: _,
                    index,
                    datas,
                } => (*index, datas.clone()),
                Val::Nat(k) if *k == 0 => (0, Rc::new(vec![])),
                Val::Nat(k) => (1, Rc::new(vec![(
                    empty_span(SmolStr::new("n")),
                    Val::Nat(k - 1).into(),
                    Icit::Expl,
                )])),
                _ => (u32::MAX, Rc::new(vec![])),
            },
        };

        arms.iter()
            .filter_map(|(pattern, body)| match pattern {
                PatternDetail::Con(constr_, _, item_pats, _) if *constr_ == index => {
                    params
                        .iter()
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
            .or_else(|| {
                arms.iter()
                    .filter_map(|(pattern, body)| match pattern {
                        PatternDetail::Any(_, _, _) => {
                            Some((body.clone(), cxt.prepend(heads.clone())))
                        }
                        PatternDetail::Bind(_) => Some((body.clone(), cxt.prepend(heads.clone()))),
                        PatternDetail::Con(..) => None,
                    })
                    .next()
            })
    }
}

/// 走查 detail → 特化用 `Raw`（树 `PatConstructor::detail_to_raw` 同款，
/// 2026-09-18 随逐臂移植降为自由函数）：把走查期**生成的**隐式绑定器名以
/// `[param=name]` 具名实参回写，让 `check_pm_final` 复用同一批已绑定
/// rigid；无名通配发 `Raw::Hole` 让 elaborator 自动填充。
fn detail_to_raw(d: &PatternDetail) -> Raw {
    match d {
        PatternDetail::Con(_, name, subs, qual) => {
            // 全限定 decl 键（走查期自 decl 表解析，span 保持 case token）：
            // check_pm 的 Var 臂 O(1) 精确命中，免后缀回退扫描 + 实时渲染
            let head = match qual {
                Some(q) => name.clone().map(|_| q.clone()),
                None => name.clone(),
            };
            subs.iter().fold(Raw::Var(head), |acc, sub| {
            let icit = match sub {
                PatternDetail::Any(var_name, param_name, Icit::Impl) => {
                    if var_name.data.is_empty() {
                        // 无名隐式 → 让 elaborated 自动填充
                        Either::Icit(Icit::Impl)
                    } else if let Some(pname) = param_name {
                        // 具名隐式 + 显式参数名：`[pi_param=var]`
                        // 让 insert_go 自动填充前置 Impl 且只绑定本个
                        Either::Name(pname.clone())
                    } else {
                        // 兼容：剥离 `_` 前缀派生参数名
                        Either::Name(var_name.clone().map(|s| SmolStr::new(&s[1..])))
                    }
                }
                PatternDetail::Any(_, _, Icit::Expl) => Either::Icit(Icit::Expl),
                PatternDetail::Bind(_) => Either::Icit(Icit::Expl),
                PatternDetail::Con(..) => Either::Icit(Icit::Expl),
            };
            Raw::App(Box::new(acc), Box::new(detail_to_raw(sub)), icit)
            })
        }
        PatternDetail::Any(name, _, _) | PatternDetail::Bind(name) => {
            if name.data.is_empty() {
                Raw::Hole(empty_span(()))
            } else {
                Raw::Var(name.clone())
            }
        }
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
