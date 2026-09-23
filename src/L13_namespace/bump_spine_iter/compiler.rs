//! compiler：模式匹配编译（参考版 pattern_match.rs 的逐臂下钻移植）——
//! `Compiler`/`Warning`/`NestedCheck` 与覆盖检查助手（`case_spans`/
//! `sum_name_span`/`detail_to_raw`/`covers`/`is_catch_all`）。原
//! bump_spine_iter.rs 的 "模式匹配编译" 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::rc::Rc;

use super::parser::syntax::{Either, Icit, Pattern, Raw};

use super::env::env_ext;
use super::machine::{clone_cxt, Cxt, Machine};
use super::spine::is_flex;
use super::syntax::{SumParamV, Tm, V, XCell, v_lvl, v_pi_of, v_tag, v_xcell_of};

use crate::parser_lib::ToSpan;

use super::{cover_at, empty_span, fmt_path, Error, PatternDetail, PosCover};


// 模式匹配编译（参考版 pattern_match.rs 的逐臂下钻移植）
// --------------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) enum Warning {
    Unreachable(Raw),
    Unmatched(Pattern),
    /// 嵌套位置覆盖缺失（L07 同文案：`match 不完整：模式位置 {path} 缺少
    /// 构造子 {ctor}`；2026-09-18 评审修复 P0 的 L13 移植）。
    IncompleteNested(String),
}

/// Display 文案与参考版 pattern_match.rs 同款（match 非穷尽/不可达作为
/// 错误文案输出：`warnings.iter().map(|w| w.to_string()).join("; ")`）。
impl std::fmt::Display for Warning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Warning::Unreachable(body) => write!(f, "unreachable pattern: {}", body),
            Warning::Unmatched(pat) => write!(f, "non-exhaustive pattern: `{}` not covered", pat),
            Warning::IncompleteNested(msg) => write!(f, "{msg}"),
        }
    }
}

pub(crate) struct Compiler<'a> {
    pub(super) warnings: Vec<Warning>,
    pub(crate) pats: Vec<(PatternDetail, &'a Tm<'a>)>,
    ret_type: V,
    /// 分支体类型错误收集：不短路，一次性报全（参考版 `errors` 字段同义）。
    errors: Vec<Error>,
    /// 隐式绑定器名计数器（产出 `_l0`/`_l1`…）。同一构造子在元组模式里出现
    /// 多次时，每个出现的隐式绑定器必须拿到不同名——否则臂上下文里两个
    /// `_l0` 互相遮蔽，`Raw` 回读取错槽。
    implicit_counter: u32,
    /// 嵌套覆盖检查的记账（参考版 pattern_match.rs 同款，两段式）：走查中
    /// 只记 (路径, 字段 Sum)；臂特化**成功后**提升为带臂上下文快照的完整
    /// 记账——L13 的精化载体是 `update_cxt`（解进臂 Cxt 的 env 槽），嵌套
    /// 位置的索引精化在 check_pm 期已写进臂上下文，延迟探测以臂上下文跑
    /// unify_pm 即可看到。整臂特化失败（荒谬臂）时丢弃。
    nested_checks: Vec<NestedCheck<'a>>,
    /// 本臂走查中的待提升位置（臂特化成功后结算）。
    pending_pos: Vec<(Vec<(String, usize)>, V)>,
    /// 当前下钻路径（根到当前字段的 ctor 选择链），臂内 push/pop 平衡。
    cur_path: Vec<(String, usize)>,
    /// `case_spans` 的 per-Compiler 缓存：一次 match 编译内 decl 表只读，
    /// 同一 Sum 的 cases span 回填恒定——根走查 / 嵌套走查 / compile 头 /
    /// nested 结算各算一遍纯属重复（每 cases 元素一次 format! + decls 查找
    /// + SmolStr）。键 = Sum 名（bump 串，'a 存放口径内）。
    case_spans_memo: FxHashMap<&'a str, Rc<Vec<crate::parser_lib::Span<SmolStr>>>>,
}

/// 一个嵌套拆分位置的记账（参考版 NestedCheck 的孪生形态）：路径 = 根到
/// 被拆字段的 (构造子名, 字段下标) 链；`field_sum` 是该字段在**走查实例
/// 化**下的 Sum 值；arm_cxt 是臂特化成功后的精化上下文快照。
struct NestedCheck<'a> {
    path: Vec<(String, usize)>,
    field_sum: V,
    arm_cxt: Cxt<'a>,
}

impl<'a> Compiler<'a> {
    pub(super) fn new(ret_type: V) -> Self {
        Compiler {
            warnings: Vec::new(),
            pats: Vec::new(),
            ret_type,
            errors: Vec::new(),
            implicit_counter: 0,
            nested_checks: Vec::new(),
            pending_pos: Vec::new(),
            cur_path: Vec::new(),
            case_spans_memo: FxHashMap::default(),
        }
    }

    /// `case_spans` 的缓存版（见 `case_spans_memo` 注）。
    fn case_spans_cached(
        &mut self,
        cxt: &Cxt<'a>,
        sum_name: &'a str,
        cases: &'a [&'a str],
    ) -> Rc<Vec<crate::parser_lib::Span<SmolStr>>> {
        if let Some(v) = self.case_spans_memo.get(sum_name) {
            return v.clone();
        }
        let v = Rc::new(case_spans(cxt, sum_name, cases));
        self.case_spans_memo.insert(sum_name, v.clone());
        v
    }

    /// 隐式绑定器名：`_{绑定器名}{序号}`（顶层绑定器名为空 → `_0`/`_1`…）。
    fn make_implicit_name(&mut self, head_name: &str) -> SmolStr {
        let counter = self.implicit_counter;
        self.implicit_counter += 1;
        SmolStr::new(format!("_{}{}", head_name, counter))
    }

    /// 构造子可达性探测（值级，L07 孪生 `probe_accessible` 口径）：构造子类型
    /// 经命名空间解析取出（decl 只登记限定名 `Enum.case`，无裸名别名——孪生
    /// 用限定名 `Raw::Obj` 探测，避免同名 case 的后缀 fallback 歧义），走 Π 链
    /// 实例化：头部 Sum 的隐式参数用其实参，其余绑定器用**探测上下文里的**
    /// fresh rigid（绑进探测器 cxt——`unify_pm` 的层级换算不容超上下文层）。
    /// 返回类型再与头部类型跑一次索引方程。成功 = 该构造子可能出现在头部类型
    /// 的值里；结构冲突（`Vec[A] zero` 上不可能有 `cons`）= absurd。
    ///
    /// **meta 探测回滚 journal 化（S3 轮）**：探测以 `mach.metas.clone()`
    /// 整表快照 + 出口整表搬回实现回滚——prelude-hdl 的 meta 表万条级，
    /// 每次探测一次 O(表) memcpy 是探测单次成本的大头（pcore/exhdl 采样
    /// ~11% 的主要成分）。改为 META_JOURNAL 帧（Call/Call has-flex 同款）：
    /// 入帧 → 探测（unify_pm 解头侧变量、infer 期新 meta 均经 journal 记
    /// 就地写）→ 出帧逆序恢复 + 截断——恢复语义与整表快照等价（恢复到探
    /// 测前状态），代价降到 O(探测期写入)。
    /// 跨 match 编译点的 (Sum, ctor) 探测结果缓存（轮内 TLS 表）经三种键
    /// 形落地实测均不划算（命中 5~6%，收益在噪声带），已按 <3% 纪律移除，
    /// 论证与计数存档见下方注释。
    fn probe_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        head_sum: V,
        ctor: &crate::parser_lib::Span<SmolStr>,
    ) -> bool {
        let (sum_name, head_params, impl_vals) = match v_xcell_of(head_sum) {
            XCell::Sum { name, params, .. } => {
                if params.is_empty() {
                    // 无参数 Sum 的短路（参考版 `probe_accessible` 同点同改）：
                    // 头部隐式实参表空 → Π 链只绑 fresh rigid（不可能失败），
                    // 构造子返回类型两侧参数表都空 → `unify_indices` 的空表 zip
                    // 恒真 ⇒ 探测结论恒为「可达」。省掉每构造子一次限定名解析
                    // + hover 渲染（孪生 `infer_expr` 同样推 hover）。
                    return true;
                }
                (
                    *name,
                    params.iter().map(|p| p.val).collect::<Vec<_>>(),
                    params
                        .iter()
                        .filter(|p| p.icit == Icit::Impl)
                        .map(|p| p.val)
                        .collect::<Vec<_>>(),
                )
            }
            _ => return false,
        };
        // S3 轮探测缓存（(Sum 形状, ctor) 轮内内容键控）探索结论存档：按
        // 单元字/内容字/层级塌缩三种键形落地实测，跨 match 编译点的重复
        // 探测在孪生现有形态下本就不存在——覆盖循环与臂前置过滤由
        // `ctor_accessible` 的 per-match memo 覆盖，无参 Sum 在入口短路，
        // 嵌套位置结算的各 (字段, ctor) 至多探一次；跨点重复仅占 5~6%
        //（pcore 282 探 16 中 / phdl 702 探 48 中 / exhdl 2397 探 136 中，
        // FUNC_PROF 计数），命中收益低于查询+守卫开销的噪声带（消融
        // `L13_NO_PROBE_CACHE` 交错实测 |Δ| ≤ 1.5%）。探测单次成本的大头
        // 是 meta 快照整表 clone（下方已改 META_JOURNAL 帧）与 clone_cxt，
        // 前者与命中无关、后者不在本文件可改范围。缓存按 <3% 收益回退
        // 纪律移除。
        let ctor_raw = Raw::Obj(
            Box::new(Raw::Var(sum_name_span(cxt, sum_name))),
            Some(ctor.clone()),
        );
        let entry_ty = match mach.infer_expr(bump, cxt, &ctor_raw) {
            Ok((_, ty)) => ty,
            Err(_) => return false,
        };
        // meta 探测回滚：整表 clone → META_JOURNAL 帧（Call/Call has-flex
        // 同款）。探测写入（unify_pm 解头侧变量、infer 期新 meta）先记帧，
        // 出口逆序恢复 + 截断——语义与 `mach.metas = snap` 等价（恢复到探测
        // 前状态），代价从 O(meta 表) memcpy 降到 O(探测期写入)；prelude-hdl
        // 的 meta 表万条级，这是探测单次成本的大头。
        let pre_meta_len = mach.metas.len();
        super::force::META_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
        // Π 链逐层实例化：头部 Sum 的隐式参数用其实参，其余绑定器用**探测
        // 上下文里的 fresh rigid**。绑定进探测器 cxt 而非超上下文的 scratch
        // 层——L13 的 `unify_pm` 走 `update_cxt` 的层级换算，层超出上下文会
        // 直接 panic（参考版同点同改）。
        let mut probe_cxt = clone_cxt(cxt);
        let mut ty = entry_ty;
        let mut impl_idx = 0;
        let ok = loop {
            let tyf = mach.force_v(bump, &probe_cxt, ty);
            if v_tag(tyf) != 4 {
                break Self::unify_indices(mach, bump, &probe_cxt, sum_name, &head_params, tyf);
            }
            let p = v_pi_of(tyf);
            let (bname, dom, body, env0) = (p.name, p.dom, p.body, p.env);
            let u = if impl_idx < impl_vals.len() {
                let v = impl_vals[impl_idx];
                impl_idx += 1;
                v
            } else {
                v_lvl(probe_cxt.lvl)
            };
            let a_t = mach.quote(bump, &probe_cxt, probe_cxt.lvl, dom);
            probe_cxt = mach.bind_name(bump, &probe_cxt, bname, empty_span(()), a_t, dom);
            let env = env_ext(bump, env0, u);
            ty = mach.eval(bump, &probe_cxt, env, body);
        };
        // 出帧 = 恢复探测前 meta 状态（成功/失败同型；帧内条目逆序恢复 +
        // 截断到入帧长度），替代旧的整表搬回。
        super::spine::meta_journal_rollback(&mut mach.metas, pre_meta_len);
        ok
    }

    /// 索引方程：头部 Sum 的参数（含索引）与构造子返回 Sum 的参数逐槽特化
    /// 合一，头部一侧在前——两侧都是可解变量时解方向是「头部变量 := 构造子侧
    /// 值」。探测只问可达性，精化出的上下文弃掉即回滚（meta 表已整表回滚）。
    fn unify_indices(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        sum_name: &str,
        head_params: &[V],
        ret_ty: V,
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
        for (a, b) in head_params.iter().zip(rp.iter()) {
            if mach.unify_pm(bump, cxt, *a, b.val, &span).is_err() {
                return false;
            }
        }
        true
    }

    /// 可达性判定 + 每 match 的 memo（`constrs[i]`；覆盖检查与臂前置过滤共用
    /// ——同一入口上下文里同构造子判定不变，探测本身是纯探测）。
    fn ctor_accessible(
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        typ: V,
        constrs: &[crate::parser_lib::Span<SmolStr>],
        memo: &mut [Option<bool>],
        i: usize,
    ) -> bool {
        match memo[i] {
            Some(b) => b,
            None => {
                let b = Self::probe_accessible(mach, bump, cxt, typ, &constrs[i]);
                memo[i] = Some(b);
                b
            }
        }
    }

    /// 单臂模式走查（L07 口径，2026-09-18 自决策树矩阵重写；参考版 `walk_pat`
    /// 的快版）。槽位纪律见参考版同名注释：头部 Sum 的隐式参数不占槽（用头部
    /// 实参直接实例化构造子 Π 链），构造子其余绑定器各占一槽——用户写的子模式
    /// 按 icit 对位消费（显式模式不被隐式绑定器消费，反之亦然），没写/对不上
    /// 就补虚通配。
    fn walk_pat(
        &mut self,
        mach: &mut Machine,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        pat: &Pattern,
        head_ty: V,
    ) -> Result<(PatternDetail, Cxt<'a>), Error> {
        match pat {
            Pattern::Any(_, icit) => {
                let b = self.make_implicit_name("");
                let a_t =  mach.quote(bump, cxt, cxt.lvl, head_ty);
                let cxt2 =
                    mach.bind_name(bump, cxt, &b, empty_span(()), a_t, head_ty)
                ;
                Ok((
                    PatternDetail::Any(
                        empty_span(b),
                        Some(empty_span(SmolStr::new(""))),
                        icit.to_icit(),
                    ),
                    cxt2,
                ))
            }
            Pattern::Con(name, subs, _) => {
                let head_sum =  mach.force_v(bump, cxt, head_ty);
                let (sum_name, sum_params, cases): (
                    &'a str,
                    Vec<SumParamV<'a>>,
                    Rc<Vec<crate::parser_lib::Span<SmolStr>>>,
                ) = if v_tag(head_sum) == 7 {
                    match v_xcell_of(head_sum) {
                        XCell::Sum {
                            name, params, cases, ..
                        } => (*name, params.to_vec(), self.case_spans_cached(cxt, name, cases)),
                        _ => ("", vec![], Rc::new(vec![])),
                    }
                } else {
                    ("", vec![], Rc::new(vec![]))
                };
                let case_idx = match cases.iter().position(|c| c.data == name.data) {
                    Some(i) => i,
                    None => {
                        // 判型上不是该类型的构造子（含非 Sum 头）：裸变量模式
                        if !subs.is_empty() {
                            return Err(Error(
                                name.clone().map(|n| {
                                    format!("`{n}` 不是该类型的构造子，不能带子模式解构")
                                }),
                                vec![],
                            ));
                        }
                        let a_t =  mach.quote(bump, cxt, cxt.lvl, head_ty);
                        let cxt2 =
                            mach.bind_name(bump, cxt, &name.data, name.to_span(), a_t, head_ty)
                        ;
                        return Ok((PatternDetail::Bind(name.clone()), cxt2));
                    }
                };
                // 构造子类型：限定名 `Enum.case`（decl 无裸名别名）。廉价通路
                // = decls 直查（孪生 `infer_expr(Raw::Obj(..))` 对
                // `Obj(Var(sum), Some(case))` 的解析结果就是 `decls[qual].vty`，
                // 省掉完整解析链）。未命中（import 限定 Sum 等）回退原
                // infer_expr 全链路。悬停面不变：case token 上的构造子条目
                // 仍由下方 push_hover 登记（infer_expr 路径里
                // push_qualified_hover 只走 receiver 链，对本形态在 token 上
                // 本就无条目）。
                let qualified = SmolStr::new(format!("{}.{}", sum_name, name.data));
                let (constr_pi, ctor_key) =  match cxt.decls.get(qualified.as_str()) {
                    Some(e) => (e.vty, Some(qualified.clone())),
                    None => {
                        let ctor_raw = Raw::Obj(
                            Box::new(Raw::Var(sum_name_span(cxt, sum_name))),
                            Some(name.clone()),
                        );
                        let (tm, constr_pi) = mach.infer_expr(bump, cxt, &ctor_raw)?;
                        // 解析出的全键（Tm::Decl 的键）供 detail 记录限定名
                        let ctor_key = match tm {
                            Tm::Decl(k) => Some(SmolStr::new(k)),
                            _ => None,
                        };
                        (constr_pi, ctor_key)
                    }
                };
                // 悬停 / goto-definition：模式 token → 构造子（参数化构造子给
                // Π 签名而非不可读的 λ 串，无参构造子给 SumCase 值），def span
                // 取登记处 span。渲染走 decl 键缓存（push_ctor_hover）：构造子
                // hover 值是闭合值，串与使用处无关。
                let hover_val = match cxt.decls.get(qualified.as_str()).or_else(|| cxt.decls.get(name.data.as_str())) {
                    Some(e) => (if v_tag(e.val) == 1 { e.vty } else { e.val }, e.span),
                    None => (constr_pi, empty_span(())),
                };

                    mach.push_ctor_hover(bump, cxt, name.to_span(), hover_val.1, hover_val.0, qualified.as_str())
                ;
                // 头部 Sum 的隐式参数（构造子 Π 链最前的 n 个绑定器）不占槽
                let mut impl_vals: Vec<V> = sum_params
                    .iter()
                    .filter(|p| p.icit == Icit::Impl)
                    .map(|p| p.val)
                    .collect();
                impl_vals.reverse();
                let mut cxt_arm =  clone_cxt(cxt);
                let mut ty = constr_pi;
                let mut next = 0usize;
                let mut details: Vec<PatternDetail> = Vec::new();
                loop {
                    let tyf =  mach.force_v(bump, &cxt_arm, ty);
                    if v_tag(tyf) != 4 {
                        break;
                    }
                    let p = v_pi_of(tyf);
                    let (bname, bicit, dom, body, env0) = (p.name, p.icit, p.dom, p.body, p.env);
                    if let Some(v) = impl_vals.pop() {
                        let env = env_ext(bump, env0, v);
                        ty =  mach.eval(bump, &cxt_arm, env, body);
                        continue;
                    }
                    // 该绑定器对应的用户子模式：icit 对位才消费
                    let head: Option<&Pattern> = match subs.get(next) {
                        Some(q) if q.get_icit().to_icit() == bicit => subs.get(next),
                        _ => None,
                    };
                    // 该字段自身的层（占槽前）：Π 闭包实例化的 fresh rigid
                    let u = v_lvl(cxt_arm.lvl);
                    let detail = match head {
                        Some(Pattern::Con(vname, csubs, Either::Name(pname)))
                            if bicit == Icit::Impl && csubs.is_empty() =>
                        {
                            // 用户具名隐式绑定器（`cons[l=l0](..)`）：按用户名占槽
                            next += 1;
                            let a_t =  mach.quote(bump, &cxt_arm, cxt_arm.lvl, dom);
                            cxt_arm =
                                mach.bind_name(bump, &cxt_arm, &vname.data, vname.to_span(), a_t, dom)
                            ;
                            PatternDetail::Any(vname.clone(), Some(pname.clone()), Icit::Impl)
                        }
                        Some(Pattern::Any(_, _)) => {
                            next += 1;
                            let b = self.make_implicit_name(bname);
                            let a_t =  mach.quote(bump, &cxt_arm, cxt_arm.lvl, dom);
                            cxt_arm =
                                mach.bind_name(bump, &cxt_arm, &b, empty_span(()), a_t, dom)
                            ;
                            PatternDetail::Any(
                                empty_span(b),
                                Some(empty_span(SmolStr::new(bname))),
                                bicit,
                            )
                        }
                        Some(q @ Pattern::Con(..)) => {
                            next += 1;
                            // 嵌套 Con：字段 dom 是含该子构造子的 Sum 时记一
                            // 笔待提升的嵌套位置（参考版 walk_pat 同款；该字
                            // 段位置沿 ctor 路径的可达构造子必须有臂覆盖），
                            // 臂特化成功后以臂上下文结算（见 compile）。
                            // cur_path 先推后弹（更深的记账要看到完整链）。
                            let Pattern::Con(cn, ..) = q else {
                                unreachable!()
                            };
                            let field_sum =  mach.force_v(bump, &cxt_arm, dom);
                            let is_ctor = v_tag(field_sum) == 7
                                && matches!(v_xcell_of(field_sum),
                                    XCell::Sum { cases, .. }
                                        if cases.iter().any(|c| *c == cn.data.as_str())
                                );
                            self.cur_path.push((name.data.to_string(), details.len()));
                            let (d, c2) = self.walk_pat(mach, bump, &cxt_arm, q, dom)?;
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
                            let b = self.make_implicit_name(bname);
                            let a_t =  mach.quote(bump, &cxt_arm, cxt_arm.lvl, dom);
                            cxt_arm =
                                mach.bind_name(bump, &cxt_arm, &b, empty_span(()), a_t, dom)
                            ;
                            PatternDetail::Any(
                                empty_span(b),
                                Some(empty_span(SmolStr::new(bname))),
                                bicit,
                            )
                        }
                    };
                    details.push(detail);
                    let env = env_ext(bump, env0, u);
                    ty =  mach.eval(bump, &cxt_arm, env, body);
                }
                if let Some(extra) = subs.get(next) {
                    // 模式比构造子字段多：参考版叶上 "invalid pattern" 同文案
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

    /// 逐臂下钻编译（L07 口径，2026-09-18 自决策树矩阵重写；参考版 `compile`
    /// 的快版）。错误收集式：某臂的走查/特化/体检查失败只记进 `errors`，其余
    /// 臂照常检查（一次性报全），最后按参考版口径返回**首个**错误。
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
        self.errors = Vec::new();
        self.implicit_counter = 0;
        self.nested_checks = Vec::new();
        self.pending_pos = Vec::new();
        self.cur_path = Vec::new();
        let typ = mach.force_v(bump, cxt, typ);
        // 值层 `XCell::Sum.cases` 只有名字，构造子**定义 span** 从 decl 表回填
        // （参考版 `Val::Sum.cases` 直接带声明 span——PM 路径的 hover/def 键与
        // Unmatched 警告形态都落在声明 token 上）。
        let (constrs, ctor_names): (Vec<crate::parser_lib::Span<SmolStr>>, Vec<SmolStr>) =
            if v_tag(typ) == 7 {
                match v_xcell_of(typ) {
                    XCell::Sum { name, cases, .. } => {
                        let cs = self.case_spans_cached(cxt, name, cases);
                        let names = cs.iter().map(|c| c.data.clone()).collect();
                        (cs.as_ref().clone(), names)
                    }
                    _ => (vec![], vec![]),
                }
            } else {
                (vec![], vec![])
            };
        // 构造子可达性 memo（下标对齐 constrs）：覆盖检查与臂前置过滤共用同一
        // 判定（决策树 filter 的 probe_memo 同口径）。
        let mut accessible: Vec<Option<bool>> = vec![None; constrs.len()];
        // 覆盖检查索引：**每 match 编译一次**的 O(n) 构建（`CtorIndex` 注），
        // 宽表下把「逐构造子 × 逐臂 × 从 `ctor_names[0]` 线性扫名」的 O(n³)
        // 字符串比较降为 O(n + 臂数) 查表；窄表返回 `None`（不建表、零额外
        // 分配），覆盖判定走原线性 `covers` 口径。
        let ctor_ix = CtorIndex::build(&ctor_names);
        let covered = ctor_ix.covered(arms, &ctor_names);
        // 覆盖检查：可达且无臂覆盖 → Unmatched（探测失败按「无结论」处理）。
        // 不可达（如 `Vec[A] zero` 上的 `cons`）不报——索引方程不可解即结构上
        // 不可能出现。
        for (i, ctor) in constrs.iter().enumerate() {
            // 与旧码同序：可达性对每个下标照常求值（结果被下面的臂前置过滤
            // 复用），只有覆盖判定换成索引路径的布尔读（`None` 时 = 旧口径，
            // 调用序列与成本逐点不变）。
            if !Self::ctor_accessible(mach, bump, cxt, typ, &constrs, &mut accessible, i) {
                continue;
            }
            let cov = match covered.as_ref() {
                Some(c) => c[i],
                None => arms
                    .iter()
                    .any(|(pat, _)| covers(pat, ctor.data.as_str(), &ctor_names)),
            };
            if !cov {
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
                if let Some(i) = ctor_ix.pos(name.data.as_str(), &ctor_names) {
                    if !
                        Self::ctor_accessible(mach, bump, cxt, typ, &constrs, &mut accessible, i)
                     {
                        unreachable.push(Warning::Unreachable(body.clone()));
                        continue;
                    }
                }
            }
            let (detail, cxt_walk) = match 
                self.walk_pat(mach, bump, cxt, pat, typ)
             {
                Ok(x) => x,
                Err(e) => {
                    // 走查失败臂的嵌套记账一并丢弃
                    self.pending_pos.clear();
                    self.errors.push(e);
                    continue;
                }
            };
            // 特化用的模式从**走查产出的 detail** 重建（参考版 `detail_to_raw`
            // 同款）：构造子隐含参数必须按走查已绑定的具名 rigid 传入
            // （`[l=_l0]`），否则 check_pm 会新解 meta，臂上下文的
            // `xs : Vec[A] _l0` 与特化出的 `Vec[A] ?m` 各说各话。
            let raw =  detail_to_raw(&detail);
            let cxt_arm = match
                mach.check_pm_final(bump, &cxt_walk, &raw, typ, target_val)
             {
                Ok((_, c)) => c,
                Err(e) => {
                    // 荒谬臂（特化失败）：其嵌套位置不产生覆盖义务——臂本
                    // 身的特化错误已承担语义（参考版同款）
                    self.pending_pos.clear();
                    self.errors.push(e);
                    continue;
                }
            };
            // 嵌套位置结算（两段式，参考版同款）：此刻本臂特化方程已解出、
            // 精化写进了臂上下文的 env 槽。
            for (path, field_sum) in std::mem::take(&mut self.pending_pos) {
                self.nested_checks.push(NestedCheck {
                    path,
                    field_sum,
                    arm_cxt: clone_cxt(&cxt_arm),
                });
            }
            // 期望类型重锚到臂上下文：quote → eval（flex 免锚）
            let ret_type =  {
                let t = mach.force_v(bump, &cxt_arm, self.ret_type);
                if is_flex(&mach.spine, t) {
                    t
                } else {
                    let tm = mach.quote(bump, &cxt_arm, cxt_arm.lvl, t);
                    mach.eval(bump, &cxt_arm, cxt_arm.env, tm)
                }
            };
            match  mach.check(bump, &cxt_arm, body, ret_type) {
                Ok(ret) => self.pats.push((detail, ret)),
                Err(e) => {
                    self.errors.push(e);
                    continue;
                }
            }
            if is_catch_all(pat, &ctor_ix, &ctor_names) {
                shadowed = true;
            }
        }
        // 参考版 `unreachable.into_iter().chain(self.warnings)`——不可达警告在前
        self.warnings = unreachable.into_iter().chain(self.warnings.drain(..)).collect();
        // 嵌套位置的覆盖检查（沿模式下钻逐节点，参考版同款）：每条记账在
        // 记录臂的实例化（臂上下文快照）下探测字段 Sum 的可达构造子；覆盖
        // 集 = 已走查臂的 PatternDetail 沿路径的结构贡献。可达集取各记账臂
        // 探测的并集（保守）。荒谬臂 / 被遮蔽臂不在 pats 里，天然不贡献
        // 覆盖——与运行时首匹配结构语义一致。
        let mut reported = std::collections::HashSet::new();
        for nc in std::mem::take(&mut self.nested_checks) {
            let field_sum = mach.force_v(bump, &nc.arm_cxt, nc.field_sum);
            let ctor_cases: Vec<crate::parser_lib::Span<SmolStr>> = if v_tag(field_sum) != 7 {
                continue;
            } else {
                match v_xcell_of(field_sum) {
                    XCell::Sum { name, cases, .. } => {
                        self.case_spans_cached(&nc.arm_cxt, name, cases).as_ref().clone()
                    }
                    _ => continue,
                }
            };
            for ctor in ctor_cases {
                if !
                    Self::probe_accessible(mach, bump, &nc.arm_cxt, field_sum, &ctor)
                 {
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
        match self.errors.drain(..).next() {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}

/// 值层 `XCell::Sum.cases` 只有名字；构造子**定义 span** 从 decl 表回填
/// （参考版 `Val::Sum.cases` 直接带声明 span，PM 路径的 hover/def 键与
/// Unmatched 警告形态都落在声明 token 上——孪生对齐）。
fn case_spans(
    cxt: &Cxt<'_>,
    sum_name: &str,
    cases: &[&str],
) -> Vec<crate::parser_lib::Span<SmolStr>> {
    cases
        .iter()
        .map(|c| {
            let key = format!("{}.{}", sum_name, c);
            let sp = cxt
                .decls
                .get(key.as_str())
                .or_else(|| cxt.decls.get(*c))
                .map(|e| e.span)
                .unwrap_or_else(|| empty_span(()));
            crate::parser_lib::Span {
                data: SmolStr::new(*c),
                start_offset: sp.start_offset,
                end_offset: sp.end_offset,
                path_id: sp.path_id,
            }
        })
        .collect()
}

/// 和类型**本体名**的声明 span（参考版 `Val::Sum` 的 `Span<SmolStr>` 名直接
/// 带声明 span；孪生值层只有名字，从 decl 表回填）。限定名 `Raw::Obj(Var(枚举),
/// Some(case))` 的 hover 键 = 「枚举名 span 起点..case span 终点」的拼接 span，
/// 不回填就会与参考版错位（observation_tests 全表互检）。
fn sum_name_span(cxt: &Cxt<'_>, sum_name: &str) -> crate::parser_lib::Span<SmolStr> {
    let sp = cxt
        .decls
        .get(sum_name)
        .map(|e| e.span)
        .unwrap_or_else(|| empty_span(()));
    crate::parser_lib::Span {
        data: SmolStr::new(sum_name),
        start_offset: sp.start_offset,
        end_offset: sp.end_offset,
        path_id: sp.path_id,
    }
}

/// 走查 detail → 特化用 `Raw`（参考版 `detail_to_raw` 同款）：把走查期
/// **生成的**隐式绑定器名以 `[param=name]` 具名实参回写，让 `check_pm_final`
/// 复用同一批已绑定 rigid；无名通配发 `Raw::Hole` 让 elaborator 自动填充。
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

/// 覆盖检查的**参考口径**（窄表路径；也是 `CtorIndex::covered` 的等价性
/// 基准）：臂是否（结构上）覆盖构造子 `ctor`（参考版 `covers` 同款）。
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
fn is_catch_all(pat: &Pattern, ctor_ix: &CtorIndex<'_>, ctor_names: &[SmolStr]) -> bool {
    match pat {
        Pattern::Any(..) => true,
        Pattern::Con(name, subs, _) => {
            subs.is_empty() && !ctor_ix.contains(name.data.as_str(), ctor_names)
        }
    }
}

/// 索引化的长度闸：构造子数 ≥ 此值才建 name→下标表。
///
/// 标定（S8/2026-09-23 实测）：线性口径每 match 的覆盖检查 ≈ Σᵢ i²/2 = n³/6
/// 次字符串比较（n=2048 实测 1.43e9 次、1.4-2.4ns/次）；索引的固定成本 =
/// 一次表分配 + n 次插入 + n 位布尔写（n×20-30ns 量级）。n=16 时线性
/// ≈ 682 次比较（~1.5µs）对索引 ≈ 0.5µs——两者同量级且都在噪声里；阈值取
/// 16 的目的是让窄表负载（struct/church/strchain/prelude-*，构造子数 2-8）
/// **零额外分配**、路径与成本逐点不变（`covered` 返回 `None` 走原码）。
/// 真正的收益区在 k≥9（n≥512，n³/6 ≥ 2.2e7 次比较）。
const COVERS_INDEX_MIN_CTORS: usize = 16;

/// 覆盖检查的构造子名索引：`ctor_names` 名 → 下标。`compile` 入口建一次
/// （O(n) 插入），此后覆盖判定 / 臂前置过滤 / 通配臂判定都是 O(1) 查表。
///
/// **与被证伪形态的区别**（务必保持）：2026-09-23 轮 §4 证伪的是 `eval_aux`
/// 值层分派臂表的**逐调用重建**索引——每分派全表触达、表宽超 L2 后强制
/// 整表 DRAM 扫（we11 +9.1%、match k=12 +16~24%）。本索引挂在 `compile`
/// 上，一个 match 表达式的编译只建一次（生命周期同 `case_spans_memo`），
/// 不存在逐调用重建；构建本身 O(n) 且只碰一遍 `ctor_names`。
enum CtorIndex<'x> {
    /// 窄表，或构造子名单重名（正常 enum 语法不可达的防御形态）：不建表，
    /// 查询全部走原线性口径（`covers`/`position`/逐串比较）。
    Linear,
    /// 名唯一且表宽达标：一次分配，查询 O(1)。
    Indexed(FxHashMap<&'x str, u32>),
}

impl<'x> CtorIndex<'x> {
    fn build(names: &'x [SmolStr]) -> Self {
        if names.len() < COVERS_INDEX_MIN_CTORS {
            return CtorIndex::Linear;
        }
        let mut map: FxHashMap<&'x str, u32> =
            FxHashMap::with_capacity_and_hasher(names.len(), Default::default());
        for (i, n) in names.iter().enumerate() {
            // 重名 ⇒ 下标不唯一（`position` 取首个，而 `covers` 的
            // `name == ctor` 会命中全部同名字）——退回线性口径保持逐点等价，
            // 不做近似。
            if map.insert(n.as_str(), i as u32).is_some() {
                return CtorIndex::Linear;
            }
        }
        CtorIndex::Indexed(map)
    }

    /// `name` 是否在构造子名单里（`is_catch_all` 的第二子句）。
    fn contains(&self, name: &str, names: &[SmolStr]) -> bool {
        match self {
            CtorIndex::Linear => names.iter().any(|c| c.as_str() == name),
            CtorIndex::Indexed(map) => map.contains_key(name),
        }
    }

    /// `name` 在名单里的**首个**下标（臂前置过滤的 `position` 口径）。
    fn pos(&self, name: &str, names: &[SmolStr]) -> Option<usize> {
        match self {
            CtorIndex::Linear => names.iter().position(|c| c.as_str() == name),
            CtorIndex::Indexed(map) => map.get(name).map(|&i| i as usize),
        }
    }

    /// 覆盖集：`covered[i]` = 存在臂覆盖 `ctor_names[i]`，宽表一遍
    /// O(n + 臂数)。窄表返回 `None`（调用方走原 `covers` 线性口径）。
    ///
    /// 等价性论证（旧外层循环对每个下标 i 求 `∃臂 covers(pat, ctor_i)`）：
    /// `covers(Con(name,_), ctor_i)` = 「`name` 不在 `ctor_names` 里」∨
    /// 「`name == ctor_i`」——前件与 i 无关，可整体提出（查不到名 ⇒ 该臂
    /// 覆盖**全部**下标，`all = true`）；名唯一时后件恰命中它自己的下标 j
    /// （命中别的 i 需要两个不同下标同串，即重名——`build` 已回退 `Linear`）。
    /// `Any` 臂覆盖全部。于是 `covered[i] = ∃臂: all ∨ map[name] = i` 与逐 i
    /// 调用 `covers` 逐点相等：布尔或的取值与臂遍历序无关，每个 i 的取值只
    /// 依赖「是否有这样的臂」，与旧码每个 i 独立求 `any` 的结果一一对应。
    /// 调用方仍按 i 升序 push 警告 ⇒ 警告集合与顺序都不变。
    fn covered(&self, arms: &[(Pattern, Raw)], names: &[SmolStr]) -> Option<Vec<bool>> {
        let map = match self {
            CtorIndex::Linear => return None,
            CtorIndex::Indexed(map) => map,
        };
        let mut covered = vec![false; names.len()];
        let mut all = false;
        for (pat, _) in arms {
            match pat {
                Pattern::Any(..) => {
                    all = true;
                    break;
                }
                Pattern::Con(name, _, _) => match map.get(name.data.as_str()) {
                    Some(&j) => covered[j as usize] = true,
                    None => {
                        all = true;
                        break;
                    }
                },
            }
        }
        if all {
            covered.iter_mut().for_each(|b| *b = true);
        }
        Some(covered)
    }
}
