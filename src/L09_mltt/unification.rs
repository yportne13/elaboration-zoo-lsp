use crate::list::List;

use super::{
    Error, Infer, Lvl, MetaEntry, MetaVar, Span, Spine, Subst, Tm, UnifyError, VTy, Val,
    cxt::Cxt, lvl2ix, v_applicable, val_mentions_lvl, wrap_sub,
    parser::syntax::Icit, syntax::Pruning, empty_span, pretty::pretty_tm,
};

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::rc::Rc;

/// η 展开的可应用性守卫的实现体已上移到 mod.rs（`super::v_applicable`，
/// frcs 的 Rigid 读点共用同一守卫）。

/// 特化合一的进行时状态（dpm-nbe `unifyS` 的 ɑ-accumulation 的 Rust 形态）。
/// `solvable` = 本子句可解的 rigid 层级（模式槽 + 外层 bind 槽基线）；
/// `acc` = 已解出的替换——编译器的 σ 作种子，方程途中叠加，调用方在方程
/// 结束后取走 `acc` 作为新 σ（臂边界回滚 = 恢复快照指针）。
pub(crate) struct SpecSolve<'a> {
    pub(crate) solvable: &'a [Lvl],
    pub(crate) acc: Rc<Subst>,
}

#[derive(Debug, Clone)]
pub struct PartialRenaming {
    pub occ: Option<MetaVar>,
    pub dom: Lvl,               // size of Γ
    pub cod: Lvl,               // size of Δ
    pub ren: HashMap<u32, Lvl>, // mapping from Δ vars to Γ vars
}

fn lift(pr: &PartialRenaming) -> PartialRenaming {
    let mut new_ren = pr.ren.clone();
    new_ren.insert(pr.cod.0, pr.dom);

    PartialRenaming {
        occ: pr.occ,
        dom: pr.dom + 1, // increment dom
        cod: pr.cod + 1, // increment cod
        ren: new_ren,    // update ren with the new mapping
    }
}

fn skip(pr: &PartialRenaming) -> PartialRenaming {
    PartialRenaming {
        occ: pr.occ,
        dom: pr.dom,         // decrement dom
        cod: pr.cod + 1,     // decrement cod
        ren: pr.ren.clone(), // no change in ren
    }
}

#[derive(Debug, Clone, Copy)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

impl Infer {
    fn invert_go(
        &self,
        sp: Spine,
    ) -> Result<(Lvl, HashMap<u32, Lvl>, HashSet<u32>, List<(Lvl, Icit)>), UnifyError> {
        match sp {
            List { head: None, .. } => Ok((Lvl(0), HashMap::default(), HashSet::default(), List::new())),
            a => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(a.tail())?;
                match self.force_arg(a.head().unwrap().0.clone()) {
                    Val::Rigid(x, List { head: None, .. }) => {
                        if ren.contains_key(&x.0) || nlvars.contains(&x.0) {
                            ren.remove(&x.0);
                            nlvars.insert(x.0);
                            Ok((dom + 1, ren, nlvars, fsp.prepend((x, a.head().unwrap().1))))
                        } else {
                            ren.insert(x.0, dom);
                            Ok((dom + 1, ren, nlvars, fsp.prepend((x, a.head().unwrap().1))))
                        }
                    }
                    _ => Err(UnifyError),
                }
            }
        }
    }
    pub fn invert(
        &self,
        gamma: Lvl,
        sp: Spine,
    ) -> Result<(PartialRenaming, Option<Pruning>), UnifyError> {
        //println!("{} {:?} {:?}", "invert".green(), gamma, sp);
        // spine 不可逆 = 判不出来（不是结构矛盾）：P3 记 Undecided，对齐 L07
        // "rename/invert/solve 族失败一律 Undecided" 的口径。
        let (dom, ren, nlvars, fsp) = self.invert_go(sp).map_err(|e| {
            self.note_unify_kind(super::UnifyKind::Undecided);
            e
        })?;

        Ok((
            PartialRenaming {
                occ: None,
                dom,
                cod: gamma,
                ren,
            },
            if nlvars.is_empty() {
                None
            } else {
                Some(fsp.map(|(x, i)| {
                    if nlvars.contains(&x.0) {
                        None
                    } else {
                        Some(*i)
                    }
                }))
            },
        ))
    }
    fn prune_ty_go(
        &mut self,
        rev: &[Option<Icit>],
        pren: &PartialRenaming,
        a: Val,
    ) -> Result<Tm, UnifyError> {
        // 掩码按"外→内"配对 Π 层：`rev` 头 = 最外层槽位（`prune_ty` 已把
        // Pruning 反转——List 头是最内层）。旧实现直接按链头配对外层 Π，
        // 多层 telescope + 混合掩码时掩码与 Π 层错位（L05–L08 已修的同款；
        // 本层快版 `prune_ty_bump` 走 `mask_inner_first.iter().rev()`）。
        match (rev.split_first(), self.force(a)) {
            (None, a) => self.rename(pren, a),
            (Some((Some(_), rest)), Val::Pi(x, i, a, b)) => {
                let a = self.rename(pren, (*a).clone())?;
                let b = self.closure_apply(&b, Val::vvar(pren.cod));
                let b = self.prune_ty_go(rest, &lift(pren), b)?;
                Ok(Tm::Pi(super::tmspan(&x), i, Rc::new(a), Rc::new(b)))
            }
            (Some((None, rest)), Val::Pi(x, i, _, b)) => {
                let b = self.closure_apply(&b, Val::vvar(pren.cod));
                self.prune_ty_go(rest, &skip(pren), b)
            }
            _ => {
                // 掩码与 Π 层对不上：判不出来（P3：Undecided）
                self.note_unify_kind(super::UnifyKind::Undecided);
                Err(UnifyError) // impossible case
            }
        }
    }
    pub fn prune_ty(&mut self, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
        // Pruning 头 = 最内层槽位；meta 类型的 Π 层从最外层剥起——先反转
        // 成"外→内"（RevPruning，上游 05/L07/L08 与快版 `prune_ty_bump` 同款）。
        let mut rev: Vec<Option<Icit>> = pr.iter().copied().collect();
        rev.reverse();
        self.prune_ty_go(
            &rev,
            &PartialRenaming {
                occ: None,
                dom: Lvl(0),
                cod: Lvl(0),
                ren: HashMap::default(),
            },
            a,
        )
    }
    fn prune_meta(&mut self, pruning: Pruning, m: MetaVar) -> Result<MetaVar, UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            // force 在 fuel 耗尽时会把已解 meta 当未解返回（拒绝展开），
            // 随后走到的剪枝/求解按合一失败降级，不 panic——与"fuel 耗尽
            // 按未解失败"的既有降级故事一致（窗口：恰在 1→0 递减帧内）
            // （L07 2026-09-18 修复 3 的同步移植）
            _ => return Err(UnifyError),
        };

        let prune_ty = self.prune_ty(&pruning, mty.clone())?;
        let prunedty = self.eval(&List::new(), prune_ty);
        let m_prime = MetaVar(self.new_meta(prunedty));

        let solution = self.eval(
            &List::new(),
            self.lams(
                Lvl(pruning.iter().count() as u32), // Assuming Lvl is based on length of pruning
                mty.clone(),
                Tm::AppPruning(Box::new(Tm::Meta(m_prime)), pruning),
            ),
        );

        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);
        Ok(m_prime)
    }
    fn prune_vflex_go(
        &mut self,
        pren: &PartialRenaming,
        sp: Spine,
    ) -> Result<(List<(Option<Tm>, Icit)>, SpinePruneStatus), UnifyError> {
        if sp.head().is_none() {
            Ok((List::new(), SpinePruneStatus::OKRenaming))
        } else {
            let (sp_rest, status) = self.prune_vflex_go(pren, sp.tail())?;
            match self.force_arg(sp.head().unwrap().0.clone()) {
                Val::Rigid(x, List { head: None, .. }) => match (pren.ren.get(&x.0), status) {
                    (Some(x), _) => Ok((
                        sp_rest
                            .prepend((Some(Tm::Var(lvl2ix(pren.dom, *x))), sp.head().unwrap().1)),
                        status,
                    )),
                    (None, SpinePruneStatus::OKNonRenaming) => Err(UnifyError),
                    (None, _) => Ok((
                        sp_rest.prepend((None, sp.head().unwrap().1)),
                        SpinePruneStatus::NeedsPruning,
                    )),
                },
                t => match status {
                    SpinePruneStatus::NeedsPruning => Err(UnifyError),
                    _ => {
                        let t = self.rename(pren, t)?;
                        Ok((
                            sp_rest.prepend((Some(t), sp.head().unwrap().1)),
                            SpinePruneStatus::OKNonRenaming,
                        ))
                    }
                },
            }
        }
    }
    fn prune_vflex(
        &mut self,
        pren: &PartialRenaming,
        m: MetaVar,
        sp: Spine,
    ) -> Result<Tm, UnifyError> {
        let (sp, status) = self.prune_vflex_go(pren, sp)?;

        let m_prime = match status {
            SpinePruneStatus::OKRenaming => {
                match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(_) => m,
                    // fuel 耗尽窗口（同 prune_meta 注）：已解 meta 被 force
                    // 当未解返回，随后走到的剪枝按合一失败降级，不 panic
                    // （L07 2026-09-18 修复 3 的同步移植）
                    _ => return Err(UnifyError),
                }
            }
            SpinePruneStatus::OKNonRenaming => {
                match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(_) => m,
                    // fuel 耗尽窗口（同 prune_meta 注）：按失败降级
                    _ => return Err(UnifyError),
                }
            }
            SpinePruneStatus::NeedsPruning => {
                self.prune_meta(sp.map(|(mt, i)| mt.as_ref().map(|_| i.clone())), m)?
            }
        };

        let t = sp.iter().fold(Tm::Meta(m_prime), |t, (mu, i)| {
            if let Some(u) = mu {
                Tm::App(Box::new(t), Box::new(u.clone()), i.clone())
            } else {
                t
            }
        }); //TODO:need rev()?

        Ok(t)
    }
    fn rename_sp(&mut self, pren: &PartialRenaming, t: Tm, sp: &Spine) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None, .. } => Ok(t),
            a => {
                let t = self.rename_sp(pren, t, &a.tail())?;
                let u = self.rename(pren, a.head().unwrap().0.clone())?;
                Ok(Tm::App(Box::new(t), Box::new(u), a.head().unwrap().1))
            }
        }
    }
    /// rename 入口：先 force 到 WHNF，再按形态分派——深链形态（Sum /
    /// SumCase / Obj 可按值深度自嵌）交给帧式收集器 [`Self::rename_deep`]；
    /// 其余形态（Lam/Pi/Match/spine 头，结构嵌套浅）回落 [`Self::rename_arm`]。
    /// 深链在任意深度进入收集器后整链消化，native 栈深 = 结构嵌套而非值深
    /// （L07 `rename_deep` 同构移植，README §7.6）。
    pub fn rename(&mut self, pren: &PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        let v = self.force(t);
        match v {
            // 只有可能深的值才走帧式收集器；浅值走直接递归臂（同 quote 的
            // `deep_chain` 探测——避免给每一层 Sum/SumCase 付帧分配）
            Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => self.rename_deep(pren, v),
            _ => self.rename_arm(pren, v),
        }
    }

    /// rename 的深链收集器：Sum / SumCase / Obj 帧式下降/组装（子件顺序、
    /// App 折叠序与旧递归臂逐点一致——rename_sp 的应用序 = spine List 尾先
    /// 头后）。子件回落 [`Self::rename_arm`]（同一 pren，无 lift——对齐旧臂：
    /// Sum 参数 / SumCase 字段 / Obj 内层与实参都在同一 renaming 下）。
    fn rename_deep(&mut self, pren: &PartialRenaming, root: Val) -> Result<Tm, UnifyError> {
        enum FrameKind {
            Sum {
                name: super::VSpan,
                cases: Vec<super::VSpan>,
                metas: Vec<(super::VSpan, Icit)>,
            },
            SumCase {
                case_name: super::VSpan,
                datas_metas: Vec<(super::VSpan, Icit)>,
            },
            Obj {
                name: super::VSpan,
            },
        }
        struct Frame {
            pending: Vec<Val>,
            icits: Vec<Icit>,
            kind: FrameKind,
            done: Vec<Tm>,
            idx: usize,
        }
        fn frame_new(v: Val) -> Frame {
            match v {
                Val::Sum(name, params, cases) => {
                    let mut pending = Vec::with_capacity(params.len() * 2);
                    let mut metas = Vec::with_capacity(params.len());
                    for (n, v, t, i) in params.iter() {
                        pending.push(super::rc_take(v.clone()));
                        pending.push(super::rc_take(t.clone()));
                        metas.push((n.clone(), *i));
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits: Vec::new(),
                        kind: FrameKind::Sum {
                            name,
                            cases: (*cases).clone(),
                            metas,
                        },
                        done: Vec::with_capacity(n_all),
                        idx: 0,
                    }
                }
                Val::SumCase {
                    typ,
                    case_name,
                    datas,
                } => {
                    let mut pending = Vec::with_capacity(datas.len() + 1);
                    pending.push(super::rc_take(typ));
                    let mut datas_metas = Vec::with_capacity(datas.len());
                    for (n, v, i) in datas.iter() {
                        pending.push(super::rc_take(v.clone()));
                        datas_metas.push((n.clone(), *i));
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits: Vec::new(),
                        kind: FrameKind::SumCase {
                            case_name,
                            datas_metas,
                        },
                        done: Vec::with_capacity(n_all),
                        idx: 0,
                    }
                }
                Val::Obj(x, name, sp) => {
                    // pending = [被投影者, spine 实参…]；实参按 List 头→尾序
                    // 入列（头 = 最外层 App），组装时逆序折叠 = rename_sp 的
                    // 应用序（List 尾的实参最先应用）
                    let mut pending = vec![(*x).clone()];
                    let mut icits = Vec::new();
                    for (u, i) in sp.iter() {
                        pending.push(u.clone());
                        icits.push(*i);
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits,
                        kind: FrameKind::Obj { name },
                        done: Vec::with_capacity(n_all),
                        idx: 0,
                    }
                }
                _ => unreachable!("rename_deep 只接受 Sum/SumCase/Obj"),
            }
        }
        fn frame_assemble(frame: Frame) -> Tm {
            match frame.kind {
                FrameKind::Sum {
                    name,
                    cases,
                    metas,
                } => {
                    let mut it = frame.done.into_iter();
                    let params = metas
                        .into_iter()
                        .map(|(n, i)| {
                            let v = it.next().unwrap();
                            let t = it.next().unwrap();
                            (super::tmspan(&n), v, t, i)
                        })
                        .collect();
                    Tm::Sum(super::tmspan(&name), params, cases.iter().map(super::tmspan).collect())
                }
                FrameKind::SumCase {
                    case_name,
                    datas_metas,
                } => {
                    let mut it = frame.done.into_iter();
                    let typ = it.next().unwrap();
                    let datas = datas_metas
                        .into_iter()
                        .map(|(n, i)| (super::tmspan(&n), it.next().unwrap(), i))
                        .collect();
                    Tm::SumCase {
                        typ: Box::new(typ),
                        case_name: super::tmspan(&case_name),
                        datas,
                    }
                }
                FrameKind::Obj { name } => {
                    let mut it = frame.done.into_iter();
                    let head = Tm::Obj(Box::new(it.next().unwrap()), super::tmspan(&name));
                    let args: Vec<Tm> = it.collect();
                    let mut acc = head;
                    for (u, i) in args.into_iter().zip(frame.icits).rev() {
                        acc = Tm::App(Box::new(acc), Box::new(u), i);
                    }
                    acc
                }
            }
        }
        let mut frames: Vec<Frame> = vec![frame_new(root)];
        let mut result: Option<Tm> = None;
        while let Some(frame) = frames.last_mut() {
            if frame.idx == frame.pending.len() {
                let frame = frames.pop().unwrap();
                let tm = frame_assemble(frame);
                match frames.last_mut() {
                    Some(parent) => {
                        parent.done.push(tm);
                        parent.idx += 1;
                    }
                    None => result = Some(tm),
                }
                continue;
            }
            // 同 quote_deep：**move 出**待处理槽，避免帧内残留深链的深递归 Drop
            let w = std::mem::replace(&mut frame.pending[frame.idx], Val::U(0));
            let w = self.force(w);
            match w {
                Val::VSub(v, _) => {
                    let frame = frames.last_mut().unwrap();
                    frame.pending[frame.idx] = (*v).clone();
                }
                Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => {
                    frames.push(frame_new(w));
                }
                _ => {
                    let tm = self.rename_arm(pren, w)?;
                    let frame = frames.last_mut().unwrap();
                    frame.done.push(tm);
                    frame.idx += 1;
                }
            }
        }
        Ok(result.expect("rename_deep 至少产出一个 Tm"))
    }

    /// rename 的浅结构臂（入口已 force、已分派掉深链形态）。
    fn rename_arm(&mut self, pren: &PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        match t {
            // 不变式：force 的返回值顶层不会是 VSub（入口已推开；fuel 耗尽的
            // 降级点在 frcs 的 lookup 命中处，返回裸 rigid）。不变式被破 ⇒
            // 判不出来（P3：Undecided），不是矛盾。
            Val::VSub(..) => {
                self.note_unify_kind(super::UnifyKind::Undecided);
                Err(UnifyError)
            }
            Val::Flex(m_prime, sp) => match pren.occ {
                // occurs 命中（解里出现被解 meta 自身）：判不出来，不是矛盾
                Some(m) if m == m_prime => {
                    self.note_unify_kind(super::UnifyKind::Undecided);
                    Err(UnifyError)
                }
                _ => self.prune_vflex(pren, m_prime, sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                // 作用域失配（层级不在 renaming 域内）：判不出来（P3）
                None => if x.0 < 1919810 {
                    self.note_unify_kind(super::UnifyKind::Undecided);
                    Err(UnifyError)
                } else {
                    let t = Tm::Var(lvl2ix(pren.dom, x));
                    self.rename_sp(pren, t, &sp)
                }, // scope error
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(pren, t, &sp)
                }
            },
            Val::Obj(x, name, sp) => {
                let t = self.rename(pren, (*x).clone())?;
                let t = Tm::Obj(Box::new(t), super::tmspan(&name));
                self.rename_sp(pren, t, &sp)
            },
            Val::Lam(x, i, closure) => {
                let t = self.rename(
                    &lift(pren),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Lam(super::tmspan(&x), i, Rc::new(t)))
            }
            Val::Pi(x, i, a, closure) => {
                let a = self.rename(pren, (*a).clone())?;
                let b = self.rename(
                    &lift(pren),
                    self.closure_apply(&closure, Val::vvar(pren.cod)),
                )?;
                Ok(Tm::Pi(super::tmspan(&x), i, Rc::new(a), Rc::new(b)))
            }
            Val::U(x) => Ok(Tm::U(x)),
            Val::LiteralType => Ok(Tm::LiteralType),
            Val::LiteralIntro(x) => Ok(Tm::LiteralIntro(super::tmspan(&x))),
            Val::Prim => Ok(Tm::Prim),
            Val::Sum(x, params, cases) => {
                let new_params = params
                    .iter()
                    .map(|x| {
                        match (
                            self.rename(pren, super::rc_take(x.1.clone())),
                            self.rename(pren, super::rc_take(x.2.clone())),
                        ) {
                            (Ok(a), Ok(b)) => Ok((super::tmspan(&x.0), a, b, x.3)),
                            (Err(x), _) | (_, Err(x)) => Err(x),
                        }
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Tm::Sum(super::tmspan(&x), new_params, cases.iter().map(super::tmspan).collect()))
            }
            Val::SumCase {
                typ,
                case_name,
                datas: params,
            } => {
                let typ = self.rename(pren, super::rc_take(typ))?;
                let params = params
                    .iter()
                    .map(|p| {
                        let z = self.rename(pren, super::rc_take(p.1.clone()))?;
                        Ok((super::tmspan(&p.0), z, p.2))
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Tm::SumCase {
                    typ: Box::new(typ),
                    case_name: super::tmspan(&case_name),
                    datas: params,
                })
            }
            Val::Match(val, env, cases, pending) => {
                let val = self.rename(pren, (*val).clone())?;
                let cases = cases
                    .iter()
                    .map(|(pat, tm)| {
                        let (env, pren) = (0..pat.bind_count())
                            .fold((env.clone(), pren.clone()), |(env, pren), _| (
                                env.prepend(Val::vvar(pren.cod)),
                                lift(&pren),
                            ));
                        // 分支体在中性全局视图下求值（全局名字不再展开，免
                        // 递归）——取代旧的整机克隆 + 就地改写 global 表
                        let body = self.rename(
                            &pren,
                            self.eval_neutral(&env, tm.clone()),
                        )?;
                        Ok((pat.clone(), body))
                    })
                    .collect::<Result<_, _>>()?;
                // 卡住期累积的实参：同 quote，包在 Match 外的 App 链里
                let m = Tm::Match(Box::new(val), cases);
                pending.iter().fold(Ok(m), |acc: Result<Tm, UnifyError>, (u, i)| {
                    let u = self.rename(pren, u.clone())?;
                    Ok(Tm::App(Box::new(acc?), Box::new(u), *i))
                })
            }
        }
    }
    fn lams_go(&self, l: Lvl, t: Tm, a: VTy, l_prime: Lvl) -> Tm {
        if l == l_prime {
            t
        } else {
            match self.force(a) {
                Val::Pi(span, icit, val, closure) if span.data == "_" => {
                    let var_name = format!("x{}", l_prime.0);
                    Tm::Lam(
                        empty_span(var_name),
                        icit,
                        Rc::new(self.lams_go(
                            l,
                            t,
                            self.closure_apply(&closure, Val::Rigid(l_prime, List::new())),
                            l_prime + 1,
                        )),
                    )
                }
                Val::Pi(span, icit, val, closure) => Tm::Lam(
                    super::tmspan(&span),
                    icit,
                    Rc::new(self.lams_go(
                        l,
                        t,
                        self.closure_apply(&closure, Val::Rigid(l_prime, List::new())),
                        l_prime + 1,
                    )),
                ),
                _ => unreachable!(),
            }
        }
    }
    pub fn lams(&self, l: Lvl, a: VTy, t: Tm) -> Tm {
        self.lams_go(l, t, a, Lvl(0))
    }
    fn solve(&mut self, gamma: Lvl, m: MetaVar, sp: Spine, rhs: Val) -> Result<(), UnifyError> {
        /*println!(
            "{} {:?} {:?} {:?}\n  rhs: {:?}",
            "solve".red(),
            gamma,
            m,
            sp,
            rhs
        );*/
        let (pren, prune_non_linear) = self.invert(gamma, sp.clone())?;
        self.solve_with_pren(m, pren, prune_non_linear, rhs)
    }
    fn solve_with_pren(
        &mut self,
        m: MetaVar,
        pren: PartialRenaming,
        prune_non_linear: Option<Pruning>,
        rhs: Val,
    ) -> Result<(), UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            // fuel 耗尽窗口（同 prune_meta 注）：已解 meta 被 force 当未解
            // 返回，随后走到的求解按合一失败降级，不 panic（L07 2026-09-18
            // 修复 3 的同步移植）。已解 meta 被求解不是矛盾（P3：Undecided）。
            _ => {
                self.note_unify_kind(super::UnifyKind::Undecided);
                return Err(UnifyError);
            }
        };

        // if the spine was non-linear, we check that the non-linear arguments
        // can be pruned from the meta type (i.e. that the pruned solution will
        // be well-typed)
        if let Some(pr) = prune_non_linear {
            self.prune_ty(&pr, mty.clone())?; // 掩码反转在 prune_ty 内完成
        }

        let rhs = self.rename(
            &PartialRenaming {
                occ: Some(m),
                ..pren
            },
            rhs,
        )?;
        let solution = self.eval(&List::new(), self.lams(pren.dom, mty.clone(), rhs));
        self.meta[m.0 as usize] = MetaEntry::Solved(solution, mty);

        Ok(())
    }
    fn unify_sp(
        &mut self,
        l: Lvl,
        cxt: &Cxt,
        sp: &Spine,
        sp_prime: &Spine,
        mut spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Ok(()), // Both spines are empty
            (a, b) if matches!(a.head(), Some(_)) && matches!(b.head(), Some(_)) => {
                self.unify_sp(l, cxt, &a.tail(), &b.tail(), spec.as_deref_mut())?; // Recursively unify the rest of the spines
                self.unify(
                    l,
                    cxt,
                    a.head().unwrap().0.clone(),
                    b.head().unwrap().0.clone(),
                    spec,
                ) // Unify the current values
            }
            _ => {
                // spine 长度不齐：判不出相等，但不是结构矛盾（P3：Undecided）
                self.note_unify_kind(super::UnifyKind::Undecided);
                Err(UnifyError)
            }
        }
    }

    fn flex_flex(
        &mut self,
        gamma: Lvl,
        m: MetaVar,
        sp: Spine,
        m_prime: MetaVar,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        let mut go =
            |m: MetaVar, sp: Spine, m_prime: MetaVar, sp_prime: Spine| -> Result<(), UnifyError> {
                match self.invert(gamma, sp.clone()) {
                    Err(UnifyError) => self.solve(gamma, m_prime, sp_prime, Val::Flex(m, sp)),
                    Ok((pren, p1)) => {
                        self.solve_with_pren(m, pren, p1, Val::Flex(m_prime, sp_prime))
                    }
                }
            };

        if sp.iter().count() < sp_prime.iter().count() {
            go(m_prime, sp_prime, m, sp)
        } else {
            go(m, sp, m_prime, sp_prime)
        }
    }

    fn intersect_go(&mut self, sp: Spine, sp_prime: Spine) -> Option<List<Option<Icit>>> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Some(List::new()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                match (
                    self.force(a.head().unwrap().0.clone()),
                    self.force(b.head().unwrap().0.clone()),
                ) {
                    (
                        Val::Rigid(x, List { head: None, .. }),
                        Val::Rigid(x_prime, List { head: None, .. }),
                    ) => self.intersect_go(a.tail(), b.tail()).map(|l| {
                        l.prepend(if x == x_prime {
                            Some(a.head().unwrap().1)
                        } else {
                            None
                        })
                    }),
                    _ => None,
                }
            }
            // 长度失配：同一 meta 以不同 arity 出现——回落 `intersect` 的
            // `None => unify_sp` 逐实参比较（不可 `unreachable!()`；L05/L06/
            // L07/L08 与快版 `intersect_bump` 对长度失配均取失败而非 panic）
            _ => None,
        }
    }
    fn intersect(
        &mut self,
        l: Lvl,
        cxt: &Cxt,
        m: MetaVar,
        sp: Spine,
        sp_prime: Spine,
        spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        match self.intersect_go(sp.clone(), sp_prime.clone()) {
            None => self.unify_sp(l, cxt, &sp, &sp_prime, spec),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }
    pub fn unify(
        &mut self,
        l: Lvl,
        cxt: &Cxt,
        t: Val,
        u: Val,
        mut spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        //println!("unify: {t:?} {u:?}");
        let mut t = self.force(t);
        let mut u = self.force(u);
        // 特化模式：方程两侧置于**当前已积累的解**之下再解释（dpm-nbe
        // `subst ɑ vs` 的惰性等价物）。每次递归入口按当时的 acc 重新包裹
        // ——先解出的方程对后到的子方程自动可见。acc 为空时零开销。
        if let Some(s) = spec.as_deref() {
            if !s.acc.is_empty() {
                t = self.force(wrap_sub(&s.acc, t));
                u = self.force(wrap_sub(&s.acc, u));
            }
        }
        /*println!(
            "uni {}\n == {}",
            pretty_tm(0, cxt.names(), &self.quote(l, t.clone())),
            pretty_tm(0, cxt.names(), &self.quote(l, u.clone())),
        );*/

        match (&t, &u) {
            (Val::U(x), Val::U(y)) if x == y => Ok(()),
            (Val::Pi(x, i, a, b), Val::Pi(_, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(l, cxt, (**a).clone(), (**a_prime).clone(), spec.as_deref_mut())?;
                self.unify(
                    l + 1,
                    // quote 用**当前层级 l**而不是 cxt.lvl：Lam 的 η 递归臂
                    // `l+1` 不推进 cxt（binder 类型在值层不可得），`l == cxt.lvl`
                    // 的不变式在那里就会破——用 cxt.lvl quote 会把 `Rigid(l)`
                    // 打越界（lvl2ix 下溢）。cxt 只服务显示名字表，名字对不上
                    // 时 go_ix 有 `@i` 兜底。（L08 评审修复回移，见其 README §5。）
                    &cxt.bind(super::tmspan(&x), self.quote(l, (**a).clone()), (**a).clone()),
                    self.closure_apply(b, Val::vvar(l)),
                    self.closure_apply(b_prime, Val::vvar(l)),
                    spec.as_deref_mut(),
                )
            }
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(l, cxt, sp, sp_prime, spec.as_deref_mut())
            }
            // 卡住的投影：字段名相同即比接收者与卡住期实参 spine（合同规则，
            // L08 8988f7c 评审修复回移）。剥链精确化（elaboration 的 Obj 臂以
            // 接收者卡住投影实例化显式依赖字段）之后，`e.witness ≡ e.witness`
            // 这类形态成为可达；无本臂则落兜底 Err 误报 can't unify。
            // `Obj` vs 其它仍按失配处理（兜底臂）。
            (Val::Obj(o1, f1, sp1), Val::Obj(o2, f2, sp2)) if f1.data == f2.data => {
                self.unify(l, cxt, (**o1).clone(), (**o2).clone(), spec.as_deref_mut())?;
                self.unify_sp(l, cxt, sp1, sp2, spec.as_deref_mut())
            }
            // 模式特化（dpm-nbe unify1 的 VVar 臂）：可解 rigid（spec 携带的
            // 模式槽集）与非 Flex 值相遇 ⇒ 解入 `spec.acc`（显式替换，force
            // 读点惰性展开）。Flex 除外——交给 Flex 规则（meta := var）。
            // occurs 环守卫失败 = Err（对齐旧 update_cxt 语义下的分支不可达）。
            // spec = None（常规转换）时守卫不成立，落到后续臂——不得解假设，
            // 否则 `Eq x y` 会被"证成" `Eq y y`。
            (Val::Rigid(x, sp), v)
                if sp.is_empty()
                    && matches!(
                        spec.as_deref(),
                        Some(s) if s.solvable.contains(x) && !matches!(v, Val::Flex(..))
                    ) =>
            {
                if val_mentions_lvl(v, *x) {
                    return Err(UnifyError);
                }
                let s = spec.as_deref_mut().unwrap();
                s.acc = Subst::extend(&s.acc, *x, v.clone());
                Ok(())
            }
            (v, Val::Rigid(x, sp))
                if sp.is_empty()
                    && matches!(
                        spec.as_deref(),
                        Some(s) if s.solvable.contains(x) && !matches!(v, Val::Flex(..))
                    ) =>
            {
                if val_mentions_lvl(v, *x) {
                    return Err(UnifyError);
                }
                let s = spec.as_deref_mut().unwrap();
                s.acc = Subst::extend(&s.acc, *x, v.clone());
                Ok(())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.intersect(l, cxt, *m, sp.clone(), sp_prime.clone(), spec.as_deref_mut())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(l, *m, sp.clone(), *m_prime, sp_prime.clone())
            }
            (Val::Lam(_, _, t), Val::Lam(_, _, t_prime)) => self.unify(
                l + 1,
                cxt,
                self.closure_apply(t, Val::vvar(l)),
                self.closure_apply(t_prime, Val::vvar(l)),
                spec.as_deref_mut(),
            ),
            (t, Val::Lam(_, i, t_prime)) if v_applicable(t) => self.unify(
                l + 1,
                cxt,
                self.v_app(t.clone(), Val::vvar(l), *i),
                self.closure_apply(t_prime, Val::vvar(l)),
                spec.as_deref_mut(),
            ),
            (Val::Lam(_, i, t), t_prime) if v_applicable(t_prime) => self.unify(
                l + 1,
                cxt,
                self.closure_apply(t, Val::vvar(l)),
                self.v_app(t_prime.clone(), Val::vvar(l), *i),
                spec.as_deref_mut(),
            ),
            (Val::Flex(m, sp), t_prime) => self.solve(l, *m, sp.clone(), t_prime.clone()),
            (t, Val::Flex(m_prime, sp_prime)) => {
                self.solve(l, *m_prime, sp_prime.clone(), t.clone())
            }
            (Val::LiteralType, Val::LiteralType) => Ok(()),
            (Val::LiteralType, Val::Prim) => Ok(()),
            (Val::Prim, Val::LiteralType) => Ok(()),
            (Val::Sum(a, params_a, _), Val::Sum(b, params_b, _)) if a.data == b.data => {
                // params_a.len() always equal to params_b.len()?
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(
                        l,
                        cxt,
                        a.1.as_ref().clone(),
                        b.1.as_ref().clone(),
                        spec.as_deref_mut(),
                    )?;
                }
                Ok(())
            }
            (
                Val::SumCase { typ: a, case_name: ca, datas: params_a },
                Val::SumCase { typ: b, case_name: cb, datas: params_b },
            ) if ca.data == cb.data => {
                // params_a.len() always equal to params_b.len()?
                self.unify(l, cxt, a.as_ref().clone(), b.as_ref().clone(), spec.as_deref_mut())?;
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(
                        l,
                        cxt,
                        a.1.as_ref().clone(),
                        b.1.as_ref().clone(),
                        spec.as_deref_mut(),
                    )?;
                }
                Ok(())
            }
            (Val::Match(s1, env1, cases1, pending1), Val::Match(s2, env2, cases2, pending2)) => {
                // 快速路径（L07 struct_eq 同款）：scrutinee / 捕获 env / 模式 /
                // 分支体 / pending 全部结构相同 ⇒ 两个 match 值在所有实例化下
                // 行为一致，直接判等。逐分支重求值会把递归函数的分支体再展开
                // 一层卡住 match（fresh rigid 层级随深度递增，永不收敛）——同一
                // 值在合一两侧各展开一份时正是这种自比较，必须短路。
                if super::struct_eq::val_eq(s1, s2)
                    && super::struct_eq::env_eq(env1, env2)
                    && cases1.len() == cases2.len()
                    && cases1
                        .iter()
                        .zip(cases2.iter())
                        .all(|((p1, b1), (p2, b2))| p1 == p2 && super::struct_eq::tm_eq(b1, b2))
                    && pending1.len() == pending2.len()
                    && pending1
                        .iter()
                        .zip(pending2.iter())
                        .all(|((a, i), (b, j))| i == j && super::struct_eq::val_eq(a, b))
                {
                    return Ok(());
                }
                // 总次数预算（P2）：快路径**先试**，只有快路径失效、真正逐分支
                // 重求值的比较才计入并消耗。超出按"无法判定为相等"保守失败
                // （P3：Undecided；不放过真矛盾——Err 在所有消费点都是失败）。
                if !self.burn_match_cmp_budget() {
                    self.note_unify_kind(super::UnifyKind::Undecided);
                    return Err(UnifyError);
                }
                // 1. 合一 scrutinees
                self.unify(l, cxt, (**s1).clone(), (**s2).clone(), spec.as_deref_mut())?;

                // 2. 检查分支数量是否相同
                if cases1.len() != cases2.len() {
                    return Err(UnifyError);
                }

                // 3. 遍历并合一每一个对应的分支
                for ((p1, clos1), (p2, clos2)) in cases1.iter().zip(cases2.iter()) {
                    // 3a. 检查模式是否完全相同（Pattern 的 PartialEq 足够）。
                    if p1 != p2 {
                        return Err(UnifyError);
                    }

                    let count = p1.bind_count();

                    let env1 = (0..count).fold(env1.clone(), |env, idx| {
                        env.prepend(Val::vvar(l + idx))
                    });

                    let env2 = (0..count).fold(env2.clone(), |env, idx| {
                        env.prepend(Val::vvar(l + idx))
                    });

                    /*println!(
                        "unify {:?}\n   == {:?}",
                        pretty_tm(0, cxt.names(), clos1),
                        pretty_tm(0, cxt.names(), clos2),
                    );*/
                    //let body1_val = self.eval(&bind_env, clos1.clone());
                    //let body2_val = self.eval(&bind_env, clos2.clone());
                    // 两个分支体在中性全局视图下求值（全局名字不再展开，免
                    // 递归）——取代旧的整机克隆 + 就地改写 global 表
                    let body1_val = self.eval_neutral(&env1, clos1.clone());
                    let body2_val = self.eval_neutral(&env2, clos2.clone());

                    /*println!(
                        "-> {:?}\n== {:?}",
                        pretty_tm(0, cxt.names(), &self.quote(l, body1_val.clone())),
                        pretty_tm(0, cxt.names(), &self.quote(l, body2_val.clone())),
                    );*/
                    self.unify(l + count, cxt, body1_val, body2_val, spec.as_deref_mut())?;
                }

                // 4. 卡住期累积的实参逐一比较（长度/icit 先判，零成本）
                if pending1.len() != pending2.len() {
                    return Err(UnifyError);
                }
                for ((u1, i1), (u2, i2)) in pending1.iter().zip(pending2.iter()) {
                    if i1 != i2 {
                        return Err(UnifyError);
                    }
                    self.unify(l, cxt, u1.clone(), u2.clone(), spec.as_deref_mut())?;
                }

                // 如果所有检查都通过，则合一成功
                Ok(())
            }
            _ => {
                // 没有任何臂命中：两侧都是规范值/类型头且形态不同 ⇒ 确定不等
                // （Absurd）；预算耗尽 ⇒ Fuel（判定不可信，最保守）；其余
                // （中性头 vs 别的东西、混合形态）⇒ 判不出来（Undecided）。
                if self.fuel_exhausted() {
                    self.note_unify_kind(super::UnifyKind::Fuel);
                } else if !(Self::is_canonical_head(&t) && Self::is_canonical_head(&u)) {
                    self.note_unify_kind(super::UnifyKind::Undecided);
                }
                Err(UnifyError) // Rigid mismatch error
            }
        }
    }

    /// 规范值 / 规范类型头：两个这样的值形态不同即确定不等（不是"判不出来"，
    /// 对齐 L07 `unify_no_arm` 的 definite 判定）。
    fn is_canonical_head(v: &Val) -> bool {
        matches!(
            v,
            Val::Sum(..)
                | Val::SumCase { .. }
                | Val::LiteralType
                | Val::LiteralIntro(_)
                | Val::U(_)
                | Val::Pi(..)
                | Val::Lam(..)
        )
    }
}
