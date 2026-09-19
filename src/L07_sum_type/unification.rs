//! Unification。骨架 = elaboration-zoo 07 的 meta 求解器（invert / prune /
//! rename / solve / intersect），在此基础上：
//! - 全局引用 `Val::Decl` 作为中性头参与（与 Rigid 同型处理）；
//! - **模式特化与常规转换共用本合一器**：可解性经 `SpecSolve` 参数显式
//!   穿参——`spec` 非空（模式走查 / 覆盖探测）时 bare rigid 可解，解记入
//!   `spec.acc`（显式替换，dpm-nbe 的 `insertSub`/`subst s2 s1`），由
//!   force 在读点惰性展开；`spec = None`（分支体检查等常规转换）时不得
//!   解假设。每次递归入口把方程两侧置于**当前 acc 之下**再解释——
//!   dpm-nbe `subst ɑ vs`（剩余方程置于解之下）的惰性等价物；
//! - Sum / SumCase 按参数逐槽合一（索引等式在此生效）；
//! - 卡住的 `Val::Match`：`Match vs Match` 先比 scrutinee、再逐分支在 fresh
//!   变量槽下比体；`Match vs 其它` 只接受严格 eta（每个分支都是通配且
//!   分支体就是 scrutinee 本身）——能归约的 match 在入口 `force` 时已
//!   消掉，防止把任意 `f x` 证成 `x`；
//! - `rename` 对 Match 的分支体做"fresh rigid 槽 + 简化 decl 表求值再
//!   rename"。槽位布局在新架构下永不漂移（精化不改写槽、不剪枝已解
//!   变量），rename 产物的 λ 深度与使用现场天然一致。

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smol_str::SmolStr;

use crate::{list::List, parser_lib::Span};

use super::{
    pretty::pretty_tm,
    v_applicable, wrap_sub, val_mentions_lvl, Infer, Lvl, MetaEntry, MetaVar, PatternDetail, Spine,
    Subst, Tm, UnifyError, Val, VTy,
    cxt::{Cxt, Decls},
    lvl2ix,
    parser::syntax::Icit,
    syntax::Pruning,
    Ix,
};

/// 特化合一的进行时状态（dpm-nbe `unifyS` 的 Γ-shrinking + ɑ-accumulation
/// 的 Rust 形态）。`solvable` = 本子句可解的 rigid 层级（模式槽 + 外层
/// bind 槽基线）；`acc` = 已解出的替换——编译器的 σ 作种子，方程途中
/// 叠加，调用方在方程结束后取走 `acc` 作为新 σ（臂边界回滚 = 恢复快照
/// 指针）。
pub(crate) struct SpecSolve<'a> {
    pub(crate) solvable: &'a [Lvl],
    pub(crate) acc: Rc<Subst>,
}

/// η 展开的可应用性守卫的实现体已上移到 mod.rs（`super::v_applicable`，
/// frcs 的 Rigid 读点共用同一守卫）。

#[derive(Debug, Clone)]
struct PartialRenaming {
    occ: Option<MetaVar>,
    dom: Lvl,               // Γ 的大小
    cod: Lvl,               // Δ 的大小
    ren: HashMap<u32, Lvl>, // Δ 变量 → Γ 变量
}

/// lift / skip 的性能口径（性能评审 P1-1）：旧版每 binder 克隆整张
/// `ren` HashMap（O(n·k) 哈希 + n 次分配，rename 单分支 O(bind²)）。现为
/// **原位插入 + 按值转移**：
/// - `lift_in_place` 在独占表上追加一个绑定器槽，O(1)；
/// - `lift` / `skip` 按值消费——调用方持有独占表（线性递归 / 每臂私有
///   副本）时零克隆；
/// - `rename_arm` 的 Lam/Pi 臂只有**借用**（兄弟子树复用同一 renaming），
///   用"原位插入 + 递归后回滚"（[`Self::unlift`]）达成同款零克隆——回滚
///   保证兄弟子树看到的表与克隆版 lift 的临时副本逐位一致。
fn lift_in_place(pr: &mut PartialRenaming) {
    pr.ren.insert(pr.cod.0, pr.dom);
    pr.dom = pr.dom + 1;
    pr.cod = pr.cod + 1;
}

fn lift(mut pr: PartialRenaming) -> PartialRenaming {
    lift_in_place(&mut pr);
    pr
}

fn skip(mut pr: PartialRenaming) -> PartialRenaming {
    pr.cod = pr.cod + 1;
    pr
}

/// lift 原位插入的回滚：恢复槽位旧值（无旧值则移除）——调用点保证插入/
/// 回滚配对，兄弟子树看到的表与克隆版 lift 语义逐位一致。
fn unlift(pr: &mut PartialRenaming, key: u32, prev: Option<Lvl>) {
    match prev {
        Some(v) => {
            pr.ren.insert(key, v);
        }
        None => {
            pr.ren.remove(&key);
        }
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
        decl: &Decls,
        sp: Spine,
    ) -> Result<(Lvl, HashMap<u32, Lvl>, HashSet<u32>, List<(Lvl, Icit)>), UnifyError> {
        match sp {
            List { head: None, .. } => Ok((Lvl(0), HashMap::new(), HashSet::new(), List::new())),
            a => {
                let (dom, mut ren, mut nlvars, fsp) = self.invert_go(decl, a.tail())?;
                match self.force_arg(decl, a.head().unwrap().0.clone()) {
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

    fn invert(
        &self,
        decl: &Decls,
        gamma: Lvl,
        sp: Spine,
    ) -> Result<(PartialRenaming, Option<Pruning>), UnifyError> {
        let (dom, ren, nlvars, fsp) = self.invert_go(decl, sp)?;
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
        decl: &Decls,
        rev: &[Option<Icit>],
        // 按值持有：本递归是线性的（每层 lift/skip 后旧表不再使用），
        // lift/skip 原位插入零克隆（P1-1）。
        mut pren: PartialRenaming,
        a: Val,
    ) -> Result<Tm, UnifyError> {
        // 掩码按"外→内"配对 Π 层：`rev` 头 = 最外层槽位（`prune_ty` 已把
        // Pruning 反转——List 头是最内层）。旧实现直接按链头配对外层 Π，
        // 多层 telescope + 混合掩码时掩码与 Π 层错位（L05 已修的同款）。
        match (rev.split_first(), self.force(decl, a)) {
            (None, a) => self.rename(decl, &mut pren, a),
            (Some((Some(_), rest)), Val::Pi(x, i, a, b)) => {
                let a = self.rename(decl, &mut pren, *a)?;
                let b = self.closure_apply(decl, &b, Val::vvar(pren.cod));
                let b = self.prune_ty_go(decl, rest, lift(pren), b)?;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            (Some((None, rest)), Val::Pi(_, _, _, b)) => {
                let b = self.closure_apply(decl, &b, Val::vvar(pren.cod));
                self.prune_ty_go(decl, rest, skip(pren), b)
            }
            _ => Err(UnifyError),
        }
    }

    fn prune_ty(&mut self, decl: &Decls, pr: &Pruning, a: Val) -> Result<Tm, UnifyError> {
        // Pruning 头 = 最内层槽位；meta 类型的 Π 层从最外层剥起——先反转
        // 成"外→内"（RevPruning，上游 05 的 pruneTy 同款）。
        let mut rev: Vec<Option<Icit>> = pr.iter().copied().collect();
        rev.reverse();
        self.prune_ty_go(
            decl,
            &rev,
            PartialRenaming {
                occ: None,
                dom: Lvl(0),
                cod: Lvl(0),
                ren: HashMap::new(),
            },
            a,
        )
    }

    fn prune_meta(&mut self, decl: &Decls, pruning: Pruning, m: MetaVar) -> Result<MetaVar, UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            // force 在 fuel 耗尽时会把已解 meta 当未解返回（拒绝展开），
            // 随后走到的剪枝/求解按合一失败降级，不 panic——与"fuel 耗尽
            // 按未解失败"的既有降级故事一致（窗口：恰在 1→0 递减帧内）
            _ => return Err(UnifyError),
        };

        let prune_ty = self.prune_ty(decl, &pruning, mty.clone())?;
        let prunedty = self.eval(decl, &List::new(), &prune_ty);
        let m_prime = self.new_meta(prunedty);

        let sol_tm = self.lams(
            decl,
            Lvl(pruning.len() as u32),
            mty.clone(),
            Tm::AppPruning(Box::new(Tm::Meta(m_prime)), pruning),
        );
        let solution = self.eval(decl, &List::new(), &sol_tm);

        self.overwrite_meta(m, MetaEntry::Solved(solution, mty));
        Ok(m_prime)
    }

    fn prune_vflex_go(
        &mut self,
        decl: &Decls,
        pren: &mut PartialRenaming,
        sp: Spine,
    ) -> Result<(List<(Option<Tm>, Icit)>, SpinePruneStatus), UnifyError> {
        if sp.head().is_none() {
            Ok((List::new(), SpinePruneStatus::OKRenaming))
        } else {
            let (sp_rest, status) = self.prune_vflex_go(decl, pren, sp.tail())?;
            match self.force_arg(decl, sp.head().unwrap().0.clone()) {
                Val::Rigid(x, List { head: None, .. }) => match (pren.ren.get(&x.0), status) {
                    (Some(x), _) => Ok((
                        sp_rest.prepend((Some(Tm::Var(lvl2ix(pren.dom, *x))), sp.head().unwrap().1)),
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
                        let t = self.rename(decl, pren, t)?;
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
        decl: &Decls,
        pren: &mut PartialRenaming,
        m: MetaVar,
        sp: Spine,
    ) -> Result<Tm, UnifyError> {
        let (sp, status) = self.prune_vflex_go(decl, pren, sp)?;

        let m_prime = match status {
            SpinePruneStatus::OKRenaming | SpinePruneStatus::OKNonRenaming => {
                match self.meta[m.0 as usize] {
                    MetaEntry::Unsolved(_) => m,
                    // fuel 耗尽窗口（同 prune_meta 注）：已解 meta 被 force
                    // 当未解返回后走到这里，按失败降级
                    _ => return Err(UnifyError),
                }
            }
            SpinePruneStatus::NeedsPruning => {
                self.prune_meta(decl, sp.map(|(mt, i)| mt.as_ref().map(|_| *i)), m)?
            }
        };

        // 应用序重建：spine 头 = 最后应用的实参，先反转成"最先应用在前"
        // 再折叠——旧实现直接从头折叠把最后应用的实参包到最内层，多实参
        // 剪枝的解应用序倒置（L05 已修的同款）。
        let mut slots: Vec<(Option<Tm>, Icit)> = sp.iter().cloned().collect();
        slots.reverse();
        let t = slots.into_iter().fold(Tm::Meta(m_prime), |t, (mu, i)| {
            if let Some(u) = mu {
                Tm::App(Box::new(t), Box::new(u), i)
            } else {
                t
            }
        });

        Ok(t)
    }

    fn rename_sp(
        &mut self,
        decl: &Decls,
        pren: &mut PartialRenaming,
        t: Tm,
        sp: &Spine,
    ) -> Result<Tm, UnifyError> {
        match sp {
            List { head: None, .. } => Ok(t),
            a => {
                let t = self.rename_sp(decl, pren, t, &a.tail())?;
                let u = self.rename(decl, pren, a.head().unwrap().0.clone())?;
                Ok(Tm::App(Box::new(t), Box::new(u), a.head().unwrap().1))
            }
        }
    }

    fn rename(&mut self, decl: &Decls, pren: &mut PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        static REN_DEPTH: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
        if super::LOOP_DEBUG.load(std::sync::atomic::Ordering::Relaxed) {
            let d = REN_DEPTH.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            if d > 2000 && d % 500 == 0 {
                eprintln!("  REN depth {d}");
            }
            struct G;
            impl Drop for G {
                fn drop(&mut self) {
                    REN_DEPTH.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                }
            }
            let _g = G;
        }
        let v = self.force(decl, t);
        // 深链分派（README §7.6，2026-09-18）：Sum / SumCase / Obj 是唯一能
        // 按值深度自嵌的形态（succ^N 链经 datas[0]），交给帧式收集器
        // [`Self::rename_deep`]；其余形态（Lam/Pi/Match/spine 头——结构嵌套
        // 浅）回落 [`Self::rename_arm`]，其子值调用点回到本入口——深链在
        // 任意深度进入收集器后整链消化，native 栈深 = 结构嵌套而非值深。
        match v {
            Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => {
                self.rename_deep(decl, pren, v)
            }
            _ => self.rename_arm(decl, pren, v),
        }
    }

    /// rename 的深链收集器：Sum / SumCase / Obj 帧式下降/组装（子件顺序、
    /// App 折叠序与旧递归臂逐点一致——rename_sp 的应用序 = spine List
    /// 尾先头后）。子件回落 [`Self::rename_arm`]（同 pren，无 lift——
    /// 对齐旧臂：Sum 参数/SumCase 字段/Obj 内层与实参都在同一 renaming 下）。
    fn rename_deep(
        &mut self,
        decl: &Decls,
        pren: &mut PartialRenaming,
        root: Val,
    ) -> Result<Tm, UnifyError> {
        enum FrameKind {
            Sum {
                name: Span<String>,
                cases: Vec<Span<String>>,
                metas: Vec<(Span<String>, Icit)>,
            },
            SumCase {
                case_name: Span<String>,
                datas_metas: Vec<(Span<String>, Icit)>,
            },
            Obj {
                name: Span<String>,
            },
        }
        // 帧**不**持有 renaming：深链所有帧共用调用方的同一 pren（子件
        // 无 lift），rename_arm 的 Lam/Pi 原位 lift 自带回滚，帧间无痕
        // （P1-1： pren 由 &mut 穿线，不再克隆进帧）。
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
                    for (n, v, t, i) in params {
                        pending.push(super::rc_take(v));
                        pending.push(super::rc_take(t));
                        metas.push((n, i));
                    }
                    let n_all = pending.len();
                    Frame {
                        pending,
                        icits: Vec::new(),
                        kind: FrameKind::Sum { name, cases, metas },
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
                    for (n, v, i) in datas {
                        pending.push(super::rc_take(v));
                        datas_metas.push((n, i));
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
                    let mut pending = vec![*x];
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
                FrameKind::Sum { name, cases, metas } => {
                    let mut it = frame.done.into_iter();
                    let params = metas
                        .into_iter()
                        .map(|(n, i)| {
                            let v = it.next().unwrap();
                            let t = it.next().unwrap();
                            (n, v, t, i)
                        })
                        .collect();
                    Tm::Sum(name, params, cases)
                }
                FrameKind::SumCase {
                    case_name,
                    datas_metas,
                } => {
                    let mut it = frame.done.into_iter();
                    let typ = it.next().unwrap();
                    let datas = datas_metas
                        .into_iter()
                        .map(|(n, i)| (n, it.next().unwrap(), i))
                        .collect();
                    Tm::SumCase {
                        typ: Box::new(typ),
                        case_name,
                        datas,
                    }
                }
                FrameKind::Obj { name } => {
                    let mut it = frame.done.into_iter();
                    let head = Tm::Obj(Box::new(it.next().unwrap()), name);
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
            let w = frame.pending[frame.idx].clone();
            let w = self.force(decl, w);
            match w {
                Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => {
                    // 子帧组装回填时推进本帧 idx
                    frames.push(frame_new(w));
                }
                _ => {
                    let tm = self.rename_arm(decl, pren, w)?;
                    let frame = frames.last_mut().unwrap();
                    frame.done.push(tm);
                    frame.idx += 1;
                }
            }
        }
        Ok(result.expect("rename_deep 至少产出一个 Tm"))
    }

    /// rename 的浅结构臂（入口已 force、已分派掉深链形态）。
    fn rename_arm(&mut self, decl: &Decls, pren: &mut PartialRenaming, t: Val) -> Result<Tm, UnifyError> {
        match t {
            // 不变式：force 的返回值顶层不会是 VSub（入口已推开）
            Val::VSub(..) => Err(UnifyError),
            // 深链形态在入口已分派给 rename_deep，这里不可达；与 VSub 臂
            // 同样的防御性回落（不改写值，直接失败交上层诊断）
            Val::Sum(..) | Val::SumCase { .. } | Val::Obj(..) => Err(UnifyError),
            Val::Flex(m_prime, sp) => match pren.occ {
                Some(m) if m == m_prime => Err(UnifyError),
                _ => self.prune_vflex(decl, pren, m_prime, sp),
            },
            Val::Rigid(x, sp) => match pren.ren.get(&x.0) {
                None => Err(UnifyError), // scope error
                Some(x_prime) => {
                    let t = Tm::Var(lvl2ix(pren.dom, *x_prime));
                    self.rename_sp(decl, pren, t, &sp)
                }
            },
            Val::Decl(name, sp) => self.rename_sp(decl, pren, Tm::Decl(name), &sp),
            Val::Lam(x, i, closure) => {
                let body_v = self.closure_apply(decl, &closure, Val::vvar(pren.cod));
                // lift 原位 + 递归后回滚（P1-1）：兄弟子树复用同一张表，
                // 回滚后与"克隆版 lift 的临时副本"逐位一致；Err 路径同样
                // 回滚（错误沿栈传播，pren 不再复用，回滚只为不变式干净）。
                let key = pren.cod.0;
                let prev = pren.ren.insert(key, pren.dom);
                pren.dom = pren.dom + 1;
                pren.cod = pren.cod + 1;
                let t = match self.rename(decl, pren, body_v) {
                    Ok(t) => t,
                    Err(e) => {
                        unlift(pren, key, prev);
                        pren.dom = pren.dom - 1;
                        pren.cod = pren.cod - 1;
                        return Err(e);
                    }
                };
                unlift(pren, key, prev);
                pren.dom = pren.dom - 1;
                pren.cod = pren.cod - 1;
                Ok(Tm::Lam(x, i, Box::new(t)))
            }
            Val::Pi(x, i, a, closure) => {
                let a = self.rename(decl, pren, *a)?;
                let body_v = self.closure_apply(decl, &closure, Val::vvar(pren.cod));
                // lift 原位 + 回滚（同 Lam 臂）
                let key = pren.cod.0;
                let prev = pren.ren.insert(key, pren.dom);
                pren.dom = pren.dom + 1;
                pren.cod = pren.cod + 1;
                let b = match self.rename(decl, pren, body_v) {
                    Ok(b) => b,
                    Err(e) => {
                        unlift(pren, key, prev);
                        pren.dom = pren.dom - 1;
                        pren.cod = pren.cod - 1;
                        return Err(e);
                    }
                };
                unlift(pren, key, prev);
                pren.dom = pren.dom - 1;
                pren.cod = pren.cod - 1;
                Ok(Tm::Pi(x, i, Box::new(a), Box::new(b)))
            }
            Val::U => Ok(Tm::U),
            Val::LiteralType => Ok(Tm::LiteralType),
            Val::LiteralIntro(x) => Ok(Tm::LiteralIntro(x)),
            Val::Prim(name, sp) => self.rename_sp(decl, pren, Tm::Prim(name), &sp),
            Val::Match(val, env, cases, pending) => {
                // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"下重新求值
                // （简化 decl 表防重展开），再在 lift 过的 renaming 下 rename
                let val = self.rename(decl, pren, *val)?;
                // P1-2：简化表旁路缓存（同实例只构建一次）
                let declb = self.simpl_decl_cached(decl);
                let cases = cases
                    .iter()
                    .map(|(pat, tm)| {
                        let count = pat.bind_count();
                        // 每分支一张私有表（原 pren 保持不动，供 pending 实参
                        // 复用）：整表克隆一次后 k 次 lift 全部原位插入
                        // （P1-1：旧版每 lift 克隆整表，单分支 O(bind²)）
                        let mut env = env.clone();
                        let mut pren_c = pren.clone();
                        for _ in 0..count {
                            env = env.prepend(Val::vvar(pren_c.cod));
                            lift_in_place(&mut pren_c);
                        }
                        // 同 quote(Match)：rename 用简化表，防止中性递归引用
                        // 被入口 force 再展开（解里带卡住 match 时发散）
                        let body = self.rename(&declb, &mut pren_c, self.eval(&declb, &env, tm))?;
                        Ok((pat.clone(), body))
                    })
                    .collect::<Result<_, UnifyError>>()?;
                // 卡住期累积的实参：同 quote，包在 Match 外的 App 链里
                let m = Tm::Match(Box::new(val), cases);
                pending.into_iter().fold(Ok(m), |acc: Result<Tm, UnifyError>, (u, i)| {
                    let u = self.rename(decl, pren, u)?;
                    Ok(Tm::App(Box::new(acc?), Box::new(u), i))
                })
            }
        }
    }

    fn lams_go(&self, decl: &Decls, l: Lvl, t: Tm, a: VTy, l_prime: Lvl) -> Tm {
        if l == l_prime {
            t
        } else {
            match self.force(decl, a) {
                Val::Pi(span, icit, _, closure) => Tm::Lam(
                    span,
                    icit,
                    Box::new(self.lams_go(
                        decl,
                        l,
                        t,
                        self.closure_apply(decl, &closure, Val::vvar(l_prime)),
                        l_prime + 1,
                    )),
                ),
                _ => unreachable!(),
            }
        }
    }

    fn lams(&self, decl: &Decls, l: Lvl, a: VTy, t: Tm) -> Tm {
        self.lams_go(decl, l, t, a, Lvl(0))
    }

    fn solve(&mut self, decl: &Decls, gamma: Lvl, m: MetaVar, sp: Spine, rhs: Val) -> Result<(), UnifyError> {
        let (pren, prune_non_linear) = self.invert(decl, gamma, sp)?;
        self.solve_with_pren(decl, m, pren, prune_non_linear, rhs)
    }

    fn solve_with_pren(
        &mut self,
        decl: &Decls,
        m: MetaVar,
        pren: PartialRenaming,
        prune_non_linear: Option<Pruning>,
        rhs: Val,
    ) -> Result<(), UnifyError> {
        let mty = match self.meta[m.0 as usize] {
            MetaEntry::Unsolved(ref a) => a.clone(),
            // fuel 耗尽窗口（同 prune_meta 注）：已解 meta 被 force 当未解
            // 返回后走到求解臂，按合一失败降级而不是 panic
            _ => return Err(UnifyError),
        };

        // spine 非线性时，检查这些参数能从 meta 类型里剪掉（保证解是良型的）
        if let Some(pr) = prune_non_linear {
            self.prune_ty(decl, &pr, mty.clone())?;
        }

        // occ 换成本 meta（occurs 守卫）；dom/cod/ren 原样转移
        let mut pren = PartialRenaming {
            occ: Some(m),
            ..pren
        };
        let rhs = self.rename(decl, &mut pren, rhs)?;
        let sol_tm = self.lams(decl, pren.dom, mty.clone(), rhs);
        let solution = self.eval(decl, &List::new(), &sol_tm);
        self.overwrite_meta(m, MetaEntry::Solved(solution, mty));

        Ok(())
    }

    fn unify_sp(
        &mut self,
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        sp: &Spine,
        sp_prime: &Spine,
        mut spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Ok(()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                self.unify_sp(decl, l, cxt, &a.tail(), &b.tail(), spec.as_deref_mut())?;
                self.unify(
                    decl,
                    l,
                    cxt,
                    a.head().unwrap().0.clone(),
                    b.head().unwrap().0.clone(),
                    spec,
                )
            }
            _ => Err(UnifyError),
        }
    }

    fn flex_flex(
        &mut self,
        decl: &Decls,
        gamma: Lvl,
        m: MetaVar,
        sp: Spine,
        m_prime: MetaVar,
        sp_prime: Spine,
    ) -> Result<(), UnifyError> {
        let mut go = |this: &mut Self,
                      m: MetaVar,
                      sp: Spine,
                      m_prime: MetaVar,
                      sp_prime: Spine|
         -> Result<(), UnifyError> {
            match this.invert(decl, gamma, sp.clone()) {
                Err(UnifyError) => this.solve(decl, gamma, m_prime, sp_prime, Val::Flex(m, sp)),
                Ok((pren, p1)) => this.solve_with_pren(decl, m, pren, p1, Val::Flex(m_prime, sp_prime)),
            }
        };

        // 先试一方，失败再试另一方。只按 spine 长度选一个方向，会在
        // "长 spine 含非 rigid 项（变量槽被精化成构造子值）"时漏掉
        // 可行方向（test5 的内层 match 场景）。
        // 第一次尝试可能已 solve 部分 meta 才失败，反向尝试前回滚。
        // （P0-2：回滚为 undo-log 水位，不再全量深拷贝 metacontext）
        let snap = self.meta_snapshot();
        let (m1, sp1, m2, sp2) = if sp.len() <= sp_prime.len() {
            (m, sp, m_prime, sp_prime)
        } else {
            (m_prime, sp_prime, m, sp)
        };
        match go(self, m1, sp1.clone(), m2, sp2.clone()) {
            Ok(()) => Ok(()),
            Err(_) => {
                self.meta_restore(snap);
                match go(self, m2, sp2, m1, sp1) {
                    Ok(()) => Ok(()),
                    Err(e) => Err(e),
                }
            }
        }
    }

    fn intersect_go(&mut self, decl: &Decls, sp: Spine, sp_prime: Spine) -> Option<List<Option<Icit>>> {
        match (sp, sp_prime) {
            (List { head: None, .. }, List { head: None, .. }) => Some(List::new()),
            (a, b) if a.head().is_some() && b.head().is_some() => {
                match (
                    self.force(decl, a.head().unwrap().0.clone()),
                    self.force(decl, b.head().unwrap().0.clone()),
                ) {
                    (
                        Val::Rigid(x, List { head: None, .. }),
                        Val::Rigid(x_prime, List { head: None, .. }),
                    ) => self.intersect_go(decl, a.tail(), b.tail()).map(|l| {
                        l.prepend(if x == x_prime {
                            Some(a.head().unwrap().1)
                        } else {
                            None
                        })
                    }),
                    _ => None,
                }
            }
            // 长度失配：不 panic，回落 unify_sp 的长度失配失败（L05 同款）
            _ => None,
        }
    }

    fn intersect(
        &mut self,
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        m: MetaVar,
        sp: Spine,
        sp_prime: Spine,
        spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        match self.intersect_go(decl, sp.clone(), sp_prime.clone()) {
            None => self.unify_sp(decl, l, cxt, &sp, &sp_prime, spec),
            Some(pr) if pr.iter().any(|x| x.is_none()) => {
                self.prune_meta(decl, pr, m)?;
                Ok(())
            }
            Some(_) => Ok(()),
        }
    }

    /// 宽松臂的实现体：未登记名放行，已登记名按登记类型把关。
    fn loose_string(
        &mut self,
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        n: &SmolStr,
        spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        match decl.get(n) {
            None => Ok(()),
            Some(e) => {
                let ty = e.ty.clone();
                self.unify(decl, l, cxt, Val::LiteralType, ty, spec)
            }
        }
    }

    pub fn unify(
        &mut self,
        decl: &Decls,
        l: Lvl,
        cxt: &Cxt,
        t: Val,
        u: Val,
        mut spec: Option<&mut SpecSolve<'_>>,
    ) -> Result<(), UnifyError> {
        // 递归深度防护：索引槽互相嵌入的构造子值比较会无限递归
        let fuel = self.unify_fuel.get();
        if fuel == 0 {
            if super::LOOP_DEBUG.load(std::sync::atomic::Ordering::Relaxed) {
                eprintln!(
                    "  LOOP @ unify: {} vs {}",
                    pretty_tm(0, cxt.names(), &self.quote(decl, l, t.clone())),
                    pretty_tm(0, cxt.names(), &self.quote(decl, l, u.clone()))
                );
            }
            return Err(UnifyError);
        }
        self.unify_fuel.set(fuel - 1);
        if super::LOOP_DEBUG.load(std::sync::atomic::Ordering::Relaxed) && fuel < 4090 && fuel % 100 == 0 {
            eprintln!(
                "  deep{fuel}: {} vs {}",
                pretty_tm(0, cxt.names(), &self.quote(decl, l, t.clone())),
                pretty_tm(0, cxt.names(), &self.quote(decl, l, u.clone()))
            );
        }
        let mut t = self.force(decl, t);
        let mut u = self.force(decl, u);
        // 特化模式：方程两侧置于**当前已积累的解**之下再解释（dpm-nbe
        // `subst ɑ vs` 的惰性等价物）。每次递归入口按当时的 acc 重新包裹
        // ——先解出的方程对后到的子方程自动可见，解两次的情形按构造
        // 排除（已解变量不再以 bare rigid 出现）。acc 为空时零开销。
        if let Some(s) = spec.as_deref() {
            if !s.acc.is_empty() {
                t = self.force(decl, wrap_sub(&s.acc, t));
                u = self.force(decl, wrap_sub(&s.acc, u));
            }
        }

        match (&t, &u) {
            (Val::U, Val::U) => Ok(()),
            (Val::Pi(x, i, a, b), Val::Pi(x_prime, i_prime, a_prime, b_prime)) if i == i_prime => {
                self.unify(decl, l, cxt, (**a).clone(), (**a_prime).clone(), spec.as_deref_mut())?;
                self.unify(
                    decl,
                    l + 1,
                    // quote 用**当前层级 l**而不是 cxt.lvl：Lam 的 η 递归臂
                    // `l+1` 不推进 cxt（binder 类型在值层不可得），`l == cxt.lvl`
                    // 的不变式在那里就会破——用 cxt.lvl quote 会把 `Rigid(l)`

                    // 打越界（lvl2ix assert；L08 Exists 的 `P witness` 域踩中，
                    // L07 同码潜伏，自 L08 回合）。cxt 只服务显示名字表，名字
                    // 对不上时 go_ix 有 `@i` 兜底。
                    &cxt.bind(
                        x.clone(),
                        self.quote(decl, l, (**a).clone()),
                        (**a).clone(),
                    ),

                    self.closure_apply(decl, b, Val::vvar(l)),
                    self.closure_apply(decl, b_prime, Val::vvar(l)),
                    spec.as_deref_mut(),
                )
            }
            (Val::Rigid(x, sp), Val::Rigid(x_prime, sp_prime)) if x == x_prime => {
                self.unify_sp(decl, l, cxt, sp, sp_prime, spec.as_deref_mut())
            }
            // 模式特化（dpm-nbe unify1 的 VVar 臂）：可解 rigid（spec 携带的
            // 模式槽集）与非 Flex 值相遇 ⇒ 解入 `spec.acc`（显式替换，force
            // 读点惰性展开）。Flex 除外——交给 Flex 规则（meta := var）。
            // occurs 环守卫失败 = Err（对齐旧 pm_solve false ⇒ Err：调用侧
            // 判为分支不可达）。spec = None（常规转换）时守卫不成立，落空
            // 到后续臂——不得解假设，否则 `Eq x y` 会被"证成" `Eq y y`。
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
            // 全局引用：同名比 spine，不同名失败（force 已展开可展开的）
            (Val::Decl(a, sp), Val::Decl(b, sp_prime)) if a == b => {
                self.unify_sp(decl, l, cxt, sp, sp_prime, spec.as_deref_mut())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) if m == m_prime => {
                self.intersect(decl, l, cxt, *m, sp.clone(), sp_prime.clone(), spec.as_deref_mut())
            }
            (Val::Flex(m, sp), Val::Flex(m_prime, sp_prime)) => {
                self.flex_flex(decl, l, *m, sp.clone(), *m_prime, sp_prime.clone())
            }
            (Val::Lam(_, _, b), Val::Lam(_, _, b_prime)) => self.unify(
                decl,
                l + 1,
                cxt,
                self.closure_apply(decl, b, Val::vvar(l)),
                self.closure_apply(decl, b_prime, Val::vvar(l)),
                spec.as_deref_mut(),
            ),
            (t, Val::Lam(_, i, b_prime)) if v_applicable(t) => self.unify(
                decl,
                l + 1,
                cxt,
                self.v_app(decl, t.clone(), Val::vvar(l), *i),
                self.closure_apply(decl, b_prime, Val::vvar(l)),
                spec.as_deref_mut(),
            ),
            (Val::Lam(_, i, b), t_prime) if v_applicable(t_prime) => self.unify(
                decl,
                l + 1,
                cxt,
                self.closure_apply(decl, b, Val::vvar(l)),
                self.v_app(decl, t_prime.clone(), Val::vvar(l), *i),
                spec.as_deref_mut(),
            ),
            (Val::Flex(m, sp), _) => self.solve(decl, l, *m, sp.clone(), u.clone()),
            (_, Val::Flex(m_prime, sp_prime)) => self.solve(decl, l, *m_prime, sp_prime.clone(), t.clone()),
            (Val::LiteralType, Val::LiteralType) => Ok(()),
            // 宽松臂（L06 同款把关）：String 与卡住内建 / 卡住 Decl 的宽松
            // 合一只对 decl 表**未登记名**放行——string_to_global_type 对
            // 未知名返回以其名字的卡住 Decl（动态类型的逃逸舱口）；已登记
            // 名按登记类型把关（U 型返回的 builtin 卡住值不再冒充 String）
            (Val::LiteralType, Val::Prim(n, _)) | (Val::Prim(n, _), Val::LiteralType) => {
                self.loose_string(decl, l, cxt, n, spec)
            }
            (Val::LiteralType, Val::Decl(n, _)) | (Val::Decl(n, _), Val::LiteralType) => {
                self.loose_string(decl, l, cxt, n, spec)
            }
            // 卡住的内建：同名比实参 spine（异名失败）——不带实参的单元
            // Prim 会把 `x ++ y ≡ x ++ z` 判成相等
            (Val::Prim(a, sp), Val::Prim(b, sp_prime)) if a == b => {
                self.unify_sp(decl, l, cxt, sp, sp_prime, spec.as_deref_mut())
            }
            (Val::Prim(..), Val::Prim(..)) => Err(UnifyError),
            // Sum：同名即逐参数（含索引）合一
            (Val::Sum(a, params_a, _), Val::Sum(b, params_b, _)) if a.data == b.data => {
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(
                        decl,
                        l,
                        cxt,
                        a.1.as_ref().clone(),
                        b.1.as_ref().clone(),
                        spec.as_deref_mut(),
                    )?;
                }
                Ok(())
            }
            // SumCase：同构造子才比；只比 datas（L07a 同款）。**不比 typ 的
            // 值**：typ 的索引槽就是这些值自身的构造子形态（succ ?l 的 typ
            // 里 len 槽是 succ ?l），比值必然在互相引用上深递归；索引等式
            // 的比较发生在**外层 Sum-Sum 的参数 zip**里。但**比 Sum 头名
            // 字**：跨 enum 重名构造子（E1.c / E2.c）是两个不同值，同
            // case_name 不足以判定身份——头名不同直接失败，构造子身份判
            // 据局部化，不押"喂进方程的两侧必齐型"这条未检查的不变式。
            (
                Val::SumCase {
                    typ: ta,
                    case_name: ca,
                    datas: params_a,
                },
                Val::SumCase {
                    typ: tb,
                    case_name: cb,
                    datas: params_b,
                },
            ) if ca.data == cb.data => {
                if let (Val::Sum(na, _, _), Val::Sum(nb, _, _)) = (ta.as_ref(), tb.as_ref()) {
                    if na.data != nb.data {
                        return Err(UnifyError);
                    }
                }
                for (a, b) in params_a.iter().zip(params_b.iter()) {
                    self.unify(
                        decl,
                        l,
                        cxt,
                        a.1.as_ref().clone(),
                        b.1.as_ref().clone(),
                        spec.as_deref_mut(),
                    )?;
                }
                Ok(())
            }
            // 卡住的 match vs 卡住的 match：scrutinee 合一 + 分支一一对应
            // + 卡住期累积的实参逐一比较
            (Val::Match(s1, env1, cases1, pending1), Val::Match(s2, env2, cases2, pending2)) => {
                // 快路径：scrutinee、捕获 env、模式与分支体全部结构相同 ⇒ 两个
                // match 值在所有实例化下行为一致，直接判等。逐分支重求值会把
                // 递归函数的分支体再展开一层卡住 match（fresh rigid 层级随深度
                // 递增，永不收敛）——同一 decl 值在合一两侧各展开一份时正是
                // 这种自比较，必须短路。新架构下层级永不漂移，"同一组变量"
                // 的两份捕获 env 字面相等，这条快路径即覆盖绝大多数情形。
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
                self.unify(decl, l, cxt, (**s1).clone(), (**s2).clone(), spec.as_deref_mut())?;
                if cases1.len() != cases2.len() {
                    return Err(UnifyError);
                }
                // P1-2：简化表旁路缓存（同实例只构建一次）
                let declb = self.simpl_decl_cached(decl);
                for ((p1, b1), (p2, b2)) in cases1.iter().zip(cases2.iter()) {
                    if p1 != p2 {
                        return Err(UnifyError);
                    }
                    let count = p1.bind_count();
                    let env1 = (0..count)
                        .fold(env1.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                    let env2 = (0..count)
                        .fold(env2.clone(), |env, i| env.prepend(Val::vvar(l + i)));
                    let v1 = self.eval(&declb, &env1, b1);
                    let v2 = self.eval(&declb, &env2, b2);
                    self.unify(decl, l + count, cxt, v1, v2, spec.as_deref_mut())?;
                }
                if pending1.len() != pending2.len() {
                    return Err(UnifyError);
                }
                for ((u1, i1), (u2, i2)) in pending1.iter().zip(pending2.iter()) {
                    if i1 != i2 {
                        return Err(UnifyError);
                    }
                    self.unify(decl, l, cxt, u1.clone(), u2.clone(), spec.as_deref_mut())?;
                }
                Ok(())
            }
            // 卡住的 match vs 其它：能归约的已在入口 force 消掉（force 会在
            // scrutinee 上重试选分支），这里只接受严格 eta——每个分支都是
            // 通配且分支体就是 scrutinee 本身。无条件接受会把 `f x` 证成 `x`。
            (Val::Match(s, _, cases, pending), other) | (other, Val::Match(s, _, cases, pending)) => {
                // 带 pending 实参的卡住 match 不是 eta 形态（分支体经实参
                // 应用后不再等于 scrutinee）
                if !pending.is_empty() {
                    return Err(UnifyError);
                }
                match (self.force(decl, (**s).clone()), other) {
                    (Val::Rigid(x, sp), Val::Rigid(y, sp2))
                        if x == *y && sp.is_empty() && sp2.is_empty() =>
                    {
                        let is_eta = !cases.is_empty()
                            && cases.iter().all(|(pat, body)| {
                                matches!(pat, PatternDetail::Any(..) | PatternDetail::Bind(_))
                                    && matches!(body, Tm::Var(Ix(0)))
                            });
                        if is_eta {
                            Ok(())
                        } else {
                            Err(UnifyError)
                        }
                    }
                    _ => Err(UnifyError),
                }
            }
            _ => Err(UnifyError),
        }
    }
}

#[cfg(test)]
mod deep_rename_tests {
    use super::*;

    /// README §7.6 回归钉：rename 的深链收集器（SumCase 链）在默认测试栈
    /// （约 2 MB）下迭代消化——旧递归版 1 万层会爆栈（收集器消化后 1 万层
    /// 通行）。两处测试基建之坑（非被测代码）：①输入链的 Rc 级联释放
    /// 是深递归——每层句柄保留在 keep 里（释放只递减不归零），末尾
    /// forget 泄漏；②产物 Tm 树逐层剥开（循环，每层 Box<Tm> 浅释放）。
    #[test]
    fn deep_rename_collector_under_default_stack() {
        const N: usize = 10_000;
        fn nat_sum() -> Val {
            Val::Sum(
                super::super::empty_span("Nat".to_string()),
                vec![],
                vec![
                    super::super::empty_span("zero".to_string()),
                    super::super::empty_span("succ".to_string()),
                ],
            )
        }
        let nat = std::rc::Rc::new(nat_sum());
        let mut keep: Vec<std::rc::Rc<Val>> = Vec::with_capacity(N);
        let mut v = Val::SumCase {
            typ: std::rc::Rc::clone(&nat),
            case_name: super::super::empty_span("zero".to_string()),
            datas: vec![],
        };
        for _ in 0..N {
            let inner = std::rc::Rc::new(v);
            keep.push(std::rc::Rc::clone(&inner));
            v = Val::SumCase {
                typ: std::rc::Rc::clone(&nat),
                case_name: super::super::empty_span("succ".to_string()),
                datas: vec![(super::super::empty_span("x".to_string()), inner, Icit::Expl)],
            };
        }
        let mut infer = Infer::new();
        let decl = Decls::new();
        let mut pren = PartialRenaming {
            occ: None,
            dom: Lvl(0),
            cod: Lvl(0),
            ren: std::collections::HashMap::new(),
        };
        let mut cur = infer.rename(&decl, &mut pren, v).expect("深链 rename 应成功");
        let mut depth = 0usize;
        loop {
            match cur {
                Tm::SumCase {
                    typ,
                    case_name,
                    datas,
                } => {
                    drop(typ);
                    if datas.is_empty() {
                        assert_eq!(case_name.data, "zero", "叶子应是 zero");
                        break;
                    }
                    let mut it = datas.into_iter();
                    let (_, next, _) = it.next().expect("succ 层应有 data");
                    depth += 1;
                    cur = next;
                }
                _ => panic!("深链产物应是 SumCase 链"),
            }
        }
        assert_eq!(depth, N, "剥链深度应等于构造层数");
        std::mem::forget(keep); // 泄漏给进程：避开深链的递归 Drop
    }
}
