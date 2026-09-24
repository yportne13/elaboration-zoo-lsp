//! rename：solve 族全迭代——`RenBuf` 换代缓冲、`invert_bump`/
//! `solve_with_pren_bump`/`solve_bump`、`RJob`/`rename_iter`、
//! `SpinePruneStatus`/`prune_vflex_bump`/`prune_meta_bump`/`prune_ty_bump`、
//! `alloc_xname`/`lams_from_ty`。原 bump_spine_iter.rs 的 "solve" 节，逐行
//! 搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use std::cell::RefCell;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::{env_ext, EMPTY_ENV, PiCell};
use super::eval::{eval_iter, W};
use super::force::force;
use super::machine::{v_u0, Cxt};
use super::prim::{Decls, Mutable};
use super::quote::{quote_iter, quote_nat_chain};
use super::spine::{journal_meta, MetaEntry, MetaSnap, Spine};
use super::syntax::{
    PrCons, SumDataT, SumParamT, Tm, V, XCell, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi_of,
    v_spine_of, v_tag, v_u_of, v_xcell_of,
};
use super::unify::declb_of;
use super::{empty_span, PatternDetail};


// solve（invert + prune 验证 + rename + lams，全迭代）
// --------------------------------------------------------------------------------

/// solve 的偏置换缓冲（generational）：`val[x]` 在第 `epoch` 代里给出
/// level x → 新下标；`stamp[x] == epoch` 表示条目有效。`reset` 只推进
/// epoch（O(1) 换代）。`NONE_MARK` 哨兵标记**非线性（重复）变量**——
/// `get` 视其为缺项。
#[derive(Default)]
pub(super) struct RenBuf {
    val: Vec<u32>,
    /// 各 level 槽位的生效代数（与 `val` 平行）；`== epoch` 才有效。
    stamp: Vec<u64>,
    epoch: u64,
}

/// 非线性（重复）变量的哨兵值。
const NONE_MARK: u32 = u32::MAX;

impl RenBuf {
    /// 换代即「清空」：旧条目的 gen 不等于新 epoch，全部失效。
    #[inline]
    pub(super) fn reset(&mut self) {
        self.epoch += 1;
    }
    /// `NONE_MARK` 视同缺项（非线性变量不在 renaming 里）。
    #[inline]
    fn get(&self, x: usize) -> Option<u32> {
        match self.stamp.get(x).copied() {
            Some(g) if g == self.epoch => {
                let v = self.val[x];
                if v == NONE_MARK {
                    None
                } else {
                    Some(v)
                }
            }
            _ => None,
        }
    }
    /// 本代里 `x` 是否已标非线性哨兵。
    #[inline]
    fn has_mark(&self, x: usize) -> bool {
        self.stamp.get(x).copied() == Some(self.epoch) && self.val[x] == NONE_MARK
    }
    #[inline]
    fn set(&mut self, x: usize, v: u32) {
        if x >= self.val.len() {
            self.val.resize(x + 1, 0);
            self.stamp.resize(x + 1, 0); // 0 != epoch（epoch 从 1 起）
        }
        self.val[x] = v;
        self.stamp[x] = self.epoch;
    }
    /// 整表逐代克隆（卡住 match 分支体的嵌套 renaming 用——参考版按分支
    /// clone 整个 HashMap 的对应物；克隆保持同代，lift 只写进克隆）。
    /// 只克隆到本代有效高水位（stamp==epoch 的最高槽）：容量只增不减，
    /// 整表克隆会背上历史最高 level 的死重；水位之上的条目本代无效，
    /// `get` 视同缺项，语义不变。
    fn clone_valid(&self) -> RenBuf {
        // 自尾回看取高水位：本代最后写入的槽通常就在尾部，几步即命中
        let end = self
            .stamp
            .iter()
            .rposition(|&g| g == self.epoch)
            .map_or(0, |i| i + 1);
        RenBuf {
            val: self.val[..end].to_vec(),
            stamp: self.stamp[..end].to_vec(),
            epoch: self.epoch,
        }
    }
}

/// 上游 `invert`：实参（应用序）逐个 force 成**裸刚性变量**。非线性
/// （重复变量）移出 renaming、记 `NONE_MARK`，产出把重复变量的全部出现
/// 记为 `None` 的掩码（**与 args 逆序 = 应用序**：最外层实参的槽在前；
/// 消费端 [`prune_ty_bump`] rev 迭代配对 Π 层）；线性时返回空 vec。非变量
/// 实参（字面量 / 带链变量 / Match）即失败（`None`）。
/// **L09 参考版无 gamma 上界检查**——全局层级（越过哨兵）同样进映射
/// （忠实移植，含其后果）。
#[allow(clippy::too_many_arguments)]
pub(super) fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    let _ = bump;
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）
        let f = force(bump, spine, defs, metas, decl, mutable, a);
        if v_tag(f) != 0 {
            return None;
        }
        let x = v_lvl_of(f);
        let i = lvs.len() as u32;
        lvs.push(x);
        match ren.get(x as usize) {
            // 已标非线性哨兵：保持 NONE_MARK 不动（第 3+ 次出现不覆盖）
            None if ren.has_mark(x as usize) => {}
            None => ren.set(x as usize, i),
            Some(_) => {
                ren.set(x as usize, NONE_MARK);
                nonlinear = true;
            }
        }
    }
    if !nonlinear {
        return Some(Vec::new());
    }
    // 掩码：内先序（mask[0] ↔ 最内层实参，与 prune_ty_bump 的
    // mask_inner_first 契约一致——后者 .rev() 后外→内配对 Π 层）；重复变量
    // 整级剪除
    let mut mask: Vec<Option<Icit>> = Vec::with_capacity(args.len());
    for k in 0..args.len() {
        // args[k] 内先 ↔ 应用序 n-1-k ↔ lvs[n-1-k]
        let x = lvs[args.len() - 1 - k] as usize;
        mask.push(match ren.get(x) {
            Some(_) => Some(args[k].1),
            None => None, // 非线性或从未映射 → 剪
        });
    }
    Some(mask)
}

/// solve 的三态结果（参考版 `Result<(), UnifyError>` 的压扁）：`Ok` = 解
/// 写入；`Stuck` = 反演失败（spine 含未解 meta 等）且常数解 fallback 也
/// 不适用——调用方（solve_flex_side）挂账约束后视为成功；`Fail` = 硬失败
/// （occurs/scope/剪枝不可行）。
pub(super) enum SolveRes {
    Ok,
    Stuck,
    Fail,
}

/// `Γ ⊢ ?m args ≡ rhs` 的求解（invert 已做）：非线性掩码先验证剪枝可行性，
/// 再 rename（occurs/scope check 在内），λ 包裹取自 **meta 类型**，空环境
/// 求值写表。失败即不改 metacontext。
#[allow(clippy::too_many_arguments)]
pub(super) fn solve_with_pren_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    m: u32,
    dom: u32,
    gamma: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> SolveRes {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(v, ..) => *v,
        _ => unreachable!(), // 只对未解 meta 求解
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &mask, mty)
            .is_none()
    {
        return SolveRes::Fail;
    }
    let Some(tm) = rename_iter(
        bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, Some(m), dom, gamma, rhs,
    ) else {
        return SolveRes::Fail;
    };
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, dom, mty, tm,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
    );
    journal_meta(metas, m as usize, MetaEntry::Solved(sol, mty));
    SolveRes::Ok
}

/// solve = invert + solve_with_pren；invert 失败时走 **non-invertible
/// 常数解 fallback**（参考版 L13 `solve` 的 Stuck 分支）：rhs 对空 renaming
/// 可 rename（即闭于上下文变量与 spine 作用域 meta）时，解是 meta 上下文
/// 上的常值函数——λ 层数取 `min(spine 长度, meta 类型 Π 链长)`（病态程序
/// 的 spine 可能超长，lams 对超出会 panic）。fallback 也不行 → Stuck。
#[allow(clippy::too_many_arguments)]
pub(super) fn solve_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> SolveRes {
    // tick 补点：元变量求解器（solve/prune 族）此前零 tick，而它是 force 的
    // 主要调用方之一——2026-09-23 的 tag-7 归因里，未打点的 force 调用方是
    // 最后一批候选。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    match invert_bump(bump, spine, defs, metas, decl, mutable, ren, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, m, args.len() as u32,
            gamma, mask, rhs,
        ),
        None => {
            // 常数解 fallback：空 renaming rename rhs
            let Some(renamed) = rename_iter(
                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, None, 0, gamma,
                rhs,
            ) else {
                return SolveRes::Stuck;
            };
            let mty = match &metas[m as usize] {
                MetaEntry::Unsolved(v, ..) => *v,
                _ => unreachable!(),
            };
            // meta 类型的前缀 Π 链长（逐步应用到 vvar）
            let mut pi_len = 0u32;
            let mut cur = force(bump, spine, defs, metas, decl, mutable, mty);
            while v_tag(cur) == 4 {
                let cell = v_pi_of(cur);
                let env = env_ext(bump, cell.env, v_lvl(pi_len));
                cur = eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, cell.body);
                pi_len += 1;
            }
            let dom = (args.len() as u32).min(pi_len);
            let lam_tm = lams_from_ty(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, dom, mty, renamed,
            );
            let sol = eval_iter(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
            );
            journal_meta(metas, m as usize, MetaEntry::Solved(sol, mty));
            SolveRes::Ok
        }
    }
}

/// rename 任务。icit 记账同 L04/L05：**只有刚性 `spine_case` 预装载**
/// `done_icits`（按收集序入栈）；flex 链走 `prune_vflex`（自持 fold，
/// 不碰 icit 栈）。
enum RJob<'a> {
    /// 引一个值到解域（产生一个 Tm 到 done）。
    Ren { dom: u32, cod: u32, v: V },
    /// 实参（逆应用序）已由其上任务引完，头是 head_tm，折叠 App
    /// （每个 App 的 icit 从平行 done_icits 栈取）。
    SpineFold {
        head_tm: &'a Tm<'a>,
        n: u32,
    },
    /// done 栈顶是体，包 Lam（icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合 Pi（icit 随 PiCell 携带）。
    Pi2(&'a PiCell<'a>),
}

/// partial renaming 的迭代版（L06 版 + L09 增量：tag 0 的大下标直通、
/// tag 3 带层级、无 Decl 头、Prim 无名；Match 的分支体在"捕获 env + fresh
/// rigid 槽"下用**中性 global 视图**重求值，再在**独立克隆的 renaming**
/// （lift 过 count 次）下 rename——参考版按分支 clone 整个 HashMap，这里
/// 逐代克隆 RenBuf）。
#[allow(clippy::too_many_arguments)]
pub(super) fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    occ: Option<u32>,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
    // tick 补点：rename 任务栈（同 solve/prune 族，force 的主要调用方）。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    let mut tasks: Vec<RJob<'a>> = vec![RJob::Ren {
        dom: dom0,
        cod: cod0,
        v: v0,
    }];
    let mut done: Vec<&'a Tm<'a>> = Vec::new();
    // SpineFold 的实参 icit 预装载栈
    let mut done_icits: Vec<Icit> = Vec::new();
    // 实参收集 / 折叠草稿：跨任务复用（clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    let mut popped: Vec<&'a Tm<'a>> = Vec::new();
    macro_rules! spine_case {
        ($dom:expr, $cod:expr, $h:expr, $head_tm:expr, $tasks:expr) => {{
            args.clear();
            spine.collect_args($h, &mut args);
            $tasks.push(RJob::SpineFold {
                head_tm: $head_tm,
                n: args.len() as u32,
            });
            for &(_, i) in args.iter() {
                done_icits.push(i);
            }
            for &(a, _) in args.iter() {
                $tasks.push(RJob::Ren {
                    dom: $dom,
                    cod: $cod,
                    v: a,
                });
            }
        }};
    }
    while let Some(job) = tasks.pop() {
        match job {
            RJob::Ren { dom, cod, v } => {
                let v = force(bump, spine, defs, metas, decl, mutable, v);
                match v_tag(v) {
                    5 => {
                        let m = v_meta_of(v);
                        if occ == Some(m) {
                            return None; // occurs check
                        }
                        done.push(bump.alloc(Tm::Meta(m)));
                    }
                    0 => {
                        let x = v_lvl_of(v) as usize;
                        // scope check（x 不在 spine 映射里；非线性哨兵也算缺项）。
                        // 全局层级没有逃逸通道——ren miss 即 Err（参考版
                        // rename 的 Rigid 臂同款）。
                        let Some(xp) = ren.get(x) else {
                            return None;
                        };
                        done.push(bump.alloc(Tm::Var(dom - xp - 1)));
                    }
                    2 => {
                        let h = v_spine_of(v);
                        let hd = spine.spine_head(h);
                        match v_tag(hd) {
                            5 => {
                                // flex 链：pruneVFlex（occ 检查在内部先行）
                                let m = v_meta_of(hd);
                                if occ == Some(m) {
                                    return None; // occurs check
                                }
                                let t = prune_vflex_bump(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, m, h,
                                )?;
                                done.push(t);
                            }
                            // 卡住投影/卡住声明头的链：rename 内层再以 Tm::Obj / Tm::Decl 为头
                            // 节点折叠实参（参考版 rename 的 Obj/Decl 臂同款）
                            7 => {
                                let head_tm: &'a Tm<'a> = bump.alloc(match v_xcell_of(hd) {
                                    XCell::Obj { val, name } => {
                                        let inner = rename_iter(
                                            bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, occ, dom, cod, *val,
                                        )?;
                                        Tm::Obj(inner, name)
                                    }
                                    XCell::Decl { name } => Tm::Decl(name),
                                    XCell::Lit(s) => Tm::LiteralIntro(s),
                                    _ => return None,
                                });
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                            _ => {
                                let x = v_lvl_of(hd) as usize;
                                let Some(xp) = ren.get(x) else {
                                    return None; // scope check
                                };
                                let head_tm = bump.alloc(Tm::Var(dom - xp - 1));
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                        }
                    }
                    1 => {
                        let c = v_clo_of(v);
                        let bv = {
                            let env = env_ext(bump, c.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body,
                            )
                        };
                        // lift：binder 槽 (cod → dom)
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Lam1(c.name, c.icit));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                    }
                    4 => {
                        let cell = v_pi_of(v);
                        let bv = {
                            let env = env_ext(bump, cell.env, v_lvl(cod));
                            eval_iter(
                                bump, spine, work, vals, icits, defs, metas, decl, mutable, env, cell.body,
                            )
                        };
                        // lift（同 Lam）
                        ren.set(cod as usize, dom);
                        tasks.push(RJob::Pi2(cell));
                        tasks.push(RJob::Ren {
                            dom: dom + 1,
                            cod: cod + 1,
                            v: bv,
                        });
                        tasks.push(RJob::Ren {
                            dom,
                            cod,
                            v: cell.dom,
                        });
                    }
                    3 => done.push(bump.alloc(Tm::U(v_u_of(v)))),
                    // 字面量类型与裸单元（Lit / Prim 空链）直出
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        // 卡住声明引用：原样产出 `Tm::Decl`（参考版 quote
                        // 的 Decl 臂；spine 在 tag 2 头分派处走 ChainRun）
                        XCell::Decl { name } => done.push(bump.alloc(Tm::Decl(name))),
                        XCell::Nat(k) => {
                            // 原生 Nat：闭 Nat 无变量可 rename；按 quote_nat
                            // 同构展开（Nat 类型项查 decl["Nat"] 登记值并
                            // quote，缺失回退 U(0)——参考版 rename 的 Nat 臂）
                            let nat_ty =
                                decl.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                            let nat_tm = quote_iter(
                                bump,
                                spine,
                                &mut Vec::new(),
                                &mut Vec::new(),
                                work,
                                vals,
                                icits,
                                defs,
                                metas,
                                decl,
                                mutable,
                                dom,
                                nat_ty,
                                None,
                            );
                            done.push(quote_nat_chain(bump, nat_tm, *k));
                        }
                        XCell::Obj { val, name } => {
                            // 卡住投影：rename 内层 → 包 Tm::Obj（空实参；
                            // 带实参的链在 tag 2 臂处理）
                            let inner = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *val,
                            )?;
                            done.push(bump.alloc(Tm::Obj(inner, name)));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                            is_trait,
                        } => {
                            let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                            for p in params.iter() {
                                let pv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, p.val,
                                )?;
                                let pt = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, p.ty,
                                )?;
                                ps.push(SumParamT {
                                    name: p.name,
                                    val: pv,
                                    ty: pt,
                                    icit: p.icit,
                                });
                            }
                            done.push(bump.alloc(Tm::Sum(
                                name,
                                bump.alloc_slice_fill_iter(ps),
                                cases,
                                *is_trait,
                            )));
                        }
                        XCell::SumCase {
                            typ,
                            index,
                            datas,
                            is_trait,
                        } => {
                            let tt = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *typ,
                            )?;
                            let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                            for d in datas.iter() {
                                let dv = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                    occ, dom, cod, d.val,
                                )?;
                                ds.push(SumDataT {
                                    name: d.name,
                                    val: dv,
                                    icit: d.icit,
                                });
                            }
                            done.push(bump.alloc(Tm::SumCase {
                                typ: tt,
                                index: *index,
                                datas: bump.alloc_slice_fill_iter(ds),
                                is_trait: *is_trait,
                            }));
                        }
                        XCell::Call { name, args, body } => {
                            // 内联调用：实参逐个 rename（icit 随行）+ 体 rename
                            //（参考版 rename 的 Call 臂）
                            let mut argv: Vec<(&'a Tm<'a>, Icit)> =
                                Vec::with_capacity(args.len());
                            for &(a, i) in args.iter() {
                                let at = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decl,
                                    mutable, occ, dom, cod, a,
                                )?;
                                argv.push((at, i));
                            }
                            let bt = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *body,
                            )?;
                            done.push(bump.alloc(Tm::Call(
                                name,
                                bump.alloc_slice_copy(&argv),
                                bt,
                            )));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                        } => {
                            // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"
                            // 下用 **declb 存根表**重新求值（防重展开），再在
                            // lift 过的独立 renaming 下用**真实表** rename
                            // （参考版 rename 的 Match 臂同款分工）
                            let declb = declb_of(bump, decl);
                            let val_tm = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable,
                                occ, dom, cod, *scrutinee,
                            )?;
                            let mut nc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (pat, tm) in cases.iter() {
                                let count = pat.bind_count();
                                let mut ren2 = ren.clone_valid();
                                let mut env2 = *menv;
                                let (mut d2, mut c2) = (dom, cod);
                                for _ in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(c2));
                                    ren2.set(c2 as usize, d2);
                                    d2 += 1;
                                    c2 += 1;
                                }
                                let bv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, &declb, mutable,
                                    env2, tm,
                                );
                                let bt = rename_iter(
                                    bump, spine, work, vals, icits, defs, &mut ren2, metas, decl, mutable, occ, d2, c2, bv,
                                )?;
                                nc.push(((*pat).clone(), bt));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(nc);
                            done.push(bump.alloc(Tm::Match(val_tm, cs)));
                        }
                    },
                    _ => return None, // 病态（Π/U/字面量被应用等）
                }
            }
            RJob::SpineFold { head_tm, n } => {
                popped.clear();
                for _ in 0..n {
                    let t = done.pop()?;
                    popped.push(t);
                }
                let mut t = head_tm;
                for k in 0..n as usize {
                    let i = done_icits.pop()?;
                    let a = popped[n as usize - 1 - k];
                    t = bump.alloc(Tm::App(t, a, i));
                }
                done.push(t);
            }
            RJob::Lam1(name, icit) => {
                let body = done.pop()?; // 栈约定：子任务必已完成
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            RJob::Pi2(cell) => {
                let cod = done.pop()?;
                let dom = done.pop()?;
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
        }
    }
    debug_assert_eq!(done_icits.len(), 0, "icit 预装载必须全部配对弹出");
    done.pop()
}

/// `pruneVFlex` 的 spine 状态（参考版 `SpinePruneStatus` 同构）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

/// `pruneVFlex`：meta + 纯变量 renaming 判定与剪枝（L06 版原样；非变量
/// 实参——含字面量/Obj/构造子值——嵌套 rename，与参考版 prune_vflex_go 的
/// 非 Rigid 臂一致；实参探测用全量 force）。
#[allow(clippy::too_many_arguments)]
fn prune_vflex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    occ: Option<u32>,
    dom: u32,
    cod: u32,
    m: u32,
    h: usize,
) -> Option<&'a Tm<'a>> {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args); // 内先序
    let mut slots: Vec<(Option<&'a Tm<'a>>, Icit)> = Vec::with_capacity(args.len());
    let mut status = SpinePruneStatus::OKRenaming;
    for &(a, i) in args.iter().rev() {
        // 应用序（外先）
        let f = force(bump, spine, defs, metas, decl, mutable, a);
        if v_tag(f) == 0 {
            match ren.get(v_lvl_of(f) as usize) {
                Some(xp) => slots.push((Some(bump.alloc(Tm::Var(dom - xp - 1))), i)),
                None if status == SpinePruneStatus::OKNonRenaming => return None,
                None => {
                    slots.push((None, i));
                    status = SpinePruneStatus::NeedsPruning;
                }
            }
        } else {
            if status == SpinePruneStatus::NeedsPruning {
                return None; // 上游：剪枝后 spine 必须全变量
            }
            let t = rename_iter(
                bump, spine, work, vals, icits, defs, ren, metas, decl, mutable, occ, dom, cod, f,
            )?;
            slots.push((Some(t), i));
            status = SpinePruneStatus::OKNonRenaming;
        }
    }
    let m_prime = if status == SpinePruneStatus::NeedsPruning {
        // 掩码内先序 = slots 反序
        let mut mask: Vec<Option<Icit>> = Vec::with_capacity(slots.len());
        for (st, i) in slots.iter().rev() {
            mask.push(if st.is_some() { Some(*i) } else { None });
        }
        prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &mask, m)?
    } else {
        m
    };
    // 折叠：上游 foldr = 最外层实参先应用（外先迭代，内层包在最外）
    let mut t: &'a Tm<'a> = bump.alloc(Tm::Meta(m_prime));
    for (st, i) in slots {
        if let Some(u) = st {
            t = bump.alloc(Tm::App(t, u, i));
        }
    }
    Some(t)
}

/// `pruneMeta`：检查剪后类型良型、造新 meta（类型 = 剪后值），旧 meta 解为
/// `λ telescope. AppPruning ?m' pruned`。掩码内先序（同 cxt 惯例）。
#[allow(clippy::too_many_arguments)]
pub(super) fn prune_meta_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    // tick 补点：剪枝（同 solve 族）。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    let (mty, origin) = match &metas[m as usize] {
        MetaEntry::Unsolved(v, _, o, _) => (*v, *o),
        _ => unreachable!(), // 只对未解 meta 剪枝
    };
    let pruned_tm = prune_ty_bump(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, mask, mty,
    )?;
    let prunedty = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, pruned_tm,
    );
    let mp = metas.len() as u32;
    // 参考版：new_meta(prunedty, 空 Cxt（只塞 decl）, origin_ty)
    let snap: Rc<MetaSnap<'static>> = unsafe {
        std::mem::transmute(Rc::new(MetaSnap {
            lvl: 0,
            types: None,
            decls: Rc::new(decl.clone()),
            cxt: std::mem::transmute::<Cxt<'_>, Cxt<'static>>(Cxt::empty()),
        }))
    };
    metas.push(MetaEntry::Unsolved(prunedty, snap, origin, empty_span(())));
    // AppPruning 项：掩码外先入链（新槽恒链头 → 最终头 = 最内层）
    let mut pr: Option<&'a PrCons<'a>> = None;
    for slot in mask.iter().rev() {
        pr = Some(bump.alloc(PrCons::new(*slot, pr)));
    }
    let ap = bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(mp)), pr));
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, decl, mutable, EMPTY_ENV, lam_tm,
    );
    journal_meta(metas, m as usize, MetaEntry::Solved(sol, mty));
    Some(mp)
}

/// `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层。自带换代缓冲。
#[allow(clippy::too_many_arguments)]
pub(super) fn prune_ty_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(bump, spine, defs, metas, decl, mutable, mty);
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, decl, mutable, None, dom,
                cod, pdom,
            )?;
            // lift：binder 进映射
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
            bump, spine, work, vals, icits, defs, metas, decl, mutable,
            env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(bump, spine, defs, metas, decl, mutable, next);
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, decl, mutable, None, dom, cod,
        cur,
    )?;
    // 保留层由内向外回包（layers 序 = 外→内，rev = 内→外 ✓）
    for (name, icit, dtm) in layers.iter().rev() {
        t = bump.alloc(Tm::Pi(name, *icit, dtm, t));
    }
    Some(t)
}

/// `String`（solve/prune 密集负载下 `lams_from_ty` 每 λ 层都要一个）。
/// （五方同款样板（L03-L10 twin，a806ff0 家族）；本层为继承连贯性轮补齐。）
fn alloc_xname<'a>(bump: &'a Bump, n: u32) -> &'a str {
    let mut buf = [0u8; 11]; // 'x' + u32 十进制最多 10 位
    let mut i = buf.len();
    let mut v = n;
    loop {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }
    i -= 1;
    buf[i] = b'x';
    bump.alloc_str(std::str::from_utf8(&buf[i..]).unwrap()) // ASCII 恒有效
}

/// `lams l a t`：沿 **meta 类型**的 Π 层包 λ（名字与 icit 随 Π，`"_"` 改名
/// `x{l'}`；逐层用 `VVar l'` 剥闭包）。
#[allow(clippy::too_many_arguments)]
pub(super) fn lams_from_ty<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(bump, spine, defs, metas, decl, mutable, ty);
    for lp in 0..l {
        if v_tag(cur) != 4 {
            unreachable!(); // 类型 Π 层数不足（上游同款不可能）
        }
        let p = v_pi_of(cur);
        let (name, icit, env, body_tm) = (p.name, p.icit, p.env, p.body);
        let name = if name == "_" {
            alloc_xname(bump, lp)
        } else {
            name
        };
        names.push((name, icit));
        let next = eval_iter(
            bump, spine, work, vals, icits, defs, metas, decl, mutable,
            env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(bump, spine, defs, metas, decl, mutable, next);
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}
