//! rename：solve 族全迭代——`RenBuf` 换代缓冲、`invert_bump`/
//! `solve_with_pren_bump`/`solve_bump`、`RJob`/`rename_iter`、
//! `prune_vflex_bump`/`prune_meta_bump`/`prune_ty_bump`、`lams_from_ty`。
//! 原 bump_spine_iter.rs 的 "solve" 节，逐行搬运（2026-09-19 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{env_ext, EMPTY_ENV, PiCell};
use super::eval::{eval_iter, W};
use super::force::{force, force_arg};
use super::prim::{DeclEntryF, Fuel, MutableMap};
use super::spine::{MetaEntry, Spine};
use super::subst::simpl_decl;
use super::syntax::{
    pending_to_vec, PrCons, SumDataT, SumParamT, Tm, V, XCell, v_clo_of, v_lvl, v_lvl_of,
    v_meta_of, v_pi_of, v_spine_of, v_tag, v_xcell_of,
};

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
    fn reset(&mut self) {
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

/// 上游 `invert`：实参（应用序）逐个 force_arg 成**裸刚性变量**。非线性
/// （重复变量）移出 renaming、记 `NONE_MARK`，产出把重复变量的全部出现
/// 记为 `None` 的掩码（**与 args 逆序 = 应用序**：最外层实参的槽在前；
/// 消费端 [`prune_ty_bump`] rev 迭代配对 Π 层）；线性时返回空 vec。非变量
/// 实参（字面量 / Decl / 带链变量 / Match）即失败（`None`）。槽位探测用
/// `force_arg`（不展开 pm 精化 / 不重选 Match——参考版 `invert_go` 同款）。
#[allow(clippy::too_many_arguments)]
pub(super) fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    ren: &mut RenBuf,
    gamma: u32,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）
        let f = force_arg(bump, spine, defs, metas, decls, mmap, fuel, a);
        if v_tag(f) != 0 {
            return None;
        }
        let x = v_lvl_of(f);
        if x >= gamma {
            return None;
        }
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
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    dom: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> bool {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        // force 在 fuel 耗尽时会把已解 meta 当未解返回（拒绝展开），随后
        // 走到的求解按合一失败降级，不 panic——与"fuel 耗尽按未解失败"的
        // 既有降级故事一致（窗口：恰在 1→0 递减帧内）
        _ => return false,
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    if !mask.is_empty()
        && prune_ty_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, &mask, mty,
        )
        .is_none()
    {
        return false;
    }
    let Some(tm) = rename_iter(
        bump, spine, work, vals, icits, defs, ren, metas, decls, mmap, fuel, Some(m),
        dom, gamma, rhs,
    ) else {
        return false;
    };
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, dom, mty, tm,
    );
    let sol = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, EMPTY_ENV,
        lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    true
}

/// solve = invert + solve_with_pren。
#[allow(clippy::too_many_arguments)]
pub(super) fn solve_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> bool {
    match invert_bump(bump, spine, defs, metas, decls, mmap, fuel, ren, gamma, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, ren, gamma,
            m, args.len() as u32, mask, rhs,
        ),
        None => false,
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
    // ---- 深链收集任务（README §7.6，2026-09-18）----
    /// done 栈顶 1 个 = 内层；包 Tm::Obj（裸 Obj，空实参）。
    ObjWrap { name: &'a str },
    /// done 栈顶 n 个实参（应用序，icit 从平行 done_icits 弹）+ 其下 1 个
    /// inner；折 Obj 头 + App 链（序与 SpineFold 同构）。
    ObjSpineFold { name: &'a str, n: u32 },
    /// done 栈顶 2n（底→顶 = v0,t0,v1,t1…）；合 Tm::Sum。
    SumBuild {
        name: &'a str,
        cases: &'a [&'a str],
        metas: Vec<(&'a str, Icit)>,
    },
    /// done 栈顶 n（底→顶 = d0…dn）+ 其下 1 个 typ；合 Tm::SumCase。
    SumCaseBuild {
        case_name: &'a str,
        datas_metas: Vec<(&'a str, Icit)>,
    },
}

/// partial renaming 的迭代版（L06 版 + L07 增量：Prim/Obj/Sum/SumCase/
/// Match 的 rename 臂。Match 的分支体在"捕获 env + fresh rigid 槽"下用
/// **简化 decl 表**重求值，再在**独立克隆的 renaming**（lift 过 count 次）
/// 下 rename——参考版按分支 clone 整个 HashMap，这里逐代克隆 RenBuf）。
#[allow(clippy::too_many_arguments)]
fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut RenBuf,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    occ: Option<u32>,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
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
                let v = force(
                bump, spine, defs, metas, decls, mmap, fuel, v,
                );
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
                        // scope check（x 不在 spine 映射里；非线性哨兵也算缺项）
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
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, occ, dom, cod, m, h,
                                )?;
                                done.push(t);
                            }
                            // Decl / Prim 头的链照参考版 rename_sp 重建 App 链
                            // （头名直出，实参逐个 rename）；Obj 头的链先
                            // rename 内层再以 Tm::Obj 为头节点折叠实参——
                            // 内层任务化（README §7.6）：头链内层是深值时
                            // 不再按值深度递归
                            7 => match v_xcell_of(hd) {
                                XCell::Decl(s) => {
                                    let head_tm: &'a Tm<'a> = bump.alloc(Tm::Decl(s));
                                    spine_case!(dom, cod, h, head_tm, tasks);
                                }
                                XCell::Prim(s) => {
                                    let head_tm: &'a Tm<'a> = bump.alloc(Tm::Prim(s));
                                    spine_case!(dom, cod, h, head_tm, tasks);
                                }
                                XCell::Obj { val, name } => {
                                    // 与 spine_case 同款：icit 预装 + 实参任务；
                                    // inner 最后压 = 最先执行，ObjSpineFold 收口
                                    args.clear();
                                    spine.collect_args(h, &mut args);
                                    tasks.push(RJob::ObjSpineFold {
                                        name,
                                        n: args.len() as u32,
                                    });
                                    for &(_, i) in args.iter() {
                                        done_icits.push(i);
                                    }
                                    for &(a, _) in args.iter() {
                                        tasks.push(RJob::Ren {
                                            dom,
                                            cod,
                                            v: a,
                                        });
                                    }
                                    tasks.push(RJob::Ren { dom, cod, v: *val });
                                }
                                XCell::Lit(s) => {
                                    let head_tm: &'a Tm<'a> = bump.alloc(Tm::LiteralIntro(s));
                                    spine_case!(dom, cod, h, head_tm, tasks);
                                }
                                _ => return None,
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
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                                env, c.body,
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
                                bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                                env, cell.body,
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
                    3 => done.push(bump.alloc(Tm::U)),
                    // 字面量类型与裸单元（Lit / Decl / Prim 空链）直出
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        // 不变式：force 的返回值顶层不会是 VSub（入口已推开；
                        // fuel 耗尽的角落按失败处理，参考版 rename 同款）
                        XCell::VSub { .. } => return None,
                        XCell::Decl(s) => done.push(bump.alloc(Tm::Decl(s))),
                        XCell::Prim(s) => done.push(bump.alloc(Tm::Prim(s))),
                        XCell::Obj { val, name } => {
                            // 卡住投影：rename 内层 → 包 Tm::Obj（空实参；
                            // 带实参的链在 tag 2 臂处理）。内层任务化
                            // （README §7.6）
                            tasks.push(RJob::ObjWrap { name });
                            tasks.push(RJob::Ren { dom, cod, v: *val });
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                        } => {
                            // 参数任务化（README §7.6）：done 底→顶 =
                            // v0,t0,v1,t1…（执行序同旧递归），SumBuild 收口
                            let metas: Vec<(&'a str, Icit)> =
                                params.iter().map(|p| (p.name, p.icit)).collect();
                            tasks.push(RJob::SumBuild { name, cases, metas });
                            for p in params.iter().rev() {
                                tasks.push(RJob::Ren { dom, cod, v: p.ty });
                                tasks.push(RJob::Ren { dom, cod, v: p.val });
                            }
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                        } => {
                            // 字段任务化（README §7.6）：done 底→顶 =
                            // typ,d0…dn（执行序同旧递归），SumCaseBuild 收口
                            let datas_metas: Vec<(&'a str, Icit)> =
                                datas.iter().map(|d| (d.name, d.icit)).collect();
                            tasks.push(RJob::SumCaseBuild {
                                case_name,
                                datas_metas,
                            });
                            for d in datas.iter().rev() {
                                tasks.push(RJob::Ren { dom, cod, v: d.val });
                            }
                            tasks.push(RJob::Ren { dom, cod, v: *typ });
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                            pending,
                        } => {
                            // 分支体是裸 Tm：先在"捕获 env + fresh rigid 槽"
                            // 下重新求值（简化 decl 表防重展开），再在 lift
                            // 过的独立 renaming 下 rename（参考版 rename 的
                            // Match 臂同款；scrutinee 与 pending 用真实表）
                            let val_tm = rename_iter(
                                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap,
                                fuel, occ, dom, cod, *scrutinee,
                            )?;
                            let declb = simpl_decl(bump, decls);
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
                                    bump, spine, work, vals, icits, defs, metas, &declb, mmap,
                                    fuel, env2, tm,
                                );
                                let bt = rename_iter(
                                    bump, spine, work, vals, icits, defs, &mut ren2, metas,
                                    &declb, mmap, fuel, occ, d2, c2, bv,
                                )?;
                                nc.push(((*pat).clone(), bt));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(nc);
                            let mut acc: &'a Tm<'a> = bump.alloc(Tm::Match(val_tm, cs));
                            // 卡住期累积的实参：同 quote，包在 Match 外的
                            // App 链里（应用序；cons 链恢复序后逐个 rename）
                            let pv = pending_to_vec(*pending);
                            for &(uu, ii) in &pv {
                                let ut = rename_iter(
                                    bump, spine, work, vals, icits, defs, ren, metas, decls,
                                    mmap, fuel, occ, dom, cod, uu,
                                )?;
                                acc = bump.alloc(Tm::App(acc, ut, ii));
                            }
                            done.push(acc);
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
            RJob::ObjWrap { name } => {
                let inner = done.pop()?;
                done.push(bump.alloc(Tm::Obj(inner, name)));
            }
            RJob::ObjSpineFold { name, n } => {
                // 与 SpineFold 同构：实参 pop 序 = 应用序逆置，icit 平行配对
                popped.clear();
                for _ in 0..n {
                    let t = done.pop()?;
                    popped.push(t);
                }
                let inner = done.pop()?;
                let mut t = bump.alloc(Tm::Obj(inner, name));
                for k in 0..n as usize {
                    let i = done_icits.pop()?;
                    let a = popped[n as usize - 1 - k];
                    t = bump.alloc(Tm::App(t, a, i));
                }
                done.push(t);
            }
            RJob::SumBuild { name, cases, metas } => {
                let n = metas.len();
                popped.clear();
                for _ in 0..n * 2 {
                    let t = done.pop()?;
                    popped.push(t);
                }
                // popped（顶→底）= t(n-1),v(n-1)…t0,v0：参数 k 的
                // v_k = popped[2(n-1-k)+1]、t_k = popped[2(n-1-k)]
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(n);
                for (k, (pname, i)) in metas.into_iter().enumerate() {
                    let base = 2 * (n - 1 - k);
                    ps.push(SumParamT {
                        name: pname,
                        val: popped[base + 1],
                        ty: popped[base],
                        icit: i,
                    });
                }
                done.push(bump.alloc(Tm::Sum(
                    name,
                    bump.alloc_slice_fill_iter(ps),
                    cases,
                )));
            }
            RJob::SumCaseBuild {
                case_name,
                datas_metas,
            } => {
                let n = datas_metas.len();
                popped.clear();
                for _ in 0..n {
                    let t = done.pop()?;
                    popped.push(t);
                }
                let typ = done.pop()?;
                // popped（顶→底）= d(n-1)…d0：d_k = popped[n-1-k]
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(n);
                for (k, (dname, i)) in datas_metas.into_iter().enumerate() {
                    ds.push(SumDataT {
                        name: dname,
                        val: popped[n - 1 - k],
                        icit: i,
                    });
                }
                done.push(bump.alloc(Tm::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                }));
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
/// 实参——含字面量/Decl/Prim/Obj/构造子值——嵌套 rename，与参考版
/// prune_vflex_go 的非 Rigid 臂一致；实参探测用 `force_arg`）。
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
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
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
        let f = force_arg(
                bump, spine, defs, metas, decls, mmap, fuel, a,
        );
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
                bump, spine, work, vals, icits, defs, ren, metas, decls, mmap, fuel, occ, dom, cod, f,
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
        prune_meta_bump(
            bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, &mask, m,
        )?
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
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        // fuel 耗尽窗口（同 solve_with_pren_bump 注）：按失败降级
        _ => return None,
    };
    let pruned_tm = prune_ty_bump(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, mask, mty,
    )?;
    let prunedty = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, EMPTY_ENV,
        pruned_tm,
    );
    let mp = metas.len() as u32;
    metas.push(MetaEntry::Unsolved(prunedty));
    // AppPruning 项：掩码外先入链（新槽恒链头 → 最终头 = 最内层）
    let mut pr: Option<&'a PrCons<'a>> = None;
    for slot in mask.iter().rev() {
        pr = Some(bump.alloc(PrCons::new(*slot, pr)));
    }
    let ap = bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(mp)), pr));
    let lam_tm = lams_from_ty(
        bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, EMPTY_ENV,
        lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    Some(mp)
}

/// `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层。自带换代缓冲。
#[allow(clippy::too_many_arguments)]
fn prune_ty_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, mty,
    );
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, decls, mmap, fuel,
                None, dom, cod, pdom,
            )?;
            // lift：binder 进映射
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, next,
        );
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, decls, mmap, fuel, None,
        dom, cod, cur,
    )?;
    // 保留层由内向外回包（layers 序 = 外→内，rev = 内→外 ✓）
    for (name, icit, dtm) in layers.iter().rev() {
        t = bump.alloc(Tm::Pi(name, *icit, dtm, t));
    }
    Some(t)
}

/// `x{n}` 的 bump 拷贝：栈上格式化，省每 binder 一次 system-heap
/// `String`（solve/prune 密集负载下 `lams_from_ty` 每 λ 层都要一个）。
/// （a806ff0 的 L07 同款补齐——该 commit 只落到 L03-L05。）
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
fn lams_from_ty<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, ty,
    );
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
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel, env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(
                bump, spine, defs, metas, decls, mmap, fuel, next,
        );
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}
