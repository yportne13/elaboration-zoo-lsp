//! quote：任务栈迭代 quote（`QJob`/`quote_iter`，流式右链 + 记忆化
//! `QuoteMemo`）。原 bump_spine_iter.rs 的 "quote" 节，逐行搬运
//! （2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{Env, env_ext, PiCell};
use super::eval::{eval_iter, W};
use super::force::force;
use super::prim::{DeclEntryF, Fuel, MutableMap};
use super::spine::{MetaEntry, Spine};
use super::subst::simpl_decl;
use super::syntax::{SumDataT, SumDataV, SumParamT, SumParamV, Tm, V, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_xcell_of, XCell};

// quote（任务栈迭代 + 流式右链；flex/Decl/Prim 头共享节点 + L07 变体）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01/L04/L05/L06；quote 不产
/// `AppPruning`（项层洞形态，值层不存在）。L07 增量：`Obj1` / `SumAsm` /
/// `SumCaseAsm` 装配任务；`Match` 直接内联处理（分支体在"捕获 env + fresh
/// rigid 槽"下用**简化 decl 表**重求值再 quote——quote → eval 往返恒等；
/// pending 实参按应用序包在 Match 外）。
pub(super) enum QJob<'a> {
    /// 引一个值（先 force）。
    Q(V, u32),
    /// done 栈顶是体，包一层 Lam（名字与 icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合一个 Pi（icit 在 PiCell 里）。
    Pi1(&'a PiCell<'a>),
    /// 先 eval（引出闭包/余定义域的体）再引。
    EvalQ(&'a Tm<'a>, Env<'a>, u32),
    /// done 栈顶两个（先 f 后 a），合一个 App（icit 随任务携带）——
    /// 二叉 fallback 用。
    App1(Icit),
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(key, level)` 结果，入表后放回。
    MemoStore(u64, u32),
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同一变量 / 同一未解
    /// meta / 同一 Decl / Prim 名时用共享节点，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: u32,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Tm<'a>>,
        prev: Option<&'a Tm<'a>>,
    },
    /// done 栈顶是投影接收者的引读：包 `Tm::Obj`。
    Obj1(&'a str),
    /// done 栈顶自底向上是 (v0,t0,...)：装配 Tm::Sum（元数据取值层槽）。
    SumAsm {
        name: &'a str,
        params: &'a [SumParamV<'a>],
        cases: &'a [&'a str],
    },
    /// done 栈顶自底向上是 (typ, d0..)：装配 Tm::SumCase（元数据取值层槽）。
    SumCaseAsm {
        case_name: &'a str,
        datas: &'a [SumDataV<'a>],
    },
}

/// (值打包字, quote level) → 已引结果子树。icit 不进键：它随 `V` 指向的
/// 单元/槽位携带，同一打包字在同一 level 的 quote 产出（含 icit）唯一。
/// tag 7 的 L07 变体（Match/Sum/…）不进表：它们的引读依赖简化 decl 表与
/// 精化状态，且同指针重引同结果的场景极少（参考版无 quote 记忆化，保守
/// 起见对新增值形态保持无记忆化口径）。
pub(super) type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote（L06 版 + LiteralType/LiteralIntro/Decl/Prim/Obj/Sum/
/// SumCase/Match 臂）。
#[allow(clippy::too_many_arguments)]
pub(super) fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decls: &FxHashMap<String, DeclEntryF>,
    mmap: &MutableMap,
    fuel: &Fuel,
    level0: u32,
    v0: V,
    mut memo: Option<&mut QuoteMemo<'a>>,
) -> &'a Tm<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, level0));
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v0, level) => {
                // 先 force（metacontext / 精化在 quote 期间冻结，同键同结果）
                let v = force(
                    bump, spine, defs, metas, decls, mmap, fuel, v0,
                );
                match v_tag(v) {
                    0 => done.push(bump.alloc(Tm::Var(level - v_lvl_of(v) - 1))),
                    1 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let c = v_clo_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, c.env, v_lvl(level));
                        tasks.push(QJob::Lam1(c.name, c.icit));
                        tasks.push(QJob::EvalQ(c.body, env, level + 1));
                    }
                    5 => done.push(bump.alloc(Tm::Meta(v_meta_of(v)))),
                    3 => done.push(bump.alloc(Tm::U)),
                    // 字面量类型与字面量值（叶子，无 memo 收益）
                    6 => done.push(bump.alloc(Tm::LiteralType)),
                    7 => match v_xcell_of(v) {
                        XCell::Lit(s) => done.push(bump.alloc(Tm::LiteralIntro(s))),
                        // 正常路径 force 后顶层不会是 VSub；fuel 耗尽时
                        // force 原样返回 VSub——解包打印内层（σ 未推开，保
                        // 真度同旧版"打印未展开 rigid"），链式 VSub 由递归
                        // 消化，不会产出垃圾节点（参考版 quote 的 VSub 臂）
                        XCell::VSub { val, .. } => {
                            tasks.push(QJob::Q(*val, level));
                        }
                        XCell::Decl(s) => done.push(bump.alloc(Tm::Decl(s))),
                        XCell::Prim(s) => done.push(bump.alloc(Tm::Prim(s))),
                        XCell::Obj { val, name } => {
                            tasks.push(QJob::Obj1(name));
                            tasks.push(QJob::Q(*val, level));
                        }
                        XCell::Sum {
                            name,
                            params,
                            cases,
                        } => {
                            tasks.push(QJob::SumAsm {
                                name,
                                params,
                                cases,
                            });
                            for p in params.iter().rev() {
                                tasks.push(QJob::Q(p.ty, level));
                                tasks.push(QJob::Q(p.val, level));
                            }
                        }
                        XCell::SumCase {
                            typ,
                            case_name,
                            datas,
                        } => {
                            tasks.push(QJob::SumCaseAsm { case_name, datas });
                            for d in datas.iter().rev() {
                                tasks.push(QJob::Q(d.val, level));
                            }
                            tasks.push(QJob::Q(*typ, level));
                        }
                        XCell::Match {
                            scrutinee,
                            env: menv,
                            cases,
                            pending,
                        } => {
                            // 分支体在"捕获 env + fresh rigid 槽"下重新求值
                            // 再 quote：quote → eval 往返恒等（参考版
                            // quote 的 Match 臂）。求值与 quote 都用简化
                            // decl 表：全局值换成中性 Decl 引用，防止分支
                            // 体里的递归调用被重展开——eval 产生的中性
                            // Decl(f, spine) 若用真实表 quote，入口 force
                            // 会再展开一层，递归函数的卡住 match 直接发散。
                            let declb = simpl_decl(bump, decls);
                            let mut qc: Vec<(PatternDetail, &'a Tm<'a>)> =
                                Vec::with_capacity(cases.len());
                            for (p, b) in cases.iter() {
                                let count = p.bind_count();
                                let mut env2 = *menv;
                                for i in 0..count {
                                    env2 = env_ext(bump, env2, v_lvl(level + i));
                                }
                                let tv = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, &declb, mmap,
                                    fuel, env2, b,
                                );
                                let q = quote_iter(
                                    bump,
                                    spine,
                                    &mut Vec::new(),
                                    &mut Vec::new(),
                                    work,
                                    vals,
                                    icits,
                                    defs,
                                    metas,
                                    &declb,
                                    mmap,
                                    fuel,
                                    level + count,
                                    tv,
                                    None,
                                );
                                qc.push(((*p).clone(), q));
                            }
                            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                                bump.alloc_slice_fill_iter(qc);
                            // scrutinee 与 pending 用真实表（调用方的 l 下正确）
                            let sq = quote_iter(
                                bump,
                                spine,
                                &mut Vec::new(),
                                &mut Vec::new(),
                                work,
                                vals,
                                icits,
                                defs,
                                metas,
                                decls,
                                mmap,
                                fuel,
                                level,
                                *scrutinee,
                                None,
                            );
                            let mut acc: &'a Tm<'a> = bump.alloc(Tm::Match(sq, cs));
                            for &(u, i) in *pending {
                                let uq = quote_iter(
                                    bump,
                                    spine,
                                    &mut Vec::new(),
                                    &mut Vec::new(),
                                    work,
                                    vals,
                                    icits,
                                    defs,
                                    metas,
                                    decls,
                                    mmap,
                                    fuel,
                                    level,
                                    u,
                                    None,
                                );
                                acc = bump.alloc(Tm::App(acc, uq, i));
                            }
                            done.push(acc);
                        }
                    },
                    4 => {
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        let cell = v_pi_of(v);
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let env = env_ext(bump, cell.env, v_lvl(level));
                        tasks.push(QJob::Pi1(cell));
                        tasks.push(QJob::EvalQ(cell.body, env, level + 1));
                        tasks.push(QJob::Q(cell.dom, level));
                    }
                    _ => {
                        // spine 链（Rigid / Flex / Decl / Prim / Obj 头）
                        if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                            done.push(*t);
                            continue;
                        }
                        if memo.is_some() {
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        // 先拷出标量再继续（后续任务会 push spine，Vec 可能扩容）
                        let h = v_spine_of(v);
                        let (ea, len, base, top_icit) = {
                            let e = &spine.stack[h];
                            (e.a, e.len, e.base, e.icit)
                        };
                        if len > 1 && base as usize + len as usize - 1 == h {
                            // 连续右链：先引 base，再 ChainRun 自底向上扫
                            let f0 = spine.stack[base as usize].f;
                            let idx_node = match v_tag(f0) {
                                0 => Some(
                                    &*bump.alloc(Tm::Var(level - v_lvl_of(f0) - 1)) as &Tm<'a>,
                                ),
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0))) as &Tm<'a>),
                                // Decl / Prim 链头：共享单一名字节点
                                7 => match v_xcell_of(f0) {
                                    XCell::Decl(s) => {
                                        Some(&*bump.alloc(Tm::Decl(s)) as &Tm<'a>)
                                    }
                                    XCell::Prim(s) => {
                                        Some(&*bump.alloc(Tm::Prim(s)) as &Tm<'a>)
                                    }
                                    // Obj 头的链（内层值要按 level 引读）与
                                    // Lit 头（不可达）挂起走 Q
                                    _ => None,
                                },
                                _ => None,
                            };
                            let base_v = spine.stack[base as usize].a;
                            tasks.push(QJob::ChainRun {
                                level,
                                next: base as usize,
                                end: h,
                                f0,
                                idx_node,
                                prev: None,
                            });
                            tasks.push(QJob::Q(base_v, level));
                        } else {
                            // 函数部分可能是「陈旧应用链」：建链后其头 meta
                            // 被解成 λ（值里的位模式不随后续求解更新）。force
                            // 单独引函数部分会停在部分应用的 λ 上，照搬 App
                            // 拼接就产出 β-redex 项（参考版整值 force 经
                            // vAppSp 一路 β，永不产出）。故函数部分 force 为
                            // 闭包时，先按 β 语义应用本槽实参、再引应用结果。
                            let fval = spine.stack[h].f;
                            let ff = force(
                                bump, spine, defs, metas, decls, mmap, fuel, fval,
                            );
                            if v_tag(ff) == 1 {
                                let c = v_clo_of(ff);
                                let applied = {
                                    let env = env_ext(bump, c.env, ea);
                                    eval_iter(
                                        bump, spine, work, vals, icits, defs, metas, decls, mmap,
                                        fuel, env, c.body,
                                    )
                                };
                                tasks.push(QJob::Q(applied, level));
                            } else {
                                tasks.push(QJob::App1(top_icit));
                                tasks.push(QJob::Q(ea, level));
                                tasks.push(QJob::Q(fval, level));
                            }
                        }
                    }
                }
            }
            QJob::Lam1(name, icit) => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Tm::Lam(name, icit, body)));
            }
            QJob::Pi1(cell) => {
                let cod = done.pop().expect("quote 栈：Pi 缺余定义域");
                let dom = done.pop().expect("quote 栈：Pi 缺定义域");
                done.push(bump.alloc(Tm::Pi(cell.name, cell.icit, dom, cod)));
            }
            QJob::EvalQ(body, env, level) => {
                let v = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, decls, mmap, fuel,
                    env, body,
                );
                tasks.push(QJob::Q(v, level));
            }
            QJob::App1(icit) => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Tm::App(f, a, icit)));
            }
            QJob::MemoStore(key, level) => {
                let m = memo
                    .as_deref_mut()
                    .expect("quote 栈：MemoStore 缺 memo 表");
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                m.insert((key, level), t);
                done.push(t);
            }
            QJob::Obj1(name) => {
                let inner = done.pop().expect("quote 栈：Obj 缺接收者");
                done.push(bump.alloc(Tm::Obj(inner, name)));
            }
            QJob::SumAsm {
                name,
                params,
                cases,
            } => {
                // done 槽序 = v0, t0, v1, t1, ...（先压者在底）→ 按 params
                // 逆序逐槽收进 ps 再反转，省掉 items 中转 + 二次下标拷贝
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("quote 栈：Sum 缺参数");
                    let val = done.pop().expect("quote 栈：Sum 缺参数");
                    ps.push(SumParamT {
                        name: p.name,
                        val,
                        ty,
                        icit: p.icit,
                    });
                }
                ps.reverse();
                done.push(bump.alloc(Tm::Sum(name, bump.alloc_slice_fill_iter(ps), cases)));
            }
            QJob::SumCaseAsm { case_name, datas } => {
                // datas 字段在 done 栈顶（typ 先压在底）：逆序 pop 落槽后
                // 反转，typ 最后 pop
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("quote 栈：SumCase 缺字段");
                    ds.push(SumDataT {
                        name: d.name,
                        val,
                        icit: d.icit,
                    });
                }
                ds.reverse();
                let typ = done.pop().expect("quote 栈：SumCase 缺 typ");
                done.push(bump.alloc(Tm::SumCase {
                    typ,
                    case_name,
                    datas: bump.alloc_slice_fill_iter(ds),
                }));
            }
            QJob::ChainRun {
                level,
                next,
                end,
                f0,
                idx_node,
                prev,
            } => {
                let mut prev = match prev {
                    Some(p) => {
                        // 恢复点：非平凡 f 刚引完在 done 栈顶，合掉一层
                        // （悬挂槽位 = next-1，其 icit 即本层应用的 icit）
                        let f_node = done.pop().expect("quote 栈：链缺函数头");
                        let icit = spine.stack[next - 1].icit;
                        bump.alloc(Tm::App(f_node, p, icit))
                    }
                    None => done.pop().expect("quote 栈：链缺 base"),
                };
                let mut i = next;
                loop {
                    if i > end {
                        done.push(prev);
                        break;
                    }
                    let fi = spine.stack[i].f;
                    match idx_node {
                        Some(n) if fi.0 == f0.0 => {
                            prev = bump.alloc(Tm::App(n, prev, spine.stack[i].icit));
                            i += 1;
                        }
                        _ => {
                            // 非平凡链头：挂起引 f，ChainRun 续跑。f 可能是
                            // 「陈旧应用链」（建链后头 meta 被解成 λ）：force
                            // 单独引它停在部分应用的 λ 上，恢复点照搬 App 拼
                            // 接就产出 β-redex 项（参考版整值 force 经 vAppSp
                            // 一路 β，永不产出）。故 f force 为闭包时改为引
                            // 「f 应用本槽实参」的整值，恢复点直接取该结果为
                            // 已累计项（prev:None = 弹出为初始累计，不再拼接）。
                            let ff = force(
                                bump, spine, defs, metas, decls, mmap, fuel, fi,
                            );
                            if v_tag(ff) == 1 {
                                let arg_v = spine.stack[i].a;
                                let c = v_clo_of(ff);
                                let applied = {
                                    let env = env_ext(bump, c.env, arg_v);
                                    eval_iter(
                                        bump, spine, work, vals, icits, defs, metas, decls, mmap,
                                        fuel, env, c.body,
                                    )
                                };
                                tasks.push(QJob::ChainRun {
                                    level,
                                    next: i + 1,
                                    end,
                                    f0,
                                    idx_node,
                                    prev: None,
                                });
                                tasks.push(QJob::Q(applied, level));
                            } else {
                                tasks.push(QJob::ChainRun {
                                    level,
                                    next: i + 1,
                                    end,
                                    f0,
                                    idx_node,
                                    prev: Some(prev),
                                });
                                tasks.push(QJob::Q(fi, level));
                            }
                            break;
                        }
                    }
                }
            }
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}
