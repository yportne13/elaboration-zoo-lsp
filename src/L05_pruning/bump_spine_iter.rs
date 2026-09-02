//! L05 核心机（eval / quote / unify / force / rename / solve / prune / check /
//! infer）的极致性能版：L04 冠军配方（`bump_spine_iter`）向 pruning 层的移植。
//! 继承 L04 的全部机制（见其模块注释与 readme）：
//!
//! 1. bump arena；打包值 [`V`]（低 3 位 tag）；扁平中性 + spine 栈；
//! 2. 复合环境（平坦 def 区域 + 持久 binder 链）；
//! 3. 迭代内核：eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈 /
//!    force 循环；
//! 4. quote 记忆化（默认口径）+ unify 判等记忆化（`L05_NO_CONV_MEMO=1`
//!    消融）+ O(1) 名字解析（`L05_NO_NAME_MAP=1` 消融）；
//! 5. `Tycker` 稳态复用（跨轮 `Bump::reset`）、热路径草稿常驻、
//!    `Pruning` 跳段（none-run）、`RenBuf` 换代缓冲、fresh meta 免 eval 快捷路径。
//!
//! L05 的增量（pruning 机制的落地）：
//!
//! - **typed metas**：[`MetaEntry`] 携带类型值。[`Machine::fresh_meta`] 物化
//!   `eval [] (close_ty locals (quote lvl a))`，三级快捷：`a` 是 U/裸 meta
//!   立即数（tag 3/5）→ 直接取；`quote` 产物无自由变量 → 跳过 telescope
//!   直接 `eval [] q`（顶层 define 链的重复 eval 全部免掉）；否则照构
//!   Let/Pi 链求值（与参考版同形，O(层深)）。
//! - **PrCons 掩码**（替代 L04 的 BdCons）：槽位 `Option<Icit>`——应用实参
//!   时 icit 取自掩码（L04 硬编码 Expl 的 `AppBdsOne` 在这里变成
//!   `AppPrunOne` 带 icit）；none-run 跳段/`eval_fresh` 快捷路径原样继承。
//! - **unify 的分派升级**：同头 flex-flex 走 [`intersect_bump`]（变量对
//!   逐槽取交，差异槽剪枝；上游 `impossible` 的长度失配落地为**直接失败**
//!   ——与参考版 unify_sp 的「失配即败、零比较」同语义，不炸栈，且不会在
//!   失败前求解共同前缀里的 flex 而污染 metacontext）；异头 flex-flex 走
//!   [`flex_flex_bump`]（较长 spine 一侧优先反演，失败落另一侧）。
//! - **rename 的 flex 分支 = [`prune_vflex_bump`]**：spine 槽位是 ren 里的
//!   变量→改名保留；越界变量→记 `None` 进 NeedsPruning；非变量→嵌套
//!   rename（共享 ren/不共享任务栈）。NeedsPruning 时 [`prune_meta_bump`]
//!   造新 meta、旧 meta 解为 `λ telescope. AppPruning ?m' pruned`——
//!   [`lams_from_ty`] 沿 meta 类型的 Π 层包 λ（L04 的 spine-icit 版 lams
//!   在本层作废）。
//! - **invert 的非线性**：[`RenBuf`] 加哨兵 `NONE_MARK`（get 视其为缺项），
//!   重复变量整级剪除、产出掩码；`solve_with_pren` 先 [`prune_ty_bump`]
//!   验证剪后类型良型。`prune_ty` 按上游走 **RevPruning**（外→内配对 Π 层），
//!   嵌套 rename 自带 RenBuf（换代缓冲不能互踩）。
//!
//! 与参考版（`super`）共用 parser / pretty / 错误显示，输出逐字节一致
//! （互检测试）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::parser::{Either, Icit, Raw};
use crate::parser_lib::Span;
use super::{Error, Name, Tm as CTm, Ix, pretty_tm, report_at, show_icit};

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
/// `AppPruning` 是 L05 的洞形态：头（实践中恒为 `Meta`）+ scope 掩码。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    /// 把头按掩码应用到求值环境：`Some(icit)` 槽位以该 icit 应用实参，
    /// `None` 槽位跳过（上游 `TAppPruning` / `vAppPruning`）。
    AppPruning(&'a Tm<'a>, Option<&'a PrCons<'a>>),
    U,
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    Meta(u32),
}

/// `AppPruning` 的掩码链表（bump 持久，头 = 最内层绑定）。
pub(crate) struct PrCons<'a> {
    /// `Some(icit)` = 绑定槽位（应用实参，icit 随槽）；`None` = define 槽
    /// （跳过）。
    slot: Option<Icit>,
    /// 本节点向外（next 方向）连续 `None`（define 槽）的个数；Some 槽为 0。
    /// AppPrun 在 binds 耗尽后用它在 O(1) 内整段跳过 none-run（继承 L04 的
    /// BdCons false-run 机制，`false` ⇔ `None`）。
    none_run: u32,
    /// 本 none-run 之后的第一个槽（Some 槽或链尾）——跳段的落点。
    after_run: Option<&'a PrCons<'a>>,
    next: Option<&'a PrCons<'a>>,
}

impl<'a> PrCons<'a> {
    /// 入链构造（新槽恒为链头，最内层）。run 统计只读既有节点。
    fn new(slot: Option<Icit>, next: Option<&'a PrCons<'a>>) -> Self {
        let (none_run, after_run) = match (slot, next) {
            (Some(_), _) => (0, next),
            (None, Some(n)) if n.slot.is_none() => (n.none_run + 1, n.after_run),
            (None, _) => (1, next),
        };
        PrCons {
            slot,
            none_run,
            after_run,
            next,
        }
    }
}

/// 局部 telescope 节点（`fresh_meta` 闭类型用）：`Bind` 槽存引好的类型项，
/// `Define` 槽再存定义项（上游 `Locals` 同款，close 只搬运不重引）。
struct LCons<'a> {
    name: &'a str,
    a_t: &'a Tm<'a>,
    /// `Some` = define（闭成 Let），`None` = binder（闭成显式 Π）。
    t_t: Option<&'a Tm<'a>>,
    next: Option<&'a LCons<'a>>,
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Lvl(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U`（立即数）、`4=Pi(ptr|4)`、`5=Meta(m<<3|5)`
/// （未解 meta 立即数）。icit 不进打包字——由 Clo/Pi 单元与 spine 槽携带
/// （打包字是 quote/unify 记忆化的键，icit 随值结构唯一确定，不影响键）。
#[derive(Clone, Copy)]
pub(crate) struct V(pub(crate) u64);

#[inline]
pub(crate) fn v_lvl(level: u32) -> V {
    V(((level as u64) << 3) | 0)
}
#[inline]
pub(crate) fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}
#[inline]
pub(crate) fn v_spine(idx: usize) -> V {
    V(((idx as u64) << 3) | 2)
}
#[inline]
pub(crate) fn v_u() -> V {
    V(3)
}
#[inline]
pub(crate) fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
pub(crate) fn v_meta(m: u32) -> V {
    V(((m as u64) << 3) | 5)
}
#[inline]
pub(crate) fn v_tag(v: V) -> u64 {
    v.0 & 7
}
#[inline]
pub(crate) fn v_lvl_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
#[inline]
pub(crate) fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
pub(crate) fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
pub(crate) fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    unsafe { &*((v.0 & !7) as *const PiCell) }
}
#[inline]
pub(crate) fn v_meta_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}

/// 复合环境：**平坦 def 区域**（elaborator 的 define 链，指入每轮
/// [`Machine::defs`]；tip 环境原地追加，`nth` O(1)；**非 tip 环境**
/// （λ 体内的 define 先占位后、外层再 define）回落到 binder 链——索引
/// 语义一致，仅查链 O(链深)）+ **持久 binder 链表**。机制与论证同 L03/L04。
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    flat_base: u32,
    flat_len: u32,
    binds: Option<&'a EnvCons<'a>>,
}

const EMPTY_ENV: Env<'static> = Env {
    flat_base: 0,
    flat_len: 0,
    binds: None,
};

/// 环境链表节点（bump 内持久链表，头 = 最内层绑定）。
pub(crate) struct EnvCons<'a> {
    val: V,
    next: Option<&'a EnvCons<'a>>,
}

/// `i < binds 深度` → 走链；否则读平坦 def 区域。
#[inline]
pub(crate) fn env_nth(defs: &[V], env: Env<'_>, i: u32) -> V {
    let mut nb = env.binds;
    let mut j = 0u32;
    while let Some(e) = nb {
        if j == i {
            return e.val;
        }
        j += 1;
        nb = e.next;
    }
    defs[(env.flat_base + env.flat_len - 1 - (i - j)) as usize]
}

/// 环境扩展（**binder 链**：bind / β / 瞬时求值扩展）——O(1)。
#[inline]
pub(crate) fn env_ext<'a>(bump: &'a Bump, env: Env<'a>, v: V) -> Env<'a> {
    Env {
        flat_base: env.flat_base,
        flat_len: env.flat_len,
        binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
    }
}

/// 环境扩展（**平坦 def 区域**：elaborator 的 define）。tip 环境原地追加
/// （chain 负载的 O(1) 线性保证）；非 tip 环境回落 binder 链（L04 同款）。
#[inline]
pub(crate) fn env_ext_defs<'a>(
    bump: &'a Bump,
    defs: &mut Vec<V>,
    env: Env<'a>,
    v: V,
) -> Env<'a> {
    if env.flat_base + env.flat_len == defs.len() as u32 {
        defs.push(v);
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len + 1,
            binds: env.binds,
        }
    } else {
        Env {
            flat_base: env.flat_base,
            flat_len: env.flat_len,
            binds: Some(bump.alloc(EnvCons { val: v, next: env.binds })),
        }
    }
}

/// 闭包单元：λ 的名字 + icit（quote 产出带 icit 的 `Lam`）+ env + 体。
pub(crate) struct CloCell<'a> {
    name: &'a str,
    icit: Icit,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

/// Π 值单元：名字 + icit + 定义域值 + 余定义域闭包（内联，一次分配）。
pub(crate) struct PiCell<'a> {
    name: &'a str,
    icit: Icit,
    dom: V,
    env: Env<'a>,
    body: &'a Tm<'a>,
}

/// spine 栈槽：一次中性应用（icit 随槽携带——quote 的 `f {a}`、rename 的
/// App 重建、prune 掩码都从这里取）。`len`/`base` 支撑流式右链 quote。
struct Entry {
    f: V,
    a: V,
    icit: Icit,
    len: u32,
    base: u32,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a`（icit i）压栈，返回句柄值。
    #[inline]
    fn push(&mut self, f: V, a: V, icit: Icit) -> V {
        let idx = self.stack.len();
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry {
            f,
            a,
            icit,
            len,
            base,
        });
        v_spine(idx)
    }

    /// 沿 `f` 指针走到链的最底层头（f 指针严格指向更早的槽位，必终止）。
    #[inline]
    fn spine_head(&self, h: usize) -> V {
        let mut cur = h;
        loop {
            let f = self.stack[cur].f;
            if v_tag(f) == 2 {
                cur = v_spine_of(f);
            } else {
                return f;
            }
        }
    }

    /// 收集链的**引用语义实参**（逆应用序：先 `h.a` 再沿 `f` 下行）。
    #[inline]
    fn collect_args(&self, h: usize, out: &mut Vec<(V, Icit)>) {
        let mut cur = h;
        loop {
            let e = &self.stack[cur];
            out.push((e.a, e.icit));
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
            } else {
                return;
            }
        }
    }

    /// force 后的未解 flex 探测：`tag 5`（空 spine）或 spine 头是 `Meta`。
    /// 返回 meta 号并把逆应用序实参（带 icit）收进 `out`。要求调用方先 force。
    fn flex_of(&self, v: V, out: &mut Vec<(V, Icit)>) -> Option<u32> {
        match v_tag(v) {
            5 => Some(v_meta_of(v)),
            2 => {
                let h = v_spine_of(v);
                let hd = self.spine_head(h);
                if v_tag(hd) != 5 {
                    return None;
                }
                self.collect_args(h, out);
                Some(v_meta_of(hd))
            }
            _ => None,
        }
    }
}

// metacontext
// --------------------------------------------------------------------------------

/// metacontext 条目（与参考版同构）：**类型一律保留**（pruning 检查与
/// `lams` 都要读），解是 bump 内的打包值。
pub(crate) enum MetaEntry {
    Solved(V, V),
    Unsolved(V),
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v, _) => *v,
        MetaEntry::Unsolved(_) => v_meta(m),
    }
}

// force（迭代）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态。已解 meta 立即数 → 替换
/// 为解；已解 flex spine → 沿 f 链收集实参（带 icit）、把解按应用序应用到
/// 实参上（应用可触发 β，经 `eval_iter`），再继续。icit 沿实参原样搬运。
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    v0: V,
) -> V {
    let mut v = v0;
    // 实参缓冲跨 force 轮复用（已解 flex 链每轮收集一次；clear 保容量）
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                MetaEntry::Unsolved(_) => return v,
            },
            2 => {
                let h = v_spine_of(v);
                let hd = spine.spine_head(h);
                if v_tag(hd) != 5 {
                    return v; // 刚性链
                }
                let m = v_meta_of(hd);
                match &metas[m as usize] {
                    MetaEntry::Unsolved(_) => return v,
                    MetaEntry::Solved(sol, _) => {
                        // 把解应用到全部实参（应用序 = 收集序的逆序）；
                        // 应用可能 β（解是闭包）——cl 式 eval
                        args.clear();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &(a, i) in args.iter().rev() {
                            if v_tag(t) == 1 {
                                let c = v_clo_of(t);
                                let env = env_ext(bump, c.env, a);
                                t = eval_iter(
                                    bump, spine, work, vals, icits, defs, metas, env, c.body,
                                );
                            } else {
                                t = spine.push(t, a, i);
                            }
                        }
                        v = t;
                    }
                }
            }
            _ => return v,
        }
    }
}

// eval（双栈迭代 + 右链快速路径 + AppPruning 实参应用）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Tm<'a>, Env<'a>),
    /// 应用（icit 来自 `Tm::App`）：vals 顶两个（先函数后实参）——β 或入栈。
    Apply(Icit),
    /// vals 顶上是实参；函数值已知是闭包（β 岔路下降时已 `env_nth` 出来），
    /// 直接 β（icit 无关）。
    ApplyKnown(V),
    /// vals 顶上是 base 值，其下 `k` 个是待应用的链头（内层最上；每个链头
    /// 的 icit 在 `icits` 侧栈平行压弹）。
    ChainWrap(u32),
    /// vals 顶是 let 绑定的值：弹出压进环境，继续求值体。
    LetBody(&'a Tm<'a>, Env<'a>),
    /// vals 顶是 Π 定义域值：弹出配余定义域闭包，压 Π 值。
    PiBody(&'a str, Icit, &'a Tm<'a>, Env<'a>),
    /// vals 顶是 `vAppPruning` 的当前值；沿 (env, pr) 平行走完剩余槽位
    /// （外层先应用，icit 取自掩码；`None` 槽跳过）。
    AppPrun(Env<'a>, Option<&'a PrCons<'a>>),
    /// vals 顶是 `vAppPruning` 的当前值；本步把 `arg` 以 `icit` 应用上去
    /// （Clo → β；其它 → spine.push）。`AppPrun` 的单步实参应用。
    AppPrunOne(V, Icit),
}

/// 双栈迭代 eval（L04 版 + AppPruning：icit 取自掩码）。
#[allow(clippy::too_many_arguments)]
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    env0: Env<'a>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    icits.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => vals.push(env_nth(defs, env, *i)),
            W::Tm(Tm::Lam(name, icit, body), env) => {
                let c = bump.alloc(CloCell {
                    name,
                    icit: *icit,
                    env,
                    body,
                });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U, _) => vals.push(v_u()),
            W::Tm(Tm::Pi(name, icit, dom, cod), env) => {
                work.push(W::PiBody(name, *icit, cod, env));
                work.push(W::Tm(dom, env));
            }
            W::Tm(Tm::Let(_, _, t, u), env) => {
                work.push(W::LetBody(u, env));
                work.push(W::Tm(t, env));
            }
            W::Tm(Tm::Meta(m), _) => vals.push(meta_val_of(metas, *m)),
            W::Tm(Tm::AppPruning(head, pr), env) => {
                work.push(W::AppPrun(env, *pr));
                work.push(W::Tm(head, env));
            }
            W::Tm(app @ Tm::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals（icit 进侧栈）
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a, i) = match tm {
                        Tm::App(f, a, i) => (f, a, i),
                        base => {
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    let i = *i;
                    match f {
                        Tm::Var(ix) => {
                            let vf = env_nth(defs, env, *ix);
                            if v_tag(vf) == 1 {
                                // β 岔路：函数值已在手上（闭包），ApplyKnown
                                // 直接管 β（icit 无关）；heads>0 时 ChainWrap
                                // 照旧收拢
                                if heads > 0 {
                                    work.push(W::ChainWrap(heads));
                                }
                                work.push(W::ApplyKnown(vf));
                                work.push(W::Tm(a, env));
                                break;
                            }
                            vals.push(vf);
                            icits.push(i);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Apply(i));
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        }
                    }
                }
            }
            W::Apply(i) => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let env = env_ext(bump, c.env, va);
                    work.push(W::Tm(c.body, env));
                } else {
                    vals.push(spine.push(vf, va, i));
                }
            }
            W::ApplyKnown(vf) => {
                let va = vals.pop().expect("eval 栈：ApplyKnown 缺实参");
                let c = v_clo_of(vf);
                let env = env_ext(bump, c.env, va);
                work.push(W::Tm(c.body, env));
            }
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    let i = icits.pop().expect("eval 栈：ChainWrap 缺 icit");
                    v = spine.push(vf, v, i);
                }
                vals.push(v);
            }
            W::LetBody(u, env) => {
                let vt = vals.pop().expect("eval 栈：LetBody 缺绑定值");
                work.push(W::Tm(u, env_ext(bump, env, vt)));
            }
            W::PiBody(name, icit, cod, env) => {
                let dom = vals.pop().expect("eval 栈：PiBody 缺定义域");
                let cell = bump.alloc(PiCell {
                    name,
                    icit,
                    dom,
                    env,
                    body: cod,
                });
                vals.push(v_pi(cell));
            }
            W::AppPrun(env, bds) => match bds {
                None => {
                    // 与 reference 的 (None, None) 对齐：掩码先行耗尽
                    debug_assert!(env.binds.is_none() && env.flat_len == 0);
                }
                Some(b) if env.binds.is_none() && b.slot.is_none() => {
                    // O(1) 跳段：binds 耗尽后剩余链只剩 define 槽（Some 槽
                    // 与 binds 链平行入链，binds 空则链上不再有绑定槽）。
                    // none-run 整段只递减 flat_len、从不产生实参——按入链时
                    // 维护的 run 长度一次跳完，落点 = run 后第一个槽。
                    assert!(env.flat_len >= b.none_run); // 链与 env 平行（release 也查：错位时 u32 减会 wrap 成静默越界）
                    work.push(W::AppPrun(
                        Env {
                            flat_len: env.flat_len - b.none_run,
                            ..env
                        },
                        b.after_run,
                    ));
                }
                Some(b) => {
                    // 内层绑定 = 链头；链耗尽后走平坦 def 区域末端。先跑
                    // 余下槽位（外层），再应用本槽（内层最后应用）
                    let (arg, rest) = if let Some(e) = env.binds {
                        (
                            b.slot.map(|_| e.val),
                            Env {
                                binds: e.next,
                                ..env
                            },
                        )
                    } else if env.flat_len > 0 {
                        let v = defs[(env.flat_base + env.flat_len - 1) as usize];
                        (
                            b.slot.map(|_| v),
                            Env {
                                flat_len: env.flat_len - 1,
                                ..env
                            },
                        )
                    } else {
                        panic!("impossible") // env 与 pr 错位
                    };
                    match (arg, b.slot) {
                        (Some(a), Some(i)) => work.push(W::AppPrunOne(a, i)),
                        (None, Some(_)) => panic!("impossible"), // env 短于 pr
                        _ => {}
                    }
                    work.push(W::AppPrun(rest, b.next));
                }
            },
            W::AppPrunOne(arg, i) => {
                let v = vals.pop().expect("eval 栈：AppPrunOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let env = env_ext(bump, c.env, arg);
                    work.push(W::Tm(c.body, env));
                } else {
                    vals.push(spine.push(v, arg, i));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；flex 头共享 ?m 节点）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01/L04；L05 不产
/// `AppPruning`（它是项层的洞形态，值层不存在），本段与 L04 逐字同构。
enum QJob<'a> {
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
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同为同一变量
    /// （或同一未解 meta）时用共享节点，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: u32,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Tm<'a>>,
        prev: Option<&'a Tm<'a>>,
    },
}

/// (值打包字, quote level) → 已引结果子树。icit 不进键：它随 `V` 指向的
/// 单元/槽位携带，同一打包字在同一 level 的 quote 产出（含 icit）唯一。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote（L04 版原样：AppPruning 不在 quote 产出形态里）。
#[allow(clippy::too_many_arguments)]
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
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
                // 先 force（metacontext 在 quote 期间冻结，同键同结果）
                let v = force(bump, spine, work, vals, icits, defs, metas, v0);
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
                                    &*bump.alloc(Tm::Var(level - v_lvl_of(f0) - 1))
                                        as &Tm<'a>,
                                ),
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0))) as &Tm<'a>),
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
                            tasks.push(QJob::App1(top_icit));
                            tasks.push(QJob::Q(ea, level));
                            tasks.push(QJob::Q(spine.stack[h].f, level));
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
                let v = eval_iter(bump, spine, work, vals, icits, defs, metas, env, body);
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
                            // 非平凡链头：挂起引 f，ChainRun 续跑
                            tasks.push(QJob::ChainRun {
                                level,
                                next: i + 1,
                                end,
                                f0,
                                idx_node,
                                prev: Some(prev),
                            });
                            tasks.push(QJob::Q(fi, level));
                            break;
                        }
                    }
                }
            }
        }
    }
    done.pop().expect("quote 必须恰有一个根")
}

// unify（工作表迭代 + force 前置 + 模式求解 + intersect/flex-flex + 判等记忆化）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L05_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L05_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// unify 工作表条目：待比较子对，或 Π 余定义域的惰性比较屏障，或判等
/// 记忆化屏障。
enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外，
/// 对应 Haskell `go` 的剥序）都取到裸变量则产出掩码（槽位相等 → 其 icit、
/// 不等 → None）；有 None 即剪枝（`pruneMeta`），全相等即成立。长度不等
/// 直接失败（上游 `impossible` 分支 → unify_sp 的长度失配）：与参考版的
/// 「失配即败、零比较」同语义——不比较共同前缀，避免前缀里的 flex 在
/// 失败前被提前求解（污染 metacontext、改变失败路径的错误渲染）。任一对
/// 含非变量 → 回落 `unify_sp` 逐实参比较（长度相等，逐对一致）。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    m: u32,
    args1: &[(V, Icit)], // 内先（collect_args 的产出序）
    args2: &[(V, Icit)],
) -> bool {
    let n1 = args1.len();
    let n2 = args2.len();
    if n1 != n2 {
        return false; // 长度失配：直败零比较（连 force/压栈都省）
    }
    let common = n1;
    let mut pr: Vec<Option<Icit>> = Vec::with_capacity(common);
    let mut fallback = false;
    for k in 0..common {
        let f1 = force(bump, spine, work, vals, icits, defs, metas, args1[k].0);
        let f2 = force(bump, spine, work, vals, icits, defs, metas, args2[k].0);
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            pr.push(if v_lvl_of(f1) == v_lvl_of(f2) {
                Some(args1[k].1)
            } else {
                None
            });
        } else {
            fallback = true; // 上游 go 的 None：回落 unify_sp
            break;
        }
    }
    if !fallback {
        if pr.iter().any(|x| x.is_none()) {
            return prune_meta_bump(bump, spine, work, vals, icits, defs, metas, &pr, m)
                .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：较长 spine 一侧优先反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    let (ma, argsa, vrhs, mb, argsb, vlhs) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, work, vals, icits, defs, metas, ren, gamma, argsa) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, ren, gamma, ma, argsa.len() as u32, mask,
            vrhs,
        ),
        None => {
            // 一侧非模式：落另一侧（solve = invert + solve_with_pren）
            match invert_bump(bump, spine, work, vals, icits, defs, metas, ren, gamma, argsb) {
                Some(mask) => solve_with_pren_bump(
                    bump, spine, work, vals, icits, defs, metas, ren, gamma, mb,
                    argsb.len() as u32, mask, vlhs,
                ),
                None => false,
            }
        }
    }
}

/// unification：结构比较 + 模式求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。分派与参考版逐项对应：λ/η → U → Π（icit 相等）→ 同头 rigid
/// 逐实参 → 同头 flex = intersect → 异头 flex = flex_flex → 单侧 flex 求解。
#[allow(clippy::too_many_arguments)]
fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配
    conv.memo.clear();
    conv.scratch1.clear();
    conv.scratch2.clear();
    let memo = &mut conv.memo;
    let mut stack: Vec<UItem<'a>> = Vec::new();
    stack.push(UItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        if t.0 == u.0 {
            continue; // 位相等：同一值
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(bump, spine, work, vals, icits, defs, metas, t);
        let u = force(bump, spine, work, vals, icits, defs, metas, u);
        if t.0 == u.0 {
            continue; // force 展开后同值（同一解的两处引用）
        }
        match (v_tag(t), v_tag(u)) {
            // λ 情形（eta 含）：两边都应用到同一个新变量
            (1, 1) => {
                let c1 = v_clo_of(t);
                let c2 = v_clo_of(u);
                let vt = {
                    let env = env_ext(bump, c1.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, env, c1.body)
                };
                let vu = {
                    let env = env_ext(bump, c2.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, env, c2.body)
                };
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            // η：中性一侧按 λ 一侧的 icit 应用（上游 `vApp t (VVar l) i`）
            (_, 1) => {
                let c = v_clo_of(u);
                let vu = {
                    let env = env_ext(bump, c.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, env, c.body)
                };
                let vt = spine.push(t, v_lvl(l), c.icit);
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            (1, _) => {
                let c = v_clo_of(t);
                let vt = {
                    let env = env_ext(bump, c.env, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, env, c.body)
                };
                let vu = spine.push(u, v_lvl(l), c.icit);
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }

            // 宇宙
            (3, 3) => {}

            // Π：icit 相等才比；先比定义域，再惰性 eval 两侧余定义域
            (4, 4) => {
                let p = v_pi_of(t);
                let q = v_pi_of(u);
                if p.icit != q.icit {
                    return false;
                }
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
            }

            // 变量
            (0, 0) => return false, // 位相等已剪同 level；异 level 必不等

            // 中性链 vs 中性链
            (2, 2) => {
                let h1 = v_spine_of(t);
                let h2 = v_spine_of(u);
                let hd1 = spine.spine_head(h1);
                let hd2 = spine.spine_head(h2);
                let f1 = v_tag(hd1) == 5;
                let f2 = v_tag(hd2) == 5;
                if f1 && f2 {
                    // 双 flex：同头 intersect、异头 flex_flex
                    let mut a1 = std::mem::take(&mut conv.scratch1);
                    a1.clear();
                    spine.collect_args(h1, &mut a1);
                    let mut a2 = std::mem::take(&mut conv.scratch2);
                    a2.clear();
                    spine.collect_args(h2, &mut a2);
                    let m1 = v_meta_of(hd1);
                    let m2 = v_meta_of(hd2);
                    let ok = if m1 == m2 {
                        intersect_bump(
                            bump, spine, work, vals, icits, defs, metas, &mut stack, l, m1, &a1,
                            &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, ren, l, m1, &a1, u, m2,
                            &a2, t,
                        )
                    };
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                if hd1.0 == hd2.0 {
                    // 同头刚性：逐实参比较（应用序；收集是逆序，压栈倒回）。
                    // 实参 icit 不比（类型已定，上游同款）。注：L03 的
                    // 「连续链长度 fail-fast」在 L04 已移除，此处同无。
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    // 同头中性逐层比较：函数部分（f）与最外层实参（a）各自作为
                    // 一对入栈，交给完整 unify 分派（同头继续下钻、异头 flex 走
                    // flex_flex、同头 flex 走 intersect）。**不能**在此直接下钻
                    // 进实参链——实参可能是异头 flex（如非线性的 `?6 a b` vs
                    // `?0 a a`），下钻会误比其内层变量。
                    let (f1, a1) = {
                        let e = &spine.stack[h1];
                        (e.f, e.a)
                    };
                    let (f2, a2) = {
                        let e = &spine.stack[h2];
                        (e.f, e.a)
                    };
                    // 对齐 unify_sp：先比函数部分（tail）再比最外层实参（head）。
                    // LIFO → 先 push 实参、后 push 函数部分（函数部分在栈顶先弹出）。
                    // 函数部分作为一整对交给 unify（同头则再逐层下钻、异头走 flex）。
                    if a1.0 != a2.0 {
                        stack.push(UItem::Pair(l, a1, a2));
                    }
                    if f1.0 != f2.0 {
                        stack.push(UItem::Pair(l, f1, f2));
                    }
                    continue;
                }
                // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve；
                // 双刚性异头 → 刚性失配。
                let (mv, h, rhs) = if f1 {
                    (v_meta_of(hd1), h1, u)
                } else if f2 {
                    (v_meta_of(hd2), h2, t)
                } else {
                    return false;
                };
                let mut args = std::mem::take(&mut conv.scratch1);
                args.clear();
                spine.collect_args(h, &mut args);
                let solved =
                    solve_bump(bump, spine, work, vals, icits, defs, metas, ren, l, mv, &args, rhs);
                conv.scratch1 = args;
                if solved {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }

            // 其余形态：一侧（或两侧）是裸/带链 flex
            _ => {
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                let ft = spine.flex_of(t, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                let fu = spine.flex_of(u, &mut a2);
                let ok = match (ft, fu) {
                    (Some(m1), Some(m2)) => {
                        if m1 == m2 {
                            intersect_bump(
                                bump, spine, work, vals, icits, defs, metas, &mut stack, l, m1,
                                &a1, &a2,
                            )
                        } else {
                            flex_flex_bump(
                                bump, spine, work, vals, icits, defs, metas, ren, l, m1, &a1, u,
                                m2, &a2, t,
                            )
                        }
                    }
                    (Some(m), None) => {
                        solve_bump(bump, spine, work, vals, icits, defs, metas, ren, l, m, &a1, u)
                    }
                    (None, Some(m)) => {
                        solve_bump(bump, spine, work, vals, icits, defs, metas, ren, l, m, &a2, t)
                    }
                    (None, None) => false, // 刚性失配 / 病态混杂
                };
                conv.scratch1 = a1;
                conv.scratch2 = a2;
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
        }
    }
    true
}

// solve（invert + prune 验证 + rename + lams，全迭代）
// --------------------------------------------------------------------------------

/// solve 的偏置换缓冲（generational）：`val[x]` 在第 `epoch` 代里给出
/// level x → 新下标；`stamp[x] == epoch` 表示条目有效。`reset` 只推进
/// epoch（O(1) 换代）。L05 增量：`NONE_MARK` 哨兵标记**非线性（重复）变量**
/// ——`get` 视其为缺项（rename 的 scope check 自然失败、invert 掩码记
/// `None`），与「未出现」同语义，无需第三集合。
#[derive(Default)]
struct RenBuf {
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
    /// 本代里 `x` 是否已标非线性哨兵（`get` 把哨兵视同缺项，invert 需要
    /// 用它区分「已标 NONE_MARK」与「从未出现」——否则重复变量的第 3+ 次
    /// 出现会把哨兵覆盖成真实映射，掩码被污染为全 Some）。
    #[inline]
    fn has_mark(&self, x: usize) -> bool {
        self.stamp.get(x).copied() == Some(self.epoch) && self.val[x] == NONE_MARK
    }
    #[inline]
    fn set(&mut self, x: usize, v: u32) {
        if x >= self.val.len() {
            self.val.resize(x + 1, 0);
            self.stamp.resize(x + 1, 0); // 0 != epoch（epoch 从 1 起），新槽全部无效
        }
        self.val[x] = v;
        self.stamp[x] = self.epoch;
    }
}

/// 上游 `invert`：实参（应用序）逐个 force 成**裸刚性变量**。非线性
/// （重复变量）不再失败：移出 renaming、记 `NONE_MARK`（后续出现保持哨兵
/// 不覆盖），产出把重复变量的
/// **全部出现**记为 `None` 的掩码（内先序 = args 序）；线性时返回空 vec
/// （参考版的 `None` 掩码）。非变量实参即失败（`None`）。`ren` 换代缓冲
/// 就地填充（后续 rename 直接消费），dom = `args.len()`。
#[allow(clippy::too_many_arguments)]
fn invert_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    ren: &mut RenBuf,
    gamma: u32,
    args: &[(V, Icit)], // 内先序（spine 收集器的输出）
) -> Option<Vec<Option<Icit>>> {
    ren.reset(); // 换代：本反演的映射从空开始
    let mut lvs: Vec<u32> = Vec::with_capacity(args.len());
    let mut nonlinear = false;
    for &(a, _) in args.iter().rev() {
        // 应用序（外先）
        let f = force(bump, spine, work, vals, icits, defs, metas, a);
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
            // 已标非线性哨兵：保持 NONE_MARK 不动。`get` 视哨兵为缺项，
            // 若走 `None` 臂会在第 3 次出现时把哨兵覆盖成真实下标（奇数次
            // 出现必坏），掩码构造随之把重复变量的槽位全标 Some。
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
    // 掩码（内先序 = args 原序；重复变量整级剪除）
    let mut mask: Vec<Option<Icit>> = Vec::with_capacity(args.len());
    for k in (0..args.len()).rev() {
        // lvs 按应用序填：lvs[0] = 最先应用（外）；args[k] 内先 ↔ 应用序 n-1-k
        let x = lvs[args.len() - 1 - k] as usize;
        mask.push(match ren.get(x) {
            Some(_) => Some(args[k].1),
            None => None, // 非线性或从未映射 → 剪
        });
    }
    Some(mask)
}

/// `Γ ⊢ ?m args ≡ rhs` 的求解（invert 已做）：非线性掩码先验证剪枝可行性，
/// 再 rename（occurs/scope check 在内），λ 包裹取自 **meta 类型**（L05 的
/// lams），空环境求值写表。失败即不改 metacontext。
#[allow(clippy::too_many_arguments)]
fn solve_with_pren_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    dom: u32,
    mask: Vec<Option<Icit>>, // invert 的非线性掩码（空 vec = 线性）
    rhs: V,
) -> bool {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 求解
    };
    // 非线性 spine：检查非线性的变量槽位可以从 meta 类型里剪掉
    // （剪后仍良型才允许求解）。嵌套 rename 自带 RenBuf（换代缓冲不互踩）。
    if !mask.is_empty() && prune_ty_bump(bump, spine, work, vals, icits, defs, metas, &mask, mty).is_none() {
        return false;
    }
    let Some(tm) =
        rename_iter(bump, spine, work, vals, icits, defs, ren, metas, Some(m), dom, gamma, rhs)
    else {
        return false;
    };
    let lam_tm = lams_from_ty(bump, spine, work, vals, icits, defs, metas, dom, mty, tm);
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    true
}

/// solve = invert + solve_with_pren。
#[allow(clippy::too_many_arguments)]
fn solve_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    ren: &mut RenBuf,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)],
    rhs: V,
) -> bool {
    match invert_bump(bump, spine, work, vals, icits, defs, metas, ren, gamma, args) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, ren, gamma, m, args.len() as u32, mask,
            rhs,
        ),
        None => false,
    }
}

/// rename 任务。icit 记账同 L04：**只有刚性 `spine_case` 预装载**
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

/// partial renaming 的迭代版（L04 版 + flex 分支升级 pruneVFlex）。`ren`
/// 单调插入无需回溯（L03/L04 论证）；flex 槽位的嵌套 rename 递归复用
/// `rename_iter`（剪枝罕见，深递归可接受；spine 长度是迭代不是递归）。
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
    // SpineFold 的实参 icit 预装载栈：spine_case 按收集序压入（最后应用
    // 的实参在栈底），SpineFold 弹出序 = 应用序（最先应用的实参先弹）。
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
                let v = force(bump, spine, work, vals, icits, defs, metas, v);
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
                                    bump, spine, work, vals, icits, defs, ren, metas, occ, dom,
                                    cod, m, h,
                                )?;
                                done.push(t);
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
                            eval_iter(bump, spine, work, vals, icits, defs, metas, env, c.body)
                        };
                        // lift：binder 槽 (cod → dom)（换代缓冲，插写即可）
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
                            eval_iter(bump, spine, work, vals, icits, defs, metas, env, cell.body)
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
                    _ => return None, // 病态（Π/U 被应用等）
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
    debug_assert_eq!(
        done_icits.len(),
        0,
        "icit 预装载必须全部配对弹出"
    );
    done.pop()
}

/// `pruneVFlex`：meta + 纯变量 renaming 判定与剪枝。槽位处理序外→内
/// （上游 `go` 的递归序——先 tail 后 head），掩码/结果折叠的 icit 全部取自
/// spine 槽位。`ren`/`metas` 共享（嵌套 rename 同域；剪枝事件写表）。
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
        let f = force(bump, spine, work, vals, icits, defs, metas, a);
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
                bump, spine, work, vals, icits, defs, ren, metas, occ, dom, cod, f,
            )?;
            slots.push((Some(t), i));
            status = SpinePruneStatus::OKNonRenaming;
        }
    }
    let m_prime = if status == SpinePruneStatus::NeedsPruning {
        // 掩码内先序 = slots 反序（上游 `map (i <$ mt)`）
        let mut mask: Vec<Option<Icit>> = Vec::with_capacity(slots.len());
        for (st, i) in slots.iter().rev() {
            mask.push(if st.is_some() { Some(*i) } else { None });
        }
        prune_meta_bump(bump, spine, work, vals, icits, defs, metas, &mask, m)?
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
fn prune_meta_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    mask: &[Option<Icit>], // 内先序
    m: u32,
) -> Option<u32> {
    let mty = match &metas[m as usize] {
        MetaEntry::Unsolved(a) => *a,
        _ => unreachable!(), // 只对未解 meta 剪枝
    };
    let pruned_tm = prune_ty_bump(bump, spine, work, vals, icits, defs, metas, mask, mty)?;
    let prunedty = eval_iter(
        bump, spine, work, vals, icits, defs, metas, EMPTY_ENV, pruned_tm,
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
        bump, spine, work, vals, icits, defs, metas, mask.len() as u32, mty, ap,
    );
    let sol = eval_iter(
        bump, spine, work, vals, icits, defs, metas, EMPTY_ENV, lam_tm,
    );
    metas[m as usize] = MetaEntry::Solved(sol, mty);
    Some(mp)
}

/// `pruneTy (revPruning pr) a`：掩码**外→内**配对 Π 层（`Some` 层保留、
/// 定义域过嵌套 renaming、进 lift；`None` 层删掉、进 skip），耗尽后剩余
/// 类型过 renaming。自带换代缓冲（外层 rename 的 `ren` 不互踩）。
#[allow(clippy::too_many_arguments)]
fn prune_ty_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    mask_inner_first: &[Option<Icit>],
    mty: V,
) -> Option<&'a Tm<'a>> {
    let mut ren2 = RenBuf::default();
    ren2.reset(); // epoch 从 1 起（新槽 stamp 0 无效）
    let mut dom: u32 = 0;
    let mut cod: u32 = 0;
    let mut layers: Vec<(&'a str, Icit, &'a Tm<'a>)> = Vec::new();
    let mut cur = force(bump, spine, work, vals, icits, defs, metas, mty);
    for entry in mask_inner_first.iter().rev() {
        // 外→内
        if v_tag(cur) != 4 {
            return None; // 上游 impossible：掩码与类型层不匹配
        }
        let p = v_pi_of(cur);
        let (name, icit, pdom, env, body) = (p.name, p.icit, p.dom, p.env, p.body);
        if entry.is_some() {
            let dtm = rename_iter(
                bump, spine, work, vals, icits, defs, &mut ren2, metas, None, dom, cod, pdom,
            )?;
            // lift：binder 进映射（cod 是即将下探的 Δ 变量，dom 是它的 Γ 位）
            ren2.set(cod as usize, dom);
            layers.push((name, icit, dtm));
            dom += 1;
        }
        let next = eval_iter(
            bump,
            spine,
            work,
            vals,
            icits,
            defs,
            metas,
            env_ext(bump, env, v_lvl(cod)),
            body,
        );
        cod += 1;
        cur = force(bump, spine, work, vals, icits, defs, metas, next);
    }
    let mut t = rename_iter(
        bump, spine, work, vals, icits, defs, &mut ren2, metas, None, dom, cod, cur,
    )?;
    // 保留层由内向外回包（layers 序 = 外→内，rev = 内→外 ✓）
    for (name, icit, dtm) in layers.iter().rev() {
        t = bump.alloc(Tm::Pi(name, *icit, dtm, t));
    }
    Some(t)
}

/// `lams l a t`（L05 版：沿 **meta 类型**的 Π 层包 λ——名字与 icit 随 Π
/// 携带，`"_"` 改名 `x{l'}`（0 起）；逐层用 `VVar l'` 剥闭包）。
#[allow(clippy::too_many_arguments)]
fn lams_from_ty<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    l: u32,
    ty: V,
    body: &'a Tm<'a>,
) -> &'a Tm<'a> {
    let mut names: Vec<(&'a str, Icit)> = Vec::with_capacity(l as usize);
    let mut cur = force(bump, spine, work, vals, icits, defs, metas, ty);
    for lp in 0..l {
        if v_tag(cur) != 4 {
            unreachable!(); // 类型 Π 层数不足（上游同款不可能）
        }
        let p = v_pi_of(cur);
        let (name, icit, env, body_tm) = (p.name, p.icit, p.env, p.body);
        let name = if name == "_" {
            bump.alloc_str(&format!("x{}", lp))
        } else {
            name
        };
        names.push((name, icit));
        let next = eval_iter(
            bump,
            spine,
            work,
            vals,
            icits,
            defs,
            metas,
            env_ext(bump, env, v_lvl(lp)),
            body_tm,
        );
        cur = force(bump, spine, work, vals, icits, defs, metas, next);
    }
    let mut t = body;
    for (name, icit) in names.iter().rev() {
        t = bump.alloc(Tm::Lam(name, *icit, t));
    }
    t
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// `pruneVFlex` 的 spine 状态（参考版 `SpinePruneStatus` 同构）。
#[derive(Debug, Clone, Copy, PartialEq)]
enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

/// 稳态复用机（L04 版 + typed metas / pruning 掩码 / telescope）。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。**只收源码
    /// binder**（bind/define）——inserted binder 不入表（对源码名不可见，
    /// 等价于参考版 `src_names` 的跳过）。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。`Cxt.mark` 记各上下文的
    /// trail 长度，退出即截断。new_binder 不留轨迹、mark 不动。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
}

/// unify 的跨调用草稿（`FxHashSet`（判等记忆化）与两个实参收集 Vec 都是
/// `'static` 类型，可常驻 Machine 复用容量——unify 的收集/判等路径零分配；
/// 带 `'a` 的 work/tasks 小栈因借过 bump 生命周期，仍按调用新建，首个 push
/// 各一次堆分配——同 L02-L04 的稳态设计）。
#[derive(Default)]
struct ConvScratch {
    memo: FxHashSet<(u64, u64)>,
    scratch1: Vec<(V, Icit)>,
    scratch2: Vec<(V, Icit)>,
}

const PI_NAME: &str = "x"; // infer App 非 Π 分支合成的闭包名（只服务 pretty）

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine {
                stack: Vec::with_capacity(4096),
            },
            vals: Vec::with_capacity(4096),
            icits: Vec::new(),
            conv: ConvScratch::default(),
            defs: Vec::with_capacity(4096),
            metas: Vec::new(),
            ren: RenBuf::default(),
            name_map: FxHashMap::default(),
            name_trail: Vec::new(),
        }
    }

    /// 每轮 reset：metacontext 清空 + 名字表/轨迹/环境区域清空。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.name_map.clear();
        self.name_trail.clear();
        self.defs.clear();
    }

    /// Extend Cxt with a bound variable（源码 binder）：环境 + types 链 +
    /// 名字表 + 撤销轨迹 + telescope/pruning 同步。`a_t` 是绑定类型的引项
    /// （参考版在 bind 调用点 quote——telescope 闭包用）。
    #[allow(clippy::too_many_arguments)]
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            pos: cxt.pos,
        }
    }

    /// Extend Cxt with an inserted implicit binder：**不入名字表**
    /// （对源码名不可见）、trail 不动、mark 不变——但 telescope/pruning
    /// 照常扩展（参考版 newBinder 同款）。
    fn new_binder<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: false,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark,
            pos: cxt.pos,
        }
    }

    /// Extend Cxt with a definition（名字解析版）：pruning 记 `None`、
    /// telescope 记 Define 槽（类型项 + 定义项直接复用 elaborated 项——
    /// 参考版 `define` 同款，不重引）。
    #[allow(clippy::too_many_arguments)]
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: Some(t_t),
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(None, cxt.pruning))),
            binds: cxt.binds, // define 槽不产生 Π 层
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            pos: cxt.pos,
        }
    }

    /// 截断撤销轨迹到 `mark`（binder 作用域退出）。
    fn unwind_names(&mut self, mark: u32) {
        while self.name_trail.len() > mark as usize {
            let (key, prev) = self.name_trail.pop().expect("unwind_names: 轨迹为空");
            match prev {
                Some(entry) => {
                    self.name_map.insert(key, entry);
                }
                None => {
                    self.name_map.remove(&key);
                }
            }
        }
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（参考版无差别 close+eval 的性能化）：
    /// **`binds == 0`**（telescope 只剩 Define 的 Let 层——eval 只往 env
    /// 塞值、不添 Π 层）时：常值类型（U / 裸未解 meta，tag 3/5）闭类型
    /// 恒等；`quote(lvl, a)` 无自由变量则可跳过 Let 链直接空环境求值
    /// （顶层 define 链的逐层重 eval 全免）。有绑定槽时闭类型必须含
    /// Π 层（与 spine 槽一一对应），一律全构造（与参考版同形）。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && (v_tag(a) == 3 || v_tag(a) == 5) {
            a
        } else {
            let q = self.quote(bump, cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, EMPTY_ENV, closed)
            }
        };
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved(mty));
        bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(m)), cxt.pruning))
    }

    /// 沿 telescope 链闭包（参考版 `close_ty` 同款：Bind → 显式 Π、
    /// Define → Let；内层先包、外层最后）。
    fn close_tm<'a>(
        &self,
        bump: &'a Bump,
        mut ls: Option<&'a LCons<'a>>,
        q: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        let mut b = q;
        while let Some(n) = ls {
            b = match n.t_t {
                None => bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b)),
                Some(t) => bump.alloc(Tm::Let(n.name, n.a_t, t, b)),
            };
            ls = n.next;
        }
        b
    }

    /// fresh meta 的求值快捷路径：掩码全为 define 槽（或空）时 AppPrun
    /// 走空转（跳段后无实参可应用），结果恒为裸 meta 立即数——免一次
    /// eval。含绑定槽时照常求值（产生 pattern spine）。
    fn eval_fresh(&mut self, bump: &Bump, env: Env, m: &Tm<'_>) -> V {
        if let Tm::AppPruning(CTm_head, pr) = m {
            // 头必须是裸 Meta 才有短路意义（telescope 求值除外）
            if let Tm::Meta(mm) = CTm_head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, env, m)
    }

    fn eval<'a>(&mut self, bump: &'a Bump, env: Env, tm: &'a Tm<'a>) -> V {
        eval_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
            &mut self.icits,
            &mut self.defs,
            &self.metas,
            env,
            tm,
        )
    }

    fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        quote_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            &mut self.icits,
            &mut self.defs,
            &self.metas,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（同 L03/L04：表随本次调用新建，绝不跨 reset 持有）。
    fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let mut memo: QuoteMemo<'a> = FxHashMap::default();
        quote_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            &mut self.icits,
            &mut self.defs,
            &self.metas,
            level,
            v,
            Some(&mut memo),
        )
    }

    fn unify(&mut self, bump: &Bump, l: u32, t: V, u: V) -> bool {
        unify_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
            &mut self.icits,
            &mut self.defs,
            &mut self.metas,
            &mut self.ren,
            &mut self.conv,
            l,
            t,
            u,
        )
    }

    fn show_val(&mut self, bump: &Bump, cxt: Cxt<'_>, v: V) -> String {
        let t = self.quote(bump, cxt.lvl, v);
        let ns: Vec<String> = types_names(cxt.types);
        super::pretty_tm(0, &ns, &export(t))
    }

    fn unify_catch(&mut self, bump: &Bump, cxt: Cxt<'_>, t: V, t_prime: V) -> Result<(), Error> {
        if self.unify(bump, cxt.lvl, t, t_prime) {
            Ok(())
        } else {
            Err(report_at(
                cxt.pos,
                format!(
                    "Cannot unify expected type\n\n  {}\n\nwith inferred type\n\n  {}",
                    self.show_val(bump, cxt, t),
                    self.show_val(bump, cxt, t_prime)
                ),
            ))
        }
    }

    // 隐式插入（上游 Elaboration.hs 的 insert 族；fresh_meta 带类型）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> (&'a Tm<'a>, V) {
        let va = force(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
            &mut self.icits,
            &mut self.defs,
            &self.metas,
            va,
        );
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, env, p.body)
            };
            let t2 = bump.alloc(Tm::App(t, m, Icit::Impl));
            self.insert_go(bump, cxt, t2, b)
        } else {
            (t, va)
        }
    }

    /// infer 后无条件插入。
    fn insert_t<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        Ok(self.insert_go(bump, cxt, t, va))
    }

    /// infer 后插入，但隐式 lambda 本身免插。
    fn insert<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        if let Tm::Lam(_, Icit::Impl, _) = t {
            Ok((t, va))
        } else {
            self.insert_t(bump, cxt, t, va)
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止；隐式前缀
    /// 耗尽仍无匹配 → `No named implicit argument with name x`。
    fn insert_until_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        name: &str,
        t: &'a Tm<'a>,
        mut va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let mut t = t;
        loop {
            let forced = force(
                bump,
                &mut self.spine,
                &mut Vec::new(),
                &mut self.vals,
                &mut Vec::new(),
                &mut self.defs,
                &self.metas,
                va,
            );
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(report_at(
                    cxt.pos,
                    format!("No named implicit argument with name {name}"),
                ));
            }
        }
    }

    /// 主 `check`：binder 形态与 Π 匹配 → 绑定检查；非 lambda 项（或 icit
    /// 失配的 lambda）对隐式 Π → 补 inserted binder；`RLet` 总可检查；
    /// 洞 → fresh meta（类型 = 期望）；其余 fall-through 到 infer +
    /// **insert** + unify。
    fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = force(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
            &mut self.icits,
            &mut self.defs,
            &self.metas,
            a,
        );
        match t {
            Raw::SrcPos(pos, t) => {
                let mut cxt = cxt;
                cxt.pos = *pos;
                self.check(bump, cxt, t, a)
            }

            Raw::Lam(x, larg, tbody) if v_tag(a) == 4 => {
                let p = v_pi_of(a);
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命名 binder 按名定位（本地名 = Raw 的 binder 名）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, cxt2, tbody, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码不可见），
                    // 整个 lambda 对余定义域重检（下一轮 matched 或继续补）
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, cxt2, t, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general（infer + insert + unify）
                    let (t2, tty) = self.infer(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt, a, tty)?;
                    Ok(t2)
                }
            }

            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            _ if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl => {
                let p = v_pi_of(a);
                let name: &'a str = bump.alloc_str(p.name);
                let body_a = {
                    let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                    self.eval(bump, env, p.body)
                };
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, p.dom);
                let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                let body = self.check(bump, cxt2, t, body_a)?;
                self.unwind_names(mark);
                Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check(bump, cxt, a_ty, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t, va)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
                let u_tm = self.check(bump, cxt2, u, a)?;
                self.unwind_names(mark);
                Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
            }

            // hole：以 fresh meta 填充（类型 = 期望类型）
            Raw::Hole => Ok(self.fresh_meta(bump, cxt, a)),

            _ => {
                let (t, tty) = self.infer(bump, cxt, t)?;
                let (t, tty) = self.insert(bump, cxt, t, tty)?;
                self.unify_catch(bump, cxt, a, tty)?;
                Ok(t)
            }
        }
    }

    /// 主 `infer`。
    fn infer<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            Raw::SrcPos(pos, t) => {
                let mut cxt = cxt;
                cxt.pos = *pos;
                self.infer(bump, cxt, t)
            }

            Raw::Var(x) => {
                if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed) {
                    // O(1)：表与 types 链由 bind/define + trail 同步维护；
                    // inserted binder 从不入表——在表里即在（源码）scope 里
                    if let Some(&(blvl, ty)) = self.name_map.get(&x.data) {
                        return Ok((bump.alloc(Tm::Var(cxt.lvl - blvl - 1)), ty));
                    }
                } else {
                    // 消融口径：沿 types 链线性找名（跳过 inserted binder）
                    let mut i = 0u32;
                    let mut tys = cxt.types;
                    while let Some(tc) = tys {
                        if tc.source && tc.name == x.data {
                            return Ok((bump.alloc(Tm::Var(i)), tc.ty));
                        }
                        i += 1;
                        tys = tc.next;
                    }
                }
                Err(report_at(
                    cxt.pos,
                    format!("Name not in scope: {}", x.data),
                ))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())), // U : U rule

            // 定义域挂洞；余定义域闭包住当前环境；体推断后在**扩展后的**
            // 上下文里 insert（上游 `insert cxt'`——meta 的 pruning 含本 binder）
            Raw::Lam(x, Either::Icit(i), t) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let (t, b) = self.infer(bump, cxt2, t)?;
                let (t, b) = self.insert(bump, cxt2, t, b)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell {
                    name,
                    icit: *i,
                    dom: a,
                    env: cxt.env,
                    body,
                });
                Ok((bump.alloc(Tm::Lam(name, *i, t)), v_pi(cell)))
            }

            Raw::Lam(_, Either::Name(_), _) => Err(report_at(
                cxt.pos,
                "Cannot infer type for lambda with named argument".to_string(),
            )),

            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用（显式给隐式）；位置 Expl → 先 insert_t
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        let (t, tty) = self.insert_until_name(bump, cxt, &name.data, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    &Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    &Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = force(
                    bump,
                    &mut self.spine,
                    &mut Vec::new(),
                    &mut self.vals,
                    &mut Vec::new(),
                    &mut self.defs,
                    &self.metas,
                    tty,
                );
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(report_at(
                            cxt.pos,
                            format!(
                                "Function icitness mismatch: expected {}, got {}.",
                                show_icit(i),
                                show_icit(p.icit)
                            ),
                        ));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder（PI_NAME）不进名字表：只延伸 env/telescope/
                    // pruning（L04 同款理由——无 Raw 在其下 elaborate，留痕
                    // 反而遮蔽用户名字）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u());
                    let a = self.eval_fresh(bump, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt.lvl, a);
                    let cxt2 = Cxt {
                        env: env_ext(bump, cxt.env, v_lvl(cxt.lvl)),
                        types: cxt.types,
                        locals: Some(bump.alloc(LCons {
                            name: PI_NAME,
                            a_t,
                            t_t: None,
                            next: cxt.locals,
                        })),
                        pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
                        binds: cxt.binds + 1, // 合成 binder 也是绑定槽
                        lvl: cxt.lvl + 1,
                        mark: cxt.mark,
                        pos: cxt.pos,
                    };
                    let cod_meta = self.fresh_meta(bump, cxt2, v_u());
                    let cell = bump.alloc(PiCell {
                        name: PI_NAME,
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    // 注意参数序：期望 = 头的推断类型，合成 Π 是被检方
                    //（上游 `unifyCatch cxt tty (VPi "x" i a b)`）
                    self.unify_catch(bump, cxt, tty, v_pi(&*cell))?;
                    (a, &*cell)
                };
                let u = self.check(bump, cxt, u, a)?;
                let arg = self.eval(bump, cxt.env, u);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg);
                    self.eval(bump, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u, i)), ty))
            }

            Raw::Pi(x, i, a, b) => {
                let a_tm = self.check(bump, cxt, a, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, va);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
                let b_tm = self.check(bump, cxt2, b, v_u())?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)), v_u()))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check(bump, cxt, a_ty, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t, va)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
                let (u_tm, uty) = self.infer(bump, cxt2, u)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }
        }
    }

    /// `displayMetas`：metacontext 逐条打印（上游 05 带类型形态），末尾
    /// 空行。`elab` 模式用。
    fn display_metas(&mut self, bump: &Bump) -> String {
        let mut out = String::new();
        for m in 0..self.metas.len() {
            let (v, a) = match &self.metas[m] {
                MetaEntry::Unsolved(a) => (None, *a),
                MetaEntry::Solved(v, a) => (Some(*v), *a),
            };
            let ty = self.quote(bump, 0, a);
            match v {
                None => out.push_str(&format!(
                    "let ?{m} : {} = ?;\n",
                    pretty_tm(0, &[], &export(ty))
                )),
                Some(v) => {
                    let val = self.quote(bump, 0, v);
                    out.push_str(&format!(
                        "let ?{m} : {} = {};\n",
                        pretty_tm(0, &[], &export(ty)),
                        pretty_tm(0, &[], &export(val))
                    ))
                }
            }
        }
        out.push('\n');
        out
    }
}

/// 项里是否含自由 `Var`（按 binder 深度算：Lam/Pi 体、Let 体 +1）。
/// `fresh_meta` 快捷路径 2 的判据（保守：自由 ⇒ 走全构造）。
fn has_free_var(t: &Tm<'_>) -> bool {
    let mut stack: Vec<(&Tm<'_>, u32)> = vec![(t, 0)];
    while let Some((x, d)) = stack.pop() {
        match x {
            Tm::Var(i) => {
                if *i >= d {
                    return true;
                }
            }
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U | Tm::Meta(_) => {}
            Tm::Pi(_, _, a, b) => {
                stack.push((a, d));
                stack.push((b, d + 1));
            }
            Tm::Let(_, a, t, u) => {
                stack.push((a, d));
                stack.push((t, d));
                stack.push((u, d + 1));
            }
        }
    }
    false
}

/// Elaboration 上下文（全 Copy，绑定量在 bump 里）。
#[derive(Clone, Copy)]
struct Cxt<'a> {
    env: Env<'a>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目；show_val 取名字）。
    types: Option<&'a TCons<'a>>,
    /// telescope（上游 `cxtLocals`）：fresh_meta 闭类型用。
    locals: Option<&'a LCons<'a>>,
    /// fresh meta 的 scope 掩码（与 env 平行；头 = 最内层）。
    pruning: Option<&'a PrCons<'a>>,
    /// 绑定层数（bind/new_binder/synth +1，define 不动）：`fresh_meta`
    /// 快捷路径的守卫——telescope 的 **binder 槽位闭成 Π 层**，
    /// `binds == 0` 时闭类型才等于自身。
    binds: u32,
    lvl: u32,
    /// 名字撤销轨迹的本上下文基线（inserted binder 不留轨迹、不动 mark）。
    mark: u32,
    pos: Span<()>,
}

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

impl<'a> Cxt<'a> {
    fn empty(pos: Span<()>) -> Self {
        Cxt {
            env: EMPTY_ENV,
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
            mark: 0,
            pos,
        }
    }
}

fn types_names(mut tys: Option<&TCons<'_>>) -> Vec<String> {
    let mut ns = Vec::new();
    while let Some(tc) = tys {
        ns.push(tc.name.to_owned());
        tys = tc.next;
    }
    ns
}

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈，深度无上限；icit/掩码
/// 随任务携带），复用参考版的 pretty。
fn export(t: &Tm<'_>) -> CTm {
    use super::parser::Icit as PIcit;
    use crate::list::List as CList;
    use CTm as B;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, PIcit),
        Pi2(&'a str, PIcit),
        Let2(&'a str),
        App2(PIcit),
        AppPrun2(CList<Option<PIcit>>),
    }
    fn name(x: &str) -> Name {
        Name {
            data: x.into(),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        }
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<CTm> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(B::Var(Ix(*i))),
            J::Do(Tm::Lam(x, i, b)) => {
                tasks.push(J::Lam2(x, *i));
                tasks.push(J::Do(b));
            }
            J::Do(Tm::App(f, a, i)) => {
                tasks.push(J::App2(*i));
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            }
            J::Do(Tm::AppPruning(h, pr)) => {
                // bds 持久链表（头 = 最内层）→ 参考版 List<Option<Icit>>（同序）
                let mut vec: Vec<Option<PIcit>> = Vec::new();
                let mut cur = *pr;
                while let Some(b) = cur {
                    vec.push(b.slot);
                    cur = b.next;
                }
                let mut list: CList<Option<PIcit>> = CList::new();
                for s in vec.into_iter().rev() {
                    list = list.prepend(s);
                }
                tasks.push(J::AppPrun2(list));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::U) => done.push(B::U),
            J::Do(Tm::Pi(x, i, a, b)) => {
                tasks.push(J::Pi2(x, *i));
                tasks.push(J::Do(b));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Let(x, a, t, u)) => {
                tasks.push(J::Let2(x));
                tasks.push(J::Do(u));
                tasks.push(J::Do(t));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Meta(m)) => done.push(B::Meta(super::MetaVar(*m))),
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(B::Lam(name(x), i, Box::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(B::Pi(name(x), i, Box::new(dom), Box::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(B::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(B::App(Box::new(f), Box::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(B::AppPruning(Box::new(h), pr));
            }
        }
    }
    done.pop().expect("export 必须恰有一个根")
}

fn tm_size(t: &Tm<'_>) -> u64 {
    let mut stack: Vec<&Tm<'_>> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U | Tm::Meta(_) => {}
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                let mut cur = *pr;
                while let Some(b) = cur {
                    n += 1;
                    cur = b.next;
                }
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
        }
    }
    n
}

/// A/B 实验开关（Raw::Var 名字解析消融）：置 `L05_NO_NAME_MAP=1` 回落为
/// 沿 `types` 链的线性找名（跳过 inserted binder；`=0` 不关闭）。
static NO_NAME_MAP: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L05_NO_NAME_MAP").is_ok_and(|v| v != "0"))
    });

/// 稳态类型检查器（同 L03/L04：owns 一个反复 `reset` 的 `Bump` 与跨调用
/// 复用的 [`Machine`]）。
pub(crate) struct Tycker {
    bump: Bump,
    machine: Machine,
}

impl Tycker {
    pub(crate) fn new() -> Self {
        Tycker {
            bump: Bump::with_capacity(1 << 20),
            machine: Machine::new(),
        }
    }

    /// Main.hs 的 `mainWith` 等价物（`nf` / `type` / `elab`；`--help` 由
    /// 参考版处理）。nf/type 的引读默认走 quote 记忆化（输出逐字节一致）。
    pub(crate) fn run(&mut self, mode: &str, file: &str, raw: &Raw) -> String {
        self.run_impl(mode, file, raw, true)
    }

    /// [`Tycker::run`] 的非记忆化对照口径（ablation 用；输出一致）。
    pub(crate) fn run_no_memo(&mut self, mode: &str, file: &str, raw: &Raw) -> String {
        self.run_impl(mode, file, raw, false)
    }

    fn run_impl(&mut self, mode: &str, file: &str, raw: &Raw, use_memo: bool) -> String {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let cxt = Cxt::empty(super::initial_pos());
        match self.machine.infer(bump, cxt, raw) {
            Err(err) => super::display_error(file, &err),
            Ok((t, a)) => match mode {
                "nf" => {
                    let v = self.machine.eval(bump, EMPTY_ENV, t);
                    let n = quote_maybe(&mut self.machine, bump, 0, v, use_memo);
                    let ty = quote_maybe(&mut self.machine, bump, 0, a, use_memo);
                    format!(
                        "{}\n  :\n{}\n",
                        super::pretty_tm(0, &[], &export(n)),
                        super::pretty_tm(0, &[], &export(ty))
                    )
                }
                "type" => format!(
                    "{}\n",
                    super::pretty_tm(
                        0,
                        &[],
                        &export(quote_maybe(&mut self.machine, bump, 0, a, use_memo))
                    )
                ),
                _ => {
                    let metas = self.machine.display_metas(bump);
                    format!("{}{}\n", metas, super::pretty_tm(0, &[], &export(t)))
                }
            },
        }
    }

    /// 基准口径（bench 用）：仅 check。
    pub(crate) fn bench_check(&mut self, raw: &Raw) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine
            .infer(bump, Cxt::empty(super::initial_pos()), raw)
            .is_ok()
    }

    /// 基准口径：check + nf（quote），返回结果树节点数。
    #[allow(dead_code)]
    pub(crate) fn bench_check_nf(&mut self, raw: &Raw) -> u64 {
        self.bench_nf_impl(raw, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, raw: &Raw) -> u64 {
        self.bench_nf_impl(raw, true)
    }

    fn bench_nf_impl(&mut self, raw: &Raw, use_memo: bool) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        match self.machine.infer(bump, Cxt::empty(super::initial_pos()), raw) {
            Err(_) => 0,
            Ok((t, _)) => {
                let v = self.machine.eval(bump, EMPTY_ENV, t);
                let n = quote_maybe(&mut self.machine, bump, 0, v, use_memo);
                tm_size(n)
            }
        }
    }
}

/// `use_memo` 分派：memo 口径共享重复子树，普通口径独立重建。
fn quote_maybe<'a>(
    m: &mut Machine,
    bump: &'a Bump,
    level: u32,
    v: V,
    use_memo: bool,
) -> &'a Tm<'a> {
    if use_memo {
        m.quote_memo(bump, level, v)
    } else {
        m.quote(bump, level, v)
    }
}

/// 一次性口径入口（与参考版 `main_with` 同签名同输出）。
pub(crate) fn main_with(mode: &str, file: &str) -> String {
    match mode {
        "nf" | "type" | "elab" => {}
        _ => return super::HELP_MSG.to_string(),
    }
    let Some(raw) = super::parser::parser(file, 0) else {
        return "parse error\n".to_string();
    };
    let mut tycker = Tycker::new();
    tycker.run(mode, file, &raw)
}

// 基准负载生成器（l05bench 共用；L04 全家桶 + L05 的 prune 特色负载）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 let 链，末尾 `p_k`。
pub(crate) fn church_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += &format!("p{k}\n");
    s
}

/// implicit 2^(k+1)（L04 特色负载的 L05 版）：每层 `id p_{i-1}` 触发一次
/// 隐式插入 + 一次求解——插入口的 fresh meta 类型恒为 `U`（tag 3 快捷路径
/// 全命中），掩码全 define 槽（eval_fresh 跳段）——验证 typed metas 不劣化
/// L04 的近线性。
pub(crate) fn implicit_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let id : {A : U} -> A -> A = \\x. x;\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..n {
        s += &format!("let p{i} : Nat = id p{};\n", i - 1);
    }
    s += "p0\n";
    s
}

/// prune 2^(k+1)（**L05 特色负载**）：每层 `m_i`（洞类型 `(A:U)(B:U) ->
/// U -> U -> U`：freshMeta 走 quote-closed 快捷路径）+ `t_i` 的
/// `m_i a a` 非线性 spine——invert 的重复变量掩码 + prune_ty 验证 +
/// solve，且类型 telescope 沿增长的 define 链闭合（参考版逐层重 eval）。
pub(crate) fn prune_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;\n\
         let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;\n\
         let the : (A : U) -> A -> A = \\ _ x. x;\n",
    );
    for i in 0..n {
        s += &format!(
            "let m{i} : (A : U)(B : U) -> U -> U -> U = _;\n\
             let t{i} = \\a b. the (Eq (m{i} a a) (\\x y. y)) refl;\n"
        );
    }
    s += "t0\n";
    s
}

/// conv 2^(k+1)：church 之上 `Eq Nat (add p_k zero) p_k = refl Nat p_k`。
pub(crate) fn conv_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let zero : Nat = \\N s z. z;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
         let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += &format!("let eqTest : Eq Nat (add p{k} zero) p{k} = refl Nat p{k};\n");
    s += "eqTest\n";
    s
}

/// conv_dup（判等记忆化的命中负载）：`Rel` 的重复谓词让 check 把同一对
/// 比较 3 次——记忆化把第 2/3 次塌缩为查表。
pub(crate) fn conv_dup_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let zero : Nat = \\N s z. z;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let Rel : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y -> P y;\n\
         let relRefl : (A : U) -> (x : A) -> Rel A x x = \\A x P p1 p2. p1;\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += &format!(
        "let relTest : Rel Nat (add p{k} zero) (add p{k} zero) = relRefl Nat p{k};\n"
    );
    s += "relTest\n";
    s
}

/// chain（名字解析负载）：n 条顶层 let 链，每层引用 scope 深处最老的名字。
pub(crate) fn chain_src(k: u32) -> String {
    let n = 1u64 << (k + 1);
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..n {
        s += &format!("let p{i} : Nat = add p{} p0;\n", i - 1);
    }
    s += "p0\n";
    s
}

/// solve 2^(k+1)：`Eq _ p_k p_k = refl _ _`——rename 沿 church 展开的整条
/// neutral 链走，rename 任务栈/force 迭代的主展示负载。
pub(crate) fn solve_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let zero : Nat = \\N s z. z;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let Eq : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y;\n\
         let refl : (A : U) -> (x : A) -> Eq A x x = \\A x P px. px;\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += &format!("let eqTest : Eq _ p{k} p{k} = refl _ _;\n");
    s += "eqTest\n";
    s
}

/// dup 2×（复制强制负载）：nf 节点数 = 4n + 12（n = 2^(k+1)）。
pub(crate) fn dup_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += "let D : Nat -> (Nat -> Nat -> Nat) -> Nat = \\x f. f x x;\n";
    s += &format!("D p{k}\n");
    s
}

/// dup 4×（两层复制）：nf 节点数 = 8n + 28。
pub(crate) fn dup_deep_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += "let D0 : Nat -> (Nat -> Nat -> Nat) -> Nat = \\x f. f x x;\n";
    s += "let D1 : ((Nat -> Nat -> Nat) -> Nat) -> \
          (((Nat -> Nat -> Nat) -> Nat) -> ((Nat -> Nat -> Nat) -> Nat) -> Nat) -> Nat \
          = \\y f. f y y;\n";
    s += &format!("D1 (D0 p{k})\n");
    s
}

#[cfg(test)]
mod tests {
    use super::super::{EX0_SRC, EX1_SRC};
    use super::*;

    /// 三模式全量互检的样例束（含 pruning 特例）——黑盒套件的
    /// assert_parity 同款，这里先在单元层兜一层。
    #[test]
    fn parity_on_pruning_examples() {
        for src in [
            EX0_SRC,
            EX1_SRC,
            // pr1/pr2/pr3：README 的剪枝三例（f 类型 meta 的合成 Π 剪 f 槽）
            "let pr1 = \\ f x. f x;\npr1\n",
            "let pr2 = \\ f x y. f x y;\npr2\n",
            "let pr3 = \\ f. f U;\npr3\n",
            // 非线性 spine 可解（m 的类型不依赖非线性实参）
            "\
             let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;\n\
             let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;\n\
             let the : (A : U) -> A -> A = \\ _ x. x;\n\
             let m : (A : U)(B : U) -> U -> U -> U = _;\n\
             let test = \\ a b. the (Eq (m a a) (\\ x y. y)) refl;\ntest\n",
            // 交集剪枝：`m a b c =? m c b a` 剪 a/c 取 b
            "\
             let Eq : {A : U} -> A -> A -> U = \\{A} x y. (P : A -> U) -> P x -> P y;\n\
             let refl : {A : U}{x : A} -> Eq {A} x x = \\ _ px. px;\n\
             let the : (A : U) -> A -> A = \\ _ x. x;\n\
             let m : U -> U -> U -> U = _;\n\
             let test = \\ a b c. the (Eq (m a b c) (m c b a)) refl;\ntest\n",
        ] {
            for mode in ["nf", "type", "elab"] {
                assert_eq!(
                    main_with(mode, src),
                    super::super::main_with(mode, src),
                    "mismatch on {src:?} ({mode})"
                );
            }
        }
    }

    /// 深度无上限：church 65536 的 check+nf 在默认栈上跑通。
    #[test]
    fn deep_church_65536() {
        let src = church_src(15);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        let size = tycker.bench_check_nf(&raw);
        // λ N s z. s^65536 z：3 个 Lam + 65536 个 App + 65537 个 Var
        assert_eq!(size, 3 + 65536 + 65537, "nf node count");
    }

    /// implicit 负载：16 层 `id p_{i-1}`，判定通过且与参考版逐字节一致。
    #[test]
    fn implicit_chain_matches_basic() {
        let src = implicit_src(3);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "implicit 未通过");
        let mut t = Tycker::new();
        assert_eq!(
            t.run("type", &src, &raw),
            super::super::main_with("type", &src),
            "implicit 判定与参考版不一致"
        );
    }

    /// prune 负载：每层非线性 solve + telescope 闭型，三模式互检。
    #[test]
    fn prune_chain_matches_basic() {
        let src = prune_src(2);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "prune 负载未通过");
        for mode in ["nf", "type", "elab"] {
            let mut t = Tycker::new();
            assert_eq!(
                t.run(mode, &src, &raw),
                super::super::main_with(mode, &src),
                "prune 负载与参考版不一致 ({mode})"
            );
        }
    }

    /// λ 体内的 `let`（define 的非 tip 回落路径，L04 同款回归）：
    /// 比对 type 与 nf 双模式。
    #[test]
    fn define_inside_lambda_matches_basic() {
        let src = concat!(
            "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n",
            "let id : {A : U} -> A -> A = \\x. x;\n",
            "let p0 : Nat = \\N s z. s (s z);\n",
            "let f : (u : Nat) -> Nat = \\u. let q0 : Nat = id u; let q1 : Nat = id q0; q1;\n",
            "let h : Nat = f p0;\n",
            "h\n"
        );
        let Some(raw) = super::super::parser::parser(src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "λ 内 let 未通过");
        for mode in ["type", "nf"] {
            let mut t = Tycker::new();
            assert_eq!(
                t.run(mode, src, &raw),
                super::super::main_with(mode, src),
                "λ 内 let 与参考版不一致 ({mode})"
            );
        }
    }

    /// AppPrun 跳段的混合形态：binder 槽夹在 define 槽之间的链。
    #[test]
    fn appprun_skip_mixed_chain_matches_basic() {
        let src = concat!(
            "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n",
            "let id : {A : U} -> A -> A = \\x. x;\n",
            "let p0 : Nat = \\N s z. s (s z);\n",
            "let p1 : Nat = id p0;\n",
            "let f : (u : Nat) -> Nat = \\u. id u;\n",
            "f p1\n"
        );
        let Some(raw) = super::super::parser::parser(src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "mixed 形态未通过");
        let mut t = Tycker::new();
        assert_eq!(
            t.run("type", src, &raw),
            super::super::main_with("type", src),
            "mixed 形态与参考版不一致"
        );
    }

    /// solve 工作负载：16384 级 rename 深度压力。
    #[test]
    fn solve_stress_16384() {
        let src = solve_src(13);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        assert!(tycker.bench_check(&raw));
    }

    /// solve / conv_dup / chain 判定与参考版一致（参考版的
    /// rename/prune_vflex 逐层栈耗用比 L04 大，深度负载在深栈线程里跑
    /// ——黑盒套件同款 `with_big_stack` 口径）。
    #[test]
    fn workload_parity() {
        for (name, src) in [
            ("solve", solve_src(8)),
            ("conv_dup", conv_dup_src(10)),
            ("chain", chain_src(8)),
        ] {
            let Some(raw) = super::super::parser::parser(&src, 0) else {
                panic!("parse failed");
            };
            let mut t = Tycker::new();
            assert!(t.bench_check(&raw), "{name} 未通过");
            let mut t = Tycker::new();
            let fast = t.run("type", &src, &raw);
            let src_c = src.clone();
            let basic = with_big_stack(move || super::super::main_with("type", &src_c));
            assert_eq!(
                fast, basic,
                "{name} 判定与参考版不一致"
            );
        }
    }

    /// 在深栈线程里跑（参考版 eval/quote/rename 全递归）。
    fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(f)
            .unwrap()
            .join()
            .unwrap()
    }

    /// 名字 map 的 shadowing + inserted-binder 不可见性。
    #[test]
    fn inserted_binder_invisible() {
        let src = "\
         let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let two : Nat = \\N s z. s (s z);\n\
         let A : Nat = two;\n\
         let f : {A : U} -> Nat -> Nat = \\x. A;\n\
         f\n";
        let Some(raw) = super::super::parser::parser(src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert_eq!(
            t.run("nf", src, &raw),
            super::super::main_with("nf", src),
            "inserted binder 可见性与参考版不一致"
        );
    }

    /// 稳态复用正确性：同一 Tycker 连续多轮，输出与每轮新建的一致。
    #[test]
    fn steady_state_reuse() {
        let Some(raw) = super::super::parser::parser(EX1_SRC, 0) else {
            panic!("parse failed");
        };
        let mut steady = Tycker::new();
        let r1 = steady.run("type", EX1_SRC, &raw);
        let r2 = steady.run("type", EX1_SRC, &raw);
        let fresh = main_with("type", EX1_SRC);
        assert_eq!(r1, r2);
        assert_eq!(r1, fresh);
    }

    /// 报错路径（错误消息 + 位置）与参考版逐字节一致。
    #[test]
    fn unify_failure_message() {
        let src = "let id : {A : U} -> A -> A\n  = \\x. x;\nlet bar : U = id id;\nbar\n";
        assert_eq!(main_with("nf", src), super::super::main_with("nf", src));
        let out = main_with("nf", src);
        assert!(out.contains("Cannot unify expected type"), "{out}");
    }

    /// icit 失配与命名实参错误的报错路径逐字节一致。
    #[test]
    fn icit_error_parity() {
        for src in [
            "let g : U -> U -> U = \\x y. x;\ng {U}",
            "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {C = U} U U\n",
        ] {
            assert_eq!(
                main_with("type", src),
                super::super::main_with("type", src)
            );
        }
    }

    /// dup 负载的 nf 输出与参考版逐字节一致（双口径）+ 节点数公式。
    #[test]
    fn dup_nf_matches_basic() {
        for (src, expect) in [(dup_src(4), 0u64), (dup_deep_src(4), 0)] {
            let Some(raw) = super::super::parser::parser(&src, 0) else {
                panic!("parse failed");
            };
            let basic = super::super::main_with("nf", &src);
            let mut t = Tycker::new();
            assert_eq!(t.run("nf", &src, &raw), basic, "memo 默认口径不一致");
            let mut t = Tycker::new();
            assert_eq!(t.run_no_memo("nf", &src, &raw), basic, "非 memo 对照口径不一致");
            let _ = expect;
        }
        let n = 1u64 << 11; // k=10 → church 2048
        for (src, expect) in [(dup_src(10), 4 * n + 12), (dup_deep_src(10), 8 * n + 28)] {
            let Some(raw) = super::super::parser::parser(&src, 0) else {
                panic!("parse failed");
            };
            let mut t = Tycker::new();
            assert_eq!(t.bench_check_nf(&raw), expect, "无 memo 节点数不符");
            let mut t = Tycker::new();
            assert_eq!(t.bench_check_nf_memo(&raw), expect, "memo 节点数不符");
        }
    }
}
