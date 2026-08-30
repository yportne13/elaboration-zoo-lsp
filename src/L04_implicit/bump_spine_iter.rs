//! L04 核心机（eval / quote / unify / force / rename / solve / check /
//! infer + 隐式插入）的极致性能版：L03 冠军配方（`bump_spine_iter`）向
//! implicit args 层的移植。继承 L03 的全部机制（见其模块注释）：
//!
//! 1. bump arena；打包值 [`V`]（低 3 位 tag）；扁平中性 + spine 栈；
//! 2. 复合环境（平坦 def 区域 + 持久 binder 链）；
//! 3. 迭代内核：eval 双栈 / quote 任务栈 / unify 工作表 / rename 任务栈 /
//!    force 循环 / invert 循环；
//! 4. quote 记忆化（默认口径）+ unify 判等记忆化（`L04_NO_CONV_MEMO=1`
//!    消融）+ O(1) 名字解析（`L04_NO_NAME_MAP=1` 消融）；
//! 5. `Tycker` 稳态复用（跨轮 `Bump::reset`）。
//!
//! L04 的增量（icit 穿线点与插入机制）：
//!
//! - **Icit 穿线**：[`Tm`] 的 `Lam/App/Pi`、[`CloCell`]/[`PiCell`]、spine
//!   槽 [`Entry`] 都带 icit。β 应用不看 icit；spine 实参比较不看 icit
//!   （类型已定，上游 Unification.hs 同款）；**Π 比较要求 icit 相等**。
//! - **icit 的搬运点**：eval 右链下降把 Var 头应用的 icit 压侧栈
//!   （`ChainWrap` 折叠时消费）；force 重建 spine 沿收集的 (实参, icit) 对；
//!   quote 的 `App1`/`ChainRun` 按槽位 icit 产出 `App` 节点；rename 的
//!   `Ren` 携带实参 icit（平行 `done_icits` 栈与 `SpineFold` 对齐）。
//! - **隐式插入**（elaboration 层，仍是 check/infer 互递归）：`insert`/
//!   `insert_t`/`insert_until_name` 移植到 [`Machine`]；隐式 lambda 检查到
//!   隐式 Π 跳过插入；检查非 lambda 项到隐式 Π 补 **inserted binder**
//!   （[`Machine::new_binder`]——**不入 name_map**，对源码名不可见，等价于
//!   参考版线性扫描跳过 `NameOrigin::Inserted`；`TCons::source` 供消融
//!   回落）。
//! - **solve 的 lams**：icit 取自 spine 收集序（= 参考版 `sp.iter()` 头序 =
//!   上游 `reverse $ map snd sp`），最外层 λ 拿最后应用槽位的 icit——
//!   β 不看 icit，仅影响解的显示。
//!
//! 与参考版（`super`）共用 parser / pretty / 错误显示，输出逐字节一致
//! （互检测试）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use super::parser::{Either, Icit, Raw};
use crate::parser_lib::Span;
use super::{Error, Name, Tm as CTm, Ix, pretty_tm, report_at, show_icit};

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, Icit, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>, Icit),
    U,
    Pi(&'a str, Icit, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
    /// 显式引用的 meta（`?m`，来自 rename 产出/解）。
    Meta(u32),
    /// hole 处插入的 meta：抽象掉 elaboration 当时的全部 Bound 变量
    /// （`bds` 与求值环境平行：`bound = true` 槽位实参应用、`false` 跳过）。
    InsertedMeta(u32, Option<&'a BdCons<'a>>),
}

/// `InsertedMeta` 的槽位掩码链表（bump 持久链表，头 = 最内层绑定）。
/// 上游 `BD` 本就不带 icit（`vAppBDs` 硬编码 Expl），同款。
pub(crate) struct BdCons<'a> {
    bound: bool,
    next: Option<&'a BdCons<'a>>,
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
/// [`Machine::defs`]；只经 define 追加、恒 tip，`nth` O(1)）+ **持久 binder
/// 链表**（bind 与全部 β/瞬时求值扩展 O(1) 一个 bump 分配）。机制与论证
/// 同 L03（`env_slice` 教训：运行时 β 的扩展禁止引入拷贝）。
#[derive(Clone, Copy)]
pub(crate) struct Env<'a> {
    flat_base: u32,
    flat_len: u32,
    binds: Option<&'a EnvCons<'a>>,
}

const EMPTY_ENV: Env<'static> = Env { flat_base: 0, flat_len: 0, binds: None };

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

/// 环境扩展（**平坦 def 区域**：elaborator 的 define）——tip 原地追加。
#[inline]
pub(crate) fn env_ext_defs<'a>(defs: &mut Vec<V>, env: Env<'a>, v: V) -> Env<'a> {
    debug_assert_eq!(env.flat_base + env.flat_len, defs.len() as u32);
    defs.push(v);
    Env { flat_base: env.flat_base, flat_len: env.flat_len + 1, binds: env.binds }
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

/// spine 栈槽：一次中性应用（icit 随槽携带——quote 的 `f {a}`、solve 的
/// lams、rename 的 App 重建都从这里取）。`len`/`base` 支撑流式右链 quote。
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
        self.stack.push(Entry { f, a, icit, len, base });
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
    /// L04：实参带 icit（force 的 spine 重建、solve 的 lams、rename 的
    /// App 重建都要）。
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
    /// 返回 (meta 号, 逆应用序实参带 icit)。要求调用方先 force。
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

/// metacontext 条目（与参考版同构；解是 bump 内的打包值）。
pub(crate) enum MetaEntry {
    Solved(V),
    Unsolved,
}

/// `vMeta` 的打包版：已解给解值，未解给 Meta 立即数。
#[inline]
fn meta_val_of(metas: &[MetaEntry], m: u32) -> V {
    match &metas[m as usize] {
        MetaEntry::Solved(v) => *v,
        MetaEntry::Unsolved => v_meta(m),
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
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol) => v = *sol,
                MetaEntry::Unsolved => return v,
            },
            2 => {
                let h = v_spine_of(v);
                let hd = spine.spine_head(h);
                if v_tag(hd) != 5 {
                    return v; // 刚性链
                }
                let m = v_meta_of(hd);
                match &metas[m as usize] {
                    MetaEntry::Unsolved => return v,
                    MetaEntry::Solved(sol) => {
                        // 把解应用到全部实参（应用序 = 收集序的逆序）；
                        // 应用可能 β（解是闭包）——cl 式 eval
                        let mut args: Vec<(V, Icit)> = Vec::new();
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

// eval（双栈迭代 + 右链快速路径 + InsertedMeta 实参应用）
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
    /// vals 顶是 `vAppBDs` 的当前值；沿 (env, bds) 平行走完剩余槽位
    /// （外层先应用——上游 `vAppBDs` 同款，icit 硬编码 Expl）。
    AppBds(Env<'a>, Option<&'a BdCons<'a>>),
    /// vals 顶两个（先 base 后实参）：把实参应用上去（Clo → β；其它 →
    /// spine.push，icit = Expl）。`AppBds` 的单个实参应用步。
    AppBdsOne(V),
}

/// 双栈迭代 eval（L03 版 + icit 穿线）。右链下降遇 Var 头（值非闭包）时，
/// 头值进 `vals`、该应用的 icit 进 `icits` 侧栈；`ChainWrap` 折叠时成对
/// 弹出（`Vec::new()` 起步的侧栈在无右链路径上零分配）。
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
                let c = bump.alloc(CloCell { name, icit: *icit, env, body });
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
            W::Tm(Tm::InsertedMeta(m, bds), env) => {
                vals.push(meta_val_of(metas, *m));
                work.push(W::AppBds(env, *bds));
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
                let cell = bump.alloc(PiCell { name, icit, dom, env, body: cod });
                vals.push(v_pi(cell));
            }
            W::AppBds(env, bds) => match bds {
                None => {
                    // 与 reference 的 (None, None) 对齐：bds 先行耗尽
                    debug_assert!(env.binds.is_none() && env.flat_len == 0);
                }
                Some(b) => {
                    // 内层绑定 = 链头；链耗尽后走平坦 def 区域末端。先跑
                    // 余下槽位（外层），再应用本槽（内层最后应用）
                    let (arg, rest) = if let Some(e) = env.binds {
                        (
                            if b.bound { Some(e.val) } else { None },
                            Env { binds: e.next, ..env },
                        )
                    } else if env.flat_len > 0 {
                        let v = defs[(env.flat_base + env.flat_len - 1) as usize];
                        (
                            if b.bound { Some(v) } else { None },
                            Env { flat_len: env.flat_len - 1, ..env },
                        )
                    } else {
                        panic!("impossible") // env 与 bds 错位
                    };
                    if let Some(a) = arg {
                        work.push(W::AppBdsOne(a));
                    }
                    work.push(W::AppBds(rest, b.next));
                }
            },
            W::AppBdsOne(arg) => {
                let v = vals.pop().expect("eval 栈：AppBdsOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let env = env_ext(bump, c.env, arg);
                    work.push(W::Tm(c.body, env));
                } else {
                    vals.push(spine.push(v, arg, Icit::Expl));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；flex 头共享 ?m 节点）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01；L04 的 App 节点带
/// 槽位 icit（共享头链按 `spine.stack[i].icit`，恢复点取悬挂槽位的 icit）。
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

/// 任务栈 quote（L03 版 + icit 穿线）。
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
                        if let Some(t) =
                            memo.as_deref_mut().and_then(|m| m.get(&(v.0, level)))
                        {
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
                        if let Some(t) =
                            memo.as_deref_mut().and_then(|m| m.get(&(v.0, level)))
                        {
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
                        if let Some(t) =
                            memo.as_deref_mut().and_then(|m| m.get(&(v.0, level)))
                        {
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
                                0 => Some(&*bump.alloc(Tm::Var(level - v_lvl_of(f0) - 1))),
                                // flex 链头：未解 meta 立即数（已解的在
                                // force 里早已展开），共享单一 ?m 节点
                                5 => Some(&*bump.alloc(Tm::Meta(v_meta_of(f0)))),
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
                let m = memo.as_deref_mut().expect("quote 栈：MemoStore 缺 memo 表");
                let t = done.pop().expect("quote 栈：MemoStore 缺结果");
                m.insert((key, level), t);
                done.push(t);
            }
            QJob::ChainRun { level, next, end, f0, idx_node, prev } => {
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

// unify（工作表迭代 + force 前置 + 模式求解 + 判等记忆化）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L04_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("L04_NO_CONV_MEMO").is_ok_and(|v| v != "0"),
        )
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

/// unification：结构比较 + 模式求解，工作表迭代。分派次序与参考版一致：
/// λ 情形（eta 按 λ 一侧的 icit 应用）→ U → Π（**icit 相等**）→ 同头中性
/// （实参 icit 不比）→ 求解。判等记忆化同 L03。
fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    let mut memo: rustc_hash::FxHashSet<(u64, u64)> = rustc_hash::FxHashSet::default();
    let mut stack: Vec<UItem<'a>> = Vec::new();
    // 实参收集草稿：跨 Pair 复用（clear 保容量），热路径上零分配
    let mut scratch1: Vec<(V, Icit)> = Vec::new();
    let mut scratch2: Vec<(V, Icit)> = Vec::new();
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

            // Π：icit 相等才比（上游 `VPi x i a b, VPi x' i' a' b' | i == i'`；
            // 失配即刚性不等，不入任何屏障）；先比定义域，再惰性 eval 两侧
            // 余定义域
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

            // 同头中性：逐对比较实参（应用序；收集是逆序，压栈倒回）。
            // **实参 icit 不比**（类型已定，上游 Unification.hs 的注释同款）。
            (2, 2) => {
                let h1 = v_spine_of(t);
                let h2 = v_spine_of(u);
                let hd1 = spine.spine_head(h1);
                let hd2 = spine.spine_head(h2);
                // 求解仅限**异头**且一侧头是未解 flex（eta 积参形态）；同号
                // flex-flex 必须落到底下逐实参比较（solve 的 occurs check
                // 对同号必败——L03 e541de0 同款修复，理由见其注释）。
                if hd1.0 != hd2.0 && (v_tag(hd1) == 5 || v_tag(hd2) == 5) {
                    let mut args = std::mem::take(&mut scratch1);
                    args.clear();
                    let solved = if let Some(m) = spine.flex_of(t, &mut args) {
                        solve(bump, spine, work, vals, icits, defs, metas, l, m, &args, u)
                    } else {
                        let mut args = std::mem::take(&mut scratch2);
                        args.clear();
                        match spine.flex_of(u, &mut args) {
                            Some(m) => {
                                solve(bump, spine, work, vals, icits, defs, metas, l, m, &args, t)
                            }
                            None => false,
                        }
                    };
                    scratch1 = args;
                    if solved {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                if hd1.0 != hd2.0 {
                    return false;
                }
                // 注：L03 此处有「连续链长度 fail-fast」（len 不同即不等）。
                // L04 移除：`push` 的 len 延展启发式（实参是 spine 句柄 ⇒ 链
                // 延长）无法区分「实参是本链的 partial（ChainWrap 惯例）」与
                // 「实参恰好是另一个中性应用」——`B (?m …)` 这类**中性头应用
                // 到中性实参**的形态（隐式插入大量制造它）会让 len 虚增，
                // fail-fast 在两链真实应用数相同时误判不等（comp 用例实测）。
                // 真实的长度失配由下方内联环兜底：partial-头 对 经工作表
                // 派发后必败，结论不变。
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                // 内联环（L02 conv 冠军配方）：沿 `.a` 同步下走，f 位相等
                // 直接跳过（icit 不参与），只有真正待比的子对才入工作表。
                let mut i1 = h1;
                let mut i2 = h2;
                loop {
                    let (f1, a1) = {
                        let e = &spine.stack[i1];
                        (e.f, e.a)
                    };
                    let (f2, a2) = {
                        let e = &spine.stack[i2];
                        (e.f, e.a)
                    };
                    if f1.0 != f2.0 {
                        stack.push(UItem::Pair(l, f1, f2));
                    }
                    if v_tag(a1) == 2 && v_tag(a2) == 2 {
                        if a1.0 == a2.0 {
                            break; // 剩余 spine 同句柄：位相等，整段后缀相等
                        }
                        i1 = v_spine_of(a1);
                        i2 = v_spine_of(a2);
                    } else {
                        if a1.0 != a2.0 {
                            stack.push(UItem::Pair(l, a1, a2));
                        }
                        break;
                    }
                }
            }

            // 求解：一侧是未解 flex；solve 成功即判等完成，直接入表。
            _ => {
                let mut args = std::mem::take(&mut scratch1);
                args.clear();
                let solved = if let Some(m) = spine.flex_of(t, &mut args) {
                    solve(bump, spine, work, vals, icits, defs, metas, l, m, &args, u)
                } else {
                    match spine.flex_of(u, &mut args) {
                        Some(m) => solve(bump, spine, work, vals, icits, defs, metas, l, m, &args, t),
                        None => false,
                    }
                };
                scratch1 = args;
                if solved {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false; // 刚性失配 / 病态混杂
            }
        }
    }
    true
}

// solve（invert + rename + lams，全迭代）
// --------------------------------------------------------------------------------

/// 求解：`Γ ⊢ ?m args ≡ rhs` → `?m := λ x1…xn. rhs[args⁻¹]`。
/// 失败即不改 metacontext（invert/rename 完成前不写表）。实参带 icit
/// （lams 用）。
fn solve<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    gamma: u32,
    m: u32,
    args: &[(V, Icit)], // 逆应用序（spine 收集器的输出）
    rhs: V,
) -> bool {
    // invert：实参（应用序）逐个 force 成刚性变量，赋解域下标；
    // 重复/非变量即非模式，失败（icit 不参与——上游 invert 丢弃之）
    let dom = args.len() as u32;
    let mut ren: Vec<Option<u32>> = vec![None; gamma as usize];
    for (i, &(a, _)) in args.iter().rev().enumerate() {
        let f = force(bump, spine, work, vals, icits, defs, metas, a);
        if v_tag(f) != 0 {
            return false;
        }
        let x = v_lvl_of(f) as usize;
        if x >= gamma as usize || ren[x].is_some() {
            return false;
        }
        ren[x] = Some(i as u32);
    }
    // rename（任务栈；occurs/scope check 在这里）
    let Some(tm) =
        rename_iter(bump, spine, work, vals, icits, defs, &mut ren, metas, m, dom, gamma, rhs)
    else {
        return false;
    };
    // 包 λ 后空环境求值，写表（icit 取收集序 = 上游 reverse 后的次序）
    let lams_tm = lams(bump, args, tm);
    let sol = eval_iter(bump, spine, work, vals, icits, defs, metas, EMPTY_ENV, lams_tm);
    metas[m as usize] = MetaEntry::Solved(sol);
    true
}

/// rename 任务。icit 记账：**只有 `spine_case` 预装载** `done_icits`（按
/// 实参完成序），组合器与 Ren 的直接情形都不碰它——合并结果压 `done`
/// 时不带 icit，配对只发生在 `SpineFold` 弹出时（LIFO 对齐）。
enum RJob<'a> {
    /// 引一个值到解域（产生一个 Tm 到 done）。
    Ren { dom: u32, cod: u32, v: V },
    /// 实参（逆应用序）已由其上任务引完，头是 head_tm，折叠 App
    /// （每个 App 的 icit 从平行 done_icits 栈取）。
    SpineFold { head_tm: &'a Tm<'a>, n: u32 },
    /// done 栈顶是体，包 Lam（icit 随闭包携带）。
    Lam1(&'a str, Icit),
    /// done 栈顶两个（先 cod 后 dom），合 Pi（icit 随 PiCell 携带）。
    Pi2(&'a PiCell<'a>),
}

/// partial renaming 的迭代版（L03 版 + icit 穿线；`ren` 单调插入无需回溯，
/// 论证见 L03 readme）。
fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    ren: &mut Vec<Option<u32>>,
    metas: &[MetaEntry],
    target_m: u32,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
    let mut tasks: Vec<RJob<'a>> = vec![RJob::Ren { dom: dom0, cod: cod0, v: v0 }];
    let mut done: Vec<&'a Tm<'a>> = Vec::new();
    // SpineFold 的实参 icit 预装载栈：spine_case 按实参完成序压入
    //（首个应用的实参最先进栈底），SpineFold 成对弹出。组合器不触碰。
    let mut done_icits: Vec<Icit> = Vec::new();
    // 实参收集 / 折叠草稿：跨任务复用（clear 保容量），热路径零分配
    let mut args: Vec<(V, Icit)> = Vec::new();
    let mut popped: Vec<&'a Tm<'a>> = Vec::new();
    // 派发辅助：spine 头分派（head_tm 就绪后按实参数压子任务；SpineFold
    // 先压——LIFO 保证实参任务先跑完，组合器最后执行；icit 预装载在
    // Rens 之前——嵌套 spine 的装载/弹出各自成对（LIFO））
    macro_rules! spine_case {
        ($dom:expr, $cod:expr, $h:expr, $head_tm:expr, $tasks:expr) => {{
            args.clear();
            spine.collect_args($h, &mut args);
            // 先压组合器（后执行）；args 逆应用序（h.a 先）→ 正序压，
            // 则 a1 的 Ren 最后压、最先弹（应用序先执行）
            $tasks.push(RJob::SpineFold { head_tm: $head_tm, n: args.len() as u32 });
            // icit 预装载：完成序 = 应用序 = args 逆序（收集序的头是
            // 最后应用的实参，最后完成）
            for &(_, i) in args.iter().rev() {
                done_icits.push(i);
            }
            for &(a, _) in args.iter() {
                $tasks.push(RJob::Ren { dom: $dom, cod: $cod, v: a });
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
                        if m == target_m {
                            return None; // occurs check
                        }
                        done.push(bump.alloc(Tm::Meta(m)));
                    }
                    0 => {
                        let x = v_lvl_of(v) as usize;
                        // scope check（x 不在 spine 映射里）
                        let Some(xp) = ren.get(x).and_then(|o| *o) else {
                            return None;
                        };
                        done.push(bump.alloc(Tm::Var(dom - xp - 1)));
                    }
                    2 => {
                        let h = v_spine_of(v);
                        let hd = spine.spine_head(h);
                        match v_tag(hd) {
                            5 => {
                                let m = v_meta_of(hd);
                                if m == target_m {
                                    return None; // occurs check
                                }
                                let head_tm = bump.alloc(Tm::Meta(m));
                                spine_case!(dom, cod, h, head_tm, tasks);
                            }
                            _ => {
                                let x = v_lvl_of(hd) as usize;
                                let Some(xp) = ren.get(x).and_then(|o| *o) else {
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
                        // lift：binder 槽 (cod → dom)，单调插入
                        let idx = cod as usize;
                        if idx >= ren.len() {
                            ren.resize(idx + 1, None);
                        }
                        ren[idx] = Some(dom);
                        tasks.push(RJob::Lam1(c.name, c.icit));
                        tasks.push(RJob::Ren { dom: dom + 1, cod: cod + 1, v: bv });
                    }
                    4 => {
                        let cell = v_pi_of(v);
                        let bv = {
                            let env = env_ext(bump, cell.env, v_lvl(cod));
                            eval_iter(bump, spine, work, vals, icits, defs, metas, env, cell.body)
                        };
                        // lift（同 Lam）
                        let idx = cod as usize;
                        if idx >= ren.len() {
                            ren.resize(idx + 1, None);
                        }
                        ren[idx] = Some(dom);
                        tasks.push(RJob::Pi2(cell));
                        tasks.push(RJob::Ren { dom: dom + 1, cod: cod + 1, v: bv });
                        tasks.push(RJob::Ren { dom, cod, v: cell.dom });
                    }
                    3 => done.push(bump.alloc(Tm::U)),
                    _ => return None, // 病态（Π/U 被应用等）
                }
            }
            RJob::SpineFold { head_tm, n } => {
                // 实参任务已完成：done 栈顶是最后完成的实参（应用序最后
                // 一位 = 收集序第一位）。done 与 done_icits 成对弹出后
                // zip 反序折叠（内层实参先应用于 head）。
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

/// `λ x1 x2. … body`（icit 取 args 收集序——头 = 最后应用的实参，与参考版
/// `sp.iter()` 及上游 `reverse $ map snd sp` 一致；bump 分配，名字只服务
/// pretty）。
fn lams<'a>(bump: &'a Bump, args: &[(V, Icit)], body: &'a Tm<'a>) -> &'a Tm<'a> {
    let mut t = body;
    for i in (0..args.len()).rev() {
        let name = bump.alloc_str(&format!("x{}", i + 1));
        t = bump.alloc(Tm::Lam(name, args[i].1, t));
    }
    t
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 稳态复用机（L03 版 + L04 的插入机制与 inserted-binder 策略）。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。**只收源码
    /// binder**（bind/define）——inserted binder 不入表（对源码名不可见，
    /// 等价于参考版线性扫描跳过 `NameOrigin::Inserted`）。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。`Cxt.mark` 记各上下文的
    /// trail 长度，退出即截断。new_binder 不留轨迹、mark 不动。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
}

const PI_NAME: &str = "x"; // infer App 非 Π 分支合成的闭包名（只服务 pretty）

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine { stack: Vec::with_capacity(4096) },
            vals: Vec::with_capacity(4096),
            defs: Vec::with_capacity(4096),
            metas: Vec::new(),
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
    /// 名字表 + 撤销轨迹四同步。
    fn bind_name<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, x: &str, ty: V) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons { name: bump.alloc_str(x), ty, source: true, next: cxt.types })),
            bds: Some(bump.alloc(BdCons { bound: true, next: cxt.bds })),
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            pos: cxt.pos,
        }
    }

    /// Extend Cxt with an inserted implicit binder（L04 新增）：**不入名字表**
    /// （对源码名不可见）、trail 不动、mark 不变——源码名字穿透它解析到
    /// 外层绑定，与参考版 `NameOrigin::Inserted` 过滤同语义。
    fn new_binder<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, x: &str, ty: V) -> Cxt<'a> {
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
            bds: Some(bump.alloc(BdCons { bound: true, next: cxt.bds })),
            lvl: cxt.lvl + 1,
            mark: cxt.mark,
            pos: cxt.pos,
        }
    }

    /// Extend Cxt with a definition（名字解析版，同 [`Machine::bind_name`]）。
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        x: &str,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext_defs(&mut self.defs, cxt.env, val);
        Cxt {
            env,
            types: Some(bump.alloc(TCons { name: bump.alloc_str(x), ty, source: true, next: cxt.types })),
            bds: Some(bump.alloc(BdCons { bound: false, next: cxt.bds })),
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

    /// 挂新洞：metacontext 追加未解条目，产出 `InsertedMeta m bds`。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, bds: Option<&'a BdCons<'a>>) -> &'a Tm<'a> {
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved);
        bump.alloc(Tm::InsertedMeta(m, bds))
    }

    fn eval<'a>(&mut self, bump: &'a Bump, env: Env, tm: &'a Tm<'a>) -> V {
        eval_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
            &mut Vec::new(),
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
            &mut Vec::new(),
            &mut self.defs,
            &self.metas,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（同 L03：表随本次调用新建，绝不跨 reset 持有）。
    fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let mut memo: QuoteMemo<'a> = FxHashMap::default();
        quote_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            &mut Vec::new(),
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
            &mut Vec::new(),
            &mut self.defs,
            &mut self.metas,
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

    // 隐式插入（L04 新增；上游 Elaboration.hs 的 insert 族）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, t: &'a Tm<'a>, va: V) -> (&'a Tm<'a>, V) {
        let va = force(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
            &mut Vec::new(),
            &mut self.defs,
            &self.metas,
            va,
        );
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt.bds);
            let mv = self.eval(bump, cxt.env, m);
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
    /// 耗尽仍无匹配 → `NoNamedImplicitArg`。
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
                let m = self.fresh_meta(bump, cxt.bds);
                let mv = self.eval(bump, cxt.env, m);
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

    /// 主 `check`：binder 形态与 Π 匹配（位置 icit 相等 / 命名按 Pi 名 +
    /// 隐式）→ 绑定检查；非 lambda 项（或 icit 失配的 lambda）对隐式 Π →
    /// 补 inserted binder；`RLet` 总可检查；洞直接挂 meta；其余 fall-through
    /// 到 infer + **insert** + unify。
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
            &mut Vec::new(),
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
                    let cxt2 = self.bind_name(bump, cxt, &x.data, p.dom);
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
                    let cxt2 = self.new_binder(bump, cxt, p.name, p.dom);
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
                let cxt2 = self.new_binder(bump, cxt, p.name, p.dom);
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
                let cxt2 = self.define_name(bump, cxt, &x.data, vt, va);
                let u_tm = self.check(bump, cxt2, u, a)?;
                self.unwind_names(mark);
                Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
            }

            // hole：直接以 fresh meta 填充（期望类型暂不约束它）
            Raw::Hole => Ok(self.fresh_meta(bump, cxt.bds)),

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
                Err(report_at(cxt.pos, format!("Name not in scope: {}", x.data)))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())), // U : U rule

            // 定义域挂洞；余定义域闭包住当前环境；体推断后在**扩展后的**
            // 上下文里 insert（上游 `insert cxt'`——meta 的 bds 含本 binder）
            Raw::Lam(x, Either::Icit(i), t) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt.bds);
                let a = self.eval(bump, cxt.env, new_meta);
                let mark = cxt.mark;
                let cxt2 = self.bind_name(bump, cxt, &x.data, a);
                let (t, b) = self.infer(bump, cxt2, t)?;
                let (t, b) = self.insert(bump, cxt2, t, b)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell { name, icit: *i, dom: a, env: cxt.env, body });
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
                    // 合成 binder（PI_NAME）不进名字表：只延伸 bds（L03 同款
                    // 理由——无 Raw 在其下 elaborate，留痕反而遮蔽用户名字）。
                    let new_meta = self.fresh_meta(bump, cxt.bds);
                    let a = self.eval(bump, cxt.env, new_meta);
                    let bds2: Option<&'a BdCons<'a>> =
                        Some(bump.alloc(BdCons { bound: true, next: cxt.bds }));
                    let cod_meta = self.fresh_meta(bump, bds2);
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
                let cxt2 = self.bind_name(bump, cxt, &x.data, va);
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
                let cxt2 = self.define_name(bump, cxt, &x.data, vt, va);
                let (u_tm, uty) = self.infer(bump, cxt2, u)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt.bds);
                let a = self.eval(bump, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt.bds);
                Ok((t, a))
            }
        }
    }

    /// `displayMetas`：metacontext 逐条打印，末尾空行。`elab` 模式用。
    fn display_metas(&mut self, bump: &Bump) -> String {
        let mut out = String::new();
        for m in 0..self.metas.len() {
            let cur = match &self.metas[m] {
                MetaEntry::Unsolved => None,
                MetaEntry::Solved(v) => Some(*v),
            };
            match cur {
                None => out.push_str(&format!("let ?{m} = ?;\n")),
                Some(v) => {
                    let q = self.quote(bump, 0, v);
                    out.push_str(&format!("let ?{m} = {};\n", pretty_tm(0, &[], &export(q))))
                }
            }
        }
        out.push('\n');
        out
    }
}

/// Elaboration 上下文（全 Copy，绑定量在 bump 里）。
#[derive(Clone, Copy)]
struct Cxt<'a> {
    env: Env<'a>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目）。
    types: Option<&'a TCons<'a>>,
    /// fresh meta 抽象的槽位掩码（与 env 平行；`bound = true` 槽位是实参）。
    bds: Option<&'a BdCons<'a>>,
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
        Cxt { env: EMPTY_ENV, types: None, bds: None, lvl: 0, mark: 0, pos }
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

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈，深度无上限；icit
/// 随任务携带），复用参考版的 pretty。
fn export(t: &Tm<'_>) -> CTm {
    use super::BD;
    use super::parser::Icit as PIcit;
    use crate::list::List as CList;
    use CTm as B;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, PIcit),
        Pi2(&'a str, PIcit),
        Let2(&'a str),
        App2(PIcit),
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
            J::Do(Tm::InsertedMeta(m, bds)) => {
                // bds 持久链表 → 参考版的 List<BD>（头 = 最内层）
                let mut vec: Vec<super::BD> = Vec::new();
                let mut cur = *bds;
                while let Some(b) = cur {
                    vec.push(if b.bound { BD::Bound } else { BD::Defined });
                    cur = b.next;
                }
                let mut list: CList<super::BD> = CList::new();
                for b in vec.into_iter().rev() {
                    list = list.prepend(b);
                }
                done.push(B::InsertedMeta(super::MetaVar(*m), list));
            }
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
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
            Tm::InsertedMeta(_, bds) => {
                let mut cur = *bds;
                while let Some(b) = cur {
                    n += 1;
                    cur = b.next;
                }
            }
        }
    }
    n
}

/// A/B 实验开关（Raw::Var 名字解析消融）：置 `L04_NO_NAME_MAP=1` 回落为
/// 沿 `types` 链的线性找名（跳过 inserted binder；`=0` 不关闭）。
static NO_NAME_MAP: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("L04_NO_NAME_MAP").is_ok_and(|v| v != "0"),
        )
    });

/// 稳态类型检查器（同 L03：owns 一个反复 `reset` 的 `Bump` 与跨调用复用的
/// [`Machine`]）。
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

// 基准负载生成器（l04bench 共用）
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

/// implicit 2^(k+1)（L04 特色负载）：每层 `id p_{i-1}` 触发一次隐式插入
/// （`{A}` 补 meta）+ 一次 `? := Nat` 求解——insert_t/insert_go/solve 的
/// 主展示负载。
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

/// conv 2^(k+1)：church 之上 `Eq Nat (add p_k zero) p_k = refl Nat p_k`
///（转换检查工作负载；无洞）。
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

    /// EX1（上游 readme 示例套件）：type 模式与参考版逐字节一致
    /// （nf 的 church-100 展开太长，type 即可覆盖判定路径）。
    #[test]
    fn ex1_type_matches_basic() {
        assert_eq!(main_with("type", EX1_SRC), super::super::main_with("type", EX1_SRC));
    }

    #[test]
    fn ex0_elab_matches_basic() {
        assert_eq!(main_with("elab", EX0_SRC), super::super::ex0());
    }

    /// 三模式全量互检的样例束（含隐式特例）——黑盒套件的 assert_parity
    /// 同款，这里先在单元层兜一层。
    #[test]
    fn parity_on_implicit_examples() {
        for src in [
            "let id : {A : U} -> A -> A = \\x. x;\nid U U\n",
            "let const : {A B} -> A -> B -> A = \\x y. x;\nconst {B = U} U U\n",
            "let f : {A : U} -> U = U;\nf {U}\n",
            "let id2 : {A} -> A -> A = \\{A} x. x;\nid2\n",
            "let the : (A : _) -> A -> A = \\_ x. x;\nthe {U} U U\n",
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

    /// implicit 负载：16 层 `id p_{i-1}`（每层一次插入 + 一次求解），判定
    /// 通过且与参考版逐字节一致。（深度受测试线程栈限制：check/infer 与
    /// parser 在 let 链上递归，大规模在 l04bench 的大栈线程下跑。）
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

    /// solve / conv_dup / chain 判定与参考版一致。
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
            assert_eq!(
                t.run("type", &src, &raw),
                super::super::main_with("type", &src),
                "{name} 判定与参考版不一致"
            );
        }
    }

    /// 名字 map 的 shadowing + inserted-binder 不可见性：`\{A} x. x` 的
    /// inserted binder A 不入表，体内 `A` 解析到外层 def。
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
            assert_eq!(main_with("type", src), super::super::main_with("type", src));
        }
    }

    // dup 复制强制负载（quote 记忆化轴）
    // --------------------------------------------------------------------------------

    /// dup 负载的 nf 输出与参考版逐字节一致（双口径）。
    #[test]
    fn dup_nf_matches_basic() {
        for src in [dup_src(4), dup_deep_src(4)] {
            let Some(raw) = super::super::parser::parser(&src, 0) else {
                panic!("parse failed");
            };
            let basic = super::super::main_with("nf", &src);
            let mut t = Tycker::new();
            assert_eq!(t.run("nf", &src, &raw), basic, "memo 默认口径不一致");
            let mut t = Tycker::new();
            assert_eq!(t.run_no_memo("nf", &src, &raw), basic, "非 memo 对照口径不一致");
        }
    }

    /// dup 负载的 nf 节点数：4n+12 / 8n+28（memo 不改逐出现计数）。
    #[test]
    fn dup_node_counts() {
        let n = 1u64 << 11; // k=10 → church 2048
        for (src, expect) in [
            (dup_src(10), 4 * n + 12),
            (dup_deep_src(10), 8 * n + 28),
        ] {
            let Some(raw) = super::super::parser::parser(&src, 0) else {
                panic!("parse failed");
            };
            let mut t = Tycker::new();
            assert_eq!(t.bench_check_nf(&raw), expect, "无 memo 节点数不符");
            let mut t = Tycker::new();
            assert_eq!(t.bench_check_nf_memo(&raw), expect, "memo 节点数不符");
        }
    }

    /// memo 命中的直接证据：`λf. f C C` 的两处 C 共享同一子树指针（DAG）。
    #[test]
    fn dup_memo_shares_forced_subtree() {
        let src = dup_src(3);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        tycker.bump.reset();
        tycker.machine.clear_round();
        let bump = &tycker.bump;
        let Ok((t, _)) = tycker.machine.infer(bump, Cxt::empty(super::super::initial_pos()), &raw)
        else {
            panic!("infer failed");
        };
        let v = tycker.machine.eval(bump, EMPTY_ENV, t);
        let Tm::Lam(_, _, Tm::App(Tm::App(_, c1, _), c2, _)) =
            tycker.machine.quote_memo(bump, 0, v)
        else {
            panic!("形状应为 λf. f C C");
        };
        assert!(
            std::ptr::eq(*c1, *c2),
            "复制分量未共享子树：memo 未命中或键不命中"
        );
        let Tm::Lam(_, _, Tm::App(Tm::App(_, c1, _), c2, _)) =
            tycker.machine.quote(bump, 0, v)
        else {
            panic!("形状应为 λf. f C C");
        };
        assert!(!std::ptr::eq(*c1, *c2), "无 memo 时两处 C 应是独立副本");
    }

    /// memo 表随每次 quote 调用新建：跨轮悬垂键回归测试。
    #[test]
    fn steady_state_memo_reuse() {
        let Some(raw) = super::super::parser::parser(&dup_src(6), 0) else {
            panic!("parse failed");
        };
        let mut steady = Tycker::new();
        let r1 = steady.run("nf", "", &raw);
        let r2 = steady.run("nf", "", &raw);
        let mut fresh = Tycker::new();
        assert_eq!(r1, r2);
        assert_eq!(r1, fresh.run("nf", "", &raw));
        assert_eq!(r1, main_with("nf", &dup_src(6)));
    }
}
