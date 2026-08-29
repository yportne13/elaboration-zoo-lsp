//! L02 核心机（eval / quote / conv / check / infer）的极致性能版：把 L01
//! 调研的冠军配方（`bump_spine_iter`，见 `L01_nbe/readme.md`「怎么选」）
//! 移植到带 Π/let 的带类型核心上。移植的机制（按 L01 消融阶梯的收益排序）：
//!
//! 1. **bump arena**：项、值、环境节点全部 bump 分配（`bumpalo`）——没有
//!    Rc 计数、没有 Box 析构，分配只是指针推进，整块 `Bump` 在一次
//!    elaboration 结束时一起释放。
//! 2. **打包值**：64 位字 [`V`]，tag 塞低 3 位（bump 分配 8 字节对齐）——
//!    比 L01 的 3 个 tag 多出 `U`（立即数）与 `Pi`（bump 单元）两个。
//! 3. **扁平中性 + spine 栈**：中性应用压进 [`Spine`]（`len`/`base` 记账
//!    支撑流式右链），配 Machine 跨调用复用（L01 的 `_ss` 稳态口径）。
//! 4. **流式右链 quote**：连续右链按下标自底向上重建，链头同为同一变量时
//!    `Idx` 节点共享。
//! 5. **迭代化**：eval 双栈（work/vals + `App(变量头, ·)` 右链快速路径）、
//!    quote 任务栈（`ChainRun` 断点续跑）——求值/quote 深度不受进程栈限。
//! 6. **conv 工作表**：beta-eta 转换检查改为 `(level, V, V)` 工作表迭代
//!    （L01 没有 conv；同一「栈即数据」改造），外加**位相等快速路径**：
//!    同一打包字 = 同一分配或同一立即数 → 直接判等。
//!
//! 与参考版（`super`，L03 风格）共用 parser / pretty / 错误显示，输出逐
//! 字节一致（互检测试）。elaboration 直接在本表示上进行：
//! `Raw → check/infer（产出 bump 核心项）→ quote → export → pretty`。
//! 稳态形态是 [`Tycker`]：`Machine` 的 spine/vals 跨调用复用，配每轮
//! `Bump::reset`——LSP 一类长驻进程的真实成本口径。

use bumpalo::Bump;

use super::parser::Raw;
use crate::parser_lib::Span;
use super::{Error, Name, Tm as CTm, Ix};

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
pub(crate) enum Tm<'a> {
    Var(u32),
    Lam(&'a str, &'a Tm<'a>),
    App(&'a Tm<'a>, &'a Tm<'a>),
    U,
    Pi(&'a str, &'a Tm<'a>, &'a Tm<'a>),
    Let(&'a str, &'a Tm<'a>, &'a Tm<'a>, &'a Tm<'a>),
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Lvl(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U`（立即数）、`4=Pi(ptr|4)`。
/// bump 分配 8 字节对齐，指针低 3 位空闲。
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

/// 闭包单元：λ 的名字（只服务 quote 产出的 pretty）+ env + 体。
pub(crate) struct CloCell<'a> {
    name: &'a str,
    env: Option<&'a EnvCons<'a>>,
    body: &'a Tm<'a>,
}

/// Π 值单元：名字 + 定义域值 + 余定义域闭包（内联，一次分配）。
pub(crate) struct PiCell<'a> {
    name: &'a str,
    dom: V,
    env: Option<&'a EnvCons<'a>>,
    body: &'a Tm<'a>,
}

/// 环境节点（bump 内持久链表，头 = 最内层绑定）。
pub(crate) struct EnvCons<'a> {
    val: V,
    next: Option<&'a EnvCons<'a>>,
}

#[inline]
fn nth<'a>(mut env: Option<&'a EnvCons<'a>>, idx: usize) -> V {
    for _ in 0..idx {
        env = env.expect("de Bruijn 越界：闭项不应查空环境").next;
    }
    env.expect("de Bruijn 越界：闭项不应查越深").val
}

/// spine 栈槽：一次中性应用。`len`/`base` 支撑流式右链 quote（连续性引理
/// 见 L01 `bump_spine.rs`：`base + len - 1 == idx` 当且仅当链上下标连续）。
struct Entry {
    f: V,
    a: V,
    len: u32,
    base: u32,
}

/// 求值机持有的扁平中性栈（只增不减，槽位下标即句柄）。
pub(crate) struct Spine {
    stack: Vec<Entry>,
}

impl Spine {
    /// 中性应用 `f a` 压栈，返回句柄值。
    #[inline]
    fn push(&mut self, f: V, a: V) -> V {
        let idx = self.stack.len();
        let (len, base) = if v_tag(a) == 2 {
            let prev = &self.stack[v_spine_of(a)];
            (prev.len + 1, prev.base)
        } else {
            (1, idx as u32)
        };
        self.stack.push(Entry { f, a, len, base });
        v_spine(idx)
    }
}

// eval（双栈迭代 + 右链快速路径）
// --------------------------------------------------------------------------------

/// eval 的 work 栈条目。
enum W<'a> {
    Tm(&'a Tm<'a>, Option<&'a EnvCons<'a>>),
    Apply,
    /// vals 顶上是 base 值，其下 `k` 个是待应用的链头（内层最上）。
    ChainWrap(u32),
    /// vals 顶是 let 绑定的值：弹出压进环境，继续求值体。
    LetBody(&'a Tm<'a>, Option<&'a EnvCons<'a>>),
    /// vals 顶是 Π 定义域值：弹出配余定义域闭包，压 Π 值。
    PiBody(&'a str, &'a Tm<'a>, Option<&'a EnvCons<'a>>),
}

/// 双栈迭代 eval（`bump_spine_iter::eval_iter` 的 L02 扩充：多了 Π/let/U）。
/// `let` 的类型槽不求值（Main.hs 的 `Let x _ t u` 同款），β 归约是尾循环。
/// **右链快速路径**：`App(变量头, ·)` 连续嵌套整条链不占 work 栈；头若
/// 解析出闭包（β 岔路）或复合函数则该层退回通用三推，已收的头由
/// [`W::ChainWrap`] 收拢——语义与逐层 Apply 等价。
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    env0: Option<&'a EnvCons<'a>>,
    tm0: &'a Tm<'a>,
) -> V {
    work.clear();
    vals.clear();
    work.push(W::Tm(tm0, env0));
    while let Some(w) = work.pop() {
        match w {
            W::Tm(Tm::Var(i), env) => vals.push(nth(env, *i as usize)),
            W::Tm(Tm::Lam(name, body), env) => {
                let c = bump.alloc(CloCell { name, env, body });
                vals.push(v_clo(c));
            }
            W::Tm(Tm::U, _) => vals.push(v_u()),
            W::Tm(Tm::Pi(name, dom, cod), env) => {
                work.push(W::PiBody(name, cod, env));
                work.push(W::Tm(dom, env));
            }
            W::Tm(Tm::Let(_, _, t, u), env) => {
                work.push(W::LetBody(u, env));
                work.push(W::Tm(t, env));
            }
            W::Tm(app @ Tm::App(..), env) => {
                // 右链下钻：头为非闭包变量时头值直接进 vals
                let mut tm = app;
                let mut heads: u32 = 0;
                loop {
                    let (f, a) = match tm {
                        Tm::App(f, a) => (f, a),
                        base => {
                            work.push(W::ChainWrap(heads));
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    match f {
                        Tm::Var(i) => {
                            let vf = nth(env, *i as usize);
                            if v_tag(vf) == 1 {
                                // β 岔路：本层退回通用三推（ChainWrap 收拢已收的头）
                                work.push(W::ChainWrap(heads));
                                work.push(W::Apply);
                                work.push(W::Tm(a, env));
                                work.push(W::Tm(f, env));
                                break;
                            }
                            vals.push(vf);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            work.push(W::ChainWrap(heads));
                            work.push(W::Apply);
                            work.push(W::Tm(a, env));
                            work.push(W::Tm(f, env));
                            break;
                        }
                    }
                }
            }
            W::Apply => {
                let va = vals.pop().expect("eval 栈：Apply 缺实参");
                let vf = vals.pop().expect("eval 栈：Apply 缺函数");
                if v_tag(vf) == 1 {
                    // β 归约是尾调用：直接推入体，继续循环
                    let c = v_clo_of(vf);
                    let node = bump.alloc(EnvCons { val: va, next: c.env });
                    work.push(W::Tm(c.body, Some(node)));
                } else {
                    vals.push(spine.push(vf, va));
                }
            }
            W::ChainWrap(k) => {
                let mut v = vals.pop().expect("eval 栈：ChainWrap 缺 base");
                for _ in 0..k {
                    let vf = vals.pop().expect("eval 栈：ChainWrap 缺链头");
                    v = spine.push(vf, v);
                }
                vals.push(v);
            }
            W::LetBody(u, env) => {
                let vt = vals.pop().expect("eval 栈：LetBody 缺绑定值");
                let node = bump.alloc(EnvCons { val: vt, next: env });
                work.push(W::Tm(u, Some(node)));
            }
            W::PiBody(name, cod, env) => {
                let dom = vals.pop().expect("eval 栈：PiBody 缺定义域");
                let cell = bump.alloc(PiCell { name, dom, env, body: cod });
                vals.push(v_pi(cell));
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01 `bump_spine_iter.rs`。
enum QJob<'a> {
    /// 引一个值。
    Q(V, u32),
    /// done 栈顶是体，包一层 Lam（名字随闭包携带）。
    Lam1(&'a str),
    /// done 栈顶两个（先 cod 后 dom），合一个 Pi。
    Pi1(&'a PiCell<'a>),
    /// 先 eval（引出闭包/余定义域的体）再引。
    EvalQ(&'a Tm<'a>, Option<&'a EnvCons<'a>>, u32),
    /// done 栈顶两个（先 f 后 a），合一个 App——二叉 fallback 用。
    App1,
    /// 流式右链：next..=end 逐层 App 自底向上；f 与 f0 同为同一变量时
    /// 用共享 idx 节点，否则挂起（Q 引 f）后续跑。
    ChainRun {
        level: u32,
        next: usize,
        end: usize,
        f0: V,
        idx_node: Option<&'a Tm<'a>>,
        prev: Option<&'a Tm<'a>>,
    },
}

/// 任务栈 quote。`level0` 是起始 quote level（`show_val` 在 `cxt.lvl` 下
/// 引用含自由变量的值时非 0）。EvalQ 强制闭包体时复用调用方的 work/vals
/// 栈（稳态口径为 [`Machine`] 的，一次性口径为新建 Vec）。
#[allow(clippy::too_many_arguments)]
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    level0: u32,
    v0: V,
) -> &'a Tm<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, level0));
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v, level) => match v_tag(v) {
                0 => done.push(bump.alloc(Tm::Var(level - v_lvl_of(v) - 1))),
                1 => {
                    let c = v_clo_of(v);
                    let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
                    tasks.push(QJob::Lam1(c.name));
                    tasks.push(QJob::EvalQ(c.body, Some(node), level + 1));
                }
                3 => done.push(bump.alloc(Tm::U)),
                4 => {
                    let cell = v_pi_of(v);
                    tasks.push(QJob::Pi1(cell));
                    tasks.push(QJob::EvalQ(
                        cell.body,
                        Some(bump.alloc(EnvCons { val: v_lvl(level), next: cell.env })),
                        level + 1,
                    ));
                    tasks.push(QJob::Q(cell.dom, level));
                }
                _ => {
                    // 先拷出标量再继续（后续任务会 push spine，Vec 可能扩容）
                    let h = v_spine_of(v);
                    let (ef, ea, len, base) = {
                        let e = &spine.stack[h];
                        (e.f, e.a, e.len, e.base)
                    };
                    if len > 1 && base as usize + len as usize - 1 == h {
                        // 连续右链：先引 base，再 ChainRun 自底向上扫
                        let f0 = spine.stack[base as usize].f;
                        let idx_node = if v_tag(f0) == 0 {
                            Some(&*bump.alloc(Tm::Var(level - v_lvl_of(f0) - 1)))
                        } else {
                            None
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
                        tasks.push(QJob::App1);
                        tasks.push(QJob::Q(ea, level));
                        tasks.push(QJob::Q(ef, level));
                    }
                }
            },
            QJob::Lam1(name) => {
                let body = done.pop().expect("quote 栈：Lam 缺体");
                done.push(bump.alloc(Tm::Lam(name, body)));
            }
            QJob::Pi1(cell) => {
                let cod = done.pop().expect("quote 栈：Pi 缺余定义域");
                let dom = done.pop().expect("quote 栈：Pi 缺定义域");
                done.push(bump.alloc(Tm::Pi(cell.name, dom, cod)));
            }
            QJob::EvalQ(body, env, level) => {
                let v = eval_iter(bump, spine, work, vals, env, body);
                tasks.push(QJob::Q(v, level));
            }
            QJob::App1 => {
                let a = done.pop().expect("quote 栈：App 缺实参");
                let f = done.pop().expect("quote 栈：App 缺函数");
                done.push(bump.alloc(Tm::App(f, a)));
            }
            QJob::ChainRun { level, next, end, f0, idx_node, prev } => {
                let mut prev = match prev {
                    Some(p) => {
                        // 恢复点：非平凡 f 刚引完在 done 栈顶，合掉一层
                        let f_node = done.pop().expect("quote 栈：链缺函数头");
                        bump.alloc(Tm::App(f_node, p))
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
                            prev = bump.alloc(Tm::App(n, prev));
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

// conv（beta-eta，工作表迭代 + 位相等快速路径）
// --------------------------------------------------------------------------------

/// A/B 实验开关（l02bench 的位相等消融用）：置 `L02_NO_BITEQ=1` 关掉
/// 位相等快速路径，走纯结构比较。
static NO_BITEQ: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L02_NO_BITEQ").is_ok())
    });

/// Beta-eta 转换检查。前提：两个值的类型相同。与 Main.hs 的递归 `conv`
/// 同语义，改成 `(level, V, V)` 工作表——合取式比较天然迭代化，深度不受
/// 进程栈限；**位相等快速路径**：同一打包字 ⇒ 同一分配（闭包/spine 句柄
/// 全局唯一）或同一立即数（Lvl/U）⇒ 同一值， church 链里大量子比较被
/// 一次整数比较剪掉。
fn conv_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let mut stack: Vec<(u32, V, V)> = Vec::new();
    stack.push((l0, t0, u0));
    while let Some((l, t, u)) = stack.pop() {
        if !NO_BITEQ.load(std::sync::atomic::Ordering::Relaxed) && t.0 == u.0 {
            continue; // 位相等：同一值
        }
        match (v_tag(t), v_tag(u)) {
            // eta：λ 与任意值比较，两边都应用到同一个新变量
            (1, 1) => {
                let c1 = v_clo_of(t);
                let c2 = v_clo_of(u);
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c1.env })),
                    c1.body,
                );
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c2.env })),
                    c2.body,
                );
                stack.push((l + 1, vt, vu));
            }
            (1, _) => {
                let c = v_clo_of(t);
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c.env })),
                    c.body,
                );
                let vu = spine.push(u, v_lvl(l));
                stack.push((l + 1, vt, vu));
            }
            (_, 1) => {
                let c = v_clo_of(u);
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c.env })),
                    c.body,
                );
                let vt = spine.push(t, v_lvl(l));
                stack.push((l + 1, vt, vu));
            }

            // Π：比较定义域，再在 binder 实例化下比较余定义域
            (4, 4) => {
                let p = v_pi_of(t);
                let q = v_pi_of(u);
                stack.push((l, p.dom, q.dom));
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: p.env })),
                    p.body,
                );
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: q.env })),
                    q.body,
                );
                stack.push((l + 1, vt, vu));
            }

            // 中性：头相同则逐对比较 spine（二叉拆分，位相等剪枝）
            (2, 2) => {
                let i1 = v_spine_of(t);
                let i2 = v_spine_of(u);
                let (f1, a1) = {
                    let e = &spine.stack[i1];
                    (e.f, e.a)
                };
                let (f2, a2) = {
                    let e = &spine.stack[i2];
                    (e.f, e.a)
                };
                stack.push((l, f1, f2));
                stack.push((l, a1, a2));
            }

            // U == U（位相等通常已覆盖；防御性保留，避免依赖快速路径）
            (3, 3) => {}

            // 两个变量：位相等开启时到达此处必为不同 level（Lvl 编码单射）；
            // L02_NO_BITEQ 消融模式下由此处的 level 比较兜底。
            (0, 0) => {
                if v_lvl_of(t) == v_lvl_of(u) {
                    continue;
                }
                return false;
            }

            // (0,2)/(3,*) 等混杂：病态或必不等
            _ => return false,
        }
    }
    true
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 稳态复用机：spine 与 vals 两个无生命周期的大栈跨调用复用（clear 保
/// 容量），配 [`Tycker`] 每轮 `Bump::reset` 即稳态近零分配（L01 `_ss` 口径）。
/// 带生命周期的小栈（work/tasks/done）每调用新建，避免 struct 持 `'a`
/// 跨 `Bump::reset` 的借用冲突。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
}

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine { stack: Vec::with_capacity(4096) },
            vals: Vec::with_capacity(4096),
        }
    }

    fn eval<'a>(&mut self, bump: &'a Bump, env: Option<&'a EnvCons<'a>>, tm: &'a Tm<'a>) -> V {
        eval_iter(bump, &mut self.spine, &mut Vec::new(), &mut self.vals, env, tm)
    }

    fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        quote_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            level,
            v,
        )
    }

    fn conv(&mut self, bump: &Bump, l: u32, t: V, u: V) -> bool {
        conv_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut self.vals,
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

    /// 参考 Main.hs 的 `check`：`RLam` 只在 `VPi` 下可检查，`RLet` 总可检查，
    /// 其余 fall-through 到 infer + conv。
    fn check<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, t: &Raw, a: V) -> Result<&'a Tm<'a>, Error> {
        match t {
            Raw::SrcPos(pos, t) => {
                let mut cxt = cxt;
                cxt.pos = *pos;
                self.check(bump, cxt, t, a)
            }

            Raw::Lam(x, t) if v_tag(a) == 4 => {
                let p = v_pi_of(a);
                let name: &'a str = bump.alloc_str(&x.data);
                let body_a = self.eval(
                    bump,
                    Some(bump.alloc(EnvCons { val: v_lvl(cxt.lvl), next: p.env })),
                    p.body,
                );
                let body = self.check(bump, cxt.bind(bump, name, p.dom), t, body_a)?;
                Ok(bump.alloc(Tm::Lam(name, body)))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check(bump, cxt, a_ty, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t, va)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let u_tm = self.check(bump, cxt.define(bump, name, vt, va), u, a)?;
                Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
            }

            _ => {
                let (t, tty) = self.infer(bump, cxt, t)?;
                if !self.conv(bump, cxt.lvl, tty, a) {
                    return Err(super::report_at(
                        cxt.pos,
                        format!(
                            "type mismatch\n\nexpected type:\n\n  {}\n\ninferred type:\n\n  {}\n",
                            self.show_val(bump, cxt, a),
                            self.show_val(bump, cxt, tty)
                        ),
                    ));
                }
                Ok(t)
            }
        }
    }

    /// 参考 Main.hs 的 `infer`。
    fn infer<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, t: &Raw) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            Raw::SrcPos(pos, t) => {
                let mut cxt = cxt;
                cxt.pos = *pos;
                self.infer(bump, cxt, t)
            }

            Raw::Var(x) => {
                let mut i = 0u32;
                let mut tys = cxt.types;
                while let Some(tc) = tys {
                    if tc.name == x.data {
                        return Ok((bump.alloc(Tm::Var(i)), tc.ty));
                    }
                    i += 1;
                    tys = tc.next;
                }
                Err(super::report_at(
                    cxt.pos,
                    format!("variable out of scope: {}", x.data),
                ))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())), // U : U rule

            Raw::App(t, u) => {
                let (t, tty) = self.infer(bump, cxt, t)?;
                if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    let u = self.check(bump, cxt, u, p.dom)?;
                    let arg = self.eval(bump, cxt.env, u);
                    // t u : B[x |-> u]
                    let ty = self.eval(
                        bump,
                        Some(bump.alloc(EnvCons { val: arg, next: p.env })),
                        p.body,
                    );
                    Ok((bump.alloc(Tm::App(t, u)), ty))
                } else {
                    Err(super::report_at(
                        cxt.pos,
                        format!(
                            "Expected a function type, instead inferred:\n\n  {}\n",
                            self.show_val(bump, cxt, tty)
                        ),
                    ))
                }
            }

            Raw::Lam(..) => Err(super::report_at(
                cxt.pos,
                "Can't infer type for lambda expression".to_string(),
            )),

            Raw::Pi(x, a, b) => {
                let a_tm = self.check(bump, cxt, a, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let b_tm = self.check(bump, cxt.bind(bump, name, va), b, v_u())?;
                Ok((bump.alloc(Tm::Pi(name, a_tm, b_tm)), v_u()))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check(bump, cxt, a_ty, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t, va)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let (u_tm, uty) = self.infer(bump, cxt.define(bump, name, vt, va), u)?;
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }
        }
    }
}

/// Elaboration 上下文（参考 Main.hs 的 Cxt；全部 Copy，绑定量在 bump 里）。
#[derive(Clone, Copy)]
struct Cxt<'a> {
    env: Option<&'a EnvCons<'a>>,
    /// type of every variable in scope（头 = 最内层，服务名字查找与报错）
    types: Option<&'a TCons<'a>>,
    lvl: u32,
    pos: Span<()>,
}

/// scope 里的一项：名字 + 类型值。
struct TCons<'a> {
    name: &'a str,
    ty: V,
    next: Option<&'a TCons<'a>>,
}

impl<'a> Cxt<'a> {
    fn empty(pos: Span<()>) -> Self {
        Cxt { env: None, types: None, lvl: 0, pos }
    }

    /// Extend Cxt with a bound variable.
    fn bind(self, bump: &'a Bump, x: &'a str, a: V) -> Cxt<'a> {
        Cxt {
            env: Some(bump.alloc(EnvCons { val: v_lvl(self.lvl), next: self.env })),
            types: Some(bump.alloc(TCons { name: x, ty: a, next: self.types })),
            lvl: self.lvl + 1,
            pos: self.pos,
        }
    }

    /// Extend Cxt with a definition.
    fn define(self, bump: &'a Bump, x: &'a str, t: V, a: V) -> Cxt<'a> {
        Cxt {
            env: Some(bump.alloc(EnvCons { val: t, next: self.env })),
            types: Some(bump.alloc(TCons { name: x, ty: a, next: self.types })),
            lvl: self.lvl + 1,
            pos: self.pos,
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

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈，深度无上限），
/// 复用参考版的 pretty。名字只保留 data（pretty 不用 span）。
fn export(t: &Tm<'_>) -> CTm {
    use CTm as B;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str),
        Pi2(&'a str),
        Let2(&'a str),
        App2,
    }
    fn name(x: &str) -> Name {
        Name {
            data: x.to_owned(),
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
            J::Do(Tm::Lam(x, b)) => {
                tasks.push(J::Lam2(x));
                tasks.push(J::Do(b));
            }
            J::Do(Tm::App(f, a)) => {
                tasks.push(J::App2);
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            }
            J::Do(Tm::U) => done.push(B::U),
            J::Do(Tm::Pi(x, a, b)) => {
                tasks.push(J::Pi2(x));
                tasks.push(J::Do(b));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Let(x, a, t, u)) => {
                tasks.push(J::Let2(x));
                tasks.push(J::Do(u));
                tasks.push(J::Do(t));
                tasks.push(J::Do(a));
            }
            J::Lam2(x) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(B::Lam(name(x), Box::new(b)));
            }
            J::Pi2(x) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(B::Pi(name(x), Box::new(dom), Box::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(B::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2 => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(B::App(Box::new(f), Box::new(a)));
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
            Tm::Var(_) | Tm::U => {}
            Tm::Lam(_, b) => stack.push(b),
            Tm::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::Pi(_, a, b) => {
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

/// 稳态类型检查器：owns 一个反复 `reset` 的 `Bump` 与跨调用复用的
/// [`Machine`]。`bump.reset` 不跑析构（bumpalo 语义），spine/vals 里的
/// 旧指针字在下轮 eval/quote 开头即被 clear，悬垂无碍。
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

    /// Main.hs 的 `mainWith` 等价物（`nf` / `type`；`--help` 由参考版处理）。
    pub(crate) fn run(&mut self, mode: &str, file: &str, raw: &Raw) -> String {
        self.bump.reset();
        let bump = &self.bump;
        let cxt = Cxt::empty(super::initial_pos());
        match self.machine.infer(bump, cxt, raw) {
            Err(err) => super::display_error(file, &err),
            Ok((t, a)) => match mode {
                "nf" => {
                    let v = self.machine.eval(bump, None, t);
                    let n = self.machine.quote(bump, 0, v);
                    let ty = self.machine.quote(bump, 0, a);
                    format!(
                        "{}\n  :\n{}\n",
                        super::pretty_tm(0, &[], &export(n)),
                        super::pretty_tm(0, &[], &export(ty))
                    )
                }
                _ => format!(
                    "{}\n",
                    super::pretty_tm(0, &[], &export(self.machine.quote(bump, 0, a)))
                ),
            },
        }
    }

    /// 基准口径（bench 用）：仅 check（conv 工作负载的转换检查发生在 check 里）。
    pub(crate) fn bench_check(&mut self, raw: &Raw) -> bool {
        self.bump.reset();
        let bump = &self.bump;
        self.machine
            .infer(bump, Cxt::empty(super::initial_pos()), raw)
            .is_ok()
    }

    /// 基准口径：check + nf（quote），返回结果树节点数（工作量佐证）。
    pub(crate) fn bench_check_nf(&mut self, raw: &Raw) -> u64 {
        self.bump.reset();
        let bump = &self.bump;
        match self.machine.infer(bump, Cxt::empty(super::initial_pos()), raw) {
            Err(_) => 0,
            Ok((t, _)) => {
                let v = self.machine.eval(bump, None, t);
                let n = self.machine.quote(bump, 0, v);
                tm_size(n)
            }
        }
    }
}

/// 一次性口径入口（与参考版 `main_with` 同签名同输出）。
pub(crate) fn main_with(mode: &str, file: &str) -> String {
    match mode {
        "nf" | "type" => {}
        _ => return super::HELP_MSG.to_string(),
    }
    let Some(raw) = super::parser::parser(file, 0) else {
        return "parse error\n".to_string();
    };
    let mut tycker = Tycker::new();
    tycker.run(mode, file, &raw)
}

// 基准负载生成器（l02bench 共用）
// --------------------------------------------------------------------------------

/// church 2^(k+1)：k 次 ×2 翻倍（`add p p`）的 let 链，末尾 `p_k`
/// （nf 工作负载）。
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

/// conv 2^(k+1)：church 2^(k+1) 之上加 `Eq Nat (add p_k zero) p_k = refl Nat p_k`
/// ——check 内 conv 强制 `(add p_k zero)` 与 `p_k` 完整展开后结构比较
/// （转换检查工作负载）。
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

#[cfg(test)]
mod tests {
    use super::super::{church_nf, EX0_SRC, EX1_SRC, EX2_SRC};
    use super::*;

    #[test]
    fn ex1_nf_and_type() {
        assert_eq!(
            main_with("nf", EX1_SRC),
            "λ A B x y. x\n  :\n(A : U)(B : U) → A → B → A\n"
        );
        assert_eq!(
            main_with("type", EX1_SRC),
            "(A : U)(B : U) → A → B → A\n"
        );
    }

    #[test]
    fn ex2_church_thousand() {
        assert_eq!(
            main_with("nf", EX2_SRC),
            format!("{}  :\n(N : U) → (N → N) → N → N\n", church_nf(1000))
        );
    }

    #[test]
    fn ex0_error_matches_basic_display() {
        assert_eq!(main_with("nf", EX0_SRC), super::super::ex0());
    }

    /// 深度无上限：church 65536（15 次 ×2 翻倍）的 check+nf 在默认栈上跑通。
    #[test]
    fn deep_church_65536() {
        let src = church_src(15);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        let size = tycker.bench_check_nf(&raw);
        // λ N s z. s^65536 z：3 个 Lam + 65536 个 App + 65537 个 Var + 1 U? U 不在 nf 里
        assert_eq!(size, 3 + 65536 + 65537, "nf node count");
    }

    /// conv 工作负载：`Eq Nat (add big zero) big` 的检查在 check 内强制两侧
    /// 完整展开后结构比较（16384 链），迭代 conv 深度无上限。
    #[test]
    fn conv_stress_16384() {
        let src = conv_src(13);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        assert!(tycker.bench_check(&raw));
    }

    /// 稳态复用正确性：同一 Tycker 连续多轮（Bump::reset + Machine 复用），
    /// 输出与每轮新建的 Tycker 一致。
    #[test]
    fn steady_state_reuse() {
        let Some(raw) = super::super::parser::parser(EX2_SRC, 0) else {
            panic!("parse failed");
        };
        let mut steady = Tycker::new();
        let r1 = steady.run("nf", EX2_SRC, &raw);
        let r2 = steady.run("nf", EX2_SRC, &raw);
        let fresh = main_with("nf", EX2_SRC);
        assert_eq!(r1, r2);
        assert_eq!(r1, fresh);
    }

    /// 报错路径（错误消息 + 位置）与参考版逐字节一致。
    #[test]
    fn conv_failure_message() {
        let src = "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
                   let two : Nat = \\N s z. s (s z);\n\
                   let three : Nat = \\N s z. s (s (s z));\n\
                   let eqTest : Nat = two;\n\
                   let bad : Nat = three;\n\
                   bad\n";
        assert_eq!(main_with("nf", src), super::super::main_with("nf", src));
        // 类型不匹配的消息内容
        let mismatch = "let f : U -> U = \\x. x;\nlet bad : U -> U -> U = f;\nbad\n";
        let out = main_with("nf", mismatch);
        assert!(out.contains("type mismatch"), "{out}");
        assert_eq!(out, super::super::main_with("nf", mismatch));
    }
}
