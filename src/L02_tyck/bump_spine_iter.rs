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
//! 5. **迭代化**：eval 双栈（work/vals + `App(变量头, ·)` 右链快速路径，
//!    β 岔路的闭包头以 [`W::ApplyKnown`] 直接送 β、不再压回 work 栈重查
//!    环境）、quote 任务栈（`ChainRun` 断点续跑）——求值/quote 深度不受
//!    进程栈限。
//! 6. **conv 工作表**：beta-eta 转换检查改为 `(level, V, V)` 工作表迭代
//!    （L01 没有 conv；同一「栈即数据」改造），外加**位相等快速路径**：
//!    同一打包字 = 同一分配或同一立即数 → 直接判等；连续中性链再走内联
//!    环（`L02_NO_BITEQ` 消融开关同时关闭两处剪枝，结构路径独立成立）。
//! 7. **quote 记忆化（call-by-need 的 readback 对偶，L01 `bump_spine_memo`
//!    的移植）**：NbE 的 CBV 只急切到 WHNF，真正的重复在 readback——同一
//!    闭包/中性句柄经 λ-binder 复制（`\x f. f x x`）后 quote 会对它多次
//!    强制。`quote_memo` 口径下 `Q` 先查 memo（键 = 打包字 × level；闭包
//!    指针与 spine 句柄单轮内全局唯一，spine 栈只增不改，缓存可靠），未
//!    命中则把 `MemoStore` 屏障压到任务栈最深处，弹出时回填；命中直接
//!    `done.push` 共享子树（结果从树变 DAG）。表随每次 quote 调用新建——
//!    `Bump::reset` 后旧键全部作废，无跨轮悬垂。线性负载（church/conv）
//!    的 `Q` 次数只有 O(λ 层)，哈希税趋近零；复制负载（l02bench
//!    `--workload dup`/`dup_deep`）把 2×/4× 的重复强制塌缩回 1×。
//! 8. **conv 判等记忆化**：工作表同一 `(t.0, u.0)` 子对只结构比较一次
//!    （依赖类型里同一昂贵索引对在 dom/cod 多处重现的常态，l02bench
//!    `conv_dup` 负载 1.4-1.6×）。判等结果与 level 无关（fresh 变量两侧
//!    对称插入、恒异于自由变量），键无需带 level；「已判等」靠工作表
//!    LIFO 屏障 `WItem::Store`（纯合取：屏障弹出时其上方子比较全部完成，
//!    任何失败早已 return）。表随本次 conv 调用新建；线性负载零税
//!    （`L02_NO_CONV_MEMO=1` 消融）。
//!
//! 机制与数据的完整叙述（四轮提速史、负载族、call-by-need/WHNF 概念
//! 注记、否决轴的教训）见 `L02_tyck/readme.md`。
//!
//! 与参考版（`super`，L03 风格）共用 parser / pretty / 错误显示，输出逐
//! 字节一致（互检测试）。elaboration 直接在本表示上进行：
//! `Raw → check/infer（产出 bump 核心项）→ quote → export → pretty`。
//! 稳态形态是 [`Tycker`]：`Machine` 的 spine/vals 跨调用复用，配每轮
//! `Bump::reset`——LSP 一类长驻进程的真实成本口径。

use super::{parser::Raw, Error, Ix, Name, Tm as CTm};
use crate::parser_lib::Span;
use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

// syntax（bump 内的项表示）
// --------------------------------------------------------------------------------

/// bump 内分配的核心项。名字只服务 pretty（`Var` 无名，索引寻址）。
enum Tm<'a> {
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
struct V(u64);

#[inline]
fn v_lvl(level: u32) -> V {
    V(((level as u64) << 3) | 0)
}
#[inline]
fn v_clo<'a>(p: &'a CloCell<'a>) -> V {
    V((p as *const _ as u64) | 1)
}
#[inline]
fn v_spine(idx: usize) -> V {
    V(((idx as u64) << 3) | 2)
}
#[inline]
fn v_u() -> V {
    V(3)
}
#[inline]
fn v_pi<'a>(p: &'a PiCell<'a>) -> V {
    V((p as *const _ as u64) | 4)
}
#[inline]
fn v_tag(v: V) -> u64 {
    v.0 & 7
}
#[inline]
fn v_lvl_of(v: V) -> u32 {
    (v.0 >> 3) as u32
}
#[inline]
fn v_clo_of<'a>(v: V) -> &'a CloCell<'a> {
    unsafe { &*((v.0 & !7) as *const CloCell) }
}
#[inline]
fn v_spine_of(v: V) -> usize {
    (v.0 >> 3) as usize
}
#[inline]
fn v_pi_of<'a>(v: V) -> &'a PiCell<'a> {
    unsafe { &*((v.0 & !7) as *const PiCell) }
}

/// 闭包单元：λ 的名字（只服务 quote 产出的 pretty）+ env + 体。
struct CloCell<'a> {
    name: &'a str,
    env: Option<&'a EnvCons<'a>>,
    body: &'a Tm<'a>,
}

/// Π 值单元：名字 + 定义域值 + 余定义域闭包（内联，一次分配）。
struct PiCell<'a> {
    name: &'a str,
    dom: V,
    env: Option<&'a EnvCons<'a>>,
    body: &'a Tm<'a>,
}

/// 环境节点（bump 内持久链表，头 = 最内层绑定）。
struct EnvCons<'a> {
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
struct Spine {
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
    /// vals 顶上是实参；函数值已知是闭包（β 岔路下降时已 `nth` 出来），
    /// 直接 β——不再经 `Tm(Var)` 重查一遍环境。
    ApplyKnown(V),
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
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
                            work.push(W::Tm(base, env));
                            break;
                        }
                    };
                    match f {
                        Tm::Var(i) => {
                            let vf = nth(env, *i as usize);
                            if v_tag(vf) == 1 {
                                // β 岔路：函数值已在手上（闭包），ApplyKnown
                                // 直接管 β；heads>0 时 ChainWrap 照旧收拢
                                if heads > 0 {
                                    work.push(W::ChainWrap(heads));
                                }
                                work.push(W::ApplyKnown(vf));
                                work.push(W::Tm(a, env));
                                break;
                            }
                            vals.push(vf);
                            heads += 1;
                            tm = a;
                        }
                        _ => {
                            // 复合函数头：通用三推（同样先收已收的头）
                            if heads > 0 {
                                work.push(W::ChainWrap(heads));
                            }
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
            W::ApplyKnown(vf) => {
                let va = vals.pop().expect("eval 栈：ApplyKnown 缺实参");
                let c = v_clo_of(vf);
                let node = bump.alloc(EnvCons { val: va, next: c.env });
                work.push(W::Tm(c.body, Some(node)));
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
    /// 记忆化屏障：done 栈顶是刚完成的 `Q(key, level)` 结果，入表后放回。
    /// 派发带 memo 的 `Q` 时压在任务栈最深处，LIFO 保证该值的整棵子任务
    /// 先跑完（机制见 L01 `bump_spine_memo.rs`）。
    MemoStore(u64, u32),
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

/// (值打包字, quote level) → 已引结果子树。同一打包字在同一 level 的
/// quote 结果只依赖 `(v, level)`：闭包/spine 句柄单轮内全局唯一，spine
/// 栈只增不改、条目压栈后不变——缓存可靠（论证同 L01 `bump_spine_memo`）。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote。`level0` 是起始 quote level（`show_val` 在 `cxt.lvl` 下
/// 引用含自由变量的值时非 0）。EvalQ 强制闭包体时复用调用方的 work/vals
/// 栈（稳态口径为 [`Machine`] 的，一次性口径为新建 Vec）。
/// `memo = Some` 时开启 quote 记忆化：Clo/Pi/spine 的 `Q` 先查表命中即
/// 共享子树，未命中以 `MemoStore` 屏障回填（Lvl/U 的 `Q` 是 O(1)，不走表）。
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
    mut memo: Option<&mut QuoteMemo<'a>>,
) -> &'a Tm<'a> {
    tasks.clear();
    done.clear();
    tasks.push(QJob::Q(v0, level0));
    while let Some(job) = tasks.pop() {
        match job {
            QJob::Q(v, level) => match v_tag(v) {
                0 => done.push(bump.alloc(Tm::Var(level - v_lvl_of(v) - 1))),
                1 => {
                    if let Some(t) = memo.as_deref_mut().and_then(|m| m.get(&(v.0, level))) {
                        done.push(*t);
                        continue;
                    }
                    let c = v_clo_of(v);
                    if memo.is_some() {
                        // 屏障压在最深处：v 的子任务全部跑完后它弹出并回填
                        tasks.push(QJob::MemoStore(v.0, level));
                    }
                    let node = bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
                    tasks.push(QJob::Lam1(c.name));
                    tasks.push(QJob::EvalQ(c.body, Some(node), level + 1));
                }
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
                    tasks.push(QJob::Pi1(cell));
                    tasks.push(QJob::EvalQ(
                        cell.body,
                        Some(bump.alloc(EnvCons { val: v_lvl(level), next: cell.env })),
                        level + 1,
                    ));
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
/// 位相等快速路径，走纯结构比较（`=0` 不关闭，避免 `set` 语义误伤）。
static NO_BITEQ: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("L02_NO_BITEQ").is_ok_and(|v| v != "0"),
        )
    });

/// A/B 实验开关（conv 工作表的判等记忆化消融）：置 `L02_NO_CONV_MEMO=1`
/// 关闭——工作表同一 (t.0, u.0) 子对只结构比较一次（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("L02_NO_CONV_MEMO").is_ok_and(|v| v != "0"),
        )
    });

/// conv 工作表条目：待比较子对，或判等记忆化屏障。
enum WItem<'a> {
    /// 待比较子对（level 相同的一对值）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较：弹出时两侧 cod 闭包体各 eval 一次（各自绑定
    /// 同一 fresh `v_lvl(l)`），结果入 Pair(l+1, ·, ·)。排在 dom 对之下——
    /// dom 不等即 `return false`，cod 的 eval 整个省掉（参考版
    /// `conv(l, a, a2) && conv(l+1, …)` 短路的对应物；旧实现把两侧 cod
    /// 先 eval 出来再比 dom，dom 不等时白付 O(n)）。
    EvalCod2(
        &'a Tm<'a>,
        Option<&'a EnvCons<'a>>,
        &'a Tm<'a>,
        Option<&'a EnvCons<'a>>,
        u32,
    ),
    /// 屏障：派发子对前压入；其弹出时上方整棵子比较已全部完成（工作表是
    /// 纯合取，任何失败早已 `return false`）——该对必已判等，入表。
    /// 机制同 quote 的 `MemoStore`（LIFO 屏障，见 L01 `bump_spine_memo`）。
    Store((u64, u64)),
}

/// Beta-eta 转换检查。前提：两个值的类型相同。与 Main.hs 的递归 `conv`
/// 同语义，改成 `(level, V, V)` 工作表——合取式比较天然迭代化，深度不受
/// 进程栈限；**位相等快速路径**：同一打包字 ⇒ 同一分配（闭包/spine 句柄
/// 全局唯一）或同一立即数（Lvl/U）⇒ 同一值， church 链里大量子比较被
/// 一次整数比较剪掉；**判等记忆化**：同一 (t.0, u.0) 子对只结构比较一次
/// （依赖类型里同一昂贵索引对在 dom/cod 多处重现的常态——l02bench
/// `conv_dup` 负载）。判等结果与 level 无关（fresh 变量两侧对称插入、
/// 恒异于自由变量，比较树在任意 level 同构），键无需带 level；表随本次
/// conv 调用新建，`Bump::reset` 后无跨轮悬垂。
fn conv_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    // 位相等/记忆化开关入口各读一次（消融模式同时关掉链内环里的剪枝）
    let biteq = !NO_BITEQ.load(std::sync::atomic::Ordering::Relaxed);
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    let mut memo: rustc_hash::FxHashSet<(u64, u64)> = rustc_hash::FxHashSet::default();
    let mut stack: Vec<WItem<'a>> = Vec::new();
    stack.push(WItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            WItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            WItem::EvalCod2(b1, e1, b2, e2, l) => {
                // dom 已判等：两侧 cod 各 eval 一次（fresh 绑定同一 level），
                // 组合成子对继续（两个 eval 顺序执行，复用的 work/vals 各自
                // clear，无跨 eval 残留）。
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: e1 })),
                    b1,
                );
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: e2 })),
                    b2,
                );
                stack.push(WItem::Pair(l + 1, vt, vu));
                continue;
            }
            WItem::Pair(l, t, u) => (l, t, u),
        };
        if biteq && t.0 == u.0 {
            continue; // 位相等：同一值
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对
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
                if memo_on {
                    stack.push(WItem::Store((t.0, u.0)));
                }
                stack.push(WItem::Pair(l + 1, vt, vu));
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
                if memo_on {
                    stack.push(WItem::Store((t.0, u.0)));
                }
                stack.push(WItem::Pair(l + 1, vt, vu));
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
                if memo_on {
                    stack.push(WItem::Store((t.0, u.0)));
                }
                stack.push(WItem::Pair(l + 1, vt, vu));
            }

            // Π：先比定义域（其上），再惰性 eval 两侧余定义域（EvalCod2
            // 排在 dom 之下——dom 不等时短路，cod 的 eval 整个省掉）。
            (4, 4) => {
                let p = v_pi_of(t);
                let q = v_pi_of(u);
                if memo_on {
                    stack.push(WItem::Store((t.0, u.0)));
                }
                stack.push(WItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(WItem::Pair(l, p.dom, q.dom));
            }

            // 中性：头相同则逐对比较 spine。连续右链（church 数一类的
            // s (s (… z)) 形状）走内联环：沿 `.a` 逐元素前进，f 位相等
            // 直接跳过（不入 worksheet），只有真正待比较的子对才入栈——
            // 每个 spine 条目从「2 次弹压 + 2 次入栈」降到 2 次顺序读。
            // 注：曾有「连续链长度 fail-fast」（两侧连续而 len 不等即判
            // 不等），不健全：链 base 的 `a` 可以是闭包，η 展开把应用
            // 吸收进 λ 体——`P (h y)`（len 2）vs `P (\x. h y x)`（len 1）
            // 实测误杀良型程序。内联环自身对长度不等的链逐层派发（闭包
            // 实参走 eta 臂），结论不变，故直接移除。
            (2, 2) => {
                let mut i1 = v_spine_of(t);
                let mut i2 = v_spine_of(u);
                if memo_on {
                    stack.push(WItem::Store((t.0, u.0)));
                }
                loop {
                    let (f1, a1) = {
                        let e = &spine.stack[i1];
                        (e.f, e.a)
                    };
                    let (f2, a2) = {
                        let e = &spine.stack[i2];
                        (e.f, e.a)
                    };
                    if !biteq || f1.0 != f2.0 {
                        stack.push(WItem::Pair(l, f1, f2));
                    }
                    if v_tag(a1) == 2 && v_tag(a2) == 2 {
                        // 两侧剩余 spine 是同一句柄：位相等即全等，直接收尾
                        if biteq && a1.0 == a2.0 {
                            break;
                        }
                        i1 = v_spine_of(a1);
                        i2 = v_spine_of(a2);
                    } else {
                        if !biteq || a1.0 != a2.0 {
                            stack.push(WItem::Pair(l, a1, a2));
                        }
                        break;
                    }
                }
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
struct Machine {
    spine: Spine,
    vals: Vec<V>,
}

impl Machine {
    fn new() -> Self {
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
            None,
        )
    }

    /// quote 的记忆化口径：同一 (值, level) 只强制一次，重复 `Q` 共享子树
    /// （结果 DAG 化）。表随本次调用新建——`Bump::reset` 后句柄作废，
    /// 绝不跨调用持有。
    fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let mut memo: QuoteMemo<'a> = FxHashMap::default();
        quote_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            level,
            v,
            Some(&mut memo),
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
            data: SmolStr::new(x),
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
        self.run_impl(mode, file, raw, false)
    }

    /// [`Tycker::run`] 的 quote 记忆化口径（输出逐字节一致，见 dup 负载）。
    pub(crate) fn run_memo(&mut self, mode: &str, file: &str, raw: &Raw) -> String {
        self.run_impl(mode, file, raw, true)
    }

    fn run_impl(&mut self, mode: &str, file: &str, raw: &Raw, use_memo: bool) -> String {
        self.bump.reset();
        let bump = &self.bump;
        let cxt = Cxt::empty(super::initial_pos());
        match self.machine.infer(bump, cxt, raw) {
            Err(err) => super::display_error(file, &err),
            Ok((t, a)) => match mode {
                "nf" => {
                    let v = self.machine.eval(bump, None, t);
                    format!(
                        "{}\n  :\n{}\n",
                        quote_str(&mut self.machine, bump, v, use_memo),
                        quote_str(&mut self.machine, bump, a, use_memo)
                    )
                }
                _ => format!("{}\n", quote_str(&mut self.machine, bump, a, use_memo)),
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
        self.bench_nf_impl(raw, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径（dup 负载的主对比行）。
    pub(crate) fn bench_check_nf_memo(&mut self, raw: &Raw) -> u64 {
        self.bench_nf_impl(raw, true)
    }

    /// 两个 bench nf 口径的公共实现，`use_memo` 分派同 [`quote_maybe`]。
    fn bench_nf_impl(&mut self, raw: &Raw, use_memo: bool) -> u64 {
        self.bump.reset();
        let bump = &self.bump;
        match self.machine.infer(bump, Cxt::empty(super::initial_pos()), raw) {
            Err(_) => 0,
            Ok((t, _)) => {
                let v = self.machine.eval(bump, None, t);
                let n = quote_maybe(&mut self.machine, bump, 0, v, use_memo);
                tm_size(n)
            }
        }
    }
}

/// `use_memo` 分派：memo 口径共享重复子树，普通口径独立重建（ablation 对照）。
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

/// quote + export + pretty 一步到位：`Tycker::run_impl` 的 nf/type 输出形态共用。
/// 做成自由函数而非 `&mut self` 方法：`run_impl` 里 `&self.bump` 的借用与
/// `&mut self.machine` 的字段拆分借用在方法调用下会冲突。
fn quote_str<'a>(m: &mut Machine, bump: &'a Bump, v: V, use_memo: bool) -> String {
    let t = quote_maybe(m, bump, 0, v, use_memo);
    super::pretty_tm(0, &[], &export(t))
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

/// dup 2×（复制强制负载，L01 `dup_pair` 的 L02 对应物）：church 2^(k+1)
/// 之上 `D p_k`（`D = \x f. f x x`），nf = `λf. f C C`——λ-binder 把同一
/// 闭包值 C 复制进两个实参槽，quote 对它**强制 2 次**（无记忆化时），
/// 打开 call-by-need / quote 记忆化轴。nf 节点数 = 4n + 12（n = 2^(k+1)）。
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

/// dup 4×（两层复制，L01 `dup_deep` 的 L02 对应物）：`D1 (D0 p_k)`，nf =
/// `λf. f (λf'. f' C C) (λf'. f' C C)`——C 被强制 **4 次**（无记忆化时：
/// 外层 f 的两个实参各引一遍内层，内层再各强制 C 两遍），复制层数每加一层
/// 收益翻倍。nf 节点数 = 8n + 28。
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

/// conv 重复子对负载（conv 判等记忆化的命中场景）：`relRefl Nat p_k` 对
/// 注解 `Rel Nat (add p_k zero) (add p_k zero)` 的 check 在 conv 里对同一
/// 昂贵子对 (C_p, C_add) 结构比较 3 次——`Rel = \A x y. (P : A -> U) ->
/// P x -> P y -> P y` 的三个 cod 槽位 x/y/y，inferred 侧全是 C_p 同一句柄，
/// expected 侧全是 C_add。无 memo：3 × O(n) 链游走；memo：1 次游走 +
/// 2 次哈希命中。建模依赖类型里「同一索引在类型多处重现」的常态
/// （check-only，无 nf）。
pub(crate) fn conv_dup_src(k: u32) -> String {
    let mut s = String::from(
        "let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let zero : Nat = \\N s z. z;\n\
         let add : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);\n\
         let p0 : Nat = \\N s z. s (s z);\n",
    );
    for i in 1..=k {
        s += &format!("let p{i} : Nat = add p{} p{};\n", i - 1, i - 1);
    }
    s += "let Rel : (A : U) -> A -> A -> U = \\A x y. (P : A -> U) -> P x -> P y -> P y;\n";
    s += "let relRefl : (A : U) -> (x : A) -> Rel A x x = \\A x P p1 p2. p1;\n";
    s += &format!("let relTest : Rel Nat (add p{k} zero) (add p{k} zero) = relRefl Nat p{k};\n");
    s += "relTest\n";
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

    /// conv_dup 负载：check 通过（p_k ≡ add p_k zero 经 3 次同一子对比较），
    /// 且与参考版判定一致。
    #[test]
    fn conv_dup_check_passes() {
        let src = conv_dup_src(10);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "conv_dup 未通过（memo 屏障有误？）");
        // 判定与参考版一致（type-mode 输出互检）
        let mut t = Tycker::new();
        assert_eq!(
            t.run("type", &src, &raw),
            super::super::main_with("type", &src),
            "conv_dup 判定与参考版不一致"
        );
    }

    // dup 复制强制负载（call-by-need / quote 记忆化轴）
    // --------------------------------------------------------------------------------

    /// dup 负载的 nf 输出与参考版逐字节一致（普通 quote 与记忆化 quote 双口径）。
    #[test]
    fn dup_nf_matches_basic() {
        for src in [dup_src(4), dup_deep_src(4)] {
            let Some(raw) = super::super::parser::parser(&src, 0) else {
                panic!("parse failed");
            };
            let basic = super::super::main_with("nf", &src);
            let mut t = Tycker::new();
            assert_eq!(t.run("nf", &src, &raw), basic, "无 memo 口径不一致");
            let mut t = Tycker::new();
            assert_eq!(t.run_memo("nf", &src, &raw), basic, "memo 口径不一致");
        }
    }

    /// church（线性）负载的 memo 口径与参考版逐字节一致——memo 不是 dup
    /// 专属：线性负载上它只付哈希税，输出必须不差分毫。
    #[test]
    fn church_memo_matches_basic() {
        let src = church_src(8); // n = 512：参考版递归 quote 深度可控
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let basic = super::super::main_with("nf", &src);
        let mut t = Tycker::new();
        assert_eq!(t.run_memo("nf", &src, &raw), basic);
    }

    /// dup 负载的 nf 节点数：`λf. f C C` = 4n+12、`λf. f X X`（X = `λf'. f' C C`）
    /// = 8n+28；memo 口径 DAG 共享不改变逐出现计数。
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

    /// memo 命中的直接证据：`λf. f C C` 的两处 C 共享同一子树指针（DAG）；
    /// 无 memo 对照应是两份独立副本。
    #[test]
    fn dup_memo_shares_forced_subtree() {
        let src = dup_src(3);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        tycker.bump.reset();
        let bump = &tycker.bump;
        let Ok((t, _)) = tycker.machine.infer(bump, Cxt::empty(super::super::initial_pos()), &raw)
        else {
            panic!("infer failed");
        };
        let v = tycker.machine.eval(bump, None, t);
        let Tm::Lam(_, Tm::App(Tm::App(_, c1), c2)) = tycker.machine.quote_memo(bump, 0, v)
        else {
            panic!("形状应为 λf. f C C");
        };
        // 在 &Tm 上模式匹配，绑定是指向父节点字段槽位的引用，比较子节点须再解一层
        assert!(
            std::ptr::eq(*c1, *c2),
            "复制分量未共享子树：memo 未命中或键不命中"
        );
        let Tm::Lam(_, Tm::App(Tm::App(_, c1), c2)) = tycker.machine.quote(bump, 0, v) else {
            panic!("形状应为 λf. f C C");
        };
        assert!(
            !std::ptr::eq(*c1, *c2),
            "无 memo 时两处 C 应是独立副本"
        );
    }

    /// memo 表随每次 quote 调用新建：同一 Tycker 反复 reset+quote，memo 口径
    /// 输出始终与每轮新建的 Tycker 一致（跨轮悬垂键回归测试）。
    #[test]
    fn steady_state_memo_reuse() {
        let Some(raw) = super::super::parser::parser(&dup_src(6), 0) else {
            panic!("parse failed");
        };
        let mut steady = Tycker::new();
        let r1 = steady.run_memo("nf", "", &raw);
        let r2 = steady.run_memo("nf", "", &raw);
        let mut fresh = Tycker::new();
        assert_eq!(r1, r2);
        assert_eq!(r1, fresh.run_memo("nf", "", &raw));
        assert_eq!(r1, main_with("nf", &dup_src(6)));
    }
}
