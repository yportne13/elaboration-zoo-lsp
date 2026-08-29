//! L03 核心机（eval / quote / unify / force / rename / solve / check /
//! infer）的极致性能版：把 L01/L02 调研的冠军配方（`bump_spine_iter`）移植
//! 到带元变量的核心上。机制（按 L02 的消融阶梯）：
//!
//! 1. **bump arena**：项、值、环境节点全部 bump 分配（`bumpalo`）。
//! 2. **打包值**：64 位字 [`V`]，tag 低 3 位——比 L02 多出 `Meta`（未解
//!    meta 立即数，tag 5）；`Flex` 的实参链就是普通 spine（头槽 `f` 存
//!    Meta 立即数），`force` 沿 `f` 指针探到链头再展开。
//! 3. **扁平中性 + spine 栈**：同 L02；`InsertaMeta` 的 `vAppBDs` 用 work
//!    栈任务（`AppBds`/`AppBdsOne`，外层实参先应用）串起来。
//! 4. **流式右链 quote**：同 L02；flex 链头（Meta 立即数）像变量一样共享
//!    单一 `?m` 节点。
//! 5. **迭代化**：eval 双栈 + quote 任务栈同 L02；**force 是循环**（解链
//!    展开 + spine 重建都是迭代）；**rename 是任务栈**（`RJob`——rename
//!    沿 spine 的递归在参考版是 O(n) 深，这里断点续跑）；
//!    **invert 是循环**（沿 f 链收集实参）。
//! 6. **unify 工作表**：`(level, V, V)` 工作表 + 位相等快速路径（同 L02 的
//!    conv）；表中分派时先 force 双方、可**触发求解**（副作用——
//!    `solve` 只发生在比较成功路径，工作表失败即 return，无回滚问题）。
//! 7. **quote 记忆化（`quote_memo`）**：复制强制负载（dup 族）把重复
//!    quote 塌缩为单次（L02 `quote_memo` 的移植；键 = 打包字 × level，
//!    quote 期间 metacontext 冻结，flex 键稳定）。
//! 8. **unify 判等记忆化（`UItem::Store` 轴，L02 conv memo 的移植）**：
//!    同一 (t.0, u.0) 子对只结构比较一次（`Rel` 型重复谓词 / solve 后的
//!    二次重走是命中场景）。与 L02 纯 conv 的差异在健壮性论证：solve
//!    是唯一副作用——meta 写一次、force 只会 flex→rigid、算法成功对
//!    metacontext 单调（见 `unify_iter` 注释），故**只缓存成功结果**仍
//!    与逐对重比观测等价。`L03_NO_CONV_MEMO=1` 消融。
//! 9. **O(1) 名字解析（`name_map`）**：`Raw::Var` 不再沿 `types` 链线性
//!    找名（深度 = scope 大小，长 let 链每层引用老名字时 O(n²)）。Machine
//!    持 `名字 → (绑定 lvl, 类型)` 哈希表，bind/define 推表 + trail，
//!    binder 作用域退出（递归返回）按 `Cxt.mark` 截断恢复——兄弟子树不
//!    泄漏、shadowing 退出还原旧绑定；错误路径跳出整轮，每轮 reset 清空。
//!    `L03_NO_NAME_MAP=1` 消融（回落线性 walk）。
//!
//! 与参考版（`super`）共用 parser / pretty / 错误显示，输出逐字节一致
//! （互检测试）。稳态形态是 [`Tycker`]：`Machine`（spine/vals/metacontxt）
//! 跨调用复用 + 每轮 `Bump::reset`。
//!
//! 与 L02 的 conv 相比，本层统一改称 **unify**：结构比较 + 模式求解。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use super::parser::Raw;
use crate::parser_lib::Span;
use super::{Error, Name, Tm as CTm, Ix, pretty_tm, report_at};

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
    /// 显式引用的 meta（`?m`，来自 rename 产出/解）。
    Meta(u32),
    /// hole 处插入的 meta：抽象掉 elaboration 当时的全部 Bound 变量
    /// （`bds` 与求值环境平行：`bound = true` 槽位实参应用、`false` 跳过）。
    InsertedMeta(u32, Option<&'a BdCons<'a>>),
}

/// `InsertedMeta` 的槽位掩码链表（bump 持久链表，头 = 最内层绑定）。
pub(crate) struct BdCons<'a> {
    bound: bool,
    next: Option<&'a BdCons<'a>>,
}

// values（打包值）
// --------------------------------------------------------------------------------

/// 打包值：tag 在低 3 位。`0=Lvl(level<<3)`、`1=Clo(ptr|1)`、
/// `2=Spine(idx<<3|2)`、`3=U`（立即数）、`4=Pi(ptr|4)`、`5=Meta(m<<3|5)`
/// （未解 meta 立即数）。bump 分配 8 字节对齐，指针低 3 位空闲。
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

    /// 沿 `f` 指针走到链的最底层头（Apply 惯例的 entry `f` = 前一个
    /// partial；ChainWrap 惯例的 `f` = 头值）——返回头字（Lvl / Meta /
    /// 其它）。f 指针严格指向更早的槽位，必终止。
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
    /// 引用语义：`value(e_i) = App(f_i, value(e_i.a))`（Apply 惯例的
    /// `a` = 真实参；ChainWrap 惯例的 `a` = 前一层 partial——两者都满足
    /// 这条规则，见 L03 readme 的 spine 语义注记）。
    #[inline]
    fn collect_args(&self, h: usize, out: &mut Vec<V>) {
        let mut cur = h;
        loop {
            let e = &self.stack[cur];
            out.push(e.a);
            if v_tag(e.f) == 2 {
                cur = v_spine_of(e.f);
            } else {
                return;
            }
        }
    }

    /// force 后的未解 flex 探测：`tag 5`（空 spine）或 spine 头是
    /// `Meta`（实参链；头经 `spine_head` 走底——Apply 惯例链的顶层
    /// entry `f` 是前一个 partial）。返回 (meta 号, 逆应用序实参)。
    /// 要求调用方先 force（已解的 flex 在 force 里已展开，不会到这里）。
    fn flex_of(&self, v: V, out: &mut Vec<V>) -> Option<u32> {
        match v_tag(v) {
            5 => Some(v_meta_of(v)),
            2 => {
                let h = v_spine_of(v);
                let hd = self.spine_head(h);
                if v_tag(hd) != 5 {
                    return None;
                }
                // 引用语义实参：从 h 沿 f 下行收集
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

/// **force**：把值更新到 metacontext 的当前状态（只到下一个不可再解阻塞
/// 的头构造器）。参考版的递归 force 展开成循环：已解 meta 立即数 → 替换
/// 为解；已解 flex spine → 沿 f 链收集实参、把解按应用序应用到实参上
/// （应用可触发 β，经 `eval_iter`），再继续。未解保持原样。
fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
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
                        let mut args: Vec<V> = Vec::new();
                        spine.collect_args(h, &mut args);
                        let mut t = *sol;
                        for &a in args.iter().rev() {
                            if v_tag(t) == 1 {
                                let c = v_clo_of(t);
                                let node = bump.alloc(EnvCons { val: a, next: c.env });
                                t = eval_iter(bump, spine, work, vals, metas, Some(node), c.body);
                            } else {
                                t = spine.push(t, a);
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
    /// vals 顶是 `vAppBDs` 的当前值；沿 (env, bds) 平行走完剩余槽位
    /// （外层先应用——递归版先走尾再回头应用头，这里用栈翻转顺序）。
    AppBds(Option<&'a EnvCons<'a>>, Option<&'a BdCons<'a>>),
    /// vals 顶两个（先 base 后实参）：把实参应用上去（Clo → β；
    /// 其它 → spine.push）。`AppBds` 的单个实参应用步。
    AppBdsOne(V),
}

/// 双栈迭代 eval（`bump_spine_iter` 的 L02 版 + Meta/InsertedMeta）。
/// `InsertedMeta m bds`：先取 `vMeta m`（已解给解值、未解给 `?m` 立即数），
/// 再把 (env, bds) 对齐的 `bound` 槽位实参按**外层优先**应用上去——
/// 与递归版 `vAppBDs`（尾递归先去尾、再应用头）同语义。
fn eval_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    metas: &[MetaEntry],
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
            W::Tm(Tm::Meta(m), _) => vals.push(meta_val_of(metas, *m)),
            W::Tm(Tm::InsertedMeta(m, bds), env) => {
                vals.push(meta_val_of(metas, *m));
                work.push(W::AppBds(env, *bds));
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
            W::AppBds(env, bds) => match (env, bds) {
                (None, None) => {}
                (Some(e), Some(b)) if b.bound => {
                    // 先跑余下槽位（外层），再应用本槽（内层最后应用）
                    work.push(W::AppBdsOne(e.val));
                    work.push(W::AppBds(e.next, b.next));
                }
                (Some(e), Some(b)) => work.push(W::AppBds(e.next, b.next)),
                _ => panic!("impossible"), // env 与 bds 错位（空环境引带 binder 的 hole）
            },
            W::AppBdsOne(arg) => {
                let v = vals.pop().expect("eval 栈：AppBdsOne 缺值");
                if v_tag(v) == 1 {
                    let c = v_clo_of(v);
                    let node = bump.alloc(EnvCons { val: arg, next: c.env });
                    work.push(W::Tm(c.body, Some(node)));
                } else {
                    vals.push(spine.push(v, arg));
                }
            }
        }
    }
    vals.pop().expect("eval 必须恰有一个根值")
}

// quote（任务栈迭代 + 流式右链；flex 头共享 ?m 节点）
// --------------------------------------------------------------------------------

/// quote 任务。`ChainRun` 的「断点续跑」语义见 L01 `bump_spine_iter.rs`。
enum QJob<'a> {
    /// 引一个值（先 force）。
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

/// (值打包字, quote level) → 已引结果子树。同一打包字在同一 level 的
/// quote 结果只依赖 `(v, level)`：闭包/spine 句柄单轮内全局唯一，spine
/// 栈只增不改——缓存可靠。quote 期间 metacontext 冻结（无 solve），
/// flex 句柄的 force 结果在同一轮内确定，键稳定。
type QuoteMemo<'a> = FxHashMap<(u64, u32), &'a Tm<'a>>;

/// 任务栈 quote。`level0` 是起始 quote level（`show_val` 在 `cxt.lvl` 下
/// 引用含自由变量的值时非 0）。EvalQ 强制闭包体时复用调用方的 work/vals
/// 栈。`memo = Some` 时开启 quote 记忆化：Clo/Pi/spine 的 `Q` 先查表命中
/// 即共享子树，未命中以 `MemoStore` 屏障回填。
#[allow(clippy::too_many_arguments)]
fn quote_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    tasks: &mut Vec<QJob<'a>>,
    done: &mut Vec<&'a Tm<'a>>,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
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
                // 先 force：已解 meta 立即数展开成解、已解 flex spine
                // 重建（metacontext 在 quote 期间冻结，同键同结果）
                let v = force(bump, spine, work, vals, metas, v0);
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
                            // 屏障压在最深处：v 的子任务全部跑完后它弹出并回填
                            tasks.push(QJob::MemoStore(v.0, level));
                        }
                        let node =
                            bump.alloc(EnvCons { val: v_lvl(level), next: c.env });
                        tasks.push(QJob::Lam1(c.name));
                        tasks.push(QJob::EvalQ(c.body, Some(node), level + 1));
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
                        tasks.push(QJob::Pi1(cell));
                        tasks.push(QJob::EvalQ(
                            cell.body,
                            Some(bump.alloc(EnvCons {
                                val: v_lvl(level),
                                next: cell.env,
                            })),
                            level + 1,
                        ));
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
                        let (ea, len, base) = {
                            let e = &spine.stack[h];
                            (e.a, e.len, e.base)
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
                            tasks.push(QJob::App1);
                            tasks.push(QJob::Q(ea, level));
                            tasks.push(QJob::Q(
                                spine.stack[h].f,
                                level,
                            ));
                        }
                    }
                }
            }
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
                let v = eval_iter(bump, spine, work, vals, metas, env, body);
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
}// unify（工作表迭代 + force 前置 + 模式求解 + 判等记忆化）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L03_NO_CONV_MEMO=1`
/// 关闭——工作表同一 (t.0, u.0) 子对只结构比较一次（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("L03_NO_CONV_MEMO").is_ok_and(|v| v != "0"),
        )
    });

/// unify 工作表条目：待比较子对，或 Π 余定义域的惰性比较屏障，或判等
/// 记忆化屏障。
enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较：弹出时两侧 cod 闭包体各 eval 一次（各自绑定
    /// 同一 fresh `v_lvl(l)`），结果入 Pair(l+1, ·, ·)。排在 dom 对之下——
    /// dom 不等即 `return false`，cod 的 eval 整个省掉（参考版
    /// `unify(l, a, a')?` 短路的对应物）。
    EvalCod2(
        &'a Tm<'a>,
        Option<&'a EnvCons<'a>>,
        &'a Tm<'a>,
        Option<&'a EnvCons<'a>>,
        u32,
    ),
    /// 判等记忆化屏障：派发子对前压入；其弹出时上方整棵子比较已全部完成
    /// （工作表是纯合取，任何失败早已 `return false`）——该对必已判等，
    /// 入表。机制同 L02 conv 的 `WItem::Store`（LIFO 屏障）。
    Store((u64, u64)),
}

/// unification：结构比较 + 模式求解，工作表迭代（深度不受进程栈限）。
/// 分派次序与参考版一致：λ 情形 → U → Π → 同头中性 → 求解。位相等快速
/// 路径在 force 前后各查一次（同一打包字 ⇒ 同一分配或同一立即数 ⇒ 同值）。
/// 求解是唯一副作用：只发生在比较成功路径（工作表纯合取，失败早已
/// return），无回滚问题。
///
/// **判等记忆化**（`L03_NO_CONV_MEMO=1` 消融）：同一 (t.0, u.0) 子对只
/// 结构比较一次，`Store` LIFO 屏障保证只在整棵子比较成功后入表（失败
/// 直接 `return false`，无失败缓存）。相对 L02 纯 conv 多出的健壮性论证
/// ——solve 改变 metacontext，同一打包字对的 force 结果随时间变化：
///
/// 1. meta **写一次**（`Unsolved → Solved` 不回退），force 只会把
///    flex 变刚性（解链展开），刚性永不回退成 flex；
/// 2. **成功单调**：M 时刻子对判等成功 ⇒ M′ ⊇ M 时刻再比较仍成功。
///    归纳：M′ 的比较树是 M 的比较树把「solve 成功的节点」替换成求解后
///    的结构比较子树（该子树在 M 时刻同样成功——解按应用序摔上去后
///    比的就是它的展开形）；基例（位相等、刚性同头逐实参）不受 expansion
///    影响，flex 集合单调收缩只会把 solve 分支变成已展开的结构分支；
/// 3. **跳过不影响 metacontext 终态**：M′ 时刻想解的 meta 在 M 时刻同样
///    未解（写一次 ⇒ 未解集单调收缩），M 时刻的成功要么已解它（⇒ M′
///    force 直接展开，无 solve 分支）要么无需解它——缓存命中跳过的
///    重比不欠任何求解；
/// 4. 判等布尔与 level 无关（fresh 变量两侧对称插入、恒异于自由变量，
///    比较树在任意 level 同构）——键无需带 level，同 L02。
///
/// 表随本次 unify 调用新建，`Bump::reset` 后无跨轮悬垂。
fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    l0: u32,
    t0: V,
    u0: V,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    let mut memo: rustc_hash::FxHashSet<(u64, u64)> = rustc_hash::FxHashSet::default();
    let mut stack: Vec<UItem<'a>> = Vec::new();
    // 实参收集草稿：跨 Pair 复用（clear 保容量），热路径上零分配
    let mut scratch1: Vec<V> = Vec::new();
    let mut scratch2: Vec<V> = Vec::new();
    stack.push(UItem::Pair(l0, t0, u0));
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                // dom 已判等：两侧 cod 各 eval 一次（fresh 绑定同一 level），
                // 组合成子对继续（两个 eval 顺序执行，复用的 work/vals 各自
                // clear，无跨 eval 残留）。
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    metas,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: e1 })),
                    b1,
                );
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    metas,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: e2 })),
                    b2,
                );
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
        let t = force(bump, spine, work, vals, metas, t);
        let u = force(bump, spine, work, vals, metas, u);
        if t.0 == u.0 {
            continue; // force 展开后同值（同一解的两处引用）
        }
        match (v_tag(t), v_tag(u)) {
            // λ 情形（eta 含）：两边都应用到同一个新变量
            (1, 1) => {
                let c1 = v_clo_of(t);
                let c2 = v_clo_of(u);
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    metas,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c1.env })),
                    c1.body,
                );
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    metas,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c2.env })),
                    c2.body,
                );
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            (_, 1) => {
                let c = v_clo_of(u);
                let vu = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    metas,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c.env })),
                    c.body,
                );
                let vt = spine.push(t, v_lvl(l));
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }
            (1, _) => {
                let c = v_clo_of(t);
                let vt = eval_iter(
                    bump,
                    spine,
                    work,
                    vals,
                    metas,
                    Some(bump.alloc(EnvCons { val: v_lvl(l), next: c.env })),
                    c.body,
                );
                let vu = spine.push(u, v_lvl(l));
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::Pair(l + 1, vt, vu));
            }

            // 宇宙
            (3, 3) => {}

            // Π：先比定义域（其上），再惰性 eval 两侧余定义域
            (4, 4) => {
                let p = v_pi_of(t);
                let q = v_pi_of(u);
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
            }

            // 变量
            (0, 0) => return false, // 位相等已剪同 level；异 level 必不等

            // 同头中性：逐对比较实参（应用序；收集是逆序，压栈倒回）。
            // force 后到达这里的 spine 头要么同字（Lvl 同 level → rigid、
            // Meta 同号 → flex-flex），要么已经位相等剪掉；头字不同必不等
            // ——**除非**任一侧的头是未解 flex：参考版在 eta 步后把 fresh
            // 实参积到 flex 的 spine 上（`(VLam, _)` → `u vApp VVar l`），
            // 形成「刚性链 vs 带参 flex」的形态，此时走求解（invert 的
            // spine 恰好覆盖 rhs 的全部自由变量）。
            (2, 2) => {
                let h1 = v_spine_of(t);
                let h2 = v_spine_of(u);
                let hd1 = spine.spine_head(h1);
                let hd2 = spine.spine_head(h2);
                // 求解仅限**异头**且一侧头是未解 flex（eta 积参形态）。同号
                // flex-flex（同一 meta 的两个独立 spine，同实参不同句柄——
                // cod 位置两次独立求值的形态）必须落到底下逐实参比较：参考
                // 版 `(VFlex m, VFlex m') | m == m'` 走 unifySpine 可成功，
                // 而 solve 的 rename 对 rhs 含目标 meta occurs check 必然
                // 失败（曾在此误报 Cannot unify，互检回归 `cod 双求值`）。
                if hd1.0 != hd2.0 && (v_tag(hd1) == 5 || v_tag(hd2) == 5) {
                    // 含未解 flex：与 `_` 分支同款求解路径。solve 成功即该对
                    // 判等完成（解按构造使两侧相等，无子比较需要屏障）——
                    // 直接入表：solve 负载里 (p_k, ?x) 型子对会因 `Eq A x x`
                    // 型的重复出现二次，命中省掉解展开后的整趟重走。
                    let mut args = std::mem::take(&mut scratch1);
                    args.clear();
                    let solved = if let Some(m) = spine.flex_of(t, &mut args) {
                        solve(bump, spine, work, vals, metas, l, m, &args, u)
                    } else {
                        let mut args = std::mem::take(&mut scratch2);
                        args.clear();
                        match spine.flex_of(u, &mut args) {
                            Some(m) => solve(bump, spine, work, vals, metas, l, m, &args, t),
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
                // 连续链长度 fail-fast（L02 conv 内联环同款）：两侧都是连续
                // 链（base+len-1 == idx，即逐条 push 相邻构建）而条目数不同
                // ⇒ 归一化后应用个数不同 ⇒ 必不等。非连续链（共享后缀句柄、
                // 跨期构建）len 不再等于应用个数，由连续性守卫排除。
                {
                    let e1 = &spine.stack[h1];
                    let e2 = &spine.stack[h2];
                    if e1.base as usize + e1.len as usize - 1 == h1
                        && e2.base as usize + e2.len as usize - 1 == h2
                        && e1.len != e2.len
                    {
                        return false;
                    }
                }
                if memo_on {
                    // 屏障先压（LIFO：其上内联环压入的子对先跑完）
                    stack.push(UItem::Store((t.0, u.0)));
                }
                // 内联环（L02 conv 冠军配方的移植）：两侧各自按本侧惯例分解
                // value(e) = App(f, v(a))，沿 `.a` 同步下走——f 位相等直接
                // 跳过（ChainWrap 链每层同头字）、剩余 spine 同句柄即位相等
                // 收尾，只有真正待比的子对才入工作表。church 链的刚性比较
                // 整条链零往返；混合惯例链自动退化为逐层派发（仍正确）。
                // 到达此处的链头为刚性或**同号**未解 flex（异头未解 flex 已
                // 走上方求解路径、已解 flex 已被 force 展开），f 分量恒非闭
                // 包（Apply/ChainWrap 的 β 岔路即时归约；unify 的 eta push
                // 只推非闭包）。
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

            // 求解：一侧是未解 flex（tag5 或 spine 头 Meta——force 后仍未
            // 解才是 flex）；异 m 情形按参考版次序先解 t 侧。solve 成功即
            // 判等完成，直接入表（同 (2,2) flex 分支的理由）。
            _ => {
                let mut args = std::mem::take(&mut scratch1);
                args.clear();
                let solved = if let Some(m) = spine.flex_of(t, &mut args) {
                    solve(bump, spine, work, vals, metas, l, m, &args, u)
                } else {
                    match spine.flex_of(u, &mut args) {
                        Some(m) => solve(bump, spine, work, vals, metas, l, m, &args, t),
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
/// 失败即不改 metacontext（invert/rename 完成前不写表）。
fn solve<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    gamma: u32,
    m: u32,
    args: &[V], // 逆应用序（spine 收集器的输出）
    rhs: V,
) -> bool {
    // invert：实参（应用序）逐个 force 成刚性变量，赋解域下标；
    // 重复/非变量即非模式，失败
    let dom = args.len() as u32;
    let mut ren: Vec<Option<u32>> = vec![None; gamma as usize];
    for (i, &a) in args.iter().rev().enumerate() {
        let f = force(bump, spine, work, vals, metas, a);
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
    let Some(tm) = rename_iter(bump, spine, work, vals, &mut ren, metas, m, dom, gamma, rhs)
    else {
        return false;
    };
    // 包 λ 后空环境求值，写表
    let lams_tm = lams(bump, dom, tm);
    let sol = eval_iter(bump, spine, work, vals, metas, None, lams_tm);
    metas[m as usize] = MetaEntry::Solved(sol);
    true
}

/// rename 任务。
enum RJob<'a> {
    /// 引一个值到解域（产生一个 Tm 到 done）。
    Ren { dom: u32, cod: u32, v: V },
    /// 实参（逆应用序）已由其上任务引完，头是 head_tm，折叠 App。
    SpineFold { head_tm: &'a Tm<'a>, n: u32 },
    /// done 栈顶是体，包 Lam。
    Lam1(&'a str),
    /// done 栈顶两个（先 cod 后 dom），合 Pi。
    Pi2(&'a str),
}

/// partial renaming 的迭代版。`ren` 初始 = invert 结果（长度 gamma、部分
/// 填充）；lift 沿深度单调插入 `ren[cod] = dom`——spine 映射管 Γ 变量
/// （< gamma），lift 管 lift 出的 binder（≥ gamma），两段不相交，插入
/// 顺序与深度同步，故**无需回溯**（正规化论证见 L03 readme）。
fn rename_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    ren: &mut Vec<Option<u32>>,
    metas: &[MetaEntry],
    target_m: u32,
    dom0: u32,
    cod0: u32,
    v0: V,
) -> Option<&'a Tm<'a>> {
    let mut tasks: Vec<RJob<'a>> = vec![RJob::Ren { dom: dom0, cod: cod0, v: v0 }];
    let mut done: Vec<&'a Tm<'a>> = Vec::new();
    // 实参收集 / 折叠草稿：跨任务复用（clear 保容量），热路径零分配
    let mut args: Vec<V> = Vec::new();
    let mut popped: Vec<&'a Tm<'a>> = Vec::new();
    // 派发辅助：spine 头分派（head_tm 就绪后按实参数压子任务；SpineFold
    // 先压——LIFO 保证实参任务先跑完，组合器最后执行）
    macro_rules! spine_case {
        ($dom:expr, $cod:expr, $h:expr, $head_tm:expr, $tasks:expr) => {{
            args.clear();
            spine.collect_args($h, &mut args);
            // 先压组合器（后执行）；args 逆应用序（h.a 先）→ 正序压，
            // 则 a1 的 Ren 最后压、最先弹（应用序先执行）
            $tasks.push(RJob::SpineFold { head_tm: $head_tm, n: args.len() as u32 });
            for &a in args.iter() {
                $tasks.push(RJob::Ren { dom: $dom, cod: $cod, v: a });
            }
        }};
    }
    while let Some(job) = tasks.pop() {
        match job {
            RJob::Ren { dom, cod, v } => {
                let v = force(bump, spine, work, vals, metas, v);
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
                        let bv = eval_iter(
                            bump,
                            spine,
                            work,
                            vals,
                            metas,
                            Some(bump.alloc(EnvCons { val: v_lvl(cod), next: c.env })),
                            c.body,
                        );
                        // lift：binder 槽 (cod → dom)，单调插入
                        let idx = cod as usize;
                        if idx >= ren.len() {
                            ren.resize(idx + 1, None);
                        }
                        ren[idx] = Some(dom);
                        tasks.push(RJob::Lam1(c.name));
                        tasks.push(RJob::Ren { dom: dom + 1, cod: cod + 1, v: bv });
                    }
                    4 => {
                        let cell = v_pi_of(v);
                        let bv = eval_iter(
                            bump,
                            spine,
                            work,
                            vals,
                            metas,
                            Some(bump.alloc(EnvCons { val: v_lvl(cod), next: cell.env })),
                            cell.body,
                        );
                        // lift（同 Lam）
                        let idx = cod as usize;
                        if idx >= ren.len() {
                            ren.resize(idx + 1, None);
                        }
                        ren[idx] = Some(dom);
                        tasks.push(RJob::Pi2(cell.name));
                        tasks.push(RJob::Ren { dom: dom + 1, cod: cod + 1, v: bv });
                        tasks.push(RJob::Ren { dom, cod, v: cell.dom });
                    }
                    3 => done.push(bump.alloc(Tm::U)),
                    _ => return None, // 病态（Π/U 被应用等）
                }
            }
            RJob::SpineFold { head_tm, n } => {
                // 实参任务已完成：done 栈顶是最后一个完成的实参
                // （应用序最后一位）——全部弹出后反序折叠成左嵌套 App
                popped.clear();
                for _ in 0..n {
                    popped.push(done.pop()?);
                }
                let mut t = head_tm;
                for &a in popped.iter().rev() {
                    t = bump.alloc(Tm::App(t, a));
                }
                done.push(t);
            }
            RJob::Lam1(name) => {
                let body = done.pop()?; // 栈约定：子任务必已完成
                done.push(bump.alloc(Tm::Lam(name, body)));
            }
            RJob::Pi2(name) => {
                let cod = done.pop()?;
                let dom = done.pop()?;
                done.push(bump.alloc(Tm::Pi(name, dom, cod)));
            }
        }
    }
    done.pop()
}

/// `λ x1 x2. … body`（与参考版 `lams` 同语义；bump 分配，名字只服务 pretty）。
fn lams<'a>(bump: &'a Bump, dom: u32, body: &'a Tm<'a>) -> &'a Tm<'a> {
    let mut t = body;
    for i in (0..dom).rev() {
        let name = bump.alloc_str(&format!("x{}", i + 1));
        t = bump.alloc(Tm::Lam(name, t));
    }
    t
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 稳态复用机：spine 与 vals 两个无生命周期的大栈跨调用复用（clear 保
/// 容量），metacontext 也常住（每轮 elaboration 清空），配 [`Tycker`] 每轮
/// `Bump::reset` 即稳态近零分配。带生命周期的小栈（work/tasks/done）每
/// 调用新建，避免 struct 持 `'a` 跨 `Bump::reset` 的借用冲突。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。与 `types` 链
    /// 同步——每个 scope 条目经 [`Machine::bind_name`]/[`Machine::define_name`]
    /// 入表，binder 退出按 [`Machine::unwind_names`] 还原（shadowing 恢复
    /// 旧值）。每轮 reset 清空（表里存着指向 bump 的 V 字）。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。`Cxt.mark` 记各上下文的
    /// trail 长度，退出即截断。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
}

const PI_NAME: &str = "x"; // infer App 非 Π 分支合成的闭包名（只服务 pretty）

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine { stack: Vec::with_capacity(4096) },
            vals: Vec::with_capacity(4096),
            metas: Vec::new(),
            name_map: FxHashMap::default(),
            name_trail: Vec::new(),
        }
    }

    /// 每轮 reset：metacontext 清空 + 名字表/轨迹清空（表里存有指向上一轮
    /// bump 的 V 字，必须随 `Bump::reset` 一同作废）。
    fn clear_round(&mut self) {
        self.metas.clear();
        self.name_map.clear();
        self.name_trail.clear();
    }

    /// Extend Cxt with a bound variable（名字解析版）：types 链 + 名字表 +
    /// 撤销轨迹三同步。调用方在 binder 的递归返回后按父 `cxt.mark`
    /// [`Machine::unwind_names`]。
    fn bind_name<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, x: &str, ty: V) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        cxt.bind(bump, bump.alloc_str(x), ty)
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
        cxt.define(bump, bump.alloc_str(x), val, ty)
    }

    /// 截断撤销轨迹到 `mark`（binder 作用域退出）：shadowing 的名字还原旧
    /// 绑定，新名字移除。错误路径（`?` 早退）会跳过本调用——轨迹残留到
    /// 轮末由 [`Machine::clear_round`] 清空，中途不再有 Var 查找。
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

    fn eval<'a>(
        &mut self,
        bump: &'a Bump,
        env: Option<&'a EnvCons<'a>>,
        tm: &'a Tm<'a>,
    ) -> V {
        eval_iter(bump, &mut self.spine, &mut Vec::new(), &mut self.vals, &self.metas, env, tm)
    }

    fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        quote_iter(
            bump,
            &mut self.spine,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut self.vals,
            &self.metas,
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

    /// 主 `check`：`RLam` 只在 `VPi` 下可检查，`RLet` 总可检查，洞直接
    /// 挂 meta，其余 fall-through 到 infer + unify。
    fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = force(bump, &mut self.spine, &mut Vec::new(), &mut self.vals, &self.metas, a);
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
                let mark = cxt.mark;
                let cxt2 = self.bind_name(bump, cxt, &x.data, p.dom);
                let body = self.check(bump, cxt2, t, body_a)?;
                self.unwind_names(mark);
                Ok(bump.alloc(Tm::Lam(name, body)))
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
                    // O(1)：表与 types 链由 bind/define + trail 同步维护，
                    // 在表里即在 scope 里。index = 当前 lvl - 绑定 lvl - 1。
                    if let Some(&(blvl, ty)) = self.name_map.get(&x.data) {
                        return Ok((bump.alloc(Tm::Var(cxt.lvl - blvl - 1)), ty));
                    }
                } else {
                    // 消融口径：沿 types 链线性找名（深度 = scope 大小）
                    let mut i = 0u32;
                    let mut tys = cxt.types;
                    while let Some(tc) = tys {
                        if tc.name == x.data {
                            return Ok((bump.alloc(Tm::Var(i)), tc.ty));
                        }
                        i += 1;
                        tys = tc.next;
                    }
                }
                Err(report_at(cxt.pos, format!("Name not in scope: {}", x.data)))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())), // U : U rule

            // 定义域挂洞；余定义域闭包住当前环境（解可引用局部变量）
            Raw::Lam(x, t) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt.bds);
                let a = self.eval(bump, cxt.env, new_meta);
                let mark = cxt.mark;
                let cxt2 = self.bind_name(bump, cxt, &x.data, a);
                let (t, b) = self.infer(bump, cxt2, t)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell { name, dom: a, env: cxt.env, body });
                Ok((bump.alloc(Tm::Lam(name, t)), v_pi(cell)))
            }

            Raw::App(t, u) => {
                let (t, tty) = self.infer(bump, cxt, t)?;
                // 确保 tty 是 Π：不是则挂一对洞（定义域 + 余定义域），
                // 用合成的 Π 与 tty 做 unification（可能求解出它们的值）
                let tty = force(bump, &mut self.spine, &mut Vec::new(), &mut self.vals, &self.metas, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    (p.dom, p)
                } else {
                    let new_meta = self.fresh_meta(bump, cxt.bds);
                    let a = self.eval(bump, cxt.env, new_meta);
                    // 合成 Π 的 binder（PI_NAME）不进名字表：cxt2 只用于
                    // 取 bds（无 Raw 在其下 elaborat），表里留痕反而会
                    // 遮蔽用户名字且无人还原——这里只延伸 bds。
                    let bds2: Option<&'a BdCons<'a>> =
                        Some(bump.alloc(BdCons { bound: true, next: cxt.bds }));
                    let cod_meta = self.fresh_meta(bump, bds2);
                    let cell = bump.alloc(PiCell {
                        name: PI_NAME,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(&*cell), tty)?;
                    (a, &*cell)
                };
                let u = self.check(bump, cxt, u, a)?;
                let arg = self.eval(bump, cxt.env, u);
                // t u : B[x |-> u]
                let ty = self.eval(
                    bump,
                    Some(bump.alloc(EnvCons { val: arg, next: bcell.env })),
                    bcell.body,
                );
                Ok((bump.alloc(Tm::App(t, u)), ty))
            }

            Raw::Pi(x, a, b) => {
                let a_tm = self.check(bump, cxt, a, v_u())?;
                let va = self.eval(bump, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.bind_name(bump, cxt, &x.data, va);
                let b_tm = self.check(bump, cxt2, b, v_u())?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Pi(name, a_tm, b_tm)), v_u()))
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

    /// `displayMetas`：metacontext 逐条打印（未解 `let ?m = ?;`，已解
    /// `let ?m = <nf>;`），末尾空行。`elab` 模式用。
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
    env: Option<&'a EnvCons<'a>>,
    /// type of every variable in scope（头 = 最内层，服务名字查找与报错）
    types: Option<&'a TCons<'a>>,
    /// fresh meta 抽象的槽位掩码（与 env 平行；`bound = true` 槽位是实参）
    bds: Option<&'a BdCons<'a>>,
    lvl: u32,
    /// 名字撤销轨迹的本上下文基线：不变量 `trail.len() == cxt.mark` 在
    /// 上下文"现役"时恒成立。binder 递归返回后按父 mark 截断恢复。
    mark: u32,
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
        Cxt { env: None, types: None, bds: None, lvl: 0, mark: 0, pos }
    }

    /// Extend Cxt with a bound variable.
    fn bind(self, bump: &'a Bump, x: &'a str, a: V) -> Cxt<'a> {
        Cxt {
            env: Some(bump.alloc(EnvCons { val: v_lvl(self.lvl), next: self.env })),
            types: Some(bump.alloc(TCons { name: x, ty: a, next: self.types })),
            bds: Some(bump.alloc(BdCons { bound: true, next: self.bds })),
            lvl: self.lvl + 1,
            mark: self.mark + 1,
            pos: self.pos,
        }
    }

    /// Extend Cxt with a definition.
    fn define(self, bump: &'a Bump, x: &'a str, t: V, a: V) -> Cxt<'a> {
        Cxt {
            env: Some(bump.alloc(EnvCons { val: t, next: self.env })),
            types: Some(bump.alloc(TCons { name: x, ty: a, next: self.types })),
            bds: Some(bump.alloc(BdCons { bound: false, next: self.bds })),
            lvl: self.lvl + 1,
            mark: self.mark + 1,
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
    use super::BD;
    use crate::list::List as CList;
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
            Tm::Var(_) | Tm::U | Tm::Meta(_) => {}
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

/// A/B 实验开关（Raw::Var 名字解析消融）：置 `L03_NO_NAME_MAP=1` 回落为
/// 沿 `types` 链的线性找名（`=0` 不关闭；map 的维护照常，trail 语义不受
/// 开关影响）。
static NO_NAME_MAP: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(
            std::env::var("L03_NO_NAME_MAP").is_ok_and(|v| v != "0"),
        )
    });

/// 稳态类型检查器：owns 一个反复 `reset` 的 `Bump` 与跨调用复用的
/// [`Machine`]（spine/vals/metacontext）。`bump.reset` 不跑析构（bumpalo
/// 语义），spine/vals 里的旧指针字在下轮 eval/quote 开头即被 clear，
/// 悬垂无碍。
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
    /// 参考版处理）。nf/type 的引读默认走 **quote 记忆化**（输出逐字节
    /// 一致；复制强制负载 1.9-3.6×，其余负载持平——见 dup 负载与 readme
    /// 「实测结果」）。
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
                    let v = self.machine.eval(bump, None, t);
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

    /// 基准口径（bench 用）：仅 check（unify/求解工作负载的转换检查发生在
    /// check 里）。
    pub(crate) fn bench_check(&mut self, raw: &Raw) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine
            .infer(bump, Cxt::empty(super::initial_pos()), raw)
            .is_ok()
    }

    /// 基准口径：check + nf（quote），返回结果树节点数（工作量佐证）。
    pub(crate) fn bench_check_nf(&mut self, raw: &Raw) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
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

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径（dup 负载的主对比行）。
    pub(crate) fn bench_check_nf_memo(&mut self, raw: &Raw) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        match self.machine.infer(bump, Cxt::empty(super::initial_pos()), raw) {
            Err(_) => 0,
            Ok((t, _)) => {
                let v = self.machine.eval(bump, None, t);
                let n = self.machine.quote_memo(bump, 0, v);
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
}// 基准负载生成器（l03bench 共用）
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
/// ——check 内 unify 强制 `(add p_k zero)` 与 `p_k` 完整展开后结构比较
/// （转换检查工作负载；无洞，L02 conv 的同款源）。
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

/// conv_dup（判等记忆化的命中负载，L02 conv_dup 同款源）：`Rel` 的余定义域
/// 重复谓词 `P x -> P y -> P y` 让 check 把 `(add p_k zero, p_k)` 这对比较
/// **3 次**（x、y、y 各一次）——记忆化把第 2/3 次塌缩为查表。
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

/// chain（名字解析负载）：n = 2^(k+1) 条顶层 let 链 `p_i = add p_{i-1} p0`
/// ——每层都引用 scope 深处最老的名字（`add`/`p0`），线性走链解析是
/// O(n²)；名字 map 下 O(n)。check-only（无 quote），每层推导本身 O(1)，
/// 工作量几乎全部来自名字解析。参考版在此负载同样 O(n²)（同款线性找名
/// ——上游逐函数对应），大 k 段用 `--only fast` 跑。
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

/// solve 2^(k+1)（L03 的特色负载）：`Eq _ p_k p_k = refl _ _`——期望侧
/// 的两个 `_` 挂洞，`refl` 的实参侧也挂洞，check 的 unify 触发三个求解：
/// 两个小解 + 一个 `? := p_k` 的大解——rename 沿 church 展开的整条 neutral
/// 链走（每层 λ 剥离 + 体求值 + spine 游走），是参考版递归 rename 的
/// 深度压力、性能版 ren 任务栈/force 迭代的主展示负载。
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

/// dup 2×（复制强制负载）：church 2^(k+1) 之上 `D p_k`（`D = \x f. f x x`），
/// nf = `λf. f C C`——λ-binder 把同一闭包值 C 复制进两个实参槽，quote 对它
/// **强制 2 次**（无记忆化时）。nf 节点数 = 4n + 12（n = 2^(k+1)）。
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

/// dup 4×（两层复制）：`D1 (D0 p_k)`，nf =
/// `λf. f (λf'. f' C C) (λf'. f' C C)`——C 被强制 **4 次**（无记忆化时）。
/// nf 节点数 = 8n + 28。
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
    use super::super::{church_nf, EX0_SRC, EX1_SRC, EX2_SRC};
    use super::*;

    #[test]
    fn ex1_nf_and_type() {
        assert_eq!(
            main_with("nf", EX1_SRC),
            "λ N s z. s (s z)\n  :\n(N : U) → (N → N) → N → N\n"
        );
        assert_eq!(
            main_with("type", EX1_SRC),
            "(N : U) → (N → N) → N → N\n"
        );
    }

    #[test]
    fn ex2_church_hundred() {
        assert_eq!(main_with("nf", EX2_SRC), super::super::ex2());
    }

    #[test]
    fn ex0_elab_matches_basic() {
        assert_eq!(main_with("elab", EX0_SRC), super::super::ex0());
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
        // λ N s z. s^65536 z：3 个 Lam + 65536 个 App + 65537 个 Var
        assert_eq!(size, 3 + 65536 + 65537, "nf node count");
    }

    /// solve 工作负载：`Eq _ p_k p_k = refl _ _` 的检查在 check 内触发
    /// `? := p_k` 的大解——rename 沿 church 展开链走（16384 级），迭代
    /// rename/force 深度无上限。
    #[test]
    fn solve_stress_16384() {
        let src = solve_src(13);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut tycker = Tycker::new();
        assert!(tycker.bench_check(&raw));
    }

    /// solve 判定与参考版一致（type-mode 输出逐字节互检，k=8 时参考版
    /// recursion 深度可控）。
    #[test]
    fn solve_matches_basic() {
        let src = solve_src(8);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert_eq!(
            t.run("type", &src, &raw),
            super::super::main_with("type", &src),
            "solve 判定与参考版不一致"
        );
    }

    /// conv_dup 判等记忆化负载：判定通过，且与参考版 type-mode 输出逐字节
    /// 一致（Store 屏障入表时机的回归测试——屏障弹早了会出现"未比完先
    /// 入表"的假命中）。
    #[test]
    fn conv_dup_check_passes() {
        let src = conv_dup_src(10);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "conv_dup 未通过（memo 屏障有误？）");
        let mut t = Tycker::new();
        assert_eq!(
            t.run("type", &src, &raw),
            super::super::main_with("type", &src),
            "conv_dup 判定与参考版不一致"
        );
    }

    /// chain 名字解析负载：判定通过，且与参考版 type-mode 输出逐字节一致
    /// （map 路径 vs 参考版线性 walk 的解析一致性；shadowing/恢复语义由
    /// 全量互检兜底）。
    #[test]
    fn chain_check_passes() {
        let src = chain_src(8);
        let Some(raw) = super::super::parser::parser(&src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "chain 未通过（名字 map 有误？）");
        let mut t = Tycker::new();
        assert_eq!(
            t.run("type", &src, &raw),
            super::super::main_with("type", &src),
            "chain 判定与参考版不一致"
        );
    }

    /// 名字 map 的 shadowing 语义：`\x. x` 的 binder 遮蔽外层同名 def，
    /// 该 binder 作用域退出后 x 必须还原为 def（`apply (\x. x) x` 的第二
    /// 实参解析到 def）——map 路径的解析结果与参考版（线性 walk）逐字节
    /// 一致。unwind 漏掉时第二实参会解析到已退出的 binder（错位索引）。
    #[test]
    fn name_map_shadowing_matches_basic() {
        let src = "\
         let Nat : U = (N : U) -> (N -> N) -> N -> N;\n\
         let two : Nat = \\N s z. s (s z);\n\
         let x : Nat = two;\n\
         let apply : (Nat -> Nat) -> Nat -> Nat = \\f a. f a;\n\
         let test : Nat = apply (\\x. x) x;\n\
         test\n";
        let Some(raw) = super::super::parser::parser(src, 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert_eq!(
            t.run("nf", src, &raw),
            super::super::main_with("nf", src),
            "shadowing 解析与参考版不一致"
        );
        // 结果佐证：apply id two ≡ two（church 2）
        assert!(t.run("nf", src, &raw).contains("s (s z)"), "{:?}", t.run("nf", src, &raw));
    }

    /// 稳态复用正确性：同一 Tycker 连续多轮（Bump::reset + Machine 复用 +
    /// metacontext 清空），输出与每轮新建的 Tycker 一致。
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
    fn unify_failure_message() {
        let src = "let id : (A : U) -> A -> A\n  = \\A x. x;\nlet bar : U = id id;\nbar\n";
        assert_eq!(main_with("nf", src), super::super::main_with("nf", src));
        let out = main_with("nf", src);
        assert!(out.contains("Cannot unify expected type"), "{out}");
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
            assert_eq!(t.run("nf", &src, &raw), basic, "memo 默认口径不一致");
            let mut t = Tycker::new();
            assert_eq!(
                t.run_no_memo("nf", &src, &raw),
                basic,
                "非 memo 对照口径不一致"
            );
        }
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
        tycker.machine.clear_round();
        let bump = &tycker.bump;
        let Ok((t, _)) = tycker.machine.infer(bump, Cxt::empty(super::super::initial_pos()), &raw)
        else {
            panic!("infer failed");
        };
        let v = tycker.machine.eval(bump, None, t);
        let Tm::Lam(_, Tm::App(Tm::App(_, c1), c2)) = tycker.machine.quote_memo(bump, 0, v) else {
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

    /// memo 表随每次 quote 调用新建：同一 Tycker 反复 reset+quote，memo
    /// 默认口径输出始终与每轮新建的 Tycker 一致（跨轮悬垂键回归测试）。
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