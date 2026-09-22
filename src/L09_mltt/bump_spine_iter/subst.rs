//! subst：显式替换（`SubstV`/`SubEntryV`/`SUBSTV_ALIVE`）、σ 克隆的跨轮回收
//! （`vsub_reclaim`）、浅扫描（`mentions_level`）、读点包裹（`wrap_sub`）、
//! 穿参状态（`SpecSolve`）。原 bump_spine_iter.rs 的 SubstV 定义 +
//! "σ 克隆的跨轮回收" 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::Env;
use super::spine::Spine;
use super::syntax::{V, XCell, v_clo_of, v_lvl_of, v_pi_of, v_spine_of, v_tag, v_xcell, v_xcell_of};

/// 模式特化的解：层级 → 值 的**持久化单链**（参考版 `Subst` 同构；链头 =
/// 最新的解）。仅由模式编译器经 [`SubstV::extend`] / 特化合一的
/// [`SpecSolve::acc`] 构建；`Rc` 共享让臂边界回滚 = 指针赋值、VSub 包裹
/// = O(1)。取代旧 `update_cxt` 的上下文改写（改写目标槽 + 全槽 refresh）。
#[derive(Clone, Default)]
pub(crate) struct SubstV {
    head: Option<Rc<SubEntryV>>,
}

struct SubEntryV {
    lvl: u32,
    /// 解的原始值。不预先包裹"更新的解"——读取时 `lookup_hit` 把整条 σ
    /// 包在外面（条件包裹，见其文档），由 force 在读点一次性推开。
    val: V,
    next: Option<Rc<SubEntryV>>,
}

/// 存活的 σ 链条目数（`SubEntryV` 各计 1；头壳 `SubstV` 带 `Clone` derive、
/// 值级复制会破坏计数配对，故不计）。仅为跨轮回收的回归测试提供观察口
/// （[SUBSTV_ALIVE]）；一次原子加减发生在 extend / compose 的分配与 Rc
/// 归零的 Drop 时机，均非热路径。观察泄漏同样有效：arena 克隆泄漏 ⇒ 其
/// head 链的条目引用不归还 ⇒ 计数不回落。
pub(crate) static SUBSTV_ALIVE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

impl Drop for SubEntryV {
    fn drop(&mut self) {
        SUBSTV_ALIVE.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// --------------------------------------------------------------------------------
// σ 克隆的跨轮回收（L07 2026-09-18 修复轮的 L09 移植，README §7.7 的落地）
// --------------------------------------------------------------------------------
// bump `reset()` 不跑 Drop：arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆
// 的强引用永不归还，链（及后缀）跨轮慢泄漏。登记表在 [`wrap_sub`] 构造
// 克隆的**同一时刻**记录 `Rc::as_ptr`，轮界（[`Machine::clear_round`]，与
// 三处 `bump.reset()` 严格伴生）逐指针 `Rc::from_raw` + drop。
//
// SAFETY（恰好归还"arena 那一份"强引用，等价于被跳过的 Drop）——按 L09
// 实际代码逐条核对（2026-09-18 移植轮）：
// - **构造点唯一**：`XCell::VSub` 在本层孪生里仅 [`wrap_sub`] 一处构造
//   （subst_cxt / frcs / unify_pm 的包裹全部经 [`wrap_sub`]），登记点与
//   构造点一一对应，不存在绕过登记的 arena 克隆；
// - 指针在登记到归还之间始终有效：Rc 节点在全局堆上（arena 只持有
//   克隆），arena 克隆持强引用 ⇒ 计数 ≥ 1，节点不会在归还前释放；外部
//   持有者（编译器局部 σ、链共享）只会让计数更多，不会提前释放节点；
// - 同一节点被 wrap 多次 = 多个克隆 = 多次登记 = 多次减一，各归还各的；
// - 表外持有者不受影响：归还后节点若仍有引用则继续存活（正常 Rc 语义），
//   归零则连同后缀级联释放（后缀条目有自己的计数与 Drop）；
// - [`vsub_reclaim`] 后表已清空（drain），旧指针不会跨轮重复 drop；
// - **线程模型**：`Rc<SubstV>` 非 Send ⇒ 持有 σ 的 Tycker 不可跨线程移动，
//   wrap_sub 与 clear_round 必在同一线程执行，thread_local 登记表所见即
//   所用；线程退出时表随 thread_local 析构（只丢指针，不 from_raw），
//   未归还份额即普通泄漏，无悬垂解引用。
thread_local! {
    static VSUB_REGS: std::cell::RefCell<Vec<*const SubstV>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// 轮界归还 arena 内的全部 σ 克隆（与 `bump.reset()` 伴生）。
pub(super) fn vsub_reclaim() {
    VSUB_REGS.with(|r| {
        for p in r.borrow_mut().drain(..) {
            // SAFETY：见上——p 来自 wrap_sub 登记的 Rc 克隆，本调用归还其
            // arena 份额且仅此一次（表已 drain）。
            drop(unsafe { Rc::from_raw(p) });
        }
    });
}

impl SubstV {
    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配零 fuel；`mentions_level` 浅扫描）；引用时把
    /// 整条 σ 包在解值外（解值不含 x 自身——occurs 守卫；比该条目更新的
    /// 解恰好借此对解值生效），由 force 在读点推开。未命中 None。
    pub(super) fn lookup_hit<'a>(
        bump: &'a Bump,
        spine: &Spine,
        defs: &[V],
        sub: &Rc<SubstV>,
        x: u32,
    ) -> Option<V> {
        let mut cur = sub.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return Some(if !mentions_level(spine, defs, e.val, sub) {
                    e.val
                } else {
                    wrap_sub(bump, sub, e.val)
                });
            }
            cur = e.next.clone();
        }
        None
    }

    /// x 是否已有解。
    pub(super) fn has(&self, x: u32) -> bool {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return true;
            }
            cur = e.next.clone();
        }
        false
    }

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新）。
    pub(super) fn extend(sub: &Rc<SubstV>, x: u32, v: V) -> Rc<SubstV> {
        SUBSTV_ALIVE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Rc::new(SubstV {
            head: Some(Rc::new(SubEntryV {
                lvl: x,
                val: v,
                next: sub.head.clone(),
            })),
        })
    }

    /// 组合：内层 `inner` 先应用、外层 `outer` 后应用。外层条目接到链头
    /// （先被查到 = 覆盖同键，"取最新"语义）。
    pub(super) fn compose(outer: &Rc<SubstV>, inner: &Rc<SubstV>) -> Rc<SubstV> {
        fn cons_all(
            entry: &Option<Rc<SubEntryV>>,
            onto: Option<Rc<SubEntryV>>,
        ) -> Option<Rc<SubEntryV>> {
            match entry {
                None => onto,
                Some(e) => {
                    SUBSTV_ALIVE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    Some(Rc::new(SubEntryV {
                        lvl: e.lvl,
                        val: e.val,
                        next: cons_all(&e.next, onto),
                    }))
                }
            }
        }
        Rc::new(SubstV {
            head: cons_all(&outer.head, inner.head.clone()),
        })
    }
}

/// 解值的浅结构是否引用 σ 的某个已解层级（参考版 `Subst::mentions_level`
/// 同款遍历面）。含闭包 **env 槽**与 Match 的 scrutinee/captured env；不含
/// 闭包体 / Match 分支体。VSub 保守记为引用。Flex 只扫 spine。误报只多
/// 一次包裹，漏报才会丢精化——宁宽勿窄。
fn mentions_level(spine: &Spine, defs: &[V], v: V, sub: &SubstV) -> bool {
    fn env_slots(spine: &Spine, defs: &[V], env: Env<'_>, sub: &SubstV) -> bool {
        let mut n = env.binds;
        while let Some(e) = n {
            if mentions_level(spine, defs, e.val, sub) {
                return true;
            }
            n = e.next;
        }
        for k in 0..env.flat_len {
            if mentions_level(
                spine,
                defs,
                defs[(env.flat_base + env.flat_len - 1 - k) as usize],
                sub,
            ) {
                return true;
            }
        }
        false
    }
    match v_tag(v) {
        0 => sub.has(v_lvl_of(v)),
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            let head_hit = match v_tag(hd) {
                0 => sub.has(v_lvl_of(hd)),
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, .. } => mentions_level(spine, defs, *val, sub),
                    XCell::VSub { .. } => true,
                    _ => false,
                },
                _ => false,
            };
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args);
            head_hit || args.iter().any(|(a, _)| mentions_level(spine, defs, *a, sub))
        }
        5 | 3 | 6 => false,
        1 => {
            let c = v_clo_of(v);
            env_slots(spine, defs, c.env, sub)
        }
        4 => {
            let p = v_pi_of(v);
            mentions_level(spine, defs, p.dom, sub) || env_slots(spine, defs, p.env, sub)
        }
        7 => match v_xcell_of(v) {
            XCell::VSub { .. } => true,
            XCell::Lit(_) | XCell::Prim => false,
            XCell::Obj { val, .. } => mentions_level(spine, defs, *val, sub),
            XCell::Sum { params, .. } => params.iter().any(|p| {
                mentions_level(spine, defs, p.val, sub)
                    || mentions_level(spine, defs, p.ty, sub)
            }),
            XCell::SumCase { typ, datas, .. } => {
                mentions_level(spine, defs, *typ, sub)
                    || datas.iter().any(|d| mentions_level(spine, defs, d.val, sub))
            }
            XCell::Match {
                scrutinee, env, ..
            } => mentions_level(spine, defs, *scrutinee, sub) || env_slots(spine, defs, *env, sub),
        },
        _ => false,
    }
}

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc
/// clone + 一次 bump 单元，force 在消费点惰性推开）。σ 为空时零开销直通。
/// 包裹克隆进 arena 的同时登记 [`VSUB_REGS`]——轮界 [`vsub_reclaim`] 补上
/// 被 bump reset 跳过的 Drop（见其 SAFETY 注释）。
#[inline]
pub(super) fn wrap_sub<'a>(bump: &'a Bump, sub: &Rc<SubstV>, v: V) -> V {
    if sub.is_empty() {
        v
    } else {
        let cell = bump.alloc(XCell::VSub {
            val: v,
            sub: sub.clone(),
        });
        // 注册后置：alloc 成功（cell 内 clone 的 +1 已落账）才登记。若注册
        // 在前而 alloc 失败 panic 又被 catch_unwind 捕获，轮界 reclaim 的
        // Rc::from_raw + drop 会按未发生的 +1 过度递减引用计数（L07 评审
        // P2，2026-09-18 修复 7 的同步移植）。
        VSUB_REGS.with(|r| r.borrow_mut().push(Rc::as_ptr(sub)));
        v_xcell(cell)
    }
}
/// 特化合一的进行时状态（参考版 `SpecSolve` 同构）。`solvable` = 本子句
/// 可解的 rigid 层级；`acc` = 已解出的替换。
pub(crate) struct SpecSolve<'a> {
    pub(crate) solvable: &'a [u32],
    pub(crate) acc: Rc<SubstV>,
}
