//! subst：模式特化的显式替换（`SubstV`/`SubEntryV`/`SUBSTV_ALIVE`）、σ 克隆
//! 的跨轮回收（`VSUB_REGS`/`vsub_reclaim`）、读点包裹（`wrap_sub`）、浅扫描
//! （`mentions_level`）与特化合一穿参状态（`SpecSolve`）。原 bump_spine_iter.rs
//! 的 SubstV 定义块 + "σ 克隆的跨轮回收" 节 + SpecSolve，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::{env_len, env_nth, Env};
use super::spine::Spine;
use super::syntax::{
    V, XCell, v_clo_of, v_lvl_of, v_pi_of, v_spine_of, v_tag, v_xcell, v_xcell_of,
};

/// 模式特化的解：层级 → 值 的**持久化单链**（参考版 `Subst` 同构；链头 =
/// 最新的解）。仅由模式编译器经 [`SubstV::extend`] / 特化合一的
/// [`SpecSolve::acc`] 构建；`Rc` 共享让臂边界回滚 = 指针赋值、VSub 包裹
/// = O(1)。替代旧的 `update_cxt`/`refresh`（改写 env 槽 + 全量重引用，
/// 值过期/槽位错位 bug 族的载体）。
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

impl SubstV {
    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// 命中返回 Some(展开前形态)：解值**不引用**任何已解层级时原样返回
    /// （读点热路径，零分配；`mentions_level` 浅扫描）；引用时把整条 σ
    /// 包在解值外（解值不含 x 自身——occurs 守卫；比该条目更新的解恰好
    /// 借此对解值生效），由 force 在读点推开。未命中 None。
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

    /// x 是否已有解（旧 `update_cxt` 的"已解"判定）。
    #[allow(dead_code)]
    fn has(&self, x: u32) -> bool {
        let mut cur = self.head.clone();
        while let Some(e) = cur {
            if e.lvl == x {
                return true;
            }
            cur = e.next.clone();
        }
        false
    }

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新 ≙ 旧 update_cxt
    /// 的后写覆盖；同键旧条目留在链上但永不命中）。
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

/// σ 链条目的存活计数（观测口，非热路径）：extend / compose 的分配 +1，
/// Rc 归零的 Drop -1。仅为跨轮回收的回归测试（fast_substv_reclaimed_
/// across_rounds）提供观察窗口——arena 克隆泄漏 ⇒ 其 head 链的条目引用
/// 不归还 ⇒ 计数不回落（L07 同款，2026-09-18 评审修复随 σ 回收移植）。
pub(crate) static SUBSTV_ALIVE: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

impl Drop for SubEntryV {
    fn drop(&mut self) {
        SUBSTV_ALIVE.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// --------------------------------------------------------------------------------
// σ 克隆的跨轮回收（L07 README §7.7 的落地，2026-09-18 评审修复移植）
// --------------------------------------------------------------------------------
// bump `reset()` 不跑 Drop：arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆
// 的强引用永不归还，链（及后缀）跨轮慢泄漏。登记表在 [`wrap_sub`] 构造
// 克隆的**同一时刻**记录 `Rc::as_ptr`，轮界（[`Machine::clear_round`]，与
// `bump.reset()` 严格伴生）逐指针 `Rc::from_raw` + drop。
//
// SAFETY（恰好归还"arena 那一份"强引用，等价于被跳过的 Drop）：
// - 指针在登记到归还之间始终有效：arena 克隆持强引用，外部持有者
//   （`Compiler` 的 σ/NestedCheck 快照、链共享）只会让计数更多，不会提前
//   释放节点；
// - 同一节点被 wrap 多次 = 多个克隆 = 多次登记 = 多次减一，各归还各的；
// - 表外持有者不受影响：归还后节点若仍有引用则继续存活（正常 Rc 语义），
//   归零则连同后缀级联释放（后缀条目有自己的计数与 Drop）；
// - [`vsub_reclaim`] 后表已清空，旧指针不会跨轮重复 drop。
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

/// "解前构建、解后消费"的值的读点纪律：用当前精化替换包裹（O(1) Rc，
/// force 在消费点惰性推开）。σ 为空时零开销直通。
/// 包裹克隆进 arena 的同时登记 [`VSUB_REGS`]——轮界 [`vsub_reclaim`] 补上
/// 被 bump reset 跳过的 Drop（见其 SAFETY 注释）。
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
        // Rc::from_raw + drop 会按未发生的 +1 过度递减引用计数（评审 P2，
        // L07 同款顺序）
        VSUB_REGS.with(|r| r.borrow_mut().push(Rc::as_ptr(sub)));
        v_xcell(cell)
    }
}

/// 解值的浅结构是否引用 σ 的某个已解层级（参考版 `Subst::mentions_level`
/// 同款遍历面）。含闭包 **env 槽**（它们是值，读点会流出）与 Match 的
/// scrutinee/captured env；不含闭包体 / Match 分支体（Tm，求值时才经 env
/// 读到槽值）。VSub 保守记为引用。Flex 的 spine 是作用域事实（含被解
/// rigid 是常态），不扫；误报只多一次包裹，漏报才丢精化——宁宽勿窄。
fn mentions_level(spine: &Spine, defs: &[V], v: V, sub: &SubstV) -> bool {
    fn env_slots(spine: &Spine, defs: &[V], env: Env<'_>, sub: &SubstV) -> bool {
        let n = env_len(env);
        (0..n).any(|i| mentions_level(spine, defs, env_nth(defs, env, i), sub))
    }
    match v_tag(v) {
        0 => sub.has(v_lvl_of(v)),
        5 | 3 | 6 => false,
        2 => {
            let h = spine.spine_head(v_spine_of(v));
            if mentions_level(spine, defs, h, sub) {
                return true;
            }
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(v_spine_of(v), &mut args);
            args.iter().any(|(a, _)| mentions_level(spine, defs, *a, sub))
        }
        1 => env_slots(spine, defs, v_clo_of(v).env, sub),
        4 => {
            let p = v_pi_of(v);
            mentions_level(spine, defs, p.dom, sub) || env_slots(spine, defs, p.env, sub)
        }
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Prim => false,
            XCell::Obj { val, .. } => mentions_level(spine, defs, *val, sub),
            XCell::Sum { params, .. } => params
                .iter()
                .any(|p| mentions_level(spine, defs, p.val, sub) || mentions_level(spine, defs, p.ty, sub)),
            XCell::SumCase { typ, datas, .. } => {
                mentions_level(spine, defs, *typ, sub)
                    || datas.iter().any(|d| mentions_level(spine, defs, d.val, sub))
            }
            XCell::Match { scrutinee, env, .. } => {
                mentions_level(spine, defs, *scrutinee, sub) || env_slots(spine, defs, *env, sub)
            }
            // 已包过的值保守视为引用（内层结构不再探查）
            XCell::VSub { .. } => true,
        },
        _ => true,
    }
}

/// 特化合一的进行时状态（参考版 `SpecSolve` 同构）。L10 的可解集 = 任意
/// 裸 Rigid（旧 `update_cxt` 对任何裸 rigid 都改写槽位），故无 `solvable`
/// 字段——臂条件即全部约束。
pub(crate) struct SpecSolve {
    pub(crate) acc: Rc<SubstV>,
}
