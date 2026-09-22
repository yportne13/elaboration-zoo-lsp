//! subst：模式特化的显式替换（`SubstV`/`SubEntryV`/`SUBSTV_ALIVE`）、σ 克隆
//! 的跨轮回收（`VSUB_REGS`/`vsub_reclaim`）、读点包裹（`wrap_sub`）、浅扫描
//! （`mentions_level`）、穿参状态（`SpecSolve`），以及卡住 match 分支体
//! 重求值用的 `simpl_decl`。原 bump_spine_iter.rs 的 SubstV 定义 +
//! "σ 克隆的跨轮回收" 节 + simpl_decl 块，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::Env;
use super::prim::DeclEntryF;
use super::spine::Spine;
use super::syntax::{V, v_clo_of, v_lvl_of, v_pi_of, v_spine_of, v_tag, v_xcell, v_xcell_of, XCell};

/// 模式特化的解：层级 → 值 的**持久化单链**（参考版 `Subst` 同构；链头 =
/// 最新的解）。仅由模式编译器经 [`SubstV::extend`] / 特化合一的
/// [`SpecSolve::acc`] 构建；`Rc` 共享让臂边界回滚 = 指针赋值、VSub 包裹
/// = O(1)。与旧 `pm_defs` 事实表的对应：`extend` ≙ `pm_solve` + push
/// （链头即最新，查询沿链首个命中 ≙ `rev().find` 取最新），`lookup_hit`
/// ≙ force 读点的查表展开——区别在于解只对**被包裹过的值**可见（读点
/// 显式），不再是全局查找表。
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
/// ([SUBSTV_ALIVE])；一次原子加减发生在 extend / compose 的分配与 Rc
/// 归零的 Drop 时机，均非热路径。观察泄漏同样有效：arena 克隆泄漏 ⇒ 其
/// head 链的条目引用不归还 ⇒ 计数不回落。
pub(crate) static SUBSTV_ALIVE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

impl Drop for SubEntryV {
    fn drop(&mut self) {
        SUBSTV_ALIVE.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// --------------------------------------------------------------------------------
// σ 克隆的跨轮回收（2026-09-18，README §7.7 的落地；L07 孪生版同款移植）
// --------------------------------------------------------------------------------
// bump `reset()` 不跑 Drop：arena 内 `XCell::VSub` 持有的 `Rc<SubstV>` 克隆
// 的强引用永不归还，链（及后缀）跨轮慢泄漏。登记表在 [`wrap_sub`] 构造
// 克隆的**同一时刻**记录 `Rc::as_ptr`，轮界（[`Machine::clear_round`]，与
// 三处 `bump.reset()` 严格伴生）逐指针 `Rc::from_raw` + drop。
//
// SAFETY（恰好归还"arena 那一份"强引用，等价于被跳过的 Drop）：
// - 指针在登记到归还之间始终有效：arena 克隆持强引用，外部持有者
//   （`Compiler.sub`、链共享）只会让计数更多，不会提前释放节点；
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

    /// x 是否已有解（旧 `pm_def(x).is_none()` 的否定形式）。
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

    /// 叠加一条解 `x := v`：O(1) cons 到链头（链头 = 最新 ≙ 旧 `pm_def`
    /// 的 `rev().find` 取最新；同键旧条目留在链上但永不命中）。
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
/// 同款遍历面）。含闭包 **env 槽**（它们是值，读点会流出）与 Match 的
/// scrutinee/captured env/pending；不含闭包体 / Match 分支体（Tm，求值时
/// 才经 env 读到槽值）。VSub 保守记为引用（已包过 σ 的值再包一层无害）。
/// Flex 只扫 spine。误报只多一次包裹，漏报才会丢精化——宁宽勿窄。
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
            let v = defs[(env.flat_base + env.flat_len - 1 - k) as usize];
            if mentions_level(spine, defs, v, sub) {
                return true;
            }
        }
        false
    }
    match v_tag(v) {
        // Rigid 裸头：该层级已被 σ 解出即引用
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
            if head_hit {
                return true;
            }
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args);
            args.iter().any(|(a, _)| mentions_level(spine, defs, *a, sub))
        }
        // Flex 裸头 / U / LiteralType：无引用
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
            // 已被包裹的值保守视为引用（内层结构不再探查）
            XCell::VSub { .. } => true,
            XCell::Lit(_) | XCell::Decl(_) | XCell::Prim(_) => false,
            XCell::Obj { val, .. } => mentions_level(spine, defs, *val, sub),
            XCell::Sum { params, .. } => params.iter().any(|p| {
                mentions_level(spine, defs, p.val, sub) || mentions_level(spine, defs, p.ty, sub)
            }),
            XCell::SumCase { typ, datas, .. } => {
                mentions_level(spine, defs, *typ, sub)
                    || datas.iter().any(|d| mentions_level(spine, defs, d.val, sub))
            }
            XCell::Match {
                scrutinee,
                env,
                pending,
                ..
            } => {
                mentions_level(spine, defs, *scrutinee, sub)
                    || env_slots(spine, defs, *env, sub)
                    || pending
                        .iter()
                        .any(|(u, _)| mentions_level(spine, defs, *u, sub))
            }
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
        // Rc::from_raw + drop 会按未发生的 +1 过度递减引用计数（评审 P2）
        VSUB_REGS.with(|r| r.borrow_mut().push(Rc::as_ptr(sub)));
        v_xcell(cell)
    }
}

/// 特化合一的进行时状态（参考版 `SpecSolve` 同构）。`solvable` = 本子句
/// 可解的 rigid 层级（模式槽 + 外层 bind 槽基线）；`acc` = 已解出的替换
/// ——编译器的 σ 作种子，方程途中叠加，调用方在方程结束后取走 `acc`
/// 作为新 σ（臂边界回滚 = 恢复快照指针）。
pub(crate) struct SpecSolve<'a> {
    pub(crate) solvable: &'a [u32],
    pub(crate) acc: Rc<SubstV>,
}
// quote/rename 卡住 match 的分支体时用的 decl 表：所有全局值换成指向自身
// 的中性 `Decl`，防止递归定义在求值分支体时被重展开。enum 类型本体的值
// （`Sum`）保持原样——构造子值的 `typ` 槽需要真实的 Sum 值。（参考版
// `simpl_decl` 同款；快版直接克隆表替换 val——与参考版逐条目换值同构，
// 无需给内核加"中性全局"开关。）
pub(super) fn simpl_decl(bump: &Bump, decls: &FxHashMap<String, DeclEntryF>) -> FxHashMap<String, DeclEntryF> {
    decls
        .iter()
        .map(|(k, e)| {
            let val = if v_tag(e.val) == 7 && matches!(v_xcell_of(e.val), XCell::Sum { .. }) {
                e.val
            } else {
                v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(k))))
            };
            (k.clone(), DeclEntryF { ty: e.ty, val })
        })
        .collect()
}
