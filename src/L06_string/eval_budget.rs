//! eval_budget：求值时间预算——协作式中止无终止的求值（L13
//! `L13_namespace/eval_budget.rs` 的 L06 版）。
//!
//! **为什么 L06 需要它**：`run` 的求值层没有终止性保证。递归 `def`（L06 的
//! `fake_bind` 占位语义，见 `docs/l13-to-low-layer-port-audit.md` §1）在**应用**
//! 自身时经 decl 表 delta 展开，无基底即发散：`def f (x : U) : U = f x` 加上
//! `println f` 会让求值器自旋——参考版是递归 `eval`（吃栈），孪生是迭代
//! `eval_iter`（不自旋不吃栈，直接挂死）。LSP 主循环内联跑分析，一次挂死即
//! 整服务冻结，故需要协作式预算。
//!
//! **与 L13 的差异（逐条）**：
//!
//! 1. **无 `NatChainOverflow` / `guard_nat_chain`**：L13 的链护栏保护的是原生
//!    `Nat(k)` → succ 链的 `for _ in 0..k` 裸分配（k 由运行期值决定）。L06 没有
//!    原生 Nat、没有 `Tm::SumCase`（`bump_spine_iter/syntax.rs`），唯一的变长
//!    分配是字面量拼接，长度由源码字面量与输入规模界定 ⇒ 无承载面，不移植。
//! 2. **掩码 2^10 而非 2^20**：见 [`TICK_MASK`]——参考版是递归求值器，栈
//!    先于预算耗尽，checkpoint 必须落在几千帧内。掩码只改 TLS 读频率，
//!    每次 tick 的固定成本不变，实测差异不可测（见移植文档性能表）。
//! 3. **参考版 tick 挂在 `Infer::eval` 调用上（不是循环里）**：L06 参考版
//!    `eval` 是递归的，自旋形态是无限递归而不是循环，只能在每次调用处计数。
//!    孪生两侧（`eval_iter` / `force`）都是循环，用循环局部计数器。
//!
//! 预算是"只收紧"作用域：`scope` 取与现存 deadline 的较早者，退出（含 unwind）
//! 恢复；`scope_default` 仅在未设预算时生效。默认（不调用 `scope`）没有任何
//! 预算，热路径只付"自增 + 掩码分支"。

use std::cell::Cell;
use std::time::{Duration, Instant};

/// 中止 payload：checkpoint 超预算时抛出；边界 [`is_timeout`] 识别，非本族
/// payload 的 panic 一律 `resume_unwind` 原样上抛。
pub struct ElabTimeout;

/// 中止 payload 判定（"本引擎主动中止"族）。与 L13 同名同义（那里还含
/// `NatChainOverflow`；L06 无该族，见模块头）。
pub fn is_timeout(p: &(dyn std::any::Any + Send)) -> bool {
    p.downcast_ref::<ElabTimeout>().is_some()
}

thread_local! {
    /// `None` = 无预算（默认：`run` / bench / 未接线的入口不受限）。
    /// 携带设定的毫秒值供诊断文案引用（实际判定只用 `Instant`）。
    static DEADLINE: Cell<Option<(Instant, u64)>> = const { Cell::new(None) };
}

/// 是否有生效预算（`scope` 已进入）。循环入口读一次即可：无预算时热循环
/// 里只保留一次分支，不付 tick 的计数器依赖链（church/strchain 这类 eval
/// 密集微负载实测 tick 单独占 5-13%，见移植文档性能表）。
///
/// 用**进程级** relaxed 计数器而不是 TLS：`enabled()` 在每个 eval/force 循环
/// 入口都要读一次，TLS 访问（Windows DLL TLS）实测 ~1-2ns，在 church 这类
/// 十万级循环入口的负载上就吃掉 2-3%；atomic relaxed load 只需无屏障的一次
/// 普通读。代价是多线程下别的线程挂预算时本线程也会 tick（checkpoint 读到
/// 本线程 DEADLINE=None 即空转）——只是多余工作，不影响正确性。
static ACTIVE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

pub fn enabled() -> bool {
    ACTIVE.load(std::sync::atomic::Ordering::Relaxed) != 0
}

/// 当前生效的预算毫秒数（最紧的一个）；None = 无预算。
pub fn current_budget_ms() -> Option<u64> {
    DEADLINE.with(|d| d.get().map(|(_, ms)| ms))
}

/// 预算作用域：进入时收紧 deadline，退出（含 unwind）恢复原值。
pub struct Scope(Option<(Instant, u64)>);

impl Drop for Scope {
    fn drop(&mut self) {
        ACTIVE.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
        DEADLINE.with(|d| d.set(self.0));
    }
}

/// 收紧预算：新 deadline = min(现存, now + ms)。嵌套时内层先到期。
pub fn scope(ms: u64) -> Scope {
    let new = (Instant::now() + Duration::from_millis(ms), ms);
    let prev = DEADLINE.with(|d| {
        d.replace(Some(d.get().map_or(new, |old| if new.0 < old.0 { new } else { old })))
    });
    ACTIVE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    Scope(prev)
}

/// 仅在未设预算时生效（返回 None 表示已有外层预算、不动）。
pub fn scope_default(ms: u64) -> Option<Scope> {
    if DEADLINE.with(|d| d.get().is_some()) {
        return None;
    }
    Some(scope(ms))
}

/// checkpoint 的迭代掩码（2^10）。`tick` 每 2^10 次调用做一次真判定。
///
/// 为什么比 L13 的 2^20 密 1024 倍：**参考版的 `eval` 是递归的**，自旋形态
/// 是无限递归 ⇒ 栈先耗尽（本机 test 线程约 2 MiB，实测 ~7k 帧就爆），
/// checkpoint 必须落在几千帧以内才能抢在栈溢出前中止。掩码只影响 TLS 读的
/// **频率**，每次 tick 的固定成本（自增 + AND + 分支）与掩码无关——2^10 与
/// 2^20 的差异是"每 1024 步多一次 ~2ns 的 TLS 读"，在 40M 步量级上仍不可测
/// （见移植文档的性能表）。
pub const TICK_MASK: u32 = 0x3FF;

/// 循环内的 tick（孪生 `eval_iter` / `force`）：`ctr` 是循环外声明的局部
/// `u32`。无 deadline 时只付一次自增 + 掩码分支。
#[inline]
pub fn tick(ctr: &mut u32) {
    *ctr = ctr.wrapping_add(1);
    if *ctr & TICK_MASK == 0 {
        checkpoint();
    }
}

/// `&Cell` 版 tick（参考版递归 `eval` 用：`&self` 拿不到 `&mut`）。
#[inline]
pub fn tick_cell(ctr: &Cell<u32>) {
    let n = ctr.get().wrapping_add(1);
    ctr.set(n);
    if n & TICK_MASK == 0 {
        checkpoint();
    }
}

#[cold]
#[inline(never)]
fn checkpoint() {
    DEADLINE.with(|d| {
        if let Some((dl, _)) = d.get() {
            if Instant::now() >= dl {
                std::panic::panic_any(ElabTimeout);
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_budget_by_default() {
        assert_eq!(current_budget_ms(), None);
    }

    #[test]
    fn scope_restores_and_nests() {
        {
            let _outer = scope(10_000);
            assert_eq!(current_budget_ms(), Some(10_000));
            {
                // 更宽的预算不生效：deadline 取较早者 ⇒ 仍是外层的 10s
                let _inner = scope(20_000);
                assert_eq!(current_budget_ms(), Some(10_000));
            }
            assert_eq!(current_budget_ms(), Some(10_000));
            {
                let _tighter = scope(1);
                assert_eq!(current_budget_ms(), Some(1));
            }
            assert_eq!(current_budget_ms(), Some(10_000));
        }
        assert_eq!(current_budget_ms(), None);
    }

    #[test]
    fn scope_default_is_noop_when_budget_exists() {
        let outer = scope(10_000);
        assert!(scope_default(1).is_none());
        drop(outer);
        let s = scope_default(5);
        assert!(s.is_some());
        assert_eq!(current_budget_ms(), Some(5));
    }

    #[test]
    fn tick_trips_only_after_mask() {
        // 无 deadline 时 tick 永不抛出（只自增 + 掩码分支）。
        let mut ctr = 0u32;
        for _ in 0..(TICK_MASK as usize * 2 + 1) {
            tick(&mut ctr);
        }
        assert_eq!(ctr, TICK_MASK * 2 + 1);
    }

    #[test]
    fn checkpoint_trips_on_expired_deadline() {
        // deadline 已过期 ⇒ 第一个 checkpoint 就抛 ElabTimeout。
        let _s = scope(0);
        let caught = std::panic::catch_unwind(|| {
            let mut ctr = 0u32;
            for _ in 0..=TICK_MASK {
                tick(&mut ctr);
            }
        });
        let p = caught.expect_err("过期预算应在 checkpoint 抛出");
        assert!(is_timeout(&*p));
    }
}
