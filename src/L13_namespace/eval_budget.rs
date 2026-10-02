//! 求值时间预算：协作式中止无终止的求值循环。
//!
//! 引擎没有终止性检查（docs/l13-quirks-analysis-2026-10.md §4）：被求值的
//! 循环定义（零参 def / println / 循环类型注解）会让迭代求值器静默自旋——
//! 不炸栈、不 OOM、无输出，LSP 主循环内联排水分析任务（drain_analysis_
//! jobs → observe_user / on_change），一次挂死即整服务冻结且无看门狗。
//!
//! 本模块提供协作式护栏：两版引擎的 eval 主循环每 2^20 次迭代做一次
//! checkpoint（局部计数器自增 + 掩码分支近乎零成本，Instant::now() 摊销后
//! 对 40M 步的 prelude 加载不可见——约 40 次调用）；超过 deadline 则
//! `panic_any(ElabTimeout)` 中止，由边界（LSP 的 twin_elaborate /
//! on_change、CLI 的 run_check）`catch_unwind` 识别：孪生侧作废 resident
//! 重 prime 并回落参考版，参考版侧把超时落成一条诊断、跳过该文件剩余
//! decl——服务与 CLI 存活，用户拿到可诊断的错误而不是永久冻结。
//!
//! 预算是"只收紧"作用域：`scope` 取与现存 deadline 的较早者，退出恢复；
//! `scope_default` 仅在未设预算时生效（CLI `--max-infer-ms` 的显式值优先
//! 于 on_change 的默认预算）。prelude prime 不设预算（可信输入，且 prime
//! 本身 ~3.3s 不该被文件级预算误伤）。

use std::cell::Cell;
use std::time::{Duration, Instant};

/// 中止 payload：checkpoint 超预算时抛出，边界 `is_timeout` 识别；
/// 非本 payload 的 panic 一律 resume_unwind 原样上抛。
pub struct ElabTimeout;

pub fn is_timeout(p: &(dyn std::any::Any + Send)) -> bool {
    p.downcast_ref::<ElabTimeout>().is_some()
}

thread_local! {
    /// `None` = 无预算（默认：prime/bench/未接线的入口不受限）。
    /// 携带设定的毫秒值供诊断文案引用（实际判定只用 Instant）。
    static DEADLINE: Cell<Option<(Instant, u64)>> = const { Cell::new(None) };
}

/// 当前生效的预算毫秒数（最紧的一个）；None = 无预算。
pub fn current_budget_ms() -> Option<u64> {
    DEADLINE.with(|d| d.get().map(|(_, ms)| ms))
}

/// 预算作用域：进入时收紧 deadline，退出（含 unwind）恢复原值。
pub struct Scope(Option<(Instant, u64)>);

impl Drop for Scope {
    fn drop(&mut self) {
        DEADLINE.with(|d| d.set(self.0));
    }
}

/// 收紧预算：新 deadline = min(现存, now + ms)。嵌套时内层先到期。
pub fn scope(ms: u64) -> Scope {
    let new = (Instant::now() + Duration::from_millis(ms), ms);
    let prev = DEADLINE.with(|d| d.replace(Some(
        d.get().map_or(new, |old| {
            if new.0 < old.0 { new } else { old }
        }),
    )));
    Scope(prev)
}

/// 仅在未设预算时生效（返回 None 表示已有外层预算、不动）。
/// on_change 用它给参考版路径兜默认预算，同时让 CLI 显式旗标（更早设好
/// 的 deadline）优先——即使旗标值比默认宽。
pub fn scope_default(ms: u64) -> Option<Scope> {
    if DEADLINE.with(|d| d.get().is_some()) {
        return None;
    }
    Some(scope(ms))
}

/// eval 主循环每迭代调用：`tick(&mut ctr)`，`ctr` 是循环外声明的局部
/// `u32`。无 deadline 时只付一次自增 + 掩码分支。
#[inline]
pub fn tick(ctr: &mut u32) {
    *ctr = ctr.wrapping_add(1);
    if *ctr & 0xF_FFFF == 0 {
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
