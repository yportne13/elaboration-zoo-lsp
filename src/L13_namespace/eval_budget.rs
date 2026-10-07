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
//! 预算只能拦"迭代多"的循环，拦不住"单步分配多"的循环：原生 Nat 的
//! succ 链展开是 `for _ in 0..k` 的裸分配（k 来自运行期值），链循环里没有
//! checkpoint——`println (nat_mul 100000 100000)`（k=10^10）会在预算到期前
//! 就把提交量顶到 121.8 GB 并拖垮主机（见 [`NAT_CHAIN_LIMIT`]）。故本模块
//! 另提供**分配量护栏** `guard_nat_chain`：与预算无关、无条件生效，超限
//! 抛 [`NatChainOverflow`]（同属本模块的"主动中止"族，边界口径一致）。
//!
//! 预算是"只收紧"作用域：`scope` 取与现存 deadline 的较早者，退出恢复；
//! `scope_default` 仅在未设预算时生效（CLI `--max-infer-ms` 的显式值优先
//! 于 on_change 的默认预算）。prelude prime 不设预算（可信输入，且 prime
//! 本身 ~3.3s 不该被文件级预算误伤）。

use std::cell::Cell;
use std::time::{Duration, Instant};

/// 中止 payload：checkpoint 超预算时抛出，边界 `is_timeout` 识别；
/// 非本族 payload 的 panic 一律 resume_unwind 原样上抛。
pub struct ElabTimeout;

/// 中止 payload 之二：原生 `Nat(k)` → succ/zero 链的单次展开节点数超
/// [`NAT_CHAIN_LIMIT`]。与 [`ElabTimeout`] 同族（[`is_timeout`] 对两者都
/// 返回 true）——语义是"本引擎无法在安全资源内完成这次运行"，边界的
/// catch_unwind 一律按放弃本次引擎运行处理（孪生作废 resident 并回落
/// 参考版），**不是** bug，不该 resume_unwind 打到用户面前。
pub struct NatChainOverflow {
    pub k: u64,
    pub limit: u64,
}

/// 中止 payload 判定（"本引擎主动中止"族）：预算超时 **或** 链展开超限。
/// 名字保留 `is_timeout`（既有调用点口径），但含义是"资源护栏中止"。
pub fn is_timeout(p: &(dyn std::any::Any + Send)) -> bool {
    p.downcast_ref::<ElabTimeout>().is_some() || p.downcast_ref::<NatChainOverflow>().is_some()
}

/// 原生 `Nat(k)` 展开成 succ/zero 链的节点数上限（内存护栏）。
///
/// 为什么必须有它（而不是只靠上面的时间预算）：`quote_nat_chain`
/// （孪生 `bump_spine_iter/quote.rs`）、`quote_nat`（参考版本文件
/// `mod.rs`）与 prim 的 NatAdd/NatMul 回退链都是 `for _ in 0..k` 的**裸
/// 分配循环**，k 由运行期求值出的值决定、与源码长度无关；而这些循环里
/// 一个 checkpoint 都没有（`tick` 只在两版 eval 主循环，见上），所以预算
/// 到期也拦不住——内存先到极限。
///
/// 实锤（2026-10-07）：`println (nat_mul 100000 100000)` 的 k = 10^10，
/// 孪生显示位 `quote` 展开该链需要 ~10^11 字节；lib 套件里的
/// `eval_budget_tests::twin_big_nat_display_aborts_via_chain_guard`
/// 把该进程提交量顶到 **121.8 GB**（Windows 事件 2004 记录），
/// 触发系统级虚拟内存耗尽，主机非正常重启（事件 41/6008）。同一二进制
/// 在 3 小时内触发 3 次（21:53 崩溃、23:21 与 23:43 各一次）。
///
/// 取值 2^22 = 4,194,304 节点 ≈ 单次展开 ≤ ~0.4 GB（Tm 链节点约
/// 100 B/节点）：比仓库内全部语料与测试实际用到的 Nat（< 10^4）高 3 个
/// 数量级——**不改变任何现存输入的行为**，同时把最坏单次分配钉死。
/// 超限即 [`NatChainOverflow`]：孪生侧由 LSP 边界回落参考版（参考版显示
/// 走 `quote_dec` 十进制，用户拿到的输出仍然正确），CLI 侧落一条诊断。
pub const NAT_CHAIN_LIMIT: u64 = 1 << 22;

/// 链展开前的 O(1) 护栏：超 [`NAT_CHAIN_LIMIT`] 立即中止，**不**开始分配。
/// 有预算无预算都生效——内存安全不能依赖调用方是否设了时间预算。
#[inline]
pub fn guard_nat_chain(k: u64) {
    if k > NAT_CHAIN_LIMIT {
        std::panic::panic_any(NatChainOverflow { k, limit: NAT_CHAIN_LIMIT });
    }
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
