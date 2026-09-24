//! force：迭代 force 主循环（`force`/`force_inner`）、独立应用（`vapp1`）
//! 与值级投影（`project`），以及 force 记忆化与孪生缓存读数块
//! （`FORCE_MEMO`/`force_memo_clear`/`TWIN_STAT_*`/`twin_mem_stats`/
//! `ReclaimOnClear`——各子系统轮界清空共用的 thread_local 缓存表一并挂此，
//! 跨模块使用的表/阈值按 `pub(super)` 开放）。原 bump_spine_iter.rs 的
//! "force（迭代）" 节及其前的 v_app/project 与 memo 基础设施块，逐行搬运
//! （2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::cell::RefCell;
use std::rc::Rc;

use super::parser::syntax::Icit;

use super::env::{env_ext, env_len};
use super::eval::{eval_iter, W};
use super::prim::{prim_exec, Decls, Mutable, PrimId};
use super::quote::quote_iter;
use super::spine::{Entry, HK_DECL, HK_FLEX, MetaEntry, Spine};
use super::syntax::{
    SumDataV, Tm, V, XCell, v_clo_of, v_meta_of, v_spine_of, v_tag, v_xcell, v_xcell_of,
};
use super::PatternDetail;


/// `v.field` 的值级投影：Sum 取索引参数的值；SumCase 先查 typ 的参数（索引）
/// 再查构造子字段。其余返回 None。（参考版 eval 的 Tm::Obj 臂自带
/// unwrap-panic 语义，调用方处理；本函数只在命中时给出值。）
pub(super) fn project<'a>(v: V, name: &str) -> Option<V> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Sum { params, .. } => {
                params.iter().find(|p| p.name == name).map(|p| p.val)
            }
            XCell::SumCase { typ, datas, .. } => {
                let params = match v_xcell_of(*typ) {
                    XCell::Sum { params, .. } => params,
                    _ => return None,
                };
                params
                    .iter()
                    .find(|p| p.name == name)
                    .map(|p| p.val)
                    .or_else(|| datas.iter().find(|d| d.name == name).map(|d| d.val))
            }
            _ => None,
        },
        _ => None,
    }
}

/// 独立应用（eval_iter 之外的 v_app：force 的解值展开、prim 执行等）。
/// 逐臂对齐参考版 v_app：λ → β；Flex/Rigid（裸或链）→ spine；Decl 头 →
/// prim 检查（命中执行：`Some` 直接返回、`None` 压 spine 卡住）；Obj 头 →
/// spine；Call 头 → args prepend + 对 body 递归 v_app；卡住 Match → 应用
/// splice 进每个分支体（参考版 L13 的 Match 臂：quote 实参后 `Tm::App`）；
/// 其余 panic（"impossible apply"——两版同时不可达 / 同时 panic）。
#[allow(clippy::too_many_arguments)]
pub(super) fn vapp1<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    lazy_pure_prim: bool,
    f: V,
    a: V,
    i: Icit,
) -> V {
    // tick 补点：force 的未打点调用方（tag-7 区间归因用）。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    if v_tag(f) == 1 {
        let c = v_clo_of(f);
        let env = env_ext(bump, c.env, a);
        eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
    } else if v_tag(f) == 2 {
        // 链头：Decl 头先查 prim（带全部既有实参 + 新实参执行）。顶端槽的
        // `hk` 让非 Decl 链免去整趟走底——每次中性应用都省这一笔。
        // lazy_pure_prim（eval 语境）= 纯 prim 不在 eval 点执行：纯 prim 的
        // 结果只依赖实参，force 期归约同值——而急切执行会让"逐层字面量
        // 串接"的 def 链每层物化全串（strchain O(D²) 字节）；保持中性则
        // 最终 quote/force 一次归约 O(n)。非纯 prim 的副作用必须发生在
        // eval 点，保持急切。
        let h = v_spine_of(f);
        if spine.stack[h].hk == HK_DECL {
            let hd = spine.spine_head(h);
            if let XCell::Decl { name } = v_xcell_of(hd) {
                let name = *name;
                // 单次查表取 prim-ness（旧实现 pure 判定与执行各查一次）
                let pid = decl.get(name).and_then(|e| e.prim);
                let pure = pid.is_some_and(prim_is_pure);
                if !(lazy_pure_prim && pure) {
                    if let Some(pid) = pid {
                        if !prim_is_pure(pid) {
                            force_taint_bump();
                        }
                        let mut args: Vec<(V, Icit)> = Vec::new();
                        spine.collect_args(h, &mut args); // 逆应用序（最新在前）
                        args.reverse(); // 自然序（最老在前）
                        args.push((a, i));
                        if let Some(r) = prim_exec(
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, pid, &args,
                        ) {
                            return r;
                        }
                    }
                }
            }
        }
        spine.push(f, a, i)
    } else if v_tag(f) == 7 {
        match v_xcell_of(f) {
            XCell::Obj { .. } => spine.push(f, a, i),
            XCell::Decl { name } => {
                // 裸 Decl 单元上应用：prim 以单实参试执行（实参不足 → None
                // → 压 spine；参考版 v_app 的 Decl 臂同款）。单次查表取
                // prim-ness（旧实现 pure 判定与执行各查一次）。
                let name = *name;
                let pid = decl.get(name).and_then(|e| e.prim);
                let pure = pid.is_some_and(prim_is_pure);
                if !(lazy_pure_prim && pure) {
                    if let Some(pid) = pid {
                        if !prim_is_pure(pid) {
                            force_taint_bump();
                        }
                        let args = [(a, i)];
                        if let Some(r) = prim_exec(
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, pid, &args,
                        ) {
                            return r;
                        }
                    }
                }
                spine.push(f, a, i)
            }
            XCell::Call { name, args, body } => {
                let mut new_args: Vec<(V, Icit)> = Vec::with_capacity(args.len() + 1);
                new_args.push((a, i));
                new_args.extend_from_slice(args);
                let nb = vapp1(
                    bump, spine, work, vals, icits, defs, metas, decl, mutable,
                    lazy_pure_prim, *body, a, i,
                );
                v_xcell(bump.alloc(XCell::Call {
                    name,
                    args: bump.alloc_slice_copy(&new_args),
                    body: nb,
                }))
            }
            XCell::Match { scrutinee, env, cases } => {
                // splice：每个分支体追 `App(body, quote_l(u), i)`；quote 用
                // 独立任务栈（quote_iter 自清）。
                let l = env_len(*env);
                let u_tm = quote_iter(
                    bump,
                    spine,
                    &mut Vec::new(),
                    &mut Vec::new(),
                    work,
                    vals,
                    icits,
                    defs,
                    metas,
                    decl,
                    mutable,
                    l,
                    a,
                    None,
                );
                let new_case_vec: Vec<(PatternDetail, &'a Tm<'a>)> = cases
                    .iter()
                    .map(|(p, b)| {
                        // bump.alloc 返回 &mut，冻结成 &（collect 期望 &Tm）
                        ((*p).clone(), &*bump.alloc(Tm::App(*b, u_tm, i)))
                    })
                    .collect();
                let new_cases: &'a [(PatternDetail, &'a Tm<'a>)] =
                    bump.alloc_slice_fill_iter(new_case_vec);
                v_xcell(bump.alloc(XCell::Match {
                    scrutinee: *scrutinee,
                    env: *env,
                    cases: new_cases,
                }))
            }
            _ => panic!("impossible apply"),
        }
    } else if v_tag(f) == 3 || v_tag(f) == 4 || v_tag(f) == 6 {
        panic!("impossible apply")
    } else {
        spine.push(f, a, i)
    }
}


// force 记忆化（参考版 mod.rs `FORCE_MEMO` 的 bump 版；L13 参考版靠它把
// prelude 22.4s → 6.0s，见 docs/l13-perf-review-4.md §16）。
//
// 参考版的三根正确性支柱在 bump 模型下的处置：
// 1. **keepalive**（条目持有输入 Rc 防地址复用）——bump 同代内单调分配、
//    地址不复用，跨代 `bump.reset()` 前一切句柄已消亡；只要 memo 在每轮
//    入口清空（见 `force_memo_clear` 的调用点）即可，无需持有输入。
// 2. **taint**：walk 途中 consult 了不可抽象状态（未解 meta / 有副作用
//    prim）就 bump 计数器，动过的条目不插入。
// 3. **prim-ness 版本**：force 唯一读的 decl 表状态是名字的 prim-ness
//    （Decl / prim 两条臂）；`decl_reg` 时 prim-ness 变化即 bump 版本，
//    条目记版本、不匹配即 miss。
thread_local! {
    /// key = 输入 `V` 的打包字（仅 tag 7 复合形状入表；同代内唯一）。
    static FORCE_MEMO: RefCell<FxHashMap<u64, (V, u64)>> =
        RefCell::new(FxHashMap::default());
    static FORCE_TAINT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    pub(super) static PRIM_VERSION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// meta 就地写的撤销日志（perf-debt 评审轮）：栈非空时所有
    /// `metas[idx] = …` 写点先记 (下标, 旧值) 到栈顶；探测回滚 = 弹栈顶
    /// 逆序恢复 + 截断到探测前长度，替代整表 clone（metas 万条级时每分派
    /// 一次整拷是 prelude-hdl 慢 decl 的主因）。栈式以支持嵌套探测：
    /// 内层回滚把自身条目并入外层（内层恢复的旧值对外层而言仍是「探测期
    /// 写入」，外层回滚需继续撤销）。
    pub(super) static META_JOURNAL: RefCell<Vec<Vec<(usize, MetaEntry)>>> =
        const { RefCell::new(Vec::new()) };
    /// `declb_of` 的单条目缓存（参考版 `DECLB_CACHE` 同款移植）：Match/Match
    /// unify、quote、rename 每碰到一对 Match 值就重建整张 decl 存根表（O(D)
    /// 键克隆 + 2 次 bump 分配/条目），adder_proof 这类 Match/Match 密集证明
    /// 每 decl 数千次。键 = (decl 表地址, len)：decl 表是 COW `Rc`，轮内
    /// `Rc::make_mut` 重分配换地址即自然 miss 重建；(addr, len) 双键挡住
    /// 同轮 free→realloc 同址不同内容的 ABA。**存放口径 'static**：条目全
    /// 指向当轮 bump（与 `unify_stack` 同纪律），`force_memo_clear()`——每个
    /// `bump.reset()` 轮入口的唯一钩子——清空。
    pub(super) static TWIN_DECLB_CACHE: RefCell<Option<(usize, usize, Rc<Decls<'static>>)>> =
        const { RefCell::new(None) };
    /// quote 的 `Nat` 类型项缓存：`XCell::Nat(k)` quote 每次都要嵌套 quote
    /// 一遍闭合的 `Nat` Sum 值（轮内恒定、与层级无关）+ 两个新草稿栈。键 =
    /// Nat 值打包字（fake/真登记各一个地址，键随值换代自然失效）。轮界
    /// `force_memo_clear()` 清。
    pub(super) static QUOTE_NAT_TM: RefCell<Option<(u64, &'static Tm<'static>)>> =
        const { RefCell::new(None) };
    /// `stuck_decl` 裸 Decl 存根 intern 表（参考版 `Val::Decl` 基座共享同
    /// 款）：旧实现每次卡住都新造单元——同名基座地址永不同，位相等捷径
    /// （`t.0 == u.0`）与 conv.memo 键系统性 miss。intern 后同名存根轮内共
    /// 享同一 bump 单元（值不可变，共享即等价）。键 = 名字内容（SmolStr
    /// 内联零堆）。轮界 `force_memo_clear()` 清。
    pub(super) static STUCK_DECL_INTERN: RefCell<FxHashMap<SmolStr, V>> =
        RefCell::new(FxHashMap::default());
}

/// 条目上限；溢出整表清空（防 keepalive 钉住垃圾，代价是一次重走）。
const FORCE_MEMO_CAP: usize = 1 << 20;

/// 整表/整栈清空不归还缓冲：容量到过该量级时在轮边界主动归还，
/// 否则峰值容量会一路常驻到进程结束（LSP 是长驻进程，这一项直接算进稳态 RSS）。
/// 阈值取 [`FORCE_MEMO_CAP`] 的 1/4——小表重建比留着更贵，大表留着就是
/// 几 MB 起的空桶（1<<18 条 × ~24B ≈ 6MB）。与参考版 L13 的
/// `CACHE_SHRINK_MIN_ENTRIES` 同值同口径（`mod.rs` 的 `force_memo_clear`）。
pub(super) const CACHE_SHRINK_MIN_ENTRIES: usize = 1 << 18;
/// 工作表栈（[`Spine::stack`] 与 unify 草稿 `scratch1/scratch2`）的同一阈值：
/// 槽位（[`Entry`] 32B / `(V, Icit)` 16B）比 memo 条目小，阈值低一档
/// （1<<16 槽 ≈ 1–2MB）。
pub(super) const SPINE_SHRINK_MIN_ENTRIES: usize = 1 << 16;

/// `Vec` / `HashMap` / `HashSet` 共用的「清空 + 按阈值归还缓冲」口径
/// （三者没有公共 trait，自备一个最小版本）：`clear()` 只清条目、桶数组照留，
/// 容量到过阈值的表在清空时顺带 `shrink_to_fit()`；阈值以下照旧只 `clear()`
/// （重建比留着更贵），故常态只是「clear 前多读一次 capacity」的固定开销。
/// **只改清空的写法，不动清空时机**——时机是既有语义（地址复用、epoch、
/// 轮边界），正确性不依赖容量。
pub(super) trait ReclaimOnClear {
    /// 清空并（容量到 `min_entries` 时）归还缓冲；返回
    /// `(清空前 len, 清空后 capacity)` 供 [`twin_stat_record`] 登记。
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize);
}

impl<T> ReclaimOnClear for Vec<T> {
    #[inline]
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize) {
        let len = self.len();
        let big = self.capacity() >= min_entries;
        self.clear();
        if big {
            self.shrink_to_fit();
        }
        (len, self.capacity())
    }
}

// `shrink_to_fit` 对 hash 容器还要 `K: Hash + Eq` / `T: Hash + Eq`（std 的
// 方法界），故如下 impl 比 `clear()` 单独可用的界更紧——调用点都是具名
// 类型，无感。
impl<K, T, S> ReclaimOnClear for std::collections::HashMap<K, T, S>
where
    K: std::hash::Hash + Eq,
    S: std::hash::BuildHasher,
{
    #[inline]
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize) {
        let len = self.len();
        let big = self.capacity() >= min_entries;
        self.clear();
        if big {
            self.shrink_to_fit();
        }
        (len, self.capacity())
    }
}

impl<T, S> ReclaimOnClear for std::collections::HashSet<T, S>
where
    T: std::hash::Hash + Eq,
    S: std::hash::BuildHasher,
{
    #[inline]
    fn reclaim(&mut self, min_entries: usize) -> (usize, usize) {
        let len = self.len();
        let big = self.capacity() >= min_entries;
        self.clear();
        if big {
            self.shrink_to_fit();
        }
        (len, self.capacity())
    }
}

thread_local! {
    /// 孪生缓存读数槽（[`twin_mem_stats`] 的唯一数据源）：每个清空点登记一次
    /// `(清空前 len, 清空后 capacity)`。四张表的存储都在 `Machine` 实例里
    /// （LSP 侧实例挂在 lib.rs 的 `TWIN_RESIDENT` TLS），模块级函数取不到，
    /// 故用影子登记；纯只读观测，不参与任何求值/统一/quote 决策。
    pub(super) static TWIN_STAT_FORCE: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
    pub(super) static TWIN_STAT_CONV: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
    pub(super) static TWIN_STAT_QUOTE: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
    pub(super) static TWIN_STAT_SPINE: std::cell::Cell<(usize, usize)> =
        const { std::cell::Cell::new((0, 0)) };
}

/// 登记一次清空快照（`try_with`：TLS 未初始化/已析构则跳过，读数保持上次值）。
#[inline]
pub(super) fn twin_stat_record(
    slot: &'static std::thread::LocalKey<std::cell::Cell<(usize, usize)>>,
    snapshot: (usize, usize),
) {
    let _ = slot.try_with(|c| c.set(snapshot));
}

/// 孪生版缓存容量读数（`typort stats` 的孪生口径）。与参考版
/// `Infer::memory_stats_with_cxt`（`mod.rs`）对位：那份报 meta / 约束 /
/// 观察表，这份报孪生引擎各自的常驻缓存（`FORCE_MEMO` / unify 判等表 /
/// quote 表 / spine 栈）——孪生是 LSP 默认引擎，这些容量就是 LSP 稳态 RSS
/// 里真实占住的部分（hashbrown 的 `clear()` 不还桶数组，故关键读数是
/// shrink 后的 `capacity`）。
///
/// 口径：四张表的存储都不在本函数的可达范围（`Machine` 实例字段），故读的是
/// 清空点登记的影子快照（[`TWIN_STAT_FORCE`] 等）：
/// - `len` = 最近一次清空前该表累积的条目数（上一段用量的峰值口径）；
/// - `capacity` = 清空（必要时含 `shrink_to_fit`）后的常驻桶容量。
/// `spine` 只计 [`Spine::stack`]（`conv.scratch1/scratch2` 同受
/// [`SPINE_SHRINK_MIN_ENTRIES`] 回收，但不在本 JSON 形状里）。
///
/// `resident` / `bump_allocated_bytes` 报常量：常驻检查点与 `Bump` 都在
/// `Tycker` 实例里（`TWIN_RESIDENT` 在 lib.rs，本文件取不到），本统计口径
/// 仅覆盖表层缓存，不假装知道 LSP 侧状态。TLS 未初始化或已析构时全部字段
/// 回落到 0。
pub fn twin_mem_stats() -> serde_json::Value {
    use serde_json::json;
    let force = TWIN_STAT_FORCE.try_with(|c| c.get()).unwrap_or((0, 0));
    let conv = TWIN_STAT_CONV.try_with(|c| c.get()).unwrap_or((0, 0));
    let quote = TWIN_STAT_QUOTE.try_with(|c| c.get()).unwrap_or((0, 0));
    let spine = TWIN_STAT_SPINE.try_with(|c| c.get()).unwrap_or((0, 0));
    let entry_size = std::mem::size_of::<Entry>();
    json!({
        "force_memo": { "len": force.0, "capacity": force.1 },
        "conv_memo": { "len": conv.0, "capacity": conv.1 },
        "quote_memo": { "len": quote.0, "capacity": quote.1 },
        "spine": { "len": spine.0, "capacity": spine.1, "entry_size": entry_size },
        "resident": false,
        "bump_allocated_bytes": 0,
    })
}

/// 每轮入口清空 memo（bump.reset() 处调用；地址可能被下一代复用）。
/// 容量到过 [`CACHE_SHRINK_MIN_ENTRIES`] 时顺带归还桶数组（长驻进程里
/// 峰值容量否则活到进程结束）。
///
/// 同为「轮界清」纪律的 TLS 缓存在此一并清空：`TWIN_DECLB_CACHE` /
/// `QUOTE_NAT_TM` 的条目是当轮 bump 句柄、`STUCK_DECL_INTERN` 的值同理——
/// 本函数是每个 `bump.reset()` 轮入口的唯一汇聚点（bench / run / prelude /
/// kick 各入口均配对调用），挂这里即继承其完整失效纪律。
pub(super) fn force_memo_clear() {
    let snap = FORCE_MEMO.with(|m| m.borrow_mut().reclaim(CACHE_SHRINK_MIN_ENTRIES));
    twin_stat_record(&TWIN_STAT_FORCE, snap);
    TWIN_DECLB_CACHE.with(|c| *c.borrow_mut() = None);
    QUOTE_NAT_TM.with(|c| *c.borrow_mut() = None);
    STUCK_DECL_INTERN.with(|c| c.borrow_mut().clear());
}

/// 当前 `FORCE_MEMO` 的条目数（`L13BENCH_DECLTIME` 逐声明读数用：该表是
/// **纯缓存**，键是打包值指针，命中率与表大小共同决定 force 的单位成本）。
pub(super) fn force_memo_len() -> usize {
    FORCE_MEMO.with(|m| m.borrow().len())
}

#[inline]
fn force_taint_bump() {
    FORCE_TAINT.with(|t| t.set(t.get() + 1));
}

/// decl 条目的 prim-ness 发生变化时调用（缓存失效）。
#[inline]
pub(super) fn prim_version_bump() {
    PRIM_VERSION.with(|v| v.set(v.get() + 1));
}

/// 结果只依赖实参的 prim（可安全记忆化）；其余（mutable 全局 / 文件 IO /
/// 诊断）一律按 impure 处理。参考版 `prim_is_pure` 的 PrimId 版。
fn prim_is_pure(pid: PrimId) -> bool {
    matches!(
        pid,
        PrimId::NatAdd
            | PrimId::NatMul
            | PrimId::NatSub
            | PrimId::NatDiv
            | PrimId::NatRem
            | PrimId::NatToDec
            | PrimId::WidthRange
            | PrimId::StringConcat
            | PrimId::StrEq
            | PrimId::StrIndent2
    )
}

// force（迭代；L13 参考版 force_inner 的臂集：Flex 链 / Nat 叶 / Obj 重建
// / Call 归一 / Decl prim / SumCase typ+datas / Sum 与其余 WHNF 叶）
// --------------------------------------------------------------------------------

/// **force**：把值更新到 metacontext 的当前状态，带记忆化（参考版
/// `Infer::force` 的 memo 壳）。只有 `SumCase | Call | Obj` 三种复合形状
/// 走 memo（叶子臂是 O(1)，连哈希查找都省）。逐臂语义见 [`force_inner`]。
pub(super) fn force<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    v0: V,
) -> V {
    super::prof_count(&super::FUNC_PROF.force.1);
    // tick 补点（backlog §3）：`force` 此前零 tick，于是它的时间全被"上一个
    // tick 点"（多半是 `eval`）吸收——2026-09-23 的 self% 报告里 `eval` 独占
    // 85.8% 而无法分辨。这条声明单次 kick 就有 173 万次 force，不拆开就只能
    // 停在"eval 里"。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    let compound = v_tag(v0) == 7
        && matches!(
            v_xcell_of(v0),
            XCell::SumCase { .. } | XCell::Call { .. } | XCell::Obj { .. }
        );
    if !compound {
        let _g = super::prof_enter(&super::FUNC_PROF.force_leaves.0, &super::FUNC_PROF.force_leaves.1);
        return force_inner(bump, spine, defs, metas, decl, mutable, v0);
    }
    let key = v0.0;
    let ver = PRIM_VERSION.with(|v| v.get());
    // tick 补点：复合值走 memo 的**查找**路径（命中即返回；本点与下一个 tick
    // 之间的区间 = 一次哈希查找 + 命中返回）。用于把 `force` 的 283ns/tick
    // 拆成"值单元解引用 + memo 查找"与"真正的 force_inner"。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    if let Some(r) = FORCE_MEMO.with(|m| {
        m.borrow()
            .get(&key)
            .filter(|(_, v)| *v == ver)
            .map(|(r, _)| *r)
    }) {
        // `.0` 计时槽测的是**命中路径本身**（探针开销），不是整条 force。
        let _g = super::prof_enter(&super::FUNC_PROF.force_hits.0, &super::FUNC_PROF.force_hits.1);
        return r;
    }
    let _g = super::prof_enter(&super::FUNC_PROF.force_misses.0, &super::FUNC_PROF.force_misses.1);
    let taint0 = FORCE_TAINT.with(|t| t.get());
    let r = force_inner(bump, spine, defs, metas, decl, mutable, v0);
    // walk 途中 consult 了未解 meta / 有副作用 prim → 不插入
    if FORCE_TAINT.with(|t| t.get()) == taint0 && PRIM_VERSION.with(|v| v.get()) == ver {
        FORCE_MEMO.with(|m| {
            let mut m = m.borrow_mut();
            if m.len() >= FORCE_MEMO_CAP {
                // 表满路径：容量必已远超 `CACHE_SHRINK_MIN_ENTRIES`，清空的
                // 同时归还桶数组（否则这几十 MB 空桶常驻到进程结束）。
                twin_stat_record(&TWIN_STAT_FORCE, m.reclaim(CACHE_SHRINK_MIN_ENTRIES));
            }
            m.insert(key, (r, ver));
        });
    } else {
        // taint / prim 版本变化 → 不入表：同一形状下次还要整走一遍。
        super::prof_count(&super::FUNC_PROF.force_tainted.1);
    }
    r
}

/// force 的实际臂集（无 memo；参考版 `force_inner` 逐臂对齐）：
/// Flex（已解 → 展开应用；未解原样）、原生 Nat（WHNF 叶）、Obj（递归进内层
/// 重建）、Call（stale nat-primop 归一 / force body + 实参）、Decl（prim
/// 执行：`Some` 结果**再 force**）、SumCase（force typ + 逐 data 重建）、
/// Sum 与其余（WHNF 叶，不下钻）。
///
/// 内部的 eval_iter 调用用**本调用私有的草稿栈**：外层 eval/unify 循环的
/// work/vals 不能被清空（force 可能在它们循环体中途被调用，且经 eval_aux
/// 与本函数互递归；Decl prim 的 `Some` 结果也就地再 force）。L04-L06 的
/// force 借用调用方的栈，是因为那几章的 eval_iter 不回调 force——这个差异
/// **不是**漏同步，别往那方向改。四个 `Vec::new()` 本身不分配，只有真正
/// 下钻时才增长，早退路径零成本。
pub(super) fn force_inner<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    defs: &mut Vec<V>,
    metas: &[MetaEntry],
    decl: &Decls<'a>,
    mutable: &RefCell<Mutable>,
    v0: V,
) -> V {
    // tick 补点：真正的 forcing（memo 未命中/叶子臂）。与上面的 memo 查找点
    // 配对，把 `force` 的 ns/tick 拆成两半。
    #[cfg(feature = "sampler")]
    crate::sampler::tick();
    let mut v = v0;
    let mut work: Vec<W<'a>> = Vec::new();
    let mut vals: Vec<V> = Vec::new();
    let mut icits: Vec<Icit> = Vec::new();
    let mut args: Vec<(V, Icit)> = Vec::new();
    loop {
        match v_tag(v) {
            5 => match &metas[v_meta_of(v) as usize] {
                MetaEntry::Solved(sol, _) => v = *sol,
                _ => {
                    // 裸未解 meta：taint（参考版 force 的 Flex 臂同款）
                    force_taint_bump();
                    return v;
                }
            },
            2 => {
                // tick 补点：spine 链臂（解 flex 链 / prim 执行 / 卡住）
                #[cfg(feature = "sampler")]
                crate::sampler::tick();
                let h = v_spine_of(v);
                // 顶端槽的 `hk` 直接给出分派（省去非 flex/Decl 链的整趟走底）
                match spine.stack[h].hk {
                    HK_FLEX => {
                        let hd = spine.spine_head(h);
                        // flex 链：解应用到全部实参（应用序 = 收集序的逆序）；
                        // 每步都可能 β（参考版 vAppSp 逐步 vApp 同款）
                        match &metas[v_meta_of(hd) as usize] {
                            MetaEntry::Unsolved(..) => {
                                // 未解 meta：解会变（ns 探测还会快照回滚），
                                // 不可抽象 → taint（参考版同款）
                                force_taint_bump();
                                return v;
                            }
                            MetaEntry::Solved(sol, _) => {
                                args.clear();
                                spine.collect_args(h, &mut args);
                                let mut t = *sol;
                                for &(a, i) in args.iter().rev() {
                                    t = vapp1(
                                        bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                        decl, mutable, false, t, a, i,
                                    );
                                }
                                v = t;
                            }
                        }
                    }
                    HK_DECL => {
                        let hd = spine.spine_head(h);
                        // Decl 头的链：prim 执行（Some 结果再 force；None
                        // 卡住返回原链——参考版 force 的 Decl 臂）
                        let name = match v_xcell_of(hd) {
                            XCell::Decl { name } => *name,
                            _ => return v,
                        };
                        match decl.get(name).and_then(|e| e.prim) {
                            Some(pid) => {
                                // 有副作用 prim：重执行可观察 → taint（参考版
                                // force 的 Decl 臂 `prim_is_pure` 同款）
                                if !prim_is_pure(pid) {
                                    force_taint_bump();
                                }
                                args.clear();
                                spine.collect_args(h, &mut args);
                                args.reverse();
                                // 实参先 force 再交 prim（参考版 force 的 Decl
                                // 臂"实参先 force 再检查字面量"同款纪律）——
                                // eval 期纯 prim 保持中性（lazy_pure_prim）后，
                                // 链上实参是中性 spine，不 force 则 lit_of /
                                // Nat 检查永不命中，prim 链无法归约。
                                for a in args.iter_mut() {
                                    a.0 = force(bump, spine, defs, metas, decl, mutable, a.0);
                                }
                                // 复用本函数主栈（arm 入口处已排空，vapp1 臂
                                // :同款）——旧实现每次 prim 执行三个新 Vec
                                match prim_exec(
                                    bump, spine, &mut work, &mut vals, &mut icits, defs, metas,
                                    decl, mutable, pid, &args,
                                ) {
                                    Some(r) => {
                                        // S3 轮本地短路：force 的结果契约是规范
                                        // WHNF，循环重派发只会原样落到叶臂（至多
                                        // 白付 2~3 次必命中 memo 查询）——直接返回。
                                        // 内层仍是 memo wrapper：中间结果的 memo
                                        // 插入不受影响（命中率的来源）。
                                        return force(bump, spine, defs, metas, decl, mutable, r);
                                    }
                                    None => return v,
                                }
                            }
                            None => return v,
                        }
                    }
                    // Rigid / Obj 头的链：卡住
                    _ => return v,
                }
            }
            7 => {
                // tick 补点：tag-7 值单元臂（Nat 叶 / Obj / Call / Decl / SumCase）
                #[cfg(feature = "sampler")]
                crate::sampler::tick();
                match v_xcell_of(v) {
                // 原生 Nat 是 WHNF（定义上 succ^n zero 的压缩表示）
                XCell::Nat(_) => return v,
                // force 递归进卡住投影的内层并**重建** Obj（参考版 force
                // 的 Obj 臂；不变则原样返回）
                XCell::Obj { val, name } => {
                    let v2 = force(bump, spine, defs, metas, decl, mutable, *val);
                    if v2 == *val {
                        return v;
                    }
                    return v_xcell(bump.alloc(XCell::Obj { val: v2, name }));
                }
                XCell::Call { name, args, body } => {
                    // stale def-shape 归一：名字现被 prim 接管时，重放实参
                    // 走 prim 路径归一到与 prim 产物相同的形状（参考版
                    // force 的 Call 臂；nat_primop_symbol 预过滤 + decl 表
                    // 权威检查）
                    let name: &str = name;
                    if super::nat_primop_symbol(name).is_some()
                        && decl.get(name).is_some_and(|e| e.prim.is_some())
                    {
                        let mut acc = v_xcell(bump.alloc(XCell::Decl { name }));
                        for &(a, i) in args.iter() {
                            acc = vapp1(
                                bump, spine, &mut work, &mut vals, &mut icits, defs, metas, decl,
                                mutable, false, acc, a, i,
                            );
                        }
                        // prim 不能返回另一个 Call；Call 形态再 force 一次
                        return if v_tag(acc) == 7 && matches!(v_xcell_of(acc), XCell::Call { .. })
                        {
                            force(bump, spine, defs, metas, decl, mutable, acc)
                        } else {
                            acc
                        };
                    }
                    let bf = force(bump, spine, defs, metas, decl, mutable, *body);
                    let mut changed = bf != *body;
                    let mut new_args: Vec<(V, Icit)> = Vec::with_capacity(args.len());
                    for &(a, i) in args.iter() {
                        let af = force(bump, spine, defs, metas, decl, mutable, a);
                        if af != a {
                            changed = true;
                        }
                        new_args.push((af, i));
                    }
                    return if changed {
                        v_xcell(bump.alloc(XCell::Call {
                            name,
                            args: bump.alloc_slice_copy(&new_args),
                            body: bf,
                        }))
                    } else {
                        v
                    };
                }
                // 裸 Decl 单元：prim 以空实参试执行（各 prim 需 ≥1 实参 →
                // None 卡住；参考版 force 的 Decl 臂同款路径）
                XCell::Decl { name } => {
                    let name = *name;
                    let prim = decl.get(name).and_then(|e| e.prim);
                    match prim {
                        Some(pid) => {
                            if !prim_is_pure(pid) {
                                force_taint_bump();
                            }
                            // 复用本函数主栈（vapp1/prim 臂同款，旧实现三个新 Vec）
                            if let Some(r) = prim_exec(
                                bump,
                                spine,
                                &mut work,
                                &mut vals,
                                &mut icits,
                                defs,
                                metas,
                                decl,
                                mutable,
                                pid,
                                &[],
                            ) {
                                // S3 轮本地短路：同 Decl 链 prim 臂——结果已是
                                // 规范 WHNF，直接返回免循环重派发。
                                return force(bump, spine, defs, metas, decl, mutable, r);
                            } else {
                                return v;
                            }
                        }
                        None => return v,
                    }
                }
                // SumCase：force typ + 逐 data（副作用必须跑），变化才重建
                XCell::SumCase { typ, index, datas, is_trait } => {
                    let tf = force(bump, spine, defs, metas, decl, mutable, *typ);
                    let mut changed = tf != *typ;
                    let mut new_datas: Vec<SumDataV<'a>> = Vec::with_capacity(datas.len());
                    for (i, d) in datas.iter().enumerate() {
                        let df = force(bump, spine, defs, metas, decl, mutable, d.val);
                        if changed {
                            // 首变化后回填已见未变字段（原值指针相同）
                            if new_datas.is_empty() {
                                for d0 in datas.iter().take(i) {
                                    new_datas.push(SumDataV { name: d0.name, val: d0.val, icit: d0.icit });
                                }
                            }
                            new_datas.push(SumDataV { name: d.name, val: df, icit: d.icit });
                        } else if df != d.val {
                            changed = true;
                            for d0 in datas.iter().take(i) {
                                new_datas.push(SumDataV { name: d0.name, val: d0.val, icit: d0.icit });
                            }
                            new_datas.push(SumDataV { name: d.name, val: df, icit: d.icit });
                        }
                    }
                    return if changed {
                        v_xcell(bump.alloc(XCell::SumCase {
                            typ: tf,
                            index: *index,
                            datas: bump.alloc_slice_copy(&new_datas),
                            is_trait: *is_trait,
                        }))
                    } else {
                        v
                    };
                }
                _ => return v,
                }
            }
            _ => return v,
        }
    }
}
