//! unify：工作表迭代 unify（`UItem`/`unify_iter`：参考臂序，无燃料、无 pm 臂、
//! (Obj,Obj) 合同臂前移）+ intersect / flex-flex / lockstep + 判等记忆化
//! （`NO_CONV_MEMO` 消融）+ 跨调用草稿（`ConvScratch`）+ declb 存根表缓存
//! （`DECLB_CACHE`/`declb_of`）+「清空按阈值归还缓冲」口径（`ReclaimOnClear`
//! 与 `CACHE_SHRINK_MIN_ENTRIES`/`SPINE_SHRINK_MIN_ENTRIES`）。原
//! bump_spine_iter.rs 的 "unify" 节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::rc::Rc;
use smol_str::SmolStr;

use super::parser::syntax::Icit;
use super::PatternDetail;

use super::env::{env_ext, DeclEntry, Decls, Env};
use super::eval::{eval_iter, W};
use super::force::{force, vapp1, vapp_ok};
use super::rename::{invert_bump, prune_meta_bump, RenBuf, solve_bump, solve_with_pren_bump};
use super::spine::{MetaEntry, Spine, HK_OBJ, HK_OTHER};
use super::syntax::{
    Tm, V, XCell, v_clo_of, v_lvl, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_xcell,
    v_u_of, v_xcell_of,
};

// unify（工作表迭代；L09 参考版臂序，无燃料、无 pm 臂、无 (Obj,Obj) 臂）
// --------------------------------------------------------------------------------

/// A/B 实验开关（unify 工作表的判等记忆化消融）：置 `L06_NO_CONV_MEMO=1`
/// 关闭（`=0` 不关闭）。
static NO_CONV_MEMO: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_CONV_MEMO").is_ok_and(|v| v != "0"))
    });

/// 整表/整栈清空不归还缓冲：容量到过该量级时在清空点主动归还，否则峰值
/// 容量会一路常驻到进程结束（多轮 bench / 长驻进程里直接算进稳态 RSS）。
/// 阈值与 L13 孪生版同值同口径：小表重建比留着更贵，大表留着就是几 MB 起
/// 的空桶（1<<18 条 × ~24B ≈ 6MB）。
pub(super) const CACHE_SHRINK_MIN_ENTRIES: usize = 1 << 18;
/// 工作表栈（`Spine::stack` 与 unify 草稿 `scratch1/scratch2`）的同一阈值：
/// 槽位（`Entry` / `(V, Icit)`）比 memo 条目小，阈值低一档（1<<16 槽
/// ≈ 1–2MB）。与 L13 同口径。
pub(super) const SPINE_SHRINK_MIN_ENTRIES: usize = 1 << 16;

/// `Vec` / `HashMap` / `HashSet` 共用的「清空 + 按阈值归还缓冲」口径
/// （三者没有公共 trait，自备一个最小版本）：`clear()` 只清条目、桶数组照留，
/// 容量到过阈值的表在清空时顺带 `shrink_to_fit()`；阈值以下照旧只 `clear()`
/// （重建比留着更贵），故常态只是「clear 前多读一次 capacity」的固定开销。
/// **只改清空的写法，不动清空时机**——时机是既有语义（地址复用、换代、
/// 轮边界），正确性不依赖容量。形状照 L13 孪生版。
pub(super) trait ReclaimOnClear {
    /// 清空并（容量到 `min_entries` 时）归还缓冲；返回 `(清空前 len, 清空后
    /// capacity)`，与 L13 同形（该处供 `twin_mem_stats` 影子登记；本版无
    /// 统计消费者，调用点 `let _ =`）。
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

// impl 的界照 L13 原样带上（`K: Hash + Eq` / `S: BuildHasher`）；调用点都是
// 具名类型，无感。
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

/// unify 的跨调用草稿。
#[derive(Default)]
pub(super) struct ConvScratch {
    memo: FxHashSet<(u64, u64)>,
    scratch1: Vec<(V, Icit)>,
    scratch2: Vec<(V, Icit)>,
}

/// unify 工作表条目：待比较子对、Π 余定义域的惰性比较屏障、判等记忆化
/// 屏障、或卡住 match 的惰性展开屏障（declb 存根表下重求值后压
/// `l+count` 层的体对）。
pub(super) enum UItem<'a> {
    /// 待比较子对（level 相同的一对值；弹出时先 force 双方再分派）。
    Pair(u32, V, V),
    /// Π 余定义域的惰性比较（排在 dom 对之下——dom 不等即失败，cod 的
    /// eval 整个省掉）。
    EvalCod2(&'a Tm<'a>, Env<'a>, &'a Tm<'a>, Env<'a>, u32),
    /// 判等记忆化屏障（LIFO；健壮性论证同 L03——solve 写一次、成功单调）。
    Store((u64, u64)),
    /// 卡住 match 的一个分支对：两侧体在"各自捕获 env + fresh rigid 槽"
    /// 下用 **declb 存根表**重求值，再压 `l + count` 层的体对。
    MatchBranch {
        b1: &'a Tm<'a>,
        e1: Env<'a>,
        b2: &'a Tm<'a>,
        e2: Env<'a>,
        declb: Rc<Decls<'a>>,
        l: u32,
        count: u32,
    },
    /// Match/Match 的结构展开屏障（scrutinee 对比完后到达）：cases 长度
    /// 检查、分支对展开（参考版 scrutinee unify 之后的余下步骤，副作用
    /// 时序与参考版一致）。
    MatchStruct {
        e1: Env<'a>,
        e2: Env<'a>,
        c1: &'a [(PatternDetail, &'a Tm<'a>)],
        c2: &'a [(PatternDetail, &'a Tm<'a>)],
        declb: Rc<Decls<'a>>,
        l: u32,
    },
    /// 分支 pattern 相等检查（参考版逐分支在分支体之前）。
    MatchPattern(&'a PatternDetail, &'a PatternDetail),
}

/// declb 缓存条目：`(存根表, 源表钉)`。把源表 `Rc` 的克隆一并存入缓存，
/// 键地址（`Rc` 分配）在缓存存活期内不会释放复用——指针键无 ABA 风险。
pub(super) type DeclbEntry<'a> = (Rc<Decls<'a>>, Rc<Decls<'a>>);

thread_local! {
    /// declb 存根表缓存：键 = 源 decl 表 `Rc` 的分配地址。卡住 match 的
    /// quote/unify/rename 每次重建 O(D) 存根表 → 每轮每表一次。放 TLS 而非
    /// Machine 字段：declb_of 深在 eval/quote/unify/rename 的参数链底，穿
    /// 参数要动 10 个核心函数约 40 个调用点（L13 meta journal 同款先例）。
    /// 清除纪律与 Machine scratch 字段同款：`clear_round` 与 `bump.reset()`
    /// 1:1 同界（Tycker 三入口均先 reset 后 clear），条目绝不跨轮存活；
    /// 存放口径 'static 同 `unify_stack` 等槽位——条目只含当轮 bump 句柄。
    pub(super) static DECLB_CACHE: RefCell<FxHashMap<usize, DeclbEntry<'static>>> =
        RefCell::new(FxHashMap::default());
}

/// 从 decl 表构建 declb 存根表（每条目换成 `Decl(name)` 卡住值——递归
/// 引用停在存根；参考版 declb 逐字同构）。带指针键缓存：同表重复构建
/// O(D) → 每轮首建后 O(1)。
pub(super) fn declb_of<'a>(bump: &'a Bump, decl: &Rc<Decls<'a>>) -> Rc<Decls<'a>> {
    let key = Rc::as_ptr(decl) as usize;
    if let Some(entry) = DECLB_CACHE.with(|c| c.borrow_mut().get(&key).map(|e| e.0.clone())) {
        // SAFETY：条目写于本轮（clear_round 之后），只含本轮 bump 句柄；
        // 'static 仅是存放口径，读出时按当轮生命周期改写（同 unify_stack
        // 的槽位纪律）。
        let stub: &Rc<Decls<'a>> =
            unsafe { &*(&entry as *const Rc<Decls<'static>> as *const Rc<Decls<'a>>) };
        return stub.clone();
    }
    let stub: Rc<Decls<'a>> = Rc::new(
        decl.iter()
            .map(|(k, e)| {
                let name = bump.alloc_str(k.as_str());
                (
                    k.clone(),
                    DeclEntry {
                        tm: bump.alloc(Tm::Decl(name)),
                        val: v_xcell(bump.alloc(XCell::Decl { name })),
                        vty: e.vty,
                    },
                )
            })
            .collect(),
    );
    // SAFETY：同上，反向写入（本轮 bump 句柄按存放口径擦成 'static）。
    // SAFETY（源表钉）：`decl` 的克隆，同分配同生命周期改写。
    let stub_static: &Rc<Decls<'static>> =
        unsafe { &*(&stub as *const Rc<Decls<'a>> as *const Rc<Decls<'static>>) };
    let decl_static: &Rc<Decls<'static>> =
        unsafe { &*(decl as *const Rc<Decls<'a>> as *const Rc<Decls<'static>>) };
    DECLB_CACHE.with(|c| c.borrow_mut().insert(key, (stub_static.clone(), decl_static.clone())));
    stub
}

/// 链（或裸单元）是否卡住投影 Obj 头——unify 的位相等捷径对它关闭，
/// (Obj, Obj) 合同臂用它做门控（L11 参考版有该臂；tag2 链的头种类在
/// spine 槽上缓存的 `HK_OBJ` O(1) 判定）。
#[inline]
fn is_objheaded(spine: &Spine, v: V) -> bool {
    match v_tag(v) {
        7 => matches!(v_xcell_of(v), XCell::Obj { .. }),
        2 => spine.stack[v_spine_of(v)].hk == HK_OBJ,
        _ => false,
    }
}

/// `?m args ≡ ?m args'`（同头 flex）：上游 `intersect`。逐槽（内→外）
/// 都取到裸变量则产出掩码（槽位相等 → 其 icit、不等 → None）；有 None 即
/// 剪枝（`pruneMeta`），全相等即成立。长度不等直接失败。任一对含非变量
/// → 回落 `unify_sp` 逐实参比较。
#[allow(clippy::too_many_arguments)]
fn intersect_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Rc<Decls<'a>>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    m: u32,
    args1: &[(V, Icit)], // 内先（collect_args 的产出序）
    args2: &[(V, Icit)],
) -> bool {
    let n1 = args1.len();
    let n2 = args2.len();
    if n1 != n2 {
        return false; // 长度失配：直败零比较（连 force/压栈都省）
    }
    let common = n1;
    let mut pr: Vec<Option<Icit>> = Vec::with_capacity(common);
    let mut fallback = false;
    for k in 0..common {
        let f1 = force(bump, spine, defs, metas, decl, mutable, args1[k].0);
        let f2 = force(bump, spine, defs, metas, decl, mutable, args2[k].0);
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            pr.push(if v_lvl_of(f1) == v_lvl_of(f2) {
                Some(args1[k].1)
            } else {
                None
            });
        } else {
            fallback = true; // 上游 go 的 None：回落 unify_sp
            break;
        }
    }
    if !fallback {
        if pr.iter().any(|x| x.is_none()) {
            return prune_meta_bump(bump, spine, work, vals, icits, defs, metas, decl, mutable, &pr, m)
                .is_some();
        }
        return true; // 两 spine 逐槽相等
    }
    // unify_sp 回落：前缀对压栈（内先压 → 弹出外先，对齐 unify_sp 的递归序）。
    // tag 7 不跳过：参考版对字面量实参照走 unify（恒败）——位相等的同单元
    // 也须分派（见 unify 的 tag 7 守卫）。
    for k in 0..common {
        let (a1, _) = args1[k];
        let (a2, _) = args2[k];
        if a1.0 != a2.0 || v_tag(a1) == 7 {
            stack.push(UItem::Pair(l, a1, a2));
        }
    }
    true
}

/// 异头 flex-flex（上游 `flexFlex`）：**短 spine 一侧优先**反演求解；反演
/// 失败则用另一侧求解（rhs 是整条 flex 值）。**L09 参考版无快照回滚、
/// 无第二方向**——单次尝试，失败即 Err（部分 meta 写入保留，参考版同款）。
#[allow(clippy::too_many_arguments)]
fn flex_flex_bump<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Rc<Decls<'a>>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    gamma: u32,
    m1: u32,
    args1: &[(V, Icit)],
    v1: V,
    m2: u32,
    args2: &[(V, Icit)],
    v2: V,
) -> bool {
    // 方向选择与参考版一致：`sp.len() < sp_prime.len()` → (m', sp') 先；
    // 相等/更长 → (m, sp) 先。调用点约定（L08 同款）：v1 = u（m1 侧的
    // rhs），v2 = t（m2 侧的 rhs）。
    let (fa, aa, va, fb, ab, vb) = if args1.len() < args2.len() {
        (m2, args2, v2, m1, args1, v1)
    } else {
        (m1, args1, v1, m2, args2, v2)
    };
    match invert_bump(bump, spine, defs, metas, decl, mutable, ren, aa) {
        Some(mask) => solve_with_pren_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, fa, aa.len() as u32, gamma,
            mask, va,
        ),
        None => solve_bump(
            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, gamma, fb, ab, vb,
        ),
    }
}

/// 同头链（unify_sp）的实参 lockstep 比较：长度失配即败；实参 icit 不比
/// （类型已定，上游同款）。位相等的实参对免比（tag 7 与 Obj 头链除外——
/// 字面量恒败、卡住投影走 `_` → Err）。
fn unify_sp_lockstep<'a>(
    spine: &Spine,
    stack: &mut Vec<UItem<'a>>,
    l: u32,
    h1: usize,
    h2: usize,
) -> bool {
    if spine.spine_len(h1) != spine.spine_len(h2) {
        return false;
    }
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
        // 位相等后缀：实参对免比（tag 7 除外）；函数部分对仍须入栈。
        // Obj 头的链（tag 2 头 = Obj 单元）同样不免——交回完整分派，
        // 由 (Obj, Obj) 合同臂接管判定（同字段可判等，非恒败）。
        let skip1 = a1.0 == a2.0 && v_tag(a1) != 7 && !is_objheaded(spine, a1);
        if skip1 {
            if f1.0 != f2.0 {
                stack.push(UItem::Pair(l, f1, f2));
            }
            break;
        }
        if v_tag(a1) == 2 && v_tag(a2) == 2 {
            // 下钻门控：两侧的实参链顶层 f 与本层 f 同字（纯 ChainWrap 同头
            // 延续）；实参若是另一条中性链（Apply 惯例：`f` = partial 句柄
            // ≠ 头字）则停下，把子对交回完整分派。派发序与参考版 unify_sp
            // 同序：停钻时先压实参对、后压函数部分对。
            let cont = spine.stack[v_spine_of(a1)].f.0 == f1.0
                && spine.stack[v_spine_of(a2)].f.0 == f2.0;
            if cont {
                if f1.0 != f2.0 {
                    stack.push(UItem::Pair(l, f1, f2));
                }
                i1 = v_spine_of(a1);
                i2 = v_spine_of(a2);
                continue;
            }
        }
        stack.push(UItem::Pair(l, a1, a2));
        if f1.0 != f2.0 {
            stack.push(UItem::Pair(l, f1, f2));
        }
        break;
    }
    true
}

/// 裸 Rigid（tag 0）或 Rigid 头的链的层级；非此形态返回 None。
#[inline]
fn rigid_lvl(spine: &Spine, v: V) -> Option<u32> {
    match v_tag(v) {
        0 => Some(v_lvl_of(v)),
        2 => {
            let h = v_spine_of(v);
            if spine.stack[h].hk != HK_OTHER {
                return None; // flex / Obj / Decl 头：必非 Rigid，免走底
            }
            let hd = spine.spine_head(h);
            if v_tag(hd) == 0 {
                Some(v_lvl_of(hd))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// unification：结构比较 + meta 求解（含 intersect / flex-flex / 剪枝），
/// 工作表迭代。臂序与参考版 `Infer::unify` 逐项对应（顺序敏感）：
/// U → Π（icit 相等）→ Rigid/Rigid 同级 → 同头 flex = intersect → 异头
/// flex-flex（单方向）→ λ/η → flex 求解 → LiteralType/宽松臂 → Sum/Sum →
/// SumCase/SumCase（typ+datas）→ Match/Match（scrutinee + 中性分支体重
/// 求值）→ 失配。**位相等捷径对 tag 7 与 Obj 头链关闭**：参考版对字面量
/// 无自反臂（同字面量也 Err）、卡住投影走 `_` → Err；捷径放行会误 Accept。
/// 本孪生与参考版一致：frcs lookup 命中与 Match 重选各烧 1（thread_local
/// `PM_FUEL` 4096，外部入口充值），耗尽时 lookup 命中降级为裸 rigid、
/// Match 不重选；无 pm 臂（L09 的模式特化在 elaboration 侧的
/// unify_pm/update_cxt 完成）。
#[allow(clippy::too_many_arguments)]
pub(super) fn unify_iter<'a>(
    bump: &'a Bump,
    spine: &mut Spine,
    work: &mut Vec<W<'a>>,
    stack: &mut Vec<UItem<'a>>,
    vals: &mut Vec<V>,
    icits: &mut Vec<Icit>,
    defs: &mut Vec<V>,
    metas: &mut Vec<MetaEntry>,
    decl: &Rc<Decls<'a>>,
    mutable: &RefCell<FxHashMap<SmolStr, V>>,
    ren: &mut RenBuf,
    conv: &mut ConvScratch,
    l0: u32,
    t0: V,
    u0: V,
    // 续跑标记：`true` = 由 trait 合成挂起点返回后续跑（跳过入口
    // clear 与初始入栈——工作栈/草稿都住在 Machine 字段里，内容跨
    // 挂起点保持，等价于旧实现「回调返回后继续循环」）。
    resume: bool,
    // trait 合成挂起信号：flex 解开后需跑 `solve_multi_trait_ref` 的
    // meta。由 `unify` 驱动在**无任何字段借用存活**的点上以独占
    // `&mut Machine` 执行（替代旧实现的 `mach_ptr` 整机重借——那在
    // Stacked Borrows 下使存活中的字段借用失效，属别名违规）。
    solve_req: &mut Option<u32>,
) -> bool {
    let memo_on = !NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed);
    // 草稿复用（Machine 常驻）：清空保容量，热路径零分配（resume 续跑
    // 不清——挂起点前已把草稿原样恢复；嵌套 unify 的入口 clear 对记忆
    // 表的影响与旧实现一致）；容量到过阈值的表在清空时归还缓冲（memo 见
    // `CACHE_SHRINK_MIN_ENTRIES`，工作表见 `SPINE_SHRINK_MIN_ENTRIES`），
    // 否则峰值容量随常驻 Machine 到进程结束。清空时机（resume 不清）不动。
    if !resume {
        let _ = conv.memo.reclaim(CACHE_SHRINK_MIN_ENTRIES);
        let _ = conv.scratch1.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        let _ = conv.scratch2.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        // UItem 工作栈由调用方常驻复用（入口已 clear）；失败早退会留下非空
        // 栈，靠下次入口 clear 兜住（Rc 随 clear 正确减计，引用无 Drop）
        debug_assert!(stack.is_empty());
        stack.push(UItem::Pair(l0, t0, u0));
    }
    let memo = &mut conv.memo;
    while let Some(item) = stack.pop() {
        let (l, t, u) = match item {
            UItem::Store(key) => {
                memo.insert(key);
                continue;
            }
            UItem::EvalCod2(b1, e1, b2, e2, l) => {
                let vt = {
                    let env = env_ext(bump, e1, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b1)
                };
                let vu = {
                    let env = env_ext(bump, e2, v_lvl(l));
                    eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, b2)
                };
                stack.push(UItem::Pair(l + 1, vt, vu));
                continue;
            }
            UItem::MatchBranch {
                b1,
                e1,
                b2,
                e2,
                declb,
                l,
                count,
            } => {
                // 分支体：两侧各自"捕获 env + fresh rigid 槽（count =
                // bind_count，lvl 从 l 起）"下用 declb 存根表重求值，再在
                // l+count 层比较（参考版 unify 的 Match/Match 全路径同款）
                let mut env1 = e1;
                let mut env2 = e2;
                for i in 0..count {
                    env1 = env_ext(bump, env1, v_lvl(l + i));
                    env2 = env_ext(bump, env2, v_lvl(l + i));
                }
                let v1 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mutable, env1, b1,
                );
                let v2 = eval_iter(
                    bump, spine, work, vals, icits, defs, metas, &declb, mutable, env2, b2,
                );
                stack.push(UItem::Pair(l + count, v1, v2));
                continue;
            }
            UItem::MatchStruct {
                e1,
                e2,
                c1,
                c2,
                declb,
                l,
            } => {
                // scrutinee 已比完（参考版 unify 的 Match/Match 臂 scrutinee
                // 递归之后）：cases 长度检查 → 逐分支（pattern → 分支体）。
                // LIFO 按执行序的逆序压：分支（体 → pattern，反序）
                if c1.len() != c2.len() {
                    return false;
                }
                for (i, ((p1, b1), (_, b2))) in c1.iter().zip(c2.iter()).enumerate().rev() {
                    stack.push(UItem::MatchBranch {
                        b1: *b1,
                        e1,
                        b2: *b2,
                        e2,
                        declb: declb.clone(),
                        l,
                        count: p1.bind_count(),
                    });
                    stack.push(UItem::MatchPattern(p1, &c2[i].0));
                }
                continue;
            }
            UItem::MatchPattern(p1, p2) => {
                if p1 != p2 {
                    return false;
                }
                continue;
            }
            UItem::Pair(l, t, u) => (l, t, u),
        };
        // 位相等：同一值。tag 7 与 Obj 头链例外（见函数注释——参考版对
        // 字面量无自反性、卡住投影走 `_` → Err）
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue;
        }
        if memo_on && memo.contains(&(t.0, u.0)) {
            continue; // 本轮已判等过的子对（命中连 force 都省——成功单调）
        }
        let t = force(bump, spine, defs, metas, decl, mutable, t);
        let u = force(bump, spine, defs, metas, decl, mutable, u);
        if t.0 == u.0 && v_tag(t) != 7 && !is_objheaded(spine, t) {
            continue; // force 展开后同值（同一解的两处引用）
        }

        // —— 宇宙（参考臂 1）：层级相等才成立（无累积）——
        if v_tag(t) == 3 && v_tag(u) == 3 {
            if v_u_of(t) == v_u_of(u) {
                continue;
            }
            return false;
        }
        // —— Π：icit 相等才比（参考臂 2）；icit 失配落到后续臂 ——
        if v_tag(t) == 4 && v_tag(u) == 4 {
            let p = v_pi_of(t);
            let q = v_pi_of(u);
            if p.icit == q.icit {
                if memo_on {
                    stack.push(UItem::Store((t.0, u.0)));
                }
                // 先比定义域，再惰性 eval 两侧余定义域
                stack.push(UItem::EvalCod2(p.body, p.env, q.body, q.env, l));
                stack.push(UItem::Pair(l, p.dom, q.dom));
                continue;
            }
        }
        // —— Rigid/Rigid（参考臂 3）：同级比实参 spine（裸×裸自反成立），
        // 异级落到后续臂（λ/η 等仍可命中，最终 `_` 失配）——
        if v_tag(t) == 0 && v_tag(u) == 0 {
            if v_lvl_of(t) == v_lvl_of(u) {
                continue; // 双裸单元：unify_sp([][]) 自反成立
            }
        }
        // —— (Obj, Obj) 合同臂（L10 新增，L08 快版同款位次）：字段名同 ⇒
        // 比接收者 + spine 实参（参考版 unify 的 Obj/Obj 臂同款）。必须
        // 先于中性链分派：tag2×tag2 的 Obj 头链在链分派里会被同头/异头
        // 失配提前拦下，参考版的合同判定就不可达了。裸 XCell 单元（tag 7）
        // 与带实参链（tag 2）统一在此处理；裸×链 = spine 长度失配即败——
        // 与参考版 unify_sp([][..]) 同判定。——
        if is_objheaded(spine, t) && is_objheaded(spine, u) {
            let (hc1, hc2) = (
                if v_tag(t) == 7 { t } else { spine.spine_head(v_spine_of(t)) },
                if v_tag(u) == 7 { u } else { spine.spine_head(v_spine_of(u)) },
            );
            let (o1, n1, o2, n2) = match (v_xcell_of(hc1), v_xcell_of(hc2)) {
                (
                    XCell::Obj { val: a1, name: m1 },
                    XCell::Obj { val: a2, name: m2 },
                ) => (*a1, *m1, *a2, *m2),
                _ => return false,
            };
            if n1 != n2 {
                return false;
            }
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l, o1, o2));
            match (v_tag(t), v_tag(u)) {
                (7, 7) => {}
                (2, 2) => {
                    if !unify_sp_lockstep(spine, stack, l, v_spine_of(t), v_spine_of(u)) {
                        return false;
                    }
                }
                _ => return false,
            }
            continue;
        }
        // —— 中性链 vs 中性链（参考臂 3/4/5 的链形态全在此分派）——
        if v_tag(t) == 2 && v_tag(u) == 2 {
            let h1 = v_spine_of(t);
            let h2 = v_spine_of(u);
            let hd1 = spine.spine_head(h1);
            let hd2 = spine.spine_head(h2);
            let f1 = v_tag(hd1) == 5;
            let f2 = v_tag(hd2) == 5;
            if f1 && f2 {
                // 双 flex：同头 intersect、异头 flex_flex（参考臂 4/5）
                let mut a1 = std::mem::take(&mut conv.scratch1);
                a1.clear();
                spine.collect_args(h1, &mut a1);
                let mut a2 = std::mem::take(&mut conv.scratch2);
                a2.clear();
                spine.collect_args(h2, &mut a2);
                let m1 = v_meta_of(hd1);
                let m2 = v_meta_of(hd2);
                let ok = if m1 == m2 {
                    intersect_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, stack, l, m1, &a1,
                        &a2,
                    )
                } else {
                    flex_flex_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m1, &a1, u,
                        m2, &a2, t,
                    )
                };
                conv.scratch1 = a1;
                conv.scratch2 = a2;
                if ok {
                    if memo_on {
                        memo.insert((t.0, u.0));
                    }
                    continue;
                }
                return false;
            }
            // —— Decl 头链的同名判定（参考臂 3.5 的链形态）：头都是卡住
            // 声明 → 同名 unlockstep 比实参、异名失配；其余组合落同头/异头
            // 分派 ——
            if v_tag(hd1) == 7 && v_tag(hd2) == 7 {
                if let (
                    XCell::Decl { name: n1 },
                    XCell::Decl { name: n2 },
                ) = (v_xcell_of(hd1), v_xcell_of(hd2))
                {
                    if n1 == n2 {
                        if memo_on {
                            stack.push(UItem::Store((t.0, u.0)));
                        }
                        if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                            return false;
                        }
                        continue;
                    }
                    return false;
                }
            }
            // 同头判定：位相等（同变量 / 同 meta / 同卡住投影单元）。Obj 头
            // 已被上文 (Obj, Obj) 合同臂接管（同头 Obj 不可达；保留防御性
            // 排除，L10 快版同款口径）
            if hd1.0 == hd2.0 {
                if !is_objheaded(spine, hd1) {
                    // 同头刚性/卡住投影以外的头：逐实参比较（lockstep，长度
                    // 失配即败）
                    if memo_on {
                        stack.push(UItem::Store((t.0, u.0)));
                    }
                    if !unify_sp_lockstep(spine, stack, l, h1, h2) {
                        return false;
                    }
                    continue;
                }
                return false; // 防御保留：同头 Obj 不会走到这里（见上臂）
            }
            // 异头：一侧 flex 头（f1/f2 已排除双 flex）→ 该侧 solve（参考
            // 臂 9/10 的链形态）；双 Obj 头已被上文 (Obj, Obj) 合同臂接管，
            // 剩余双刚性异级 / Obj×刚性组合 → 失配。
            let (mv, h, rhs) = if f1 {
                (v_meta_of(hd1), h1, u)
            } else if f2 {
                (v_meta_of(hd2), h2, t)
            } else {
                return false;
            };
            let mut args = std::mem::take(&mut conv.scratch1);
            args.clear();
            spine.collect_args(h, &mut args);
            let solved = solve_bump(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, mv, &args, rhs,
            );
            conv.scratch1 = args;
            if solved {
                if memo_on {
                    memo.insert((t.0, u.0));
                }
                // 参考 solve 臂：解后跑 trait 合成（失败 → Err）。经挂起信号
                // 交回 unify 驱动以独占 &mut Machine 执行（SB 别名安全）
                *solve_req = Some(mv);
                return false;
            }
            return false;
        }
        // —— 裸 Rigid vs 链（同级）：参考臂 3 的 unify_sp——裸侧空 spine
        // 与链长失配即败；异级落后续臂 ——
        if v_tag(t) == 0 && v_tag(u) == 2 {
            if rigid_lvl(spine, u) == Some(v_lvl_of(t)) {
                return false; // 空 spine vs 非空链：长度失配
            }
        }
        if v_tag(t) == 2 && v_tag(u) == 0 {
            if rigid_lvl(spine, t) == Some(v_lvl_of(u)) {
                return false;
            }
        }
        // —— λ / η（参考臂 6/7/8；在 flex 求解之前：Flex vs λ 走 η）——
        if v_tag(t) == 1 && v_tag(u) == 1 {
            let c1 = v_clo_of(t);
            let c2 = v_clo_of(u);
            let vt = {
                let env = env_ext(bump, c1.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c1.body)
            };
            let vu = {
                let env = env_ext(bump, c2.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c2.body)
            };
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // η：中性一侧按 λ 一侧的 icit 应用（卡住投影/声明/链的应用压链）。
        // 可应用性守卫（参考版 `v_applicable` 同款）：字面量/U/Π/Sum 等形态
        // 不做 η，落后续臂 → 最终 false（参考版同处 Err），不再 panic。
        if v_tag(u) == 1 && vapp_ok(t) {
            let c = v_clo_of(u);
            let vu = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
            };
            let vt = vapp1(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, t, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        if v_tag(t) == 1 && vapp_ok(u) {
            let c = v_clo_of(t);
            let vt = {
                let env = env_ext(bump, c.env, v_lvl(l));
                eval_iter(bump, spine, work, vals, icits, defs, metas, decl, mutable, env, c.body)
            };
            let vu = vapp1(
                bump, spine, work, vals, icits, defs, metas, decl, mutable, u, v_lvl(l), c.icit,
            );
            if memo_on {
                stack.push(UItem::Store((t.0, u.0)));
            }
            stack.push(UItem::Pair(l + 1, vt, vu));
            continue;
        }
        // —— flex 求解（参考臂 4/5/9/10 的裸形态）——
        {
            let mut a1 = std::mem::take(&mut conv.scratch1);
            a1.clear();
            let ft = spine.flex_of(t, &mut a1);
            let mut a2 = std::mem::take(&mut conv.scratch2);
            a2.clear();
            let fu = spine.flex_of(u, &mut a2);
            match (ft, fu) {
                (Some(m1), Some(m2)) => {
                    let ok = if m1 == m2 {
                        intersect_bump(
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, stack, l, m1,
                            &a1, &a2,
                        )
                    } else {
                        flex_flex_bump(
                            bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m1, &a1,
                            u, m2, &a2, t,
                        )
                    };
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        continue;
                    }
                    return false;
                }
                (Some(m), None) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m, &a1, u,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        // 参考 solve 臂：解后跑 trait 合成（失败 → Err）。经挂起
                        // 信号交回 unify 驱动以独占 &mut Machine 执行
                        *solve_req = Some(m);
                        return false;
                    }
                    return false;
                }
                (None, Some(m)) => {
                    let ok = solve_bump(
                        bump, spine, work, vals, icits, defs, metas, decl, mutable, ren, l, m, &a2, t,
                    );
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    if ok {
                        if memo_on {
                            memo.insert((t.0, u.0));
                        }
                        *solve_req = Some(m);
                        return false;
                    }
                    return false;
                }
                (None, None) => {
                    conv.scratch1 = a1;
                    conv.scratch2 = a2;
                    // 非 flex：落到字面量 / Sum / SumCase / Match 臂
                }
            }
        }
        // —— (LiteralType, LiteralType)（参考臂 11）——
        if v_tag(t) == 6 && v_tag(u) == 6 {
            continue;
        }
        // —— Prim 带类型臂（参考臂 12/12.5）：`(_, Prim(b, _)) → unify(t, b)`
        // 与 `(Prim(a, _), _) → unify(a, u)`（参考版逐字——先检次位再检
        // 首位；双 Prim 经两臂传导到 typ-vs-typ）——
        if v_tag(u) == 7 {
            if let XCell::Prim { typ, .. } = v_xcell_of(u) {
                stack.push(UItem::Pair(l, t, *typ));
                continue;
            }
        }
        if v_tag(t) == 7 {
            if let XCell::Prim { typ, .. } = v_xcell_of(t) {
                stack.push(UItem::Pair(l, *typ, u));
                continue;
            }
        }
        // —— Sum/Sum（参考臂 13）：同名即逐参数（含索引）值合一；zip 语义
        // （参数数不等取 min——参考版同款）；异名失配 ——
        if v_tag(t) == 7 && v_tag(u) == 7 {
            let (xt, xu) = (v_xcell_of(t), v_xcell_of(u));
            // —— Decl/Decl 同名（参考臂 3.5）：裸头同名比 spine（空 spine
            // 即成立）；异名失配（参考版 `_` 落点同款）——
            if let (XCell::Decl { name: n1 }, XCell::Decl { name: n2 }) = (xt, xu) {
                if n1 == n2 {
                    continue;
                }
                return false;
            }
            if let (
                XCell::Sum {
                    name: n1,
                    params: p1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: p2,
                    ..
                },
            ) = (xt, xu)
            {
                if n1 == n2 {
                    for (a, b) in p1.iter().zip(p2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    continue;
                }
                return false; // 异名 Sum：参考版无后续可命中臂 → Err
            }
            // —— SumCase/SumCase（参考臂 14）：同构造子才比；**先比 Sum 头
            // 名字**（2026-09-18 评审修复，L07 同款——跨 enum 重名构造子直
            // 接失败），typ 与 datas 都比（typ 先、datas 后——L09 参考版与
            // L07+ 的 datas-only 不同）——
            if let (
                XCell::SumCase {
                    typ: ty1,
                    case_name: c1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: ty2,
                    case_name: c2,
                    datas: d2,
                    ..
                },
            ) = (xt, xu)
            {
                if c1 == c2 {
                    if let (XCell::Sum { name: na, .. }, XCell::Sum { name: nb, .. }) =
                        (v_xcell_of(*ty1), v_xcell_of(*ty2))
                    {
                        if na != nb {
                            return false;
                        }
                    }
                    // pop 序 = typ, d0, d1, ...（参考版执行序）
                    for (a, b) in d1.iter().zip(d2.iter()).rev() {
                        stack.push(UItem::Pair(l, a.val, b.val));
                    }
                    stack.push(UItem::Pair(l, *ty1, *ty2));
                    continue;
                }
                return false; // 异 case：参考版无后续可命中臂 → Err
            }
            // —— Match/Match（参考臂 15）：scrutinee 最先合一（真实副作用
            // 时序），cases 长度与 pattern 检查及其后分支体的中性重求值由
            // MatchStruct 屏障执行 ——
            if let (
                XCell::Match {
                    scrutinee: s1,
                    env: e1,
                    cases: c1,
                },
                XCell::Match {
                    scrutinee: s2,
                    env: e2,
                    cases: c2,
                },
            ) = (xt, xu)
            {
                stack.push(UItem::MatchStruct {
                    e1: *e1,
                    e2: *e2,
                    c1,
                    c2,
                    declb: declb_of(bump, decl),
                    l,
                });
                stack.push(UItem::Pair(l, *s1, *s2));
                continue;
            }
        }
        // (Obj, Obj) 合同臂已前移到中性链分派之前（L08 快版同款位次）：
        // tag2×tag2 的 Obj 头链（含同头/异头）若落进上面的链分派，会被
        // "同头 Obj → false / 异头非 flex → false" 提前判败，永远到不了
        // 臂本身——参考版 (Obj,Obj) 臂对同字段投影是可判等的，故必须
        // 先于链分派拦截（与参考版同判定）。
        return false;
    }
    true
}
