//! machine：稳态复用机（`Machine`）与 elaboration（check/infer/decl 表）、
//! Elaboration 上下文（`Cxt`/`TCons`/`decl_insert`）、builtin 注册
//! （`prime_round`/`elab_all`）。原 bump_spine_iter.rs 的 "Machine（稳态
//! 复用）与 elaboration"、"Elaboration 上下文与 decl 表（写时复制）"、
//! "builtin 注册" 三节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

use super::parser::syntax::{Decl, Either, Icit, Raw};
use super::pretty::pretty_tm;
use super::{empty_span, Error, PatternDetail};

use super::compiler::Compiler;
use super::entry::{export, NO_NAME_MAP};
use super::env::{EMPTY_ENV, Env, env_ext, env_ext_defs, env_len, env_nth, PiCell};
use super::eval::{eval_iter, W};
use super::force::{force, frcs_env};
use super::prim::{DeclEntryF, Fuel, MutableMap, UNIFY_FUEL};
use super::quote::{QJob, quote_iter, QuoteMemo};
use super::rename::RenBuf;
use super::spine::{is_flex, MetaEntry, Spine};
use super::subst::{SpecSolve, SubstV, vsub_reclaim, wrap_sub};
use super::syntax::{LCons, PrCons, SumDataT, SumParamT, Tm, V, v_lit_ty, v_lvl, v_lvl_of, v_meta, v_pi, v_pi_of, v_tag, v_u, v_xcell, v_xcell_of, XCell};
use super::unify::{UItem, unify_iter};

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

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
    pub(super) memo: FxHashSet<(u64, u64)>,
    pub(super) scratch1: Vec<(V, Icit)>,
    pub(super) scratch2: Vec<(V, Icit)>,
}

const PI_NAME: &str = "x"; // infer App 非 Π 分支合成的闭包名（只服务 pretty）

/// 稳态复用机（L06 版 + L07 增量：unify_fuel 池、pm 特化事实表/可解集——
/// 分支局部的 (层级 → 值) 记录，`force` 在读点惰性展开；decl 表不在机上
/// ——它在 `Cxt.decl`（`Rc<FxHashMap>` 写时复制，随上下文传递，与参考版
/// `Infer` 方法逐点接收 `decl: &Decls` 同构））。
pub(crate) struct Machine {
    pub(super) spine: Spine,
    vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    pub(super) defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。**只收源码
    /// binder**（bind/define）——inserted binder 与参考版 `new_binder`
    /// 一样不入 src_names。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
    /// 可变全局（L06 同款）：builtin `create_global` / `change_mutable` 族
    /// 的存取目标。值指向本轮 bump——每轮清空（参考版每次调用新建 Infer）。
    mutable_map: MutableMap,
    /// force 展开与 unify 递归的共享燃料池（每次 unify_catch / 编译入口 /
    /// nf 充值；耗尽即把值当未解处理 / Err）。
    pub(super) fuel: Fuel,
    /// eval / quote / unify 的可复用工作栈。`'static` 仅是**存放口径**：
    /// 进核前 clear，借出期间写入的当轮条目不跨调用存活——与 `conv` /
    /// `icits` 的「进核前 clear」纪律同款。`W`/`QJob`/`UItem` 均为无 Drop
    /// 的 Copy 枚举，`Vec` 布局与元素生命周期参数无关，出借时按当次
    /// 生命周期重写指针类型（SAFETY 见各包装方法）。
    eval_work: Vec<W<'static>>,
    quote_tasks: Vec<QJob<'static>>,
    quote_done: Vec<&'static Tm<'static>>,
    quote_work: Vec<W<'static>>,
    unify_work: Vec<W<'static>>,
    /// unify 的 UItem 主工作栈（同上口径；`UItem::MatchBranch` 持
    /// `Rc`——失败早退留下的 Rc 随下次入口 clear 正确减计，非 Drop 项
    /// 是引用 Copy，'static 存放无析构风险）。
    unify_stack: Vec<UItem<'static>>,
    /// quote 记忆化表：容量跨调用复用，内容**每次调用 clear**——meta 可
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项（表随
    /// 调用新鲜是口径的一部分，绝不跨 reset 持有）。
    quote_memo: QuoteMemo<'static>,
}

impl Machine {
    pub(crate) fn new() -> Self {
        Machine {
            spine: Spine {
                stack: Vec::with_capacity(4096),
            },
            vals: Vec::with_capacity(4096),
            icits: Vec::new(),
            conv: ConvScratch::default(),
            defs: Vec::with_capacity(4096),
            metas: Vec::new(),
            ren: RenBuf::default(),
            name_map: FxHashMap::default(),
            name_trail: Vec::new(),
            mutable_map: RefCell::new(FxHashMap::default()),
            fuel: Cell::new(UNIFY_FUEL),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/轨迹/环境区域 + 可变全局全部清空
    /// （builtin 的重注册在 [`Machine::prime_round`]；decl 表随 Cxt 的 Rc
    /// 释放。模式精化的 σ 在 `Compiler` 本地，随 compile 结束消亡，无跨轮
    /// 状态）。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮 bump 值 /
    /// metas / defs / mutable_map 持有，轮边界后无任何旧句柄可达，截断防
    /// 稳态复用下的无界增长；容量到过 `SPINE_SHRINK_MIN_ENTRIES` 时清空
    /// 顺带归还缓冲（否则峰值容量随常驻 Machine 到进程结束）。
    pub(super) fn clear_round(&mut self) {
        self.metas.clear();
        self.name_map.clear();
        self.name_trail.clear();
        self.defs.clear();
        self.mutable_map.borrow_mut().clear();
        let _ = self.spine.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        self.fuel.set(UNIFY_FUEL);
        // 与三处 bump.reset() 严格伴生：归还 arena 内 σ 克隆的强引用
        // （Rc 节点在全局堆上，reset 不动其数据；见 VSUB_REGS 的 SAFETY 注释）
        vsub_reclaim();
    }

    /// fuel 是否已耗尽（本编译单元的共享池）。错误诊断用：特化方程失败
    /// 时区分"结构冲突（真 absurd）"与"预算耗尽（假 absurd）"。
    pub(crate) fn fuel_exhausted(&self) -> bool {
        self.fuel.get() == 0
    }

    pub(super) fn is_flex_v(&self, v: V) -> bool {
        is_flex(&self.spine, v)
    }

    /// `subst_cxt` 之后、臂体检查之前：把 name_map（types 链的 O(1) 影子
    /// 索引）中本臂 types 链上的源码 binder 类型替换为**已包 σ 的版本**。
    /// subst_cxt 只重塑 types 链；影子不同步的话，`Raw::Var` 的快路径
    /// （name_map 先于 types）会绕过精化，嵌套 match 的 scrutinee 类型丢掉
    /// 外层已解变量。返回撤销表（按发现序，还原时逆序）。
    pub(super) fn wrap_names<'x>(&mut self, cxt: &Cxt<'x>) -> Vec<(SmolStr, (u32, V))> {
        let mut undo = Vec::new();
        let mut seen: FxHashSet<&str> = FxHashSet::default();
        let mut tys = cxt.types;
        while let Some(tc) = tys {
            // 同名遮蔽取最内层（链头在前）
            if tc.source && seen.insert(tc.name) {
                if let Some(old) = self.name_map.get(tc.name).cloned() {
                    if old.1.0 != tc.ty.0 {
                        self.name_map.insert(SmolStr::new(tc.name), (old.0, tc.ty));
                        undo.push((SmolStr::new(tc.name), old));
                    }
                }
            }
            tys = tc.next;
        }
        undo
    }

    pub(super) fn restore_names(&mut self, undo: Vec<(SmolStr, (u32, V))>) {
        for (k, old) in undo.into_iter().rev() {
            self.name_map.insert(k, old);
        }
    }

    // Extend Cxt（源码 binder / inserted binder / define）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    #[allow(clippy::too_many_arguments)]
    pub(super) fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            decl: cxt.decl.clone(),
        }
    }

    /// Extend Cxt with an inserted implicit binder：**不入名字表**、trail
    /// 不动、mark 不变——但 telescope/pruning 照常扩展。
    fn new_binder<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: false,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: None,
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark,
            decl: cxt.decl.clone(),
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    #[allow(clippy::too_many_arguments)]
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        debug_assert_eq!(self.name_trail.len(), cxt.mark as usize);
        let key = SmolStr::new(x);
        let prev = self.name_map.insert(key.clone(), (cxt.lvl, ty));
        self.name_trail.push((key, prev));
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            types: Some(bump.alloc(TCons {
                name: bump.alloc_str(x),
                ty,
                source: true,
                next: cxt.types,
            })),
            locals: Some(bump.alloc(LCons {
                name: bump.alloc_str(x),
                a_t,
                t_t: Some(t_t),
                next: cxt.locals,
            })),
            pruning: Some(bump.alloc(PrCons::new(None, cxt.pruning))),
            binds: cxt.binds, // define 槽不产生 Π 层
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
            decl: cxt.decl.clone(),
        }
    }

    /// 撤销轨迹当前长度（模式编译的臂边界用它取基线——臂内 walk 的绑定
    /// 不经 unwind_names 退出，需显式截断）。
    pub(super) fn name_mark(&self) -> u32 {
        self.name_trail.len() as u32
    }

    /// 截断撤销轨迹到 `mark`（binder 作用域退出）。
    pub(super) fn unwind_names(&mut self, mark: u32) {
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

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等（telescope 只剩 Define 的 Let 层——eval 只往 env
    /// 塞值不添 Π 层）；**快捷路径 1**：telescope 为"头 bind 段 + 其后全
    /// define"时只闭 bind 段成 Π、define 槽由 `cxt.env` 快照供给，免全
    /// close 的 Θ(层深²) Let 链重建与重求值；**快捷路径 2**（交错形态的
    /// 兜底）：`quote` 无自由变量则直接空环境求值；否则全构造（与参考版
    /// 同形）。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, &cxt.decl.borrow(), cxt.lvl, a);
            if let Some(k) = bind_prefix_of_telescope(cxt.locals) {
                // 快路径：bind 段闭 Π、define 槽由 cxt.env 快照（平坦 def
                // 区）供给，免全 close 的 Θ(层深²) Let 链重建与重求值（论证
                // 见 L05 同名分支注释）。
                let mut b = q;
                let mut ls = cxt.locals;
                for _ in 0..k {
                    let n = ls.expect("bind 段长度已验证");
                    b = bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b));
                    ls = n.next;
                }
                self.eval(bump, &cxt.decl.borrow(), cxt.env, b)
            } else if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, closed)
            }
        };
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved(mty));
        bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(m)), cxt.pruning))
    }

    /// 沿 telescope 链闭包（Bind → 显式 Π、Define → Let）。
    fn close_tm<'a>(
        &self,
        bump: &'a Bump,
        mut ls: Option<&'a LCons<'a>>,
        q: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        let mut b = q;
        while let Some(n) = ls {
            b = match n.t_t {
                None => bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b)),
                Some(t) => bump.alloc(Tm::Let(n.name, n.a_t, t, b)),
            };
            ls = n.next;
        }
        b
    }

    /// fresh meta 的求值快捷路径：掩码全为 define 槽（或空）时 AppPrun
    /// 走空转，结果恒为裸 meta 立即数——免一次 eval。
    fn eval_fresh(
        &mut self,
        bump: &Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        env: Env,
        m: &Tm<'_>,
    ) -> V {
        if let Tm::AppPruning(head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, decls, env, m)
    }

    // 内核包装（Machine 字段借出）
    // --------------------------------------------------------------------------------

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn eval<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        env: Env<'a>,
        tm: &'a Tm<'a>,
    ) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            fuel,
            eval_work,
            ..
        } = self;
        // SAFETY：'static 仅是存放口径（字段注释）。W 无 Drop、Vec 布局与
        // 生命周期参数无关；借出期 = 本次调用，槽内容下次借出前必 clear，
        // 任何 'a 条目都不会被以 'static 读到。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        work.clear();
        eval_iter(
            bump,
            spine,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            fuel,
            env,
            tm,
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn quote<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        level: u32,
        v: V,
    ) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            fuel,
            quote_tasks,
            quote_done,
            quote_work,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(quote_tasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> = unsafe {
            &mut *(quote_done as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>)
        };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(quote_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        tasks.clear();
        done.clear();
        work.clear();
        quote_iter(
            bump,
            spine,
            tasks,
            done,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            fuel,
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（表容量跨调用复用、内容每次调用 clear，绝不跨
    /// reset 持有条目——meta 求解会让旧条目过期）。
    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn quote_memo<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        level: u32,
        v: V,
    ) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            fuel,
            quote_tasks,
            quote_done,
            quote_work,
            quote_memo,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(quote_tasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> = unsafe {
            &mut *(quote_done as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>)
        };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(quote_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let memo: &mut QuoteMemo<'a> = unsafe {
            &mut *(quote_memo as *mut QuoteMemo<'static> as *mut QuoteMemo<'a>)
        };
        tasks.clear();
        done.clear();
        work.clear();
        // 清空保容量（表随 Machine 常驻），容量到阈值时顺带归还缓冲。
        let _ = memo.reclaim(CACHE_SHRINK_MIN_ENTRIES);
        quote_iter(
            bump,
            spine,
            tasks,
            done,
            work,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            fuel,
            level,
            v,
            Some(&mut *memo),
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn unify<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        l: u32,
        t: V,
        u: V,
    ) -> bool {
        self.unify_with(bump, decls, l, t, u, None)
    }

    /// 带特化状态（`SpecSolve`）穿参的 unify：模式走查 / 覆盖探测传
    /// `Some(spec)`（可解 rigid 解入 `spec.acc`），常规转换传 `None`。
    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn unify_with<'a>(
        &mut self,
        bump: &'a Bump,
        decls: &FxHashMap<String, DeclEntryF>,
        l: u32,
        t: V,
        u: V,
        spec: Option<&mut SpecSolve<'_>>,
    ) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable_map,
            ren,
            conv,
            fuel,
            unify_work,
            unify_stack,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear（unify
        // 的失败早退会把非空栈留在槽里，靠入口 clear 兜住）。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let stack: &mut Vec<UItem<'a>> =
            unsafe { &mut *(unify_stack as *mut Vec<UItem<'static>> as *mut Vec<UItem<'a>>) };
        work.clear();
        stack.clear();
        unify_iter(
            bump,
            spine,
            work,
            stack,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ren,
            conv,
            fuel,
            spec,
            l,
            t,
            u,
        )
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表 + fuel 耗尽
    /// 尾巴；快版导出项的 Span 全零，消息内容与参考版同构）。
    fn unify_catch(&mut self, bump: &Bump, cxt: &Cxt<'_>, t: V, t_prime: V) -> Result<(), Error> {
        let decls = cxt.decl.borrow();
        self.fuel.set(UNIFY_FUEL);
        if self.unify(bump, &decls, cxt.lvl, t, t_prime) {
            Ok(())
        } else {
            let fuel_note = if self.fuel.get() == 0 {
                " (fuel exhausted)"
            } else {
                ""
            };
            let tq = export(self.quote(bump, &decls, cxt.lvl, t));
            let uq = export(self.quote(bump, &decls, cxt.lvl, t_prime));
            let names = types_names_list(cxt.types);
            Err(Error(format!(
                "can't unify{} {} == {}",
                fuel_note,
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            )))
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β / 触发 prim / 吸收 pending——分配一律落本轮 bump）。
    pub(super) fn force_v(&mut self, bump: &Bump, decls: &FxHashMap<String, DeclEntryF>, v: V) -> V {
        let Machine {
            spine,
            defs,
            metas,
            mutable_map,
            fuel,
            ..
        } = self;
        force(bump, spine, defs, metas, decls, mutable_map, fuel, v)
    }

    // 隐式插入（上游 Elaboration.hs 的 insert 族）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> (&'a Tm<'a>, V) {
        let decls = cxt.decl.borrow();
        let va = self.force_v(bump, &decls, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, &decls, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, &decls, env, p.body)
            };
            let t2 = bump.alloc(Tm::App(t, m, Icit::Impl));
            self.insert_go(bump, cxt, t2, b)
        } else {
            (t, va)
        }
    }

    /// infer 后无条件插入。
    fn insert_t<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        Ok(self.insert_go(bump, cxt, t, va))
    }

    /// infer 后插入，但隐式 lambda 本身免插。
    fn insert<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        if let Tm::Lam(_, Icit::Impl, _) = t {
            Ok((t, va))
        } else {
            self.insert_t(bump, cxt, t, va)
        }
    }

    /// `insertUntilName`：插入到名字匹配的隐式 Pi binder 为止。
    fn insert_until_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        name: &str,
        t: &'a Tm<'a>,
        mut va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let decls = cxt.decl.borrow();
        let mut t = t;
        loop {
            let forced = self.force_v(bump, &decls, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, &decls, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, &decls, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(Error(format!(
                    "no named implicit arg {:?}",
                    empty_span(name.to_owned())
                )));
            }
        }
    }

    // 主 check（与参考版 elaboration.rs `check` 逐臂对应）
    // --------------------------------------------------------------------------------

    pub(super) fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        let decls = cxt.decl.borrow();
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, &decls, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫：命名隐式 `[x = e]` 对准同名隐式 Π；
                // 显式对显式（Span 的 PartialEq 只比 data——命名 binder 按
                // 名字匹配，L06 同款语义）
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命中：按 λ 的 binder 名绑定（源码名，入名字表）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, &decls, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, &decls, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, &cxt2, tbody, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, &decls, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, &decls, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, &cxt2, t, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general
                    let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt, a, tty)?;
                    Ok(t2)
                }
            } else {
                let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                self.unify_catch(bump, cxt, a, tty)?;
                Ok(t2)
            }
        } else if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl {
            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            let p = v_pi_of(a);
            let name: &'a str = bump.alloc_str(p.name);
            let body_a = {
                let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                self.eval(bump, &decls, env, p.body)
            };
            let mark = cxt.mark;
            let a_t = self.quote(bump, &decls, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, &cxt2, t, body_a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t2, u2) = t {
            let a_tm = self.check_ty(bump, cxt, a_ty)?;
            let va = self.eval(bump, &decls, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t2, va)?;
            let vt = self.eval(bump, &decls, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let mark = cxt.mark;
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, &cxt2, u2, a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else if let Raw::Match(expr, clauses) = t {
            // match：编译（特化合一在编译期完成）+ 逐分支检查
            let (tm, typ) = self.infer_expr(bump, cxt, expr)?;
            let mut compiler = Compiler::new();
            compiler.compile(self, bump, typ, tm, clauses, cxt, a)?;
            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                bump.alloc_slice_fill_iter(compiler.pats.into_iter());
            Ok(bump.alloc(Tm::Match(tm, cs)))
        } else {
            let (t2, tty) = self.infer_expr(bump, cxt, t)?;
            let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
            self.unify_catch(bump, cxt, a, tty)?;
            Ok(t2)
        }
    }

    /// 类型注解的 universe 结构预检（L13 `check_universe` 轻量移植，零副作用）：
    /// `LiteralIntro` 恒非类型；`Var` 经 name_map（局部）或 decl 表（全局）
    /// 命中且类型已确定（非 U、非未解 meta）→ 定向报错。洞 / 未解 meta /
    /// 其余形态放行——可解性交主检查路径（预检不推断、不造 meta，?N 编号
    /// 不受扰动）。
    fn ty_precheck(&mut self, bump: &Bump, decls: &FxHashMap<String, DeclEntryF>, t: &Raw) -> Result<(), Error> {
        match t {
            Raw::LiteralIntro(_) => Err(Error("expected universe, got LiteralType".to_owned())),
            Raw::Var(x) => {
                // 局部优先（name_map），其次全局 decl 表——与 infer 的
                // Var 臂解析序一致
                let ty = self
                    .name_map
                    .get(x.data.as_str())
                    .map(|&(_, ty)| ty)
                    .or_else(|| decls.get(x.data.as_str()).map(|e| e.ty));
                if let Some(ty) = ty {

                    // force 已展开已解 meta；未解 flex（裸 tag 5，或任意
                    // spine 的 meta 头链）放行——参考版 `Val::Flex(_, _) =>
                    // Ok(())` 对 spine 形状不设限，这里用 is_flex 走 spine_head
                    // 判头（只看栈顶槽的 f 会把 ≥2 实参的 flex 链误判成非
                    // flex）

                    let v = self.force_v(bump, decls, ty);
                    if v_tag(v) == 3 {
                        return Ok(());
                    }

                    // force 已展开已解 meta；未解 flex（裸 tag 5，或任意
                    // spine 的 meta 头链）放行——参考版 `Val::Flex(_, _) =>
                    // Ok(())` 对 spine 形状不设限，这里用 is_flex 走 spine_head
                    // 判头（只看栈顶槽的 f 会把 ≥2 实参的 flex 链误判成非
                    // flex——L07 已修，2026-09 连续性审计回移）

                    if is_flex(&self.spine, v) {
                        Ok(())
                    } else {
                        Err(Error(format!("expected universe, got V({})", v.0)))
                    }
                } else {
                    Ok(()) // 未知名：主检查报 name-not-in-scope（原路径）
                }
            }
            _ => Ok(()),
        }
    }

    /// 类型注解检查入口（Def/enum/struct 类型 / let 注解 / Π 域与余域）：
    /// 结构预检后回落原 `check(…, v_u())`；Π 链逐段预检——域检查后在绑定
    /// 上下文里预检余域（与原 Pi 臂同构，域/余域各只检查一次，无额外 meta）。
    fn check_ty<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<&'a Tm<'a>, Error> {
        if let Raw::Pi(x, i, a, b) = t {
            let decls = cxt.decl.borrow();
            self.ty_precheck(bump, &decls, a)?;
            let a_tm = self.check(bump, cxt, a, v_u())?;
            let va = self.eval(bump, &decls, cxt.env, a_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let mark = cxt.mark;
            let a_t = self.quote(bump, &decls, cxt.lvl, va);
            let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
            let res: Result<&'a Tm<'a>, Error> = {
                self.ty_precheck(bump, &decls, b)?;
                let b_tm = self.check(bump, &cxt2, b, v_u())?;
                Ok(bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)))
            };
            self.unwind_names(mark);
            res
        } else {
            let decls = cxt.decl.borrow();
            self.ty_precheck(bump, &decls, t)?;
            self.check(bump, cxt, t, v_u())
        }
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let decls = cxt.decl.borrow();
        match t {
            // 变量：先局部（src_names / name_map），再全局（decl 表）
            Raw::Var(x) => {
                if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed) {
                    if let Some(&(blvl, ty)) = self.name_map.get(x.data.as_str()) {
                        return Ok((bump.alloc(Tm::Var(cxt.lvl - blvl - 1)), ty));
                    }
                } else {
                    // 消融口径：沿 types 链线性找名（跳过 inserted binder）
                    let mut i = 0u32;
                    let mut tys = cxt.types;
                    while let Some(tc) = tys {
                        if tc.source && tc.name == x.data {
                            return Ok((bump.alloc(Tm::Var(i)), tc.ty));
                        }
                        i += 1;
                        tys = tc.next;
                    }
                }
                if let Some(e) = cxt.decl.borrow().get(x.data.as_str()) {
                    return Ok((bump.alloc(Tm::Decl(bump.alloc_str(&x.data))), e.ty));
                }
                Err(Error(format!("name not in scope: {}", x.data)))
            }

            Raw::Obj(x, f) => {
                // 限定构造子引用 `Enum.case`——**局部遮蔽优先**：接收者名字
                // 已被局部 binder 占用时必须走正常投影（与 Raw::Var 的
                // 「局部先于全局」同序），否则同名局部会让 `Foo.c2` 静默
                // 解析成全局构造子（类型恰巧对上即是错误的 Ok）
                if let Raw::Var(n) = &**x {
                    let shadowed = if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed)
                    {
                        self.name_map.contains_key(n.data.as_str())
                    } else {
                        // 消融口径：沿 types 链线性找名（跳过 inserted binder）
                        let mut tys = cxt.types;
                        loop {
                            match tys {
                                Some(tc) if tc.source && tc.name == n.data => break true,
                                Some(tc) => tys = tc.next,
                                None => break false,
                            }
                        }
                    };
                    if !shadowed {
                        let key = format!("{}.{}", n.data, f.data);
                        if let Some(e) = cxt.decl.borrow().get(key.as_str()) {
                            return Ok((bump.alloc(Tm::Decl(bump.alloc_str(&key))), e.ty));
                        }
                    }
                }
                let (tm, ty) = self.infer_expr(bump, cxt, x)?;
                let tyf = self.force_v(bump, &decls, ty);
                if v_tag(tyf) == 7 {
                    if let XCell::Sum {
                        name: sname,
                        params,
                        cases,
                    } = v_xcell_of(tyf)
                    {
                        // 接收者类型是 Sum：索引/参数槽优先取类型槽；未命中
                        // 且是 **struct**（单 case、名字形如 `{Name}.mk`）时
                        // 剥 `mk` 的构造子类型链取字段类型——与参考版
                        // elaboration 的 `Raw::Obj` 臂逐句对应。隐式参数用
                        // 头部 Sum 实参实例化；显式字段 binder 用接收者的
                        // **卡住投影值**实例化（`eval(Obj(接收者项, 字段名))`，
                        // 如 `Exists.proof` 剥出 `Eq e.witness two`）。旧实现
                        // 以 `U` 占位，依赖在前字段的在后字段在检查位会假拒，
                        // 修正于评审，两版同步。
                        if let Some(p) = params.iter().find(|p| p.name == f.data) {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                p.ty,
                            ));
                        }
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let ctor_ty = cxt.decl.borrow().get(cases[0]).map(|e| e.ty);
                            if let Some(mut ty) = ctor_ty {
                                let impl_vals: Vec<V> = params
                                    .iter()
                                    .filter(|p| p.icit == Icit::Impl)
                                    .map(|p| p.val)
                                    .collect();
                                let mut impl_idx = 0;
                                loop {
                                    let tyf2 = self.force_v(bump, &decls, ty);
                                    if v_tag(tyf2) == 4 {
                                        let p = v_pi_of(tyf2);
                                        if p.name == f.data {
                                            return Ok((
                                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                                p.dom,
                                            ));
                                        }
                                        let u = if impl_idx < impl_vals.len() {
                                            let v = impl_vals[impl_idx];
                                            impl_idx += 1;
                                            v
                                        } else {
                                            let obj =
                                                bump.alloc(Tm::Obj(tm, bump.alloc_str(p.name)));
                                            self.eval(bump, &decls, cxt.env, obj)
                                        };
                                        let env = env_ext(bump, p.env, u);
                                        ty = self.eval(bump, &decls, env, p.body);
                                    } else {
                                        break;
                                    }
                                }
                            }
                        }
                        return Err(Error(format!("{} has no field {}", sname, f.data)));
                    }
                    if let XCell::SumCase {
                        typ,
                        case_name,
                        datas,
                    } = v_xcell_of(tyf)
                    {
                        // 接收者类型是构造子值：索引参数优先，否则剥构造子
                        // 类型取字段真实类型
                        let (sname, sparams) = match v_xcell_of(*typ) {
                            XCell::Sum { name, params, .. } => (*name, *params),
                            _ => return Err(Error("ill-scoped SumCase".to_owned())),
                        };
                        if let Some(p) = sparams.iter().find(|p| p.name == f.data) {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                p.ty,
                            ));
                        }
                        let ctor_ty = cxt
                            .decl
                            .borrow()
                            .get(&format!("{}.{}", sname, case_name))
                            .ok_or_else(|| Error("missing constructor decl".to_owned()))?
                            .ty;
                        let impl_vals: Vec<V> = sparams
                            .iter()
                            .filter(|p| p.icit == Icit::Impl)
                            .map(|p| p.val)
                            .collect();
                        let mut ty = ctor_ty;
                        let mut impl_idx = 0;
                        loop {
                            let tyf2 = self.force_v(bump, &decls, ty);
                            if v_tag(tyf2) == 4 {
                                let p = v_pi_of(tyf2);
                                if p.name == f.data {
                                    return Ok((
                                        bump.alloc(Tm::Obj(tm, bump.alloc_str(&f.data))),
                                        p.dom,
                                    ));
                                }
                                let u = if impl_idx < impl_vals.len() {
                                    let v = impl_vals[impl_idx];
                                    impl_idx += 1;
                                    v
                                } else {
                                    match datas.iter().find(|d| d.name == p.name) {
                                        Some(d) => d.val,
                                        None => {
                                            return Err(Error(format!(
                                                "no field {} on {}",
                                                f.data, sname
                                            )))
                                        }
                                    }
                                };
                                let env = env_ext(bump, p.env, u);
                                ty = self.eval(bump, &decls, env, p.body);
                            } else {
                                return Err(Error(format!(
                                    "{} has no field {}",
                                    sname, f.data
                                )));
                            }
                        }
                    }
                }
                Err(Error(format!("cannot project field {}", f.data)))
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, &decls, cxt.env, new_meta);
                let mark = cxt.mark;
                let a_t = self.quote(bump, &decls, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let (t_inferred, b) = self.infer_expr(bump, &cxt2, tbody)?;
                let (t_inferred, b) = self.insert(bump, &cxt2, t_inferred, b)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, &decls, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell {
                    name,
                    icit: *i,
                    dom: a,
                    env: cxt.env,
                    body,
                });
                Ok((bump.alloc(Tm::Lam(name, *i, t_inferred)), v_pi(cell)))
            }

            Raw::Lam(x, Either::Name(_), _) => {
                Err(Error(format!("infer named lambda {:?}", x)))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_until_name(bump, cxt, &name.data, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, &decls, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(format!("icit mismatch {:?} {:?}", i, p.icit)));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder（PI_NAME）不进名字表：只延伸 env/telescope/
                    // pruning。参数序：期望 = 合成 Π（参考版把合成 Π 放在
                    // unify_catch 的首位——忠实复刻，只影响报错文案方向）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u());
                    let a = self.eval_fresh(bump, &decls, cxt.env, new_meta);
                    let a_t = self.quote(bump, &decls, cxt.lvl, a);
                    let cxt2 = Cxt {
                        env: env_ext(bump, cxt.env, v_lvl(cxt.lvl)),
                        types: cxt.types,
                        locals: Some(bump.alloc(LCons {
                            name: PI_NAME,
                            a_t,
                            t_t: None,
                            next: cxt.locals,
                        })),
                        pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
                        binds: cxt.binds + 1, // 合成 binder 也是绑定槽
                        lvl: cxt.lvl + 1,
                        mark: cxt.mark,
                        decl: cxt.decl.clone(),
                    };
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u());
                    let cell = bump.alloc(PiCell {
                        name: PI_NAME,
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u_checked = self.check(bump, cxt, u, a)?;
                let arg_v = self.eval(bump, &decls, cxt.env, u_checked);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, &decls, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u_checked, i)), ty))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())),

            Raw::Pi(x, i, a, b) => {
                let a_tm = self.check_ty(bump, cxt, a)?;
                let va = self.eval(bump, &decls, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let a_t = self.quote(bump, &decls, cxt.lvl, va);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
                let b_tm = self.check_ty(bump, &cxt2, b)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)), v_u()))
            }

            Raw::Let(x, a_ty, t2, u2) => {
                let a_tm = self.check_ty(bump, cxt, a_ty)?;
                let va = self.eval(bump, &decls, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t2, va)?;
                let vt = self.eval(bump, &decls, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
                let (u_tm, uty) = self.infer_expr(bump, &cxt2, u2)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, &decls, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&literal.data))),
                v_lit_ty(),
            )),

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(..) => Err(Error(
                "match cannot be inferred; give it an expected type".to_owned(),
            )),

            // enum 本体（Decl::Enum 注册期构造）：逐参数推断值 + 引读类型
            Raw::Sum(name, params, cases) => {
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for (n, i, raw) in params {
                    let (value_checked, value_ty) = self.infer_expr(bump, cxt, raw)?;
                    let ty = self.quote(bump, &decls, cxt.lvl, value_ty);
                    ps.push(SumParamT {
                        name: bump.alloc_str(&n.data),
                        val: value_checked,
                        ty,
                        icit: *i,
                    });
                }
                let cs: Vec<&'a str> = cases.iter().map(|c| &*bump.alloc_str(&c.data)).collect();
                Ok((
                    bump.alloc(Tm::Sum(
                        bump.alloc_str(&name.data),
                        bump.alloc_slice_fill_iter(ps),
                        bump.alloc_slice_fill_iter(cs),
                    )),
                    v_u(),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造）：typ 只推断不检查
            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, &decls, cxt.env, typ_checked);
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for (n, raw, i) in datas {
                    let (tm, _) = self.infer_expr(bump, cxt, raw)?;
                    ds.push(SumDataT {
                        name: bump.alloc_str(&n.data),
                        val: tm,
                        icit: *i,
                    });
                }
                Ok((
                    bump.alloc(Tm::SumCase {
                        typ: typ_checked,
                        case_name: bump.alloc_str(&case_name.data),
                        datas: bump.alloc_slice_fill_iter(ds),
                    }),
                    typ_val,
                ))
            }
        }
    }

    /// decl 层的推断（参考版 `Infer::infer(Decl)`）：Def 折叠参数后检查，
    /// **占位 → 检查 → force 到 WHNF → 覆盖登记**（副作用在声明序上驱动
    /// ——递归自引用由 force 的占位守卫兜住）；Println 推断体；Enum 注册
    /// 类型本体 + 逐构造子（限定名 `Enum.case` + 裸名别名）。
    pub(super) fn infer_decl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        d: &Decl,
    ) -> Result<(DeclOut<'a>, Cxt<'a>), Error> {
        match d {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                // 参数折叠：typ = Π 参数. 返回类型；bod = λ 参数. 体。
                // 无参时零克隆（借用直用），有参才构造包装层
                let mut typ = std::borrow::Cow::Borrowed(ret_type);
                for (n, a, i) in params.iter().rev() {
                    typ = std::borrow::Cow::Owned(Raw::Pi(
                        n.clone(),
                        *i,
                        Box::new(a.clone()),
                        Box::new(typ.into_owned()),
                    ));
                }
                let mut bod = std::borrow::Cow::Borrowed(body);
                for (n, _, i) in params.iter().rev() {
                    bod = std::borrow::Cow::Owned(Raw::Lam(
                        n.clone(),
                        Either::Icit(*i),
                        Box::new(bod.into_owned()),
                    ));
                }
                // 借用块化：Ref 带 Drop，作用域尾才释放——顶层的借力会压到
                // 整个 match，与后面的 decl_insert（borrow_mut）冲突
                let vtyp = {
                    let decls = cxt.decl.borrow();
                    let typ_tm = self.check_ty(bump, cxt, &typ)?;
                    self.eval(bump, &decls, cxt.env, typ_tm)
                };
                // 重定义检查（与参考版同款，L13 `fake_bind` 移植）：builtin /
                // 先前 def / enum / struct 已登记 → 定向报错。必须在占位插入
                // 之前查（占位会平铺覆盖同名条目），且先类型后重定义一致。
                if cxt.decl.borrow().contains_key(name.data.as_str()) {
                    return Err(Error(format!("redefine {}", name.data)));
                }
                // 递归：先把名字登记成指向自身的中性占位，检查体，再用真实
                // 值覆盖。占位只存在于克隆出来的 decl 表里，不影响外层。
                let fake = decl_insert(
                    cxt,
                    &name.data,
                    DeclEntryF {
                        ty: vtyp,
                        val: v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(&name.data)))),
                    },
                );
                // decls_f 块化：Ref 带 Drop（作用域尾释放），必须在
                // 终值覆盖的 decl_insert 之前释放
                let vt = {
                    let decls_f = fake.decl.borrow();
                    let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                    // 注册值归约到 WHNF：builtin 副作用（可变全局写 / 文件
                    // IO）在声明序上驱动——L06「应用时触发」的等价物（否则
                    // change_mutable 等只在别处 force 到它时才生效）。
                    let v = self.eval(bump, &decls_f, fake.env, t_tm);
                    self.force_v(bump, &decls_f, v)
                };
                let out = decl_insert(cxt, &name.data, DeclEntryF { ty: vtyp, val: vt });
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), Cxt { env: cxt.env, types: cxt.types, locals: cxt.locals, pruning: cxt.pruning, binds: cxt.binds, lvl: cxt.lvl, mark: cxt.mark, decl: cxt.decl.clone() }))
            }
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U（与参考版
                // 同步）。域洞若保留，第 2+ 个参数的域 meta 会带 pruning
                // （形如 `?m A`），使用点解 `?m A := U` 时 invert 无法倒序
                // Decl 头 spine 而失败——显式提供隐式实参即报 can't unify。

                // 方括号参数在语言定义上就是类型参数；显式标注与显式索引
                // 不动。struct 脱糖走的也是本臂。（L07 黑盒三轮修复，
                // 2026-09 连续性审计回移。）

                let params: Vec<(crate::parser_lib::Span<String>, Raw, Icit)> = params
                    .iter()
                    .map(|(n, a, i)| {
                        let a = if *i == Icit::Impl && matches!(a, Raw::Hole) {
                            Raw::U
                        } else {
                            a.clone()
                        };
                        (n.clone(), a, *i)
                    })
                    .collect();
                // enum 类型本体：λ params → Sum(name, [(p, Var p, ?, icit)], cases)
                let new_params: Vec<(crate::parser_lib::Span<String>, Icit, Raw)> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数（显式索引留给
                // 构造子的 -> 给出）
                let default_ret = params
                    .iter()
                    .filter(|x| x.2 == Icit::Impl)
                    .fold(Raw::Var(name.clone()), |ret, x| {
                        Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Var(x.0.clone())),
                            Either::Icit(Icit::Impl),
                        )
                    });
                // 构造子类型：Pi(枚举隐式参数 ++ 构造子绑定器) -> (用户 ret || 缺省)
                let new_cases: Vec<(crate::parser_lib::Span<String>, Raw)> = cases
                    .iter()
                    .map(|(case_name, p, bind)| {
                        let ty = params
                            .iter()
                            .filter(|x| x.2 == Icit::Impl)
                            .cloned()
                            .chain(p.clone())
                            .rev()
                            .fold(
                                bind.clone().unwrap_or(default_ret.clone()),
                                |ret, x| {
                                    Raw::Pi(x.0.clone(), x.2, Box::new(x.1.clone()), Box::new(ret))
                                },
                            );
                        (case_name.clone(), ty)
                    })
                    .collect::<Vec<_>>();
                let cases_spanned: Vec<crate::parser_lib::Span<String>> = new_cases
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect();
                let sum = Raw::Sum(name.clone(), new_params, cases_spanned);
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U, |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let vtyp = {
                    let decls = cxt.decl.borrow();
                    let typ_tm = self.check_ty(bump, cxt, &typ)?;
                    self.eval(bump, &decls, cxt.env, typ_tm)
                };
                // 重定义检查（与参考版同款）：同名 enum / struct / def /
                // builtin → 定向报错，占位插入之前查表。
                if cxt.decl.borrow().contains_key(name.data.as_str()) {
                    return Err(Error(format!("redefine {}", name.data)));
                }
                // 先占位再检查本体（本体内部引用自身时报"指向自身的中性值"）
                let fake = decl_insert(
                    cxt,
                    &name.data,
                    DeclEntryF {
                        ty: vtyp,
                        val: v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(&name.data)))),
                    },
                );
                // decls_f 块化（同 Def 臂：Ref 作用域尾释放）
                let vt = {
                    let decls_f = fake.decl.borrow();
                    let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                    self.eval(bump, &decls_f, fake.env, t_tm)
                };
                let mut cxt = decl_insert(cxt, &name.data, DeclEntryF { ty: vtyp, val: vt });
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}
                for ((case_name, binders, ret), (ctor_name, ctor_ty)) in
                    cases.iter().zip(new_cases.iter())
                {
                    let body_ret = Raw::SumCase {
                        typ: Box::new(ret.clone().unwrap_or(default_ret.clone())),
                        case_name: case_name.clone(),
                        datas: binders
                            .iter()
                            .map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i))
                            .collect(),
                    };
                    let bod = params
                        .iter()
                        .filter(|x| x.2 == Icit::Impl)
                        .cloned()
                        .chain(binders.clone())
                        .rev()
                        .fold(body_ret, |a, b| {
                            Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                        });
                    // 借用作用域化：decls_c 必须在 decl_insert（borrow_mut）
                    // 之前释放；entry 是 Copy 可逃逸
                    let entry = {
                        let decls_c = cxt.decl.borrow();
                        let typ_tm = self.check(bump, &cxt, ctor_ty, v_u())?;
                        let vtyp = self.eval(bump, &decls_c, cxt.env, typ_tm);
                        // 构造子良构性（参考版同步）：ret 必须是本 enum 的
                        // Sum 且参数位是 telescope 内的 bare rigid
                        self.check_ctor_wf(bump, &cxt, &name.data, &ctor_name.data, vtyp)?;
                        let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                        let vt = self.eval(bump, &decls_c, cxt.env, t_tm);
                        DeclEntryF { ty: vtyp, val: vt }
                    };
                    // 限定名 `Enum.case` + 裸名别名（后注册者覆盖同名裸名）
                    cxt = decl_insert(
                        &cxt,
                        &format!("{}.{}", name.data, ctor_name.data),
                        entry,
                    );
                    cxt = decl_insert(&cxt, &ctor_name.data, entry);
                }
                Ok((DeclOut::Enum, cxt))
            }
        }
    }

    /// 构造子返回类型良构性（参考版 `Infer::check_ctor_wf` 同款，
    /// 2026-09-18）：实例化构造子类型的全部绑定器后，ret 的 WHNF 必须是
    /// `enum_name` 的 `Sum`，且其隐式参数位逐一等于 telescope 内的 bare
    /// rigid。允许构造子重绑定参数（`p[A,B](a,b) -> Pack[A][B] a b`，
    /// 多索引 GADT 钉），拒绝参数位非变量（`c -> Foo[Bool]`）与
    /// 非本 enum 的 ret（`c -> Nat`）——后者向构造子名字空间注入永不匹配
    /// 任何模式的 phantom 值，对覆盖检查完备的 match 在封闭输入上卡死。
    fn check_ctor_wf(
        &mut self,
        bump: &Bump,
        cxt: &Cxt<'_>,
        enum_name: &str,
        ctor_name: &str,
        ctor_vtyp: V,
    ) -> Result<(), Error> {
        let decls = cxt.decl.borrow();
        let base = cxt.lvl;
        let mut ty = ctor_vtyp;
        let mut bound = 0u32;
        let ret = loop {
            let tyf = self.force_v(bump, &decls, ty);
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let u = v_lvl(base + bound);
                bound += 1;
                let env = env_ext(bump, p.env, u);
                ty = self.eval(bump, &decls, env, p.body);
            } else {
                break tyf;
            }
        };
        let retf = self.force_v(bump, &decls, ret);
        if !(v_tag(retf) == 7 && matches!(v_xcell_of(retf), XCell::Sum { .. })) {
            return Err(Error(format!(
                "构造子 {ctor_name} 的返回类型不是和类型"
            )));
        }
        match v_xcell_of(retf) {
            XCell::Sum { name: sname, params, .. } => {
                if *sname != enum_name {
                    return Err(Error(format!(
                        "构造子 {ctor_name} 的返回类型是 {sname}，不是 {enum_name}"
                    )));
                }
                for p in params.iter() {
                    if p.icit == Icit::Impl {
                        let v = p.val;
                        let bare_rigid = v_tag(v) == 0
                            && v_lvl_of(v) >= base
                            && v_lvl_of(v) < base + bound;
                        if !bare_rigid {
                            return Err(Error(format!(
                                "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
                            )));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// decl 层推断的产出：Def 带名（bench 的 nf 口径按名查表），Println 带
/// elaborated 体（run 的 nf 输出用）。
pub(super) enum DeclOut<'a> {
    Def { name: &'a str },
    Println(&'a Tm<'a>),
    Enum,
}

/// locals 链形态判定（见 L05 同名函数）：头 bind 段长 k + 其后全 define
/// → Some(k)；交错 → None。
fn bind_prefix_of_telescope(mut ls: Option<&LCons<'_>>) -> Option<u32> {
    let mut k = 0u32;
    while let Some(n) = ls {
        if n.t_t.is_none() {
            k += 1;
            ls = n.next;
        } else {
            break;
        }
    }
    for n in std::iter::successors(ls, |l| l.next) {
        if n.t_t.is_none() {
            return None;
        }
    }
    Some(k)
}

/// 项里是否含自由 `Var`（按 binder 深度算）。`fresh_meta` 快捷路径 2 的
/// 判据（保守：自由 ⇒ 走全构造）。
fn has_free_var(t: &Tm<'_>) -> bool {
    let mut stack: Vec<(&Tm<'_>, u32)> = vec![(t, 0)];
    while let Some((x, d)) = stack.pop() {
        match x {
            Tm::Var(i) => {
                if *i >= d {
                    return true;
                }
            }
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Decl(_)
            | Tm::Prim(_) => {}
            Tm::Obj(h, _) => stack.push((h, d)),
            Tm::Pi(_, _, a, b) => {
                stack.push((a, d));
                stack.push((b, d + 1));
            }
            Tm::Let(_, a, t, u) => {
                stack.push((a, d));
                stack.push((t, d));
                stack.push((u, d + 1));
            }
            Tm::Sum(_, params, _) => {
                for p in params.iter() {
                    stack.push((p.val, d));
                    stack.push((p.ty, d));
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push((typ, d));
                for dd in datas.iter() {
                    stack.push((dd.val, d));
                }
            }
            Tm::Match(s, cases) => {
                stack.push((s, d));
                for (_, b) in cases.iter() {
                    stack.push((b, d));
                }
            }
        }
    }
    false
}
// Elaboration 上下文与 decl 表（写时复制）
// --------------------------------------------------------------------------------

/// Elaboration 上下文（绑定量在 bump 里）。`decl` = Rc 写时复制的全局
/// decl 表（参考版 `Cxt::decl_insert` 的 `Rc::make_mut` 语义）。方法一律
/// 借用 `&Cxt`（Rc 非 Copy——扩展上下文返回**新的** Cxt 值）。
pub(super) struct Cxt<'a> {
    pub(super) env: Env<'a>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目；println 的 pretty 名
    /// 单也走这里，与参考版 `Cxt::names()` 的 locals 序一致）。
    pub(super) types: Option<&'a TCons<'a>>,
    /// telescope（上游 `cxtLocals`）：fresh_meta 闭类型用。
    locals: Option<&'a LCons<'a>>,
    /// fresh meta 的 scope 掩码（与 env 平行；头 = 最内层）。
    pruning: Option<&'a PrCons<'a>>,
    /// 绑定层数（bind/new_binder/synth +1，define 不动）。
    binds: u32,
    pub(super) lvl: u32,
    /// 名字撤销轨迹的本上下文基线（inserted binder 不留轨迹、不动 mark）。
    mark: u32,
    /// 全局 decl 表（名 → (类型值, WHNF 值)）：def / enum / 构造子都登记
    /// 在这里；项层引用 `Tm::Decl(名)` 求值时查表取缓存的 WHNF。
    /// RefCell 共享可变：decl_insert **平铺覆盖**（O(1)，不克隆整表）——
    /// 顶层 elaboration 的插入全部单调（占位 → 同名覆盖为终值），平铺表
    /// 与参考版写时复制在该使用形态下语义等价；检查期间无插入（插入只在
    /// decl 边界），borrow 纪律成立。
    pub(super) decl: Rc<RefCell<FxHashMap<String, DeclEntryF>>>,
}

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
pub(super) struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

impl<'a> Cxt<'a> {
    fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
            mark: 0,
            decl: Rc::new(RefCell::new(FxHashMap::default())),
        }
    }
}

/// 写入一个 decl。**平铺覆盖**（O(1)）：顶层 elaboration 的插入全部
/// 单调（占位 → 同名覆盖为终值），RefCell 共享同一张表——递归定义的
/// "占位只对本定义的检查可见"由覆盖时序保证（占位先插、终值后插同名
/// 键，查表取后者）。写时复制克隆整表是 O(n)/次 → def 链 O(n²)
/// （strchain k=12 实测 830ms 的根因），平铺后 ~13ms。
fn decl_insert<'a>(cxt: &Cxt<'a>, k: &str, e: DeclEntryF) -> Cxt<'a> {
    {
        let mut d = cxt.decl.borrow_mut();
        // 覆盖写（占位 → 终值）不重分配键串
        match d.get_mut(k) {
            Some(slot) => *slot = e,
            None => {
                d.insert(k.to_string(), e);
            }
        }
    }
    Cxt {
        env: cxt.env,
        types: cxt.types,
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
        mark: cxt.mark,
        decl: cxt.decl.clone(),
    }
}

/// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
/// 这些是模式特化方程可以求解的对象。let 定义槽（槽里是值不是 vvar）天然
/// 不在其中。嵌套 match 的入口上下文可能已被外层精化包裹（`subst_cxt`）
/// ——解包 VSub 看**槽的原始形态**；外层已解变量也按 raw 层级进入基线
///（无害：方程里它不再以 bare rigid 出现，force 在读点已展开）。
///（参考版 `Cxt::bind_slots` 同款过滤。）
pub(super) fn bind_slots(defs: &[V], cxt: &Cxt<'_>) -> Vec<u32> {
    let n = cxt.lvl;
    let len = env_len(cxt.env);
    let mut out = Vec::new();
    for i in 0..len {
        let mut v = env_nth(defs, cxt.env, i);
        while v_tag(v) == 7 {
            match v_xcell_of(v) {
                XCell::VSub { val, .. } => v = *val,
                _ => break,
            }
        }
        if v_tag(v) == 0 {
            let l = v_lvl_of(v);
            if l + i + 1 == n {
                out.push(l);
            }
        }
    }
    out
}

/// 把精化替换 σ 施加到上下文（dpm-nbe `subst sub ctx` / 参考版
/// `Cxt::subst_cxt`）：env 槽与 types 链的类型包 VSub；lvl / locals /
/// pruning / binds / mark / decl 不动——**槽位布局（= 运行时布局）不变**，
/// 被解变量仍在原槽位，读点经 force 展开看到解。σ 为空时零开销直通。
pub(super) fn subst_cxt<'a>(bump: &'a Bump, defs: &[V], sub: &Rc<SubstV>, cxt: &Cxt<'a>) -> Cxt<'a> {
    fn wrap_types<'a>(
        bump: &'a Bump,
        sub: &Rc<SubstV>,
        t: Option<&'a TCons<'a>>,
    ) -> Option<&'a TCons<'a>> {
        match t {
            None => None,
            Some(tc) => {
                let next = wrap_types(bump, sub, tc.next);
                Some(bump.alloc(TCons {
                    name: tc.name,
                    ty: wrap_sub(bump, sub, tc.ty),
                    source: tc.source,
                    next,
                }))
            }
        }
    }
    Cxt {
        env: if sub.is_empty() {
            cxt.env
        } else {
            frcs_env(bump, defs, sub, cxt.env)
        },
        types: if sub.is_empty() {
            cxt.types
        } else {
            wrap_types(bump, sub, cxt.types)
        },
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
        mark: cxt.mark,
        decl: cxt.decl.clone(),
    }
}

/// types 链 → 参考版 pretty 的名字 List（头 = 最内层；List::prepend 从尾
/// 起构回，序不变）。
pub(super) fn types_names_list(tys: Option<&TCons<'_>>) -> crate::list::List<String> {
    let mut ns: Vec<String> = Vec::new();
    let mut cur = tys;
    while let Some(tc) = cur {
        ns.push(tc.name.to_owned());
        cur = tc.next;
    }
    let mut list = crate::list::List::new();
    for n in ns.into_iter().rev() {
        list = list.prepend(n);
    }
    list
}
// builtin 注册（每轮 prime；参考版 `Cxt::new` + `add_builtin` 逐条对应）
// --------------------------------------------------------------------------------

/// `(String ->)^n ret` —— L07 builtin 的参数类型全为 String。
fn str_pi<'a>(bump: &'a Bump, params: &[&str], ret: &'a Tm<'a>) -> &'a Tm<'a> {
    let mut t = ret;
    for name in params.iter().rev() {
        t = bump.alloc(Tm::Pi(
            bump.alloc_str(name),
            Icit::Expl,
            bump.alloc(Tm::LiteralType),
            t,
        ));
    }
    t
}

/// `(name : dom) -> cod`。
fn tm_pi<'a>(bump: &'a Bump, name: &str, dom: &'a Tm<'a>, cod: &'a Tm<'a>) -> &'a Tm<'a> {
    bump.alloc(Tm::Pi(bump.alloc_str(name), Icit::Expl, dom, cod))
}

/// `string_to_global_type Var(ix)`（de Bruijn 引用前序参数）。
fn st2g_app<'a>(bump: &'a Bump, ix: u32) -> &'a Tm<'a> {
    bump.alloc(Tm::App(
        bump.alloc(Tm::Decl(bump.alloc_str("string_to_global_type"))),
        bump.alloc(Tm::Var(ix)),
        Icit::Expl,
    ))
}

impl Machine {
    /// 每轮注册（参考版 `Cxt::new(&infer)`）：String 类型进 decl 表；全组
    /// builtin 登记（类型经 eval 成 Π 链值；**值 = λ 参数链 → `Tm::Prim`
    /// 体**——应用满元数后由 force 的 [`prim_reduce`] 归约，L07 的触发
    /// 语义；L06 是应用时触发）。**注册顺序与参考版一致**——
    /// string_to_global_type 必须先于引用它的 global 族（其类型闭包体在
    /// check 期才查表，但防御性保持顺序）。与 L06 不同：builtin 名**不进
    /// env**（源码名经 decl 表解析，参考版 Raw::Var 同序）。
    pub(super) fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let cxt = decl_insert(
            &Cxt::empty(),
            "String",
            DeclEntryF {
                ty: v_u(),
                val: v_lit_ty(),
            },
        );
        let lit_ty: &'a Tm<'a> = bump.alloc(Tm::LiteralType);
        let u_t: &'a Tm<'a> = bump.alloc(Tm::U);
        let builtins: Vec<(&str, &'a Tm<'a>)> = vec![
            ("string_concat", str_pi(bump, &["x", "y"], lit_ty)),
            ("str_eq", str_pi(bump, &["x", "y"], lit_ty)),
            ("str_indent2", str_pi(bump, &["x"], lit_ty)),
            (
                "report_check_issue",
                str_pi(bump, &["code", "module", "signal", "message"], u_t),
            ),
            ("string_to_global_type", str_pi(bump, &["x"], u_t)),
            (
                "create_global",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(bump, "y", st2g_app(bump, 0), u_t),
                ),
            ),
            (
                "change_mutable",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(
                        bump,
                        "f",
                        tm_pi(bump, "_", st2g_app(bump, 0), st2g_app(bump, 1)),
                        u_t,
                    ),
                ),
            ),
            (
                "get_global",
                tm_pi(bump, "x", lit_ty, st2g_app(bump, 0)),
            ),
            (
                "get_global_default",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(bump, "z", st2g_app(bump, 0), st2g_app(bump, 1)),
                ),
            ),
            (
                "change_mutable_default",
                tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    tm_pi(
                        bump,
                        "f",
                        tm_pi(bump, "_", st2g_app(bump, 0), st2g_app(bump, 1)),
                        tm_pi(bump, "z", st2g_app(bump, 1), u_t),
                    ),
                ),
            ),
            ("file_read_all_text", str_pi(bump, &["path"], lit_ty)),
            ("file_write_all_text", str_pi(bump, &["path", "content"], u_t)),
            ("file_append_all_text", str_pi(bump, &["path", "content"], u_t)),
            ("file_exists", str_pi(bump, &["path"], lit_ty)),
            ("file_delete", str_pi(bump, &["path"], u_t)),
        ];
        let mut cxt = cxt;
        for (name, ty) in builtins {
            let va = self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, ty);
            // 值 = λ 参数链 → Prim(name)；参数名从类型的 Π 链取（与域同序）
            let mut names: Vec<&str> = Vec::new();
            let mut cur = ty;
            while let Tm::Pi(n, _, _, body) = cur {
                names.push(n);
                cur = body;
            }
            let mut val: &'a Tm<'a> = bump.alloc(Tm::Prim(bump.alloc_str(name)));
            for p in names.iter().rev() {
                val = bump.alloc(Tm::Lam(bump.alloc_str(p), Icit::Expl, val));
            }
            let head = self.eval(bump, &cxt.decl.borrow(), EMPTY_ENV, val);
            cxt = decl_insert(&cxt, name, DeclEntryF { ty: va, val: head });
        }
        cxt
    }

    /// 参考版 `bench_check` 的主循环（无输出变体）：返回 (是否通过，最终
    /// 上下文，最后一个 def 的名)。
    pub(super) fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Cxt<'a>, Option<&'a str>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            match self.infer_decl(bump, &cxt, d) {
                Ok((out, nc)) => {
                    if let DeclOut::Def { name } = out {
                        last = Some(name);
                    }
                    cxt = nc;
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        (Ok(()), cxt, last)
    }
}
