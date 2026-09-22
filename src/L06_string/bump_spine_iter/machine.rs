//! machine：稳态复用机（`Machine`）与 elaboration（check/infer/decl 表）、
//! Elaboration 上下文（`Cxt`/`TCons`）、builtin 注册（`prime_round`/
//! `elab_all`）。原 bump_spine_iter.rs 的 "Machine（稳态复用）与
//! elaboration"、"builtin 注册" 两节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::cell::RefCell;

use super::parser::syntax::{Decl, Either, Icit, Raw};
use super::{empty_span, Error};

use super::entry::{export, NO_NAME_MAP};
use super::env::{env_ext, env_ext_defs, EMPTY_ENV, Env, PiCell};
use super::eval::{eval_iter, force, W};
use super::prim::{DeclEntryF, MutableMap, Prim};
use super::quote::{quote_iter, QJob, QuoteMemo};
use super::rename::{RenBuf, RenameScratch};
use super::spine::{MetaEntry, Spine};
use super::syntax::{LCons, PrCons, Tm, V, XCell, v_lit_ty, v_lvl, v_meta, v_pi, v_pi_of, v_tag, v_spine_of, v_u, v_xcell};
use super::unify::{unify_iter, UItem};

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// `pruneVFlex` 的 spine 状态（参考版 `SpinePruneStatus` 同构）。
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum SpinePruneStatus {
    OKRenaming,
    OKNonRenaming,
    NeedsPruning,
}

/// 稳态复用机（L05 版 + L06 增量：decl 表与可变全局挂在机上——求值 /
/// 引读 / unify 都要按名查；随轮清空并重新注册 builtin）。
pub(crate) struct Machine {
    spine: Spine,
    vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 名字 → (绑定 lvl, 类型值)：`Raw::Var` 的 O(1) 解析。**只收源码
    /// binder**（bind/define）——inserted binder 不入表。
    name_map: FxHashMap<SmolStr, (u32, V)>,
    /// bind/define 的撤销轨迹：(名字, 旧值)。
    name_trail: Vec<(SmolStr, Option<(u32, V)>)>,
    /// decl 表（L06）：名 → (值, 类型, 可选 builtin prim)。key 用 `SmolStr`
    /// （≤23 字节内联，负载里的 `s12345` 类短键 insert 免堆分配）。
    decls: FxHashMap<SmolStr, DeclEntryF>,
    /// 可变全局（L06）：builtin `create_global` / `change_mutable` 族的
    /// 存取目标。值指向本轮 bump——每轮清空（参考版每次调用新建 Infer）。
    mutable_map: MutableMap,
    /// [perf] 常驻 eval/unify/quote 工作栈（lifetime 洗白存储：核函数进入
    /// 即 clear，条目仅在核函数活动期被读，bump 生命期覆盖之，跨轮无读取）。
    /// eval/quote/unify 共用一个 `workbuf` 是安全的：`work` 是「排空即返回」
    /// 的暂存栈，嵌套调用点（`unify_iter → solve → eval_iter`）进入时它必已
    /// 为空。收益实测见 L03 同名字段注释。
    workbuf: Vec<W<'static>>,
    unifybuf: Vec<UItem<'static>>,
    qtasks: Vec<QJob<'static>>,
    qdone: Vec<&'static Tm<'static>>,
    /// rename 的草稿栈池（[`RenameScratch`]）：rename 经 prune_vflex/prune_ty
    /// 再入，嵌套各取一套；归还前清空，`'static` 洗白存储同 workbuf。
    rename_pool: Vec<RenameScratch<'static>>,
    /// quote 记忆化表：容量跨调用复用，内容**每次调用 clear**——meta 可
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项。
    quote_memo: QuoteMemo<'static>,
}

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
            decls: FxHashMap::default(),
            mutable_map: RefCell::new(FxHashMap::default()),
            workbuf: Vec::new(),
            unifybuf: Vec::new(),
            qtasks: Vec::new(),
            qdone: Vec::new(),
            rename_pool: Vec::new(),
            quote_memo: FxHashMap::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/轨迹/环境区域 + decl 表/可变全局
    /// + 中性 spine 全部清空（保容量；builtin 的重注册在 [`Machine::prime_round`]）。
    /// tag-2 句柄只被上述各项与当轮 bump 值持有，轮边界后无旧句柄可达；
    /// `ren` 存的是层级而非 spine 句柄（且 solve 入口换代），
    /// `vals`/`conv`/`quote_memo`/工作栈各在核函数入口 clear。
    pub(super) fn clear_round(&mut self) {
        self.metas.clear();
        self.name_map.clear();
        self.name_trail.clear();
        self.defs.clear();
        self.decls.clear();
        self.mutable_map.borrow_mut().clear();
        self.spine.clear();
    }

    /// Extend Cxt with a bound variable（源码 binder）。
    #[allow(clippy::too_many_arguments)]
    fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
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
            locals: Some(LCons::alloc(bump, bump.alloc_str(x), a_t, None, cxt.locals)),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
        }
    }

    /// Extend Cxt with an inserted implicit binder：**不入名字表**、trail
    /// 不动、mark 不变——但 telescope/pruning 照常扩展。
    fn new_binder<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
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
            locals: Some(LCons::alloc(bump, bump.alloc_str(x), a_t, None, cxt.locals)),
            pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
            binds: cxt.binds + 1,
            lvl: cxt.lvl + 1,
            mark: cxt.mark,
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    #[allow(clippy::too_many_arguments)]
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
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
            locals: Some(LCons::alloc(bump, bump.alloc_str(x), a_t, Some(t_t), cxt.locals)),
            pruning: Some(bump.alloc(PrCons::new(None, cxt.pruning))),
            binds: cxt.binds, // define 槽不产生 Π 层
            lvl: cxt.lvl + 1,
            mark: cxt.mark + 1,
        }
    }

    /// 截断撤销轨迹到 `mark`（binder 作用域退出）。
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

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等（telescope 只剩 Define 的 Let 层——eval 只往 env
    /// 塞值不添 Π 层）；**快捷路径 1**：locals 为"头 bind 段 + 其后全
    /// define"时只闭 bind 段成 Π、define 槽由 `cxt.env` 快照供给；
    /// **快捷路径 2**（交错形态的兜底）：`quote` 无自由变量则直接空环境
    /// 求值；否则全构造（与参考版同形）。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt.lvl, a);
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
                self.eval(bump, cxt.env, b)
            } else if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, EMPTY_ENV, closed)
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
    fn eval_fresh(&mut self, bump: &Bump, env: Env, m: &Tm<'_>) -> V {
        if let Tm::AppPruning(head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, env, m)
    }

    pub(super) fn eval<'a>(&mut self, bump: &'a Bump, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            workbuf,
            ..
        } = self;
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(workbuf as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
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
            env,
            tm,
        )
    }

    pub(super) fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            workbuf,
            qtasks,
            qdone,
            ..
        } = self;
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(qtasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> =
            unsafe { &mut *(qdone as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>) };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(workbuf as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
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
            level,
            v,
            None,
        )
    }

    /// quote 的记忆化口径（表随本次调用新建，绝不跨 reset 持有）。
    pub(super) fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            workbuf,
            qtasks,
            qdone,
            quote_memo,
            ..
        } = self;
        let tasks: &mut Vec<QJob<'a>> =
            unsafe { &mut *(qtasks as *mut Vec<QJob<'static>> as *mut Vec<QJob<'a>>) };
        let done: &mut Vec<&'a Tm<'a>> =
            unsafe { &mut *(qdone as *mut Vec<&'static Tm<'static>> as *mut Vec<&'a Tm<'a>>) };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(workbuf as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let memo: &mut QuoteMemo<'a> =
            unsafe { &mut *(quote_memo as *mut QuoteMemo<'static> as *mut QuoteMemo<'a>) };
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
            level,
            v,
            Some(memo),
        )
    }

    fn unify<'a>(&mut self, bump: &'a Bump, l: u32, t: V, u: V) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ren,
            conv,
            workbuf,
            unifybuf,
            rename_pool,
            ..
        } = self;
        let stack: &mut Vec<UItem<'a>> =
            unsafe { &mut *(unifybuf as *mut Vec<UItem<'static>> as *mut Vec<UItem<'a>>) };
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(workbuf as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let pool: &mut Vec<RenameScratch<'a>> = unsafe {
            &mut *(rename_pool as *mut Vec<RenameScratch<'static>> as *mut Vec<RenameScratch<'a>>)
        };
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
            pool,
            l,
            t,
            u,
        )
    }

    /// 错误消息（参考版 `unify_catch` 的 `{:?}` Debug 口径；快版项不含
    /// 源码偏移，span 全零——判定一致，文案数字与参考版有已知偏差）。
    fn unify_catch(&mut self, bump: &Bump, lvl: u32, t: V, t_prime: V) -> Result<(), Error> {
        if self.unify(bump, lvl, t, t_prime) {
            Ok(())
        } else {
            let tq = export(self.quote(bump, lvl, t));
            let uq = export(self.quote(bump, lvl, t_prime));
            Err(Error(format!("can't unify {:?} == {:?}", tq, uq)))
        }
    }

    // 隐式插入（上游 Elaboration.hs 的 insert 族）
    // --------------------------------------------------------------------------------

    /// `insert'`：类型的隐式 Pi 前缀逐个补 fresh meta 实参。
    fn insert_go<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> (&'a Tm<'a>, V) {
        let va = self.force_v(bump, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, env, p.body)
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
        cxt: Cxt<'a>,
        t: &'a Tm<'a>,
        va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        Ok(self.insert_go(bump, cxt, t, va))
    }

    /// infer 后插入，但隐式 lambda 本身免插。
    fn insert<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
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
        cxt: Cxt<'a>,
        name: &str,
        t: &'a Tm<'a>,
        mut va: V,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let mut t = t;
        loop {
            let forced = self.force_v(bump, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, env, p.body)
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

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β / 触发 prim——分配一律落本轮 bump）。
    fn force_v(&mut self, bump: &Bump, v: V) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            ..
        } = self;
        force(
            bump,
            spine,
            &mut Vec::new(),
            vals,
            icits,
            defs,
            metas,
            decls,
            mutable_map,
            v,
        )
    }

    // 主 check / infer（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    fn check<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<&'a Tm<'a>, Error> {
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫 `(i, i_t) == (Either::Name(x_t), Impl)
                // || i == Either::Icit(i_t)`——Span 的 PartialEq 是**只比
                // data** 的自定义实现（parser_lib.rs），故命名 binder 按
                // 名字匹配（L05 同款语义）
                let matched = match larg {
                    Either::Name(n) => n.data == p.name && p.icit == Icit::Impl,
                    &Either::Icit(j) => j == p.icit,
                };
                if matched {
                    // 命中：按 λ 的 binder 名绑定（源码名，入名字表）
                    let name: &'a str = bump.alloc_str(&x.data);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, cxt2, tbody, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let mark = cxt.mark;
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, cxt2, t, body_a)?;
                    self.unwind_names(mark);
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general
                    let (t2, tty) = self.infer(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt.lvl, a, tty)?;
                    Ok(t2)
                }
            } else {
                let (t2, tty) = self.infer(bump, cxt, t)?;
                let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                self.unify_catch(bump, cxt.lvl, a, tty)?;
                Ok(t2)
            }
        } else if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl {
            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            let p = v_pi_of(a);
            let name: &'a str = bump.alloc_str(p.name);
            let body_a = {
                let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                self.eval(bump, env, p.body)
            };
            let mark = cxt.mark;
            let a_t = self.quote(bump, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, cxt2, t, body_a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t, u) = t {
            let a_tm = self.check_ty(bump, cxt, a_ty)?;
            let va = self.eval(bump, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t, va)?;
            let vt = self.eval(bump, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let mark = cxt.mark;
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, cxt2, u, a)?;
            self.unwind_names(mark);
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else {
            let (t2, tty) = self.infer(bump, cxt, t)?;
            let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
            self.unify_catch(bump, cxt.lvl, a, tty)?;
            Ok(t2)
        }
    }

    /// 类型注解的 universe 结构预检（L13 `check_universe` 轻量移植，零副作用）：
    /// `LiteralIntro` 恒非类型；`Var` 经 name_map 命中且类型已确定（非 U、非
    /// 未解 meta）→ 定向报错。洞 / 未解 meta / 其余形态放行——可解性交主检
    /// 查路径（预检不推断、不造 meta，?N 编号不受扰动）。
    fn ty_precheck<'a>(&mut self, bump: &Bump, t: &Raw) -> Result<(), Error> {
        match t {
            Raw::LiteralIntro(_) => Err(Error("expected universe, got LiteralType".to_owned())),
            Raw::Var(x) => {
                // 名字解析：name_map 优先，decl 表回退（与参考版 ty_precheck
                // 对齐——覆盖 def 体检查期间的自身占位名）
                let ty = self
                    .name_map
                    .get(x.data.as_str())
                    .map(|&(_, ty)| ty)
                    .or_else(|| self.decls.get(x.data.as_str()).map(|e| e.va));
                match ty {
                    Some(ty) => {
                        // force 已展开已解 meta；未解 flex（tag 5，或 tag 2 链
                        // 头是 Meta）放行
                        let v = self.force_v(bump, ty);
                        if v_tag(v) == 3 {
                            return Ok(());
                        }
                        let is_flex = match v_tag(v) {
                            5 => true,
                            2 => v_tag(self.spine.stack[v_spine_of(v)].f) == 5,
                            _ => false,
                        };
                        if is_flex {
                            Ok(())
                        } else {
                            Err(Error(format!("expected universe, got V({})", v.0)))
                        }
                    }
                    None => Ok(()), // 未知名：主检查报 name-not-in-scope（原路径）
                }
            }
            _ => Ok(()),
        }
    }

    /// 类型注解检查入口（Def 类型 / let 注解 / Π 域与余域）：结构预检后回落
    /// 原 `check(…, v_u())`；Π 链逐段预检——域检查后在绑定上下文里预检余域
    /// （与原 Pi 臂同构，域/余域各只检查一次，无额外 meta）。
    fn check_ty<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        t: &Raw,
    ) -> Result<&'a Tm<'a>, Error> {
        if let Raw::Pi(x, i, a, b) = t {
            self.ty_precheck(bump, a)?;
            let a_tm = self.check(bump, cxt, a, v_u())?;
            let va = self.eval(bump, cxt.env, a_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let mark = cxt.mark;
            let a_t = self.quote(bump, cxt.lvl, va);
            let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
            let res: Result<&'a Tm<'a>, Error> = {
                self.ty_precheck(bump, b)?;
                let b_tm = self.check(bump, cxt2, b, v_u())?;
                Ok(bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)))
            };
            self.unwind_names(mark);
            res
        } else {
            self.ty_precheck(bump, t)?;
            self.check(bump, cxt, t, v_u())
        }
    }

    /// 主 `infer`（表达式层；参考版 `infer_expr` 逐臂对应，L06 无 SrcPos）。
    fn infer<'a>(&mut self, bump: &'a Bump, cxt: Cxt<'a>, t: &Raw) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            Raw::Var(x) => {
                if !NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed) {
                    // O(1)：表与 types 链由 bind/define + trail 同步维护
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
                // decl 表回退（与参考版同款）：正常程序里 name_map 覆盖全部
                // 可见名（def/builtin 都 define），唯一 miss 而 decl 表命中的
                // 是递归 def 体检查期间的自身占位——引用走 `Tm::Decl`
                // （求值期查表取登记值，检查期即占位的卡住 Decl 头）
                if let Some(e) = self.decls.get(x.data.as_str()) {
                    return Ok((bump.alloc(Tm::Decl(bump.alloc_str(&x.data))), e.va));
                }
                Err(Error(format!(
                    "error name not in scope: {:?}",
                    empty_span(x.data.clone())
                )))
            }

            Raw::U => Ok((bump.alloc(Tm::U), v_u())),

            Raw::LiteralIntro(l) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&l.data))),
                v_lit_ty(),
            )),

            // 定义域挂洞；余定义域闭包住当前环境；体推断后在扩展后的
            // 上下文里 insert
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let (t, b) = self.infer(bump, cxt2, tbody)?;
                let (t, b) = self.insert(bump, cxt2, t, b)?;
                self.unwind_names(mark);
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
                let cell = bump.alloc(PiCell {
                    name,
                    icit: *i,
                    dom: a,
                    env: cxt.env,
                    body,
                });
                Ok((bump.alloc(Tm::Lam(name, *i, t)), v_pi(cell)))
            }

            Raw::Lam(_, Either::Name(_), _) => Err(Error("infer named lambda".to_owned())),

            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        let (t, tty) =
                            self.insert_until_name(bump, cxt, &name.data, t, tty)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let (t, tty) = self.infer(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, t, tty)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(format!(
                            "icit mismatch {:?} {:?}",
                            i, p.icit
                        )));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 合成 binder（PI_NAME）不进名字表：只延伸 env/telescope/
                    // pruning。注意参数序：期望 = 合成 Π（L06 参考版把合成
                    // Π 放在 unify_catch 的**首位**，与 L05 相反——忠实复刻，
                    // 只影响报错文案方向）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u());
                    let a = self.eval_fresh(bump, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt.lvl, a);
                    let cxt2 = Cxt {
                        env: env_ext(bump, cxt.env, v_lvl(cxt.lvl)),
                        types: cxt.types,
                        locals: Some(LCons::alloc(
                            bump,
                            PI_NAME,
                            a_t,
                            None,
                            cxt.locals,
                        )),
                        pruning: Some(bump.alloc(PrCons::new(Some(Icit::Expl), cxt.pruning))),
                        binds: cxt.binds + 1, // 合成 binder 也是绑定槽
                        lvl: cxt.lvl + 1,
                        mark: cxt.mark,
                    };
                    let cod_meta = self.fresh_meta(bump, cxt2, v_u());
                    let cell = bump.alloc(PiCell {
                        name: PI_NAME,
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt.lvl, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u = self.check(bump, cxt, u, a)?;
                let arg = self.eval(bump, cxt.env, u);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg);
                    self.eval(bump, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u, i)), ty))
            }

            Raw::Pi(x, i, a, b) => {
                let a_tm = self.check_ty(bump, cxt, a)?;
                let va = self.eval(bump, cxt.env, a_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let a_t = self.quote(bump, cxt.lvl, va);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, va);
                let b_tm = self.check_ty(bump, cxt2, b)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Pi(name, *i, a_tm, b_tm)), v_u()))
            }

            Raw::Let(x, a_ty, t, u) => {
                let a_tm = self.check_ty(bump, cxt, a_ty)?;
                let va = self.eval(bump, cxt.env, a_tm);
                let t_tm = self.check(bump, cxt, t, va)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                let name: &'a str = bump.alloc_str(&x.data);
                let mark = cxt.mark;
                let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
                let (u_tm, uty) = self.infer(bump, cxt2, u)?;
                self.unwind_names(mark);
                Ok((bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)), uty))
            }

            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u());
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }
        }
    }

    /// decl 层的 `infer`（参考版 `Infer::infer(Decl)`）：Def 把参数折叠成
    /// Pi/Lam 后检查，登记 decl 表并 define；Println 推断体（返回引读用）。
    pub(super) fn infer_decl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: Cxt<'a>,
        d: &Decl,
    ) -> Result<(DeclOut<'a>, Cxt<'a>), Error> {
        match d {
            Decl::Def {
                name,
                params,
                ret_type,
                body,
            } => {
                // 参数折叠：typ = Π 参数. 返回类型；bod = λ 参数. 体
                // （与参考版同款在 Raw 层做，一次成本）。Cow 免深拷
                // （L13 Def 臂同款已验证形态）：零参数 def（strchain/global
                // 负载的全部 def）typ/bod 直接借用原树，连 ret_type/body 的
                // 深拷都省掉；有参时首折才克隆基底，余层仅移动。
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
                let typ_tm = self.check_ty(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, cxt.env, typ_tm);
                // 重定义检查 + 占位登记合并为一次 entry（原三连写
                // contains_key + insert×2 各散列/克隆一次 key，现仅一次）：
                // builtin / 先前 def 已登记 → 定向报错（redefine，与参考版
                // 同款）；否则登记指向自身的中性占位，体检查期间 Var 经 decl
                // 表回退命中，检查完成后用真实值原地覆写（下方 get_mut）。
                // 检查失败时 run 整体 Err 退出，占位不会外泄。
                match self.decls.entry(SmolStr::from(&name.data)) {
                    std::collections::hash_map::Entry::Occupied(_) => {
                        return Err(Error(format!("redefine {}", name.data)));
                    }
                    std::collections::hash_map::Entry::Vacant(v) => {
                        let self_name: &'a str = bump.alloc_str(&name.data);
                        v.insert(DeclEntryF {
                            vt: v_xcell(bump.alloc(XCell::Decl(self_name))),
                            va: vtyp,
                            prim: None,
                        });
                    }
                }
                let t_tm = self.check(bump, cxt, &bod, vtyp)?;
                let vt = self.eval(bump, cxt.env, t_tm);
                // decl 表终值原地覆写（运行期按名取值：string_to_global_type
                // 等）：占位刚插入且无中途删除路径，get_mut 必命中，免二次
                // key 克隆
                if let Some(slot) = self.decls.get_mut(name.data.as_str()) {
                    slot.vt = vt;
                }
                let cxt2 = self.define_name(bump, cxt, &name.data, typ_tm, t_tm, vt, vtyp);
                Ok((
                    DeclOut::Def {
                        name: bump.alloc_str(&name.data),
                        vt,
                    },
                    cxt2,
                ))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), cxt))
            }
        }
    }
}

/// decl 层推断的产出：Def 带名与值（bench 的 nf 口径用），Println 带
/// elaborated 体（run 的 nf 输出用）。
pub(super) enum DeclOut<'a> {
    Def { name: &'a str, vt: V },
    Println(&'a Tm<'a>),
}

/// locals 链形态判定（见 L05 同名函数）：头 bind 段长 k + 其后全 define
/// → Some(k)；交错 → None。
fn bind_prefix_of_telescope(ls: Option<&LCons<'_>>) -> Option<u32> {
    // O(1) 读构造期缓存（语义同旧全链走查；缓存规则见 LCons::alloc）。
    ls.and_then(|n| n.prefix)
}

/// 项里是否含自由 `Var`（按 binder 深度算）。`fresh_meta` 快捷路径 2 的
/// 判据（保守：自由 ⇒ 走全构造）。L06 新叶（字面量/类型/名字）无变量。
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
            Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Decl(_) => {}
            Tm::Pi(_, _, a, b) => {
                stack.push((a, d));
                stack.push((b, d + 1));
            }
            Tm::Let(_, a, t, u) => {
                stack.push((a, d));
                stack.push((t, d));
                stack.push((u, d + 1));
            }
        }
    }
    false
}

/// Elaboration 上下文（全 Copy，绑定量在 bump 里）。L06 无位置跟踪
/// （错误不带 span 位置，`Error(String)`）。
#[derive(Clone, Copy)]
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
        }
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

impl Machine {
    /// `(String ->)^n ret` —— L06 builtin 的参数类型全为 String。
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

    /// 每轮注册（参考版 `Cxt::new(&mut infer)`）：String 类型进 decl 表并
    /// define；全组 builtin 登记（值 = 卡住 Decl 头，应用时触发 prim）+
    /// 位置 define（源码可用名）。**注册顺序与参考版一致**——
    /// create_global 等的类型引用 `string_to_global_type`，须先登记。
    pub(super) fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let mut cxt = Cxt::empty();
        // String
        self.decls.insert(
            SmolStr::new("String"),
            DeclEntryF {
                vt: v_lit_ty(),
                va: v_u(),
                prim: None,
            },
        );
        let u_tm: &'a Tm<'a> = bump.alloc(Tm::U);
        let lit_ty_tm: &'a Tm<'a> = bump.alloc(Tm::LiteralType);
        cxt = self.define_name(
            bump,
            cxt,
            "String",
            u_tm,
            lit_ty_tm,
            v_lit_ty(),
            v_u(),
        );
        // builtin 组（名, 类型项, prim）——与参考版 Cxt::new 同序
        let lit_ty = bump.alloc(Tm::LiteralType);
        let u_t = bump.alloc(Tm::U);
        let builtins: Vec<(&str, &'a Tm<'a>, Prim)> = vec![
            ("string_concat", Self::str_pi(bump, &["x", "y"], lit_ty), Prim::StrConcat),
            ("str_eq", Self::str_pi(bump, &["x", "y"], lit_ty), Prim::StrEq),
            ("str_indent2", Self::str_pi(bump, &["x"], lit_ty), Prim::StrIndent2),
            (
                "report_check_issue",
                Self::str_pi(bump, &["code", "module", "signal", "message"], u_t),
                Prim::ReportCheckIssue,
            ),
            (
                "string_to_global_type",
                Self::str_pi(bump, &["x"], u_t),
                Prim::StringToGlobalType,
            ),
            (
                "create_global",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(bump, "y", Self::st2g_app(bump, 0), u_t),
                ),
                Prim::CreateGlobal,
            ),
            (
                "change_mutable",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(
                        bump,
                        "f",
                        Self::tm_pi(bump, "_", Self::st2g_app(bump, 0), Self::st2g_app(bump, 1)),
                        u_t,
                    ),
                ),
                Prim::ChangeMutable,
            ),
            (
                "get_global",
                Self::tm_pi(bump, "x", lit_ty, Self::st2g_app(bump, 0)),
                Prim::GetGlobal,
            ),
            (
                "get_global_default",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(bump, "z", Self::st2g_app(bump, 0), Self::st2g_app(bump, 1)),
                ),
                Prim::GetGlobalDefault,
            ),
            (
                "change_mutable_default",
                Self::tm_pi(
                    bump,
                    "x",
                    lit_ty,
                    Self::tm_pi(
                        bump,
                        "f",
                        Self::tm_pi(bump, "_", Self::st2g_app(bump, 0), Self::st2g_app(bump, 1)),
                        Self::tm_pi(bump, "z", Self::st2g_app(bump, 1), u_t),
                    ),
                ),
                Prim::ChangeMutableDefault,
            ),
            (
                "file_read_all_text",
                Self::str_pi(bump, &["path"], lit_ty),
                Prim::FileReadAllText,
            ),
            (
                "file_write_all_text",
                Self::str_pi(bump, &["path", "content"], u_t),
                Prim::FileWriteAllText,
            ),
            (
                "file_append_all_text",
                Self::str_pi(bump, &["path", "content"], u_t),
                Prim::FileAppendAllText,
            ),
            (
                "file_exists",
                Self::str_pi(bump, &["path"], lit_ty),
                Prim::FileExists,
            ),
            (
                "file_delete",
                Self::str_pi(bump, &["path"], u_t),
                Prim::FileDelete,
            ),
        ];
        for (name, ty, prim) in builtins {
            let va = self.eval(bump, EMPTY_ENV, ty);
            let head = v_xcell(bump.alloc(XCell::Decl(bump.alloc_str(name))));
            self.decls.insert(
                SmolStr::new(name),
                DeclEntryF {
                    vt: head,
                    va,
                    prim: Some(prim),
                },
            );
            let name_tm: &'a Tm<'a> = bump.alloc(Tm::Decl(bump.alloc_str(name)));
            cxt = self.define_name(bump, cxt, name, ty, name_tm, head, va);
        }
        cxt
    }

    /// 参考版 `run` 的主循环（无输出变体，bench 用）：返回 (是否通过，
    /// 最后一个 def 的名与值)。
    pub(super) fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Option<(&'a str, V)>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            match self.infer_decl(bump, cxt, d) {
                Ok((out, nc)) => {
                    if let DeclOut::Def { name, vt } = out {
                        last = Some((name, vt));
                    }
                    cxt = nc;
                }
                Err(e) => return (Err(e), last),
            }
        }
        (Ok(()), last)
    }
}
