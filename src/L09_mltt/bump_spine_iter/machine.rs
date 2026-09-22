//! machine：稳态复用机（`Machine`/`Names`）与 elaboration（check/infer/
//! check_universe）、Elaboration 上下文（`Cxt`/`TCons`/`DeclOut`）、builtin
//! 注册（每轮 prime + string_concat 源项）。原 bump_spine_iter.rs 的
//! "Machine（稳态复用）与 elaboration"、"Elaboration 上下文"、"builtin 注册"
//! 三节，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::rc::Rc;

use super::parser::syntax::{Decl, Either, Icit, Raw};
use super::pretty::pretty_tm;
use super::{Error, PatternDetail, empty_span};

use super::compiler::Compiler;
use super::debug::debug_val;
use super::entry::export;
use super::env::{CloCell, EMPTY_ENV, Env, EnvCons, PiCell, env_ext, env_ext_defs, env_len, env_nth};
use super::eval::{W, eval_iter};
use super::force::{force, refuel, val_mentions_lvl};
use super::quote::{QJob, QuoteMemo, quote_iter};
use super::rename::{RenBuf, invert_bump, lams_from_ty, prune_ty_bump, rename_iter};
use super::spine::{MetaEntry, Spine, is_flex};
use super::subst::{SpecSolve, SubstV, vsub_reclaim, wrap_sub};
use super::syntax::{GLOBAL_BASE, LCons, PrCons, SumDataT, SumParamT, Tm, V, XCell, v_clo, v_lit_ty, v_lvl, v_lvl_of, v_meta, v_pi, v_pi_of, v_tag, v_u, v_u_of, v_xcell_of};
use super::unify::{CACHE_SHRINK_MIN_ENTRIES, SPINE_SHRINK_MIN_ENTRIES, ConvScratch, ReclaimOnClear, UItem, unify_iter};

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 名字表快照（参考版 BiMap 的 map1/map2 同构；**随 Cxt 克隆**——
/// bind/define/fake_bind 克隆插入，与参考版 `src_names.clone()` 的
/// 逐上下文隔离语义逐字对应，无需撤销轨迹）。
///
/// 只装**当前 def 的局部条目**（binder + fake 占位；顶层 define 已迁
/// [`Machine::global_names`]，perf-debt P2）——表大小 = 当前 def 的
/// binder 数（个位数），每 binder 克隆 O(1)。
#[derive(Clone, Default)]
struct Names {
    /// 名字 → 层级（map1：只收源码 binder 与 fake_bind；inserted binder
    /// 与参考版 `new_binder` 一样不入）。
    by_name: FxHashMap<SmolStr, u32>,
    /// 层级 → 类型值（map2：按层级持久，refresh 的 get_by_key2_mut 目标；
    /// 名字查类型经此中转，refresh 更新即生效）。
    by_lvl: FxHashMap<u32, V>,
}

/// 稳态复用机（L06/L08 版 + L09 增量：global 表）。L09 没有 decl 表 /
/// 可变全局 / 燃料池 / pm 事实表——全局 def 走 [`Machine::globals`]（下标
/// = global_idx，项层以 `GLOBAL_BASE` 偏移的大下标引用）；名字状态在
/// [`Cxt`] 的 `names` 快照里（参考版 BiMap 同构）。
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
    /// 全局 def/enum 值表（下标 = global_idx）。递归 def 的占位（自身大
    /// 层级的 Rigid）先压入、检查后覆盖。每轮清空（参考版每次调用新建
    /// Infer 的 global 表）。
    globals: Vec<V>,
    /// 全局名字表（顶层 define 的 名字 → (层级, 类型)）：Machine 独有的
    /// append-only 表，**不随 Cxt 克隆**。与 L11+ 的 decls 表同角色——
    /// 旧设计把顶层 define 累积进 Cxt 的 names 快照（每 def 各 +1 条，
    /// 表大小 O(D)），`bind_name` 每 binder 克隆整表即 O(D²)（perf-debt
    /// P2）。查找顺序：Cxt 的局部 names（当前 def 的 binder + fake 占位，
    /// 覆盖全局）之后回落本表。每轮清空（同 globals）。
    global_names: FxHashMap<SmolStr, (u32, V)>,
    /// globals 的中性视图缓存：neutral[i] == v_lvl(i + GLOBAL_BASE)，
    /// 随 globals 同步 push。quote/eval/unify 包装器每次调用都要这串值
    /// （卡住 match 分支重求值的 avoid_recursive 视图）——旧实现每次
    /// neutral_of(&self.globals) 整拷 O(D)（perf-debt P2 残余平方项），
    /// 现按字段借用 O(1)。每轮清空（同 globals）。
    neutral: Vec<V>,
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
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项。
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
            globals: Vec::new(),
            global_names: FxHashMap::default(),
            neutral: Vec::new(),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/类型表/轨迹 + 环境区域 + global 表
    /// 全部清空。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮 bump 值 /
    /// metas / defs / globals 持有，轮边界后无任何旧句柄可达；容量到过
    /// `SPINE_SHRINK_MIN_ENTRIES` 时清空顺带归还缓冲（否则峰值容量随常驻
    /// Machine 到进程结束）。
    pub(super) fn clear_round(&mut self) {
        self.metas.clear();
        self.defs.clear();
        self.globals.clear();
        self.global_names.clear();
        self.neutral.clear();
        let _ = self.spine.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        // 与三处 bump.reset()（run_decls / bench_check / bench_nf_impl）
        // 严格伴生：归还 arena 内 σ 克隆的强引用（Rc 节点在全局堆上，reset
        // 不动其数据；见 VSUB_REGS 的 SAFETY 注释）
        vsub_reclaim();
    }

    // Extend Cxt（源码 binder / inserted binder / define / fake_bind）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    pub(super) fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, ty);
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            names: Rc::new(names),
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
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            names: cxt.names.clone(),
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
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
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
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, ty);
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            names: Rc::new(names),
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
        }
    }

    /// fake_bind（参考版 `Cxt::fake_bind`）：递归 def 的占位——名字指到
    /// 全局层级（`GLOBAL_BASE + global_idx`），env/lvl/locals/pruning 一概
    /// 不动。
    ///
    /// **就地 COW（2026-09-12）**：`Rc::make_mut` 在 cxt 独占名字快照
    /// （强计数 1，顺序 decl 路径恒成立）时原地插入，替代旧的整表深克隆
    /// ——大 decl 数负载（universe/macro 等 2^(k+1) 个 def）上每 def
    /// O(D) 克隆实测 O(D²)；有别的快照观察者（match 臂捕获、refresh 克隆
    /// 等）时自动回退深拷贝，隔离语义与旧实现逐字一致。随后 define 用真
    /// 名覆盖同名 by_name 条目；占位残留的 `by_lvl[GLOBAL_BASE+idx]` 键
    /// 无查找路径可达（by_lvl 只点查，按名解析已指向真实层级）。调用方
    /// 需在使用完返回的 fake 视图后 `drop(fake)` 再就地 define（否则多出
    /// 的 Rc 引用会触发 make_mut 克隆回退）。
    fn fake_bind<'a>(&mut self, cxt: &mut Cxt<'a>, x: &str, ty: V, global_idx: u32) -> Cxt<'a> {
        let names = Rc::make_mut(&mut cxt.names);
        names.by_name.insert(SmolStr::new(x), global_idx + GLOBAL_BASE);
        names.by_lvl.insert(global_idx + GLOBAL_BASE, ty);
        clone_cxt(cxt)
    }

    /// [`Self::define_name`] 的就地版（调用方独占 cxt 的 decl 臂 /
    /// prime_round 顺序路径专用）：真名进 **Machine 的全局名字表**
    /// （append-only，不随 Cxt 克隆——P2：旧实现插进 Cxt 的 names 快照，
    /// 表随 def 数累积，`bind_name` 每 binder 克隆即 O(D²)），并撤除
    /// fake_bind 留在局部 names 里的同名占位（by_name 旧键即其 by_lvl
    /// 键；prime_round 的 builtin 注册无占位，remove 为 no-op）。调用点
    /// 审计：返回后父视图立即被丢弃/覆盖（infer_decl Def/Enum 臂、
    /// prime_round），无"父视图仍被读取"的形态；check 路径的 Let/Pi
    /// （父视图存活、体局部作用域）继续走克隆版 [`Self::define_name`]。
    fn define_name_in<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
        x: &str,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        self.global_names
            .insert(SmolStr::new(x), (cxt.lvl, ty));
        let names = Rc::make_mut(&mut cxt.names);
        if let Some(old_lvl) = names.by_name.remove(x) {
            names.by_lvl.remove(&old_lvl);
        }
        cxt.env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        cxt.types = Some(bump.alloc(TCons {
            name: bump.alloc_str(x),
            ty,
            source: true,
            next: cxt.types,
        }));
        cxt.locals = Some(bump.alloc(LCons {
            name: bump.alloc_str(x),
            a_t,
            t_t: Some(t_t),
            next: cxt.locals,
        }));
        cxt.pruning = Some(bump.alloc(PrCons::new(None, cxt.pruning)));
        cxt.lvl += 1;
        clone_cxt(cxt)
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。
    ///
    /// **L05-L08 的 bind-prefix 快路径（`bind_prefix_of_telescope` + define
    /// 槽由 `cxt.env` 快照供给）在本层刻意不移植**：那条路径要求"telescope
    /// 里 define 槽的项 ≡ env 快照里的值"。L05-L08 的模式特化走 pm_defs
    /// （只追加等式，快照恒成立）；本层起改走参考版 `Cxt::update_cxt`——
    /// 精化就地改写 env 槽再 refresh 重锚定，而 `locals` 照参考版保持陈旧
    /// （参考版 cxt.rs 里 `locals: self.locals.clone()` 的 TODO），全 close
    /// 正是靠这份陈旧项与参考版逐值同轨。改读快照会拿到精化后的值：孪生的
    /// 契约是与参考版 Ok 输出逐字节一致，不是比参考版更正确。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
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

    // 内核包装（Machine 字段借出）
    // --------------------------------------------------------------------------------

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn eval<'a>(&mut self, bump: &'a Bump, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
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
            bump, spine, work, vals, icits, defs, metas, globals, env, tm,
        )
    }

    /// 中性 global 视图下的 eval（卡住 match 分支体的重求值——参考版
    /// avoid_recursive 克隆：全局值全部换成指向自身大层级的 Rigid）。
    #[allow(clippy::unnecessary_cast)]
    fn eval_neutral<'a>(&mut self, bump: &'a Bump, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            neutral,
            eval_work,
            ..
        } = self;
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        work.clear();
        eval_iter(
            bump, spine, work, vals, icits, defs, metas, neutral, env, tm,
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn quote<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
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
            globals,
            &neutral,
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
    pub(super) fn quote_memo<'a>(&mut self, bump: &'a Bump, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
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
            globals,
            neutral,
            level,
            v,
            Some(&mut *memo),
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    fn unify<'a>(&mut self, bump: &'a Bump, l: u32, t: V, u: V) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            ren,
            conv,
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
            bump, spine, work, stack, vals, icits, defs, metas, globals, neutral, ren, conv, None,
            l, t, u,
        )
    }

    /// 特化合一入口（参考版 `unify(…, Some(&mut SpecSolve))` 穿参）：模式
    /// 方程与覆盖探测用——bare rigid 可解，解入 `spec.acc`。
    fn unify_spec(
        &mut self,
        bump: &Bump,
        l: u32,
        t: V,
        u: V,
        spec: &mut SpecSolve<'_>,
    ) -> bool {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            ren,
            conv,
            unify_work,
            unify_stack,
            ..
        } = self;
        // SAFETY：同 unify。
        #[allow(clippy::unnecessary_cast)]
        let work: &mut Vec<W<'_>> =
            unsafe { &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'_>>) };
        #[allow(clippy::unnecessary_cast)]
        let stack: &mut Vec<UItem<'_>> =
            unsafe { &mut *(unify_stack as *mut Vec<UItem<'static>> as *mut Vec<UItem<'_>>) };
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
            globals,
            neutral,
            ren,
            conv,
            Some(spec),
            l,
            t,
            u,
        )
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表；快版导出项
    /// 的 Span 全零，消息内容与参考版同构）。
    fn unify_catch(&mut self, bump: &Bump, cxt: &Cxt<'_>, t: V, t_prime: V) -> Result<(), Error> {
        // 常规转换（spec = None）；一次合一入口充值精化燃料池
        refuel();
        if self.unify(bump, cxt.lvl, t, t_prime) {
            Ok(())
} else {
            let tq = export(self.quote(bump, cxt.lvl, t));
            let uq = export(self.quote(bump, cxt.lvl, t_prime));
            let names = types_names_list(cxt.types);
            Err(Error(empty_span(format!(
                "can't unify\n      find: {}\n  expected: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            ))))
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β——分配一律落本轮 bump）。
    pub(super) fn force_v(&mut self, bump: &Bump, v: V) -> V {
        let Machine {
            spine,
            defs,
            metas,
            globals,
            ..
        } = self;
        force(bump, spine, defs, metas, globals, v)
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
                return Err(Error(empty_span(format!("no named implicit arg {}", name))));
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
        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, a);
        if let Raw::Lam(x, larg, tbody) = t {
            if v_tag(a) == 4 {
                let p = v_pi_of(a);
                // 参考版首臂的守卫：命名隐式对准同名隐式 Π；显式对显式
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
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, p.dom);
                    let body = self.check(bump, &cxt2, tbody, body_a)?;
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, &cxt2, t, body_a)?;
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
                self.eval(bump, env, p.body)
            };
            let a_t = self.quote(bump, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, &cxt2, t, body_a)?;
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t2, u2) = t {
            let (a_tm, _) = self.check_universe(bump, cxt, a_ty)?;
            let va = self.eval(bump, cxt.env, a_tm);
            let t_tm = self.check(bump, cxt, t2, va)?;
            let vt = self.eval(bump, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            let cxt2 = self.define_name(bump, cxt, &x.data, a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, &cxt2, u2, a)?;
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else if let Raw::Match(expr, clauses) = t {
            // match：编译（特化合一在编译期完成）+ 逐分支检查
            let expr_span = expr.to_span();
            let (tm, typ) = self.infer_expr(bump, cxt, expr)?;
            let target = self.eval(bump, cxt.env, tm);
            let mut compiler = Compiler::new(a);
            compiler.compile(self, bump, typ, clauses, cxt, target)?;
            if !compiler.warnings.is_empty() {
                return Err(Error(expr_span.map(|_| format!("{:?}", compiler.warnings))));
            }
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

    // 类型注解的 universe 检查（参考版 elaboration.rs `check_universe` 完整
    // 移植：可解 meta——两分支都把 meta 解成 `U(0)` 形态并返回层级 0）
    // --------------------------------------------------------------------------------

    fn check_universe<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, u32), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        // U：层级直出（参考版 match 的 U 臂，不 force）
        if v_tag(inferred_type) == 3 {
            return Ok((t_inferred, v_u_of(inferred_type)));
        }
        // Flex：反演 spine，可解则把 meta 解成 `U(0)` 形态（参考版不 force
        // 直接 match——已解 flex 会触发参考版的 unreachable!，快版同款）
        let mut args: Vec<(V, Icit)> = Vec::new();
        if let Some(m) = self.spine.flex_of(inferred_type, &mut args) {
            let mty = match &self.metas[m as usize] {
                MetaEntry::Unsolved(a) => *a,
                _ => unreachable!(),
            };
            let inv = {
                let Machine {
                    spine,
                    defs,
                    metas,
                    globals,
                    ren,
                    ..
                } = self;
                invert_bump(bump, spine, defs, metas, globals, ren, &args)
            };
            let Some(mask) = inv else {
                return Err(Error(t_span.map(|_| "invert failed".to_owned())));
            };
            // 非线性：剪枝可行性检查（结果弃置——参考版只用作把关）
            if !mask.is_empty() {
                let ok = {
                    let Machine {
                        spine,
                        vals,
                        icits,
                        defs,
                        metas,
                        globals,
                        eval_work,
                        ..
                    } = self;
                    let work: &mut Vec<W<'a>> = unsafe {
                        &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                    };
                    work.clear();
                    prune_ty_bump(
                        bump, spine, work, vals, icits, defs, metas, globals, &mask, mty,
                    )
                };
                if ok.is_none() {
                    return Err(Error(t_span.map(|_| "prune failed".to_owned())));
                }
            }
            if args.is_empty() {
                // pren.dom == 0：meta 类型 force 后是 U 即解 `U(0)`
                let f = self.force_v(bump, mty);
                if v_tag(f) == 3 {
                    self.metas[m as usize] = MetaEntry::Solved(v_u(0), mty);
                    return Ok((t_inferred, 0));
                }
                let f2 = self.force_v(bump, mty);
                let msg = format!("meta type {} is not a universe", debug_val(&self.spine, &self.defs, f2));
                return Err(Error(t_span.map(|_| msg.clone())));
            }
            // rename 出 `U(0)` 的解（occ = m），λ 包裹后空环境求值写表
            let rhs = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas,
                    globals,
                    ren,
                    unify_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                rename_iter(
                    bump, spine, work, vals, icits, defs, ren, metas, globals, Some(m),
                    args.len() as u32, cxt.lvl, v_u(0),
                )
            };
            let Some(rhs) = rhs else {
                return Err(Error(
                    t_span.map(|_| "when check universe, try to rename failed".to_string()),
                ));
            };
            let lam_tm = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas,
                    globals,
                    eval_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                lams_from_ty(bump, spine, work, vals, icits, defs, metas, globals, args.len() as u32, mty, rhs)
            };
            let solution = self.eval(bump, EMPTY_ENV, lam_tm);
            self.metas[m as usize] = MetaEntry::Solved(solution, mty);
            return Ok((t_inferred, 0));
        }
        Err(Error(t_span.map(|_| {
            format!(
                "expected universe, got {}",
                debug_val(&self.spine, &self.defs, inferred_type)
            )
        })))
    }
}
// Elaboration 上下文
// --------------------------------------------------------------------------------

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
pub(super) struct TCons<'a> {
    name: &'a str,
    ty: V,
    source: bool,
    next: Option<&'a TCons<'a>>,
}

/// Elaboration 上下文（绑定量在 bump 里）。方法一律借用 `&Cxt`（扩展上下
/// 文返回**新的** Cxt 值；名字/类型的可变状态在 [`Machine`] 的
/// name_map/lvl_types，随 `mark` 轨迹撤销）。
pub(super) struct Cxt<'a> {
    pub(super) env: Env<'a>,
    /// 名字快照（参考版 `src_names: BiMap` 同构；随扩展克隆——隔离语义
    /// 与参考版逐字对应）。
    names: Rc<Names>,
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
}

impl<'a> Cxt<'a> {
    fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            names: Rc::new(Names::default()),
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
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
            Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Prim => {}
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

impl Machine {
    // check_pm / unify_pm / update_cxt / refresh（参考版 elaboration.rs +
    // cxt.rs 的模式特化机制——精化等式直接改写进环境）
    // --------------------------------------------------------------------------------

    /// `unify_pm`：模式特化的合一（参考版 elaboration.rs 同款臂序）：双裸
    /// Rigid 同级自反；单侧裸 Rigid → 解累积进 σ（旧 `update_cxt` 的显式
    /// 替换形态）；同名 SumCase 逐 datas、同名 Sum 逐参数（均**只比值槽**）
    /// 递归；其余落 `unify_spec`（带 spec 的常规合一——途中的 bare rigid
    /// 继续累积进 σ）。失败语义不变。
    pub(super) fn unify_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
        t_span: &crate::parser_lib::Span<()>,
        spec: &mut SpecSolve<'_>,
    ) -> Result<(), Error> {
        let mut f1 = self.force_v(bump, t);
        let mut f2 = self.force_v(bump, t_prime);
        // 方程两侧置于当前 acc 之下（dpm-nbe `subst ɑ vs` 的惰性等价物）
        if !spec.acc.is_empty() {
            let acc = spec.acc.clone();
            f1 = self.force_v(bump, wrap_sub(bump, &acc, f1));
            f2 = self.force_v(bump, wrap_sub(bump, &acc, f2));
        }
        // (Rigid(x1, []), Rigid(x2, [])) if x1 == x2 → 自反
        if v_tag(f1) == 0 && v_tag(f2) == 0 && v_lvl_of(f1) == v_lvl_of(f2) {
            return Ok(());
        }
        // (Rigid(x, []), v) → 精化 x := v
        if v_tag(f1) == 0 {
            return self.spec_refine(cxt, v_lvl_of(f1), f2, t_span, spec);
        }
        // (v, Rigid(x, [])) → 精化 x := v
        if v_tag(f2) == 0 {
            return self.spec_refine(cxt, v_lvl_of(f2), f1, t_span, spec);
        }
        // 同名 SumCase：先比 typ 的 Sum 头名字（L07/L10 同款，2026-09-18
        // 评审修复 4：跨 enum 重名构造子是两个不同值，同 case_name 不足
        // 以判定身份；**不比 typ 的值**——索引槽互相引用深递归），再逐
        // datas（值槽）
        if v_tag(f1) == 7 && v_tag(f2) == 7 {
            if let (
                XCell::SumCase {
                    typ: t1,
                    case_name: n1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: t2,
                    case_name: n2,
                    datas: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    let t1f = self.force_v(bump, *t1);
                    let t2f = self.force_v(bump, *t2);
                    if v_tag(t1f) == 7 && v_tag(t2f) == 7 {
                        if let (
                            XCell::Sum { name: na, .. },
                            XCell::Sum { name: nb, .. },
                        ) = (v_xcell_of(t1f), v_xcell_of(t2f))
                        {
                            if na != nb {
                                return Err(Error(t_span.map(|_| "".to_string())));
                            }
                        }
                    }
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(bump, cxt, x.val, y.val, t_span, spec)?;
                    }
                    return Ok(());
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
            // 同名 Sum：逐参数（值槽）
            if let (
                XCell::Sum {
                    name: n1,
                    params: d1,
                    ..
                },
                XCell::Sum {
                    name: n2,
                    params: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(bump, cxt, x.val, y.val, t_span, spec)?;
                    }
                    return Ok(());
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
        }
        // 其余落常规合一（spec 穿参）
        if self.unify_spec(bump, cxt.lvl, f1, f2, spec) {
            Ok(())
        } else {
            let tq = export(self.quote(bump, cxt.lvl, f1));
            let uq = export(self.quote(bump, cxt.lvl, f2));
            let names = types_names_list(cxt.types);
            let msg = format!(
                "can't unify\n      find: {}\n  expected: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            );
            Err(Error(t_span.map(|_| msg.clone())))
        }
    }

    /// 一条特化解 `x := v` 累积进 σ（旧 `Cxt::update_cxt` 的单步）。守卫：
    /// Flex 不精化（旧直通）；越界 / 全局层级无操作；浅 occurs 失败 = Err。
    fn spec_refine(
        &self,
        cxt: &Cxt<'_>,
        x: u32,
        v: V,
        t_span: &crate::parser_lib::Span<()>,
        spec: &mut SpecSolve<'_>,
    ) -> Result<(), Error> {
        if is_flex(&self.spine, v) {
            return Ok(());
        }
        if x >= cxt.lvl {
            return Ok(());
        }
        if val_mentions_lvl(&self.spine, &self.defs, v, x) {
            return Err(Error(t_span.map(|_| "".to_string())));
        }
        spec.acc = SubstV::extend(&spec.acc, x, v);
        Ok(())
    }

    /// 「纯探测」统一执行器：进入前快照 `metas`，跑完闭包后**无条件**换回
    /// （无论闭包返回 Ok/Err），把探测期分配的 fresh meta 与对已有 meta 的求解
    /// 一律回滚，杜绝污染外泄到真实机。可达性探测等投机性 check 都走此入口。
    /// 必须**整表 clone**，不能只按 meta 上界截断——探测期 unify 可能解掉已有
    /// meta，而这些解又引用闭包内新建 meta，截断会让解悬空（后续查找越界 panic）。
    pub(super) fn run_pure_probe<R>(&mut self, f: impl FnOnce(&mut Machine) -> R) -> R {
        let metas = self.metas.clone();
        let r = f(self);
        self.metas = metas;
        r
    }

    /// `check_pm`：infer + insert + `unify_pm`；返回累积的精化替换 σ（调用方
    /// 做 `subst_cxt`），不再返回改写过的 Cxt。
    fn check_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<(&'a Tm<'a>, Rc<SubstV>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        refuel();
        let solvable = self.bind_slots(cxt);
        let mut spec = SpecSolve {
            solvable: &solvable,
            acc: Rc::new(SubstV::default()),
        };
        self.unify_pm(bump, cxt, a, inferred_type, &t_span, &mut spec)?;
        Ok((t_inferred, spec.acc))
    }

    /// `check_pm_final`：第二条方程把原始值与模式的值再对一次（失败容忍）。
    pub(super) fn check_pm_final<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
        ori: V,
    ) -> Result<(&'a Tm<'a>, Rc<SubstV>), Error> {
        let t_span = t.to_span();
        let x = self.infer_expr(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, cxt, x.0, x.1)?;
        refuel();
        let solvable = self.bind_slots(cxt);
        let mut acc = Rc::new(SubstV::default());
        {
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc,
            };
            self.unify_pm(bump, cxt, a, inferred_type, &t_span, &mut spec)?;
            acc = spec.acc;
        }
        // 在**未改写**的原 env 下求值 t_inferred（旧实现是在已改写 env 下
        // 求值——显式替换的等价口径）；失败容忍。
        let ori_v = self.eval(bump, cxt.env, t_inferred);
        {
            let mut spec = SpecSolve {
                solvable: &solvable,
                acc,
            };
            let _ = self.unify_pm(bump, cxt, ori, ori_v, &t_span, &mut spec);
            acc = spec.acc;
        }
        Ok((t_inferred, acc))
    }

    /// 把精化替换 σ 施加到上下文（参考版 `Cxt::subst_cxt` / dpm-nbe
    /// `subst sub ctx`）：env 槽、types 链、names.by_lvl（name_map 影子索引：
    /// by_name 不动，按层级持久）的类型值包 VSub；lvl / locals / pruning /
    /// binds 不动——**槽位布局不变**，读点经 force 展开。σ 为空零开销直通。
    pub(super) fn subst_cxt<'a>(&mut self, bump: &'a Bump, sub: &Rc<SubstV>, cxt: &Cxt<'a>) -> Cxt<'a> {
        if sub.is_empty() {
            return clone_cxt(cxt);
        }
        // env：全部槽包裹（包裹值不进 defs 平坦区，整体退化为 binder 链）
        let env = {
            let defs = &self.defs;
            let n = env_len(cxt.env);
            let mut e: Option<&'a EnvCons<'a>> = None;
            for i in (0..n).rev() {
                let v = env_nth(defs, cxt.env, i);
                e = Some(bump.alloc(EnvCons {
                    val: wrap_sub(bump, sub, v),
                    next: e,
                }));
            }
            Env {
                flat_base: 0,
                flat_len: 0,
                binds: e,
            }
        };
        // types 链：逐节点包裹类型值（头 = 最内层，序不变）
        let types = {
            let mut nodes: Vec<(&'a str, V, bool)> = Vec::new();
            let mut cur = cxt.types;
            while let Some(tc) = cur {
                nodes.push((tc.name, tc.ty, tc.source));
                cur = tc.next;
            }
            let mut types: Option<&'a TCons<'a>> = None;
            for (name, ty, source) in nodes.into_iter().rev() {
                types = Some(bump.alloc(TCons {
                    name,
                    ty: wrap_sub(bump, sub, ty),
                    source,
                    next: types,
                }));
            }
            types
        };
        // names：by_name 影子索引保持（层级键不变），by_lvl 类型值同步包裹
        let names = {
            let mut names = (*cxt.names).clone();
            let keys: Vec<u32> = names.by_lvl.keys().copied().collect();
            for k in keys {
                let ty = names.by_lvl[&k];
                names.by_lvl.insert(k, wrap_sub(bump, sub, ty));
            }
            Rc::new(names)
        };
        Cxt {
            env,
            names,
            types,
            locals: cxt.locals,
            pruning: cxt.pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
        }
    }

    /// 当前上下文里"真变量"（bind 槽，env 槽仍指向自身 vvar）的层级集合：
    /// 模式特化方程可解的对象。嵌套 match 的入口上下文可能已被外层精化
    /// 包裹（subst_cxt）——解包 VSub 看槽的原始形态。
    pub(super) fn bind_slots(&self, cxt: &Cxt<'_>) -> Vec<u32> {
        let n = cxt.lvl;
        let mut out = Vec::new();
        for i in 0..env_len(cxt.env) {
            let mut raw = env_nth(&self.defs, cxt.env, i);
            while v_tag(raw) == 7 {
                match v_xcell_of(raw) {
                    XCell::VSub { val, .. } => raw = *val,
                    _ => break,
                }
            }
            if v_tag(raw) == 0 && v_lvl_of(raw) + i + 1 == n {
                out.push(v_lvl_of(raw));
            }
        }
        out
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    pub(super) fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            // 变量：局部 names（当前 def 的 binder + fake 占位，覆盖全局）
            // 优先，之后回落 Machine 的全局名字表（顶层 define，append-only
            // 不随 Cxt 克隆）。都缺即 not in scope（参考版 Raw::Var 臂同款）。
            Raw::Var(x) => {
                if let Some(&blvl) = cxt.names.by_name.get(x.data.as_str()) {
                    let ty = *cxt.names.by_lvl.get(&blvl).expect("by_lvl 缺层级");
                    let ix = if blvl >= GLOBAL_BASE {
                        blvl
                    } else {
                        cxt.lvl - blvl - 1
                    };
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                if let Some(&(blvl, ty)) = self.global_names.get(x.data.as_str()) {
                    let ix = if blvl >= GLOBAL_BASE {
                        blvl
                    } else {
                        cxt.lvl - blvl - 1
                    };
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                Err(Error(x.clone().map(|x| format!("error name not in scope: {}", x))))
            }

            Raw::Obj(x, t) => {
                // `Point.mk` 限定构造子引用：改写成 Var("Point.mk")（src_names
                // 里 struct 的 case 名）——参考版 Obj 臂的 mk 特例同款
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(
                            bump,
                            cxt,
                            &Raw::Var(sum_name.clone().map(|n| format!("{n}.mk"))),
                        );
                    }
                }
                let (tm, a) = self.infer_expr(bump, cxt, x)?;
                let a_f = self.force_v(bump, a);
                if v_tag(a_f) == 7 {
                    if let XCell::Sum { params, cases, .. } = v_xcell_of(a_f) {
                        // struct：单 case 且名字带 `.mk` → 剥 mk 的构造子
                        // 类型链取字段类型。隐式 binder 用头部 Sum 实参实例化
                        // （只取 Impl——显式索引不占槽）；**显式字段 binder 用
                        // 接收者的卡住投影实例化**（eval(Obj(接收者项, 字段名))，
                        // L08 评审修复回移——旧 U(0) 占位会让依赖在前字段的
                        // 在后字段出现在检查位时假拒，与参考版同步）
                        let mut c: Option<Vec<(&str, V)>> = None;
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let case = cases[0];
                            if let Ok((_, case_typ)) =
                                self.infer_expr(bump, cxt, &Raw::Var(empty_span(case.to_string())))
                            {
                                let mut ret: Vec<(&str, V)> = vec![];
                                let mut typ = case_typ;
                                // struct 隐式参数的实例值（声明序）
                                let mut param: Vec<V> = params
                                    .iter()
                                    .filter(|p| p.icit == Icit::Impl)
                                    .map(|p| p.val)
                                    .collect();
                                param.reverse();
                                loop {
                                    let typ_f = self.force_v(bump, typ);
                                    if v_tag(typ_f) == 4 {
                                        let p = v_pi_of(typ_f);
                                        if p.icit == Icit::Expl {
                                            ret.push((p.name, p.dom));
                                            let val = self.eval(
                                                bump,
                                                cxt.env,
                                                bump.alloc(Tm::Obj(tm, p.name)),
                                            );
                                            typ = {
                                                let env = env_ext(bump, p.env, val);
                                                self.eval(bump, env, p.body)
                                            };
                                        } else {
                                            let val = param
                                                .pop()
                                                .unwrap_or_else(v_u0);
                                            ret.push((p.name, p.dom));
                                            typ = {
                                                let env = env_ext(bump, p.env, val);
                                                self.eval(bump, env, p.body)
                                            };
                                        }
                                    } else {
                                        break;
                                    }
                                }
                                c = Some(ret);
                            }
                        }
                        let field = c
                            .and_then(|params| {
                                params
                                    .into_iter()
                                    .find(|(fields_name, _)| *fields_name == t.data.as_str())
                                    .map(|(_, ty)| ty)
                            })
                            .or_else(|| {
                                params
                                    .iter()
                                    .find(|p| p.name == t.data.as_str())
                                    .map(|p| p.ty)
                            });
                        if let Some(ty) = field {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        return Err(Error(t.clone().map(|t| format!(
                            "`{}`: {} has no object `{}`",
                            pretty_tm(
                                0,
                                types_names_list(cxt.types),
                                &export(tm)
                            ),
                            debug_val(&self.spine, &self.defs, a),
                            t,
                        ))));
                    }
                    if let XCell::SumCase { datas, .. } = v_xcell_of(a_f) {
                        // 接收者类型是构造子值：字段类型在 datas 里
                        let field = datas
                            .iter()
                            .find(|d| d.name == t.data.as_str())
                            .map(|d| d.val);
                        if let Some(ty) = field {
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        return Err(Error(t.clone().map(|t| format!(
                            "`{}`: {} has no object `{}`",
                            pretty_tm(0, types_names_list(cxt.types), &export(tm)),
                            debug_val(&self.spine, &self.defs, a),
                            t,
                        ))));
                    }
                }
                Err(Error(t.clone().map(|t| format!(
                    "`{}` has no object `{}`",
                    pretty_tm(0, types_names_list(cxt.types), &export(tm)),
                    t,
                ))))
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let a_t = self.quote(bump, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a);
                let infered = self.infer_expr(bump, &cxt2, tbody);
                let (t_inferred0, b0) = infered?;
                let (t_inferred, b) = self.insert(bump, &cxt2, t_inferred0, b0)?;
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt.lvl + 1, b);
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
                Err(Error(x.clone().map(|_| "infer named lambda".to_owned())))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let t_span = t.to_span();
                let (i, t, tty) = match arg {
                    Either::Name(name) => {
                        let infered = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_until_name(bump, cxt, &name.data, infered.0, infered.1)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Impl) => {
                        let (t, tty) = self.infer_expr(bump, cxt, t)?;
                        (Icit::Impl, t, tty)
                    }
                    Either::Icit(Icit::Expl) => {
                        let infered = self.infer_expr(bump, cxt, t)?;
                        let (t, tty) = self.insert_t(bump, cxt, infered.0, infered.1)?;
                        (Icit::Expl, t, tty)
                    }
                };
                let tty = self.force_v(bump, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(t_span.map(|_| {
                            format!("icit mismatch {:?} {:?}", i, p.icit)
                        })));
                    }
                    (p.dom, p)
                } else {
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 参考版把合成 Π 放在 unify_catch 的首位——忠实复刻，
                    // 只影响报错文案方向。合成 binder（"x"）按参考版
                    // cxt.bind 走全量 bind（env/telescope/pruning 扩展），
                    // 但名字不入表外泄（临时 cxt 只喂 fresh_meta）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                    let a = self.eval_fresh(bump, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt.lvl, a);
                    let cxt2 = self.bind_name(bump, cxt, "x", a_t, a);
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u(0));
                    let cell = bump.alloc(PiCell {
                        name: "x",
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty)?;
                    (a, &*cell)
                };
                let u_checked = self.check(bump, cxt, u, a)?;
                let arg_v = self.eval(bump, cxt.env, u_checked);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u_checked, i)), ty))
            }

            // Infer universe type
            Raw::U(x) => Ok((bump.alloc(Tm::U(*x)), v_u(x + 1))),

            // Infer dependent function types
            Raw::Pi(x, i, a, b) => {
                let mut universe = 0u32;
                let (a_checked, lvl) = self.check_universe(bump, cxt, a)?;
                universe = universe.max(lvl);
                let a_eval = self.eval(bump, cxt.env, a_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let a_t = self.quote(bump, cxt.lvl, a_eval);
                let cxt2 = self.bind_name(bump, cxt, &x.data, a_t, a_eval);
                let checked = self.check_universe(bump, &cxt2, b);
                let (b_checked, lvl) = checked?;
                universe = universe.max(lvl);
                Ok((
                    bump.alloc(Tm::Pi(name, *i, a_checked, b_checked)),
                    v_u(universe),
                ))
            }

            // Infer let bindings
            Raw::Let(x, a_ty, t2, u2) => {
                let (a_checked, _) = self.check_universe(bump, cxt, a_ty)?;
                let va = self.eval(bump, cxt.env, a_checked);
                let t_checked = self.check(bump, cxt, t2, va)?;
                let vt = self.eval(bump, cxt.env, t_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let cxt2 = self.define_name(bump, cxt, &x.data, a_checked, t_checked, vt, va);
                let inferred = self.infer_expr(bump, &cxt2, u2);
                let (u_inferred, b) = inferred?;
                Ok((
                    bump.alloc(Tm::Let(name, a_checked, t_checked, u_inferred)),
                    b,
                ))
            }

            // Infer holes
            Raw::Hole => {
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&literal.data))),
                v_lit_ty(),
            )),

            // match 只能在检查模式下使用（期望类型决定分支体怎么查）
            Raw::Match(_, _) => Err(Error(
                t_span_of(t).map(|_| "try to infer match".to_owned()),
            )),

            // enum 本体（Decl::Enum 注册期构造）：逐参数推断值 + 引读类型
            Raw::Sum(name, params, cases, universe) => {
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for (n, i, raw) in params {
                    let (value_checked, value_ty) = self.infer_expr(bump, cxt, raw)?;
                    let ty = self.quote(bump, cxt.lvl, value_ty);
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
                    v_u(*universe),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造）：typ 只推断不检查
            Raw::SumCase {
                typ,
                case_name,
                datas,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, cxt.env, typ_checked);
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

    // decl 层的推断（参考版 `Infer::infer(Decl)`）：def 折叠参数后
    // check_universe 类型、fake_bind 占位、检查体、global 表覆盖真值；
    // Println 推断体；enum 先扫宇宙层级再注册类型本体 + 逐构造子（裸名）。
    pub(super) fn infer_decl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
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
                let global_idx = self.globals.len() as u32;
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, cxt.env, typ_tm);
                // 递归：先把名字登记成指向自身的大层级占位（src_names +
                // global 表），检查体，再用真实值覆盖。
                let fake = self.fake_bind(cxt, &name.data, vtyp, global_idx);
                self.globals.push(v_lvl(global_idx + GLOBAL_BASE));
                self.neutral.push(v_lvl(global_idx + GLOBAL_BASE));
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                let vt = self.eval(bump, fake.env, t_tm);
                self.globals[global_idx as usize] = vt;
                drop(fake); // 释放 Rc 引用，define 的 make_mut 才能原地写
                let out = self.define_name_in(bump, cxt, &name.data, typ_tm, t_tm, vt, vtyp);
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                Ok((DeclOut::Println(tm), clone_cxt(cxt)))
            }
            Decl::Enum {
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U(0)（与参考版
                // 同步，L07/L08 黑盒三轮修复的 L09 形态）。域洞若保留，第
                // 2+ 个参数的域是 AppPruning 部分应用 meta（`?m A`），使用
                // 点显式供给隐式实参需解该 meta，invert 对非变量 spine 实参
                // 直接 Err——误报 can't unify。宇宙扫描对 U(0) 域贡献 lvl 0
                // = max 恒等；显式标注与显式索引不动。
                let params: Vec<(crate::parser_lib::Span<String>, Raw, Icit)> = params
                    .iter()
                    .map(|(n, a, i)| {
                        let a = if *i == Icit::Impl && matches!(a, Raw::Hole) {
                            Raw::U(0)
                        } else {
                            a.clone()
                        };
                        (n.clone(), a, *i)
                    })
                    .collect();
                // 宇宙层级扫描（副作用照参考版：infer_expr/check_universe
                // 的 meta 分配全保留，结果只取层级）
                let mut universe_lvl = 0u32;
                for p in params.iter() {
                    if let Ok((Tm::U(lvl), _)) = self.infer_expr(bump, cxt, &p.1) {
                        universe_lvl = universe_lvl.max(*lvl);
                    }
                }
                for case in cases.iter() {
                    for c in case.1.iter() {
                        if let Ok((_, lvl)) = self.check_universe(bump, cxt, &c.1) {
                            universe_lvl = universe_lvl.max(lvl);
                        }
                    }
                }
                // enum 类型本体：λ params → Sum(name, [(p, Var p, ?, icit)], cases)
                let new_params: Vec<(crate::parser_lib::Span<String>, Icit, Raw)> = params
                    .iter()
                    .map(|x| (x.0.clone(), x.2, Raw::Var(x.0.clone())))
                    .collect();
                // 构造子缺省返回类型：Name 逐个应用到隐式参数
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
                let sum = Raw::Sum(name.clone(), new_params, cases_spanned, universe_lvl);
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U(universe_lvl), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let global_idx = self.globals.len() as u32;
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, cxt.env, typ_tm);
                let fake = self.fake_bind(cxt, &name.data, vtyp, global_idx);
                self.globals.push(v_lvl(global_idx + GLOBAL_BASE));
                self.neutral.push(v_lvl(global_idx + GLOBAL_BASE));
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                let vt = self.eval(bump, fake.env, t_tm);
                self.globals[global_idx as usize] = vt;
                drop(fake); // 释放 Rc 引用，define 的 make_mut 才能原地写
                let mut cxt = self.define_name_in(bump, cxt, &name.data, typ_tm, t_tm, vt, vtyp);
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}；
                // **裸名登记**（L09 无 Enum.case 别名）
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
                    let (typ_tm, _) = self.check_universe(bump, &cxt, ctor_ty)?;
                    let vtyp = self.eval(bump, cxt.env, typ_tm);
                    // 构造子良构性（参考版同步，L07 2026-09-18 评审修复 6）：
                    // ret 必须是本 enum 的 Sum 且参数位是 telescope 内的
                    // bare rigid
                    self.check_ctor_wf(bump, &cxt, &name.data, &ctor_name.data, vtyp)?;
                    let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                    let vt = self.eval(bump, cxt.env, t_tm);
                    cxt = self.define_name_in(bump, &mut cxt, &ctor_name.data, typ_tm, t_tm, vt, vtyp);
                }
                Ok((DeclOut::Enum, cxt))
            }
        }
    }

    /// 构造子返回类型良构性（参考版 `Infer::check_ctor_wf` 同款，L07
    /// 2026-09-18 评审修复 6 的同步移植）：实例化构造子类型的全部绑定器
    /// 后，ret 的 WHNF 必须是 `enum_name` 的 `Sum`，且其隐式参数位逐一等
    /// 于 telescope 内的 bare rigid。允许构造子重绑定参数
    /// （`p[A,B](a,b) -> Pack[A][B] a b`），拒绝参数位非变量
    /// （`c -> Foo[Bool]`）与非本 enum 的 ret（`c -> Nat`）——后者向构造
    /// 子名字空间注入永不匹配任何模式的 phantom 值，对覆盖检查完备的
    /// match 在封闭输入上卡死。
    fn check_ctor_wf(
        &mut self,
        bump: &Bump,
        cxt: &Cxt<'_>,
        enum_name: &str,
        ctor_name: &str,
        ctor_vtyp: V,
    ) -> Result<(), Error> {
        let base = cxt.lvl;
        let mut ty = ctor_vtyp;
        let mut bound = 0u32;
        let ret = loop {
            let tyf = self.force_v(bump, ty);
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let u = v_lvl(base + bound);
                bound += 1;
                let env = env_ext(bump, p.env, u);
                ty = self.eval(bump, env, p.body);
            } else {
                break tyf;
            }
        };
        let retf = self.force_v(bump, ret);
        if !(v_tag(retf) == 7 && matches!(v_xcell_of(retf), XCell::Sum { .. })) {
            return Err(Error(empty_span(()).map(|_| {
                format!("构造子 {ctor_name} 的返回类型不是和类型")
            })));
        }
        if let XCell::Sum { name: sname, params, .. } = v_xcell_of(retf) {
            if *sname != enum_name {
                return Err(Error(empty_span(()).map(|_| {
                    format!("构造子 {ctor_name} 的返回类型是 {sname}，不是 {enum_name}")
                })));
            }
            for p in params.iter() {
                if p.icit == Icit::Impl {
                    let v = p.val;
                    let bare_rigid = v_tag(v) == 0
                        && v_lvl_of(v) >= base
                        && v_lvl_of(v) < base + bound;
                    if !bare_rigid {
                        return Err(Error(empty_span(()).map(|_| {
                            format!(
                                "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
                            )
                        })));
                    }
                }
            }
        }
        Ok(())
    }
}

/// `Raw::Match` 推断错误用的 span（to_span 的借用版）。
fn t_span_of(t: &Raw) -> crate::parser_lib::Span<()> {
    t.to_span()
}

/// `Val::U(0)` 占位（参考版 struct 字段剥链的 `unwrap_or(Val::U(0))`）。
fn v_u0() -> V {
    v_u(0)
}

/// Cxt 的浅克隆（env/引用 Copy，names 是 Rc 克隆——快照共享）。
pub(super) fn clone_cxt<'a>(cxt: &Cxt<'a>) -> Cxt<'a> {
    Cxt {
        env: cxt.env,
        names: cxt.names.clone(),
        types: cxt.types,
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
    }
}

/// 中性 global 视图（参考版 avoid_recursive 克隆：全局值全部换成指向
/// 自身大层级的 Rigid）。
pub(crate) fn neutral_of(globals: &[V]) -> Vec<V> {
    globals
        .iter()
        .enumerate()
        .map(|(i, _)| v_lvl(i as u32 + GLOBAL_BASE))
        .collect()
}

/// 槽位向量 → 纯链环境（头 = 最内层）。
fn chain_env<'a>(bump: &'a Bump, slots: &[V]) -> Env<'a> {
    let mut env: Option<&'a EnvCons<'a>> = None;
    for val in slots.iter().rev() {
        env = Some(bump.alloc(EnvCons { val: *val, next: env }));
    }
    Env {
        flat_base: 0,
        flat_len: 0,
        binds: env,
    }
}

/// decl 层推断的产出：Def 带名（bench 的 nf 口径按名定位），Println 带
/// elaborated 体（run 的 nf 输出用）。
pub(super) enum DeclOut<'a> {
    Def { name: &'a str },
    Println(&'a Tm<'a>),
    Enum,
}
// builtin 注册（每轮 prime；参考版 `Cxt::new` 逐条对应）
// --------------------------------------------------------------------------------

impl Machine {
    /// 每轮注册（参考版 `Cxt::new`）：String 类型 + string_concat。两者的
    /// **值按参考版手工构造**——string_concat 的 λ/Π 闭包 env 里钉着
    /// `LiteralType` 填充槽（使 `Tm::Prim` 读 env 前两槽、Π 类型的
    /// `Var(2)` 指回 String），与 eval 出来的形态逐槽一致。
    pub(super) fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let lit_ty: &'a Tm<'a> = bump.alloc(Tm::LiteralType);
        let u0_t: &'a Tm<'a> = bump.alloc(Tm::U(0));
        // String : U(0)，值 = LiteralType
        let mut cxt = Cxt::empty();
        self.define_name_in(
            bump,
            &mut cxt,
            "String",
            u0_t,
            lit_ty,
            v_lit_ty(),
            v_u(0),
        );
        // string_concat：λ x y → Prim；类型 Π x:String. Π y:String. String
        // （体 Tm 的 Var 索引与参考版一致：域 Var(0)/Var(1)，返回 Var(2)）
        let sc_lam_tm: &'a Tm<'a> = bump.alloc(Tm::Lam(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim))),
        ));
        let sc_pi_tm: &'a Tm<'a> = bump.alloc(Tm::Pi(
            "x",
            Icit::Expl,
            bump.alloc(Tm::Var(0)),
            bump.alloc(Tm::Pi(
                "y",
                Icit::Expl,
                bump.alloc(Tm::Var(1)),
                bump.alloc(Tm::Var(2)),
            )),
        ));
        // 值 = Lam("x", Expl, Closure([LiteralType], Lam("y", Expl, Prim)))
        let filled = env_ext(bump, EMPTY_ENV, v_lit_ty());
        let sc_val = v_clo(bump.alloc(CloCell {
            name: "x",
            icit: Icit::Expl,
            env: filled,
            body: sc_lam_body(bump),
        }));
        // 类型 = Pi("x", Expl, LiteralType, Closure([LiteralType], Pi 体))
        let sc_ty = v_pi(bump.alloc(PiCell {
            name: "x",
            icit: Icit::Expl,
            dom: v_lit_ty(),
            env: filled,
            body: sc_pi_cod(bump),
        }));
        self.define_name_in(bump, &mut cxt, "string_concat", sc_pi_tm, sc_lam_tm, sc_val, sc_ty)
    }

    /// 参考版 `bench_check` 的主循环（无输出变体）：返回 (是否通过，最终
    /// 上下文，最后一个 def 的值)。
    pub(super) fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Cxt<'a>, Option<V>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            let is_def = matches!(d, Decl::Def { .. });
            match self.infer_decl(bump, &mut cxt, d) {
                Ok((_, nc)) => {
                    cxt = nc;
                    if matches!(d, Decl::Def { .. }) {
                        // define 链的 env 槽顶 = 本 def 的登记值
                        last = Some(env_nth(&self.defs, cxt.env, 0));
                    }
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        (Ok(()), cxt, last)
    }
}

/// `Lam("y", Expl, Prim)`（string_concat 值闭包的体）。
fn sc_lam_body<'a>(bump: &'a Bump) -> &'a Tm<'a> {
    bump.alloc(Tm::Lam("y", Icit::Expl, bump.alloc(Tm::Prim)))
}

/// `Pi("y", Expl, Var(1), Var(2))`（string_concat 类型闭包的体）。
fn sc_pi_cod<'a>(bump: &'a Bump) -> &'a Tm<'a> {
    bump.alloc(Tm::Pi(
        "y",
        Icit::Expl,
        bump.alloc(Tm::Var(1)),
        bump.alloc(Tm::Var(2)),
    ))
}
