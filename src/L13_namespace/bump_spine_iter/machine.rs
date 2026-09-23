//! machine：稳态复用机（`Machine`/`Names`/`SuffixMemo`）与 state journal
//! （`STATE_JOURNAL`/`StateUndo` 七表撤销日志）、Elaboration 上下文
//! （`Cxt`/`TCons`/`NsCons`）、elaboration 全量（check/check_universe/隐式
//! 插入 insert 族/模式特化 unify_pm/refresh/主 infer/infer_expr/infer_decl/
//! wrap_match_in_call）、名字与 decl 键解析助手（qualified_path_str/
//! split_first_segment）与参考域助手（nat_chain_len_ref/tm_to_raw_type/
//! prefix_decl_name/tm_refs_bn/clone_cxt/chain_env/DeclOut）。原
//! bump_spine_iter.rs 的 "Machine（稳态复用）与 elaboration" 与
//! "Elaboration 上下文" 两节（trait 求解方法移入 typeclass 子模块、观察面
//! push 方法移入 observe 子模块——两者均以独立 `impl Machine` 块承载），
//! 逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::cell::RefCell;
use std::rc::Rc;

use super::parser::syntax::{ClassItem, Decl, Either, Icit, Raw};
use super::pretty::pretty_tm;
use super::{empty_span, Error, PatternDetail, CTm, CVal};
use crate::L13_namespace::typeclass::{Assertion, Instance};
use crate::parser_lib::ToSpan;

use super::compiler::Compiler;
use super::debug::debug_val;
use super::entry::{export, no_metas};
use super::env::{
    env_collect, env_ext, env_ext_defs, env_len, env_nth, EMPTY_ENV, Env, EnvCons, PiCell,
};
use super::eval::{eval_iter, W};
use super::force::{
    force, prim_version_bump, twin_stat_record, ReclaimOnClear, CACHE_SHRINK_MIN_ENTRIES,
    META_JOURNAL, SPINE_SHRINK_MIN_ENTRIES, TWIN_STAT_QUOTE, TWIN_STAT_SPINE,
};
use super::prim::{
    is_nat_sum_v, tm_scan_global_ops, DeclEntry, Decls, Mutable, PrimId,
};
use super::quote::{quote_iter, QJob, QuoteMemo};
use super::rename::{invert_bump, lams_from_ty, prune_ty_bump, rename_iter, RenBuf};
use super::spine::{
    is_flex, journal_meta, meta_journal_discard, meta_journal_rollback, MetaEntry, MetaSnap,
    Spine,
};
use super::syntax::{
    LCons, PrCons, SumDataT, SumParamT, SumParamV, Tm, V, XCell, lvl2ix, v_lit_ty, v_lvl, v_lvl_of,
    v_meta, v_meta_of, v_pi, v_pi_of, v_tag, v_u, v_u_of, v_xcell, v_xcell_of,
};
use super::typeclass::{TraitDefEntry, TraitState, v_to_ref_val};
use super::unify::{unify_iter, ConvScratch, UItem};

/// 第一/二组表（`clear_round` 每轮清 + 观察面每 kick 清）的归还档阈值：
/// **槽 ≥24B** 的表（键带 `SmolStr` / 条目带 `String` / 值带三 `Rc`）。与
/// force.rs 的 `CACHE_SHRINK_MIN_ENTRIES`（1<<18 × ~24B ≈ 6MB，配合
/// [`FORCE_MEMO_CAP`] 的百万级 CAP）同构，但这两组表没有 force memo 式的
/// CAP——沿用 1<<18 意味着归还档永不触发（归档项变死代码）。按「空桶
/// ≥ ~0.3MB 才值得还，且须高于稳态峰值」定标 1<<13。稳态实测（l06l13mem
/// k=11 + 临时表长探针，2026-09-23）：suffix_indexed_keys ≤ 4104
/// （struct/strchain）、mutable.replay ≤ 4103、decl_suffix_index ≤ 98
/// （prelude-core；hdl 形态的限定键也在千条级）——全在 1<<13 之下，归还
/// 只对超阈病态峰值触发；阈值以下照旧只 `clear`，稳态复用与分配计数零
/// 变化（归档预期，perf-l13-round §3.1.3）。
const TBL_SHRINK_MIN_ENTRIES: usize = 1 << 13;
/// 指针键/值表（`tm_import` / `val_import`：槽 16–20B）的同一水位：
/// 1<<15 × ~20B ≈ 0.65MB。
const PTR_TBL_SHRINK_MIN_ENTRIES: usize = 1 << 15;
/// 观察面六表的归还水位：**稳态峰值实测**（l06l13mem k=11 + TBLPROBE）
/// struct hover_table = 24605 条/轮、strchain 16382——观察面在 bench/LSP
/// kick 口径是合法稳态（每轮同量重建），阈值必须在其上方，否则每轮付
/// ~13 次 Vec 重增长（+2.6MB/轮 churn）拆掉稳态复用。定 1<<15（×40B 槽
/// ≈ 1.3MB 空缓冲）：≥3.3 万条目的超大文件才触发归还。
const OBS_TBL_SHRINK_MIN_ENTRIES: usize = 1 << 15;

thread_local! {
    /// 稳态七表撤销日志（评审 B#2 二期）：`Tycker::observe_user` 每 kick
    /// 的整克隆恢复（tstate/mutable/symbol_table/import_map/
    /// trait_method_cache/tm_import/val_import）改为「kick 末撤销日志」
    /// ——kick 开帧后所有写点记 (key, 旧值 Option)，kick 末逆序撤销，
    /// 逐键回到 checkpoint 形态。七表 add-mostly/覆盖少（用户段只追加
    /// trait/实例/算符方法/import 别名/指针导入与可变全局），撤销面 =
    /// 本 kick 增量；首条 (key, 旧值) 即 checkpoint 值，逆序撤销必然
    /// 终止于 checkpoint 形态。纪律与 [`META_JOURNAL`] 同款：栈式帧、
    /// **栈空时写点零成本 no-op**（bench / run_decls / prime 路径不记）。
    /// 当前只有 kick 单层帧——探测（`run_pure_probe` 等）只回滚
    /// metas/trait_metas，探测期七表写照记 kick 帧、kick 末一并撤销
    /// （与旧行为一致：探测期表写本就存活到 kick 末）。
    ///
    /// 恢复语义注意：
    /// - mutable 的 check_lines/check_line_set 恒配对（ReportCheckIssue
    ///   成对插入、排水成对清空），`CheckLinesTake` 撤销时按 lines 重建
    ///   set；
    /// - `Synth` 的 scratch（generator_stack/resume_stack/assertion_table/
    ///   root_answer）L13 从不填充（`synth` 只被 L10-L12 调用；
    ///   can_satisfy 是 &self 读），clean() 清的恒是空表，无需记账。
    static STATE_JOURNAL: RefCell<Vec<Vec<StateUndo>>> =
        const { RefCell::new(Vec::new()) };
}

/// 撤销条目：表写点的 (key, 旧值 Option)。撤销 = Some 重插 / None 移除；
/// Push 型撤销 = 桶 pop（`impl_trait_for` 的实例/索引桶只增）。
/// `pub(super)`：`typeclass.rs` 的 Synth 写点（new_trait /
/// set_trait_out_params / impl_trait_for）直接记账。
pub(in crate::L13_namespace) enum StateUndo {
    SymbolTable((SmolStr, usize), Option<SmolStr>),
    ImportMap(SmolStr, Option<SmolStr>),
    TraitMethodCache((SmolStr, SmolStr), Option<(Rc<CTm>, Rc<CVal>, Rc<CTm>)>),
    TmImport(usize, Option<&'static Tm<'static>>),
    ValImport(usize, Option<V>),
    MutableMap(SmolStr, Option<V>),
    MutableReplay(SmolStr, Option<bool>),
    /// 排水 take+clear 联合撤销：lines 恢复进 check_lines，set 按 lines 重建。
    CheckLinesTake(Vec<SmolStr>),
    /// ReportCheckIssue 的新行推送（行进 check_lines、键进 check_line_set
    /// 恒配对）：撤销 = vec pop + set 移除。
    CheckLinesPush(SmolStr),
    /// check_seen 新键（排水去重 insert 返回 true 才记）。
    CheckSeenInsert(SmolStr),
    /// `new_trait`：键可覆盖（用户重声明 prelude trait 名）→ 记整桶旧值。
    TraitInstancesSet(SmolStr, Option<Vec<Instance>>),
    /// `impl_trait_for` 实例桶追加（撤销 = pop；桶若为本次 entry 新建，
    /// pop 后整键移除——第二元 = 桶在 push 前是否已存在）。
    TraitInstancesPush(SmolStr, bool),
    /// `impl_trait_for` head 索引桶追加（同上）。
    TraitHeadIndexPush((SmolStr, SmolStr), bool),
    /// `set_trait_out_params`：solver 侧 out 参数掩码。
    TraitSolverOutParamsSet(SmolStr, Option<Vec<bool>>),
    /// `TraitState.definition` 整条覆盖。
    TraitDefinitionSet(SmolStr, Option<TraitDefEntry>),
    /// `TraitState.out_param` 掩码覆盖。
    TraitStateOutParamSet(SmolStr, Option<Vec<bool>>),
    /// `TraitState.assoc_defaults` 条目覆盖。
    TraitAssocDefaultSet((SmolStr, SmolStr), Option<Option<Raw>>),
}

/// kick 开帧（[`Tycker::observe_user`] 起点一次）。
pub(super) fn state_journal_open_frame() {
    STATE_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
}

/// 写点记账：journal 未激活（栈空）时零成本。`pub(super)` 同 [`StateUndo`]。
pub(in crate::L13_namespace) fn state_journal_record(ent: StateUndo) {
    STATE_JOURNAL.with(|j| {
        if let Some(top) = j.borrow_mut().last_mut() {
            top.push(ent);
        }
    });
}

/// kick 末回滚：弹栈顶帧逆序撤销（栈空 = 无帧期写点，无事可撤）。
pub(super) fn state_journal_rollback(m: &mut Machine) {
    let top = STATE_JOURNAL.with(|j| j.borrow_mut().pop());
    let Some(log) = top else { return };
    // 回滚可能撤销 decl 键（SymbolTable/ImportMap 等）——suffix_memo 的
    // 正/负结果都可能过期，版本 bump 使查询侧整表弃用
    m.suffix_memo_version = m.suffix_memo_version.wrapping_add(1);
    for ent in log.into_iter().rev() {
        match ent {
            StateUndo::SymbolTable(k, old) => match old {
                Some(v) => {
                    m.symbol_table.insert(k, v);
                }
                None => {
                    m.symbol_table.remove(&k);
                }
            },
            StateUndo::ImportMap(k, old) => match old {
                Some(v) => {
                    m.import_map.insert(k, v);
                }
                None => {
                    m.import_map.remove(&k);
                }
            },
            StateUndo::TraitMethodCache(k, old) => match old {
                Some(v) => {
                    m.trait_method_cache.insert(k, v);
                }
                None => {
                    m.trait_method_cache.remove(&k);
                }
            },
            StateUndo::TmImport(k, old) => match old {
                Some(v) => {
                    m.tm_import.insert(k, v);
                }
                None => {
                    m.tm_import.remove(&k);
                }
            },
            StateUndo::ValImport(k, old) => match old {
                Some(v) => {
                    m.val_import.insert(k, v);
                }
                None => {
                    m.val_import.remove(&k);
                }
            },
            StateUndo::MutableMap(k, old) => match old {
                Some(v) => {
                    m.mutable.borrow_mut().map.insert(k, v);
                }
                None => {
                    m.mutable.borrow_mut().map.remove(&k);
                }
            },
            StateUndo::MutableReplay(k, old) => match old {
                Some(v) => {
                    m.mutable.borrow_mut().replay.insert(k, v);
                }
                None => {
                    m.mutable.borrow_mut().replay.remove(&k);
                }
            },
            StateUndo::CheckLinesTake(lines) => {
                let mut mu = m.mutable.borrow_mut();
                mu.check_lines = lines;
                mu.check_line_set = mu.check_lines.iter().cloned().collect();
            }
            StateUndo::CheckLinesPush(k) => {
                let mut mu = m.mutable.borrow_mut();
                mu.check_line_set.remove(&k);
                // 配对不变式：push 的键恒在 vec 尾部（排水期 vec 被整体
                // take 走，残留 push 必发生在 take 之后且无中间 push）。
                if mu.check_lines.last().map(|x| *x == k).unwrap_or(false) {
                    mu.check_lines.pop();
                }
            }
            StateUndo::CheckSeenInsert(k) => {
                m.mutable.borrow_mut().check_seen.remove(&k);
            }
            StateUndo::TraitInstancesSet(k, old) => match old {
                Some(v) => {
                    m.tstate.solver.class_instances.insert(k, v);
                }
                None => {
                    m.tstate.solver.class_instances.remove(&k);
                }
            },
            StateUndo::TraitInstancesPush(k, existed) => {
                let mut solver = &mut m.tstate.solver;
                if let Some(v) = solver.class_instances.get_mut(&k) {
                    v.pop();
                }
                if !existed {
                    solver.class_instances.remove(&k);
                }
            }
            StateUndo::TraitHeadIndexPush(k, existed) => {
                let mut solver = &mut m.tstate.solver;
                if let Some(v) = solver.head_index.get_mut(&k) {
                    v.pop();
                }
                if !existed {
                    solver.head_index.remove(&k);
                }
            }
            StateUndo::TraitSolverOutParamsSet(k, old) => match old {
                Some(v) => {
                    m.tstate.solver.trait_out_params.insert(k, v);
                }
                None => {
                    m.tstate.solver.trait_out_params.remove(&k);
                }
            },
            StateUndo::TraitDefinitionSet(k, old) => match old {
                Some(v) => {
                    m.tstate.definition.insert(k, v);
                }
                None => {
                    m.tstate.definition.remove(&k);
                }
            },
            StateUndo::TraitStateOutParamSet(k, old) => match old {
                Some(v) => {
                    m.tstate.out_param.insert(k, v);
                }
                None => {
                    m.tstate.out_param.remove(&k);
                }
            },
            StateUndo::TraitAssocDefaultSet(k, old) => match old {
                Some(v) => {
                    m.tstate.assoc_defaults.insert(k, v);
                }
                None => {
                    m.tstate.assoc_defaults.remove(&k);
                }
            },
        }
    }
}

/// qualified path 拼接（参考版 `qualified_path_str`）：`a.b.c` 形的 Obj 链
/// → 全路径字符串；非 Var/Obj 形态 None。
pub(super) fn qualified_path_str(x: &Raw, field: &str) -> Option<SmolStr> {
    match x {
        Raw::Var(name) => Some(SmolStr::new(format!("{}.{}", name.data, field))),
        Raw::Obj(inner, Some(seg)) => qualified_path_str(inner.as_ref(), &seg.data)
            .map(|p| SmolStr::new(format!("{p}.{field}"))),
        _ => None,
    }
}

/// 路径首段切分（参考版 `split_first_segment`）。
pub(super) fn split_first_segment(path: &SmolStr) -> Option<(SmolStr, SmolStr)> {
    let s = path.as_str();
    let dot = s.find('.')?;
    Some((SmolStr::new(&s[..dot]), SmolStr::new(&s[dot + 1..])))
}

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

/// 名字表快照（参考版 BiMap 的 map1/map2 同构；**随 Cxt 克隆**——
/// bind/define/fake_bind 克隆整表插入，与参考版 `src_names.clone()` 的
/// 逐上下文隔离语义逐字对应，无需撤销轨迹）。
#[derive(Clone, Default)]
pub(super) struct Names {
    /// 名字 → 层级（map1：只收源码 binder 与 fake_bind；inserted binder
    /// 与参考版 `new_binder` 一样不入）。
    pub(super) by_name: FxHashMap<SmolStr, u32>,
    /// 层级 →（类型值, binder 名源码 span）（map2：按层级持久，refresh 的
    /// get_by_key2_mut 目标；名字查类型经此中转，refresh 更新即生效。
    /// span 为观察面 def_span（局部 hover/goto，合成 binder 记零 span）；
    /// 并入元组而非平行表——Names 随 bind 链 COW 克隆，三表克隆实测 +5% 。
    pub(super) by_lvl: FxHashMap<u32, (V, crate::parser_lib::Span<()>)>,
}

/// 稳态复用机（L06/L08 版 + L12/L13 增量：decl 表 / trait 合成 / 可变全局
/// / pm 事实表）。全局走 `Cxt.decls`（名字键，参考版 `Cxt.decl` 同构），
/// **没有** L09/L10 的 `Infer.global` 大下标与 `GLOBAL_BASE` 哨兵——无相应
/// 下溢边界；名字状态在 [`Cxt`] 的 `names` 快照里（参考版 BiMap 同构）。
/// Var 后缀回退 memo 的条目（失效纪律见 [`Machine::suffix_memo`] 字段注释）
#[derive(Clone)]
enum SuffixMemo {
    /// 唯一命中：全键（头在填表时可见，可见性单调 → 无需复查头）
    Pos { full_key: SmolStr, bucket_ptr: usize },
    /// 确定无唯一命中：记填表时被"头不可见"过滤的候选首段集（空桶为空集）。
    /// 活检头可见性，任一转可见即重查；桶指针变化（新候选）同样重查。
    Neg {
        bucket_ptr: usize,
        blocked_heads: Vec<SmolStr>,
    },
}

pub(crate) struct Machine {
    pub(super) spine: Spine,
    pub(super) vals: Vec<V>,
    /// icit 侧栈（eval 右链下降用；跨调用复用容量，进核前 clear）。
    pub(super) icits: Vec<Icit>,
    /// unify 的判等记忆化 + 实参收集草稿（跨调用复用容量，进核前 clear）。
    pub(super) conv: ConvScratch,
    /// 平坦环境区域（每轮 append-only，只增不减）。
    pub(super) defs: Vec<V>,
    pub(crate) metas: Vec<MetaEntry>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    pub(super) ren: RenBuf,
    /// 可变全局表（create_global/change_mutable/get_global 的
    /// `mutable_map`；每轮清空——参考版 per-Infer 同款）。值
    /// 是 bump 句柄，跨轮前一切句柄已消亡。
    pub(super) mutable: RefCell<Mutable>,
    /// 求解 Stuck 挂账（参考版 `Infer.meta_contrains`）：unify_catch
    /// 入口/出口清空；flex 求解遇 Stuck 时压入。
    pub(super) constraints: Vec<(V, V)>,
    /// eval / quote / unify 的可复用工作栈。`'static` 仅是**存放口径**：
    /// 进核前 clear，借出期间写入的当轮条目不跨调用存活——与 `conv` /
    /// `icits` 的「进核前 clear」纪律同款。`W`/`QJob`/`UItem` 均为无 Drop
    /// 的 Copy 枚举，`Vec` 布局与元素生命周期参数无关，出借时按当次
    /// 生命周期重写指针类型（SAFETY 见各包装方法）。
    pub(super) eval_work: Vec<W<'static>>,
    pub(super) quote_tasks: Vec<QJob<'static>>,
    pub(super) quote_done: Vec<&'static Tm<'static>>,
    pub(super) quote_work: Vec<W<'static>>,
    pub(super) unify_work: Vec<W<'static>>,
    /// unify 的 UItem 主工作栈（同上口径；`UItem::MatchBranch` 持
    /// `Rc`——失败早退留下的 Rc 随下次入口 clear 正确减计，非 Drop 项
    /// 是引用 Copy，'static 存放无析构风险）。
    pub(super) unify_stack: Vec<UItem<'static>>,
    /// quote 记忆化表：容量跨调用复用，内容**每次调用 clear**——meta 可
    /// 能在两次调用之间被求解，跨调用保留条目会拿到过期中性项。
    pub(super) quote_memo: QuoteMemo<'static>,
    /// trait 合成状态（每轮清空——参考版每次调用新建 Infer 的三表）。
    pub(super) tstate: TraitState,
    /// decl 键的末段倒排索引：`末段 -> 含该末段的完整 decl 键列表`（只收
    /// 含 `.` 的限定键）。Var 裸名解析的第 5 级 `.name` 后缀 fallback 旧实现
    /// 每 miss 一次全 decl 表 `ends_with` 扫描（O(D)/次，prelude-hdl 900+
    /// decl 时合计量级 ~秒），索引后 O(命中数)。登记点（fake_bind /
    /// decl_reg_in）增量维护；同键重复登记（fake 占位 → 真值覆盖）会产生
    /// 重复条目，查询侧 dedup。decls 只增不删，轮界 clear。
    decl_suffix_index: FxHashMap<SmolStr, Rc<Vec<SmolStr>>>,
    suffix_indexed_keys: FxHashSet<SmolStr>,
    /// `BindingName.mk` 的解析缓存（含 package 前缀的限定形态）。精确键
    /// 存在时各查询点本就走 O(1) contains_key；此缓存只加速「键带前缀」
    /// 的 `keys().find(ends_with)` 兜底——旧实现每次全表扫。首见即冻结
    /// （旧实现的 HashMap 迭代序本就任取一，语义面无差）。轮界 clear。
    binding_name_mk: Option<SmolStr>,
    /// namespace 方法键缓存（`(链头指针, 键集)`）：Var 后缀 fallback 的
    /// 排除集。链头指针在两次 namespace 登记之间稳定（bump 分配），缓存
    /// 命中即免每次 fallback 的全链重建（每方法一次 format! 分配，
    /// prelude-hdl 标识符密集 decl 单个数万次 fallback）。轮界 clear。
    pub(super) ns_method_cache: Option<(usize, FxHashSet<SmolStr>)>,
    /// Var 后缀回退的**解析结果 memo**：裸名 → 已解析结果。回退查询对同一
    /// 裸名是重读纯函数（候选桶 + 活过滤），合成负载与真实源里高频重复
    /// （struct 负载 `P.mk`/`zero` 各 1 次/decl、名字全部相同；match 负载的
    /// 构造子名同理），memo 命中免整桶扫描与四级过滤。
    ///
    /// 失效纪律（按失效源精确到条目）：
    /// * **桶内容变化 / 跨 kick 重新可见**——`index_decl_key` 在
    ///   `suffix_indexed_keys` 早退**之前**按桶名 `suffix_memo.remove(tail)`
    ///   精确弃用。**不能靠桶指针发现**：稳态下桶 `Rc` 的 refcount==1
    ///   （memo 只存裸指针、不持 `Rc`），`Rc::make_mut` 原地追加、地址不变；
    ///   且索引跨 kick 常驻而 decl 表每 kick 重建，同键重登记会早退。
    ///   两处漏弃都会让"先唯一解析、后候选可见"沿用旧结论（2026-09-22 修复，
    ///   回归用例 `parity_suffix_fallback_memo_invalidated_by_new_candidate`）。
    ///   指针纪元保留为兜底（轮界 `clear` 后新桶可能复用旧地址）。
    /// * **首段可见性翻转**（负结果专用）——负条目记填表时被"头不可见"
    ///   过滤掉的候选首段集；活检 `decls/namespaces` 可见性，任一转可见
    ///   即重查。正向条目不需要这条：候选能进 `cxt.decls` 必经过
    ///   `index_decl_key`，注册时已按桶名弃用该条目；`cxt.namespaces` 的变化
    ///   （package/import）走下面的版本纪元整表弃用。
    /// * **namespace 方法键集 / namespace 准入集变化**——`Package`/`Import`
    ///   登记与 state journal 回滚 bump `suffix_memo_version`，查询侧纪元
    ///   不符整表弃用。
    suffix_memo: FxHashMap<SmolStr, SuffixMemo>,
    suffix_memo_version: u64,
    /// memo 表当前所处的版本纪元（≠ version 即待清）
    suffix_memo_epoch: u64,
    /// trait 型 Unsolved meta 登记表（参考版 `Infer.trait_metas`）：
    /// `fresh_meta` 对 trait Sum 走此表，`solve_multi_trait` 只扫它。
    /// （每轮清空。）
    pub(super) trait_metas: Vec<u32>,
    /// 算符方法恢复表（参考版 `Infer.symbol_table`）：`(helper 名, 实参
    /// 个数) → 算符符号`，inherent impl 的算符名方法登记。export 的 Call
    /// 臂在此命中时产 `CTm::OpCall`。（每轮清空。）
    pub(super) symbol_table: FxHashMap<(SmolStr, usize), SmolStr>,
    /// 文件局部 import 别名（参考版 `Infer.import_map`，挂 Infer 不挂
    /// Cxt 以免跨文件泄漏）：alias → decl 全键。（每轮清空。）
    pub(super) import_map: FxHashMap<SmolStr, SmolStr>,
    /// trait 方法 elaboration 缓存（参考版 `Infer.trait_method_cache`；
    /// clone 时清空）：`(类型头, 方法名) → (导出项 Rc, twin Tm, twin V)`。
    /// Raw::Tm 的指针导入表随条目登记。（每轮清空。）
    pub(super) trait_method_cache: FxHashMap<(SmolStr, SmolStr), (Rc<CTm>, Rc<CVal>, Rc<CTm>)>,
    /// **指针导入表**：`export` / `v_to_ref_val` 产出的参考版 Rc 指针 →
    /// 本机 Tm/V。class Phase B 的 `Raw::Tm` 检查臂与 trait 方法缓存经此
    /// 取回本机结果（export 每次产出新 Rc，指针唯一；每轮清空——本轮
    /// bump 值跨轮消亡）。
    pub(super) tm_import: FxHashMap<usize, &'static Tm<'static>>,
    pub(super) val_import: FxHashMap<usize, V>,
    // ── 观察面（LSP 接线阶段 1，docs/lsp-twin-wiring-2026-09.md）──
    // 与参考版 `Infer` 同名表逐字段同契约（push 期渲染成 owned String；
    // bump 域 Tm 轮末即弃）。每轮 `clear_round` 清空，`run_decls` 返回后
    // 由 LSP 读取——本轮声明的本轮快照，与 bump 生命周期严格同界。
    pub(crate) hover_table: Vec<(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)>,
    pub(crate) completion_table: Vec<(crate::parser_lib::Span<()>, SmolStr)>,
    pub(crate) inlay_hint_table: Vec<(u32, String)>,
    /// println 输出（span + 渲染串）：孪生自产 INFORMATION 诊断用
    /// （参考版 `println_jobs` 的对位；每轮 `clear_round` 清空）。
    pub(crate) println_spans: Vec<(crate::parser_lib::Span<()>, String)>,
    /// HDL 自检警告行（decl 下标 + 原始行）：孪生自产 WARNING 诊断用——
    /// 下标记住归属 decl，LSP 侧按 `check_issue_span` 解析到信号 span
    /// （参考版 `take_fresh_check_issues` + `check_issue_span` 同口径）。
    /// 每轮 `clear_round` 清空。
    pub(crate) check_issue_lines: Vec<(usize, String)>,
    /// 构造子 hover 渲染缓存（`push_ctor_hover`，walk_pat Con 臂专用）：
    /// 构造子 hover 值是 decl 条目的闭合值，渲染与使用处上下文无关——同键
    /// 第二次起免 quote/export/pretty 全管线（match 负载实测每 Con 模式
    /// ~0.9µs，walk_pat 内最大单项）。只在渲染**无未解 meta** 时缓存
    /// （`push_hover_cached` 的 typ_pretty_final 同一保守线：meta 可能在
    /// 首见之后才求解，缓存串会把 `?N` 冻进使用处悬浮）。与观察表同纪律
    /// 每轮清空：decls 表轮界重建，跨轮保留只会白占内存。
    pub(super) ctor_hover_memo: FxHashMap<SmolStr, Rc<str>>,
    /// 观察面 push 总闸：prelude 装载段置 `false`（push 期渲染 + decl_reg
    /// 的 typ_pretty 渲染是本轮末 `clear_observation_tables` 要丢弃的纯死
    /// 工作——参考版 LSP 只在进程启动装一次 prelude，孪生每 kick 重放就
    /// 不应为被删的表条目付费），用户段恢复 `true`。默认 `true`——bench
    /// /run 口径维持与参考版同含渲染成本的对称口径。
    pub(super) observe: bool,
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
            mutable: RefCell::new(Mutable {
                map: FxHashMap::default(),
                replay: FxHashMap::default(),
                check_lines: Vec::new(),
                check_line_set: FxHashSet::default(),
                check_seen: FxHashSet::default(),
            }),
            constraints: Vec::new(),
            eval_work: Vec::new(),
            quote_tasks: Vec::new(),
            quote_done: Vec::new(),
            quote_work: Vec::new(),
            unify_work: Vec::new(),
            unify_stack: Vec::new(),
            quote_memo: FxHashMap::default(),
            tstate: TraitState::default(),
            decl_suffix_index: FxHashMap::default(),
            suffix_indexed_keys: FxHashSet::default(),
            binding_name_mk: None,
            ns_method_cache: None,
            suffix_memo: FxHashMap::default(),
            suffix_memo_version: 0,
            suffix_memo_epoch: 0,
            trait_metas: Vec::new(),
            symbol_table: FxHashMap::default(),
            import_map: FxHashMap::default(),
            trait_method_cache: FxHashMap::default(),
            tm_import: FxHashMap::default(),
            val_import: FxHashMap::default(),
            hover_table: Vec::new(),
            completion_table: Vec::new(),
            inlay_hint_table: Vec::new(),
            println_spans: Vec::new(),
            check_issue_lines: Vec::new(),
            ctor_hover_memo: FxHashMap::default(),
            observe: true,
        }
    }

    /// 每轮 reset：metacontext + 名字表/类型表/轨迹 + 环境区域 + 可变全局
    /// 表全部清空。spine 栈同轮清空（保容量，到阈值归还）——tag-2 句柄只
    /// 被当轮 bump 值 / metas / defs 持有，轮边界后无任何旧句柄可达。decl
    /// 表随 Cxt 快照消亡（参考版每次调用新建 Cxt 同款）。L13 增量：
    /// trait_metas / symbol_table / import_map / trait 方法缓存 / 指针导入
    /// 表 / 可变全局五件 / 后缀索引与 memo / 观察面六表一并清空（均为
    /// per-run 状态——参考版 Infer::clone 的重置面 + 新建 Infer），且全部
    /// 挂归还档（[`ReclaimOnClear`]：`TBL_SHRINK_MIN_ENTRIES` /
    /// `PTR_TBL_SHRINK_MIN_ENTRIES` / spine 档，逐表理由见各调用行注释）——
    /// mem-l13-opt §3.3 归档的第一/二组"清空不还桶"在此收口：阈值以上的
    /// 峰值容量不再常驻到进程结束（长会话 RSS），阈值以下照旧只 clear
    /// （稳态复用与分配计数零变化）。
    pub(super) fn clear_round(&mut self) {
        self.metas.clear();
        self.defs.clear();
        self.constraints.clear();
        // 压栈工作表的峰值容量同样常驻（`SPINE_SHRINK_MIN_ENTRIES`）。
        twin_stat_record(&TWIN_STAT_SPINE, self.spine.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES));
        // ── 第一组（per-run，参考版 Infer 重置面）归还档 ──
        // 可变全局五件：清空语义留在 prim.rs `Mutable::clear`（不动），这里
        // 叠加还桶（reclaim 内部的 clear 对已空表是 O(1) no-op）。map 槽
        // (SmolStr,V) ~38B / replay 槽 (SmolStr,bool) ~37B / check 行缓存槽
        // 24–32B（String 堆随 clear 已释放，还的是缓冲本体）。
        {
            let mut mu = self.mutable.borrow_mut();
            mu.clear();
            let _ = mu.map.reclaim(TBL_SHRINK_MIN_ENTRIES);
            let _ = mu.replay.reclaim(TBL_SHRINK_MIN_ENTRIES);
            let _ = mu.check_lines.reclaim(TBL_SHRINK_MIN_ENTRIES);
            let _ = mu.check_line_set.reclaim(TBL_SHRINK_MIN_ENTRIES);
            let _ = mu.check_seen.reclaim(TBL_SHRINK_MIN_ENTRIES);
        }
        // trait 合成状态整体换新：旧 `TraitState`（含三张 HashMap 的桶数组）
        // 随 drop 即刻归还——本就是"每轮新建"语义，无清空保容量问题，也正
        // 因此不存在跨轮峰值滞留。
        self.tstate = TraitState::default();
        // trait 型 meta 下标表：槽 4B（裸 u32），走工作栈档
        // （1<<16 × 4B ≈ 262KB）。
        let _ = self.trait_metas.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        // 算符方法恢复表：键 (SmolStr, usize)+值 SmolStr，槽 ~66B（≥1<<13
        // 条即 ~0.55MB 空桶，稳态峰值仅数十条——inherent impl 算符名）。
        let _ = self.symbol_table.reclaim(TBL_SHRINK_MIN_ENTRIES);
        // import 别名表：键值均 SmolStr，槽 ~29B；稳态 = 文件 import 数，
        // 数十条。
        let _ = self.import_map.reclaim(TBL_SHRINK_MIN_ENTRIES);
        // trait 方法 elaboration 缓存：键 (SmolStr, SmolStr)+值 3×Rc，槽
        // ~84B——本组最肥的空桶（1<<13 条 ≈ 0.7MB）；条目 keepalive 的 Rc
        // 堆随 clear 释放，这里归还桶数组。prelude-hdl 稳态千条级，低于阈值。
        let _ = self.trait_method_cache.reclaim(TBL_SHRINK_MIN_ENTRIES);
        // 指针导入表：键 usize + 值指针/V，槽 16–20B，水位 1<<15（≈0.65MB）；
        // 稳态 = 每轮 export 产出数，数百条级。
        let _ = self.tm_import.reclaim(PTR_TBL_SHRINK_MIN_ENTRIES);
        let _ = self.val_import.reclaim(PTR_TBL_SHRINK_MIN_ENTRIES);
        // ── 第二组（per-kick / 后缀回退面）归还档 ──
        // decl 后缀倒排索引与键集：mem-l13-opt §3.3 点名的 prelude-hdl 常驻
        // 项（900+ decl 限定键 → 桶数组数百 KB 常驻到进程结束）；值侧
        // `Rc<Vec<SmolStr>>` 堆随 clear 释放，这里还桶。稳态峰值数千条
        // （955 decl 的限定键），低于 1<<13——只有超阈文件（≥8k 限定键）
        // 触发归还，下一轮重建照旧。
        let _ = self.decl_suffix_index.reclaim(TBL_SHRINK_MIN_ENTRIES);
        let _ = self.suffix_indexed_keys.reclaim(TBL_SHRINK_MIN_ENTRIES);
        // 后缀回退 memo：条目 SuffixMemo 槽 ~40B（Neg 臂的 blocked_heads
        // Vec 堆随 clear 释放）；与 decl_suffix_index 同界清（版本号一并
        // 归零，纪元语义不变——表已空，首次查询的 epoch 对齐是 no-op）。
        let _ = self.suffix_memo.reclaim(TBL_SHRINK_MIN_ENTRIES);
        self.suffix_memo_version = 0;
        // `binding_name_mk` 是单个 `Option<SmolStr>`（≤23B 内联零堆）、
        // `ns_method_cache` 整体 drop（桶随 HashSet 析构归还）——两者本就
        // 无"清空保容量"问题，保持原写法。
        self.binding_name_mk = None;
        self.ns_method_cache = None;
        self.clear_observation_tables();
        self.reclaim_observation_tables();
    }

    /// 观察面六表的容量归还档（清空点在 [`Machine::clear_observation_tables`]/
    /// entry.rs，这里只按 [`TBL_SHRINK_MIN_ENTRIES`] 还桶）：五张 Vec 槽
    /// 32–40B（String 堆随 clear 已释放）+ `ctor_hover_memo` 槽 ~38B。
    /// 调用点：`clear_round` 每轮、`observe_user` 每 kick 开、prime /
    /// run_decls_with_prelude 的装载收尾——均已是观察表的轮界/ kick 界，
    /// 只改清空的写法不动时机（[`ReclaimOnClear`] 同款纪律）。
    pub(super) fn reclaim_observation_tables(&mut self) {
        let _ = self.hover_table.reclaim(OBS_TBL_SHRINK_MIN_ENTRIES);
        let _ = self.completion_table.reclaim(OBS_TBL_SHRINK_MIN_ENTRIES);
        let _ = self.inlay_hint_table.reclaim(OBS_TBL_SHRINK_MIN_ENTRIES);
        let _ = self.println_spans.reclaim(OBS_TBL_SHRINK_MIN_ENTRIES);
        let _ = self.check_issue_lines.reclaim(OBS_TBL_SHRINK_MIN_ENTRIES);
        let _ = self.ctor_hover_memo.reclaim(OBS_TBL_SHRINK_MIN_ENTRIES);
    }

    // Extend Cxt（源码 binder / inserted binder / define / fake_bind）
    // --------------------------------------------------------------------------------

    /// Extend Cxt with a bound variable（源码 binder）。
    pub(super) fn bind_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        b_span: crate::parser_lib::Span<()>,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, (ty, b_span));
        let env = env_ext(bump, cxt.env, v_lvl(cxt.lvl));
        Cxt {
            env,
            update_from: cxt.update_from,
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
            decls: cxt.decls.clone(),
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            // 参考版 `bind`：进入新 binder 域，绑定名清空
            binding_name: None,
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
            update_from: cxt.update_from,
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
            decls: cxt.decls.clone(),
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: None,
        }
    }

    /// Extend Cxt with a definition（pruning 记 `None`、telescope 记 Define
    /// 槽）。
    fn define_name<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        b_span: crate::parser_lib::Span<()>,
        a_t: &'a Tm<'a>,
        t_t: &'a Tm<'a>,
        val: V,
        ty: V,
    ) -> Cxt<'a> {
        let mut names = (*cxt.names).clone();
        names.by_name.insert(SmolStr::new(x), cxt.lvl);
        names.by_lvl.insert(cxt.lvl, (ty, b_span));
        let env = env_ext_defs(bump, &mut self.defs, cxt.env, val);
        Cxt {
            env,
            update_from: cxt.update_from,
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
            decls: cxt.decls.clone(),
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            // 参考版 `define`：let 续体仍在同一绑定上下文，绑定名保留
            binding_name: cxt.binding_name.clone(),
        }
    }

    /// fake_bind（参考版 `Cxt::fake_bind`）：递归 def 的占位——decl 表插入
    /// `Decl(name)` 存根条目（tm/val 都是名字自引用），**撞名（含内建）
    /// 即 `redefine {name}`**；env/lvl/locals/pruning/names 一概不动。
    fn fake_bind<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
        x: &str,
        span: crate::parser_lib::Span<()>,
        a_t: &'a Tm<'a>,
        ty: V,
    ) -> Result<Cxt<'a>, Error> {
        // 就地 COW（2026-09-12）：cxt 独占 decls 快照（强计数 1，顺序 decl
        // 路径恒成立）时 make_mut 原地插存根，替代旧的先克隆整表再写——
        // 大 decl 数负载上每 def O(D) 克隆实测 O(D²)；有别的快照观察者时
        // make_mut 自动回退深拷贝，隔离语义与旧实现逐字一致。decl_reg 随
        // 后以真值静默覆盖同名条目；调用方需先 drop(fake) 释放 Rc 引用。
        let name = bump.alloc_str(x);
        let stub = bump.alloc(Tm::Decl(name));
        let prev = Rc::make_mut(&mut cxt.decls).insert(
            SmolStr::new(x),
            DeclEntry {
                span,
                typ_pretty: None,
                typ_pretty_final: false,
                tm: stub,
                ty: a_t,
                val: v_xcell(bump.alloc(XCell::Decl { name })),
                vty: ty,
                prim: None,
            },
        );
        if prev.is_some() {
            return Err(Error(span.map(|_| format!("redefine {}", x)), vec![]));
        }
        self.index_decl_key(x);
        Ok(clone_cxt(cxt))
    }

    /// Var 后缀 fallback 的 namespace 方法键集（按链头指针缓存）——与
    /// 「现场沿 `cxt.namespace` 链重建」逐字同集，链头不变时 O(1)。
    /// [`Self::ns_method_keys_for`] 的成员查询版：缓存命中时免克隆整表
    /// （查询侧原 clone FxHashSet → std HashSet 两头重建，缓存被抵消）。
    fn ns_is_method_key(&mut self, head: Option<&NsCons<'_>>, key: &SmolStr) -> bool {
        let key_ptr = head.map(|n| n as *const _ as usize).unwrap_or(0);
        if self
            .ns_method_cache
            .as_ref()
            .map_or(true, |(k, _)| *k != key_ptr)
        {
            let mut set = FxHashSet::default();
            let mut cur = head;
            while let Some(ns) = cur {
                for m in ns.methods.iter() {
                    set.insert(SmolStr::new(format!("{}.{}", ns.type_name, m)));
                }
                cur = ns.next;
            }
            self.ns_method_cache = Some((key_ptr, set));
        }
        self.ns_method_cache
            .as_ref()
            .map_or(false, |(_, s)| s.contains(key.as_str()))
    }

    fn ns_method_keys_for(&mut self, head: Option<&NsCons<'_>>) -> FxHashSet<SmolStr> {
        let key = head.map(|n| n as *const _ as usize).unwrap_or(0);
        if self
            .ns_method_cache
            .as_ref()
            .map_or(true, |(k, _)| *k != key)
        {
            let mut set = FxHashSet::default();
            let mut cur = head;
            while let Some(ns) = cur {
                for m in ns.methods.iter() {
                    set.insert(SmolStr::new(format!("{}.{}", ns.type_name, m)));
                }
                cur = ns.next;
            }
            self.ns_method_cache = Some((key, set));
        }
        self.ns_method_cache.as_ref().unwrap().1.clone()
    }

    /// 后缀桶当前指针（桶只在 `Rc::make_mut` 实插时换地址；缺席 = 0）。
    /// memo 条目的桶纪元比对用——见 [`Machine::suffix_memo`] 注释。
    fn suffix_bucket_ptr(&self, tail: &str) -> usize {
        self.decl_suffix_index
            .get(tail)
            .map(|rc| Rc::as_ptr(rc) as usize)
            .unwrap_or(0)
    }

    /// decl 登记点共用的索引/缓存维护：末段倒排索引（Var 后缀 fallback 用）
    /// 与 BindingName.mk 解析缓存。同键重复登记（fake 占位 → 真值覆盖）会
    /// 在索引里留重复条目，查询侧 dedup。
    ///
    /// 索引键 = 被查名字的**每个点分尾缀**（`Core.Add.mk` 同时入
    /// `Add.mk` 与 `mk` 两个桶）：fallback 匹配 `k.ends_with(".{name}")`，
    /// 多段键可被较短尾缀命中，只按末段建桶会漏（实测 prelude-hdl
    /// `Add.mk` 解析失败的回归）。
    fn index_decl_key(&mut self, key: &str) {
        // 后缀回退 memo 的**内容失效**，与"索引是否实插"无关——必须早于下面
        // 的 `suffix_indexed_keys` 早退：
        //  1) 本键的每个点分尾缀桶新增了一个候选；稳态下桶 refcount==1
        //     （memo 只存裸指针、不持 `Rc`），`Rc::make_mut` 原地追加、地址
        //     不变，指针纪元看不见这次新增；
        //  2) **跨 kick**：索引常驻（prime 段建的 prelude 桶必须留用），而
        //     decl 表每 kick 从检查点重建 → 同键重登记走早退，但该键在本轮
        //     `cxt` 里是**新可见**的；memo 里可能存着"它还没可见时"填的唯一
        //     命中（LSP 常驻路径实测：kick 0 正确报 ambiguous，kick 1 静默
        //     解析回 A.foo）。
        for (i, b) in key.char_indices() {
            if b == '.' {
                self.suffix_memo.remove(&key[i + 1..]);
            }
        }
        // 同键重复登记（fake 占位→真值覆盖）只索引一次——查询侧原
        // sort+dedup 每 miss 整桶复制重排 O(n log n)，责任移到写入侧
        // 一次 O(1) 查集。集合随 decl_suffix_index 同界清空。
        if !self.suffix_indexed_keys.insert(SmolStr::new(key)) {
            return;
        }
        for (i, b) in key.char_indices() {
            if b == '.' {
                let e = self
                    .decl_suffix_index
                    .entry(SmolStr::new(&key[i + 1..]))
                    .or_default();
                Rc::make_mut(e).push(SmolStr::new(key));
            }
        }
        if key == "BindingName.mk" {
            self.binding_name_mk = Some(SmolStr::new(key));
        } else if key.ends_with(".BindingName.mk") && self.binding_name_mk.is_none() {
            self.binding_name_mk = Some(SmolStr::new(key));
        }
    }

    /// 登记处类型渲染（push_hover 同管线：`quote → export → pretty_tm`，
    /// observe 门控同款——prelude 装载段总闸下不渲染）。Def 臂以
    /// `Rc` 共享给 push_hover 与 decl_reg_in，一次渲染两处消费
    /// （评审机会 4）。
    fn render_typ_pretty<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        vtyp: V,
    ) -> Option<(Rc<String>, bool)> {
        if !self.observe {
            return None;
        }
        Some( {
            let qt = self.quote(bump, cxt, cxt.lvl, vtyp);
            // final = 引出项无未解 meta——此时渲染串与使用处实时渲染逐字节
            // 一致（meta 后续求解不再改变形态），push_hover_cached 可安全
            // 复用（评审 B#1：prelude-hdl 使用处 hover 实时渲染 ~10% 观察
            // 面开销的大头）。
            let typ_pretty_final = no_metas(bump, self, cxt, qt).is_none();
            let qn = types_names_list(cxt.types);
            (Rc::new(pretty_tm(0, qn, &export(&self.symbol_table, qt))), typ_pretty_final)
        })
    }

    /// 声明登记（参考版 `Cxt::decl`）：**静默覆盖**（参考版 redefine 检查
    /// 被注释）——fake_bind 之后以真值覆盖存根。prim-ness 翻转在快版无
    /// force memo，无需 PRIM_VERSION。
    ///
    /// `typ_pretty`：调用方已渲染的类型串（Def 臂与 push_hover 共享一次
    /// 渲染，评审机会 4）；`None` = 登记处自渲染（observe 门控，Enum 臂
    /// 同旧行为）。
    fn decl_reg_in<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
        x: &str,
        span: crate::parser_lib::Span<()>,
        t_tm: &'a Tm<'a>,
        vt: V,
        typ_tm: &'a Tm<'a>,
        vtyp: V,
        prim: Option<PrimId>,
        typ_pretty: Option<(Rc<String>, bool)>,
    ) -> Cxt<'a> {
        // 就地 COW（2026-09-12，论证见 [`Self::fake_bind`]）：独占时原地
        // 写 O(1)；observe 渲染保持 decl_reg 同款条件。
        let (typ_pretty, typ_pretty_final) = match typ_pretty {
            Some((s, f)) => (Some(s), f),
            None => match self.render_typ_pretty(bump, cxt, vtyp) {
                Some((s, f)) => (Some(s), f),
                None => (None, false),
            },
        };
        Rc::make_mut(&mut cxt.decls).insert(
            SmolStr::new(x),
            DeclEntry {
                span,
                typ_pretty,
                typ_pretty_final,
                tm: t_tm,
                ty: typ_tm,
                val: vt,
                vty: vtyp,
                prim,
            },
        );
        self.index_decl_key(x);
        clone_cxt(cxt)
    }

    /// 声明登记（参考版 `Cxt::decl`）：**静默覆盖**（参考版 redefine 检查
    /// 被注释）——fake_bind 之后以真值覆盖存根。prim-ness 翻转在快版无
    /// force memo，无需 PRIM_VERSION。
    pub(super) fn decl_reg<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: &str,
        span: crate::parser_lib::Span<()>,
        t_tm: &'a Tm<'a>,
        vt: V,
        typ_tm: &'a Tm<'a>,
        vtyp: V,
        prim: Option<PrimId>,
    ) -> Cxt<'a> {
        let mut decls = cxt.decls.clone();
        // prim-ness 变化会让 force 对同名链的结果改变（Decl 臂走不走 prim
        // 执行）→ 版本号 bump，旧 memo 条目惰性失效（参考版 Cxt::decl 同款）
        let had_prim = decls.get(x).map(|e| e.prim.is_some()).unwrap_or(false);
        // 登记处渲染类型一次（每 decl 一次 quote→export→pretty）。消费方
        // 是 LSP def-site 悬浮（参考版 Path1 直读 decl 行 typ_pretty）；
        // 使用处悬浮是实时渲染（push_hover_cached），不读此串。prelude 装
        // 载段 observe=false 跳过渲染（每 kick 重放时这段是表清空前的死
        // 工作；参考版 LSP 只在进程启动装一次）。
        let (typ_pretty, typ_pretty_final) = if self.observe {
             {
                let qt = self.quote(bump, cxt, cxt.lvl, vtyp);
                let no_meta = no_metas(bump, self, cxt, qt).is_none();
                let qn = types_names_list(cxt.types);
                (Some(Rc::new(pretty_tm(0, qn, &export(&self.symbol_table, qt)))), no_meta)
            }
        } else {
            (None, false)
        };
        Rc::make_mut(&mut decls).insert(
            SmolStr::new(x),
            DeclEntry {
                span,
                typ_pretty,
                typ_pretty_final,
                tm: t_tm,
                ty: typ_tm,
                val: vt,
                vty: vtyp,
                prim,
            },
        );
        if had_prim != prim.is_some() {
            prim_version_bump();
        }
        Cxt {
            env: cxt.env,
            update_from: cxt.update_from,
            names: cxt.names.clone(),
            types: cxt.types,
            locals: cxt.locals,
            pruning: cxt.pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
            decls,
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: cxt.binding_name.clone(),
        }
    }

    /// 追加未解条目（参考版 `new_meta(a, cxt, origin_typ)`）：上下文快照
    /// 存 lvl + names telescope + decls（'static 存放口径，两步入 'a）。
    fn new_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V, origin_typ: V) -> u32 {
        let _ = bump;
        let snap: Rc<MetaSnap<'static>> = unsafe {
            std::mem::transmute(Rc::new(MetaSnap {
                lvl: cxt.lvl,
                types: cxt.types,
                decls: cxt.decls.clone(),
                // 完整上下文快照（参考版 Arc<Cxt> 第二元）：solve_multi_trait
                // 用它求解，而不是调用方的 cxt。
                cxt: std::mem::transmute::<Cxt<'a>, Cxt<'static>>(clone_cxt(cxt)),
            }))
        };
        self.metas.push(MetaEntry::Unsolved(a, snap, origin_typ, empty_span(())));
        self.metas.len() as u32 - 1
    }

    /// 挂新洞（上游 `freshMeta`）：物化闭类型、追加未解条目，产出
    /// `AppPruning ?m (cxt.pruning)`。快捷（L05 三级 + tag 6）：
    /// **`binds == 0`** 时常值类型（U / 裸未解 meta / LiteralType，tag
    /// 3/5/6）闭类型恒等；`quote` 无自由变量则跳过 Let 链直接空环境求值；
    /// 否则全构造（与参考版同形）。L13：trait Sum 的 meta 进 `trait_metas`
    /// 登记表（solve_multi_trait 只扫它）。
    ///
    /// **L05-L08 的 bind-prefix 快路径（`bind_prefix_of_telescope` + define
    /// 槽由 `cxt.env` 快照供给）在 L09 起刻意不移植**：那条路径要求
    /// "telescope 里 define 槽的项 ≡ env 快照里的值"。L05-L08 的模式特化走
    /// pm_defs（只追加等式，快照恒成立）；L09 起改走参考版
    /// `Cxt::update_cxt`——精化就地改写 env 槽再 refresh 重锚定，而
    /// `locals` 照参考版保持陈旧（参考版 cxt.rs 里
    /// `locals: self.locals.clone()` 的 TODO），全 close 正是靠这份陈旧项
    /// 与参考版逐值同轨。改读快照会拿到精化后的值：孪生的契约是与参考版
    /// Ok 输出逐字节一致，不是比参考版更正确。
    pub(super) fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {

        // L10：trait 类型先试实例合成（成功 → 直接给实例项）；
        // trait Sum → 裸 Meta（无 AppPruning 掩码）
        if let Ok(Some((tm, _))) = self.solve_trait_ref(bump, cxt, a, false) {
            return tm;
        }
        let is_trait_sum = v_tag(a) == 7
            && match v_xcell_of(a) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if is_trait_sum {
            let m = self.new_meta(bump, cxt, a, a);
            self.trait_metas.push(m);
            return bump.alloc(Tm::Meta(m));
        }
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt, cxt.lvl, a);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, cxt, EMPTY_ENV, q)
            } else {
                let closed = self.close_tm(bump, cxt.locals, q);
                self.eval(bump, cxt, EMPTY_ENV, closed)
            }
        };
        let m = self.new_meta(bump, cxt, mty, a);
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
    pub(super) fn eval_fresh(&mut self, bump: &Bump, cxt: &Cxt<'_>, env: Env<'_>, m: &Tm<'_>) -> V {
        if let Tm::AppPruning(head, pr) = m {
            // 头必须是裸 Meta 才有短路意义
            if let Tm::Meta(mm) = head {
                if pr.map_or(true, |p| p.slot.is_none() && p.after_run.is_none()) {
                    return v_meta(*mm);
                }
            }
        }
        self.eval(bump, cxt, env, m)
    }

    // 内核包装（Machine 字段借出）
    // --------------------------------------------------------------------------------

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn eval<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, env: Env<'a>, tm: &'a Tm<'a>) -> V {
        super::prof_count(&super::FUNC_PROF.eval.1);
        #[cfg(feature = "sampler")]
        crate::sampler::tick();

        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
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
            bump, spine, work, vals, icits, defs, metas, &*cxt.decls, mutable, env, tm,
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn quote<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, level: u32, v: V) -> &'a Tm<'a> {
        super::prof_count(&super::FUNC_PROF.quote.1);
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
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
            &*cxt.decls,
            mutable,
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
    pub(super) fn quote_memo<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, level: u32, v: V) -> &'a Tm<'a> {
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
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
        // 清空保容量（表随 Machine 常驻），容量到阈值时顺带归还。
        twin_stat_record(&TWIN_STAT_QUOTE, memo.reclaim(CACHE_SHRINK_MIN_ENTRIES));
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
            &*cxt.decls,
            mutable,
            level,
            v,
            Some(&mut *memo),
        )
    }

    // 'static → 'a 的两步指针转换是刻意的一生期重写（SAFETY 见方法体），
    // clippy 在其类型显示里塌缩生命周期参数会误报 unnecessary_cast
    #[allow(clippy::unnecessary_cast)]
    pub(super) fn unify<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        l: u32,
        t: V,
        u: V,
        fuel: u32,
        trait_err: &mut Option<String>,
    ) -> bool {
        super::prof_count(&super::FUNC_PROF.unify.1);
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        // 先取裸指针再解构字段（避免 &mut self 与字段借用的叠加）
        let mach_ptr: *mut Machine = self;
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            mutable,
            ren,
            conv,
                        constraints,
            unify_work,
            unify_stack,
            ..
        } = self;
        // SAFETY：同 eval_work——'static 存放口径，进核前 clear。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        let stack: &mut Vec<UItem<'a>> =
            unsafe { &mut *(unify_stack as *mut Vec<UItem<'static>> as *mut Vec<UItem<'a>>) };
        work.clear();
        // **不能**在这里无条件 `stack.clear()`：`unify_iter` 允许嵌套重入
        // （flex 求解 → `solve_multi_trait_ref` → 候选实例合成 → 再次
        // unify），而 `unify_stack` 是 Machine 常驻的**共享**工作栈。嵌套
        // 调用若清空它，外层尚未弹出的待办对（同一 Sum/Sum 或同头链臂压入
        // 的其余参数对）会被静默丢弃——外层主循环见栈空即 `return true`，
        // 症状是"判定成功但 meta 未解"：`Eq ?x ?y ≡ Eq (7, 7)` 只解掉第一个
        // 参数 `A`（解它会触发 trait 合成 → 嵌套 unify → 清栈），随后
        // `?x ?y` 悬空（examples/theorem_proving 的 `cong` 隐参分叉）。
        // 改为入口暂存：成功时内层栈必已空（主循环以空栈结束），把调用方
        // 挂起的项原样放回，嵌套调用得以续跑；失败时丢弃（旧契约：残留由
        // 下次入口自行清理，不跨调用持有）。
        // （重入句柄 mach_ptr 在解构前取得：unify 的 flex 求解点要回调
        // trait 求解——参考版 solve 臂的 solve_multi_trait；字段已按不相交
        // 集合借出，重入经裸指针走 Machine 方法，仅触碰同分配的堆内容。）
        // 重入保护：外层尚未弹出的待办对要先暂存出来（内层 success 时栈必空，
        // 主循环以空栈结束）。**只在非空时 take**——非重入入口若也 take，
        //  field 里的 buffer 被挪进局部量、内层从 0 重新长，成功路径再整体
        // 换回去就把长大的 buffer 丢掉了（下次调用重放 4→8→16 的整段增长）。
        // 非空才 take 让"上次长大的空 buffer"留在 field 里被内层直接续用。
        let mut saved = Vec::new();
        if !stack.is_empty() {
            saved = std::mem::take(stack);
        }
        let r = unify_iter(
            bump, spine, work, stack, vals, icits, defs, metas, &*cxt.decls, mutable, ren, conv,
            constraints, l, t, u, fuel, cxt, mach_ptr, trait_err,
        );
        if r {
            if stack.is_empty() {
                // 外层挂起项原样放回；field 里已是本层长大的 buffer（空），
                // 直接留给下次调用续用，不重新分配。
                if !saved.is_empty() {
                    let mut s = saved;
                    stack.append(&mut s);
                }
            } else {
                // 非预期残留（成功却非空）：照旧整体替换，语义对齐旧行为。
                *stack = saved;
            }
        } else {
            stack.clear();
        }
        r
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表；快版导出项
    /// 的 Span 全零，消息内容与参考版同构）。入口/出口清空约束挂账；非空
    /// 即"can't unify for unsolved meta"（参考版同款两段文案）。
    pub(super) fn unify_catch<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
        span: crate::parser_lib::Span<()>,
    ) -> Result<(), Error> {

        let mut trait_err: Option<String> = None;
        self.constraints.clear();
        let ok = self.unify(bump, cxt, cxt.lvl, t, t_prime, 100, &mut trait_err);
        if ok && !self.constraints.is_empty() {
            let tq0 = self.quote(bump, cxt, cxt.lvl, t);
            let uq0 = self.quote(bump, cxt, cxt.lvl, t_prime);
            let tq = export(&self.symbol_table, tq0);
            let uq = export(&self.symbol_table, uq0);
            let names = types_names_list(cxt.types);
            let msg = format!(
                "can't unify for unsolved meta\n  expected: {}\n      find: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            );
            self.constraints.clear();
            return Err(Error(span.map(|_| msg.clone()), vec![]));
        }
        self.constraints.clear();
        if ok {
            Ok(())
        } else {
            if let Some(e) = trait_err {
                return Err(Error(span.map(|_| e.clone()), vec![]));
            }
            let tq0 = self.quote(bump, cxt, cxt.lvl, t);
            let uq0 = self.quote(bump, cxt, cxt.lvl, t_prime);
            let tq = export(&self.symbol_table, tq0);
            let uq = export(&self.symbol_table, uq0);
            let names = types_names_list(cxt.types);
            let msg = format!(
                "can't unify\n  expected: {}\n      find: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            );
            Err(Error(span.map(|_| msg.clone()), vec![]))
        }
    }

    /// 参数表逐个 force（solve_trait_ref 的多次收集点共用）。
    pub(super) fn force_list<'a>(&mut self, bump: &'a Bump, decl: &Decls<'a>, vals: &[V]) -> Vec<V> {
        let Machine {
            spine,
            defs,
            metas,
            mutable,
            ..
        } = self;
        vals.iter().map(|&v| force(bump, spine, defs, metas, decl, mutable, v)).collect()
    }

    /// 指针导入表取回本机 Tm（export 登记的 Rc 指针 → 本轮 bump 项）。
    /// miss = 内部错误（Phase A / trait 方法缓存必须先登记）。
    fn tm_import_lookup<'a>(&self, rc: &Rc<CTm>) -> &'a Tm<'a> {
        let key = Rc::as_ptr(rc) as usize;
        match self.tm_import.get(&key) {
            Some(t) => unsafe { &*(*t as *const Tm<'static> as *const Tm<'a>) },
            None => panic!("tm_import miss: prechecked term not registered"),
        }
    }

    /// 指针导入表取回本机 V（v_to_ref_val 登记的 Rc 指针 → 本机值）。
    fn val_import_lookup(&self, rc: &Rc<CVal>) -> V {
        let key = Rc::as_ptr(rc) as usize;
        *self
            .val_import
            .get(&key)
            .expect("val_import miss: prechecked type not registered")
    }

    /// 值是否是 `BindingName` 类型（参考版 `is_binding_name_type`：Sum 名
    /// 相等，或卡住的**空 spine** Decl 同名——链形态不算，参考版同款）。
    fn is_binding_name_type(&mut self, bump: &Bump, cxt: &Cxt<'_>, a: V) -> bool {
        let a_f = self.force_v(bump, cxt, a);
        match v_tag(a_f) {
            7 => match v_xcell_of(a_f) {
                XCell::Sum { name: "BindingName", .. } => true,
                XCell::Decl { name } => *name == "BindingName",
                _ => false,
            },
            _ => false,
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β——分配一律落本轮 bump）。
    pub(super) fn force_v(&mut self, bump: &Bump, cxt: &Cxt<'_>, v: V) -> V {
        let Machine {
            spine,
            defs,
            metas,
            mutable,
            ..
        } = self;        force(bump, spine, defs, metas, &*cxt.decls, mutable, v)
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
        let va = self.force_v(bump, cxt, va);
        if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
            let p = v_pi_of(va);
            // BindingName 特例（参考版 insert_go 207-232）：隐式参数类型是
            // BindingName 时，以当前绑定名自动合成实参（`BindingName.mk
            // "名字"`）
            if self.is_binding_name_type(bump, cxt, p.dom) {
                let name_str =
                    cxt.binding_name.clone().unwrap_or_else(|| SmolStr::new(""));
                let mk_key = if cxt.decls.contains_key("BindingName.mk") {
                    "BindingName.mk".to_string()
                } else {
                    // 带 package 前缀的限定键：从登记期缓存取（旧实现每次
                    // 全表 keys().find 扫描 O(D)；首见冻结与 HashMap 迭代序
                    // 任取一语义等价）
                    self.binding_name_mk
                        .clone()
                        .unwrap_or_else(|| SmolStr::new("BindingName.mk"))
                        .to_string()
                };
                let bn_tm = bump.alloc(Tm::App(
                    bump.alloc(Tm::Decl(bump.alloc_str(&mk_key))),
                    bump.alloc(Tm::LiteralIntro(bump.alloc_str(&name_str))),
                    Icit::Expl,
                ));
                let bn_val = self.eval(bump, cxt, cxt.env, bn_tm);
                let b = {
                    let env = env_ext(bump, p.env, bn_val);
                    self.eval(bump, cxt, env, p.body)
                };
                let t2 = bump.alloc(Tm::App(t, bn_tm, Icit::Impl));
                return self.insert_go(bump, cxt, t2, b);
            }
            let m = self.fresh_meta(bump, cxt, p.dom);
            let mv = self.eval_fresh(bump, cxt, cxt.env, m);
            let b = {
                let env = env_ext(bump, p.env, mv);
                self.eval(bump, cxt, env, p.body)
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
    pub(super) fn insert<'a>(
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
            let forced = self.force_v(bump, cxt, va);
            va = forced;
            if v_tag(va) == 4 && v_pi_of(va).icit == Icit::Impl {
                let p = v_pi_of(va);
                if p.name == name {
                    return Ok((t, va));
                }
                let m = self.fresh_meta(bump, cxt, p.dom);
                let mv = self.eval_fresh(bump, cxt, cxt.env, m);
                let b = {
                    let env = env_ext(bump, p.env, mv);
                    self.eval(bump, cxt, env, p.body)
                };
                t = bump.alloc(Tm::App(t, m, Icit::Impl));
                va = b;
            } else {
                return Err(Error(empty_span(format!("no named implicit arg {}", name)), vec![]));
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
        super::prof_count(&super::FUNC_PROF.check.1);
        #[cfg(feature = "sampler")]
        crate::sampler::tick();

        // force 期望类型后分派（已解 meta 可能展开成 Pi）
        let a = self.force_v(bump, cxt, a);
        // 预检查值（class Phase-B / trait 方法缓存复用——参考版 check 的
        // Raw::Tm 臂 649-666）：eval 驱动副作用（模块树全局）与良构性；
        // 未注解字段（期望是 fresh meta）**直解** meta := Phase-A 类型（整
        // unify 的 flex_flex 会重建闭包链产生幻影解，参考版注释）；注解
        // 复验走 unify_catch。内层值不重复 elaboration——经指针导入表取回。
        if let Raw::Tm(rc_tm, rc_ty) = t {
            let tm: &'a Tm<'a> = self.tm_import_lookup(rc_tm);
            let ty = self.val_import_lookup(rc_ty);
            {
                let _ = self.eval(bump, cxt, cxt.env, tm);
            }
            match v_tag(a) {
                5 => {
                    let m = v_meta_of(a);
                    // 空 spine 未解 meta：直解（meta 类型保留在第二元）
                    let mty = match &self.metas[m as usize] {
                        MetaEntry::Unsolved(v, ..) => *v,
                        _ => unreachable!(),
                    };
                    journal_meta(&mut self.metas, m as usize, MetaEntry::Solved(ty, mty));
                }
                _ => {
                    self.unify_catch(bump, cxt, a, ty, t.to_span())?;
                }
            }
            return Ok(tm);
        }
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
                        self.eval(bump, cxt, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt, cxt.lvl, p.dom);
                    // 不 push binder 定义处 hover——参考版 check 的 Lam 臂没有
                    // push（接线文档旧表的"742"实为 **let** 臂；def 参数折叠
                    // 成 λ 会经过这里，推了参考版没有的条目——实测见
                    // prelude_full_observation_tables_match_reference）。局部
                    // 变量的 hover 在使用处 Var 臂推（binder span 由
                    // Names.by_lvl 携带）。
                    let cxt2 = self.bind_name(bump, cxt, &x.data, x.to_span(), a_t, p.dom);
                    let body = self.check(bump, &cxt2, tbody, body_a)?;
                    Ok(bump.alloc(Tm::Lam(name, p.icit, body)))
                } else if p.icit == Icit::Impl {
                    // 检查到隐式 Π：补 inserted binder（Pi 侧名字，源码
                    // 不可见），整个项对余定义域重检
                    let name: &'a str = bump.alloc_str(p.name);
                    let body_a = {
                        let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                        self.eval(bump, cxt, env, p.body)
                    };
                    let a_t = self.quote(bump, cxt, cxt.lvl, p.dom);
                    let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
                    let body = self.check(bump, &cxt2, t, body_a)?;
                    Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
                } else {
                    // 显式 Π 上的 icit 失配：回落 general
                    let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                    let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                    self.unify_catch(bump, cxt, a, tty, t.to_span())?;
                    Ok(t2)
                }
            } else {
                let (t2, tty) = self.infer_expr(bump, cxt, t)?;
                let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
                self.unify_catch(bump, cxt, a, tty, t.to_span())?;
                Ok(t2)
            }
        } else if v_tag(a) == 4 && v_pi_of(a).icit == Icit::Impl {
            // 非 lambda 项检查到隐式 Π：插入隐式 binder
            let p = v_pi_of(a);
            let name: &'a str = bump.alloc_str(p.name);
            let body_a = {
                let env = env_ext(bump, p.env, v_lvl(cxt.lvl));
                self.eval(bump, cxt, env, p.body)
            };
            let a_t = self.quote(bump, cxt, cxt.lvl, p.dom);
            let cxt2 = self.new_binder(bump, cxt, p.name, a_t, p.dom);
            let body = self.check(bump, &cxt2, t, body_a)?;
            Ok(bump.alloc(Tm::Lam(name, Icit::Impl, body)))
        } else if let Raw::Let(x, a_ty, t2, u2) = t {
            // Raw::Tm 注解：指针导入表直取（参考版同款）
            let (a_tm, va) = if let Raw::Tm(rc_tm, rc_ty) = a_ty.as_ref() {
                let tm: &'a Tm<'a> = self.tm_import_lookup(rc_tm);
                let v = self.val_import_lookup(rc_ty);
                (tm, v)
            } else {
                let (a_tm, _) = self.check_universe(bump, cxt, a_ty)?;
                let va = self.eval(bump, cxt, cxt.env, a_tm);
                (a_tm, va)
            };
            // 绑定名（隐式 BindingName 参数合成）
            let cxt_named = cxt.with_binding_name(x.data.clone());
            let t_tm = self.check(bump, &cxt_named, t2, va)?;
            let vt = self.eval(bump, &cxt, cxt.env, t_tm);
            let name: &'a str = bump.alloc_str(&x.data);
            // 观察面：**检查路径** let binder 定义处 hover（参考版 check 的
            // Let 臂 742 同点位——接线旧文档误归为"Lam 臂"；推断路径的
            // 同款 push 在 infer_expr 的 Let 臂）
            self.push_hover(bump, cxt, x.to_span(), x.to_span(), va);
            let cxt2 = self.define_name(bump, cxt, &x.data, x.to_span(), a_tm, t_tm, vt, va);
            let u_tm = self.check(bump, &cxt2, u2, a)?;
            Ok(bump.alloc(Tm::Let(name, a_tm, t_tm, u_tm)))
        } else if let Raw::Hole(_) = t {
            // hole：以 fresh meta 填充（类型 = 期望类型）
            Ok(self.fresh_meta(bump, cxt, a))
        } else if let Raw::Match(expr, clauses) = t {
            // match：编译（特化合一在编译期完成）+ 逐分支检查
            let expr_span = expr.to_span();
            let (tm, typ) = self.infer_expr(bump, cxt, expr)?;
            let target = self.eval(bump, cxt, cxt.env, tm);
            let mut compiler = Compiler::new(a);
            compiler.compile(self, bump, typ, clauses, cxt, target)?;
            if !compiler.warnings.is_empty() {
                // 参考版同款：warnings 以 Display 逐条 join("; ") 作错误文案
                //（原为 Debug 形式，与参考版文案分叉）
                let msg = compiler
                    .warnings
                    .iter()
                    .map(|w| w.to_string())
                    .collect::<Vec<_>>()
                    .join("; ");
                return Err(Error(expr_span.map(|_| msg.clone()), vec![]));
            }
            let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                bump.alloc_slice_fill_iter(compiler.pats.into_iter());
            Ok(bump.alloc(Tm::Match(tm, cs)))
        } else {
            let (t2, tty) = self.infer_expr(bump, cxt, t)?;
            let (t2, tty) = self.insert(bump, cxt, t2, tty)?;
            self.unify_catch(bump, cxt, a, tty, t.to_span())?;
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
        super::prof_count(&super::FUNC_PROF.check_universe.1);
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
                MetaEntry::Unsolved(v, _, _, _) => *v,
                _ => unreachable!(),
            };
            let inv = {
                let Machine {
                    spine,
                    defs,
                    metas, mutable,
                    ren,
                    ..
                } = self;
                invert_bump(bump, spine, defs, metas, &*cxt.decls, mutable, ren, &args)
            };
            let Some(mask) = inv else {
                return Err(Error(t_span.map(|_| "invert failed".to_owned()), vec![]));
            };
            // 非线性：剪枝可行性检查（结果弃置——参考版只用作把关）
            if !mask.is_empty() {
                let ok = {
                    let Machine {
                        spine,
                        vals,
                        icits,
                        defs,
                        metas, mutable,
                        eval_work,
                        ..
                    } = self;
                    let work: &mut Vec<W<'a>> = unsafe {
                        &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                    };
                    work.clear();
                    prune_ty_bump(
                        bump, spine, work, vals, icits, defs, metas, &*cxt.decls, mutable, &mask, mty,
                    )
                };
                if ok.is_none() {
                    return Err(Error(t_span.map(|_| "prune failed".to_owned()), vec![]));
                }
            }
            if args.is_empty() {
                // pren.dom == 0：meta 类型 force 后是 U 即解 `U(0)`
                let f = self.force_v(bump, cxt, mty);
                if v_tag(f) == 3 {
                    journal_meta(&mut self.metas, m as usize, MetaEntry::Solved(v_u(0), mty));
                    return Ok((t_inferred, 0));
                }
                let f2 = self.force_v(bump, cxt, mty);
                let msg = format!("meta type {} is not a universe", debug_val(&self.spine, &self.defs, f2));
                return Err(Error(t_span.map(|_| msg.clone()), vec![]));
            }
            // rename 出 `U(0)` 的解（occ = m），λ 包裹后空环境求值写表
            let rhs = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas, mutable,
                    ren,
                    unify_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(unify_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                rename_iter(
                    bump, spine, work, vals, icits, defs, ren, metas, &*cxt.decls, mutable,
                    Some(m), args.len() as u32, cxt.lvl, v_u(0),
                )
            };
            let Some(rhs) = rhs else {
                return Err(Error(
                    t_span.map(|_| "when check universe, try to rename failed".to_string()),
                    vec![],
                ));
            };
            let lam_tm = {
                let Machine {
                    spine,
                    vals,
                    icits,
                    defs,
                    metas, mutable,
                    eval_work,
                    ..
                } = self;
                let work: &mut Vec<W<'a>> = unsafe {
                    &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                };
                work.clear();
                lams_from_ty(bump, spine, work, vals, icits, defs, metas, &*cxt.decls, mutable, args.len() as u32, mty, rhs)
            };
            let solution = self.eval(bump, cxt, EMPTY_ENV, lam_tm);
            journal_meta(&mut self.metas, m as usize, MetaEntry::Solved(solution, mty));
            return Ok((t_inferred, 0));
        }
        Err(Error(
            t_span.map(|_| {
                format!(
                    "expected universe, got {}",
                    debug_val(&self.spine, &self.defs, inferred_type)
                )
            }),
            vec![],
        ))
    }
}

// Elaboration 上下文
// --------------------------------------------------------------------------------

/// scope 里的一项：名字 + 类型值 + 来源（源码 binder / inserted binder）。
pub(super) struct TCons<'a> {
    pub(super) name: &'a str,
    pub(super) ty: V,
    pub(super) source: bool,
    pub(super) next: Option<&'a TCons<'a>>,
}

/// namespace 条目链（参考版 `Cxt.namespace: List<(Rc<Val>, HashSet<SmolStr>,
/// SmolStr)>` 的 bump 持久链；方法名集以切片线性查——条目少）。
pub(crate) struct NsCons<'a> {
    /// 类型值（`trait_wrap` 的接收者类型探测）。
    pub(super) val: V,
    /// 实例方法名集。
    pub(super) methods: &'a [SmolStr],
    /// TypeHead 字符串（`TypeHead.method` 的注册前缀）。
    pub(super) type_name: &'a str,
    pub(super) next: Option<&'a NsCons<'a>>,
}

/// Elaboration 上下文（绑定量在 bump 里）。方法一律借用 `&Cxt`（扩展上下
/// 文返回**新的** Cxt 值；名字/类型的可变状态在 [`Machine`] 的
/// name_map/lvl_types，随 `mark` 轨迹撤销）。
pub(super) struct Cxt<'a> {
    pub(super) env: Env<'a>,
    /// 已精化的最低层级（L10 `update_from`：refresh 只走增量区间）。
    pub(super) update_from: Option<usize>,
    /// 名字快照（参考版 `src_names: BiMap` 同构；随扩展克隆——隔离语义
    /// 与参考版逐字对应）。
    pub(super) names: Rc<Names>,
    /// type of every variable in scope（头 = 最内层；`source` 标记源码
    /// binder——消融口径的线性找名跳过非源码条目；println 的 pretty 名
    /// 单也走这里，与参考版 `Cxt::names()` 的 locals 序一致）。
    pub(super) types: Option<&'a TCons<'a>>,
    /// telescope（上游 `cxtLocals`）：fresh_meta 闭类型用。
    pub(super) locals: Option<&'a LCons<'a>>,
    /// fresh meta 的 scope 掩码（与 env 平行；头 = 最内层）。
    pub(super) pruning: Option<&'a PrCons<'a>>,
    /// 绑定层数（bind/new_binder/synth +1，define 不动）。
    pub(super) binds: u32,
    pub(super) lvl: u32,
    /// 全局声明表（参考版 `Cxt.decl: HashMap` 同构；写时复制——
    /// fake_bind 的撞名检查与 decl 登记都经 `Rc::make_mut`）。
    pub(super) decls: Rc<Decls<'a>>,
    /// inherent impl 登记的类型→实例方法集（参考版 `Cxt.namespace`）。
    pub(super) namespace: Option<&'a NsCons<'a>>,
    /// `package a.b` 后对 def/enum/trait/class 名生效的前缀。
    pub(super) namespace_prefix: Option<SmolStr>,
    /// 可见 namespace 集（后缀 fallback 的准入判定；写时复制）。
    pub(super) namespaces: Rc<FxHashSet<SmolStr>>,
    /// 当前 let/字段绑定的名字（`BindingName` 隐参合成用）。bind 清、
    /// define 保留、`with_binding_name` 显式设。
    pub(super) binding_name: Option<SmolStr>,
}

impl<'a> Cxt<'a> {
    pub(super) fn empty() -> Self {
        Cxt {
            env: EMPTY_ENV,
            update_from: None,
            names: Rc::new(Names::default()),
            types: None,
            locals: None,
            pruning: None,
            binds: 0,
            lvl: 0,
            decls: Rc::new(Decls::default()),
            namespace: None,
            namespace_prefix: None,
            namespaces: Rc::new(FxHashSet::default()),
            binding_name: None,
        }
    }

    /// `with_binding_name`：let RHS / class 字段检查前设绑定名（参考版
    /// cxt.rs 同名方法；binding_name 只影响隐式 `BindingName` 参数合成）。
    fn with_binding_name(&self, name: SmolStr) -> Self {
        Cxt {
            namespace: self.namespace,
            namespace_prefix: self.namespace_prefix.clone(),
            namespaces: self.namespaces.clone(),
            binding_name: Some(name),
            env: self.env,
            update_from: self.update_from,
            names: self.names.clone(),
            types: self.types,
            locals: self.locals,
            pruning: self.pruning,
            binds: self.binds,
            lvl: self.lvl,
            decls: self.decls.clone(),
        }
    }
}

/// prelude 短名别名 auto-import（参考版 `load_prelude_state_impl` 尾部
/// 逐句）：全局 decl 表里带 `.` 的键给短名别名（`Nat.zero` → `zero`），
/// **ns 方法键排除**（`TypeHead.method` 只经 `x.m` 分派可达、绝不裸名，
/// 不得遮构造子别名）；短名冲突按全键排序 `or_insert` first-wins（结果
/// 与 HashMap 迭代序无关的确定性）。
pub(super) fn insert_prelude_aliases<'a>(mut cxt: Cxt<'a>) -> Cxt<'a> {
    let mut ns_method_keys: FxHashSet<SmolStr> = FxHashSet::default();
    let mut cur = cxt.namespace;
    while let Some(ns) = cur {
        for m in ns.methods {
            ns_method_keys.insert(SmolStr::new(format!("{}.{}", ns.type_name, m)));
        }
        cur = ns.next;
    }
    let mut aliases: Vec<(SmolStr, SmolStr, DeclEntry<'a>)> = cxt
        .decls
        .iter()
        .filter(|(k, _)| k.contains('.') && !ns_method_keys.contains(*k))
        .map(|(k, v)| {
            let short = SmolStr::new(k.split('.').last().unwrap());
            (short, k.clone(), v.clone())
        })
        .collect();
    aliases.sort_by(|a, b| a.1.cmp(&b.1));
    let map = Rc::make_mut(&mut cxt.decls);
    for (short, _full_key, v) in aliases {
        map.entry(short).or_insert(v);
    }
    cxt
}

fn tuple_n_arity(name: &str) -> Option<usize> {
    let digits = name.strip_prefix("Tuple")?;
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// 判定函数位是否为组合子字面构造 `TupleN.mk e0 … en`
/// （参考版 is_tuple_mk_head 逐句对应，服务元素 hover）。
fn is_tuple_mk_head(head: &Raw) -> bool {
    let mut cur = head;
    loop {
        match cur {
            Raw::App(f, _, _) => cur = f.as_ref(),
            _ => break,
        }
    }
    match cur {
        Raw::Var(n) => n
            .data
            .strip_suffix(".mk")
            .and_then(tuple_n_arity)
            .is_some(),
        Raw::Obj(base, Some(m)) if m.data == "mk" => {
            let mut cur = base.as_ref();
            loop {
                match cur {
                    Raw::App(f, _, _) => cur = f.as_ref(),
                    _ => break,
                }
            }
            matches!(cur, Raw::Var(n) if tuple_n_arity(&n.data).is_some())
        }
        _ => false,
    }
}

/// types 链 → 参考版 pretty 的名字 List（头 = 最内层；List::prepend 从尾
/// 起构回，序不变）。
pub(super) fn types_names_list(tys: Option<&TCons<'_>>) -> crate::list::List<SmolStr> {
    let mut ns: Vec<SmolStr> = Vec::new();
    let mut cur = tys;
    while let Some(tc) = cur {
        ns.push(SmolStr::new(tc.name));
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
            Tm::Decl(_) => {}
            Tm::Lam(_, _, b) => stack.push((b, d + 1)),
            Tm::App(f, a, _) => {
                stack.push((f, d));
                stack.push((a, d));
            }
            Tm::AppPruning(h, _) => stack.push((h, d)),
            Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {}
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
            Tm::Sum(_, params, ..) => {
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
            Tm::Call(_, args, body) => {
                for (a, _) in args.iter() {
                    stack.push((a, d));
                }
                stack.push((body, d));
            }
        }
    }
    false
}

impl Machine {
    // check_pm / unify_pm / update_cxt / refresh（参考版 elaboration.rs +
    // cxt.rs 的模式特化机制——精化等式直接改写进环境）
    // --------------------------------------------------------------------------------

    /// 环境槽（0 = 最内层，`lvl2ix` 口径）；层级超出上下文给 None。
    fn env_lvl_slot(&self, cxt: &Cxt<'_>, lvl: u32) -> Option<V> {
        let ix = cxt.lvl.checked_sub(lvl + 1)?;
        if ix >= env_len(cxt.env) {
            return None;
        }
        Some(env_nth(&self.defs, cxt.env, ix))
    }

    /// 该层在环境里是否仍是自引用（未精化）。越界按 true（参考版
    /// `env.iter().nth(..).map(..).unwrap_or(true)` 同款）。
    fn env_lvl_is_self(&self, cxt: &Cxt<'_>, lvl: u32) -> bool {
        match self.env_lvl_slot(cxt, lvl) {
            Some(v) => v_tag(v) == 0 && v_lvl_of(v) == lvl,
            None => true,
        }
    }

    /// 该层若已精化（环境槽不再是自引用），给出当前精化值；未精化给 None。
    fn env_lvl_refined(&self, cxt: &Cxt<'_>, lvl: u32) -> Option<V> {
        match self.env_lvl_slot(cxt, lvl) {
            Some(v) if !(v_tag(v) == 0 && v_lvl_of(v) == lvl) => Some(v),
            _ => None,
        }
    }

    /// `unify_pm`：模式特化的合一（参考版 elaboration.rs 同款臂序）：
    /// 双裸 Rigid 同级自反；双裸 Rigid 异名按「谁还没精化就精化谁」；
    /// 单侧裸 Rigid 已精化时**与旧精化值继续合一**（而不是覆盖）；同名
    /// SumCase 逐 datas、同名 Sum 逐参数（均**只比值槽**）递归；其余落
    /// `unify_catch`（全文案合一错误）。
    pub(super) fn unify_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
        t_span: &crate::parser_lib::Span<()>,
    ) -> Result<Cxt<'a>, Error> {
        let f1 = self.force_v(bump, cxt, t);
        let f2 = self.force_v(bump, cxt, t_prime);
        // (Rigid(x1, []), Rigid(x2, [])) if x1 == x2 → 同变量也走精化
        // （L10：update_cxt(x1, t_prime, update_prune=false)）
        if v_tag(f1) == 0 && v_tag(f2) == 0 && v_lvl_of(f1) == v_lvl_of(f2) {
            return self.update_cxt_impl(bump, cxt, v_lvl_of(f1), f2, false);
        }
        // 双裸 Rigid 异名：一侧可能已被**前面字段**的构造子精化过（环境槽
        // 不再是自引用），另一侧是 fresh 模式变量。精化未精化的一侧，保住
        // 早先的精化（参考版同臂；缺了它 `cons` 的第二个隐式 `_l1` 会把
        // 前一个的 `l := _l0+1` 覆盖成 `l := _l1+1`，`_l0`/`_l1` 永不相等，
        // 臂体里 `Vec _l0` vs `Vec _l1` 误报 can't unify——adder_proof 实测）。
        if v_tag(f1) == 0 && v_tag(f2) == 0 {
            let x1 = v_lvl_of(f1);
            let x2 = v_lvl_of(f2);
            let x1_is_self = self.env_lvl_is_self(cxt, x1);
            let x2_is_self = self.env_lvl_is_self(cxt, x2);
            if x1_is_self && !x2_is_self {
                return self.update_cxt_impl(bump, cxt, x1, f2, true);
            } else if x2_is_self && !x1_is_self {
                return self.update_cxt_impl(bump, cxt, x2, f1, true);
            }
            return self.update_cxt_impl(bump, cxt, x1, f2, true);
        }
        // (Rigid(x, []), v)：x 已精化时**不覆盖**——把旧精化值与 v 继续
        // 合一（约束传播：`l := succ _l0` 与 `l := succ _l1` 相遇时下钻到
        // `_l0 = _l1`；参考版 already_refined 分支同款）。
        if v_tag(f1) == 0 {
            let x = v_lvl_of(f1);
            if let Some(cur) = self.env_lvl_refined(cxt, x) {
                return self.unify_pm(bump, cxt, cur, f2, t_span);
            }
            return self.update_cxt_impl(bump, cxt, x, f2, true);
        }
        // (v, Rigid(x, [])) → 对称
        if v_tag(f2) == 0 {
            let x = v_lvl_of(f2);
            if let Some(cur) = self.env_lvl_refined(cxt, x) {
                return self.unify_pm(bump, cxt, f1, cur, t_span);
            }
            return self.update_cxt_impl(bump, cxt, x, f1, true);
        }
        // 原生 Nat ↔ 一元 `SumCase` 链（参考版 unify_pm 的两条 Nat 臂同口径）：
        // 压缩后的具体 Nat（`Nat(k)`）与 `zero`/`succ` 链按定义逐层比——探测面
        // 的构造子返回索引常把 `succ n` 具体化，而头部一侧是 `Nat(k)`。
        let nat_of = |v: V| match v_xcell_of(v) {
            XCell::Nat(k) => Some(*k),
            _ => None,
        };
        if v_tag(f1) == 7 && v_tag(f2) == 7 && (nat_of(f1).is_some() || nat_of(f2).is_some()) {
            if let Some(r) = self.unify_nat_sumcase(bump, cxt, f1, f2, t_span)? {
                return Ok(r);
            }
        }
        // 同名 SumCase：逐 datas（值槽）
        if v_tag(f1) == 7 && v_tag(f2) == 7 {
            if let (
                XCell::SumCase {
                    typ: ty1,
                    index: i1,
                    datas: d1,
                    ..
                },
                XCell::SumCase {
                    typ: ty2,
                    index: i2,
                    datas: d2,
                    ..
                },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if i1 == i2 {
                    // Sum 头名字判据（L07 修复 4 同款，参考版 unify_pm 同点）：
                    // 跨 enum 重名构造子（index 同、typ 的 Sum 头异）直接
                    // Err——只比头名，不 unify typ 值（避免互相引用深递归）。
                    // typ 非和类型（meta / 未定型）时不加严。
                    let h1 = self.force_v(bump, cxt, *ty1);
                    let h2 = self.force_v(bump, cxt, *ty2);
                    if v_tag(h1) == 7
                        && v_tag(h2) == 7
                        && matches!(v_xcell_of(h1), XCell::Sum { .. })
                        && matches!(v_xcell_of(h2), XCell::Sum { .. })
                    {
                        let (n1, n2) = match (v_xcell_of(h1), v_xcell_of(h2)) {
                            (XCell::Sum { name: n1, .. }, XCell::Sum { name: n2, .. }) => (*n1, *n2),
                            _ => unreachable!(),
                        };
                        if n1 != n2 {
                            return Err(Error(t_span.map(|_| "".to_string()), vec![]));
                        }
                    }
                    let mut cxt = clone_cxt(cxt);
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(bump, &cxt, x.val, y.val, t_span)?;
                    }
                    return Ok(cxt);
                }
                return Err(Error(t_span.map(|_| "".to_string()), vec![]));
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
                    let mut cxt = clone_cxt(cxt);
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        cxt = self.unify_pm(bump, &cxt, x.val, y.val, t_span)?;
                    }
                    return Ok(cxt);
                }
                return Err(Error(t_span.map(|_| "".to_string()), vec![]));
            }
        }
        self.unify_catch(bump, cxt, f1, f2, *t_span).map(|_| clone_cxt(cxt))
    }

    /// 「纯探测」统一执行器：进入前快照 `metas` 与 `trait_metas`，跑完闭包后
    /// **无条件**换回（无论闭包返回 Ok/Err），把探测期分配的 fresh meta 与对
    /// 已有 meta/trait meta 的求解一律回滚，杜绝污染外泄到真实机。可达性探测等
    /// 投机性 check 都走此入口，避免各处手写快照漏掉错误路径（AV 根因）。
    ///
    /// 注意：必须**整表 clone**，不能只按 meta 上界截断——探测期的 unify 可能
    /// 解掉**已有**的 meta，而这些解又引用闭包内新建的 meta，截断会让那些解
    /// 悬空（后续查找越界 panic）；参考版 pattern_match.rs 同款理由。
    /// `Nat(k)` ↔ 一元 `SumCase` 链（参考版 `unify_pm` 的两条 Nat 臂逐句）：
    /// 任一侧是压缩 Nat、另一侧是 SumCase 时按定义逐层展开（`zero` 空链 ↔ 0、
    /// `succ d` ↔ k+1 → 比 d 与 k-1）。SumCase 的 `typ` 必须是 Nat 和类型
    /// （参考版 `is_nat_sum` 闸）；`Ok(None)` = 不适用（两侧都不是 Nat 形态），
    /// 交回通用臂。
    fn unify_nat_sumcase<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        f1: V,
        f2: V,
        t_span: &crate::parser_lib::Span<()>,
    ) -> Result<Option<Cxt<'a>>, Error> {
        let nat_of = |v: V| match v_xcell_of(v) {
            XCell::Nat(k) => Some(*k),
            _ => None,
        };
        let case_of = |v: V| match v_xcell_of(v) {
            XCell::SumCase { typ, index, datas, .. } => Some((*typ, *index, datas)),
            _ => None,
        };
        // (Nat(k), SumCase) 或 (SumCase, Nat(k))：k 侧与 case 侧各自取
        let (k, case) = match (nat_of(f1), case_of(f1), nat_of(f2), case_of(f2)) {
            (Some(k), _, _, Some(c)) => (k, c),
            (_, Some(c), Some(k), _) => (k, c),
            _ => return Ok(None),
        };
        let (case_typ, index, datas) = case;
        let ty = self.force_v(bump, cxt, case_typ);
        if !is_nat_sum_v(ty) {
            return Err(Error(t_span.map(|_| "".to_string()), vec![]));
        }
        match (index, datas.len(), k) {
            (0, 0, 0) => Ok(Some(clone_cxt(cxt))),
            (1, 1, k) if k > 0 => {
                let prev = v_xcell(bump.alloc(XCell::Nat(k - 1)));
                Ok(Some(self.unify_pm(bump, cxt, prev, datas[0].val, t_span)?))
            }
            _ => Err(Error(t_span.map(|_| "".to_string()), vec![])),
        }
    }

    fn run_pure_probe<R>(&mut self, f: impl FnOnce(&mut Machine) -> R) -> R {
        // 探测回滚（perf-debt 评审轮）：旧实现整表 clone metas+trait_metas
        // （match 编译每 (节点×构造子) 探测一次，metas 万条级时 47-case
        // match 单 decl 数百 ms）。journal 记就地写、截断收 append；
        // META_JOURNAL 栈式支持嵌套探测。
        let pre_meta_len = self.metas.len();
        let pre_tm_len = self.trait_metas.len();
        META_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
        let r = f(self);
        meta_journal_rollback(&mut self.metas, pre_meta_len);
        self.trait_metas.truncate(pre_tm_len);
        r
    }

    /// Pattern-matching version of `infer_expr`（参考版 `infer_expr_pm` 的
    /// 孪生镜像，2026-09-19 GADT 嵌套漂移修复）：对 `Raw::App` 的**实参**
    /// 用 `check_pm`（→ `unify_pm`）而不是常规 `check`（→ `unify_catch`），
    /// 嵌套构造子模式（`cons(x, nil)` 的 `nil` 应用）才能把走查 rigid 精化
    /// （`_l0 := zero`）——否则嵌套 GADT 匹配在 `unify_catch` 的 rigid 冲突
    /// 上误报 `can't unify expected: Vec[Nat](_l0) find: Vec[Nat](0)`
    ///（iso_a/b/c 探针钉）。头部侧的 Name/Impl/Expl 分派与常规 infer_expr
    /// 逐句同构（参考版同款：头部不精化，只精化实参）。
    fn infer_expr_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V, Cxt<'a>), Error> {
        match t {
            Raw::App(t, u, arg) => {
                let t_span = t.to_span();
                let t_raw = (**t).clone();
                let u_raw = (**u).clone();
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
                let tty = self.force_v(bump, cxt, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(
                            t_span.map(|_| format!("icit mismatch {:?} {:?}", i, p.icit)),
                            vec![],
                        ));
                    }
                    (p.dom, p)
                } else {
                    // Scala 式 apply（参考版同款）：非 Π 头先试 `expr.apply(arg)`
                    let meta_before = self.metas.len();
                    let apply_obj = Raw::Obj(Box::new(t_raw), Some(empty_span(SmolStr::new("apply"))));
                    let apply_call = Raw::App(Box::new(apply_obj), Box::new(u_raw), Either::Icit(i));
                    if let Ok(result) = self.infer_expr(bump, cxt, &apply_call) {
                        return Ok((result.0, result.1, clone_cxt(cxt)));
                    }
                    self.metas.truncate(meta_before);
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一
                    let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                    let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt, cxt.lvl, a);
                    let cxt2 = self.bind_name(bump, cxt, "x", empty_span(()), a_t, a);
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u(0));
                    let cell = bump.alloc(PiCell {
                        name: "x",
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty, t_span)?;
                    (a, &*cell)
                };
                // KEY DIFFERENCE: use check_pm instead of check（参考版同款注释）
                let (u_checked, cxt) = self.check_pm(bump, cxt, u, a)?;
                let arg_v = self.eval(bump, &cxt, cxt.env, u_checked);
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, &cxt, env, bcell.body)
                };
                Ok((bump.alloc(Tm::App(t, u_checked, i)), ty, cxt))
            }
            _ => self
                .infer_expr(bump, cxt, t)
                .map(|(tm, ty)| (tm, ty, clone_cxt(cxt))),
        }
    }

    /// `check_pm`：infer + insert + `unify_pm`（实参经 `infer_expr_pm` 精化）。
    fn check_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
    ) -> Result<(&'a Tm<'a>, Cxt<'a>), Error> {
        let t_span = t.to_span();
        let (t_inferred, inferred_type, refined_cxt) = self.infer_expr_pm(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, &refined_cxt, t_inferred, inferred_type)?;
        let new_cxt = self.unify_pm(bump, &refined_cxt, a, inferred_type, &t_span)?;
        Ok((t_inferred, new_cxt))
    }

    /// `check_pm_final`：`check_pm` 之后把原始值与精化后的期望再对一次
    /// （`.unwrap_or(new_cxt)`——失败容忍，参考版同款）。模式 raw 经
    /// `infer_expr_pm` 精化（嵌套构造子应用把走查 rigid 解进上下文）。
    pub(super) fn check_pm_final<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
        a: V,
        ori: V,
    ) -> Result<(&'a Tm<'a>, Cxt<'a>), Error> {
        let t_span = t.to_span();
        let (t_inferred, inferred_type, refined_cxt) = self.infer_expr_pm(bump, cxt, t)?;
        let (t_inferred, inferred_type) = self.insert(bump, &refined_cxt, t_inferred, inferred_type)?;
        let new_cxt = self.unify_pm(bump, &refined_cxt, a, inferred_type, &t_span)?;
        let ori_v = self.eval(bump, &new_cxt, new_cxt.env, t_inferred);
        // ori 精化**要传下去**（参考版 `let new_cxt = ...unwrap_or(new_cxt)`
        // ——被匹配变量本身的值写进环境，期望类型重锚定后才能选中分支）
        let refined = self.unify_pm(bump, &new_cxt, ori, ori_v, &t_span);
        let new_cxt = refined.unwrap_or(new_cxt);
        Ok((t_inferred, new_cxt))
    }

    /// 构造子返回类型良构性（参考版 elaboration.rs `check_ctor_wf` 的孪生
    /// 镜像，2026-09-18 L07 修复 6 移植）：实例化构造子类型的全部绑定器后，
    /// ret 的 WHNF 必须是 `enum_name` 的 `Sum`，且其隐式参数位逐一等于
    /// telescope 内的 bare rigid（孪生值层裸 rigid = tag 0 的 `v_lvl`）。允许
    /// 构造子重绑定参数（`p[A,B](a,b) -> Pack[A][B] a b` 惯用法），拒绝参数
    /// 位特化（`c -> Foo[Nat]`）与非本 enum 的 ret（`c -> Nat`）——后者注入
    /// 永不匹配任何模式的 phantom 值。显式索引位任由特化（GADT 保留）。
    fn check_ctor_wf<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        enum_name: &str,
        ctor_name: &str,
        ctor_vtyp: V,
    ) -> Result<(), Error> {
        let base = cxt.lvl;
        let mut ty = ctor_vtyp;
        let mut bound = 0u32;
        let ret = loop {
            let tyf = self.force_v(bump, cxt, ty);
            if v_tag(tyf) == 4 {
                let p = v_pi_of(tyf);
                let u = v_lvl(base + bound);
                bound += 1;
                let env = env_ext(bump, p.env, u);
                ty = self.eval(bump, cxt, env, p.body);
            } else {
                break tyf;
            }
        };
        let retf = self.force_v(bump, cxt, ret);
        if v_tag(retf) != 7 {
            return Err(Error(
                empty_span(()).map(|_| format!("构造子 {ctor_name} 的返回类型不是和类型")),
                vec![],
            ));
        }
        let (sum_name, params) = match v_xcell_of(retf) {
            XCell::Sum { name, params, .. } => (*name, params),
            _ => {
                return Err(Error(
                    empty_span(()).map(|_| format!("构造子 {ctor_name} 的返回类型不是和类型")),
                    vec![],
                ))
            }
        };
        if sum_name != enum_name {
            return Err(Error(
                empty_span(()).map(|_| {
                    format!("构造子 {ctor_name} 的返回类型是 {sum_name}，不是 {enum_name}")
                }),
                vec![],
            ));
        }
        for p in params.iter() {
            if p.icit != Icit::Impl {
                continue;
            }
            let bare = v_tag(p.val) == 0 && {
                let l = v_lvl_of(p.val);
                base <= l && l < base + bound
            };
            if !bare {
                return Err(Error(
                    empty_span(()).map(|_| {
                        format!(
                            "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
                        )
                    }),
                    vec![],
                ));
            }
        }
        Ok(())
    }

    fn update_cxt<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: u32,
        v: V,
    ) -> Result<Cxt<'a>, Error> {
        self.update_cxt_impl(bump, cxt, x, v, true)
    }

    /// `Cxt::update_cxt` 的 L10 版本体：Flex 不动；`update_from` 记录已
    /// 精化的最低层级（单调取小）；`update_prune=false` 时 pruning 保持；
    /// refresh 只走 `lvl - update_from` 的增量区间（walk 参数），src_names
    /// 按层级同步（L10 `if let Some`——无条目静默跳过）。
    fn update_cxt_impl<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: u32,
        v: V,
        update_prune: bool,
    ) -> Result<Cxt<'a>, Error> {
        if is_flex(&self.spine, v) {
            return Ok(clone_cxt(cxt));
        }
        let update_from = match cxt.update_from {
            Some(u) if u < x as usize => u,
            _ => x as usize,
        };
        // lvl2ix(lvl, x)：x 恒为局部层级（顶层声明不进环境——参考版
        // update_cxt 同款）
        let x_prime: usize = lvl2ix(cxt.lvl, x) as usize;
        let n = env_len(cxt.env) as usize;
        let mut slots2: Vec<V> = Vec::with_capacity(n);
        env_collect(&self.defs, cxt.env, &mut slots2);
        if x_prime < n {
            slots2[x_prime] = v;
        }
        let mut names = (*cxt.names).clone();
        let walk = cxt.lvl as usize - update_from;
        let refreshed = self.refresh(bump, cxt, &slots2, &mut names, walk);
        // pruning：update_prune 时目标槽改 None（define 槽）并前缀重建；
        // 否则保持原 pruning（参考版 update_prune=false 同款）
        let mut pr_slots: Vec<Option<Icit>> = Vec::with_capacity(n);
        {
            let mut cur = cxt.pruning;
            while let Some(b) = cur {
                pr_slots.push(b.slot);
                cur = b.next;
            }
        }
        if update_prune && x_prime < pr_slots.len() {
            pr_slots[x_prime] = None;
        }
        let pruning: Option<&'a PrCons<'a>> = if update_prune {
            let mut pr: Option<&'a PrCons<'a>> = None;
            for slot in pr_slots.into_iter().rev() {
                pr = Some(bump.alloc(PrCons::new(slot, pr)));
            }
            pr
        } else {
            cxt.pruning
        };
        // 环境：纯链重建（refresh 后的槽序，头 = 最内层）
        let mut env: Option<&'a EnvCons<'a>> = None;
        for val in refreshed.into_iter().rev() {
            env = Some(bump.alloc(EnvCons { val, next: env }));
        }
        Ok(Cxt {
            env: Env {
                flat_base: 0,
                flat_len: 0,
                binds: env,
            },
            update_from: Some(update_from),
            names: Rc::new(names),
            types: cxt.types,
            locals: cxt.locals,
            pruning,
            binds: cxt.binds,
            lvl: cxt.lvl,
            decls: cxt.decls.clone(),
            namespace: cxt.namespace,
            namespace_prefix: cxt.namespace_prefix.clone(),
            namespaces: cxt.namespaces.clone(),
            binding_name: cxt.binding_name.clone(),
        })
    }

    /// `Cxt::refresh`（参考版递归的迭代化）：从最内层槽向外逐槽把旧值在
    /// 「目标槽已替换 + 更外槽已刷新」的环境下重锚定（quote 旧 env 长度 →
    /// eval 新 env），`names.by_lvl` 同槽更新（**调用方传入的克隆快照**，
    /// 与参考版 `new_src_names` 的 clone-then-mutate 同款）。参考版
    /// `get_by_key2_mut(...).unwrap()`：无条目的层级（inserted binder）
    /// panic——同款保留。
    #[allow(clippy::too_many_arguments)]
    fn refresh<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        slots2: &[V],
        names: &mut Names,
        walk: usize,
    ) -> Vec<V> {
        let n = env_len(cxt.env) as usize;
        let old: Vec<V> = {
            let mut v = Vec::with_capacity(n);
            env_collect(&self.defs, cxt.env, &mut v);
            v
        };
        let mut refreshed: Vec<Option<V>> = vec![None; n];
        // L10 walk：只刷新最后 `walk` 个槽（参考版 walk 参数——其余槽
        // 原样直通）；walk 区间外的槽先填原值（内层引用直接可见）
        let walk_n = walk.min(n);
        for d in walk_n..n {
            refreshed[d] = Some(old[d]);
        }
        for d in (0..walk_n).rev() {
            // env_tt：头 d+1 个取 slots2（含目标替换），其余取已刷新槽
            let mut env_tt: Vec<V> = Vec::with_capacity(n);
            env_tt.extend_from_slice(&slots2[..d + 1]);
            for i in d + 1..n {
                env_tt.push(refreshed[i].expect("refresh: 内层槽未刷新"));
            }
            let env_tt_chain = chain_env(bump, &env_tt);
            // 槽值重锚定
            let q = self.quote(bump, cxt, n as u32, old[d]);
            let rv = self.eval(bump, cxt, env_tt_chain, q);
            refreshed[d] = Some(rv);
            // src_names 按层级同步（Lvl(env_t.len()) = n-1-d）；L10：
            // 无条目静默跳过（if let Some 同款）
            let lvl = (n - 1 - d) as u32;
            if let Some((old_ty, sp)) = names.by_lvl.get(&lvl) {
                let old_ty = *old_ty;
                let sp = *sp;
                let qt = self.quote(bump, cxt, n as u32, old_ty);
                let rty = self.eval(bump, cxt, env_tt_chain, qt);
                names.by_lvl.insert(lvl, (rty, sp));
            }
        }
        refreshed.into_iter().map(|x| x.expect("refresh: 槽未刷新")).collect()
    }
}

impl Machine {
    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    pub(super) fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        super::prof_count(&super::FUNC_PROF.infer_expr.1);
        #[cfg(feature = "sampler")]
        crate::sampler::tick();

        // 整个 Raw 节点的 span（参考版 infer_expr 的 t_span 形参；Ob臂
        // qualified 三试的 hover 键跟它对齐，其余站点用各自 token span）
        let raw_span = t.to_span();
        match t {
            // 变量：五级解析链（参考版 Raw::Var 臂逐句）——局部名字 → decl
            // 精确键 → import 别名 → namespace 前缀 → `.name` 后缀唯一回退
            //（歧义报错；排除 namespace 方法键、要求首段可见）
            Raw::Var(x) => {
                if let Some(&blvl) = cxt.names.by_name.get(x.data.as_str()) {
                    let (ty, def_span) = *cxt.names.by_lvl.get(&blvl).expect("by_lvl 缺层级");
                    // 观察面：局部变量使用处现场渲染（与参考版使用处同溝）；
                    // def_span = binder 源码 span（Names.by_lvl 元组携带，合成 binder 为零）。
                    self.push_hover(bump, cxt, x.to_span(), def_span, ty);
                    let ix = lvl2ix(cxt.lvl, blvl);
                    return Ok((bump.alloc(Tm::Var(ix)), ty));
                }
                if let Some(e) = cxt.decls.get(x.data.as_str()) {
                    self.push_hover_cached(bump, cxt, x.to_span(), e);
                    let name = bump.alloc_str(x.data.as_str());
                    return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                }
                // import 别名（`import mylib.add` 让裸 `add` → 全键）
                if let Some(full) = self.import_map.get(x.data.as_str()).cloned() {
                    if let Some(e) = cxt.decls.get(full.as_str()) {
                        self.push_hover_cached(bump, cxt, x.to_span(), e);
                        let name = bump.alloc_str(full.as_str());
                        return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                    }
                }
                // namespace 前缀（`package mylib` 内的裸名）
                if let Some(prefix) = &cxt.namespace_prefix {
                    let qualified = format!("{}.{}", prefix, x.data);
                    if let Some(e) = cxt.decls.get(qualified.as_str()) {
                        self.push_hover_cached(bump, cxt, x.to_span(), e);
                        let name = bump.alloc_str(&qualified);
                        return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                    }
                }
                // `.name` 后缀回退：唯一命中解析；多义报错（HashMap 迭代序
                // 不定，任意取一会静默解析错构造子）。namespace 方法键
                //（`TypeHead.method`）排除——实例方法只经 `x.m` 分派。
                #[cfg(feature = "sampler")]
                crate::sampler::tick();
                // 【后缀回退 memo】版本纪元不符即整表弃用；正结果 = 全键
                // 直取（与唯一命中分支同出口），负结果 = 确定未命中（与
                // 空桶/滤空同文案）。多义（>1 命中）不记，逐次重查。
                if self.suffix_memo_epoch != self.suffix_memo_version {
                    self.suffix_memo.clear();
                    self.suffix_memo_epoch = self.suffix_memo_version;
                }
                if let Some(memo) = self.suffix_memo.get(x.data.as_str()).cloned() {
                    let tail = x.data.as_str();
                    match memo {
                        SuffixMemo::Pos { full_key, bucket_ptr }
                            if self.suffix_bucket_ptr(tail) == bucket_ptr =>
                        {
                            if let Some(e) = cxt.decls.get(full_key.as_str()) {
                                self.push_hover_cached(bump, cxt, x.to_span(), e);
                                let name = bump.alloc_str(full_key.as_str());
                                return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                            }
                        }
                        SuffixMemo::Neg {
                            bucket_ptr,
                            blocked_heads,
                        }
                            if self.suffix_bucket_ptr(tail) == bucket_ptr
                                && blocked_heads.iter().all(|h| {
                                    !cxt.decls.contains_key(h.as_str())
                                        && !cxt.namespaces.contains(h)
                                }) =>
                        {
                            return Err(Error(
                                x.clone().map(|x| format!("error name not in scope: {}", x)),
                                vec![],
                            ));
                        }
                        _ => {} // 桶已变 / 被阻头已可见 → 全量查询重查
                    }
                }
                // 候选从倒排索引取（perf-debt 评审轮：旧实现每 miss 全
                // decl 表 ends_with 扫描 O(D)）；空候选直接 not in scope
                // （与旧实现滤空后 matches.len()==0 的出口一致）。桶为
                // Rc 共享（克隆 O(1)），插入侧已按键去重，查询免整桶
                // 复制与重排序。
                let candidates = self
                    .decl_suffix_index
                    .get(x.data.as_str())
                    .cloned()
                    .unwrap_or_default();
                if candidates.is_empty() {
                    self.suffix_memo.insert(
                        x.data.clone(),
                        SuffixMemo::Neg {
                            bucket_ptr: 0,
                            blocked_heads: Vec::new(),
                        },
                    );
                    return Err(Error(
                        x.clone().map(|x| format!("error name not in scope: {}", x)),
                        vec![],
                    ));
                }
                let tail = x.data.as_str();
                let matches: Vec<(SmolStr, V, crate::parser_lib::Span<()>)> = candidates
                    .iter()
                    .filter(|k| {
                        // 等价 `k.ends_with(".{tail}") && k.len() > 1+tail.len()`
                        // （免每 miss 的 format! 分配）
                        k.len() > tail.len() + 1
                            && k.ends_with(tail)
                            && k.as_bytes()[k.len() - tail.len() - 1] == b'.'
                    })
                    .filter(|k| {
                        // 候选首段必须是 decl 键或本文件可见的 namespace
                        match k.rfind('.') {
                            Some(dot) => {
                                let head = &k[..dot];
                                let first = head.split('.').next().unwrap_or(head);
                                cxt.decls.contains_key(first)
                                    || cxt.namespaces.contains(first)
                            }
                            None => false,
                        }
                    })
                    .filter(|k| !self.ns_is_method_key(cxt.namespace, k))
                    .filter_map(|k| {
                        cxt.decls.get(k.as_str()).map(|e| (k.clone(), e.vty, e.span))
                    })
                    .collect();
                if matches.len() == 1 {
                    let (full_key, vty, dspan) = &matches[0];
                    // 观察面（ref 2220）：唯一回退命中也登记 hover。final
                    // 条目直推登记期缓存串（push_hover_cached 同契约：登记
                    // 期无未解 meta 时缓存串与使用处实时渲染逐字节一致，
                    // 评审 B#1 已验证）；非 final 条目仍实时渲染（缓存串
                    // 可能是 meta 解出前的旧形态；参考版此处 push vty 同款）。
                    if let Some(e) = cxt.decls.get(full_key.as_str()) {
                        self.push_hover_cached(bump, cxt, x.to_span(), e);
                    } else {
                        let tm = self.quote(bump, cxt, cxt.lvl, *vty);
                        let rendered = pretty_tm(
                            0,
                            types_names_list(cxt.types),
                            &export(&self.symbol_table, tm),
                        );
                        self.hover_table.push((x.to_span(), *dspan, rendered));
                    }
                    let name = bump.alloc_str(full_key.as_str());
                    self.suffix_memo.insert(
                        x.data.clone(),
                        SuffixMemo::Pos {
                            full_key: full_key.clone(),
                            bucket_ptr: self.suffix_bucket_ptr(tail),
                        },
                    );
                    return Ok((bump.alloc(Tm::Decl(name)), *vty));
                } else if matches.len() > 1 {
                    let names = matches
                        .iter()
                        .map(|(k, _, _)| k.as_str())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Error(
                        x.clone().map(|x| {
                            format!("ambiguous name `{}`: could refer to {}", x, names)
                        }),
                        vec![],
                    ));
                }
                // 滤后零命中：记负结果（含被"头不可见"过滤的候选首段集）
                let mut blocked: Vec<SmolStr> = Vec::new();
                for k in candidates.iter() {
                    if let Some(dot) = k.rfind('.') {
                        let head = &k[..dot];
                        let first = head.split('.').next().unwrap_or(head);
                        if !cxt.decls.contains_key(first)
                            && !cxt.namespaces.contains(first)
                            && !blocked.iter().any(|b| b == first)
                        {
                            blocked.push(SmolStr::new(first));
                        }
                    }
                }
                self.suffix_memo.insert(
                    x.data.clone(),
                    SuffixMemo::Neg {
                        bucket_ptr: self.suffix_bucket_ptr(tail),
                        blocked_heads: blocked,
                    },
                );
                Err(Error(x.clone().map(|x| format!("error name not in scope: {}", x)), vec![]))
            }

            // 预检查项无 Raw 结构可推（`check` 在此之前拦截——参考版同款）
            Raw::Tm(_, _) => Err(Error(
                empty_span("internal: cannot infer a pre-checked term".to_string()),
                vec![],
            )),

            // 原生 Nat 字面量（参考版 Raw::Nat 臂）：类型取 decl["Nat"] 登记值
            //（缺失回退 U(0)），值直接建 Nat(k)，quote 回链成 Tm
            Raw::Nat(n) => {
                let nat_type = cxt.decls.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                let nat_val = v_xcell(bump.alloc(XCell::Nat(n.data)));
                let nat_tm = self.quote(bump, cxt, cxt.lvl, nat_val);
                Ok((nat_tm, nat_type))
            }

            Raw::Obj(x, t) => {
                // 字段名可缺省（中缀运算符前缀 / 空 `.foo` 补全场景）；参考版
                // Obj 臂兣口 unwrap_or(empty_span("")) 同款
                let t = t.clone().unwrap_or(empty_span(SmolStr::new("")));
                // 观察面：限定访问中间段 hover（ref 2313 同点，无条件调用）
                self.push_qualified_hover(bump, cxt, x);
                if t.data == "mk" {
                    if let Raw::Var(sum_name) = x.as_ref() {
                        return self.infer_expr(
                            bump,
                            cxt,
                            &Raw::Var(sum_name.clone().map(|n| SmolStr::new(format!("{n}.mk")))),
                        );
                    }
                }
                // asMaster/asSlave 链式诊断（参考版同款文案）
                if t.data == "asMaster" || t.data == "asSlave" {
                    if let Raw::Obj(_, Some(prev)) = x.as_ref() {
                        if prev.data == "asMaster" || prev.data == "asSlave" {
                            return Err(Error(
                                t.clone().map(|_| format!(
                                    "`{}` on an already-directed bundle: `asMaster`/`asSlave` rebuild the bundle's ports, so chaining them (`...{}.{}`) would declare every port twice (input + output of the same name) — call them on a fresh `TypeName.create` result instead",
                                    t.data, prev.data, t.data
                                )),
                                vec![],
                            ));
                        }
                    }
                }
                // qualified path 三试（参考版 2307-2343）：全路径 → import 头段
                // 重写 → namespace 前缀
                if !t.data.is_empty() {
                    if let Some(qual) = qualified_path_str(x.as_ref(), &t.data) {
                        if let Some(e) = cxt.decls.get(qual.as_str()) {
                            self.push_hover_cached(bump, cxt, raw_span, e);
                            let name = bump.alloc_str(qual.as_str());
                            return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                        }
                        if let Some((head, rest)) = split_first_segment(&qual) {
                            if let Some(full_head) = self.import_map.get(head.as_str()) {
                                let resolved = format!("{}.{}", full_head, rest);
                                if let Some(e) = cxt.decls.get(resolved.as_str()) {
                                    self.push_hover_cached(bump, cxt, raw_span, e);
                                    let name = bump.alloc_str(&resolved);
                                    return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                                }
                            }
                        }
                        if let Some(prefix) = &cxt.namespace_prefix {
                            let prefixed = format!("{}.{}", prefix, qual);
                            if let Some(e) = cxt.decls.get(prefixed.as_str()) {
                                self.push_hover_cached(bump, cxt, raw_span, e);
                                let name = bump.alloc_str(&prefixed);
                                return Ok((bump.alloc(Tm::Decl(name)), e.vty));
                            }
                        }
                    }
                }
                let (mut tm, mut a) = self.infer_expr(bump, cxt, x)?;
                let mut a_f = self.force_v(bump, cxt, a);
                // 接收者隐式 BindingName 参数展开（参考版 2352-2371）：
                // `Test.create.tree` 等限定访问在构造子带隐式 bn 时也能走
                let _ = &mut tm;
                while v_tag(a_f) == 4 {
                    let p = v_pi_of(a_f);
                    if p.icit != Icit::Impl || !self.is_binding_name_type(bump, cxt, p.dom) {
                        break;
                    }
                    let name_str = cxt
                        .binding_name
                        .clone()
                        .unwrap_or_else(|| SmolStr::new(""));
                    let mk_key = if cxt.decls.contains_key("BindingName.mk") {
                        "BindingName.mk".to_string()
                    } else {
                        // 同上：登记期缓存（perf-debt 评审轮）
                        self.binding_name_mk
                            .clone()
                            .unwrap_or_else(|| SmolStr::new("BindingName.mk"))
                            .to_string()
                    };
                    let bn_tm = bump.alloc(Tm::App(
                        bump.alloc(Tm::Decl(bump.alloc_str(&mk_key))),
                        bump.alloc(Tm::LiteralIntro(bump.alloc_str(&name_str))),
                        Icit::Expl,
                    ));
                    let bn_val = self.eval(bump, cxt, cxt.env, bn_tm);
                    tm = bump.alloc(Tm::App(tm, bn_tm, Icit::Impl));
                    let cod = {
                        let env = env_ext(bump, p.env, bn_val);
                        self.eval(bump, cxt, env, p.body)
                    };
                    a_f = self.force_v(bump, cxt, cod);
                }
                a = a_f;
                if v_tag(a) == 7 {
                    if let XCell::Sum { params, cases, .. } = v_xcell_of(a) {
                        // struct：单 case 且名字带 `.mk` → 剥 mk 的构造子类型
                        // 链取字段类型。实例化口径照参考版（elaboration.rs
                        // 2380-2398）：**显式** binder 以接收者自身
                        // （`Obj(接收者)`）实例化——这样 `this.data` 的类型是
                        // `Vec[ModuleDef](this.num)` 而非占位值，下游
                        // `cons m this.data` 的隐式 len 才能解到 `this.num`；
                        // **隐式** binder 用 struct 的实际参数值，缺失回退
                        // 接收者。曾误用 `U(0)` 占位两处：依赖索引字段的投影
                        // 类型全部退化成 `Vec[..](U(0))`（HDL prelude 的
                        // `impl $trait_name$ModuleTree` 处 can't unify）。
                        let receiver = self.eval(bump, cxt, cxt.env, tm);
                        let mut c: Option<Vec<(&str, V)>> = None;
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let case = cases[0];
                            if let Ok((_, case_typ)) =
                                self.infer_expr(bump, cxt, &Raw::Var(empty_span(SmolStr::new(case))))
                            {
                                let mut ret: Vec<(&str, V)> = vec![];
                                let mut typ = case_typ;
                                let mut param: Vec<&SumParamV<'_>> =
                                    params.iter().collect();
                                param.reverse();
                                loop {
                                    let typ_f = self.force_v(bump, cxt, typ);
                                    if v_tag(typ_f) == 4 {
                                        let p = v_pi_of(typ_f);
                                        let this_obj =
                                            v_xcell(bump.alloc(XCell::Obj {
                                                val: receiver,
                                                name: bump.alloc_str(p.name),
                                            }));
                                        let val = if p.icit == Icit::Expl {
                                            this_obj
                                        } else {
                                            param.pop().map(|x| x.val).unwrap_or(this_obj)
                                        };
                                        ret.push((p.name, p.dom));
                                        typ = {
                                            let env = env_ext(bump, p.env, val);
                                            self.eval(bump, cxt, env, p.body)
                                        };
                                    } else {
                                        break;
                                    }
                                }
                                c = Some(ret);
                            }
                        }
                        // 观察面：type-ahead completion 关键集（ref 2431/2446——
                        // 命中与未命中都推，键 = 接收者 span，owned 零渲染）。
                        if self.observe {
                            let rcv = x.to_span();
                            self.completion_table.extend(
                                c.iter()
                                    .flatten()
                                    .map(|(n, _)| (rcv, SmolStr::new(*n)))
                                    .chain(params.iter().map(|pp| (rcv, SmolStr::new(pp.name)))),
                            );
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
                            // 观察面：字段访问 hover（ref 2422；def_span 降级为字段
                            // token 自身——双值不持字段 binder span，待评估）
                            self.push_hover(bump, cxt, t.to_span(), t.to_span(), ty);
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        // L10：Sum 接收者字段未命中 → trait 方法包装
                        //（参考版把 **force 后**的类型传给 trait_wrap）
                        return self.trait_wrap(bump, cxt, t.clone(), a, x, tm);
                    }
                    if let XCell::SumCase { datas, .. } = v_xcell_of(a) {
                        // 接收者类型是构造子值：字段类型在 datas 里
                        let field = datas
                            .iter()
                            .find(|d| d.name == t.data.as_str())
                            .map(|d| d.val);
                        {
                            // 观察面：构造子值字段名 completion（ref 2466 口径）
                            if self.observe {
                                let rcv = x.to_span();
                                self.completion_table
                                    .extend(datas.iter().map(|d| (rcv, SmolStr::new(d.name))));
                            }
                        }
                        if let Some(ty) = field {
                            // 观察面：构造子字段访问 hover（ref 2455，同样降级 def_span）
                            self.push_hover(bump, cxt, t.to_span(), t.to_span(), ty);
                            return Ok((
                                bump.alloc(Tm::Obj(tm, bump.alloc_str(&t.data))),
                                ty,
                            ));
                        }
                        // L10：SumCase 接收者字段未命中 → trait 方法包装
                        return self.trait_wrap(bump, cxt, t.clone(), a, x, tm);
                    }
                }
                // L10：其余接收者形态 → trait 方法包装（失败给原文案）
                self.trait_wrap(bump, cxt, t.clone(), a, x, tm)
            }

            // λ 推断：域用 fresh meta，值域闭包封口
            Raw::Lam(x, Either::Icit(i), tbody) => {
                let name: &'a str = bump.alloc_str(&x.data);
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                let a_t = self.quote(bump, cxt, cxt.lvl, a);
                let cxt2 = self.bind_name(bump, cxt, &x.data, x.to_span(), a_t, a);
                let infered = self.infer_expr(bump, &cxt2, tbody);
                let (t_inferred0, b0) = infered?;
                let (t_inferred, b) = self.insert(bump, &cxt2, t_inferred0, b0)?;
                // closeVal：quote 在 lvl+1——给即将到来的 binder 留第 0 槽
                let body = self.quote(bump, cxt, cxt.lvl + 1, b);
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
                Err(Error(x.clone().map(|_| "infer named lambda".to_owned()), vec![]))
            }

            // 应用
            Raw::App(t, u, arg) => {
                // 实参分派：命名 → insertUntilName 后按 Impl 应用；
                // 位置 Impl → 直接应用；位置 Expl → 先 insert_t
                let t_span = t.to_span();
                let t_raw = (**t).clone();
                let tuple_head = is_tuple_mk_head(&t_raw); // 观察面：提前计算（t_raw 后续可能被移动）
                let u_raw = (**u).clone();
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
                let tty = self.force_v(bump, cxt, tty);
                let (a, bcell) = if v_tag(tty) == 4 {
                    let p = v_pi_of(tty);
                    if p.icit != i {
                        return Err(Error(
                            t_span.map(|_| {
                                format!("icit mismatch {:?} {:?}", i, p.icit)
                            }),
                            vec![],
                        ));
                    }
                    (p.dom, p)
                } else {
                    // Scala 式 apply（参考版）：非 Π 头先试把 `expr(arg)` 脱糖
                    // 成 `expr.apply(arg)`（icit 保持），失败截断 metas 再走
                    // 合成 Π
                    let meta_before = self.metas.len();
                    let apply_obj = Raw::Obj(
                        Box::new(t_raw),
                        Some(empty_span(SmolStr::new("apply"))),
                    );
                    let apply_call =
                        Raw::App(Box::new(apply_obj), Box::new(u_raw), Either::Icit(i));
                    if let Ok(result) = self.infer_expr(bump, cxt, &apply_call) {
                        return Ok(result);
                    }
                    self.metas.truncate(meta_before);
                    // 非 Π 头：合成 Π（定义域 + 余定义域挂洞）与之合一。
                    // 参考版把合成 Π 放在 unify_catch 的首位——忠实复刻，
                    // 只影响报错文案方向。合成 binder（"x"）按参考版
                    // cxt.bind 走全量 bind（env/telescope/pruning 扩展），
                    // 但名字不入表外泄（临时 cxt 只喂 fresh_meta）。
                    let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                    let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                    let a_t = self.quote(bump, cxt, cxt.lvl, a);
                    let cxt2 = self.bind_name(bump, cxt, "x", empty_span(()), a_t, a);
                    let cod_meta = self.fresh_meta(bump, &cxt2, v_u(0));
                    let cell = bump.alloc(PiCell {
                        name: "x",
                        icit: i,
                        dom: a,
                        env: cxt.env,
                        body: cod_meta,
                    });
                    self.unify_catch(bump, cxt, v_pi(cell), tty, t_span)?;
                    (a, &*cell)
                };
                let u_checked = self.check(bump, cxt, u, a)?;
                // 观察面（ref 2554-2556）：组合子字面每个元素独立 hover
                // 条目（键 = 元素 span，值 = 元素类型 Pi dom）；LSP 取最窄 span。
                if tuple_head {
                    self.push_hover(bump, cxt, u.to_span(), u.to_span(), a);
                }
                let arg_v = self.eval(bump, cxt, cxt.env, u_checked);
                // t u : B[x |-> u]
                let ty = {
                    let env = env_ext(bump, bcell.env, arg_v);
                    self.eval(bump, cxt, env, bcell.body)
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
                let a_eval = self.eval(bump, &cxt, cxt.env, a_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                let a_t = self.quote(bump, &cxt, cxt.lvl, a_eval);
                let cxt2 = self.bind_name(bump, cxt, &x.data, x.to_span(), a_t, a_eval);
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
                // Raw::Tm 注解是缓存的已查类型（trait 方法 Π 链复用）——经
                // 指针导入表取回本机结果，不再过 check_universe（参考版同款）
                let (a_checked, va) = if let Raw::Tm(rc_tm, rc_ty) = a_ty.as_ref() {
                    let tm: &'a Tm<'a> = self.tm_import_lookup(rc_tm);
                    let v = self.val_import_lookup(rc_ty);
                    (tm, v)
                } else {
                    let (a_checked, _) = self.check_universe(bump, cxt, a_ty)?;
                    let va = self.eval(bump, &cxt, cxt.env, a_checked);
                    (a_checked, va)
                };
                // 绑定名：let RHS 检查前设置（隐式 BindingName 参数合成用）
                let cxt_named = cxt.with_binding_name(x.data.clone());
                let t_checked = self.check(bump, &cxt_named, t2, va)?;
                let vt = self.eval(bump, &cxt, cxt.env, t_checked);
                let name: &'a str = bump.alloc_str(&x.data);
                // 观察面：let 无标注 → inlay 展示推断值类型（参考版 2601，
                // 注意其传的是右值语 vt、offset 取 binder 名结束）
                if matches!(a_ty.as_ref(), Raw::Hole(_)) {
                    self.push_inlay_hint(bump, cxt, x.to_span().end_offset, vt);
                }
                // 观察面：let binder 定义处 hover（参考版 2627 同点位）
                self.push_hover(bump, cxt, x.to_span(), x.to_span(), va);
                let cxt2 = self.define_name(bump, cxt, &x.data, x.to_span(), a_checked, t_checked, vt, va);
                let inferred = self.infer_expr(bump, &cxt2, u2);
                let (u_inferred, b) = inferred?;
                Ok((
                    bump.alloc(Tm::Let(name, a_checked, t_checked, u_inferred)),
                    b,
                ))
            }

            // Infer holes
            Raw::Hole(_) => {
                let new_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt, cxt.env, new_meta);
                let t = self.fresh_meta(bump, cxt, a);
                Ok((t, a))
            }

            Raw::LiteralIntro(literal) => Ok((
                bump.alloc(Tm::LiteralIntro(bump.alloc_str(&literal.data))),
                v_lit_ty(),
            )),

            // match 可推断（参考版 L13）：scrutinee 类型挂 fresh meta，经
            // check 编译后返回
            Raw::Match(_, _) => {
                let a_meta = self.fresh_meta(bump, cxt, v_u(0));
                let a = self.eval_fresh(bump, cxt, cxt.env, a_meta);
                let tm = self.check(bump, cxt, t, a)?;
                Ok((tm, a))
            }

            // enum 本体（Decl::Enum 注册期构造）：逐参数推断值 + 引读类型
            Raw::Sum(name, params, cases, universe, is_trait) => {
                let mut ps: Vec<SumParamT<'_>> = Vec::with_capacity(params.len());
                for (n, i, raw) in params {
                    let (value_checked, value_ty) = self.infer_expr(bump, cxt, raw)?;
                    let ty = self.quote(bump, cxt, cxt.lvl, value_ty);
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
                        *is_trait,
                    )),
                    v_u(*universe),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造 / 程序内 SumCase）：typ 只推
            // 断不检查；**index** 由 typ 值的 cases 表 position 查得（参考
            // 版 2687-2708）；typ 存**展开形**（求值后的类型 quote——下游
            // pretty/Nat 字面量/投影都假设展开形）
            Raw::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
            } => {
                let (typ_checked, _) = self.infer_expr(bump, cxt, typ)?;
                let typ_val = self.eval(bump, cxt, cxt.env, typ_checked);
                let index = match v_tag(typ_val) {
                    7 => match v_xcell_of(typ_val) {
                        XCell::Sum { cases, .. } => cases
                            .iter()
                            .position(|c| *c == case_name.data.as_str())
                            .ok_or_else(|| {
                                Error(
                                    case_name
                                        .clone()
                                        .map(|x| format!("no such constructor `{}`", x)),
                                    vec![],
                                )
                            })? as u32,
                        _ => {
                            return Err(Error(
                                case_name.clone().map(|_| {
                                    format!(
                                        "expected a sum type, got {}",
                                        debug_val(&self.spine, &self.defs, typ_val)
                                    )
                                }),
                                vec![],
                            ));
                        }
                    },
                    _ => {
                        return Err(Error(
                            case_name.clone().map(|_| {
                                format!(
                                    "expected a sum type, got {}",
                                    debug_val(&self.spine, &self.defs, typ_val)
                                )
                            }),
                            vec![],
                        ));
                    }
                };
                let mut ds: Vec<SumDataT<'_>> = Vec::with_capacity(datas.len());
                for (n, raw, i) in datas {
                    let (tm, _) = self.infer_expr(bump, cxt, raw)?;
                    ds.push(SumDataT {
                        name: bump.alloc_str(&n.data),
                        val: tm,
                        icit: *i,
                    });
                }
                let typ_expanded = self.quote(bump, cxt, cxt.lvl, typ_val);
                Ok((
                    bump.alloc(Tm::SumCase {
                        typ: typ_expanded,
                        index,
                        datas: bump.alloc_slice_fill_iter(ds),
                        is_trait: *is_trait,
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
        // package 前缀（参考版 infer 入口）：Def/Enum/TraitDecl/Class 的名字
        // 加 `pkg.` 前缀（方法名不加——trait_wrap 与 impl 方法匹配按写出的
        // 名字分派；Package/Import 自身不前缀）
        let d_owned;
        let d = if matches!(d, Decl::Package { .. } | Decl::Import { .. }) {
            d
        } else if let Some(prefix) = &cxt.namespace_prefix {
            d_owned = prefix_decl_name(d, prefix);
            &d_owned
        } else {
            d
        };
        self.infer_after_prefix_mut(bump, cxt, d)
    }

    /// 已前缀的 decl 推断（class Phase B 复用，免二次前缀——参考版
    /// `infer_after_prefix`）。
    fn infer_after_prefix<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        d: &Decl,
    ) -> Result<(DeclOut<'a>, Cxt<'a>), Error> {
        let mut cxt = clone_cxt(cxt);
        return self.infer_after_prefix_mut(bump, &mut cxt, d);
    }

    /// [`Self::infer_after_prefix`] 的就地版：调用方独占 cxt 时免浅克隆
    /// （infer_decl 顺序路径直通；COW 论证见 [`Self::fake_bind`]）。
    fn infer_after_prefix_mut<'a>(
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
                let this_meta = self.metas.len() as u32;
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
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, &cxt, cxt.env, typ_tm);
                // 递归：fake_bind 先把名字登记成 `Decl(name)` 存根（撞名即
                // redefine 报错），检查体，再 wrap_match_in_call 包装。
                let fake = self.fake_bind(bump, cxt, &name.data, name.to_span(), typ_tm, vtyp)?;
                let t_checked = self.check(bump, &fake, &bod, vtyp)?;
                let t_tm = self.wrap_match_in_call(bump, name.data.as_str(), t_checked);
                // solve_multi_trait(this_meta, **true**)（参考版 Def 臂
                // elaboration.rs:972）：失败 **返回 Err** 交上层（`.map_err(
                // |e| Error(name.span, ..))?`），不是 panic——参考版没有
                // unwrap。孪生早前误写成 unwrap，会让 trait 求解失败直接崩，
                // 掩盖后续的 Nat 默认化重试与丰富错误文案路径（HDL prelude
                // decl 308 的 `impl Add for UInt[width]` 就是这样从 panic
                // 变成可诊断的 Err，推进 171→308）。
                self.solve_multi_trait_ref(bump, &fake, this_meta, true)
                    .map_err(|e| {
                        let msg = e.clone();
                        Error(name.clone().map(move |_| msg.clone()), vec![])
                    })?;
                // no_metas 三元检查 + Nat 默认化重试 + 丰富错误文案
                if let Some((meta_names, oty)) =
                    no_metas(bump, self, &fake, t_tm)
                {
                    // --- Nat 默认化（Lean 式回退）：把类型值 meta 批量解成
                    // Nat 再重试 trait 求解，失败回滚 ---
                    // journal 帧（trait_wrap / run_pure_probe 同款）替代旧
                    // 的整表 clone 保存现场：重试期就地写走 journal_meta、
                    // append 由 truncate 收，失败恢复 = 弹帧回滚；成功 =
                    // 出帧保留（旧实现 `self.metas = saved_meta` 只走失败
                    // 分支，语义一致）。
                    let pre_meta_len = self.metas.len();
                    META_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
                    let nat_val = cxt.decls.get("Nat").map(|e| e.val).unwrap_or_else(v_u0);
                    let nat_ok = is_nat_sum_v(nat_val);
                    let nat_solved = if nat_ok {
                        let to_default: Vec<usize> = {
                            // 先拷出 Unsolved 类型值，避免闭包内 self.force_v(&mut)
                            // 与 self.metas 借用冲突
                            let unsolved: Vec<(usize, V)> = self
                                .metas
                                .iter()
                                .enumerate()
                                .filter_map(|(i, entry)| match entry {
                                    MetaEntry::Unsolved(ty, ..) => Some((i, *ty)),
                                    _ => None,
                                })
                                .collect();
                            unsolved
                                .into_iter()
                                .filter(|(_, ty)| v_tag(self.force_v(bump, cxt, *ty)) == 3)
                                .map(|(i, _)| i)
                                .collect()
                        };
                        if to_default.is_empty() {
                            // 无可默认化 meta：无写发生，直接出帧
                            meta_journal_discard();
                            false
                        } else {
                            for idx in &to_default {
                                if let MetaEntry::Unsolved(ty, ..) = &self.metas[*idx] {
                                    let ty = *ty;
                                    journal_meta(&mut self.metas, *idx, MetaEntry::Solved(nat_val, ty));
                                }
                            }
                            let _ = self.solve_multi_trait_ref(bump, &fake, this_meta, false);
                            if no_metas(bump, self, &fake, t_tm).is_none() {
                                meta_journal_discard();
                                true
                            } else {
                                meta_journal_rollback(&mut self.metas, pre_meta_len);
                                false
                            }
                        }
                    } else {
                        meta_journal_discard();
                        false
                    };
                    if !nat_solved {
                        return Err(self.mk_unsolved_meta_err(
                            bump, &fake, t_tm, meta_names, oty, &name.data,
                        ));
                    }
                }
                // 登记值：无参 def 的 body 含全局副作用（REPLAY_GLOBAL_OPS）
                // 时存 `Decl(name)` 占位不求值（副作用对当前 mutable 状态生
                // 效在调用点重放——`def_needs_replay`）；否则在**含存根的
                // fake 表**下求值（自引用停在国内）。
                let vt = if params.is_empty() {
                    let mut visiting = std::collections::HashSet::new();
                    let mut found = false;
                    let mut scan_truncated = false;
                    tm_scan_global_ops(&self.mutable, &fake.decls, t_tm, &mut visiting, &mut found, &mut scan_truncated);
                    if found {
                        v_xcell(bump.alloc(XCell::Decl { name: bump.alloc_str(&name.data) }))
                    } else {
                        self.eval(bump, &fake, fake.env, t_tm)
                    }
                } else {
                    self.eval(bump, &fake, fake.env, t_tm)
                };
                // 观察面：def 无显式返回类型 → inlay 推断返回类型
                // （参考版 1157-1176：peel_pi 后 quote 于 ret_lvl，no_metas
                // 干净才推；锚点 = 最后参数结束+1，无参则名结束）
                if matches!(*ret_type, Raw::Hole(_)) {
                    let (ret_val, ret_lvl, peeled) = self.peel_pi_collect(bump, cxt, vtyp);
                    let ret_tm = self.quote(bump, cxt, ret_lvl, ret_val);
                    if no_metas(bump, self, cxt, ret_tm).is_none() {
                        let mut names = types_names_list(cxt.types);
                        // peeled 为外→内剥集序；List 头 = 最内层 → 逆序 prepend
                        for pn in peeled.iter().rev() {
                            names = names.prepend(pn.clone());
                        }
                        let mut label = format!(
                            ": {}",
                            pretty_tm(0, names, &export(&self.symbol_table, ret_tm))
                        );
                        const MAX_LEN: usize = 80;
                        if label.chars().count() > MAX_LEN {
                            let truncated: String =
                                label.chars().take(MAX_LEN.saturating_sub(1)).collect();
                            label = format!("{}\u{2026}", truncated);
                        }
                        let pos = params
                            .last()
                            .map(|p| p.1.to_span().end_offset + 1)
                            .unwrap_or_else(|| name.to_span().end_offset);
                        self.inlay_hint_table.push((pos, label));
                    }
                }
                // 观察面：def 名定义处 hover（参考版 1153 同点位）。类型串
                // 此处渲染一次，`Rc` 共享给下方 decl_reg_in 的 typ_pretty
                // （同 vtyp 同 lvl 同管线，原实现各渲染一遍——评审机会 4）；
                // hover_table 推进顺序与原实现一致（先 push 后登记）。
                let rendered = self.render_typ_pretty(bump, cxt, vtyp);
                if let Some((r, _)) = &rendered {
                    self.hover_table
                        .push((name.to_span(), name.to_span(), r.as_ref().clone()));
                }
                drop(fake); // 释放 Rc 引用，decl_reg_in 的 make_mut 才能原地写
                let out = self.decl_reg_in(bump, cxt, &name.data, name.to_span(), t_tm, vt, typ_tm, vtyp, None, rendered);
                Ok((DeclOut::Def { name: bump.alloc_str(&name.data) }, out))
            }
            Decl::Println(t) => {
                // 立即 nf + pretty（参考版 run() 口径；defer_println 不移植）
                let (tm, _) = self.infer_expr(bump, cxt, t)?;
                let t_pretty = {
                    let v = self.eval(bump, cxt, cxt.env, tm);
                    let q = self.quote(bump, cxt, cxt.lvl, v);
                    let e = export(&self.symbol_table, q);
                    let names = types_names_list(cxt.types);
                    pretty_tm(0, names, &e)
                };
                Ok((DeclOut::Println(tm, t.to_span(), t_pretty), clone_cxt(cxt)))
            }
            Decl::Enum {
                is_trait,
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U(0)（与参考版
                // 同步，L07/L08 黑盒三轮修复、L09-L12 回移的 L13 形态）。
                // 域洞若保留，第 2+ 个参数的域是 AppPruning 部分应用 meta
                // （`?m A`），使用点显式供给隐式实参需解该 meta，invert 对
                // 非变量 spine 实参直接失败——误报 can't unify。宇宙扫描对
                // U(0) 域贡献 lvl 0 = max 恒等；显式标注与显式索引不动；
                // struct 脱糖走同一 Decl::Enum 臂。
                let params: Vec<_> = params
                    .iter()
                    .map(|(n, a, i)| {
                        let a = if *i == Icit::Impl && matches!(a, Raw::Hole(_)) {
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
                let new_params: Vec<(crate::parser_lib::Span<SmolStr>, Icit, Raw)> = params
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
                let new_cases: Vec<(crate::parser_lib::Span<SmolStr>, Raw)> = cases
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
                let cases_spanned: Vec<crate::parser_lib::Span<SmolStr>> = new_cases
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect();
                let sum = Raw::Sum(
                    name.clone(),
                    new_params,
                    cases_spanned,
                    universe_lvl,
                    *is_trait,
                );
                let typ = params
                    .iter()
                    .rev()
                    .fold(Raw::U(universe_lvl), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    });
                let bod = params.iter().rev().fold(sum, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                });
                let (typ_tm, _) = self.check_universe(bump, cxt, &typ)?;
                let vtyp = self.eval(bump, &cxt, cxt.env, typ_tm);
                let fake = self.fake_bind(bump, cxt, &name.data, name.to_span(), typ_tm, vtyp)?;
                let t_tm = self.check(bump, &fake, &bod, vtyp)?;
                // 登记值在含存根的 fake 表下求值（注意用**原 cxt 的 decl**：
                // Enum 臂与 Def 臂不同，参考版在此用 `cxt.decl`）
                let vt = self.eval(bump, cxt, fake.env, t_tm);
                drop(fake); // 释放 Rc 引用，decl_reg_in 的 make_mut 才能原地写
                let mut cxt = self.decl_reg_in(bump, cxt, &name.data, name.to_span(), t_tm, vt, typ_tm, vtyp, None, None);
                // 逐构造子注册：体 = λ(隐式参数, 字段) → SumCase{typ: ret, datas: 字段自身}；
                // **限定键 `EnumName.caseName` 登记**（无裸名别名——裸名靠 Var
                // 的后缀 fallback 解析；参考版 1322 同款）
                for ((case_name, binders, ret), (_, ctor_ty)) in
                    cases.iter().zip(new_cases.iter())
                {
                    let body_ret = Raw::SumCase {
                        typ: Box::new(ret.clone().unwrap_or(default_ret.clone())),
                        case_name: case_name.clone(),
                        datas: binders
                            .iter()
                            .map(|(n, _, i)| (n.clone(), Raw::Var(n.clone()), *i))
                            .collect(),
                        is_trait: *is_trait,
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
                    let vtyp = self.eval(bump, &cxt, cxt.env, typ_tm);
                    // 构造子良构性（参考版 elaboration.rs 同点同改）：ret 必须
                    // 是本 enum 的 Sum 且隐式参数位是 telescope 内 bare rigid。
                    // trait/class enum（is_trait）的 case 是方法签名，不适用。
                    if !*is_trait {
                        self.check_ctor_wf(bump, &cxt, &name.data, &case_name.data, vtyp)?;
                    }
                    let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                    let vt = self.eval(bump, &cxt, cxt.env, t_tm);
                    let case_key = format!("{}.{}", name.data, case_name.data);
                    cxt = self.decl_reg_in(bump, &mut cxt, &case_key, case_name.to_span(), t_tm, vt, typ_tm, vtyp, None, None);
                }
                Ok((DeclOut::Enum, cxt))
            }
            // trait 声明（参考版 1672-1767）：supertrait 经前缀解析 + DFS
            // 合并方法（路径集环检测，钻石不误报）；Self + params 组 enum
            // 参数（outParam 参数类型是 `outParam(...)` 应用）；方法表（含
            // 默认体）记入 trait_definition 与 solver.set_trait_out_params；
            // 本体脱糖成单构造子（`{Name}.mk`）的 trait enum（is_trait=true）
            Decl::TraitDecl { name, params, supertraits, methods, assoc_defaults } => {
                // X3：supertrait 名经 namespace 前缀解析
                let resolved_supertraits: Vec<crate::parser_lib::Span<SmolStr>> = supertraits
                    .iter()
                    .map(|s| {
                        let bare = s.data.clone();
                        let resolved = if self.tstate.definition.contains_key(&bare) {
                            bare
                        } else if let Some(prefix) = &cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, bare));
                            if self.tstate.definition.contains_key(&qualified) {
                                qualified
                            } else {
                                bare
                            }
                        } else {
                            bare
                        };
                        s.clone().map(|_| resolved.clone())
                    })
                    .collect();
                // DFS 合并 supertrait 方法（路径环检测）
                let mut all_methods = methods.clone();
                let mut stack: Vec<(SmolStr, std::collections::HashSet<SmolStr>)> =
                    resolved_supertraits
                        .iter()
                        .map(|s| {
                            let mut path = std::collections::HashSet::new();
                            path.insert(name.data.clone());
                            (s.data.clone(), path)
                        })
                        .collect();
                while let Some((st_name, path)) = stack.pop() {
                    if path.contains(&st_name) {
                        return Err(Error(
                            empty_span(format!(
                                "cyclic supertrait: `{}` appears twice in the chain",
                                st_name
                            )),
                            vec![],
                        ));
                    }
                    let mut path = path;
                    path.insert(st_name.clone());
                    if let Some((_, _, st_sts, st_methods)) =
                        self.tstate.definition.get(&st_name).cloned()
                    {
                        for st_st in &st_sts {
                            if path.contains(&st_st.data) {
                                return Err(Error(
                                    empty_span(format!(
                                        "cyclic supertrait: `{}` appears twice in the chain",
                                        st_st.data
                                    )),
                                    vec![],
                                ));
                            }
                            stack.push((st_st.data.clone(), path.clone()));
                        }
                        for st_m in &st_methods {
                            let name_exists = all_methods.iter().any(|(mn, _, _, _)| mn.data == st_m.0.data);
                            if !name_exists {
                                all_methods.push(st_m.clone());
                            }
                        }
                    }
                }
                self.tstate.solver.new_trait(name.data.clone());
                let mut param = vec![(
                    name.clone().map(|_| SmolStr::new("Self")),
                    Raw::Hole(name.to_span()),
                    Icit::Impl,
                )];
                param.append(&mut params.clone());
                let out_param = param
                    .iter()
                    .map(|x| match &x.1 {
                        Raw::App(t, ..)
                            if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam") =>
                        {
                            true
                        }
                        _ => false,
                    })
                    .collect::<Vec<_>>();
                self.tstate
                    .solver
                    .set_trait_out_params(name.data.clone(), out_param.clone());
                // 以下三表 kick 撤销帧记账（评审 B#2 二期）：insert 返回值
                // 即旧值（用户重声明 prelude trait 名时为 Some）。
                let old_def = self.tstate.definition.insert(
                    name.data.clone(),
                    (
                        param.clone(),
                        out_param.clone(),
                        resolved_supertraits.clone(),
                        all_methods.clone(),
                    ),
                );
                state_journal_record(StateUndo::TraitDefinitionSet(name.data.clone(), old_def));
                let old_op = self.tstate.out_param.insert(name.data.clone(), out_param);
                state_journal_record(StateUndo::TraitStateOutParamSet(name.data.clone(), old_op));
                // 关联类型默认值
                for (aname, adefault) in assoc_defaults {
                    let old_ad = self
                        .tstate
                        .assoc_defaults
                        .insert((name.data.clone(), aname.clone()), adefault.clone());
                    state_journal_record(StateUndo::TraitAssocDefaultSet(
                        (name.data.clone(), aname.clone()),
                        old_ad,
                    ));
                }
                let cxt2 = clone_cxt(cxt);
                let new_cases = vec![(
                    name.clone().map(|x| SmolStr::new(format!("{x}.mk"))),
                    all_methods
                        .iter()
                        .map(|(mn, mparams, mret, _mb)| {
                            (
                                mn.clone(),
                                std::iter::once((
                                    mn.clone().map(|_| SmolStr::new("this")),
                                    Raw::Var(mn.clone().map(|_| SmolStr::new("Self"))),
                                    Icit::Expl,
                                ))
                                .chain(mparams.iter().cloned())
                                .rev()
                                .fold(mret.clone(), |a, b| {
                                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                }),
                                Icit::Expl,
                            )
                        })
                        .collect(),
                    None,
                )];
                let (_, c) = self.infer_after_prefix(bump, &cxt2, &Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: new_cases,
                })?;
                Ok((DeclOut::Trait, c))
            }
            // impl 声明（参考版 1333-1671）：inherent（方法注册进类型
            // namespace，`x.m` 经 namespace 条目分派 + 算符方法登记
            // symbol_table）/ trait（实例注册 + from_class 过滤 + 默认方法
            // 填充 + assoc 默认补全 + `Trait.mk` 组装）。
            Decl::ImplDecl { name, params, trait_name, trait_params, methods, inherent, from_class } => {
                let mut cxt = clone_cxt(cxt);
                if *inherent {
                    // ── inherent impl（`impl Foo { ... }`）──
                    let name_raw = params
                        .iter()
                        .rev()
                        .fold(name.clone(), |a, b| {
                            Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                        });
                    let (name_t, _) = self.infer_expr(bump, &cxt, &name_raw)?;
                    let name_v = self.eval(bump, &cxt, cxt.env, name_t);
                    let type_name = raw_ctor_name(name).unwrap_or_else(|| SmolStr::new(""));
                    // 只有实例方法参与 `x.method` 分派
                    let method_names: Vec<SmolStr> = methods
                        .iter()
                        .filter(|(_, is_static)| !is_static)
                        .filter_map(|(x, _)| match x {
                            Decl::Def { name, .. } => Some(name.data.clone()),
                            _ => None,
                        })
                        .collect();
                    cxt.namespace = Some(bump.alloc(NsCons {
                        val: name_v,
                        methods: bump.alloc_slice_fill_iter(method_names.iter().cloned()),
                        type_name: bump.alloc_str(&type_name),
                        next: cxt.namespace,
                    }));
                    for (decl, is_static) in methods.iter() {
                        match decl {
                            Decl::Def { name: name_d, params: p, ret_type, body } => {
                                if !is_static {
                                    // 算符方法登记 symbol_table（体是 helper
                                    // 直接应用时记 (helper, 元数) → 算符）
                                    if is_operator_method_name(&name_d.data) {
                                        if let Some(head) = raw_ctor_name(body) {
                                            // kick 撤销帧记账（评审 B#2 二期）
                                            let k = (head.clone(), params.len() + 1 + p.len());
                                            let old =
                                                self.symbol_table.insert(k.clone(), name_d.data.clone());
                                            state_journal_record(StateUndo::SymbolTable(k, old));
                                        }
                                    }
                                    // 实例方法：前置 `this` 参数、注册为
                                    // `TypeName.method`（走 infer_after_prefix
                                    // 免二次前缀——方法名已全限定）
                                    let t = self.infer_after_prefix(bump, &cxt, &Decl::Def {
                                        name: name_d.clone().map(|x| {
                                            SmolStr::new(format!("{}.{x}", type_name))
                                        }),
                                        params: params
                                            .iter()
                                            .cloned()
                                            .chain(std::iter::once((
                                                name_d.to_span().map(|_| SmolStr::new("this")),
                                                name.clone(),
                                                Icit::Expl,
                                            )))
                                            .chain(p.iter().cloned())
                                            .collect(),
                                        ret_type: ret_type.clone(),
                                        body: body.clone(),
                                    })?;
                                    cxt = t.1;
                                } else {
                                    let static_name = format!("{}.{}", type_name, name_d.data);
                                    let t = self.infer_after_prefix(bump, &cxt, &Decl::Def {
                                        name: name_d.clone().map(|_| SmolStr::new(static_name.clone())),
                                        params: params.iter().cloned().chain(p.iter().cloned()).collect(),
                                        ret_type: ret_type.clone(),
                                        body: body.clone(),
                                    })?;
                                    cxt = t.1;
                                }
                            }
                            _ => {
                                return Err(Error(
                                    name.to_span().map(|_| {
                                        "unsupported method declaration in inherent impl".to_string()
                                    }),
                                    vec![],
                                ));
                            }
                        }
                    }
                } else {
                    // ── trait impl（`impl Trait for Ty`）──
                    // I3b：trait 名经 namespace 前缀解析（裸名优先）
                    let trait_full: SmolStr = {
                        let bare = trait_name.data.clone();
                        if self.tstate.out_param.contains_key(&bare) {
                            bare
                        } else if let Some(prefix) = &cxt.namespace_prefix {
                            let qualified = SmolStr::new(format!("{}.{}", prefix, bare));
                            if self.tstate.out_param.contains_key(&qualified) {
                                qualified
                            } else {
                                bare
                            }
                        } else {
                            bare
                        }
                    };
                    let mut temp_cxt = clone_cxt(&cxt);
                    for (x, a, _) in params.iter() {
                        let (a_checked, _) = self.check_universe(bump, &temp_cxt, a)?;
                        let a_eval = self.eval(bump, &temp_cxt, temp_cxt.env, a_checked);
                        let a_t = self.quote(bump, &temp_cxt, temp_cxt.lvl, a_eval);
                        temp_cxt = self.bind_name(bump, &temp_cxt, &x.data, x.to_span(), a_t, a_eval);
                    }
                    let (typ_tm, _) = self.check_universe(bump, &temp_cxt, name)?;
                    let typ_val = self.eval(bump, &temp_cxt, temp_cxt.env, typ_tm);
                    // 观察面（参考版 1452-1486 impl header hover 对）：
                    //  A) trait 名 token → trait 声明处（点 trait_name 跳声明，
                    //     而非实现自跳）；B) 实现方法名 token → trait 方法声明
                    //     名 span，值 = 方法自身 Pi 类型（实现参数上下文求值）。
                    if let Some(e) = cxt.decls.get(trait_full.as_str()) {
                        let (espan, evty) = (e.span, e.vty);
                        self.push_hover(bump, &cxt, trait_name.to_span(), espan, evty);
                    }
                    if let Some((_, _, _, trait_methods)) =
                        self.tstate.definition.get(&trait_full).cloned()
                    {
                        for (decl, _) in methods.iter() {
                            if let Decl::Def { name: def_name, params: m_params, ret_type: m_ret, .. } = decl {
                                if let Some((tm_name, _, _, _)) =
                                    trait_methods.iter().find(|(mn, _, _, _)| mn.data == def_name.data)
                                {
                                    let mty = m_params.iter().rev().fold(m_ret.clone(), |a, b| {
                                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                    });
                                    let mty_val = self
                                        .infer_expr(bump, &temp_cxt, &mty)
                                        .map(|(t, _)| self.eval(bump, &temp_cxt, temp_cxt.env, t))
                                        .unwrap_or_else(|_| v_u(0));
                                    self.push_hover(bump, &temp_cxt, def_name.to_span(), tm_name.to_span(), mty_val);
                                }
                            }
                        }
                    }
                    // 保留全部参数（含 outParam）——求解器要区分仅 out 参数
                    // 不同的实例（Into[String] vs Into[Bool]）
                    let mut trait_param: Vec<Rc<CVal>> = {
                        let fv = self.force_v(bump, &cxt, typ_val);
                        vec![v_to_ref_val(&self.spine, &self.defs, fv)]
                    };
                    for a in trait_params.iter() {
                        let (a_checked, _) = self.infer_expr(bump, &temp_cxt, a)?;
                        let a_eval = self.eval(bump, &temp_cxt, temp_cxt.env, a_checked);
                        let fv = self.force_v(bump, &cxt, a_eval);
                        trait_param.push(v_to_ref_val(
                            &self.spine,
                            &self.defs,
                            fv,
                        ));
                    }
                    let out_param = self
                        .tstate
                        .out_param
                        .get(&trait_full)
                        .ok_or(Error(
                            trait_name.clone().map(|n| format!("trait `{}` not declared", n)),
                            vec![],
                        ))?
                        .clone();
                    let typ_name = format!("{:?}{:?}", trait_full, trait_param);
                    let inst = Instance {
                        assertion: Assertion {
                            name: trait_full.clone(),
                            arguments: trait_param,
                        },
                        dependencies: crate::list::List::new(),
                        lvl: trait_name
                            .clone()
                            .to_span()
                            .map(|_| SmolStr::new(typ_name.clone())),
                    };
                    self.tstate.solver.impl_trait_for(trait_full.clone(), inst);
                    // from_class 过滤 + 默认方法填充
                    let mut methods = methods.clone();
                    let mut class_method_count = methods.len();
                    if let Some((_, _, _, trait_methods)) =
                        self.tstate.definition.get(&trait_full).cloned()
                    {
                        if *from_class {
                            methods.retain(|(decl, is_static)| {
                                !is_static
                                    && match decl {
                                        Decl::Def { name, .. } => trait_methods
                                            .iter()
                                            .any(|(tm, _, _, _)| tm.data == name.data),
                                        _ => false,
                                    }
                            });
                        }
                        class_method_count = methods.len();
                        for (tm_name, tm_params, tm_ret, tm_default_body) in trait_methods {
                            let has_impl = methods.iter().any(|(decl, _)| match decl {
                                Decl::Def { name, .. } => name.data == tm_name.data,
                                _ => false,
                            });
                            if !has_impl {
                                if let Some(default_body) = tm_default_body {
                                    methods.push((
                                        Decl::Def {
                                            name: tm_name,
                                            params: tm_params,
                                            ret_type: tm_ret,
                                            body: default_body,
                                        },
                                        false,
                                    ));
                                } else {
                                    return Err(Error(
                                        tm_name.map(|n| {
                                            format!("method `{}` has no default implementation", n)
                                        }),
                                        vec![],
                                    ));
                                }
                            }
                        }
                    }
                    // 关联类型缺省补全（trailing 顺序）
                    let mut trait_params = trait_params.clone();
                    if let Some((trait_params_def, _, _, _)) =
                        self.tstate.definition.get(&trait_full).cloned()
                    {
                        let assoc_names: Vec<(usize, SmolStr)> = trait_params_def
                            .iter()
                            .enumerate()
                            .filter_map(|(i, (pname, _, _))| {
                                if self
                                    .tstate
                                    .assoc_defaults
                                    .contains_key(&(trait_full.clone(), pname.data.clone()))
                                {
                                    Some((i, pname.data.clone()))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        if !assoc_names.is_empty() {
                            let expected_total = trait_params_def.len() - 1;
                            let expected_explicit = expected_total - assoc_names.len();
                            let provided_total = trait_params.len();
                            let provided_assoc = provided_total.saturating_sub(expected_explicit);
                            let missing_count = assoc_names.len().saturating_sub(provided_assoc);
                            if missing_count > 0 {
                                for (_, aname) in assoc_names.iter().skip(provided_assoc) {
                                    if let Some(default_type) = self
                                        .tstate
                                        .assoc_defaults
                                        .get(&(trait_full.clone(), aname.clone()))
                                    {
                                        trait_params
                                            .push(default_type.clone().unwrap_or(Raw::Hole(empty_span(()))));
                                    } else {
                                        return Err(Error(
                                            empty_span(format!(
                                                "associated type `{}` has no default value",
                                                aname
                                            )),
                                            vec![],
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    let mut ret = std::iter::once(name.clone())
                        .chain(trait_params.iter().cloned())
                        .fold(
                            Raw::Var(empty_span(SmolStr::new(format!("{}.mk", trait_full)))),
                            |ret, x| {
                                Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                            },
                        );
                    // class 生成的 impl：方法已由 inherent impl 以
                    // `TypeName.method` 登记——引用这些 def 而不是把体重查
                    // 成 λ（单一 elaboration、单一语义源，方法体内可经 this
                    // 调兄弟方法）
                    let class_type_name = if *from_class { raw_ctor_name(name) } else { None };
                    for (i, (decl, _)) in methods.into_iter().enumerate() {
                        if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                            if is_operator_method_name(&def_name.data) {
                                if let Some(head) = raw_ctor_name(&body) {
                                    if class_type_name.is_none() {
                                        // kick 撤销帧记账（评审 B#2 二期）
                                        let k = (head.clone(), params.len() + 1);
                                        let old = self
                                            .symbol_table
                                            .insert(k.clone(), def_name.data.clone());
                                        state_journal_record(StateUndo::SymbolTable(k, old));
                                    }
                                }
                            }
                            let method_expr = match &class_type_name {
                                Some(ty) if i < class_method_count => Raw::Var(
                                    def_name.map(|n| SmolStr::new(format!("{}.{}", ty, n))),
                                ),
                                _ => Raw::Lam(
                                    def_name.map(|_| SmolStr::new("this")),
                                    Either::Icit(Icit::Expl),
                                    Box::new(
                                        params
                                            .iter()
                                            .rev()
                                            .fold(body, |ret, x| {
                                                Raw::Lam(
                                                    x.0.clone(),
                                                    Either::Icit(x.2),
                                                    Box::new(ret),
                                                )
                                            }),
                                    ),
                                ),
                            };
                            ret = Raw::App(
                                Box::new(ret),
                                Box::new(method_expr),
                                Either::Icit(Icit::Expl),
                            );
                        }
                    }
                    // 实例本身登记为合成名 def
                    let (_, c) = self.infer_after_prefix(bump, &cxt, &Decl::Def {
                        name: empty_span(SmolStr::new(typ_name.clone())),
                        params: params.clone(),
                        ret_type: trait_params.into_iter().fold(
                            Raw::App(
                                Box::new(Raw::Var(empty_span(trait_full.clone()))),
                                Box::new(name.clone()),
                                Either::Icit(Icit::Impl),
                            ),
                            |a, b| {
                                Raw::App(Box::new(a), Box::new(b), Either::Icit(Icit::Impl))
                            },
                        ),
                        body: ret,
                    })?;
                    cxt = c;
                }
                Ok((DeclOut::TraitImpl, cxt))
            }
            Decl::Package { path } => {
                let pkg_path = path
                    .iter()
                    .map(|s| s.data.as_str())
                    .collect::<Vec<_>>()
                    .join(".");
                let mut cxt = clone_cxt(cxt);
                cxt.namespace_prefix = Some(SmolStr::new(&pkg_path));
                // G6：声明的 package 记为可见 namespace（后缀 fallback 准入）
                Rc::make_mut(&mut cxt.namespaces).insert(SmolStr::new(&pkg_path));
                // namespace 准入集变化 ⇒ suffix_memo 过滤结果过期
                self.suffix_memo_version = self.suffix_memo_version.wrapping_add(1);
                Ok((DeclOut::Package, cxt))
            }
            Decl::Import { prefix, names, wildcard } => {
                let prefix_str = prefix.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(".");
                let mut cxt = clone_cxt(cxt);
                // G6：import 的 namespace 记为可见
                if !prefix_str.is_empty() {
                    Rc::make_mut(&mut cxt.namespaces).insert(SmolStr::new(&prefix_str));
                    // namespace 准入集变化 ⇒ suffix_memo 过滤结果过期
                    self.suffix_memo_version = self.suffix_memo_version.wrapping_add(1);
                }
                // G4：拒绝单名 import
                if prefix.is_empty() && !names.is_empty() {
                    return Err(Error(
                        empty_span(format!(
                            "single-name import `{}` is not supported; import a package namespace instead (e.g. `import ns.{}`)",
                            names.join(", "),
                            names.join(", ")
                        )),
                        vec![],
                    ));
                }
                // 收集 (alias, 全键) 对——不动 decl 表（import 是文件局部可见性）
                let mut aliases: Vec<(SmolStr, SmolStr)> = vec![];
                if *wildcard {
                    let prefix_search = format!("{}.", prefix_str);
                    let matched: Vec<SmolStr> = cxt
                        .decls
                        .keys()
                        .filter(|k| k.starts_with(&prefix_search))
                        .cloned()
                        .collect();
                    if matched.is_empty() {
                        return Err(Error(
                            empty_span(format!(
                                "cannot import '{}': no such namespace in scope",
                                prefix_str
                            )),
                            vec![],
                        ));
                    }
                    for full in matched {
                        let stripped = SmolStr::new(full.strip_prefix(&prefix_search).unwrap());
                        aliases.push((stripped, full));
                    }
                    // prefix 自身是 decl（如 `import mylib.Tree` 且
                    // `mylib.Tree` 是类型）时也带进来
                    if let Some(k) = cxt
                        .decls
                        .keys()
                        .find(|k| k.as_str() == prefix_str)
                        .cloned()
                    {
                        let last = prefix.last().unwrap().clone();
                        aliases.push((last, k));
                    }
                } else {
                    for n in names {
                        let full_name = SmolStr::new(format!("{}.{}", prefix_str, n));
                        if !cxt.decls.contains_key(full_name.as_str()) {
                            return Err(Error(
                                empty_span(format!(
                                    "cannot import '{}': not in scope",
                                    full_name
                                )),
                                vec![],
                            ));
                        }
                        aliases.push((n.clone(), full_name.clone()));
                        // 点状成员别名：`import mylib.Tree` 带进 `Tree.mk`
                        // / `Tree.leaf`…（`.mk` 简写与限定成员访问保活）
                        let member_prefix = format!("{}.", full_name);
                        let members: Vec<SmolStr> = cxt
                            .decls
                            .keys()
                            .filter(|k| k.starts_with(&member_prefix))
                            .cloned()
                            .collect();
                        for full in members {
                            let stripped = full.strip_prefix(&member_prefix).unwrap();
                            aliases.push((
                                SmolStr::new(format!("{}.{}", n, stripped)),
                                full,
                            ));
                        }
                    }
                }
                // I1：冲突别名拒绝
                for (alias, full) in aliases {
                    if let Some(existing) = self.import_map.get(&alias) {
                        if existing != &full {
                            return Err(Error(
                                empty_span(format!(
                                    "ambiguous import: '{}' refers to both '{}' and '{}'",
                                    alias, existing, full
                                )),
                                vec![],
                            ));
                        }
                    } else {
                        // kick 撤销帧记账（评审 B#2 二期）：此臂键必为新。
                        state_journal_record(StateUndo::ImportMap(alias.clone(), None));
                        self.import_map.insert(alias, full);
                    }
                }
                Ok((DeclOut::Import, cxt))
            }
            Decl::Derive { .. } => {
                panic!("Derive should have been expanded before elaboration")
            }
            Decl::Class { name, params, items, traits } => {
                // ══ Phase A：在 create 的参数上下文里逐字段推类型（struct
                // 尚不存在）══（参考版 1861-1967 逐句）
                let __probe = std::env::var_os("TYPORT_DECL_PROBE").is_some();
                let __pa0 = self.metas.len();
                if __probe {
                    eprintln!("[CLASS {}] twin A-start", name.data);
                }
                let mut a_cxt = clone_cxt(cxt);
                for (pname, pty, _) in params.iter() {
                    let (a_checked, _) = self.check_universe(bump, &a_cxt, pty)?;
                    let a_eval = self.eval(bump, &a_cxt, a_cxt.env, a_checked);
                    let a_t = self.quote(bump, &a_cxt, a_cxt.lvl, a_eval);
                    a_cxt = self.bind_name(bump, &a_cxt, &pname.data, pname.to_span(), a_t, a_eval);
                }
                if traits.iter().any(|(t, _)| t.data == "Module") {
                    let (a_checked, _) = self.check_universe(
                        bump,
                        &a_cxt,
                        &Raw::Var(empty_span(SmolStr::new("BindingName"))),
                    )?;
                    let a_eval = self.eval(bump, &a_cxt, a_cxt.env, a_checked);
                    let a_t = self.quote(bump, &a_cxt, a_cxt.lvl, a_eval);
                    a_cxt = self.bind_name(
                        bump,
                        &a_cxt,
                        "bn",
                        empty_span(()),
                        a_t,
                        a_eval,
                    );
                }
                let mut struct_field_types: Vec<(crate::parser_lib::Span<SmolStr>, Raw)> =
                    Vec::new();
                // Phase-A 复用数据（参考版 Rc 四元组的导出侧；本机侧经
                // 指针导入表取回）
                struct PreA {
                    name: crate::parser_lib::Span<SmolStr>,
                    rc_tm: Rc<CTm>,
                    rc_a: Rc<CTm>,
                    rc_ty: Rc<CVal>,
                }
                let mut prechecked: Vec<PreA> = Vec::new();
                let mut bn_refs: Vec<bool> = Vec::new();
                let mut stmt_idx = 0usize;
                let mut bind_idx = 0usize;
                for item in items.iter() {
                    let (n, ty, val) = match item {
                        ClassItem::Field(n, t, v) => (n.clone(), t.clone(), v.clone()),
                        ClassItem::Stmt(expr) => {
                            let n = empty_span(SmolStr::new(format!("_s{stmt_idx}")));
                            stmt_idx += 1;
                            (n.clone(), Raw::Hole(n.to_span()), expr.clone())
                        }
                        ClassItem::Method(_, _) => continue,
                    };
                    let (a_checked, _) = self.check_universe(bump, &a_cxt, &ty)?;
                    let va = self.eval(bump, &a_cxt, a_cxt.env, a_checked);
                    // 未注解字段直解 fresh meta 为推断类型；注解字段按注解查
                    let cxt_named = a_cxt.with_binding_name(n.data.clone());
                    let __im0 = self.metas.len();
                    let t_checked = self.check(bump, &cxt_named, &val, va)?;
                    if __probe {
                        eprintln!("[PHA {}] {} ck={} metas+{}", name.data, n.data, bind_idx, self.metas.len() - __im0);
                    }
                    let vt = self.eval(bump, &a_cxt, a_cxt.env, t_checked);
                    if matches!(ty, Raw::Hole(_)) {
                        if v_tag(va) == 5 {
                            let m = v_meta_of(va);
                            if let MetaEntry::Unsolved(mty, ..) = &self.metas[m as usize] {
                                let mty = *mty;
                                journal_meta(&mut self.metas, m as usize, MetaEntry::Solved(vt, mty));
                            }
                        }
                    }
                    let raw_ty = if matches!(ty, Raw::Hole(_)) {
                        // 未注解：字段类型 = 推断类型（重表达为 Raw；不可表
                        // 达则回退 Hole——参考版同款）
                        let field_ty = self.force_v(bump, &a_cxt, va);
                        let q = self.quote(bump, &a_cxt, a_cxt.lvl, field_ty);
                        let e = export(&self.symbol_table, q);
                        let names = types_names_list(a_cxt.types);
                        tm_to_raw_type(&names, &e).unwrap_or(Raw::Hole(n.to_span()))
                    } else {
                        ty.clone()
                    };
                    if matches!(item, ClassItem::Field(..)) {
                        struct_field_types.push((n.clone(), raw_ty));
                    }
                    bn_refs.push(tm_refs_bn(t_checked, bind_idx));
                    bind_idx += 1;
                    let a_t = self.quote(bump, &a_cxt, a_cxt.lvl, va);
                    a_cxt = self.define_name(
                        bump,
                        &a_cxt,
                        &n.data,
                        n.to_span(),
                        a_checked,
                        t_checked,
                        vt,
                        va,
                    );
                    // 导出参考版 (name, t_checked, va, a_checked) + 全部登记
                    // 指针导入表（parser 的 build_class_chain_tm /
                    // maybe_prechecked_method_body 会以 (t, va) 与
                    // (a_checked, va) 两种组合嵌 Raw::Tm）
                    // （kick 撤销帧同步记账，评审 B#2 二期）
                    let rc_tm = export(&self.symbol_table, t_checked);
                    let rc_a = export(&self.symbol_table, a_checked);
                    let rc_ty = v_to_ref_val(&self.spine, &self.defs, va);
                    let kt = Rc::as_ptr(&rc_tm) as usize;
                    let old_t = self.tm_import.insert(
                        kt,
                        unsafe {
                            std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(t_checked)
                        },
                    );
                    state_journal_record(StateUndo::TmImport(kt, old_t));
                    let ka = Rc::as_ptr(&rc_a) as usize;
                    let old_a = self.tm_import.insert(
                        ka,
                        unsafe {
                            std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(a_checked)
                        },
                    );
                    state_journal_record(StateUndo::TmImport(ka, old_a));
                    let kv = Rc::as_ptr(&rc_ty) as usize;
                    let old_v = self.val_import.insert(kv, va);
                    state_journal_record(StateUndo::ValImport(kv, old_v));
                    prechecked.push(PreA {
                        name: n,
                        rc_tm,
                        rc_a,
                        rc_ty,
                    });
                }
                // ══ Phase B：组装 struct + create + inherent impl + trait
                // impls（共享 parser 的 expand_class_decls；Raw::Tm 经指针
                // 导入表复用 Phase A 结果）══
                if __probe {
                    eprintln!("[CLASS {}] twin phaseA metas+{}", name.data, self.metas.len() - __pa0);
                }
                let __pb0 = self.metas.len();
                let prechecked_items: Vec<(
                    crate::parser_lib::Span<SmolStr>,
                    Rc<CTm>,
                    Rc<CVal>,
                    Rc<CTm>,
                )> = prechecked
                    .into_iter()
                    .map(|p| (p.name, p.rc_tm, p.rc_ty, p.rc_a))
                    .collect();
                let pc = super::parser::PrecheckedItems {
                    items: prechecked_items,
                    bn_refs: bn_refs.clone(),
                };
                let decls = super::parser::expand_class_decls(
                    name.clone(),
                    params.clone(),
                    items.clone(),
                    traits.clone(),
                    struct_field_types.clone(),
                    Some(&pc),
                );
                let mut cxt2 = clone_cxt(cxt);
                for (di, dd) in decls.into_iter().enumerate() {
                    let (_, c) = self.infer_after_prefix(bump, &cxt2, &dd)?;
                    cxt2 = c;
                    if __probe {
                        eprintln!("[CLASS {}] twin phaseB[{}] metas+{}", name.data, di, self.metas.len() - __pb0);
                    }
                }
                Ok((DeclOut::Class, cxt2))
            }
        }
    }

    /// `wrap_match_in_call`（参考版 mod.rs:1029）：λ 链体顶端的 Match 包成
    /// `Call(name, Var 链+icit, Match)`——eval 的 Call 帧由此产出
    /// `Val::Call`（println 卡住 match 的显示走 `name(args)`）。
    fn wrap_match_in_call<'a>(
        &mut self,
        bump: &'a Bump,
        name: &str,
        tm: &'a Tm<'a>,
    ) -> &'a Tm<'a> {
        // 迭代剥 λ 链，Match 顶点时组装（icit 收集序 = 参考版）
        fn go<'a>(bump: &'a Bump, name: &str, tm: &'a Tm<'a>, l: u32, icits: &mut Vec<Icit>) -> &'a Tm<'a> {
            match tm {
                Tm::Lam(span_n, i, body) => {
                    icits.push(*i);
                    let r = go(bump, name, body, l + 1, icits);
                    icits.pop();
                    bump.alloc(Tm::Lam(span_n, *i, r))
                }
                Tm::Match(scru, cases) => {
                    // List 序（参考版 prepend 构造）：head = Var(l-1) … 尾 =
                    // Var(0)；icit 平行 [icits[0], …, icits[l-1]]
                    let mut argv: Vec<(&'a Tm<'a>, Icit)> = Vec::with_capacity(l as usize);
                    for i in 0..l {
                        argv.push((
                            bump.alloc(Tm::Var(l - 1 - i)),
                            icits[i as usize],
                        ));
                    }
                    bump.alloc(Tm::Call(
                        bump.alloc_str(name),
                        bump.alloc_slice_copy(&argv),
                        bump.alloc(Tm::Match(scru, cases)),
                    ))
                }
                _ => tm,
            }
        }
        let _ = self;
        go(bump, name, tm, 0, &mut Vec::new())
    }

    /// Def 臂的未解 meta 报错（参考版 1015-1090 的文案族）：trait 型给
    /// "cannot infer typeclass / no instance / no matching instance +
    /// available instances"（Into 特判给 resize 提示）；否则 "find unsolved
    /// meta with type"。meta_names 为 no_metas 给出的名字表。
    #[allow(clippy::too_many_arguments)]
    fn mk_unsolved_meta_err<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t_tm: &'a Tm<'a>,
        meta_names: crate::list::List<SmolStr>,
        oty: V,
        _def_name: &str,
    ) -> Error {
        let _ = t_tm;
        let oty_f = self.force_v(bump, cxt, oty);
        if v_tag(oty_f) == 7 {
            if let XCell::Sum { name, params, is_trait: true, .. } = v_xcell_of(oty_f) {
                let has_flex = params
                    .iter()
                    .any(|p| v_tag(self.force_v(bump, cxt, p.val)) == 5);
                let instances = self
                    .tstate
                    .solver
                    .class_instances
                    .get(&SmolStr::new(name))
                    .cloned();
                if has_flex {
                    return Error(
                        empty_span(format!(
                            "cannot infer typeclass `{}`: type parameter is unknown",
                            name
                        )),
                        vec![],
                    );
                } else if params.is_empty() {
                    return Error(
                        empty_span(format!("no instance of typeclass `{}`", name)),
                        vec![],
                    );
                } else {
                    // 参数 pretty（借用 meta 上下文名单——近似参考版 meta_cxt）
                    let names = match meta_names.head() {
                        Some(_) => types_names_list(cxt.types),
                        None => types_names_list(cxt.types),
                    };
                    let pretty_val = |mach: &mut Machine, v: V| -> String {
                        let q = mach.quote(bump, cxt, cxt.lvl, v);
                        let e = export(&mach.symbol_table, q);
                        pretty_tm(0, names.clone(), &e)
                    };
                    let first = pretty_val(self, params[0].val);
                    let rest: Vec<String> = params[1..]
                        .iter()
                        .map(|p| pretty_val(self, p.val))
                        .collect();
                    let trait_repr = if rest.is_empty() {
                        name.to_string()
                    } else {
                        format!("{}[{}]", name, rest.join(", "))
                    };
                    if instances.as_ref().map_or(true, |i| i.is_empty()) {
                        return Error(
                            empty_span(format!(
                                "no instance of typeclass `{}` for types `{}`",
                                trait_repr, first
                            )),
                            vec![],
                        );
                    } else {
                        let insts = instances.unwrap();
                        return Error(
                            empty_span(format!(
                                "no matching instance of typeclass `{}` for types `{}`\navailable instances: {}",
                                trait_repr,
                                first,
                                insts.iter().map(|i| i.lvl.data.to_string()).collect::<Vec<_>>().join(", "),
                            )),
                            vec![],
                        );
                    }
                }
            }
        }
        // 其余：find unsolved meta with type
        let q = self.quote(bump, cxt, cxt.lvl, oty);
        let e = export(&self.symbol_table, q);
        let names = types_names_list(cxt.types);
        Error(
            empty_span(format!(
                "find unsolved meta with type `{}`",
                pretty_tm(0, names, &e)
            )),
            vec![],
        )
    }
}

/// 参考版 `nat_chain_len`（elaboration.rs 一带）：SumCase 链是否是具体
/// `succ^k zero`（Nat 类型）——是则给 k。
fn nat_chain_len_ref(tm: &CTm) -> Option<u64> {
    let mut k = 0u64;
    let mut cur = tm;
    loop {
        match cur {
            CTm::SumCase {
                typ: t2,
                index: 0,
                datas,
                ..
            } if matches!(t2.as_ref(), CTm::Sum(name, _, _, false) if name.data == "Nat")
                && datas.is_empty() =>
            {
                return Some(k)
            }
            CTm::SumCase {
                typ: t2,
                index: 1,
                datas,
                ..
            } if matches!(t2.as_ref(), CTm::Sum(name, _, _, false) if name.data == "Nat")
                && datas.len() == 1
                && datas[0].0.data == "n" =>
            {
                k += 1;
                cur = &datas[0].1;
            }
            _ => return None,
        }
    }
}

/// 参考 `Infer::tm_to_raw_type`：已导出的 CTm → 可作注解的 Raw（Var 按名字
/// 表回名；Sum/SumCase 复原应用形；Nat 链复原字面量；不可表达 → None，
/// 调用方回退 Hole）。
fn tm_to_raw_type(names: &crate::list::List<SmolStr>, tm: &CTm) -> Option<Raw> {
    fn go(tm: &CTm, names: &crate::list::List<SmolStr>) -> Option<Raw> {
        match tm {
            CTm::Var(ix) => {
                let name = names.iter().nth(ix.0 as usize)?;
                Some(Raw::Var(empty_span(name.clone())))
            }
            CTm::Decl(n) => Some(Raw::Var(n.clone())),
            CTm::Obj(f, n) => Some(Raw::Obj(Box::new(go(f, names)?), Some(n.clone()))),
            CTm::App(f, a, i) => Some(Raw::App(
                Box::new(go(f, names)?),
                Box::new(go(a, names)?),
                Either::Icit(*i),
            )),
            CTm::AppPruning(f, _) => go(f, names),
            CTm::Lam(x, i, b) => Some(Raw::Lam(
                x.clone(),
                Either::Icit(*i),
                Box::new(go(b, &names.prepend(x.data.clone()))?),
            )),
            CTm::Pi(x, i, a, b) => Some(Raw::Pi(
                x.clone(),
                *i,
                Box::new(go(a, names)?),
                Box::new(go(b, &names.prepend(x.data.clone()))?),
            )),
            CTm::U(u) => Some(Raw::U(*u)),
            CTm::Sum(name, params, _, _) => {
                let mut acc = Raw::Var(name.clone());
                for (_, v, _, i) in params.iter() {
                    acc = Raw::App(Box::new(acc), Box::new(go(v, names)?), Either::Icit(*i));
                }
                Some(acc)
            }
            CTm::SumCase { is_trait, typ, index, datas } => {
                if !*is_trait {
                    if let Some(k) = nat_chain_len_ref(tm) {
                        return Some(Raw::Nat(empty_span(k)));
                    }
                }
                let case_name = match typ.as_ref() {
                    CTm::Sum(_, _, cases, _) => cases.iter().nth(*index as usize)?.clone(),
                    _ => return None,
                };
                let ds = datas
                    .iter()
                    .map(|(n, d, i)| Some((n.clone(), go(d, names)?, *i)))
                    .collect::<Option<Vec<_>>>()?;
                Some(Raw::SumCase {
                    is_trait: *is_trait,
                    typ: Box::new(go(typ, names)?),
                    case_name,
                    datas: ds,
                })
            }
            // 项专属 / 不可表达节点：调用方回退 Hole
            _ => None,
        }
    }
    go(tm, names)
}

/// decl 名字的 package 前缀（参考版 `prefix_decl_name`，elaboration.rs:36
/// 一带）：Def/Enum/TraitDecl/Class 的名字加前缀；嵌套 Package.path 逐段
/// 累加；方法名一律不加。
fn prefix_decl_name(d: &Decl, prefix: &str) -> Decl {
    let qual = |n: &crate::parser_lib::Span<SmolStr>| {
        n.clone().map(|x| SmolStr::new(format!("{}.{}", prefix, x)))
    };
    match d {
        Decl::Def { name, params, ret_type, body } => Decl::Def {
            name: qual(name),
            params: params.clone(),
            ret_type: ret_type.clone(),
            body: body.clone(),
        },
        Decl::Enum { is_trait, name, params, cases } => Decl::Enum {
            is_trait: *is_trait,
            name: qual(name),
            params: params.clone(),
            cases: cases.clone(),
        },
        Decl::TraitDecl { name, params, supertraits, methods, assoc_defaults } => {
            Decl::TraitDecl {
                name: qual(name),
                params: params.clone(),
                supertraits: supertraits.clone(),
                methods: methods.clone(),
                assoc_defaults: assoc_defaults.clone(),
            }
        }
        Decl::Class { name, params, items, traits } => Decl::Class {
            name: qual(name),
            params: params.clone(),
            items: items.clone(),
            traits: traits.clone(),
        },
        Decl::Package { path } => {
            let new_path: Vec<crate::parser_lib::Span<SmolStr>> =
                vec![empty_span(SmolStr::new(prefix))]
                    .into_iter()
                    .chain(path.iter().cloned())
                    .collect();
            Decl::Package { path: new_path }
        }
        other => other.clone(),
    }
}

/// Raw 的头构造子名（参考版 `raw_ctor_name`）。
fn raw_ctor_name(raw: &Raw) -> Option<SmolStr> {
    match raw {
        Raw::Var(name) => Some(name.data.clone()),
        Raw::App(head, _, _) => raw_ctor_name(head),
        _ => None,
    }
}

/// 算符方法名判定（参考版 `is_operator_method_name`）。
fn is_operator_method_name(name: &str) -> bool {
    name.chars().next().map(super::is_operator_char).unwrap_or(false)
}

/// 项是否引用第 `bind_idx` 个（非方法）绑定的层级（bn 引用判定——参考版
/// `tm_refs_bn` 的逐句移植）。
///
/// 快版 `Var(i)` 与参考版 `Ix(i)` 表示同构（产生侧同为 `cxt.lvl - blvl - 1`，
/// 导出侧恒等映射）——de Bruijn 索引随 λ 深度增大而增大：目标绑定在值顶层的
/// 索引是 `bind_idx`（bn 绑在 params 层，第 i 项在 params + bn + i 层检查，
/// 索引 = (params+1+i) − 1 − params = i），每进一层 λ 索引 +1。原实现误写成
/// `depth + i == bind_idx`（符号反向）：深度 >0 时既漏判真实 bn 引用（复用
/// 时会静默把引用位移到 `this`——参考版注释警告的情形），又误判普通字段值
/// 为 bn 引用，使 `maybe_prechecked_method_body` 的复用门恒真、tree/create
/// 方法体整链重推（18-utils 隐参分叉的根因）。
fn tm_refs_bn(tm: &Tm<'_>, bind_idx: usize) -> bool {
    fn go(tm: &Tm<'_>, i: usize, d: usize) -> bool {
        match tm {
            Tm::Var(ix) => *ix as usize == i + d,
            Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => false,
            Tm::Obj(h, _) => go(h, i, d),
            Tm::Lam(_, _, b) => go(b, i, d + 1),
            Tm::App(f, a, _) => go(f, i, d) || go(a, i, d),
            Tm::AppPruning(h, _) => go(h, i, d),
            Tm::Pi(_, _, a, b) => go(a, i, d) || go(b, i, d + 1),
            Tm::Let(_, a, t, u) => go(a, i, d) || go(t, i, d) || go(u, i, d + 1),
            Tm::Sum(_, ps, _, _) => ps.iter().any(|p| go(p.val, i, d) || go(p.ty, i, d)),
            Tm::SumCase { typ, datas, .. } => {
                go(typ, i, d) || datas.iter().any(|x| go(x.val, i, d))
            }
            Tm::Match(s, cases) => go(s, i, d) || cases.iter().any(|(_, b)| go(b, i, d + 1)),
            // Call 体是内联 def 体；字段值不含它，深度多算只损失优化
            // （回退），不会误复用（参考版同款注释）。
            Tm::Call(_, args, body) => args.iter().any(|(a, _)| go(a, i, d)) || go(body, i, d + 1),
        }
    }
    go(tm, bind_idx, 0)
}

/// `Raw::Match` 推断错误用的 span（to_span 的借用版）。
fn t_span_of(t: &Raw) -> crate::parser_lib::Span<()> {
    t.to_span()
}

/// `Val::U(0)` 占位（参考版 struct 字段剥链的 `unwrap_or(Val::U(0))`）。
pub(super) fn v_u0() -> V {
    v_u(0)
}

/// Cxt 的浅克隆（env/引用 Copy，names 是 Rc 克隆——快照共享）。
pub(super) fn clone_cxt<'a>(cxt: &Cxt<'a>) -> Cxt<'a> {
    Cxt {
        env: cxt.env,
        update_from: cxt.update_from,
        names: cxt.names.clone(),
        types: cxt.types,
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
        decls: cxt.decls.clone(),
        namespace: cxt.namespace,
        namespace_prefix: cxt.namespace_prefix.clone(),
        namespaces: cxt.namespaces.clone(),
        binding_name: cxt.binding_name.clone(),
    }
}

/// 槽位向量 → 纯链环境（头 = 最内层）。
pub(super) fn chain_env<'a>(bump: &'a Bump, slots: &[V]) -> Env<'a> {
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
    /// println：源码 span + elaborated 体（run 的 nf 输出用；原 Println 行
    /// 的声明 span 与宏展开产物同形）。
    Println(&'a Tm<'a>, crate::parser_lib::Span<()>, String),
    Enum,
    Trait,
    TraitImpl,
    Package,
    Import,
    Class,
}

// ── 第一/二组表归还档回归测试（mem-l13-opt §3.3 收口，perf-l13-round §3.1.3）──
#[cfg(test)]
mod clear_round_reclaim_tests {
    //! 到阈值的表在 [`Machine::clear_round`] 后归还桶数组（长会话 RSS 不再
    //! 滞留峰值容量）；阈值下的表保容量（稳态复用不回退，分配计数零变化）。

    use super::*;

    /// 把各表填到各自阈值（归还判据是容量越过 `min_entries`，恰过阈值即
    /// 成立；`clear_round` 对本测试只触表操作，不涉 bump）。
    fn stuffed_machine() -> Machine {
        let mut m = Machine::new();
        for i in 0..TBL_SHRINK_MIN_ENTRIES {
            let k = SmolStr::new(format!("sym{i}"));
            m.symbol_table.insert((k.clone(), 0), k.clone());
            let k = SmolStr::new(format!("imp{i}"));
            m.import_map.insert(k.clone(), k);
            let k = SmolStr::new(format!("q{i}"));
            m.decl_suffix_index.insert(k.clone(), Rc::new(Vec::new()));
            m.suffix_indexed_keys.insert(k.clone());
            m.suffix_memo.insert(
                k,
                SuffixMemo::Pos { full_key: SmolStr::new(""), bucket_ptr: 0 },
            );
            let k = SmolStr::new(format!("mut{i}"));
            m.mutable.borrow_mut().map.insert(k, v_u(i as u32));
        }
        for i in 0..OBS_TBL_SHRINK_MIN_ENTRIES {
            m.hover_table.push((empty_span(()), empty_span(()), String::new()));
            m.completion_table.push((empty_span(()), SmolStr::new("")));
            m.inlay_hint_table.push((i as u32, String::new()));
            m.println_spans.push((empty_span(()), String::new()));
            m.check_issue_lines.push((i, String::new()));
            m.ctor_hover_memo.insert(SmolStr::new(format!("c{i}")), Rc::from(""));
        }
        m.trait_metas.extend(0..SPINE_SHRINK_MIN_ENTRIES as u32);
        let leak: &'static Tm<'static> = Box::leak(Box::new(Tm::U(0)));
        for i in 0..PTR_TBL_SHRINK_MIN_ENTRIES {
            m.tm_import.insert(i, leak);
            m.val_import.insert(i, v_u(i as u32));
        }
        m
    }

    #[test]
    fn oversized_tables_shrink_on_clear_round() {
        let mut m = stuffed_machine();
        assert!(m.symbol_table.capacity() >= TBL_SHRINK_MIN_ENTRIES);
        m.clear_round();
        assert_eq!(m.symbol_table.capacity(), 0, "symbol_table 桶未归还");
        assert_eq!(m.import_map.capacity(), 0, "import_map 桶未归还");
        assert_eq!(m.decl_suffix_index.capacity(), 0, "decl_suffix_index 桶未归还");
        assert_eq!(m.suffix_indexed_keys.capacity(), 0, "suffix_indexed_keys 桶未归还");
        assert_eq!(m.suffix_memo.capacity(), 0, "suffix_memo 桶未归还");
        assert_eq!(m.trait_metas.capacity(), 0, "trait_metas 缓冲未归还");
        assert_eq!(m.tm_import.capacity(), 0, "tm_import 桶未归还");
        assert_eq!(m.val_import.capacity(), 0, "val_import 桶未归还");
        assert_eq!(m.hover_table.capacity(), 0, "hover_table 缓冲未归还");
        assert_eq!(m.completion_table.capacity(), 0, "completion_table 缓冲未归还");
        assert_eq!(m.inlay_hint_table.capacity(), 0, "inlay_hint_table 缓冲未归还");
        assert_eq!(m.println_spans.capacity(), 0, "println_spans 缓冲未归还");
        assert_eq!(m.check_issue_lines.capacity(), 0, "check_issue_lines 缓冲未归还");
        assert_eq!(m.ctor_hover_memo.capacity(), 0, "ctor_hover_memo 桶未归还");
        let mu = m.mutable.borrow();
        assert_eq!(mu.map.capacity(), 0, "mutable.map 桶未归还");
        assert_eq!(mu.replay.capacity(), 0, "mutable.replay 桶未归还");
        assert_eq!(mu.check_lines.capacity(), 0, "check_lines 缓冲未归还");
        assert_eq!(mu.check_line_set.capacity(), 0, "check_line_set 桶未归还");
        assert_eq!(mu.check_seen.capacity(), 0, "check_seen 桶未归还");
    }

    #[test]
    fn undersized_tables_keep_capacity_for_reuse() {
        let mut m = Machine::new();
        // 两轮小用量：clear 前后容量都在（阈值以下不 shrink——重建比留着贵）。
        for i in 0..100u32 {
            m.symbol_table.insert((SmolStr::new(format!("s{i}")), 0), SmolStr::new("x"));
            m.trait_metas.push(i);
        }
        let cap0 = m.symbol_table.capacity();
        assert!(cap0 > 0);
        let tcap0 = m.trait_metas.capacity();
        m.clear_round();
        assert_eq!(m.symbol_table.capacity(), cap0, "小表容量被错误归还");
        assert_eq!(m.trait_metas.capacity(), tcap0, "小表缓冲被错误归还");
        // 第二轮照常复用并重新登记（语义面：clear_round 后表功能不变）。
        for i in 0..100u32 {
            m.symbol_table.insert((SmolStr::new(format!("s{i}")), 0), SmolStr::new("y"));
            m.trait_metas.push(i);
        }
        assert_eq!(m.symbol_table.len(), 100);
        assert_eq!(m.trait_metas.len(), 100);
    }
}
