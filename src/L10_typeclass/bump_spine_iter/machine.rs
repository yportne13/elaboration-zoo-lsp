//! machine：稳态复用机（`Machine`）与 elaboration（check/infer/decl 层）、
//! Elaboration 上下文（`Cxt`/`subst_cxt`/`chain_env`）、Debug 复刻（错误消息
//! 内嵌 `{:?}` 输出；L10 特有分节，唯一消费者是本子模块的错误构造，故并入）、
//! builtin 注册（`prime_round`/`elab_all`）、`GLOBAL_BASE` 哨兵与临时探针
//! solve_probe。原 bump_spine_iter.rs 的 "Machine（稳态复用）与 elaboration"、
//! "Elaboration 上下文"、"Debug 复刻"、"builtin 注册" 各节（文件头的
//! GLOBAL_BASE 一并归属本模块；trait 求解的三个 Machine 方法移入 typeclass
//! 子模块的独立 `impl Machine` 块），逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::FxHashMap;
use smol_str::SmolStr;
use std::rc::Rc;

use super::parser::syntax::{Decl, Either, Icit, Raw};
use super::pretty::pretty_tm;
use super::{empty_span, Error, PatternDetail};
use crate::L10_typeclass::typeclass::{Assertion, Instance, Typ};
use crate::parser_lib::ToSpan;

use super::compiler::Compiler;
use super::entry::{export, tm_size};
use super::env::{
    env_ext, env_ext_defs, env_len, env_nth, CloCell, DN_FB, DN_TIP, EMPTY_ENV, Env,
    EnvCons, PiCell,
};
use super::eval::{eval_iter, W};
use super::force::{force, force_deep, frcs_env, refuel, val_mentions_lvl};
use super::quote::{quote_iter, QJob, QuoteMemo};
use super::rename::{invert_bump, lams_from_ty, prune_ty_bump, rename_iter, RenBuf};
use super::spine::{is_flex, MetaEntry, Spine};
use super::subst::{vsub_reclaim, SpecSolve, SubstV, wrap_sub};
use super::syntax::{
    LCons, PrCons, SumDataT, SumParamT, SumParamV, Tm, V, XCell, v_clo, v_clo_of, v_lit_ty,
    v_lvl, v_lvl_of, v_meta, v_meta_of, v_pi, v_pi_of, v_spine_of, v_tag, v_u, v_u_of,
    v_xcell_of,
};
use super::typeclass::{TraitState, val_to_typ};
use super::unify::{
    unify_iter, CACHE_SHRINK_MIN_ENTRIES, ConvScratch, ReclaimOnClear, SPINE_SHRINK_MIN_ENTRIES,
    UItem,
};

/// 全局下标哨兵：`Ix >= GLOBAL_BASE` 的 Var/Rigid 引用 global 表。
pub(super) const GLOBAL_BASE: u32 = 1919810;

// Machine（稳态复用）与 elaboration
// --------------------------------------------------------------------------------

// ==== 临时探针（L10SOLVE_PROBE=1 启用，perf-debt「剩余机会清单」1 的定位；
// 定位完成后整体删除）====
pub(super) mod solve_probe {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    use std::sync::LazyLock;

    pub static ON: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("L10SOLVE_PROBE").is_some());
    static PRINTED: AtomicBool = AtomicBool::new(false);

    /// 全部计数用 fetch_add/fetch_max 累积，elab_all 末尾统一 dump。
    pub struct Cnt {
        pub smt_calls: AtomicU64,
        pub smt_scan: AtomicU64,
        pub smt_scan_max: AtomicU64,
        pub smt_prepare: AtomicU64,
        pub smt_ns: AtomicU64,
        pub str_calls: AtomicU64,
        pub str_trait: AtomicU64,
        pub str_ok: AtomicU64,
        pub str_fail: AtomicU64,
        pub str_ns: AtomicU64,
        pub str_synth_ns: AtomicU64,
        pub str_infer_ns: AtomicU64,
        pub str_unify_ns: AtomicU64,
        pub fm_calls: AtomicU64,
        pub fm_trait_unsolved: AtomicU64,
        pub fm_close_calls: AtomicU64,
        pub fm_k_sum: AtomicU64,
        pub fm_k_max: AtomicU64,
    pub fm_kept_sum: AtomicU64,
    pub fm_kept_max: AtomicU64,
        pub metas_max: AtomicU64,
        pub tw_calls: AtomicU64,
        pub tw_cand: AtomicU64,
        pub tw_infer: AtomicU64,
        pub tw_ns: AtomicU64,
        pub tw_defs_ns: AtomicU64,
        pub tw_build_ns: AtomicU64,
        pub tw_infer_ns: AtomicU64,
        pub un_calls: AtomicU64,
        pub un_ns: AtomicU64,
        pub un_iter_ns: AtomicU64,
        pub un_pair_force_ns: AtomicU64,
        pub un_kod_ns: AtomicU64,
        pub un_pro_ns: AtomicU64,
        pub un_store_ns: AtomicU64,
        pub un_pre_ns: AtomicU64,
        pub un_disp_ns: AtomicU64,
        pub un_item_max_ns: AtomicU64,
        pub un_item_sum_ns: AtomicU64,
        pub un_arm_obj_ns: AtomicU64,
        pub un_arm_chain_ns: AtomicU64,
        pub un_arm_flex_ns: AtomicU64,
        pub un_arm_sum_ns: AtomicU64,
        pub un_flexof_ns: AtomicU64,
        pub un_bare_solve_ns: AtomicU64,
        pub un_bare_solve_cnt: AtomicU64,
        pub sb_rename_ns: AtomicU64,
        pub sb_lams_ns: AtomicU64,
        pub sb_eval_ns: AtomicU64,
        pub sb_l_sum: AtomicU64,
        pub sb_l_max: AtomicU64,
        pub sb_lams_pre_ns: AtomicU64,
        pub sb_lams_loop_ns: AtomicU64,
        pub sb_lams_eval_ns: AtomicU64,
        pub sb_lams_force_ns: AtomicU64,
        pub sb_lams_cu_cnt: AtomicU64,
        pub sb_lams_prune_cnt: AtomicU64,
        pub sb_body_nodes_sum: AtomicU64,
        pub sb_body_nodes_max: AtomicU64,
        pub sb_env_len_sum: AtomicU64,
        pub sb_env_len_max: AtomicU64,
        pub sb_q_nodes_sum: AtomicU64,
        pub sb_q_nodes_max: AtomicU64,
        pub un_tag_pairs: [AtomicU64; 64],
        pub q_calls: AtomicU64,
        pub q_ns: AtomicU64,
        pub e_calls: AtomicU64,
        pub e_ns: AtomicU64,
        pub ins_calls: AtomicU64,
        pub ins_ns: AtomicU64,
        pub fv_ns: AtomicU64,
        pub cu_calls: AtomicU64,
        pub cu_ns: AtomicU64,
        pub ie_calls: AtomicU64,
        pub ie_ns: AtomicU64,
        pub un_items: AtomicU64,
        pub un_solve_bump: AtomicU64,
        pub un_eval: AtomicU64,
        // 自耗时（重入门控：嵌套递归不计入外层）
        pub ie_self_ns: AtomicU64,
        pub un_self_ns: AtomicU64,
        pub ins_self_ns: AtomicU64,
        pub cu_self_ns: AtomicU64,
        pub str_self_ns: AtomicU64,
        pub tw_self_ns: AtomicU64,
        // infer_expr 臂直方图
        pub ie_var: AtomicU64,
        pub ie_obj: AtomicU64,
        pub ie_app: AtomicU64,
        pub ie_pi: AtomicU64,
        pub ie_lam: AtomicU64,
        pub ie_let: AtomicU64,
        pub ie_other: AtomicU64,
        // trait_wrap 分桶：前 64 次 vs 之后（钉单次耗时是否随 def 序号增长）
        pub tw_early_ns: AtomicU64,
        pub tw_late_ns: AtomicU64,
        pub tw_early_max_ns: AtomicU64,
        pub tw_late_max_ns: AtomicU64,
        pub defs: AtomicU64,
        pub def_scan_unsolved: AtomicU64,
        pub def_scan_trait_unsolved: AtomicU64,
    }

    /// 自耗时门控：未重入返回 Some(起点)，已重入返回 None。
    #[inline]
    pub fn self_t0(busy: &AtomicBool) -> Option<std::time::Instant> {
        if busy.swap(true, Ordering::Relaxed) {
            None
        } else {
            Some(std::time::Instant::now())
        }
    }

    #[inline]
    pub fn self_end(busy: &AtomicBool, acc: &AtomicU64, t0: Option<std::time::Instant>) {
        if let Some(t0) = t0 {
            busy.store(false, Ordering::Relaxed);
            acc.fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// 相位出口：重入未开的 None 不动 busy；Some(t0) 记 cum + 自耗时并开门。
    #[inline]
    pub fn phase_end(
        busy: &AtomicBool,
        cum: &AtomicU64,
        self_acc: &AtomicU64,
        t0: Option<std::time::Instant>,
    ) {
        if let Some(t0) = t0 {
            busy.store(false, Ordering::Relaxed);
            let d = t0.elapsed().as_nanos() as u64;
            cum.fetch_add(d, Ordering::Relaxed);
            self_acc.fetch_add(d, Ordering::Relaxed);
        }
    }

    /// trait_wrap 专用出口：同 phase_end，另按调用序号分桶（前 64 次 vs 之后）。
    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub fn tw_phase_end(
        busy: &AtomicBool,
        cum: &AtomicU64,
        self_acc: &AtomicU64,
        t0: Option<std::time::Instant>,
        idx: u64,
        early: &AtomicU64,
        early_max: &AtomicU64,
        late: &AtomicU64,
        late_max: &AtomicU64,
    ) {
        if let Some(t0) = t0 {
            busy.store(false, Ordering::Relaxed);
            let d = t0.elapsed().as_nanos() as u64;
            cum.fetch_add(d, Ordering::Relaxed);
            self_acc.fetch_add(d, Ordering::Relaxed);
            if idx < 64 {
                early.fetch_add(d, Ordering::Relaxed);
                early_max.fetch_max(d, Ordering::Relaxed);
            } else {
                late.fetch_add(d, Ordering::Relaxed);
                late_max.fetch_max(d, Ordering::Relaxed);
            }
        }
    }

    pub static C: Cnt = Cnt {
        smt_calls: AtomicU64::new(0),
        smt_scan: AtomicU64::new(0),
        smt_scan_max: AtomicU64::new(0),
        smt_prepare: AtomicU64::new(0),
        smt_ns: AtomicU64::new(0),
        str_calls: AtomicU64::new(0),
        str_trait: AtomicU64::new(0),
        str_ok: AtomicU64::new(0),
        str_fail: AtomicU64::new(0),
        str_ns: AtomicU64::new(0),
        str_synth_ns: AtomicU64::new(0),
        str_infer_ns: AtomicU64::new(0),
        str_unify_ns: AtomicU64::new(0),
        fm_calls: AtomicU64::new(0),
        fm_trait_unsolved: AtomicU64::new(0),
        fm_close_calls: AtomicU64::new(0),
        fm_k_sum: AtomicU64::new(0),
        fm_k_max: AtomicU64::new(0),
    fm_kept_sum: AtomicU64::new(0),
    fm_kept_max: AtomicU64::new(0),
        metas_max: AtomicU64::new(0),
        tw_calls: AtomicU64::new(0),
        tw_cand: AtomicU64::new(0),
        tw_infer: AtomicU64::new(0),
        tw_ns: AtomicU64::new(0),
        tw_defs_ns: AtomicU64::new(0),
        tw_build_ns: AtomicU64::new(0),
        tw_infer_ns: AtomicU64::new(0),
        un_calls: AtomicU64::new(0),
        un_ns: AtomicU64::new(0),
        un_iter_ns: AtomicU64::new(0),
        un_pair_force_ns: AtomicU64::new(0),
        un_kod_ns: AtomicU64::new(0),
        un_pro_ns: AtomicU64::new(0),
        un_store_ns: AtomicU64::new(0),
        un_pre_ns: AtomicU64::new(0),
        un_disp_ns: AtomicU64::new(0),
        un_item_max_ns: AtomicU64::new(0),
        un_item_sum_ns: AtomicU64::new(0),
        un_arm_obj_ns: AtomicU64::new(0),
        un_arm_chain_ns: AtomicU64::new(0),
        un_arm_flex_ns: AtomicU64::new(0),
        un_arm_sum_ns: AtomicU64::new(0),
        un_flexof_ns: AtomicU64::new(0),
        un_bare_solve_ns: AtomicU64::new(0),
        un_bare_solve_cnt: AtomicU64::new(0),
        sb_rename_ns: AtomicU64::new(0),
        sb_lams_ns: AtomicU64::new(0),
        sb_eval_ns: AtomicU64::new(0),
        sb_l_sum: AtomicU64::new(0),
        sb_l_max: AtomicU64::new(0),
        sb_lams_pre_ns: AtomicU64::new(0),
        sb_lams_loop_ns: AtomicU64::new(0),
        sb_lams_eval_ns: AtomicU64::new(0),
        sb_lams_force_ns: AtomicU64::new(0),
        sb_lams_cu_cnt: AtomicU64::new(0),
        sb_lams_prune_cnt: AtomicU64::new(0),
        sb_body_nodes_sum: AtomicU64::new(0),
        sb_body_nodes_max: AtomicU64::new(0),
        sb_env_len_sum: AtomicU64::new(0),
        sb_env_len_max: AtomicU64::new(0),
        sb_q_nodes_sum: AtomicU64::new(0),
        sb_q_nodes_max: AtomicU64::new(0),
        un_tag_pairs: [const { AtomicU64::new(0) }; 64],
        q_calls: AtomicU64::new(0),
        q_ns: AtomicU64::new(0),
        e_calls: AtomicU64::new(0),
        e_ns: AtomicU64::new(0),
        ins_calls: AtomicU64::new(0),
        ins_ns: AtomicU64::new(0),
        fv_ns: AtomicU64::new(0),
        cu_calls: AtomicU64::new(0),
        cu_ns: AtomicU64::new(0),
        ie_calls: AtomicU64::new(0),
        ie_ns: AtomicU64::new(0),
        un_items: AtomicU64::new(0),
        un_solve_bump: AtomicU64::new(0),
        un_eval: AtomicU64::new(0),
        ie_self_ns: AtomicU64::new(0),
        un_self_ns: AtomicU64::new(0),
        ins_self_ns: AtomicU64::new(0),
        cu_self_ns: AtomicU64::new(0),
        str_self_ns: AtomicU64::new(0),
        tw_self_ns: AtomicU64::new(0),
        ie_var: AtomicU64::new(0),
        ie_obj: AtomicU64::new(0),
        ie_app: AtomicU64::new(0),
        ie_pi: AtomicU64::new(0),
        ie_lam: AtomicU64::new(0),
        ie_let: AtomicU64::new(0),
        ie_other: AtomicU64::new(0),
        tw_early_ns: AtomicU64::new(0),
        tw_late_ns: AtomicU64::new(0),
        tw_early_max_ns: AtomicU64::new(0),
        tw_late_max_ns: AtomicU64::new(0),
        defs: AtomicU64::new(0),
        def_scan_unsolved: AtomicU64::new(0),
        def_scan_trait_unsolved: AtomicU64::new(0),
    };

    // 自耗时的重入门控标志（单线程机，Relaxed 即可）
    pub static B_IE: AtomicBool = AtomicBool::new(false);
    pub static B_UN: AtomicBool = AtomicBool::new(false);
    pub static B_INS: AtomicBool = AtomicBool::new(false);
    pub static B_CU: AtomicBool = AtomicBool::new(false);
    pub static B_STR: AtomicBool = AtomicBool::new(false);
    pub static B_TW: AtomicBool = AtomicBool::new(false);

    /// 作用域累计计时守卫：构造取 now，Drop 时累计进槽——`continue` /
    /// `return` 路径全覆盖。探针关时 t0=None 零成本。需提前结束用
    /// `drop(g)` 显式落账。
    pub struct TGuard<'a> {
        t0: Option<std::time::Instant>,
        slot: &'a AtomicU64,
    }
    impl<'a> TGuard<'a> {
        #[inline]
        pub fn on(slot: &'a AtomicU64) -> Self {
            Self {
                t0: if *ON { Some(std::time::Instant::now()) } else { None },
                slot,
            }
        }
    }
    impl Drop for TGuard<'_> {
        #[inline]
        fn drop(&mut self) {
            if let Some(t0) = self.t0.take() {
                self.slot.fetch_add(t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
            }
        }
    }

    /// 单 item 计时守卫：sum 累计 + max 单点（判「均匀慢」vs「个别病态」）。
    pub struct ItemGuard<'a> {
        t0: Option<std::time::Instant>,
        sum: &'a AtomicU64,
        mx: &'a AtomicU64,
    }
    impl<'a> ItemGuard<'a> {
        #[inline]
        pub fn on(sum: &'a AtomicU64, mx: &'a AtomicU64) -> Self {
            Self {
                t0: if *ON { Some(std::time::Instant::now()) } else { None },
                sum,
                mx,
            }
        }
    }
    impl Drop for ItemGuard<'_> {
        #[inline]
        fn drop(&mut self) {
            if let Some(t0) = self.t0.take() {
                let d = t0.elapsed().as_nanos() as u64;
                self.sum.fetch_add(d, Ordering::Relaxed);
                self.mx.fetch_max(d, Ordering::Relaxed);
            }
        }
    }

    #[inline]
    pub fn on() -> bool {
        *ON
    }

    /// elab_all 末尾统一打印（每进程一次，防 parity 多用例刷屏）。
    pub fn dump() {
        if !*ON || PRINTED.swap(true, Ordering::Relaxed) {
            return;
        }
        let g = |x: &AtomicU64| x.load(Ordering::Relaxed);
        eprintln!(
            "[L10SOLVE_PROBE] CLOSE: calls={} k_sum={} k_avg={} k_max={} | kept_sum={} kept_avg={} kept_max={} (kept = 化简后实际包装层数) | flat_env_paths_ok",
            g(&C.fm_close_calls),
            g(&C.fm_k_sum),
            if g(&C.fm_close_calls) > 0 { g(&C.fm_k_sum) / g(&C.fm_close_calls) } else { 0 },
            g(&C.fm_k_max),
            g(&C.fm_kept_sum),
            if g(&C.fm_close_calls) > 0 { g(&C.fm_kept_sum) / g(&C.fm_close_calls) } else { 0 },
            g(&C.fm_kept_max),
        );
        eprintln!(
            "[L10SOLVE_PROBE] env_ext_defs: tip={} fallback={}",
            g(&super::DN_TIP),
            g(&super::DN_FB),
        );
        eprintln!(
            "[L10SOLVE_PROBE] solve_trait分段: synth={:.1}ms infer+insert={:.1}ms unify={:.1}ms (trait调用总数={})",
            g(&C.str_synth_ns) as f64 / 1e6,
            g(&C.str_infer_ns) as f64 / 1e6,
            g(&C.str_unify_ns) as f64 / 1e6,
            g(&C.str_trait),
        );
        eprintln!(
            "[L10SOLVE_PROBE] unify内部分解(ms): pro={:.1} store={:.1} pre={:.1} force={:.1} kod={:.1} disp={:.1} | 臂: obj={:.1} chain22={:.1} flex={:.1} sum77={:.1} | iter={:.1} | item: sum={:.1} max={:.3}",
            g(&C.un_pro_ns) as f64 / 1e6,
            g(&C.un_store_ns) as f64 / 1e6,
            g(&C.un_pre_ns) as f64 / 1e6,
            g(&C.un_pair_force_ns) as f64 / 1e6,
            g(&C.un_kod_ns) as f64 / 1e6,
            g(&C.un_disp_ns) as f64 / 1e6,
            g(&C.un_arm_obj_ns) as f64 / 1e6,
            g(&C.un_arm_chain_ns) as f64 / 1e6,
            g(&C.un_arm_flex_ns) as f64 / 1e6,
            g(&C.un_arm_sum_ns) as f64 / 1e6,
            g(&C.un_iter_ns) as f64 / 1e6,
            g(&C.un_item_sum_ns) as f64 / 1e6,
            g(&C.un_item_max_ns) as f64 / 1e6,
        );
        eprintln!(
            "[L10SOLVE_PROBE] flex块分解(ms): flex_of={:.1} | bare solve_bump: cnt={} time={:.1}ms | solve内: rename={:.1} lams={:.1} eval={:.1} | lams: pre-force={:.1} loop={:.1} (loop内 eval={:.1} force={:.1}) | l: sum={} max={} | 调用点: cu={} prune={} | Π体: nodes_sum={} nodes_max={} | env_len: sum={} max={} | quote: sum={} max={}",
            g(&C.un_flexof_ns) as f64 / 1e6,
            g(&C.un_bare_solve_cnt),
            g(&C.un_bare_solve_ns) as f64 / 1e6,
            g(&C.sb_rename_ns) as f64 / 1e6,
            g(&C.sb_lams_ns) as f64 / 1e6,
            g(&C.sb_eval_ns) as f64 / 1e6,
            g(&C.sb_lams_pre_ns) as f64 / 1e6,
            g(&C.sb_lams_loop_ns) as f64 / 1e6,
            g(&C.sb_lams_eval_ns) as f64 / 1e6,
            g(&C.sb_lams_force_ns) as f64 / 1e6,
            g(&C.sb_l_sum),
            g(&C.sb_l_max),
            g(&C.sb_lams_cu_cnt),
            g(&C.sb_lams_prune_cnt),
            g(&C.sb_body_nodes_sum),
            g(&C.sb_body_nodes_max),
            g(&C.sb_env_len_sum),
            g(&C.sb_env_len_max),
            g(&C.sb_q_nodes_sum),
            g(&C.sb_q_nodes_max),
        );
        let mut tags = String::new();
        for (i, c) in C.un_tag_pairs.iter().enumerate() {
            let n = c.load(Ordering::Relaxed);
            if n > 0 {
                tags.push_str(&format!(" t{}u{}={}", i >> 3, i & 7, n));
            }
        }
        eprintln!("[L10SOLVE_PROBE] item-tag-pairs:{}", tags);
        eprintln!(
            "[L10SOLVE_PROBE] defs={} metas_max={} | solve_multi: calls={} scan_sum={} scan_max={} prepare_sum={} time={:.1}ms (scan口径v2=unsolved worklist长度，原metas后缀扫) | solve_trait: calls={} trait={} synth_ok={} synth_fail={} time={:.1}ms | fresh_meta: calls={} trait_unsolved_push={} | trait_wrap: calls={} cand={} infer={} time={:.1}ms (defs收集={:.1}ms raw构建={:.1}ms wrapper_infer={:.1}ms) | def臂扫描: Σunsolved={} Σtrait_unsolved={} | 相位cum: unify={}(cum {:.1}ms) quote={}(cum {:.1}ms) eval={}(cum {:.1}ms) insert_go={}(cum {:.1}ms) force_v cum={:.1}ms check_univ={}(cum {:.1}ms) infer_expr={}(cum {:.1}ms) | unify内部: items={} solve_bump={} eval/η={}",
            g(&C.defs),
            g(&C.metas_max),
            g(&C.smt_calls),
            g(&C.smt_scan),
            g(&C.smt_scan_max),
            g(&C.smt_prepare),
            g(&C.smt_ns) as f64 / 1e6,
            g(&C.str_calls),
            g(&C.str_trait),
            g(&C.str_ok),
            g(&C.str_fail),
            g(&C.str_ns) as f64 / 1e6,
            g(&C.fm_calls),
            g(&C.fm_trait_unsolved),
            g(&C.tw_calls),
            g(&C.tw_cand),
            g(&C.tw_infer),
            g(&C.tw_ns) as f64 / 1e6,
            g(&C.tw_defs_ns) as f64 / 1e6,
            g(&C.tw_build_ns) as f64 / 1e6,
            g(&C.tw_infer_ns) as f64 / 1e6,
            g(&C.def_scan_unsolved),
            g(&C.def_scan_trait_unsolved),
            g(&C.un_calls),
            g(&C.un_ns) as f64 / 1e6,
            g(&C.q_calls),
            g(&C.q_ns) as f64 / 1e6,
            g(&C.e_calls),
            g(&C.e_ns) as f64 / 1e6,
            g(&C.ins_calls),
            g(&C.ins_ns) as f64 / 1e6,
            g(&C.fv_ns) as f64 / 1e6,
            g(&C.cu_calls),
            g(&C.cu_ns) as f64 / 1e6,
            g(&C.ie_calls),
            g(&C.ie_ns) as f64 / 1e6,
            g(&C.un_items),
            g(&C.un_solve_bump),
            g(&C.un_eval),
        );
        eprintln!(
            "[L10SOLVE_PROBE] 自耗时: infer_expr={:.1}ms unify={:.1}ms insert_go={:.1}ms check_univ={:.1}ms solve_trait={:.1}ms trait_wrap={:.1}ms | infer_expr臂: Var={} Obj={} App={} Pi={} Lam={} Let={} 其他={} | tw分桶: 前64次Σ={:.1}ms max={:.1}ms / 之后Σ={:.1}ms max={:.1}ms",
            g(&C.ie_self_ns) as f64 / 1e6,
            g(&C.un_self_ns) as f64 / 1e6,
            g(&C.ins_self_ns) as f64 / 1e6,
            g(&C.cu_self_ns) as f64 / 1e6,
            g(&C.str_self_ns) as f64 / 1e6,
            g(&C.tw_self_ns) as f64 / 1e6,
            g(&C.ie_var),
            g(&C.ie_obj),
            g(&C.ie_app),
            g(&C.ie_pi),
            g(&C.ie_lam),
            g(&C.ie_let),
            g(&C.ie_other),
            g(&C.tw_early_ns) as f64 / 1e6,
            g(&C.tw_early_max_ns) as f64 / 1e6,
            g(&C.tw_late_ns) as f64 / 1e6,
            g(&C.tw_late_max_ns) as f64 / 1e6,
        );
    }
}
// ==== 临时探针结束 ====

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
    /// 未解 meta worklist（A-2，评审第二轮）：当前仍为
    /// [`MetaEntry::Unsolved`] 的 meta 下标集合，**无序**（含 swap_remove
    /// 摘除）。入表点 = 3 处 `metas.push(Unsolved)`（fresh_meta 两路 +
    /// prune_meta_bump 新 meta），出表点 = 5 处 `Solved` 写（solve_with_pren /
    /// prune_meta / solve_multi / check_universe ×2）——与 metas 表严格同步，
    /// [`Machine::run_pure_probe`] 的快照回滚两表同换。用途：
    /// `solve_multi_trait_ref` 旧实现每次对 metas 表做全后缀线性扫
    /// （traitchain 一轮 3076 次调用、Σscan 2.1M、仅产出个位候选），现只遍历
    /// 本表（活跃未解数，个位量级）。每轮 clear_round 清空。
    pub(super) unsolved: Vec<u32>,
    /// solve 的偏置换换代缓冲（跨求解持久，epoch 换代免逐槽清零）。
    ren: RenBuf,
    /// 全局 def/enum 值表（下标 = global_idx）。递归 def 的占位（自身大
    /// 层级的 Rigid）先压入、检查后覆盖。每轮清空（参考版每次调用新建
    /// Infer 的 global 表）。
    pub(super) globals: Vec<V>,
    /// 全局名字表（顶层 define 的 名字 → (层级, 类型)）：Machine 独有的
    /// append-only 表，**不随 Cxt 克隆**（与 L11+ 的 decls 表同角色；
    /// perf-debt P2：旧设计顶层 define 累积进 Cxt 的 names 快照，
    /// bind_name 每 binder 克隆整表 O(D²)）。查找顺序：Cxt 局部 names
    /// 优先（当前 def 的 binder + fake 占位），之后回落本表。每轮清空。
    global_names: FxHashMap<SmolStr, (u32, V)>,
    /// globals 的中性视图缓存：neutral[i] == v_lvl(i + GLOBAL_BASE)，
    /// 随 globals 同步 push。quote/eval/unify 包装器的旧实现每次
    /// neutral_of(&self.globals) 整拷 O(D)，现按字段借用 O(1)。每轮清空。
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
    /// trait 合成状态（每轮清空——参考版每次调用新建 Infer 的三表）。
    pub(super) tstate: TraitState,
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
            unsolved: Vec::new(),
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
            tstate: TraitState::default(),
        }
    }

    /// 每轮 reset：metacontext + 名字表/类型表/轨迹 + 环境区域 + global 表
    /// 全部清空。spine 栈同轮清空（保容量）——tag-2 句柄只被当轮 bump 值 /
    /// metas / defs / globals 持有，轮边界后无任何旧句柄可达；容量到过
    /// `SPINE_SHRINK_MIN_ENTRIES` 时清空顺带归还缓冲（否则峰值容量随常驻
    /// Machine 到进程结束）。
    pub(super) fn clear_round(&mut self) {
        self.metas.clear();
        self.unsolved.clear();
        self.defs.clear();
        self.globals.clear();
        self.global_names.clear();
        self.neutral.clear();
        let _ = self.spine.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        self.tstate = TraitState::default();
        // 与 bump.reset() 严格伴生：归还 arena 内 σ 克隆的强引用（Rc 节点
        // 在全局堆上，reset 不动其数据；见 VSUB_REGS 的 SAFETY 注释；
        // 2026-09-18 评审修复 σ 跨轮回收移植）
        vsub_reclaim();
    }

    /// 未解 meta worklist 摘除（A-2）：任一 meta 写成 `Solved` 时调用。
    /// 无序表 → swap_remove O(1)；按值定位 O(n)，n = 活跃未解数（个位量级）。
    /// 双重摘除无害（side-effect 求解后 prepare 快照重放同一写点时容错）。
    pub(super) fn remove_unsolved(&mut self, m: u32) {
        if let Some(p) = self.unsolved.iter().position(|&x| x == m) {
            self.unsolved.swap_remove(p);
        }
    }

    /// 构造子返回类型良构性（参考版 `Infer::check_ctor_wf` 同款，L07 孪生
    /// 镜像，2026-09-18 评审修复）：实例化构造子类型的全部绑定器后，ret 的
    /// WHNF 必须是 `enum_name` 的 `Sum`，且其隐式参数位逐一等于 telescope
    /// 内的 bare rigid。允许构造子重绑定参数（`p[A,B](a,b) -> Pack[A][B]
    /// a b`），拒绝参数位非变量（`c -> Foo[Bool]`）与非本 enum 的 ret
    /// （`c -> Nat`）——后者向构造子名字空间注入永不匹配任何模式的
    /// phantom 值，对覆盖检查完备的 match 在封闭输入上卡死。
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
            return Err(Error(empty_span(format!(
                "构造子 {ctor_name} 的返回类型不是和类型"
            ))));
        }
        match v_xcell_of(retf) {
            XCell::Sum { name: sname, params, .. } => {
                if *sname != enum_name {
                    return Err(Error(empty_span(format!(
                        "构造子 {ctor_name} 的返回类型是 {sname}，不是 {enum_name}"
                    ))));
                }
                for p in params.iter() {
                    if p.icit == Icit::Impl {
                        let v = p.val;
                        let bare_rigid = v_tag(v) == 0
                            && v_lvl_of(v) >= base
                            && v_lvl_of(v) < base + bound;
                        if !bare_rigid {
                            return Err(Error(empty_span(format!(
                                "构造子 {ctor_name} 的返回类型参数必须是 {enum_name} 的参数变量（参数不得特化，特化请用显式索引）"
                            ))));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
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
                val: None,
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
                val: None,
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
                val: Some(val),
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
    /// ——大 decl 数负载上每 def O(D) 克隆实测 O(D²)；有别的快照观察者
    /// （match 臂捕获、refresh 克隆等）时自动回退深拷贝，隔离语义与旧
    /// 实现逐字一致。调用方需在使用完返回的 fake 视图后 `drop(fake)` 再
    /// 就地 define（否则多出的 Rc 引用会触发 make_mut 克隆回退）。
    fn fake_bind<'a>(&mut self, cxt: &mut Cxt<'a>, x: &str, ty: V, global_idx: u32) -> Cxt<'a> {
        let names = Rc::make_mut(&mut cxt.names);
        names.by_name.insert(SmolStr::new(x), global_idx + GLOBAL_BASE);
        names.by_lvl.insert(global_idx + GLOBAL_BASE, ty);
        clone_cxt(cxt)
    }

    /// [`Self::define_name`] 的就地版（调用方独占 cxt 的 decl 臂 /
    /// prime_round 顺序路径专用）：`Rc::make_mut` 独占时原地扩展 O(1)，
    /// 语义与克隆版逐字一致（COW 论证见 [`Self::fake_bind`]）。check
    /// 路径的 Let（父视图存活）继续走克隆版 [`Self::define_name`]。
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
        // 真名进 Machine 全局表（append-only，不随 Cxt 克隆——perf-debt
        // P2），并撤除 fake_bind 留在局部 names 里的同名占位（by_name 旧
        // 键即其 by_lvl 键；prime_round 的 builtin 注册无占位，remove
        // 为 no-op）。
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
            val: Some(val),
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
    /// 槽由 `cxt.env` 快照供给）在 L09 起刻意不移植**：那条路径要求
    /// "telescope 里 define 槽的项 ≡ env 快照里的值"。L05-L08 的模式特化走
    /// pm_defs（只追加等式，快照恒成立）；L09 起改走参考版的上下文精化
    /// （旧 `Cxt::update_cxt` 就地改写 env 槽再 refresh 重锚定；本轮起改为
    /// 显式替换 `subst_cxt` 包裹、读点 force 推开），两种机制下 `locals`
    /// 都照参考版保持陈旧（参考版 cxt.rs 里
    /// `locals: self.locals.clone()` 的 TODO），全 close 正是靠这份陈旧项
    /// 与参考版逐值同轨。改读快照会拿到精化后的值：孪生的契约是与参考版
    /// Ok 输出逐字节一致，不是比参考版更正确。
    fn fresh_meta<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>, a: V) -> &'a Tm<'a> {
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        // 期望类型可能被精化 σ 包裹：先推开，实例合成 / trait 判形才看得到
        // 真实形态（对齐旧 refresh 后槽值已展开的世界）
        let a = self.force_v(bump, a);
        solve_probe::on().then(|| {
            solve_probe::C.fm_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        });
        // L10：trait 类型先试实例合成（成功 → 直接给实例项）；
        // trait Sum → 裸 Meta（无 AppPruning 掩码）
        if let Ok(Some((tm, _))) = self.solve_trait_ref(bump, cxt, a) {
            return tm;
        }
        let is_trait_sum = v_tag(a) == 7
            && match v_xcell_of(a) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if is_trait_sum {
            let m = self.metas.len() as u32;
            self.metas.push(MetaEntry::Unsolved(a));
            self.unsolved.push(m); // A-2 worklist 入表
            solve_probe::on().then(|| {
                solve_probe::C.fm_trait_unsolved.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                solve_probe::C.metas_max.fetch_max(self.metas.len() as u64, std::sync::atomic::Ordering::Relaxed);
            });
            return bump.alloc(Tm::Meta(m));
        }
        let mty = if cxt.binds == 0 && matches!(v_tag(a), 3 | 5 | 6) {
            a
        } else {
            let q = self.quote(bump, cxt.lvl, a);
            solve_probe::C.sb_q_nodes_sum.fetch_add(tm_size(q), std::sync::atomic::Ordering::Relaxed);
            solve_probe::C.sb_q_nodes_max.fetch_max(tm_size(q), std::sync::atomic::Ordering::Relaxed);
            if cxt.binds == 0 && !has_free_var(q) {
                self.eval(bump, EMPTY_ENV, q)
            } else {
                // 全局段免包装（perf-debt 实现轮）：只包当前 def 的
                // k = cxt.lvl - flat_len 个局部条目，以平坦区为基底环境求值
                // （论证见 git 历史 c7f6349 前版）。
                //
                // 评审 A-1「登记值链直评」尝试（2026-09-13，已回退）：把
                // define 槽的 Let 重求值换成 LCons.val 登记值直评——k=9 正常
                // （88ms）但 k=10 起 >100s 病态化：`LCons.val` 是登记时刻的
                // 快照，而 def 项里 insert_go/合成的 meta 在登记后才求解，
                // 旧 close 路径每次重求值会内联**最新**解，「登记值 ≡ 重求
                // 值」不变式对含 late-solve meta 的链不成立。复活此方案的前
                // 置：(a) LCons 缓存带 meta-epoch 失效（任一 meta 求解即作
                // 废重评），或 (b) 证明/保证登记后 def 项再无未解 meta。
                let flat_len = cxt.env.flat_len;
                let k = cxt.lvl as usize - flat_len as usize;
                solve_probe::C.fm_close_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                solve_probe::C.fm_k_sum.fetch_add(k as u64, std::sync::atomic::Ordering::Relaxed);
                solve_probe::C.fm_k_max.fetch_max(k as u64, std::sync::atomic::Ordering::Relaxed);
                let global_env = Env {
                    flat_base: cxt.env.flat_base,
                    flat_len,
                    binds: None,
                };
                if k == 0 {
                    self.eval(bump, global_env, q)
                } else {
                    // 值中性化简（2026-09-21，L10 traitchain O(n²) 内存修复）：
                    // 全链 close 里「q 未引用的 define 槽」是纯浪费——`Let(x, A,
                    // t, body)` 包一个 body 不引用的 x，求值结果与不包相同
                    // （`binds == 0 && !has_free_var(q)` 快路径的同族论证：
                    // 参考版的 Let 层在这种位置上从不进入输出）。traitchain
                    // 实测（L10SOLVE_PROBE CLOSE 行）：75% 的 close 调用 q 是
                    // 闭项（`Type 0`），25% 只引用一个 impl 泄漏的深层 Bind——
                    // 全链包装 2.1M 节点里 95%+ 是这种死重，k=11 时 2.1GB。
                    // 化简规则（与参考版逐值同轨）：
                    // - **Bind 槽全留**：Π 层是参考版可观察语义；
                    // - **q 引用的 define 槽留**：q 的 Var 靠它们解析；
                    // - 其余 define 槽丢弃，q 的自由变量下标按保留槽位重编号
                    //   （`remap_free_vars`；未被引用 ⇒ 无下标需要改）。
                    // 走查范围 = 前 k 条（≥flat_len 的非平坦层）；平坦层由
                    // `global_env` 供给，q 引用它们的 Var 保持自由、原样解析
                    // （与舊路径「以平坦区为基底环境求值」一致）。
                    let (closed, kept) = close_tm_reduced(bump, cxt.locals, q, k);
                    solve_probe::C.fm_kept_sum.fetch_add(kept as u64, std::sync::atomic::Ordering::Relaxed);
                    solve_probe::C.fm_kept_max.fetch_max(kept as u64, std::sync::atomic::Ordering::Relaxed);
                    self.eval(bump, global_env, closed)
                }
            }
        };
        let m = self.metas.len() as u32;
        self.metas.push(MetaEntry::Unsolved(mty));
        self.unsolved.push(m); // A-2 worklist 入表
        solve_probe::on().then(|| {
            solve_probe::C.metas_max.fetch_max(self.metas.len() as u64, std::sync::atomic::Ordering::Relaxed);
        });
        bump.alloc(Tm::AppPruning(bump.alloc(Tm::Meta(m)), cxt.pruning))
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
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = solve_probe::on().then(|| {
            solve_probe::C.e_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            std::time::Instant::now()
        });
        let Machine {
            spine,
            vals,
            icits,
            defs,
            metas,
            globals,
            neutral,
            eval_work,
            ..
        } = self;
        // SAFETY：'static 仅是存放口径（字段注释）。W 无 Drop、Vec 布局与
        // 生命周期参数无关；借出期 = 本次调用，槽内容下次借出前必 clear，
        // 任何 'a 条目都不会被以 'static 读到。
        let work: &mut Vec<W<'a>> =
            unsafe { &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>) };
        work.clear();
        let r = eval_iter(
            bump, spine, work, vals, icits, defs, metas, globals, env, tm,
        );
        if let Some(t0) = probe_t0 {
            solve_probe::C.e_ns.fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        r
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
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = solve_probe::on().then(|| {
            solve_probe::C.q_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            std::time::Instant::now()
        });
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
        let r = quote_iter(
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
            None,
        );
        if let Some(t0) = probe_t0 {
            solve_probe::C.q_ns.fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        r
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
    pub(super) fn unify<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        l: u32,
        t: V,
        u: V,
        trait_err: &mut Option<String>,
    ) -> bool {
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = if solve_probe::on() {
            solve_probe::C.un_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            solve_probe::self_t0(&solve_probe::B_UN)
        } else {
            None
        };
        // trait 合成与字段借用的分离（SB 别名安全）：unify_iter 遇到「flex
        // 解开后需跑 trait 合成」的点不再经裸指针重建整机 &mut（旧实现
        // 在字段借用存活时 `(&mut *mach_ptr).solve_multi_trait_ref(..)`，
        // Stacked Borrows 下字段借用被弹出，回调返回后继续使用属
        // use-after-invalidate），而是写入 solve_req 挂起返回；本驱动在
        // 字段借用已结束（NLL：上次使用 = unify_iter 调用）的点上以独占
        // &mut self 执行合成，随后每轮循环**重新解构**字段——不存在与
        // 字段借用并存的整机重借，整段除既有 'static 槽位生命周期改写
        // 外无 unsafe。
        let mut resume = false;
        let mut solve_req: Option<u32> = None;
        loop {
            let Machine {
                spine,
                vals,
                icits,
                defs,
                metas,
                unsolved,
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
            if !resume {
                work.clear();
                stack.clear();
            }
            let probe_tit = solve_probe::on().then(std::time::Instant::now);
            let iter_r = unify_iter(
                bump, spine, work, stack, vals, icits, defs, metas, unsolved, globals, neutral,
                ren, conv, l, t, u, resume, &mut solve_req,
            );
            if let Some(ti) = probe_tit {
                solve_probe::C
                    .un_iter_ns
                    .fetch_add(ti.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            }
            if iter_r {
                solve_probe::phase_end(&solve_probe::B_UN, &solve_probe::C.un_ns, &solve_probe::C.un_self_ns, probe_t0);
                return true;
            }
            // None = 真实失败；Some(m) = trait 合成挂起（solve 后续跑）
            let Some(m) = solve_req.take() else {
                solve_probe::phase_end(&solve_probe::B_UN, &solve_probe::C.un_ns, &solve_probe::C.un_self_ns, probe_t0);
                return false;
            };
            if let Err(e) = self.solve_multi_trait_ref(bump, cxt, m) {
                *trait_err = Some(e);
                solve_probe::phase_end(&solve_probe::B_UN, &solve_probe::C.un_ns, &solve_probe::C.un_self_ns, probe_t0);
                return false;
            }
            resume = true;
        }
    }

    /// 错误消息（参考版 `unify_catch`：pretty + 上下文名字表；快版导出项
    /// 的 Span 全零，消息内容与参考版同构）。
    fn unify_catch<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
    ) -> Result<(), Error> {
        self.unify_catch_at(bump, cxt.lvl, cxt, t, t_prime)
    }

    /// `unify_catch` 的显式层级版（参考版同款，2026-09-18 评审修复）：可达
    /// 性探测的构造子绑定器以**超出上下文的 scratch 层级**实例化（嵌套位置
    /// 的延迟探测还落在臂内全部真槽之外）——η/Π 展开的 binder 层级必须随
    /// 之抬高，否则会与真槽撞号。
    fn unify_catch_at<'a>(
        &mut self,
        bump: &'a Bump,
        l: u32,
        cxt: &Cxt<'a>,
        t: V,
        t_prime: V,
    ) -> Result<(), Error> {
        let mut trait_err: Option<String> = None;
        // 一次合一入口充值精化燃料池
        refuel();
        let ok = self.unify(bump, cxt, l, t, t_prime, &mut trait_err);
        if ok {
            Ok(())
} else {
            if let Some(e) = trait_err {
                return Err(Error(empty_span(e)));
            }
            let tq = export(self.quote(bump, l, t));
            let uq = export(self.quote(bump, l, t_prime));
            let names = types_names_list(cxt.types);
            // 标签方向对齐参考版 `unify_catch`（`mod.rs:525`）：`t` = expected、
            // `t_prime` = find。旧快版写成 find-first，而调用点全部与参考版
            // 同序传入（expected 在前），导致同一错误的 expected/find 两版
            // 相反——parity Err 正文裂缝（本轮探针暴露）。
            Err(Error(empty_span(format!(
                "can't unify\n  expected: {}\n      find: {}",
                pretty_tm(0, names.clone(), &tq),
                pretty_tm(0, names, &uq),
            ))))
        }
    }

    /// force 的方法包装（Machine 内 elaboration 侧的散装调用点用；解值
    /// 应用可能 β——分配一律落本轮 bump）。
    pub(super) fn force_v(&mut self, bump: &Bump, v: V) -> V {
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = solve_probe::on().then(std::time::Instant::now);
        let Machine {
            spine,
            defs,
            metas,
            globals,
            neutral,
            ..
        } = self;
        let r = force(bump, spine, defs, metas, globals, v);
        if let Some(t0) = probe_t0 {
            solve_probe::C.fv_ns.fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        r
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
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = if solve_probe::on() {
            solve_probe::C.ins_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            solve_probe::self_t0(&solve_probe::B_INS)
        } else {
            None
        };
        let r = self.insert_go_inner(bump, cxt, t, va);
        solve_probe::phase_end(&solve_probe::B_INS, &solve_probe::C.ins_ns, &solve_probe::C.ins_self_ns, probe_t0);
        r
    }

    fn insert_go_inner<'a>(
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
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
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
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = if solve_probe::on() {
            solve_probe::C.cu_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            solve_probe::self_t0(&solve_probe::B_CU)
        } else {
            None
        };
        let r = self.check_universe_inner(bump, cxt, t);
        solve_probe::phase_end(&solve_probe::B_CU, &solve_probe::C.cu_ns, &solve_probe::C.cu_self_ns, probe_t0);
        r
    }

    fn check_universe_inner<'a>(
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
                        unsolved,
                        globals,
                        eval_work,
                        ..
                    } = self;
                    let work: &mut Vec<W<'a>> = unsafe {
                        &mut *(eval_work as *mut Vec<W<'static>> as *mut Vec<W<'a>>)
                    };
                    work.clear();
                    prune_ty_bump(
                        bump, spine, work, vals, icits, defs, metas, unsolved, globals, &mask, mty,
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
                    self.remove_unsolved(m); // A-2 worklist 出表
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
                    unsolved,
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
                    bump, spine, work, vals, icits, defs, ren, metas, unsolved, globals, Some(m),
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
                solve_probe::C.sb_lams_cu_cnt.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                lams_from_ty(bump, spine, work, vals, icits, defs, metas, globals, args.len() as u32, mty, rhs)
            };
            let solution = self.eval(bump, EMPTY_ENV, lam_tm);
            self.metas[m as usize] = MetaEntry::Solved(solution, mty);
            self.remove_unsolved(m); // A-2 worklist 出表
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

/// q 的自由 `Var` 下标集合（升序去重；绑定器内的下标不算）。`fresh_meta`
/// close 化简用：只有这些下标对应的 telescope 槽必须保留 Let 包装。
fn free_var_indices(t: &Tm<'_>) -> Vec<u32> {
    let mut stack: Vec<(&Tm<'_>, u32)> = vec![(t, 0)];
    let mut out: Vec<u32> = Vec::new();
    while let Some((x, d)) = stack.pop() {
        match x {
            Tm::Var(i) => {
                if *i >= d && out.binary_search(i).is_err() {
                    let pos = out.partition_point(|y| *y < *i);
                    out.insert(pos, *i);
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
        }
    }
    out
}

/// 按 `map` 重编号项的自由 `Var` 下标（绑定器内的下标不动）。子树无变化时
/// 原样返回（指针相等），闭项零分配。
fn remap_free_vars<'a>(
    bump: &'a Bump,
    t: &'a Tm<'a>,
    map: &dyn Fn(u32) -> u32,
) -> &'a Tm<'a> {
    fn go<'a>(bump: &'a Bump, t: &'a Tm<'a>, d: u32, map: &dyn Fn(u32) -> u32) -> &'a Tm<'a> {
        match *t {
            Tm::Var(i) => {
                if i >= d {
                    let j = map(i);
                    if j != i {
                        return bump.alloc(Tm::Var(j));
                    }
                }
                t
            }
            Tm::Lam(n, icit, b) => {
                let b2 = go(bump, b, d + 1, map);
                if std::ptr::eq(b2, b) {
                    t
                } else {
                    bump.alloc(Tm::Lam(n, icit, b2))
                }
            }
            Tm::App(f, a, icit) => {
                let f2 = go(bump, f, d, map);
                let a2 = go(bump, a, d, map);
                if std::ptr::eq(f2, f) && std::ptr::eq(a2, a) {
                    t
                } else {
                    bump.alloc(Tm::App(f2, a2, icit))
                }
            }
            Tm::AppPruning(h, pr) => {
                let h2 = go(bump, h, d, map);
                if std::ptr::eq(h2, h) {
                    t
                } else {
                    bump.alloc(Tm::AppPruning(h2, pr))
                }
            }
            Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) | Tm::Prim => t,
            Tm::Obj(h, f) => {
                let h2 = go(bump, h, d, map);
                if std::ptr::eq(h2, h) {
                    t
                } else {
                    bump.alloc(Tm::Obj(h2, f))
                }
            }
            Tm::Pi(n, icit, a, b) => {
                let a2 = go(bump, a, d, map);
                let b2 = go(bump, b, d + 1, map);
                if std::ptr::eq(a2, a) && std::ptr::eq(b2, b) {
                    t
                } else {
                    bump.alloc(Tm::Pi(n, icit, a2, b2))
                }
            }
            Tm::Let(n, a, tt, u) => {
                let a2 = go(bump, a, d, map);
                let t2 = go(bump, tt, d, map);
                let u2 = go(bump, u, d + 1, map);
                if std::ptr::eq(a2, a) && std::ptr::eq(t2, tt) && std::ptr::eq(u2, u) {
                    t
                } else {
                    bump.alloc(Tm::Let(n, a2, t2, u2))
                }
            }
            Tm::Sum(name, params, cases, is_trait) => {
                let mut changed = false;
                let ps: &'a [SumParamT<'a>] = bump.alloc_slice_fill_iter(params.iter().map(|p| {
                    let v2 = go(bump, p.val, d, map);
                    let t2 = go(bump, p.ty, d, map);
                    if !std::ptr::eq(v2, p.val) || !std::ptr::eq(t2, p.ty) {
                        changed = true;
                    }
                    SumParamT {
                        name: p.name,
                        val: v2,
                        ty: t2,
                        icit: p.icit,
                    }
                }));
                if !changed {
                    t
                } else {
                    bump.alloc(Tm::Sum(name, ps, cases, is_trait))
                }
            }
            Tm::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
            } => {
                let t2 = go(bump, typ, d, map);
                let mut changed = !std::ptr::eq(t2, typ);
                let ds: &'a [SumDataT<'a>] = bump.alloc_slice_fill_iter(datas.iter().map(|dd| {
                    let v2 = go(bump, dd.val, d, map);
                    if !std::ptr::eq(v2, dd.val) {
                        changed = true;
                    }
                    SumDataT {
                        name: dd.name,
                        val: v2,
                        icit: dd.icit,
                    }
                }));
                if !changed {
                    t
                } else {
                    bump.alloc(Tm::SumCase {
                        typ: t2,
                        case_name,
                        datas: ds,
                        is_trait,
                    })
                }
            }
            Tm::Match(s, cases) => {
                let s2 = go(bump, s, d, map);
                let mut changed = !std::ptr::eq(s2, s);
                let cs: &'a [(PatternDetail, &'a Tm<'a>)] =
                    bump.alloc_slice_fill_iter(cases.iter().map(|(pd, b)| {
                        let b2 = go(bump, b, d, map);
                        if !std::ptr::eq(b2, *b) {
                            changed = true;
                        }
                        (pd.clone(), b2)
                    }));
                if !changed {
                    t
                } else {
                    bump.alloc(Tm::Match(s2, cs))
                }
            }
        }
    }
    go(bump, t, 0, map)
}

/// `fresh_meta` close 的**值中性化简**（2026-09-21 L10 traitchain O(n²) 内存
/// 修复）：`close_tm_until(locals, k, q)` 把前 k 条 telescope 全量包上，其中
/// 「q 未引用的 define 槽」是纯死重——`Let(x, A, t, body)` 包一个 body 不
/// 引用的 x，求值结果与不包相同（参考版的 Let 层在这种位置从不进入输出；
/// `binds == 0 && !has_free_var(q)` 快路径的同族论证）。本函数只保留：
///
/// 1. **全部 Bind 槽**（Π 层是参考版可观察语义，丢了会与参考版分叉）；
/// 2. **q 实际引用的 define 槽**（q 的 Var 靠它们解析）。
///
/// 其余 define 槽丢弃；q 的自由变量下标按保留槽位重编号到新位置。走查范围
/// = 前 k 条（≥ flat_len 的非平坦层）——Bind 只可能出现在这一区（平坦区
/// 只由 `env_ext_defs`  tip 路径增长、该路径要求 `binds.is_none()`）；q 引用
/// 平坦层（下标 ≥ k）的 Var 保持自由、由调用方的 `global_env` 解析，与舊
/// 路径「以平坦区为基底环境求值」一致。
fn close_tm_reduced<'a>(
    bump: &'a Bump,
    locals: Option<&'a LCons<'a>>,
    q: &'a Tm<'a>,
    k: usize,
) -> (&'a Tm<'a>, usize) {
    let free = free_var_indices(q);
    let mut kept: Vec<&'a LCons<'a>> = Vec::new();
    let mut kept_pos: Vec<usize> = Vec::new();
    let mut ls = locals;
    for p in 0..k {
        let Some(n) = ls else { break };
        // Bind 槽（t_t = None）全留；define 槽仅被引用时留
        if n.t_t.is_none() || free.binary_search(&(p as u32)).is_ok() {
            kept.push(n);
            kept_pos.push(p);
        }
        ls = n.next;
    }
    let n_kept = kept.len();
    if kept.is_empty() {
        // 无 Bind 且 q 不引用任何非平坦 define：q 原样（其自由变量只能指向
        // 平坦层，由 global_env 解析）
        return (q, 0);
    }
    let q2 = remap_free_vars(bump, q, &|i| {
        kept_pos
            .binary_search(&(i as usize))
            .map(|r| r as u32)
            .unwrap_or(i)
    });
    let mut b = q2;
    for n in kept.iter() {
        b = match n.t_t {
            None => bump.alloc(Tm::Pi(n.name, Icit::Expl, n.a_t, b)),
            Some(t) => bump.alloc(Tm::Let(n.name, n.a_t, t, b)),
        };
    }
    (b, n_kept)
}

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
        }
    }
    false
}

impl Machine {
    // check_pm / unify_pm / subst_cxt（参考版 elaboration.rs + cxt.rs 的模式
    // 特化机制——特化解累积为显式替换 σ，消费点 subst_cxt 包裹）
    // --------------------------------------------------------------------------------

    /// 特化合一（参考版 elaboration.rs `unify_pm` 同构）：可解臂把解**累加
    /// 进 `spec.acc`**（显式替换），不再改写 env 槽。方程两侧在入口置于当前
    /// acc 之下再解释（`subst ɑ vs` 的惰性等价物）。
    ///
    /// 与 trait 求解的交互：本函数**只**服务模式方程路径（Compiler 的
    /// `check_pm`/`check_pm_final`）；trait 实例求解走常规 `unify`
    /// （`solve_trait_ref`），不带 spec——实例求解过程中的合一**不会**获得
    /// 特化解能力（对齐旧 update_cxt 只从 unify_pm 调用的边界）。
    pub(super) fn unify_pm<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        l: u32,
        t: V,
        t_prime: V,
        t_span: &crate::parser_lib::Span<()>,
        spec: &mut SpecSolve,
    ) -> Result<(), Error> {
        let mut f1 = self.force_v(bump, t);
        let mut f2 = self.force_v(bump, t_prime);
        if !spec.acc.is_empty() {
            f1 = {
                let Machine { spine, defs, metas, globals, .. } = self;
                force(bump, spine, defs, metas, globals, wrap_sub(bump, &spec.acc, f1))
            };
            f2 = {
                let Machine { spine, defs, metas, globals, .. } = self;
                force(bump, spine, defs, metas, globals, wrap_sub(bump, &spec.acc, f2))
            };
        }
        // (Rigid(x1, []), Rigid(x2, [])) if x1 == x2 → 自反（旧
        // update_cxt(x1, t_prime, false) 对槽值的重写是恒等，语义为 Ok）
        if v_tag(f1) == 0 && v_tag(f2) == 0 && v_lvl_of(f1) == v_lvl_of(f2) {
            return Ok(());
        }
        // 单侧裸 Rigid → 解入 acc（update_prune 的 pruning 改写不再发生）
        if v_tag(f1) == 0 {
            return self.solve_pm(f1, f2, t_span, spec);
        }
        if v_tag(f2) == 0 {
            return self.solve_pm(f2, f1, t_span, spec);
        }
        // 同名 SumCase：逐 datas（值槽）。**不比 typ 的值**（typ 的索引槽是
        // 这些值自身的构造子形态，比值会在互相引用上深递归），但**比 typ 的
        // Sum 头名字**：跨 enum 重名构造子（E1.c / E2.c）是两个不同值，同
        // case_name 不足以判定身份——头名不同直接失败，构造子身份判据局部
        // 化，不押"喂进方程的两侧必齐型"这条未检查的不变式（参考版 2026-
        // 09-18 评审修复同步）。
        if v_tag(f1) == 7 && v_tag(f2) == 7 {
            if let (
                XCell::SumCase { typ: ty1, case_name: n1, datas: d1, .. },
                XCell::SumCase { typ: ty2, case_name: n2, datas: d2, .. },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    if let (
                        XCell::Sum { name: m1, .. },
                        XCell::Sum { name: m2, .. },
                    ) = (v_xcell_of(self.force_v(bump, *ty1)), v_xcell_of(self.force_v(bump, *ty2)))
                    {
                        if m1 != m2 {
                            return Err(Error(t_span.map(|_| "".to_string())));
                        }
                    }
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(bump, cxt, l, x.val, y.val, t_span, spec)?;
                    }
                    return Ok(());
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
            // 同名 Sum：逐参数（值槽）
            if let (
                XCell::Sum { name: n1, params: d1, .. },
                XCell::Sum { name: n2, params: d2, .. },
            ) = (v_xcell_of(f1), v_xcell_of(f2))
            {
                if n1 == n2 {
                    for (x, y) in d1.iter().zip(d2.iter()) {
                        self.unify_pm(bump, cxt, l, x.val, y.val, t_span, spec)?;
                    }
                    return Ok(());
                }
                return Err(Error(t_span.map(|_| "".to_string())));
            }
        }
        self.unify_catch_at(bump, l, cxt, f1, f2)
    }

    /// 可解臂：x（裸 rigid）:= v 解入 acc。Flex 解值保持旧 `update_cxt` 的
    /// no-op（那时对 Flex 直接 clone、不改写槽）；occurs 环守卫只扫解值
    /// 自身结构，失败 = 方程不可满足（分支不可达）。
    fn solve_pm(
        &self,
        xv: V,
        v: V,
        t_span: &crate::parser_lib::Span<()>,
        spec: &mut SpecSolve,
    ) -> Result<(), Error> {
        if is_flex(&self.spine, v) {
            return Ok(());
        }
        let x = v_lvl_of(xv);
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
    /// A-2：`unsolved` worklist 与 metas 表严格同步（探测期 push/Solved 摘除
    /// 照常入出表），回滚两表同换。
    fn run_pure_probe<R>(&mut self, f: impl FnOnce(&mut Machine) -> R) -> R {
        let metas = self.metas.clone();
        let unsolved = self.unsolved.clone();
        let r = f(self);
        self.metas = metas;
        self.unsolved = unsolved;
        r
    }

    /// `check_pm`：infer + insert + `unify_pm`（返回累积的 σ）。
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
        // 模式编译入口充值精化燃料池
        refuel();
        let mut spec = SpecSolve { acc: Rc::new(SubstV::default()) };
        self.unify_pm(bump, cxt, cxt.lvl, a, inferred_type, &t_span, &mut spec)?;
        Ok((t_inferred, spec.acc))
    }

    /// `check_pm_final`：`check_pm` 之后把原始值与精化后的期望再对一次
    /// （失败容忍——丢弃第二次方程的解，参考版 `.unwrap_or(new_cxt)` 同款）。
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
        // 模式编译入口充值精化燃料池
        refuel();
        let mut spec = SpecSolve { acc: Rc::new(SubstV::default()) };
        self.unify_pm(bump, cxt, cxt.lvl, a, inferred_type, &t_span, &mut spec)?;
        // 期望类型重锚：在 σ 之下的上下文里重求值模式项值
        let cxt2 = subst_cxt(bump, &self.defs, &spec.acc, cxt);
        let ori_v = self.eval(bump, cxt2.env, t_inferred);
        let mut spec2 = SpecSolve { acc: spec.acc.clone() };
        if self.unify_pm(bump, &cxt2, cxt2.lvl, ori, ori_v, &t_span, &mut spec2).is_ok() {
            spec.acc = spec2.acc;
        }
        Ok((t_inferred, spec.acc))
    }

    // L10：trait 方法包装（参考版 elaboration.rs `trait_wrap` 逐句移植）
    // --------------------------------------------------------------------------------

    /// 字段未命中时在 trait 表里找同名方法：能合成出实例 → 生成
    /// `let $method = λ...; $method x` 的包装项；否则报 "has no object"。
    fn trait_wrap<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: crate::parser_lib::Span<String>,
        a: V,
        x: &Raw,
        tm: &'a Tm<'a>,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = if solve_probe::on() {
            solve_probe::C.tw_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            solve_probe::self_t0(&solve_probe::B_TW)
        } else {
            None
        };
        let probe_idx = solve_probe::on().then(|| solve_probe::C.tw_calls.load(std::sync::atomic::Ordering::Relaxed));
        // 接收者类型深推开（槽位嵌套精化 σ），旧机制下这些槽位已被
        // update_cxt/refresh 物化
        let a = {
            let Machine {
                spine,
                defs,
                metas,
                globals,
                ..
            } = self;
            force_deep(bump, spine, defs, metas, globals, a)
        };
        // has_no_object 不做成闭包（避免 &self 捕获与 infer_expr 的 &mut
        // 冲突）——两个错误点直接调用 [`Self::mk_no_object_err`]
        let Some(typ) = val_to_typ(&self.spine, &self.defs, a) else {
            if let (Some(t0), Some(idx)) = (probe_t0, probe_idx) {
                solve_probe::tw_phase_end(&solve_probe::B_TW, &solve_probe::C.tw_ns, &solve_probe::C.tw_self_ns, Some(t0), idx, &solve_probe::C.tw_early_ns, &solve_probe::C.tw_early_max_ns, &solve_probe::C.tw_late_ns, &solve_probe::C.tw_late_max_ns);
            }
            return Err(self.mk_no_object_err(cxt, &t, a, tm));
        };
        // 方法名命中的 trait：合成 `Any × len(out_param)` 参数的 Assertion
        // （首参 = 接收者类型）——能解出实例才包装
        let defs: Vec<(
            String,
            Vec<(crate::parser_lib::Span<String>, Raw, Icit)>,
            Vec<bool>,
            (crate::parser_lib::Span<String>, Vec<(crate::parser_lib::Span<String>, Raw, Icit)>, Raw),
        )> = self
            .tstate
            .definition
            .iter()
            .flat_map(|(trait_name, (trait_params, out_param, methods))| {
                methods.iter().find(|x| x.0.data == t.data).map(|x| {
                    (trait_name.clone(), trait_params.clone(), out_param.clone(), x.clone())
                })
            })
            .filter(|(trait_name, _, out_param, _)| {
                let len = out_param.iter().filter(|x| !**x).count();
                if len == 0 {
                    return false;
                }
                let mut args = vec![Typ::Any; len];
                args[0] = typ.clone();
                self.tstate.solver.clean();
                // 参考版：断言名用 **trait 名**（类表按 trait 名注册；用方法
                // 名会让 new_subgoal 的 unwrap panic）
                self.tstate
                    .solver
                    .synth(Assertion {
                        name: trait_name.clone(),
                        arguments: args,
                    })
                    .is_some()
            })
            .collect();
        if let Some(t0) = probe_t0 {
            solve_probe::C.tw_cand.fetch_add(defs.len() as u64, std::sync::atomic::Ordering::Relaxed);
            solve_probe::C.tw_defs_ns.fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        let probe_tb = solve_probe::on().then(std::time::Instant::now);
        // 参考版取第一个能推断成功的包装（traits.first().and_then(infer.ok)）
        let mut result: Option<Result<(&'a Tm<'a>, V), Error>> = None;
        for (trait_name, trait_params, _out_param, (methods_name, methods_params, ret_type)) in defs {
            let mut params = trait_params.clone();
            params.push((
                methods_name.clone().map(|_| "$this".to_owned()),
                Raw::Var(methods_name.clone().map(|_| "Self".to_owned())),
                Icit::Expl,
            ));
            params.push((
                methods_name.clone().map(|_| "$$".to_owned()),
                trait_params
                    .iter()
                    .map(|x| x.0.clone())
                    .fold(
                        Raw::Var(methods_name.clone().map(|_| trait_name.clone())),
                        |ret, x| Raw::App(Box::new(ret), Box::new(Raw::Var(x)), Either::Icit(Icit::Impl)),
                    ),
                Icit::Impl,
            ));
            params.extend(methods_params.iter().cloned());
            let body = std::iter::once((
                Raw::Var(methods_name.clone().map(|_| "$this".to_owned())),
                Icit::Expl,
            ))
            .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
            .fold(
                Raw::Obj(
                    Box::new(Raw::Var(methods_name.clone().map(|_| "$$".to_owned()))),
                    methods_name.clone(),
                ),
                |ret, (x, icit)| Raw::App(Box::new(ret), Box::new(x), Either::Icit(icit)),
            );
            let decl = Raw::Let(
                methods_name.clone().map(|x| format!("${x}")),
                Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                })),
                Box::new(params.iter().rev().fold(body, |a, b| {
                    Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                })),
                Box::new(Raw::App(
                    Box::new(Raw::Var(methods_name.clone().map(|x| format!("${x}")))),
                    Box::new(x.clone()),
                    Either::Icit(Icit::Expl),
                )),
            );
            if let Some(tb) = probe_tb {
                solve_probe::C.tw_build_ns.fetch_add(tb.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            }
            let probe_ti = solve_probe::on().then(std::time::Instant::now);
            let r = self.infer_expr(bump, cxt, &decl);
            if let Some(ti) = probe_ti {
                solve_probe::C.tw_infer_ns.fetch_add(ti.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            }
            if r.is_ok() {
                result = Some(r);
                break;
            }
        }
        match result {
            Some(r) => {
                if let Some(t0) = probe_t0 {
                    solve_probe::C.tw_infer.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                if let (Some(t0), Some(idx)) = (probe_t0, probe_idx) {
                    solve_probe::tw_phase_end(&solve_probe::B_TW, &solve_probe::C.tw_ns, &solve_probe::C.tw_self_ns, Some(t0), idx, &solve_probe::C.tw_early_ns, &solve_probe::C.tw_early_max_ns, &solve_probe::C.tw_late_ns, &solve_probe::C.tw_late_max_ns);
                }
                r
            }
            None => {
                if let (Some(t0), Some(idx)) = (probe_t0, probe_idx) {
                    solve_probe::tw_phase_end(&solve_probe::B_TW, &solve_probe::C.tw_ns, &solve_probe::C.tw_self_ns, Some(t0), idx, &solve_probe::C.tw_early_ns, &solve_probe::C.tw_early_max_ns, &solve_probe::C.tw_late_ns, &solve_probe::C.tw_late_max_ns);
                }
                Err(self.mk_no_object_err(cxt, &t, a, tm))
            }
        }
    }

    /// Obj/trait 包装失败的消息（参考版 `\`{}\`: {:?} has no object \`{}\``）。
    fn mk_no_object_err(
        &self,
        cxt: &Cxt<'_>,
        t: &crate::parser_lib::Span<String>,
        a: V,
        tm: &Tm<'_>,
    ) -> Error {
        Error(t.clone().map(|t| {
            format!(
                "`{}`: {} has no object `{}`",
                pretty_tm(0, types_names_list(cxt.types), &export(tm)),
                debug_val(&self.spine, &self.defs, a),
                t,
            )
        }))
    }

    // 主 infer / infer_expr（与参考版 elaboration.rs 逐臂对应）
    // --------------------------------------------------------------------------------

    pub(super) fn infer_expr<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = if solve_probe::on() {
            solve_probe::C.ie_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            match t {
                Raw::Var(_) => solve_probe::C.ie_var.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                Raw::Obj(_, _) => solve_probe::C.ie_obj.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                Raw::App(_, _, _) => solve_probe::C.ie_app.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                Raw::Pi(_, _, _, _) => solve_probe::C.ie_pi.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                Raw::Lam(_, _, _) => solve_probe::C.ie_lam.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                Raw::Let(_, _, _, _) => solve_probe::C.ie_let.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                _ => solve_probe::C.ie_other.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            };
            solve_probe::self_t0(&solve_probe::B_IE)
        } else {
            None
        };
        let r = self.infer_expr_inner(bump, cxt, t);
        solve_probe::phase_end(&solve_probe::B_IE, &solve_probe::C.ie_ns, &solve_probe::C.ie_self_ns, probe_t0);
        r
    }

    /// 名字 → (Tm::Var 的索引, 类型值)：局部 names 优先，之后回落 Machine 的
    /// 全局名字表（参考版 Raw::Var 臂同款解析序）。可达性探测只要类型值，
    /// 与 `infer_expr_inner` 的 Var 臂共用本函数，避免两处解析漂移。
    #[inline]
    pub(super) fn resolve_name(&self, cxt: &Cxt<'_>, x: &str) -> Option<(u32, V)> {
        let (blvl, ty) = if let Some(&blvl) = cxt.names.by_name.get(x) {
            (blvl, *cxt.names.by_lvl.get(&blvl).expect("by_lvl 缺层级"))
        } else if let Some(&(blvl, ty)) = self.global_names.get(x) {
            (blvl, ty)
        } else {
            return None;
        };
        let ix = if blvl >= GLOBAL_BASE {
            blvl
        } else {
            cxt.lvl - blvl - 1
        };
        Some((ix, ty))
    }

    fn infer_expr_inner<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: &Raw,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        match t {
            // 变量：局部 names（当前 def 的 binder + fake 占位，覆盖全局）
            // 优先，之后回落 Machine 的全局名字表（顶层 define）。都缺即
            // not in scope（参考版 Raw::Var 臂同款）。
            Raw::Var(x) => match self.resolve_name(cxt, x.data.as_str()) {
                Some((ix, ty)) => Ok((bump.alloc(Tm::Var(ix)), ty)),
                None => Err(Error(x.clone().map(|x| format!("error name not in scope: {}", x)))),
            },

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
                        // 类型链取字段类型（**U(0) 占位怪癖保留**——参考版
                        // TODO 注释原样：显式 binder 以 U(0) 实例化）
                        let mut c: Option<Vec<(&str, V)>> = None;
                        if cases.len() == 1 && cases[0].contains(".mk") {
                            let case = cases[0];
                            if let Ok((_, case_typ)) =
                                self.infer_expr(bump, cxt, &Raw::Var(empty_span(case.to_string())))
                            {
                                let mut ret: Vec<(&str, V)> = vec![];
                                let mut typ = case_typ;
                                let mut param: Vec<&SumParamV<'_>> =
                                    params.iter().collect();
                                param.reverse();
                                loop {
                                    let typ_f = self.force_v(bump, typ);
                                    if v_tag(typ_f) == 4 {
                                        let p = v_pi_of(typ_f);
                                        if p.icit == Icit::Expl {
                                            ret.push((p.name, p.dom));
                                            typ = {
                                                let env = env_ext(bump, p.env, v_u(0));
                                                self.eval(bump, env, p.body)
                                            };
                                        } else {
                                            let val = param
                                                .pop()
                                                .map(|x| x.val)
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
                        // L10：Sum 接收者字段未命中 → trait 方法包装
                        //（参考版把 **force 后**的类型传给 trait_wrap）
                        return self.trait_wrap(bump, cxt, t.clone(), a_f, x, tm);
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
                        // L10：SumCase 接收者字段未命中 → trait 方法包装
                        return self.trait_wrap(bump, cxt, t.clone(), a_f, x, tm);
                    }
                }
                // L10：其余接收者形态 → trait 方法包装（失败给原文案）
                self.trait_wrap(bump, cxt, t.clone(), a, x, tm)
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
            Raw::Sum(name, params, cases, universe, is_trait) => {
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
                        *is_trait,
                    )),
                    v_u(*universe),
                ))
            }

            // 构造子值（Decl::Enum 注册期构造）：typ 只推断不检查
            Raw::SumCase {
                typ,
                case_name,
                datas,
                is_trait,
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

                // 参考版 Def 臂：检查后 `solve_multi_trait(0)`，求解失败由
                // `.map_err(...)?` 返回可恢复错误（对齐参考版口径：Debug
                // 序列化 `UnifyError::Trait(msg)` → `Trait("...")`；L11 快版
                // 同款——此前本臂缺这道 def 级求解，检查过但留有可解 trait
                // meta 的 def 会漏解，与参考版分叉）。

                self.solve_multi_trait_ref(bump, &fake, 0)
                    .map_err(|e| Error(name.to_span().map(|_| format!("Trait({:?})", e))))?;
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
                is_trait,
                name,
                params,
                cases,
            } => {
                // 隐式参数是类型参数：无标注（Hole）的域钉为 U(0)（与参考版
                // 同步，L07/L08 黑盒三轮修复的前向传播）。域洞若保留，第
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
                    let vtyp = self.eval(bump, cxt.env, typ_tm);
                    // 构造子良构性（参考版同步，2026-09-18 评审修复）：ret 必
                    // 须是本 enum 的 Sum 且参数位是 telescope 内的 bare rigid
                    self.check_ctor_wf(bump, &cxt, &name.data, &ctor_name.data, vtyp)?;
                    let t_tm = self.check(bump, &cxt, &bod, vtyp)?;
                    let vt = self.eval(bump, cxt.env, t_tm);
                    cxt = self.define_name_in(bump, &mut cxt, &ctor_name.data, typ_tm, t_tm, vt, vtyp);
                }
                Ok((DeclOut::Enum, cxt))
            }
            // trait 声明：solver 注册新类；Self + params 组成 enum 参数
            //（out_param 参数的类型是 `outParam(...)` 应用）；方法表记入
            // trait_definition；本体脱糖成单构造子（`{Name}.mk`）的 trait
            // enum（is_trait=true）
            Decl::TraitDecl { name, params, methods } => {
                self.tstate.solver.new_trait(name.data.clone());
                let mut param = vec![(name.clone().map(|_| "Self".to_owned()), Raw::Hole, Icit::Impl)];
                param.append(&mut params.clone());
                let out_param = param.iter().map(|x| match &x.1 {
                        Raw::App(t, ..) if matches!(t.as_ref(), Raw::Var(d) if d.data == "outParam") => true,
                        _ => false,
                    }).collect::<Vec<_>>();
                self.tstate.definition.insert(name.data.clone(), (param.clone(), out_param.clone(), methods.clone()));
                self.tstate.out_param.insert(name.data.clone(), out_param);
                let mut cxt = clone_cxt(cxt);
                let new_cases = vec![(
                    name.clone().map(|x| format!("{x}.mk")),
                    methods
                        .iter()
                        .map(|x| (
                            x.0.clone(),
                            std::iter::once((x.0.clone().map(|_| "this".to_owned()), Raw::Var(x.0.clone().map(|_| "Self".to_owned())), Icit::Expl))
                                .chain(x.1.iter().cloned())
                                .rev()
                                .fold(x.2.clone(), |a, b| {
                                    Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                                }),
                            Icit::Expl,
                        ))
                        .collect(),
                    None,
                )];
                let (_, c) = self.infer_decl(bump, &mut cxt, &Decl::Enum {
                    is_trait: true,
                    name: name.clone(),
                    params: param,
                    cases: new_cases,
                })?;
                cxt = c;
                Ok((DeclOut::Trait, cxt))
            }
            // 实例声明：need_create 时先合成 trait 声明；实例类型经
            // to_typ 收集（out_param 槽剔除）；登记 Instance 后把方法
            // 包成 `λ this. body` 的 def（名 = "{:?}{:?}" 的 typ_name）
            Decl::ImplDecl { name, params, trait_name, trait_params, methods, need_create } => {
                let mut cxt = clone_cxt(cxt);
                if *need_create {
                    let new_methods = methods
                        .iter()
                        .filter_map(|x| match x {
                            Decl::Def { name, params, ret_type, body: _ } => {
                                Some((name.clone(), params.clone(), ret_type.clone()))
                            },
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    let (_, new_cxt) = self.infer_decl(bump, &mut cxt, &Decl::TraitDecl {
                        name: trait_name.clone(),
                        params: params.clone(),
                        methods: new_methods,
                    })?;
                    cxt = new_cxt;
                }
                for (x, a, _) in params.iter() {
                    let (a_checked, _) = self.check_universe(bump, &cxt, a)?;
                    let a_eval = self.eval(bump, cxt.env, a_checked);
                    let a_t = self.quote(bump, cxt.lvl, a_eval);
                    cxt = self.bind_name(bump, &cxt, &x.data, a_t, a_eval);
                }
                let name_raw = (*name).clone();
                let typ = self.check_universe(bump, &cxt, &name_raw)?.0;
                let typ_val = self.eval(bump, cxt.env, typ);
                let typ = val_to_typ(&self.spine, &self.defs, typ_val)
                    .ok_or_else(|| Error(name.to_span().map(|_| "Not a type".to_string())))?;
                let mut trait_param = vec![typ.clone()];
                for a in trait_params.iter() {
                    let (a_checked, _) = self.check_universe(bump, &cxt, a)?;
                    let a_eval = self.eval(bump, cxt.env, a_checked);
                    match val_to_typ(&self.spine, &self.defs, a_eval) {
                        Some(x) => trait_param.push(x),
                        None => return Err(Error(trait_name.clone().map(|_| "Not a type".to_string()))),
                    };
                }
                let out_param = self.tstate.out_param.get(&trait_name.data)
                    .ok_or(Error(trait_name.clone().map(|n| format!("trait `{}` not declared", n))))?;
                let trait_param: Vec<Typ> = trait_param.into_iter()
                    .zip(out_param.iter())
                    .filter(|(_, o)| !**o)
                    .map(|(x, _)| x)
                    .collect();
                let typ_name = format!("{:?}{:?}", trait_name.data, trait_param);
                let inst = Instance {
                    assertion: Assertion { name: trait_name.data.clone(), arguments: trait_param },
                    dependencies: crate::list::List::new(),
                    lvl: trait_name.clone().to_span().map(|_| typ_name.clone()),
                };
                self.tstate.solver.impl_trait_for(trait_name.data.clone(), inst);
                let mut ret = std::iter::once((*name).clone())
                    .chain(trait_params.iter().cloned())
                    .fold(Raw::Var(trait_name.clone().map(|x| format!("{x}.mk"))), |ret, x| {
                        Raw::App(Box::new(ret), Box::new(x), Either::Icit(Icit::Impl))
                    });
                for decl in methods {
                    if let Decl::Def { name: def_name, params, ret_type: _, body } = decl {
                        ret = Raw::App(
                            Box::new(ret),
                            Box::new(Raw::Lam(
                                def_name.clone().map(|_| "this".to_owned()),
                                Either::Icit(Icit::Expl),
                                Box::new(params.iter().rev()
                                    .fold(body.clone(), |ret, x| Raw::Lam(x.0.clone(), Either::Icit(x.2), Box::new(ret)))
                                )
                            )),
                            Either::Icit(Icit::Expl),
                        );
                    }
                }
                let trait_name_raw = Raw::Var(trait_name.clone());
                let ret_type = trait_params.iter().cloned()
                    .fold(Raw::App(
                        Box::new(trait_name_raw),
                        Box::new((*name).clone()),
                        Either::Icit(Icit::Impl)
                    ), |a, b| Raw::App(Box::new(a), Box::new(b), Either::Icit(Icit::Impl)));
                let def_name = trait_name.clone().to_span().map(|_| typ_name.clone());
                let (_, c) = self.infer_decl(bump, &mut cxt, &Decl::Def {
                    name: def_name,
                    params: params.clone(),
                    ret_type,
                    body: ret,
                })?;
                cxt = c;
                Ok((DeclOut::TraitImpl, cxt))
            }
        }
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

/// 把精化替换 σ 施加到上下文（参考版 `Cxt::subst_cxt` / dpm-nbe
/// `subst sub ctx`）：env 槽、`names.by_lvl`（名字查类型的影子索引）与
/// `types` 链的类型包 VSub；lvl / locals / pruning / binds 不动——**槽位
/// 布局（= 运行时布局）不变**，被解变量仍在原槽位，读点经 force 展开看到
/// 解。σ 为空时零开销直通。
///
/// 影子索引同步是孪生特有坑：`Raw::Var` 的快路径经 `names.by_name` 取层级、
/// 再读 `names.by_lvl` 的类型；只包 `types` 链会漏掉那条路径（嵌套 match 的
/// scrutinee 类型丢外层精化 → 误判 nil 可达）。
pub(super) fn subst_cxt<'a>(bump: &'a Bump, defs: &[V], sub: &Rc<SubstV>, cxt: &Cxt<'a>) -> Cxt<'a> {
    if sub.is_empty() {
        return clone_cxt(cxt);
    }
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
    let names = {
        let mut n = (*cxt.names).clone();
        for (_, v) in n.by_lvl.iter_mut() {
            *v = wrap_sub(bump, sub, *v);
        }
        Rc::new(n)
    };
    Cxt {
        env: frcs_env(bump, defs, sub, cxt.env),
        names,
        types: wrap_types(bump, sub, cxt.types),
        locals: cxt.locals,
        pruning: cxt.pruning,
        binds: cxt.binds,
        lvl: cxt.lvl,
    }
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
    Trait,
    TraitImpl,
}

// Debug 复刻（错误消息里内嵌的 `{:?}` 输出；名字 Span 全零——套件比对
// 前按 start_offset/end_offset/path_id 归一化）
// --------------------------------------------------------------------------------

fn dbg_span_str(s: &str) -> String {
    format!("{:?} @ {},{}", s, 0, 0)
}

fn dbg_span_unit() -> String {
    "() @ 0,0".to_string()
}

/// `{:?}` 的字符串字面量转义（Debug 的 escape_debug 语义：引号与控制
/// 字符转义，其余原样）。
fn strconv_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// 参考 `Val` 的 Debug 形态（递归；闭包体走 Tm Debug）。
fn debug_val(spine: &Spine, defs: &[V], v: V) -> String {
    let mut out = String::new();
    debug_val_go(spine, defs, v, &mut out);
    out
}

fn debug_spine(spine: &Spine, defs: &[V], h: usize, out: &mut String) {
    let mut args: Vec<(V, Icit)> = Vec::new();
    spine.collect_args(h, &mut args);
    // collect_args 产出 = 逆应用序（内层在前）；参考 Spine = List（头 =
    // 最后应用 = 内层）——Debug 序一致
    out.push('[');
    for (k, (a, i)) in args.iter().enumerate() {
        if k > 0 {
            out.push_str(", ");
        }
        out.push('(');
        debug_val_go(spine, defs, *a, out);
        out.push_str(", ");
        out.push_str(debug_icit(*i));
        out.push(')');
    }
    out.push(']');
}

fn debug_val_go(spine: &Spine, defs: &[V], v: V, out: &mut String) {
    match v_tag(v) {
        0 => {
            out.push_str(&format!("Rigid(Lvl({}), ", v_lvl_of(v)));
            out.push_str("[])");
        }
        1 => {
            let c = v_clo_of(v);
            out.push_str(&format!(
                "Lam({}, {}, Closure(.., ",
                dbg_span_str(c.name),
                debug_icit(c.icit)
            ));
            debug_tm_go(c.body, out);
            out.push_str("))");
        }
        2 => {
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            match v_tag(hd) {
                0 => {
                    out.push_str(&format!("Rigid(Lvl({}), ", v_lvl_of(hd)));
                    debug_spine(spine, defs, h, out);
                    out.push(')');
                }
                5 => {
                    out.push_str(&format!("Flex(MetaVar({}), ", v_meta_of(hd)));
                    debug_spine(spine, defs, h, out);
                    out.push(')');
                }
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, name } => {
                        out.push_str("Obj(");
                        debug_val_go(spine, defs, *val, out);
                        out.push_str(&format!(", {}, ", dbg_span_str(name)));
                        debug_spine(spine, defs, h, out);
                        out.push(')');
                    }
                    _ => {
                        // 其余头不可达（v_app panic，进不了链）；防御输出
                        out.push_str("Neutral(...)");
                    }
                },
                _ => out.push_str("Neutral(...)"),
            }
        }
        3 => {
            out.push_str(&format!("U({})", v_u_of(v)));
        }
        4 => {
            let p = v_pi_of(v);
            out.push_str(&format!(
                "Pi({}, {}, {}, Closure(.., ",
                dbg_span_str(p.name),
                debug_icit(p.icit),
                debug_val(spine, defs, p.dom)
            ));
            debug_tm_go(p.body, out);
            out.push_str("))");
        }
        5 => {
            out.push_str(&format!("Flex(MetaVar({}), [])", v_meta_of(v)));
        }
        6 => out.push_str("LiteralType"),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => {
                out.push_str(&format!("LiteralIntro({})", dbg_span_str(s)));
            }
            XCell::Prim => out.push_str("Prim"),
            XCell::Obj { val, name } => {
                out.push_str(&format!(
                    "Obj({}, {}, [])",
                    debug_val(spine, defs, *val),
                    dbg_span_str(name)
                ));
            }
            XCell::VSub { val, .. } => {
                out.push_str(&format!("VSub({})", debug_val(spine, defs, *val)));
            }
            XCell::Sum { name, params, cases, is_trait } => {
                out.push_str(&format!("Sum({}, [", dbg_span_str(name)));
                for (k, p) in params.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!(
                        "({}, {}, {}, {})",
                        dbg_span_str(p.name),
                        debug_val(spine, defs, p.val),
                        debug_val(spine, defs, p.ty),
                        debug_icit(p.icit)
                    ));
                }
                out.push_str("], [");
                for (k, c) in cases.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&dbg_span_str(c));
                }
                out.push_str(&format!("], {})", is_trait));
            }
            XCell::SumCase { is_trait, typ, case_name, datas } => {
                out.push_str(&format!(
                    "SumCase {{ is_trait: {}, typ: {}, case_name: {}, datas: [",
                    is_trait,
                    debug_val(spine, defs, *typ),
                    dbg_span_str(case_name)
                ));
                for (k, d) in datas.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&format!(
                        "({}, {}, {})",
                        dbg_span_str(d.name),
                        debug_val(spine, defs, d.val),
                        debug_icit(d.icit)
                    ));
                }
                out.push_str("]) }");
            }
            XCell::Match { scrutinee, env, cases } => {
                out.push_str(&format!(
                    "Match({}, ",
                    debug_val(spine, defs, *scrutinee)
                ));
                // 捕获 env（List<Val> 的 debug_list）
                out.push('[');
                let n = env_len(*env);
                for i in 0..n {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let sv = env_nth(defs, *env, i);
                    let mut tmp = String::new();
                    debug_val_go(spine, defs, sv, &mut tmp);
                    out.push_str(&tmp);
                }
                out.push_str("], [");
                for (k, (p, b)) in cases.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    out.push('(');
                    debug_pat_go(p, out);
                    out.push_str(", ");
                    debug_tm_go(b, out);
                    out.push(')');
                }
                out.push_str("])");
            }
        },
        _ => out.push_str("Val(...)"),
    }
}

fn debug_icit(i: Icit) -> &'static str {
    match i {
        Icit::Impl => "Impl",
        Icit::Expl => "Expl",
    }
}

fn debug_pat_go(p: &PatternDetail, out: &mut String) {
    match p {
        PatternDetail::Any(_) => {
            out.push_str(&format!("Any({})", dbg_span_unit()));
        }
        PatternDetail::Bind(name) => {
            out.push_str(&format!("Bind({})", dbg_span_str(&name.data)));
        }
        PatternDetail::Con(name, subs) => {
            out.push_str(&format!("Con({}, [", dbg_span_str(&name.data)));
            for (k, s) in subs.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                debug_pat_go(s, out);
            }
            out.push_str("])");
        }
    }
}

/// 参考 `Tm` 的 Debug 形态（快版 bump 项 → 参考格式；`Var` 印成 `Ix`）。
fn debug_tm(t: &Tm<'_>) -> String {
    let mut out = String::new();
    debug_tm_go(t, &mut out);
    out
}

fn debug_tm_go(t: &Tm<'_>, out: &mut String) {
    match t {
        Tm::Var(i) => out.push_str(&format!("Var(Ix({}))", i)),
        Tm::Lam(x, i, b) => {
            out.push_str(&format!(
                "Lam({}, {}, ",
                dbg_span_str(x),
                debug_icit(*i)
            ));
            debug_tm_go(b, out);
            out.push(')');
        }
        Tm::App(f, a, i) => {
            out.push_str("App(");
            debug_tm_go(f, out);
            out.push_str(", ");
            debug_tm_go(a, out);
            out.push_str(&format!(", {})", debug_icit(*i)));
        }
        Tm::AppPruning(h, pr) => {
            out.push_str("AppPruning(");
            debug_tm_go(h, out);
            out.push_str(", ");
            // Pruning = List<Option<Icit>>（头 = 最内层）
            out.push('[');
            let mut slots: Vec<Option<Icit>> = Vec::new();
            let mut cur = *pr;
            while let Some(b) = cur {
                slots.push(b.slot);
                cur = b.next;
            }
            for (k, s) in slots.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                match s {
                    Some(i) => out.push_str(&format!("Some({})", debug_icit(*i))),
                    None => out.push_str("None"),
                }
            }
            out.push_str("])");
        }
        Tm::U(l) => out.push_str(&format!("U({})", l)),
        Tm::Pi(x, i, a, b) => {
            out.push_str(&format!(
                "Pi({}, {}, ",
                dbg_span_str(x),
                debug_icit(*i)
            ));
            debug_tm_go(a, out);
            out.push_str(", ");
            debug_tm_go(b, out);
            out.push(')');
        }
        Tm::Let(x, a, t, u) => {
            out.push_str(&format!("Let({}, ", dbg_span_str(x)));
            debug_tm_go(a, out);
            out.push_str(", ");
            debug_tm_go(t, out);
            out.push_str(", ");
            debug_tm_go(u, out);
            out.push(')');
        }
        Tm::Meta(m) => out.push_str(&format!("Meta(MetaVar({}))", m)),
        Tm::LiteralType => out.push_str("LiteralType"),
        Tm::LiteralIntro(s) => out.push_str(&format!("LiteralIntro({})", dbg_span_str(s))),
        Tm::Prim => out.push_str("Prim"),
        Tm::Obj(h, name) => {
            out.push_str("Obj(");
            debug_tm_go(h, out);
            out.push_str(&format!(", {})", dbg_span_str(name)));
        }
        Tm::Sum(name, params, cases, ..) => {
            out.push_str(&format!("Sum({}, [", dbg_span_str(name)));
            for (k, p) in params.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!(
                    "({}, ",
                    dbg_span_str(p.name)
                ));
                debug_tm_go(p.val, out);
                out.push_str(", ");
                debug_tm_go(p.ty, out);
                out.push_str(&format!(", {})", debug_icit(p.icit)));
            }
            out.push_str("], [");
            for (k, c) in cases.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&dbg_span_str(c));
            }
            out.push_str("])");
        }
        Tm::SumCase { typ, case_name, datas, .. } => {
            out.push_str(&format!(
                "SumCase {{ typ: {}, case_name: {}, datas: [",
                {
                    let mut tmp = String::new();
                    debug_tm_go(typ, &mut tmp);
                    tmp
                },
                dbg_span_str(case_name)
            ));
            for (k, d) in datas.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!("({}, ", dbg_span_str(d.name)));
                debug_tm_go(d.val, out);
                out.push_str(&format!(", {})", debug_icit(d.icit)));
            }
            out.push_str("]) }");
        }
        Tm::Match(s, cases) => {
            out.push_str("Match(");
            debug_tm_go(s, out);
            out.push_str(", [");
            for (k, (p, b)) in cases.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                out.push('(');
                debug_pat_go(p, out);
                out.push_str(", ");
                debug_tm_go(b, out);
                out.push(')');
            }
            out.push_str("])");
        }
    }
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
                    if is_def {
                        // define 链的 env 槽顶 = 本 def 的登记值
                        last = Some(env_nth(&self.defs, cxt.env, 0));
                    }
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        solve_probe::dump();
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
