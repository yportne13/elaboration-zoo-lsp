//! typeclass：trait 求解与类型类设施（L10 特有）——`Machine::
//! solve_multi_trait_ref`/`solve_trait_ref`/`solve_trait_ref_inner`（参考版
//! `Infer::solve_multi_trait`/`solve_trait` 的快版镜像）、中性 global 视图
//! （`neutral_of`）、trait 状态（`TraitState`）与快版 `Val::to_typ`
//! （`val_to_typ`）。原 bump_spine_iter.rs 中 impl Machine 的三个 trait 求解
//! 方法（独立 `impl Machine` 块承载——本拆分唯一的非逐行结构差异）与
//! "Elaboration 上下文" 节尾的类型类块，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use std::collections::HashMap;

use super::parser::syntax::{Icit, Raw};

use crate::L10_typeclass::typeclass::{Assertion, Synth, Typ};

use super::force::force_deep;
use super::machine::{GLOBAL_BASE, solve_probe, Cxt, Machine};
use super::spine::{MetaEntry, Spine};
use super::syntax::{Tm, V, XCell, v_lvl, v_lvl_of, v_tag, v_u_of, v_xcell_of};

impl Machine {
    /// 参考 `Infer::solve_multi_trait`：对「下标 ≥ m」的所有未解 meta，
    /// 类型是 trait 的逐个跑实例合成（合成成功 → meta := 实例值）。
    ///
    /// A-2（评审第二轮）：旧实现每次对 metas 表做全后缀线性扫
    /// （`metas[m..]` 逐槽过一遍，Solved 槽也在内）——traitchain 一轮
    /// 3076 次调用、Σscan 2.1M、仅产出个位候选。现遍历
    /// [`Machine::unsolved`] worklist（= 当前仍 Unsolved 的下标集，严格
    /// 同步入出表），过滤 `idx ≥ m` 后按 idx 升序处理（与旧表序逐字同序，
    /// 求解顺序不变）。worklist 无序（swap_remove 摘除），排序只对
    /// prepare 快照做，量级 = 待合成候选数。
    pub(super) fn solve_multi_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        m: u32,
    ) -> Result<(), String> {
        let probe_t0 = solve_probe::on().then(std::time::Instant::now);
        let mut prepare: Vec<(u32, V)> = self
            .unsolved
            .iter()
            .filter(|&&i| i >= m)
            .filter_map(|&i| match &self.metas[i as usize] {
                MetaEntry::Unsolved(v) => Some((i, *v)),
                _ => None, // 表/worklist 严格同步下不可达（防御保留）
            })
            .collect();
        prepare.sort_unstable_by_key(|&(i, _)| i);
        if let Some(t0) = probe_t0 {
            solve_probe::C.smt_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            // 口径 v2（A-2）：scan 原为 metas 后缀长度，现 = worklist 长度
            // （本次调用实际遍历的未解条目数）
            let scan = self.unsolved.len() as u64;
            solve_probe::C.smt_scan.fetch_add(scan, std::sync::atomic::Ordering::Relaxed);
            solve_probe::C.smt_scan_max.fetch_max(scan, std::sync::atomic::Ordering::Relaxed);
            solve_probe::C.smt_prepare.fetch_add(prepare.len() as u64, std::sync::atomic::Ordering::Relaxed);
            // def 臂（m == 0）：顺带钉每 def 扫描时表中未解 / 未解 trait 形态数
            // （m == 0 时过滤恒真，prepare = 全部未解，与旧口径一致）
            if m == 0 {
                solve_probe::C.defs.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                for (_, v) in prepare.iter() {
                    if v_tag(*v) == 7
                        && matches!(v_xcell_of(*v), XCell::Sum { is_trait: true, .. })
                    {
                        solve_probe::C.def_scan_trait_unsolved.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                }
                solve_probe::C.def_scan_unsolved.fetch_add(prepare.len() as u64, std::sync::atomic::Ordering::Relaxed);
            }
        }
        for (idx, x) in prepare {
            let solved = self.solve_trait_ref(bump, cxt, x)?;
            if let Some((_, val)) = solved {
                self.metas[idx as usize] = MetaEntry::Solved(val, x);
                self.remove_unsolved(idx);
            }
        }
        if let Some(t0) = probe_t0 {
            solve_probe::C.smt_ns.fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        Ok(())
    }

    /// 参考 `Infer::solve_trait`：x 是 trait Sum → 查实例表合成；命中给
    /// (实例项, 实例值)，失败给 Err 文案，非 trait 给 None。
    pub(super) fn solve_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: V,
    ) -> Result<Option<(&'a Tm<'a>, V)>, String> {
        #[cfg(feature = "sampler")]
        crate::sampler::tick();
        let probe_t0 = if solve_probe::on() {
            solve_probe::C.str_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            solve_probe::self_t0(&solve_probe::B_STR)
        } else {
            None
        };
        let r = self.solve_trait_ref_inner(bump, cxt, x);
        solve_probe::phase_end(&solve_probe::B_STR, &solve_probe::C.str_ns, &solve_probe::C.str_self_ns, probe_t0);
        r
    }

    fn solve_trait_ref_inner<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: V,
    ) -> Result<Option<(&'a Tm<'a>, V)>, String> {
        // 精化 σ 包裹的期望类型先推开（子句体内引用被解槽时会出现；
        // 对齐旧 refresh 后槽值已展开的世界）
        let x = self.force_v(bump, x);
        let is_trait_sum = v_tag(x) == 7
            && match v_xcell_of(x) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if !is_trait_sum {
            return Ok(None);
        }
        solve_probe::on().then(|| {
            solve_probe::C.str_trait.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        });
        let (name, params) = match v_xcell_of(x) {
            XCell::Sum { name, params, .. } => (*name, *params),
            _ => unreachable!(),
        };
        let out_param = match self.tstate.out_param.get(name) {
            Some(o) => o.clone(),
            None => return Ok(None),
        };
        let args: Vec<Typ> = {
            let Machine {
                spine,
                defs,
                metas,
                globals,
                ..
            } = self;
            params
                .iter()
                .zip(out_param.iter())
                .filter(|(_, o)| !**o)
                .filter_map(|(p, _)| {
                    // 参考 solve_trait：实参先 force 再 to_typ（未解 meta
                    // 在求解钩子点应已被前一步 solve 落表）；槽位嵌套精化
                    // σ 一并推开（参考版 solve_trait 的 force + 槽位已物化）
                    let f = force_deep(bump, spine, defs, metas, globals, p.val);
                    val_to_typ(spine, defs, f)
                })
                .collect()
        };
        self.tstate.solver.clean();
        let probe_ts = solve_probe::on().then(std::time::Instant::now);
        let answer = self.tstate.solver.synth(Assertion {
            name: name.to_string(),
            arguments: args,
        });
        if let Some(ts) = probe_ts {
            solve_probe::C.str_synth_ns.fetch_add(ts.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        if solve_probe::on() {
            if answer.is_some() {
                solve_probe::C.str_ok.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            } else {
                solve_probe::C.str_fail.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }
        if let Some(a) = answer {
            // infer_expr(Var 实例名) + insert
            let raw = Raw::Var(crate::parser_lib::Span {
                data: a.data,
                start_offset: a.start_offset,
                end_offset: a.end_offset,
                path_id: a.path_id,
            });
            let probe_ti = solve_probe::on().then(std::time::Instant::now);
            let infered =
                self.infer_expr(bump, cxt, &raw).map_err(|e| e.0.data)?;
            let (tm, _) =
                self.insert(bump, cxt, infered.0, infered.1).map_err(|e| e.0.data)?;
            let val = self.eval(bump, cxt.env, tm);
            if let Some(ti) = probe_ti {
                solve_probe::C.str_infer_ns.fetch_add(ti.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            }
            let probe_tu = solve_probe::on().then(std::time::Instant::now);
            if v_tag(val) == 7 {
                if let XCell::SumCase { typ, .. } = v_xcell_of(val) {
                    let mut te = None;
                    let _ = self.unify(bump, cxt, cxt.lvl, *typ, x, &mut te);
                }
            }
            if let Some(tu) = probe_tu {
                solve_probe::C.str_unify_ns.fetch_add(tu.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            }
            Ok(Some((tm, val)))
        } else {
            let params: Vec<String> = {
                let Machine {
                    spine,
                    defs,
                    metas,
                    globals,
                    ..
                } = self;
                params
                    .iter()
                    .zip(self.tstate.out_param.get(name).map(|o| o.clone()).unwrap_or_default())
                    .filter(|(_, o)| !*o)
                    .filter_map(|(p, _)| {
                        let f = force_deep(bump, spine, defs, metas, globals, p.val);
                        val_to_typ(spine, defs, f)
                    })
                    .map(|t| format!("{:?}", t))
                    .collect()
            };
            Err(format!("solve trait failed: {:?}", params))
        }
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

/// trait 定义 / 合成状态（参考版 `Infer` 的 trait_solver / trait_definition /
/// trait_out_param 三表同构；Clone 供 temp-infer 快照换入换出）。
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Prolog 式实例求解器。
    pub(super) solver: Synth,
    /// trait 名 → (参数表（含 Self）, out_param 掩码, 方法表)。
    pub(super) definition:
        HashMap<String, (Vec<(crate::parser_lib::Span<String>, Raw, Icit)>, Vec<bool>, Vec<(crate::parser_lib::Span<String>, Vec<(crate::parser_lib::Span<String>, Raw, Icit)>, Raw)>)>,
    /// trait 名 → 参数 out_param 掩码。
    pub(super) out_param: HashMap<String, Vec<bool>>,
}

/// 参考 `Val::to_typ` 的快版（快版 Val → trait 求解器的 Typ）。
/// 字面量 / Prim 分支参考版是 `todo!()`——同款不可达即崩。
pub(crate) fn val_to_typ(spine: &Spine, defs: &[V], v: V) -> Option<Typ> {
    match v_tag(v) {
        5 => None, // Flex
        0 => {
            let _ = (spine, defs);
            Some(Typ::Var(v_lvl_of(v)))
        }
        2 => {
            // Rigid/Flex/Obj 头的链 → None（参考版 Rigid(_, _) 非空 spine → None）
            let _ = (spine, defs);
            None
        }
        3 => Some(Typ::Val(crate::parser_lib::Span {
            data: format!("Type {}", v_u_of(v)),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        })),
        7 => match v_xcell_of(v) {
            XCell::Sum {
                name,
                params,
                is_trait,
                ..
            } => {
                let _ = is_trait;
                Some(if params.is_empty() {
                    Typ::Val(crate::parser_lib::Span {
                        data: name.to_string(),
                        start_offset: 0,
                        end_offset: 0,
                        path_id: 0,
                    })
                } else {
                    let args: Vec<Typ> = params
                        .iter()
                        // **刻意语义**：不可作类型的参数槽（未解 meta）被
                        // filter_map 剔除——参考版 `Val::to_typ` 同款（见该处
                        // 注释：实例登记侧 None 即 Err、目标侧 arity 失配即
                        // no-instance、trait_wrap 接收者路径依赖该剔除），勿
                        // 改成整体 None。
                        .filter_map(|p| val_to_typ(spine, defs, p.val))
                        .collect();
                    Typ::Construct(
                        crate::parser_lib::Span {
                            data: name.to_string(),
                            start_offset: 0,
                            end_offset: 0,
                            path_id: 0,
                        },
                        args,
                    )
                })
            }
            _ => None,
        },
        _ => None,
    }
}
