//! typeclass：trait 求解设施（L11 继承 L10 的 typeclass 层）——`Machine::
//! solve_multi_trait_ref`/`solve_trait_ref`（参考版 `Infer::solve_multi_trait`/
//! `solve_trait` 的快版镜像）、trait 状态（`TraitState`）与快版 `Val::to_typ`
//! （`val_to_typ`）。原 bump_spine_iter.rs 中 impl Machine 的两个 trait 求解
//! 方法（独立 `impl Machine` 块承载——本拆分唯一的非逐行结构差异）与
//! "Elaboration 上下文" 节尾的类型类块，逐行搬运（2026-09-23 拆分）。

use std::collections::HashMap;

use bumpalo::Bump;

use super::parser::syntax::{Icit, Raw};

use crate::L11_macro::typeclass::{Assertion, Synth, Typ};

use super::force::{force, force_deep};
use super::machine::{Cxt, Machine};
use super::spine::{MetaEntry, Spine};
use super::syntax::{Tm, V, XCell, v_lvl_of, v_tag, v_u_of, v_xcell_of};

impl Machine {
    /// 参考 `Infer::solve_multi_trait`：从 meta m 起扫描所有未解 meta，
    /// 类型是 trait 的逐个跑实例合成（合成成功 → meta := 实例值）。
    pub(super) fn solve_multi_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        m: u32,
    ) -> Result<(), String> {
        let prepare: Vec<(u32, V)> = self
            .metas
            .get(m as usize..)
            .unwrap_or(&[])
            .iter()
            .enumerate()
            .flat_map(|(i, x)| match x {
                MetaEntry::Unsolved(v) => Some((i as u32, *v)),
                _ => None,
            })
            .collect();
        for (idx, x) in prepare {
            let solved = self.solve_trait_ref(bump, cxt, x)?;
            if let Some((_, val)) = solved {
                self.metas[(idx + m) as usize] = MetaEntry::Solved(val, x);
            }
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
        // 精化 σ 包裹的期望类型先推开（子句体内引用被解槽时会出现）
        let x = {
            let Machine {
                spine,
                defs,
                metas,
                mutable,
                ..
            } = self;
            force(bump, spine, defs, metas, &*cxt.decls, mutable, x)
        };
        let is_trait_sum = v_tag(x) == 7
            && match v_xcell_of(x) {
                XCell::Sum { is_trait, .. } => *is_trait,
                _ => false,
            };
        if !is_trait_sum {
            return Ok(None);
        }
        let (name, params) = match v_xcell_of(x) {
            XCell::Sum { name, params, .. } => (*name, *params),
            _ => unreachable!(),
        };
        let out_param = match self.tstate.out_param.get(name) {
            Some(o) => o.clone(),
            None => return Ok(None),
        };
        // 参考版 solve_trait（L11 unification.rs 471-482）：实参逐个
        // force 再 to_typ，**任一个 to_typ 失败（未解 meta 等）即提前
        // Ok(None)**——确定性短路，不是 filter 跳过（跳过会把缺参的
        // Assertion 送进 synth，误报 "solve trait failed"）。
        let args: Vec<Typ> = {
            let Machine {
                spine,
                defs,
                metas,
                mutable,
                ..
            } = self;
            let collected: Option<Vec<Typ>> = params
                .iter()
                .zip(out_param.iter())
                .filter(|(_, o)| !**o)
                .map(|(p, _)| {
                    let f = force_deep(bump, spine, defs, metas, &*cxt.decls, mutable, p.val);
                    val_to_typ(spine, defs, f)
                })
                .collect();
            match collected {
                Some(a) => a,
                None => return Ok(None),
            }
        };
        self.tstate.solver.clean();
        let answer = self.tstate.solver.synth(Assertion {
            name: name.to_string(),
            arguments: args.clone(),
        });
        if let Some(a) = answer {
            // infer_expr(Var 实例名) + insert
            let raw = Raw::Var(crate::parser_lib::Span {
                data: a.data,
                start_offset: a.start_offset,
                end_offset: a.end_offset,
                path_id: a.path_id,
            });
            let infered =
                self.infer_expr(bump, cxt, &raw).map_err(|e| e.0.data)?;
            let (tm, _) =
                self.insert(bump, cxt, infered.0, infered.1).map_err(|e| e.0.data)?;
            let val = self.eval(bump, cxt, cxt.env, tm);
            if v_tag(val) == 7 {
                if let XCell::SumCase { typ, .. } = v_xcell_of(val) {
                    let mut te = None;
                    let _ = self.unify(bump, cxt, cxt.lvl, *typ, x, &mut te);
                }
            }
            Ok(Some((tm, val)))
        } else {
            // 参考版文案：`{}[{:?}]` + 类实例表逐行（Debug 序列化）
            let args_dbg = format!("{:?}", args);
            Err(format!(
                "solve trait failed: {}[{}]
{}",
                name,
                args_dbg,
                self.tstate
                    .solver
                    .class_instances
                    .get(name)
                    .unwrap_or(&vec![])
                    .iter()
                    .map(|x| format!("{:?}", x))
                    .reduce(|a, b| a + "
" + &b)
                    .unwrap_or_default(),
            ))
        }
    }
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
