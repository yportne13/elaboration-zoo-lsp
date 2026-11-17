//! typeclass：L10 trait 求解的孪生辅助（TraitState + 打包值到 Typ 的转换）。
//!
//! 2026-11-17 重建：参考版求解算法（`crate::L10_typeclass::typeclass::Synth`）
//! 与孪生共用；本文件只放孪生的状态载体与 `V -> Typ` 适配。trait 身份按
//! 名字查 `TraitState.out_param`（不设 XCell::Sum 的 is_trait 标记）。

use rustc_hash::FxHashMap as HashMap;

use super::parser::syntax::{Icit, Raw};
use crate::L10_typeclass::typeclass::{Synth, Typ};
use super::syntax::{V, v_lvl_of, v_tag, v_u_of, v_xcell_of, XCell};

/// trait 定义 / 合成状态（参考版 `Infer` 三张表同构；每轮由 TraitDecl 重建）。
#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Prolog 式实例求解器。
    pub(super) solver: Synth,
    /// trait 名 → (参数表（含 Self）, out_param 掩码, 方法表)。
    pub(super) definition: HashMap<
        String,
        (
            Vec<(crate::parser_lib::Span<String>, Raw, Icit)>,
            Vec<bool>,
            Vec<(
                crate::parser_lib::Span<String>,
                Vec<(crate::parser_lib::Span<String>, Raw, Icit)>,
                Raw,
            )>,
        ),
    >,
    /// trait 名 → 参数 out_param 掩码。
    pub(super) out_param: HashMap<String, Vec<bool>>,
}

/// 参考 `Val::to_typ` 的快版：打包值 V → trait 求解器的 Typ。
pub(crate) fn val_to_typ(v: V) -> Option<Typ> {
    match v_tag(v) {
        5 => None, // Flex
        0 => Some(Typ::Var(v_lvl_of(v))),
        2 => None, // 中性链：非空 spine 的 Rigid/Flex/Obj 头
        3 => Some(Typ::Val(crate::parser_lib::Span {
            data: format!("Type {}", v_u_of(v)),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        })),
        7 => match v_xcell_of(v) {
            XCell::Sum { name, params, .. } => Some(if params.is_empty() {
                Typ::Val(crate::parser_lib::Span {
                    data: name.to_string(),
                    start_offset: 0,
                    end_offset: 0,
                    path_id: 0,
                })
            } else {
                // 刻意语义同参考版：不可作类型的实参（未解 meta）被剔除，
                // trait_wrap 接收者路径依赖该剔除。
                Typ::Construct(
                    crate::parser_lib::Span {
                        data: name.to_string(),
                        start_offset: 0,
                        end_offset: 0,
                        path_id: 0,
                    },
                    params.iter().filter_map(|p| val_to_typ(p.val)).collect(),
                )
            }),
            _ => None,
        },
        _ => None,
    }
}
