//! typeclass：trait 求解与类型类设施（L13 继承 typeclass 层）——
//! `Machine::solve_multi_trait_ref`/`solve_trait_ref`（参考版
//! `Infer::solve_multi_trait`/`solve_trait` 的快版镜像）与 `trait_wrap`/
//! `mk_no_object_err`（trait 方法包装），以独立 `impl Machine` 块承载
//! （L10 先例）；类型类状态（`TraitDefEntry`/`TraitState`）、实例匹配头键
//! （`head_key_v`）、缓存键（`val_cache_key_t`）与快版 Val 解码桥
//! （`v_to_ref_val`）。原 bump_spine_iter.rs 中 impl Machine 的 trait 求解
//! 方法与 "Elaboration 上下文" 节尾的类型类块，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::rc::Rc;

use super::parser::syntax::{Either, Icit, Raw};

use super::entry::{export, no_metas};
use super::env::env_ext;
use super::force::META_JOURNAL;
use super::machine::{state_journal_record, types_names_list, Cxt, Machine, StateUndo};
use super::spine::{
    is_flex, journal_meta, meta_journal_rollback, HK_DECL, MetaEntry, MetaSnap, Spine,
};
use super::syntax::{
    Tm, V, XCell, v_lvl, v_lvl_of, v_meta_of, v_pi_of, v_spine_of, v_tag, v_u_of, v_xcell_of,
};

use crate::L13_namespace::typeclass::GENERIC_SELF_HEAD;
use crate::L13_namespace::typeclass::{Instance, Synth};
use crate::parser_lib::ToSpan;

use super::{empty_span, Error};
use super::pretty::pretty_tm;
use crate::L13_namespace::Val as CVal;
use crate::list::List as CList;


/// 值的实例匹配头键（参考版 typeclass.rs `head_key` 的快版对应）：
/// Decl 头给名字、Sum 给类型名；其余（Rigid 等）None → 通配桶。
fn head_key_v(spine: &Spine, v: V) -> Option<SmolStr> {
    match v_tag(v) {
        7 => match v_xcell_of(v) {
            XCell::Decl { name } => Some(SmolStr::new(*name)),
            XCell::Sum { name, .. } => Some(SmolStr::new(*name)),
            _ => None,
        },
        2 => {
            let h = v_spine_of(v);
            // 链头能给出头键的只有 Decl（Sum 不可应用，进不了链）；顶端槽
            // 种类非 Decl 时 O(1) 落通配桶，免整趟走底
            if spine.stack[h].hk != HK_DECL {
                return None;
            }
            let hd = spine.spine_head(h);
            match v_xcell_of(hd) {
                XCell::Decl { name } => Some(SmolStr::new(*name)),
                _ => None,
            }
        }
        _ => None,
    }
}

impl Machine {
    /// 参考 `Infer::solve_multi_trait`（L13）：只扫 `trait_metas` 登记表
    /// （fresh_meta 对 trait Sum 走此表），清理指向截断 meta 的条目；从 m
    /// 起逐个跑实例合成（合成成功 → meta := 实例值）。
    pub(super) fn solve_multi_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        m: u32,
        allow_flex_defaulting: bool,
    ) -> Result<(), String> {
        self.trait_metas
            .retain(|mv| (*mv as usize) < self.metas.len());
        for mv in self.trait_metas.clone() {
            if mv < m {
                continue;
            }
            let idx = mv as usize;
            if idx >= self.metas.len() {
                continue;
            }
            let (x, snap): (V, Rc<MetaSnap<'static>>) = match &self.metas[idx] {
                MetaEntry::Unsolved(v, s, ..) => (*v, s.clone()),
                _ => continue,
            };
            // 用 **meta 创建处**的上下文求解（参考版 `meta_cxt`）：goal 里的
            // Rigid 层级按创建处 de Bruijn 编号，用调用方的浅上下文会让
            // rename/quote 算出越界变量。
            //
            // `snap` 是**保命强引用**：`solve_trait_ref` 的候选实例走嵌套
            // unify 时可能把 `self.metas[idx]` 换成 `Solved`，丢掉该快照最后
            // 一个 `Rc` —— 不留住，下面的 solve 就会读已释放快照的 `cxt`
            // （释放块填充 `0xFEEEFEEE`，读 `cxt.decls` 即
            // `HashMap::get` 解引用野指针 → STATUS_ACCESS_VIOLATION）。参考版
            // 同点位是 `arc_cxt.as_ref().clone()` 先克隆 `Arc` 再调 `&mut self`。
            let meta_cxt: &Cxt<'a> =
                unsafe { &*(&snap.cxt as *const Cxt<'static> as *const Cxt<'a>) };
            let typ = self
                .solve_trait_ref(bump, meta_cxt, x, allow_flex_defaulting)
                .map_err(|e| e)?;
            if let Some((_, val)) = typ {
                journal_meta(&mut self.metas, idx, MetaEntry::Solved(val, x));
            }
        }
        Ok(())
    }

    /// 参考 `Infer::solve_trait`（L13 unification.rs:600 逐句）：trait Sum →
    /// flex defaulting（多个非 out 参数仅 1 个已知时把其余 unify 到它）→
    /// Phase 1 轻量过滤实例（head_index 桶 + val_match；非 out 参数 Flex /
    /// 多候选且 out 参数 Flex → 推迟 `Ok(None)`）→ Phase 2 逐候选
    /// infer+insert+eval（SumCase 时 unify 把关 + **重 eval**——闭包捕获已解
    /// meta），失败截断 metas 换下一个；全败给含实例表的 Err 文案。
    pub(super) fn solve_trait_ref<'a>(
        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        x: V,
        allow_flex_defaulting: bool,
    ) -> Result<Option<(&'a Tm<'a>, V)>, String> {
        super::prof_count(&super::FUNC_PROF.solve_trait.1);
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
        // 非 out 参数下标（flex defaulting 与多次收集共用）
        let non_out_idx: Vec<usize> = params
            .iter()
            .zip(out_param.iter())
            .enumerate()
            .filter(|(_, (_, o))| !**o)
            .map(|(i, _)| i)
            .collect();
        // flex defaulting：多个非 out 参数仅 1 个已知 → 把其余 unify 到它
        let mut non_out_params: Vec<V> = {
            let pv: Vec<V> = non_out_idx.iter().map(|&i| params[i].val).collect();
            self.force_list(bump, &cxt.decls, &pv)
        };
        if allow_flex_defaulting
            && non_out_params.iter().any(|v| is_flex(&self.spine, *v))
        {
            let known: Vec<V> = non_out_params
                .iter()
                .copied()
                .filter(|v| !is_flex(&self.spine, *v))
                .collect();
            if known.len() == 1 && non_out_params.len() > 1 {
                let known_type = known[0];
                let mut ok = true;
                for v in non_out_params.iter() {
                    if is_flex(&self.spine, *v) {
                        let mut terr = None;
                        if !self.unify(bump, cxt, cxt.lvl, *v, known_type, 100, &mut terr) {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    let pv: Vec<V> = non_out_idx.iter().map(|&i| params[i].val).collect();
                    non_out_params = self.force_list(bump, &cxt.decls, &pv);
                    if non_out_params.iter().any(|v| is_flex(&self.spine, *v)) {
                        return Ok(None);
                    }
                } else {
                    return Ok(None);
                }
            } else {
                return Ok(None);
            }
        }
        // 全参数（含 outParam）force，供实例匹配
        let all_params: Vec<V> =
            self.force_list(bump, &cxt.decls, &params.iter().map(|p| p.val).collect::<Vec<_>>());
        // goal 参数解码一次（原实现对每个实例重复 v_to_ref_val 同一批
        // g_arg——纯解码分配 ×C，多实例桶下占该相位大头）。
        let g_refs: Vec<_> = all_params
            .iter()
            .map(|g| v_to_ref_val(&self.spine, &self.defs, *g))
            .collect();
        let name_key = SmolStr::new(name);
        // —— Phase 1：轻量过滤（head_index 桶优先 + val_match 确认）——
        let matching_lvls: Vec<crate::parser_lib::Span<SmolStr>> = {
            let instances = match self.tstate.solver.class_instances.get(&name_key) {
                Some(insts) => insts,
                None => return Ok(None),
            };
            let filter = |inst: &Instance| -> Option<crate::parser_lib::Span<SmolStr>> {
                if inst.assertion.name != name {
                    return None;
                }
                if inst.assertion.arguments.len() != all_params.len() {
                    return None;
                }
                let mut subst = std::collections::HashMap::new();
                let mut ok = true;
                for (i, (g_ref, i_arg)) in
                    g_refs.iter().zip(inst.assertion.arguments.iter()).enumerate()
                {
                    let is_out = out_param.get(i).copied().unwrap_or(false);
                    if is_out && is_flex(&self.spine, all_params[i]) {
                        continue;
                    }
                    if !Synth::val_match(g_ref.as_ref(), i_arg, &mut subst) {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    Some(inst.lvl.clone())
                } else {
                    None
                }
            };
            // 首个非 out 参数的已知头 → 具体桶 + 通配桶；否则全扫
            let self_head: Option<SmolStr> = (|| {
                for (i, arg) in all_params.iter().enumerate() {
                    if !out_param.get(i).copied().unwrap_or(false) {
                        return head_key_v(&self.spine, *arg);
                    }
                }
                None
            })();
            match self_head {
                Some(head) => {
                    let mut idxs: Vec<usize> = Vec::new();
                    if let Some(indices) = self
                        .tstate
                        .solver
                        .head_index
                        .get(&(SmolStr::new(name), head.clone()))
                    {
                        idxs.extend(indices.iter().copied());
                    }
                    if let Some(indices) = self.tstate.solver.head_index.get(&(
                        SmolStr::new(name),
                        SmolStr::new(super::typeclass::GENERIC_SELF_HEAD),
                    )) {
                        idxs.extend(indices.iter().copied());
                    }
                    if idxs.is_empty() {
                        // 桶空早退（评审机会 4）：head_index 由
                        // `impl_trait_for` 对每个带非 out 参数的实例**无条件**
                        // 维护（trait 注册时 `set_trait_out_params` 先行，
                        // ImplDecl 臂 `tstate.out_param` 缺失即 Err，故索引
                        // 覆盖完备；无具体头的实例——Rigid/Flex/Nat 等——
                        // `head_key` 给 None 一律入通配桶）。两桶皆空 ⇒
                        // 具体头实例按头键必不匹配、可变通实例不在通配桶 ⇒
                        // 全实例 `filter` 必空（每实例的 `v_to_ref_val` Rc
                        // 分配与逐参数 val_match 全部可免）。
                        Vec::new()
                    } else {
                        idxs.iter().filter_map(|&i| filter(&instances[i])).collect()
                    }
                }
                None => instances.iter().filter_map(filter).collect(),
            }
        };
        let candidate_count = matching_lvls.len();
        if candidate_count == 0 {
            return Ok(None); // 无实例：交给后续（solve_multi_trait / 报错路径）
        }
        // 非 out 参数仍 Flex → 推迟（val_match(Flex, _) 恒真会选错实例）。
        // 注意 `is_flex` 同时覆盖裸 meta 与 meta 头链（`?m x`）——goal 的
        // 参数形态常是后者；只测 `v_tag == 5` 会漏判，让 flex goal 进入
        // 实例匹配（val_match 对每个实例恒真）后按登记序选中错误实例。
        // Phase 1（上面）是纯过滤（val_match / is_flex / head_key_v 全只
        // 读），两次 force 之间无任何状态变更——`all_params` 即
        // `forced_params`，旧实现第二遍 force_list 是纯重复（2026-09-22 移除）。
        let forced_params: &Vec<V> = &all_params;
        let has_flex_non_out = non_out_idx
            .iter()
            .any(|&i| is_flex(&self.spine, forced_params[i]));
        if has_flex_non_out {
            return Ok(None);
        }
        // 多候选且 out 参数 Flex → 推迟（等上下文约束 out 参数）
        let out_idx: Vec<usize> = params
            .iter()
            .zip(out_param.iter())
            .enumerate()
            .filter(|(_, (_, o))| **o)
            .map(|(i, _)| i)
            .collect();
        let has_flex_out = out_idx
            .iter()
            .any(|&i| is_flex(&self.spine, forced_params[i]));
        if has_flex_out && candidate_count > 1 {
            return Ok(None);
        }
        // —— Phase 2：逐候选 elaborate ——
        let mut last_err = String::new();
        for lvl in &matching_lvls {
            let meta_before = self.metas.len();
            let result = (|| -> Result<(&'a Tm<'a>, V), String> {
                let raw = Raw::Var(lvl.clone());
                let infered = self.infer_expr(bump, cxt, &raw).map_err(|e| e.0.data)?;
                let (tm, _) = self
                    .insert(bump, cxt, infered.0, infered.1)
                    .map_err(|e| e.0.data)?;
                let mut val = self.eval(bump, cxt, cxt.env, tm);
                if v_tag(val) == 7 {
                    if let XCell::SumCase { typ, .. } = v_xcell_of(val) {
                        self.unify_catch(bump, cxt, *typ, x, empty_span(())).map_err(|e| e.0.data)?;
                        // 重 eval：首次 eval 在实例隐参（fresh meta）求解前
                        // 跑，闭包捕获冻结的未解 meta 环境——宽度参数会永远
                        // 悬空（typeclass instance Nat param bug）。以已解
                        // meta 重求使闭包捕获合一后的值。
                        val = self.eval(bump, cxt, cxt.env, tm);
                    }
                }
                Ok((tm, val))
            })();
            match result {
                Ok((tm, val)) => return Ok(Some((tm, val))),
                Err(e) => {
                    self.metas.truncate(meta_before);
                    last_err = e;
                }
            }
        }
        // 全部候选失败
        let params_dbg = all_params
            .iter()
            .map(|v| {
                let r = v_to_ref_val(&self.spine, &self.defs, *v);
                format!("{:?}", r)
            })
            .collect::<Vec<_>>()
            .join(", ");
        Err(format!(
            "solve trait failed: {}[{}]\n  last error: {}\n  instances:\n{}",
            name,
            params_dbg,
            last_err,
            matching_lvls
                .iter()
                .map(|x| format!("{:?}", x.data))
                .reduce(|a, b| a + "\n" + &b)
                .unwrap_or_default(),
        ))
    }
}

impl Machine {
    // L10：trait 方法包装（参考版 elaboration.rs `trait_wrap` 逐句移植）
    // --------------------------------------------------------------------------------

    /// 字段未命中时在 trait 表里找同名方法：能合成出实例 → 生成
    /// `let $method = λ...; $method x` 的包装项；否则报 "has no object"。
    pub(super) fn trait_wrap<'a>(
    // cnt 在函数体首行（trait_wrap 是多行签名，函数体首语句在下方标注）

        &mut self,
        bump: &'a Bump,
        cxt: &Cxt<'a>,
        t: crate::parser_lib::Span<SmolStr>,
        a: V,
        x: &Raw,
        tm: &'a Tm<'a>,
    ) -> Result<(&'a Tm<'a>, V), Error> {
        let t_span = t.to_span();
        // typ_raw = eval(quote(a))（参考版同款二次正规化）
        let typ_raw = {
            let q = self.quote(bump, cxt, cxt.lvl, a);
            self.eval(bump, cxt, cxt.env, q)
        };
        let typ_raw_head = head_key_v(&self.spine, typ_raw);
        let typ_raw_ref = v_to_ref_val(&self.spine, &self.defs, typ_raw);

        // —— namespace 条目查表（参考版 2742-2846）——
        // 匹配方法名的条目逐个探测（metas/trait_metas 快照回滚——探测可能
        // 解出引用临时 meta 的解，truncate 会留悬空）。
        let mut ns_result: Vec<(V, SmolStr)> = Vec::new();
        {
            let mut cur = cxt.namespace;
            while let Some(ns) = cur {
                if ns.methods.iter().any(|m| *m == t.data) {
                    // 预过滤 1：条目 trait 对该 Self 无实例 → 跳过
                    let mut skip = false;
                    if let Some(head) = &typ_raw_head {
                        if v_tag(ns.val) == 4 {
                            let p = v_pi_of(ns.val);
                            if p.icit == Icit::Impl {
                                let dom_f = self.force_v(bump, cxt, p.dom);
                                if v_tag(dom_f) == 7 {
                                    if let XCell::Sum { name: tn, is_trait: true, .. } =
                                        v_xcell_of(dom_f)
                                    {
                                        if !self
                                            .tstate
                                            .solver
                                            .can_satisfy(&SmolStr::new(tn), &typ_raw_ref)
                                        {
                                            skip = true;
                                        }
                                    }
                                }
                            }
                        }
                        let _ = head;
                    }
                    if !skip {
                        // 预过滤 2：条目首个显式参数（接收者）类型头须与接收者
                        // 类型头一致（Flex/generic 头放行）。隐式 Π 用
                        // Rigid(u32::MAX) 闭——不造 meta（参考版同款）。
                        if let Some(head) = &typ_raw_head {
                            let mut self_ty = ns.val;
                            let mut guard = 0;
                            while v_tag(self_ty) == 4 && v_pi_of(self_ty).icit == Icit::Impl {
                                let p = v_pi_of(self_ty);
                                self_ty = {
                                    let env = env_ext(bump, p.env, v_lvl(u32::MAX));
                                    self.eval(bump, cxt, env, p.body)
                                };
                                guard += 1;
                                if guard > 64 {
                                    break;
                                }
                            }
                            if v_tag(self_ty) == 4 && v_pi_of(self_ty).icit == Icit::Expl {
                                let dom_f = self.force_v(bump, cxt, v_pi_of(self_ty).dom);
                                if let Some(param_head) = head_key_v(&self.spine, dom_f) {
                                    if param_head != *head {
                                        skip = true;
                                    }
                                }
                            }
                        }
                    }
                    if !skip {
                        // 探测回滚（perf-debt 评审轮）：旧实现整表 clone
                        // metas（万条级 × 每方法分派一次 = prelude-hdl 慢
                        // decl 主因）。现 journal 就地写 + 截断 append：
                        // trait_metas 探测期只 push，truncate 即可。
                        let pre_meta_len = self.metas.len();
                        let pre_tm_len = self.trait_metas.len();
                        META_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
                        // 探测：剥隐式 Π（fresh meta 实参化）后与接收者类型合一
                        let mut check_typ = ns.val;
                        let mut guard = 0;
                        while v_tag(check_typ) == 4 && v_pi_of(check_typ).icit == Icit::Impl {
                            let p = v_pi_of(check_typ);
                            let mv = {
                                let m = self.fresh_meta(bump, cxt, p.dom);
                                self.eval_fresh(bump, cxt, cxt.env, m)
                            };
                            check_typ = {
                                let env = env_ext(bump, p.env, mv);
                                self.eval(bump, cxt, env, p.body)
                            };
                            guard += 1;
                            if guard > 64 {
                                break;
                            }
                        }
                        let probe_ok =
                            self.unify_catch(bump, cxt, check_typ, typ_raw, empty_span(())).is_ok();
                        meta_journal_rollback(&mut self.metas, pre_meta_len);
                        self.trait_metas.truncate(pre_tm_len);
                        if probe_ok {
                            ns_result.push((ns.val, SmolStr::new(ns.type_name)));
                        }
                    }
                }
                cur = ns.next;
            }
        }
        if ns_result.len() > 1 {
            let names: Vec<SmolStr> = ns_result
                .iter()
                .filter_map(|(v, _)| {
                    if v_tag(*v) == 4 {
                        let p = v_pi_of(*v);
                        if p.icit == Icit::Impl {
                            let dom_f = self.force_v(bump, cxt, p.dom);
                            if v_tag(dom_f) == 7 {
                                if let XCell::Sum { name: tn, is_trait: true, .. } =
                                    v_xcell_of(dom_f)
                                {
                                    return Some(SmolStr::new(tn));
                                }
                            }
                        }
                    }
                    None
                })
                .collect();
            return Err(Error(
                t.clone().map(|m| format!(
                    "ambiguous method `{}`: found in traits {}",
                    m,
                    names.iter().map(|n| format!("`{}`", n)).collect::<Vec<_>>().join(", "),
                )),
                vec![],
            ));
        }
        if let Some((_, type_name)) = ns_result.into_iter().next() {
            // 命中：`TypeHead.method` 限定键分派（与 inherent impl 注册的键
            // 一致；裸名 fallback 排除 namespace 方法键，模式 `mux` 仍只解
            // 构造子）
            let qname = SmolStr::new(format!("{}.{}", type_name, t.data));
            let qname2 = qname.clone();
            let call = Raw::App(
                Box::new(Raw::Var(t_span.map(move |_| qname2.clone()))),
                Box::new(x.clone()),
                Either::Icit(Icit::Expl),
            );
            match self.infer_expr(bump, cxt, &call) {
                Ok(r) => {
                    // 观察面（ref 2817）：ns 方法命中 → 方法名 token hover。
                    // 参考版 def_span 取 ns 条目登记 span；此处从 decl 表取
                    // 限定键登记项的 span（同一登记来源）。
                    let ds = cxt
                        .decls
                        .get(qname.as_str())
                        .map(|e| e.span)
                        .unwrap_or(t_span);
                    self.push_hover(bump, cxt, t_span, ds, r.1);
                    return Ok(r);
                }
                // 参考版此处是 `?`——失败直接传播，不收 completion（补全只在
                // trait 定义查表未命中的 else 支）。
                Err(e) => return Err(e),
            }
        }

        // —— trait 定义查表（参考版 2847-2988）——
        let mut traits: Vec<(
            SmolStr,
            Raw,
            crate::parser_lib::Span<SmolStr>, // trait 方法声明名 span（hover def）
            usize, // argc（显式参数数——同名算符消歧）
        )> = self
            .tstate
            .definition
            .iter()
            .flat_map(|(trait_name, (trait_params, _out, _st, methods))| {
                methods
                    .iter()
                    .find(|m| m.0.data == t.data)
                    .map(|m| (trait_name.clone(), trait_params.clone(), m))
            })
            .filter(|(tn, _, _)| {
                self.tstate.solver.clean();
                self.tstate.solver.can_satisfy(tn, &typ_raw_ref)
            })
            .map(|(trait_name, trait_params, (methods_name, methods_params, ret_type, _default))| {
                let argc = methods_params.iter().filter(|p| p.2 == Icit::Expl).count();
                let call_span = t.clone();
                // **$$ 先于 $this**：insert_go 先填 Self 与 trait 实例再到位
                // $this（Self 仍 Flex 时 solve_trait 推迟 $$，$this 合一后
                // solve_multi_trait 再解——参考版注释）
                let mut params = trait_params.clone();
                params.push((
                    call_span.clone().map(|_| SmolStr::new("$$")),
                    trait_params
                        .iter()
                        .map(|x| x.0.clone())
                        .fold(
                            Raw::Var(call_span.clone().map(|_| trait_name.clone())),
                            |ret, x| {
                                Raw::App(
                                    Box::new(ret),
                                    Box::new(Raw::Var(x)),
                                    Either::Icit(Icit::Impl),
                                )
                            },
                        ),
                    Icit::Impl,
                ));
                params.push((
                    call_span.clone().map(|_| SmolStr::new("$this")),
                    Raw::Var(call_span.clone().map(|_| SmolStr::new("Self"))),
                    Icit::Expl,
                ));
                params.extend(methods_params.iter().cloned());
                let body = std::iter::once((
                    Raw::Var(call_span.clone().map(|_| SmolStr::new("$this"))),
                    Icit::Expl,
                ))
                .chain(methods_params.iter().map(|x| (Raw::Var(x.0.clone()), x.2)))
                .fold(
                    Raw::Obj(
                        Box::new(Raw::Var(call_span.clone().map(|_| SmolStr::new("$$")))),
                        Some(call_span.clone()),
                    ),
                    |ret, (x, icit)| {
                        Raw::App(Box::new(ret), Box::new(x), Either::Icit(icit))
                    },
                );
                let decl = Raw::Let(
                    call_span.clone().map(|x| SmolStr::new(format!("${x}"))),
                    Box::new(params.iter().rev().fold(ret_type.clone(), |a, b| {
                        Raw::Pi(b.0.clone(), b.2, Box::new(b.1.clone()), Box::new(a))
                    })),
                    Box::new(params.iter().rev().fold(body, |a, b| {
                        Raw::Lam(b.0.clone(), Either::Icit(b.2), Box::new(a))
                    })),
                    Box::new(Raw::App(
                        Box::new(Raw::Var(
                            call_span.clone().map(|x| SmolStr::new(format!("${x}"))),
                        )),
                        Box::new(x.clone()),
                        Either::Icit(Icit::Expl),
                    )),
                );
                (trait_name, decl, methods_name.clone(), argc)
            })
            .collect();
        if traits.len() > 1 {
            // 同名算符按显参个数消歧（中缀 `a - b` 恒有 ≥1 实参——Neg.- 0 参
            // vs Sub.- 1 参）；仍歧义才报错
            let nonzero: Vec<(SmolStr, Raw, crate::parser_lib::Span<SmolStr>, usize)> =
                traits.iter().filter(|(_, _, _, argc)| *argc > 0).cloned().collect();
            if nonzero.len() == 1 && nonzero.len() < traits.len() {
                traits = nonzero;
            } else {
                let trait_names: Vec<&SmolStr> = traits.iter().map(|(n, _, _, _)| n).collect();
                return Err(Error(
                    t.clone().map(|m| format!(
                        "ambiguous method `{}`: found in traits {}",
                        m,
                        trait_names
                            .iter()
                            .map(|n| format!("`{}`", n))
                            .collect::<Vec<_>>()
                            .join(", "),
                    )),
                    vec![],
                ));
            }
        }
        if let Some((_, decl, def_span, _)) = traits.first() {
            // trait 方法 elaboration 缓存：同算符在结构相等的接收者类型上
            // 再次 elaborate 时，经 Raw::Tm 注解复用已查 Π 链与方法体 λ
            //（跳过 check_universe 与体重查）。缓存仅在**全无 meta** 时写入
            //（引用 per-call meta 的项在后续调用里下标过期）。
            let cache_key =
                val_cache_key_t(&self.spine, a, 0).map(|k| (t.data.clone(), k));
            let result = match &cache_key {
                Some(key) => match self.trait_method_cache.get(key) {
                    Some((rc_a, rc_va, rc_t)) => {
                        // 登记指针导入表后走 Raw::Tm 注解复用
                        let new_decl = if let Raw::Let(n, _, _, u) = decl {
                            Raw::Let(
                                n.clone(),
                                Box::new(Raw::Tm(rc_a.clone(), rc_va.clone())),
                                Box::new(Raw::Tm(rc_t.clone(), rc_va.clone())),
                                u.clone(),
                            )
                        } else {
                            decl.clone()
                        };
                        self.infer_expr(bump, cxt, &new_decl)?
                    }
                    None => {
                        let result = self.infer_expr(bump, cxt, decl)?;
                        if let Tm::Let(_, a_checked, t_checked, _) = result.0 {
                            let clean = no_metas(bump, self, cxt, a_checked).is_none()
                                && no_metas(bump, self, cxt, t_checked).is_none();
                            if clean {
                                let va = self.eval(bump, cxt, cxt.env, a_checked);
                                let rc_a = export(&self.symbol_table, a_checked);
                                let rc_t = export(&self.symbol_table, t_checked);
                                let rc_va = v_to_ref_val(&self.spine, &self.defs, va);
                                // 登记指针导入表（kick 撤销帧同步记账，评审 B#2 二期）
                                let ka = Rc::as_ptr(&rc_a) as usize;
                                let old_a = self.tm_import.insert(
                                    ka,
                                    unsafe {
                                        std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(
                                            a_checked,
                                        )
                                    },
                                );
                                state_journal_record(StateUndo::TmImport(ka, old_a));
                                let kt = Rc::as_ptr(&rc_t) as usize;
                                let old_t = self.tm_import.insert(
                                    kt,
                                    unsafe {
                                        std::mem::transmute::<&Tm<'a>, &'static Tm<'static>>(
                                            t_checked,
                                        )
                                    },
                                );
                                state_journal_record(StateUndo::TmImport(kt, old_t));
                                let kv = Rc::as_ptr(&rc_va) as usize;
                                let old_v = self.val_import.insert(kv, va);
                                state_journal_record(StateUndo::ValImport(kv, old_v));
                                let old_c = self.trait_method_cache
                                    .insert(key.clone(), (rc_a, rc_va, rc_t));
                                state_journal_record(StateUndo::TraitMethodCache(key.clone(), old_c));
                            }
                        }
                        result
                    }
                },
                None => self.infer_expr(bump, cxt, decl)?,
            };
            // 观察面（ref 2955）：trait 方法调用解析成功 → 方法名 token 的
            // hover，def = trait 方法声明名 span，值 = 实例化后的调用类型。
            self.push_hover(bump, cxt, t_span, def_span.to_span(), result.1);
            Ok(result)
        } else {
            // 观察面（ref 2964-2970）：方法未解析 = 补全现场，键 = 接收者
            // span；收集可满足 trait 的方法名（失败路径才收集，同参考版）。
            if self.observe {
                let rcv = x.to_span();
                let mut tn: Vec<SmolStr> = Vec::new();
                for (tname, (_p, _o, _st, ms)) in self.tstate.definition.iter() {
                    self.tstate.solver.clean();
                    if self.tstate.solver.can_satisfy(tname, &typ_raw_ref) {
                        for m in ms.iter() {
                            tn.push(m.0.data.clone());
                        }
                    }
                }
                for name in tn {
                    self.completion_table.push((rcv, name));
                }
            }
            // 未解析：no object 错误（LSP 补全收集不移植）
            Err(self.mk_no_object_err(bump, cxt, &t, a, tm))
        }
    }


    fn mk_no_object_err(
        &mut self,
        bump: &Bump,
        cxt: &Cxt<'_>,
        t: &crate::parser_lib::Span<SmolStr>,
        a: V,
        tm: &Tm<'_>,
    ) -> Error {
        if std::env::var("L11_LOOPCAP").is_ok() {
            eprintln!("TRACE no_object field={}", t.data);
        }
        // 参考版：`self.nf(&cxt.decl, &cxt.env, &self.quote(&cxt.decl,
        // cxt.lvl, &a))`——quote 后再 eval 再 quote（nf = quote(eval)）
        let q1 = self.quote(bump, cxt, cxt.lvl, a);
        let v = self.eval(bump, cxt, cxt.env, q1);
        let q2 = self.quote(bump, cxt, cxt.lvl, v);
        let names = types_names_list(cxt.types);
        Error(t.clone().map(|t| {
            format!(
                "`{}`: {} has no object `{}`",
                pretty_tm(0, names.clone(), &export(&self.symbol_table, tm)),
                pretty_tm(0, names.clone(), &export(&self.symbol_table, q2)),
                t,
            )
        }), vec![])
    }
}

/// trait 定义 / 合成状态（参考版 `Infer` 的 trait_solver / trait_definition /
/// trait_out_param 三表同构；Clone 供 temp-infer 快照换入换出）。L13：
/// definition 多 supertraits 与方法默认体两元（参考版同构）。
/// `TraitDefEntry` = definition 的值型（撤销日志 [`StateUndo`] 引用）。
pub(super) type TraitDefEntry = (
    Vec<(crate::parser_lib::Span<SmolStr>, Raw, Icit)>,
    Vec<bool>,
    Vec<crate::parser_lib::Span<SmolStr>>,
    Vec<(
        crate::parser_lib::Span<SmolStr>,
        Vec<(crate::parser_lib::Span<SmolStr>, Raw, Icit)>,
        Raw,
        Option<Raw>,
    )>,
);

#[derive(Clone, Default)]
pub(crate) struct TraitState {
    /// Prolog 式实例求解器。
    pub(super) solver: Synth,
    /// trait 名 → (参数表（含 Self）, out_param 掩码, supertrait 链, 方法表)。
    /// 方法表条目：(名字, 参数表, 返回类型, 默认体)。
    pub(super) definition: HashMap<SmolStr, TraitDefEntry>,
    /// trait 名 → 参数 out_param 掩码。
    pub(super) out_param: HashMap<SmolStr, Vec<bool>>,
    /// (trait, 关联类型名) → 默认类型（参考版 `Infer.assoc_defaults`）。
    pub(super) assoc_defaults: HashMap<(SmolStr, SmolStr), Option<Raw>>,
}

/// 类型值的确定性结构键（参考版 `val_cache_key` 的快版对应）——trait 方法
/// Π 链缓存的键。不可缓存（per-call meta / 开放类型 / 超深结构）→ None。
fn val_cache_key_t(spine: &Spine, v: V, depth: u32) -> Option<SmolStr> {
    if depth > 64 {
        return None;
    }
    match v_tag(v) {
        3 => Some(SmolStr::new(format!("u{}", v_u_of(v)))),
        6 => Some(SmolStr::new("lt")),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Some(SmolStr::new(format!("l:{}", s))),
            XCell::Nat(k) => Some(SmolStr::new(format!("n{}", k))),
            XCell::Sum { name, params, .. } => {
                let mut s = String::from(*name);
                s.push('(');
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        s.push(',');
                    }
                    s.push_str(&val_cache_key_t(spine, p.val, depth + 1)?);
                }
                s.push(')');
                Some(SmolStr::new(s))
            }
            XCell::SumCase { index, datas, .. } => {
                let mut s = format!("sc{}({}", index, datas.len());
                for d in datas.iter() {
                    s.push(',');
                    s.push_str(&val_cache_key_t(spine, d.val, depth + 1)?);
                }
                s.push(')');
                Some(SmolStr::new(s))
            }
            _ => None,
        },
        _ => None,
    }
}

/// 快版 V → 参考版 `Rc<Val>` 的解码（trait 求解器是 Val 级匹配——L12
/// typeclass.rs 移除 Typ 桥接；解码只用于 solving 边界，非热路径）。
/// 支持：Rigid（裸）/U/LiteralType/LiteralIntro/Sum/SumCase/Flex（未解
/// meta 立即数）；其余形态 unreachable（参考版 solve_trait 的实参是
/// 已 force 的类型实参，实际只会出现这些形态）。
pub(crate) fn v_to_ref_val(spine: &Spine, defs: &[V], v: V) -> Rc<CVal> {
    fn nspan(x: &str) -> crate::parser_lib::Span<SmolStr> {
        crate::parser_lib::Span {
            data: SmolStr::new(x),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        }
    }
    fn unmatchable() -> Rc<CVal> {
        Rc::new(CVal::LiteralIntro(crate::parser_lib::Span {
            data: "$unmatchable$".to_string(),
            start_offset: 0,
            end_offset: 0,
            path_id: 0,
        }))
    }
    match v_tag(v) {
        0 => Rc::new(CVal::Rigid(super::Lvl(v_lvl_of(v)), CList::new())),
        2 => {
            // 链：头解码 + 实参逐个挂上（参考版 spine 是 List（最新在前）；
            // collect_args 产出的正是最新在前序，逐个 prepend 即还原同序）。
            // **必须保留真实头**：先前把每步 acc 整体换成
            // `Flex(MetaVar(u32::MAX), [该实参])`，既丢了头（`?A x` 变成
            // 通配 `?_ x`，val_match 对任何实例恒真）又丢了更早的实参——
            // trait 求解 Phase 1 的候选集被污染成全部实例，再按登记序选中
            // 错误实例（core prelude `a + 0` 命中 Add[String,String] for
            // String，报 `can't unify expected: String find: Nat`）。
            let h = v_spine_of(v);
            let hd = spine.spine_head(h);
            let mut acc = match v_tag(hd) {
                5 => Rc::new(CVal::Flex(super::MetaVar(v_meta_of(hd)), CList::new())),
                0 => Rc::new(CVal::Rigid(super::Lvl(v_lvl_of(hd)), CList::new())),
                7 => match v_xcell_of(hd) {
                    XCell::Decl { name } => Rc::new(CVal::Decl(nspan(name), CList::new())),
                    XCell::Obj { val, name } => Rc::new(CVal::Obj(
                        v_to_ref_val(spine, defs, *val),
                        nspan(name),
                        CList::new(),
                    )),
                    _ => return unmatchable(),
                },
                _ => return unmatchable(),
            };
            let mut args: Vec<(V, Icit)> = Vec::new();
            spine.collect_args(h, &mut args); // 最新在前
            for (a, i) in args.iter() {
                let av = v_to_ref_val(spine, defs, *a);
                acc = match acc.as_ref() {
                    CVal::Flex(m, sp) => {
                        Rc::new(CVal::Flex(*m, sp.prepend((av, *i))))
                    }
                    CVal::Rigid(l, sp) => {
                        Rc::new(CVal::Rigid(*l, sp.prepend((av, *i))))
                    }
                    CVal::Decl(n, sp) => {
                        Rc::new(CVal::Decl(n.clone(), sp.prepend((av, *i))))
                    }
                    CVal::Obj(x, n, sp) => {
                        Rc::new(CVal::Obj(x.clone(), n.clone(), sp.prepend((av, *i))))
                    }
                    _ => return unmatchable(),
                };
            }
            acc
        }
        3 => Rc::new(CVal::U(v_u_of(v))),
        5 => Rc::new(CVal::Flex(super::MetaVar(v_meta_of(v)), CList::new())),
        6 => Rc::new(CVal::LiteralType),
        7 => match v_xcell_of(v) {
            XCell::Lit(s) => Rc::new(CVal::LiteralIntro(crate::parser_lib::Span {
                data: s.to_string(),
                start_offset: 0,
                end_offset: 0,
                path_id: 0,
            })),
            // 原生 Nat（L13）
            XCell::Nat(k) => Rc::new(CVal::Nat(*k)),
            XCell::Sum {
                name,
                params,
                cases,
                is_trait,
            } => {
                let mut ps: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CVal>, Rc<CVal>, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter() {
                    ps.push((
                        nspan(p.name),
                        v_to_ref_val(spine, defs, p.val),
                        v_to_ref_val(spine, defs, p.ty),
                        p.icit,
                    ));
                }
                let cs: Vec<crate::parser_lib::Span<SmolStr>> =
                    cases.iter().map(|c| nspan(c)).collect();
                Rc::new(CVal::Sum(nspan(name), Rc::new(ps), Rc::new(cs), *is_trait))
            }
            XCell::SumCase {
                typ,
                index,
                datas,
                is_trait,
            } => {
                let mut ds: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CVal>, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter() {
                    ds.push((nspan(d.name), v_to_ref_val(spine, defs, d.val), d.icit));
                }
                Rc::new(CVal::SumCase {
                    is_trait: *is_trait,
                    typ: v_to_ref_val(spine, defs, *typ),
                    // index 制（L13）：快版值在解码点拿不到所属 Sum 的 cases
                    // 表，直接透传 index——消费端 val_match 同为 index 比较，
                    // 与参考版解码路径（index 相等）一致。
                    index: *index,
                    datas: Rc::new(ds),
                })
            }
            XCell::Call { name, args, body } => {
                let mut list: CList<(Rc<CVal>, Icit)> = CList::new();
                for (a, i) in args.iter().rev() {
                    list = list.prepend((v_to_ref_val(spine, defs, *a), *i));
                }
                Rc::new(CVal::Call(SmolStr::new(name), list, v_to_ref_val(spine, defs, *body)))
            }
            // Pi / 卡住 Match 等形态：参考版 val_match 对非构造子 goal 一律
            // false——降级为永不匹配的标记值，观察面相同。
            _ => unmatchable(),
        },
        _ => unmatchable(),
    }
}
