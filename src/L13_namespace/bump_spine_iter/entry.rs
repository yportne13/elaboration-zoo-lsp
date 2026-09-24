//! entry：对外入口——`export`（bump 项 → 参考 Box 树）、`tm_size`、no_metas
//! 族（未解 meta 报错路径）、builtin 注册（`prime_round`/`register_nat_builtins`/
//! `register_vconn_builtin`/`elab_all`）、常驻检查点（`Resident`）与稳态
//! 检查器 `Tycker`（run_decls/run_input/bench/prelude 口径）、`run_fast`/
//! `parse`/`SourceDecl`。原 bump_spine_iter.rs 的 "export 与对外入口" 节，
//! 逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;
use std::rc::Rc;

use super::parser::syntax::{Decl, Icit};
use super::{empty_span, Error, PatternDetail, CTm, CVal, Ix, MetaVar};

use super::compact;

use super::env::{EMPTY_ENV, CloCell, Env, PiCell};
use super::force::{
    force_memo_clear, twin_stat_record, ReclaimOnClear, CACHE_SHRINK_MIN_ENTRIES,
    META_JOURNAL, SPINE_SHRINK_MIN_ENTRIES, TWIN_STAT_CONV, TWIN_STAT_SPINE,
};
use super::machine::{
    clone_cxt, insert_prelude_aliases, state_journal_open_frame, state_journal_record,
    state_journal_rollback, types_names_list, Cxt, DeclOut, Machine, StateUndo,
};
use super::prim::{Mutable, PrimId};
use super::spine::{meta_journal_rollback, MetaEntry, MetaSnap};
use super::syntax::{
    SumDataT, SumParamT, Tm, V, XCell, v_clo_of, v_lit_ty, v_meta_of, v_pi_of, v_spine_of,
    v_tag, v_u, v_xcell, v_xcell_of,
};
use super::typeclass::{v_to_ref_val, TraitState};


// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。
pub(super) fn export(symbols: &FxHashMap<(SmolStr, usize), SmolStr>, t: &Tm<'_>) -> Rc<CTm> {
    use crate::list::List as CList;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, Icit),
        Pi2(&'a str, Icit),
        Let2(&'a str),
        App2(Icit),
        AppPrun2(CList<Option<Icit>>),
        Obj2(&'a str),
        Sum2 {
            name: &'a str,
            params: &'a [SumParamT<'a>],
            cases: &'a [&'a str],
            is_trait: bool,
        },
        SumCase2 {
            index: u32,
            datas: &'a [SumDataT<'a>],
            is_trait: bool,
        },
        /// Call 装配：`symbol` 命中（实参全 Expl 且 1-2 个）→ OpCall
        Call2 {
            name: &'a str,
            symbol: Option<SmolStr>,
            icits: Vec<Icit>,
        },
    }
    fn name(x: &str) -> crate::parser_lib::Span<SmolStr> {
        empty_span(SmolStr::new(x))
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<Rc<CTm>> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(Rc::new(CTm::Var(Ix(*i)))),
            J::Do(Tm::Lam(x, i, b)) => {
                tasks.push(J::Lam2(x, *i));
                tasks.push(J::Do(b));
            }
            J::Do(Tm::App(f, a, i)) => {
                tasks.push(J::App2(*i));
                tasks.push(J::Do(a));
                tasks.push(J::Do(f));
            }
            J::Do(Tm::AppPruning(h, pr)) => {
                // bds 持久链表（头 = 最内层）→ 参考版 List<Option<Icit>>（同序）
                let mut vec: Vec<Option<Icit>> = Vec::new();
                let mut cur = *pr;
                while let Some(b) = cur {
                    vec.push(b.slot);
                    cur = b.next;
                }
                let mut list: CList<Option<Icit>> = CList::new();
                for s in vec.into_iter().rev() {
                    list = list.prepend(s);
                }
                tasks.push(J::AppPrun2(list));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::U(l)) => done.push(Rc::new(CTm::U(*l))),
            J::Do(Tm::Pi(x, i, a, b)) => {
                tasks.push(J::Pi2(x, *i));
                tasks.push(J::Do(b));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Let(x, a, t, u)) => {
                tasks.push(J::Let2(x));
                tasks.push(J::Do(u));
                tasks.push(J::Do(t));
                tasks.push(J::Do(a));
            }
            J::Do(Tm::Meta(m)) => done.push(Rc::new(CTm::Meta(MetaVar(*m)))),
            J::Do(Tm::LiteralType) => done.push(Rc::new(CTm::LiteralType)),
            J::Do(Tm::LiteralIntro(s)) => done.push(Rc::new(CTm::LiteralIntro(
                crate::parser_lib::Span {
                    data: s.to_string(),
                    start_offset: 0,
                    end_offset: 0,
                    path_id: 0,
                },
            ))),
            J::Do(Tm::Decl(x)) => done.push(Rc::new(CTm::Decl(name(x)))),
            J::Do(Tm::Obj(h, n)) => {
                tasks.push(J::Obj2(n));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::Sum(nm, params, cases, is_trait)) => {
                let is_trait = *is_trait;
                tasks.push(J::Sum2 {
                    name: nm,
                    params,
                    cases,
                    is_trait,
                });
                for p in params.iter().rev() {
                    tasks.push(J::Do(p.ty));
                    tasks.push(J::Do(p.val));
                }
            }
            J::Do(Tm::SumCase {
                typ,
                index,
                datas,
                is_trait,
            }) => {
                let is_trait = *is_trait;
                tasks.push(J::SumCase2 {
                    index: *index,
                    datas,
                    is_trait,
                });
                for d in datas.iter().rev() {
                    tasks.push(J::Do(d.val));
                }
                tasks.push(J::Do(typ));
            }
            J::Do(Tm::Call(nm, args, body)) => {
                // OpCall 决策（参考版 quote 的 Call 臂）：实参全 Expl 且
                // 1-2 个且 symbol_table 命中 → 显示专用 OpCall（保留全部
                // call 数据保证 eval 往返恒等）
                let icits_buf: Vec<Icit> = args.iter().map(|(_, i)| *i).collect();
                let sym_hit = if args.iter().all(|(_, i)| *i == Icit::Expl) {
                    symbols.get(&(SmolStr::new(nm), args.len())).cloned()
                } else {
                    None
                }
                .filter(|_| args.len() == 1 || args.len() == 2);
                tasks.push(J::Call2 {
                    name: nm,
                    symbol: sym_hit,
                    icits: icits_buf,
                });
                tasks.push(J::Do(body));
                for (a, _) in args.iter() {
                    tasks.push(J::Do(a));
                }
            }
            J::Do(Tm::Match(s, cases)) => {
                // 分支体逐个内联导出（递归深度 = match 嵌套深度）；模式直接
                // 克隆（PatternDetail 是参考版类型，两版共用）
                let s2 = export(symbols, s);
                let mut cs: Vec<(PatternDetail, Rc<CTm>)> = Vec::with_capacity(cases.len());
                for (p, b) in cases.iter() {
                    cs.push((p.clone(), export(symbols, b)));
                }
                done.push(Rc::new(CTm::Match(s2, cs)));
            }
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(Rc::new(CTm::Lam(name(x), i, b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(Rc::new(CTm::Pi(name(x), i, dom, cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(Rc::new(CTm::Let(name(x), a, t, u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(Rc::new(CTm::App(f, a, i)));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(Rc::new(CTm::AppPruning(h, pr)));
            }
            J::Obj2(n) => {
                let h = done.pop().expect("export 栈：Obj 缺接收者");
                done.push(Rc::new(CTm::Obj(h, name(n))));
            }
            J::Sum2 {
                name: nm,
                params,
                cases,
                is_trait,
            } => {
                let mut ps: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CTm>, Rc<CTm>, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("export 栈：Sum 缺参数类型");
                    let val = done.pop().expect("export 栈：Sum 缺参数值");
                    ps.push((name(p.name), val, ty, p.icit));
                }
                ps.reverse();
                let cs: Vec<crate::parser_lib::Span<SmolStr>> =
                    cases.iter().map(|c| name(c)).collect();
                // L13 CTm::Sum 携带 Rc<Vec>（O(1) 克隆）
                done.push(Rc::new(CTm::Sum(
                    name(nm),
                    Rc::new(ps),
                    Rc::new(cs),
                    is_trait,
                )));
            }
            J::SumCase2 {
                index,
                datas,
                is_trait,
            } => {
                let mut ds: Vec<(crate::parser_lib::Span<SmolStr>, Rc<CTm>, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("export 栈：SumCase 缺字段");
                    ds.push((name(d.name), val, d.icit));
                }
                ds.reverse();
                let typ = done.pop().expect("export 栈：SumCase 缺 typ");
                done.push(Rc::new(CTm::SumCase {
                    typ,
                    index,
                    datas: Rc::new(ds),
                    is_trait,
                }));
            }
            J::Call2 { name: nm, symbol, icits } => {
                // done 自底向上是 (a_{n-1}, ..., a0, body)（body 最后导、在顶）
                let body = done.pop().expect("export 栈：Call 缺体");
                let mut items: Vec<Rc<CTm>> = Vec::with_capacity(icits.len());
                for _ in 0..icits.len() {
                    items.push(done.pop().expect("export 栈：Call 缺实参"));
                }
                // 弹出序 = a0..a_{n-1}；List 序 head = 首实参 → 逆序 prepend
                let mut args: CList<(Rc<CTm>, Icit)> = CList::new();
                for (t, i) in items.into_iter().zip(icits.iter().copied()).rev() {
                    args = args.prepend((t, i));
                }
                match symbol {
                    Some(symbol) => done.push(Rc::new(CTm::OpCall {
                        symbol,
                        name: SmolStr::new(nm),
                        args,
                        body,
                    })),
                    None => done.push(Rc::new(CTm::Call(SmolStr::new(nm), args, body))),
                }
            }
        }
    }
    done.pop().expect("export 必须恰有一个根")
}
/// 参考版项的节点数（与 mod.rs `tm_size_ref` 同口径）。
fn tm_size(t: &Tm<'_>) -> u64 {
    let mut stack: Vec<&Tm<'_>> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType
            | Tm::LiteralIntro(_) => {}
            Tm::Obj(h, _) => stack.push(h),
            Tm::Lam(_, _, b) => stack.push(b),
            Tm::App(f, a, _) => {
                stack.push(f);
                stack.push(a);
            }
            Tm::AppPruning(h, pr) => {
                stack.push(h);
                let mut cur = *pr;
                while let Some(b) = cur {
                    n += 1;
                    cur = b.next;
                }
            }
            Tm::Pi(_, _, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Tm::Let(_, a, t, u) => {
                stack.push(a);
                stack.push(t);
                stack.push(u);
            }
            Tm::Sum(_, params, _, _) => {
                for p in params.iter() {
                    stack.push(p.val);
                    stack.push(p.ty);
                }
            }
            Tm::SumCase { typ, datas, .. } => {
                stack.push(typ);
                for d in datas.iter() {
                    stack.push(d.val);
                }
            }
            Tm::Match(s, cases) => {
                stack.push(s);
                for (p, b) in cases.iter() {
                    n += p.bind_count() as u64;
                    stack.push(b);
                }
            }
            Tm::Call(_, args, body) => {
                for (a, _) in args.iter() {
                    stack.push(a);
                }
                stack.push(body);
            }
        }
    }
    n
}

impl Machine {
    /// 每轮注册（参考版 `Cxt::new` 逐条对应）：String 类型 + 15 个内建
    /// （string_concat / str_eq / str_indent2 / report_check_issue /
    /// string_to_global_type / create_global / change_mutable / get_global /
    /// get_global_default / change_mutable_default / file_read_all_text /
    /// file_write_all_text / file_append_all_text / file_exists /
    /// file_delete）。值/类型形态按参考版手工构造——类型项经 `tm_pi` 同序
    /// 折叠、空环境求值；登记项是自引用 `Tm::Decl(name)` 占位 + 卡住
    /// `Decl` 单元 + prim 挂表，真正行为在 force / v_app 的 Decl 臂按
    /// [`PrimId`] 分派（`def_needs_replay` 对内建恒 false）。
    fn prime_round<'a>(&mut self, bump: &'a Bump) -> Cxt<'a> {
        let empty = Cxt::empty();
        // String : U(0)，值 = LiteralType（参考版 Cxt::new 首项）
        let cxt = self.decl_reg(
            bump, &empty, "String", empty_span(()),
            bump.alloc(Tm::LiteralType),
            v_lit_ty(),
            bump.alloc(Tm::U(0)),
            v_u(0),
            None,
        );
        // ── 15 个内建（参考版 add_builtin 逐字）：登记项是自引用
        // `Tm::Decl(name)` 占位 + 卡住 Decl 单元 + prim 挂表——真正行为在
        // force / v_app 的 Decl 臂按 PrimId 分派（def_needs_replay 对内建
        // 恒 false）。类型项按参考版 tm_pi 链手工构造，空环境求值。──
        let st = bump.alloc(Tm::Decl(bump.alloc_str("String"))); // String
        let stgt = |bump: &'a Bump, var: u32| -> &'a Tm<'a> {
            bump.alloc(Tm::App(
                bump.alloc(Tm::Decl(bump.alloc_str("string_to_global_type"))),
                bump.alloc(Tm::Var(var)),
                Icit::Expl,
            ))
        };
        let u0 = || bump.alloc(Tm::U(0));
        // Π 链折叠（head = 首参数；与参考 tm_pi 同序）
        let pi = |bump: &'a Bump, args: Vec<(&'static str, &'a Tm<'a>)>, ret: &'a Tm<'a>| -> &'a Tm<'a> {
            args.iter().rev().fold(ret, |acc, (n, d)| {
                bump.alloc(Tm::Pi(bump.alloc_str(n), Icit::Expl, *d, acc))
            })
        };
        let str_str = || pi(bump, vec![("x", st), ("y", st)], st);
        let boolean = || bump.alloc(Tm::Decl(bump.alloc_str("Boolean")));
        let builtins: Vec<(&'static str, PrimId, &'a Tm<'a>)> = vec![
            ("string_concat", PrimId::StringConcat, str_str()),
            ("str_eq", PrimId::StrEq, pi(bump, vec![("x", st), ("y", st)], boolean())),
            ("str_indent2", PrimId::StrIndent2, pi(bump, vec![("x", st)], st)),
            (
                "report_check_issue",
                PrimId::ReportCheckIssue,
                pi(bump, vec![("code", st), ("module", st), ("signal", st), ("message", st)], u0()),
            ),
            ("string_to_global_type", PrimId::StringToGlobalType, pi(bump, vec![("x", st)], u0())),
            (
                "create_global",
                PrimId::CreateGlobal,
                pi(bump, vec![("x", st), ("y", stgt(bump, 0))], u0()),
            ),
            (
                "change_mutable",
                PrimId::ChangeMutable,
                pi(
                    bump,
                    vec![
                        ("x", st),
                        (
                            "f",
                            pi(bump, vec![("_", stgt(bump, 0))], stgt(bump, 1)),
                        ),
                    ],
                    u0(),
                ),
            ),
            ("get_global", PrimId::GetGlobal, pi(bump, vec![("x", st)], stgt(bump, 0))),
            (
                "get_global_default",
                PrimId::GetGlobalDefault,
                pi(bump, vec![("x", st), ("z", stgt(bump, 0))], stgt(bump, 1)),
            ),
            (
                "change_mutable_default",
                PrimId::ChangeMutableDefault,
                pi(
                    bump,
                    vec![
                        ("x", st),
                        (
                            "f",
                            pi(bump, vec![("_", stgt(bump, 0))], stgt(bump, 1)),
                        ),
                        ("z", stgt(bump, 1)),
                    ],
                    u0(),
                ),
            ),
            ("file_read_all_text", PrimId::FileReadAllText, pi(bump, vec![("path", st)], st)),
            (
                "file_write_all_text",
                PrimId::FileWriteAllText,
                pi(bump, vec![("path", st), ("content", st)], u0()),
            ),
            (
                "file_append_all_text",
                PrimId::FileAppendAllText,
                pi(bump, vec![("path", st), ("content", st)], u0()),
            ),
            ("file_exists", PrimId::FileExists, pi(bump, vec![("path", st)], st)),
            ("file_delete", PrimId::FileDelete, pi(bump, vec![("path", st)], u0())),
        ];
        let mut cxt = cxt;
        for (name, pid, ty_tm) in builtins {
            let vty = self.eval(bump, &cxt, EMPTY_ENV, ty_tm);
            let nm = bump.alloc_str(name);
            let placeholder = bump.alloc(Tm::Decl(nm));
            let val = v_xcell(bump.alloc(XCell::Decl { name: nm }));
            cxt = self.decl_reg(bump, &cxt, name, empty_span(()), placeholder, val, ty_tm, vty, Some(pid));
        }
        cxt
    }

    /// nat 族内建注册（参考版 `Cxt::register_nat_builtins` 逐条对应）：
    /// `nat_to_dec` / `width_range` / `nat_is_ground` + 五则算术 primop。
    /// **时机**：参考版在 nat.typort 加载后调用（该文件的 `+`/`-` impl 体要
    /// 能解析这些名字，故先有递归 def 兜底、再由 prim 覆盖）。
    fn register_nat_builtins<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>) -> Cxt<'a> {
        let nat = bump.alloc(Tm::Decl(bump.alloc_str("Nat")));
        let st = bump.alloc(Tm::Decl(bump.alloc_str("String")));
        let boolean = bump.alloc(Tm::Decl(bump.alloc_str("Boolean")));
        let pi = |bump: &'a Bump, args: Vec<(&'static str, &'a Tm<'a>)>, ret: &'a Tm<'a>| -> &'a Tm<'a> {
            args.iter().rev().fold(ret, |acc, (n, d)| {
                bump.alloc(Tm::Pi(bump.alloc_str(n), Icit::Expl, *d, acc))
            })
        };
        let nat2 = || pi(bump, vec![("x", nat), ("y", nat)], nat);
        let builtins: Vec<(&'static str, PrimId, &'a Tm<'a>)> = vec![
            ("nat_to_dec", PrimId::NatToDec, pi(bump, vec![("n", nat)], st)),
            ("width_range", PrimId::WidthRange, pi(bump, vec![("w", nat)], st)),
            ("nat_is_ground", PrimId::NatIsGround, pi(bump, vec![("w", nat)], boolean)),
            ("nat_add", PrimId::NatAdd, nat2()),
            ("nat_mul", PrimId::NatMul, nat2()),
            ("nat_sub", PrimId::NatSub, nat2()),
            ("nat_div", PrimId::NatDiv, nat2()),
            ("nat_rem", PrimId::NatRem, nat2()),
        ];
        let mut cxt = clone_cxt(cxt);
        for (name, pid, ty_tm) in builtins {
            let vty = self.eval(bump, &cxt, EMPTY_ENV, ty_tm);
            let nm = bump.alloc_str(name);
            let placeholder = bump.alloc(Tm::Decl(nm));
            let val = v_xcell(bump.alloc(XCell::Decl { name: nm }));
            cxt = self.decl_reg(bump, &cxt, name, empty_span(()), placeholder, val, ty_tm, vty, Some(pid));
        }
        cxt
    }

    /// Verilog 兼容具名端口连接内建 `vconnT`（参考版 `Cxt::
    /// register_vconn_builtin` 对应）：`ModuleTree -> Expr -> Expr -> U(0)`。
    /// **时机**：prelude 全部装载后（nat 内建之后）——签名引用的
    /// ModuleTree/Expr 只有 prelude 里有；提前登记的 `tm_decl("ModuleTree")`
    /// 是悬空 neutral，会让后续 unify 打转（参考版注释同款）。
    fn register_vconn_builtin<'a>(&mut self, bump: &'a Bump, cxt: &Cxt<'a>) -> Cxt<'a> {
        let mt = bump.alloc(Tm::Decl(bump.alloc_str("ModuleTree")));
        let expr = bump.alloc(Tm::Decl(bump.alloc_str("Expr")));
        let pi = |bump: &'a Bump, args: Vec<(&'static str, &'a Tm<'a>)>, ret: &'a Tm<'a>| -> &'a Tm<'a> {
            args.iter().rev().fold(ret, |acc, (n, d)| {
                bump.alloc(Tm::Pi(bump.alloc_str(n), Icit::Expl, *d, acc))
            })
        };
        let ty_tm = pi(
            bump,
            vec![("childTree", mt), ("port", expr), ("sig", expr)],
            bump.alloc(Tm::U(0)),
        );
        let vty = self.eval(bump, cxt, EMPTY_ENV, ty_tm);
        let nm = bump.alloc_str("vconnT");
        let placeholder = bump.alloc(Tm::Decl(nm));
        let val = v_xcell(bump.alloc(XCell::Decl { name: nm }));
        self.decl_reg(bump, cxt, "vconnT", empty_span(()), placeholder, val, ty_tm, vty, Some(PrimId::VconnT))
    }

    fn elab_all<'a>(
        &mut self,
        bump: &'a Bump,
        ast: &[Decl],
    ) -> (Result<(), Error>, Cxt<'a>, Option<V>) {
        let mut cxt = self.prime_round(bump);
        let mut last = None;
        for d in ast {
            match self.infer_decl(bump, &mut cxt, d) {
                Ok((out, nc)) => {
                    cxt = nc;
                    if let DeclOut::Def { name } = out {
                        last = cxt.decls.get(name).map(|e| e.val);
                    }
                }
                Err(e) => return (Err(e), cxt, last),
            }
        }
        (Ok(()), cxt, last)
    }
}

/// no_metas 的已解 meta quote 层级（参考版 `val_no_metas` 的
/// `NM_QUOTE_LVL = u32::MAX / 2` 同款）：解出时的上下文可以比当前 cxt 深
/// （值里 Rigid 层级 ≥ cxt.lvl），按 cxt.lvl 引会在 `level - l - 1` 下溢
/// （实测 09-hierarchy 的 def no_metas 检查）。结果只被扫 `Tm::Meta`
/// 节点，de Bruijn 下标无所谓，层级任意但必须足够大。
const NM_QUOTE_LVL: u32 = u32::MAX / 2;

/// 参考版 `Tm::no_metas`（L12）：项里第一个**未解** meta 的（上下文快照,
/// 原始类型）——已解 meta **递归进解**。
///
/// **必须走值图 + 访问集，不能对已解 meta 的解做 quote 再查**（参考版
/// mod.rs `no_metas` 的同一修复）：扁平化的 module/bundle 链上，解里嵌着
/// 巨大且**自引用**的已解 meta——quote 出解再查会重新遇到同一个 meta，
/// 无限展开（实测 `examples/hdl/01-basics.typort`：表达式 `let x = a + b`
/// 展开出的 create 体在 `no_metas` 处死循环）。值图上按值身份去重即可终止；
/// 参考版注释记录该 quote 版曾占某 HDL 例 65% 采样。
///
/// 两套访问集分开：`Tm` 用指针、值用打包字——二者是不同地址空间，混用会
/// 误判同号（参考版两套都是 Rc 指针故可共用）。
pub(super) fn no_metas<'a>(
    bump: &'a Bump,
    m: &mut Machine,
    cxt: &Cxt<'a>,
    t: &'a Tm<'a>,
) -> Option<(crate::list::List<SmolStr>, V)> {
    let mut seen_v: FxHashSet<u64> = FxHashSet::default();
    let mut seen_tm: FxHashSet<usize> = FxHashSet::default();
    tm_no_metas(bump, m, cxt, t, &mut seen_v, &mut seen_tm)
}

/// 未解 meta 的（名字表, 原始类型）——取自快照 telescope（参考版用整个快照
/// cxt 的 names()，错误消息 pretty 用）。
fn meta_unsolved_result(snap: &Rc<MetaSnap<'static>>, oty: V) -> (crate::list::List<SmolStr>, V) {
    let snap: &MetaSnap<'_> =
        unsafe { &*(snap.as_ref() as *const MetaSnap<'static> as *const MetaSnap<'_>) };
    (types_names_list(snap.types), oty)
}

/// 项层遍历（指针去重）。`Tm::Meta` 已解 → 转值图（`val_no_metas`）。
fn tm_no_metas<'a>(
    bump: &'a Bump,
    m: &mut Machine,
    cxt: &Cxt<'a>,
    t: &'a Tm<'a>,
    seen_v: &mut FxHashSet<u64>,
    seen_tm: &mut FxHashSet<usize>,
) -> Option<(crate::list::List<SmolStr>, V)> {
    if !seen_tm.insert(t as *const Tm<'a> as usize) {
        return None;
    }
    match t {
        Tm::Var(_) | Tm::Decl(_) | Tm::U(_) | Tm::LiteralType | Tm::LiteralIntro(_) => None,
        Tm::Lam(_, _, b) => tm_no_metas(bump, m, cxt, b, seen_v, seen_tm),
        Tm::App(f, a, _) => tm_no_metas(bump, m, cxt, f, seen_v, seen_tm)
            .or_else(|| tm_no_metas(bump, m, cxt, a, seen_v, seen_tm)),
        Tm::AppPruning(h, _) => tm_no_metas(bump, m, cxt, h, seen_v, seen_tm),
        Tm::Pi(_, _, a, b) => tm_no_metas(bump, m, cxt, a, seen_v, seen_tm)
            .or_else(|| tm_no_metas(bump, m, cxt, b, seen_v, seen_tm)),
        Tm::Let(_, a, x, u) => tm_no_metas(bump, m, cxt, a, seen_v, seen_tm)
            .or_else(|| tm_no_metas(bump, m, cxt, x, seen_v, seen_tm))
            .or_else(|| tm_no_metas(bump, m, cxt, u, seen_v, seen_tm)),
        Tm::Meta(mm) => match &m.metas[*mm as usize] {
            MetaEntry::Unsolved(_, snap, oty, _) => Some(meta_unsolved_result(snap, *oty)),
            MetaEntry::Solved(sol, _) => val_no_metas(bump, m, cxt, *sol, seen_v, seen_tm),
        },
        Tm::Obj(h, _) => tm_no_metas(bump, m, cxt, h, seen_v, seen_tm),
        Tm::Sum(_, params, ..) => params.iter().find_map(|p| {
            tm_no_metas(bump, m, cxt, p.val, seen_v, seen_tm)
                .or_else(|| tm_no_metas(bump, m, cxt, p.ty, seen_v, seen_tm))
        }),
        Tm::SumCase { typ, datas, .. } => tm_no_metas(bump, m, cxt, typ, seen_v, seen_tm)
            .or_else(|| {
                datas.iter().find_map(|d| tm_no_metas(bump, m, cxt, d.val, seen_v, seen_tm))
            }),
        Tm::Match(s, cases) => tm_no_metas(bump, m, cxt, s, seen_v, seen_tm).or_else(|| {
            cases.iter().find_map(|(_, b)| tm_no_metas(bump, m, cxt, b, seen_v, seen_tm))
        }),
        Tm::Call(_, args, body) => args
            .iter()
            .find_map(|(a, _)| tm_no_metas(bump, m, cxt, a, seen_v, seen_tm))
            .or_else(|| tm_no_metas(bump, m, cxt, body, seen_v, seen_tm)),
    }
}

/// 值层遍历（按打包字去重，破自引用环）。对照参考版 `val_no_metas`。
fn val_no_metas<'a>(
    bump: &'a Bump,
    m: &mut Machine,
    cxt: &Cxt<'a>,
    v: V,
    seen_v: &mut FxHashSet<u64>,
    seen_tm: &mut FxHashSet<usize>,
) -> Option<(crate::list::List<SmolStr>, V)> {
    if !seen_v.insert(v.0) {
        return None;
    }
    match v_tag(v) {
        0 | 3 | 6 => None, // Rigid / U / LiteralType
        1 => {
            let c: &CloCell<'a> = v_clo_of(v);
            env_no_metas(bump, m, cxt, c.env, seen_v, seen_tm)
                .or_else(|| tm_no_metas(bump, m, cxt, c.body, seen_v, seen_tm))
        }
        2 => {
            let h = v_spine_of(v);
            let hd = m.spine.spine_head(h);
            let mut args: Vec<(V, Icit)> = Vec::new();
            m.spine.collect_args(h, &mut args);
            let in_args = |m: &mut Machine,
                           seen_v: &mut FxHashSet<u64>,
                           seen_tm: &mut FxHashSet<usize>|
             -> Option<(crate::list::List<SmolStr>, V)> {
                args.iter()
                    .find_map(|(a, _)| val_no_metas(bump, m, cxt, *a, seen_v, seen_tm))
            };
            match v_tag(hd) {
                // 头是 meta：等价参考版 `Val::Flex(m, sp)`。带 spine 的解
                // 只有求值才能得，退回 quote（参考版同款，层级用 NM_QUOTE_LVL）。
                5 => {
                    if !args.is_empty() {
                        let q = m.quote(bump, cxt, NM_QUOTE_LVL, v);
                        return tm_no_metas(bump, m, cxt, q, seen_v, seen_tm);
                    }
                    let mi = v_meta_of(hd);
                    match &m.metas[mi as usize] {
                        MetaEntry::Unsolved(_, snap, oty, _) => Some(meta_unsolved_result(snap, *oty)),
                        MetaEntry::Solved(sol, _) => val_no_metas(bump, m, cxt, *sol, seen_v, seen_tm),
                    }
                }
                // 卡住投影头：本体 + 实参都要走（参考版 `Val::Obj`）。
                7 => match v_xcell_of(hd) {
                    XCell::Obj { val, .. } => val_no_metas(bump, m, cxt, *val, seen_v, seen_tm)
                        .or_else(|| in_args(m, seen_v, seen_tm)),
                    _ => in_args(m, seen_v, seen_tm),
                },
                // Rigid / Decl 头：只看实参（参考版 `Val::Rigid | Val::Decl`）。
                _ => in_args(m, seen_v, seen_tm),
            }
        }
        4 => {
            let p: &PiCell<'a> = v_pi_of(v);
            val_no_metas(bump, m, cxt, p.dom, seen_v, seen_tm)
                .or_else(|| env_no_metas(bump, m, cxt, p.env, seen_v, seen_tm))
                .or_else(|| tm_no_metas(bump, m, cxt, p.body, seen_v, seen_tm))
        }
        5 => {
            let mi = v_meta_of(v);
            match &m.metas[mi as usize] {
                MetaEntry::Unsolved(_, snap, oty, _) => Some(meta_unsolved_result(snap, *oty)),
                MetaEntry::Solved(sol, _) => val_no_metas(bump, m, cxt, *sol, seen_v, seen_tm),
            }
        }
        7 => match v_xcell_of(v) {
            XCell::Lit(_) | XCell::Nat(_) | XCell::Decl { .. } => None,
            XCell::Obj { val, .. } => val_no_metas(bump, m, cxt, *val, seen_v, seen_tm),
            XCell::Sum { params, .. } => params.iter().find_map(|p| {
                val_no_metas(bump, m, cxt, p.val, seen_v, seen_tm)
                    .or_else(|| val_no_metas(bump, m, cxt, p.ty, seen_v, seen_tm))
            }),
            XCell::SumCase { typ, datas, .. } => val_no_metas(bump, m, cxt, *typ, seen_v, seen_tm)
                .or_else(|| {
                    datas.iter().find_map(|d| val_no_metas(bump, m, cxt, d.val, seen_v, seen_tm))
                }),
            XCell::Call { args, body, .. } => args
                .iter()
                .find_map(|(a, _)| val_no_metas(bump, m, cxt, *a, seen_v, seen_tm))
                .or_else(|| val_no_metas(bump, m, cxt, *body, seen_v, seen_tm)),
            XCell::Match { scrutinee, env, cases, .. } => {
                val_no_metas(bump, m, cxt, *scrutinee, seen_v, seen_tm)
                    .or_else(|| env_no_metas(bump, m, cxt, *env, seen_v, seen_tm))
                    .or_else(|| {
                        cases.iter().find_map(|(_, b)| tm_no_metas(bump, m, cxt, b, seen_v, seen_tm))
                    })
            }
        },
        _ => None,
    }
}

/// 环境遍历：链（binds）逐节点值 + 平坦区（defs 切片）。
fn env_no_metas<'a>(
    bump: &'a Bump,
    m: &mut Machine,
    cxt: &Cxt<'a>,
    env: Env<'a>,
    seen_v: &mut FxHashSet<u64>,
    seen_tm: &mut FxHashSet<usize>,
) -> Option<(crate::list::List<SmolStr>, V)> {
    let mut cur = env.binds;
    while let Some(e) = cur {
        if let Some(r) = val_no_metas(bump, m, cxt, e.val, seen_v, seen_tm) {
            return Some(r);
        }
        cur = e.next;
    }
    let base = env.flat_base as usize;
    let end = base + env.flat_len as usize;
    for i in base..end {
        if let Some(r) = val_no_metas(bump, m, cxt, m.defs[i], seen_v, seen_tm) {
            return Some(r);
        }
    }
    None
}

/// 参考版 Def 臂的未解 meta 报错（elaboration.rs 逐字——类型类是 trait
/// Sum 时给类型类消息，否则 `find unsolved meta with type ...`）。
/// 常驻 prelude 检查点（阶段 3b，docs/lsp-twin-wiring-2026-09.md）：prelude
/// 装载后的稳态快照，使每次交互 kick 只支付用户段增量（~59ms）而非整轮
/// 重放（~2.8s）。
///
/// **生命周期口径**：`cxt` 与快照里的句柄都指向 [`Tycker::bump`]；检查点
/// 存活期间 bump 绝不 `reset()`（任何 reset 路径都清 `resident`），故地址
/// 稳定、句柄有效。`cxt` 以 `'static` 存放（[`Tycker::prime_resident`] 处
/// transmute，与模块内 workbuf / `MetaSnap` 的 'static 存放口径同款），取出
/// 时按 `Cxt` 的协变降回 `bump` 的实生命周期。
struct Resident {
    cxt: Cxt<'static>,
    /// prelude 段的 `defs` 长度（用户段 append-only，下轮 truncate 回此）。
    defs_len: usize,
    /// prime 完成时的 bump 已分配字节数（基线）。用户段每 kick 的中间值
    /// 无法回收，超过 `base + RESIDENT_BUMP_LIMIT` 时下轮就地压实
    /// （[`Tycker::compact_resident`]，`base_bytes` 随新 arena 刷新）。
    base_bytes: usize,
    /// 压实用的新 arena 容量提示（prime 由实测 live 推得，跨 kick 恒定——
    /// 用 `base_bytes` 反推会形成每压一次涨 12.5% 的反馈环）。
    cap_hint: usize,
    /// 稳态快照：用户段可能改动这些 per-run 状态（新增 meta、注册实例、
    /// 写可变全局、挂算符方法、导入别名），每 kick 恢复。值均为 owned 或被
    /// 常驻 bump 钉住的句柄（Clone 即安全）。
    metas: Vec<MetaEntry>,
    /// 常驻基线（prelude）decl 键集——`observe_user` 每 kick diff 出本轮
    /// 新声明用。源 `cxt` 在 kick 间只读，prime 时预计算一次（评审 B#2h：
    /// 原每 kick 重建 943+ SmolStr 集合 ~1-2ms）。
    base_keys: FxHashSet<SmolStr>,
    tstate: TraitState,
    mutable: Mutable,
    symbol_table: FxHashMap<(SmolStr, usize), SmolStr>,
    import_map: FxHashMap<SmolStr, SmolStr>,
    trait_method_cache: FxHashMap<(SmolStr, SmolStr), (Rc<CTm>, Rc<CVal>, Rc<CTm>)>,
    tm_import: FxHashMap<usize, &'static Tm<'static>>,
    val_import: FxHashMap<usize, V>,
}

/// 常驻 bump 上限（字节）：用户段增量超限时下个 kick 由
/// [`Tycker::compact_resident`] 就地压实检查点（换新 arena，O(可达)）。
/// 用户段每 kick 分配的中间值无法回收（bump 不支持截断），压实把不可达
/// 垃圾整体丢弃；旧实现此处重放整个 prelude（~3s/次），2026-09-14 改为
/// 压实（~几十 ms/次），消除周期性多秒卡顿。
pub(super) const RESIDENT_BUMP_LIMIT: usize = 512 << 20;

/// prime 期的 arena 累计分配阈值（字节）：超过即在下一个 decl 前就地压实。
///
/// 文件边界的粒度不足以约束峰值——单个大文件可在文件边界之前把 arena
/// 累计分配到 ~1GB（`Bump` 不回收旧 chunk，`allocated_bytes` 即 chunk 链
/// 总和 ≈ RSS 占用）。远大于 prelude 的 live 状态（实测 ~53MB，压实拷贝
/// 成本 ~50ms/次），又远小于单文件可累积的量；**出厂 384MB** 是
/// `docs/mem-round-2026-09-20.md` §7.3 的实测取舍（+1.3% 启动时间换
/// −10% 活 arena 峰值，并保证单文件不会把 chunk 链顶到 1GB 量级；内存
/// 受限部署可调 `192 << 20` 得 −19.7% / +5.4%）。
const PRIME_COMPACT_BYTES: usize = 384 << 20;

thread_local! {
    /// 本线程的常驻用户段预算（默认 [`RESIDENT_BUMP_LIMIT`]）。测试/测量
    /// 可调小以在小区间内走到 [`Tycker::compact_resident`]；线程局部，故
    /// 并行测试互不干扰。
    static RESIDENT_BUMP_BUDGET: std::cell::Cell<usize> =
        const { std::cell::Cell::new(RESIDENT_BUMP_LIMIT) };
    /// 本线程压实次数（测试断言压实路径确实被走到）。
    static RESIDENT_COMPACTIONS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// 设置本线程的常驻用户段预算（测试/测量钩子）。
#[cfg(test)]
pub(crate) fn set_resident_bump_budget(budget: usize) {
    RESIDENT_BUMP_BUDGET.with(|c| c.set(budget));
}

/// 本线程累计的检查点压实次数（测试钩子）。
#[cfg(test)]
pub(crate) fn resident_compactions() -> usize {
    RESIDENT_COMPACTIONS.with(|c| c.get())
}

/// `TYPORT_TWIN_MEM` 开时打印 prime 的逐文件 bump 增长（内存剖析）。
fn twin_mem_prof() -> bool {
    std::env::var_os("TYPORT_TWIN_MEM").is_some()
}

/// 稳态类型检查器（同 L03-L08：owns 反复 `reset` 的 `Bump` 与跨调用复用
/// 的 [`Machine`]）。
pub(crate) struct Tycker {
    pub(super) bump: Bump,
    pub(super) machine: Machine,
    /// 阶段 3b 常驻 prelude 检查点（[`Tycker::prime_resident`] 置，
    /// [`Tycker::observe_user`] 消费；`bump.reset()` 的任何路径清空）。
    resident: Option<Resident>,
    /// 用户段累积错误（[`Tycker::observe_user`] 逐 decl 收集，不早退）——
    /// 孪生自产诊断用（参考版 `Infer.accumulated_errors` 等的对位）。
    user_errors: Vec<Error>,
    /// 上一轮 `observe_user` 用户段的 net meta 创建量（journal 回滚前
    /// 记录）——18-utils 分叉调查的对照信号（孪生 vs 参考版
    /// `infer.meta.len()` 增量）。
    last_kick_metas_created: usize,
    /// 本轮用户段声明的参考域导出（[`Tycker::observe_user`] 末尾导出）：
    /// 供 LSP 合并进参考域 `cxt.decl`（Path1 定义处悬浮/成员渲染/跨文件）。
    user_decl_exports: Vec<(SmolStr, super::ExportedDecl)>,
}

impl Tycker {
    pub(crate) fn new() -> Self {
        Tycker {
            bump: Bump::with_capacity(1 << 20),
            machine: Machine::new(),
            resident: None,
            user_errors: Vec::new(),
            last_kick_metas_created: 0,
            user_decl_exports: Vec::new(),
        }
    }

    /// 本轮用户段累积的错误（每 kick `observe_user` 前清空）。
    pub(crate) fn user_errors(&self) -> &[Error] {
        &self.user_errors
    }

    /// 上一轮用户段的 net meta 创建量（见字段注释）。
    pub(crate) fn last_kick_metas_created(&self) -> usize {
        self.last_kick_metas_created
    }

    /// 本轮用户段声明的参考域导出（prim 条目不导出——用户声明不会是
    /// prim；prim 条目仍由参考版 prelude 表持有）。
    pub(crate) fn user_decl_exports(&self) -> &[(SmolStr, super::ExportedDecl)] {
        &self.user_decl_exports
    }

    /// **阶段 3b 常驻入口**：装载 prelude 并固化检查点。之后多次
    /// [`Tycker::observe_user`] 复用这份 prelude，只支付用户段增量。
    /// `prelude.failed` 非 `None` 快速失败（同 `run_decls_with_prelude`）。
    pub(crate) fn prime_resident(&mut self, prelude: &super::PreludeParse) -> Result<(), Error> {
        if let Some(f) = &prelude.failed {
            return Err(Error(
                empty_span(format!("prelude file `{f}` failed to parse")),
                vec![],
            ));
        }
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        // prelude 段关观察面 push（同 run_decls_with_prelude）。
        self.machine.observe = false;
        // cxt 以 'static 存放口径持有（见 `compact` 模块头）：每文件边界就地
        // 压实把它与 machine 的可达状态拷进紧凑 bump，`self.bump` 随之更换
        // ——故不缓存 `&self.bump`，每处用前现取。
        let mut cxt: Cxt<'static> = unsafe {
            std::mem::transmute::<Cxt<'_>, Cxt<'static>>(self.machine.prime_round(&self.bump))
        };
        let mut cap_hint: usize = 8 << 20;
        let mut file_i = 0usize;
        // TYPORT_TWIN_MEM 的逐 decl churn 打印水位（见循环内探针）。
        let mut mem_last: usize = self.bump.allocated_bytes();
        for (i, d) in prelude.decls.iter().enumerate() {
            // 单文件内的垃圾兜底：文件边界太粗。实测（2026-09-20）单个大
            // 文件（hdl-verilog 等）在到达文件边界前就能把 arena 累计分配到
            // ~1GB——bump 不回收、chunk 只增不减，于是 prime 峰值 RSS 由
            // 「文件边界之间那段累计量」决定（收尾压实的 962MB vs 关压实的
            // 1939MB 即此）。文件边界之外再按累计分配量触发一次就地压实，
            // 把 arena 常驻量钉在阈值 + 一次拷贝（live ~53MB → ~50ms）上。
            // 位置在 decl 之间：此刻唯一的活句柄是 `cxt`（与文件边界同纪律，
            // 逐 decl 的临时值已在上一次迭代的语句块尾析构）。
            if compact::compact_enabled() && self.bump.allocated_bytes() > PRIME_COMPACT_BYTES {
                // memo 键是 arena 地址（压实后失效），与文件边界同款先清。
                force_memo_clear();
                let (nc, live) = self.compact_state(cxt, cap_hint);
                cxt = nc;
                cap_hint = (live + live / 8 + (1 << 20)).max(8 << 20);
            }
            // TYPORT_TWIN_MEM：单 decl 的 arena 分配量（累计差）超过 64MB 时
            // 打印——prime 峰值的真正来源是"单个 decl 内的 churn"，文件边界
            // 与 decl 边界都拦不住它，只能靠这条探针定位到 decl。
            if twin_mem_prof() {
                let now = self.bump.allocated_bytes();
                if now < mem_last {
                    eprintln!("[TMEM] decl i={i}: arena 已压实（cap {} MB）", now >> 20);
                    mem_last = now;
                } else if now - mem_last > (64 << 20) {
                    eprintln!(
                        "[TMEM] decl i={i}: +{} MB churn（cap {} MB）",
                        (now - mem_last) >> 20,
                        now >> 20
                    );
                    mem_last = now;
                }
            }
            let (_out, nc) = {
                let b: &Bump = &self.bump;
                // Cxt<'static> 经 &mut 不可缩（不变型），浅克隆出本地可变
                // 副本再走 infer_decl（浅克隆 = Rc 引用计数 + Copy 字段）
                let mut cxt_local = clone_cxt(&cxt);
                self.machine.infer_decl(b, &mut cxt_local, d)?
            };
            cxt = unsafe { std::mem::transmute::<Cxt<'_>, Cxt<'static>>(nc) };
            if prelude.nat_after.contains(&i) {
                let nc = {
                    let b: &Bump = &self.bump;
                    self.machine.register_nat_builtins(b, &cxt)
                };
                cxt = unsafe { std::mem::transmute::<Cxt<'_>, Cxt<'static>>(nc) };
            }
            if file_i < prelude.file_ends.len() && prelude.file_ends[file_i] == i {
                force_memo_clear();
                if compact::compact_enabled() {
                    // 就地压实：arena 只承载可达状态，峰值 RSS 不随装载累积。
                    let (nc, live) = self.compact_state(cxt, cap_hint);
                    cxt = nc;
                    cap_hint = (live + live / 8 + (1 << 20)).max(8 << 20);
                }
                if twin_mem_prof() {
                    eprintln!(
                        "[TMEM] after file {file_i}: decl i={i} cap={} MB",
                        self.bump.allocated_bytes() >> 20
                    );
                }
                file_i += 1;
            }
        }
        self.machine.observe = true;
        let nc = {
            let b: &Bump = &self.bump;
            self.machine.register_vconn_builtin(b, &cxt)
        };
        cxt = unsafe { std::mem::transmute::<Cxt<'_>, Cxt<'static>>(nc) };
        cxt = insert_prelude_aliases(cxt);
        {
            let mut m = self.machine.mutable.borrow_mut();
            // 会话级全局复位（参考版 `clone_prelude_state` 逐字：装载期由
            // 声明处 check 求值写脏的这些键，每次 run 从空基线重来，由
            // prelude 自身的 `change_mutable_default` 再播种）。孪生此前只
            // 复位 HdlLoopIdx——残留的 ModuleTree 等会让模块 close-check
            // 看到脏树：13-adder-tree 实测**漏报** HDL001/HDL002 警告。
            for k in ["WhenStack", "ModuleTree", "CombCtx", "ModulePortTable"] {
                m.map.remove(k);
            }
            let b: &Bump = &self.bump;
            m.map.insert(
                SmolStr::new("HdlLoopIdx"),
                v_xcell(b.alloc(XCell::Decl {
                    name: b.alloc_str("hdlLoopIdxEmpty"),
                })),
            );
        }
        self.machine.clear_observation_tables();
        // 归还档：prime 段 observe=false 表不该有条目，但前一会话遗留的
        // 峰值容量（≥OBS_TBL_SHRINK_MIN_ENTRIES）在此随固化检查点一并归还。
        self.machine.reclaim_observation_tables();
        // 收尾压实：把最后一个文件遗留的垃圾一并丢掉（若文件边界已压过，
        // 这里只处理尾巴；`compact_enabled` 关时跳过）。
        if compact::compact_enabled() {
            let (nc, live) = self.compact_state(cxt, cap_hint);
            cxt = nc;
            if twin_mem_prof() {
                eprintln!("[TMEM] final compact: live={} MB cap={} MB", live >> 20, self.bump.allocated_bytes() >> 20);
            }
        }
        // 固化检查点（bump 自此常驻不 reset，句柄地址稳定）。
        let base_keys = cxt.decls.keys().cloned().collect();
        self.resident = Some(Resident {
            cxt,
            defs_len: self.machine.defs.len(),
            base_bytes: self.bump.allocated_bytes(),
            cap_hint,
            base_keys,
            metas: self.machine.metas.clone(),
            tstate: self.machine.tstate.clone(),
            mutable: self.machine.mutable.borrow().clone(),
            symbol_table: self.machine.symbol_table.clone(),
            import_map: self.machine.import_map.clone(),
            trait_method_cache: self.machine.trait_method_cache.clone(),
            tm_import: self.machine.tm_import.clone(),
            val_import: self.machine.val_import.clone(),
        });
        Ok(())
    }

    /// Refresh the resident checkpoint **without replaying the prelude**.
    ///
    /// The user segment's intermediate values are unreclaimable bump garbage
    /// (journal rollback restores table entries, not arena bytes), so after
    /// enough kicks `resident_user_bytes` crosses [`RESIDENT_BUMP_LIMIT`].
    /// Replaying the whole prelude to reset the arena costs ~3 s; instead,
    /// deep-copy the — already rolled back — checkpoint state into a fresh
    /// arena (the same [`Tycker::compact_state`] prime uses at file
    /// boundaries) and re-pin `Resident` to it.  Cost is O(live state)
    /// (~tens of ms) rather than O(prelude).
    ///
    /// `compact_state` copies `metas`/`defs`/`spine` **order-preservingly**,
    /// so every index-valued handle stays valid: tag-2 spine handles, tag-5
    /// meta handles and `trait_metas`' meta indices.  The owned / reference-
    /// domain tables (`tstate`, `symbol_table`, `import_map`,
    /// `trait_method_cache`) carry no arena pointers and are re-snapshotted
    /// from the (unchanged) machine; `tm_import`/`val_import` are remapped by
    /// the copier.
    fn compact_resident(&mut self) {
        let Some(r) = self.resident.take() else { return };
        RESIDENT_COMPACTIONS.with(|c| c.set(c.get() + 1));
        // Stable capacity hint from prime's measured live state; the checkpoint
        // footprint does not grow with kicks (user state is rolled back).
        let cap_hint = r.cap_hint;
        let cxt = clone_cxt(&r.cxt);
        let cxt = {
            let (cxt, _live) = self.compact_state(cxt, cap_hint);
            cxt
        };
        // The force memo is keyed by packed `V` words (arena addresses) and
        // holds `V` results: after the arena swap both are dangling, and a
        // recycled address would even produce a false hit.  Prime does the
        // same clear before its file-boundary compactions; the unify
        // scratch/rename buffers hold `V`s too, so drop their contents as
        // well (all are entry-cleared scratch by contract).
        force_memo_clear();
        twin_stat_record(&TWIN_STAT_CONV, self.machine.conv.memo.reclaim(CACHE_SHRINK_MIN_ENTRIES));
        let _ = self.machine.conv.scratch1.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        let _ = self.machine.conv.scratch2.reclaim(SPINE_SHRINK_MIN_ENTRIES);
        self.machine.ren.reset();
        // Pointer-keyed caches into the old arena are stale after the swap;
        // they are pure caches, so dropping them is semantically neutral.
        self.machine.ns_method_cache = None;
        self.resident = Some(Resident {
            cxt,
            defs_len: r.defs_len,
            base_bytes: self.bump.allocated_bytes(),
            cap_hint,
            base_keys: r.base_keys,
            metas: self.machine.metas.clone(),
            tstate: self.machine.tstate.clone(),
            mutable: self.machine.mutable.borrow().clone(),
            symbol_table: self.machine.symbol_table.clone(),
            import_map: self.machine.import_map.clone(),
            trait_method_cache: self.machine.trait_method_cache.clone(),
            tm_import: self.machine.tm_import.clone(),
            val_import: self.machine.val_import.clone(),
        });
    }

    /// **阶段 3b 常驻用户段**：从检查点恢复 machine 稳态，用常驻 prelude
    /// 上下文推进 `user_ast`，观察三表落 `machine`（调用方经
    /// [`Tycker::hover_table`] 等读取）。用户段 bump 垃圾超
    /// [`RESIDENT_BUMP_LIMIT`] 时 [`Tycker::compact_resident`] 就地压实检查点。
    ///
    /// **错误不早退**：单 decl 失败记入 [`Tycker::user_errors`] 并跳过该
    /// decl 的 cxt 推进（参考版 `elaborate` 逐 decl `err_collect` 同口径），
    /// 这样后续 decl 仍被检查、诊断能列全。只有 prelude prime 失败才是
    /// `Err`（调用方据此降级）。
    pub(crate) fn observe_user(
        &mut self,
        prelude: &super::PreludeParse,
        user_ast: &[Decl],
    ) -> Result<(), Error> {
        self.user_errors.clear();
        let kick_t0 = if std::env::var_os("TYPORT_KICK_PROBE").is_some() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        let over = match &self.resident {
            Some(r) => {
                let budget = RESIDENT_BUMP_BUDGET.with(|c| c.get());
                self.bump.allocated_bytes().saturating_sub(r.base_bytes) > budget
            }
            None => true,
        };
        if over {
            if self.resident.is_some() && compact::compact_enabled() {
                // Arena full of user-segment garbage: refresh the checkpoint
                // in place instead of replaying the prelude (see
                // `compact_resident`).  `prime_resident` only on a cold start.
                self.compact_resident();
            } else {
                self.prime_resident(prelude)?;
            }
        }
        let r = self.resident.as_ref().expect("resident just primed");
        // 恢复稳态：defs 截回 prelude 长度（用户段 append-only），scratch
        // 栈清空。七表（tstate/mutable/symbol_table/import_map/
        // trait_method_cache/tm_import/val_import）不再整克隆恢复（评审
        // B#2 一期 metas / 二期七表）：kick 开撤销帧，写点经 journal 记
        // (key, 旧值)，kick 末逆序撤销——起点即 checkpoint 形态（上一
        // kick 末已回滚），与本轮写点集合无关地逐键还原。
        self.machine.defs.truncate(r.defs_len);
        // 上一 kick 的槽位（tag-2 句柄）在轮界后无任何持有者，容量到阈值
        // 时归还缓冲不影响地址语义（`SPINE_SHRINK_MIN_ENTRIES`）。
        twin_stat_record(
            &TWIN_STAT_SPINE,
            self.machine.spine.stack.reclaim(SPINE_SHRINK_MIN_ENTRIES),
        );
        self.machine.vals.clear();
        self.machine.icits.clear();
        self.machine.constraints.clear();
        self.machine.clear_observation_tables();
        // 归还档（LSP 每 kick 界）：上一 kick 用户段撑大的观察表容量
        // （大文件 10³ 级条目 × 32–40B 槽）不再跨 kick 常驻。
        self.machine.reclaim_observation_tables();
        let pre_meta_len = self.machine.metas.len();
        // `trait_metas` is append-only (meta indices, order-preserving with
        // `metas`) and NOT covered by the seven-table journal — without this
        // truncation it grows ~hundreds of entries per kick forever, and every
        // `solve_multi_trait` clones the whole vec.
        let pre_trait_metas_len = self.machine.trait_metas.len();
        META_JOURNAL.with(|j| j.borrow_mut().push(Vec::new()));
        // 七表撤销帧（评审 B#2 二期）：随后的 symbol_table/import_map/
        // trait_method_cache/tm_import/val_import/mutable(t)/tstate 写点
        // 全部经 state_journal_record 记账。
        state_journal_open_frame();
        let restore_done = kick_t0.map(|t| std::time::Instant::now());
        // 常驻基线（prelude）键集——prime 时预计算，每 kick 只读借用。
        let base_keys = &r.base_keys;
        let bump = &self.bump;
        let mut cxt = clone_cxt(&r.cxt);
        let mut sink = String::new();
        let decl_probe = std::env::var_os("TYPORT_DECL_PROBE").is_some();
        for (i, d) in user_ast.iter().enumerate() {
            let m0 = self.machine.metas.len();
            match Self::step_round_decl(&mut self.machine, bump, &mut cxt, d, i, &[], &mut sink) {
                Ok(nc) => cxt = nc,
                // Keep the previous cxt for subsequent decls (reference
                // `elaborate` keeps `local_cxt` on error).
                Err(e) => self.user_errors.push(e),
            }
            if decl_probe {
                eprintln!("[DECL{}] metas+{}", i, self.machine.metas.len() - m0);
            }
        }
        // 本轮新增的用户声明名（相对 prelude 基线）。
        let user_keys: Vec<SmolStr> = cxt
            .decls
            .keys()
            .filter(|k| !base_keys.contains(*k))
            .cloned()
            .collect();
        // 导出成参考域 Decl 行（`.3` 读类型项——pretty_sum_definition 的
        // 构造子/方法签名渲染需要它，必须真实导出而非占位）。
        let mut exports: Vec<(SmolStr, super::ExportedDecl)> = Vec::with_capacity(user_keys.len());
        for k in &user_keys {
            let Some(e) = cxt.decls.get(k) else { continue };
            if e.prim.is_some() {
                continue;
            }
            let tm_rc = export(&self.machine.symbol_table, e.tm);
            let val_rc = v_to_ref_val(&self.machine.spine, &self.machine.defs, e.val);
            // `.3` 是类型**项**（参考版行的 a_quote），非引出的类型值——
            // pretty_sum_definition 靠它渲染构造子签名。
            let ty_rc = export(&self.machine.symbol_table, e.ty);
            let vty_rc = v_to_ref_val(&self.machine.spine, &self.machine.defs, e.vty);
            let typ_pretty = e.typ_pretty.as_ref().map(|s| (**s).clone()).unwrap_or_default();
            exports.push((k.clone(), super::ExportedDecl {
                span: e.span,
                tm: tm_rc,
                val: val_rc,
                ty: ty_rc,
                vty: vty_rc,
                typ_pretty,
            }));
        }
        self.user_decl_exports = exports;
        // 回滚前记录本轮 net meta 创建量（18-utils 分叉对照信号）。
        self.last_kick_metas_created = self.machine.metas.len() - pre_meta_len;
        // kick 末：撤销本 kick 的 meta 就地写与新增（journal 帧回滚）+ 七表
        // 写点逆序撤销（评审 B#2 二期）——下 kick 起点的整表恢复由此免除。
        // 导出数据已深快照成 owned Rc，不受回滚影响。
        meta_journal_rollback(&mut self.machine.metas, pre_meta_len);
        self.machine.trait_metas.truncate(pre_trait_metas_len);
        state_journal_rollback(&mut self.machine);
        // 撤销后自检（TYPORT_KICK_PROBE 门控）：七表逐键回到 checkpoint
        // 形态。可全等比较的表做整表全等；值无 PartialEq 的表（Rc/AST 型）
        // 按键做指针全等（journal 撤销恢复的就是 checkpoint 条目本身，
        // 指针全等是真全等）；tstate 桶型（definition/instances 等）查
        // 键集/长度守恒 + 桶长守恒。防「漏埋写点」回归。
        if std::env::var_os("TYPORT_KICK_PROBE").is_some() {
            let mu = self.machine.mutable.borrow();
            assert!(self.machine.symbol_table == r.symbol_table, "symbol_table undo");
            assert!(self.machine.import_map == r.import_map, "import_map undo");
            assert!(mu.map == r.mutable.map, "mutable.map undo");
            assert!(mu.replay == r.mutable.replay, "mutable.replay undo");
            assert!(mu.check_lines == r.mutable.check_lines, "check_lines undo");
            assert!(mu.check_line_set == r.mutable.check_line_set, "check_line_set undo");
            assert!(mu.check_seen == r.mutable.check_seen, "check_seen undo");
            // 指针导入表：键集 + 值指针全等。
            for (k, v) in &r.tm_import {
                assert_eq!(
                    self.machine.tm_import.get(k).map(|x| *x as *const Tm as usize),
                    Some(*v as *const Tm as usize),
                    "tm_import undo at {k}"
                );
            }
            assert_eq!(self.machine.tm_import.len(), r.tm_import.len(), "tm_import size");
            assert!(self.machine.val_import == r.val_import, "val_import undo");
            // trait 方法缓存：键集 + Rc 指针全等。
            for (k, (a, va, t)) in &r.trait_method_cache {
                match self.machine.trait_method_cache.get(k) {
                    Some((a2, va2, t2)) => {
                        assert!(Rc::ptr_eq(a, a2) && Rc::ptr_eq(va, va2) && Rc::ptr_eq(t, t2),
                            "trait_method_cache undo at {k:?}");
                    }
                    None => panic!("trait_method_cache undo missing {k:?}"),
                }
            }
            assert_eq!(self.machine.trait_method_cache.len(), r.trait_method_cache.len());
            // tstate：可全等的两掩码表全等；桶型表键集 + 桶长守恒。
            assert!(self.machine.tstate.solver.trait_out_params == r.tstate.solver.trait_out_params);
            assert!(self.machine.tstate.out_param == r.tstate.out_param);
            for (k, v) in &r.tstate.solver.class_instances {
                assert_eq!(
                    self.machine.tstate.solver.class_instances.get(k).map(|x| x.len()),
                    Some(v.len()),
                    "class_instances undo at {k}"
                );
            }
            assert_eq!(
                self.machine.tstate.solver.class_instances.len(),
                r.tstate.solver.class_instances.len()
            );
            for (k, v) in &r.tstate.solver.head_index {
                assert_eq!(
                    self.machine.tstate.solver.head_index.get(k).map(|x| x.len()),
                    Some(v.len()),
                    "head_index undo at {k:?}"
                );
            }
            assert_eq!(self.machine.tstate.solver.head_index.len(), r.tstate.solver.head_index.len());
            for k in r.tstate.definition.keys() {
                assert!(self.machine.tstate.definition.contains_key(k), "definition undo at {k}");
            }
            if self.machine.tstate.definition.len() != r.tstate.definition.len() {
                let extra: Vec<&SmolStr> = self
                    .machine
                    .tstate
                    .definition
                    .keys()
                    .filter(|k| !r.tstate.definition.contains_key(*k))
                    .collect();
                panic!("definition undo: machine={} checkpoint={} extra={extra:?}",
                    self.machine.tstate.definition.len(), r.tstate.definition.len());
            }
            for k in r.tstate.assoc_defaults.keys() {
                assert!(
                    self.machine.tstate.assoc_defaults.contains_key(k),
                    "assoc_defaults undo at {k:?}"
                );
            }
            assert_eq!(self.machine.tstate.assoc_defaults.len(), r.tstate.assoc_defaults.len());
        }
        if let (Some(t0), Some(t_restore)) = (kick_t0, restore_done) {
            // µs 精度（评审 B#2 二期基线：七表克隆恢复在毫秒取整下不可见）。
            eprintln!(
                "[KICK_PROBE] restore(clones)={:.1}ms loop+export={:.1}ms",
                t_restore.duration_since(t0).as_secs_f64() * 1e3,
                t_restore.elapsed().as_secs_f64() * 1e3,
            );
        }
        Ok(())
    }

    /// 本轮用户段的 println 输出（span + 渲染串）——孪生 INFORMATION 诊断。
    pub(crate) fn println_spans(&self) -> &[(crate::parser_lib::Span<()>, String)] {
        &self.machine.println_spans
    }

    /// 本轮用户段的 HDL 自检警告行（decl 下标 + 原始行）——孪生 WARNING 诊断。
    pub(crate) fn check_issue_lines(&self) -> &[(usize, String)] {
        &self.machine.check_issue_lines
    }

    /// 常驻 bump 自检查点以来的用户段增长字节数（内存上界诊断/测试用）。
    pub(crate) fn resident_user_bytes(&self) -> usize {
        match &self.resident {
            Some(r) => self.bump.allocated_bytes().saturating_sub(r.base_bytes),
            None => 0,
        }
    }

    // ── 观察面访问器（`run_decls*` 返回后读取本轮快照；契约与参考版 `Infer`
    // 的三张表逐字段同型，接线时消费端可按同一套逻辑处理两引擎）──
    pub(crate) fn hover_table(&self) -> &[(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)] {
        &self.machine.hover_table
    }
    pub(crate) fn completion_table(&self) -> &[(crate::parser_lib::Span<()>, SmolStr)] {
        &self.machine.completion_table
    }
    pub(crate) fn inlay_hint_table(&self) -> &[(u32, String)] {
        &self.machine.inlay_hint_table
    }
    pub(crate) fn hover_entry_at(
        &self,
        path_id: u32,
        offset: usize,
    ) -> Option<&(crate::parser_lib::Span<()>, crate::parser_lib::Span<()>, String)> {
        self.machine.hover_entry_at(path_id, offset)
    }

    /// 参考版 `run` 的等价物：preprocess + parse 由调用方完成（与参考版
    /// 共用 parser；参考版对 parse 失败 unwrap panic、对 parse 错误只
    /// 打印后继续——快版同口径：None panic、错误静默），本方法做轮重置 +
    /// builtin 重注册 + 逐 decl 推断，println 的 nf 经 pretty 输出（quote
    /// 走记忆化口径——与无记忆化输出逐字节一致，L03-L06 已证）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.run_decls_bounded(ast, &[])
    }

    /// [`Tycker::run_decls`] 的带 nat 注册边界变体：`nat_after` 的下标后注册
    /// nat 内建（镜像参考版按文件边界调用 `register_nat_builtins`）。
    pub(crate) fn run_decls_bounded(
        &mut self,
        ast: &[Decl],
        nat_after: &[usize],
    ) -> Result<String, Error> {
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for (i, d) in ast.iter().enumerate() {
            cxt = Self::step_round_decl(&mut self.machine, bump, &mut cxt, d, i, nat_after, &mut ret)?;
        }
        Ok(ret)
    }

    /// 轮内推进单个 decl：infer + nat 边界 + CheckIssues 逐 decl 排水 +
    /// println 收集（[`Tycker::run_decls_bounded`] 与
    /// [`Tycker::run_decls_with_prelude`] 的用户段共用）。显式取
    /// `&mut Machine`——调用方持有 `&self.bump`，字段不相交方可借用。
    fn step_round_decl<'a>(
        machine: &mut Machine,
        bump: &'a Bump,
        cxt: &mut Cxt<'a>,
        d: &Decl,
        i: usize,
        nat_after: &[usize],
        ret: &mut String,
    ) -> Result<Cxt<'a>, Error> {
        let (out, nc) = machine.infer_decl(bump, cxt, d)?;
        let mut cxt = nc;
        if nat_after.contains(&i) {
            cxt = machine.register_nat_builtins(bump, &cxt);
        }
        // HDL 自检警告：逐 decl 排水（行级去重——参考版
        // take_fresh_check_issues + format_check_warning）。行集缓存版
        // （评审机会 5）：pending 行存 `Mutable.check_lines`（插入序），
        // 已排水行存 `check_seen` 成员集——原版每轮 `seen.clone()` 整串
        // 拷贝 + 每 pending 行 O(S) 线性扫，现 O(1)；输出拼装序
        // （pending 插入序 × seen 首见判定）与原 split 版逐字节一致。
        {
            let mut m = machine.mutable.borrow_mut();
            if !m.check_lines.is_empty() {
                let pending = std::mem::take(&mut m.check_lines);
                // kick 撤销帧记账（评审 B#2 二期）：take+clear 联合撤销
                // （set 与 lines 恒配对，撤销时按 lines 重建）。
                state_journal_record(StateUndo::CheckLinesTake(pending.clone()));
                m.check_line_set.clear();
                for line in &pending {
                    if m.check_seen.insert(line.clone()) {
                        state_journal_record(StateUndo::CheckSeenInsert(line.clone()));
                        *ret += &super::format_check_warning(line);
                        *ret += "\n";
                        // 结构化记录（孪生自产 WARNING 诊断；下标记 decl）
                        if machine.observe {
                            machine.check_issue_lines.push((i, line.to_string()));
                        }
                    }
                }
            }
        }
        if let DeclOut::Println(_, span, out_s) = out {
            // elaboration 期即算好的 pretty 串（参考版 DeclTm::Println）
            if machine.observe {
                machine.println_spans.push((span, out_s.clone()));
            }
            *ret += &out_s;
            *ret += "\n";
        }
        Ok(cxt)
    }

    /// **阶段 2（prelude 装载）整轮入口**：本轮 = prelude 重放 + 用户 decls。
    /// `prelude` 来自共享 `super::parse_prelude_files`（参考版
    /// `load_prelude_state_impl` 同口径的 parse 段）；`prelude.failed`
    /// 非 `None` 时**快速失败**（parse 截断的 prelude 静默重放会以难诊断
    /// 的 infer 错误形式爆在下游）。装载段镜像参考版：逐 decl 推断
    /// （println/排水不收集——参考版加载器丢弃输出同款）、nat 边界注册
    /// nat 内建、每文件边界清 force memo（参考版逐文件清空的内存口径）、
    /// 全部完成后注册 vconnT → 短名别名 or_insert → HdlLoopIdx 复位 →
    /// 清观察表（缓存态不参与 hover/completion）。用户段与
    /// [`Tycker::run_decls_bounded`] 同一推进。
    ///
    /// 每 kick 都从 prime_round 重放整个 prelude（bump 一次性口径）——
    /// 这是接线文档阶段 3a 要实测的 seed 开销基线。
    pub(crate) fn run_decls_with_prelude(
        &mut self,
        prelude: &super::PreludeParse,
        user_ast: &[Decl],
    ) -> Result<String, Error> {
        if let Some(f) = &prelude.failed {
            return Err(Error(
                empty_span(format!("prelude file `{f}` failed to parse")),
                vec![],
            ));
        }
        let prelude_decls: &[Decl] = &prelude.decls;
        let prelude_file_ends: &[usize] = &prelude.file_ends;
        let prelude_nat_after: &[usize] = &prelude.nat_after;
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        // prelude 段关观察面 push（含 decl_reg 的 typ_pretty 渲染）——
        // 装载完即清表，渲染全是死工作；用户段恢复。
        self.machine.observe = false;
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut file_i = 0usize;
        for (i, d) in prelude_decls.iter().enumerate() {
            let (_out, nc) = self.machine.infer_decl(bump, &mut cxt, d)?;
            cxt = nc;
            if prelude_nat_after.contains(&i) {
                cxt = self.machine.register_nat_builtins(bump, &cxt);
            }
            if file_i < prelude_file_ends.len() && prelude_file_ends[file_i] == i {
                force_memo_clear();
                file_i += 1;
            }
        }
        self.machine.observe = true;
        cxt = self.machine.register_vconn_builtin(bump, &cxt);
        cxt = insert_prelude_aliases(cxt);
        {
            let mut m = self.machine.mutable.borrow_mut();
            let b: &Bump = &self.bump;
            m.map.insert(
                SmolStr::new("HdlLoopIdx"),
                v_xcell(b.alloc(XCell::Decl {
                    name: b.alloc_str("hdlLoopIdxEmpty"),
                })),
            );
        }
        self.machine.clear_observation_tables();
        // 归还档：装载收尾同 prime_resident（前次会话遗留容量一并归还）。
        self.machine.reclaim_observation_tables();
        let mut ret = String::new();
        for (i, d) in user_ast.iter().enumerate() {
            cxt = Self::step_round_decl(&mut self.machine, bump, &mut cxt, d, i, &[], &mut ret)?;
        }
        Ok(ret)
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        let (ast, _parse_errs) = match super::parser::parser(&super::preprocess(input), path_id) {
            Some(x) => x,
            // 参考版 run 对 parse 失败 unwrap panic——同款
            None => panic!("parse failed"),
        };
        self.run_decls(&ast)
    }

    /// 基准口径（bench 用）：仅 elaborate。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 的登记值空层级引读，与参考版
    /// `bench_check_nf` 同口径——quote 无记忆化），返回结果树节点数。
    pub(crate) fn bench_check_nf(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, true)
    }

    fn bench_nf_impl(&mut self, ast: &[Decl], use_memo: bool) -> u64 {
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        let (r, _cxt, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some(v) = last else {
            return 0;
        };
        let q = if use_memo {
            self.machine.quote_memo(bump, &_cxt, 0, v)
        } else {
            self.machine.quote(bump, &_cxt, 0, v)
        };
        tm_size(q)
    }

    /// 带 nat 注册边界的 check+nf 口径（bench 用）：与 [`Tycker::bench_check_nf`]
    /// 同，但在 `nat_after` 的下标后注册 nat 内建（镜像参考版按文件边界调用
    /// `register_nat_builtins`）。多文件 prelude 拼成单一 decl 序列时用。
    pub(crate) fn bench_check_nf_bounded(&mut self, ast: &[Decl], nat_after: &[usize]) -> u64 {
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        // 实验 口径开关（L13BENCH_NOBSERVE=1 时关观察面渲染，量化 observe
        // 成本占比；仅实验用，落地后删除）
        if std::env::var_os("L13BENCH_NOBSERVE").is_some() {
            self.machine.observe = false;
        }
        let bump = &self.bump;
        let mut cxt =  self.machine.prime_round(bump);
        let mut last: Option<V> = None;
        for (i, d) in ast.iter().enumerate() {
            match  self.machine.infer_decl(bump, &mut cxt, d) {
                Ok((out, nc)) => {
                    cxt = nc;
                    if nat_after.contains(&i) {
                        cxt = self.machine.register_nat_builtins(bump, &cxt);
                    }
                    if let DeclOut::Def { name } = out {
                        last = cxt.decls.get(name).map(|e| e.val);
                    }
                }
                Err(_) => return 0,
            }
        }
        let Some(v) = last else {
            return 0;
        };
        let q =  self.machine.quote(bump, &cxt, 0, v);
        let r = tm_size(q);
        r
    }

    /// [`Tycker::bench_check_nf_bounded`] 的**内容**变体：回末 def 值的 pretty
    /// 串而非节点数（参考版 `bench_check_nf_pretty_bounded` 的对位）。互检只报
    /// 尺寸时，`NF-DIVERGE basic=26307 fast=26357` 说不出差异在哪；本变体让
    /// `l13bench --file` 能把两边的范式直接 diff。`Err` 回 `None`。
    pub(crate) fn bench_check_nf_pretty_bounded(
        &mut self,
        ast: &[Decl],
        nat_after: &[usize],
    ) -> Option<String> {
        self.bump.reset();
        self.resident = None;
        self.machine.clear_round();
        force_memo_clear();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut last: Option<V> = None;
        for (i, d) in ast.iter().enumerate() {
            match self.machine.infer_decl(bump, &mut cxt, d) {
                Ok((out, nc)) => {
                    cxt = nc;
                    if nat_after.contains(&i) {
                        cxt = self.machine.register_nat_builtins(bump, &cxt);
                    }
                    if let DeclOut::Def { name } = out {
                        last = cxt.decls.get(name).map(|e| e.val);
                    }
                }
                Err(_) => return None,
            }
        }
        let v = last?;
        let q = self.machine.quote(bump, &cxt, 0, v);
        let e = export(&self.machine.symbol_table, q);
        let names = types_names_list(cxt.types);
        Some(super::pretty::pretty_tm(0, names, &e).to_string())
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

/// 测试/基准辅助：共用参考版 parser（fast 是 L09_mltt 的子模块，可见
/// 私有 parser；产出的 `Decl` 同时喂参考版与快版的 bench 口径）。
pub(crate) fn parse(input: &str, path_id: u32) -> Result<Vec<Decl>, String> {
    match super::parser::parser(&super::preprocess(input), path_id) {
        Some((ast, _errs)) => Ok(ast),
        None => Err("parse failed".to_owned()),
    }
}

/// 解析产出的 decl AST 类型别名（测试/基准用；Decl 本身的 use 是私有的）。
pub(crate) type SourceDecl = Decl;
