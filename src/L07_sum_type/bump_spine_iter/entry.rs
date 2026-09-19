//! entry：对外入口——`export`（bump 项 → 参考 Box 树）、`tm_size`、
//! 稳态检查器 `Tycker`（run_decls/run_input/bench 口径）、`run_fast`/
//! `parse`/`SourceDecl`，以及内嵌回归测试 `deep_value_tests`。
//! 原 bump_spine_iter.rs 的 "export 与对外入口" 节 + 文件尾测试，逐行
//! 搬运（2026-09-19 拆分）。

use bumpalo::Bump;

use super::parser::syntax::{Decl, Icit};
use super::pretty::pretty_tm;
use super::{empty_span, Error, Ix, MetaVar, PatternDetail};
use crate::L07_sum_type::Tm as CTm;

use super::machine::{types_names_list, DeclOut, Machine};
use super::prim::UNIFY_FUEL;
use super::subst::vsub_reclaim;
use super::syntax::{SumDataT, SumParamT, Tm};

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。L07 新变体的 span 全零（内容即输出）。
pub(super) fn export(t: &Tm<'_>) -> CTm {
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
        },
        SumCase2 {
            case_name: &'a str,
            datas: &'a [SumDataT<'a>],
        },
    }
    fn name(x: &str) -> crate::parser_lib::Span<String> {
        empty_span(x.to_owned())
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<CTm> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(CTm::Var(Ix(*i))),
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
            J::Do(Tm::U) => done.push(CTm::U),
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
            J::Do(Tm::Meta(m)) => done.push(CTm::Meta(MetaVar(*m))),
            J::Do(Tm::LiteralType) => done.push(CTm::LiteralType),
            J::Do(Tm::LiteralIntro(s)) => done.push(CTm::LiteralIntro(name(s))),
            J::Do(Tm::Decl(s)) => done.push(CTm::Decl(smol_str::SmolStr::new(s))),
            J::Do(Tm::Prim(s)) => done.push(CTm::Prim(smol_str::SmolStr::new(s))),
            J::Do(Tm::Obj(h, n)) => {
                tasks.push(J::Obj2(n));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::Sum(nm, params, cases)) => {
                tasks.push(J::Sum2 { name: nm, params, cases });
                for p in params.iter().rev() {
                    tasks.push(J::Do(p.ty));
                    tasks.push(J::Do(p.val));
                }
            }
            J::Do(Tm::SumCase {
                typ,
                case_name,
                datas,
            }) => {
                tasks.push(J::SumCase2 { case_name, datas });
                for d in datas.iter().rev() {
                    tasks.push(J::Do(d.val));
                }
                tasks.push(J::Do(typ));
            }
            J::Do(Tm::Match(s, cases)) => {
                // 分支体逐个内联导出（递归深度 = match 嵌套深度，体本身的
                // 导出仍走任务栈）；模式直接克隆（PatternDetail 是参考版
                // 类型，两版共用）
                let s2 = export(s);
                let mut cs: Vec<(PatternDetail, CTm)> = Vec::with_capacity(cases.len());
                for (p, b) in cases.iter() {
                    cs.push((p.clone(), export(b)));
                }
                done.push(CTm::Match(Box::new(s2), cs));
            }
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(CTm::Lam(name(x), i, Box::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(CTm::Pi(name(x), i, Box::new(dom), Box::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(CTm::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(CTm::App(Box::new(f), Box::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(CTm::AppPruning(Box::new(h), pr));
            }
            J::Obj2(n) => {
                let h = done.pop().expect("export 栈：Obj 缺接收者");
                done.push(CTm::Obj(Box::new(h), name(n)));
            }
            J::Sum2 { name: nm, params, cases } => {
                let mut ps: Vec<(crate::parser_lib::Span<String>, CTm, CTm, Icit)> =
                    Vec::with_capacity(params.len());
                for p in params.iter().rev() {
                    let ty = done.pop().expect("export 栈：Sum 缺参数类型");
                    let val = done.pop().expect("export 栈：Sum 缺参数值");
                    ps.push((name(p.name), val, ty, p.icit));
                }
                ps.reverse();
                let cs: Vec<crate::parser_lib::Span<String>> =
                    cases.iter().map(|c| name(c)).collect();
                done.push(CTm::Sum(name(nm), ps, cs));
            }
            J::SumCase2 { case_name, datas } => {
                let mut ds: Vec<(crate::parser_lib::Span<String>, CTm, Icit)> =
                    Vec::with_capacity(datas.len());
                for d in datas.iter().rev() {
                    let val = done.pop().expect("export 栈：SumCase 缺字段");
                    ds.push((name(d.name), val, d.icit));
                }
                ds.reverse();
                let typ = done.pop().expect("export 栈：SumCase 缺 typ");
                done.push(CTm::SumCase {
                    typ: Box::new(typ),
                    case_name: name(case_name),
                    datas: ds,
                });
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
            Tm::Var(_) | Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Decl(_) | Tm::Prim(_) => {}
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
            Tm::Sum(_, params, _) => {
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
        }
    }
    n
}


/// 稳态类型检查器（同 L03-L06：owns 反复 `reset` 的 `Bump` 与跨调用复用
/// 的 [`Machine`]）。
pub(crate) struct Tycker {
    bump: Bump,
    machine: Machine,
}

impl Tycker {
    pub(crate) fn new() -> Self {
        Tycker {
            bump: Bump::with_capacity(1 << 20),
            machine: Machine::new(),
        }
    }

    /// 参考版 `run` 的等价物：preprocess + parse 由调用方完成（与参考版
    /// 共用 parser），本方法做轮重置 + builtin 重注册 + 逐 decl 推断，
    /// println 的 nf 经 pretty 输出（quote 走记忆化口径——与无记忆化
    /// 输出逐字节一致，L03-L06 已证；L07 新值形态不进 memo 表，口径与
    /// 参考版的全量 quote 一致）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.bump.reset();
        self.machine.clear_round();
        // 轮尾/出错出口都归还本轮 arena 克隆（轮首 clear_round 覆盖不到
        // "最后一轮"——Tycker 长存时其 σ 会挂到进程结束；归还后 arena 内
        // XCell::VSub 的 Rc 悬垂，但本轮出口已无人再读 arena）
        struct ReclaimOnExit;
        impl Drop for ReclaimOnExit {
            fn drop(&mut self) {
                vsub_reclaim();
            }
        }
        let _reclaim = ReclaimOnExit;
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for d in ast {
            let (out, nc) = self.machine.infer_decl(bump, &cxt, d)?;
            cxt = nc;
            if let DeclOut::Println(t) = out {
                let decls = cxt.decl.borrow();
                // nf 入口充值 fuel（参考版 `Infer::nf` 同款）
                self.machine.fuel.set(UNIFY_FUEL);
                let v = self.machine.eval(bump, &decls, cxt.env, t);
                let q = self.machine.quote_memo(bump, &decls, cxt.lvl, v);
                let names = types_names_list(cxt.types);
                ret += &pretty_tm(0, names, &export(q));
                ret += "\n";
            }
        }
        Ok(ret)
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        let ast = super::parser::parser(&super::preprocess(input), path_id).map_err(Error)?;
        self.run_decls(&ast)
    }

    /// 基准口径（bench 用）：仅 elaborate。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 在 decl 表登记的值空层级引读，
    /// 与参考版 `bench_check_nf` 同口径——按名查表、quote 无记忆化），
    /// 返回结果树节点数。
    pub(crate) fn bench_check_nf(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, true)
    }

    fn bench_nf_impl(&mut self, ast: &[Decl], use_memo: bool) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let (r, cxt, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some(name) = last else {
            return 0;
        };
        let Some(entry) = cxt.decl.borrow().get(name).copied() else {
            return 0;
        };
        let q = if use_memo {
            self.machine.quote_memo(bump, &cxt.decl.borrow(), 0, entry.val)
        } else {
            self.machine.quote(bump, &cxt.decl.borrow(), 0, entry.val)
        };
        tm_size(q)
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

/// 测试/基准辅助：共用参考版 parser（fast 是 L07_sum_type 的子模块，可见
/// 私有 parser；产出的 `Decl` 同时喂参考版与快版的 bench 口径）。
pub(crate) fn parse(input: &str, path_id: u32) -> Result<Vec<Decl>, String> {
    super::parser::parser(&super::preprocess(input), path_id)
}

/// 解析产出的 decl AST 类型别名（测试/基准用；Decl 本身的 use 是私有的）。
pub(crate) type SourceDecl = Decl;

#[cfg(test)]
mod deep_value_tests {
    use super::*;
    // 拆分后按路径补引（原单文件内同模块直接可见的跨子系统项）：
    use super::super::force::val_mentions_lvl;
    use super::super::spine::Spine;
    use super::super::struct_eq::struct_val_eq;
    use super::super::subst::{mentions_level, SubstV};
    use super::super::syntax::{SumDataV, V, v_xcell, XCell};

    /// README §7.6 回归钉（孪生）：深值（succ^N 链）上的浅扫描（occurs /
    /// mentions）与结构比较在默认测试栈（约 2 MB）下迭代化（旧递归版
    /// 万级深度爆栈）。bump 内值随 Bump 释放，无深 Drop 之虞。
    #[test]
    fn deep_value_iterative_under_default_stack() {
        fn succ_chain(bump: &Bump, n: usize) -> V {
            let nat = v_xcell(bump.alloc(XCell::Sum {
                name: "Nat",
                params: &[],
                cases: &["zero", "succ"],
            }));
            let mut v = v_xcell(bump.alloc(XCell::SumCase {
                typ: nat,
                case_name: "zero",
                datas: &[],
            }));
            for _ in 0..n {
                v = v_xcell(bump.alloc(XCell::SumCase {
                    typ: nat,
                    case_name: "succ",
                    datas: bump.alloc_slice_fill_iter([SumDataV {
                        name: "x",
                        val: v,
                        icit: Icit::Expl,
                    }]),
                }));
            }
            v
        }

        let bump = Bump::new();
        let spine = Spine { stack: Vec::new() };
        let defs: Vec<V> = Vec::new();
        // ① occurs / mentions：10 万层（无预算遍历，不爆栈）
        let deep = succ_chain(&bump, 100_000);
        assert!(!val_mentions_lvl(&spine, &defs, deep, 1));
        assert!(!mentions_level(&spine, &defs, deep, &SubstV::default()));
        // ② 结构比较：位相等捷径对 tag 7 关闭，逐结构燃烧——2
        // 千层约 6 千 spend < EQ_BUDGET（2 万）判等；10 万层超预算
        // 有界降级 false——两者都不爆栈
        let small = succ_chain(&bump, 2_000);
        assert!(struct_val_eq(&spine, &defs, small, small));
        assert!(!struct_val_eq(&spine, &defs, deep, deep));
    }
}
