//! Level A 终止性检查（docs/l13-quirks-analysis-2026-10.md §4.3 档 A）。
//! 挂载点：machine.rs Def 臂 `check` 之后、`wrap_match_in_call` 之前。
//! 语言无互递归（前向引用 not in scope）⇒ 单 def 自调用分析覆盖全部递归。
//!
//! 判据（启发式，**不健全**）：对 elaborated 体里每个自调用 `f a1..an`
//! （App-spine 头 = `Decl(自身键)`），要求至少一个实参是「结构位置模式变
//! 量」——即某 match 的模式变量，且该 match 的 scrutinee 链（Var / `x.field`
//! 投影）下落到 def 参数或（传递地）另一个结构位置模式变量；实参允许是
//! 这类模式变量的**构造器应用**（`ofNat b` / `negSucc a`——int_add/int_mul
//! 需要；构造器 = decl 表里 tm 为 λ*→SumCase 的条目，隐式实参是类型/字
//! 典不参与判定）。裸自引用（零参 def 的 `def p = p`、把自身当值传）无递
//! 减实参 ⇒ 拒绝。
//!
//! 已知放行（钉在 termination_check_tests）：
//! - ping-pong 换参 `weird b k`：k 是模式变量即放行（Level A 口径，文档
//!   化不健全；实测该形态按 (a+b) 递减本身也终止）；
//! - 构造器包裹可增 `bad (succ k)`；
//! - 方法自调用经 `Obj` 派发（`ys.insert x p`），头不是 Decl-spine，不在
//!   判定内。
//!
//! 成本 O(|body|)/def，不触 unify/eval 热路径。参考版逐句对齐在
//! elaboration.rs `check_def_termination`（两版 Tm 表示不同：本版 bump
//! `&Tm` de Bruijn，参考版 `Rc<Tm>` Ix；判据/注释同构，改动须成对）。

use crate::L13_namespace::parser::syntax::Icit;

use super::prim::Decls;
use super::syntax::{PrCons, Tm};

/// 引擎侧 allowlist（**临时**，直到声明级 opt-out 语法落地——§4.4 第 3 步；
/// 语法落地后清空本表）。全部是「真非结构递归且 load-bearing」的定义：
/// - `nat_div` / `nat_rem`：nat.typort 重复减法回退实现，递归实参是 let
///   计算值 `nat_sub x y`（非模式变量）；nat 内建注册后被 primop 覆盖。
/// - `combReach`：hdl-check-graph 组合环 worklist，frontier/visited 是
///   `strAppend` 累加的计算值。
/// - `gcd`：examples/typeclass_complex.typort 欧几里得（`gcd(b, a)` 换参、
///   `nat_sub_safe(a, b)` 计算值）；examples 全树经 twin_engine_tests 双
///   引擎过 elaboration，不在表内即误杀。
/// - `log2Up`：hdl-core.typort 折半度量（`div2Up (tail + 2)` 计算值实参，
///   度量对半递减非语法可见）。
/// - `metaDiv`：hdl-utils.typort 重复减法（`succ (metaDiv sub y)`，sub 是
///   let 计算值）——nat_div 同形，正确版除法。
/// - `countOnesExprAt`：hdl-utils.typort 位宽对半拆分（lo_w/hi_w 来自
///   match+计算的宽度分裂，度量对半递减）。
/// - `designVisit`：hdl-verilog.typort worklist（seen/queue/acc 累加计算
///   值）——combReach 同族。
/// - `bbParamsDeclStr` / `bbInstItemsStr`：hdl-macros.typort，scrutinee 是
///   `list_reverse(gs)` 计算值（保长度变换，tail 结构递减非语法可见）。
/// - `NonEmpty.last`：nonempty.typort 方法自递归，实参 `new NonEmpty(x, xs)`
///   是 struct 构造器包裹两个模式变量——walker 的 is_ctor 只认 SumCase
///   注册形状，struct mk 形状待精化（TODO：is_ctor 纳入 struct 单 case）。
const ALLOWLIST: &[&str] = &[
    "nat_div", "nat_rem", "combReach", "gcd", "log2Up",
    "metaDiv", "countOnesExprAt", "designVisit",
    "bbParamsDeclStr", "bbInstItemsStr", "NonEmpty.last",
    "adder_tree",
];

/// 走查器：decl 表（构造器判定）+ 自身限定键 + 模式变量层标记。
/// 层（level）= 从体根起跨过的 binder 数（参数 λ 链占 0..k-1）；层 L 处
/// `Var(i)` 指 L-1-i。两套判定严格分开：
/// - **scrutinee 链**：match 的 scrutinee 链（Var / `x.field`）根落在
///   「def 参数（层 < k）或已标模式变量层」上 ⇒ 该 match 结构化，其全 arm
///   的模式变量层（L..L+bind_count-1）续标（传递闭包：模式变量再作
///   scrutinee 的 match 同样下落到参数）；
/// - **递减实参**：`Var` 必须是**已标模式变量层**——参数本身不算（`bad x`
///   的 x 是参数非模式变量，须拒），零层构造器常量也不算。
/// 多 arm 层号重叠无害：arm 体只能引用低于自身起点的层，重叠层在该 arm
/// 视角即本 arm 自己的模式变量，同属这个（已验结构性的）match。
struct Walker<'a> {
    decls: &'a Decls<'a>,
    self_key: &'a str,
    /// def 参数个数（参数占层 0..k-1，只参与 scrutinee 链判定）。
    n_params: u32,
    /// 结构位置模式变量层标记（单调增长；只参与递减实参判定）。
    pat_marks: Vec<bool>,
}

/// Level A 检查：`Err(())` = 存在无法证明终止的自调用（调用方渲染 decl 错
/// 误；错误恢复按既有失败 decl 通道自动生效——占位回滚 / 下游引用降噪）。
pub(super) fn check_def_termination<'a>(
    decls: &Decls<'a>,
    self_key: &str,
    n_params: usize,
    body: &Tm<'a>,
) -> Result<(), ()> {
    if ALLOWLIST.contains(&self_key) {
        return Ok(());
    }
    let mut w = Walker {
        decls,
        self_key,
        n_params: n_params as u32,
        pat_marks: Vec::new(),
    };
    w.walk(body, 0)
}

impl<'a> Walker<'a> {
    /// scrutinee 链根是否结构化：def 参数层或已标模式变量层。
    fn scrut_marked(&self, lvl: u32) -> bool {
        lvl < self.n_params || self.pat_marked(lvl)
    }

    fn pat_marked(&self, lvl: u32) -> bool {
        (lvl as usize) < self.pat_marks.len() && self.pat_marks[lvl as usize]
    }

    fn pat_mark(&mut self, lvl: u32) {
        let i = lvl as usize;
        if i >= self.pat_marks.len() {
            self.pat_marks.resize(i + 1, false);
        }
        self.pat_marks[i] = true;
    }

    /// scrutinee 链：`Var` → 层号；`Obj(h, _)` 投影跟头；**构造器应用**
    ///（含元组 `(a, b)`——TupleN.mk 的 App-spine）当全部显式实参自身是
    /// 链根时视为链根（层号取首个实参的——只用于 structural 判定，元组
    /// match 的臂模式变量按既有口径全标）；其余（计算值 / 嵌套 match /
    /// let）不算下落到参数（保守拒绝 ⇒ 走 allowlist 口径）。
    /// 与参考版 elaboration.rs TermWalker::chain_level 逐句对齐。
    fn chain_level(&self, t: &Tm<'a>, lvl: u32) -> Option<u32> {
        match t {
            Tm::Var(i) if *i < lvl => Some(lvl - 1 - *i),
            Tm::Obj(h, _) => self.chain_level(h, lvl),
            Tm::App(..) => {
                let mut args: Vec<&Tm<'a>> = Vec::new();
                let mut cur = t;
                while let Tm::App(f, a, i) = cur {
                    if matches!(i, Icit::Expl) {
                        args.push(a);
                    }
                    cur = f;
                }
                match cur {
                    Tm::Decl(h) if self.is_ctor(h) => {
                        let mut first: Option<u32> = None;
                        for a in args {
                            match self.chain_level(a, lvl) {
                                Some(l) => {
                                    if first.is_none() {
                                        first = Some(l);
                                    }
                                }
                                None => return None,
                            }
                        }
                        first
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// decl 表构造器判定：tm 为 λ*→SumCase（enum 臂登记构造子的形状；prim
    /// 条目——nat 内建换装的 nat_div 等——不算）。
    fn is_ctor(&self, key: &str) -> bool {
        match self.decls.get(key) {
            Some(e) if e.prim.is_none() => {
                let mut t = e.tm;
                while let Tm::Lam(_, _, b) = t {
                    t = b;
                }
                matches!(t, Tm::SumCase { .. })
            }
            _ => false,
        }
    }

    /// 实参是否「结构递减候选」：模式变量（已标层，参数不算）/ 构造器应
    /// 用（SumCase 或 Decl 头 App-spine；显式字段全为候选，空字段集的常
    /// 量构造子不算——无模式变量即无结构证据）。
    fn smaller_arg(&self, t: &Tm<'a>, lvl: u32) -> bool {
        match t {
            Tm::Var(i) => *i < lvl && self.pat_marked(lvl - 1 - *i),
            Tm::SumCase { datas, .. } => {
                !datas.is_empty() && datas.iter().all(|d| self.smaller_arg(d.val, lvl))
            }
            Tm::App(..) => {
                let mut args: Vec<(&Tm<'a>, Icit)> = Vec::new();
                let mut cur = t;
                while let Tm::App(f, a, i) = cur {
                    args.push((a, *i));
                    cur = f;
                }
                match cur {
                    Tm::Decl(h) if self.is_ctor(h) => {
                        let expl: Vec<&Tm<'a>> = args
                            .iter()
                            .filter(|(_, i)| matches!(i, Icit::Expl))
                            .map(|(a, _)| *a)
                            .collect();
                        !expl.is_empty() && expl.iter().all(|a| self.smaller_arg(a, lvl))
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// 显式栈走查（同 `has_free_var` 的纪律，免深体递归栈）。Match 先验链
    /// 标记再入 arm（标记沿包含关系自上而下传播，兄弟子树互不污染）；自
    /// 调用 spine 判定后实参照常入栈（嵌套自调用逐个受检）。
    fn walk(&mut self, t: &Tm<'a>, lvl: u32) -> Result<(), ()> {
        let mut stack: Vec<(&Tm<'a>, u32)> = vec![(t, lvl)];
        while let Some((t, l)) = stack.pop() {
            match t {
                Tm::Var(_) | Tm::U(_) | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_) => {}
                Tm::Decl(s) => {
                    if *s == self.self_key {
                        // 裸自引用：零参自调用或把自身当值传——无递减实参。
                        return Err(());
                    }
                }
                Tm::Lam(_, _, b) => stack.push((b, l + 1)),
                Tm::Pi(_, _, a, b) => {
                    stack.push((a, l));
                    stack.push((b, l + 1));
                }
                Tm::Let(_, ty, v, u) => {
                    stack.push((ty, l));
                    stack.push((v, l));
                    stack.push((u, l + 1));
                }
                Tm::Obj(h, _) => stack.push((h, l)),
                Tm::AppPruning(h, pr) => {
                    // 掩码链 = 插入的 λ 槽（含 define 槽），每槽一层 binder
                    // （`binder_occurs` 同款）。
                    let mut slots = 0u32;
                    let mut cur: Option<&PrCons<'a>> = *pr;
                    while let Some(node) = cur {
                        slots += 1;
                        cur = node.next;
                    }
                    stack.push((h, l + slots));
                }
                Tm::Sum(_, params, ..) => {
                    for (k, p) in params.iter().enumerate() {
                        stack.push((p.ty, l + k as u32));
                        stack.push((p.val, l + k as u32));
                    }
                }
                Tm::SumCase { typ, datas, .. } => {
                    stack.push((typ, l));
                    for d in datas.iter() {
                        stack.push((d.val, l));
                    }
                }
                Tm::Match(scrut, cases) => {
                    if let Some(root) = self.chain_level(scrut, l) {
                        if self.scrut_marked(root) {
                            for (pat, _) in cases.iter() {
                                let b = pat.bind_count();
                                for k in 0..b {
                                    self.pat_mark(l + k);
                                }
                            }
                        }
                    }
                    stack.push((scrut, l));
                    for (pat, body) in cases.iter() {
                        stack.push((body, l + pat.bind_count()));
                    }
                }
                Tm::Call(_, args, body) => {
                    // wrap 前不可能出现（Call 只由 wrap_match_in_call 产）；
                    // 防御性走查实参与体（真出现宁可误拒也不静默漏检）。
                    for (a, _) in args.iter() {
                        stack.push((a, l));
                    }
                    stack.push((body, l));
                }
                Tm::App(..) => {
                    let mut args: Vec<(&Tm<'a>, Icit)> = Vec::new();
                    let mut cur = t;
                    while let Tm::App(f, a, i) = cur {
                        args.push((a, *i));
                        cur = f;
                    }
                    if let Tm::Decl(s) = cur {
                        if *s == self.self_key {
                            if !args.iter().any(|(a, _)| self.smaller_arg(a, l)) {
                                return Err(());
                            }
                            for (a, _) in args {
                                stack.push((a, l));
                            }
                            continue;
                        }
                    }
                    stack.push((cur, l));
                    for (a, _) in args {
                        stack.push((a, l));
                    }
                }
            }
        }
        Ok(())
    }
}
