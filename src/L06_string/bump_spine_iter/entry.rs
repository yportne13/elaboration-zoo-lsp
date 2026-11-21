//! entry：对外入口——`export`（bump 项 → 参考 Box 树）、`tm_size`、
//! 消融开关 `NO_NAME_MAP`、稳态检查器 `Tycker`（run_decls/run_input/bench
//! 口径）、`run_fast`，以及内嵌回归测试。原 bump_spine_iter.rs 的
//! "export 与对外入口" 节 + 文件尾测试，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;

use std::rc::Rc;

use super::parser::syntax::Decl;
use super::pretty;
use super::{empty_span, Error, Ix};
use crate::L06_string::Tm as CTm;

use super::machine::{types_names_list, DeclOut, Machine};
use super::syntax::Tm;

// export 与对外入口
// --------------------------------------------------------------------------------

/// 把 bump 结果项转回参考版的 `Box` 树（迭代任务栈；icit/掩码随任务
/// 携带），复用参考版的 pretty。L06 新叶的 span 全零（内容即输出）。
pub(super) fn export(t: &Tm<'_>) -> CTm {
    use crate::list::List as CList;
    use super::parser::syntax::Icit as PIcit;
    use CTm as B;
    enum J<'a> {
        Do(&'a Tm<'a>),
        Lam2(&'a str, PIcit),
        Pi2(&'a str, PIcit),
        Let2(&'a str),
        App2(PIcit),
        AppPrun2(CList<Option<PIcit>>),
    }
    fn name(x: &str) -> crate::parser_lib::Span<String> {
        empty_span(x.to_owned())
    }
    let mut tasks: Vec<J<'_>> = vec![J::Do(t)];
    let mut done: Vec<CTm> = Vec::new();
    while let Some(j) = tasks.pop() {
        match j {
            J::Do(Tm::Var(i)) => done.push(B::Var(Ix(*i))),
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
                let mut vec: Vec<Option<PIcit>> = Vec::new();
                let mut cur = *pr;
                while let Some(b) = cur {
                    vec.push(b.slot);
                    cur = b.next;
                }
                let mut list: CList<Option<PIcit>> = CList::new();
                for s in vec.into_iter().rev() {
                    list = list.prepend(s);
                }
                tasks.push(J::AppPrun2(list));
                tasks.push(J::Do(h));
            }
            J::Do(Tm::U) => done.push(B::U),
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
            J::Do(Tm::Meta(m)) => done.push(B::Meta(super::MetaVar(*m))),
            J::Do(Tm::LiteralType) => done.push(B::LiteralType),
            J::Do(Tm::LiteralIntro(s)) => done.push(B::LiteralIntro(name(s))),
            J::Do(Tm::Decl(s)) => done.push(B::Decl(name(s))),
            J::Lam2(x, i) => {
                let b = done.pop().expect("export 栈：Lam 缺体");
                done.push(B::Lam(name(x), i, Rc::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(B::Pi(name(x), i, Rc::new(dom), Rc::new(cod)));
            }
            J::Let2(x) => {
                let u = done.pop().expect("export 栈：Let 缺体");
                let t = done.pop().expect("export 栈：Let 缺值");
                let a = done.pop().expect("export 栈：Let 缺类型");
                done.push(B::Let(name(x), Box::new(a), Box::new(t), Box::new(u)));
            }
            J::App2(i) => {
                let a = done.pop().expect("export 栈：App 缺实参");
                let f = done.pop().expect("export 栈：App 缺函数");
                done.push(B::App(Box::new(f), Box::new(a), i));
            }
            J::AppPrun2(pr) => {
                let h = done.pop().expect("export 栈：AppPruning 缺头");
                done.push(B::AppPruning(Box::new(h), pr));
            }
        }
    }
    done.pop().expect("export 必须恰有一个根")
}

fn tm_size(t: &Tm<'_>) -> u64 {
    let mut stack: Vec<&Tm<'_>> = vec![t];
    let mut n = 0u64;
    while let Some(x) = stack.pop() {
        n += 1;
        match x {
            Tm::Var(_) | Tm::U | Tm::Meta(_) | Tm::LiteralType | Tm::LiteralIntro(_)
            | Tm::Decl(_) => {}
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
        }
    }
    n
}

/// A/B 实验开关（Raw::Var 名字解析消融）：置 `L06_NO_NAME_MAP=1` 回落为
/// 沿 `types` 链的线性找名（`=0` 不关闭）。
pub(super) static NO_NAME_MAP: std::sync::LazyLock<std::sync::atomic::AtomicBool> =
    std::sync::LazyLock::new(|| {
        std::sync::atomic::AtomicBool::new(std::env::var("L06_NO_NAME_MAP").is_ok_and(|v| v != "0"))
    });

/// 稳态类型检查器（同 L03-L05：owns 反复 `reset` 的 `Bump` 与跨调用复用
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
    /// 输出逐字节一致，L03-L05 已证）。
    pub(crate) fn run_decls(&mut self, ast: &[Decl]) -> Result<String, Error> {
        self.run_decls_impl(ast, false, Default::default())
            .map(|(out, _)| out)
    }

    /// 带**观察面**的驱动：与 [`Tycker::run_decls`] 同输出，返回 owned 快照
    /// （`docs/l06-lsp-port-2026-11-20.md` §2.2）。
    pub(crate) fn run_decls_with_surface(
        &mut self,
        ast: &[Decl],
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_decls_impl(ast, true, Default::default())
    }

    /// 带观察面 + **查询口径**（惰性 hover + inlay 可见区）。
    pub(crate) fn run_decls_with_surface_query(
        &mut self,
        ast: &[Decl],
        q: crate::L06_string::surface::SurfaceQuery,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_decls_impl(ast, true, q)
    }

    /// 带观察面 + **按偏移采集**（惰性 hover，参考版 `run_with_surface_at`
    /// 的孪生版）：只有使用处 span 含 `offset` 的悬停条目被渲染。
    pub(crate) fn run_decls_with_surface_at(
        &mut self,
        ast: &[Decl],
        offset: u32,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_decls_impl(ast, true, crate::L06_string::surface::SurfaceQuery::hover_only(offset as usize))
    }

    /// 采集开关（默认关；与 L13 的默认相反，见移植文档 §1.1）。
    pub(crate) fn set_observe(&mut self, on: bool) {
        self.machine.observe = on;
    }

    /// 当前采集开关状态（测试/诊断用）。
    pub(crate) fn observe_on(&self) -> bool {
        self.machine.observe
    }

    /// 当前观察面快照（`run_decls*` 返回后读取本轮结果）。
    pub(crate) fn surface(&self) -> crate::L06_string::surface::LspSurface {
        self.machine.surface()
    }

    /// 与 L13 `Tycker::hover_entry_at` 同签名同规则。
    pub(crate) fn hover_entry_at(
        &self,
        path_id: u32,
        offset: usize,
    ) -> Option<&crate::L06_string::surface::HoverEntry> {
        self.machine.hover_entry_at(path_id, offset)
    }

    fn run_decls_impl(
        &mut self,
        ast: &[Decl],
        collect: bool,
        q: crate::L06_string::surface::SurfaceQuery,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.bump.reset();
        self.machine.clear_round();
        self.machine.observe = collect;
        self.machine.hover_query = q.hover.map(|o| o as u32);
        self.machine.inlay_query = q.inlay;
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for (idx, d) in ast.iter().enumerate() {
            let (out, nc) = self.machine.infer_decl(bump, cxt, d)?;
            cxt = nc;
            if collect {
                self.machine.drain_check_issues(idx);
            }
            if let DeclOut::Println(t) = out {
                let v = self.machine.eval(bump, cxt.env, t);
                let q = self.machine.quote_memo(bump, cxt.lvl, v);
                let names = types_names_list(cxt.types);
                let rendered = pretty::pretty_tm(0, names, &export(q));
                ret += &rendered;
                ret += "\n";
                if collect {
                    let span = match d {
                        Decl::Println(r) => crate::L06_string::surface::raw_span(r),
                        Decl::Def { .. } => empty_span(()),
                    };
                    self.machine.push_println_span(span, &rendered);
                }
            }
        }
        Ok((ret, self.machine.surface()))
    }

    /// 带观察面的**继续型**检查驱动（失败 decl 通道的观察/测试用；与参考版
    /// `L06_string::check_with_surface` 同语义：遇错记名字后继续）。
    pub(crate) fn check_with_surface(
        &mut self,
        ast: &[Decl],
    ) -> (Option<Error>, crate::L06_string::surface::LspSurface) {
        self.bump.reset();
        self.machine.clear_round();
        self.machine.observe = true;
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut first_err: Option<Error> = None;
        for (idx, d) in ast.iter().enumerate() {
            match self.machine.infer_decl(bump, cxt, d) {
                Ok((out, nc)) => {
                    cxt = nc;
                    if let DeclOut::Println(t) = out {
                        let v = self.machine.eval(bump, cxt.env, t);
                        let q = self.machine.quote_memo(bump, cxt.lvl, v);
                        let names = types_names_list(cxt.types);
                        let rendered = pretty::pretty_tm(0, names, &export(q));
                        let span = match d {
                            Decl::Println(r) => crate::L06_string::surface::raw_span(r),
                            Decl::Def { .. } => empty_span(()),
                        };
                        self.machine.push_println_span(span, &rendered);
                    }
                    self.machine.drain_check_issues(idx);
                }
                Err(e) => {
                    self.machine.note_failed_decl(d);
                    // 失败 decl 不进上下文（保留旧 cxt 继续），后续引用
                    // 会落到 not-in-scope。
                    if first_err.is_none() {
                        first_err = Some(e);
                    }
                    self.machine.drain_check_issues(idx);
                }
            }
        }
        (first_err, self.machine.surface())
    }

    /// 参考版 `run` 的全流程等价物（含 preprocess/parse）。
    pub(crate) fn run_input(&mut self, input: &str, path_id: u32) -> Result<String, Error> {
        self.run_input_impl(input, path_id, false, None, Default::default())
            .map(|(out, _)| out)
    }

    /// [`Tycker::run_input`] + 观察面。
    pub(crate) fn run_input_with_surface(
        &mut self,
        input: &str,
        path_id: u32,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_input_impl(input, path_id, true, None, Default::default())
    }

    /// [`Tycker::run_input_with_surface`] + **查询口径**（惰性 hover + inlay 可见区）。
    pub(crate) fn run_input_with_surface_query(
        &mut self,
        input: &str,
        path_id: u32,
        q: crate::L06_string::surface::SurfaceQuery,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_input_impl(input, path_id, true, None, q)
    }

    /// [`Tycker::run_input_with_surface`] + **按偏移采集**（惰性 hover）：只在
    /// 光标处渲染悬停条目（参考版 `L06_string::run_with_surface_at` 的孪生版）。
    pub(crate) fn run_input_with_surface_at(
        &mut self,
        input: &str,
        path_id: u32,
        offset: usize,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_input_impl(
            input,
            path_id,
            true,
            None,
            crate::L06_string::surface::SurfaceQuery::hover_only(offset),
        )
    }

    /// [`Tycker::run_input_with_surface`] + 求值预算（毫秒）。超时落成 `Err`。
    pub(crate) fn run_input_with_surface_budget(
        &mut self,
        input: &str,
        path_id: u32,
        ms: u64,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        self.run_input_impl(input, path_id, true, Some(ms), Default::default())
    }

    fn run_input_impl(
        &mut self,
        input: &str,
        path_id: u32,
        collect: bool,
        budget_ms: Option<u64>,
        q: crate::L06_string::surface::SurfaceQuery,
    ) -> Result<(String, crate::L06_string::surface::LspSurface), Error> {
        let ast = super::parser::parser(&super::preprocess(input), path_id).map_err(Error)?;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _scope = budget_ms.map(crate::L06_string::eval_budget::scope);
            self.run_decls_impl(&ast, collect, q)
        }));
        match outcome {
            Ok(r) => r,
            Err(p) if crate::L06_string::eval_budget::is_timeout(&*p) => Err(Error(format!(
                "elab timeout: evaluation exceeded {}ms budget",
                budget_ms.unwrap_or(0)
            ))),
            Err(p) => std::panic::resume_unwind(p),
        }
    }

    /// 基准口径（bench 用）：仅 elaborate。采集显式关（`clear_round` 不碰
    /// `observe`，跨轮复用同一 `Tycker` 时必须自己置位）。
    pub(crate) fn bench_check(&mut self, ast: &[Decl]) -> bool {
        self.bench_check_observe(ast, Default::default(), false)
    }

    /// 基准口径 + 观察面采集（`query=None` 全量；`Some(off)` 按偏移采集）。
    /// 与 [`Tycker::bench_check`] 同一工作量，差值即采集开销。
    pub(crate) fn bench_check_observe(
        &mut self,
        ast: &[Decl],
        q: crate::L06_string::surface::SurfaceQuery,
        observe: bool,
    ) -> bool {
        self.bump.reset();
        self.machine.clear_round();
        self.machine.observe = observe;
        self.machine.hover_query = q.hover.map(|o| o as u32);
        self.machine.inlay_query = q.inlay;
        let bump = &self.bump;
        self.machine.elab_all(bump, ast).0.is_ok()
    }

    /// 基准口径：check + nf（最后一个 def 的登记值空层级引读），返回
    /// 结果树节点数。
    pub(crate) fn bench_check_nf(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, false)
    }

    /// [`Tycker::bench_check_nf`] 的 quote 记忆化口径。
    pub(crate) fn bench_check_nf_memo(&mut self, ast: &[Decl]) -> u64 {
        self.bench_nf_impl(ast, true)
    }

    /// 基准口径 + 观察面采集（`query=None` 全量；`Some(off)` 按偏移采集 =
    /// 惰性 hover）。与 [`Tycker::bench_check_nf`] 同一工作量（含 nf）。
    pub(crate) fn bench_check_nf_observe(
        &mut self,
        ast: &[Decl],
        q: crate::L06_string::surface::SurfaceQuery,
        observe: bool,
    ) -> u64 {
        self.bench_nf_impl_with(ast, false, observe, q)
    }

    fn bench_nf_impl(&mut self, ast: &[Decl], use_memo: bool) -> u64 {
        self.bench_nf_impl_with(ast, use_memo, false, Default::default())
    }

    fn bench_nf_impl_with(
        &mut self,
        ast: &[Decl],
        use_memo: bool,
        observe: bool,
        q: crate::L06_string::surface::SurfaceQuery,
    ) -> u64 {
        self.bump.reset();
        self.machine.clear_round();
        self.machine.observe = observe;
        self.machine.hover_query = q.hover.map(|o| o as u32);
        self.machine.inlay_query = q.inlay;
        let bump = &self.bump;
        let (r, last) = self.machine.elab_all(bump, ast);
        if r.is_err() {
            return 0;
        }
        let Some((_, vt)) = last else {
            return 0;
        };
        let q = if use_memo {
            self.machine.quote_memo(bump, 0, vt)
        } else {
            self.machine.quote(bump, 0, vt)
        };
        tm_size(q)
    }
}

/// 一次性口径入口（与参考版 `run` 同签名同 Ok 输出）。
pub(crate) fn run_fast(input: &str, path_id: u32) -> Result<String, Error> {
    let mut tycker = Tycker::new();
    tycker.run_input(input, path_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::FILE_IO_LOCK;

    // 拆分后按路径补引（原单文件内同模块直接可见的跨子系统项）：
    use super::super::bench_src::{church_src, globals_src, strchain_src};
    use super::super::unify::NO_CONV_MEMO;

    /// Ok 输出逐字节互检；Err 判定互检（错误文案的 Debug-span 偏移是已知
    /// 偏差，不比内容）。
    fn assert_parity(src: &str) {
        let basic = super::super::run(src, 0);
        let fast = run_fast(src, 0);
        match (&basic, &fast) {
            (Ok(b), Ok(f)) => assert_eq!(
                b, f,
                "Ok 输出不一致，src:\n{src}\n--- basic ---\n{b}--- fast ---\n{f}"
            ),
            (Err(_), Err(_)) => {}
            _ => panic!(
                "判定不一致（basic={:?}, fast={:?}），src:\n{src}",
                basic.map(|_| ".."),
                fast.map(|_| "..")
            ),
        }
    }

    /// DEMO_SRC 全量互检（pruning + 字面量 + builtin 注册表 + decl 表 +
    /// 可变全局 + 文件 IO——两个实现先后跑，各自写删同一文件，幂等）。
    /// 文件 IO 用固定文件名，相关测试经 `FILE_IO_LOCK` 串行（并行线程下
    /// Windows 的文件句柄竞争会让删除报 os error 5）。
    #[test]
    fn parity_on_demo_src() {
        let _guard = FILE_IO_LOCK.lock().unwrap();
        assert_parity(super::super::DEMO_SRC);
    }

    /// 剪枝样例束（L05 EX1 的 L06 语法版）。源码无分号（Eof 检查下 `;`
    /// 会截断 decl 流导致解析失败），多 def 用例带全 Eq/refl 前置——
    /// 历史 `;` 版只解析出第一条，剪枝路径实际没跑到。
    #[test]
    fn parity_on_pruning_examples() {
        for src in [
            "def pr1 = f => x => f x\nprintln pr1\n",
            "def pr2 = f => x => y => f x y\nprintln pr2\n",
            "def pr3 = f => f U\nprintln pr3\n",
            // 非线性 spine 可解（m 的类型不依赖非线性实参）
            concat!(
                "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
                "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
                "def the (A : U)(x : A) : A = x\n",
                "def m (A : U)(B : U) : U -> U -> U = _\n",
                "def test = a => b => the (Eq (m a a) (x => y => y)) refl\n",
                "println test\n",
            ),
            // 交集剪枝：m a b c =? m c b a 剪 a/c 取 b
            concat!(
                "def Eq [A : U] (x : A, y : A) : U = (P : A -> U) -> P x -> P y\n",
                "def refl [A : U, x : A] : Eq[A] x x = P => px => px\n",
                "def the (A : U)(x : A) : A = x\n",
                "def m : U -> U -> U -> U = _\n",
                "def test = a => b => c => the (Eq (m a b c) (m c b a)) refl\n",
                "println test\n",
            ),
        ] {
            assert_parity(src);
        }
    }

    /// 字面量 + builtin 全组（部分应用卡住、同名 stuck decl 的 unify、
    /// str_eq 的真假、indent）。
    #[test]
    fn parity_on_string_builtins() {
        for src in [
            "def s : String = string_concat \"hello \" \"world\"\nprintln s\n",
            // 部分应用：卡住的 Decl 头（quote 成 `string_concat x` 形态）
            "def f = s => string_concat s\nprintln f\n",
            // 卡住 decl 与 String 类型的 unify（get_global 的返回类型）
            "def st : U = string_to_global_type \"String\"\nprintln st\n",
            "def st : U = string_to_global_type \"Missing\"\nprintln st\n",
            "def eq1 = str_eq \"foo\" \"foo\"\nprintln eq1\n",
            "def eq2 = str_eq \"foo\" \"bar\"\nprintln eq2\n",
            "def ind = str_indent2 \"line1\nline2\"\nprintln ind\n",
        ] {
            assert_parity(src);
        }
    }

    /// 命名 λ：按名字匹配 Π binder（Span 的 PartialEq 只比 data——与参考
    /// 版/L05 同款语义）。L06 λ 语法无反斜杠：binder 组 + `=>`。
    #[test]
    fn named_lambda_matches_by_name() {
        // 名字命中：elaborated binder 用 λ 侧的 binder 名（a）
        assert_parity(
            "def f : [A : U] -> A -> A = [A = a] x => x\n\
             println f\n",
        );
        // 名字未命中：按 Π 名补 inserted binder（A）
        assert_parity(
            "def g : [A : U] -> A -> A = [B = b] y => y\n\
             println g\n",
        );
    }

    /// 报错路径：判定一致（文案含 span 偏移为已知偏差）。
    #[test]
    fn error_parity() {
        for src in [
            "println nope\n",
            "def g : U -> U -> U = x => y => x\nprintln (g U)\n", // icit 失配
            "def h = [B = x] y => y\nprintln h\n",                // 命名 λ 不可推断
            "def bad : U = \"not a type\"\nprintln bad\n",        // Lit vs U
        ] {
            assert_parity(src);
        }
    }

    /// 深负载：church k=12 的 elaborate 判定一致（8192 层），strchain 512。
    #[test]
    fn deep_workloads() {
        let src = church_src(12);
        let Ok(raw) = super::super::parser::parser(&super::super::preprocess(&src), 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "church k=12 未通过");
        assert_eq!(t.bench_check_nf_memo(&raw), 2 * (1u64 << 13) + 4, "nf 节点数");

        let src = strchain_src(9);
        let Ok(raw) = super::super::parser::parser(&super::super::preprocess(&src), 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "strchain 未通过");
        assert_eq!(t.bench_check_nf_memo(&raw), 1, "strchain nf 节点数");
        // 与参考版逐字节（含 println 输出）
        let src_print = strchain_src(5) + "println s0\n";
        let basic = super::super::run(&src_print, 0).unwrap();
        assert_eq!(run_fast(&src_print, 0).unwrap(), basic);

        let src = globals_src(9);
        let Ok(raw) = super::super::parser::parser(&super::super::preprocess(&src), 0) else {
            panic!("parse failed");
        };
        let mut t = Tycker::new();
        assert!(t.bench_check(&raw), "globals 未通过");
        assert_eq!(t.bench_check_nf_memo(&raw), 1, "globals nf 节点数");
    }

    /// 稳态复用正确性：同一 Tycker 连续多轮（含 mutable_map / decl 表的
    /// 轮清空），输出与每轮新建的一致。
    #[test]
    fn steady_state_reuse() {
        let _guard = FILE_IO_LOCK.lock().unwrap();
        let src = super::super::DEMO_SRC;
        let mut steady = Tycker::new();
        let r1 = steady.run_input(src, 0).unwrap();
        let r2 = steady.run_input(src, 0).unwrap();
        let fresh = run_fast(src, 0).unwrap();
        assert_eq!(r1, r2, "稳态两轮不一致");
        assert_eq!(r1, fresh, "稳态与一次性不一致");
    }

    /// 判等记忆化消融口径输出一致。
    #[test]
    fn ablation_env_off_by_default() {
        assert!(!NO_CONV_MEMO.load(std::sync::atomic::Ordering::Relaxed));
        assert!(!NO_NAME_MAP.load(std::sync::atomic::Ordering::Relaxed));
    }
}

// L07 优化回填的回归钉（2026-11-18）
// --------------------------------------------------------------------------------

/// 载体切换（top-level defs 只走 decl 表，不进 env）：引用距离与 def 数无关。
///
/// 回归口径：`strchain` 每层都回头引用**最早**注册的 `string_concat`。旧
/// 实现把它 `define` 进 env 头部，`eval(Tm::Var)` 用 `env.iter().nth()` 线性
/// 走链 ⇒ O(D²) 指针追逐（k=11 实测 57 ms）；现在 builtin / def 都只在 decl
/// 表，引用走 `Tm::Decl` 的 O(1) 查找（同负载 5.6 ms）。这里钉住的是**复杂
/// 度形态**：k 翻倍时耗时比应接近 2（线性），而不是 4（平方）。
#[test]
fn carrier_defs_live_only_in_decl_table() {
    use std::time::Instant;
    let time_one = |k: u32| {
        let src = super::strchain_src(k) + &format!("println s{}\n", (1u64 << (k + 1)) - 1);
        let ok = super::super::run(&src, 0).unwrap();
        let t0 = Instant::now();
        for _ in 0..3 {
            let out = super::super::run(&src, 0).unwrap();
            assert_eq!(out, ok);
        }
        t0.elapsed().as_secs_f64() / 3.0
    };
    let t9 = time_one(9);
    let t11 = time_one(11);
    // 线性应为 4×（D 翻 4 倍）；旧平方形态会是 16×。取 8× 作为宽松上界
    // （覆盖计时噪声；旧实现在同机同口径下是 13×+）。
    assert!(
        t11 / t9 < 8.0,
        "strchain k=11/k=9 耗时比 {:.1}×（应近线性：4×；平方形态 ≥13×）",
        t11 / t9
    );
}

/// P5 跨 meta 环守卫：`?a := ?b`、`?b := ?a` 的展开必须**有界终止**，
/// 不得无限递归（旧实现只能等爆栈）。
#[test]
fn cross_meta_cycle_force_is_bounded() {
    use super::super::{Infer, Val};
    let mut infer = Infer::new();
    infer.solve_meta_cycle_for_test();
    let out = infer.force(&infer.meta_cycle_root_for_test());
    assert!(
        matches!(out.as_ref(), Val::Flex(..)),
        "环上的展开应停在卡住的 Flex，实际 {out:?}"
    );
}
