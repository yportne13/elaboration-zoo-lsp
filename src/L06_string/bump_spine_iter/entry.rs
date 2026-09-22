//! entry：对外入口——`export`（bump 项 → 参考 Box 树）、`tm_size`、
//! 消融开关 `NO_NAME_MAP`、稳态检查器 `Tycker`（run_decls/run_input/bench
//! 口径）、`run_fast`，以及内嵌回归测试。原 bump_spine_iter.rs 的
//! "export 与对外入口" 节 + 文件尾测试，逐行搬运（2026-09-23 拆分）。

use bumpalo::Bump;

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
                done.push(B::Lam(name(x), i, Box::new(b)));
            }
            J::Pi2(x, i) => {
                let cod = done.pop().expect("export 栈：Pi 缺余定义域");
                let dom = done.pop().expect("export 栈：Pi 缺定义域");
                done.push(B::Pi(name(x), i, Box::new(dom), Box::new(cod)));
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
        self.bump.reset();
        self.machine.clear_round();
        let bump = &self.bump;
        let mut cxt = self.machine.prime_round(bump);
        let mut ret = String::new();
        for d in ast {
            let (out, nc) = self.machine.infer_decl(bump, cxt, d)?;
            cxt = nc;
            if let DeclOut::Println(t) = out {
                let v = self.machine.eval(bump, cxt.env, t);
                let q = self.machine.quote_memo(bump, cxt.lvl, v);
                let names = types_names_list(cxt.types);
                ret += &pretty::pretty_tm(0, names, &export(q));
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

    /// 基准口径：check + nf（最后一个 def 的登记值空层级引读），返回
    /// 结果树节点数。
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
