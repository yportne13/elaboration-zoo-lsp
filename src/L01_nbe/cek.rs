//! CEK 机变体（Felleisen & Friedman 1987）：**显式 continuation 栈的迭代
//! 求值器**，且 eval → quote → 解码**全链路迭代**。
//!
//! eval 不再递归下降：状态只有（待求值项或值，环境，kont 栈）三元组，每步
//! 一次小匹配。`App` 的求值顺序（先函数、再实参、之后 apply）由 kont 记录，
//! 而不是由调用栈记录。quote 用显式工作栈输出前缀字节码（与 `Term::to_vec2`
//! 同格式，Lam 长度占位回填），解码是前向扫描 + 组装循环——`Clo` 内部发起的
//! eval 复用同一个迭代循环（重入深度 = 结果树的 Lam 嵌套深度，对教堂数这类
//! 项是常数）。
//!
//! 收益：**求值深度不受进程栈限制**——基准里其余递归变体在 n ≥ 16000 时
//! 构造/求值/比较全链路爆栈，`cek` 可以一路跑到 n = 10 万级（readme 有实测）。
//! 代价：每步多一次显式栈压弹和宽分派，小规模上比递归版略慢。

use crate::list::List;
use super::Term;

#[derive(Debug, Clone)]
enum Value {
    Lvl(usize),
    Clo(List<Value>, Term),
    App(Box<Value>, Box<Value>),
}

/// continuation 栈条目。
enum Kont {
    /// 函数已求得，实参待求值（记录实参与其求值环境）。
    Fun(Term, List<Value>),
    /// 实参已求得（值），等函数来应用。
    Arg(Value),
}

/// eval env tm =
///      match tm with
///      | Idx idx   -> List.nth env idx
///      | Lam tm'   -> VLam(env, tm')
///      | App(f, a) -> apply_val (eval env f) (eval env a)
///
/// 递归定义被改写成循环，转移规则：
///
/// ```text
/// (App f a, e, k)        -> 求值 f，k 推入 Fun(a, e)
/// (Idx i,   e, k)        -> 查表出值，转值状态
/// (Lam b,   e, k)        -> Clo(e, b) 出值，转值状态
/// (v, Fun(a, e') :: k)   -> 求值 a（环境 e'），k 推入 Arg(v)
/// (v, Arg(Clo(e', b)))   -> 以 v::e' 求值 b，k 不动（同一上下文继续）
/// (v, Arg(f))            -> 出值 App(f, v)，转值状态
/// (v, [])                -> 定案，v 即结果
/// ```
fn eval(env: List<Value>, tm: Term) -> Value {
    let mut env = env;
    let mut tm: Option<Term> = Some(tm);
    let mut val: Option<Value> = None;
    let mut kont: Vec<Kont> = Vec::new();

    loop {
        if let Some(t) = tm.take() {
            match t {
                Term::Idx(i) => val = Some(env.iter().nth(i).unwrap().clone()),
                Term::Lam(b) => val = Some(Value::Clo(env.clone(), *b)),
                Term::App(f, a) => {
                    kont.push(Kont::Fun(*a, env.clone()));
                    tm = Some(*f);
                },
            }
            continue; // 转值状态
        }

        let v = val.take().expect("值状态必须持有值");
        match kont.pop() {
            Some(Kont::Fun(a, e)) => {
                env = e;
                tm = Some(a);
                kont.push(Kont::Arg(v));
            },
            Some(Kont::Arg(f)) => match f {
                Value::Clo(e, body) => {
                    env = e.prepend(v);
                    tm = Some(body);
                },
                f => val = Some(Value::App(Box::new(f), Box::new(v))),
            },
            None => return v,
        }
    }
}

/// quote 工作栈条目。
enum QW {
    /// 继续 quote 一个值（level 是当前 lambda 深度）。
    Qt(usize, Value),
    /// `Lam` 头（tag+长度占位）已写，等体输出后回填长度（`pos` 记长度字段位置）。
    LamFill(usize),
}

/// 迭代 quote：输出与 `Term::to_vec2` 相同的前缀字节码。
///
/// ```text
/// quote level value =
///      match value with
///      | VLvl lvl        -> Idx(level - lvl - 1)
///      | VLam(env, body) -> Lam(quote (level + 1) @@ eval (VLvl level :: env) body)
///      | VApp(vf, va)    -> App(quote level vf, quote level va)
/// ```
fn quote_pre(level0: usize, v0: Value) -> Vec<u8> {
    let mut out = Vec::new();
    let mut work: Vec<QW> = vec![QW::Qt(level0, v0)];
    while let Some(w) = work.pop() {
        match w {
            QW::Qt(level, value) => match value {
                Value::Lvl(l) => {
                    out.push(0);
                    out.extend_from_slice(&(level - l - 1).to_le_bytes());
                },
                Value::Clo(env, body) => {
                    // body 的求值复用同一个迭代 eval；重入深度 = Lam 嵌套深度
                    let v = eval(env.prepend(Value::Lvl(level)), body);
                    out.push(1);
                    let pos = out.len();
                    out.extend_from_slice(&0u64.to_le_bytes()); // 长度占位
                    work.push(QW::LamFill(pos));
                    work.push(QW::Qt(level + 1, v));
                },
                Value::App(f, a) => {
                    out.push(2);
                    work.push(QW::Qt(level, *a));
                    work.push(QW::Qt(level, *f));
                },
            },
            QW::LamFill(pos) => {
                let len = (out.len() - pos - 8) as u64;
                out[pos..pos + 8].copy_from_slice(&len.to_le_bytes());
            },
        }
    }
    out
}

/// 解码 `to_vec2` 前缀编码（与 `Term::from_vec2` 语义相同，迭代实现）。
///
/// 前向扫描 + 组装循环：tag 直接给出子树顺序，`Lam`/`App` 头先压栈，
/// 子树解码完成的 `Term` 压上后由 `assemble` 并进其上的 Pending。收尾再
/// 组装一次，把残余子树并进外层 Pending（App 的函数常常先于实参压栈）。
fn decode_pre(bytes: Vec<u8>) -> Term {
    #[derive(Debug)]
    enum P {
        Lam,
        App,
    }
    #[derive(Debug)]
    enum E {
        T(Term),
        P(P),
    }
    fn assemble(stack: &mut Vec<E>) {
        loop {
            // 从栈顶收集一叠连续子树（subs[0] 是最顶层的实参）
            let mut subs: Vec<Term> = Vec::new();
            let pending = loop {
                match stack.pop() {
                    Some(E::T(t)) => subs.push(t),
                    Some(E::P(p)) => break Some(p),
                    None => break None,
                }
            };
            let Some(p) = pending else {
                for t in subs.into_iter().rev() {
                    stack.push(E::T(t));
                }
                break;
            };
            match p {
                P::Lam if subs.len() == 1 => {
                    let body = subs.pop().unwrap();
                    stack.push(E::T(Term::Lam(Box::new(body))));
                },
                P::App if subs.len() == 2 => {
                    let f = subs.pop().unwrap();
                    let a = subs.pop().unwrap();
                    stack.push(E::T(Term::App(Box::new(f), Box::new(a))));
                },
                p => {
                    stack.push(E::P(p));
                    for t in subs.into_iter().rev() {
                        stack.push(E::T(t));
                    }
                    break;
                },
            }
        }
    }

    let mut stack: Vec<E> = Vec::new();
    let mut pos = 0usize;
    while pos < bytes.len() {
        match bytes[pos] {
            0 => {
                let mut b = [0u8; 8];
                b.copy_from_slice(&bytes[pos + 1..pos + 9]);
                pos += 9;
                stack.push(E::T(Term::Idx(usize::from_le_bytes(b))));
            },
            1 => {
                pos += 9; // 长度字段解码用不到（体由栈机自然给出）
                stack.push(E::P(P::Lam));
            },
            2 => {
                pos += 1;
                stack.push(E::P(P::App));
            },
            _ => unreachable!("to_vec2 格式 tag 只可能是 0/1/2"),
        }
        assemble(&mut stack);
    }
    assemble(&mut stack); // 收尾合并
    match stack.pop() {
        Some(E::T(root)) => root,
        _ => panic!("to_vec2 解码必须恰好有一个根"),
    }
}

pub(crate) fn normalize(t: Term) -> Term {
    decode_pre(quote_pre(0, eval(List::new(), t)))
}