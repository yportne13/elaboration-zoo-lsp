//! 项（de Bruijn 索引的纯 lambda 演算）与三种字节编码。
//!
//! `Term` 是各 AST 变体（`naive`/`rc_value`/`rc_term`）直接使用的表示；
//! 字节码变体（`bytes_*`/`rpn_owned`）先经 `to_vec`/`to_vec2`/`to_vec3`
//! 编码后再求值。三种编码的差异：
//!
//! * `to_vec`/`from_vec` — 后缀（RPN）编码，tag 在末尾，解析从右往左
//!   （`rpn_owned` 用）。
//! * `to_vec2`/`from_vec2` — 前缀编码，tag 在开头，解析从左往右
//!   （`bytes_env_list`/`bytes_env_arena`/`bytes_flat_value` 用）。
//! * `to_vec3`/`from_vec3` — 前缀编码，但 `Lam` 的体不再内联，而是存入
//!   共享的 `arena_tm: Vec<Rc<Vec<u8>>>`，字节流里只存下标
//!   （`bytes_env_arena_tm` 用）。
//!
//! 编码本身带长度字段（`Lam` 体用小端 u64 记长），解码时可直接切出子串。
//! 三个 `from_*` 都**假定输入由对应的 `to_*` 产出**：`from_vec` 用
//! `get_unchecked` 读 tag/负载，`from_vec2`/`from_vec3` 用安全下标但把未知
//! tag 交给 `unreachable_unchecked`——畸形输入一律是调用方违约（release 下
//! 可能 UB，而非受控 panic）。

use std::rc::Rc;

/// 小端 u64 直读（编码必 8 字节对齐，越界即输入损坏）。
#[inline]
fn u64_at(bytes: &[u8], pos: usize) -> u64 {
    u64::from_le_bytes(bytes[pos..pos + 8].try_into().unwrap())
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Idx(usize),
    Lam(Box<Term>),
    App(Box<Term>, Box<Term>),
}

impl Term {
    pub fn to_vec(self) -> Vec<u8> {
        match self {
            Term::Idx(x) => {
                let mut result = x.to_le_bytes().to_vec();
                result.push(0);
                result
            },
            Term::Lam(term) => {
                let mut result = term.to_vec();
                let len = result.len() as u64;
                result.extend_from_slice(&len.to_le_bytes());
                result.push(1);
                result
            },
            Term::App(term1, term2) => {
                let mut result = term1.to_vec();
                result.extend(term2.to_vec());
                result.push(2);
                result
            },
        }
    }

    pub fn from_vec(mut bytes: Vec<u8>) -> (Term, Vec<u8>) {
        // SAFETY: 契约（模块头）是 `bytes` 由 `to_vec` 产出，故至少含 1 字节
        // tag；畸形/空输入属调用方违约（release 为 UB）。
        let tag = unsafe { *bytes.get_unchecked(bytes.len() - 1) };
        bytes.pop();

        match tag {
            0 => {
                // Idx case: read 8 bytes as usize
                let mut idx_bytes = [0u8; 8];
                let start = bytes.len() - 8;
                // SAFETY: `to_vec` 的 Idx 分支在 tag 前写了完整 8 字节索引，
                // `start..start+8` 落在该负载内。
                idx_bytes.copy_from_slice(unsafe { bytes.get_unchecked(start..start + 8) });
                bytes.truncate(start);
                let idx = usize::from_le_bytes(idx_bytes);
                (Term::Idx(idx), bytes)
            },
            1 => {
                // Lam case: read length (8 bytes) and extract term
                let mut len_bytes = [0u8; 8];
                let start = bytes.len() - 8;
                // SAFETY: `to_vec` 的 Lam 分支在 tag 前写了完整 8 字节长度，
                // `start..start+8` 落在该字段内。
                len_bytes.copy_from_slice(unsafe { bytes.get_unchecked(start..start + 8) });
                bytes.truncate(start);
                let len = u64::from_le_bytes(len_bytes) as usize;
                let term_start = bytes.len() - len;
                let term_bytes = bytes[term_start..].to_vec();
                bytes.truncate(term_start);
                let (term, _) = Term::from_vec(term_bytes);
                (Term::Lam(Box::new(term)), bytes)
            },
            2 => {
                // App case: parse from right to left (the argument comes first)
                let (arg2, remaining) = Term::from_vec(bytes);
                let (arg1, final_remaining) = Term::from_vec(remaining);
                (Term::App(Box::new(arg1), Box::new(arg2)), final_remaining)
            },
            // SAFETY: `to_vec` 产出的 tag 只会是 0/1/2；畸形输入属调用方违约。
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }

    pub fn to_vec2(self) -> Vec<u8> {
        match self {
            Term::Idx(x) => {
                let mut result = vec![0]; // tag for Idx
                result.extend_from_slice(&x.to_le_bytes());
                result
            },
            Term::Lam(term) => {
                let term_bytes = term.to_vec2();
                let mut result = vec![1]; // tag for Lam
                result.extend_from_slice(&(term_bytes.len() as u64).to_le_bytes());
                result.extend(term_bytes);
                result
            },
            Term::App(term1, term2) => {
                let term1_bytes = term1.to_vec2();
                let term2_bytes = term2.to_vec2();
                let mut result = vec![2]; // tag for App
                result.extend(term1_bytes);
                result.extend(term2_bytes);
                result
            },
        }
    }

    /// 解码 `to_vec2` 前缀编码（单根，消费全部字节）。
    /// 光标版：旧实现每层 `drain(0..)` 把剩余 Vec 整体前移，深链解码退化
    /// O(n²)；光标只推进不搬移，O(n)。
    pub fn from_vec2(bytes: &[u8]) -> Term {
        fn parse_at(bytes: &[u8], pos: &mut usize) -> Term {
            let tag = bytes[*pos];
            *pos += 1;
            match tag {
                0 => {
                    let start = *pos;
                    let idx = u64_at(bytes, start) as usize;
                    *pos += 8;
                    Term::Idx(idx)
                },
                1 => {
                    let start = *pos;
                    let len = u64_at(bytes, start) as usize;
                    *pos += 8;
                    // 体自带长度：在子切片上用独立光标解析（等长消费）
                    let mut body_pos = 0;
                    let body = parse_at(&bytes[*pos..*pos + len], &mut body_pos);
                    debug_assert_eq!(body_pos, len);
                    *pos += len;
                    Term::Lam(Box::new(body))
                },
                2 => {
                    let f = parse_at(bytes, pos);
                    let a = parse_at(bytes, pos);
                    Term::App(Box::new(f), Box::new(a))
                },
                // SAFETY: `bytes` 必须由 `to_vec2` 产出；tag 只会是 0/1/2。
                _ => unsafe { std::hint::unreachable_unchecked() },
            }
        }
        let mut pos = 0;
        let t = parse_at(bytes, &mut pos);
        debug_assert_eq!(pos, bytes.len());
        t
    }

    pub fn to_vec3(self, arena_tm: &mut Vec<Rc<Vec<u8>>>) -> Vec<u8> {
        match self {
            Term::Idx(x) => {
                let mut result = vec![0]; // tag for Idx
                result.extend_from_slice(&x.to_le_bytes());
                result
            },
            Term::Lam(term) => {
                let term_bytes = term.to_vec3(arena_tm);
                let mut result = vec![1]; // tag for Lam
                result.extend_from_slice(&arena_tm.len().to_le_bytes());
                arena_tm.push(term_bytes.into());
                result
            },
            Term::App(term1, term2) => {
                let term1_bytes = term1.to_vec3(arena_tm);
                let term2_bytes = term2.to_vec3(arena_tm);
                let mut result = vec![2]; // tag for App
                result.extend(term1_bytes);
                result.extend(term2_bytes);
                result
            },
        }
    }

    /// 解码 `to_vec3` 前缀编码（单根，消费全部字节；`Lam` 体取 arena 下标）。
    /// 同 `from_vec2`：光标版 O(n)，旧 `drain(0..)` 是 O(n²)。
    pub fn from_vec3(bytes: &[u8], arena_tm: &[Rc<Vec<u8>>]) -> Term {
        fn parse_at(bytes: &[u8], arena_tm: &[Rc<Vec<u8>>], pos: &mut usize) -> Term {
            let tag = bytes[*pos];
            *pos += 1;
            match tag {
                0 => {
                    let start = *pos;
                    let idx = u64_at(bytes, start) as usize;
                    *pos += 8;
                    Term::Idx(idx)
                },
                1 => {
                    let idx = u64_at(bytes, *pos) as usize;
                    *pos += 8;
                    // 体在 arena 里（编码期入表，见 to_vec3）
                    let mut body_pos = 0;
                    let body = parse_at(arena_tm.get(idx).unwrap(), arena_tm, &mut body_pos);
                    debug_assert_eq!(body_pos, arena_tm[idx].len());
                    Term::Lam(Box::new(body))
                },
                2 => {
                    let f = parse_at(bytes, arena_tm, pos);
                    let a = parse_at(bytes, arena_tm, pos);
                    Term::App(Box::new(f), Box::new(a))
                },
                // SAFETY: `bytes` 必须由 `to_vec3` 产出；tag 只会是 0/1/2。
                _ => unsafe { std::hint::unreachable_unchecked() },
            }
        }
        let mut pos = 0;
        let t = parse_at(bytes, arena_tm, &mut pos);
        debug_assert_eq!(pos, bytes.len());
        t
    }

    pub fn into_rc(self) -> TermRc {
        match self {
            Term::Idx(idx) => TermRc::Idx(idx),
            Term::Lam(body) => TermRc::Lam(body.into_rc().into()),
            Term::App(f, a) => TermRc::App(f.into_rc().into(), a.into_rc().into()),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TermRc {
    Idx(usize),
    Lam(Rc<TermRc>),
    App(Rc<TermRc>, Rc<TermRc>),
}

fn lam(body: Term) -> Term {
    Term::Lam(Box::new(body))
}

fn apply(f: Term, args: Vec<Term>) -> Term {
    args.into_iter().fold(f, |acc, a| Term::App(Box::new(acc), Box::new(a)))
}

/// let rec church_aux = function
///    | 0 -> Idx 0
///    | n -> App(Idx 1, church_aux (n - 1))
fn church_aux(n: usize) -> Term {
    match n {
        0 => Term::Idx(0),
        _ => Term::App(Box::new(Term::Idx(1)), Box::new(church_aux(n - 1))),
    }
}

pub(crate) fn church(n: usize) -> Term {
    Term::Lam(Box::new(Term::Lam(Box::new(church_aux(n)))))
}

fn church_add() -> Term {
    lam(
        lam(
            lam(
                lam(
                    apply(
                        Term::Idx(3),
                        vec![Term::Idx(1), apply(Term::Idx(2), vec![Term::Idx(1), Term::Idx(0)])])
                )
            )
        )
    )
}

/// 基准工作负载：`(λa.λb. a 1 (b 1 0)) · church n · church n`，规范化结果应为
/// `church(2n)`。所有变体共用，输入构造在计时之外。
pub(crate) fn church_pair(n: usize) -> Term {
    apply(church_add(), vec![church(n), church(n)])
}

/// church pair：`pair = λa.λb.λf. f a b`。
pub(crate) fn pair_term() -> Term {
    lam(lam(lam(apply(Term::Idx(0), vec![Term::Idx(2), Term::Idx(1)]))))
}

/// `λx. pair x x`：经 λ-binder 复制实参值（同一闭包/句柄在 quote 时被引两次）。
fn dup_lam() -> Term {
    lam(apply(pair_term(), vec![Term::Idx(0), Term::Idx(0)]))
}

/// 复制强制负载：`(λx. pair x x) · church_pair(n)`。
/// 正态形 `λf. f C C`（C = church(2n)）——quote 把同一个闭包 x **强制两次**。
pub(crate) fn dup_pair(n: usize) -> Term {
    apply(dup_lam(), vec![church_pair(n)])
}

pub(crate) fn dup_pair_expect(n: usize) -> Term {
    let c = church(n + n);
    lam(apply(Term::Idx(0), vec![c.clone(), c]))
}

/// 两层复制：`(λx. pair x x) ((λy. pair y y) · church_pair(n))`。
/// 正态形 `λf. f (λf. f C C) (λf. f C C)`——C 被强制 **4 次**（无记忆化时）。
pub(crate) fn dup_deep(n: usize) -> Term {
    apply(dup_lam(), vec![apply(dup_lam(), vec![church_pair(n)])])
}

pub(crate) fn dup_deep_expect(n: usize) -> Term {
    let c = church(n + n);
    let inner = lam(apply(Term::Idx(0), vec![c.clone(), c]));
    lam(apply(Term::Idx(0), vec![inner.clone(), inner]))
}

// ===== guest 负载形状（移植自 guest0x0/normalization-bench 的 bench.ml）=====
//
// 该基准的负载设计与 L01 原有的单一线性 church_pair 互补：church_mul 压
// “输出规模 ~n²”的输出构建，parigot/exponential 压“正态形规模 ~2^n 且
// 求值期高度共享”的 readback（记忆化/共享轴）。规模按 L01 的 Box<Term>
// 结果表示调小——guest 用 OCaml 的物理共享可到 2^24，L01 的期望值是逐
// 节点真树，n 上限受内存与递归析构约束（见 bench_guest）。

/// church 乘法：`λm.λn.λsucc.λzero. m (n succ) zero`。
fn church_mul() -> Term {
    lam(lam(lam(lam(apply(
        Term::Idx(3),
        vec![apply(Term::Idx(2), vec![Term::Idx(1)]), Term::Idx(0)],
    )))))
}

/// `church_mul (church n) (church n)` → `church(n²)`。
pub(crate) fn church_mul_pair(n: usize) -> Term {
    apply(church_mul(), vec![church(n), church(n)])
}

/// Parigot 后继：`λn.λsucc.λzero. succ n (n succ zero)`。
fn parigot_succ() -> Term {
    lam(lam(lam(apply(
        Term::Idx(1),
        vec![
            Term::Idx(2),
            apply(Term::Idx(2), vec![Term::Idx(1), Term::Idx(0)]),
        ],
    ))))
}

fn parigot_zero() -> Term {
    lam(lam(Term::Idx(0)))
}

/// `aux 0 = 0`；`aux n = succ (λ.λ. aux(n-1)) (aux(n-1))`——后一项出现两次，
/// 正态形的结构大小随 n 指数增长。
fn parigot_aux(n: usize) -> Term {
    match n {
        0 => Term::Idx(0),
        _ => {
            let p = parigot_aux(n - 1);
            apply(Term::Idx(1), vec![lam(lam(p.clone())), p])
        },
    }
}

/// Parigot 数的**正态形**（`λ.λ. aux n`，结构大小 ~2^n）。
pub(crate) fn parigot(n: usize) -> Term {
    lam(lam(parigot_aux(n)))
}

/// Parigot 数的**共享输入**：`succ (succ … zero)`，求值期各层闭包被引两次。
fn parigot_shared(n: usize) -> Term {
    match n {
        0 => parigot_zero(),
        _ => Term::App(Box::new(parigot_succ()), Box::new(parigot_shared(n - 1))),
    }
}

/// Parigot 加法：`λm.λn. n (λ.λ. succ 0) 0`。
fn parigot_add() -> Term {
    lam(lam(apply(
        Term::Idx(1),
        vec![
            lam(lam(apply(parigot_succ(), vec![Term::Idx(0)]))),
            Term::Idx(0),
        ],
    )))
}

/// `parigot_add (parigot_shared n) (parigot_shared n)` → `parigot(2n)`。
pub(crate) fn parigot_add_pair(n: usize) -> Term {
    apply(parigot_add(), vec![parigot_shared(n), parigot_shared(n)])
}

/// `λx. (λy. y y) ((λy. y y) (… x))`（n 层 `(λy. y y)`）。
fn exponential_src(k: usize) -> Term {
    match k {
        0 => Term::Idx(0),
        _ => {
            let yy = lam(Term::App(Box::new(Term::Idx(0)), Box::new(Term::Idx(0))));
            Term::App(Box::new(yy), Box::new(exponential_src(k - 1)))
        },
    }
}

/// `λx. t(n)`，`t(0)=x`、`t(k+1)=(λy. y y) t(k)`——正态形规模 2^n 且高度共享。
pub(crate) fn exponential(n: usize) -> Term {
    lam(exponential_src(n))
}

/// 上式的期望正态形 `λx. r(n)`，`r(0)=x`、`r(k)=r(k-1) r(k-1)`。
pub(crate) fn exponential_expect(n: usize) -> Term {
    fn r(k: usize) -> Term {
        match k {
            0 => Term::Idx(0),
            _ => {
                let t = r(k - 1);
                Term::App(Box::new(t.clone()), Box::new(t))
            },
        }
    }
    lam(r(n))
}