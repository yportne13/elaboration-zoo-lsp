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
//! 编码本身带长度字段（`Lam` 体用小端 u64 记长），解码时可直接切出子串；
//! 所有 `from_*` 都用 `get_unchecked` 假定输入由对应的 `to_*` 产生。

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
        let tag = unsafe { *bytes.get_unchecked(bytes.len() - 1) };
        bytes.pop();

        match tag {
            0 => {
                // Idx case: read 8 bytes as usize
                let mut idx_bytes = [0u8; 8];
                let start = bytes.len() - 8;
                idx_bytes.copy_from_slice(unsafe { bytes.get_unchecked(start..start + 8) });
                bytes.truncate(start);
                let idx = usize::from_le_bytes(idx_bytes);
                (Term::Idx(idx), bytes)
            },
            1 => {
                // Lam case: read length (8 bytes) and extract term
                let mut len_bytes = [0u8; 8];
                let start = bytes.len() - 8;
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