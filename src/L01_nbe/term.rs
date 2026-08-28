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

    pub fn from_vec2(mut bytes: Vec<u8>) -> (Term, Vec<u8>) {
        let tag = unsafe { *bytes.get_unchecked(0) };
        bytes.drain(0..1);

        match tag {
            0 => {
                // Idx case: read 8 bytes as usize
                let mut idx_bytes = [0u8; 8];
                idx_bytes.copy_from_slice(unsafe { bytes.get_unchecked(0..8) });
                bytes.drain(0..8);
                let idx = usize::from_le_bytes(idx_bytes);
                (Term::Idx(idx), bytes)
            },
            1 => {
                // Lam case: read length (8 bytes) then the term
                let mut len_bytes = [0u8; 8];
                len_bytes.copy_from_slice(unsafe { bytes.get_unchecked(0..8) });
                bytes.drain(0..8);
                let len = u64::from_le_bytes(len_bytes) as usize;
                let term_bytes = bytes[..len].to_vec();
                bytes.drain(0..len);
                let (term, _) = Term::from_vec2(term_bytes);
                (Term::Lam(Box::new(term)), bytes)
            },
            2 => {
                // App case: parse two consecutive terms
                let (term1, remaining) = Term::from_vec2(bytes);
                let (term2, final_remaining) = Term::from_vec2(remaining);
                (Term::App(Box::new(term1), Box::new(term2)), final_remaining)
            },
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
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

    pub fn from_vec3(mut bytes: Vec<u8>, arena_tm: &Vec<Rc<Vec<u8>>>) -> (Term, Vec<u8>) {
        let tag = unsafe { *bytes.get_unchecked(0) };
        bytes.drain(0..1);

        match tag {
            0 => {
                // Idx case: read 8 bytes as usize
                let mut idx_bytes = [0u8; 8];
                idx_bytes.copy_from_slice(unsafe { bytes.get_unchecked(0..8) });
                bytes.drain(0..8);
                let idx = usize::from_le_bytes(idx_bytes);
                (Term::Idx(idx), bytes)
            },
            1 => {
                // Lam case: the body lives in arena_tm at the stored index
                let mut len_bytes = [0u8; 8];
                len_bytes.copy_from_slice(unsafe { bytes.get_unchecked(0..8) });
                bytes.drain(0..8);
                let len = u64::from_le_bytes(len_bytes) as usize;
                let (term, _) = Term::from_vec3(arena_tm.get(len).unwrap().to_vec(), arena_tm);
                (Term::Lam(Box::new(term)), bytes)
            },
            2 => {
                // App case: parse two consecutive terms
                let (term1, remaining) = Term::from_vec3(bytes, arena_tm);
                let (term2, final_remaining) = Term::from_vec3(remaining, arena_tm);
                (Term::App(Box::new(term1), Box::new(term2)), final_remaining)
            },
            _ => unsafe { std::hint::unreachable_unchecked() },
        }
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