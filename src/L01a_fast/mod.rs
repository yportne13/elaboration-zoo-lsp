use std::{rc::Rc, time::Duration};

use crate::L01a_fast::list_arena::ListArena;

mod nbe_closure;
mod nbe_closure_rc;
mod nbe_closure_rc2;
mod nbe_closure1;
mod nbe_closure2;
mod nbe_closure22;
mod nbe_closure3;
mod nbe_closure4;
mod list_arena;

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
                // App case: need to parse from right to left
                // First parse the second argument
                let (arg2, remaining) = Term::from_vec(bytes);
                // Then parse the first argument
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
                // Lam case: read length (8 bytes) then the term
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

fn church(n: usize) -> Term {
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

pub fn main() -> Duration {
    //println!("Hello, world!");
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    //let add = add.to_vec();
    let start = std::time::Instant::now();
    let result = nbe_closure::normalize(add);
    let end = start.elapsed();
    //let result = Term::from_vec(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main1() -> Duration {
    //println!("Hello, world!");
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    //let add = add.to_vec();
    let start = std::time::Instant::now();
    let result = nbe_closure_rc::normalize(add);
    let end = start.elapsed();
    //let result = Term::from_vec(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main11() -> Duration {
    //println!("Hello, world!");
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    let add = add.into_rc();
    let start = std::time::Instant::now();
    let result = nbe_closure_rc2::normalize(add);
    let end = start.elapsed();
    //let result = Term::from_vec(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main2() -> Duration {
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    let add = add.to_vec2();
    let start = std::time::Instant::now();
    let result = nbe_closure1::normalize(add);
    let end = start.elapsed();
    let result = Term::from_vec2(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main3() -> Duration {
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    let add = add.to_vec2();
    let start = std::time::Instant::now();
    let mut arena = ListArena::new();
    let result = nbe_closure2::normalize(add, &mut arena);
    let end = start.elapsed();
    let result = Term::from_vec2(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main32() -> Duration {
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    let mut arena_tm = Vec::new();
    let add = add.to_vec3(&mut arena_tm);
    let start = std::time::Instant::now();
    let mut arena = ListArena::new();
    let result = nbe_closure22::normalize(add, &mut arena, &mut arena_tm);
    let end = start.elapsed();
    let result = Term::from_vec3(result, &arena_tm).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main4() -> Duration {
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    let add = add.to_vec2();
    let start = std::time::Instant::now();
    let mut arena = ListArena::new();
    let result = nbe_closure3::normalize(add, &mut arena);
    let end = start.elapsed();
    let result = Term::from_vec2(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}

pub fn main5() -> Duration {
    //println!("Hello, world!");
    let i = 1000;
    let a = church(i);
    let b = church(i);
    let add = apply(church_add(), vec![a, b]);
    let add = add.to_vec();
    let start = std::time::Instant::now();
    let result = nbe_closure4::normalize(add);
    let end = start.elapsed();
    let result = Term::from_vec(result).0;
    //println!("{:?}", result);
    let check = church(i + i);
    assert!(result == check);
    end
}
