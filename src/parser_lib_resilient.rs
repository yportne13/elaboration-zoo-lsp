use std::{fmt::Debug, ops::Add, str::pattern::Pattern, hash::Hash};

pub use crate::parser_lib::{Span, ToSpan, Severity, Diagnostic};

pub trait Parser<I: Copy, A, S, E>: Sized + Copy {
    fn parse(&self, input: I, state: &mut S) -> Result<(I, A), E>;
    fn with<P, B>(self, rhs: P) -> impl Parser<I, (A, B), S, E>
    //T: AsRef<P>,
    where
        P: Parser<I, B, S, E>,
    {
        move |input, state: &mut S| {
            let (input, a) = self.parse(input, state)?;
            let (input, b) = rhs.parse(input, state)?;
            Ok((input, (a, b)))
        }
    }
    fn or<P>(self, rhs: P) -> impl Parser<I, A, S, E>
    where
        P: Parser<I, A, S, E>,
    {
        move |input, state: &mut S| self.parse(input, state).or_else(|e| rhs.parse(input, state))//TODO: err combine
    }
    fn map<B, F>(self, f: F) -> impl Parser<I, B, S, E>
    where
        F: Fn(A) -> B + Copy,
    {
        move |input, state: &mut S| {
            let (input, a) = self.parse(input, state)?;
            Ok((input, f(a)))
        }
    }
    fn option(self) -> impl Parser<I, Option<A>, S, E> {
        move |input, state: &mut S| match self.parse(input, state) {
            Ok((i, a)) => Ok((i, Some(a))),
            Err(_) => Ok((input, None)),
        }
    }
    fn many0(self) -> impl Parser<I, Vec<A>, S, E> {
        move |input, state: &mut S| {
            let mut input = input;
            let mut result = Vec::new();
            while let Ok((input_, a)) = self.parse(input, state) {
                input = input_;
                result.push(a);
            }
            Ok((input, result))
        }
        //self.with(self.many0()).map(|(a, b)| [vec![a], b].concat()).or(&|input| Some((input, vec![])))
    }
    fn many0_sep<P, X>(self, sep: P) -> impl Parser<I, Vec<A>, S, E>
    where
        P: Parser<I, X, S, E>,
    {
        move |input, state: &mut S| {
            let mut input = input;
            let mut result = Vec::new();
            while let Ok((input_, a)) = self.parse(input, state) {
                input = input_;
                result.push(a);
                if let Ok((i, _)) = sep.parse(input, state) {
                    input = i;
                } else {
                    break;
                }
            }
            Ok((input, result))
        }
        //self.with(self.many0()).map(|(a, b)| [vec![a], b].concat()).or(&|input| Some((input, vec![])))
    }
}

/*    #[allow(unused)]
    fn many1(self) -> impl Parser<I, Vec<A>, E> {
        move |input| match self.many0().parse(input) {
            Ok((_, v)) if v.is_empty() => None,
            x => x,
        }
    }
    fn many1_sep<P, X>(self, sep: P) -> impl Parser<I, Vec<A>, E>
    where
        P: Parser<I, X, E>,
    {
        move |input| match self.many0_sep(sep).parse(input) {
            Some((_, v)) if v.is_empty() => None,
            x => x,
        }
    }
}*/

impl<I: Copy, A, F, S, E> Parser<I, A, S, E> for F
where
    F: Fn(I, &mut S) -> Result<(I, A), E> + Copy,
{
    fn parse(&self, input: I, state: &mut S) -> Result<(I, A), E> {
        self(input, state)
    }
}

/*impl<I: Copy, A, B, P1, P2> Parser<I, (A, B)> for (P1, P2)
where
    P1: Parser<I, A>,
    P2: Parser<I, B>,
{
    fn parse(&self, input: I) -> Option<(I, (A, B))> {
        if let Some((input, a)) = self.0.parse(input) {
            if let Some((input, b)) = self.1.parse(input) {
                Some((input, (a, b)))
            } else {
                None
            }
        } else {
            None
        }
    }
}*/

macro_rules! tuple_parser {
    ($t0:tt | $p0:tt | $idx0:tt, $($t:tt | $p:tt | $idx:tt),*) => {
        impl<
            I: Copy,
            S,
            Err,
            $t0, $($t),*,
            $p0, $($p),*
        > Parser<I, ($t0, $($t),*), S, Err> for ($p0, $($p),*)
        where
            $p0: Parser<I, $t0, S, Err>,
            $($p: Parser<I, $t, S, Err>),*
        {
            fn parse(&self, input: I, state: &mut S) -> Result<(I, ($t0, $($t),*)), Err> {
                let (input, val) = self.$idx0.parse(input, state)?;
                tuple_parser!(self => input => state => val => $($t | $p | $idx),*)
            }
        }
    };
    ($self:expr => $input:expr => $state:expr => $($parsed:expr)+ => $t0:tt | $p0:tt | $idx0:tt, $($t:tt | $p:tt | $idx:tt),+) => ({
        let (input, val) = $self.$idx0.parse($input, $state)?;
        tuple_parser!($self => input => $state => $($parsed)+ val => $($t | $p | $idx),+)
    });
    ($self:expr => $input:expr => $state:expr => $($parsed:expr)+ => $t0:tt | $p0:tt | $idx0:tt) => ({
        let (input, val) = $self.$idx0.parse($input, $state)?;
        Ok((input, ($($parsed),*, val)))
    });
}

tuple_parser!(A | PA | 0, B | PB | 1);
tuple_parser!(A | PA | 0, B | PB | 1, C | PC | 2);
tuple_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3);
tuple_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4);
tuple_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4, F | PF | 5);
tuple_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4, F | PF | 5, G | PG | 6);
tuple_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4, F | PF | 5, G | PG | 6, H | PH | 7);

#[derive(Clone, Copy)]
pub struct Cut<P>(pub P);

macro_rules! tuple_cut_parser {
    ($t0:tt | $p0:tt | $idx0:tt, $($t:tt | $p:tt | $idx:tt),*) => {
        impl<
            I: Copy,
            Err,
            $t0, $($t),*,
            $p0, $($p),*
        > Parser<I, ($t0, $(Option<$t>),*), Vec<Err>, Err> for Cut<($p0, $($p),*)>
        where
            $p0: Parser<I, $t0, Vec<Err>, Err>,
            $($p: Parser<I, $t, Vec<Err>, Err>),*
        {
            fn parse(&self, input: I, state: &mut Vec<Err>) -> Result<(I, ($t0, $(Option<$t>),*)), Err> {
                let (input, val) = self.0.$idx0.parse(input, state)?;
                tuple_cut_parser!(self => input => state => val => $($t | $p | $idx),*)
            }
        }
    };
    ($self:expr => $input:expr => $state:expr => $($parsed:expr)+ => $t0:tt | $p0:tt | $idx0:tt, $($t:tt | $p:tt | $idx:tt),+) => ({
        let (input, val) = match $self.0.$idx0.parse($input, $state) {
            Ok((i, v)) => (i, Some(v)),
            Err(e) => {
                $state.push(e);
                ($input, None)
            }
        };
        tuple_cut_parser!($self => input => $state => $($parsed)+ val => $($t | $p | $idx),+)
    });
    ($self:expr => $input:expr => $state:expr => $($parsed:expr)+ => $t0:tt | $p0:tt | $idx0:tt) => ({
        match $self.0.$idx0.parse($input, $state) {
            Ok((input, val)) => Ok((input, ($($parsed),*, Some(val)))),
            Err(e) => {
                $state.push(e);
                Ok(($input, ($($parsed),*, None)))
            }
        }
    });
}

tuple_cut_parser!(A | PA | 0, B | PB | 1);
tuple_cut_parser!(A | PA | 0, B | PB | 1, C | PC | 2);
tuple_cut_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3);
tuple_cut_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4);
tuple_cut_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4, F | PF | 5);
tuple_cut_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4, F | PF | 5, G | PG | 6);
tuple_cut_parser!(A | PA | 0, B | PB | 1, C | PC | 2, D | PD | 3, E | PE | 4, F | PF | 5, G | PG | 6, H | PH | 7);

pub type Input<'a> = Span<&'a str>;

#[derive(Clone, Copy, Debug)]
pub enum Maybe<T, E> {
    Some(T),
    Hole(Span<E>),
}

impl<T: AstDebug, E> AstDebug for Maybe<T, E> {
    fn fmt(&self, s: &mut String, depth: usize) {
        match self {
            Maybe::Some(x) => x.fmt(s, depth),
            Maybe::Hole(x) => {
                s.push_str(&format!("{}Hole @ {}\n", " ".repeat(depth), x.start_offset))
            }
        }
    }
}

impl<T, E> Maybe<T, E> {
    pub fn map<U, F>(self, mut f: F) -> Maybe<U, E>
    where
        F: FnMut(T) -> U
    {
        match self {
            Maybe::Some(x) => Maybe::Some(f(x)),
            Maybe::Hole(span) => Maybe::Hole(span),
        }
    }
    pub fn and_then<U, F>(self, f: F) -> Maybe<U, E>
    where
        F: FnOnce(T) -> Maybe<U, E>
    {
        match self {
            Maybe::Some(x) => f(x),
            Maybe::Hole(span) => Maybe::Hole(span),
        }
    }
    pub fn unwrap_or_else<F>(self, f: F) -> T
    where
        F: Fn(Span<E>) -> T
    {
        match self {
            Maybe::Some(x) => x,
            Maybe::Hole(span) => f(span),
        }
    }
}

impl<T, E: Debug> Maybe<T, E> {
    pub fn raise_err(self, err: &mut Vec<Diagnostic>) -> Self {
        match &self {
            Maybe::Some(_) => {},
            Maybe::Hole(span) => {
                err.push(span.error(format!("{:?}", span.data)));
            },
        }
        self
    }
}

impl<T: ToSpan, E> ToSpan for Maybe<T, E> {
    fn to_span(&self) -> Span<()> {
        match self {
            Maybe::Some(x) => x.to_span(),
            Maybe::Hole(span) => span.to_span(),
        }
    }
}

/*pub fn maybe<'a: 'b, 'b, T, P, N: 'a + Copy, E: Copy>(
    x: P,
    err: E,
) -> impl Parser<&'b [Span<N>], Maybe<T, E>>
where
    P: Parser<&'b [Span<N>], T>,
{
    move |input| match x.parse(input) {
        Some((input, a)) => Some((input, Maybe::Some(a))),
        None => input
            .last()
            .map(|span| (input, Maybe::Hole(span.map(|_| err)))),
    }
}

pub fn pmatch<'a, P: Pattern + Copy>(pat: P) -> impl Parser<Input<'a>, Span<&'a str>> {
    move |input: Input<'a>| {
        let x = input.data.trim_start_matches(pat);
        if x.len() == input.data.len() {
            None
        } else {
            Some((
                Span {
                    data: x,
                    start_offset: input.start_offset + (input.data.len() - x.len()) as u32,
                    end_offset: input.end_offset,
                    path_id: input.path_id,
                },
                Span {
                    data: &input.data[..(input.data.len() - x.len())],
                    start_offset: input.start_offset,
                    end_offset: input.start_offset + (input.data.len() - x.len()) as u32,
                    path_id: input.path_id,
                },
            ))
        }
    }
}

pub fn is<'a, P: Pattern + Copy>(pat: P) -> impl Parser<Input<'a>, Span<&'a str>> {
    move |input: Input<'a>| {
        input.data.strip_prefix(pat).map(|x| {
            (
                Span {
                    data: x,
                    start_offset: input.start_offset + (input.data.len() - x.len()) as u32,
                    end_offset: input.end_offset,
                    path_id: input.path_id,
                },
                Span {
                    data: &input.data[..(input.data.len() - x.len())],
                    start_offset: input.start_offset,
                    end_offset: input.start_offset + (input.data.len() - x.len()) as u32,
                    path_id: input.path_id,
                },
            )
        })
    }
}*/

pub trait AstDebug {
    fn fmt(&self, s: &mut String, depth: usize);
}

impl<T: AstDebug> AstDebug for Box<T> {
    fn fmt(&self, s: &mut String, depth: usize) {
        self.as_ref().fmt(s, depth)
    }
}

impl<T: AstDebug> AstDebug for Vec<T> {
    fn fmt(&self, s: &mut String, depth: usize) {
        for x in self {
            x.fmt(s, depth);
        }
    }
}

impl AstDebug for String {
    fn fmt(&self, s: &mut String, depth: usize) {
        s.push_str(&format!("{}{}\n", " ".repeat(depth), self))
    }
}

impl AstDebug for &str {
    fn fmt(&self, s: &mut String, depth: usize) {
        s.push_str(&format!("{}{}\n", " ".repeat(depth), self))
    }
}

impl<T: std::fmt::Display> AstDebug for Span<T> {
    fn fmt(&self, s: &mut String, depth: usize) {
        s.push_str(&format!("{}{} @ {},{}\n", " ".repeat(depth), self.data, self.start_offset, self.end_offset))
    }
}
