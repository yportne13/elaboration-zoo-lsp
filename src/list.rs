use std::sync::Arc as Rc;
use std::fmt::{Debug, Formatter};

#[derive(Default, Clone)]
pub struct List<T> {
    pub head: Link<T>,
    pub size: usize,
}

impl<T: Debug> Debug for List<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

pub type Link<T> = Option<Rc<Node<T>>>;

#[derive(Debug)]
pub struct Node<T> {
    pub elem: T,
    pub size: usize,
    pub next: Link<T>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: None, size: 0 }
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn prepend(&self, elem: T) -> List<T> {
        List {
            size: self.size + 1,
            head: Some(Rc::new(Node {
                elem,
                size: self.size + 1,
                next: self.head.clone(),
            })),
        }
    }

    pub fn head(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn tail(&self) -> List<T> {
        match self.head.as_ref() {
            None => List { head: None, size: 0 },
            Some(node) => List {
                size: node.next.as_ref().map(|n| n.size).unwrap_or(0),
                head: node.next.clone(),
            },
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn map<U, F>(&self, f: F) -> List<U>
    where
        F: Fn(&T) -> U,
    {
        let mut buf: Vec<U> = Vec::with_capacity(self.len());
        for elem in self.iter() {
            buf.push(f(elem));
        }
        let mut result = List::new();
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        result
    }

    pub fn flat_map<U, F>(&self, f: F) -> List<U>
    where
        F: Fn(&T) -> Option<U>,
    {
        let mut buf: Vec<U> = Vec::with_capacity(self.len());
        for elem in self.iter() {
            if let Some(mapped) = f(elem) {
                buf.push(mapped);
            }
        }
        let mut result = List::new();
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        result
    }

    pub fn result_map<U, E, F>(&self, f: F) -> Result<List<U>, E>
    where
        F: FnMut(&T) -> Result<U, E>,
    {
        let mut buf: Vec<U> = Vec::with_capacity(self.len());
        let mut f = f;
        for elem in self.iter() {
            buf.push(f(elem)?);
        }
        let mut result = List::new();
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        Ok(result)
    }

    pub fn split(&self) -> (Option<&T>, List<T>) {
        match self {
            List { head: None, .. } => (None, List::new()),
            x => (x.head(), x.tail()),
        }
    }
}

impl<T: Clone> List<T> {
    pub fn filter<F>(&self, f: F) -> List<T>
    where
        F: Fn(&T) -> bool,
    {
        let mut buf: Vec<T> = Vec::with_capacity(self.len());
        for elem in self.iter() {
            if f(elem) {
                buf.push(elem.clone());
            }
        }
        let mut result = List::new();
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        result
    }

    pub fn change_n(&self, n: usize, f: impl FnOnce(&T) -> T) -> List<T> {
        let mut f = Some(f);
        let mut buf: Vec<T> = Vec::with_capacity(self.len());
        for (i, elem) in self.iter().enumerate() {
            if i == n {
                buf.push(f.take().unwrap()(elem));
            } else {
                buf.push(elem.clone());
            }
        }
        let mut result = List::new();
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        result
    }

    pub fn change_tail(self, new_tail: List<T>) -> List<T> {
        let head_len = self.len() - new_tail.len();
        let mut buf: Vec<T> = Vec::with_capacity(head_len);
        for elem in self.iter().take(head_len) {
            buf.push(elem.clone());
        }
        let mut result = new_tail;
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        result
    }

    pub fn zip<U: Clone>(&self, other: &List<U>) -> List<(T, U)> {
        let mut buf: Vec<(T, U)> = Vec::with_capacity(self.len().min(other.len()));
        let mut other_iter = other.iter();
        for elem in self.iter() {
            match other_iter.next() {
                Some(other_elem) => buf.push((elem.clone(), other_elem.clone())),
                None => break,
            }
        }
        let mut result = List::new();
        for elem in buf.into_iter().rev() {
            result = result.prepend(elem);
        }
        result
    }

    pub fn split_at(self, n: usize) -> (List<T>, List<T>) {
        let mut left_buf: Vec<T> = Vec::with_capacity(n);
        let mut right_buf: Vec<T> = Vec::with_capacity(self.len().saturating_sub(n));
        for (i, elem) in self.iter().enumerate() {
            if i < n {
                left_buf.push(elem.clone());
            } else {
                right_buf.push(elem.clone());
            }
        }
        let mut left = List::new();
        for elem in left_buf.into_iter().rev() {
            left = left.prepend(elem);
        }
        let mut right = List::new();
        for elem in right_buf.into_iter().rev() {
            right = right.prepend(elem);
        }
        (left, right)
    }
}

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<T> List<T> {
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { next: self.head.as_deref() }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_deref();
            &node.elem
        })
    }
}
