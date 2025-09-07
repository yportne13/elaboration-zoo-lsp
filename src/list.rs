use std::rc::Rc;
use std::fmt::{Debug, Formatter};

#[derive(Default, Clone)]
pub struct List<T> {
    pub head: Link<T>,
}

impl<T: Debug> Debug for List<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

pub type Link<T> = Option<Rc<Node<T>>>;

#[derive(Debug)]
pub struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: None }
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    pub fn prepend(&self, elem: T) -> List<T> {
        List { head: Some(Rc::new(Node {
            elem,
            next: self.head.clone(),
        }))}
    }

    pub fn head(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn tail(&self) -> List<T> {
        List { head: self.head.as_ref().and_then(|node| node.next.clone()) }
    }

    pub fn len(&self) -> usize {
        self.iter().count()
    }

    pub fn map<U, F>(&self, f: F) -> List<U>
    where
        F: Fn(&T) -> U + Copy,
    {
        match self {
            List { head: None } => List::new(),
            x => x.tail().map(f).prepend(f(self.head().unwrap()))
        }
    }
}

impl<T: Clone> List<T> {
    pub fn change_n(&self, n: usize, f: impl FnOnce(&T) -> T) -> List<T> {
        if n == 0 {
            self.tail().prepend(f(self.head().unwrap()))
        } else {
            self.tail().change_n(n - 1, f).prepend(self.head().unwrap().clone())
        }
    }

    pub fn change_tail(self, new_tail: List<T>) -> List<T> {
        let head_len = self.len() - new_tail.len();
        self.change_tail_helper(new_tail, head_len)
    }

    fn change_tail_helper(self, new_tail: List<T>, head_len: usize) -> List<T> {
        if head_len == 0 {
            new_tail
        } else {
            self.tail().change_tail_helper(new_tail, head_len - 1).prepend(self.head().unwrap().clone())
        }
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
