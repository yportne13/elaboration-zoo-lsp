use std::num::NonZeroUsize;


pub struct ListArena<T>(Vec<(T, Option<NonZeroUsize>)>);

impl<T: Default> ListArena<T> {
    pub fn new() -> Self {
        Self(vec![(T::default(), None)])
    }
}

impl<T> ListArena<T> {
    pub fn alloc(&mut self, value: T) -> NonZeroUsize {
        let index = self.0.len();
        self.0.push((value, None));
        unsafe { NonZeroUsize::new_unchecked(index) }
    }

    pub fn prepend(&mut self, list: NonZeroUsize, value: T) -> NonZeroUsize {
        let index = self.0.len();
        self.0.push((value, Some(list)));
        unsafe { NonZeroUsize::new_unchecked(index) }
    }

    pub fn nth(&self, list: NonZeroUsize, idx: usize) -> &T {
        let mut list = list;
        for _ in 0..idx {
            list = unsafe { self.0.get_unchecked(list.get()).1.unwrap_unchecked() };
        }
        unsafe { &self.0.get_unchecked(list.get()).0 }
    }
}
