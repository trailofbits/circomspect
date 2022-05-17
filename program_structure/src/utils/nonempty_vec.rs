use anyhow::{anyhow, Error};
use std::convert::TryFrom;
use std::ops::{Index, IndexMut};

pub struct NonEmptyVec<T> {
    head: T,
    tail: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    pub fn new(x: T) -> NonEmptyVec<T> {
        NonEmptyVec {
            head: x,
            tail: Vec::new(),
        }
    }

    pub fn first(&self) -> &T {
        &self.head
    }

    pub fn first_mut(&mut self) -> &mut T {
        &mut self.head
    }

    pub fn last(&self) -> &T {
        match self.tail.last() {
            Some(x) => x,
            None => &self.head,
        }
    }

    pub fn last_mut(&mut self) -> &mut T {
        match self.tail.last_mut() {
            Some(x) => x,
            None => &mut self.head,
        }
    }

    pub fn push(&mut self, x: T) {
        self.tail.push(x);
    }

    /// Pops the last element of the non-empty vector.
    ///
    /// Note: This method will return `None` when there is one element left in
    /// the vector to preserve the invariant of always being non-empty.
    pub fn pop(&mut self) -> Option<T> {
        self.tail.pop()
    }

    pub fn len(&self) -> usize {
        return self.tail.len() + 1;
    }

    pub fn iter(&self) -> NonEmptyIter<'_, T> {
        NonEmptyIter::new(self)
    }
}

pub struct NonEmptyIter<'a, T> {
    index: usize,
    vec: &'a NonEmptyVec<T>,
}

impl<'a, T> NonEmptyIter<'a, T> {
    fn new(vec: &'a NonEmptyVec<T>) -> NonEmptyIter<'a, T> {
        NonEmptyIter { index: 0, vec }
    }
}

impl<'a, T> Iterator for NonEmptyIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let x = if self.index == 0 {
            Some(&self.vec.head)
        } else {
            self.vec.tail.get(self.index - 1)
        };
        self.index += 1;
        x
    }
}

impl<T> Index<usize> for NonEmptyVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        match index {
            0 => &self.head,
            n => &self.tail[n - 1],
        }
    }
}

impl<T> Index<&usize> for NonEmptyVec<T> {
    type Output = T;

    fn index(&self, index: &usize) -> &Self::Output {
        match index {
            0 => &self.head,
            n => &self.tail[n - 1],
        }
    }
}

impl<T> IndexMut<usize> for NonEmptyVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        match index {
            0 => &mut self.head,
            n => &mut self.tail[n - 1],
        }
    }
}

impl<T> IndexMut<&usize> for NonEmptyVec<T> {
    fn index_mut(&mut self, index: &usize) -> &mut Self::Output {
        match index {
            0 => &mut self.head,
            n => &mut self.tail[n - 1],
        }
    }
}

impl<T> From<NonEmptyVec<T>> for Vec<T> {
    fn from(xs: NonEmptyVec<T>) -> Vec<T> {
        let mut res = Vec::with_capacity(xs.len());
        res.push(xs.head);
        res.extend(xs.tail);
        res
    }
}

impl<T: Clone> From<&NonEmptyVec<T>> for Vec<T> {
    fn from(xs: &NonEmptyVec<T>) -> Vec<T> {
        xs.iter().cloned().collect()
    }
}

impl<T> TryFrom<Vec<T>> for NonEmptyVec<T> {
    type Error = Error;

    fn try_from(mut xs: Vec<T>) -> Result<NonEmptyVec<T>, Error> {
        if let Some(x) = xs.pop() {
            Ok(NonEmptyVec { head: x, tail: xs })
        } else {
            Err(anyhow!(
                "cannot create a non-empty vector from an empty vector"
            ))
        }
    }
}

impl<T: Clone> TryFrom<&Vec<T>> for NonEmptyVec<T> {
    type Error = Error;

    fn try_from(xs: &Vec<T>) -> Result<NonEmptyVec<T>, Error> {
        if let Some(x) = xs.first() {
            Ok(NonEmptyVec {
                head: x.clone(),
                tail: xs[1..].iter().cloned().collect(),
            })
        } else {
            Err(anyhow!(
                "cannot create a non-empty vector from an empty vector"
            ))
        }
    }
}
