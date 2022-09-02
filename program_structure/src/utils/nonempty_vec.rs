use anyhow::{anyhow, Error};
use std::convert::TryFrom;
use std::ops::{Index, IndexMut};

/// A vector type which is guaranteed to be non-empty.
///
/// New instances must be created with an initial element to ensure that the
/// vector is non-empty. This means that the methods `first` and `last` always
/// produce an element of type `T`.
///
/// ```
/// # use program_structure::nonempty_vec::NonEmptyVec;
///
/// let v = NonEmptyVec::new(1);
/// assert_eq!(*v.first(), 1);
/// assert_eq!(*v.last(), 1);
/// ```
///
/// It is possible to `push` new elements into the vector, but `pop` will return
/// `None` if there is only one element left to ensure that the vector is always
/// nonempty.
///
/// ```
/// # use program_structure::nonempty_vec::NonEmptyVec;
///
/// let mut v = NonEmptyVec::new(1);
/// v.push(2);
/// assert_eq!(v.pop(), Some(2));
/// assert_eq!(v.pop(), None);
/// ```
#[derive(Clone, PartialEq)]
pub struct NonEmptyVec<T> {
    head: T,
    tail: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    pub fn new(x: T) -> NonEmptyVec<T> {
        NonEmptyVec { head: x, tail: Vec::new() }
    }

    pub fn first(&self) -> &T {
        &self.head
    }

    pub fn first_mut(&mut self) -> &mut T {
        &mut self.head
    }

    /// Returns a reference to the last element.
    pub fn last(&self) -> &T {
        match self.tail.last() {
            Some(x) => x,
            None => &self.head,
        }
    }

    /// Returns a mutable reference to the last element.
    pub fn last_mut(&mut self) -> &mut T {
        match self.tail.last_mut() {
            Some(x) => x,
            None => &mut self.head,
        }
    }

    /// Append an element to the vector.
    pub fn push(&mut self, x: T) {
        self.tail.push(x);
    }

    /// Pops the last element of the vector.
    ///
    /// This method will return `None` when there is one element left in the
    /// vector to ensure that the vector remains non-empty.
    ///
    /// ```
    /// # use program_structure::nonempty_vec::NonEmptyVec;
    ///
    /// let mut v = NonEmptyVec::new(1);
    /// v.push(2);
    /// assert_eq!(v.pop(), Some(2));
    /// assert_eq!(v.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.tail.pop()
    }

    /// Returns the length of the vector.
    ///
    /// ```
    /// # use program_structure::nonempty_vec::NonEmptyVec;
    ///
    /// let mut v = NonEmptyVec::new(1);
    /// v.push(2);
    /// v.push(3);
    /// assert_eq!(v.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }

    /// Always returns false.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Returns an iterator over the vector.
    pub fn iter(&self) -> NonEmptyIter<'_, T> {
        NonEmptyIter::new(self)
    }
}

/// Allows for constructions on the form `for t in ts`.
impl<'a, T> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = NonEmptyIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        NonEmptyIter::new(self)
    }
}

/// An iterator over a non-empty vector.
///
/// ```
/// # use program_structure::nonempty_vec::NonEmptyVec;
/// # use std::convert::TryFrom;
/// let v = NonEmptyVec::try_from(&[1, 2, 3]).unwrap();
///
/// let mut iter = v.iter();
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), Some(&3));
/// assert_eq!(iter.next(), None);
/// ```
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
            // self.index > 0 here so the subtraction cannot underflow.
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
            Err(anyhow!("cannot create a non-empty vector from an empty vector"))
        }
    }
}

impl<T: Clone> TryFrom<&Vec<T>> for NonEmptyVec<T> {
    type Error = Error;

    fn try_from(xs: &Vec<T>) -> Result<NonEmptyVec<T>, Error> {
        if let Some(x) = xs.first() {
            Ok(NonEmptyVec { head: x.clone(), tail: xs[1..].to_vec() })
        } else {
            Err(anyhow!("cannot create a non-empty vector from an empty vector"))
        }
    }
}

impl<T: Clone> TryFrom<&[T]> for NonEmptyVec<T> {
    type Error = Error;

    fn try_from(xs: &[T]) -> Result<NonEmptyVec<T>, Error> {
        if let Some(x) = xs.first() {
            Ok(NonEmptyVec { head: x.clone(), tail: xs[1..].to_vec() })
        } else {
            Err(anyhow!("cannot create a non-empty vector from an empty vector"))
        }
    }
}

impl<T: Clone, const N: usize> TryFrom<&[T; N]> for NonEmptyVec<T> {
    type Error = Error;

    fn try_from(xs: &[T; N]) -> Result<NonEmptyVec<T>, Error> {
        if let Some(x) = xs.first() {
            Ok(NonEmptyVec { head: x.clone(), tail: xs[1..].to_vec() })
        } else {
            Err(anyhow!("cannot create a non-empty vector from an empty vector"))
        }
    }
}
