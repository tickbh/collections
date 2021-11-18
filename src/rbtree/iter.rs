// Copyright 2017-2018 By tickdream125@hotmail.com.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cmp::Ord;
use std::fmt::{self, Debug};
use std::iter::{FromIterator, IntoIterator};
use std::marker;
use std::ops::Index;

use super::rb::RBTree;
use super::node::NodePtr;


// Drop all owned pointers if the tree is dropped
impl<K: Ord, V> Drop for RBTree<K, V> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

/// If key and value are both impl Clone, we can call clone to get a copy.
impl<K: Ord + Clone, V: Clone> Clone for RBTree<K, V> {
    fn clone(&self) -> RBTree<K, V> {
        unsafe {
            let mut new = RBTree::new();
            new.root = self.root.deep_clone();
            new.len = self.len;
            new
        }
    }
}

impl<K, V> Debug for RBTree<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// This is a method to help us to get inner struct.
impl<K: Ord + Debug, V: Debug> RBTree<K, V> {
    fn tree_print(&self, node: NodePtr<K, V>, direction: i32) {
        if node.is_null() {
            return;
        }
        if direction == 0 {
            unsafe {
                println!("'{:?}' is root node", (*node.0));
            }
        } else {
            let direct = if direction == -1 { "left" } else { "right" };
            unsafe {
                println!(
                    "{:?} is {:?}'s {:?} child ",
                    (*node.0),
                    *node.parent().0,
                    direct
                );
            }
        }
        self.tree_print(node.left(), -1);
        self.tree_print(node.right(), 1);
    }

    pub fn print_tree(&self) {
        if self.root.is_null() {
            println!("This is a empty tree");
            return;
        }
        println!("This tree size = {:?}, begin:-------------", self.len());
        self.tree_print(self.root, 0);
        println!("end--------------------------");
    }
}

/// all key be same, but it has multi key, if has multi key, it perhaps no correct
impl<K, V> PartialEq for RBTree<K, V>
where
    K: Eq + Ord,
    V: PartialEq,
{
    fn eq(&self, other: &RBTree<K, V>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V> Eq for RBTree<K, V>
where
    K: Eq + Ord,
    V: Eq,
{
}

impl<'a, K, V> Index<&'a K> for RBTree<K, V>
where
    K: Ord,
{
    type Output = V;

    #[inline]
    fn index(&self, index: &K) -> &V {
        self.get(index).expect("no entry found for key")
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for RBTree<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> RBTree<K, V> {
        let mut tree = RBTree::new();
        tree.extend(iter);
        tree
    }
}

/// RBTree into iter
impl<K: Ord, V> Extend<(K, V)> for RBTree<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// provide the rbtree all keys
/// # Examples
/// ```
/// use datastruct::RBTree;
/// let mut m = RBTree::new();
/// for i in 1..6 {
///     m.insert(i, i);
/// }
/// let vec = vec![1, 2, 3, 4, 5];
/// let key_vec: Vec<_> = m.keys().cloned().collect();
/// assert_eq!(vec, key_vec);
/// ```
pub struct Keys<'a, K: Ord + 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: Ord, V> Clone for Keys<'a, K, V> {
    fn clone(&self) -> Keys<'a, K, V> {
        Keys {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug, V> fmt::Debug for Keys<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// provide the rbtree all values order by key
/// # Examples
/// ```
/// use datastruct::RBTree;
/// let mut m = RBTree::new();
/// m.insert(2, 5);
/// m.insert(1, 6);
/// m.insert(3, 8);
/// m.insert(4, 9);
/// let vec = vec![6, 5, 8, 9];
/// let key_vec: Vec<_> = m.values().cloned().collect();
/// assert_eq!(vec, key_vec);
/// ```
pub struct Values<'a, K: 'a + Ord, V: 'a> {
    inner: Iter<'a, K, V>,
}

impl<'a, K: Ord, V> Clone for Values<'a, K, V> {
    fn clone(&self) -> Values<'a, K, V> {
        Values {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug, V: Debug> fmt::Debug for Values<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// provide the rbtree all values and it can be modify
/// # Examples
/// ```
/// use datastruct::RBTree;
/// let mut m = RBTree::new();
/// for i in 0..32 {
///     m.insert(i, i);
/// }
/// assert_eq!(m.len(), 32);
/// for v in m.values_mut() {
///     *v *= 2;
/// }
/// for i in 0..32 {
///     assert_eq!(m.get(&i).unwrap(), &(i * 2));
/// }
/// ```
pub struct ValuesMut<'a, K: 'a + Ord, V: 'a> {
    inner: IterMut<'a, K, V>,
}

impl<'a, K: Ord, V> Clone for ValuesMut<'a, K, V> {
    fn clone(&self) -> ValuesMut<'a, K, V> {
        ValuesMut {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K: Ord + Debug, V: Debug> fmt::Debug for ValuesMut<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, v)| v)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// Convert RBTree to iter, move out the tree.
pub struct IntoIter<K: Ord, V> {
    head: NodePtr<K, V>,
    tail: NodePtr<K, V>,
    len: usize,
}

// Drop all owned pointers if the collection is dropped
impl<K: Ord, V> Drop for IntoIter<K, V> {
    #[inline]
    fn drop(&mut self) {
        for (_, _) in self {}
    }
}

impl<K: Ord, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let next = self.head.next();
        let obj = unsafe { Box::from_raw(self.head.0) };
        let (k, v) = obj.pair();
        self.head = next;
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<K: Ord, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(K, V)> {
        if self.len == 0 {
            return None;
        }

        if self.tail.is_null() {
            return None;
        }

        let prev = self.tail.prev();
        let obj = unsafe { Box::from_raw(self.tail.0) };
        let (k, v) = obj.pair();
        self.tail = prev;
        self.len -= 1;
        Some((k, v))
    }
}

/// provide iter ref for RBTree
/// # Examples
/// ```
/// use datastruct::RBTree;
/// let mut m = RBTree::new();
/// for i in 0..32 {
///     m.insert(i, i * 2);
/// }
/// assert_eq!(m.len(), 32);
/// let mut observed: u32 = 0;
/// for (k, v) in m.iter() {
///     assert_eq!(*v, *k * 2);
///     observed |= 1 << *k;
/// }
/// assert_eq!(observed, 0xFFFF_FFFF);
/// ```
pub struct Iter<'a, K: Ord + 'a, V: 'a> {
    head: NodePtr<K, V>,
    tail: NodePtr<K, V>,
    len: usize,
    _marker: marker::PhantomData<&'a ()>,
}

impl<'a, K: Ord + 'a, V: 'a> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: self._marker,
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let (k, v) = unsafe { (&(*self.head.0).key, &(*self.head.0).value) };
        self.head = self.head.next();
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K: Ord + 'a, V: 'a> DoubleEndedIterator for Iter<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        // println!("len = {:?}", self.len);
        if self.len == 0 {
            return None;
        }

        if self.tail == self.head {
            return None;
        }

        let (k, v) = unsafe { (&(*self.tail.0).key, &(*self.tail.0).value) };
        self.tail = self.tail.prev();
        self.len -= 1;
        Some((k, v))
    }
}

/// provide iter mut ref for RBTree
/// # Examples
/// ```
/// use datastruct::RBTree;
/// let mut m = RBTree::new();
/// for i in 0..32 {
///     m.insert(i, i);
/// }
/// assert_eq!(m.len(), 32);
/// for (_, v) in m.iter_mut() {
///     *v *= 2;
/// }
/// for i in 0..32 {
///     assert_eq!(m.get(&i).unwrap(), &(i * 2));
/// }
/// ```
pub struct IterMut<'a, K: Ord + 'a, V: 'a> {
    head: NodePtr<K, V>,
    tail: NodePtr<K, V>,
    len: usize,
    _marker: marker::PhantomData<&'a ()>,
}

impl<'a, K: Ord + 'a, V: 'a> Clone for IterMut<'a, K, V> {
    fn clone(&self) -> IterMut<'a, K, V> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: self._marker,
        }
    }
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        if self.head.is_null() {
            return None;
        }

        let (k, v) = unsafe { (&(*self.head.0).key, &mut (*self.head.0).value) };
        self.head = self.head.next();
        self.len -= 1;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, K: Ord + 'a, V: 'a> DoubleEndedIterator for IterMut<'a, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> {
        if self.len == 0 {
            return None;
        }

        if self.tail == self.head {
            return None;
        }

        let (k, v) = unsafe { (&(*self.tail.0).key, &mut (*self.tail.0).value) };
        self.tail = self.tail.prev();
        self.len -= 1;
        Some((k, v))
    }
}

impl<K: Ord, V> IntoIterator for RBTree<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(mut self) -> IntoIter<K, V> {
        let iter = if self.root.is_null() {
            IntoIter {
                head: NodePtr::null(),
                tail: NodePtr::null(),
                len: self.len,
            }
        } else {
            IntoIter {
                head: self.first_child(),
                tail: self.last_child(),
                len: self.len,
            }
        };
        self.fast_clear();
        iter
    }
}


/// A red black tree implemented with Rust
/// It is required that the keys implement the [`Ord`] traits.

/// # Examples
/// ```rust
/// use datastruct::RBTree;
/// // type inference lets us omit an explicit type signature (which
/// // would be `RBTree<&str, &str>` in this example).
/// let mut book_reviews = RBTree::new();
///
/// // review some books.
/// book_reviews.insert("Adventures of Huckleberry Finn", "My favorite book.");
/// book_reviews.insert("Grimms' Fairy Tales", "Masterpiece.");
/// book_reviews.insert("Pride and Prejudice", "Very enjoyable.");
/// book_reviews.insert("The Adventures of Sherlock Holmes", "Eye lyked it alot.");
///
/// // check for a specific one.
/// if !book_reviews.contains_key(&"Les Misérables") {
///     println!(
///         "We've got {} reviews, but Les Misérables ain't one.",
///         book_reviews.len()
///     );
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// book_reviews.remove(&"The Adventures of Sherlock Holmes");
///
/// // look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for book in &to_find {
///     match book_reviews.get(book) {
///         Some(review) => println!("{}: {}", book, review),
///         None => println!("{} is unreviewed.", book),
///     }
/// }
///
/// // iterate over everything.
/// for (book, review) in book_reviews.iter() {
///     println!("{}: \"{}\"", book, review);
/// }
///
/// book_reviews.print_tree();
/// ```
///
/// // A `RBTree` with fixed list of elements can be initialized from an array:
///  ```
/// use datastruct::RBTree;
///  let timber_resources: RBTree<&str, i32> =
///  [("Norway", 100),
///   ("Denmark", 50),
///   ("Iceland", 10)]
///   .iter().cloned().collect();
///  // use the values stored in rbtree
///  ```
 
 impl<K: Ord, V> RBTree<K, V> {
 
     /// Return the keys iter
     #[inline]
     pub fn keys(&self) -> Keys<K, V> {
         Keys { inner: self.iter() }
     }
 
     /// Return the value iter
     #[inline]
     pub fn values(&self) -> Values<K, V> {
         Values { inner: self.iter() }
     }
 
     /// Return the value iter mut
     #[inline]
     pub fn values_mut(&mut self) -> ValuesMut<K, V> {
         ValuesMut {
             inner: self.iter_mut(),
         }
     }
 
     /// Return the key and value iter
     #[inline]
     pub fn iter(&self) -> Iter<K, V> {
         Iter {
             head: self.first_child(),
             tail: self.last_child(),
             len: self.len,
             _marker: marker::PhantomData,
         }
     }
 
     /// Return the key and mut value iter
     #[inline]
     pub fn iter_mut(&mut self) -> IterMut<K, V> {
         IterMut {
             head: self.first_child(),
             tail: self.last_child(),
             len: self.len,
             _marker: marker::PhantomData,
         }
     }
 }