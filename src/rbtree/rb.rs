// Copyright 2017-2018 By tickdream125@hotmail.com.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cmp::Ord;
use std::cmp::Ordering;
use std::mem;

use super::node::{NodePtr, Color};


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
pub struct RBTree<K: Ord, V> {
   pub root: NodePtr<K, V>,
   pub len: usize,
   pub repeat: bool,
}


impl<K: Ord, V> RBTree<K, V> {
    /// Creates an empty `RBTree`.
    pub fn new() -> RBTree<K, V> {
        RBTree {
            root: NodePtr::null(),
            len: 0,
            repeat: false,
        }
    }

    pub fn new_repeat() -> RBTree<K, V> {
        RBTree {
            root: NodePtr::null(),
            len: 0,
            repeat: true,
        }
    }

    /// Returns the len of `RBTree`.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the `RBTree` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.root.is_null()
    }

    /*
     * 对红黑树的节点(x)进行左旋转
     *
     * 左旋示意图(对节点x进行左旋)：
     *      px                              px
     *     /                               /
     *    x                               y
     *   /  \      --(左旋)-->           / \                #
     *  lx   y                          x  ry
     *     /   \                       /  \
     *    ly   ry                     lx  ly
     *
     *
     */
    #[inline]
    unsafe fn left_rotate(&mut self, mut node: NodePtr<K, V>) {
        let mut temp = node.right();
        node.set_right(temp.left());

        if !temp.left().is_null() {
            temp.left().set_parent(node.clone());
        }

        temp.set_parent(node.parent());
        if node == self.root {
            self.root = temp.clone();
        } else if node == node.parent().left() {
            node.parent().set_left(temp.clone());
        } else {
            node.parent().set_right(temp.clone());
        }

        temp.set_left(node.clone());
        node.set_parent(temp.clone());
    }

    /*
     * 对红黑树的节点(y)进行右旋转
     *
     * 右旋示意图(对节点y进行左旋)：
     *            py                               py
     *           /                                /
     *          y                                x
     *         /  \      --(右旋)-->            /  \                     #
     *        x   ry                           lx   y
     *       / \                                   / \                   #
     *      lx  rx                                rx  ry
     *
     */
    #[inline]
    unsafe fn right_rotate(&mut self, mut node: NodePtr<K, V>) {
        let mut temp = node.left();
        node.set_left(temp.right());

        if !temp.right().is_null() {
            temp.right().set_parent(node.clone());
        }

        temp.set_parent(node.parent());
        if node == self.root {
            self.root = temp.clone();
        } else if node == node.parent().right() {
            node.parent().set_right(temp.clone());
        } else {
            node.parent().set_left(temp.clone());
        }

        temp.set_right(node.clone());
        node.set_parent(temp.clone());
    }

    /// replace value if key exist, if not exist insert it.
    /// # Examples
    /// ```
    /// use datastruct::RBTree;
    /// let mut m = RBTree::new();
    /// assert_eq!(m.len(), 0);
    /// m.insert(2, 4);
    /// assert_eq!(m.len(), 1);
    /// assert_eq!(m.replace_or_insert(2, 6).unwrap(), 4);
    /// assert_eq!(m.len(), 1);
    /// assert_eq!(*m.get(&2).unwrap(), 6);
    /// ```
    #[inline]
    pub fn replace_or_insert(&mut self, k: K, mut v: V) -> Option<V> {
        let node = self.find_node(&k);
        if node.is_null() {
            self.insert(k, v);
            return None;
        }

        unsafe {
            mem::swap(&mut v, &mut (*node.0).value);
        }

        Some(v)
    }

    #[inline]
    unsafe fn insert_fixup(&mut self, mut node: NodePtr<K, V>) {
        let mut parent;
        let mut gparent;

        while node.parent().is_red_color() {
            parent = node.parent();
            gparent = parent.parent();
            //若“父节点”是“祖父节点的左孩子”
            if parent == gparent.left() {
                // Case 1条件：叔叔节点是红色
                let mut uncle = gparent.right();
                if !uncle.is_null() && uncle.is_red_color() {
                    uncle.set_black_color();
                    parent.set_black_color();
                    gparent.set_red_color();
                    node = gparent;
                    continue;
                }

                // Case 2条件：叔叔是黑色，且当前节点是右孩子
                if parent.right() == node {
                    self.left_rotate(parent);
                    let temp = parent;
                    parent = node;
                    node = temp;
                }

                // Case 3条件：叔叔是黑色，且当前节点是左孩子。
                parent.set_black_color();
                gparent.set_red_color();
                self.right_rotate(gparent);
            } else {
                // Case 1条件：叔叔节点是红色
                let mut uncle = gparent.left();
                if !uncle.is_null() && uncle.is_red_color() {
                    uncle.set_black_color();
                    parent.set_black_color();
                    gparent.set_red_color();
                    node = gparent;
                    continue;
                }

                // Case 2条件：叔叔是黑色，且当前节点是右孩子
                if parent.left() == node {
                    self.right_rotate(parent);
                    let temp = parent;
                    parent = node;
                    node = temp;
                }

                // Case 3条件：叔叔是黑色，且当前节点是左孩子。
                parent.set_black_color();
                gparent.set_red_color();
                self.left_rotate(gparent);
            }
        }
        self.root.set_black_color();
    }

    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> bool {
        let mut node = NodePtr::new(k, v);
        let mut y = NodePtr::null();
        let mut x = self.root;

        while !x.is_null() {
            y = x;
            match node.cmp(&&mut x) {
                Ordering::Less => {
                    x = x.left();
                }
                Ordering::Greater => {
                    x = x.right();
                }
                Ordering::Equal => {
                    if !self.repeat {
                        return false;
                    }
                    x = x.right();
                }
            };
        }
        self.len += 1;
        node.set_parent(y);

        if y.is_null() {
            self.root = node;
        } else {
            match node.cmp(&&mut y) {
                Ordering::Less => {
                    y.set_left(node);
                }
                _ => {
                    y.set_right(node);
                }
            };
        }

        node.set_red_color();
        unsafe {
            self.insert_fixup(node);
        }
        true
    }

    #[inline]
    fn find_node(&self, k: &K) -> NodePtr<K, V> {
        if self.root.is_null() {
            return NodePtr::null();
        }
        let mut temp = &self.root;
        unsafe {
            loop {
                let next = match k.cmp(&(*temp.0).key) {
                    Ordering::Less => &mut (*temp.0).left,
                    Ordering::Greater => &mut (*temp.0).right,
                    Ordering::Equal => return *temp,
                };
                if next.is_null() {
                    break;
                }
                temp = next;
            }
        }
        NodePtr::null()
    }

    #[inline]
    pub fn first_child(&self) -> NodePtr<K, V> {
        if self.root.is_null() {
            NodePtr::null()
        } else {
            let mut temp = self.root;
            while !temp.left().is_null() {
                temp = temp.left();
            }
            return temp;
        }
    }

    #[inline]
    pub fn last_child(&self) -> NodePtr<K, V> {
        if self.root.is_null() {
            NodePtr::null()
        } else {
            let mut temp = self.root;
            while !temp.right().is_null() {
                temp = temp.right();
            }
            return temp;
        }
    }

    #[inline]
    pub fn get_first(&self) -> Option<(&K, &V)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some((&(*first.0).key, &(*first.0).value)) }
    }

    #[inline]
    pub fn get_last(&self) -> Option<(&K, &V)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some((&(*last.0).key, &(*last.0).value)) }
    }

    #[inline]
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some(self.delete(first)) }
    }

    #[inline]
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some(self.delete(last)) }
    }

    #[inline]
    pub fn get_first_mut(&mut self) -> Option<(&K, &mut V)> {
        let first = self.first_child();
        if first.is_null() {
            return None;
        }
        unsafe { Some((&(*first.0).key, &mut (*first.0).value)) }
    }

    #[inline]
    pub fn get_last_mut(&mut self) -> Option<(&K, &mut V)> {
        let last = self.last_child();
        if last.is_null() {
            return None;
        }
        unsafe { Some((&(*last.0).key, &mut (*last.0).value)) }
    }

    #[inline]
    pub fn get(&self, k: &K) -> Option<&V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }

        unsafe { Some(&(*node.0).value) }
    }

    #[inline]
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }

        unsafe { Some(&mut (*node.0).value) }
    }

    #[inline]
    pub fn contains_key(&self, k: &K) -> bool {
        let node = self.find_node(k);
        if node.is_null() {
            return false;
        }
        true
    }

    #[inline]
    fn clear_recurse(&mut self, current: NodePtr<K, V>) {
        if !current.is_null() {
            unsafe {
                self.clear_recurse(current.left());
                self.clear_recurse(current.right());
                Box::from_raw(current.0);
            }
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        let root = self.root;
        self.root = NodePtr::null();
        self.clear_recurse(root);
    }

    /// Empties the `RBTree` without freeing objects in it.
    #[inline]
    pub(crate) fn fast_clear(&mut self) {
        self.root = NodePtr::null();
    }

    #[inline]
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }
        unsafe { Some(self.delete(node).1) }
    }

    #[inline]
    unsafe fn delete_fixup(&mut self, mut node: NodePtr<K, V>, mut parent: NodePtr<K, V>) {
        let mut other;
        while node != self.root && node.is_black_color() {
            if parent.left() == node {
                other = parent.right();
                //x的兄弟w是红色的
                if other.is_red_color() {
                    other.set_black_color();
                    parent.set_red_color();
                    self.left_rotate(parent);
                    other = parent.right();
                }

                //x的兄弟w是黑色，且w的俩个孩子也都是黑色的
                if other.left().is_black_color() && other.right().is_black_color() {
                    other.set_red_color();
                    node = parent;
                    parent = node.parent();
                } else {
                    //x的兄弟w是黑色的，并且w的左孩子是红色，右孩子为黑色。
                    if other.right().is_black_color() {
                        other.left().set_black_color();
                        other.set_red_color();
                        self.right_rotate(other);
                        other = parent.right();
                    }
                    //x的兄弟w是黑色的；并且w的右孩子是红色的，左孩子任意颜色。
                    other.set_color(parent.get_color());
                    parent.set_black_color();
                    other.right().set_black_color();
                    self.left_rotate(parent);
                    node = self.root;
                    break;
                }
            } else {
                other = parent.left();
                //x的兄弟w是红色的
                if other.is_red_color() {
                    other.set_black_color();
                    parent.set_red_color();
                    self.right_rotate(parent);
                    other = parent.left();
                }

                //x的兄弟w是黑色，且w的俩个孩子也都是黑色的
                if other.left().is_black_color() && other.right().is_black_color() {
                    other.set_red_color();
                    node = parent;
                    parent = node.parent();
                } else {
                    //x的兄弟w是黑色的，并且w的左孩子是红色，右孩子为黑色。
                    if other.left().is_black_color() {
                        other.right().set_black_color();
                        other.set_red_color();
                        self.left_rotate(other);
                        other = parent.left();
                    }
                    //x的兄弟w是黑色的；并且w的右孩子是红色的，左孩子任意颜色。
                    other.set_color(parent.get_color());
                    parent.set_black_color();
                    other.left().set_black_color();
                    self.right_rotate(parent);
                    node = self.root;
                    break;
                }
            }
        }

        node.set_black_color();
    }

    #[inline]
    unsafe fn delete(&mut self, node: NodePtr<K, V>) -> (K, V) {
        let mut child;
        let mut parent;
        let color;

        self.len -= 1;
        // 被删除节点的"左右孩子都不为空"的情况。
        if !node.left().is_null() && !node.right().is_null() {
            // 被删节点的后继节点。(称为"取代节点")
            // 用它来取代"被删节点"的位置，然后再将"被删节点"去掉。
            let mut replace = node.right().min_node();
            if node == self.root {
                self.root = replace;
            } else {
                if node.parent().left() == node {
                    node.parent().set_left(replace);
                } else {
                    node.parent().set_right(replace);
                }
            }

            // child是"取代节点"的右孩子，也是需要"调整的节点"。
            // "取代节点"肯定不存在左孩子！因为它是一个后继节点。
            child = replace.right();
            parent = replace.parent();
            color = replace.get_color();
            if parent == node {
                parent = replace;
            } else {
                if !child.is_null() {
                    child.set_parent(parent);
                }
                parent.set_left(child);
                replace.set_right(node.right());
                node.right().set_parent(replace);
            }

            replace.set_parent(node.parent());
            replace.set_color(node.get_color());
            replace.set_left(node.left());
            node.left().set_parent(replace);

            if color == Color::Black {
                self.delete_fixup(child, parent);
            }

            let obj = Box::from_raw(node.0);
            return obj.pair();
        }

        if !node.left().is_null() {
            child = node.left();
        } else {
            child = node.right();
        }

        parent = node.parent();
        color = node.get_color();
        if !child.is_null() {
            child.set_parent(parent);
        }

        if self.root == node {
            self.root = child
        } else {
            if parent.left() == node {
                parent.set_left(child);
            } else {
                parent.set_right(child);
            }
        }

        if color == Color::Black {
            self.delete_fixup(child, parent);
        }

        let obj = Box::from_raw(node.0);
        return obj.pair();
    }

}
