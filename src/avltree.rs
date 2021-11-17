use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::iter::{FromIterator, IntoIterator};
use std::marker;
use std::mem;
use std::ops::Index;
use std::ptr;

/*****************AVLTreeNode***************************/
struct AVLTreeNode<K: Ord, V> {
    left: NodePtr<K, V>,
    right: NodePtr<K, V>,
    parent: NodePtr<K, V>,
    key: K,
    value: V,
    bf: i8,
}

impl<K, V> Debug for AVLTreeNode<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "k:{:?} v:{:?}, bf:{:?}", self.key, self.value, self.bf)
    }
}

impl<K: Ord, V> AVLTreeNode<K, V> {
    #[inline]
    fn pair(self) -> (K, V) {
        (self.key, self.value)
    }
}

/*****************NodePtr***************************/
#[derive(Debug)]
struct NodePtr<K: Ord, V>(*mut AVLTreeNode<K, V>);

impl<K: Ord, V> Clone for NodePtr<K, V> {
    fn clone(&self) -> NodePtr<K, V> {
        NodePtr(self.0)
    }
}

impl<K: Ord, V> Copy for NodePtr<K, V> {}

impl<K: Ord, V> Ord for NodePtr<K, V> {
    fn cmp(&self, other: &NodePtr<K, V>) -> Ordering {
        unsafe { (*self.0).key.cmp(&(*other.0).key) }
    }
}

impl<K: Ord, V> PartialOrd for NodePtr<K, V> {
    fn partial_cmp(&self, other: &NodePtr<K, V>) -> Option<Ordering> {
        unsafe { Some((*self.0).key.cmp(&(*other.0).key)) }
    }
}

impl<K: Ord, V> PartialEq for NodePtr<K, V> {
    fn eq(&self, other: &NodePtr<K, V>) -> bool {
        self.0 == other.0
    }
}

impl<K: Ord, V> Eq for NodePtr<K, V> {}

impl<K: Ord, V> NodePtr<K, V> {
    fn new(k: K, v: V) -> NodePtr<K, V> {
        let node = AVLTreeNode {
            left: NodePtr::null(),
            right: NodePtr::null(),
            parent: NodePtr::null(),
            key: k,
            value: v,
            bf: 0,
        };
        NodePtr(Box::into_raw(Box::new(node)))
    }

    #[inline]
    fn is_left_child(&self) -> bool {
        self.parent().left() == *self
    }

    #[inline]
    fn is_right_child(&self) -> bool {
        self.parent().right() == *self
    }

    #[inline]
    fn min_node(self) -> NodePtr<K, V> {
        let mut temp = self.clone();
        while !temp.left().is_null() {
            temp = temp.left();
        }
        return temp;
    }

    #[inline]
    fn max_node(self) -> NodePtr<K, V> {
        let mut temp = self.clone();
        while !temp.right().is_null() {
            temp = temp.right();
        }
        return temp;
    }

    #[inline]
    fn next(self) -> NodePtr<K, V> {
        if !self.right().is_null() {
            self.right().min_node()
        } else {
            let mut temp = self;
            loop {
                if temp.parent().is_null() {
                    return NodePtr::null();
                }
                if temp.is_left_child() {
                    return temp.parent();
                }
                temp = temp.parent();
            }
        }
    }

    #[inline]
    fn prev(self) -> NodePtr<K, V> {
        if !self.left().is_null() {
            self.left().max_node()
        } else {
            let mut temp = self;
            loop {
                if temp.parent().is_null() {
                    return NodePtr::null();
                }
                if temp.is_right_child() {
                    return temp.parent();
                }
                temp = temp.parent();
            }
        }
    }

    #[inline]
    fn set_parent(&mut self, parent: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).parent = parent }
    }

    #[inline]
    fn set_left(&mut self, left: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).left = left }
    }

    #[inline]
    fn set_right(&mut self, right: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).right = right }
    }

    #[inline]
    fn parent(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).parent.clone() }
    }

    #[inline]
    fn left(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).left.clone() }
    }

    #[inline]
    fn right(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).right.clone() }
    }

    #[inline]
    fn null() -> NodePtr<K, V> {
        NodePtr(ptr::null_mut())
    }

    #[inline]
    fn is_null(&self) -> bool {
        self.0.is_null()
    }

    #[inline]
    fn bf_mut(&self) -> &mut i8 {
        unsafe { &mut (*self.0).bf }
    }

    #[inline]
    fn set_bf(&self, bf: i8) {
        unsafe {  (*self.0).bf   = bf; }
    }
    
    #[inline]
    fn add_bf(&self, bf: i8) -> i8 {
        unsafe {  (*self.0).bf += bf; (*self.0).bf }
    }

    #[inline]
    fn bf(&self) -> i8 {
        unsafe { (*self.0).bf }
    }
}

pub struct AVLTree<K: Ord, V> {
    root: NodePtr<K, V>,
    len: usize,
    height: usize,
}


impl<K, V> Debug for AVLTree<K, V>
where
    K: Ord + Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// This is a method to help us to get inner struct.
impl<K: Ord + Debug, V: Debug> AVLTree<K, V> {
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

impl<K: Ord, V> IntoIterator for AVLTree<K, V> {
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


impl<K: Ord, V> AVLTree<K, V> {
    /// Creates an empty `AVLTree`.
    pub fn new() -> AVLTree<K, V> {
        AVLTree {
            root: NodePtr::null(),
            len: 0,
            height: 0,
        }
    }

    /// Returns the len of `AVLTree`.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the `AVLTree` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.root.is_null()
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
    pub fn insert(&mut self, k: K, v: V) {
        self.len += 1;
        let mut node = NodePtr::new(k, v);
        let mut parent = NodePtr::null();
        let mut tmp = self.root;

        while !tmp.is_null() {
            parent = tmp;
            match node.cmp(&&mut tmp) {
                Ordering::Less => {
                    tmp = tmp.left();
                }
                _ => {
                    tmp = tmp.right();
                }
            };
        }
        node.set_parent(parent);

        if parent.is_null() {
            self.root = node;
            self.height = 1;
            return;
        }

        match node.cmp(&&mut parent) {
            Ordering::Less => {
                parent.set_left(node);
            }
            _ => {
                parent.set_right(node);
            }
        };

        self.fixup_node(node, true);
    }

    fn fixup_node(&mut self,mut node: NodePtr<K, V>, is_add: bool) {
        let mut parent = node.parent();
        let step = if is_add {1} else {-1};
        while !parent.is_null() {
            if node == parent.left() {
                *parent.bf_mut() -= step;
            } else {
                *parent.bf_mut() += step;
            }

            if parent.bf() == 0 {
                break;
            } else if parent.bf() == -1 || parent.bf() == 1 {
                node = parent;
                parent = parent.parent();
            } else {
                if parent.bf() == 2 {
                    if node.bf() == 1 {
                        self.left_rotate(parent);
                    } else {
                        self.rl_rotate(parent);
                    }
                } else {
                    if node.bf() == 1 {
                        self.right_rotate(parent);
                    } else {
                        self.lr_rotate(parent);
                    }
                }
                break;
            }
        }
    }
    
    #[inline]
    unsafe fn delete(&mut self, mut node: NodePtr<K, V>) -> (K, V) {

        self.len -= 1;
        
        let mut fix_parent = NodePtr::null();
        let mut is_left = false;

        if !node.left().is_null() && !node.right().is_null() {
            let mut replace = node.right().min_node();
            fix_parent = replace.parent();
            is_left = replace.is_left_child();
            if node == self.root  {
                self.root = replace;
            } else {
                if node.is_left_child() {
                    node.parent().set_left(replace);
                } else {
                    node.parent().set_right(replace);
                }
                replace.set_bf(node.bf());
            }
            // if min_parent != node {
            //     min_parent.set_left(NodePtr::null());
            //     min_parent.add_bf(-1);
            // } else {
            //     min_parent.add_bf(1);
            // }
            replace.set_parent(node.parent());
        } else if !node.left().is_null() {
            node.left().set_parent(node.parent());
            node.parent().set_left(node.left());
            fix_parent = node.parent();
            is_left = true;
        } else if !node.right().is_null() {
            node.right().set_parent(node.parent());
            node.parent().set_right(node.right());
            fix_parent = node.parent();
            is_left = false;
        } else {
            is_left = node.is_left_child();
            fix_parent = node.parent();
            if is_left {
                fix_parent.set_left(NodePtr::null());
            } else {
                fix_parent.set_right(NodePtr::null());
            }
        }

        while !fix_parent.is_null() {
            if is_left {
                fix_parent.add_bf(1);
            } else {
                fix_parent.add_bf(-1);
            }

            if fix_parent.bf() == 0 {
                is_left = fix_parent.is_left_child();
            } else if fix_parent.bf() == -1 || fix_parent.bf() == 1 {
                break;
            } else {
                if fix_parent.bf() == 2 {
                    self.left_rotate(fix_parent);
                } else {
                    self.right_rotate(fix_parent);
                }
            }
            fix_parent = fix_parent.parent();
        }

        let obj = Box::from_raw(node.0);
        return obj.pair();
    }

    #[inline]
    fn first_child(&self) -> NodePtr<K, V> {
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
    fn last_child(&self) -> NodePtr<K, V> {
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
    fn fast_clear(&mut self) {
        self.root = NodePtr::null();
    }

    
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

    #[inline]
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let node = self.find_node(k);
        if node.is_null() {
            return None;
        }
        unsafe { Some(self.delete(node).1) }
    }


    /*
     * 对的节点(x)进行左旋转
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
    fn left_rotate(&mut self, mut node: NodePtr<K, V>) {
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

        *temp.bf_mut() = 0;
        *node.bf_mut() = 0;
    }

    /*
     * 对的节点(y)进行右旋转
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
    fn right_rotate(&mut self, mut node: NodePtr<K, V>) {
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

        *temp.bf_mut() = 0;
        *node.bf_mut() = 0;
    }

    
    #[inline]
    fn lr_rotate(&mut self, node: NodePtr<K, V>) {
        let left_node = node.left();
        let lr_node = left_node.right();
        let bf = lr_node.bf();
        self.left_rotate(node.left());
        self.right_rotate(node);

        if bf == 0 {
            left_node.set_bf(0);
            lr_node.set_bf(0);
            node.set_bf(0);
        } else if bf == 1 {
            left_node.set_bf(0);
            lr_node.set_bf(-1);
            node.set_bf(0);
        } else if bf == -1 {
            left_node.set_bf(0);
            lr_node.set_bf(0);
            node.set_bf(1);
        } else {
            panic!("un reached");
        }
    }

    
    #[inline]
    fn rl_rotate(&mut self, node: NodePtr<K, V>) {
        let right_node = node.right();
        let rl_node = right_node.left();
        let bf = rl_node.bf();
        self.right_rotate(node.right());
        self.left_rotate(node);

        if bf == 0 {
            right_node.set_bf(0);
            rl_node.set_bf(0);
            node.set_bf(0);
        } else if bf == 1 {
            right_node.set_bf(0);
            rl_node.set_bf(0);
            node.set_bf(-1);
        } else if bf == -1 {
            right_node.set_bf(1);
            rl_node.set_bf(0);
            node.set_bf(0);
        } else {
            panic!("un reached");
        }
    }
}
