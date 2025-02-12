use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::mem;

use super::node::{NodePtr};

pub struct AVLTree<K: Ord, V> {
    pub root: NodePtr<K, V>,
    pub len: usize,
    pub repeat: bool,
}

impl<K: Ord, V> AVLTree<K, V> {
    /// Creates an empty `AVLTree`.
    pub fn new() -> AVLTree<K, V> {
        AVLTree {
            root: NodePtr::null(),
            len: 0,
            repeat: false,
        }
    }

    pub fn new_repeat() -> AVLTree<K, V> {
        AVLTree {
            root: NodePtr::null(),
            len: 0,
            repeat: true,
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

    
    /// replace value if key exist, if not exist insert it.
    /// # Examples
    /// ```
    /// use datastruct::AVLTree;
    /// let mut m = AVLTree::new();
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
    pub fn insert(&mut self, k: K, v: V) -> bool {
        let mut node = NodePtr::new(k, v);
        let mut parent = NodePtr::null();
        let mut tmp = self.root;

        while !tmp.is_null() {
            parent = tmp;
            match node.cmp(&&mut tmp) {
                Ordering::Less => {
                    tmp = tmp.left();
                }
                Ordering::Greater => {
                    tmp = tmp.right();
                }
                Ordering::Equal => {
                    if !self.repeat {
                        return false;
                    }
                    tmp = tmp.right();
                }
            };
        }
        
        self.len += 1;
        node.set_parent(parent);

        if parent.is_null() {
            self.root = node;
            return true;
        }

        match node.cmp(&&mut parent) {
            Ordering::Less => {
                parent.set_left(node);
            }
            _ => {
                parent.set_right(node);
            }
        };

        self.fixup_node(node);
        true
    }

    fn fixup_node(&mut self,mut node: NodePtr<K, V>) {
        let mut parent = node.parent();
        while !parent.is_null() {
            parent.update_height();

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
                    if node.bf() == -1 {
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
    unsafe fn delete(&mut self, node: NodePtr<K, V>) -> (K, V) {

        self.len -= 1;
        
        let mut fix_parent;

        let is_root = node == self.root;

        if !node.left().is_null() && !node.right().is_null() {
            let mut replace = node.right().min_node();
            fix_parent = replace.parent();
            let is_left = replace.is_left_child();
            if is_root  {
                replace.set_left(self.root.left());
                replace.set_right(self.root.right());
                self.root = replace;
            } else {
                if node.is_left_child() {
                    node.parent().set_left(replace);
                    replace.set_right(node.right());
                } else {
                    node.parent().set_right(replace);
                    replace.set_left(node.left());
                }
            }
            replace.set_height(node.height());
            replace.set_parent(node.parent());
            if is_left {
                fix_parent.set_left(NodePtr::null());
            } else {
                fix_parent.set_right(NodePtr::null());
            }
        } else if !node.left().is_null() {
            node.left().set_parent(node.parent());
            if node.is_left_child() {
                node.parent().set_left(node.left());
            } else {
                node.parent().set_right(node.left());
            }
            fix_parent = node.left();
            fix_parent.set_height(node.height());
            if is_root {
                self.root = fix_parent;
            }
        } else if !node.right().is_null() {
            node.right().set_parent(node.parent());
            if node.is_left_child() {
                node.parent().set_left(node.right());
            } else {
                node.parent().set_right(node.right());
            }
            fix_parent = node.right();
            fix_parent.set_height(node.height());
            if is_root {
                self.root = fix_parent;
            }
        } else {
            fix_parent = node.parent();
            if node.is_left_child() {
                fix_parent.set_left(NodePtr::null());
            } else {
                fix_parent.set_right(NodePtr::null());
            }
            if is_root {
                self.root = NodePtr::null();
            }
        }

        while !fix_parent.is_null() {
            fix_parent.update_height();

            if fix_parent.bf() == 0 {
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
    pub(crate) fn first_child(&self) -> NodePtr<K, V> {
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
    pub(crate) fn last_child(&self) -> NodePtr<K, V> {
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
        self.clear_recurse(self.root);
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
        node.update_height();

        if node == self.root {
            self.root = temp.clone();
            temp.set_parent(NodePtr::null());
        } else if node.is_left_child() {
            node.parent().set_left(temp.clone());
        } else {
            node.parent().set_right(temp.clone());
        }

        temp.set_left(node.clone());
        temp.update_height();
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
            node.update_height();
        }

        if node == self.root {
            self.root = temp.clone();
            temp.set_parent(node.parent());
        } else if node == node.parent().right() {
            node.parent().set_right(temp.clone());
        } else {
            node.parent().set_left(temp.clone());
        }

        temp.set_right(node.clone());
        temp.update_height();
    }

    
    #[inline]
    fn lr_rotate(&mut self, node: NodePtr<K, V>) {
        self.left_rotate(node.left());
        self.right_rotate(node);

    }

    
    #[inline]
    fn rl_rotate(&mut self, node: NodePtr<K, V>) {
        self.right_rotate(node.right());
        self.left_rotate(node);
    }
}

