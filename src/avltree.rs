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
        write!(f, "k:{:?} v:{:?}", self.key, self.value)
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
    fn bf(&self) -> i8 {
        unsafe { (*self.0).bf }
    }
}

pub struct AVLTree<K: Ord, V> {
    root: NodePtr<K, V>,
    len: usize,
    height: usize,
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

        while !parent.is_null() {
            if tmp == parent.left() {
                *parent.bf_mut() -= 1;
            } else {
                *parent.bf_mut() += 1;
            }

            if parent.bf() == 0 {
                break;
            } else if parent.bf() == -1 || parent.bf() == 1 {
                tmp = parent;
                parent = parent.parent();
            } else {
                if parent.bf() == 2 {
                    if tmp.bf() == 1 {
                        self.left_rotate(parent);
                    } else {
                        self.rl_rotate(parent);
                    }
                } else {
                    if tmp.bf() == 1 {
                        self.right_rotate(parent);
                    } else {
                        self.lr_rotate(parent);
                    }
                }
            }
        }

        // unsafe {
        //     self.insert_fixup(node);
        // }
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
