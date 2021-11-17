use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::ptr;


/*****************AVLTreeNode***************************/
pub struct AVLTreeNode<K: Ord, V> {
    pub left: NodePtr<K, V>,
    pub right: NodePtr<K, V>,
    pub parent: NodePtr<K, V>,
    pub key: K,
    pub value: V,
    pub bf: i8,
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
    pub fn pair(self) -> (K, V) {
        (self.key, self.value)
    }
}

/*****************NodePtr***************************/
#[derive(Debug)]
pub struct NodePtr<K: Ord, V>(pub *mut AVLTreeNode<K, V>);

impl<K: Ord, V> Clone for NodePtr<K, V> {
    fn clone(&self) -> NodePtr<K, V> {
        NodePtr(self.0)
    }
}


impl<K: Ord + Clone, V: Clone> NodePtr<K, V> {
    pub fn deep_clone(&self) -> NodePtr<K, V> {
        unsafe {
            let mut node = NodePtr::new((*self.0).key.clone(), (*self.0).value.clone());
            node.set_bf(self.bf());
            if !self.left().is_null() {
                node.set_left(self.left().deep_clone());
                node.left().set_parent(node);
            }
            if !self.right().is_null() {
                node.set_right(self.right().deep_clone());
                node.right().set_parent(node);
            }
            node
        }
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
    pub fn new(k: K, v: V) -> NodePtr<K, V> {
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

    pub fn get_node(&self) -> &AVLTreeNode<K, V> {
        unsafe { &*(self).0 }
    }
    
    pub fn get_mut_node(&self) -> &AVLTreeNode<K, V> {
        unsafe { &mut *(self).0 }
    }

    pub fn from_raw(self) -> Box<AVLTreeNode<K, V>> {
        unsafe {
            Box::from_raw( self.0  )
        }
    }

    #[inline]
    pub fn is_left_child(&self) -> bool {
        self.parent().left() == *self
    }

    #[inline]
    pub fn is_right_child(&self) -> bool {
        self.parent().right() == *self
    }

    #[inline]
    pub fn min_node(self) -> NodePtr<K, V> {
        let mut temp = self.clone();
        while !temp.left().is_null() {
            temp = temp.left();
        }
        return temp;
    }

    #[inline]
    pub fn max_node(self) -> NodePtr<K, V> {
        let mut temp = self.clone();
        while !temp.right().is_null() {
            temp = temp.right();
        }
        return temp;
    }

    #[inline]
    pub fn next(self) -> NodePtr<K, V> {
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
    pub fn prev(self) -> NodePtr<K, V> {
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
    pub fn set_parent(&mut self, parent: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).parent = parent }
    }

    #[inline]
    pub fn set_left(&mut self, mut left: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).left = left;  }
    }

    #[inline]
    pub fn set_right(&mut self, mut right: NodePtr<K, V>) {
        if self.is_null() {
            return;
        }
        unsafe { (*self.0).right = right;  }
    }

    #[inline]
    pub fn parent(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).parent.clone() }
    }

    #[inline]
    pub fn left(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).left.clone() }
    }

    #[inline]
    pub fn right(&self) -> NodePtr<K, V> {
        if self.is_null() {
            return NodePtr::null();
        }
        unsafe { (*self.0).right.clone() }
    }

    #[inline]
    pub fn null() -> NodePtr<K, V> {
        NodePtr(ptr::null_mut())
    }

    #[inline]
    pub fn is_null(&self) -> bool {
        self.0.is_null()
    }

    #[inline]
    pub fn bf_mut(&self) -> &mut i8 {
        unsafe { &mut (*self.0).bf }
    }

    #[inline]
    pub fn set_bf(&self, bf: i8) {
        unsafe {  (*self.0).bf   = bf; }
    }
    
    #[inline]
    pub fn add_bf(&self, bf: i8) -> i8 {
        unsafe {  (*self.0).bf += bf; (*self.0).bf }
    }

    #[inline]
    pub fn bf(&self) -> i8 {
        unsafe { (*self.0).bf }
    }
}