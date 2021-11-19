
use std::cmp::Ord;
use std::cmp::Ordering;
use super::node::BMTreeNode;

pub struct BMinusTree<K: Ord, V> {
    pub root: BMTreeNode<K, V>,
    pub degree: usize,
    pub len: usize,
}


impl<K: Ord, V> BMinusTree<K, V> {
    pub fn new(degree: usize) -> BMinusTree<K, V> {
        assert!(degree >= 3, "b-tree must >= 3");
        BMinusTree {
            root: BMTreeNode::new(degree),
            degree: degree,
            len: 0,
        }
    }

    pub fn insert(&mut self, k: K, v: V) -> bool {
        if self.root.is_empty() {
            self.root.insert(k, v);
            self.len += 1;
            return true;
        }

        


        self.len += 1;
        true
    }

    pub fn insert_iter(&mut self, node: &mut BMTreeNode<K, V>, k: K, v: V) -> Option<&mut BMTreeNode<K, V>> {
        // for i in range(0 .. node.keys().len())  {
        //     if let Some(child) = match k.cmp(node.get_key(i).unwrap()) {
        //         Ordering::Less => self.insert_iter(),
        //         Ordering::Greater => self.insert_iter(),
        //         Ordering::Equal => return None,
        //     } {
                
        //     }
            
        // };
        // true
        None
    }
}
