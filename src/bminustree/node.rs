

pub struct BMTreeNode<K: Ord, V> {
    pub keys: Vec<(K, V)>,
    pub childrens: Vec<Option<BMTreeNode<K, V>>>,
}

impl<K: Ord, V> BMTreeNode<K, V> {
    pub fn new(degree: usize) -> BMTreeNode<K, V> {
        BMTreeNode {
            keys: Vec::with_capacity(degree - 1),
            childrens: Vec::with_capacity(degree),
        }
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn insert(&mut self, k: K, v: V) {
        self.keys.push((k, v));
    }

    pub fn get_key(&self, idx: usize) -> Option<&K> {
        if idx < self.keys.len() {
            return None;
        }
        return Some(&self.keys[idx].0);
    }

    // pub fn get_child(&self, idx: usize) -> &mut Option<BMTreeNode<K, V>> {
    //     if idx < self.keys.len() {
    //         return None;
    //     }
    //     return Some(self.keys[idx]);
    // }
}