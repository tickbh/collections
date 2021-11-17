extern crate datastruct;
use datastruct::AVLTree;

fn main() {
    let mut avl = AVLTree::new();
    print!("ok");
    avl.insert(1, 2);
    avl.insert(3, 4);
    avl.insert(5, 4);
    avl.insert(7, 4);
    avl.remove(&7);

    avl.print_tree();

    println!("avl ==={:?}", avl);
}
