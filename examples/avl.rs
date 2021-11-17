extern crate datastruct;
use datastruct::AVLTree;

fn test1() {
    let mut avl = AVLTree::new();
    print!("ok");
    avl.insert(12, 2);
    avl.insert(6, 1);
    avl.insert(14, 1);
    avl.insert(2, 1);
    avl.insert(8, 1);
    avl.insert(4, 1);

    avl.print_tree();

}


fn test2() {
    let mut avl = AVLTree::new();
    print!("ok");
    avl.insert(12, 2);
    avl.insert(6, 1);
    avl.insert(14, 1);
    avl.insert(2, 1);
    avl.insert(8, 1);
    avl.insert(7, 1);
    avl.print_tree();
}

fn test3() {
    let mut avl = AVLTree::new();
    print!("ok");
    avl.insert(4, 1);
    avl.insert(2, 1);
    avl.insert(10, 1);
    avl.insert(6, 1);
    avl.insert(12, 1);
    avl.insert(7, 1);
    avl.remove(&10);
    avl.print_tree();
}


fn test4() {
    let mut avl = AVLTree::new();
    print!("ok");
    avl.insert(4, 1);
    avl.insert(2, 1);
    avl.insert(10, 1);
    avl.insert(6, 1);
    avl.insert(12, 1);
    avl.insert(11, 1);
    avl.remove(&10);
    avl.print_tree();
}

fn main() {
    // test1();
    // test2();
    test3();
    // test4();
    // let mut avl = AVLTree::new();
    // print!("ok");
    // avl.insert(1, 2);
    // avl.insert(3, 1);
    // avl.insert(5, 1);
    // avl.insert(7, 1);
    // avl.remove(&7);

    // avl.print_tree();

    // println!("avl ==={:?}", avl);
}
