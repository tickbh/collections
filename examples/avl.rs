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


// fn test2() {
//     let mut avl = AVLTree::new();
//     print!("ok");
//     avl.insert(12, 2);
//     avl.insert(6, 1);
//     avl.insert(14, 1);
//     avl.insert(2, 1);
//     avl.insert(8, 1);
//     avl.insert(7, 1);
//     avl.print_tree();
// }

// fn test3() {
//     let mut avl = AVLTree::new();
//     print!("ok");
//     avl.insert(4, 1);
//     avl.insert(2, 1);
//     avl.insert(10, 1);
//     avl.insert(6, 1);
//     avl.insert(12, 1);
//     avl.insert(7, 1);
//     avl.remove(&10);
//     avl.print_tree();
// }


// fn test4() {
//     let mut avl = AVLTree::new();
//     print!("ok");
//     avl.insert(4, 1);
//     avl.insert(2, 1);
//     avl.insert(10, 1);
//     avl.insert(6, 1);
//     avl.insert(12, 1);
//     avl.insert(11, 1);
//     avl.remove(&10);
//     avl.print_tree();
// }

fn test_lots_of_insertions() {
    let mut m = AVLTree::new();

    // Try this a few times to make sure we never screw up the hashmap's
    // internal state.
    for _ in 0..10 {
        assert!(m.is_empty());

        for i in 1..101 {
            m.insert(i, i);

            for j in 1..i + 1 {
                let r = m.get(&j);
                assert_eq!(r, Some(&j));
            }

            for j in i + 1..101 {
                let r = m.get(&j);
                assert_eq!(r, None);
            }
        }

        for i in 101..201 {
            assert!(!m.contains_key(&i));
        }

        // remove forwards
        for i in 1..101 {
            if i == 99 {
                println!("ok");
            }
            assert!(m.remove(&i) == Some(i));
            println!("i============{}",i);

        

            for j in 1..i + 1 {
                assert!(!m.contains_key(&j));
            }

            for j in i + 1..101 {
                assert!(m.contains_key(&j));
            }

        }

        for i in 1..101 {
            assert!(!m.contains_key(&i));
        }

        for i in 1..101 {
            m.insert(i, i);
        }

        // remove backwards
        for i in (1..101).rev() {
            assert!(m.remove(&i).is_some());

            for j in i..101 {
                assert!(!m.contains_key(&j));
            }

            for j in 1..i {
                assert!(m.contains_key(&j));
            }
        }
    }
}


fn main() {
    test1();
    // test2();
    // test3();
    // test4();
    test_lots_of_insertions();
    print!("ok");

    
    // let mut avl = AVLTree::new();
    // avl.insert(1, 1);
    // avl.insert(2, 2);
    // avl.insert(4, 4);
    // avl.print_tree();
    
    // avl.insert(1, 2);
    // avl.insert(3, 1);
    // avl.insert(5, 1);
    // avl.insert(7, 1);
    // avl.remove(&7);

    // avl.print_tree();

    // println!("avl ==={:?}", avl);

    // let mut m = AVLTree::new();
    // assert_eq!(m.len(), 0);
    // m.insert(1, 2);
    // assert_eq!(m.len(), 1);
    // m.insert(2, 4);
    // assert_eq!(m.len(), 2);
    // let m2 = m.clone();
    // m.clear();
    // assert_eq!(*m2.get(&1).unwrap(), 2);
    // assert_eq!(*m2.get(&2).unwrap(), 4);
    // assert_eq!(m2.len(), 2);

}
