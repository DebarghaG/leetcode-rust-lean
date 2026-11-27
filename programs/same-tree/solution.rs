pub fn is_same_tree(p: &Tree, q: &Tree) -> bool {
    match (p, q) {
        (Tree::Null, Tree::Null) => true,
        (Tree::Node(v1, l1, r1), Tree::Node(v2, l2, r2)) => {
            if *v1 != *v2 {
                false
            } else {
                is_same_tree(&**l1, &**l2) && is_same_tree(&**r1, &**r2)
            }
        }
        _ => false,
    }
}
