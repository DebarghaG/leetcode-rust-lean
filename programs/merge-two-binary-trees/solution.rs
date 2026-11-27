pub fn merge_trees(root1: &Tree, root2: &Tree) -> Tree {
    match root1 {
        Tree::Null => clone_tree(root2),
        Tree::Node(v1, l1, r1) => match root2 {
            Tree::Null => clone_tree(root1),
            Tree::Node(v2, l2, r2) => Tree::Node(
                *v1 + *v2,
                Box::new(merge_trees(&**l1, &**l2)),
                Box::new(merge_trees(&**r1, &**r2)),
            ),
        },
    }
}

fn clone_tree(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => Tree::Node(
            *v,
            Box::new(clone_tree(&**l)),
            Box::new(clone_tree(&**r)),
        ),
    }
}
