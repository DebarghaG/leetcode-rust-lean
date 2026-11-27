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

fn insert_into_max_tree_helper(t: &Tree, val: i64) -> Tree {
    match t {
        Tree::Null => Tree::Node(
            val,
            Box::new(Tree::Null),
            Box::new(Tree::Null),
        ),
        Tree::Node(v, l, r) => {
            if val > *v {
                Tree::Node(
                    val,
                    Box::new(clone_tree(t)),
                    Box::new(Tree::Null),
                )
            } else {
                Tree::Node(
                    *v,
                    Box::new(clone_tree(&**l)),
                    Box::new(insert_into_max_tree_helper(&**r, val)),
                )
            }
        }
    }
}

pub fn insert_into_max_tree(root: &Tree, val: i64) -> Tree {
    insert_into_max_tree_helper(root, val)
}
