fn clone_tree(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => Tree::Node(
            *v,
            Box::new(clone_tree(left)),
            Box::new(clone_tree(right)),
        ),
    }
}

fn insert(t: &Tree, val: i64) -> Tree {
    match t {
        Tree::Null => Tree::Node(
            val,
            Box::new(Tree::Null),
            Box::new(Tree::Null),
        ),
        Tree::Node(v, left, right) => {
            if val < *v {
                Tree::Node(
                    *v,
                    Box::new(insert(left, val)),
                    Box::new(clone_tree(right)),
                )
            } else if val > *v {
                Tree::Node(
                    *v,
                    Box::new(clone_tree(left)),
                    Box::new(insert(right, val)),
                )
            } else {
                clone_tree(t)
            }
        }
    }
}

pub fn insert_into_bst(root: &Tree, val: i64) -> Tree {
    insert(root, val)
}
