pub fn search_bst(root: &Tree, val: i64) -> Tree {
    match root {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => {
            if *v == val {
                clone_tree(root)
            } else if val < *v {
                search_bst(&**left, val)
            } else {
                search_bst(&**right, val)
            }
        }
    }
}

fn clone_tree(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => Tree::Node(
            *v,
            Box::new(clone_tree(&**left)),
            Box::new(clone_tree(&**right)),
        ),
    }
}
