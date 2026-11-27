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

fn add_helper(t: &Tree, val: i64, depth: i64, cur_depth: i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => {
            if cur_depth + 1 == depth {
                Tree::Node(
                    *v,
                    Box::new(Tree::Node(
                        val,
                        Box::new(clone_tree(&**l)),
                        Box::new(Tree::Null),
                    )),
                    Box::new(Tree::Node(
                        val,
                        Box::new(Tree::Null),
                        Box::new(clone_tree(&**r)),
                    )),
                )
            } else {
                Tree::Node(
                    *v,
                    Box::new(add_helper(&**l, val, depth, cur_depth + 1)),
                    Box::new(add_helper(&**r, val, depth, cur_depth + 1)),
                )
            }
        }
    }
}

pub fn add_one_row(root: &Tree, val: i64, depth: i64) -> Tree {
    if depth == 1 {
        Tree::Node(
            val,
            Box::new(clone_tree(root)),
            Box::new(Tree::Null),
        )
    } else {
        add_helper(root, val, depth, 1)
    }
}
