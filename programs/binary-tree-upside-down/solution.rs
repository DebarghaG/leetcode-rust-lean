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

fn attach_rightmost(t: Tree, new_left: Tree, parent_val: i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => match *right {
            Tree::Null => Tree::Node(
                v,
                Box::new(new_left),
                Box::new(Tree::Node(
                    parent_val,
                    Box::new(Tree::Null),
                    Box::new(Tree::Null),
                )),
            ),
            Tree::Node(rv, rl, rr) => {
                let new_right =
                    attach_rightmost(Tree::Node(rv, rl, rr), new_left, parent_val);
                Tree::Node(v, left, Box::new(new_right))
            }
        },
    }
}

fn transform(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => match &**left {
            Tree::Null => clone_tree(t),
            Tree::Node(_, _, _) => {
                let new_root = transform(&**left);
                attach_rightmost(new_root, clone_tree(&**right), *v)
            }
        },
    }
}

pub fn upside_down_binary_tree(root: &Tree) -> Tree {
    transform(root)
}
