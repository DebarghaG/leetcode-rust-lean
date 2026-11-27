pub fn sum_of_left_leaves(root: &Tree) -> i64 {
    sum_left_leaves_go(root, false)
}

fn sum_left_leaves_is_leaf(t: &Tree) -> bool {
    match t {
        Tree::Null => false,
        Tree::Node(_, left, right) => match &**left {
            Tree::Null => match &**right {
                Tree::Null => true,
                Tree::Node(_, _, _) => false,
            },
            Tree::Node(_, _, _) => false,
        },
    }
}

fn sum_left_leaves_go(t: &Tree, is_left: bool) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            if is_left {
                if sum_left_leaves_is_leaf(t) {
                    *value
                } else {
                    sum_left_leaves_go(&**left, true) + sum_left_leaves_go(&**right, false)
                }
            } else {
                sum_left_leaves_go(&**left, true) + sum_left_leaves_go(&**right, false)
            }
        }
    }
}
