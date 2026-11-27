pub fn check_equal_tree(root: &Tree) -> bool {
    let total = tree_sum(root);

    if total % 2 != 0 {
        return false;
    }

    let target = total / 2;
    check_subtree(root, target)
}

fn tree_sum(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, left, right) => {
            *v + tree_sum(&**left) + tree_sum(&**right)
        }
    }
}

fn check_subtree(t: &Tree, target: i64) -> bool {
    match t {
        Tree::Null => false,
        Tree::Node(_, left, right) => {
            match &**left {
                Tree::Null => {}
                Tree::Node(_, _, _) => {
                    let left_sum = tree_sum(&**left);
                    if left_sum == target {
                        return true;
                    }
                    if check_subtree(&**left, target) {
                        return true;
                    }
                }
            };

            match &**right {
                Tree::Null => {}
                Tree::Node(_, _, _) => {
                    let right_sum = tree_sum(&**right);
                    if right_sum == target {
                        return true;
                    }
                    if check_subtree(&**right, target) {
                        return true;
                    }
                }
            };

            false
        }
    }
}
