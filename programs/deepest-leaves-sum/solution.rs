fn tree_depth(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let dl = tree_depth(&**left);
            let dr = tree_depth(&**right);
            if dl > dr {
                dl + 1
            } else {
                dr + 1
            }
        }
    }
}

fn sum_at_depth(t: &Tree, target: i64, current: i64) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            if current == target {
                *value
            } else {
                let left_sum = sum_at_depth(&**left, target, current + 1);
                let right_sum = sum_at_depth(&**right, target, current + 1);
                left_sum + right_sum
            }
        }
    }
}

pub fn deepest_leaves_sum(root: &Tree) -> i64 {
    let deepest = tree_depth(root);
    sum_at_depth(root, deepest, 1)
}
