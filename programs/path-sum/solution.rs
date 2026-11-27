fn has_path_sum_rec(node: &Tree, remaining: i64) -> bool {
    match node {
        Tree::Null => false,
        Tree::Node(value, left, right) => {
            let next_remaining = remaining - *value;

            let left_is_null = match &**left {
                Tree::Null => true,
                _ => false,
            };
            let right_is_null = match &**right {
                Tree::Null => true,
                _ => false,
            };

            if left_is_null && right_is_null {
                next_remaining == 0
            } else if left_is_null {
                has_path_sum_rec(&**right, next_remaining)
            } else if right_is_null {
                has_path_sum_rec(&**left, next_remaining)
            } else if has_path_sum_rec(&**left, next_remaining) {
                true
            } else {
                has_path_sum_rec(&**right, next_remaining)
            }
        }
    }
}

pub fn has_path_sum(root: &Tree, targetSum: i64) -> bool {
    has_path_sum_rec(root, targetSum)
}
