fn sum_numbers_helper(node: &Tree, prefix: i64) -> i64 {
    match node {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            let current = prefix * 10 + *value;

            let left_is_null = match &**left {
                Tree::Null => true,
                _ => false,
            };
            let right_is_null = match &**right {
                Tree::Null => true,
                _ => false,
            };

            if left_is_null && right_is_null {
                current
            } else if left_is_null {
                sum_numbers_helper(&**right, current)
            } else if right_is_null {
                sum_numbers_helper(&**left, current)
            } else {
                sum_numbers_helper(&**left, current) + sum_numbers_helper(&**right, current)
            }
        }
    }
}

pub fn sum_numbers(root: &Tree) -> i64 {
    sum_numbers_helper(root, 0)
}
