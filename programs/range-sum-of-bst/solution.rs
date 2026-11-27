pub fn range_sum_bst(root: &Tree, low: i64, high: i64) -> i64 {
    range_sum_bst_helper(root, low, high)
}

fn range_sum_bst_helper(node: &Tree, low: i64, high: i64) -> i64 {
    match node {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            let val: i64 = *value;
            let mut total: i64 = 0;

            if val >= low && val <= high {
                total = total + val;
            }
            if val > low {
                total = total + range_sum_bst_helper(&**left, low, high);
            }
            if val < high {
                total = total + range_sum_bst_helper(&**right, low, high);
            }

            total
        }
    }
}
