fn sum_helper(t: &Tree, acc: i64) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let cur = acc * 2 + *v;

            let left_null = match &**l {
                Tree::Null => true,
                _ => false,
            };
            let right_null = match &**r {
                Tree::Null => true,
                _ => false,
            };

            if left_null && right_null {
                cur
            } else {
                sum_helper(&**l, cur) + sum_helper(&**r, cur)
            }
        }
    }
}

pub fn sum_root_to_leaf(root: &Tree) -> i64 {
    sum_helper(root, 0)
}
