pub fn count_unival_subtrees(root: &Tree) -> i64 {
    count_in_subtree(root)
}

fn count_in_subtree(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            let mut count: i64 = 0;

            if all_equal(t, *value) {
                count += 1;
            }

            count += count_in_subtree(&**left);
            count += count_in_subtree(&**right);

            count
        }
    }
}

fn all_equal(t: &Tree, value: i64) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(v, left, right) => {
            if *v != value {
                false
            } else {
                let left_ok = all_equal(&**left, value);
                if !left_ok {
                    false
                } else {
                    all_equal(&**right, value)
                }
            }
        }
    }
}
