fn count_good(node: &Tree, max_so_far: i64) -> i64 {
    match node {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            let v = *value;
            let mut current_max = max_so_far;
            let mut count = 0;

            if v >= max_so_far {
                count = 1;
                current_max = v;
            }

            count + count_good(&**left, current_max) + count_good(&**right, current_max)
        }
    }
}

pub fn good_nodes(root: &Tree) -> i64 {
    match root {
        Tree::Null => 0,
        Tree::Node(value, left, right) => {
            let v = *value;
            1 + count_good(&**left, v) + count_good(&**right, v)
        }
    }
}
