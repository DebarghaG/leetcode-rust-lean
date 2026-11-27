fn count_nodes(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => {
            let left_count = count_nodes(&**l);
            let right_count = count_nodes(&**r);
            1 + left_count + right_count
        }
    }
}

fn kth_smallest_in(t: &Tree, k: i64) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let left_count = count_nodes(&**l);
            if k <= left_count {
                kth_smallest_in(&**l, k)
            } else if k == left_count + 1 {
                *v
            } else {
                kth_smallest_in(&**r, k - left_count - 1)
            }
        }
    }
}

pub fn kth_smallest(root: &Tree, k: i64) -> i64 {
    kth_smallest_in(root, k)
}
