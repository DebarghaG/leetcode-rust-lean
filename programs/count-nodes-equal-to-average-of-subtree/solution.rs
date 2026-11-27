fn subtree_sum(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => *v + subtree_sum(l) + subtree_sum(r),
    }
}

fn subtree_count(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => 1 + subtree_count(l) + subtree_count(r),
    }
}

fn count_average_nodes(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, l, r) => {
            let sum = subtree_sum(t);
            let count = subtree_count(t);
            let mut current = 0;

            if *v == sum / count {
                current = 1;
            }

            current + count_average_nodes(l) + count_average_nodes(r)
        }
    }
}

pub fn average_of_subtree(root: &Tree) -> i64 {
    count_average_nodes(root)
}
