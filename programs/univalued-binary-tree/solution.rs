fn check_unival(t: &Tree, val: i64) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(v, left, right) => {
            if *v != val {
                false
            } else {
                check_unival(left, val) && check_unival(right, val)
            }
        }
    }
}

pub fn is_unival_tree(root: &Tree) -> bool {
    match root {
        Tree::Null => true,
        Tree::Node(v, left, right) => {
            check_unival(left, *v) && check_unival(right, *v)
        }
    }
}
