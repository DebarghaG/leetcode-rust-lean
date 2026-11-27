fn value_or_zero(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(v, _, _) => *v,
    }
}

pub fn check_tree(root: &Tree) -> bool {
    match root {
        Tree::Null => false,
        Tree::Node(v, left, right) => {
            *v == value_or_zero(&**left) + value_or_zero(&**right)
        }
    }
}
