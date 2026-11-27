fn count_nodes(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            1 + count_nodes(&**left) + count_nodes(&**right)
        }
    }
}

fn check_complete(t: &Tree, index: i64, total: i64) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(_, left, right) => {
            if index > total {
                false
            } else {
                let left_ok = check_complete(&**left, index * 2, total);
                if !left_ok {
                    false
                } else {
                    check_complete(&**right, index * 2 + 1, total)
                }
            }
        }
    }
}

pub fn is_complete_tree(root: &Tree) -> bool {
    let total = count_nodes(root);
    check_complete(root, 1, total)
}
