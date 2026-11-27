pub fn height_of_tree(root: &Tree) -> i64 {
    tree_height(root)
}

fn tree_height(node: &Tree) -> i64 {
    match node {
        Tree::Null => -1,
        Tree::Node(_, left, right) => {
            let left_height = tree_height(left);
            let right_height = tree_height(right);
            if left_height > right_height {
                left_height + 1
            } else {
                right_height + 1
            }
        }
    }
}
