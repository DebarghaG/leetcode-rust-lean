fn inorder(node: &Tree) -> Vec<i64> {
    match node {
        Tree::Null => Vec::new(),
        Tree::Node(value, left, right) => {
            let mut out = inorder(left);
            out.push(*value);

            let right_values = inorder(right);
            let mut i: usize = 0;
            while i < right_values.len() {
                out.push(right_values[i]);
                i += 1;
            }

            out
        }
    }
}

pub fn inorder_traversal(root: &Tree) -> Vec<i64> {
    inorder(root)
}
