fn preorder_helper(t: &Tree, out: &mut Vec<i64>) {
    match t {
        Tree::Null => {}
        Tree::Node(v, left, right) => {
            out.push(*v);
            preorder_helper(left, out);
            preorder_helper(right, out);
        }
    }
}

pub fn preorder_traversal(root: &Tree) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    preorder_helper(root, &mut out);
    out
}
