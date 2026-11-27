fn postorder_helper(t: &Tree) -> Vec<i64> {
    match t {
        Tree::Null => {
            let empty: Vec<i64> = Vec::new();
            empty
        }
        Tree::Node(v, l, r) => {
            let mut result = postorder_helper(&**l);
            let right = postorder_helper(&**r);

            let mut i = 0;
            while i < right.len() {
                result.push(right[i]);
                i += 1;
            }

            result.push(*v);
            result
        }
    }
}

pub fn postorder_traversal(root: &Tree) -> Vec<i64> {
    postorder_helper(root)
}
