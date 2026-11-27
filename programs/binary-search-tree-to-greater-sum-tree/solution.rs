fn build(t: &Tree, acc: &mut i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => {
            // reverse inorder: right, node, left
            let new_right = build(&**right, acc);
            *acc = *acc + *v;
            let new_val = *acc;
            let new_left = build(&**left, acc);
            Tree::Node(new_val, Box::new(new_left), Box::new(new_right))
        }
    }
}

pub fn bst_to_gst(root: &Tree) -> Tree {
    let mut acc: i64 = 0;
    build(root, &mut acc)
}
