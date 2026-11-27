fn invert(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => {
            let inverted_left = invert(&**right);
            let inverted_right = invert(&**left);
            Tree::Node(*v, Box::new(inverted_left), Box::new(inverted_right))
        }
    }
}

pub fn invert_tree(root: &Tree) -> Tree {
    invert(root)
}
