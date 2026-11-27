fn helper(t: &Tree, sum: &mut i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => {
            // Reverse in-order: process the (structurally) right subtree first,
            // since it holds the larger keys in a BST.
            let new_r = helper(&**r, sum);

            let new_v = *v + *sum;
            *sum = *sum + *v;

            let new_l = helper(&**l, sum);

            Tree::Node(new_v, Box::new(new_l), Box::new(new_r))
        }
    }
}

pub fn convert_bst(root: &Tree) -> Tree {
    let mut sum: i64 = 0;
    helper(root, &mut sum)
}
