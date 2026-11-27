fn same_tree(a: &Tree, b: &Tree) -> bool {
    match a {
        Tree::Null => match b {
            Tree::Null => true,
            Tree::Node(_, _, _) => false,
        },
        Tree::Node(av, al, ar) => match b {
            Tree::Null => false,
            Tree::Node(bv, bl, br) => {
                if *av != *bv {
                    false
                } else if !same_tree(al, bl) {
                    false
                } else {
                    same_tree(ar, br)
                }
            }
        },
    }
}

pub fn is_subtree(root: &Tree, subRoot: &Tree) -> bool {
    if same_tree(root, subRoot) {
        true
    } else {
        match root {
            Tree::Null => false,
            Tree::Node(_, left, right) => {
                is_subtree(left, subRoot) || is_subtree(right, subRoot)
            }
        }
    }
}
