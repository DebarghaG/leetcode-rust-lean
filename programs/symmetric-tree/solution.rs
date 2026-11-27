fn is_mirror(a: &Tree, b: &Tree) -> bool {
    match a {
        Tree::Null => {
            match b {
                Tree::Null => true,
                Tree::Node(_, _, _) => false,
            }
        }
        Tree::Node(av, al, ar) => {
            match b {
                Tree::Null => false,
                Tree::Node(bv, bl, br) => {
                    if av != bv {
                        false
                    } else {
                        let outer = is_mirror(&**al, &**br);
                        if !outer {
                            false
                        } else {
                            is_mirror(&**ar, &**bl)
                        }
                    }
                }
            }
        }
    }
}

pub fn is_symmetric(root: &Tree) -> bool {
    match root {
        Tree::Null => true,
        Tree::Node(_, left, right) => is_mirror(&**left, &**right),
    }
}
