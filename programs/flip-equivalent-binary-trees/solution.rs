pub fn flip_equiv(root1: &Tree, root2: &Tree) -> bool {
    match root1 {
        Tree::Null => match root2 {
            Tree::Null => true,
            Tree::Node(_, _, _) => false,
        },
        Tree::Node(v1, l1, r1) => match root2 {
            Tree::Null => false,
            Tree::Node(v2, l2, r2) => {
                if *v1 != *v2 {
                    return false;
                }

                let left1: &Tree = &**l1;
                let right1: &Tree = &**r1;
                let left2: &Tree = &**l2;
                let right2: &Tree = &**r2;

                if flip_equiv(left1, left2) && flip_equiv(right1, right2) {
                    return true;
                }

                flip_equiv(left1, right2) && flip_equiv(right1, left2)
            }
        },
    }
}
