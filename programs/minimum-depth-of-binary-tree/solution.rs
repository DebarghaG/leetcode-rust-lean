fn min_depth_helper(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, l, r) => {
            let left = &**l;
            let right = &**r;

            match (left, right) {
                (Tree::Null, Tree::Null) => 1,
                (Tree::Null, _) => 1 + min_depth_helper(right),
                (_, Tree::Null) => 1 + min_depth_helper(left),
                _ => {
                    let a = min_depth_helper(left);
                    let b = min_depth_helper(right);
                    let m = if a < b { a } else { b };
                    1 + m
                }
            }
        }
    }
}

pub fn min_depth(root: &Tree) -> i64 {
    min_depth_helper(root)
}
