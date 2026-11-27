fn max_depth(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_v, l, r) => {
            let left: &Tree = &**l;
            let right: &Tree = &**r;
            let lh = max_depth(left);
            let rh = max_depth(right);
            if lh > rh {
                lh + 1
            } else {
                rh + 1
            }
        }
    }
}

fn clone_tree(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => {
            let left: &Tree = &**l;
            let right: &Tree = &**r;
            let left_clone = clone_tree(left);
            let right_clone = clone_tree(right);
            Tree::Node(*v, Box::new(left_clone), Box::new(right_clone))
        }
    }
}

fn solve(t: &Tree, cur_depth: i64, target_depth: i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(_v, l, r) => {
            let left: &Tree = &**l;
            let right: &Tree = &**r;

            let lh = max_depth(left);
            let rh = max_depth(right);

            let left_reaches = lh > 0 && cur_depth + lh == target_depth;
            let right_reaches = rh > 0 && cur_depth + rh == target_depth;

            if left_reaches && right_reaches {
                clone_tree(t)
            } else if left_reaches {
                solve(left, cur_depth + 1, target_depth)
            } else if right_reaches {
                solve(right, cur_depth + 1, target_depth)
            } else {
                clone_tree(t)
            }
        }
    }
}

pub fn subtree_with_all_deepest(root: &Tree) -> Tree {
    let h = max_depth(root);
    if h == 0 {
        return Tree::Null;
    }
    let target_depth = h - 1;
    solve(root, 0, target_depth)
}
