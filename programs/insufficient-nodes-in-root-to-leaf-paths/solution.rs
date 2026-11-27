fn is_null(t: &Tree) -> bool {
    match t {
        Tree::Null => true,
        _ => false,
    }
}

fn dfs(t: &Tree, sum: i64, limit: i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, l, r) => {
            let val = *v;

            if is_null(&**l) && is_null(&**r) {
                if sum + val < limit {
                    Tree::Null
                } else {
                    Tree::Node(val, Box::new(Tree::Null), Box::new(Tree::Null))
                }
            } else {
                let new_left = dfs(&**l, sum + val, limit);
                let new_right = dfs(&**r, sum + val, limit);

                if is_null(&new_left) && is_null(&new_right) {
                    Tree::Null
                } else {
                    Tree::Node(val, Box::new(new_left), Box::new(new_right))
                }
            }
        }
    }
}

pub fn sufficient_subset(root: &Tree, limit: i64) -> Tree {
    dfs(root, 0, limit)
}
