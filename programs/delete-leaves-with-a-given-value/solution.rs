fn is_null(t: &Tree) -> bool {
    match t {
        Tree::Null => true,
        Tree::Node(_, _, _) => false,
    }
}

fn dfs(t: &Tree, target: i64) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => {
            let new_left = dfs(&**left, target);
            let new_right = dfs(&**right, target);

            if *v == target && is_null(&new_left) && is_null(&new_right) {
                Tree::Null
            } else {
                Tree::Node(*v, Box::new(new_left), Box::new(new_right))
            }
        }
    }
}

pub fn remove_leaf_nodes(root: &Tree, target: i64) -> Tree {
    dfs(root, target)
}
