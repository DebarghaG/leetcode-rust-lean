fn tree_depth(t: &Tree) -> i64 {
    match t {
        Tree::Null => -1,
        Tree::Node(_, left, right) => {
            let dl = tree_depth(&**left);
            let dr = tree_depth(&**right);
            if dl > dr {
                dl + 1
            } else {
                dr + 1
            }
        }
    }
}

fn clone_tree(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(v, left, right) => Tree::Node(
            *v,
            Box::new(clone_tree(&**left)),
            Box::new(clone_tree(&**right)),
        ),
    }
}

fn lca_deepest_helper(t: &Tree) -> Tree {
    match t {
        Tree::Null => Tree::Null,
        Tree::Node(_, left, right) => {
            let dl = tree_depth(&**left);
            let dr = tree_depth(&**right);

            if dl > dr {
                lca_deepest_helper(&**left)
            } else if dr > dl {
                lca_deepest_helper(&**right)
            } else {
                clone_tree(t)
            }
        }
    }
}

pub fn lca_deepest_leaves(root: &Tree) -> Tree {
    lca_deepest_helper(root)
}
