fn max2(a: i64, b: i64) -> i64 {
    if a > b { a } else { b }
}

fn tree_height(t: &Tree) -> i64 {
    match t {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let lh = tree_height(&**left);
            let rh = tree_height(&**right);
            let m = max2(lh, rh);
            m + 1
        }
    }
}

pub fn diameter_of_binary_tree(root: &Tree) -> i64 {
    match root {
        Tree::Null => 0,
        Tree::Node(_, left, right) => {
            let ld = diameter_of_binary_tree(&**left);
            let rd = diameter_of_binary_tree(&**right);
            let lh = tree_height(&**left);
            let rh = tree_height(&**right);
            let through = lh + rh;
            let best = max2(through, ld);
            max2(best, rd)
        }
    }
}
